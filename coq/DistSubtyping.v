(*******************************************************************************
*                                                                              *
*   DistSubtyping.v                                                            *
*   Xuejing Huang 2021                                                         *
*   Distributed under the terms of the GPL-v3 license                          *
*                                                                              *
*   This file is part of DistributingTypes.                                    *
*                                                                              *
*   DistributingTypes is free software: you can redistribute it and/or modify  *
*   it under the terms of the GNU General Public License as published by       *
*   the Free Software Foundation, either version 3 of the License, or          *
*   (at your option) any later version.                                        *
*                                                                              *
*   DistributingTypes is distributed in the hope that it will be useful,       *
*   but WITHOUT ANY WARRANTY; without even the implied warranty of             *
*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *
*   GNU General Public License for more details.                               *
*                                                                              *
*   You should have received a copy of the GNU General Public License          *
*   along with DistributingTypes.  If not, see <https://www.gnu.org/licenses/>.*
*                                                                              *
*******************************************************************************)

(** This file contains the declarative and algorithmic subtyping formalization.
    The algorithmic system is proved to be sound and complete w.r.t the
    declarative one (in Thereoem dsub2asub).
    Some inversion lemmas (end with _inv) are provided to justify the algorithm.
    The formulation is the same as ../coq/syntax_ott.v.
    We hope this stand-alone file can make your work simpler if you are going to
    use the subtyping part (but not the duotyping) only.
 *)

Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Export Definitions.
Require Import LN_Lemmas.

Create HintDb AllHd.
Create HintDb SizeHd.
Create HintDb FalseHd.

Hint Constructors ordi ordu : core.
#[local] Hint Resolve OrdI_var OrdI_top OrdI_bot OrdU_var OrdU_top OrdU_top OrdU_bot OrdU_arrow SpI_and SpU_or : core.
#[local] Hint Resolve ASub_top ASub_bot : core.

(* redefine gather_atoms for pick fresh *)
Ltac gather_atoms ::= (* for type var *)
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let E := gather_atoms_with (fun x : typ => typefv_typ x) in
  constr:(A `union` B `union` C `union` E).


(************************************ Ltac ************************************)

(* try solve the goal by contradiction *)
Create HintDb FalseHd.
Ltac solve_false := try intro; try solve [false; eauto with FalseHd].

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    end
         end.

(* Ltac from Alvin *)
Ltac detect_fresh_var_and_do t :=
  match goal with
  | Fr : ?x `notin` ?L1 |- _ => t x
  | _ =>
    let x := fresh "x" in
    pick fresh x; t x
  end.

Ltac instantiate_cofinite_with H X :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
    let H1 := fresh "H" in
    assert (H1 : X `notin` L) by solve_notin;
    specialize (H X H1); clear H1
  end.

Ltac instantiate_cofinites_with x :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> _ |- _ =>
    instantiate_cofinite_with H x
         end;
  destruct_conj.

Ltac instantiate_cofinites :=
  detect_fresh_var_and_do instantiate_cofinites_with.

Ltac applys_and_instantiate_cofinites_with H x :=
  applys H x; try solve_notin; instantiate_cofinites_with x.

Ltac pick_fresh_applys_and_instantiate_cofinites H :=
  let X:= fresh in
  pick fresh X; applys_and_instantiate_cofinites_with H X.

Ltac detect_fresh_var_and_apply H :=
  let f x := applys_and_instantiate_cofinites_with H x in
  detect_fresh_var_and_do f.

(************************ Notations related to types **************************)
Notation "[ z ~~> u ] t" := (typsubst_typ u z t) (at level 0).
Notation "t ^-^ u"       := (open_typ_wrt_typ t u) (at level 67).
Notation "t -^ x"        := (open_typ_wrt_typ t (t_tvar_f x))(at level 67).
Notation "[[ A ]]"         := (typefv_typ A) (at level 0).

(********************* lc & rename & subst **********************************)

Ltac try_lc_typ_constructors :=
  now applys lc_t_tvar_f +
  now applys lc_t_top +
  now applys lc_t_bot +
  match goal with
  | |- _ lc_typ (t_arrow _ _) => applys lc_t_arrow
  | |- _ lc_typ (t_and _ _) => applys lc_t_and
  | |- _ lc_typ (t_rcd _ _) => applys lc_t_rcd
         (* pick fresh first if no atom exists *)
  | x : atom |- _ =>
    (* use the lemma from rule_inf.v instead of lc_t_forall *)
    applys lc_t_forall_exists x;
    instantiate_cofinites_with x
  | |- _ =>
    let x := fresh in pick fresh x;
    applys lc_t_forall_exists x;
    instantiate_cofinites_with x
  end.

(* destruct hypotheses *)
Ltac inverts_all_lc :=
repeat match goal with
| H: lc_typ (t_and _ _) |- _ => inverts H
| H: lc_typ (t_rcd _ _) |- _ => inverts H
| H: lc_typ (t_arrow _ _) |- _ => inverts H
| H: lc_typ (t_forall _) |- _ => inverts H
end.

Ltac inverts_all_ord :=
repeat match goal with
| H: ordu (t_and _ _) |- _ => inverts H
| H: ordi (t_or _ _) |- _ => inverts H
| H: ordi (t_rcd _ _) |- _ => inverts H
| H: ordu (t_rcd _ _) |- _ => inverts H
| H: ordi (t_arrow _ _) |- _ => inverts H
| H: ordu (t_arrow _ _) |- _ => inverts H
| H: ordi (t_forall _) |- _ => inverts H
| H: ordu (t_forall _) |- _ => inverts H
end.


Ltac inverts_for_lc u :=
  repeat match goal with
  | H: lc_typ ?B |- _ => match B with
                           | u => try exact H
                           | context [ u ] => inverts H
                         end
         end.

#[export] Hint Extern 1 (lc_typ ?A ) =>
destruct_conj; progress inverts_for_lc A : core.

#[export] Hint Extern 1 (lc_typ (?A -^ _) ) =>
  destruct_conj;
  progress match A with
           | t_and ?A1 ?A2 => inverts_for_lc A1; inverts_for_lc A2
           | _ => inverts_for_lc A
           end : core.

#[export] Hint Extern 1 (lc_typ _ ) => try_lc_typ_constructors : core.

Lemma ordu_lc : forall A, ordu A -> lc_typ A.
Proof.
  introv H.
  induction~ H.
Qed.

Lemma ordi_lc : forall A, ordi A -> lc_typ A.
Proof.
  introv H.
  induction~ H. eauto using ordu_lc.
Qed.

Hint Immediate ordu_lc ordi_lc : core.

Lemma splu_lc : forall A B C, splu A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof.
  introv H.
  induction H; repeat split*.
Qed.

(* get lc_typ information from existing hypotheses *)
Ltac solve_lc_1 A :=
match goal with
| H: ordi A |- _ => lets: ordi_lc H; assumption
| H: ordu A |- _ => lets: ordi_lc H; assumption
| H: splu A _ _ |- _ => lets (?&?&?): splu_lc H; assumption
| H: splu _ A _ |- _ => lets (?&?&?): splu_lc H; assumption
| H: splu _ _ A |- _ => lets (?&?&?): splu_lc H; assumption
end.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_1 A : core.

Lemma spli_lc : forall A B C, spli A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof.
  introv H.
  induction H; repeat split*.
Qed.

Ltac solve_lc_2 A :=
match goal with
| H: spli A _ _ |- _ => lets (?&?&?): spli_lc H; assumption
| H: spli _ A _ |- _ => lets (?&?&?): spli_lc H; assumption
| H: spli _ _ A |- _ => lets (?&?&?): spli_lc H; assumption
end.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_2 A : core.


Lemma lc_typ_rename : forall A X Y,
    X \notin (typefv_typ A) -> lc_typ (A -^ X) -> lc_typ (A -^ Y).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: lc_typ [X ~~> (t_tvar_f Y)] (A -^ X)).
  applys~ typsubst_typ_lc_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma lc_forall_inv : forall X A,
    lc_typ (t_forall A) -> lc_typ (A -^ X).
Proof.
  intros. inverts* H.
Qed.

#[local] Hint Resolve lc_forall_inv : core.


(* rename / typsubst in ord & split *)
#[local] Hint Resolve typsubst_typ_lc_typ : core.
(* #[local] Hint Constructors ordi ordu spli splu : core FalseHd. *)

(*********************************)
(* some useful lemmas            *)
(* for proving typsubst lemmas:  *)
(* lc_t_forall_exists            *)
(* typsubst_typ_spec             *)
(* typsubst_typ_open_typ_wrt_typ *)
(*********************************)

(* mimic typsubst_typ_lc_typ *)
Lemma typsubst_typ_ordu_typ : forall A X Y,
  ordu A ->
  ordu ( [X ~~> (t_tvar_f Y)] A ).
Proof with (simpl in *; eauto).
  introv Ord. gen X Y. induction Ord; intros...
  - destruct (X==X0)...
  - applys~ (OrdU_forall (L \u {{X}})).
    introv Fr. forwards* Ord: H0 X0 X Y.
    rewrite typsubst_typ_open_typ_wrt_typ in Ord...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in Ord...
Qed.

Lemma typsubst_typ_ordi_typ : forall A X Y,
  ordi A ->
  ordi ( [X ~~> (t_tvar_f Y)] A ).
Proof with (simpl in *; eauto using typsubst_typ_ordu_typ).
  introv Ord. gen X Y. induction Ord; intros...
  - destruct (X==X0)...
  - applys~ (OrdI_forall (L \u {{X}})).
    introv Fr. forwards* Ord: H0 X0 X Y.
    rewrite typsubst_typ_open_typ_wrt_typ in Ord...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in Ord...
Qed.

Hint Immediate typsubst_typ_ordu_typ typsubst_typ_ordi_typ : core.

Lemma typsubst_typ_splu_typ : forall A B C X Y,
  splu A B C->
  splu ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B) ([X ~~> (t_tvar_f Y)] C).
Proof with (simpl in *; eauto).
  introv Spl. gen X Y.
  induction Spl; intros...
  - applys~ (SpU_forall (L \u {{X}})).
    introv Fr. forwards* Spl: H0 X0 X Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in Spl...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in Spl...
Qed.

Lemma typsubst_typ_spli_typ : forall A B C X Y,
  spli A B C->
  spli ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B) ([X ~~> (t_tvar_f Y)] C).
Proof with (simpl in *; eauto using typsubst_typ_ordi_typ, typsubst_typ_splu_typ).
  introv Spl. gen X Y.
  induction Spl; intros...
  - applys~ (SpI_forall (L \u {{X}})).
    introv Fr. forwards* Spl: H0 X0 X Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in Spl...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in Spl...
Qed.

#[export] Hint Resolve typsubst_typ_ordu_typ typsubst_typ_ordi_typ
 typsubst_typ_spli_typ typsubst_typ_splu_typ : core.

Lemma ordu_rename : forall A X Y,
    X \notin (typefv_typ A) -> ordu( A -^ X ) -> ordu( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: ordu[X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ typsubst_typ_ordu_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma ordi_rename : forall A X Y,
    X \notin (typefv_typ A) -> ordi ( A -^ X ) -> ordi ( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: ordi [X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ typsubst_typ_ordi_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma splu_rename : forall A B C X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) \u (typefv_typ C)->
    splu ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    splu ( A -^ Y ) ( B -^ Y ) ( C -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: splu [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X) [X ~~> (t_tvar_f Y)] (C -^ X)).
  applys~ typsubst_typ_splu_typ.
  simpl in H. rewrite 3 typsubst_typ_spec in H.
  rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma spli_rename : forall A B C X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) \u (typefv_typ C)->
    spli ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    spli ( A -^ Y ) ( B -^ Y ) ( C -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: spli [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X) [X ~~> (t_tvar_f Y)] (C -^ X)).
  applys~ typsubst_typ_spli_typ.
  simpl in H. rewrite 3 typsubst_typ_spec in H.
  rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

#[export]
Hint Extern 1 (ordu ( ?A -^ ?Y )) =>
  match goal with
  | H: ordu ( A -^ ?X ) |- _ => let Fr := fresh in
                               assert (Fr: X \notin (typefv_typ A)) by solve_notin;
                                 applys ordu_rename Fr H
  end : core.

#[export]
Hint Extern 1 (ordi ( ?A -^ ?Y )) =>
  match goal with
  | H: ordi ( A -^ ?X ) |- _ => let Fr := fresh in
                               assert (Fr: X \notin (typefv_typ A)) by solve_notin;
                                 applys ordi_rename Fr H
  end : core.

#[export]
Hint Extern 1 (splu ( ?A -^ ?Y ) _ _) =>
  match goal with
| H: splu ( A -^ ?X ) ( ?B -^ ?X ) ( ?C -^ ?X ) |- _ => applys splu_rename H; solve_notin
end : core.

#[export]
Hint Extern 1 (spli ( ?A -^ ?Y ) _ _) =>
  match goal with
| H: spli ( A -^ ?X ) ( ?B -^ ?X ) ( ?C -^ ?X ) |- _ => applys spli_rename H; solve_notin
end : core.

#[local] Hint Resolve ordi_rename ordu_rename spli_rename splu_rename : core.

Lemma ordu_forall_exists : forall X B,
  X `notin` typefv_typ B ->
  ordu (open_typ_wrt_typ B (t_tvar_f X)) ->
  ordu (t_forall B).
Proof with (simpl in *; eauto).
  introv Fr Ord.
  applys~ OrdU_forall (typefv_typ B).
Qed.

Lemma ordi_forall_exists : forall X B,
  X `notin` typefv_typ B ->
  ordi (open_typ_wrt_typ B (t_tvar_f X)) ->
  ordi (t_forall B).
Proof with (simpl in *; eauto).
  introv Fr Ord.
  applys~ OrdI_forall (typefv_typ B).
Qed.

#[export]
Hint Extern 1 =>
match goal with
| H: ordi (open_typ_wrt_typ ?B (t_tvar_f ?X)) |- ordi (t_forall _ ?B) =>
  applys~ ordi_forall_exists H; solve_notin
end : core.

#[export]
Hint Extern 1 =>
match goal with
| H: ordu (open_typ_wrt_typ ?B (t_tvar_f ?X)) |- ordu (t_forall _ ?B) =>
  applys~ ordu_forall_exists H; solve_notin
end : core.


Lemma splu_fv_1 : forall A B C,
    splu A B C -> (typefv_typ B) [<=] (typefv_typ A).
Proof with (subst; simpl in *).
  introv Hspl.
  induction Hspl; simpl in *; try fsetdec.
  remember ((typefv_typ A) \u (typefv_typ A1)).
  pick fresh X.
  forwards~ Aux1: H0 X.
  lets* Aux2: typefv_typ_open_typ_wrt_typ_upper A (t_tvar_f X).
  lets* Aux3: typefv_typ_open_typ_wrt_typ_lower A1 (t_tvar_f X).
  assert (HS: typefv_typ A1 [<=] union (typefv_typ (t_tvar_f X)) (typefv_typ A)) by fsetdec.
  clear Aux1 Aux2 Aux3...
  fsetdec.
Qed.

Lemma splu_fv_2 : forall A B C,
    splu A B C -> (typefv_typ C) [<=] (typefv_typ A).
Proof with (subst; simpl in *).
  introv Hspl.
  induction Hspl; simpl in *; try fsetdec.
  remember ((typefv_typ A) \u (typefv_typ A2)).
  pick fresh X.
  forwards~ Aux1: H0 X.
  lets* Aux2: typefv_typ_open_typ_wrt_typ_upper A (t_tvar_f X).
  lets* Aux3: typefv_typ_open_typ_wrt_typ_lower A2 (t_tvar_f X).
  assert (HS: typefv_typ A2 [<=] union (typefv_typ (t_tvar_f X)) (typefv_typ A)) by fsetdec.
  clear Aux1 Aux2 Aux3...
  fsetdec.
Qed.

Lemma splu_forall_exists : forall X B B1 B2,
  X `notin` typefv_typ B ->
  splu (B -^ X) B1 B2->
  splu (t_forall B) (t_forall (close_typ_wrt_typ X B1)) (t_forall (close_typ_wrt_typ X B2)).
Proof with (simpl in *; eauto).
  introv Fr H.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B1 X) in H.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B2 X) in H.
  applys SpU_forall. intros. applys splu_rename H.
  repeat rewrite typefv_typ_close_typ_wrt_typ.
  solve_notin.
  Unshelve. applys empty.
Qed.

Lemma spli_fv_1 : forall A B C,
    spli A B C -> (typefv_typ B) [<=] (typefv_typ A).
Proof with (subst; simpl in *).
  introv Hspl.
  induction Hspl; simpl in *; try fsetdec.
  - lets: splu_fv_1 H0. fsetdec.
  -
  remember ((typefv_typ A) \u (typefv_typ A1)).
  pick fresh X.
  forwards~ Aux1: H0 X.
  lets* Aux2: typefv_typ_open_typ_wrt_typ_upper A (t_tvar_f X).
  lets* Aux3: typefv_typ_open_typ_wrt_typ_lower A1 (t_tvar_f X).
  assert (HS: typefv_typ A1 [<=] union (typefv_typ (t_tvar_f X)) (typefv_typ A)) by fsetdec.
  clear Aux1 Aux2 Aux3...
  fsetdec.
Qed.

Lemma spli_fv_2 : forall A B C,
    spli A B C -> (typefv_typ C) [<=] (typefv_typ A).
Proof with (subst; simpl in *).
  introv Hspl.
  induction Hspl; simpl in *; try fsetdec.
  - lets: splu_fv_2 H0. fsetdec.
  -
  remember ((typefv_typ A) \u (typefv_typ A2)).
  pick fresh X.
  forwards~ Aux1: H0 X.
  lets* Aux2: typefv_typ_open_typ_wrt_typ_upper A (t_tvar_f X).
  lets* Aux3: typefv_typ_open_typ_wrt_typ_lower A2 (t_tvar_f X).
  assert (HS: typefv_typ A2 [<=] union (typefv_typ (t_tvar_f X)) (typefv_typ A)) by fsetdec.
  clear Aux1 Aux2 Aux3...
  fsetdec.
Qed.

Lemma spli_forall_exists : forall X B B1 B2,
  X `notin` typefv_typ B ->
  spli (B -^ X) B1 B2->
  spli (t_forall B) (t_forall (close_typ_wrt_typ X B1)) (t_forall (close_typ_wrt_typ X B2)).
Proof with (simpl in *; eauto).
  introv Fr H.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B1 X) in H.
  rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ B2 X) in H.
  applys SpI_forall. intros. applys spli_rename H.
  repeat rewrite typefv_typ_close_typ_wrt_typ.
  solve_notin.
  Unshelve. applys empty.
Qed.

#[export]
Hint Extern 2 =>
match goal with
| H: spli (?B -^ ?X) ?B1 ?B2 |-
  spli (t_forall ?B) (t_forall ?A (close_typ_wrt_typ ?X ?B1)) (t_forall ?A (close_typ_wrt_typ ?X ?B2)) =>
  applys spli_forall_exists H; solve_notin
| H: splu (?B -^ ?X) ?B1 ?B2 |-
  splu (t_forall ?B) (t_forall ?A (close_typ_wrt_typ ?X ?B1)) (t_forall ?A (close_typ_wrt_typ ?X ?B2)) =>
  applys splu_forall_exists H; solve_notin
| H: spli (?B -^ ?X) _ _ |-
  spli (t_forall ?B) _ _ =>
  applys spli_forall_exists H; solve_notin
| H: splu (?B -^ ?X) _ _ |-
  splu (t_forall ?B) _ _ =>
  applys splu_forall_exists H; solve_notin
end : core.


(*********************************** ord & split *******************************)
#[export] Hint Extern 1 (ordi _) =>
progress match goal with
         | H: forall X : atom, X `notin` _ -> ordi (?B -^ X) |- ordi (t_forall ?B) => applys OrdI_forall H
         | |- ordi (t_forall _) => detect_fresh_var_and_apply ordi_forall_exists
         | _ => applys OrdI_var + applys OrdI_top + applys OrdI_bot + applys OrdI_arrow + applys OrdI_forall
         end : core.

#[export] Hint Extern 1 (ordu _) =>
progress match goal with
         | H: forall X : atom, X `notin` _ -> ordu (?B -^ X) |- ordu (t_forall ?B) => applys OrdU_forall H
         | |- ordu (t_forall _) => detect_fresh_var_and_apply ordu_forall_exists
         | _ => applys OrdU_var + applys OrdU_top + applys OrdU_bot + applys OrdU_arrow + applys OrdU_forall
         end : core.

#[export] Hint Extern 0 (spli (t_and _ _) _ _) => applys SpI_and : core.
#[export] Hint Extern 0 (splu (t_or _ _) _ _) => applys SpU_or : core.
#[export] Hint Extern 1 (spli _ _ _) => applys SpI_arrow + applys SpI_in + applys SpI_and : core.
#[export] Hint Extern 1 (splu _ _ _) => applys SpU_in + applys SpU_or : core.

#[export] Hint Extern 1 (spli (t_forall _)  _ _) => applys SpI_forall : core.
#[export] Hint Extern 1 (splu (t_forall _)  _ _) => applys SpU_forall : core.


(* Types are Either Ordinary or Splittable *)
Lemma ordu_or_split: forall A,
    lc_typ A -> ordu A \/ exists B C, splu A B C.
Proof with (subst~; simpl in *; eauto).
  introv Lc. induction Lc...
  - forwards* [?|(?&?&?)]: IHLc.
  - (* and *)
    forwards* [?|(?&?&?)]: IHLc1.
    forwards* [?|(?&?&?)]: IHLc2.
  - (* forall *)
    pick fresh x for [[B]].
    forwards* [?|(?&?&?)]: H0 x.
Qed.

Lemma ordi_or_split: forall A,
    lc_typ A -> ordi A \/ exists B C, spli A B C.
Proof with (subst~; simpl in *; eauto).
  introv Lc. induction Lc...
  - forwards* [?|(?&?&?)]: IHLc.
  - (* and *)
    forwards* [?|(?&?&?)]: IHLc1.
    forwards* [?|(?&?&?)]: IHLc2.
  - (* arrow *)
    forwards* [?|(?&?&?)]: IHLc2.
    forwards* [?|(?&?&?)]: ordu_or_split A.
  - (* forall *)
    pick fresh x for [[B]].
    forwards* [?|(?&?&?)]: H0 x.
Qed.

(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)

(* splittable types and disjoint types are not overlapping *)

Lemma splu_ord_false : forall A B C,
    lc_typ A -> splu A B C -> ordu A -> False.
Proof with eauto.
  introv Lc Spl Ord. gen B C.
  induction Ord; intros; inverts Spl...
  pick fresh X. eauto.
Qed.

#[export]
 Hint Extern 0 =>
match goal with
| [ H1: splu ?T _ _ , H2: ordu ?T |- _ ] => applys~ splu_ord_false H1 H2
| [ H1: ordu (t_or _ _) |- _ ] => inverts H1; fail
| [ H1: splu _ _ _ |- _ ] => inverts H1; fail
end : FalseHd.

Lemma spli_ord_false : forall A B C,
    lc_typ A -> spli A B C -> ordi A -> False.
Proof with eauto.
  introv Lc Spl Ord. gen B C.
  induction Ord; intros; inverts Spl...
  solve_false.
  pick fresh X. eauto.
Qed.

#[export]
 Hint Extern 0 =>
match goal with
| [ H1: spli ?T _ _ , H2: ordi ?T |- _ ] => applys~ spli_ord_false H1 H2
| [ H1: ordi (t_and _ _) |- _ ] => inverts H1; fail
| [ H1: spli _ _ _ |- _ ] => inverts H1; fail
end : FalseHd.

#[export]
 Hint Extern 1 => try match goal with
                               | [ H1: ordi (t_arrow _ ?A), H2: spli ?A _ _ |- _ ] =>
                                 inverts H1; applys spli_ord_false H2; trivial;
                                   fail
                               | [ H1: ordi ?A, H2: spli (t_arrow _ ?A) _ _ |- _ ] =>
                                 inverts H2; applys spli_ord_false H1; trivial;
                                   fail
                               end : FalseHd.

#[export]
 Hint Extern 3 (False) =>
match goal with
| [ H1: forall _, _ `notin` _ -> spli _ _ _ , H2: forall _ , _ `notin` _ -> ordi _ |- _ ]
  => let Xf := fresh in
     let H1f := fresh in
     let H2f := fresh in
     (pick fresh Xf; forwards~ H1f: H1 Xf; forwards~ H2f: H2 Xf; applys~ spli_ord_false H1f H2f); fail
| [ H1: forall _, _ `notin` _ -> splu _ _ _ , H2: forall _ , _ `notin` _ -> ordu _ |- _ ]
  => let Xf := fresh in
     let H1f := fresh in
     let H2f := fresh in
     (pick fresh Xf; forwards~ H1f: H1 Xf; forwards~ H2f: H2 Xf; applys~ splu_ord_false H1f H2f); fail
end : FalseHd.

(* lemmas for ordinary *)
Lemma spli_keep_ord_l : forall A B C,
   spli A B C -> ordu A -> ordu B.
Proof.
  introv Hspl Hord.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

Lemma spli_keep_ord_r : forall A B C,
   spli A B C -> ordu A -> ordu C.
Proof.
  introv Hspl Hord.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

Lemma splu_keep_ord_l : forall A B C,
   splu A B C -> ordi A -> ordi B.
Proof.
  introv Hspl Hord.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

Lemma splu_keep_ord_r : forall A B C,
   splu A B C -> ordi A -> ordi C.
Proof.
  introv Hspl Hord.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

#[local] Hint Resolve spli_keep_ord_l spli_keep_ord_r splu_keep_ord_l splu_keep_ord_r : core.


(************************ type sizes **************************)
(** defines size on types and proves some related
lemmas. It aims to make later proofs easier if they do
induction on the size of types *)

Lemma splu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  pick fresh X. forwards* (?&?): H0.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H2.
  eauto...
Qed.

Lemma spli_decrease_size: forall A B C,
    spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  - forwards (?&?): splu_decrease_size H0...
  - pick fresh X. forwards* (?&?): H0.
    rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
    rewrite 2 size_typ_open_typ_wrt_typ_var in H2.
    eauto...
Qed.

Ltac spl_size :=
  try repeat match goal with
         | [ H: splu _ _ _ |- _ ] =>
           ( lets (?&?): splu_decrease_size H; clear H)
         | [ H: spli _ _ _ |- _ ] =>
           ( lets (?&?): spli_decrease_size H; clear H)
             end.

(********************************************)
(*                                          *)
(*               Ltac elia                  *)
(*  enhanced lia with split_decrease_size   *)
(*                                          *)
(********************************************)
Ltac elia :=
  try solve [pose proof (size_typ_min);
             spl_size; simpl in *;
             try repeat rewrite size_typ_open_typ_wrt_typ_var;
             try lia].
(* eauto with typSize lngen ? *)

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].



(* Splitting types is deterministic *)
(********************************************)
(*                                          *)
(*          Lemma split_unique              *)
(*                                          *)
(********************************************)
Lemma splu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with eauto.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts* s2;
    try solve [forwards* (eq1&eq2): IHs1; subst*]; solve_false.
  pick fresh X.
  forwards* HS: H2 X.
  forwards* (eq1&eq2): H0 HS.
  assert (HR0: A1 = close_typ_wrt_typ X (A1 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR1: A2 = close_typ_wrt_typ X (A2 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR2: A4 = close_typ_wrt_typ X (A4 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  assert (HR3: A5 = close_typ_wrt_typ X (A5 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
  rewrite HR0. rewrite HR1. rewrite HR2. rewrite HR3.
  rewrite eq1. rewrite eq2. split*.
Qed.

Lemma spli_unique : forall T A1 A2 B1 B2,
    spli T A1 B1 -> spli T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with eauto.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts* s2;
    try solve [forwards* (eq1&eq2): IHs1; subst*]; solve_false.
  - forwards~ (?&?): splu_unique H0 H6. subst~.
  -
    pick fresh X.
    forwards* HS: H2 X.
    forwards* (eq1&eq2): H0 HS.
    assert (HR0: A1 = close_typ_wrt_typ X (A1 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
    assert (HR1: A2 = close_typ_wrt_typ X (A2 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
    assert (HR2: A4 = close_typ_wrt_typ X (A4 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
    assert (HR3: A5 = close_typ_wrt_typ X (A5 -^X)). rewrite close_typ_wrt_typ_open_typ_wrt_typ...
    rewrite HR0. rewrite HR1. rewrite HR2. rewrite HR3.
    rewrite eq1. rewrite eq2. split*.
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_unify              *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end                *)
(*                                          *)
(********************************************)
Ltac auto_unify :=
  simpl in *;
  try solve [applys SpI_and];
  try solve [applys SpU_or];
  try repeat match goal with
         | [ H1: spli ?A  _ _ , H2: spli ?A _ _ |- _ ] =>
           (forwards (?&?): spli_unique H1 H2;
            subst; clear H2)
         | [ H1: splu ?A  _ _ , H2: splu ?A _ _ |- _ ] =>
           (forwards (?&?): splu_unique H1 H2;
            subst; clear H2)
         end.


(*****************************************************************************)
Inductive i_part : typ -> typ -> Prop :=
| IP_refl  : forall A, lc_typ A -> i_part A A
| IP_spl   : forall A B C B', spli A B C -> i_part B B' -> i_part A B'
| IP_spr   : forall A B C C', spli A B C -> i_part C C' -> i_part A C'
.

Inductive u_part : typ -> typ -> Prop :=
| UP_refl  : forall A, lc_typ A -> u_part A A
| UP_spl   : forall A B C B', splu A B C -> u_part B B' -> u_part A B'
| UP_spr   : forall A B C C', splu  A B C -> u_part C C' -> u_part A C'
.

#[local] Hint Constructors i_part u_part : core.
#[local] Hint Resolve IP_refl UP_refl : core.

Lemma i_part_lc : forall A B,
    i_part A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H.
  induction* H.
Qed.

Lemma u_part_lc : forall A B,
    u_part A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H.
  induction* H.
Qed.

Ltac solve_lc_3 A :=
match goal with
| H: i_part A _ |- _ => lets (?&?): i_part_lc H; assumption
| H: i_part _ A |- _ => lets (?&?): i_part_lc H; assumption
| H: u_part A _ |- _ => lets (?&?): u_part_lc H; assumption
| H: u_part _ A |- _ => lets (?&?): u_part_lc H; assumption
end.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_3 A : core.

Lemma i_part_keep_ordu : forall A B,
   i_part A B -> ordu A -> ordu B.
Proof.
  introv Par Ord.
  induction~ Par.
  all: apply IHPar.
  applys* spli_keep_ord_l Ord.
  applys* spli_keep_ord_r Ord.
Qed.

Lemma u_part_keep_ordi : forall A B,
   u_part A B -> ordi A -> ordi B.
Proof.
  introv Par Ord.
  induction~ Par.
  all: apply IHPar.
  applys* splu_keep_ord_l Ord.
  applys* splu_keep_ord_r Ord.
Qed.

#[local] Hint Resolve i_part_keep_ordu u_part_keep_ordi : core.

Lemma i_part_spl : forall A B B1 B2,
    i_part A B -> spli B B1 B2 -> i_part A B1 /\ i_part A B2.
Proof with (eauto with AllHd).
  introv Hp Hspl.
  induction Hp; try forwards~ (?&?): IHHp; split;
    eauto with AllHd.
Qed.

Lemma u_part_spl : forall A B B1 B2,
    u_part A B -> splu B B1 B2 -> u_part A B1 /\ u_part A B2.
Proof with (eauto with AllHd).
  introv Hp Hspl.
  induction Hp; try forwards~ (?&?): IHHp; split;
    eauto with AllHd.
Qed.

#[local] Hint Resolve i_part_spl u_part_spl : core.

#[export]
 Hint Extern 0 =>
match goal with
| [ H1: lc_typ _ |- _ ] => inverts H1; fail
end : FalseHd.


Ltac algo_sub_apply_IH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- algo_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; try elia)
end.

Ltac algo_sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- algo_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; try elia; eauto 3)
end.
(* proved
Lemma algo_sub_part : forall A B,
    (i_part A B -> algo_sub A B)
    /\ (ordi A -> ordi B -> u_part B A -> algo_sub A B).
Proof with (try eassumption; try constructor; try solve [algo_sub_part_autoIH]; eauto 3).
  introv.
  indTypSize (size_typ A + size_typ B).
  split.

  --
  introv Hp.
  lets~ [Hi|(?&?&Hi)]: ordi_or_split B.
  - (* ord B *)
    inverts~ Hp.
    + lets~ [Hu|(?&?&Hu)]: ordu_or_split B; solve_false.
      * destruct B; auto_unify; solve_false...
        all: inverts_all_ord; inverts_all_lc.
        ** applys ASub_forall...
           intros X Fry. instantiate_cofinites_with X. algo_sub_apply_IH.
           applys~ IH1.
      * applys ASub_or Hu; algo_sub_apply_IH; applys* IH2.
    + applys ASub_andl...
    + applys ASub_andr...

  - (* spl B *)
    lets~ (?&?): i_part_spl Hp Hi.
    applys ASub_and Hi...

    --
    introv Ho1 Ho2 Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + inverts Hp; auto_unify...
      * (* ord B *)
      destruct A; auto_unify; auto; solve_false...
        ** applys ASub_forall...
           intros X Fry. instantiate_cofinites_with X. algo_sub_apply_IH.
           applys~ IH1.
      * applys ASub_orl...
      * applys ASub_orr...
    +
      lets~ (?&?): u_part_spl Hp Hu.
      applys ASub_or...
  Unshelve. apply empty.
Qed.
*)
Lemma algo_sub_part : forall A B,
    (i_part A B -> algo_sub A B)
    /\ (u_part B A -> algo_sub A B).
Proof with (try eassumption; try constructor; try solve [algo_sub_part_autoIH]; eauto 3).
  introv.
  indTypSize (size_typ A + size_typ B).
  split.

  --
  introv Hp.
  lets~ [Hi|(?&?&Hi)]: ordi_or_split B.
  - (* ord B *)
    inverts~ Hp.
    + lets~ [Hu|(?&?&Hu)]: ordu_or_split B; solve_false.
      * destruct B; auto_unify; solve_false...
        all: inverts_all_ord; inverts_all_lc.
        ** applys ASub_forall...
           intros X Fry. instantiate_cofinites_with X. algo_sub_apply_IH.
           applys~ IH1.
      * applys ASub_or Hu; algo_sub_apply_IH; applys* IH2.
    + applys ASub_andl...
    + applys ASub_andr...

  - (* spl B *)
    lets~ (?&?): i_part_spl Hp Hi.
    applys ASub_and Hi...

    --
    introv Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + inverts Hp; auto_unify...
      * (* ord B *)
        destruct A; auto_unify; auto; solve_false...
        ** inverts_all_lc. applys ASub_and. eauto.
           all: algo_sub_apply_IH; applys* IH1.
        ** applys ASub_forall...
           intros X Fry. instantiate_cofinites_with X. algo_sub_apply_IH.
           applys~ IH1.
      * applys ASub_orl...
      * applys ASub_orr...
    +
      lets~ (?&?): u_part_spl Hp Hu.
      applys ASub_or...
  Unshelve. apply empty.
Qed.

Theorem algo_sub_refl : forall A, lc_typ A -> algo_sub A A.
Proof.
  introv.
  pose proof (algo_sub_part A A).
  destruct H; auto with *.
Qed.

Lemma algo_sub_part1 : forall A B,
    i_part A B -> algo_sub A B.
Proof.
  introv.
  pose proof (algo_sub_part A B).
  destruct* H.
Qed.

Lemma algo_sub_part2 : forall A B,
    u_part B A -> algo_sub A B.
Proof.
  introv.
  pose proof (algo_sub_part A B).
  destruct* H.
Qed.

#[local] Hint Resolve algo_sub_refl : MulHd.
#[local] Hint Resolve algo_sub_part1 algo_sub_part2 : AllHd.

(* algorithm correctness *)
Lemma algo_rule_and_inv : forall A B B1 B2,
    algo_sub A B -> spli B B1 B2 -> algo_sub A B1 /\ algo_sub A B2.
Proof.
  intros.
  induction H; solve_false; auto_unify; jauto; auto with *.
  Show.
Qed.

(* previous and_inv spl_inv *)
Lemma algo_rule_andlr_inv : forall A B A1 A2,
    algo_sub A B -> spli A A1 A2 -> ordi B ->
    algo_sub A1 B \/ algo_sub A2 B.
Proof.
  introv Hsub Hord Hspl.
  inverts Hsub; solve_false; auto_unify; auto with *.
Qed.


Lemma algo_rule_or_inv : forall A A1 A2 B,
    algo_sub A B -> splu A A1 A2 ->
    algo_sub A1 B /\ algo_sub A2 B.
Proof with (auto_unify; try eassumption; algo_elia; eauto 4 with AllHd ).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - inverts Hsub; solve_false; auto_unify; auto with AllHd.
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A0 A2) A0 A2 B...
      * forwards* (?&?): IH (t_or A1 B1) A1 B1 B...
      * forwards* (?&?): IH H2 B...
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A5 A2) A5 A2 B...
      * forwards* (?&?): IH (t_or A1 B2) A1 B2 B...
      * forwards* (?&?): IH H1...
  - forwards (?&?): algo_rule_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...
Qed.

Lemma algo_rule_orlr_inv : forall A B B1 B2,
    algo_sub A B -> ordu A -> splu B B1 B2 ->
    algo_sub A B1 \/ algo_sub A B2.
Proof with (solve_false; auto_unify; try eassumption; algo_elia; eauto 3 with AllHd).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub...
  + (* double split *)
    inverts Hspl; inverts H...
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
    * forwards [?|?]: IH H2...
    * forwards [?|?]: IH H1 H3...
  + forwards [?|?]: IH H1... eauto 4 with AllHd. eauto 4 with AllHd.
  + forwards* [?|?]: IH H1...  eauto 4 with AllHd. eauto 4 with AllHd.
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_inv                *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end               *)
(*                                          *)
(********************************************)
Ltac algo_auto_inv :=
  repeat try match goal with
         | [ H1: algo_sub ?A ?B, H2: spli ?B _ _ |- _ ] =>
           try (forwards~ (?&?): algo_rule_and_inv H1 H2; clear H1)
         | [ H1: algo_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_rule_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ordi ?B, H1: algo_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_rule_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algo_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: algo_rule_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: algo_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): algo_rule_or_inv H1 H2; clear H1)
         | [ H1: algo_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): algo_rule_or_inv H1; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: algo_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_rule_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: algo_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: algo_rule_orlr_inv H1 Hord; clear H1)
             end.


Lemma algo_sub_or : forall A A1 A2 B,
    splu A A1 A2 -> algo_sub A1 B -> algo_sub A2 B -> algo_sub A B.
Proof with (auto_unify; try eassumption; algo_auto_inv; algo_elia).
  introv Hspli Hs1 Hs2.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B...
  lets [Hi'|(?&?&Hi')]: ordi_or_split A...
  - applys ASub_or...
  - (* double spliit A *)
    inverts keep Hspli; inverts keep Hi'...
    + applys~ ASub_andl Hi'... applys IH...
    + applys~ ASub_andr Hi'... applys IH...
    + applys~ ASub_andl Hi'... applys IH...
    + applys~ ASub_andr Hi'... applys IH...
    + applys~ ASub_andl Hi'... applys IH...
    + applys~ ASub_andr Hi'...
    + applys~ ASub_andr Hi'...
    + applys~ ASub_andr Hi'...
    + applys~ ASub_andl Hi'...
    + applys~ ASub_andl Hi'...
    + applys~ ASub_andl Hi'...
    + applys~ ASub_andr Hi'... applys IH; eauto; try eassumption; algo_elia.
  - applys~ ASub_and Hi...
    applys IH... applys IH...
Qed.

#[local] Hint Resolve algo_sub_or : AllHd.

Ltac algo_trans_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ , H1: algo_sub ?A  ?B , H2: algo_sub ?B  ?C |- algo_sub ?A  ?C ] =>
    (applys~ IH H1 H2; algo_elia; auto)
  | [ IH: forall A B : typ, _ , H1: algo_sub ?A  ?B  |- algo_sub ?A  ?C ] =>
    (applys~ IH H1; algo_elia; constructor~)
  | [ IH: forall A B : typ, _ , H2: algo_sub ?B  ?C |- algo_sub ?A  ?C ] =>
    (applys~ IH H2; algo_elia; constructor~)
  end.

Lemma algo_trans : forall A B C, algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof with (solve_false; auto_unify; try eassumption; auto with *; algo_auto_inv; try solve algo_trans_autoIH).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets [Hi|(?&?&Hi)]: ordi_or_split C...
  - lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split B...
      lets [Hu'|(?&?&Hu')]: ordu_or_split B...
      lets [Hi''|(?&?&Hi'')]: ordi_or_split A...
      * (* double ord A B *)
        inverts s1; auto_unify...
        ** (* top *)
          inverts~ s2...
          *** applys~ ASub_orl H2...
          *** applys~ ASub_orr H2...
        ** (* arrow *)
          inverts~ s2...
          *** applys~ ASub_arrow...
          *** applys~ ASub_orl H6...
          *** applys~ ASub_orr H6...
      * applys ASub_andl...
      * applys ASub_andr...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split A...
      * applys ASub_or Hu...
      * assert (algo_sub x C)...
        assert (algo_sub x0 C)...
        applys algo_sub_or...
  - applys ASub_and Hi...
Qed.

#[local] Hint Resolve algo_trans : AllHd.

Lemma algo_sub_arrow : forall A1 A2 B1 B2,
    algo_sub B1 A1 -> algo_sub A2 B2 -> algo_sub (t_arrow A1 A2) (t_arrow B1 B2).
Proof with (try eassumption; auto_unify; algo_auto_inv; solve_false; algo_elia; try solve [constructor; auto with AllHd]).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow A1 A2)...
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2)...
  lets [Hu1|(?&?&Hu1)]: ordu_or_split (t_arrow A1 A2)...
  lets [Hu2|(?&?&Hu2)]: ordu_or_split (t_arrow B1 B2)...
  - inverts Hi2.
    + forwards (?&?): algo_rule_and_inv Hs2 H3...
      applys ASub_and.
      econstructor; try eassumption.
      applys~ IH. algo_elia.
      applys~ IH. algo_elia.
    + forwards (?&?): algo_rule_or_inv Hs1 H4.
      applys ASub_and. applys SpI_arrowUnion; try eassumption.
      applys~ IH; algo_elia. applys~ IH; algo_elia.
  - inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: algo_rule_andlr_inv Hs2 H3. inverts~ Hi2.
        applys ASub_andl; try eassumption.
        econstructor. apply H3.
        applys~ IH. algo_elia.
        applys ASub_andr; try eassumption.
        econstructor. apply H3.
        applys~ IH. algo_elia.
      * inverts Hi2.
        ** forwards (?&?): algo_rule_and_inv Hs2 H4.
           applys ASub_and. econstructor; try eassumption.
           applys~ IH; algo_elia. applys~ IH; algo_elia.
        ** forwards (?&?): algo_rule_or_inv Hs1 H5.
           applys ASub_and. applys SpI_arrowUnion; try eassumption.
           applys~ IH; algo_elia. applys~ IH; algo_elia.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: algo_rule_orlr_inv Hs1 H4. inverts~ Hi2.
        1: { applys ASub_andl; try eassumption.
        applys SpI_arrowUnion; try eassumption.
        applys~ IH. algo_elia. }
        1: { applys ASub_andr; try eassumption.
        applys SpI_arrowUnion; try eassumption.
        applys~ IH. algo_elia. }
      * inverts Hi2.
        ** forwards (?&?): algo_rule_and_inv Hs2 H5.
           applys ASub_and. econstructor; try eassumption.
           applys~ IH; algo_elia. applys~ IH; algo_elia.
        ** forwards (?&?): algo_rule_or_inv Hs1 H6.
           applys ASub_and. applys SpI_arrowUnion; try eassumption.
           applys~ IH; algo_elia. applys~ IH; algo_elia.
Qed.

Lemma algo_sub_orl : forall A B B1 B2,
    splu B B1 B2 -> algo_sub A B1 -> algo_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hspli Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ ASub_orl Hspli.
  - applys~ algo_sub_or Hu; applys IH Hspli; algo_elia; applys algo_trans Hs; applys algo_sub_part2...
  - forwards~ [?|?]: algo_rule_andlr_inv Hs Hi'...
      applys~ ASub_andl Hi'. applys~ IH Hspli. algo_elia.
      applys~ ASub_andr Hi'. applys~ IH Hspli. algo_elia.
  - inverts Hspli; inverts Hi; solve_false; auto_unify.
    + applys ASub_and...
      applys IH; algo_elia. 2: {eauto. } applys algo_trans Hs...
      applys IH; algo_elia. 2: {eauto. } applys algo_trans Hs...
    + applys ASub_and...
      applys IH; algo_elia. 2: {eauto. } applys algo_trans Hs...
      applys IH; algo_elia. 2: {eauto. } applys algo_trans Hs...
    + algo_auto_inv.
      applys ASub_and. eauto.
      applys~ IH H; algo_elia.
      try eassumption.
    + algo_auto_inv.
      applys ASub_and. eauto.
      try eassumption.
      applys~ IH H0; algo_elia.
Qed.

Lemma algo_sub_orr : forall A B B1 B2,
    splu B B1 B2 -> algo_sub A B2 -> algo_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hspli Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ ASub_orr Hspli.
  - applys~ algo_sub_or Hu; applys IH Hspli; algo_elia; applys algo_trans Hs; applys algo_sub_part2...
  - forwards~ [?|?]: algo_rule_andlr_inv Hs Hi'...
      applys~ ASub_andl Hi'. applys~ IH Hspli. algo_elia.
      applys~ ASub_andr Hi'. applys~ IH Hspli. algo_elia.
  - inverts Hspli; inverts Hi; solve_false; auto_unify.
    + applys ASub_and...
      applys IH; algo_elia. eauto. applys algo_trans Hs...
      applys IH; algo_elia. eauto. applys algo_trans Hs...
    + applys ASub_and...
      applys IH; algo_elia. eauto. applys algo_trans Hs...
      applys IH; algo_elia. eauto. applys algo_trans Hs...
    + algo_auto_inv.
      applys ASub_and. eauto.
      applys~ IH H; algo_elia.
      try eassumption.
    + algo_auto_inv.
      applys ASub_and. eauto.
      try eassumption.
      applys~ IH H0; algo_elia.
Qed.

Lemma algo_sub_distArrU: forall A B C,
    algo_sub (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_or A B) C).
Proof with (auto_unify; try eassumption).
  introv.
  indTypSize (size_typ C).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split C.
  - applys ASub_and; eauto with *.
  - (* split C x x0 *)
    forwards Hs1: IH A B x. algo_elia.
    forwards Hs2: IH A B x0. algo_elia.
    applys ASub_and. eauto with *.
    + applys algo_trans Hs1. applys ASub_and; eauto with *.
    + applys algo_trans Hs2. applys ASub_and; eauto with *.
Qed.

#[local] Hint Resolve algo_sub_arrow algo_sub_orl algo_sub_orr algo_sub_distArrU : AllHd.

Lemma arrow_inv : forall A B C D,
    algo_sub (t_arrow A B) (t_arrow C D) -> (algo_sub C A) /\ (algo_sub B D).
Proof with (simpl in *; solve_false; auto_unify; try eassumption; algo_auto_inv; eauto 3 with AllHd).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow A B).
  - inverts s...
  - inverts keep Hi1;
      forwards~ [?|?]: algo_rule_andlr_inv s Hi1;
      forwards(IH1&IH2): IH H; try solve [s_elia];
        split; try eassumption; inverts~ Hi2...
  - (* uses and_inv_1 and_inv_2 *)
    forwards (?&?): algo_rule_and_inv s Hi2.
    inverts keep Hi2;
      forwards (?&?): IH H; try solve [s_elia];
        forwards (?&?): IH H0; try solve [s_elia];
          split...
Qed.

Theorem decidability : forall A B,
    algo_sub A B \/ not (algo_sub A B).
Proof with (simpl in *; solve_false; jauto; algo_elia; try solve [right; intros HF; algo_auto_inv; inverts HF; simpl in *; solve_false]; eauto 3 with AllHd).
  introv.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - lets [Hi'|(?&?&Hi')]: ordi_or_split A.
    + lets [Hu|(?&?&Hu)]: ordu_or_split A.
      * lets [Hu'|(?&?&Hu')]: ordu_or_split B.
        ** (* all ordinary *)
          destruct A; destruct B...
          *** forwards [IHA1|IHA1] : IH B1 A1...
              forwards [IHA2|IHA2] : IH A2 B2...
        ** (* spl > B, S-orl/r *)
          forwards [IHA1|IHA1] : IH A x...
          forwards [IHA2|IHA2] : IH A x0...
      * forwards [IHA1|IHA1] : IH x B...
        forwards [IHA2|IHA2] : IH x0 B...
    + (* spl < A, S-andl/r *)
      forwards [IHA1|IHA1] : IH x B...
      forwards [IHA2|IHA2] : IH x0 B...
  - (* spl < B, S-and *)
    forwards [IHA1|IHA1] : IH A x...
    forwards [IHA2|IHA2] : IH A x0...
Qed.

#[local] Hint Constructors declarative_subtyping : AllHd.
#[local] Hint Resolve algo_sub_refl : core.

Lemma dsub_splu: forall A B C,
    splu A B C -> declarative_subtyping B A /\ declarative_subtyping C A.
Proof with intuition.
  introv H.
  induction H; try intuition; eauto 3 with AllHd.
Qed.

Lemma dsub_spl: forall A B C,
    spli A B C -> declarative_subtyping A B /\ declarative_subtyping A C.
Proof with intuition.
  introv H.
  induction H; try forwards: dsub_splu H0; try intuition; eauto 4 with AllHd.
Qed.

#[local] Hint Resolve dsub_splu dsub_spl : AllDb.

Lemma dsub_symm_and: forall A B,
    declarative_subtyping (t_and A B) (t_and B A).
Proof.
  introv.
  applys DS_and; eauto with *.
Qed.

Lemma dsub_symm_or: forall A B,
    declarative_subtyping (t_or A B) (t_or B A).
Proof.
  introv.
  applys DS_or; eauto with *.
Qed.

#[local] Hint Resolve dsub_symm_and dsub_symm_or : AllHd.

Lemma dsub_or: forall A B C,
    splu A B C -> declarative_subtyping A (t_or B C).
Proof with (eauto 3 with AllHd).
  introv H.
  induction H; try intuition; eauto 3 with AllHd.
  - applys DS_trans.
    2: { applys DS_distAnd. }
    eauto 3 with AllHd.
  - applys DS_trans. applys dsub_symm_and.
    applys DS_trans (t_or (t_and B1 A) (t_and B2 A)).
    1: { applys DS_trans.
        2: { applys DS_distAnd. }
        eauto 3 with AllHd. }
    applys DS_or.
    applys DS_trans (t_and A B1)...
    applys DS_trans (t_and A B2)...
Qed.

Lemma dsub_and: forall A B C,
    spli A B C -> declarative_subtyping (t_and B C) A.
Proof with (eauto 3 with AllHd).
  introv H.
  induction H; try intuition...
  - forwards: dsub_or H0...
  - applys DS_trans.
    1: { applys DS_distOr. }
    eauto 3 with AllHd.
  - applys DS_trans. 2: { applys dsub_symm_or. }
    applys DS_trans (t_and (t_or B1 A) (t_or B2 A)).
    2: { applys DS_trans.
         applys DS_distOr.
        eauto 3 with AllHd. }
    applys DS_and.
    applys DS_trans (t_or A B1)...
    applys DS_trans (t_or A B2)...
Qed.

#[local] Hint Resolve dsub_and dsub_or : AllHd.

Theorem dsub2asub: forall A B,
    declarative_subtyping A B <-> algo_sub A B.
Proof with (simpl in *; try eassumption; eauto 3 with *).
  split; introv H.
  - induction H; try solve [constructor; eauto 3 with AllHd]; eauto.
    + applys algo_trans...
    + applys algo_sub_arrow...
    + applys* ASub_and.
    + applys algo_sub_part1...
    + applys algo_sub_part1...
    + applys algo_sub_or. eauto 4 with *. auto. auto.
    + applys algo_sub_orl...
    + applys algo_sub_orr...
    + applys ASub_and...
    + applys ASub_and... eauto 4 with *. eauto 4 with *.
    + applys algo_sub_distArrU.
    + applys* ASub_and...
    + applys algo_sub_or. eauto 4 with *.
      applys ASub_and... applys algo_sub_orl... applys algo_sub_orr...
    + applys algo_sub_or. eauto 4 with *.
      applys algo_sub_orl... applys algo_sub_orr...
  - induction H; auto with *.
    + (* and *)
      applys DS_trans (t_and B1 B2)...
    + (* andl *)
      forwards (?&?): dsub_spl H0. applys DS_trans IHalgo_sub...
    + (* andr *)
      forwards (?&?): dsub_spl H0. applys DS_trans IHalgo_sub...
    +  (* or *)
      applys DS_trans (t_or A1 A2)...
    + (* orl *)
      forwards (?&?): dsub_splu H2. applys DS_trans IHalgo_sub...
    + (* orr *)
      forwards (?&?): dsub_splu H2. applys DS_trans IHalgo_sub...
Qed.
