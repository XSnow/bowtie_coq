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
Ltac solve_false := try intro; try solve [false; eauto 2 with FalseHd].

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
                         match T with
                         | exists _ , _ => destruct H
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
  | X `notin` ?L -> _ =>
    let H1 := fresh "H" in
    assert (H1 : X `notin` L) by solve_notin;
    specialize (H H1); clear H1
  end.

Ltac instantiate_cofinites_with x :=
  repeat match goal with
  | H : forall x, x `notin` ?L -> _ |- _ =>
    instantiate_cofinite_with H x
  | H : x `notin` ?L -> _ |- _ =>
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

Lemma lc_typ_rename : forall A X Y,
    X \notin (typefv_typ A) -> lc_typ (A -^ X) -> lc_typ (A -^ Y).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: lc_typ [X ~~> (t_tvar_f Y)] (A -^ X)).
  applys~ typsubst_typ_lc_typ.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Ltac solve_lc_4 :=
  progress (* in case X is Y *)
    ( match goal with
      | |- lc_typ (?A -^ ?y) => unfold open_typ_wrt_typ; simpl
      end;
      try econstructor;
      match goal with
      | H: ?y `notin` _ |- lc_typ (open_typ_wrt_typ_rec 0 (t_tvar_f ?x) ?A) => applys lc_typ_rename y; [solve_notin | ]
      end ).

#[export] Hint Extern 1 (lc_typ _) => progress solve_lc_4 : core.

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

Lemma typsubst_typ_algo_sub_typ : forall A B X Y,
  algo_sub A B ->
  algo_sub ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B).
Proof with (simpl in *; eauto using typsubst_typ_spli_typ, typsubst_typ_splu_typ).
  introv s. gen X Y.
  induction s; intros...
  - applys~ (ASub_forall (L \u {{X}})).
    introv Fr. forwards* HS: H0 X0 X Y.
    rewrite 2 typsubst_typ_open_typ_wrt_typ in HS...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in HS...
Qed.

#[export] Hint Resolve typsubst_typ_ordu_typ typsubst_typ_ordi_typ
 typsubst_typ_spli_typ typsubst_typ_splu_typ typsubst_typ_algo_sub_typ : core.

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

Lemma algo_sub_rename : forall A B X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) ->
    algo_sub ( A -^ X ) ( B -^ X ) ->
    algo_sub ( A -^ Y ) ( B -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: algo_sub [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X)).
  applys~ typsubst_typ_algo_sub_typ.
  simpl in H. rewrite 2 typsubst_typ_spec in H.
  rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H...
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

#[export]
Hint Extern 1 (algo_sub ( ?A -^ ?Y ) _ ) =>
  match goal with
| H: algo_sub ( A -^ ?X ) ( ?B -^ ?X ) |- _ => applys algo_sub_rename H; solve_notin
  end : core.

#[local] Hint Resolve ordi_rename ordu_rename spli_rename splu_rename algo_sub_rename : core.


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
Hint Extern 1 =>
match goal with
| H: spli (?B -^ ?X) ?B1 ?B2 |-
  spli (t_forall ?B) (t_forall ?A (close_typ_wrt_typ ?X ?B1)) (t_forall ?A (close_typ_wrt_typ ?X ?B2)) =>
  applys spli_forall_exists H; solve_notin
| H: splu (?B -^ ?X) ?B1 ?B2 |-
  splu (t_forall ?B) (t_forall ?A (close_typ_wrt_typ ?X ?B1)) (t_forall ?A (close_typ_wrt_typ ?X ?B2)) =>
  applys splu_forall_exists H; solve_notin
| H: spli (?B -^ ?X) _ _ |-
  spli (t_forall ?B) _ _ =>
  apply spli_forall_exists in H; try rewrite close_typ_wrt_typ_open_typ_wrt_typ in *; try solve_notin
| H: splu (?B -^ ?X) _ _ |-
  splu (t_forall ?B) _ _ =>
  apply splu_forall_exists in H; try rewrite close_typ_wrt_typ_open_typ_wrt_typ in *; try solve_notin
end : core.

Ltac try_lc_typ_constructors :=
  (now applys lc_t_tvar_f +
  applys lc_t_top +
  applys lc_t_bot) +
  match goal with
  | |- lc_typ (t_arrow _ _) => applys lc_t_arrow
  | |- lc_typ (t_and _ _) => applys lc_t_and
  | |- lc_typ (t_rcd _ _) => applys lc_t_rcd
  | |- lc_typ (t_forall _) => applys lc_t_forall; intros; instantiate_cofinites
                                                            (*
         (* pick fresh first if no atom exists *)
  | x : atom |- _ =>
    (* use the lemma from rule_inf.v instead of lc_t_forall *)
    applys lc_t_forall_exists x;
    instantiate_cofinites_with x
  | |- _ =>
    let x := fresh in pick fresh x;
    applys lc_t_forall_exists x;
    instantiate_cofinites_with x *)
  end.

(* destruct hypotheses *)
Ltac inverts_all_lc :=
  repeat match goal with
         | H: lc_typ (t_or _ _) |- _ => inverts H
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


Ltac inverts_all_spl :=
repeat match goal with
| H: splu (t_and _ _) _ _ |- _ => inverts H
| H: spli (t_or _ _) _ _ |- _ => inverts H
| H: spli (t_rcd _ _) _ _ |- _ => inverts H
| H: splu (t_rcd _ _) _ _ |- _ => inverts H
| H: spli (t_arrow _ _) _ _ |- _ => inverts H
| H: splu (t_arrow _ _) _ _ |- _ => inverts H
| H: spli (t_forall _) _ _ |- _ => inverts H
| H: splu (t_forall _) _ _ |- _ => inverts H
end.


Ltac inverts_for_lc u :=
  repeat match goal with
  | H: lc_typ ?B |- _ => match B with
                           | u => try exact H
                           | context [ u ] => inverts H
                         end
         end.

#[export] Hint Extern 4 (lc_typ ?A ) =>
destruct_conj; progress inverts_for_lc A : LcHd.

#[export] Hint Extern 4 (lc_typ (?A -^ _) ) =>
  destruct_conj;
  progress match A with
           | t_and ?A1 ?A2 => inverts_for_lc A1; inverts_for_lc A2
           | _ => inverts_for_lc A
           end : LcHd.

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

Lemma algo_sub_lc : forall A B, algo_sub A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H.
  induction~ H;split*.
Qed.

Ltac solve_lc_3 A :=
match goal with
| H: algo_sub A _ |- _ => lets (?&?): algo_sub_lc H; assumption
| H: algo_sub _ A |- _ => lets (?&?): algo_sub_lc H; assumption
end.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_3 A : core.

Lemma lc_forall_inv : forall X A,
    lc_typ (t_forall A) -> lc_typ (A -^ X).
Proof.
  intros. inverts* H.
Qed.

#[local] Hint Resolve lc_forall_inv : core.

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
#[export] Hint Extern 0 (spli (t_arrow _ (t_and _ _)) _ _) => applys SpI_arrow : core.
#[export] Hint Extern 1 (spli (t_arrow (t_or _ _) _) _ _) => applys SpI_arrowUnion : core.
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
| [ H1: ordu (t_tvar_b _ ) |- _ ] => inverts H1; fail
| [ H1: splu (t_tvar_b _ ) |- _ ] => inverts H1; fail
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
| [ H1: ordi (t_tvar_b _ ) |- _ ] => inverts H1; fail
| [ H1: spli (t_tvar_b _ ) |- _ ] => inverts H1; fail
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

#[export] Hint Extern 1 (ordi _) => applys splu_keep_ord_l; eassumption.
#[export] Hint Extern 1 (ordi _) => applys splu_keep_ord_r; eassumption.
#[export] Hint Extern 1 (ordu _) => applys spli_keep_ord_l; eassumption.
#[export] Hint Extern 1 (ordu _) => applys spli_keep_ord_r; eassumption.

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
             let x := fresh "x" in
             pick fresh x; instantiate_cofinites_with x; (* forall x, x `notin` .. -> spli .. *)
             spl_size; simpl in *;
             try repeat rewrite size_typ_open_typ_wrt_typ_var in *; (* spl A-^X ... *)
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

Ltac solve_algo_sub :=
match goal with
| |- algo_sub (t_tvar_f _) (t_tvar_f _) => simple apply ASub_refl
| |- algo_sub _ t_top => simple apply ASub_top
| |- algo_sub t_bot _ => simple apply ASub_bot
| |- algo_sub (t_and ?A ?B) (t_and ?A ?B) => applys ASub_and; [ | applys ASub_andl | applys ASub_andr ]
| |- algo_sub _ (t_and _ _) => applys ASub_and
| H1: spli ?A ?A1 ?A2 |- algo_sub _ ?A => applys ASub_and H1
| H: algo_sub ?A ?C |- algo_sub (t_and ?A _) ?C => applys ASub_andl H
| H: algo_sub ?B ?C |- algo_sub (t_and _ ?B) ?C => applys ASub_andr H
| |- algo_sub (t_and ?A _) ?A => applys ASub_andl
| |- algo_sub (t_and _ ?A) ?A => applys ASub_andr
| H1: spli ?A ?A1 ?A2 , H2: algo_sub ?A1 ?C |- algo_sub ?A ?C => applys ASub_andl H1 H2
| H1: spli ?A ?A1 ?A2 , H2: algo_sub ?A2 ?C |- algo_sub ?A ?C => applys ASub_andr H1 H2

| |- algo_sub (t_or ?A ?B) (t_or ?A ?B) => applys ASub_or; [ | applys ASub_or | applys ASub_or ]
| |- algo_sub (t_or _ _) _ => applys ASub_or
| H1: splu ?A ?A1 ?A2 |- algo_sub ?A _ => applys ASub_or H1
| H: algo_sub ?C ?A |- algo_sub ?C (t_or ?A _) => applys ASub_orl H
| H: algo_sub ?C ?B |- algo_sub ?C (t_or _ ?B) => applys ASub_orr H
| |- algo_sub ?A (t_or ?A _) => applys ASub_orl
| |- algo_sub ?A (t_or _ ?A) => applys ASub_orr
| H1: splu ?A ?A1 ?A2 , H2: algo_sub ?C ?A1 |- algo_sub ?C ?A => applys ASub_orl H1 H2
| H1: splu ?A ?A1 ?A2 , H2: algo_sub ?C ?A2 |- algo_sub ?C ?A => applys ASub_orr H1 H2
| |- algo_sub (t_arrow _ _) (t_arrow _ _) => simple apply ASub_arrow
| |- algo_sub (t_forall _) (t_forall _) => simple apply ASub_forall
| |- algo_sub (t_rcd _ _) (t_rcd _ _) => simple apply ASub_rcd
end.

Hint Extern 1 (algo_sub _ _) => solve_algo_sub : core.

(* algorithm correctness *)
Lemma algo_sub_rcd_inv : forall l A B,
    algo_sub (t_rcd l A) (t_rcd l B) -> algo_sub A B.
Proof.
  introv H.
  indTypSize (size_typ A + size_typ B).
  inverts H; inverts_all_spl; inverts_all_ord; try assumption;
    repeat match goal with
           | H: algo_sub (t_rcd l _) (t_rcd l _) |- _ => forwards: IH H; elia; clear H
           end; inverts_all_lc.
  all: eauto.
Qed.
(* no need
Lemma algo_sub_forall_inv : forall A B X,
    algo_sub (t_forall A) (t_forall B) ->
    (exists L, X `notin` L -> algo_sub (A -^ X) (B -^ X)).
Proof.
  introv H.
  indTypSize (size_typ (A -^ X) + size_typ (B -^ X)).
  inverts H; inverts_all_spl; inverts_all_ord; try assumption;
    repeat match goal with
           | H: algo_sub (t_forall _) (t_forall _) |- _ => forwards(?&?): IH H; elia; clear H
           end.
  1: exists*.
  all: pick_fresh Y;
    match type of Fr with
      _ `notin` ?U => exists U; intros Fry; instantiate_cofinites_with X; eauto
    end.
  Unshelve. apply empty.
Qed.

Lemma algo_sub_forall_inv_2 : forall A B,
    algo_sub (t_forall A) (t_forall B) ->
    (exists L, forall X, X `notin` L -> algo_sub (A -^ X) (B -^ X)).
Proof with (try eassumption; eauto).
  intros.
  indTypSize (size_typ A + size_typ B).
  inverts H; inverts_all_spl; inverts_all_lc; try assumption;
    repeat match goal with
           | H: algo_sub (t_forall _) (t_forall _) |- _ => forwards(?&?): IH H; elia; clear H
           end.
  1: exists*.
  all: pick_fresh Y; assert (algo_sub (A -^ Y) (B -^ Y)); instantiate_cofinites_with Y...
  Unshelve. all: applys empty.
Qed.
*)
Lemma algo_sub_forall_inv : forall A B X,
    algo_sub (t_forall A) (t_forall B) -> algo_sub (A -^ X) (B -^ X).
Proof with (try eassumption).
  intros.
  indTypSize (size_typ A + size_typ B).
  inverts H; inverts_all_spl; inverts_all_lc; try assumption;
    repeat match goal with
           | H: algo_sub (t_forall _) (t_forall _) |- _ => forwards: IH H; elia; clear H
           end.
  1: eauto.
  all: pick_fresh Y; instantiate_cofinites_with Y...
  1: try solve [applys~ algo_sub_rename].
  all:  repeat match goal with
           | H: spli (_ -^ ?Y) _ _ |- _ => forwards~: spli_rename X H; clear H
           | H: splu (_ -^ ?Y) _ _ |- _ => forwards~: splu_rename X H; clear H
           end.
Qed.

Lemma algo_sub_arrow_inv : forall A B C D,
    algo_sub (t_arrow A B) (t_arrow C D) -> (algo_sub C A) /\ (algo_sub B D).
Proof with (try eassumption).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  inverts s; inverts_all_spl; inverts_all_ord; try assumption;
    repeat match goal with
           | H: algo_sub (t_arrow _ _) (t_arrow _ _) |- _ => forwards (?&?): IH H; elia; clear H
           end; inverts_all_lc.
  all: split*.
Qed.

(* key lemma? *)
(* may not hold if arrow can splu since spli and splu do not have to happen on the
same substructure *)
Lemma double_split : forall T A1 A2 B1 B2,
    splu T A1 A2 -> spli T B1 B2 ->
    ((exists C1 C2, spli A1 C1 C2 /\ splu B1 C1 A2 /\ splu B2 C2 A2) \/
    (exists C1 C2, spli A2 C1 C2 /\ splu B1 A1 C1 /\ splu B2 A1 C2)) \/
    ((exists C1 C2, splu B1 C1 C2 /\ spli A1 C1 B2 /\ spli A2 C2 B2) \/
    (exists C1 C2, splu B2 C1 C2 /\ spli A1 B1 C1 /\ spli A2 B1 C2)).
Proof with exists; repeat split*.
  introv Hu Hi.
  indTypSize (size_typ T).
  inverts keep Hu; inverts keep Hi.
  - (* spli or *) left. left...
  - (* spli or *) left. right...
  - (* splu and *) right. left...
  - (* splu and *) right. right...
  - (* forall *) pick fresh X. instantiate_cofinites_with X.
    forwards [ [?|?] | [?|?] ] : IH (A -^ X); try eassumption; elia; destruct_conj.
    left; left... left; right... right; left... right; right...
  - (* rcd *) inverts_all_spl.
    forwards [ [?|?] | [?|?] ] : IH A; try eassumption; elia; destruct_conj.
    left; left... left; right... right; left... right; right...
Qed.


Lemma algo_sub_or_inv : forall A A1 A2 B,
    algo_sub A B -> splu A A1 A2 ->
    algo_sub A1 B /\ algo_sub A2 B.
Proof with (auto_unify; auto; try eassumption; elia; try solve [split; auto]; eauto 4).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; solve_false; auto_unify; auto.
  - split*.
  - (* forall *)
    split; applys ASub_forall (L `union` L0); intros X Fry; instantiate_cofinites_with X.
    all: match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; elia
         end; eauto.
  - (* rcd *)
    match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; elia
    end; split; eauto.
  - (* spli B *)
    repeat match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; clear H1; elia
           end; split; eauto.
  -  (* double split A *)
    forwards [ [?|?] | [?|?] ]: double_split Hspl; try eassumption; destruct_conj;
      try solve [
            match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; elia
            end; split; eauto].
    split*.
  -  (* double split A *)
    forwards [ [?|?] | [?|?] ]: double_split Hspl; try eassumption; destruct_conj;
      try solve [
            match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; elia
            end; split; eauto].
    split*.
  - (* splu B *)
    repeat match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; clear H1; elia
           end; split; eauto.
  - (* splu B *)
    repeat match goal with
              H1 : algo_sub ?A ?B, H2 : splu ?A _ _ |- _ => forwards(?&?): IH H2 H1; clear H1; elia
           end; split; eauto.
Qed.

Lemma algo_sub_orlr_inv : forall A B B1 B2,
    algo_sub A B -> ordu A -> splu B B1 B2 ->
    algo_sub A B1 \/ algo_sub A B2.
Proof with (solve_false; auto_unify; try eassumption; elia; eauto 3).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; solve_false; auto_unify; auto.
  - (* forall *)
    pick fresh X. instantiate_cofinites_with X.
    match goal with
              H0: ordu ?A, H1 : algo_sub ?A ?B, H2 : splu ?B _ _ |- _ => forwards [?|?]: IH H0 H1 H2; elia
    end; eauto.
  - (* rcd *)
    match goal with
              H0: ordu ?A, H1 : algo_sub ?A ?B, H2 : splu ?B _ _ |- _ => forwards [?|?]: IH H0 H1 H2; elia
    end; eauto.
  - (* double split *)
    forwards [ [?|?] | [?|?] ]: double_split H; try eassumption; destruct_conj;
      repeat match goal with
               H0: ordu ?A, H1 : algo_sub ?A ?B, H2 : splu ?B _ _ |- _ => forwards [?|?]: IH H0 H1 H2; clear H1; elia
             end; eauto.
  - forwards [?|?]: IH H1...
  - forwards [?|?]: IH H1...
    Unshelve. all: apply empty.
Qed.

Lemma algo_sub_and_inv : forall A B B1 B2,
    algo_sub A B -> spli B B1 B2 -> algo_sub A B1 /\ algo_sub A B2.
Proof with (try eassumption).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; solve_false; auto_unify; auto;
    repeat match goal with
              H1 : algo_sub ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): IH H1 H2; clear H1; elia
    end.
  - split*.
  - split; applys* ASub_arrow.
  - forwards (?&?): algo_sub_or_inv H... split; applys* ASub_arrow.
  - (* forall *)
    split; applys ASub_forall (L `union` L0); intros X Fry; instantiate_cofinites_with X.
    all: match goal with
              H1 : algo_sub ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): IH H1 H2; elia
         end; eauto.
  - (* rcd *) split*.
  - (* spli B *) split~.
  - (* spli B *) split~.
  - (* spli B *) split~.
  - (* double split B *)
    forwards [ [?|?] | [?|?] ]: double_split Hspl; try eassumption; destruct_conj;
      try solve [
            match goal with
              H1 : algo_sub ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): IH H1 H2; clear H1; elia
            end; split; eauto].
    split*.
  - (* double split B *)
    forwards [ [?|?] | [?|?] ]: double_split Hspl; try eassumption; destruct_conj;
      try solve [
            match goal with
              H1 : algo_sub ?A ?B, H2 : spli ?B _ _ |- _ => forwards(?&?): IH H1 H2; clear H1; elia
            end; split; eauto].
    split*.
Qed.

(* previous and_inv spl_inv *)
Lemma algo_sub_andlr_inv : forall A B A1 A2,
    algo_sub A B -> spli A A1 A2 -> ordi B ->
    algo_sub A1 B \/ algo_sub A2 B.
Proof with (try eassumption; elia).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; inverts_all_spl; inverts_all_ord; solve_false; auto_unify; auto;
    repeat match goal with
              H0: ordi ?B, H1 : algo_sub ?A ?B, H2 : spli ?A _ _ |- _ => forwards [?|?]: IH H1 H2 H0; clear H1; elia
    end.
  - (* arrow *) eauto. - (* arrow *) eauto.
  - forwards [?|?]: algo_sub_orlr_inv H7... all: eauto.
  - (* forall *)
    pick fresh X. instantiate_cofinites_with X.
    match goal with
              H0: ordi ?B, H1 : algo_sub ?A ?B, H2 : spli ?A _ _ |- _ => forwards [?|?]: IH H1 H2 H0; clear H1; elia
    end; eauto.
  - (* rcd *) eauto. - (* rcd *) eauto.
  - (* double split *)
    forwards [ [?|?] | [?|?] ]: double_split Hspl; try eassumption; destruct_conj;
      repeat match goal with
               H0: ordi ?B, H1 : algo_sub ?A ?B, H2 : spli ?A _ _ |- _ => forwards [?|?]: IH H1 H2 H0; clear H1; elia
             end; eauto.
  - forwards [?|?]: IH H1... all: eauto.
  - forwards [?|?]: IH H1... all: eauto.
    Unshelve. all: apply empty.
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_inv                *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end               *)
(*                                          *)
(********************************************)
Ltac auto_inv :=
  repeat try match goal with
         | [ H1: algo_sub (t_arrow _ _) (t_arrow _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_arrow_inv H1; clear H1)
         | [ H1: algo_sub (t_forall _) (t_forall _) |- _ ] =>
           try (forwards~ : algo_sub_forall_inv H1; clear H1)
         | [ H1: algo_sub (t_rcd ?l _) (t_rcd ?l _) |- _ ] =>
           try (forwards~ : algo_sub_rcd_inv H1; clear H1)
         | [ H1: algo_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ H1: algo_sub ?A ?B, H2: spli ?B _ _ |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1 H2; clear H1)
         | [ H1: algo_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ordi ?B, H1: algo_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_sub_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algo_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: algo_sub_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: algo_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): algo_sub_or_inv H1 H2; clear H1)
         | [ H1: algo_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): algo_sub_or_inv H1; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: algo_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_sub_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: algo_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: algo_sub_orlr_inv H1 Hord; clear H1)
             end.

Lemma trans_via_top : forall A B,
    algo_sub t_top B -> lc_typ A -> algo_sub A B.
Proof.
  introv s c.
  inductions s; eauto; solve_false.
Qed.

Ltac algo_trans_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ , H1: algo_sub ?A  ?B , H2: algo_sub ?B  ?C |- algo_sub ?A  ?C ] =>
    (applys~ IH H1 H2; elia; auto)
  | [ IH: forall A B : typ, _ , H1: algo_sub ?A  ?B  |- algo_sub ?A  ?C ] =>
    (applys~ IH H1; elia; try constructor~)
  | [ IH: forall A B : typ, _ , H2: algo_sub ?B  ?C |- algo_sub ?A  ?C ] =>
    (applys~ IH H2; elia; try constructor~)
  end.

Lemma algo_trans : forall A B C, algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof with (solve_false; auto_unify; try (intros Fry; instantiate_cofinites); try eassumption; auto; auto_inv; try solve algo_trans_autoIH).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).

  lets [Hi|(?&?&Hi)]: ordi_or_split C...
  - lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split B...
      lets [Hu'|(?&?&Hu')]: ordu_or_split B...
      lets [Hi''|(?&?&Hi'')]: ordi_or_split A...
      * (* double ord A B *)
        inverts s1; auto_unify...
        ** (* top *) applys~ trans_via_top.
        ** (* arrow *) inverts~ s2...
           *** applys ASub_arrow...
           *** applys ASub_orl...
           *** applys ASub_orr...
        ** (* forall *) inverts~ s2...
           *** applys ASub_forall...
           *** applys ASub_forall (L `union` L0)...
           *** applys ASub_orl... algo_trans_autoIH. applys ASub_forall...
           *** applys ASub_orr... algo_trans_autoIH. applys ASub_forall...
        ** (* rcd *) inverts~ s2...
           *** applys ASub_rcd...
           *** applys ASub_orl...
           *** applys ASub_orr...
      * applys ASub_andl...
      * applys ASub_andr...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split A...
      * applys ASub_or Hu...
      * assert (algo_sub x C)...
        assert (algo_sub x0 C)...
  - applys ASub_and Hi...
Qed.

#[local] Hint Resolve algo_trans : AllHd.

Lemma algo_sub_distArrU: forall A B C,
    lc_typ A -> lc_typ B -> lc_typ C -> algo_sub (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_or A B) C).
Proof with (try eassumption; elia; eauto 3).
  introv.
  indTypSize (size_typ C).
  lets~ [Hi1|(?&?&Hi1)]: ordi_or_split C.
  - applys* ASub_and.
  - (* split C x x0 *)
    forwards Hs1: IH A B x... forwards Hs2: IH A B x0...
    applys ASub_and...
    + applys algo_trans Hs1... applys ASub_and. eauto. applys* ASub_andl. applys* ASub_andr.
    + applys algo_trans Hs2. applys ASub_and. eauto. applys* ASub_andl. applys* ASub_andr.
Qed.

#[local] Hint Resolve algo_sub_distArrU : core.

Lemma label_dec : forall l1 l2: l, {l1=l2}+{~l1=l2}.
Proof.
  repeat decide equality.
Defined.

Theorem decidability : forall A B,
    lc_typ A -> lc_typ B -> algo_sub A B \/ not (algo_sub A B).
Proof with (elia; inverts_all_lc; try eassumption; simpl in *; solve_false; try solve [right; intros HF; auto_inv; inverts HF; simpl in *; solve_false]; eauto 3).
  introv.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)] : ordi_or_split B. easy.
  - lets [Hi'|(?&?&Hi')]: ordi_or_split A. easy.
    + lets [Hu|(?&?&Hu)]: ordu_or_split A. easy.
      * lets [Hu'|(?&?&Hu')]: ordu_or_split B. easy.
        ** (* all ordinary *)
          destruct A; destruct B...
          *** (* fvar *) case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intros.
              **** subst*.
              **** right... inverts H2...
          *** (* rcd *) case_eq (@eq_dec l label_dec l5 l0); intros.
              **** subst*. forwards [IHA1|IHA1] : IH A B...
              **** right... inverts H0...
          *** (* arrow *)
            forwards [IHA1|IHA1] : IH B1 A1...
            forwards [IHA2|IHA2] : IH A2 B2...
          *** (* forall *) instantiate_cofinites. specialize (H1 x). specialize (H2 x).
              forwards [IHA1|IHA1] : IH (A -^ x) (B -^ x)...
              (* right. intros HF. forwards~: algo_sub_forall_inv HF. *)
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
  Unshelve. applys empty.
Qed.


Lemma dsub_splu: forall A B C,
    splu A B C -> declarative_subtyping B A /\ declarative_subtyping C A.
Proof.
  introv H.
  induction H; try solve [intuition; eauto 3].
  - split; applys DSub_CovAll; intros X Fry; instantiate_cofinites_with X;
    eauto.
Qed.

Lemma dsub_spli: forall A B C,
    spli A B C -> declarative_subtyping A B /\ declarative_subtyping A C.
Proof.
  introv H.
  induction H; try forwards: dsub_splu H0;  try solve [intuition; eauto 3].
  - split; applys DSub_CovAll; intros X Fry; instantiate_cofinites_with X;
    eauto.
Qed.

Lemma dsub_symm_and: forall A B,
    lc_typ A -> lc_typ B -> declarative_subtyping (t_and A B) (t_and B A).
Proof.
  intros. applys~ DSub_InterR.
Qed.

Lemma dsub_symm_or: forall A B,
    lc_typ A -> lc_typ B -> declarative_subtyping (t_or A B) (t_or B A).
Proof.
  intros. applys~ DSub_UnionL.
Qed.

Lemma dsub_or: forall A B C,
    splu A B C -> declarative_subtyping A (t_or B C).
Proof.
  introv H.
  induction H.
  - eauto.
  - applys DSub_Trans. 2: { applys~ DSub_CovDistUInterL. } eauto.
  - applys DSub_Trans. 2: { applys~ DSub_CovDistUInterR. } eauto.
  - applys DSub_Trans. applys DSub_CovAll (t_or A1 A2).
    intros X Fry. unfolds open_typ_wrt_typ. simpl. auto.
    applys~ DSub_CovDistUAll.
  - applys DSub_Trans. applys~ DSub_CovIn (t_or A1 A2).
    applys~ DSub_CovDistUIn.
Qed.

Lemma dsub_and: forall A B C,
    spli A B C -> declarative_subtyping (t_and B C) A.
Proof.
  introv H.
  induction H.
  - eauto.
  - applys DSub_Trans. applys~ DSub_CovDistIUnionL. applys* DSub_UnionL.
  - applys DSub_Trans. applys~ DSub_CovDistIUnionR. applys* DSub_UnionL.
  - applys DSub_Trans. applys~ DSub_CovDistIArr. eauto.
  - applys DSub_Trans. applys~ DSub_FunDistI. applys~ DSub_FunCon.
    eauto using dsub_or.
  - applys DSub_Trans.
    2: { applys DSub_CovAll (t_and A1 A2).
         intros X Fry. unfolds open_typ_wrt_typ. simpl. auto. }
    applys~ DSub_CovDistIAll.
  - applys DSub_Trans.
    2: { applys~ DSub_CovIn (t_and A1 A2). }
    applys~ DSub_CovDistIIn.
Qed.

#[local] Hint Resolve dsub_and dsub_or : core.


Lemma asub_symm_and: forall A B,
    lc_typ A -> lc_typ B -> algo_sub (t_and A B) (t_and B A).
Proof.
  intros. applys~ ASub_and.
Qed.

Lemma asub_symm_or: forall A B,
    lc_typ A -> lc_typ B -> algo_sub (t_or A B) (t_or B A).
Proof.
  intros. applys~ ASub_or.
Qed.

Theorem dsub2asub: forall A B,
    declarative_subtyping A B <-> algo_sub A B.
Proof with (simpl in *; try applys SpI_and; try applys SpU_or; try eassumption; eauto 4).
  split; introv H.
  - induction H; eauto 3.
    1: applys algo_trans...
    1,2,3,4: solve_algo_sub...
    1,2,3,5: applys* ASub_and.
    2,4: applys* ASub_or.
    2: {
    inverts_all_lc. pick fresh Y. specialize (H1 Y). unfolds open_typ_wrt_typ. simpl in *. inverts_all_lc.
    applys* ASub_or. }
    1: {
      applys algo_trans (t_and (t_or A C) (t_or B C)).
      - applys ASub_and; [eauto | applys* ASub_andl | applys* ASub_andr].
      - applys algo_trans (t_or (t_and A B) C).
        + applys* ASub_and.
        + applys* asub_symm_or.
    }
    1: {
      applys algo_trans (t_or (t_and A C) (t_and B C)).
      - applys algo_trans (t_and (t_or A B) C).
        + applys* asub_symm_and.
        + applys* ASub_or.
      - applys ASub_or; [eauto | applys* ASub_orl | applys* ASub_orr].
    }
    Unshelve. all: applys empty.
  - induction H; auto.
    + (* arrow *) applys DSub_Trans. applys~ DSub_CovArr IHalgo_sub2. applys~ DSub_FunCon IHalgo_sub1.
    + (* forall *) applys* DSub_CovAll.
    + (* and *) applys DSub_Trans (t_and B1 B2)...
    + (* andl *) forwards (?&?): dsub_spli H. applys DSub_Trans IHalgo_sub...
    + (* andr *) forwards (?&?): dsub_spli H. applys DSub_Trans IHalgo_sub...
    + (* or *) applys DSub_Trans (t_or A1 A2)...
    + (* orl *) forwards (?&?): dsub_splu H. applys DSub_Trans IHalgo_sub...
    + (* orr *) forwards (?&?): dsub_splu H. applys DSub_Trans IHalgo_sub...
Qed.
