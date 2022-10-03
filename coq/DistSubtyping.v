(** This file contains the declarative and algorithmic subtyping formalization.
    The algorithmic system is proved to be sound and complete w.r.t the
    declarative one (in Thereoem dsub2asub).
    Some inversion lemmas (end with _inv) are provided to justify the algorithm.
 *)

Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export Definitions.


(************************ Notations related to types **************************)
Notation "[ z ~~> u ] t" := (typsubst_typ u z t) (at level 0).
Notation "t ^-^ u"       := (open_typ_wrt_typ t u) (at level 67).
Notation "t -^ x"        := (open_typ_wrt_typ t (t_tvar_f x))(at level 67).
Notation "[[ A ]]"       := (typefv_typ A) (at level 0).
Notation "A <: B"        := (declarative_subtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

(************************************ Ltac ************************************)

(* redefine gather_atoms for pick fresh *)
Ltac gather_atoms ::= (* for type var *)
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let E := gather_atoms_with (fun x : typ => typefv_typ x) in
  constr:(A `union` B `union` C `union` E).

(* autorewrite with open *)
Create HintDb open.

Lemma open_into_and : forall B C X, (t_and B C) -^ X = t_and (B -^ X) (C -^ X).
Proof. eauto. Qed.

Lemma open_into_or : forall B C X, (t_or B C) -^ X = t_or (B -^ X) (C -^ X).
Proof. eauto. Qed.

Lemma open_into_top : forall X, t_top -^ X = t_top.
Proof. eauto. Qed.

Lemma open_into_bot : forall X, t_bot -^ X = t_bot.
Proof. eauto. Qed.

#[export] Hint Rewrite open_into_and open_into_or open_into_top open_into_bot : open.


(* try solve the goal by contradiction *)
Create HintDb FalseHd.
Ltac solve_false := try intro; try solve [false; eauto 4 with FalseHd].

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
                         lazymatch T with
                         | exists _ , _ => destruct H
                         | _ /\ _ => destruct H
                         end
    end.

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

Ltac specialize_with X :=
  repeat match goal with
  | H : forall X : typevar, _ |- _ => specialize (H X)
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


(******************************* type sizes ***********************************)
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
             pick fresh x; try instantiate_cofinites_with x; (* forall x, x `notin` .. -> spli .. *)
             spl_size; simpl in *; simpl;
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


(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)

#[export] Hint Extern 1 => progress instantiate_cofinites : FalseHd.

(* splittable types and ordinary types do not overlap *)
Lemma splu_ord_false : forall A B C,
    splu A B C -> ordu A -> False.
Proof with solve_false.
  introv Spl Ord. gen B C.
  induction Ord; intros; inverts* Spl...
Qed.

Lemma spli_ord_false : forall A B C,
    spli A B C -> ordi A -> False.
Proof.
  introv Spl Ord. gen B C.
  induction Ord; intros; inverts* Spl.
  eauto using splu_ord_false. solve_false.
Qed.

Ltac find_contradiction_on_split :=
  match goal with
  | [ H1: splu ?T _ _ , H2: ordu ?T |- _ ] => applys~ splu_ord_false H1 H2
  | [ H1: spli ?T _ _ , H2: ordi ?T |- _ ] => applys~ spli_ord_false H1 H2
  | [ H: ordu _ |- _ ] => inverts H; fail
  | [ H: splu _ _ _ |- _ ] => inverts H; fail
  | [ H: ordi _ |- _ ] => inverts H; fail
  | [ H: spli _ _ _ |- _ ] => inverts H; fail
  end.

#[export] Hint Extern 1 => find_contradiction_on_split : FalseHd.

#[export] Hint Extern 1 => applys splu_ord_false; [ eassumption | ] : FalseHd.

#[export] Hint Extern 1 => applys spli_ord_false; [ eassumption | ] : FalseHd.


(*********************** locally closed types and terms ***********************)

Lemma lc_forall_inv : forall A X,
    lc_typ (t_forall A) -> lc_typ (A -^ X).
Proof. intros. inverts~ H. Qed.

#[export] Hint Immediate lc_forall_inv : core.

Ltac solve_lc_by_inv A :=
  match goal with
  | H: lc_typ A |- _ => exact H
  | H: lc_typ (_ -^ _) |- _ => match type of H with context[ A ] => autorewrite with open in H end
  | H: lc_typ (t_or _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_and _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_rcd _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_arrow _ _) |- _ => match type of H with context[ A ] => inverts H end
  | H: lc_typ (t_forall _) |- _ => match type of H with context[ A ] => inverts H end
  end.

#[export] Hint Extern 1 (lc_typ ?A ) => progress repeat solve_lc_by_inv A : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress instantiate_cofinites : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress repeat solve_lc_by_inv A : core.
#[export] Hint Extern 1 (lc_typ (?A -^ ?X) ) =>
            match goal with
              H: forall x, lc_typ _ |- _ =>
              match type of H with context [A] => specialize (H X) end
            end : core.

Lemma ordu_lc : forall A, ordu A -> lc_typ A.
Proof. introv H. induction~ H. Qed.

Lemma ordi_lc : forall A, ordi A -> lc_typ A.
Proof. introv H. induction~ H. eauto using ordu_lc. Qed.

Lemma orduFty_lc : forall Fty, UnionOrdinaryFty Fty -> lc_Fty Fty.
Proof with eauto using ordu_lc. introv H. induction H... Qed.

Lemma splu_lc : forall A B C, splu A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof.
  introv H.
  induction H; repeat split; firstorder using ordu_lc, ordi_lc.
Qed.

Lemma spli_lc : forall A B C, spli A B C -> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof with firstorder using ordu_lc, ordi_lc, splu_lc.
  introv H.
  induction H; repeat split~; constructor...
Qed.

Lemma declarative_subtyping_lc : forall A B, declarative_subtyping A B -> lc_typ A /\ lc_typ B.
Proof.
  introv H. induction H; destruct_conj; split*.
  all: eauto.
  all: inverts H; inverts H0; econstructor;
    intros; autorewrite with open; eauto.
Qed.

Lemma algo_sub_lc : forall A B, algo_sub A B -> lc_typ A /\ lc_typ B.
Proof with firstorder using ordu_lc, ordi_lc, splu_lc, spli_lc.
  introv H.
  induction~ H; split; destruct_conj...
Qed.

Lemma new_splu_lc : forall A B C, new_splu A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof. introv H. induction* H. splits; eauto. Qed.

Lemma new_spli_lc : forall A B C, new_spli A B C-> lc_typ A /\ lc_typ B /\ lc_typ C.
Proof with firstorder using new_splu_lc.
  introv H.
  induction~ H; split; destruct_conj...
Qed.


Ltac solve_lc_by_regularity A :=
  match goal with
  | H: ordu _ |- _ => match type of H with context[ A ] => apply ordu_lc in H end
  | H: ordi _ |- _ => match type of H with context[ A ] => apply ordi_lc in H end
  | H: UnionOrdinaryFty _ |- _ => match type of H with context[ A ] => apply orduFty_lc in H end
  | H: splu _ _ _ |- _ => match type of H with context[ A ] => apply splu_lc in H end
  | H: spli _ _ _ |- _ => match type of H with context[ A ] => apply spli_lc in H end
  | H: algo_sub _ _ |- _ => match type of H with context[ A ] => apply algo_sub_lc in H end
  | H: new_splu _ _ _ |- _ => match type of H with context[ A ] => apply new_splu_lc in H end
  | H: new_spli _ _ _ |- _ => match type of H with context[ A ] => apply new_spli_lc in H end
  | H: declarative_subtyping _ _ |- _ => match type of H with context[ A ] => apply declarative_subtyping_lc in H end
  end;
  destruct_conj.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_by_regularity A : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress solve_lc_by_regularity A : core.

(* destruct hypotheses *)
Ltac inverts_all_lc :=
  repeat lazymatch goal with
         | H: lc_typ (t_or _ _) |- _ => inverts H
         | H: lc_typ (t_and _ _) |- _ => inverts H
         | H: lc_typ (t_rcd _ _) |- _ => inverts H
         | H: lc_typ (t_arrow _ _) |- _ => inverts H
         | H: lc_typ (t_forall _) |- _ => inverts H
         end.

Ltac inverts_all_ord :=
repeat lazymatch goal with
| H: ordi (t_and _ _) |- _ => inverts H
| H: ordu (t_and _ _) |- _ => inverts H
| H: ordi (t_or _ _) |- _ => inverts H
| H: ordu (t_or _ _) |- _ => inverts H
| H: ordi (t_rcd _ _) |- _ => inverts H
| H: ordu (t_rcd _ _) |- _ => inverts H
| H: ordi (t_arrow _ _) |- _ => inverts H
| H: ordu (t_arrow _ _) |- _ => inverts H
| H: ordi (t_forall _) |- _ => inverts H
| H: ordu (t_forall _) |- _ => inverts H
end.


Ltac inverts_all_spl :=
repeat lazymatch goal with
| H: spli (t_and _ _) _ _ |- _ => inverts H
| H: splu (t_and _ _) _ _ |- _ => inverts H
| H: spli (t_or _ _) _ _ |- _ => inverts H
| H: splu (t_or _ _) _ _ |- _ => inverts H
| H: spli (t_rcd _ _) _ _ |- _ => inverts H
| H: splu (t_rcd _ _) _ _ |- _ => inverts H
| H: spli (t_arrow _ _) _ _ |- _ => inverts H
| H: splu (t_arrow _ _) _ _ |- _ => inverts H
| H: spli (t_forall _) _ _ |- _ => inverts H
| H: splu (t_forall _) _ _ |- _ => inverts H
end.

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

(*********************************)
(* some useful lemmas            *)
(* for proving typsubst lemmas:  *)
(* lc_t_forall_exists            *)
(* typsubst_typ_spec             *)
(* typsubst_typ_open_typ_wrt_typ *)
(*********************************)

(* mimic typsubst_lc *)
Lemma rename_ordu : forall A X Y,
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

Lemma rename_ordi : forall A X Y,
  ordi A ->
  ordi ( [X ~~> (t_tvar_f Y)] A ).
Proof with (simpl in *; eauto using rename_ordu).
  introv Ord. gen X Y. induction Ord; intros...
  - destruct (X==X0)...
  - applys~ (OrdI_forall (L \u {{X}})).
    introv Fr. forwards* Ord: H0 X0 X Y.
    rewrite typsubst_typ_open_typ_wrt_typ in Ord...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in Ord...
Qed.

#[export] Hint Immediate rename_ordu rename_ordi : core.

Lemma rename_splu : forall A B C X Y,
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

Lemma rename_spli : forall A B C X Y,
  spli A B C->
  spli ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B) ([X ~~> (t_tvar_f Y)] C).
Proof with (simpl in *; eauto using rename_ordi, rename_splu).
  introv Spl. gen X Y.
  induction Spl; intros...
  - applys~ (SpI_forall (L \u {{X}})).
    introv Fr. forwards* Spl: H0 X0 X Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in Spl...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in Spl...
Qed.

Lemma rename_algo_sub : forall A B X Y,
  algo_sub A B ->
  algo_sub ([X ~~> (t_tvar_f Y)] A) ([X ~~> (t_tvar_f Y)] B).
Proof with (simpl in *; eauto using rename_spli, rename_splu).
  introv s. gen X Y.
  induction s; intros...
  - applys~ (ASub_forall (L \u {{X}})).
    introv Fr. forwards* HS: H0 X0 X Y.
    rewrite 2 typsubst_typ_open_typ_wrt_typ in HS...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in HS...
Qed.

#[export] Hint Immediate rename_ordu rename_ordi
 rename_spli rename_splu rename_algo_sub : core.

Lemma ordu_rename_open : forall A X Y,
    X \notin (typefv_typ A) -> ordu( A -^ X ) -> ordu( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: ordu[X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ rename_ordu.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma ordi_rename_open : forall A X Y,
    X \notin (typefv_typ A) -> ordi ( A -^ X ) -> ordi ( A -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: ordi [X ~~> (t_tvar_f Y)] (A -^ X) ).
  applys~ rename_ordi.
  simpl in H. rewrite typsubst_typ_spec in H.
  rewrite close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma splu_rename_open : forall A B C X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) \u (typefv_typ C)->
    splu ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    splu ( A -^ Y ) ( B -^ Y ) ( C -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: splu [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X) [X ~~> (t_tvar_f Y)] (C -^ X)).
  applys~ rename_splu.
  simpl in H. rewrite 3 typsubst_typ_spec in H.
  rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma spli_rename_open : forall A B C X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) \u (typefv_typ C)->
    spli ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    spli ( A -^ Y ) ( B -^ Y ) ( C -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: spli [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X) [X ~~> (t_tvar_f Y)] (C -^ X)).
  applys~ rename_spli.
  simpl in H. rewrite 3 typsubst_typ_spec in H.
  rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

Lemma algo_sub_rename_open : forall A B X Y,
    X \notin (typefv_typ A) \u (typefv_typ B) ->
    algo_sub ( A -^ X ) ( B -^ X ) ->
    algo_sub ( A -^ Y ) ( B -^ Y ).
Proof with (simpl in *; eauto).
  introv Fr Lc.
  assert (H: algo_sub [X ~~> (t_tvar_f Y)] (A -^ X) [X ~~> (t_tvar_f Y)] (B -^ X)).
  applys~ rename_algo_sub.
  simpl in H. rewrite 2 typsubst_typ_spec in H.
  rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H...
Qed.

#[export]
Hint Extern 1 (ordu ( ?A -^ ?Y )) =>
  match goal with
  | H: ordu ( A -^ ?X ) |- _ => let Fr := fresh in
                               assert (Fr: X \notin (typefv_typ A)) by solve_notin;
                                 applys ordu_rename_open Fr H
  end : core.

#[export]
Hint Extern 1 (ordi ( ?A -^ ?Y )) =>
  match goal with
  | H: ordi ( A -^ ?X ) |- _ => let Fr := fresh in
                               assert (Fr: X \notin (typefv_typ A)) by solve_notin;
                                 applys ordi_rename_open Fr H
  end : core.

#[export]
Hint Extern 1 (splu ( ?A -^ ?Y ) _ _) =>
  match goal with
| H: splu ( A -^ ?X ) ( ?B -^ ?X ) ( ?C -^ ?X ) |- _ => applys splu_rename_open H; solve_notin
end : core.

#[export]
Hint Extern 1 (spli ( ?A -^ ?Y ) _ _) =>
  match goal with
| H: spli ( A -^ ?X ) ( ?B -^ ?X ) ( ?C -^ ?X ) |- _ => applys spli_rename_open H; solve_notin
end : core.

#[export]
Hint Extern 1 (algo_sub ( ?A -^ ?Y ) _ ) =>
  match goal with
| H: algo_sub ( A -^ ?X ) ( ?B -^ ?X ) |- _ => applys algo_sub_rename_open H; solve_notin
  end : core.

#[local] Hint Immediate ordi_rename_open ordu_rename_open spli_rename_open
 splu_rename_open algo_sub_rename_open : core.


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
  applys SpU_forall. intros. applys splu_rename_open H.
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
  applys SpI_forall. intros. applys spli_rename_open H.
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


(*********************************** ord & split *******************************)
#[export] Hint Extern 1 (ordi _) =>
progress match goal with
         | H: forall X : atom, X `notin` _ -> ordi (?B -^ X) |- ordi (t_forall ?B) => applys OrdI_forall H
         | |- ordi (t_forall _) => detect_fresh_var_and_apply ordi_forall_exists
(*         | _ => applys OrdI_var + applys OrdI_top + applys OrdI_bot + applys OrdI_arrow + applys OrdI_forall *)
         end : core.

#[export] Hint Extern 1 (ordu _) =>
progress match goal with
         | H: forall X : atom, X `notin` _ -> ordu (?B -^ X) |- ordu (t_forall ?B) => applys OrdU_forall H
         | |- ordu (t_forall _) => detect_fresh_var_and_apply ordu_forall_exists
 (*         | _ => applys OrdU_var + applys OrdU_top + applys OrdU_bot + applys OrdU_arrow + applys OrdU_forall  *)
         end : core.


#[export] Hint Extern 0 (spli (t_and _ _) _ _) => applys SpI_and : core.
#[export] Hint Extern 0 (splu (t_or _ _) _ _) => applys SpU_or : core.
#[export] Hint Extern 0 (spli (t_arrow _ (t_and _ _)) _ _) => applys SpI_arrow : core.
(*
#[export] Hint Extern 1 (spli (t_arrow (t_or _ _) _) _ _) => applys SpI_arrowUnion : core.
#[export] Hint Extern 1 (spli _ _ _) => applys SpI_arrow + applys SpI_in + applys SpI_and : core.
#[export] Hint Extern 1 (splu _ _ _) => applys SpU_in + applys SpU_or : core.

#[export] Hint Extern 1 (spli (t_forall _)  _ _) => applys SpI_forall : core.
#[export] Hint Extern 1 (splu (t_forall _)  _ _) => applys SpU_forall : core.
*)

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
Defined.

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
Defined.

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

#[export] Hint Extern 1 (ordi _) => applys splu_keep_ord_l; [ eassumption | ] : core.
#[export] Hint Extern 1 (ordi _) => applys splu_keep_ord_r; [ eassumption | ] : core.
#[export] Hint Extern 1 (ordu _) => applys spli_keep_ord_l; [ eassumption | ] : core.
#[export] Hint Extern 1 (ordu _) => applys spli_keep_ord_r; [ eassumption | ] : core.

(*********************** binding ********************************)

Ltac close_typ_var X :=
  repeat match goal with
         | H: ?A = ?B -^ X |- _ =>
           let H' := fresh "Heq" in
           forwards~ H': close_typ_wrt_typ_open_typ_wrt_typ B;
           rewrite <- H in H'; clear H
         end.

Ltac simpl_rename H :=
  match type of H with
  | context [ [?X ~~> _] (_ -^ ?X) ] =>
    rewrite typsubst_typ_spec in H; rewrite close_typ_wrt_typ_open_typ_wrt_typ in H
  | context [ [?X ~~> _] ?A ] =>
    rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ A X) in H;
    rewrite typsubst_typ_spec in H; rewrite close_typ_wrt_typ_open_typ_wrt_typ in H
  end.

Ltac simpl_rename_goal :=
  match goal with
  | |- context [ [?X ~~> _] (_ -^ ?X) ] =>
    rewrite typsubst_typ_spec; rewrite close_typ_wrt_typ_open_typ_wrt_typ
  | |- context [ [?X ~~> _] ?A ] =>
    rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ A X);
    rewrite typsubst_typ_spec; rewrite close_typ_wrt_typ_open_typ_wrt_typ
  end.

Local Ltac open_typ_by_var_in_goal A X :=
    let HR := fresh "Heq" in
    assert (HR: A = close_typ_wrt_typ X (A -^X));
    try solve [rewrite close_typ_wrt_typ_open_typ_wrt_typ; auto];
    rewrite HR.

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
    try solve [forwards* (eq1&eq2): IHs1; subst; split*]; solve_false.
  pick fresh X.
  forwards* HS: H2 X.
  forwards* (eq1&eq2): H0 HS.
  open_typ_by_var_in_goal A1 X.
  open_typ_by_var_in_goal A2 X.
  open_typ_by_var_in_goal A4 X.
  open_typ_by_var_in_goal A5 X.
  rewrite eq1. rewrite eq2. split*.
Qed.

Lemma spli_unique : forall T A1 A2 B1 B2,
    spli T A1 B1 -> spli T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with eauto.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts* s2;
    try solve [forwards* (eq1&eq2): IHs1; subst; split*]; solve_false.
  - forwards~ (?&?): splu_unique H0 H6. subst~.
  -
    pick fresh X.
    forwards* HS: H2 X.
    forwards* (eq1&eq2): H0 HS.
    open_typ_by_var_in_goal A1 X.
    open_typ_by_var_in_goal A2 X.
    open_typ_by_var_in_goal A4 X.
    open_typ_by_var_in_goal A5 X.
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
             | [ H1: spli (t_and _ _)  _ _  |- _ ] =>
               inverts H1
             | [ H1: splu (t_or _ _)  _ _  |- _ ] =>
               inverts H1
             | [ H1: spli ?A  _ _ , H2: spli ?A _ _ |- _ ] =>
               (forwards (?&?): spli_unique H1 H2;
                subst; clear H2)
             | [ H1: splu ?A  _ _ , H2: splu ?A _ _ |- _ ] =>
               (forwards (?&?): splu_unique H1 H2;
                subst; clear H2)
         end.


Ltac basic_auto :=
  destruct_conj; auto_unify;
  try exists; try splits;
  try reflexivity;
  try lazymatch goal with
      | |- lc_typ _ => eauto
      | |- spli _ _ _ => try eapply spli_rename_open; try eassumption; econstructor; try eassumption;
                         eauto
      | |- splu _ _ _ => try eapply splu_rename_open; try eassumption; econstructor; try eassumption;
                         eauto
    end; try eassumption; elia.

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

#[local] Hint Extern 1 (algo_sub _ _) => solve_algo_sub : core.

(* algorithm correctness *)

(* Lemma Inversion of Subtyping [1] *)
Lemma algo_sub_rcd_inv : forall l1 l2 A B,
    algo_sub (t_rcd l1 A) (t_rcd l2 B) -> l1=l2 /\ algo_sub A B.
Proof.
  introv H.
  indTypSize (size_typ A + size_typ B).
  inverts H; inverts_all_spl; inverts_all_ord; try assumption;
    repeat match goal with
           | H: algo_sub (t_rcd _ _) (t_rcd _ _) |- _ => forwards (?&?): IH H; elia; clear H
           end.
  all: eauto.
Qed.

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
  1: try solve [applys~ algo_sub_rename_open].
  all:  repeat match goal with
           | H: spli (_ -^ ?Y) _ _ |- _ => forwards~: spli_rename_open X H; clear H
           | H: splu (_ -^ ?Y) _ _ |- _ => forwards~: splu_rename_open X H; clear H
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

(* A very useful inversion lemma when the type T is both intersection- and
   union- splittable *)
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

(* Lemma Inversion of Subtyping [2] *)
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

Lemma botlike_inv : forall A B,
    algo_sub (t_and A B) t_bot -> algo_sub A t_bot \/ algo_sub B t_bot.
Proof with inverts_all_spl; solve_false.
  introv Sub.
  inductions Sub...
  all: auto.
  all: forwards [?|?]: IHSub1; try reflexivity; try eassumption; elia.
  all: forwards [?|?]: IHSub2; try reflexivity; try eassumption; elia.
  all: try solve [left*].
  all: try solve [right*].
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
  repeat try lazymatch goal with
         | [ H1: algo_sub (t_arrow _ _) (t_arrow _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_arrow_inv H1; clear H1)
         | [ H1: algo_sub (t_forall _) (t_forall _) |- _ ] =>
           try (forwards~ : algo_sub_forall_inv H1; clear H1)
         | [ H1: algo_sub (t_rcd _ _) (t_rcd _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_rcd_inv H1; subst; clear H1)
         | [ H1: algo_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1; clear H1)
      end;
  repeat try lazymatch goal with
         | [ H1: algo_sub ?A ?B, H2: spli ?B _ _ |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1 H2; clear H1)
         | [ H1: algo_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): algo_sub_and_inv H1; clear H1)
      end;
  repeat try lazymatch goal with
         | [ Hord: ordi ?B, H1: algo_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: algo_sub_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algo_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: algo_sub_andlr_inv H1 Hord; clear H1)
      end;
  repeat try lazymatch goal with
         | [ H1: algo_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): algo_sub_or_inv H1 H2; clear H1)
         | [ H1: algo_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): algo_sub_or_inv H1; clear H1)
         end;
  repeat try lazymatch goal with
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

Local Ltac algo_trans_autoIH :=
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


Lemma algo_sub_distArrU: forall A B C,
    lc_typ A -> lc_typ B -> lc_typ C -> algo_sub (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_or A B) C).
Proof with (try eassumption; elia; eauto 3).
  introv.
  indTypSize (size_typ C).
  lets~ [Hi1|(?&?&Hi1)]: ordi_or_split C.
  - applys* ASub_and; [ applys* ASub_andl | applys* ASub_andr ].
  - (* split C x x0 *)
    forwards Hs1: IH A B x... forwards Hs2: IH A B x0...
    applys ASub_and...
    + applys algo_trans Hs1. applys ASub_and. eauto. applys* ASub_andl. applys* ASub_andr.
    + applys algo_trans Hs2. applys ASub_and. eauto. applys* ASub_andl. applys* ASub_andr.
Qed.

#[local] Hint Resolve algo_sub_distArrU : core.

Lemma label_dec : forall l1 l2: l, {l1=l2}+{~l1=l2}.
Proof.
  repeat decide equality.
Defined.

(* decidability of subtyping algorithm *)
Theorem decidability : forall A B,
    lc_typ A -> lc_typ B -> algo_sub A B \/ not (algo_sub A B).
Proof with (elia; inverts_all_lc; try eassumption; simpl in *; solve_false; try solve [right; intros HF; auto_inv; inverts HF; simpl in *; solve_false]; eauto).
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
          *** (* forall *) pick fresh x. specialize (H1 x). specialize (H2 x).
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
Defined.

(* admissible rules *)
Lemma DSub_CovInterL : forall (A C B:typ),
    lc_typ C -> declarative_subtyping A B ->
    declarative_subtyping (t_and A C) (t_and B C).
Proof.
  introv Lc HS.
  applys~ DSub_InterR.
Qed.

Lemma DSub_CovInterR : forall (C A B:typ),
     lc_typ C -> declarative_subtyping A B ->
     declarative_subtyping (t_and C A) (t_and C B).
Proof.
  introv Lc HS.
  applys~ DSub_InterR.
Qed.

Lemma DSub_CovUnionL : forall (A C B:typ),
     lc_typ C -> declarative_subtyping A B ->
     declarative_subtyping (t_or A C) (t_or B C).
Proof.
  introv Lc HS.
  applys* DSub_UnionL.
Qed.

Lemma DSub_CovUnionR : forall (C A B:typ),
     lc_typ C -> declarative_subtyping A B ->
     declarative_subtyping (t_or C A) (t_or C B).
Proof.
  introv Lc HS.
  applys~ DSub_UnionL.
Qed.

Lemma DSub_CovDistIUnionL : forall (A C B:typ),
    lc_typ A -> lc_typ B -> lc_typ C ->
    declarative_subtyping (t_and  (t_or A C) (t_or B C) ) (t_or (t_and A B) C).
Proof.
  introv Lc1 Lc2 Lc3.
  applys DSub_Trans.
  applys* DSub_CovDistUInterL.
  applys DSub_UnionL.
  - applys DSub_Trans (t_and (t_or B C) A).
    + applys~ DSub_InterR.
    + applys DSub_Trans.
      applys~ DSub_CovDistUInterL.
      applys~ DSub_UnionL.
  - applys~ DSub_UnionRR.
Qed.

Lemma DSub_CovDistIUnionR : forall (C A B:typ),
    lc_typ C -> lc_typ A -> lc_typ B ->
    declarative_subtyping (t_and  (t_or C A) (t_or C B) ) (t_or C (t_and A B) ).
Proof.
  introv Lc1 Lc2 Lc3.
  applys DSub_Trans.
  applys* DSub_CovDistUInterL.
  applys DSub_UnionL.
  - applys~ DSub_UnionRL.
  - applys DSub_Trans (t_and (t_or C B) A).
    + applys~ DSub_InterR.
    + applys DSub_Trans.
      applys~ DSub_CovDistUInterL.
      applys~ DSub_UnionL.
Qed.

Lemma DSub_CovDistUInterR : forall (C A B:typ),
    lc_typ A -> lc_typ C -> lc_typ B ->
     declarative_subtyping (t_and C (t_or A B) ) (t_or  (t_and C A) (t_and C B) ).
Proof.
  introv Lc1 Lc2 Lc3.
  applys DSub_Trans (t_and (t_or A B) C).
  - applys~ DSub_InterR.
  - applys DSub_Trans.
    applys~ DSub_CovDistUInterL.
    applys DSub_UnionL.
    + applys~ DSub_UnionRL.
    + applys~ DSub_UnionRR.
Qed.

#[export] Hint Resolve DSub_CovInterL DSub_CovInterR DSub_CovUnionL DSub_CovUnionR DSub_CovDistIUnionL DSub_CovDistIUnionR DSub_CovDistUInterR : core.

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

Ltac split_inter_constructors :=
  applys* SpI_and + applys* SpI_orl +
  applys* SpI_in + applys* SpI_arrow + applys* SpI_orl +
  (applys* SpI_forall; intros; autorewrite with open; auto).
Ltac split_union_constructors :=
  applys* SpU_or + applys* SpU_andl + applys* SpU_in +
  (applys* SpU_forall; intros; autorewrite with open; auto).

Ltac swap_or_r := applys algo_trans; [ | applys asub_symm_or ].
Ltac swap_and_l := applys algo_trans; [ (applys asub_symm_and) | ].
Ltac split_r := applys ASub_and; try split_inter_constructors.
Ltac split_l := applys ASub_or; try split_union_constructors.
Ltac use_left_l := applys ASub_andl; try split_inter_constructors.
Ltac use_right_l := applys ASub_andr; try split_inter_constructors.
Ltac use_left_r := applys ASub_orl; try split_union_constructors.
Ltac use_right_r := applys ASub_orr; try split_union_constructors.

Ltac match_or := split_l; [ use_left_r | use_right_r].
Ltac match_and := split_r; [ use_left_l | use_right_l].
Ltac match_or_rev := split_l; [ use_right_r |  use_left_r ].
Ltac match_and_rev := split_r; [ use_right_l | use_left_l ].
Ltac swap_or_l := applys algo_trans; [ applys asub_symm_or | ].
Ltac swap_and_r := applys algo_trans; [ | (applys asub_symm_and) ].


Theorem dsub2asub: forall A B,
    declarative_subtyping A B <-> algo_sub A B.
Proof with (simpl in *; try applys SpI_and; try applys SpU_or; try eassumption; eauto 4).
  split; introv H.
  - induction H; eauto.
    all: try solve [ match goal with
        | H1: algo_sub ?A ?B, H2: algo_sub ?B ?C |- algo_sub ?A ?C => applys algo_trans H1 H2
        | |- algo_sub (t_and _ _) (t_and _ _) => match_and; auto
        | |- algo_sub (t_and (t_or _ _) (t_or _ _)) (t_or (t_and _ _) _) =>
          match_and; auto
        | |- algo_sub (t_and (t_or _ _) (t_or _ _)) (t_or _ (t_and _ _)) =>
          swap_or_r; auto; match_and; match_or_rev; auto

        | |- algo_sub _ (t_or _ _) => match_or; try applys ASub_refl; auto
        | |- algo_sub (t_or _ _) (_ (t_or _ _)) => match_or; auto
        | |- algo_sub (t_and (t_or _ _) _) (t_or (t_and _ _) (t_and _ _)) =>
          match_or; auto
        | |- algo_sub (t_and _ (t_or _ _)) (t_or (t_and _ _) (t_and _ _)) =>
          swap_and_l; auto; match_or; match_and_rev; auto

        | |- algo_sub (t_and _ _) (_ (t_and _ _)) => match_and; auto
        | |- algo_sub (t_or _ _) (_ _ (t_or _ _)) => match_or; auto
                     end ].
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


Lemma sub_dec : forall A B,
    lc_typ A -> lc_typ B -> declarative_subtyping A B \/ ~ (declarative_subtyping A B).
Proof.
  intros.
  forwards~ [?|?]: decidability A B.
  left. applys~ dsub2asub.
  right. intro HF. apply dsub2asub in HF. eauto.
Qed.


#[export] Hint Extern 1 (lc_typ (t_forall _)) =>
let Y:= fresh "Y" in pick_fresh Y; instantiate_cofinites_with Y; applys lc_t_forall_exists Y : core.


Ltac inv_arrow :=
  repeat match goal with
         | H: algo_sub (t_arrow _ _) (t_arrow _ _) |- _ => forwards (?&?): algo_sub_arrow_inv H; clear H
         | H: declarative_subtyping (t_arrow _ _) (t_arrow _ _) |- _ => apply dsub2asub in H
         end.

Ltac inv_forall :=
  repeat match goal with
         | H: algo_sub (t_forall _) (t_forall _) |- _ => forwards : algo_sub_forall_inv H; clear H
         | H: declarative_subtyping (t_forall _) (t_forall _) |- _ => apply dsub2asub in H
         end.


Ltac convert2asub :=
  repeat match goal with
           H: declarative_subtyping _ _ |- _ => apply dsub2asub in H
           | |- declarative_subtyping _ _ => apply dsub2asub
         end.

Ltac convert2dsub :=
  repeat match goal with
           | H: algo_sub _ _ |- _ => apply dsub2asub in H
           | |- algo_sub _ _ => apply dsub2asub
         end.

(* Some impossible cases *)
Lemma sub_inv_1 : forall X B D,
    algo_sub (t_tvar_f X) (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_2 : forall l5 A B D,
    algo_sub (t_rcd l5 A) (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_rcd l5 A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_3 : forall B D,
    algo_sub t_top (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_4 : forall A B D,
    algo_sub (t_forall A) (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_5 : forall X B,
    algo_sub (t_tvar_f X) (t_forall B) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_6 : forall l5 A B,
    algo_sub (t_rcd l5 A) (t_forall B) -> False.
Proof.
  introv H. indTypSize (size_typ (t_rcd l5 A) + size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_7 : forall B,
    algo_sub t_top (t_forall B) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_8 : forall A B D,
    algo_sub (t_arrow B D) (t_forall A) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_9 : forall l5 A X,
    algo_sub (t_rcd l5 A) (t_tvar_f X) -> False.
Proof.
  introv H.
  indTypSize (size_typ (t_rcd l5 A)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

#[export] Hint Extern 1 False => lazymatch goal with
   | H: algo_sub (t_tvar_f _) (t_arrow _ _) |- _ => applys sub_inv_1 H
   | H: algo_sub (t_rcd _ _) (t_arrow _ _) |- _ => applys sub_inv_2 H
   | H: algo_sub t_top (t_arrow _ _) |- _ => applys sub_inv_3 H
   | H: algo_sub (t_forall _) (t_arrow _ _) |- _ => applys sub_inv_4 H
   | H: algo_sub (t_tvar_f _) (t_forall _) |- _ => applys sub_inv_5 H
   | H: algo_sub (t_rcd _ _) (t_forall _) |- _ => applys sub_inv_6 H
   | H: algo_sub t_top (t_forall _) |- _ => applys sub_inv_7 H
   | H: algo_sub (t_arrow _ _) (t_forall _) |- _ => applys sub_inv_8 H
   | H: algo_sub (t_rcd _ _) (t_tvar_f _) |- _ => applys sub_inv_9 H
                            end : FalseHd.

Lemma sub_inv_10 : forall A B D l,
    algo_sub (t_arrow B D) (t_rcd l A) -> False.
Proof.
  introv H.
  indTypSize (size_typ (t_rcd l A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.
Lemma sub_inv_11 : forall A B l,
    algo_sub (t_forall B) (t_rcd l A) -> False.
Proof.
  introv H.
  indTypSize (size_typ (t_rcd l A) + size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_12 : forall l A,
    algo_sub t_top (t_rcd l A) -> False.
Proof.
  introv H. indTypSize (size_typ (t_rcd l A)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

#[export] Hint Immediate sub_inv_10 sub_inv_11 sub_inv_12 : FalseHd.

Lemma sub_inv_13 :
    algo_sub t_top t_bot -> False.
Proof.
  introv H.
  inverts H; solve_false.
Qed.

Lemma sub_inv_14 : forall A B,
    algo_sub (t_arrow A B) t_bot -> False.
Proof.
  introv H.
  inductions H; inverts_all_spl; solve_false.
Qed.

Lemma sub_inv_15 : forall l A,
    algo_sub (t_rcd l A) t_bot -> False.
Proof.
  introv H.
  inductions H; inverts_all_spl; solve_false.
Qed.

Lemma sub_inv_16 : forall A,
    algo_sub (t_forall A) t_bot -> False.
Proof.
  introv H.
  inductions H; inverts_all_spl; solve_false.
Qed.

#[export] Hint Immediate sub_inv_13 sub_inv_14 sub_inv_15 sub_inv_16 : FalseHd.

(******** nondeterministic split & alternative subtyping definition *******)

Lemma new_splu_decrease_size: forall A B C,
    new_splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  pick fresh X. forwards* (?&?): H0.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H2.
  eauto...
Qed.

Lemma new_spli_decrease_size: forall A B C,
    new_spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  - forwards (?&?): new_splu_decrease_size H0...
  - pick fresh X. forwards* (?&?): H0.
    rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
    rewrite 2 size_typ_open_typ_wrt_typ_var in H2.
    eauto...
Qed.

Ltac new_spl_size :=
  repeat match goal with
         | [ H: new_splu _ _ _ |- _ ] =>
           ( lets (?&?): new_splu_decrease_size H; clear H)
         | [ H: new_spli _ _ _ |- _ ] =>
           ( lets (?&?): new_spli_decrease_size H; clear H)
         end.

Ltac new_elia :=
  try solve [pose proof (size_typ_min);
             let x := fresh "x" in
             pick fresh x; instantiate_cofinites_with x; (* forall x, x `notin` .. -> spli .. *)
             spl_size; new_spl_size; simpl in *; simpl;
             try repeat rewrite size_typ_open_typ_wrt_typ_var in *; (* spl A-^X ... *)
             try lia].

(******* relates to original definitions ********)

Lemma splu2nsplu : forall A B1 B2,
    splu A B1 B2 -> new_splu A B1 B2.
Proof.
  introv H. induction* H.
Qed.

Lemma spli2nspli : forall A B1 B2,
    spli A B1 B2 -> new_spli A B1 B2.
Proof.
  introv H. induction~ H.
  - apply splu2nsplu in H0. eauto.
  - econstructor. intros. instantiate_cofinites. easy.
Qed.

#[export] Hint Resolve splu2nsplu spli2nspli : core.

Notation "A <:: B" := (algo_sub A B) (at level 15).
Notation "A ~~ B" := ((algo_sub A B) /\ (algo_sub B A)) (at level 15).
Notation "A & B" := (t_and A B) (at level 10).
Notation "A | B" := (t_or A B) (at level 11).

Lemma nsplu2splu : forall A B1 B2,
    new_splu A B1 B2 ->
    exists C1 C2, splu A C1 C2.
Proof with destruct_conj; eauto.
  introv H. induction H...
  - destruct* (ordu_or_split A)...
  - pick fresh Y for (L `union` [[A]]). instantiate_cofinites. exists.
    applys splu_forall_exists Y...
Qed.

Lemma nspli2spli : forall A B1 B2,
    new_spli A B1 B2 ->
    exists C1 C2, spli A C1 C2.
Proof with destruct_conj; eauto.
  introv H. induction H...
  - destruct* (ordi_or_split A)...
  - destruct* (ordi_or_split B)...
    + apply nsplu2splu in H0...
  - pick fresh Y for (L `union` [[A]]). instantiate_cofinites. exists.
    applys spli_forall_exists Y...
Qed.

Ltac gets_all_lc :=
  repeat match goal with
         | H: ordi _ |- _ => lets: ordi_lc H; assumption
         | H: ordu _ |- _ => lets: ordi_lc H; assumption
         | H: splu _ _ _ |- _ => lets (?&?&?): splu_lc H; assumption
         | H: spli _ _ _ |- _ => lets (?&?&?): spli_lc H; assumption
         | H: algo_sub _ _ |- _ => lets (?&?): algo_sub_lc H; assumption
         end.

Lemma open_into_var : forall X Y, t_tvar_f Y -^ X = t_tvar_f Y.
Proof. eauto. Qed.

#[export] Hint Rewrite open_into_var : open.

Lemma nsplu_isomorphic : forall A B1 B2,
    new_splu A B1 B2 -> A ~~ B1|B2.
Proof with try applys ASub_refl; try match goal with |- lc_typ _ => eauto with lngen end.
  introv H. split; induction~ H.
  - split_r.
    + swap_or_r... split_r.
      swap_or_r... applys* ASub_andl. applys* ASub_andr.
    + applys* ASub_orl.
  - swap_and_l... split_r.
    + applys* ASub_orl.
    + swap_or_r... split_r. applys* ASub_andr.
      swap_or_r... applys* ASub_andl.
  - applys algo_trans; [ | applys dsub2asub; applys DSub_CovDistUAll ]...
    econstructor. intros. instantiate_cofinites.
    applys algo_trans H0. autorewrite with open.
    auto.
  - applys algo_trans; [ | applys dsub2asub; applys DSub_CovDistUIn ]...
    econstructor. easy.
  - split_l.
    + split_r.
      * use_left_l. applys algo_trans IHnew_splu. use_left_r...
      * use_right_l...
    + split_r.
      * use_left_l. applys algo_trans IHnew_splu. use_right_r...
      * use_right_l...
  - split_l.
    + split_r.
      * use_left_l...
      * applys algo_trans IHnew_splu. use_left_r... use_right_l...
    + split_r.
      * use_left_l...
      * applys algo_trans IHnew_splu. use_right_r... use_right_l...
  - applys algo_trans (t_forall (A1|A2))...
    + split_l; auto;
      applys ASub_forall; intros; instantiate_cofinites;
       autorewrite with open...
      use_left_r... use_right_r...
    + applys ASub_forall; intros; instantiate_cofinites;
        autorewrite with open... easy.
  - applys algo_trans (t_rcd l5 (A1|A2))...
    + split_l; applys ASub_rcd. use_left_r... use_right_r...
    + applys ASub_rcd. easy.
Qed.

Lemma nspli_isomorphic : forall A B1 B2,
    new_spli A B1 B2 -> A ~~ B1&B2.
Proof with eauto using ASub_refl.
  introv Hs. induction Hs.
  - split*.
  - destruct IHHs.
    split; applys algo_trans ((A1&A2)|B).
    + match_or...
    + match_and...
    + match_and...
    + match_or...
  - destruct IHHs. split.
    + applys algo_trans (A|B1&B2).
      * match_or...
      * swap_or_l... split_l.
        use_right_r. swap_and_r...
        use_right_r.
        match_and_rev...
        use_left_r. swap_and_r... use_left_r.
        split_r...
    + applys algo_trans (A|B1&B2).
      * swap_or_r...
        split_l. swap_and_l... split_l.
        use_right_r. use_left_l...
        use_right_l. use_right_r...
        swap_and_l... split_l.
        use_left_l. use_right_r...
        use_left_r. match_and_rev...
      * match_or...
  - destruct IHHs. split; applys algo_trans (t_arrow A (B1&B2)).
    + econstructor...
    + match_and...
    + split_r. eauto.
      use_left_l...
      use_right_l...
    + econstructor...
  - apply nsplu_isomorphic in H0.
    destruct H0. split; applys algo_trans (t_arrow (A1|A2) B).
    + econstructor...
    + split_r; constructor~.
    + convert2dsub. applys* DSub_FunDistI.
    + constructor~.
  - split; applys algo_trans (t_forall (A1&A2)).
    + econstructor. intros. instantiate_cofinites. autorewrite with open. easy.
    + split_r; auto; econstructor; intros; autorewrite with open. use_left_l... use_right_l...
    + convert2dsub. applys~ DSub_CovDistIAll.
    + econstructor. intros. instantiate_cofinites. autorewrite with open. easy.
  - destruct IHHs. split; applys algo_trans (t_rcd l5 (A1&A2)).
    + econstructor...
    + match_and...
    + split_r. eauto.
      use_left_l...
      use_right_l...
    + econstructor...
Qed.

Lemma asub2nsub : forall A B,
    algo_sub A B <-> new_sub A B.
Proof with new_elia; try easy.
  introv; split; intro H.
  - induction H.
    all: now eauto.
  - indTypSize (size_typ A + size_typ B). inverts H.
    1-3: eauto.
    1,3-9: repeat match goal with
                | H: new_sub _ _ |- _ => forwards~ : IH H; new_elia; clear H
                  end.
    + (* and *) applys~ algo_trans (B1&B2).
      forwards~ (?&?): nspli_isomorphic H0.
    + (* andl *) applys~ algo_trans (A1&A2).
      forwards~ (?&?): nspli_isomorphic H0.
    + (* andr *) applys~ algo_trans (A1&A2). forwards~ (?&?): nspli_isomorphic H0.
    + (* or *) applys~ algo_trans (A1|A2).
      forwards~ (?&?): nsplu_isomorphic H0.
    + (* orl *) applys~ algo_trans (B1|B2).
      forwards~ (?&?): nsplu_isomorphic H0.
    + (* orr *) applys~ algo_trans (B1|B2).
      forwards~ (?&?): nsplu_isomorphic H0.
    + applys ASub_forall (L `union` [[A0]] `union` [[B0]]). intros X Fry.
      instantiate_cofinites. applys~ IH; elia.
Qed.

(*********************** binding ********************************)

Lemma typsubst_typ_splu : forall A B C X U,
    new_splu A B C -> lc_typ U ->
    new_splu ([X ~~> U] A) ([X ~~> U] B) ([X ~~> U] C).
Proof with eauto with lngen.
  introv spl lc. induction spl; simpl.
  all: auto...
  -
    applys NSpU_forall (L `union` [[A]] `union` [[A1]] `union` [[A2]] `union` {{X}}).
    intros Y Fry. instantiate_cofinites_with Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in H0...
    rewrite (typsubst_typ_fresh_eq (t_tvar_f Y) U X) in H0...
Qed.

Lemma typsubst_typ_spli : forall A B C X U,
    new_spli A B C -> lc_typ U ->
    new_spli ([X ~~> U] A) ([X ~~> U] B) ([X ~~> U] C).
Proof with eauto using typsubst_typ_splu with lngen.
  introv spl lc. induction spl; simpl.
  1-4, 7: auto...
  - applys NSpI_arrowUnion...
  - applys NSpI_forall (L `union` [[A]] `union` [[A1]] `union` [[A2]] `union` {{X}}).
    intros Y Fry. instantiate_cofinites_with Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in H0...
    rewrite (typsubst_typ_fresh_eq (t_tvar_f Y) U X) in H0...
Qed.

Lemma typsubst_typ_new_sub : forall A B C X,
  new_sub A B -> lc_typ C ->
  new_sub ([X ~~> C] A) ([X ~~> C] B).
Proof with (simpl in *; eauto with lngen; eauto using typsubst_typ_lc_typ, typsubst_typ_spli, typsubst_typ_splu).
  introv s lc.
  indTypSize (size_typ A + size_typ B).
  inverts s; simpl.
  - applys NSub_refl...
  - applys~ NSub_top...
  - applys~ NSub_bot...
  - applys~ NSub_arrow... all: applys IH; elia...
  - applys~ NSub_forall (L `union` {{X}} `union` [[C]])...
    intros Y HF. instantiate_cofinites_with Y.
    rewrite 2 typsubst_typ_open_typ_wrt_typ_var...
    applys IH; elia...
  - applys~ NSub_rcd... applys IH; new_elia...
  - applys~ NSub_and. applys typsubst_typ_spli H...
    all: applys IH; new_elia...
  - applys~ NSub_andl. applys typsubst_typ_spli H...
    all: applys IH; new_elia...
  - applys~ NSub_andr. applys typsubst_typ_spli H...
    all: applys IH; new_elia...
  - applys~ NSub_or. applys typsubst_typ_splu H...
    all: applys IH; new_elia...
  - applys~ NSub_orl. applys typsubst_typ_splu H...
    all: applys IH; new_elia...
  - applys~ NSub_orr. applys typsubst_typ_splu H...
    all: applys IH; new_elia...
Qed.


Lemma typsubst_typ_algo_sub : forall A B C X,
  algo_sub A B -> lc_typ C ->
  algo_sub ([X ~~> C] A) ([X ~~> C] B).
Proof.
  intros.
  apply asub2nsub. apply asub2nsub in H.
  applys~ typsubst_typ_new_sub.
Qed.

Ltac solve_dsub := repeat match goal with
                          | H: declarative_subtyping _ _ |- _ => apply dsub2asub in H
                          | |- declarative_subtyping _ _ => apply dsub2asub
                          end; try solve (solve_algo_sub).

Lemma nsub_splitu : forall A B B1 B2,
    ~ declarative_subtyping B A -> splu B B1 B2 -> lc_typ A ->
    ~ declarative_subtyping B1 A \/ ~ declarative_subtyping B2 A.
Proof.
  introv HN HS HL.
  destruct (sub_dec B1 A); eauto.
  destruct (sub_dec B2 A); eauto.
  exfalso. applys HN.
  apply dsub2asub in H, H0. applys~ dsub2asub.
Qed.


(*****************************************************************************)
Definition iso A B := A <: B /\ B <: A.

Notation "A ~= B"        := (iso A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Lemma iso_subst_sub : forall A B C,
    A <: B -> A ~= C -> C <: B.
Proof.
  introv H1 (H2&H3). convert2asub. applys algo_trans; try eassumption.
Qed.

Lemma iso_lc : forall A B,
    A ~= B -> lc_typ A /\ lc_typ B.
Proof.
  introv (H1&H2). eauto.
Qed.

Ltac iso_inverts_all_lc := repeat lazymatch goal with
                             | H: _ ~= _ |- _ => forwards (?&?): iso_lc H; clear H
                             end;
                           inverts_all_lc.

Lemma iso_symm : forall A B,
    A ~= B -> B ~= A.
Proof.
  introv (H1&H2).
  split~.
Qed.

Lemma iso_refl : forall A,
    lc_typ A -> A ~= A.
Proof.
  introv H. induction H; split.
  all: applys~ DSub_Refl.
Qed.

Lemma iso_trans : forall A B C,
    A ~= B -> B ~= C -> A ~= C.
Proof. introv (?&?) (?&?).
       split; applys DSub_Trans; eassumption.
Qed.

Lemma iso_or : forall A B C,
    A ~= B -> A ~= C -> A ~= B|C.
Proof.
  introv (H1&H2) (H3&H4).
  all: split; constructor~.
Qed.
Lemma iso_or_2 : forall A B C,
    A ~= C -> B ~= C -> A|B ~= C.
Proof.
  introv H1 H2. eauto using iso_or, iso_symm.
Qed.

Lemma iso_or_match : forall A1 A2 B1 B2,
    A1 ~= B1 -> A2 ~= B2 -> A1|A2 ~= B1|B2.
Proof.
  introv (H1&H2) (H3&H4).
  all: split; convert2asub; match_or; auto.
Qed.

Lemma iso_and : forall A B C,
    A ~= B -> A ~= C -> A ~= B&C.
Proof.
  introv (H1&H2) (H3&H4).
  all: split; constructor~.
Qed.

Lemma iso_and_match : forall A1 A2 B1 B2,
    A1 ~= B1 -> A2 ~= B2 -> A1&A2 ~= B1&B2.
Proof.
  introv (H1&H2) (H3&H4).
  all: split; convert2asub; match_and; auto.
Qed.

Lemma iso_shuffle : forall A B C D,
    lc_typ A -> lc_typ B -> lc_typ C -> lc_typ D ->
    (A | B) | (C | D) ~= (A | C) | (B | D).
Proof.
  intros. split.
  - applys DSub_UnionL.
    convert2asub; match_or; applys* ASub_orl.
    convert2asub; match_or; applys* ASub_orr.
  - applys DSub_UnionL.
    convert2asub; match_or; applys* ASub_orl.
    convert2asub; match_or; applys* ASub_orr.
Qed.

Lemma iso_dist_1 : forall A B C,
    lc_typ A -> lc_typ B -> lc_typ C ->
    (A | B) & C ~= (A & C) | (B & C).
Proof.
  intros. split.
  all: convert2asub; match_or; eauto.
Qed.

Lemma iso_dist_2 : forall A B C,
    lc_typ A -> lc_typ B -> lc_typ C ->
    C & (A | B) ~= (C & A) | (C & B).
Proof with try solve [eassumption || constructor; eassumption].
  intros. split.
  - convert2asub. swap_and_l...
    match_or; swap_and_l; eauto.
  - convert2asub. swap_and_r...
    match_or; swap_and_r; eauto.
Qed.

Lemma iso_absorb_1 : forall A B,
    lc_typ A -> lc_typ B -> A ~= A | A & B.
Proof.
  introv HA HB. splits.
  - applys* DSub_UnionRL.
  - applys* DSub_UnionL.
Qed.

Lemma iso_absorb_2 : forall A B,
    lc_typ A -> lc_typ B -> A ~= A & B | A.
Proof.
  introv HA HB. splits.
  - applys* DSub_UnionRR.
  - applys* DSub_UnionL.
Qed.

Lemma iso_absorb_3 : forall A B,
    lc_typ A -> lc_typ B -> A ~= A | B & A.
Proof.
  introv HA HB. splits.
  - applys* DSub_UnionRL.
  - applys* DSub_UnionL.
Qed.

Lemma iso_absorb_4 : forall A B,
    lc_typ A -> lc_typ B -> A ~= B & A | A.
Proof.
  introv HA HB. splits.
  - applys* DSub_UnionRR.
  - applys* DSub_UnionL.
Qed.

Lemma iso_dup_1 : forall A B C,
    A ~= B -> A ~= C -> A ~= B | C.
Proof.
  introv (?&?) (?&?). splits.
  - applys~ DSub_UnionRL.
  - applys* DSub_UnionL.
Qed.

#[export] Hint Resolve iso_refl : core.

#[export] Hint Immediate iso_symm iso_trans iso_or iso_or_2 iso_and
  iso_or_match iso_and_match : core.

Lemma iso_asub2dsub : forall A B,
    A ~~ B <-> A ~= B.
Proof.
  split; intros (H1&H2); split; convert2dsub; easy.
Qed.

Lemma new_splu_iso : forall A B C,
    new_splu A B C -> A ~= B | C.
Proof.
  introv H. applys iso_asub2dsub.
  applys* nsplu_isomorphic.
Qed.

Lemma splu_iso : forall A B C,
    splu A B C -> A ~= B | C.
Proof.
  introv H. applys* new_splu_iso.
Qed.

#[export] Hint Resolve new_splu_iso splu_iso : core.
