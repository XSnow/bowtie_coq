Set Warnings "-non-recursive,-deprecated-hint-without-locality,-deprecated,-fragile-hint-constr".

Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Definitions.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme l_ind' := Induction for l Sort Prop.

Definition l_mutind :=
  fun H1 H2 H3 H4 =>
  l_ind' H1 H2 H3 H4.

Scheme l_rec' := Induction for l Sort Set.

Definition l_mutrec :=
  fun H1 H2 H3 H4 =>
  l_rec' H1 H2 H3 H4.

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme Fty_ind' := Induction for Fty Sort Prop.

Definition Fty_mutind :=
  fun H1 H2 H3 =>
  Fty_ind' H1 H2 H3.

Scheme Fty_rec' := Induction for Fty Sort Set.

Definition Fty_mutrec :=
  fun H1 H2 H3 =>
  Fty_rec' H1 H2 H3.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : typevar) (A1 : typ) {struct A1} : typ :=
  match A1 with
    | t_tvar_f X2 => if (X1 == X2) then (t_tvar_b n1) else (t_tvar_f X2)
    | t_tvar_b n2 => if (lt_ge_dec n2 n1) then (t_tvar_b n2) else (t_tvar_b (S n2))
    | t_rcd l1 A2 => t_rcd l1 (close_typ_wrt_typ_rec n1 X1 A2)
    | t_and A2 A3 => t_and (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 A3)
    | t_or A2 A3 => t_or (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 A3)
    | t_arrow A2 B1 => t_arrow (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 B1)
    | t_forall B1 => t_forall (close_typ_wrt_typ_rec (S n1) X1 B1)
    | t_top => t_top
    | t_bot => t_bot
  end.

Definition close_typ_wrt_typ X1 A1 := close_typ_wrt_typ_rec 0 X1 A1.

Fixpoint close_Fty_wrt_typ_rec (n1 : nat) (X1 : typevar) (Fty1 : Fty) {struct Fty1} : Fty :=
  match Fty1 with
    | fty_StackArg A1 => fty_StackArg (close_typ_wrt_typ_rec n1 X1 A1)
    | fty_StackTyArg A1 => fty_StackTyArg (close_typ_wrt_typ_rec n1 X1 A1)
  end.

Definition close_Fty_wrt_typ X1 Fty1 := close_Fty_wrt_typ_rec 0 X1 Fty1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_l (l1 : l) {struct l1} : nat :=
  match l1 with
    | lbl_TagIndex i1 => 1
    | lbl_TagLeft => 1
    | lbl_TagRight => 1
  end.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_tvar_f X1 => 1
    | t_tvar_b n1 => 1
    | t_rcd l1 A2 => 1 + (size_l l1) + (size_typ A2)
    | t_and A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | t_or A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_forall B1 => 1 + (size_typ B1)
    | t_top => 1
    | t_bot => 1
  end.

Fixpoint size_Fty (Fty1 : Fty) {struct Fty1} : nat :=
  match Fty1 with
    | fty_StackArg A1 => 1 + (size_typ A1)
    | fty_StackTyArg A1 => 1 + (size_typ A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_t_tvar_f : forall n1 X1,
    degree_typ_wrt_typ n1 (t_tvar_f X1)
  | degree_wrt_typ_t_tvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (t_tvar_b n2)
  | degree_wrt_typ_t_rcd : forall n1 l1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 (t_rcd l1 A1)
  | degree_wrt_typ_t_and : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (t_and A1 A2)
  | degree_wrt_typ_t_or : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (t_or A1 A2)
  | degree_wrt_typ_t_arrow : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_arrow A1 B1)
  | degree_wrt_typ_t_forall : forall n1 B1,
    degree_typ_wrt_typ (S n1) B1 ->
    degree_typ_wrt_typ n1 (t_forall B1)
  | degree_wrt_typ_t_top : forall n1,
    degree_typ_wrt_typ n1 (t_top)
  | degree_wrt_typ_t_bot : forall n1,
    degree_typ_wrt_typ n1 (t_bot).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Definition degree_typ_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_typ_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_Fty_wrt_typ : nat -> Fty -> Prop :=
  | degree_wrt_typ_fty_StackArg : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_Fty_wrt_typ n1 (fty_StackArg A1)
  | degree_wrt_typ_fty_StackTyArg : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_Fty_wrt_typ n1 (fty_StackTyArg A1).

Scheme degree_Fty_wrt_typ_ind' := Induction for degree_Fty_wrt_typ Sort Prop.

Definition degree_Fty_wrt_typ_mutind :=
  fun H1 H2 H3 =>
  degree_Fty_wrt_typ_ind' H1 H2 H3.

Hint Constructors degree_Fty_wrt_typ : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_t_tvar_f : forall X1,
    lc_set_typ (t_tvar_f X1)
  | lc_set_t_rcd : forall l1 A1,
    lc_set_typ A1 ->
    lc_set_typ (t_rcd l1 A1)
  | lc_set_t_and : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (t_and A1 A2)
  | lc_set_t_or : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (t_or A1 A2)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_arrow A1 B1)
  | lc_set_t_forall : forall B1,
    (forall X1 : typevar, lc_set_typ (open_typ_wrt_typ B1 (t_tvar_f X1))) ->
    lc_set_typ (t_forall B1)
  | lc_set_t_top :
    lc_set_typ (t_top)
  | lc_set_t_bot :
    lc_set_typ (t_bot).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Definition lc_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Definition lc_set_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Definition lc_set_typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors lc_typ : core lngen.

Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_Fty : Fty -> Set :=
  | lc_set_fty_StackArg : forall A1,
    lc_set_typ A1 ->
    lc_set_Fty (fty_StackArg A1)
  | lc_set_fty_StackTyArg : forall A1,
    lc_set_typ A1 ->
    lc_set_Fty (fty_StackTyArg A1).

Scheme lc_Fty_ind' := Induction for lc_Fty Sort Prop.

Definition lc_Fty_mutind :=
  fun H1 H2 H3 =>
  lc_Fty_ind' H1 H2 H3.

Scheme lc_set_Fty_ind' := Induction for lc_set_Fty Sort Prop.

Definition lc_set_Fty_mutind :=
  fun H1 H2 H3 =>
  lc_set_Fty_ind' H1 H2 H3.

Scheme lc_set_Fty_rec' := Induction for lc_set_Fty Sort Set.

Definition lc_set_Fty_mutrec :=
  fun H1 H2 H3 =>
  lc_set_Fty_rec' H1 H2 H3.

Hint Constructors lc_Fty : core lngen.

Hint Constructors lc_set_Fty : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (t_tvar_f X1)).

Hint Unfold body_typ_wrt_typ : core.

Definition body_Fty_wrt_typ Fty1 := forall X1, lc_Fty (open_Fty_wrt_typ Fty1 (t_tvar_f X1)).

Hint Unfold body_Fty_wrt_typ : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_l_min_mutual :
(forall l1, 1 <= size_l l1).
Proof.
apply_mutual_ind l_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_l_min :
forall l1, 1 <= size_l l1.
Proof.
pose proof size_l_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_l_min : lngen.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_Fty_min_mutual :
(forall Fty1, 1 <= size_Fty Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Fty_min :
forall Fty1, 1 <= size_Fty Fty1.
Proof.
pose proof size_Fty_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Fty_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Fty_close_Fty_wrt_typ_rec_mutual :
(forall Fty1 X1 n1,
  size_Fty (close_Fty_wrt_typ_rec n1 X1 Fty1) = size_Fty Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Fty_close_Fty_wrt_typ_rec :
forall Fty1 X1 n1,
  size_Fty (close_Fty_wrt_typ_rec n1 X1 Fty1) = size_Fty Fty1.
Proof.
pose proof size_Fty_close_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Fty_close_Fty_wrt_typ_rec : lngen.
Hint Rewrite size_Fty_close_Fty_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_Fty_close_Fty_wrt_typ :
forall Fty1 X1,
  size_Fty (close_Fty_wrt_typ X1 Fty1) = size_Fty Fty1.
Proof.
unfold close_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve size_Fty_close_Fty_wrt_typ : lngen.
Hint Rewrite size_Fty_close_Fty_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Fty_open_Fty_wrt_typ_rec_mutual :
(forall Fty1 A1 n1,
  size_Fty Fty1 <= size_Fty (open_Fty_wrt_typ_rec n1 A1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Fty_open_Fty_wrt_typ_rec :
forall Fty1 A1 n1,
  size_Fty Fty1 <= size_Fty (open_Fty_wrt_typ_rec n1 A1 Fty1).
Proof.
pose proof size_Fty_open_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Fty_open_Fty_wrt_typ_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_Fty_open_Fty_wrt_typ :
forall Fty1 A1,
  size_Fty Fty1 <= size_Fty (open_Fty_wrt_typ Fty1 A1).
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve size_Fty_open_Fty_wrt_typ : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Fty_open_Fty_wrt_typ_rec_var_mutual :
(forall Fty1 X1 n1,
  size_Fty (open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1) = size_Fty Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Fty_open_Fty_wrt_typ_rec_var :
forall Fty1 X1 n1,
  size_Fty (open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1) = size_Fty Fty1.
Proof.
pose proof size_Fty_open_Fty_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Fty_open_Fty_wrt_typ_rec_var : lngen.
Hint Rewrite size_Fty_open_Fty_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (t_tvar_f X1)) = size_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_Fty_open_Fty_wrt_typ_var :
forall Fty1 X1,
  size_Fty (open_Fty_wrt_typ Fty1 (t_tvar_f X1)) = size_Fty Fty1.
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve size_Fty_open_Fty_wrt_typ_var : lngen.
Hint Rewrite size_Fty_open_Fty_wrt_typ_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_Fty_wrt_typ_S_mutual :
(forall n1 Fty1,
  degree_Fty_wrt_typ n1 Fty1 ->
  degree_Fty_wrt_typ (S n1) Fty1).
Proof.
apply_mutual_ind degree_Fty_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Fty_wrt_typ_S :
forall n1 Fty1,
  degree_Fty_wrt_typ n1 Fty1 ->
  degree_Fty_wrt_typ (S n1) Fty1.
Proof.
pose proof degree_Fty_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Fty_wrt_typ_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_Fty_wrt_typ_O :
forall n1 Fty1,
  degree_Fty_wrt_typ O Fty1 ->
  degree_Fty_wrt_typ n1 Fty1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_Fty_wrt_typ_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_close_Fty_wrt_typ_rec_mutual :
(forall Fty1 X1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  degree_Fty_wrt_typ (S n1) (close_Fty_wrt_typ_rec n1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_close_Fty_wrt_typ_rec :
forall Fty1 X1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  degree_Fty_wrt_typ (S n1) (close_Fty_wrt_typ_rec n1 X1 Fty1).
Proof.
pose proof degree_Fty_wrt_typ_close_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Fty_wrt_typ_close_Fty_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_Fty_wrt_typ_close_Fty_wrt_typ :
forall Fty1 X1,
  degree_Fty_wrt_typ 0 Fty1 ->
  degree_Fty_wrt_typ 1 (close_Fty_wrt_typ X1 Fty1).
Proof.
unfold close_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve degree_Fty_wrt_typ_close_Fty_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_close_Fty_wrt_typ_rec_inv_mutual :
(forall Fty1 X1 n1,
  degree_Fty_wrt_typ (S n1) (close_Fty_wrt_typ_rec n1 X1 Fty1) ->
  degree_Fty_wrt_typ n1 Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_close_Fty_wrt_typ_rec_inv :
forall Fty1 X1 n1,
  degree_Fty_wrt_typ (S n1) (close_Fty_wrt_typ_rec n1 X1 Fty1) ->
  degree_Fty_wrt_typ n1 Fty1.
Proof.
pose proof degree_Fty_wrt_typ_close_Fty_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_Fty_wrt_typ_close_Fty_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_Fty_wrt_typ_close_Fty_wrt_typ_inv :
forall Fty1 X1,
  degree_Fty_wrt_typ 1 (close_Fty_wrt_typ X1 Fty1) ->
  degree_Fty_wrt_typ 0 Fty1.
Proof.
unfold close_Fty_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_Fty_wrt_typ_close_Fty_wrt_typ_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_open_Fty_wrt_typ_rec_mutual :
(forall Fty1 A1 n1,
  degree_Fty_wrt_typ (S n1) Fty1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_Fty_wrt_typ n1 (open_Fty_wrt_typ_rec n1 A1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_open_Fty_wrt_typ_rec :
forall Fty1 A1 n1,
  degree_Fty_wrt_typ (S n1) Fty1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_Fty_wrt_typ n1 (open_Fty_wrt_typ_rec n1 A1 Fty1).
Proof.
pose proof degree_Fty_wrt_typ_open_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Fty_wrt_typ_open_Fty_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_Fty_wrt_typ_open_Fty_wrt_typ :
forall Fty1 A1,
  degree_Fty_wrt_typ 1 Fty1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_Fty_wrt_typ 0 (open_Fty_wrt_typ Fty1 A1).
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve degree_Fty_wrt_typ_open_Fty_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_open_Fty_wrt_typ_rec_inv_mutual :
(forall Fty1 A1 n1,
  degree_Fty_wrt_typ n1 (open_Fty_wrt_typ_rec n1 A1 Fty1) ->
  degree_Fty_wrt_typ (S n1) Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Fty_wrt_typ_open_Fty_wrt_typ_rec_inv :
forall Fty1 A1 n1,
  degree_Fty_wrt_typ n1 (open_Fty_wrt_typ_rec n1 A1 Fty1) ->
  degree_Fty_wrt_typ (S n1) Fty1.
Proof.
pose proof degree_Fty_wrt_typ_open_Fty_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_Fty_wrt_typ_open_Fty_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_Fty_wrt_typ_open_Fty_wrt_typ_inv :
forall Fty1 A1,
  degree_Fty_wrt_typ 0 (open_Fty_wrt_typ Fty1 A1) ->
  degree_Fty_wrt_typ 1 Fty1.
Proof.
unfold open_Fty_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_Fty_wrt_typ_open_Fty_wrt_typ_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Fty_wrt_typ_rec_inj_mutual :
(forall Fty1 Fty2 X1 n1,
  close_Fty_wrt_typ_rec n1 X1 Fty1 = close_Fty_wrt_typ_rec n1 X1 Fty2 ->
  Fty1 = Fty2).
Proof.
apply_mutual_ind Fty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Fty_wrt_typ_rec_inj :
forall Fty1 Fty2 X1 n1,
  close_Fty_wrt_typ_rec n1 X1 Fty1 = close_Fty_wrt_typ_rec n1 X1 Fty2 ->
  Fty1 = Fty2.
Proof.
pose proof close_Fty_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_Fty_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_Fty_wrt_typ_inj :
forall Fty1 Fty2 X1,
  close_Fty_wrt_typ X1 Fty1 = close_Fty_wrt_typ X1 Fty2 ->
  Fty1 = Fty2.
Proof.
unfold close_Fty_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_Fty_wrt_typ_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec_mutual :
(forall Fty1 X1 n1,
  X1 `notin` typefv_Fty Fty1 ->
  close_Fty_wrt_typ_rec n1 X1 (open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1) = Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec :
forall Fty1 X1 n1,
  X1 `notin` typefv_Fty Fty1 ->
  close_Fty_wrt_typ_rec n1 X1 (open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1) = Fty1.
Proof.
pose proof close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec : lngen.
Hint Rewrite close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (t_tvar_f X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_Fty_wrt_typ_open_Fty_wrt_typ :
forall Fty1 X1,
  X1 `notin` typefv_Fty Fty1 ->
  close_Fty_wrt_typ X1 (open_Fty_wrt_typ Fty1 (t_tvar_f X1)) = Fty1.
Proof.
unfold close_Fty_wrt_typ; unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve close_Fty_wrt_typ_open_Fty_wrt_typ : lngen.
Hint Rewrite close_Fty_wrt_typ_open_Fty_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Fty_wrt_typ_rec_close_Fty_wrt_typ_rec_mutual :
(forall Fty1 X1 n1,
  open_Fty_wrt_typ_rec n1 (t_tvar_f X1) (close_Fty_wrt_typ_rec n1 X1 Fty1) = Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Fty_wrt_typ_rec_close_Fty_wrt_typ_rec :
forall Fty1 X1 n1,
  open_Fty_wrt_typ_rec n1 (t_tvar_f X1) (close_Fty_wrt_typ_rec n1 X1 Fty1) = Fty1.
Proof.
pose proof open_Fty_wrt_typ_rec_close_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_Fty_wrt_typ_rec_close_Fty_wrt_typ_rec : lngen.
Hint Rewrite open_Fty_wrt_typ_rec_close_Fty_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (t_tvar_f X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_Fty_wrt_typ_close_Fty_wrt_typ :
forall Fty1 X1,
  open_Fty_wrt_typ (close_Fty_wrt_typ X1 Fty1) (t_tvar_f X1) = Fty1.
Proof.
unfold close_Fty_wrt_typ; unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve open_Fty_wrt_typ_close_Fty_wrt_typ : lngen.
Hint Rewrite open_Fty_wrt_typ_close_Fty_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) A2 = open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 (t_tvar_f X1) A2 = open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Fty_wrt_typ_rec_inj_mutual :
(forall Fty2 Fty1 X1 n1,
  X1 `notin` typefv_Fty Fty2 ->
  X1 `notin` typefv_Fty Fty1 ->
  open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty2 = open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1 ->
  Fty2 = Fty1).
Proof.
apply_mutual_ind Fty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Fty_wrt_typ_rec_inj :
forall Fty2 Fty1 X1 n1,
  X1 `notin` typefv_Fty Fty2 ->
  X1 `notin` typefv_Fty Fty1 ->
  open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty2 = open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1 ->
  Fty2 = Fty1.
Proof.
pose proof open_Fty_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_Fty_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ A2 (t_tvar_f X1) = open_typ_wrt_typ A1 (t_tvar_f X1) ->
  A2 = A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_Fty_wrt_typ_inj :
forall Fty2 Fty1 X1,
  X1 `notin` typefv_Fty Fty2 ->
  X1 `notin` typefv_Fty Fty1 ->
  open_Fty_wrt_typ Fty2 (t_tvar_f X1) = open_Fty_wrt_typ Fty1 (t_tvar_f X1) ->
  Fty2 = Fty1.
Proof.
unfold open_Fty_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_Fty_wrt_typ_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_Fty_wrt_typ_of_lc_Fty_mutual :
(forall Fty1,
  lc_Fty Fty1 ->
  degree_Fty_wrt_typ 0 Fty1).
Proof.
apply_mutual_ind lc_Fty_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Fty_wrt_typ_of_lc_Fty :
forall Fty1,
  lc_Fty Fty1 ->
  degree_Fty_wrt_typ 0 Fty1.
Proof.
pose proof degree_Fty_wrt_typ_of_lc_Fty_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Fty_wrt_typ_of_lc_Fty : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_Fty_of_degree_size_mutual :
forall i1,
(forall Fty1,
  size_Fty Fty1 = i1 ->
  degree_Fty_wrt_typ 0 Fty1 ->
  lc_Fty Fty1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Fty_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_Fty_of_degree :
forall Fty1,
  degree_Fty_wrt_typ 0 Fty1 ->
  lc_Fty Fty1.
Proof.
intros Fty1; intros;
pose proof (lc_Fty_of_degree_size_mutual (size_Fty Fty1));
intuition eauto.
Qed.

Hint Resolve lc_Fty_of_degree : lngen.

Ltac l_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac Fty_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Fty_wrt_typ_of_lc_Fty in J1; clear H
          end).

Lemma lc_t_forall_exists :
forall X1 B1,
  lc_typ (open_typ_wrt_typ B1 (t_tvar_f X1)) ->
  lc_typ (t_forall B1).
Proof.
intros; typ_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_typ (t_forall _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_t_forall_exists X1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_Fty_wrt_typ :
forall Fty1 A1,
  body_Fty_wrt_typ Fty1 ->
  lc_typ A1 ->
  lc_Fty (open_Fty_wrt_typ Fty1 A1).
Proof.
unfold body_Fty_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
Fty_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_Fty_wrt_typ : lngen.

Lemma lc_body_t_forall_1 :
forall B1,
  lc_typ (t_forall B1) ->
  body_typ_wrt_typ B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_t_forall_1 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_Fty_unique_mutual :
(forall Fty1 (proof2 proof3 : lc_Fty Fty1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Fty_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Fty_unique :
forall Fty1 (proof2 proof3 : lc_Fty Fty1), proof2 = proof3.
Proof.
pose proof lc_Fty_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_Fty_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_Fty_of_lc_set_Fty_mutual :
(forall Fty1, lc_set_Fty Fty1 -> lc_Fty Fty1).
Proof.
apply_mutual_ind lc_set_Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Fty_of_lc_set_Fty :
forall Fty1, lc_set_Fty Fty1 -> lc_Fty Fty1.
Proof.
pose proof lc_Fty_of_lc_set_Fty_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_Fty_of_lc_set_Fty : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_l_of_lc_l];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_Fty_of_lc_Fty_size_mutual :
forall i1,
(forall Fty1,
  size_Fty Fty1 = i1 ->
  lc_Fty Fty1 ->
  lc_set_Fty Fty1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Fty_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_Fty_of_lc_Fty
 | apply lc_set_l_of_lc_l];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_Fty_of_lc_Fty :
forall Fty1,
  lc_Fty Fty1 ->
  lc_set_Fty Fty1.
Proof.
intros Fty1; intros;
pose proof (lc_set_Fty_of_lc_Fty_size_mutual (size_Fty Fty1));
intuition eauto.
Qed.

Hint Resolve lc_set_Fty_of_lc_Fty : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Fty_wrt_typ_rec_degree_Fty_wrt_typ_mutual :
(forall Fty1 X1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  X1 `notin` typefv_Fty Fty1 ->
  close_Fty_wrt_typ_rec n1 X1 Fty1 = Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Fty_wrt_typ_rec_degree_Fty_wrt_typ :
forall Fty1 X1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  X1 `notin` typefv_Fty Fty1 ->
  close_Fty_wrt_typ_rec n1 X1 Fty1 = Fty1.
Proof.
pose proof close_Fty_wrt_typ_rec_degree_Fty_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_Fty_wrt_typ_rec_degree_Fty_wrt_typ : lngen.
Hint Rewrite close_Fty_wrt_typ_rec_degree_Fty_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_Fty_wrt_typ_lc_Fty :
forall Fty1 X1,
  lc_Fty Fty1 ->
  X1 `notin` typefv_Fty Fty1 ->
  close_Fty_wrt_typ X1 Fty1 = Fty1.
Proof.
unfold close_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve close_Fty_wrt_typ_lc_Fty : lngen.
Hint Rewrite close_Fty_wrt_typ_lc_Fty using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Fty_wrt_typ_rec_degree_Fty_wrt_typ_mutual :
(forall Fty1 A1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  open_Fty_wrt_typ_rec n1 A1 Fty1 = Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Fty_wrt_typ_rec_degree_Fty_wrt_typ :
forall Fty1 A1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  open_Fty_wrt_typ_rec n1 A1 Fty1 = Fty1.
Proof.
pose proof open_Fty_wrt_typ_rec_degree_Fty_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_Fty_wrt_typ_rec_degree_Fty_wrt_typ : lngen.
Hint Rewrite open_Fty_wrt_typ_rec_degree_Fty_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_Fty_wrt_typ_lc_Fty :
forall Fty1 A1,
  lc_Fty Fty1 ->
  open_Fty_wrt_typ Fty1 A1 = Fty1.
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve open_Fty_wrt_typ_lc_Fty : lngen.
Hint Rewrite open_Fty_wrt_typ_lc_Fty using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typefv_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  typefv_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (typefv_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  typefv_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (typefv_typ A1).
Proof.
pose proof typefv_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite typefv_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_Fty_close_Fty_wrt_typ_rec_mutual :
(forall Fty1 X1 n1,
  typefv_Fty (close_Fty_wrt_typ_rec n1 X1 Fty1) [=] remove X1 (typefv_Fty Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_Fty_close_Fty_wrt_typ_rec :
forall Fty1 X1 n1,
  typefv_Fty (close_Fty_wrt_typ_rec n1 X1 Fty1) [=] remove X1 (typefv_Fty Fty1).
Proof.
pose proof typefv_Fty_close_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_close_Fty_wrt_typ_rec : lngen.
Hint Rewrite typefv_Fty_close_Fty_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma typefv_typ_close_typ_wrt_typ :
forall A1 X1,
  typefv_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (typefv_typ A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_typ_close_typ_wrt_typ : lngen.
Hint Rewrite typefv_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma typefv_Fty_close_Fty_wrt_typ :
forall Fty1 X1,
  typefv_Fty (close_Fty_wrt_typ X1 Fty1) [=] remove X1 (typefv_Fty Fty1).
Proof.
unfold close_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_Fty_close_Fty_wrt_typ : lngen.
Hint Rewrite typefv_Fty_close_Fty_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof typefv_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_Fty_open_Fty_wrt_typ_rec_lower_mutual :
(forall Fty1 A1 n1,
  typefv_Fty Fty1 [<=] typefv_Fty (open_Fty_wrt_typ_rec n1 A1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_Fty_open_Fty_wrt_typ_rec_lower :
forall Fty1 A1 n1,
  typefv_Fty Fty1 [<=] typefv_Fty (open_Fty_wrt_typ_rec n1 A1 Fty1).
Proof.
pose proof typefv_Fty_open_Fty_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_open_Fty_wrt_typ_rec_lower : lngen.

(* end hide *)

Lemma typefv_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_lower : lngen.

Lemma typefv_Fty_open_Fty_wrt_typ_lower :
forall Fty1 A1,
  typefv_Fty Fty1 [<=] typefv_Fty (open_Fty_wrt_typ Fty1 A1).
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_Fty_open_Fty_wrt_typ_lower : lngen.

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  typefv_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] typefv_typ A2 `union` typefv_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  typefv_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] typefv_typ A2 `union` typefv_typ A1.
Proof.
pose proof typefv_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_Fty_open_Fty_wrt_typ_rec_upper_mutual :
(forall Fty1 A1 n1,
  typefv_Fty (open_Fty_wrt_typ_rec n1 A1 Fty1) [<=] typefv_typ A1 `union` typefv_Fty Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_Fty_open_Fty_wrt_typ_rec_upper :
forall Fty1 A1 n1,
  typefv_Fty (open_Fty_wrt_typ_rec n1 A1 Fty1) [<=] typefv_typ A1 `union` typefv_Fty Fty1.
Proof.
pose proof typefv_Fty_open_Fty_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_open_Fty_wrt_typ_rec_upper : lngen.

(* end hide *)

Lemma typefv_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  typefv_typ (open_typ_wrt_typ A1 A2) [<=] typefv_typ A2 `union` typefv_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_typ_open_typ_wrt_typ_upper : lngen.

Lemma typefv_Fty_open_Fty_wrt_typ_upper :
forall Fty1 A1,
  typefv_Fty (open_Fty_wrt_typ Fty1 A1) [<=] typefv_typ A1 `union` typefv_Fty Fty1.
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typefv_Fty_open_Fty_wrt_typ_upper : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` typefv_typ A1 ->
  typefv_typ (typsubst_typ A2 X1 A1) [=] typefv_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_fresh :
forall A1 A2 X1,
  X1 `notin` typefv_typ A1 ->
  typefv_typ (typsubst_typ A2 X1 A1) [=] typefv_typ A1.
Proof.
pose proof typefv_typ_typsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_fresh : lngen.
Hint Rewrite typefv_typ_typsubst_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_Fty_typsubst_Fty_fresh_mutual :
(forall Fty1 A1 X1,
  X1 `notin` typefv_Fty Fty1 ->
  typefv_Fty (typsubst_Fty A1 X1 Fty1) [=] typefv_Fty Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Fty_typsubst_Fty_fresh :
forall Fty1 A1 X1,
  X1 `notin` typefv_Fty Fty1 ->
  typefv_Fty (typsubst_Fty A1 X1 Fty1) [=] typefv_Fty Fty1.
Proof.
pose proof typefv_Fty_typsubst_Fty_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_typsubst_Fty_fresh : lngen.
Hint Rewrite typefv_Fty_typsubst_Fty_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (typefv_typ A1) [<=] typefv_typ (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_lower :
forall A1 A2 X1,
  remove X1 (typefv_typ A1) [<=] typefv_typ (typsubst_typ A2 X1 A1).
Proof.
pose proof typefv_typ_typsubst_typ_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_lower : lngen.

(* begin hide *)

Lemma typefv_Fty_typsubst_Fty_lower_mutual :
(forall Fty1 A1 X1,
  remove X1 (typefv_Fty Fty1) [<=] typefv_Fty (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Fty_typsubst_Fty_lower :
forall Fty1 A1 X1,
  remove X1 (typefv_Fty Fty1) [<=] typefv_Fty (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typefv_Fty_typsubst_Fty_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_typsubst_Fty_lower : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ (typsubst_typ A2 X1 A1).
Proof.
pose proof typefv_typ_typsubst_typ_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_notin : lngen.

(* begin hide *)

Lemma typefv_Fty_typsubst_Fty_notin_mutual :
(forall Fty1 A1 X1 X2,
  X2 `notin` typefv_Fty Fty1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_Fty (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Fty_typsubst_Fty_notin :
forall Fty1 A1 X1 X2,
  X2 `notin` typefv_Fty Fty1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_Fty (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typefv_Fty_typsubst_Fty_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_typsubst_Fty_notin : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_upper_mutual :
(forall A1 A2 X1,
  typefv_typ (typsubst_typ A2 X1 A1) [<=] typefv_typ A2 `union` remove X1 (typefv_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_typ_typsubst_typ_upper :
forall A1 A2 X1,
  typefv_typ (typsubst_typ A2 X1 A1) [<=] typefv_typ A2 `union` remove X1 (typefv_typ A1).
Proof.
pose proof typefv_typ_typsubst_typ_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_typ_typsubst_typ_upper : lngen.

(* begin hide *)

Lemma typefv_Fty_typsubst_Fty_upper_mutual :
(forall Fty1 A1 X1,
  typefv_Fty (typsubst_Fty A1 X1 Fty1) [<=] typefv_typ A1 `union` remove X1 (typefv_Fty Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Fty_typsubst_Fty_upper :
forall Fty1 A1 X1,
  typefv_Fty (typsubst_Fty A1 X1 Fty1) [<=] typefv_typ A1 `union` remove X1 (typefv_Fty Fty1).
Proof.
pose proof typefv_Fty_typsubst_Fty_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Fty_typsubst_Fty_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 A2).
Proof.
pose proof typsubst_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma typsubst_Fty_close_Fty_wrt_typ_rec_mutual :
(forall Fty1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_Fty A1 X1 (close_Fty_wrt_typ_rec n1 X2 Fty1) = close_Fty_wrt_typ_rec n1 X2 (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_close_Fty_wrt_typ_rec :
forall Fty1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_Fty A1 X1 (close_Fty_wrt_typ_rec n1 X2 Fty1) = close_Fty_wrt_typ_rec n1 X2 (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typsubst_Fty_close_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_close_Fty_wrt_typ_rec : lngen.

Lemma typsubst_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (typsubst_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ : lngen.

Lemma typsubst_Fty_close_Fty_wrt_typ :
forall Fty1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_Fty A1 X1 (close_Fty_wrt_typ X2 Fty1) = close_Fty_wrt_typ X2 (typsubst_Fty A1 X1 Fty1).
Proof.
unfold close_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_Fty_close_Fty_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (typsubst_typ A2 X1 A1).
Proof.
pose proof typsubst_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_Fty_degree_Fty_wrt_typ_mutual :
(forall Fty1 A1 X1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_Fty_wrt_typ n1 (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_degree_Fty_wrt_typ :
forall Fty1 A1 X1 n1,
  degree_Fty_wrt_typ n1 Fty1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_Fty_wrt_typ n1 (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typsubst_Fty_degree_Fty_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_degree_Fty_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  typsubst_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  typsubst_typ A1 X1 A2 = A2.
Proof.
pose proof typsubst_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_fresh_eq : lngen.
Hint Rewrite typsubst_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_Fty_fresh_eq_mutual :
(forall Fty1 A1 X1,
  X1 `notin` typefv_Fty Fty1 ->
  typsubst_Fty A1 X1 Fty1 = Fty1).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_fresh_eq :
forall Fty1 A1 X1,
  X1 `notin` typefv_Fty Fty1 ->
  typsubst_Fty A1 X1 Fty1 = Fty1.
Proof.
pose proof typsubst_Fty_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_fresh_eq : lngen.
Hint Rewrite typsubst_Fty_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X1 A2).
Proof.
pose proof typsubst_typ_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_Fty_fresh_same_mutual :
(forall Fty1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_Fty (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_fresh_same :
forall Fty1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_Fty (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typsubst_Fty_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X2 A2).
Proof.
pose proof typsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_fresh : lngen.

(* begin hide *)

Lemma typsubst_Fty_fresh_mutual :
(forall Fty1 A1 X1 X2,
  X1 `notin` typefv_Fty Fty1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_Fty (typsubst_Fty A1 X2 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_fresh :
forall Fty1 A1 X1 X2,
  X1 `notin` typefv_Fty Fty1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_Fty (typsubst_Fty A1 X2 Fty1).
Proof.
pose proof typsubst_Fty_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_fresh : lngen.

Lemma typsubst_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (typsubst_typ A2 X1 A1).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_typ_lc_typ : lngen.

Lemma typsubst_Fty_lc_Fty :
forall Fty1 A1 X1,
  lc_Fty Fty1 ->
  lc_typ A1 ->
  lc_Fty (typsubst_Fty A1 X1 Fty1).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_Fty_lc_Fty : lngen.

(* begin hide *)

Lemma typsubst_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_typ A1 X1 A3).
Proof.
pose proof typsubst_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_Fty_open_Fty_wrt_typ_rec_mutual :
(forall Fty1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_Fty A1 X1 (open_Fty_wrt_typ_rec n1 A2 Fty1) = open_Fty_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_Fty_open_Fty_wrt_typ_rec :
forall Fty1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_Fty A1 X1 (open_Fty_wrt_typ_rec n1 A2 Fty1) = open_Fty_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typsubst_Fty_open_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_open_Fty_wrt_typ_rec : lngen.

(* end hide *)

Lemma typsubst_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (typsubst_typ A1 X1 A3) (typsubst_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_open_typ_wrt_typ : lngen.

Lemma typsubst_Fty_open_Fty_wrt_typ :
forall Fty1 A1 A2 X1,
  lc_typ A1 ->
  typsubst_Fty A1 X1 (open_Fty_wrt_typ Fty1 A2) = open_Fty_wrt_typ (typsubst_Fty A1 X1 Fty1) (typsubst_typ A1 X1 A2).
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_Fty_open_Fty_wrt_typ : lngen.

Lemma typsubst_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (typsubst_typ A1 X1 A2) (t_tvar_f X2) = typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_tvar_f X2)).
Proof.
intros; rewrite typsubst_typ_open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_open_typ_wrt_typ_var : lngen.

Lemma typsubst_Fty_open_Fty_wrt_typ_var :
forall Fty1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_Fty_wrt_typ (typsubst_Fty A1 X1 Fty1) (t_tvar_f X2) = typsubst_Fty A1 X1 (open_Fty_wrt_typ Fty1 (t_tvar_f X2)).
Proof.
intros; rewrite typsubst_Fty_open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_Fty_open_Fty_wrt_typ_var : lngen.

(* begin hide *)

Lemma typsubst_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_spec_rec :
forall A1 A2 X1 n1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof typsubst_typ_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_Fty_spec_rec_mutual :
(forall Fty1 A1 X1 n1,
  typsubst_Fty A1 X1 Fty1 = open_Fty_wrt_typ_rec n1 A1 (close_Fty_wrt_typ_rec n1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_Fty_spec_rec :
forall Fty1 A1 X1 n1,
  typsubst_Fty A1 X1 Fty1 = open_Fty_wrt_typ_rec n1 A1 (close_Fty_wrt_typ_rec n1 X1 Fty1).
Proof.
pose proof typsubst_Fty_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_spec_rec : lngen.

(* end hide *)

Lemma typsubst_typ_spec :
forall A1 A2 X1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_spec : lngen.

Lemma typsubst_Fty_spec :
forall Fty1 A1 X1,
  typsubst_Fty A1 X1 Fty1 = open_Fty_wrt_typ (close_Fty_wrt_typ X1 Fty1) A1.
Proof.
unfold close_Fty_wrt_typ; unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_Fty_spec : lngen.

(* begin hide *)

Lemma typsubst_typ_typsubst_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_typ A2 ->
  X2 <> X1 ->
  typsubst_typ A2 X1 (typsubst_typ A3 X2 A1) = typsubst_typ (typsubst_typ A2 X1 A3) X2 (typsubst_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_typsubst_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_typ A2 ->
  X2 <> X1 ->
  typsubst_typ A2 X1 (typsubst_typ A3 X2 A1) = typsubst_typ (typsubst_typ A2 X1 A3) X2 (typsubst_typ A2 X1 A1).
Proof.
pose proof typsubst_typ_typsubst_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_typsubst_typ : lngen.

(* begin hide *)

Lemma typsubst_Fty_typsubst_Fty_mutual :
(forall Fty1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_Fty A1 X1 (typsubst_Fty A2 X2 Fty1) = typsubst_Fty (typsubst_typ A1 X1 A2) X2 (typsubst_Fty A1 X1 Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_typsubst_Fty :
forall Fty1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_Fty A1 X1 (typsubst_Fty A2 X2 Fty1) = typsubst_Fty (typsubst_typ A1 X1 A2) X2 (typsubst_Fty A1 X1 Fty1).
Proof.
pose proof typsubst_Fty_typsubst_Fty_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_typsubst_Fty : lngen.

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X2) A2)).
Proof.
pose proof typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_Fty_close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec_mutual :
(forall Fty1 A1 X1 X2 n1,
  X2 `notin` typefv_Fty Fty1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_Fty A1 X1 Fty1 = close_Fty_wrt_typ_rec n1 X2 (typsubst_Fty A1 X1 (open_Fty_wrt_typ_rec n1 (t_tvar_f X2) Fty1))).
Proof.
apply_mutual_ind Fty_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_Fty_close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec :
forall Fty1 A1 X1 X2 n1,
  X2 `notin` typefv_Fty Fty1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_Fty A1 X1 Fty1 = close_Fty_wrt_typ_rec n1 X2 (typsubst_Fty A1 X1 (open_Fty_wrt_typ_rec n1 (t_tvar_f X2) Fty1)).
Proof.
pose proof typsubst_Fty_close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_close_Fty_wrt_typ_rec_open_Fty_wrt_typ_rec : lngen.

(* end hide *)

Lemma typsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ X2 (typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_tvar_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma typsubst_Fty_close_Fty_wrt_typ_open_Fty_wrt_typ :
forall Fty1 A1 X1 X2,
  X2 `notin` typefv_Fty Fty1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_Fty A1 X1 Fty1 = close_Fty_wrt_typ X2 (typsubst_Fty A1 X1 (open_Fty_wrt_typ Fty1 (t_tvar_f X2))).
Proof.
unfold close_Fty_wrt_typ; unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_Fty_close_Fty_wrt_typ_open_Fty_wrt_typ : lngen.

Lemma typsubst_typ_t_forall :
forall X2 B1 A1 X1,
  lc_typ A1 ->
  X2 `notin` typefv_typ A1 `union` typefv_typ B1 `union` singleton X1 ->
  typsubst_typ A1 X1 (t_forall B1) = t_forall (close_typ_wrt_typ X2 (typsubst_typ A1 X1 (open_typ_wrt_typ B1 (t_tvar_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_typ_t_forall : lngen.

(* begin hide *)

Lemma typsubst_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = typsubst_typ A2 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = typsubst_typ A2 X1 (open_typ_wrt_typ_rec n1 (t_tvar_f X1) A1).
Proof.
pose proof typsubst_typ_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_typ_intro_rec : lngen.
Hint Rewrite typsubst_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_Fty_intro_rec_mutual :
(forall Fty1 X1 A1 n1,
  X1 `notin` typefv_Fty Fty1 ->
  open_Fty_wrt_typ_rec n1 A1 Fty1 = typsubst_Fty A1 X1 (open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1)).
Proof.
apply_mutual_ind Fty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Fty_intro_rec :
forall Fty1 X1 A1 n1,
  X1 `notin` typefv_Fty Fty1 ->
  open_Fty_wrt_typ_rec n1 A1 Fty1 = typsubst_Fty A1 X1 (open_Fty_wrt_typ_rec n1 (t_tvar_f X1) Fty1).
Proof.
pose proof typsubst_Fty_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Fty_intro_rec : lngen.
Hint Rewrite typsubst_Fty_intro_rec using solve [auto] : lngen.

Lemma typsubst_typ_intro :
forall X1 A1 A2,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ A1 A2 = typsubst_typ A2 X1 (open_typ_wrt_typ A1 (t_tvar_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_typ_intro : lngen.

Lemma typsubst_Fty_intro :
forall X1 Fty1 A1,
  X1 `notin` typefv_Fty Fty1 ->
  open_Fty_wrt_typ Fty1 A1 = typsubst_Fty A1 X1 (open_Fty_wrt_typ Fty1 (t_tvar_f X1)).
Proof.
unfold open_Fty_wrt_typ; default_simp.
Qed.

Hint Resolve typsubst_Fty_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
