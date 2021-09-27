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

Scheme A_ind' := Induction for A Sort Prop.

Definition A_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  A_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme A_rec' := Induction for A Sort Set.

Definition A_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  A_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme Tcov_ind' := Induction for Tcov Sort Prop.

Definition Tcov_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  Tcov_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme Tcov_rec' := Induction for Tcov Sort Set.

Definition Tcov_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  Tcov_rec' H1 H2 H3 H4 H5 H6 H7 H8.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_A_wrt_A_rec (n1 : nat) (X1 : typevar) (A1 : A) {struct A1} : A :=
  match A1 with
    | t_tvar_f X2 => if (X1 == X2) then (t_tvar_b n1) else (t_tvar_f X2)
    | t_tvar_b n2 => if (lt_ge_dec n2 n1) then (t_tvar_b n2) else (t_tvar_b (S n2))
    | t_rcd l1 A2 => t_rcd l1 (close_A_wrt_A_rec n1 X1 A2)
    | t_and A2 A3 => t_and (close_A_wrt_A_rec n1 X1 A2) (close_A_wrt_A_rec n1 X1 A3)
    | t_or A2 A3 => t_or (close_A_wrt_A_rec n1 X1 A2) (close_A_wrt_A_rec n1 X1 A3)
    | t_arrow A2 B1 => t_arrow (close_A_wrt_A_rec n1 X1 A2) (close_A_wrt_A_rec n1 X1 B1)
    | t_forall B1 => t_forall (close_A_wrt_A_rec (S n1) X1 B1)
    | t_top => t_top
    | t_bot => t_bot
  end.

Definition close_A_wrt_A X1 A1 := close_A_wrt_A_rec 0 X1 A1.

Fixpoint close_Tcov_wrt_A_rec (n1 : nat) (X1 : typevar) (Tcov1 : Tcov) {struct Tcov1} : Tcov :=
  match Tcov1 with
    | ty_ctx_covTcovIn l1 => ty_ctx_covTcovIn l1
    | ty_ctx_covTcovArr A1 => ty_ctx_covTcovArr (close_A_wrt_A_rec n1 X1 A1)
    | ty_ctx_covTcovAll => ty_ctx_covTcovAll
    | ty_ctx_covTCovInterL A1 => ty_ctx_covTCovInterL (close_A_wrt_A_rec n1 X1 A1)
    | ty_ctx_covTCovInterR A1 => ty_ctx_covTCovInterR (close_A_wrt_A_rec n1 X1 A1)
    | ty_ctx_covTCovUnionL A1 => ty_ctx_covTCovUnionL (close_A_wrt_A_rec n1 X1 A1)
    | ty_ctx_covTCovUnionR A1 => ty_ctx_covTCovUnionR (close_A_wrt_A_rec n1 X1 A1)
  end.

Definition close_Tcov_wrt_A X1 Tcov1 := close_Tcov_wrt_A_rec 0 X1 Tcov1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_l (l1 : l) {struct l1} : nat :=
  match l1 with
    | lbl_TagIndex i1 => 1
    | lbl_TagLeft => 1
    | lbl_TagRight => 1
  end.

Fixpoint size_A (A1 : A) {struct A1} : nat :=
  match A1 with
    | t_tvar_f X1 => 1
    | t_tvar_b n1 => 1
    | t_rcd l1 A2 => 1 + (size_l l1) + (size_A A2)
    | t_and A2 A3 => 1 + (size_A A2) + (size_A A3)
    | t_or A2 A3 => 1 + (size_A A2) + (size_A A3)
    | t_arrow A2 B1 => 1 + (size_A A2) + (size_A B1)
    | t_forall B1 => 1 + (size_A B1)
    | t_top => 1
    | t_bot => 1
  end.

Fixpoint size_Tcov (Tcov1 : Tcov) {struct Tcov1} : nat :=
  match Tcov1 with
    | ty_ctx_covTcovIn l1 => 1 + (size_l l1)
    | ty_ctx_covTcovArr A1 => 1 + (size_A A1)
    | ty_ctx_covTcovAll => 1
    | ty_ctx_covTCovInterL A1 => 1 + (size_A A1)
    | ty_ctx_covTCovInterR A1 => 1 + (size_A A1)
    | ty_ctx_covTCovUnionL A1 => 1 + (size_A A1)
    | ty_ctx_covTCovUnionR A1 => 1 + (size_A A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_A_wrt_A : nat -> A -> Prop :=
  | degree_wrt_A_t_tvar_f : forall n1 X1,
    degree_A_wrt_A n1 (t_tvar_f X1)
  | degree_wrt_A_t_tvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_A_wrt_A n1 (t_tvar_b n2)
  | degree_wrt_A_t_rcd : forall n1 l1 A1,
    degree_A_wrt_A n1 A1 ->
    degree_A_wrt_A n1 (t_rcd l1 A1)
  | degree_wrt_A_t_and : forall n1 A1 A2,
    degree_A_wrt_A n1 A1 ->
    degree_A_wrt_A n1 A2 ->
    degree_A_wrt_A n1 (t_and A1 A2)
  | degree_wrt_A_t_or : forall n1 A1 A2,
    degree_A_wrt_A n1 A1 ->
    degree_A_wrt_A n1 A2 ->
    degree_A_wrt_A n1 (t_or A1 A2)
  | degree_wrt_A_t_arrow : forall n1 A1 B1,
    degree_A_wrt_A n1 A1 ->
    degree_A_wrt_A n1 B1 ->
    degree_A_wrt_A n1 (t_arrow A1 B1)
  | degree_wrt_A_t_forall : forall n1 B1,
    degree_A_wrt_A (S n1) B1 ->
    degree_A_wrt_A n1 (t_forall B1)
  | degree_wrt_A_t_top : forall n1,
    degree_A_wrt_A n1 (t_top)
  | degree_wrt_A_t_bot : forall n1,
    degree_A_wrt_A n1 (t_bot).

Scheme degree_A_wrt_A_ind' := Induction for degree_A_wrt_A Sort Prop.

Definition degree_A_wrt_A_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_A_wrt_A_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors degree_A_wrt_A : core lngen.

Inductive degree_Tcov_wrt_A : nat -> Tcov -> Prop :=
  | degree_wrt_A_ty_ctx_covTcovIn : forall n1 l1,
    degree_Tcov_wrt_A n1 (ty_ctx_covTcovIn l1)
  | degree_wrt_A_ty_ctx_covTcovArr : forall n1 A1,
    degree_A_wrt_A n1 A1 ->
    degree_Tcov_wrt_A n1 (ty_ctx_covTcovArr A1)
  | degree_wrt_A_ty_ctx_covTcovAll : forall n1,
    degree_Tcov_wrt_A n1 (ty_ctx_covTcovAll)
  | degree_wrt_A_ty_ctx_covTCovInterL : forall n1 A1,
    degree_A_wrt_A n1 A1 ->
    degree_Tcov_wrt_A n1 (ty_ctx_covTCovInterL A1)
  | degree_wrt_A_ty_ctx_covTCovInterR : forall n1 A1,
    degree_A_wrt_A n1 A1 ->
    degree_Tcov_wrt_A n1 (ty_ctx_covTCovInterR A1)
  | degree_wrt_A_ty_ctx_covTCovUnionL : forall n1 A1,
    degree_A_wrt_A n1 A1 ->
    degree_Tcov_wrt_A n1 (ty_ctx_covTCovUnionL A1)
  | degree_wrt_A_ty_ctx_covTCovUnionR : forall n1 A1,
    degree_A_wrt_A n1 A1 ->
    degree_Tcov_wrt_A n1 (ty_ctx_covTCovUnionR A1).

Scheme degree_Tcov_wrt_A_ind' := Induction for degree_Tcov_wrt_A Sort Prop.

Definition degree_Tcov_wrt_A_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  degree_Tcov_wrt_A_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Hint Constructors degree_Tcov_wrt_A : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_A : A -> Set :=
  | lc_set_t_tvar_f : forall X1,
    lc_set_A (t_tvar_f X1)
  | lc_set_t_rcd : forall l1 A1,
    lc_set_A A1 ->
    lc_set_A (t_rcd l1 A1)
  | lc_set_t_and : forall A1 A2,
    lc_set_A A1 ->
    lc_set_A A2 ->
    lc_set_A (t_and A1 A2)
  | lc_set_t_or : forall A1 A2,
    lc_set_A A1 ->
    lc_set_A A2 ->
    lc_set_A (t_or A1 A2)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_A A1 ->
    lc_set_A B1 ->
    lc_set_A (t_arrow A1 B1)
  | lc_set_t_forall : forall B1,
    (forall X1 : typevar, lc_set_A (open_A_wrt_A B1 (t_tvar_f X1))) ->
    lc_set_A (t_forall B1)
  | lc_set_t_top :
    lc_set_A (t_top)
  | lc_set_t_bot :
    lc_set_A (t_bot).

Scheme lc_A_ind' := Induction for lc_A Sort Prop.

Definition lc_A_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_A_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_A_ind' := Induction for lc_set_A Sort Prop.

Definition lc_set_A_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_A_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_A_rec' := Induction for lc_set_A Sort Set.

Definition lc_set_A_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_A_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors lc_A : core lngen.

Hint Constructors lc_set_A : core lngen.

Inductive lc_set_Tcov : Tcov -> Set :=
  | lc_set_ty_ctx_covTcovIn : forall l1,
    lc_set_Tcov (ty_ctx_covTcovIn l1)
  | lc_set_ty_ctx_covTcovArr : forall A1,
    lc_set_A A1 ->
    lc_set_Tcov (ty_ctx_covTcovArr A1)
  | lc_set_ty_ctx_covTcovAll :
    lc_set_Tcov (ty_ctx_covTcovAll)
  | lc_set_ty_ctx_covTCovInterL : forall A1,
    lc_set_A A1 ->
    lc_set_Tcov (ty_ctx_covTCovInterL A1)
  | lc_set_ty_ctx_covTCovInterR : forall A1,
    lc_set_A A1 ->
    lc_set_Tcov (ty_ctx_covTCovInterR A1)
  | lc_set_ty_ctx_covTCovUnionL : forall A1,
    lc_set_A A1 ->
    lc_set_Tcov (ty_ctx_covTCovUnionL A1)
  | lc_set_ty_ctx_covTCovUnionR : forall A1,
    lc_set_A A1 ->
    lc_set_Tcov (ty_ctx_covTCovUnionR A1).

Scheme lc_Tcov_ind' := Induction for lc_Tcov Sort Prop.

Definition lc_Tcov_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_Tcov_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_Tcov_ind' := Induction for lc_set_Tcov Sort Prop.

Definition lc_set_Tcov_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_Tcov_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_Tcov_rec' := Induction for lc_set_Tcov Sort Set.

Definition lc_set_Tcov_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_Tcov_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Hint Constructors lc_Tcov : core lngen.

Hint Constructors lc_set_Tcov : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_A_wrt_A A1 := forall X1, lc_A (open_A_wrt_A A1 (t_tvar_f X1)).

Hint Unfold body_A_wrt_A : core.

Definition body_Tcov_wrt_A Tcov1 := forall X1, lc_Tcov (open_Tcov_wrt_A Tcov1 (t_tvar_f X1)).

Hint Unfold body_Tcov_wrt_A : core.


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

Lemma size_A_min_mutual :
(forall A1, 1 <= size_A A1).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_A_min :
forall A1, 1 <= size_A A1.
Proof.
pose proof size_A_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_A_min : lngen.

(* begin hide *)

Lemma size_Tcov_min_mutual :
(forall Tcov1, 1 <= size_Tcov Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Tcov_min :
forall Tcov1, 1 <= size_Tcov Tcov1.
Proof.
pose proof size_Tcov_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Tcov_min : lngen.

(* begin hide *)

Lemma size_A_close_A_wrt_A_rec_mutual :
(forall A1 X1 n1,
  size_A (close_A_wrt_A_rec n1 X1 A1) = size_A A1).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_A_close_A_wrt_A_rec :
forall A1 X1 n1,
  size_A (close_A_wrt_A_rec n1 X1 A1) = size_A A1.
Proof.
pose proof size_A_close_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_A_close_A_wrt_A_rec : lngen.
Hint Rewrite size_A_close_A_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tcov_close_Tcov_wrt_A_rec_mutual :
(forall Tcov1 X1 n1,
  size_Tcov (close_Tcov_wrt_A_rec n1 X1 Tcov1) = size_Tcov Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tcov_close_Tcov_wrt_A_rec :
forall Tcov1 X1 n1,
  size_Tcov (close_Tcov_wrt_A_rec n1 X1 Tcov1) = size_Tcov Tcov1.
Proof.
pose proof size_Tcov_close_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Tcov_close_Tcov_wrt_A_rec : lngen.
Hint Rewrite size_Tcov_close_Tcov_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_A_close_A_wrt_A :
forall A1 X1,
  size_A (close_A_wrt_A X1 A1) = size_A A1.
Proof.
unfold close_A_wrt_A; default_simp.
Qed.

Hint Resolve size_A_close_A_wrt_A : lngen.
Hint Rewrite size_A_close_A_wrt_A using solve [auto] : lngen.

Lemma size_Tcov_close_Tcov_wrt_A :
forall Tcov1 X1,
  size_Tcov (close_Tcov_wrt_A X1 Tcov1) = size_Tcov Tcov1.
Proof.
unfold close_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve size_Tcov_close_Tcov_wrt_A : lngen.
Hint Rewrite size_Tcov_close_Tcov_wrt_A using solve [auto] : lngen.

(* begin hide *)

Lemma size_A_open_A_wrt_A_rec_mutual :
(forall A1 A2 n1,
  size_A A1 <= size_A (open_A_wrt_A_rec n1 A2 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_A_open_A_wrt_A_rec :
forall A1 A2 n1,
  size_A A1 <= size_A (open_A_wrt_A_rec n1 A2 A1).
Proof.
pose proof size_A_open_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_A_open_A_wrt_A_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tcov_open_Tcov_wrt_A_rec_mutual :
(forall Tcov1 A1 n1,
  size_Tcov Tcov1 <= size_Tcov (open_Tcov_wrt_A_rec n1 A1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tcov_open_Tcov_wrt_A_rec :
forall Tcov1 A1 n1,
  size_Tcov Tcov1 <= size_Tcov (open_Tcov_wrt_A_rec n1 A1 Tcov1).
Proof.
pose proof size_Tcov_open_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Tcov_open_Tcov_wrt_A_rec : lngen.

(* end hide *)

Lemma size_A_open_A_wrt_A :
forall A1 A2,
  size_A A1 <= size_A (open_A_wrt_A A1 A2).
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve size_A_open_A_wrt_A : lngen.

Lemma size_Tcov_open_Tcov_wrt_A :
forall Tcov1 A1,
  size_Tcov Tcov1 <= size_Tcov (open_Tcov_wrt_A Tcov1 A1).
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve size_Tcov_open_Tcov_wrt_A : lngen.

(* begin hide *)

Lemma size_A_open_A_wrt_A_rec_var_mutual :
(forall A1 X1 n1,
  size_A (open_A_wrt_A_rec n1 (t_tvar_f X1) A1) = size_A A1).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_A_open_A_wrt_A_rec_var :
forall A1 X1 n1,
  size_A (open_A_wrt_A_rec n1 (t_tvar_f X1) A1) = size_A A1.
Proof.
pose proof size_A_open_A_wrt_A_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_A_open_A_wrt_A_rec_var : lngen.
Hint Rewrite size_A_open_A_wrt_A_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_Tcov_open_Tcov_wrt_A_rec_var_mutual :
(forall Tcov1 X1 n1,
  size_Tcov (open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1) = size_Tcov Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_Tcov_open_Tcov_wrt_A_rec_var :
forall Tcov1 X1 n1,
  size_Tcov (open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1) = size_Tcov Tcov1.
Proof.
pose proof size_Tcov_open_Tcov_wrt_A_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Tcov_open_Tcov_wrt_A_rec_var : lngen.
Hint Rewrite size_Tcov_open_Tcov_wrt_A_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_A_open_A_wrt_A_var :
forall A1 X1,
  size_A (open_A_wrt_A A1 (t_tvar_f X1)) = size_A A1.
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve size_A_open_A_wrt_A_var : lngen.
Hint Rewrite size_A_open_A_wrt_A_var using solve [auto] : lngen.

Lemma size_Tcov_open_Tcov_wrt_A_var :
forall Tcov1 X1,
  size_Tcov (open_Tcov_wrt_A Tcov1 (t_tvar_f X1)) = size_Tcov Tcov1.
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve size_Tcov_open_Tcov_wrt_A_var : lngen.
Hint Rewrite size_Tcov_open_Tcov_wrt_A_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_A_wrt_A_S_mutual :
(forall n1 A1,
  degree_A_wrt_A n1 A1 ->
  degree_A_wrt_A (S n1) A1).
Proof.
apply_mutual_ind degree_A_wrt_A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_A_wrt_A_S :
forall n1 A1,
  degree_A_wrt_A n1 A1 ->
  degree_A_wrt_A (S n1) A1.
Proof.
pose proof degree_A_wrt_A_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_A_wrt_A_S : lngen.

(* begin hide *)

Lemma degree_Tcov_wrt_A_S_mutual :
(forall n1 Tcov1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  degree_Tcov_wrt_A (S n1) Tcov1).
Proof.
apply_mutual_ind degree_Tcov_wrt_A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_Tcov_wrt_A_S :
forall n1 Tcov1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  degree_Tcov_wrt_A (S n1) Tcov1.
Proof.
pose proof degree_Tcov_wrt_A_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Tcov_wrt_A_S : lngen.

Lemma degree_A_wrt_A_O :
forall n1 A1,
  degree_A_wrt_A O A1 ->
  degree_A_wrt_A n1 A1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_A_wrt_A_O : lngen.

Lemma degree_Tcov_wrt_A_O :
forall n1 Tcov1,
  degree_Tcov_wrt_A O Tcov1 ->
  degree_Tcov_wrt_A n1 Tcov1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_Tcov_wrt_A_O : lngen.

(* begin hide *)

Lemma degree_A_wrt_A_close_A_wrt_A_rec_mutual :
(forall A1 X1 n1,
  degree_A_wrt_A n1 A1 ->
  degree_A_wrt_A (S n1) (close_A_wrt_A_rec n1 X1 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_A_wrt_A_close_A_wrt_A_rec :
forall A1 X1 n1,
  degree_A_wrt_A n1 A1 ->
  degree_A_wrt_A (S n1) (close_A_wrt_A_rec n1 X1 A1).
Proof.
pose proof degree_A_wrt_A_close_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_A_wrt_A_close_A_wrt_A_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_close_Tcov_wrt_A_rec_mutual :
(forall Tcov1 X1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  degree_Tcov_wrt_A (S n1) (close_Tcov_wrt_A_rec n1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_close_Tcov_wrt_A_rec :
forall Tcov1 X1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  degree_Tcov_wrt_A (S n1) (close_Tcov_wrt_A_rec n1 X1 Tcov1).
Proof.
pose proof degree_Tcov_wrt_A_close_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Tcov_wrt_A_close_Tcov_wrt_A_rec : lngen.

(* end hide *)

Lemma degree_A_wrt_A_close_A_wrt_A :
forall A1 X1,
  degree_A_wrt_A 0 A1 ->
  degree_A_wrt_A 1 (close_A_wrt_A X1 A1).
Proof.
unfold close_A_wrt_A; default_simp.
Qed.

Hint Resolve degree_A_wrt_A_close_A_wrt_A : lngen.

Lemma degree_Tcov_wrt_A_close_Tcov_wrt_A :
forall Tcov1 X1,
  degree_Tcov_wrt_A 0 Tcov1 ->
  degree_Tcov_wrt_A 1 (close_Tcov_wrt_A X1 Tcov1).
Proof.
unfold close_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve degree_Tcov_wrt_A_close_Tcov_wrt_A : lngen.

(* begin hide *)

Lemma degree_A_wrt_A_close_A_wrt_A_rec_inv_mutual :
(forall A1 X1 n1,
  degree_A_wrt_A (S n1) (close_A_wrt_A_rec n1 X1 A1) ->
  degree_A_wrt_A n1 A1).
Proof.
apply_mutual_ind A_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_A_wrt_A_close_A_wrt_A_rec_inv :
forall A1 X1 n1,
  degree_A_wrt_A (S n1) (close_A_wrt_A_rec n1 X1 A1) ->
  degree_A_wrt_A n1 A1.
Proof.
pose proof degree_A_wrt_A_close_A_wrt_A_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_A_wrt_A_close_A_wrt_A_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_close_Tcov_wrt_A_rec_inv_mutual :
(forall Tcov1 X1 n1,
  degree_Tcov_wrt_A (S n1) (close_Tcov_wrt_A_rec n1 X1 Tcov1) ->
  degree_Tcov_wrt_A n1 Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_close_Tcov_wrt_A_rec_inv :
forall Tcov1 X1 n1,
  degree_Tcov_wrt_A (S n1) (close_Tcov_wrt_A_rec n1 X1 Tcov1) ->
  degree_Tcov_wrt_A n1 Tcov1.
Proof.
pose proof degree_Tcov_wrt_A_close_Tcov_wrt_A_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_Tcov_wrt_A_close_Tcov_wrt_A_rec_inv : lngen.

(* end hide *)

Lemma degree_A_wrt_A_close_A_wrt_A_inv :
forall A1 X1,
  degree_A_wrt_A 1 (close_A_wrt_A X1 A1) ->
  degree_A_wrt_A 0 A1.
Proof.
unfold close_A_wrt_A; eauto with lngen.
Qed.

Hint Immediate degree_A_wrt_A_close_A_wrt_A_inv : lngen.

Lemma degree_Tcov_wrt_A_close_Tcov_wrt_A_inv :
forall Tcov1 X1,
  degree_Tcov_wrt_A 1 (close_Tcov_wrt_A X1 Tcov1) ->
  degree_Tcov_wrt_A 0 Tcov1.
Proof.
unfold close_Tcov_wrt_A; eauto with lngen.
Qed.

Hint Immediate degree_Tcov_wrt_A_close_Tcov_wrt_A_inv : lngen.

(* begin hide *)

Lemma degree_A_wrt_A_open_A_wrt_A_rec_mutual :
(forall A1 A2 n1,
  degree_A_wrt_A (S n1) A1 ->
  degree_A_wrt_A n1 A2 ->
  degree_A_wrt_A n1 (open_A_wrt_A_rec n1 A2 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_A_wrt_A_open_A_wrt_A_rec :
forall A1 A2 n1,
  degree_A_wrt_A (S n1) A1 ->
  degree_A_wrt_A n1 A2 ->
  degree_A_wrt_A n1 (open_A_wrt_A_rec n1 A2 A1).
Proof.
pose proof degree_A_wrt_A_open_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_A_wrt_A_open_A_wrt_A_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_open_Tcov_wrt_A_rec_mutual :
(forall Tcov1 A1 n1,
  degree_Tcov_wrt_A (S n1) Tcov1 ->
  degree_A_wrt_A n1 A1 ->
  degree_Tcov_wrt_A n1 (open_Tcov_wrt_A_rec n1 A1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_open_Tcov_wrt_A_rec :
forall Tcov1 A1 n1,
  degree_Tcov_wrt_A (S n1) Tcov1 ->
  degree_A_wrt_A n1 A1 ->
  degree_Tcov_wrt_A n1 (open_Tcov_wrt_A_rec n1 A1 Tcov1).
Proof.
pose proof degree_Tcov_wrt_A_open_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Tcov_wrt_A_open_Tcov_wrt_A_rec : lngen.

(* end hide *)

Lemma degree_A_wrt_A_open_A_wrt_A :
forall A1 A2,
  degree_A_wrt_A 1 A1 ->
  degree_A_wrt_A 0 A2 ->
  degree_A_wrt_A 0 (open_A_wrt_A A1 A2).
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve degree_A_wrt_A_open_A_wrt_A : lngen.

Lemma degree_Tcov_wrt_A_open_Tcov_wrt_A :
forall Tcov1 A1,
  degree_Tcov_wrt_A 1 Tcov1 ->
  degree_A_wrt_A 0 A1 ->
  degree_Tcov_wrt_A 0 (open_Tcov_wrt_A Tcov1 A1).
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve degree_Tcov_wrt_A_open_Tcov_wrt_A : lngen.

(* begin hide *)

Lemma degree_A_wrt_A_open_A_wrt_A_rec_inv_mutual :
(forall A1 A2 n1,
  degree_A_wrt_A n1 (open_A_wrt_A_rec n1 A2 A1) ->
  degree_A_wrt_A (S n1) A1).
Proof.
apply_mutual_ind A_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_A_wrt_A_open_A_wrt_A_rec_inv :
forall A1 A2 n1,
  degree_A_wrt_A n1 (open_A_wrt_A_rec n1 A2 A1) ->
  degree_A_wrt_A (S n1) A1.
Proof.
pose proof degree_A_wrt_A_open_A_wrt_A_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_A_wrt_A_open_A_wrt_A_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_open_Tcov_wrt_A_rec_inv_mutual :
(forall Tcov1 A1 n1,
  degree_Tcov_wrt_A n1 (open_Tcov_wrt_A_rec n1 A1 Tcov1) ->
  degree_Tcov_wrt_A (S n1) Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_Tcov_wrt_A_open_Tcov_wrt_A_rec_inv :
forall Tcov1 A1 n1,
  degree_Tcov_wrt_A n1 (open_Tcov_wrt_A_rec n1 A1 Tcov1) ->
  degree_Tcov_wrt_A (S n1) Tcov1.
Proof.
pose proof degree_Tcov_wrt_A_open_Tcov_wrt_A_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_Tcov_wrt_A_open_Tcov_wrt_A_rec_inv : lngen.

(* end hide *)

Lemma degree_A_wrt_A_open_A_wrt_A_inv :
forall A1 A2,
  degree_A_wrt_A 0 (open_A_wrt_A A1 A2) ->
  degree_A_wrt_A 1 A1.
Proof.
unfold open_A_wrt_A; eauto with lngen.
Qed.

Hint Immediate degree_A_wrt_A_open_A_wrt_A_inv : lngen.

Lemma degree_Tcov_wrt_A_open_Tcov_wrt_A_inv :
forall Tcov1 A1,
  degree_Tcov_wrt_A 0 (open_Tcov_wrt_A Tcov1 A1) ->
  degree_Tcov_wrt_A 1 Tcov1.
Proof.
unfold open_Tcov_wrt_A; eauto with lngen.
Qed.

Hint Immediate degree_Tcov_wrt_A_open_Tcov_wrt_A_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_A_wrt_A_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_A_wrt_A_rec n1 X1 A1 = close_A_wrt_A_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind A_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_A_wrt_A_rec_inj :
forall A1 A2 X1 n1,
  close_A_wrt_A_rec n1 X1 A1 = close_A_wrt_A_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_A_wrt_A_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_A_wrt_A_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tcov_wrt_A_rec_inj_mutual :
(forall Tcov1 Tcov2 X1 n1,
  close_Tcov_wrt_A_rec n1 X1 Tcov1 = close_Tcov_wrt_A_rec n1 X1 Tcov2 ->
  Tcov1 = Tcov2).
Proof.
apply_mutual_ind Tcov_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tcov_wrt_A_rec_inj :
forall Tcov1 Tcov2 X1 n1,
  close_Tcov_wrt_A_rec n1 X1 Tcov1 = close_Tcov_wrt_A_rec n1 X1 Tcov2 ->
  Tcov1 = Tcov2.
Proof.
pose proof close_Tcov_wrt_A_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_Tcov_wrt_A_rec_inj : lngen.

(* end hide *)

Lemma close_A_wrt_A_inj :
forall A1 A2 X1,
  close_A_wrt_A X1 A1 = close_A_wrt_A X1 A2 ->
  A1 = A2.
Proof.
unfold close_A_wrt_A; eauto with lngen.
Qed.

Hint Immediate close_A_wrt_A_inj : lngen.

Lemma close_Tcov_wrt_A_inj :
forall Tcov1 Tcov2 X1,
  close_Tcov_wrt_A X1 Tcov1 = close_Tcov_wrt_A X1 Tcov2 ->
  Tcov1 = Tcov2.
Proof.
unfold close_Tcov_wrt_A; eauto with lngen.
Qed.

Hint Immediate close_Tcov_wrt_A_inj : lngen.

(* begin hide *)

Lemma close_A_wrt_A_rec_open_A_wrt_A_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` typefv_A A1 ->
  close_A_wrt_A_rec n1 X1 (open_A_wrt_A_rec n1 (t_tvar_f X1) A1) = A1).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_A_wrt_A_rec_open_A_wrt_A_rec :
forall A1 X1 n1,
  X1 `notin` typefv_A A1 ->
  close_A_wrt_A_rec n1 X1 (open_A_wrt_A_rec n1 (t_tvar_f X1) A1) = A1.
Proof.
pose proof close_A_wrt_A_rec_open_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_A_wrt_A_rec_open_A_wrt_A_rec : lngen.
Hint Rewrite close_A_wrt_A_rec_open_A_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec_mutual :
(forall Tcov1 X1 n1,
  X1 `notin` typefv_Tcov Tcov1 ->
  close_Tcov_wrt_A_rec n1 X1 (open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1) = Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec :
forall Tcov1 X1 n1,
  X1 `notin` typefv_Tcov Tcov1 ->
  close_Tcov_wrt_A_rec n1 X1 (open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1) = Tcov1.
Proof.
pose proof close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec : lngen.
Hint Rewrite close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_A_wrt_A_open_A_wrt_A :
forall A1 X1,
  X1 `notin` typefv_A A1 ->
  close_A_wrt_A X1 (open_A_wrt_A A1 (t_tvar_f X1)) = A1.
Proof.
unfold close_A_wrt_A; unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve close_A_wrt_A_open_A_wrt_A : lngen.
Hint Rewrite close_A_wrt_A_open_A_wrt_A using solve [auto] : lngen.

Lemma close_Tcov_wrt_A_open_Tcov_wrt_A :
forall Tcov1 X1,
  X1 `notin` typefv_Tcov Tcov1 ->
  close_Tcov_wrt_A X1 (open_Tcov_wrt_A Tcov1 (t_tvar_f X1)) = Tcov1.
Proof.
unfold close_Tcov_wrt_A; unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve close_Tcov_wrt_A_open_Tcov_wrt_A : lngen.
Hint Rewrite close_Tcov_wrt_A_open_Tcov_wrt_A using solve [auto] : lngen.

(* begin hide *)

Lemma open_A_wrt_A_rec_close_A_wrt_A_rec_mutual :
(forall A1 X1 n1,
  open_A_wrt_A_rec n1 (t_tvar_f X1) (close_A_wrt_A_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_A_wrt_A_rec_close_A_wrt_A_rec :
forall A1 X1 n1,
  open_A_wrt_A_rec n1 (t_tvar_f X1) (close_A_wrt_A_rec n1 X1 A1) = A1.
Proof.
pose proof open_A_wrt_A_rec_close_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_A_wrt_A_rec_close_A_wrt_A_rec : lngen.
Hint Rewrite open_A_wrt_A_rec_close_A_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tcov_wrt_A_rec_close_Tcov_wrt_A_rec_mutual :
(forall Tcov1 X1 n1,
  open_Tcov_wrt_A_rec n1 (t_tvar_f X1) (close_Tcov_wrt_A_rec n1 X1 Tcov1) = Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tcov_wrt_A_rec_close_Tcov_wrt_A_rec :
forall Tcov1 X1 n1,
  open_Tcov_wrt_A_rec n1 (t_tvar_f X1) (close_Tcov_wrt_A_rec n1 X1 Tcov1) = Tcov1.
Proof.
pose proof open_Tcov_wrt_A_rec_close_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_Tcov_wrt_A_rec_close_Tcov_wrt_A_rec : lngen.
Hint Rewrite open_Tcov_wrt_A_rec_close_Tcov_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_A_wrt_A_close_A_wrt_A :
forall A1 X1,
  open_A_wrt_A (close_A_wrt_A X1 A1) (t_tvar_f X1) = A1.
Proof.
unfold close_A_wrt_A; unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve open_A_wrt_A_close_A_wrt_A : lngen.
Hint Rewrite open_A_wrt_A_close_A_wrt_A using solve [auto] : lngen.

Lemma open_Tcov_wrt_A_close_Tcov_wrt_A :
forall Tcov1 X1,
  open_Tcov_wrt_A (close_Tcov_wrt_A X1 Tcov1) (t_tvar_f X1) = Tcov1.
Proof.
unfold close_Tcov_wrt_A; unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve open_Tcov_wrt_A_close_Tcov_wrt_A : lngen.
Hint Rewrite open_Tcov_wrt_A_close_Tcov_wrt_A using solve [auto] : lngen.

(* begin hide *)

Lemma open_A_wrt_A_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` typefv_A A2 ->
  X1 `notin` typefv_A A1 ->
  open_A_wrt_A_rec n1 (t_tvar_f X1) A2 = open_A_wrt_A_rec n1 (t_tvar_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind A_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_A_wrt_A_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` typefv_A A2 ->
  X1 `notin` typefv_A A1 ->
  open_A_wrt_A_rec n1 (t_tvar_f X1) A2 = open_A_wrt_A_rec n1 (t_tvar_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_A_wrt_A_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_A_wrt_A_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tcov_wrt_A_rec_inj_mutual :
(forall Tcov2 Tcov1 X1 n1,
  X1 `notin` typefv_Tcov Tcov2 ->
  X1 `notin` typefv_Tcov Tcov1 ->
  open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov2 = open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1 ->
  Tcov2 = Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tcov_wrt_A_rec_inj :
forall Tcov2 Tcov1 X1 n1,
  X1 `notin` typefv_Tcov Tcov2 ->
  X1 `notin` typefv_Tcov Tcov1 ->
  open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov2 = open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1 ->
  Tcov2 = Tcov1.
Proof.
pose proof open_Tcov_wrt_A_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_Tcov_wrt_A_rec_inj : lngen.

(* end hide *)

Lemma open_A_wrt_A_inj :
forall A2 A1 X1,
  X1 `notin` typefv_A A2 ->
  X1 `notin` typefv_A A1 ->
  open_A_wrt_A A2 (t_tvar_f X1) = open_A_wrt_A A1 (t_tvar_f X1) ->
  A2 = A1.
Proof.
unfold open_A_wrt_A; eauto with lngen.
Qed.

Hint Immediate open_A_wrt_A_inj : lngen.

Lemma open_Tcov_wrt_A_inj :
forall Tcov2 Tcov1 X1,
  X1 `notin` typefv_Tcov Tcov2 ->
  X1 `notin` typefv_Tcov Tcov1 ->
  open_Tcov_wrt_A Tcov2 (t_tvar_f X1) = open_Tcov_wrt_A Tcov1 (t_tvar_f X1) ->
  Tcov2 = Tcov1.
Proof.
unfold open_Tcov_wrt_A; eauto with lngen.
Qed.

Hint Immediate open_Tcov_wrt_A_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_A_wrt_A_of_lc_A_mutual :
(forall A1,
  lc_A A1 ->
  degree_A_wrt_A 0 A1).
Proof.
apply_mutual_ind lc_A_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_A_wrt_A_of_lc_A :
forall A1,
  lc_A A1 ->
  degree_A_wrt_A 0 A1.
Proof.
pose proof degree_A_wrt_A_of_lc_A_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_A_wrt_A_of_lc_A : lngen.

(* begin hide *)

Lemma degree_Tcov_wrt_A_of_lc_Tcov_mutual :
(forall Tcov1,
  lc_Tcov Tcov1 ->
  degree_Tcov_wrt_A 0 Tcov1).
Proof.
apply_mutual_ind lc_Tcov_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_Tcov_wrt_A_of_lc_Tcov :
forall Tcov1,
  lc_Tcov Tcov1 ->
  degree_Tcov_wrt_A 0 Tcov1.
Proof.
pose proof degree_Tcov_wrt_A_of_lc_Tcov_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_Tcov_wrt_A_of_lc_Tcov : lngen.

(* begin hide *)

Lemma lc_A_of_degree_size_mutual :
forall i1,
(forall A1,
  size_A A1 = i1 ->
  degree_A_wrt_A 0 A1 ->
  lc_A A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind A_mutind;
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

Lemma lc_A_of_degree :
forall A1,
  degree_A_wrt_A 0 A1 ->
  lc_A A1.
Proof.
intros A1; intros;
pose proof (lc_A_of_degree_size_mutual (size_A A1));
intuition eauto.
Qed.

Hint Resolve lc_A_of_degree : lngen.

(* begin hide *)

Lemma lc_Tcov_of_degree_size_mutual :
forall i1,
(forall Tcov1,
  size_Tcov Tcov1 = i1 ->
  degree_Tcov_wrt_A 0 Tcov1 ->
  lc_Tcov Tcov1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Tcov_mutind;
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

Lemma lc_Tcov_of_degree :
forall Tcov1,
  degree_Tcov_wrt_A 0 Tcov1 ->
  lc_Tcov Tcov1.
Proof.
intros Tcov1; intros;
pose proof (lc_Tcov_of_degree_size_mutual (size_Tcov Tcov1));
intuition eauto.
Qed.

Hint Resolve lc_Tcov_of_degree : lngen.

Ltac l_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac A_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_A_wrt_A_of_lc_A in J1; clear H
          end).

Ltac Tcov_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_Tcov_wrt_A_of_lc_Tcov in J1; clear H
          end).

Lemma lc_t_forall_exists :
forall X1 B1,
  lc_A (open_A_wrt_A B1 (t_tvar_f X1)) ->
  lc_A (t_forall B1).
Proof.
intros; A_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_A (t_forall _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_t_forall_exists X1) : core.

Lemma lc_body_A_wrt_A :
forall A1 A2,
  body_A_wrt_A A1 ->
  lc_A A2 ->
  lc_A (open_A_wrt_A A1 A2).
Proof.
unfold body_A_wrt_A;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
A_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_A_wrt_A : lngen.

Lemma lc_body_Tcov_wrt_A :
forall Tcov1 A1,
  body_Tcov_wrt_A Tcov1 ->
  lc_A A1 ->
  lc_Tcov (open_Tcov_wrt_A Tcov1 A1).
Proof.
unfold body_Tcov_wrt_A;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
Tcov_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_Tcov_wrt_A : lngen.

Lemma lc_body_t_forall_1 :
forall B1,
  lc_A (t_forall B1) ->
  body_A_wrt_A B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_t_forall_1 : lngen.

(* begin hide *)

Lemma lc_A_unique_mutual :
(forall A1 (proof2 proof3 : lc_A A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_A_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_A_unique :
forall A1 (proof2 proof3 : lc_A A1), proof2 = proof3.
Proof.
pose proof lc_A_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_A_unique : lngen.

(* begin hide *)

Lemma lc_Tcov_unique_mutual :
(forall Tcov1 (proof2 proof3 : lc_Tcov Tcov1), proof2 = proof3).
Proof.
apply_mutual_ind lc_Tcov_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_Tcov_unique :
forall Tcov1 (proof2 proof3 : lc_Tcov Tcov1), proof2 = proof3.
Proof.
pose proof lc_Tcov_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_Tcov_unique : lngen.

(* begin hide *)

Lemma lc_A_of_lc_set_A_mutual :
(forall A1, lc_set_A A1 -> lc_A A1).
Proof.
apply_mutual_ind lc_set_A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_A_of_lc_set_A :
forall A1, lc_set_A A1 -> lc_A A1.
Proof.
pose proof lc_A_of_lc_set_A_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_A_of_lc_set_A : lngen.

(* begin hide *)

Lemma lc_Tcov_of_lc_set_Tcov_mutual :
(forall Tcov1, lc_set_Tcov Tcov1 -> lc_Tcov Tcov1).
Proof.
apply_mutual_ind lc_set_Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_Tcov_of_lc_set_Tcov :
forall Tcov1, lc_set_Tcov Tcov1 -> lc_Tcov Tcov1.
Proof.
pose proof lc_Tcov_of_lc_set_Tcov_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_Tcov_of_lc_set_Tcov : lngen.

(* begin hide *)

Lemma lc_set_A_of_lc_A_size_mutual :
forall i1,
(forall A1,
  size_A A1 = i1 ->
  lc_A A1 ->
  lc_set_A A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind A_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_A_of_lc_A
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

Lemma lc_set_A_of_lc_A :
forall A1,
  lc_A A1 ->
  lc_set_A A1.
Proof.
intros A1; intros;
pose proof (lc_set_A_of_lc_A_size_mutual (size_A A1));
intuition eauto.
Qed.

Hint Resolve lc_set_A_of_lc_A : lngen.

(* begin hide *)

Lemma lc_set_Tcov_of_lc_Tcov_size_mutual :
forall i1,
(forall Tcov1,
  size_Tcov Tcov1 = i1 ->
  lc_Tcov Tcov1 ->
  lc_set_Tcov Tcov1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind Tcov_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_A_of_lc_A
 | apply lc_set_Tcov_of_lc_Tcov
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

Lemma lc_set_Tcov_of_lc_Tcov :
forall Tcov1,
  lc_Tcov Tcov1 ->
  lc_set_Tcov Tcov1.
Proof.
intros Tcov1; intros;
pose proof (lc_set_Tcov_of_lc_Tcov_size_mutual (size_Tcov Tcov1));
intuition eauto.
Qed.

Hint Resolve lc_set_Tcov_of_lc_Tcov : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_A_wrt_A_rec_degree_A_wrt_A_mutual :
(forall A1 X1 n1,
  degree_A_wrt_A n1 A1 ->
  X1 `notin` typefv_A A1 ->
  close_A_wrt_A_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_A_wrt_A_rec_degree_A_wrt_A :
forall A1 X1 n1,
  degree_A_wrt_A n1 A1 ->
  X1 `notin` typefv_A A1 ->
  close_A_wrt_A_rec n1 X1 A1 = A1.
Proof.
pose proof close_A_wrt_A_rec_degree_A_wrt_A_mutual as H; intuition eauto.
Qed.

Hint Resolve close_A_wrt_A_rec_degree_A_wrt_A : lngen.
Hint Rewrite close_A_wrt_A_rec_degree_A_wrt_A using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_Tcov_wrt_A_rec_degree_Tcov_wrt_A_mutual :
(forall Tcov1 X1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  X1 `notin` typefv_Tcov Tcov1 ->
  close_Tcov_wrt_A_rec n1 X1 Tcov1 = Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_Tcov_wrt_A_rec_degree_Tcov_wrt_A :
forall Tcov1 X1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  X1 `notin` typefv_Tcov Tcov1 ->
  close_Tcov_wrt_A_rec n1 X1 Tcov1 = Tcov1.
Proof.
pose proof close_Tcov_wrt_A_rec_degree_Tcov_wrt_A_mutual as H; intuition eauto.
Qed.

Hint Resolve close_Tcov_wrt_A_rec_degree_Tcov_wrt_A : lngen.
Hint Rewrite close_Tcov_wrt_A_rec_degree_Tcov_wrt_A using solve [auto] : lngen.

(* end hide *)

Lemma close_A_wrt_A_lc_A :
forall A1 X1,
  lc_A A1 ->
  X1 `notin` typefv_A A1 ->
  close_A_wrt_A X1 A1 = A1.
Proof.
unfold close_A_wrt_A; default_simp.
Qed.

Hint Resolve close_A_wrt_A_lc_A : lngen.
Hint Rewrite close_A_wrt_A_lc_A using solve [auto] : lngen.

Lemma close_Tcov_wrt_A_lc_Tcov :
forall Tcov1 X1,
  lc_Tcov Tcov1 ->
  X1 `notin` typefv_Tcov Tcov1 ->
  close_Tcov_wrt_A X1 Tcov1 = Tcov1.
Proof.
unfold close_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve close_Tcov_wrt_A_lc_Tcov : lngen.
Hint Rewrite close_Tcov_wrt_A_lc_Tcov using solve [auto] : lngen.

(* begin hide *)

Lemma open_A_wrt_A_rec_degree_A_wrt_A_mutual :
(forall A2 A1 n1,
  degree_A_wrt_A n1 A2 ->
  open_A_wrt_A_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_A_wrt_A_rec_degree_A_wrt_A :
forall A2 A1 n1,
  degree_A_wrt_A n1 A2 ->
  open_A_wrt_A_rec n1 A1 A2 = A2.
Proof.
pose proof open_A_wrt_A_rec_degree_A_wrt_A_mutual as H; intuition eauto.
Qed.

Hint Resolve open_A_wrt_A_rec_degree_A_wrt_A : lngen.
Hint Rewrite open_A_wrt_A_rec_degree_A_wrt_A using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_Tcov_wrt_A_rec_degree_Tcov_wrt_A_mutual :
(forall Tcov1 A1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  open_Tcov_wrt_A_rec n1 A1 Tcov1 = Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_Tcov_wrt_A_rec_degree_Tcov_wrt_A :
forall Tcov1 A1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  open_Tcov_wrt_A_rec n1 A1 Tcov1 = Tcov1.
Proof.
pose proof open_Tcov_wrt_A_rec_degree_Tcov_wrt_A_mutual as H; intuition eauto.
Qed.

Hint Resolve open_Tcov_wrt_A_rec_degree_Tcov_wrt_A : lngen.
Hint Rewrite open_Tcov_wrt_A_rec_degree_Tcov_wrt_A using solve [auto] : lngen.

(* end hide *)

Lemma open_A_wrt_A_lc_A :
forall A2 A1,
  lc_A A2 ->
  open_A_wrt_A A2 A1 = A2.
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve open_A_wrt_A_lc_A : lngen.
Hint Rewrite open_A_wrt_A_lc_A using solve [auto] : lngen.

Lemma open_Tcov_wrt_A_lc_Tcov :
forall Tcov1 A1,
  lc_Tcov Tcov1 ->
  open_Tcov_wrt_A Tcov1 A1 = Tcov1.
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve open_Tcov_wrt_A_lc_Tcov : lngen.
Hint Rewrite open_Tcov_wrt_A_lc_Tcov using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typefv_A_close_A_wrt_A_rec_mutual :
(forall A1 X1 n1,
  typefv_A (close_A_wrt_A_rec n1 X1 A1) [=] remove X1 (typefv_A A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_A_close_A_wrt_A_rec :
forall A1 X1 n1,
  typefv_A (close_A_wrt_A_rec n1 X1 A1) [=] remove X1 (typefv_A A1).
Proof.
pose proof typefv_A_close_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_close_A_wrt_A_rec : lngen.
Hint Rewrite typefv_A_close_A_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_Tcov_close_Tcov_wrt_A_rec_mutual :
(forall Tcov1 X1 n1,
  typefv_Tcov (close_Tcov_wrt_A_rec n1 X1 Tcov1) [=] remove X1 (typefv_Tcov Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_Tcov_close_Tcov_wrt_A_rec :
forall Tcov1 X1 n1,
  typefv_Tcov (close_Tcov_wrt_A_rec n1 X1 Tcov1) [=] remove X1 (typefv_Tcov Tcov1).
Proof.
pose proof typefv_Tcov_close_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_close_Tcov_wrt_A_rec : lngen.
Hint Rewrite typefv_Tcov_close_Tcov_wrt_A_rec using solve [auto] : lngen.

(* end hide *)

Lemma typefv_A_close_A_wrt_A :
forall A1 X1,
  typefv_A (close_A_wrt_A X1 A1) [=] remove X1 (typefv_A A1).
Proof.
unfold close_A_wrt_A; default_simp.
Qed.

Hint Resolve typefv_A_close_A_wrt_A : lngen.
Hint Rewrite typefv_A_close_A_wrt_A using solve [auto] : lngen.

Lemma typefv_Tcov_close_Tcov_wrt_A :
forall Tcov1 X1,
  typefv_Tcov (close_Tcov_wrt_A X1 Tcov1) [=] remove X1 (typefv_Tcov Tcov1).
Proof.
unfold close_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typefv_Tcov_close_Tcov_wrt_A : lngen.
Hint Rewrite typefv_Tcov_close_Tcov_wrt_A using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_A_open_A_wrt_A_rec_lower_mutual :
(forall A1 A2 n1,
  typefv_A A1 [<=] typefv_A (open_A_wrt_A_rec n1 A2 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_A_open_A_wrt_A_rec_lower :
forall A1 A2 n1,
  typefv_A A1 [<=] typefv_A (open_A_wrt_A_rec n1 A2 A1).
Proof.
pose proof typefv_A_open_A_wrt_A_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_open_A_wrt_A_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_Tcov_open_Tcov_wrt_A_rec_lower_mutual :
(forall Tcov1 A1 n1,
  typefv_Tcov Tcov1 [<=] typefv_Tcov (open_Tcov_wrt_A_rec n1 A1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_Tcov_open_Tcov_wrt_A_rec_lower :
forall Tcov1 A1 n1,
  typefv_Tcov Tcov1 [<=] typefv_Tcov (open_Tcov_wrt_A_rec n1 A1 Tcov1).
Proof.
pose proof typefv_Tcov_open_Tcov_wrt_A_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_open_Tcov_wrt_A_rec_lower : lngen.

(* end hide *)

Lemma typefv_A_open_A_wrt_A_lower :
forall A1 A2,
  typefv_A A1 [<=] typefv_A (open_A_wrt_A A1 A2).
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve typefv_A_open_A_wrt_A_lower : lngen.

Lemma typefv_Tcov_open_Tcov_wrt_A_lower :
forall Tcov1 A1,
  typefv_Tcov Tcov1 [<=] typefv_Tcov (open_Tcov_wrt_A Tcov1 A1).
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typefv_Tcov_open_Tcov_wrt_A_lower : lngen.

(* begin hide *)

Lemma typefv_A_open_A_wrt_A_rec_upper_mutual :
(forall A1 A2 n1,
  typefv_A (open_A_wrt_A_rec n1 A2 A1) [<=] typefv_A A2 `union` typefv_A A1).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_A_open_A_wrt_A_rec_upper :
forall A1 A2 n1,
  typefv_A (open_A_wrt_A_rec n1 A2 A1) [<=] typefv_A A2 `union` typefv_A A1.
Proof.
pose proof typefv_A_open_A_wrt_A_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_open_A_wrt_A_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_Tcov_open_Tcov_wrt_A_rec_upper_mutual :
(forall Tcov1 A1 n1,
  typefv_Tcov (open_Tcov_wrt_A_rec n1 A1 Tcov1) [<=] typefv_A A1 `union` typefv_Tcov Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma typefv_Tcov_open_Tcov_wrt_A_rec_upper :
forall Tcov1 A1 n1,
  typefv_Tcov (open_Tcov_wrt_A_rec n1 A1 Tcov1) [<=] typefv_A A1 `union` typefv_Tcov Tcov1.
Proof.
pose proof typefv_Tcov_open_Tcov_wrt_A_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_open_Tcov_wrt_A_rec_upper : lngen.

(* end hide *)

Lemma typefv_A_open_A_wrt_A_upper :
forall A1 A2,
  typefv_A (open_A_wrt_A A1 A2) [<=] typefv_A A2 `union` typefv_A A1.
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve typefv_A_open_A_wrt_A_upper : lngen.

Lemma typefv_Tcov_open_Tcov_wrt_A_upper :
forall Tcov1 A1,
  typefv_Tcov (open_Tcov_wrt_A Tcov1 A1) [<=] typefv_A A1 `union` typefv_Tcov Tcov1.
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typefv_Tcov_open_Tcov_wrt_A_upper : lngen.

(* begin hide *)

Lemma typefv_A_typsubst_A_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` typefv_A A1 ->
  typefv_A (typsubst_A A2 X1 A1) [=] typefv_A A1).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_A_typsubst_A_fresh :
forall A1 A2 X1,
  X1 `notin` typefv_A A1 ->
  typefv_A (typsubst_A A2 X1 A1) [=] typefv_A A1.
Proof.
pose proof typefv_A_typsubst_A_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_typsubst_A_fresh : lngen.
Hint Rewrite typefv_A_typsubst_A_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_Tcov_typsubst_Tcov_fresh_mutual :
(forall Tcov1 A1 X1,
  X1 `notin` typefv_Tcov Tcov1 ->
  typefv_Tcov (typsubst_Tcov A1 X1 Tcov1) [=] typefv_Tcov Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Tcov_typsubst_Tcov_fresh :
forall Tcov1 A1 X1,
  X1 `notin` typefv_Tcov Tcov1 ->
  typefv_Tcov (typsubst_Tcov A1 X1 Tcov1) [=] typefv_Tcov Tcov1.
Proof.
pose proof typefv_Tcov_typsubst_Tcov_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_typsubst_Tcov_fresh : lngen.
Hint Rewrite typefv_Tcov_typsubst_Tcov_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_A_typsubst_A_lower_mutual :
(forall A1 A2 X1,
  remove X1 (typefv_A A1) [<=] typefv_A (typsubst_A A2 X1 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_A_typsubst_A_lower :
forall A1 A2 X1,
  remove X1 (typefv_A A1) [<=] typefv_A (typsubst_A A2 X1 A1).
Proof.
pose proof typefv_A_typsubst_A_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_typsubst_A_lower : lngen.

(* begin hide *)

Lemma typefv_Tcov_typsubst_Tcov_lower_mutual :
(forall Tcov1 A1 X1,
  remove X1 (typefv_Tcov Tcov1) [<=] typefv_Tcov (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Tcov_typsubst_Tcov_lower :
forall Tcov1 A1 X1,
  remove X1 (typefv_Tcov Tcov1) [<=] typefv_Tcov (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typefv_Tcov_typsubst_Tcov_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_typsubst_Tcov_lower : lngen.

(* begin hide *)

Lemma typefv_A_typsubst_A_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` typefv_A A1 ->
  X2 `notin` typefv_A A2 ->
  X2 `notin` typefv_A (typsubst_A A2 X1 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_A_typsubst_A_notin :
forall A1 A2 X1 X2,
  X2 `notin` typefv_A A1 ->
  X2 `notin` typefv_A A2 ->
  X2 `notin` typefv_A (typsubst_A A2 X1 A1).
Proof.
pose proof typefv_A_typsubst_A_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_typsubst_A_notin : lngen.

(* begin hide *)

Lemma typefv_Tcov_typsubst_Tcov_notin_mutual :
(forall Tcov1 A1 X1 X2,
  X2 `notin` typefv_Tcov Tcov1 ->
  X2 `notin` typefv_A A1 ->
  X2 `notin` typefv_Tcov (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Tcov_typsubst_Tcov_notin :
forall Tcov1 A1 X1 X2,
  X2 `notin` typefv_Tcov Tcov1 ->
  X2 `notin` typefv_A A1 ->
  X2 `notin` typefv_Tcov (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typefv_Tcov_typsubst_Tcov_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_typsubst_Tcov_notin : lngen.

(* begin hide *)

Lemma typefv_A_typsubst_A_upper_mutual :
(forall A1 A2 X1,
  typefv_A (typsubst_A A2 X1 A1) [<=] typefv_A A2 `union` remove X1 (typefv_A A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_A_typsubst_A_upper :
forall A1 A2 X1,
  typefv_A (typsubst_A A2 X1 A1) [<=] typefv_A A2 `union` remove X1 (typefv_A A1).
Proof.
pose proof typefv_A_typsubst_A_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_A_typsubst_A_upper : lngen.

(* begin hide *)

Lemma typefv_Tcov_typsubst_Tcov_upper_mutual :
(forall Tcov1 A1 X1,
  typefv_Tcov (typsubst_Tcov A1 X1 Tcov1) [<=] typefv_A A1 `union` remove X1 (typefv_Tcov Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma typefv_Tcov_typsubst_Tcov_upper :
forall Tcov1 A1 X1,
  typefv_Tcov (typsubst_Tcov A1 X1 Tcov1) [<=] typefv_A A1 `union` remove X1 (typefv_Tcov Tcov1).
Proof.
pose proof typefv_Tcov_typsubst_Tcov_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve typefv_Tcov_typsubst_Tcov_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typsubst_A_close_A_wrt_A_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_A_wrt_A n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_A A1 ->
  typsubst_A A1 X1 (close_A_wrt_A_rec n1 X2 A2) = close_A_wrt_A_rec n1 X2 (typsubst_A A1 X1 A2)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_close_A_wrt_A_rec :
forall A2 A1 X1 X2 n1,
  degree_A_wrt_A n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_A A1 ->
  typsubst_A A1 X1 (close_A_wrt_A_rec n1 X2 A2) = close_A_wrt_A_rec n1 X2 (typsubst_A A1 X1 A2).
Proof.
pose proof typsubst_A_close_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_close_A_wrt_A_rec : lngen.

(* begin hide *)

Lemma typsubst_Tcov_close_Tcov_wrt_A_rec_mutual :
(forall Tcov1 A1 X1 X2 n1,
  degree_A_wrt_A n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_A A1 ->
  typsubst_Tcov A1 X1 (close_Tcov_wrt_A_rec n1 X2 Tcov1) = close_Tcov_wrt_A_rec n1 X2 (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_close_Tcov_wrt_A_rec :
forall Tcov1 A1 X1 X2 n1,
  degree_A_wrt_A n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_A A1 ->
  typsubst_Tcov A1 X1 (close_Tcov_wrt_A_rec n1 X2 Tcov1) = close_Tcov_wrt_A_rec n1 X2 (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typsubst_Tcov_close_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_close_Tcov_wrt_A_rec : lngen.

Lemma typsubst_A_close_A_wrt_A :
forall A2 A1 X1 X2,
  lc_A A1 ->  X1 <> X2 ->
  X2 `notin` typefv_A A1 ->
  typsubst_A A1 X1 (close_A_wrt_A X2 A2) = close_A_wrt_A X2 (typsubst_A A1 X1 A2).
Proof.
unfold close_A_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_A_close_A_wrt_A : lngen.

Lemma typsubst_Tcov_close_Tcov_wrt_A :
forall Tcov1 A1 X1 X2,
  lc_A A1 ->  X1 <> X2 ->
  X2 `notin` typefv_A A1 ->
  typsubst_Tcov A1 X1 (close_Tcov_wrt_A X2 Tcov1) = close_Tcov_wrt_A X2 (typsubst_Tcov A1 X1 Tcov1).
Proof.
unfold close_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_Tcov_close_Tcov_wrt_A : lngen.

(* begin hide *)

Lemma typsubst_A_degree_A_wrt_A_mutual :
(forall A1 A2 X1 n1,
  degree_A_wrt_A n1 A1 ->
  degree_A_wrt_A n1 A2 ->
  degree_A_wrt_A n1 (typsubst_A A2 X1 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_degree_A_wrt_A :
forall A1 A2 X1 n1,
  degree_A_wrt_A n1 A1 ->
  degree_A_wrt_A n1 A2 ->
  degree_A_wrt_A n1 (typsubst_A A2 X1 A1).
Proof.
pose proof typsubst_A_degree_A_wrt_A_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_degree_A_wrt_A : lngen.

(* begin hide *)

Lemma typsubst_Tcov_degree_Tcov_wrt_A_mutual :
(forall Tcov1 A1 X1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  degree_A_wrt_A n1 A1 ->
  degree_Tcov_wrt_A n1 (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_degree_Tcov_wrt_A :
forall Tcov1 A1 X1 n1,
  degree_Tcov_wrt_A n1 Tcov1 ->
  degree_A_wrt_A n1 A1 ->
  degree_Tcov_wrt_A n1 (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typsubst_Tcov_degree_Tcov_wrt_A_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_degree_Tcov_wrt_A : lngen.

(* begin hide *)

Lemma typsubst_A_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_A A2 ->
  typsubst_A A1 X1 A2 = A2).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_fresh_eq :
forall A2 A1 X1,
  X1 `notin` typefv_A A2 ->
  typsubst_A A1 X1 A2 = A2.
Proof.
pose proof typsubst_A_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_fresh_eq : lngen.
Hint Rewrite typsubst_A_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_Tcov_fresh_eq_mutual :
(forall Tcov1 A1 X1,
  X1 `notin` typefv_Tcov Tcov1 ->
  typsubst_Tcov A1 X1 Tcov1 = Tcov1).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_fresh_eq :
forall Tcov1 A1 X1,
  X1 `notin` typefv_Tcov Tcov1 ->
  typsubst_Tcov A1 X1 Tcov1 = Tcov1.
Proof.
pose proof typsubst_Tcov_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_fresh_eq : lngen.
Hint Rewrite typsubst_Tcov_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_A_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_A (typsubst_A A1 X1 A2)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_fresh_same :
forall A2 A1 X1,
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_A (typsubst_A A1 X1 A2).
Proof.
pose proof typsubst_A_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_Tcov_fresh_same_mutual :
(forall Tcov1 A1 X1,
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_Tcov (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_fresh_same :
forall Tcov1 A1 X1,
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_Tcov (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typsubst_Tcov_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_A_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` typefv_A A2 ->
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_A (typsubst_A A1 X2 A2)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_fresh :
forall A2 A1 X1 X2,
  X1 `notin` typefv_A A2 ->
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_A (typsubst_A A1 X2 A2).
Proof.
pose proof typsubst_A_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_fresh : lngen.

(* begin hide *)

Lemma typsubst_Tcov_fresh_mutual :
(forall Tcov1 A1 X1 X2,
  X1 `notin` typefv_Tcov Tcov1 ->
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_Tcov (typsubst_Tcov A1 X2 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_fresh :
forall Tcov1 A1 X1 X2,
  X1 `notin` typefv_Tcov Tcov1 ->
  X1 `notin` typefv_A A1 ->
  X1 `notin` typefv_Tcov (typsubst_Tcov A1 X2 Tcov1).
Proof.
pose proof typsubst_Tcov_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_fresh : lngen.

Lemma typsubst_A_lc_A :
forall A1 A2 X1,
  lc_A A1 ->
  lc_A A2 ->
  lc_A (typsubst_A A2 X1 A1).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_A_lc_A : lngen.

Lemma typsubst_Tcov_lc_Tcov :
forall Tcov1 A1 X1,
  lc_Tcov Tcov1 ->
  lc_A A1 ->
  lc_Tcov (typsubst_Tcov A1 X1 Tcov1).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_Tcov_lc_Tcov : lngen.

(* begin hide *)

Lemma typsubst_A_open_A_wrt_A_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_A A1 ->
  typsubst_A A1 X1 (open_A_wrt_A_rec n1 A2 A3) = open_A_wrt_A_rec n1 (typsubst_A A1 X1 A2) (typsubst_A A1 X1 A3)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_A_open_A_wrt_A_rec :
forall A3 A1 A2 X1 n1,
  lc_A A1 ->
  typsubst_A A1 X1 (open_A_wrt_A_rec n1 A2 A3) = open_A_wrt_A_rec n1 (typsubst_A A1 X1 A2) (typsubst_A A1 X1 A3).
Proof.
pose proof typsubst_A_open_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_open_A_wrt_A_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_Tcov_open_Tcov_wrt_A_rec_mutual :
(forall Tcov1 A1 A2 X1 n1,
  lc_A A1 ->
  typsubst_Tcov A1 X1 (open_Tcov_wrt_A_rec n1 A2 Tcov1) = open_Tcov_wrt_A_rec n1 (typsubst_A A1 X1 A2) (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_Tcov_open_Tcov_wrt_A_rec :
forall Tcov1 A1 A2 X1 n1,
  lc_A A1 ->
  typsubst_Tcov A1 X1 (open_Tcov_wrt_A_rec n1 A2 Tcov1) = open_Tcov_wrt_A_rec n1 (typsubst_A A1 X1 A2) (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typsubst_Tcov_open_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_open_Tcov_wrt_A_rec : lngen.

(* end hide *)

Lemma typsubst_A_open_A_wrt_A :
forall A3 A1 A2 X1,
  lc_A A1 ->
  typsubst_A A1 X1 (open_A_wrt_A A3 A2) = open_A_wrt_A (typsubst_A A1 X1 A3) (typsubst_A A1 X1 A2).
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_A_open_A_wrt_A : lngen.

Lemma typsubst_Tcov_open_Tcov_wrt_A :
forall Tcov1 A1 A2 X1,
  lc_A A1 ->
  typsubst_Tcov A1 X1 (open_Tcov_wrt_A Tcov1 A2) = open_Tcov_wrt_A (typsubst_Tcov A1 X1 Tcov1) (typsubst_A A1 X1 A2).
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_Tcov_open_Tcov_wrt_A : lngen.

Lemma typsubst_A_open_A_wrt_A_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_A A1 ->
  open_A_wrt_A (typsubst_A A1 X1 A2) (t_tvar_f X2) = typsubst_A A1 X1 (open_A_wrt_A A2 (t_tvar_f X2)).
Proof.
intros; rewrite typsubst_A_open_A_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_A_open_A_wrt_A_var : lngen.

Lemma typsubst_Tcov_open_Tcov_wrt_A_var :
forall Tcov1 A1 X1 X2,
  X1 <> X2 ->
  lc_A A1 ->
  open_Tcov_wrt_A (typsubst_Tcov A1 X1 Tcov1) (t_tvar_f X2) = typsubst_Tcov A1 X1 (open_Tcov_wrt_A Tcov1 (t_tvar_f X2)).
Proof.
intros; rewrite typsubst_Tcov_open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_Tcov_open_Tcov_wrt_A_var : lngen.

(* begin hide *)

Lemma typsubst_A_spec_rec_mutual :
(forall A1 A2 X1 n1,
  typsubst_A A2 X1 A1 = open_A_wrt_A_rec n1 A2 (close_A_wrt_A_rec n1 X1 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_A_spec_rec :
forall A1 A2 X1 n1,
  typsubst_A A2 X1 A1 = open_A_wrt_A_rec n1 A2 (close_A_wrt_A_rec n1 X1 A1).
Proof.
pose proof typsubst_A_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_Tcov_spec_rec_mutual :
(forall Tcov1 A1 X1 n1,
  typsubst_Tcov A1 X1 Tcov1 = open_Tcov_wrt_A_rec n1 A1 (close_Tcov_wrt_A_rec n1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_Tcov_spec_rec :
forall Tcov1 A1 X1 n1,
  typsubst_Tcov A1 X1 Tcov1 = open_Tcov_wrt_A_rec n1 A1 (close_Tcov_wrt_A_rec n1 X1 Tcov1).
Proof.
pose proof typsubst_Tcov_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_spec_rec : lngen.

(* end hide *)

Lemma typsubst_A_spec :
forall A1 A2 X1,
  typsubst_A A2 X1 A1 = open_A_wrt_A (close_A_wrt_A X1 A1) A2.
Proof.
unfold close_A_wrt_A; unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_A_spec : lngen.

Lemma typsubst_Tcov_spec :
forall Tcov1 A1 X1,
  typsubst_Tcov A1 X1 Tcov1 = open_Tcov_wrt_A (close_Tcov_wrt_A X1 Tcov1) A1.
Proof.
unfold close_Tcov_wrt_A; unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_Tcov_spec : lngen.

(* begin hide *)

Lemma typsubst_A_typsubst_A_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_A A2 ->
  X2 <> X1 ->
  typsubst_A A2 X1 (typsubst_A A3 X2 A1) = typsubst_A (typsubst_A A2 X1 A3) X2 (typsubst_A A2 X1 A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_typsubst_A :
forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_A A2 ->
  X2 <> X1 ->
  typsubst_A A2 X1 (typsubst_A A3 X2 A1) = typsubst_A (typsubst_A A2 X1 A3) X2 (typsubst_A A2 X1 A1).
Proof.
pose proof typsubst_A_typsubst_A_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_typsubst_A : lngen.

(* begin hide *)

Lemma typsubst_Tcov_typsubst_Tcov_mutual :
(forall Tcov1 A1 A2 X2 X1,
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  typsubst_Tcov A1 X1 (typsubst_Tcov A2 X2 Tcov1) = typsubst_Tcov (typsubst_A A1 X1 A2) X2 (typsubst_Tcov A1 X1 Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_typsubst_Tcov :
forall Tcov1 A1 A2 X2 X1,
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  typsubst_Tcov A1 X1 (typsubst_Tcov A2 X2 Tcov1) = typsubst_Tcov (typsubst_A A1 X1 A2) X2 (typsubst_Tcov A1 X1 Tcov1).
Proof.
pose proof typsubst_Tcov_typsubst_Tcov_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_typsubst_Tcov : lngen.

(* begin hide *)

Lemma typsubst_A_close_A_wrt_A_rec_open_A_wrt_A_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_A A2 ->
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  degree_A_wrt_A n1 A1 ->
  typsubst_A A1 X1 A2 = close_A_wrt_A_rec n1 X2 (typsubst_A A1 X1 (open_A_wrt_A_rec n1 (t_tvar_f X2) A2))).
Proof.
apply_mutual_ind A_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_A_close_A_wrt_A_rec_open_A_wrt_A_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_A A2 ->
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  degree_A_wrt_A n1 A1 ->
  typsubst_A A1 X1 A2 = close_A_wrt_A_rec n1 X2 (typsubst_A A1 X1 (open_A_wrt_A_rec n1 (t_tvar_f X2) A2)).
Proof.
pose proof typsubst_A_close_A_wrt_A_rec_open_A_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_close_A_wrt_A_rec_open_A_wrt_A_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_Tcov_close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec_mutual :
(forall Tcov1 A1 X1 X2 n1,
  X2 `notin` typefv_Tcov Tcov1 ->
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  degree_A_wrt_A n1 A1 ->
  typsubst_Tcov A1 X1 Tcov1 = close_Tcov_wrt_A_rec n1 X2 (typsubst_Tcov A1 X1 (open_Tcov_wrt_A_rec n1 (t_tvar_f X2) Tcov1))).
Proof.
apply_mutual_ind Tcov_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma typsubst_Tcov_close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec :
forall Tcov1 A1 X1 X2 n1,
  X2 `notin` typefv_Tcov Tcov1 ->
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  degree_A_wrt_A n1 A1 ->
  typsubst_Tcov A1 X1 Tcov1 = close_Tcov_wrt_A_rec n1 X2 (typsubst_Tcov A1 X1 (open_Tcov_wrt_A_rec n1 (t_tvar_f X2) Tcov1)).
Proof.
pose proof typsubst_Tcov_close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_close_Tcov_wrt_A_rec_open_Tcov_wrt_A_rec : lngen.

(* end hide *)

Lemma typsubst_A_close_A_wrt_A_open_A_wrt_A :
forall A2 A1 X1 X2,
  X2 `notin` typefv_A A2 ->
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  lc_A A1 ->
  typsubst_A A1 X1 A2 = close_A_wrt_A X2 (typsubst_A A1 X1 (open_A_wrt_A A2 (t_tvar_f X2))).
Proof.
unfold close_A_wrt_A; unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_A_close_A_wrt_A_open_A_wrt_A : lngen.

Lemma typsubst_Tcov_close_Tcov_wrt_A_open_Tcov_wrt_A :
forall Tcov1 A1 X1 X2,
  X2 `notin` typefv_Tcov Tcov1 ->
  X2 `notin` typefv_A A1 ->
  X2 <> X1 ->
  lc_A A1 ->
  typsubst_Tcov A1 X1 Tcov1 = close_Tcov_wrt_A X2 (typsubst_Tcov A1 X1 (open_Tcov_wrt_A Tcov1 (t_tvar_f X2))).
Proof.
unfold close_Tcov_wrt_A; unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_Tcov_close_Tcov_wrt_A_open_Tcov_wrt_A : lngen.

Lemma typsubst_A_t_forall :
forall X2 B1 A1 X1,
  lc_A A1 ->
  X2 `notin` typefv_A A1 `union` typefv_A B1 `union` singleton X1 ->
  typsubst_A A1 X1 (t_forall B1) = t_forall (close_A_wrt_A X2 (typsubst_A A1 X1 (open_A_wrt_A B1 (t_tvar_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve typsubst_A_t_forall : lngen.

(* begin hide *)

Lemma typsubst_A_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` typefv_A A1 ->
  open_A_wrt_A_rec n1 A2 A1 = typsubst_A A2 X1 (open_A_wrt_A_rec n1 (t_tvar_f X1) A1)).
Proof.
apply_mutual_ind A_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_A_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` typefv_A A1 ->
  open_A_wrt_A_rec n1 A2 A1 = typsubst_A A2 X1 (open_A_wrt_A_rec n1 (t_tvar_f X1) A1).
Proof.
pose proof typsubst_A_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_A_intro_rec : lngen.
Hint Rewrite typsubst_A_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_Tcov_intro_rec_mutual :
(forall Tcov1 X1 A1 n1,
  X1 `notin` typefv_Tcov Tcov1 ->
  open_Tcov_wrt_A_rec n1 A1 Tcov1 = typsubst_Tcov A1 X1 (open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1)).
Proof.
apply_mutual_ind Tcov_mutind;
default_simp.
Qed.

(* end hide *)

Lemma typsubst_Tcov_intro_rec :
forall Tcov1 X1 A1 n1,
  X1 `notin` typefv_Tcov Tcov1 ->
  open_Tcov_wrt_A_rec n1 A1 Tcov1 = typsubst_Tcov A1 X1 (open_Tcov_wrt_A_rec n1 (t_tvar_f X1) Tcov1).
Proof.
pose proof typsubst_Tcov_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve typsubst_Tcov_intro_rec : lngen.
Hint Rewrite typsubst_Tcov_intro_rec using solve [auto] : lngen.

Lemma typsubst_A_intro :
forall X1 A1 A2,
  X1 `notin` typefv_A A1 ->
  open_A_wrt_A A1 A2 = typsubst_A A2 X1 (open_A_wrt_A A1 (t_tvar_f X1)).
Proof.
unfold open_A_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_A_intro : lngen.

Lemma typsubst_Tcov_intro :
forall X1 Tcov1 A1,
  X1 `notin` typefv_Tcov Tcov1 ->
  open_Tcov_wrt_A Tcov1 A1 = typsubst_Tcov A1 X1 (open_Tcov_wrt_A Tcov1 (t_tvar_f X1)).
Proof.
unfold open_Tcov_wrt_A; default_simp.
Qed.

Hint Resolve typsubst_Tcov_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
