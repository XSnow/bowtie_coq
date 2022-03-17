Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.

(* Two types are sim iff they are splu from a value type *)
Lemma sim_no_distinguishability : forall A B,
    sim A B -> Distinguishability A B -> False.
Proof with solve_false.
  introv Sim Dis.
  induction Sim; intros.
  - induction Dis; try inverts_typ...
    + inverts H...
    + inverts H1...
  - forwards* : distinguishability_rcd_inv Dis.
  - inverts Dis...
  - inverts Dis...
Qed.

Lemma dispatch_gen : forall (A1 A2 B B' C1 C2' : typ),
    Mergeability A1 A2 ->
    ApplyTy A1 B C1 -> NApplyTy A1 B' -> ApplyTy A2 B' C2' ->
    NApplyTy A2 B -> (* this premise is not on the paper def *)
    Distinguishability B B'.
Proof with elia; solve_false.
  (* introv Val1 Val2 App1 PSub App2. *)
  (* indTypSize (size_typ V + size_typ V' + size_typ A). *)
  (* lets~ [Hu|(?&?&Hu)]: ordu_or_split V'. *)
  (* lets~ [Hu'|(?&?&Hu')]: ordu_or_split V. *)
Admitted.

(* This is equivalent to the dispatch lemma w/o ordu constraints *)
Lemma applyty_merge_sim : forall A A' B B' x1 x2,
    Mergeability A A' -> sim B B' ->
    ApplyTy A B x1 -> ApplyTy A' B' x2 ->
    exists y, ApplyTy A' B y \/ ApplyTy A B' y.
Proof with solve_false.
  introv HM HS HA1 HA2.
  forwards* [(?&?)|?]: applyty_total A B'.
  forwards* [(?&?)|?]: applyty_total A' B.
  false. applys sim_no_distinguishability HS.
  applys* dispatch_gen HM.
Qed.

Lemma lemma_for_B16 : forall A A' V B1 B2 x1 x2,
    Mergeability A A' -> isValTyp V
    -> splu V B1 B2 -> ApplyTy A B1 x1 -> ApplyTy A' B2 x2 ->
    exists y, ApplyTy A' B1 y \/ ApplyTy A B2 y.
Proof.
  intros. applys~ applyty_merge_sim.
  - applys sim2similar.
    unfold similar. exists*.
  - eauto.
  - eauto.
Qed.

(* B.16 Inversion of Abstract Application to Value Types *)
(* Here we only consider V to be StackArg. Note that V can also be StackTypArg
but that case is trivial *)
Lemma applyty_valtyp_inter_inv : forall (A A' V B : typ),
    ApplyTy (A&A') V B -> isValTyp V -> TypeWF nil (A&A') ->
    exists B', ApplyTy A V B' \/ ApplyTy A' V B'.
Proof with solve_false.
  introv HA HV WF.
  indTypSize (size_typ V).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split V.
  - inverts HA... all: exists*.
  - inverts_typ.
    inverts* HA.
    forwards~ (?&[?|?]): IH H3; elia; forwards~ (?&[?|?]): IH H5; elia.
    1,4: exists*.
    * inverts WF. forwards~ (?&[?|?]): lemma_for_B16 H2 H1 H4.
      all: exists*.
    * inverts WF. forwards~ (?&[?|?]): lemma_for_B16 H2 H1 H4.
      all: exists*.
Qed.
