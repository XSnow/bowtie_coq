Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Export DistSubtyping.
Require Import LN_Lemmas.

(******** subtyping **********)

Lemma sub_dec : forall A B,
    lc_typ A -> lc_typ B -> declarative_subtyping A B \/ ~ (declarative_subtyping A B).
Proof.
  intros.
  forwards~ [?|?]: decidability A B.
  left. applys~ dsub2asub.
  right. intro HF. apply dsub2asub in HF. eauto.
Qed.

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

(******** appty **************)

#[export]
Hint Extern 0 =>
match goal with
| H: UnionOrdinaryFty (fty_StackArg _) |- _ => inverts H
end : FalseHd.

Ltac indTypFtySize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  repeat match goal with | [ h : Fty |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

Lemma orduFty_lc : forall Fty, UnionOrdinaryFty Fty -> lc_Fty Fty.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate orduFty_lc : core.

Lemma nappty_lc_1 : forall A B, NApplyTy A B -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma nappty_lc_2 : forall A B, NApplyTy A B -> lc_Fty B.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate nappty_lc_1 nappty_lc_2 : core.

Lemma nappty_splitu_inv : forall A B B1 B2,
    NApplyTy A (fty_StackArg B) -> splu B B1 B2 ->
    NApplyTy A (fty_StackArg B1) \/ NApplyTy A (fty_StackArg B2).
Proof.
  introv HN HS.
  inverts HN; solve_false; auto_unify; eauto.
  - (* arrow sub *)
    forwards* [?|?]: nsub_splitu H5 HS.
Qed.

Lemma appty_contradication : forall A B C,
    ApplyTy A B C -> NApplyTy A B -> False.
Proof with solve_false.
  introv HA HN.
  indTypFtySize (size_typ A + size_Fty B).

  inverts HA;
    match goal with
    | H1: NApplyTy _ (fty_StackArg ?B), H2: splu ?B _ _  |- _ =>
      forwards~ [?|?]: nappty_splitu_inv H1 H2
    | _ => inverts HN
    end...

  all: repeat match goal with
  | H1: ApplyTy (t_forall _) (fty_StackArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyFunTy
  | H1: ApplyTy (t_arrow _ _) (fty_StackTyArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyTyFunFty
  | H1: ApplyTy ?A ?B _, H2: NApplyTy ?A ?B |- _ => forwards: IH H2 H1; elia
              end.
Qed.

#[export] Hint Resolve appty_contradication : FalseHd.

Lemma appty_unique : forall A B C1 C2,
    ApplyTy A B C1 -> ApplyTy A B C2 -> C1 = C2.
Proof with solve_false; auto_unify; auto.
  introv HA1 HA2. gen C1 C2.
  indTypFtySize (size_typ A + size_Fty B).
  inverts HA1; inverts HA2...
  all: repeat match goal with
  | H1: ApplyTy ?A ?B _, H2: ApplyTy ?A ?B _ |- _ => forwards: IH H1 H2; elia; clear H1 H2
              end; subst~.
Qed.

Ltac auto_unify_2 :=
  auto_unify; (* unify split *)
  (* unify appty *)
  try repeat match goal with
         | [ H1: ApplyTy ?A ?B _ , H2: ApplyTy ?A ?B _ |- _ ] =>
           (forwards (?&?): appty_unique H1 H2;
            subst; clear H2)
             end.

Lemma ordu_or_split_Fty: forall F,
    lc_Fty F -> UnionOrdinaryFty F \/ exists A B C, F = fty_StackArg A /\ splu A B C.
Proof.
  introv HL.
  destruct~ HL.
  forwards* [?|(?&?&?)]: ordu_or_split A.
Qed.

Lemma appty_total : forall A F,
    lc_typ A -> lc_Fty F -> exists C, ApplyTy A F C \/ NApplyTy A F.
Proof.
  introv.
  indTypFtySize (size_typ A + size_Fty F).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F).
  - destruct* H.
    (* and / or *)
    all: try forwards~ (?&[?|?]): IH F A1; elia.
    all: try forwards~ (?&[?|?]): IH F A2; elia.
    all: eauto.

    (* arrow / forall *)
    all: destruct H0.
    2,3: solve [exists; right*].

    + destruct* (sub_dec A0 A).
    + eauto.

  - subst.
    forwards~ (?&[?|?]): IH (fty_StackArg x0) A; elia.
    forwards~ (?&[?|?]): IH (fty_StackArg x1) A; elia.
    all: eauto.

  Unshelve. all: apply t_top.
Qed.

Lemma monotonicity_appty_1 : forall A A' B C,
    ApplyTy A B C -> declarative_subtyping A' A -> exists C', declarative_subtyping C' C /\ ApplyTy A' B C'.

Lemma monotonicity_appty_2 : forall A B B' C,
    ApplyTy A B C -> declarative_subtyping B' B -> exists C', declarative_subtyping C' C /\ ApplyTy A B' C'.
