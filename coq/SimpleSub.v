Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export MatchTy.

Notation "A <p B"        := (PositiveSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Notation "A <n B"        := (NegativeSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

#[export]
Hint Extern 0 =>
match goal with
| H: isNegTyp (t_rcd _ _) |- _ => inverts H
end : FalseHd.

(*-------------------------- neg types and val types -------------------------*)

Lemma negtyp2valtyp : forall A,
    isNegTyp A -> isValTyp A.
Proof.
  introv Neg.
  induction* Neg.
Qed.

Lemma valtyp_merge : forall A A1 A2,
    spli A A1 A2 -> isValTyp A1 -> isValTyp A2 -> isValTyp A.
Proof.
  introv Spl Val1 Val2.
  induction Spl; inverts Val1; inverts Val2.
Abort. (* COUNTER EXAMPLE: In l V1 & In l V2 *)

#[export] Hint Immediate negtyp2valtyp : core.

Lemma negtyp_spli_inv : forall A A1 A2,
    isNegTyp A -> spli A A1 A2 -> isNegTyp A1 /\ isNegTyp A2.
Proof.
  introv Val Spl.
  induction Spl; inverts~ Val; split*.
  all: try forwards* (?&?): IHSpl.
Qed.

Lemma valtyp_spli_inv : forall A A1 A2,
    isValTyp A -> spli A A1 A2 -> isValTyp A1 /\ isValTyp A2.
Proof.
  introv Val Spl.
  induction Spl; inverts~ Val; split*.
  all: match goal with
         H1: spli ?A _ _, H2: isNegTyp ?A |- _ => forwards* (?&?): negtyp_spli_inv H2 H1
       end.
Qed.

Lemma negtyp_splu_inv : forall A A1 A2,
    isNegTyp A -> splu A A1 A2 -> isNegTyp A1 /\ isNegTyp A2.
Proof.
  introv Val Spl.
  induction Spl; inverts~ Val; split*.
  all: try forwards* (?&?): IHSpl.
Qed.

Lemma valtyp_splu_inv : forall A A1 A2,
    isValTyp A -> splu A A1 A2 -> isValTyp A1 /\ isValTyp A2.
Proof.
  introv Val Spl.
  induction Spl; inverts~ Val; split*.
  all: match goal with
         H1: splu ?A _ _, H2: isNegTyp ?A |- _ => forwards* (?&?): negtyp_splu_inv H2 H1
       end.
Qed.

Ltac inverts_typ :=
  match goal with
  | H1: isNegTyp (_ & _) |- _ => forwards~ (?&?): negtyp_spli_inv H1
  | H1: isNegTyp (_ | _) |- _ => forwards~ (?&?): negtyp_splu_inv H1
  | H1: isValTyp (_ & _) |- _ => inverts H1
  | H1: isValTyp (_ | _) |- _ => inverts H1
  | H1: isValTyp (t_rcd _ _) |- _ => inverts H1
  | H1: isNegTyp ?A, H2: spli ?A _ _ |- _ => forwards (?&?): negtyp_spli_inv H1 H2
  | H1: isNegTyp ?A, H2: splu ?A _ _ |- _ => forwards (?&?): negtyp_splu_inv H1 H2
  | H1: isValTyp ?A, H2: spli ?A _ _ |- _ => forwards (?&?): valtyp_spli_inv H1 H2
  | H1: isValTyp ?A, H2: splu ?A _ _ |- _ => forwards (?&?): valtyp_splu_inv H1 H2
  | H1: isValFty (fty_StackArg (_ & _)) |- _ => inverts H1
  | H1: isValFty (fty_StackArg (_ | _)) |- _ => inverts H1
  end.

Lemma psub_valtyp : forall A B,
    A <p B -> isValTyp A.
Proof.
  introv Sub.
  induction* Sub.
Qed.

#[export] Hint Immediate psub_valtyp : core.

Lemma nsub_valfty : forall A B,
    A <n B -> isValFty B.
Proof.
  introv H. induction~ H.
Qed.

Lemma nsub_valtyp : forall A B,
    A <n (fty_StackArg B) -> isValTyp B.
Proof.
  introv H. inductions H; eauto.
Qed.

#[export] Hint Immediate nsub_valfty nsub_valtyp : core.

(*-------------------------- psub inversion lemmas  -------------------------*)

Lemma psub_or_inv : forall V B1 B2,
    V <p B1 | B2 -> V <p B1 \/ V <p B2.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

Lemma psub_and_inv : forall V B1 B2,
    V <p B1 & B2 -> V <p B1 /\ V <p B2.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

Lemma psub_rcd_inv : forall V l B,
    V <p (t_rcd l B) -> exists A, V = t_rcd l A /\ A <p B.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

Lemma psub_rcd_left_inv : forall C l B,
    (t_rcd l B) <p C -> exists A, C = t_rcd l A /\ B <p A.
Proof.
  introv Sub.
  inverts* Sub. Abort.

Local Ltac inverts_psub H :=
  try forwards [?|?]: psub_or_inv H;
  try forwards (?&?): psub_and_inv H;
  try forwards (?&?&?): psub_rcd_inv H; subst.

(*-------------------------- psub admissible rules  -------------------------*)

Lemma psub_merge_intersection : forall A B B1 B2,
    spli B B1 B2 -> isValTyp A -> A <p B1 -> A <p B2 -> A <p B.
Proof.
  introv Spl Val Sub1 Sub2. gen A.
  induction* Spl; intros.
  - inverts_psub Sub1; inverts_psub Sub2; eauto.
  - inverts_psub Sub1; inverts_psub Sub2; eauto.
  - inverts_psub Sub1; inverts_psub Sub2; subst; eauto.
    injection H; intros; subst. inverts Val.
    forwards~: IHSpl x0.
Qed.

Lemma psub_spli_left : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A1 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A2.
  induction Sub; intros; eauto.
  - (* rcd *) inverts* Spl.
    + (* (Box_l V) B <p Box_l A *)
      inverts Val; solve_false.
    + inverts Val. forwards~: IHSub H4.
Qed.

Lemma psub_spli_right : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A2 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A1.
  induction Sub; intros; eauto.
  - (* rcd *) inverts* Spl.
    + (* (Box_l V) B <p Box_l A *)
      inverts Val; solve_false.
    + inverts Val. forwards~: IHSub H3.
Qed.

Lemma psub_splu_left : forall A B B1 B2,
    splu B B1 B2 -> A <p B1 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  all: inverts_psub Sub. eauto.
  - inverts_psub Sub. eauto.
Qed.

Lemma psub_splu_right : forall A B B1 B2,
    splu B B1 B2 -> A <p B2 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  all: inverts_psub Sub; eauto.
Qed.


Lemma psub_negtyp : forall V1 V2 A,
    V1 <p A -> isNegTyp V1 -> isNegTyp V2 -> V2 <p A.
Proof.
  introv Sub Neg1 Neg2. gen V2.
  induction Sub; try solve [inverts Neg1]; intros; eauto.
Qed.

Lemma psub_forall : forall A1 A2 B,
    (t_forall A1) <p B -> isValTyp (t_forall A2) -> (t_forall A2) <p B.
Proof.
  introv Sub.
  inductions Sub; eauto.
Qed.

Lemma psub_trans : forall A B C,
    A <p B -> B <p C -> A <p C.
Proof with try eassumption.
  introv Sub1 Sub2. gen A.
  induction Sub2; intros; eauto.
  - (* rcd at right *) inverts_psub Sub1. forwards: IHSub2...
    eauto.
Qed.

Lemma psub_rcd : forall la V B A,
    (t_rcd la V) <p B -> A <p V -> (t_rcd la A) <p B.
Proof.
  introv Sub1 Sub2. gen A.
  inductions Sub1; intros; eauto.
  forwards*: psub_trans Sub2 Sub1.
Qed.

Lemma psub_rcd_choose : forall la Va Vb A B,
    (t_rcd la Va) <p A -> (t_rcd la Vb) <p B -> (t_rcd la Vb) <p A \/ (t_rcd la Va) <p B.
Proof.
  introv Sub1 Sub2. gen Vb B.
  inductions Sub1; intros; eauto.
Abort.

Lemma psub_merge_union : forall A A1 A2 B,
    splu A A1 A2 -> isValTyp A -> A1 <p B -> A2 <p B -> A <p B.
Proof with try eassumption; elia.
  introv Spl Val Sub1 Sub2.
  indTypFtySize (size_typ A + size_typ B).
  inverts Spl; intros.
  - (* union at left *) inverts_typ. applys~ psub_negtyp Sub1.
  - (* inter at left *) inverts_typ. inverts_typ.
    applys~ psub_negtyp Sub1.
  - (* inter at left *) inverts_typ. inverts_typ.
    applys~ psub_negtyp Sub1.
Qed.
(*   - (* forall *) applys~ psub_forall Sub1. *)
(*   -(* record *) *)
(*     inverts Sub1; try inverts_typ; eauto. *)
(*     + inverts_psub Sub2. injection H0; intros; subst~. *)
(*       forwards: IH H... eauto. *)
(*     + inverts_psub Sub2. *)
(*       * applys~ PSub_UnionL. applys* IH H2 H1... *)
(* (*  COUNTER EXAMPLE: Box_l (Box_r1 T | Box_r2 T) <p Box_l Box_r1 T | Box_l Box_r2 T *) *)
(* Restart. *)
(*   introv Spl Val Sub1 Sub2. gen B. *)
(*   induction* Spl; intros. *)
(*   - (* union at left *) inverts_typ. applys~ psub_negtyp Sub1. *)
(*   - (* inter at left *) inverts_typ. inverts_typ. *)
(*     applys~ psub_negtyp Sub1. *)
(*   - (* inter at left *) inverts_typ. inverts_typ. *)
(*     applys~ psub_negtyp Sub1. *)
(*   - applys~ psub_forall Sub1. *)
(*   - (* record *) *)
(*     inverts Sub1; try inverts_typ; eauto. *)
(*     + inverts_psub Sub2. injection H; intros; subst~. *)
(*     + inverts_psub Sub2. *)
(*       * applys~ PSub_UnionL. *)
(*         assert (t_rcd l5 A <p t_rcd l5 (A1&A2)). admit. *)
(*         inverts_psub H2. *)
(*         injection H4; intros; subst~. *)
(* Abort. *)


Lemma nsub_negtyp : forall V1 V2 A,
    A <n (fty_StackArg V1) -> isNegTyp V1 -> isNegTyp V2 -> A <n (fty_StackArg V2).
Proof.
  introv Sub Neg1 Neg2. gen V2.
  inductions Sub; try solve [inverts Neg1]; intros; eauto using psub_negtyp.
Qed.

(*------------------------------ Lemma B.1 -----------------------------------*)

Lemma sub2psub : forall V A,
    isValTyp V -> V <: A -> V <p A.
Proof.
  introv Val Sub.
  convert2asub.
  induction Sub; try solve [inverts Val]; try inverts_typ.
  - (* refl *) induction* Val.
  - (* top *) eauto.
  - (* arrow *) eauto.
  - (* forall *) eauto.
  - (* rcd *) eauto.
  - (* intersect on the right *) applys~ psub_merge_intersection H.
  - (* on the left *) applys~ psub_spli_left H.
  - (* on the left *) applys~ psub_spli_right H.
  - (* PREVIOUS COUNTER EXAMPLE: Box_l (Box_r1 T | Box_r2 T) <p Box_l Box_r1 T | Box_l Box_r2 T *)
    applys~ psub_merge_union H.
  - applys* psub_splu_left H.
  - applys* psub_splu_right H.
Qed.

Lemma nsub_merge_union : forall A B B1 B2,
    splu B B1 B2 -> isNegTyp A -> isValTyp B ->
    A <n (fty_StackArg B1) -> A <n (fty_StackArg B2) -> A <n (fty_StackArg B).
Proof.
  introv Spl Neg Val Sub1 Sub2.
  induction Neg.
  - (* arrow *) inverts Sub1; inverts Sub2.
    forwards~ : psub_merge_union Spl H6.
    (* PREVIOUSLY BROKEN isValTyp B1 -> isValTyp B2 -> splu B B1 B2 -> isValTyp B *)
  - (* {l:A} encode by arrow *) inverts Sub1; inverts Sub2.
    forwards~ : psub_merge_union Spl H5.
    (* PREVIOUSLY BROKEN isValTyp B1 -> isValTyp B2 -> splu B B1 B2 -> isValTyp B *)
  - (* forall *) inverts* Sub1.
  - (* and *)
    inverts Val; inverts Spl.
    + inverts Sub1; inverts* Sub2; inverts_typ.
      * econstructor; eauto. applys nsub_negtyp; try eassumption; eauto.
      * econstructor; eauto. applys nsub_negtyp; try eassumption; eauto.
    + inverts Sub1; inverts* Sub2; inverts_typ.
      * econstructor; eauto. applys nsub_negtyp; try eassumption; eauto.
      * econstructor; eauto. applys nsub_negtyp; try eassumption; eauto.
    + inverts Sub1; inverts* Sub2; try inverts_typ.
      * econstructor; eauto. applys nsub_negtyp; try eassumption; eauto.
      * econstructor; eauto. applys nsub_negtyp; try eassumption; eauto.
  - (* or *)
    inverts Sub1; inverts* Sub2.
  - (* top *)
    inverts Sub1; inverts* Sub2.
Qed.

(* Let A := In l V | In r V *)
(* apply(A->B , A) => B *)
(* But A->B <n A cannot be proved *)
(* because A is not a Vtyp *)

Lemma apply2nsub : forall A F C,
    isNegTyp A -> isValFty F -> ApplyTy A F C -> A <n F.
Proof.
  introv Neg Val App.
  induction App; try solve [inverts Neg]; inverts Val.
  - (* forall *) eauto.
  - (* arrow *)
    inverts* H0. constructor~.
    applys~ sub2psub.
  - (* union *) inverts* Neg.
  - (* union *) inverts* Neg.
  - (* splu *) inverts_typ. applys* nsub_merge_union.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
Qed.


(*------------------------------ Lemma B.9 -----------------------------------*)
Definition iso A B := A <: B /\ B <: A.

Notation "A ~= B"        := (iso A B)
                              (at level 65, B at next level, no associativity) : type_scope.

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

Hint Immediate iso_symm iso_refl iso_or iso_or_2 iso_and iso_or_match iso_and_match : core.

Lemma applyty_bot : forall B C,
    ApplyTy t_bot B C -> C ~= t_bot.
Proof.
  introv H. inductions H; auto.
  - forwards~ : IHApplyTy1. forwards~ : IHApplyTy2.
Qed.

Hint Resolve iso_refl iso_or iso_and : core.

Lemma isnegtyp_lc : forall A, isNegTyp A -> lc_typ A.
Proof. introv H. induction~ H. Qed.

Lemma isvaltyp_lc : forall A, isValTyp A -> lc_typ A.
Proof. introv H. induction H; auto using isnegtyp_lc. Qed.

Hint Immediate isnegtyp_lc isvaltyp_lc : core.

Lemma applyty_iso : forall A B1 C1 B2 C2,
    ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2
    -> C1 ~= C2.
Proof with elia.
  introv HA1 HA2.
  indTypSize (size_typ A + size_typ B1 + size_typ B2).
  inverts keep HA1; inverts keep HA2; auto.
  all: repeat match goal with
              | H: ApplyTy _ _ ?A |- _ ~= ?A|?B => forwards~ : IH HA1 H; elia; clear H
              | H: ApplyTy _ _ ?B |- _ ~= ?A|?B => forwards~ : IH HA1 H; elia; clear H
              | H: ApplyTy _ _ ?A |- ?A|?B ~= _ => forwards~ : IH H HA2; elia; clear H
              | H: ApplyTy _ _ ?B |- ?A|?B ~= _ => forwards~ : IH H HA2; elia; clear H
              end.
  all: clear HA1 HA2.
  all: repeat match goal with
              | H1: ApplyTy _ _ ?A1, H2: ApplyTy _ _ ?B1 |- ?A1|?A2 ~= ?B1|?B2 =>
                forwards~ : IH H1 H2; elia; clear H1 H2
              | H1: ApplyTy _ _ ?A2, H2: ApplyTy _ _ ?B2 |- ?A1|?A2 ~= ?B1|?B2 =>
                forwards~ : IH H1 H2; elia; clear H1 H2
              | H1: ApplyTy _ _ ?A, H2: ApplyTy _ _ ?B |- ?A ~= ?B =>
                forwards~ : IH H1 H2; elia; clear H1 H2
              end.

  [ (Forall X.B) -> C1 ]  & [ (A->B) -> C2 ]

                                       (Forall X.B) | (A->B)
  - forwards~ : IH HA1 H2... forwards~ : IH HA1 H4...
  -

Definition isAtomic B := forall A B1 B2 C1 C2, splu B B1 B2 -> ApplyTy A (fty_StackArg B1) C1
                                               -> ApplyTy A (fty_StackArg B2) C2 -> C1 ~= C2.

Lemma dispatch : forall A, isValTyp A -> isAtomic A.
Proof.
  introv Val.
  indTypSize (size_typ A).
  forwards* [?|(?&?&?)]: ordu_or_split A.
  - unfolds. intros. solve_false.
  - inverts_typ.
    forwards Val1: IH H0; elia. forwards Val2: IH H1; elia.
    unfolds; intros.
    lets App1: H3. lets App2: H4. clear H3 H4.
    forwards Lc: applyty_lc_1 App1.
    induction Lc.
    inverts keep App1; inverts keep App2; auto.
    + admit.
    +
  inverts Val.
  induction Val.
