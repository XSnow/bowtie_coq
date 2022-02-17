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

#[export] Hint Extern 1 (isValTyp _) => inverts_typ : core.

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

Lemma psub_bot_inv : forall V,
    V <p t_bot -> False.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

Lemma sub_neg_r_inv : forall V A,
    V <: A -> isValTyp V -> isNegTyp A -> isNegTyp V.
Proof with elia.
  introv Sub Val Neg.
  indTypSize (size_typ V + size_typ A).
  inverts~ Val.
  - inverts~ Neg; try solve [convert2asub; solve_false].
    + assert (HS: t_rcd l5 V0 <: A0) by applys* DSub_Trans Sub.
      forwards* : IH HS...
    + lets~ [Hu|(?&?&Hu)]: ordu_or_split V0.
      * convert2asub. forwards~ [HS|HS]: algo_sub_orlr_inv Sub.
        all: convert2dsub; forwards* : IH HS...
      * exfalso. inverts_typ.
        convert2asub. forwards~ : algo_sub_or_inv Sub. eauto.
        destruct_conj. convert2dsub.
        forwards~ : IH H4... inverts H6.
    + admit.
Abort.

Lemma applyty_arrow : forall A1 A2 V B,
    ApplyTy (t_arrow A1 A2) V B -> isValFty V -> exists V', V = fty_StackArg V' /\ isValTyp V'.
Proof.
  introv App Val.
  inductions App.
  - inverts* Val.
  - inverts* Val.
Qed.

Lemma applyty_forall : forall A V B,
    ApplyTy (t_forall A) V B -> isValFty V -> exists C, V = fty_StackTyArg C.
Proof.
  introv App Val.
  inductions App.
  - inverts* Val.
  - exfalso.
    inverts Val. inverts_typ.
    forwards~ (?&?): IHApp1. inverts H3.
Qed.

Lemma applyty_top : forall V A,
    ApplyTy t_top V A -> isValFty V -> False.
Proof.
  introv App Val.
  inductions App.
  - inverts Val. inverts_typ.
    forwards~ : IHApp1.
Qed.
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
Qed.

Lemma psub_spli_right : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A2 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A1.
  induction Sub; intros; eauto.
  - (* rcd *) inverts* Spl.
    + (* (Box_l V) B <p Box_l A *)
      inverts Val; solve_false.
Qed.

Lemma psub_splu_left : forall A B B1 B2,
    splu B B1 B2 -> A <p B1 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  - inverts_psub Sub. eauto.
  - inverts_psub Sub. eauto.
  - inverts_psub Sub. eauto.
Qed.

Lemma psub_splu_right : forall A B B1 B2,
    splu B B1 B2 -> A <p B2 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  all: inverts_psub Sub; eauto.
Qed.

Hint Immediate psub_spli_left psub_spli_right psub_splu_left psub_splu_right : core.

Lemma psub_refl : forall A,
    isValTyp A -> A <p A.
Proof.
  introv H. induction~ H.
Qed.

(* (5) If split(V) => V1 | V2 then V1/V => ok and V2/V => ok *)
Lemma psub_splu_valtyp_left_rev : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A1 <p A.
Proof.
  introv Spl Val.
  applys psub_splu_left Spl. applys* psub_refl.
Qed.

Lemma psub_splu_valtyp_right_rev : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A2 <p A.
Proof.
  introv Spl Val.
  applys psub_splu_right Spl. applys* psub_refl.
Qed.

Lemma psub_splu_valtyp_left : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A <p A1.
Proof.
  introv Spl Val.
  induction Spl; inverts Val; eauto.
  all: try forwards*: IHSpl.
  - constructor*. applys~ psub_spli_left.
  - constructor*. applys~ psub_spli_right.
  - constructor*.
Qed.

Lemma psub_splu_valtyp_right : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A <p A2.
Proof.
  introv Spl Val.
  induction Spl; inverts Val; eauto.
  all: try forwards*: IHSpl.
  - constructor*. applys~ psub_spli_left.
  - constructor*. applys~ psub_spli_right.
  - constructor*.
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


Lemma psub_unionL : forall A A1 A2 B,
    splu A A1 A2 -> isValTyp A -> A1 <p B -> A <p B.
Proof with try eassumption; elia.
  introv Spl Val Sub.
  indTypFtySize (size_typ A + size_typ B).
  inverts Spl; intros.
  - (* union at left *) inverts_typ. applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ. inverts_typ.
    applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ. inverts_typ.
    applys~ psub_negtyp Sub.
  - (* forall *) applys~ psub_forall Sub.
  -(* record *)
    inverts Sub; try inverts_typ; eauto.
    + forwards: IH H... eauto.
    + applys~ PSub_UnionL. applys psub_rcd H2. applys* psub_splu_valtyp_left.
    + applys~ PSub_UnionR. applys psub_rcd H2. applys* psub_splu_valtyp_left.
    + applys~ PSub_Intersect.
      * applys psub_rcd H1. applys* psub_splu_valtyp_left.
      * applys psub_rcd H2. applys* psub_splu_valtyp_left.
Qed.

Lemma psub_unionR : forall A A1 A2 B,
    splu A A1 A2 -> isValTyp A -> A2 <p B -> A <p B.
Proof with try eassumption; elia.
  introv Spl Val Sub.
  indTypFtySize (size_typ A + size_typ B).
  inverts Spl; intros.
  - (* union at left *) inverts_typ. applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ. inverts_typ.
    applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ. inverts_typ.
    applys~ psub_negtyp Sub.
  - (* forall *) applys~ psub_forall Sub.
  -(* record *)
    inverts Sub; try inverts_typ; eauto.
    + forwards: IH H... eauto.
    + applys~ PSub_UnionL. applys psub_rcd H2. applys* psub_splu_valtyp_right.
    + applys~ PSub_UnionR. applys psub_rcd H2. applys* psub_splu_valtyp_right.
    + applys~ PSub_Intersect.
      * applys psub_rcd H1. applys* psub_splu_valtyp_right.
      * applys psub_rcd H2. applys* psub_splu_valtyp_right.
Qed.

Lemma psub_merge_union : forall A A1 A2 B,
    splu A A1 A2 -> isValTyp A -> A1 <p B -> A2 <p B -> A <p B.
Abort. (* weak than the above two *)


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
  - applys~ psub_unionL H.
  - applys* psub_splu_left H.
  - applys* psub_splu_right H.
Qed.

Lemma nsub_unionL : forall A B B1 B2,
    splu B B1 B2 -> isNegTyp A -> isValTyp B ->
    A <n (fty_StackArg B1) -> A <n (fty_StackArg B).
Proof.
  introv Spl Neg Val Sub.
  induction Neg.
  - (* arrow *) inverts Sub.
    forwards~ : psub_unionL Spl H6.
  - (* {l:A} encode by arrow *) inverts Sub.
    forwards~ : psub_unionL Spl H5.
  - (* forall *) inverts* Sub.
  - (* and *)
    inverts Val; inverts Spl.
    1,3,4: inverts Sub; inverts_typ; [ applys* NSub_IntersectL | applys* NSub_IntersectR].
    all: applys nsub_negtyp; try eassumption; eauto.
  - (* or *)
    inverts* Sub.
  - (* top *)
    inverts* Sub.
Qed.


Lemma nsub_unionR : forall A B B1 B2,
    splu B B1 B2 -> isNegTyp A -> isValTyp B ->
    A <n (fty_StackArg B2) -> A <n (fty_StackArg B).
Proof.
  introv Spl Neg Val Sub.
  induction Neg.
  - (* arrow *) inverts Sub.
    forwards~ : psub_unionR Spl H6.
  - (* {l:A} encode by arrow *) inverts Sub.
    forwards~ : psub_unionR Spl H5.
  - (* forall *) inverts* Sub.
  - (* and *)
    inverts Val; inverts Spl.
    1,3,4: inverts Sub; inverts_typ; [ applys* NSub_IntersectL | applys* NSub_IntersectR].
    all: applys nsub_negtyp; try eassumption; eauto.
  - (* or *)
    inverts* Sub.
  - (* top *)
    inverts* Sub.
Qed.

Lemma nsub_merge_union : forall A B B1 B2,
    splu B B1 B2 -> isNegTyp A -> isValTyp B ->
    A <n (fty_StackArg B1) -> A <n (fty_StackArg B2) -> A <n (fty_StackArg B).
Abort. (* weak than the above two *)

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
  - (* splu *) inverts_typ. applys* nsub_unionL.
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
Proof. introv H. inductions H; eauto using iso_or_2. Qed.

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
Abort. (*
  [ (Forall X.B) -> C1 ]  & [ (A->B) -> C2 ]
                                       (Forall X.B) | (A->B)
        *)

Lemma splu_twice : forall A B C B1 B2,
    splu A B C -> splu B B1 B2 -> exists A1 A2, splu A1 B1 C /\ splu A2 B2 C /\
                                                size_typ A1 < size_typ A /\
                                                size_typ A2 < size_typ A.
Proof with try splits; elia; auto.
  introv Spl1 Spl2.
  indTypSize (size_typ A).
  inverts Spl1.
  - exists (B1 | C) (B2 | C)...
  - inverts Spl2.
    + forwards (T1&T2&?): IH H0 H6... destruct_conj.
      exists (T1&B0) (T2&B0)...
    + (* A0 & B0 where splitu A0 = A1|A2 and A1 is ordu *)
Abort. (* counter example exists *)

#[export]
Hint Extern 0 =>
match goal with
| H : binds _ _ nil |- _ => inverts H
end : FalseHd.

Lemma dispatch_neg : forall A B1 B2 C1 C2,
    TypeWF nil A -> isNegTyp B1 -> isNegTyp B2 ->
    ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2 -> C1 ~= C2.
Proof.
  introv Tw Neg1 Neg2 App1 App2. gen B1 B2 C1 C2.
  inductions Tw; intros; solve_false.
  all: try solve [forwards HF: applyty_soundness_1 App1; convert2asub; solve_false].
  - inverts App1; inverts App2.
Abort.
(******************************************************************************)
    (* if B1 and B2 are ordinary it can be easier to prove *)
(*
  indTypSize (size_typ B1).
  forwards* [?|(?&?&?)]: ordu_or_split A.

  - inverts Spl.
  - inverts Spl. inductions Tw; solve_false.

Lemma dispatch_neg : forall A B B1 B2 C1 C2,
    TypeWF nil A -> isNegTyp B -> splu B B1 B2 ->
    ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2 -> C1 ~= C2.
Proof.
  introv Tw Neg Spl App1 App2.
  induction Neg.
  - inverts Spl.
  - inverts Spl.
  - inverts Spl. inductions Tw; solve_false.
    all: try solve [forwards HF: applyty_soundness_1 App1; convert2asub; solve_false].



Lemma dispatch_alt : forall A B B1 B2 C1 C2,
    TypeWF nil A -> isValTyp B -> splu B B1 B2 ->
    ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2 -> C1 ~= C2.
Proof.
  introv Tw Val Spl App1 App2.
  induction Tw.
  - inverts App1.

Definition isAtomic B := forall A B1 B2 C1 C2, TypeWF nil A -> splu B B1 B2 ->
   ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2 -> C1 ~= C2.

Lemma dispatch : forall A, isValTyp A -> isAtomic A.
Proof.
  introv Val.
  indTypSize (size_typ A).
  forwards* [?|(?&?&?)]: ordu_or_split A.
  - unfolds. intros. solve_false.
  - inverts_typ.
    forwards Val1: IH H0; elia. forwards Val2: IH H1; elia.
    unfolds; intros.
    lets App1: H4. lets App2: H5. clear H5 H4.
    forwards Lc: applyty_lc_1 App1.
    induction Lc.
    inverts keep App1; inverts keep App2; auto.
-    + admit.
-    +
-  inverts Val.
-  induction Val.
*)


#[export]
 Hint Extern 0 =>
   match goal with
   | H: isValTyp (t_rcd _ _ | _) |- _ => inverts H
   | H: isValTyp (_ | t_rcd _ _ ) |- _ => inverts H
   | H: isValTyp _ |- _ => inverts H; fail
   end : FalseHd.

Definition applicable A B := exists C, ApplyTy A B C.

Definition typ_as_ftyp := fty_StackArg.
Coercion typ_as_ftyp : typ >-> Fty.

Definition similar A B := exists V, splu V A B /\ isValTyp V.

Lemma similar_rcd_inv : forall l1 l2 A B,
    similar (t_rcd l1 A) (t_rcd l2 B) -> similar A B.
Proof with solve_false.
  introv HS.
  unfolds in HS. destruct_conj.
  inverts H...
  unfolds. exists. split.
  {eassumption.} {auto.}
Qed.

Lemma similar_rcd : forall l A B,
    similar A B -> similar (t_rcd l A) (t_rcd l B).
Proof.
  introv Sim.
  unfolds. unfolds in Sim. destruct_conj.
  exists*.
Qed.

Lemma sim2similar : forall A B,
    sim A B <-> similar A B.
Proof.
  introv. split; introv Sim.
  - induction Sim.
    all: try solve [unfolds; exists; split~].
    + applys* similar_rcd.
  - unfolds in Sim. destruct_conj.
    induction H; try inverts_typ; eauto.
    + inverts_typ. applys* Sim_Neg.
    + inverts_typ. applys* Sim_Neg.
    + applys* Sim_Neg.
Qed.

Lemma sub_neg_l_inv : forall A B,
    A <: B -> isNegTyp A -> isNegTyp B.
Proof with elia.
  introv Sub Neg.
  indTypSize (size_typ A + size_typ B).
  inverts Neg.
Abort. (* counter example: B = Bneg | B2 *)

Lemma applyty_valtyp : forall A B V1 V2,
      Distinguishability A B -> sim V1 V2-> ordu V1 -> ordu V2 ->
      V1 <: A -> V2 <: A -> V1 <: B -> V2 <: B.
Proof with solve_false.
  introv Dis Sim Ord1 Ord2 Sub1 Sub2 Sub3.
  gen A B. induction Sim; intros.
  (* A0,B0 = Neg | Empty *)
(*********************************************************************)
(*   gen V1 V2. induction Dis; intros. *)
(*   - inverts Val. inverts keep Spl. inverts H4. *)
(*     + inverts H. *)
(*       convert2asub. auto_inv. convert2dsub. *)

(* Lemma applyty_valtyp : forall A1 A2 V V1 V2, *)
(*     Mergeability A1 A2 -> isValTyp V -> splu V V1 V2 -> ordu V1 -> ordu V2 -> *)
(*     (applicable A1 V1 /\ applicable A1 V2 /\ applicable A2 V1 /\ NApplyTy A2 V2) \/ *)
(*     (applicable A1 V1 /\ applicable A1 V2 /\ NApplyTy A2 V1 /\ applicable A2 V2) \/ *)
(*     (applicable A1 V1 /\ NApplyTy A1 V2 /\ applicable A2 V1 /\ applicable A2 V2) \/ *)
(*     (NApplyTy A1 V1 /\ applicable A1 V2 /\ applicable A2 V1 /\ applicable A2 V2) \/ *)
(*     (NApplyTy A1 V1 /\ applicable A1 V2 /\ applicable A2 V1 /\ NApplyTy A2 V2) \/ *)
(*     (applicable A1 V1 /\ NApplyTy A1 V2 /\ NApplyTy A2 V1 /\ applicable A2 V2) *)
(*     -> False. *)
(* Proof with solve_false. *)
(*   introv Meg Val Spl Ord1 Ord2 [HF|HF]. *)
(*   - unfold applicable in HF. destruct_conj. *)
(*     inverts Meg. *)
(*     all: try solve [inverts keep H; solve_false]. *)
(*     + inverts keep H... inverts keep H0... *)
(*       inverts H2... inverts keep H1... *)
(*     + *)
