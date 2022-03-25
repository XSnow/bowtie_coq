Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export MatchTy.

Notation "A <p B"        := (PositiveSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Notation "A <n B"        := (NegativeSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Definition typ_as_ftyp := fty_StackArg.
Coercion typ_as_ftyp : typ >-> Fty.

Ltac inverts_neg_false :=
  try match goal with
  | H: isNegTyp (_ & _) |- _ => inverts H
  | H: isNegTyp (_ | _) |- _ => inverts H
  end;
  match goal with
  | H: isNegTyp (t_rcd _ _) |- _ => inverts H
  | H: isNegTyp t_bot |- _ => inverts H
  end; fail.

#[export]
Hint Extern 0 => inverts_neg_false : FalseHd.

#[export]
 Hint Extern 1 =>
   match goal with
  | H1: isValTyp (_ & _) |- _ => inverts H1
  | H1: isValTyp (_ | _) |- _ => inverts H1
  | H1: isValTyp _ |- _ => inverts H1
   end; inverts_neg_false : FalseHd.

#[export]
Hint Extern 0 =>
match goal with
| H : binds _ _ nil |- _ => inverts H; fail
end : FalseHd.

#[export]
 Hint Extern 1 => match goal with
                 | H: DistinguishabilityAx _ _ |- _ => inverts~ H; fail
end : FalseHd.

Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].

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
  all: try match goal with
           | H1: isNegTyp (_ & _) |- _ => inverts* H1
           | H1: isNegTyp (_ | _) |- _ => inverts* H1
           end.
  all: try forwards* (?&?): IHSpl.
  all: try match goal with
         | H1: spli ?A _ _, H2: isNegTyp ?A |- _ => forwards* (?&?): negtyp_spli_inv H2 H1
         | H2: isNegTyp _ _ _ |- _ => forwards* (?&?): negtyp_spli_inv H2
           end.
  all: solve_false.
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
  introv Val Spl. gen A1 A2.
  induction Val; intros.
  - inverts Spl.
  - forwards* (?&?): negtyp_splu_inv H.
Qed.

Ltac inverts_typ :=
  try match goal with
  | H1: isValFty (fty_StackArg (_ & _)) |- _ => inverts H1
  | H1: isValFty (fty_StackArg (_ | _)) |- _ => inverts H1
  | H1: isValTyp (_ & _) |- _ => inverts H1
  | H1: isValTyp (_ | _) |- _ => inverts H1
  | H1: isValTyp (t_rcd _ _) |- _ => inverts H1
  | H1: isValTyp ?A, H2: spli ?A _ _ |- _ => forwards (?&?): valtyp_spli_inv H1 H2
  | H1: isValTyp ?A, H2: splu ?A _ _ |- _ => forwards (?&?): valtyp_splu_inv H1 H2
  end;
  try match goal with
  | H1: isNegTyp (_ & _) |- _ => forwards (?&?): negtyp_spli_inv H1; [applys SpI_and | ]; clear H1
  | H1: isNegTyp (_ | _) |- _ => forwards (?&?): negtyp_splu_inv H1; [applys SpU_or | ]; clear H1
  | H1: isNegTyp ?A, H2: spli ?A _ _ |- _ => forwards (?&?): negtyp_spli_inv H1 H2
  | H1: isNegTyp ?A, H2: splu ?A _ _ |- _ => forwards (?&?): negtyp_splu_inv H1 H2
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
  inverts~ Sub. inverts~ H0.
Qed.

Lemma psub_and_inv : forall V B1 B2,
    V <p B1 & B2 -> V <p B1 /\ V <p B2.
Proof.
  introv Sub.
  inverts~ Sub. inverts~ H0.
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
  inverts* Sub.
Abort.

Lemma psub_spli_inv : forall A B B1 B2,
    spli B B1 B2 -> isValTyp A -> A <p B -> A <p B1 /\ A <p B2.
Proof.
  introv Spl Val Sub. gen A.
  induction* Spl; split; intros.
  all: try solve [inverts~ Sub; match goal with H: isNegTyp _ |- _ => inverts~ H end].
  all: inverts~ Sub; try match goal with H: isNegTyp _ |- _ => inverts~ H end; forwards (?&?): IHSpl; try eassumption; now eauto.
Qed.

Lemma psub_splu_inv : forall A B B1 B2,
    splu B B1 B2 -> isValTyp A -> A <p B -> A <p B1 \/ A <p B2.
Proof.
  introv Spl Val Sub. gen A.
  induction* Spl; intros.
  all: try forwards [?|?]: psub_or_inv Sub.
  all: try forwards (?&?): psub_and_inv Sub.
  all: try solve [inverts~ Sub; match goal with H: isNegTyp _ |- _ => inverts~ H end].
  all: try solve [forwards [?|?]: IHSpl; try eassumption; eauto].
  - (* forall *) left. eauto.
Qed.

Local Ltac inverts_psub H :=
  try forwards [?|?]: psub_or_inv H;
  try forwards (?&?): psub_and_inv H;
  try forwards (?&?&?): psub_rcd_inv H;
  try match type of H with
        ?A <p ?B => match goal with
                    | Hspl: spli B _ _ |- _ =>
                      forwards (?&?): psub_spli_inv Hspl H
                    | Hspl: splu B _ _ |- _ =>
                      forwards [?|?]: psub_splu_inv Hspl H
                  end
      end; subst.

Lemma psub_bot_inv : forall V,
    V <p t_bot -> False.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

#[export] Hint Immediate psub_bot_inv : FalseHd.

Lemma psub_sub_bot_inv : forall V A,
    V <p A -> A <: t_bot -> False.
Proof.
  introv PSub Sub. convert2asub. gen V.
  inductions Sub; intros; eauto; solve_false.
  inverts_psub PSub; now eauto.
  inverts_psub PSub; now eauto.
  inverts_psub PSub; now eauto.
Qed.

(* wrong lemma *)
Lemma nsub_sub_bot_inv : forall V A,
    V <n A -> V <: t_bot -> False.
Proof.
  introv PSub Sub. convert2asub. gen A.
  inductions Sub; intros.
  all: try solve [inverts keep PSub]; solve_false.
  - inverts H; try solve [inverts PSub; forwards: IHSub; eassumption]; solve_false.
    + inverts PSub. forwards~: IHSub; eassumption.
Abort.

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
        ** inverts Hu.
    (*     ** *)
    (*       convert2asub. forwards~ : algo_sub_or_inv Sub. eauto. *)
    (*       destruct_conj. convert2dsub. *)
    (*       forwards~ : IH H4... inverts H6. *)
    (* + admit. *)
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
    forwards~ (?&?): IHApp1. solve_false.
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
    injection H; intros; subst. inverts_typ.
    forwards~: IHSpl x0.
    solve_false.
Qed.

Lemma psub_spli_left : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A1 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A2.
  induction Sub; intros; eauto.
  - (* rcd *) inverts~ Spl; solve_false.
    inverts_typ; solve_false. constructor*.
Qed.

Lemma psub_spli_right : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A2 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A1.
  induction Sub; intros; eauto.
  - (* rcd *) inverts~ Spl; inverts_typ; eauto; solve_false.
Qed.

Lemma psub_splu_left : forall A B B1 B2,
    splu B B1 B2 -> A <p B1 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  all: inverts_psub Sub; eauto.
Qed.

Lemma psub_splu_right : forall A B B1 B2,
    splu B B1 B2 -> A <p B2 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  all: inverts_psub Sub; eauto.
Qed.

#[export] Hint Immediate psub_spli_left psub_spli_right psub_splu_left psub_splu_right : core.

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
  induction Spl; inverts Val; eauto; solve_false.
  all: try forwards~ : IHSpl.
  all: inverts_typ; eauto.
  - constructor*. applys~ psub_spli_left.
  - constructor*. applys~ psub_spli_right.
Qed.

Lemma psub_splu_valtyp_right : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A <p A2.
Proof.
  introv Spl Val.
  induction Spl; inverts Val; eauto; solve_false.
  all: try forwards~ : IHSpl.
  all: inverts_typ; eauto.
  - constructor*. applys~ psub_spli_left.
  - constructor*. applys~ psub_spli_right.
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
Proof with solve_false.
  introv Spl Val Sub.
  indTypFtySize (size_typ A + size_typ B).
  inverts Spl; intros.
  - (* union at left *) inverts_typ; eauto. applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ; eauto. inverts_typ; eauto.
    applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ; eauto. inverts_typ; eauto.
    applys~ psub_negtyp Sub.
  - (* forall *) applys~ psub_forall Sub.
Qed.

Lemma psub_unionR : forall A A1 A2 B,
    splu A A1 A2 -> isValTyp A -> A2 <p B -> A <p B.
Proof with solve_false.
  introv Spl Val Sub.
  indTypFtySize (size_typ A + size_typ B).
  inverts Spl; intros.
  - (* union at left *) inverts_typ; eauto. applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ; eauto. inverts_typ; eauto.
    applys~ psub_negtyp Sub.
  - (* inter at left *) inverts_typ; eauto. inverts_typ; eauto.
    applys~ psub_negtyp Sub.
  - (* forall *) applys~ psub_forall Sub.
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
  induction Sub; try solve [inverts Val]; try inverts_typ; solve_false.
  all: eauto.
  - (* refl *) induction* Val.
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
  - (* forall *) inverts* Sub.
  - (* and *)
    inverts Val; inverts Spl.
    all: applys nsub_negtyp; try eassumption.
    all: inverts_typ; eauto; inverts_typ; eauto; solve_false.
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
  - (* forall *) inverts* Sub.
  - (* and *)
    inverts Val; inverts Spl.
    all: applys nsub_negtyp; try eassumption.
    all: inverts_typ; eauto; inverts_typ; eauto; solve_false.
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

(******************************************************************************)
(** Distinguishability *)

Lemma distinguishabilityAx_lc : forall A B,
    DistinguishabilityAx A B -> lc_typ A /\ lc_typ B.
Proof. induction 1; destruct_conj; split; eauto. Qed.

Lemma distinguishability_lc : forall A B,
    Distinguishability A B -> lc_typ A /\ lc_typ B.
Proof. induction 1; destruct_conj; eauto.
       all: forwards~ (?&?): distinguishabilityAx_lc H.
Qed.

Lemma distinguishability_lc_1 : forall A B,
    Distinguishability A B -> lc_typ A.
Proof. intros. applys distinguishability_lc H. Qed.

Lemma distinguishability_lc_2 : forall A B,
    Distinguishability A B -> lc_typ B.
Proof. intros. applys distinguishability_lc H. Qed.

#[export] Hint Resolve distinguishability_lc_1 distinguishability_lc_2 : core.

Lemma distinguishability_negtyp : forall A B,
    Distinguishability A B -> isNegTyp A.
Proof.
  introv H. induction* H.
Abort. (* It does not hold for records *)
(*
Lemma distinguishability_spl_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, splu A A1 A2 -> Distinguishability A1 B /\ Distinguishability A2 B) /\
    (forall B1 B2, splu B B1 B2 -> Distinguishability A B1 /\ Distinguishability A B2) /\
    (forall A1 A2, spli A A1 A2 -> ordu B -> Distinguishability A1 B \/ Distinguishability A2 B) /\
    (forall B1 B2, spli B B1 B2 -> ordu A -> Distinguishability A B1 \/ Distinguishability A B2).
Proof with try match goal with |- lc_typ _ => eauto end.

  Local Ltac get_IH IH IHH IHH1 IHH2 :=
    match goal with
    | H1 : Distinguishability _ _, H2 : Distinguishability _ _ |- _ =>
      forwards IHH1: IH H1; elia; forwards IHH2: IH H2; elia;
      destruct IHH1 as (IHDis11 & IHDis12 & IHDis13 & IHDis14);
      destruct IHH2 as (IHDis21 & IHDis22 & IHDis23 & IHDis24)
    end + match goal with
          | H : Distinguishability ?A ?B |- _ =>
            forwards IHH: IH H; elia;
            destruct IHH as (IHDis1 & IHDis2 & IHDis3 & IHDis4)
          end.

  introv Dis.
  indTypSize( size_typ A + size_typ B ).
  inverts Dis; intros.
  all: splits; introv Spl; try intro Ord; inverts_all_ord; inverts_all_spl; solve_false; try split.
  all: (* Ax cases *) try match type of H with (DistinguishabilityAx _ _) => induction* H; inverts* Spl end.
  all: try get_IH IH IHH IHH1 IHH2.
  all: try ( forwards (?&?): IHDis1; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis2; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis11; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis12; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis21; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis22; [ eassumption | ] ).
  all: try solve [constructor~].
  all: try solve [assumption].
  all: try ( forwards [?|?]: IHDis13; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis14; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis23; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis24; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis3; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis4; [ eassumption | eassumption | | ] ).
  all: try solve [left~].
  all: try solve [right~].
  (* Distributive cases require the inversion lemma from the other splitting relation
     and IH from induction on Dis is not enough so I have to use indTypSize *)
  all: try forwards [?|(?&?&?)]: ordu_or_split A...
  1-4: forwards (?&?): IHDis12; [ now eauto | ];
       forwards (?&?): IHDis22; [ now eauto | ];
         now eauto.
  1-4: forwards : IHDis14; [ now eauto | now eauto | ];
    forwards : IHDis24; [ now eauto | now eauto | ].
  1-8: repeat match goal with | H : _ \/ _ |- _ => destruct H end.
  1-16: now eauto.

  all: try forwards [?|(?&?&?)]: ordu_or_split B...
  1-4: forwards (?&?): IHDis11; [ now eauto | ];
       forwards (?&?): IHDis21; [ now eauto | ];
         now eauto.
  all: forwards : IHDis13; [ now eauto | now eauto | ];
    forwards : IHDis23; [ now eauto | now eauto | ].
  all: repeat match goal with | H : _ \/ _ |- _ => destruct H end.
  all: eauto.
Qed.

Lemma distinguishability_splu_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, splu A A1 A2 -> Distinguishability A1 B /\ Distinguishability A2 B) /\
    (forall B1 B2, splu B B1 B2 -> Distinguishability A B1 /\ Distinguishability A B2).
Proof.
  introv Dis.
  forwards* : distinguishability_spl_inv Dis.
Qed.

Lemma distinguishability_spli_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, spli A A1 A2 -> ordu B -> Distinguishability A1 B \/ Distinguishability A2 B) /\
    (forall B1 B2, spli B B1 B2 -> ordu A -> Distinguishability A B1 \/ Distinguishability A B2).
Proof.
  introv Dis.
  forwards* : distinguishability_spl_inv Dis.
Qed.

(* A1 <> B1 *)
(* A2 <> B2 *)
(* ---------------------- *)
(* A1 /\ A2 <> B1 \/ B2 *)


Ltac inverts_all_distinguishability :=
  repeat match goal with
         | Dis: Distinguishability ?A (_ & _), Ord: ordu ?A |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_spli_inv Dis;
           forwards [?|?]: HB Ord; [ eauto | | ]; clear Dis
         | Dis: Distinguishability (_ & _) ?B, Ord: ordu ?B |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_spli_inv Dis;
           forwards [?|?]: HA Ord; [ eauto | | ]; clear Dis
         | Dis: Distinguishability ?A ?B, Ord: ordu ?A, Spl: spli ?B _ _ |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_spli_inv Dis;
           forwards [?|?]: HB Spl Ord; clear Dis
         | Dis: Distinguishability ?A (_ | _) |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HB; [ eauto | ]; clear Dis
         | Dis: Distinguishability (_ | _) ?B |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HA; [ eauto | ]; clear Dis
         | Dis: Distinguishability ?A ?B, Spl: splu ?B _ _ |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HB Spl; clear Dis
         | Dis: Distinguishability ?A ?B, Spl: splu ?A _ _ |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HA Spl; clear Dis
         end.

Notation "A <<>> B"        := (Distinguishability A B)
                                (at level 65, B at next level, no associativity) : type_scope.

Lemma DistSym : forall A B,
    A <<>> B -> B <<>> A.
Proof.
  introv H. induction~ H.
Qed.

Lemma distinguishability_arrow_r : forall A B1 B2 C1 C2,
    A <<>> (t_arrow B1 B2) -> lc_typ (t_arrow C1 C2) -> A <<>> (t_arrow C1 C2).
Proof.
    introv Dis. gen C1 C2.
    inductions Dis; intros; eauto.
  - inverts* H.
  - inverts* H.
Qed.

Lemma distinguishability_arrow_l : forall A B1 B2 C1 C2,
    (t_arrow B1 B2) <<>> A -> lc_typ (t_arrow C1 C2) -> (t_arrow C1 C2) <<>> A.
Proof.
    introv Dis. gen C1 C2.
    inductions Dis; intros; eauto.
  - inverts* H.
  - inverts* H.
Qed.

Lemma distinguishability_forall_r : forall A B1 C1,
    A <<>> (t_forall B1) -> lc_typ (t_forall C1) -> A <<>> (t_forall C1)
with distinguishability_forall_l : forall A B1 C1,
    (t_forall B1) <<>> A -> lc_typ (t_forall C1) -> (t_forall C1) <<>> A.
Proof.
  +
    introv Dis. gen C1. clear distinguishability_forall_r.
    inductions Dis; intros; try solve [clear distinguishability_forall_l; eauto].
  - clear distinguishability_forall_l. inverts* H.
  - inverts* H.
  +
    introv Dis. gen C1. clear distinguishability_forall_l.
    inductions Dis; intros; try solve [clear distinguishability_forall_r; eauto].
  - clear distinguishability_forall_r. inverts* H.
  - inverts* H.
Qed.

Hint Immediate distinguishability_arrow_l distinguishability_arrow_r
     distinguishability_forall_l distinguishability_forall_r : core.

Lemma distinguishability_spli_l_1 : forall A B B1 B2,
      spli B B1 B2 -> (Distinguishability A B1 -> Distinguishability A B).
Proof.
  introv Spl Dis.
  indTypSize (size_typ A + size_typ B).
  inverts Spl; intros; inverts_all_distinguishability.
  1: applys~ DistIntersectLSym.
  1-2: applys~ DistUnionSym.
  all: try solve [applys IH; [ | | eassumption]; eauto; elia].
  1-3: (* arrow/forall *) eauto using
                                distinguishability_arrow_l, distinguishability_arrow_r,
                                distinguishability_forall_l, distinguishability_forall_r.
  - (* rcd *)
    inverts Dis; solve_false.
    1-2: now inverts* H0.
    1: applys DistIn.
    2: applys DistUnion.
    4: applys~ DistIntersectL.
    5: applys~ DistIntersectR.
    all: try solve [ applys IH; [ | | eauto ]; eauto; elia ].
    all: (* distributivity *)
      eapply SpI_in in H; forwards: IH H0 H; elia; forwards: IH H1 H; elia;
      now eauto.
Qed.

Lemma distinguishability_spli_r_1 : forall A B B1 B2,
      spli B B1 B2 -> (Distinguishability B1 A -> Distinguishability B A).
Proof.
  introv Spl Dis.
  applys DistSym. apply DistSym in Dis.
  applys* distinguishability_spli_l_1.
Qed.

Lemma distinguishability_spli_l_2 : forall A B B1 B2,
      spli B B1 B2 -> (Distinguishability A B2 -> Distinguishability A B).
Proof.
  introv Spl Dis.
  indTypSize (size_typ A + size_typ B).
  inverts Spl; intros; inverts_all_distinguishability.
  1: applys~ DistIntersectRSym.
  1-2: applys~ DistUnionSym.
  all: try solve [applys IH; [ | eassumption | ]; eauto; elia].
  1-3: (* arrow/forall *) eauto using
                                distinguishability_arrow_l, distinguishability_arrow_r,
                                distinguishability_forall_l, distinguishability_forall_r.
  - (* rcd *)
    inverts Dis; solve_false.
    1-2: now inverts* H0.
    1: applys DistIn.
    2: applys DistUnion.
    4: applys~ DistIntersectL.
    5: applys~ DistIntersectR.
    all: try solve [ applys IH; [ | | eauto ]; eauto; elia ].
    all: (* distributivity *)
      eapply SpI_in in H; forwards: IH H H0; elia; forwards: IH H H1; elia;
      now eauto.
Qed.

Lemma distinguishability_spli_r_2 : forall A B B1 B2,
      spli B B1 B2 -> (Distinguishability B2 A -> Distinguishability B A).
Proof.
Proof.
  introv Spl Dis.
  applys DistSym. apply DistSym in Dis.
  applys* distinguishability_spli_l_2.
Qed.


Lemma distinguishability_splu_r : forall A B B1 B2,
    splu B B1 B2 -> Distinguishability A B1 -> Distinguishability A B2 ->
    Distinguishability A B.
Proof with solve_false; inverts_all_ord.
  introv Spl Dis1 Dis2.
  indTypSize (size_typ A + size_typ B).
  inverts Spl; intros.
  - eauto.
  - forwards [?|(?&?&?)]: ordu_or_split A. now eauto.
    + inverts_all_distinguishability.
      1: applys~ DistIntersectLSym; forwards: IH; try eassumption; elia.
      all: now eauto.
    + (* splu A *)
      inverts_all_distinguishability.
      apply DistSym in H2. apply DistSym in H3.
      forwards HH1: IH H2 H3; [ | eauto | ]; elia. apply DistSym in HH1.
      apply DistSym in H4. apply DistSym in H5.
      forwards HH2: IH H4 H5; [ | eauto | ]; elia. apply DistSym in HH2.
      Admitted.
(*       applys DistDistribL. *)
(*       forwards: IH H5 H3; [ | eauto | ]; elia. *)
(*   - inverts_all_distinguishability. *)
(*     + applys~ DistIntersectLSym. *)
(*     + applys~ DistIntersectLSym. *)
(*     + applys~ DistIntersectLSym. *)
(*     + applys~ DistIntersectRSym. applys IH; try eassumption; elia. *)
(*   - applys* distinguishability_forall_r Dis1. *)
(*   - inverts Dis1... *)
(*     + (* rcd *) *)
(*       inverts Dis2... *)
(*       applys DistIn. applys~ IH H. elia. *)
(*     + inverts~ H0. *)
(*     + inverts~ H0. *)
(* Qed. *)

Lemma distinguishability_splu_l : forall A B B1 B2,
    ordi A -> ordu A -> splu B B1 B2 -> Distinguishability B1 A -> Distinguishability B2 A ->
    Distinguishability B A.
Proof with solve_false; inverts_all_ord.
  introv Ordi Ordu Spl Dis1 Dis2.
  applys DistSym.
  apply DistSym in Dis1. apply DistSym in Dis2.
  applys distinguishability_splu_r; eassumption.
Qed.

Lemma distinguishability_rcd_inv : forall l A B,
    (t_rcd l A) <<>> (t_rcd l B) -> A <<>> B.
Proof.
  introv H. inverts~ H; solve_false.
Qed.

Lemma distinguishability_splu_gen : forall A B B1 B2,
    splu B B1 B2 -> Distinguishability B1 A -> Distinguishability B2 A ->
    Distinguishability B A.
Proof with solve_false; inverts_all_ord.
  introv Spl Dis1 Dis2.
  indTypSize (size_typ A + size_typ B).
  inverts keep Spl; auto.
  - (* and *)
    inverts keep Dis1; auto; inverts keep Dis2; try solve [constructor~]; solve_false.
    + applys~ DistIntersectL. applys~ IH H0. elia.
    (* + inverts_all_distinguishability. *)
    (*   applys DistUnionSym; applys IH Spl; elia; eauto. *)
    (* + inverts_all_distinguishability. *)
Abort.
(* A1 <> B1 *)
(* A2 /\ A3 <> B2 (note this does not imply A2 <> B2 \/ A3 <> B2) *)
(* --------------------------------------------------------------- cannot prove this *)
(* (A1 \/ A2) /\ A3 <> B1 /\ B2 *)

(* A1 <> B1 /\ B2 *)
(* A2 /\ A3 <> B1 /\ B2 *)
(* ----------------------------- *)
(* A1 \/ (A2 /\ A3) <> B1 /\ B2 *)

(* BUT its subtype (A1 \/ A2) /\ A3 is not <> B1 /\ B2 *)

Section ConcreteExample.
Notation "{Box l T}" := (t_rcd l t_top) (at level 10).

Parameter l1 l2 l3 : l.
Axiom neq1 : l1 <> l2.
Axiom neq2 : l2 <> l3.
Axiom neq3 : l1 <> l3.
#[local] Hint Resolve neq1 neq2 neq3 : core.
Definition A1 := {Box l3 T}.
Definition A2 := {Box l1 T}.
Definition A3 := {Box l2 T}.
Definition B1 := {Box l1 T} | {Box l2 T}.
Definition B2 := ({Box l1 T} | {Box l2 T}) | {Box l3 T}.

Lemma HA1 : A1 <<>> B1.
  unfold A1. unfold B1. applys DistUnionSym; applys DistAx; applys* DistAxIn.
Qed.

Lemma HA2 : A2 & A3 <<>> B2.
  unfold A2. unfold A3. unfold B2. applys DistUnionSym.
  2: { applys~ DistIntersectL. }
  applys DistUnionSym.
  - applys~ DistIntersectR.
  - applys~ DistIntersectL.
Qed.

Lemma G1 : A1 | (A2 & A3) <<>> B1 & B2.
  applys DistUnion.
  - applys~ DistIntersectLSym HA1. { unfold B2. repeat constructor. }
  - applys~ DistIntersectRSym HA2. { unfold B1. repeat constructor. }
Qed.

Lemma HN21 : A2 <<>> B1 -> False.
  unfold A2. unfold B1. intro H.
  inverts H.
  - (* Ax *) inverts H0.
  (* - (* Union RHS *) inverts H3; solve_false. *)
  (*    * inverts H0; solve_false. *)
  (* - (* Ax *) inverts H0. *)
(* Qed. *) Admitted.

(* Lemma HN22 : A2 <<>> B2 -> False. *)
(*   unfold A2. unfold B2. intro H. *)
(*   inverts H. *)
(*   - (* Ax *) inverts H0. *)
(*   - (* Union RHS *) inverts H3. *)
(*     + (* Ax *) inverts H; solve_false. *)
(*     + inverts H2; solve_false. *)
(*       * inverts H0; solve_false. *)
(*     + inverts H. *)
(*   - (* Ax *) inverts H0. *)
(* Qed. *)

(* Lemma HN31 : A3 <<>> B1 -> False. *)
(* Proof with solve_false. *)
(*   unfold A3. unfold B1. intro H. *)
(*   inverts H... *)
(*   - (* Union RHS *) inverts H4... *)
(*     + (* Ax *) inverts H0... *)
(* Qed. *)

(* Lemma HN32 : A3 <<>> B2 -> False. *)
(*   unfold A3. unfold B2. intro H. *)
(*   inverts H. *)
(*   - (* Ax *) inverts H0. *)
(*   - (* Union RHS *) inverts H3. *)
(*     + (* Ax *) inverts H; solve_false. *)
(*     + inverts H5; solve_false. *)
(*       * inverts H0; solve_false. *)
(*     + inverts H. *)
(*   - (* Ax *) inverts H0. *)
(* Qed. *)

(* Lemma G2 : (A1 | A2) & A3 <<>> B1 & B2 -> False. *)
(* Proof with solve_false. *)
(*   introv H. *)
(*   inverts H... *)
(*   - inverts H4... *)
(*     + inverts H5... *)
(*       * applys~ HN21. *)
(*       * applys~ HN22. *)
(*     + inverts H5... *)
(*       * applys~ HN21. *)
(*       * unfold A2 in H4. inverts H4... inverts H7... inverts H0... *)
(*     + inverts H5... *)
(*       * applys~ HN22. *)
(*       * unfold A1 in H6. inverts H6... inverts H1... inverts H0... *)
(*   - inverts H4... *)
(*     + applys~ HN31. *)
(*     + applys~ HN32. *)
(*   - inverts H4... *)
(*     + inverts H5... *)
(*       * applys~ HN21. *)
(*       * unfold A2 in H4. inverts H4... inverts H7... inverts H0... *)
(*     + applys~ HN31. *)
(*     + unfold A1 in H2. unfold A2 in H2. unfold A3 in H2. *)
(*       unfold A1 in H5. unfold A2 in H5. unfold A3 in H5. *)
(*       inverts H5... *)
(*       * inverts H2... *)
(*         ** inverts H7... inverts H8... inverts H0... *)
(*         ** Abort. *)
End ConcreteExample.

(* Lemma distinguishability_splu_r : forall A B B1 B2, *)
(*     ordu A -> splu B B1 B2 -> Distinguishability A B1 -> Distinguishability A B2 -> *)
(*     Distinguishability A B. *)
(* Proof with solve_false; inverts_all_ord. *)
(*   introv Ord Spl Dis1 Dis2. *)
(*   indTypSize (size_typ A + size_typ B). *)
(*   inverts Spl; intros; inverts_all_distinguishability; eauto. *)
(*   - forwards: IH; try eassumption; elia. applys~ DistIntersectLSym. *)
(*   - applys~ DistIntersectRSym. applys IH; try eassumption; elia. *)
(*   - applys* distinguishability_forall_r Dis1. *)
(*   - inverts Dis1... *)
(*     + (* rcd *) *)
(*       inverts Dis2... *)
(*       applys DistIn. applys~ IH H. elia. *)
(*     + inverts Dis2... *)
(*       * applys~ DistIntersectL. applys~ IH H1 H8. elia. *)
(*       * applys~ DistIntersectR. applys~ IH H8. elia. *)
(*       inverts_all_distinguishability. inverts~ H0. *)
(*   all: . *)
(*   - applys~ DistIntersectLSym. *)
(*   - *)

Lemma distinguishabilityAx_downward : forall A B B',
    DistinguishabilityAx A B -> B' <: B -> Distinguishability A B'.
Proof with try reflexivity; elia; auto.
  introv Dis Sub.
  inverts~ Dis. convert2asub.
  inductions Sub; solve_false; inverts_all_spl; auto.
  - forwards: IHSub1...
  - forwards: IHSub... applys~ distinguishability_spli_l_1 H.
  - forwards: IHSub... applys~ distinguishability_spli_l_2 H.
  - forwards: IHSub1... forwards: IHSub2...
Abort.

Lemma distinguishability_downward : forall A B B',
    Distinguishability A B -> B' <: B -> Distinguishability A B'.
Proof.
  introv Dis Sub.
  indTypSize (size_typ A + size_typ B + size_typ B').
  forwards [?|(?&?&?)]: ordu_or_split A. now eauto. Abort.
  (* 2: { forwards (HA&HB): distinguishability_splu_inv Dis. *)
  (*   forwards (HA1&HA2): HA H. *)
  (*   forwards: IH HA1 Sub. elia. forwards: IH HA2 Sub. elia. } *)
  (* (* ordi A & ordu A *) *)
  (* forwards [?|(?&?&?)]: ordu_or_split B'. now eauto. *)
  (* 2: { convert2asub. auto_inv. convert2dsub. *)
  (*      forwards: IH Dis H0. elia. forwards: IH Dis H1. elia. *)
  (*      applys~ distinguishability_splu_r H. } *)

(*       induction Dis; intros. *)
(*     inverts Ord; solve_false. repeat convert2asub. inverts Sub try solve [repeat convert2asub; inverts Sub]. *)
(*   - repeat convert2asub. inverts Sub; solve_false; auto. *)
(*     + inverts~ Dis. *)

(*   - repeat convert2asub. inverts Sub; solve_false; auto. *)
(*     + false. eauto. *)
(*     + econstructor. inverts Ord. convert2dsub. applys~ IHDis. *)
(*     + inverts H. (* relies on distinguishability_spli_inv *) *)
(*   - *)
(*     distinguishability_spli_inv *)
(*       Restart. *)
(*     introv Dis Sub Nsub Ord. gen B'. *)
(*     induction Dis; intros. *)
(*   - inverts Sub; solve_false; auto. *)
(*     (* applys* Nsub. convert2asub. eauto. *) *)
(* Admitted. *)

(* Lemma B.12 *)
Lemma dispatch_ord : forall A1 A2 B B' C1 C2',
    ordu B -> ordu B' -> Mergeability A1 A2 ->
    ApplyTy A1 B C1 -> NApplyTy A1 B' -> ApplyTy A2 B' C2' ->
    Distinguishability B B'.
Proof.
  introv Ord1 Ord2 Meg App1 Napp1 App2. gen B B' C1 C2'.
  induction Meg; intros.
  all: try solve [inverts Napp1; inverts App1; inverts App2; solve_false].
  - (* arrow *)
    inverts App1; inverts Napp1; inverts App2.
    + Abort.
(* A <> B *)
(* C1 <: A *)
(* C2 <: B *)
(* ~ C2 <: A *)
(* splu C1 =/> *)
(* splu C2 =/> *)
(* ----------- *)
(* C1 <> C2 *)
(*****************************************************************************)

  (*     match goal with *)
  (*     | H1: declarative_subtyping ?B _, H2: declarative_subtyping _  _ |- _ => idtac end. *)
  (*         false; apply H3; applys DSub_Trans H2 H1 *)
  (* end. *)
  (* , H2: declarative_subtyping _ ?B , *)
  (*       H3: ~ (declarative_subtyping ?C ?A)| *)

Lemma applyty_iso : forall A B1 C1 B2 C2,
    ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2
    -> C1 ~= C2.
Proof with elia.
  introv HHA1 HHA2.
  indTypSize (size_typ A + size_typ B1 + size_typ B2).
  inverts keep HHA1; inverts keep HHA2; auto.
  all: repeat match goal with
              | H: ApplyTy _ _ ?A |- _ ~= ?A|?B => forwards~ : IH HHA1 H; elia; clear H
              | H: ApplyTy _ _ ?B |- _ ~= ?A|?B => forwards~ : IH HHA1 H; elia; clear H
              | H: ApplyTy _ _ ?A |- ?A|?B ~= _ => forwards~ : IH H HHA2; elia; clear H
              | H: ApplyTy _ _ ?B |- ?A|?B ~= _ => forwards~ : IH H HHA2; elia; clear H
              end.
  all: clear HHA1 HHA2.
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
  (* - exists (B1 | C) (B2 | C)... *)
  (* - inverts Spl2. *)
  (*   + forwards (T1&T2&?): IH H0 H6... destruct_conj. *)
  (*     exists (T1&B0) (T2&B0)... *)
    + (* A0 & B0 where splitu A0 = A1|A2 and A1 is ordu *)
Abort. (* counter example exists *)


Lemma dispatch_neg : forall A B1 B2 C1 C2,
    TypeWF nil A -> isNegTyp B1 -> isNegTyp B2 ->
    ApplyTy A (fty_StackArg B1) C1 -> ApplyTy A (fty_StackArg B2) C2 -> C1 ~= C2.
Proof.
  intros A B1 B2 C1 C2 Tw Neg1 Neg2 App1 App2. gen B1 B2 C1 C2.
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

Definition applicable A B := exists C, ApplyTy A B C.

Definition similar A B := exists V, splu V A B /\ isValTyp V.

Lemma similar_rcd_inv : forall l1 l2 A B,
    similar (t_rcd l1 A) (t_rcd l2 B) -> similar A B.
Proof with solve_false.
  introv HS.
  unfolds in HS. destruct_conj.
  inverts H... inverts H0...
  unfolds. exists. split.
  all: eassumption.
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
    + solve_false.
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
Abort.

(****************************************************************************)
(* B.14 If apply(A, V) => C and V'/V => ok and apply(A, V')=>C' then C <: C' *)
Lemma apply_valtyp_psub : forall (A V C V' C' : typ),
    isValTyp V -> isValTyp V' -> ApplyTy A V C -> V' <p V -> ApplyTy A V' C' -> C <: C'.
Proof with elia; solve_false.
  introv Val1 Val2 App1 PSub App2.
  indTypSize (size_typ V + size_typ V' + size_typ A).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split V'.
  lets~ [Hu'|(?&?&Hu')]: ordu_or_split V.
  - (* V and V' ordu *)
    inverts App1... (* analysis the form of A *)
    + (* bot *) eauto.
    + (* arrow *) inverts~ App2...
    + (* union *) inverts~ App2...
      repeat match goal with
        H1: ApplyTy ?A _ _, H2: ApplyTy ?A _ _ |- _ =>
        forwards~: IH H1 H2; elia; clear H1
             end.
    + (* intersection *) inverts~ App2...
      * repeat match goal with
                 H1: ApplyTy ?A _ _, H2: ApplyTy ?A _ _ |- _ =>
                 forwards~: IH H1 H2; elia; clear H1
               end.
      * admit.
     (* The key case? *)
     (*   Hu : ordu V' *)
     (*   Hu': ordu V  *)
     (* PSub : V' <p V *)
     (*   H0 : ApplyTy A1 V C *)
     (*   H1 : NApplyTy A2 V *)
     (*   H5 : NApplyTy A1 V' *)
     (*   H8 : ApplyTy A2 V' C' *)
     (*   ============================ *)
     (*   C <: C' *)
     * repeat match goal with
                H1: ApplyTy ?A _ _, H2: ApplyTy ?A _ _ |- _ =>
                      forwards~: IH H1 H2; elia; clear H1
              end. admit.
       (* Similar case *)
       (* Hu : ordu V' *)
       (* Hu' : ordu V *)
       (* H0 : ApplyTy A1 V C *)
       (* H1 : NApplyTy A2 V *)
       (* H5 : ApplyTy A1 V' A1' *)
       (* H8 : ApplyTy A2 V' A2' *)
       (* ============================ *)
       (* C <: A1' & A2' *)
    + (* intersection again *) admit.
    + (* intersection again *) admit.
  - forwards HS1: psub_trans PSub.
    applys~ psub_splu_valtyp_left Hu'.
    forwards HS2: psub_trans PSub.
    applys~ psub_splu_valtyp_right Hu'.
    forwards: applyty_splitu_arg_inv App1 Hu'. destruct_conj. subst.
    forwards: IH HS1; try eassumption. now eauto. now elia.
    forwards: IH HS2; try eassumption. now eauto. now elia.
    eauto.
  - forwards~ HS1: psub_trans (psub_splu_valtyp_left_rev _ _ _ Hu) PSub.
    forwards~ HS2: psub_trans (psub_splu_valtyp_right_rev _ _ _ Hu) PSub.
    forwards: applyty_splitu_arg_inv App2 Hu. destruct_conj. subst.
    forwards: IH HS1; try eassumption. now eauto. now elia.
    forwards: IH HS2; try eassumption. now eauto. now elia.
    eauto.
Abort. (* move to dispatch.v *)

(******************************************************************************)
#[export]
Hint Extern 0 =>
match goal with
| H: NotDistinguishable _ _ |- _ => inverts H; fail
| H: NotDistinguishableTypes _ |- _ => inverts H; fail
end : FalseHd.

Lemma distinguishability_complement_ord : forall A B,
    ordi A -> ordu A -> ordi B -> ordu B ->
    Distinguishability A B -> NotDistinguishable A B -> False.
Proof with solve_false.
  introv HIA HUA HIB HUB HD HN.
  induction HN...
  all: inverts_all_ord.
  - inverts~ HD...
  - inverts~ H0.
    all: inverts HD...
  - inverts~ H0.
    all: inverts HD...
  - inverts H; inverts H0; inverts HD...
Qed.

Lemma distinguishability_decidable_ord: forall A B,
    ordi A -> ordu A -> ordi B -> ordu B ->
    Distinguishability A B \/ NotDistinguishable A B.
Proof with solve_false.
  introv HIA HUA HIB HUB.
  gen B. induction A; intros...
  - admit.
  - induction B...
    + right*.
    + case_eq (@eq_dec _ label_dec l5 l0); intros; subst; inverts_all_ord.
      * forwards~ [?|?]: IHA B.
      * left*.
    + right*. + right*. + right*.
    + left*.
  - destruct B; clear HIA HUA IHA1 IHA2...
    all: clear HUB HIB; try solve [left*]; try solve [right*].
    + right*. applys~ NDistAxAx.
Admitted.

Lemma NDist_or_inv : forall A B C,
    NotDistinguishable (A | B) C -> NotDistinguishable A C \/
                                      NotDistinguishable B C.
Proof with solve_false.
  intros A B C. gen A B.
  induction C; introv HN.
  1,2,3,6,7,8,9: now inverts~ HN...
  - (* inter *) inverts~ HN...
    forwards~ : IHC1 H2. forwards~ : IHC2 H3.
Abort.

(* Counter example *)
(* A | B <X> C & D *)

Lemma distinguishability_complement : forall A B,
    Distinguishability A B -> NotDistinguishable A B -> False.
Proof with solve_false.
  introv HD HN.
  induction HD.
  - inverts HN...
Abort.

Lemma distinguishability_decidable: forall A B,
    Distinguishability A B \/ NotDistinguishable A B.
Abort.

Lemma notdistinguishability_upward : forall A B B',
    NotDistinguishable A B -> B <: B' -> NotDistinguishable A B'.
Abort.
*)
