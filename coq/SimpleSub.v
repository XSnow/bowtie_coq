Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export DistSubtyping.

Notation "A <p B"        := (PositiveSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Notation "A <n B"        := (NegativeSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Ltac auto_lc := try match goal with
                    | |- lc_typ _ => eauto
                    end.

#[export]
Hint Extern 0 =>
lazymatch goal with
| H : binds _ _ nil |- _ => inverts H; fail
end : FalseHd.

#[export]
 Hint Extern 1 => lazymatch goal with
                 | H: DistinguishabilityAx _ _ |- _ => inverts H; fail
end : FalseHd.

Lemma valtyp_bot_false :  isValTyp t_bot -> False.
Proof. introv H. inverts H. inverts H0. Qed.

#[export] Hint Immediate valtyp_bot_false : FalseHd.

Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].
Ltac inverts_neg_false :=
  match goal with
  | H: isNegTyp _ |- _ => inverts H; fail
  end.

#[export]
Hint Extern 1 => inverts_neg_false : FalseHd.

#[export]
Hint Extern 2 => repeat lazymatch goal with
                 | H: isNegTyp (_ & _) |- _ => inverts H
                 | H: isNegTyp (_ | _) |- _ => inverts H
                 end; inverts_neg_false : FalseHd.

#[export]
 Hint Extern 2 =>
  repeat lazymatch goal with
  | H1: isValTyp (_ & _) |- _ => inverts H1
  | H1: isValTyp (_ | _) |- _ => inverts H1
  | H1: isValTyp (t_rcd _ _) |- _ => inverts H1
   end;
  try lazymatch goal with
  | H1: isValTyp t_bot |- _ => inverts H1
  | H1: isValTyp (t_tvar_b _) |- _ => inverts H1
  | H1: isValTyp (t_tvar_f _) |- _ => inverts H1
   end; inverts_neg_false : FalseHd.

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
  induction i as [ | i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

(*-------------------------- neg types and val types -------------------------*)

Lemma isnegtyp_lc : forall A, isNegTyp A -> lc_typ A.
Proof. introv H. induction~ H. Qed.

Lemma isvaltyp_lc : forall A, isValTyp A -> lc_typ A.
Proof. introv H. induction H; auto using isnegtyp_lc. Qed.

#[export] Hint Immediate isnegtyp_lc isvaltyp_lc : core.

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
  - inverts Spl. forwards* : IHVal.
  - forwards* (?&?): negtyp_splu_inv H.
Qed.

Lemma valtyp_rcd_inv : forall l V,
    isValTyp(t_rcd l V) -> isValTyp V.
Proof.
  introv H. inverts~ H. inverts H0.
Qed.

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
  all: auto.
  all: solve_false.
Qed.

Ltac inverts_typ :=
  try
    lazymatch goal with
    | H1:isValFty (fty_StackArg (_ & _)) |- _ => inverts H1
    | H1:isValFty (fty_StackArg (_ | _)) |- _ => inverts H1
    | H1:isValTyp (_ & _) |- _ => inverts H1
    | H1:isValTyp (_ | _) |- _ => inverts H1
    | H1:isValTyp (t_rcd _ _) |- _ => apply valtyp_rcd_inv in H1
    | H1:isValTyp ?A, H2:spli ?A _ _ |- _ => forwards (?, ?) : valtyp_spli_inv H1 H2
    | H1:isValTyp ?A, H2:splu ?A _ _ |- _ => forwards (?, ?) : valtyp_splu_inv H1 H2
    end;
  try
    lazymatch goal with
    | H1:isNegTyp t_bot |- _ => inverts H1
    | H1:isNegTyp (t_rcd _ _) |- _ => inverts H1
    | H1:isNegTyp (_ & _) |- _ => inverts H1
    | H1:isNegTyp (_ | _) |- _ => inverts H1
    | H1:isNegTyp ?A, H2:spli ?A _ _ |- _ => forwards (?, ?) : negtyp_spli_inv H1 H2
    | H1:isNegTyp ?A, H2:splu ?A _ _ |- _ => forwards (?, ?) : negtyp_splu_inv H1 H2
    end.

#[export] Hint Extern 1 (isValTyp _) => inverts_typ : core.

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

(* B.3 (1) *)
Lemma psub_rcd_inv : forall V l B,
    V <p (t_rcd l B) -> exists A, V = t_rcd l A /\ A <p B.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

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
  - (* rcd *) inverts Sub. solve [forwards [?|?]: IHSpl; try eassumption; eauto].
    inverts H0.
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

(*-------------------------- psub admissible rules  -------------------------*)

Lemma psub_merge_intersection : forall A B B1 B2,
    spli B B1 B2 -> isValTyp A -> A <p B1 -> A <p B2 -> A <p B.
Proof.
  introv Spl Val Sub1 Sub2. gen A.
  induction* Spl; intros; auto.
  - inverts_psub Sub1; inverts_psub Sub2; eauto.
  - inverts_psub Sub1; inverts_psub Sub2; eauto.
  - inverts_psub Sub1; inverts_psub Sub2; subst; eauto.
    injection H; intros; subst. inverts_typ.
    forwards~: IHSpl x0.
Qed.

Lemma psub_spli_left : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A1 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A2.
  induction Sub; intros; eauto.
  - (* rcd *) inverts~ Spl; inverts_typ; solve_false.
    constructor*.
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
  -(* record *)
    inverts Sub.
    + inverts_typ; eauto... forwards: IH H; try eassumption; elia. eauto.
    + inverts Val... applys~ PSub_UnionL. applys psub_rcd H2. applys* psub_splu_valtyp_left.
    + inverts Val... applys~ PSub_UnionR. applys psub_rcd H2. applys* psub_splu_valtyp_left.
    + inverts Val... applys~ PSub_Intersect.
      * applys psub_rcd H1. applys* psub_splu_valtyp_left.
      * applys psub_rcd H2. applys* psub_splu_valtyp_left.
    + inverts Val... eauto.
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
  -(* record *)
    inverts Sub.
    + inverts_typ; eauto... forwards: IH H; try eassumption; elia. eauto.
    + inverts Val... applys~ PSub_UnionL. applys psub_rcd H2. applys* psub_splu_valtyp_right.
    + inverts Val... applys~ PSub_UnionR. applys psub_rcd H2. applys* psub_splu_valtyp_right.
    + inverts Val... applys~ PSub_Intersect.
      * applys psub_rcd H1. applys* psub_splu_valtyp_right.
      * applys psub_rcd H2. applys* psub_splu_valtyp_right.
    + inverts Val... eauto.
Qed.

Lemma psub_andl_inv : forall A B C,
    A & B <p C -> A <p C /\ B <p C.
Proof.
  introv H.
  inductions H; inverts_typ; auto_lc; split~.
  all: try forwards: IHPositiveSubtyping; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping1; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping2; try reflexivity; destruct_conj.
  - applys* PSub_UnionL.
  - applys* PSub_UnionL.
  - applys* PSub_UnionR.
  - applys* PSub_UnionR.
  - applys* PSub_Intersect.
  - applys* PSub_Intersect.
Qed.

Lemma psub_orl_inv : forall A B C,
    A | B <p C -> A <p C /\ B <p C.
Proof.
  introv H.
  inductions H; inverts_typ; auto_lc; split~.
  all: try forwards: IHPositiveSubtyping; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping1; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping2; try reflexivity; destruct_conj.
  - applys* PSub_UnionL.
  - applys* PSub_UnionL.
  - applys* PSub_UnionR.
  - applys* PSub_UnionR.
  - applys* PSub_Intersect.
  - applys* PSub_Intersect.
Qed.

Lemma psub_forall_inv : forall A B C,
    t_forall A <p C -> lc_typ (t_forall B) -> t_forall B <p C.
Proof.
  introv H Lc.
  inductions H; eauto.
  all: try forwards: IHPositiveSubtyping1; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping2; try reflexivity; destruct_conj.
  all: auto_lc.
  eauto.
Qed.

Lemma psub_arrow_inv : forall A B C D1 D2,
    t_arrow A B <p C -> lc_typ (t_arrow D1 D2) -> t_arrow D1 D2 <p C.
Proof.
  introv H Lc.
  inductions H; eauto.
  all: try forwards: IHPositiveSubtyping1; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping2; try reflexivity; destruct_conj.
  all: auto_lc.
  eauto.
Qed.

Lemma psub_spli_l_inv : forall A A1 A2 C,
    spli A A1 A2 -> isValTyp A -> A <p C -> A1 <p C /\ A2 <p C.
Proof.
  introv Spl Val Sub.
  indTypSize (size_typ A + size_typ C).
  destruct A; intros; inverts_typ; solve_false.
  - inverts Spl. inverts Sub.
    + forwards: IH H4; try eassumption; elia; destruct_conj.
      split; applys~ PSub_In.
    + forwards* (?&?): IH H1; elia.
    + forwards* (?&?): IH H1; elia.
    + forwards~ (?&?): IH H0; [eauto | ..]; elia.
      forwards~ (?&?): IH H1; [eauto | ..]; elia.
      split*.
    + split*.
  - inverts Spl. applys~ psub_andl_inv.
  - apply psub_orl_inv in Sub. destruct_conj.
    inverts Spl.
    + split; applys* psub_unionR.
    + split; applys* psub_unionL.
  - inverts Spl; split; applys* psub_arrow_inv.
  - inverts Spl; split; applys* psub_forall_inv.
Qed.

Lemma psub_splu_l_inv : forall A A1 A2 C,
    splu A A1 A2 -> isValTyp A -> A <p C -> A1 <p C /\ A2 <p C.
Proof.
  introv Spl Val Sub.
  indTypSize (size_typ A + size_typ C).
  destruct A; intros; inverts_typ; solve_false.
  - inverts Spl. inverts Sub.
    + forwards: IH H4; try eassumption; elia; destruct_conj.
      split; applys~ PSub_In.
    + forwards* (?&?): IH H1; elia.
    + forwards* (?&?): IH H1; elia.
    + forwards~ (?&?): IH H0; [eauto | ..]; elia.
      forwards~ (?&?): IH H1; [eauto | ..]; elia.
      split*.
    + split*.
  - apply psub_andl_inv in Sub. destruct_conj.
    inverts Spl.
    + forwards: IH; [ | eassumption | ..]; try eassumption; elia. now eauto.
      destruct_conj. split; applys* psub_spli_left.
    + forwards: IH; [ | eassumption | ..]; try eassumption; elia. now eauto.
      destruct_conj. split; applys* psub_spli_left.
  - inverts Spl. applys~ psub_orl_inv.
  - inverts Spl; split; applys* psub_forall_inv.
Qed.

Ltac inverts_all_psub :=
  repeat lazymatch goal with
    | Sub : _ & _ <p _ |- _ =>
        forwards (?&?): psub_andl_inv Sub; clear Sub
    | Sub : _ | _ <p _ |- _ =>
                  forwards (?&?): psub_orl_inv Sub; clear Sub
    | Sub : _ <p _ & _ |- _ =>
        forwards (?&?): psub_and_inv Sub; clear Sub
    | Sub : _ <p (t_rcd _ _) |- _ =>
        forwards (?&?&?): psub_rcd_inv Sub; clear Sub
    | Sub : _ <p ?B, Hspl: spli ?B _ _ |- _ =>
        forwards (?&?): psub_spli_inv Hspl Sub; clear Sub
    | Sub : t_forall _ <p _ |- _ =>
        lets: psub_forall_inv Sub; clear Sub
    | Sub : ?A <p _, Hspl: splu ?A _ _ |- _ =>
        forwards (?&?): psub_splu_l_inv Hspl Sub; clear Sub
    | Sub : ?A <p _, Hspl: spli ?A _ _ |- _ =>
        forwards (?&?): psub_spli_l_inv Hspl Sub; clear Sub
    | Sub : _ <p ?B, Hspl: splu ?B _ _ |- _ =>
        forwards [?|?]: psub_splu_inv Hspl Sub; clear Sub
    | Sub : _ <p _ | _ |- _ =>
                       forwards [?|?]: psub_or_inv Sub; clear Sub
    end;
  try lazymatch goal with |- isValTyp _ => eauto 2 end.

Lemma nsub_negtyp : forall V1 V2 A,
    A <n (fty_StackArg V1) -> isNegTyp V1 -> isNegTyp V2 -> A <n (fty_StackArg V2).
Proof.
  introv Sub Neg1 Neg2. gen V2.
  inductions Sub; try solve [inverts Neg1]; intros; eauto using psub_negtyp.
Qed.

(*--------------- Lemma B.1 Completeness of Coverage Relations ---------------*)

(* Completeness of Coverage Relations [1] *)
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
    all: (* rcd *) try solve [inverts* Sub].
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
    all: (* rcd *) try solve [inverts* Sub].
    all: applys nsub_negtyp; try eassumption.
    all: inverts_typ; eauto; inverts_typ; eauto; solve_false.
  - (* or *)
    inverts* Sub.
  - (* top *)
    inverts* Sub.
Qed.

(* Completeness of Coverage Relations [2] *)
Lemma apply2nsub : forall A F C,
    isNegTyp A -> isValFty F -> ApplyTy A F C -> A <n F.
Proof with auto.
  introv Neg Val App.
  induction App; try solve [inverts Neg]; inverts Val...
  - (* arrow *)
    inverts* H0. constructor~.
    applys~ sub2psub.
  - (* union *) inverts* Neg...
  - (* union *) inverts* Neg...
  - (* splu *) inverts_typ. applys* nsub_unionL.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
  - (* intersection *) inverts* Neg.
Qed.

(*------------------------------ Lemma B.2 -----------------------------------*)

Lemma psub_sub_bot_inv : forall V A,
    V <p A -> A <: t_bot -> False.
Proof.
  introv PSub Sub. convert2asub. gen V.
  inductions Sub; intros; eauto; solve_false.
  inverts_psub PSub; now eauto.
  inverts_psub PSub; now eauto.
  inverts_psub PSub; now eauto.
Qed.

(*----------- Lemma B.4 Inversion of Subtyping on (Co-)Value types -----------*)

Lemma negtyp_sub_rcd_inv : forall Aneg l A,
    isNegTyp Aneg -> Aneg <: (t_rcd l A) -> False.
Proof with convert2asub; try eassumption; elia.
  introv Neg Sub.
  indTypSize (size_typ Aneg + size_typ A).
  lets [Hi|(?&?&Hi)]: ordi_or_split A... now eauto.
  - gen l A. inverts Neg; intros; convert2asub; solve_false.
    + forwards [?|?]: algo_sub_andlr_inv Sub; [eauto | eauto |.. ].
      applys IH A...  applys IH B...
    + cut (A <:: t_rcd l A0). cut (B <:: t_rcd l A0).
      * intros. applys IH...
      * applys algo_trans Sub. eauto.
      * applys algo_trans Sub. eauto.
  - forwards (?&?): algo_sub_and_inv Sub.
    now eauto.
    applys IH Neg...
Qed.

(* B.4 [1]) *)
Lemma valtyp_sub_rcd_inv : forall V l A,
    isValTyp V -> V <: (t_rcd l A) -> exists B, V = t_rcd l B.
Proof.
  introv Val Sub.
  induction Val.
  - convert2asub. auto_inv. eauto.
  - false. applys* negtyp_sub_rcd_inv A0.
Qed.

(* B.4 [1] *)
Lemma valtyp_sub_rcd_inv_2 : forall V l A,
    isValTyp V -> V <: (t_rcd l A) -> exists B, V = t_rcd l B /\ B <p A.
Proof.
  introv Val Sub.
  apply sub2psub in Sub.
  applys~ psub_rcd_inv.
  auto.
Qed.

(* B.4 [2] *)
Lemma valtyp_sub_arrow_inv : forall V A B,
    isValTyp V -> V <: (t_arrow A B) -> isNegTyp V.
Proof.
  introv Val Sub.
  induction~ Val; intros.
  - convert2asub; solve_false.
Qed.

(* B.4 [3] *)
Lemma valtyp_sub_forall_inv : forall V A,
    isValTyp V -> V <: (t_forall A) -> isNegTyp V.
Proof.
  introv Val Sub.
  induction~ Val; intros.
  - convert2asub; solve_false.
Qed.

(* B.4 [4] *)
Lemma valtyp_bot_inv : forall V,
    isValTyp V -> V <: t_bot -> False.
Proof.
  introv Val Sub.
  induction~ Val; intros.
  - convert2asub; solve_false.
  - induction H; convert2asub; solve_false; auto_inv.
    forwards~ [?|?]: algo_sub_andlr_inv Sub; clear Sub.
    all: convert2dsub; eauto.
Qed.

(******************************************************************************)
(** similar *)

Definition similar A B := exists V, splu V A B /\ isValTyp V.

Lemma similar_rcd_inv : forall l1 l2 A B,
    similar (t_rcd l1 A) (t_rcd l2 B) -> similar A B.
Proof with solve_false.
  introv HS.
  unfolds in HS. destruct_conj.
  inverts H... inverts_typ...
  unfolds. inverts*H0.
Qed.

Lemma similar_rcd : forall l A B,
    similar A B -> similar (t_rcd l A) (t_rcd l B).
Proof.
  introv Sim.
  unfolds. unfolds in Sim. destruct_conj.
  exists*.
Qed.

(* Properties of the Union-Split Results of a Value Type (Similar Types) [1] *)
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
    + applys~ Sim_Neg.
Qed.

Lemma sim_psub : forall A B,
    sim A B -> A <p B.
Proof.
  introv H.
  induction* H.
Qed.

Lemma sim_psub_2 : forall A B,
    sim A B -> B <p A.
Proof.
  introv H.
  induction* H.
Qed.
