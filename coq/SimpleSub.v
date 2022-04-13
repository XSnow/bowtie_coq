(* B.1 B.2 B.3 (1)-(3) *)

Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export MatchTy.

Notation "A <p B"        := (PositiveSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Notation "A <n B"        := (NegativeSubtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.

Ltac auto_lc := try match goal with
                    | |- lc_typ _ => eauto
                    end.

#[export]
Hint Extern 1 False =>
    match goal with
    | H : isValTyp (t_rcd _ _ | t_rcd _ _ ) |- _ => inverts H
    end;
    match goal with
    | H : isNegTyp (t_rcd _ _ | t_rcd _ _ ) |- _ => inverts H
    end;
    try match goal with
    | H : isNegTyp (t_rcd _ _ ) |- _ => inverts H
      end : FalseHd.

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


(* I break this intentionally to save sub2psub *)
Lemma psub_valtyp : forall A B,
    A <p B -> isValTyp A.
Abort.
(* Proof. *)
(*   introv Sub. *)
(*   induction* Sub. *)
(* Qed. *)

(* #[export] Hint Immediate psub_valtyp : core. *)

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

Lemma psub_or_r_inv : forall V B1 B2,
    V <p B1 | B2 -> V <p B1 \/ V <p B2.
Proof.
  introv Sub.
  inverts~ Sub. inverts~ H0.
Qed.

Lemma psub_and_r_inv : forall V B1 B2,
    V <p B1 & B2 -> V <p B1 /\ V <p B2.
Proof.
  introv Sub.
  inverts~ Sub. inverts~ H0.
Qed.

(* B.3 (1) *)
Lemma psub_rcd_r_inv : forall V l B,
    V <p (t_rcd l B) -> exists A, V = t_rcd l A /\ A <p B.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

(* I tried remove the Val condition but then the proof does not work? *)
Lemma psub_spli_r_inv : forall A B B1 B2,
    spli B B1 B2 -> isValTyp A -> A <p B -> A <p B1 /\ A <p B2.
Proof.
  introv Spl Val Sub. gen A.
  induction* Spl; split; intros.
  all: try solve [inverts~ Sub; match goal with H: isNegTyp _ |- _ => inverts~ H end].
  all: inverts~ Sub; try match goal with H: isNegTyp _ |- _ => inverts~ H end; forwards (?&?): IHSpl; try eassumption; now eauto.
Qed.

Lemma psub_splu_r_inv : forall A B B1 B2,
    splu B B1 B2 -> isValTyp A -> A <p B -> A <p B1 \/ A <p B2.
Proof.
  introv Spl Val Sub. gen A.
  induction* Spl; intros.
  all: try forwards [?|?]: psub_or_r_inv Sub.
  all: try forwards (?&?): psub_and_r_inv Sub.
  all: try solve [inverts~ Sub; match goal with H: isNegTyp _ |- _ => inverts~ H end].
  all: try solve [forwards [?|?]: IHSpl; try eassumption; eauto].
  - (* forall *) left. eauto.
  - (* rcd *) inverts Sub. solve [forwards [?|?]: IHSpl; try eassumption; eauto].
    inverts H0.
Qed.

Lemma psub_and_l_inv : forall A B C,
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

Local Ltac inverts_psub H :=
  try forwards [?|?]: psub_or_r_inv H;
  try forwards (?&?): psub_and_r_inv H;
  try forwards (?&?&?): psub_rcd_r_inv H;
  try match type of H with
        ?A <p ?B => match goal with
                    | Hspl: spli B _ _ |- _ =>
                      forwards (?&?): psub_spli_r_inv Hspl H
                    | Hspl: splu B _ _ |- _ =>
                      forwards [?|?]: psub_splu_r_inv Hspl H
                    end;
                    match A with
                    | _ & _ => forwards (?&?): psub_and_l_inv H
                    end
    end;
  subst.

Lemma psub_bot_r_inv : forall V,
    V <p t_bot -> False.
Proof.
  introv Sub.
  inverts* Sub. inverts~ H0.
Qed.

#[export] Hint Immediate psub_bot_r_inv : FalseHd.

(*-------------------------- psub admissible rules  -------------------------*)

Lemma psub_spli_r : forall A B B1 B2,
    spli B B1 B2 -> isValTyp A -> A <p B1 -> A <p B2 -> A <p B.
Proof.
  introv Spl Val Sub1 Sub2. gen A.
  induction* Spl; intros.
  - inverts_psub Sub1; inverts_psub Sub2; eauto.
  - inverts_psub Sub1; inverts_psub Sub2; eauto.
  - inverts_psub Sub1; inverts_psub Sub2; subst; eauto.
    injection H; intros; subst. inverts_typ.
    forwards~: IHSpl x0.
Qed.

Lemma psub_spli_l_1 : forall A A1 A2 B,
    spli A A1 A2 -> isValTyp A -> A1 <p B -> A <p B.
Proof.
  introv Spl Val Sub. gen A A2.
  induction Sub; intros; eauto.
  - (* rcd *) inverts~ Spl; inverts_typ; solve_false.
    constructor*.
Qed.

Lemma psub_spli_l_2 : forall A A1 A2 B,
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
  (* stuck here because of valtyp conditions; going to remove them in psub *)
Abort.

Lemma psub_splu_right : forall A B B1 B2,
    splu B B1 B2 -> A <p B2 -> A <p B.
Proof.
  introv Spl Sub. gen A.
  induction Spl; intros; eauto.
  all: inverts_psub Sub; eauto.
Qed.

#[export] Hint Immediate psub_spli_l_1 psub_spli_l_2 psub_splu_left psub_splu_right : core.

Lemma psub_refl : forall A,
    isValTyp A -> A <p A.
Proof.
  introv H. induction~ H.
Qed.

(* (5) If split(V) => V1 | V2 then V1/V => ok and V2/V => ok *)
Lemma psub_splu_valtyp_rev : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A1 <p A \/ A2 <p A.
Proof.
  introv Spl Val.
  inverts_typ; solve_false.
  3: inverts H3.
  1,3: left; applys psub_splu_left Spl; applys* psub_refl.
  all: right; applys psub_splu_right Spl; applys* psub_refl.
Qed.

Lemma psub_splu_valtyp : forall A A1 A2,
    splu A A1 A2 -> isValTyp A -> A <p A1 \/ A <p A2.
Proof.
  introv Spl Val.
  induction Spl; inverts Val; eauto; solve_false.
  all: try forwards [?|?]: IHSpl; [eauto | .. ].
  all: inverts_typ; eauto.
  - left; applys~ psub_spli_l_1.
  - right; applys~ psub_spli_l_1.
  - left; applys~ psub_spli_l_2.
  - right; applys~ psub_spli_l_2.
  - constructor*.
Qed.

Lemma psub_negtyp : forall V1 V2 A,
    V1 <p A -> isNegTyp V1 -> isValTyp V2 -> V2 <p A.
Proof.
  introv Sub Neg Val. gen V2.
  induction Sub; try solve [inverts Neg]; intros; eauto.
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
  inverts~ Sub.
  - (* record *)
    inverts Spl...
Abort. (* broken *)
(*     inverts Val. inverts H3.  inverts H7. solve_false. *)
(*     + inverts_typ... applys* PSub_Neg. constructor. *)
(*   - forwards: IH H1; [ | eassumption | .. ]; auto; elia. *)
(*   - forwards: IH H1; [ | eassumption | .. ]; auto; elia. *)
(*   - forwards: IH H0; [ | eassumption | .. ]; auto; elia. *)
(*     forwards: IH H1; [ | eassumption | .. ]; auto; elia. *)
(*   - *)
(*   inverts Spl; intros. *)
(*   - (* union at left *) inverts_typ; eauto. destruct Sub. applys psub_negtyp; try eassumption. *)
(*   - (* inter at left *) inverts_typ; eauto. inverts_typ; eauto. *)
(*     applys~ psub_negtyp Sub. *)
(*   - (* inter at left *) inverts_typ; eauto. inverts_typ; eauto. *)
(*     applys~ psub_negtyp Sub. *)
(*   - (* forall *) applys~ psub_forall Sub. *)
(*   -(* record *) *)
(*     inverts Sub. *)
(*     + inverts_typ; eauto... forwards: IH H; try eassumption; elia. eauto. *)
(*     + inverts_typ; eauto... *)
(*     + inverts Val... applys~ PSub_UnionL. applys psub_rcd H2. applys* psub_splu_valtyp_left. *)
(*     + inverts Val... applys~ PSub_UnionR. applys psub_rcd H2. applys* psub_splu_valtyp_left. *)
(*     + inverts Val... applys~ PSub_Intersect. *)
(*       * applys psub_rcd H1. applys* psub_splu_valtyp_left. *)
(*       * applys psub_rcd H2. applys* psub_splu_valtyp_left. *)
(*     + inverts Val... eauto. *)
(* Qed. *)


(* c V / (c A | Bneg) => + *)
(* V  / (c A | Bneg) => + *)
(* But (c V | V) / (c A | Bneg) =/> + *)
(* this union is not a ValTyp *)
Lemma psub_union : forall A A1 A2 B,
    splu A A1 A2 -> isValTyp A -> A1 <p B -> A2 <p B -> A <p B.
Proof with solve_false.
  introv Spl Val Sub1 Sub2.
  indTypFtySize (size_typ A + size_typ B).
  inverts Spl; inverts_typ...
  all: try solve [ applys psub_negtyp; [ | eassumption | ..]; eauto ].
  all: repeat match goal with
         | H : _&_ <p _ |- _ => forwards (?&?): psub_and_l_inv H; clear H
         end.
  - applys* psub_spli_l_2.
  - applys* psub_spli_l_1.
  - applys* psub_negtyp.
  - (* record *)
    inverts~ Sub1; inverts~ Sub2...
    + forwards~: IH H H4 H6; elia.
    + eapply SpU_in in H. forwards: IH H; try eassumption; elia; eauto.
    + forwards~ [HN|HN]: psub_splu_valtyp H.
      all: applys* psub_rcd HN.
    + forwards~ [HN|HN]: psub_splu_valtyp H.
      all: applys* psub_rcd HN.
    + forwards~ [HN|HN]: psub_splu_valtyp H.
      all: applys* psub_rcd HN.
    + forwards~ [HN|HN]: psub_splu_valtyp H.
      all: applys* psub_rcd HN.
Qed.


Lemma psub_orl_inv : forall A B C,
    A | B <p C -> (isValTyp A -> A <p C) /\ (isValTyp B -> B <p C).
Proof.
  introv H.
  inductions H; auto_lc; split; intros; auto.
  all: try forwards: IHPositiveSubtyping; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping1; try reflexivity; destruct_conj.
  all: try forwards: IHPositiveSubtyping2; try reflexivity; destruct_conj.
  all: eauto.
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

Lemma psub_spli_valtyp : forall A A1 A2,
    spli A A1 A2 -> isValTyp A -> A1 <p A /\ A2 <p A.
Proof.
  introv Spl Val.
  induction Spl; solve_false.
  all: try solve [ inverts_typ; split* ].
  - split; applys* PSub_Neg.
Qed.

(* isValTyp A -> spli/u A A1 A2 -> either there is a neg in A1/2 or they are
rcd with the same label so from the two psub of A1/2 we can conclude the rest *)
Lemma psub_spli_l_inv : forall A A1 A2 C,
    spli A A1 A2 -> A <p C -> A1 <p C /\ A2 <p C.
Proof.
  introv Spl Sub.
  indTypSize (size_typ A + size_typ C).
  inverts~ Sub; inverts_all_spl; inverts_typ.
  - forwards (?&?): IH; [ | eassumption | .. ]; try eassumption; elia.
    eauto.
  - forwards (?&?): IH; [ | eassumption | .. ]; try eassumption; elia.
    eauto.
  - forwards (?&?): IH; [ | eassumption | .. ]; try eassumption; elia.
    eauto.
  - forwards (?&?): IH; [ | eassumption | .. ]; try eassumption; elia.
    inverts H.
    + inverts Spl; solve_false.
      forwards~ (?&?): psub_spli_valtyp H10.
      split.
      all : applys~ PSub_Intersect.
      * applys~ psub_rcd H.
      * applys~ psub_rcd H0.
    + split; applys~ PSub_Intersect; applys psub_negtyp; try eassumption.
Qed.

Ltac inverts_all_psub :=
  repeat lazymatch goal with
    | Sub : _ & _ <p _ |- _ =>
        forwards (?&?): psub_and_l_inv Sub; clear Sub
    | Sub : _ | _ <p _ |- _ =>
                  forwards (?&?): psub_orl_inv Sub; clear Sub
    | Sub : _ <p _ & _ |- _ =>
        forwards (?&?): psub_and_r_inv Sub; clear Sub
    | Sub : _ <p (t_rcd _ _) |- _ =>
        forwards (?&?&?): psub_rcd_r_inv Sub; clear Sub
    | Sub : _ <p ?B, Hspl: spli ?B _ _ |- _ =>
        forwards (?&?): psub_spli_r_inv Hspl Sub; clear Sub
    | Sub : t_forall _ <p _ |- _ =>
        lets: psub_forall_inv Sub; clear Sub
    (* | Sub : ?A <p _, Hspl: splu ?A _ _ |- _ => *)
    (*     forwards (?&?): psub_splu_l_inv Hspl Sub; clear Sub *)
    | Sub : ?A <p _, Hspl: spli ?A _ _ |- _ =>
        forwards (?&?): psub_spli_l_inv Hspl Sub; clear Sub
    | Sub : _ <p ?B, Hspl: splu ?B _ _ |- _ =>
        forwards [?|?]: psub_splu_r_inv Hspl Sub; clear Sub
    | Sub : _ <p _ | _ |- _ =>
                       forwards [?|?]: psub_or_r_inv Sub; clear Sub
    end;
  try lazymatch goal with |- isValTyp _ => eauto 2 end.

Lemma nsub_negtyp : forall V1 V2 A,
    A <n (fty_StackArg V1) -> isNegTyp V1 -> isNegTyp V2 -> A <n (fty_StackArg V2).
Proof.
  introv Sub Neg1 Neg2. gen V2.
  inductions Sub; try solve [inverts Neg1]; intros; eauto using psub_negtyp.
Qed.

(******************************************************************************)
(** similar *)

Definition applicable A B := exists C, ApplyTy A B C.

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

Lemma sim2similar : forall A B,
    sim A B <-> similar A B.
Proof.
  introv. split; introv Sim.
  - induction Sim.
    all: try solve [unfolds; exists; split~].
    + applys* similar_rcd.
  - unfolds in Sim. destruct_conj.
    induction H; try inverts_typ; eauto.
    + forwards*: IHsplu. inverts_typ.
      * applys* Sim_NegL.
      * applys* Sim_NegR.
    + forwards*: IHsplu. inverts_typ.
      * applys* Sim_NegL.
      * applys* Sim_NegR.
    + applys* Sim_NegL.
Qed.

Lemma sim_psub : forall A B,
    sim A B -> (isValTyp A -> A <p B) \/ (isValTyp B -> B <p A).
Proof.
  introv H.
  induction* H.
Qed.

Lemma sim_psub_trans : forall V A B C D,
   sim A B -> A <p C -> B <p D -> splu V A B -> isValTyp V -> V <p C | D.
Proof.
  introv HS HP1 HP2 Spl Val. gen V C D.
  induction HS; intros.
  - applys PSub_UnionL; try applys* psub_negtyp; eauto. admit.
  - applys PSub_UnionR; try applys* psub_negtyp; eauto. admit.
  - inverts Spl; solve_false.
Abort. (* maybe not right? not sure how to state the lemma *)
(*     inverts_typ. forwards~ : IHHS H1. *)
(*     lets: psub_rcd_r_inv. *)
(* Qed. *)

(******************************************************************************)


(*------------------------------ Lemma B.1 -----------------------------------*)

(* B.1 (1) *)
Lemma sub2psub : forall V A,
    isValTyp V -> V <: A -> V <p A.
Proof with try eassumption; elia.
  introv Val Sub. convert2asub.
  indTypSize (size_typ V + size_typ A).
  inverts Sub; try solve [inverts Val]; inverts_typ; solve_false.
  all: eauto.
  all: try (forwards: IH; [ eassumption | eassumption | .. ])...
  all: eauto.
  - (* refl *) applys~ psub_refl.
  - (* intersect on the right *)  forwards: IH H0... applys~ psub_spli_r H.
  - (* on the left *) applys~ psub_spli_l_1 H. applys IH...
  - (* on the left *) applys psub_negtyp A1... applys* IH...
  -  applys psub_negtyp A2... applys* IH...
Abort. (* stuck in the next case *)
(*   - destruct H4. *)
(*     + forwards~: IHSub1. *)

(*     applys psub_trans H1. unionL H. *)
(*   - applys* psub_splu_left H. *)
(*   - applys* psub_splu_right H. *)
(* Qed. *)

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

(* B.1 (2) *)
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

(*------------------------------ Lemma B.3 -----------------------------------*)

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

(* B.3 (1) *)
Lemma valtyp_sub_rcd_inv : forall V l A,
    isValTyp V -> V <: (t_rcd l A) -> exists B, V = t_rcd l B.
Proof.
  introv Val Sub.
  induction Val.
  - convert2asub. auto_inv. eauto.
  - false. applys* negtyp_sub_rcd_inv A0.
Qed.

(* B.3 (1) *)
Lemma valtyp_sub_rcd_inv_2 : forall V l A,
    isValTyp V -> V <: (t_rcd l A) -> exists B, V = t_rcd l B /\ B <p A.
Proof.
  introv Val Sub.
  apply sub2psub in Sub.
  applys~ psub_rcd_r_inv.
  auto.
Qed.

(* B.3 (2) *)
Lemma valtyp_sub_arrow_inv : forall V A B,
    isValTyp V -> V <: (t_arrow A B) -> isNegTyp V.
Proof.
  introv Val Sub.
  induction~ Val; intros.
  - convert2asub; solve_false.
Qed.

(* B.3 (3) *)
Lemma valtyp_sub_forall_inv : forall V A,
    isValTyp V -> V <: (t_forall A) -> isNegTyp V.
Proof.
  introv Val Sub.
  induction~ Val; intros.
  - convert2asub; solve_false.
Qed.
