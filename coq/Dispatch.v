Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.

Ltac auto_lc := try match goal with
                    | |- lc_typ _ => eauto
                    end.

Section B13.

  Lemma distinguishability_top_neg_false : forall Aneg,
    Distinguishability Aneg t_top -> isNegTyp Aneg -> False.
  Proof with solve_false; eauto 3.
    introv Dis Neg.
    inductions Dis; inverts_typ; auto_lc;
      try forwards(?&?): distinguishability_lc Dis;
      try forwards(?&?): distinguishability_lc Dis1;
      try forwards(?&?): distinguishability_lc Dis2...
    inverts H...
    all: auto_lc.
  Qed.

  Hint Immediate distinguishability_top_neg_false : FalseHd.

  Lemma distinguishability_top_rcd_false : forall l A,
    Distinguishability (t_rcd l A) t_top -> False.
  Proof with solve_false; eauto 3.
    introv Dis.
    inductions Dis; inverts_all_spl.
    - inverts H...
    - forwards* : IHDis1.
    - inverts H.
  Qed.

  Hint Immediate distinguishability_top_rcd_false : FalseHd.

  Lemma distinguishability_top_val_false : forall V,
    Distinguishability V t_top -> isValTyp V -> False.
  Proof with solve_false; eauto 3.
    introv Dis Val.
    inductions Dis; inverts_typ; auto_lc;
      try forwards(?&?): distinguishability_lc Dis;
      try forwards(?&?): distinguishability_lc Dis1;
      try forwards(?&?): distinguishability_lc Dis2...
    inverts H...
  Qed.

  Hint Immediate distinguishability_top_val_false : FalseHd.

  Lemma distinguishability_negtyp_not_apply : forall V U,
      Distinguishability V U -> isNegTyp V -> isNegTyp U -> V <p U -> False.
  Proof with try inverts_typ; solve_false.
    introv Dis Val1 Val2 Sub.
    indTypSize (size_typ V + size_typ U).
    lets~ [Hu|(?&?&Hu)]: ordu_or_split U;
      lets~ [Hv|(?&?&Hv)]: ordu_or_split V;
      lets~ [Hiu|(?&?&Hiu)]: ordu_or_split U;
      lets~ [Hiv|(?&?&Hiv)]: ordu_or_split V; inverts_all_distinguishability.
    Abort.
  (*   - inverts Val1; inverts Val2... *)
  (*     all: first [inverts_all_distinguishability; *)
  (*                 try solve [repeat match goal with *)
  (*                                   | H: Distinguishability _ _ |- _ => inverts H *)
  (*                                   | H: DistinguishabilityAx _ _ |- _ => inverts H; fail *)
  (*                                   end] ]. *)
  (*     inverts_all_distinguishability. *)

  (*   gen U. induction Val1; intros; induction Val2; intros. *)
  (*   all: try solve [inverts Dis; try inverts_typ; solve_false]. *)
  (*   - inverts Dis; inverts Sub... *)
  (*   - admit. *)
  (*   - inverts Dis; inverts Sub... *)
  (*   - inverts Dis. ; inverts Sub. inverts_all_distinguishability.  eauto.;try inverts_typ; solve_false]. *)

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
      + split*.
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
      + split*.
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

  Lemma valtyp_bot_false :  isValTyp t_bot -> False.
  Proof. introv H. inverts H. inverts H0. Qed.

  (* #[export] *)
    Hint Immediate valtyp_bot_false : FalseHd.

  Lemma distinguishability_valtyp_not_psub : forall V U,
    Distinguishability V U -> isValTyp V -> isValTyp U -> V <p U -> False.
  Proof with try eassumption; elia.
    introv Dis Val1 Val2 Sub.
    indTypSize (size_typ V + size_typ U).
    (* forwards [?|(?&?&?)]: ordu_or_split V. now eauto. *)
    forwards [?|(?&?&?)]: ordu_or_split U. now eauto.
    forwards [?|(?&?&?)]: ordu_or_split V. now eauto.
    - inverts Dis; solve_false.
      + inverts H1; try solve [inverts Sub; solve_false].
      + inverts Sub; inverts_typ; solve_false.
        * applys* IH A B...
      + inverts_typ. inverts_all_psub. applys* IH A U...
      + inverts_typ. inverts_all_psub. applys* IH A' U...
      + inverts_typ. inverts_all_psub. applys* IH V A...
      + inverts_typ. inverts_all_psub. applys* IH V A'...
    - inverts_all_distinguishability.
      inverts_all_psub.
      applys* IH x U. elia.

      (* inverts H0. (* splu V *) *)
      (* all: inverts_all_spl; inverts_typ; inverts_all_distinguishability; *)
      (*   inverts_all_psub; auto_lc. *)
      (* + applys IH; [ | | | eassumption | ..]... *)
      (*   all: eauto. *)
      (* + applys IH; [ | eassumption | ..]... *)
      (*   all: eauto. *)
      (* + applys IH B... *)
      (*   all: eauto. *)
      (* + applys IH; [ | eassumption | ..]... *)
      (*   all: eauto. *)
      (* + applys IH; [ | eassumption | ..]... *)
      (*   all: eauto. *)
      (* + assert (Hspl: splu (t_forall A) (t_forall A1) (t_forall A2)) by eauto. *)
      (*   inverts_all_distinguishability. *)
      (*   applys IH (t_forall A1)... *)
      (*   all: eauto. *)
      (* + (* rcd *) *)
      (*   inverts Sub; solve_false. *)
      (*   all: inverts_typ. *)
      (*   * apply distinguishability_rcd_inv in Dis. *)
      (*     applys IH; [ | eassumption | ..]... *)
      (*   * assert (Hspl: splu (t_rcd l5 A) (t_rcd l5 A1) (t_rcd l5 A2)) by eauto. *)
      (*     inverts_all_distinguishability. *)
      (*     inverts_all_psub. *)
      (*     applys IH H4... *)
      (*     all: eauto. *)
      (*   * assert (Hspl: splu (t_rcd l5 A) (t_rcd l5 A1) (t_rcd l5 A2)) by eauto. *)
      (*     inverts_all_distinguishability. *)
      (*   * applys* IH (t_rcd l5 A1) U. *)
      (*   applys distinguishability_rcd_inv... *)
      (* + inverts H0. *)
      (* + *)
      (*   inverts_typ... solve_false. *)
      (* + inverts_typ. now eauto. now eauto. *)
      (*   inverts_all_distinguishability. *)
      (*   inverts Val1. *)
      (*   * inverts Dis; solve_false. solve_false.inverts Dis. inverts H1. inverts Val2. inverts H2. ; solve_false. inverts_all_distinguishability. *)

      (* + *)
      (* (* try inverts_typ; solve_false. *) *)
      (*  admit. *)
    - inverts_typ. inverts_all_distinguishability.
      forwards [?|?]: psub_splu_inv Sub...
      all: applys IH; [ | | | eassumption | ..]...
Qed.

End B13.
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
Admitted.

Lemma distinguishability_forall_false: forall A B,
    t_forall A <<>> t_forall B -> False.
  introv H. inductions H; inverts_all_spl; solve_false.
Qed.

#[export] Hint Immediate distinguishability_forall_false : FalseHd.

(* Two types are sim iff they are splu from a value type *)
Lemma sim_no_distinguishability : forall A B,
    sim A B -> Distinguishability A B -> False.
Proof with auto_lc; inverts_all_spl; solve_false.
  introv Sim Dis.
  induction Sim; intros.
  - induction Dis; try inverts_typ...
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
(* Here we only consider V to be StackArg. *)
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

(* B.16 Inversion of Abstract Application to Value Types *)
(* Here we only consider V to be StackTypArg. *)
Lemma applyty_inter_inv : forall A1 A2 B C,
    ApplyTy (A1&A2) [|B|] C ->
    exists C', ApplyTy A1 [|B|] C' \/ ApplyTy A2 [|B|] C'.
Proof with destruct_conj; try subst; try solve [exists*].
  introv HA.
  inverts HA; solve_false...
Qed.
