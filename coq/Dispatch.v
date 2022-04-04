Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.

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


  (* B. 13 *)
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


Lemma dispatch : forall (A1 A2 B B' C1 C2' : typ),
    Mergeability A1 A2 -> ordu B -> ordu B' ->
    ApplyTy A1 B C1 -> NApplyTy A1 B' -> ApplyTy A2 B' C2' ->
    Distinguishability B B'.
Proof with elia; solve_false.
  (* introv Val1 Val2 App1 PSub App2. *)
  (* indTypSize (size_typ V + size_typ V' + size_typ A). *)
  (* lets~ [Hu|(?&?&Hu)]: ordu_or_split V'. *)
  (* lets~ [Hu'|(?&?&Hu')]: ordu_or_split V. *)
Admitted.

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

Notation "A >><< B"        := (Mergeability A B)
                                (at level 65, B at next level, no associativity) : type_scope.
Lemma mergeability_symm : forall A B,
    Mergeability A B -> Mergeability B A.
Proof.
  introv H. induction~ H. all: eauto.
Admitted.

#[export] Hint Immediate mergeability_symm : core.

(****************************************************************************)
(* B.14 If apply(A, V) => C and V'/V => ok and apply(A, V')=>C' then C <: C' *)
Lemma applyty_valtyp_psub : forall (A V C V' C' : typ),
    TypeWF nil A -> isValTyp V -> isValTyp V' ->
    V' <p V -> ApplyTy A V C -> ApplyTy A V' C' -> C <: C'.
Proof with elia; solve_false.
  introv WF Val1 Val2 PSub App1 App2.
  indTypSize (size_typ V + size_typ V' + size_typ A).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split V'.
  lets~ [Hu'|(?&?&Hu')]: ordu_or_split V.
  - (* V and V' ordu *)
    inverts App1; inverts WF... (* analysis the form of A *)
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
      * false.
        forwards: dispatch A1 A2 V V'; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.

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

        (* inverts H7; solve_false. (* mergeability *) *)
        (* ** admit. *)
        (* ** (* arrow input diff *) *)
        (*   forwards (SubA & (SubC1 & SubC2)): applyty_arrow_sound_2 H0. (* B.5 (2) *) *)
        (*   forwards (SubB & (SubC3 & SubC4)): applyty_arrow_sound_2 H11. (* B.5 (2) *) *)
        (* ** (* arrow return diff *) *)
        (*   forwards (SubA & (SubC1 & SubC2)): applyty_arrow_sound_2 H0. (* B.5 (2) *) *)
        (*   forwards (SubB & (SubC3 & SubC4)): applyty_arrow_sound_2 H11. (* B.5 (2) *) *)
        (*   forwards SubB : applyty_soundness_1 H11. *)
        (*   forwards~ : applyty_completeness_1 (t_arrow A B) C B... *)
        (* inverts PSub; solve_false; inverts_typ. *)
     *  false.
        forwards~: dispatch A2 A1 V' V; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.
        (* this case require dispatch to be defined as paper *)
        (* repeat match goal with *)
        (*         H1: ApplyTy ?A _ _, H2: ApplyTy ?A _ _ |- _ => *)
        (*               forwards~: IH H1 H2; elia; clear H1 *)
        (*       end. *)
       (* Similar case *)
       (* Hu : ordu V' *)
       (* Hu' : ordu V *)
       (* H0 : ApplyTy A1 V C *)
       (* H1 : NApplyTy A2 V *)
       (* H5 : ApplyTy A1 V' A1' *)
       (* H8 : ApplyTy A2 V' A2' *)
       (* ============================ *)
       (* C <: A1' & A2' *)
    + (* intersection again *) inverts~ App2...
      2: repeat match goal with
                 H1: ApplyTy ?A _ _, H2: ApplyTy ?A _ _ |- _ =>
                 forwards~: IH H1 H2; elia; clear H1
               end.
      * false.
        forwards: dispatch A1 A2 V' V; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.
      * false.
        forwards~ : dispatch A1 A2 V' V; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.
    + (* intersection again *) inverts~ App2...
      3: repeat match goal with
                 H1: ApplyTy ?A _ _, H2: ApplyTy ?A _ _ |- _ =>
                 forwards~: IH H1 H2; elia; clear H1
               end.
      * false.
        forwards~: dispatch A2 A1 V V'; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.
      * false.
        forwards~ : dispatch A1 A2 V V'; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.
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
Qed.

Lemma iso_subst_sub : forall A B C,
    A <: B -> A ~= C -> C <: B.
Proof.
  introv H1 (H2&H3). convert2asub. applys algo_trans; try eassumption.
Qed.

(* B.15 *)
Lemma applyty_andl_sub : forall (A1 A2 B B1 B2 : typ) (V:Fty),
    TypeWF nil (A1&A2) -> isValFty V ->
    ApplyTy (A1&A2) V B -> ApplyTy A1 V B1 -> ApplyTy A2 V B2 -> B1&B2 <: B.
Proof with try eassumption; elia; destruct_conj; subst.
  introv WF Val AppA App1 App2.
    indTypFtySize (size_typ A1 + size_typ A2 + size_Fty V).
    lets~ [Hu|(?&?&Hu)]: ordu_or_split_Fty V... now eauto.
  - inverts AppA; solve_false.
    forwards: applyty_unique App1...
    forwards: applyty_unique App2...
    convert2asub. match_and; eauto.
  - assert (HS: similar x0 x1). {
      inverts Val. unfold similar; exists; split; eassumption.
    }
    apply sim2similar in HS.
    forwards HS1: sim_psub HS. forwards HS2: sim_psub_2 HS.
    forwards (?&?) : applyty_splitu_arg_inv App1...
    forwards (?&?) : applyty_splitu_arg_inv App2...
    forwards (?&?) : applyty_splitu_arg_inv AppA...
    forwards: IH (fty_StackArg x0) A1 A2... now eauto.
    forwards: IH (fty_StackArg x1) A1 A2... now eauto.
    inverts WF.
    forwards: applyty_valtyp_psub A2 HS1... 1-2: eauto.
    (* forwards: applyty_valtyp_psub A2 HS2... 1-2: eauto. *)
    forwards: applyty_valtyp_psub A1 HS1... 1-2: eauto.
    (* forwards: applyty_valtyp_psub A1 HS2... 1-2: eauto. *)
    applys DSub_Trans ((x2 | x2) & (x4 | x4)).
    applys DSub_Trans.
    applys DSub_CovInterL. now eauto.
    applys DSub_CovUnionR... now eauto.
    applys DSub_CovInterR. now eauto.
    applys DSub_CovUnionR... now eauto.
    applys DSub_Trans (x2 & x4).
    all: convert2asub.
    2: use_left_r; easy.
    split_l; swap_and_l. all: auto_lc.
    all: split_l; swap_and_l. all: auto_lc.
    all: eauto.
Qed.

(******************************************************************************)
(* Two types are sim iff they are splu from a value type *)
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
