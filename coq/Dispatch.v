Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.

Section B13.

  Lemma distinguishability_top_neg_false : forall Aneg,
    Distinguishability Aneg t_top -> isNegTyp Aneg -> False.
  Proof with solve_false; eauto 3.
    introv Dis Neg.
    inductions Dis; repeat inverts_typ;
      try forwards(?&?): distinguishability_lc Dis;
      try forwards(?&?): distinguishability_lc Dis1;
      try forwards(?&?): distinguishability_lc Dis2...
    inverts H...
  Qed.

  Hint Immediate distinguishability_top_neg_false : FalseHd.

  Lemma distinguishability_negtyp_not_apply : forall V U,
      Distinguishability V U -> isNegTyp V -> isNegTyp U -> V <p U -> False.
  Proof with try inverts_typ; solve_false.
    introv Dis Val1 Val2 Sub.
    indTypSize (size_typ V + size_typ U).
    lets~ [Hu|(?&?&Hu)]: ordu_or_split U;
      lets~ [Hv|(?&?&Hv)]: ordu_or_split V;
      lets~ [Hiu|(?&?&Hiu)]: ordu_or_split U;
      lets~ [Hiv|(?&?&Hiv)]: ordu_or_split V; inverts_all_distinguishability.
    - inverts Val1; inverts Val2...
      all: first [inverts_all_distinguishability;
                  try solve [repeat match goal with
                                    | H: Distinguishability _ _ |- _ => inverts H
                                    | H: DistinguishabilityAx _ _ |- _ => inverts H; fail
                                    end] ].
      inverts_all_distinguishability.

    gen U. induction Val1; intros; induction Val2; intros.
    all: try solve [inverts Dis; try inverts_typ; solve_false].
    - inverts Dis; inverts Sub...
    - admit.
    - inverts Dis; inverts Sub...
    - inverts Dis. ; inverts Sub. inverts_all_distinguishability.  eauto.;try inverts_typ; solve_false].

  Lemma distinguishability_valtyp_not_apply : forall V U,
    Distinguishability V U -> isValTyp V -> isValTyp U -> V <p U -> False.
  Proof with try inverts_typ; solve_false.
    introv Dis Val1 Val2 Sub.
    induction Sub...
    - forwards* : distinguishability_rcd_inv Dis.
    - inverts Dis...
      + inverts H0...
    - inverts_all_distinguishability. eauto.
    - inverts_all_distinguishability. eauto.
    - (* the inv lemma has preconditions *)
  Restart.
  Proof with try inverts_typ; solve_false.
  introv Dis Val1 Val2 Sub.
  gen U. induction Val1; intros; induction Val2; intros.
    all: try solve [inverts Dis; try inverts_typ; solve_false].
    - (* rcd *) inverts Dis.
      + inverts Sub...
      + inverts Sub...
      + inverts H. inverts Sub...
    - inverts Dis; inverts Sub...
      applys IHVal1.dd

        * applys* IHVal1 V0.
        * forwards* : distinguishability_rcd_inv H0.
  all: try solve [inverts_all_distinguishability; eauto].
  try solve [inverts Sub].
  try solve [inverts Dis].

    -


  end Section.
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
