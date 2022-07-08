Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export ApplyTy.
Require Export Distinguishability.


(****************************************************************************)
(** Mergeability *)

Notation "A >><< B"        := (Mergeability A B)
                                (at level 65, B at next level, no associativity) : type_scope.
Lemma mergeability_symm : forall A B,
    A >><< B -> B >><< A.
Proof.
  introv H. induction~ H. all: eauto.
Qed.

#[export] Hint Immediate mergeability_symm : core.


(****************************************************************************)

(* Corollary of B.11 *)
Lemma distinguishability_downward_both : forall A A' B B',
    Distinguishability A B -> A' <: A -> B' <: B -> Distinguishability A' B'.
Proof.
  introv Dis Sub1 Sub2.
  applys distinguishability_downward.
  applys DistSym. apply DistSym in Dis.
  applys distinguishability_downward Dis.
  all: eauto.
Qed.

#[export] Hint Immediate distinguishability_downward_both : core.


Lemma lc_andl_inv : forall A B,
    lc_typ (A&B) -> lc_typ A.
Proof.
  introv H. inverts~ H.
Qed.

Lemma lc_andr_inv : forall A B,
    lc_typ (A&B) -> lc_typ B.
Proof.
  introv H. inverts~ H.
Qed.

Lemma lc_orl_inv : forall A B,
    lc_typ (A|B) -> lc_typ A.
Proof.
  introv H. inverts~ H.
Qed.

Lemma lc_orr_inv : forall A B,
    lc_typ (A|B) -> lc_typ B.
Proof.
  introv H. inverts~ H.
Qed.

#[export] Hint Resolve lc_andl_inv lc_andr_inv lc_orl_inv lc_orr_inv : core.

(****************************************************************************)

(* Lemma B.12 Dispatch *)
Lemma dispatch : forall A1 A2 B B' C1 C2',
    ordu B -> ordu B' -> A1 >><< A2 ->
    ApplyTy A1 B C1 -> NApplyTy A1 B' -> ApplyTy A2 B' C2' ->
    Distinguishability B B'.
Proof with try eassumption; destruct_conj; subst.
 introv Ord1 Ord2 Meg App1 Napp1 App2. gen B B' C1 C2'.
 induction Meg; intros.
 - forwards: applyty_arrow_sound_2 App1...
   forwards: applyty_arrow_sound_2 App2...
   eauto.
 - forwards (?&(?&?)): applyty_arrow_sound_2 App2...
   false. applys~ napplyty_sub_inv Napp1.
 - solve_false.
 - forwards: napplyty_spliti_inv Napp1... now constructor*.
   inverts App1; solve_false.
   + forwards: IHMeg1 B0 B'...
   + forwards: IHMeg2 B0 B'...
   + forwards: IHMeg1 B0 B'...
 - inverts App2; solve_false.
   + forwards: IHMeg1 B0 B'...
   + forwards: IHMeg2 B0 B'...
   + forwards: IHMeg1 B0 B'...
 - forwards : applyty_splitu_inv App1... now constructor*.
   forwards [?|?]: napplyty_splitu_inv Napp1... now constructor*.
   + forwards: IHMeg1 B0 B'...
   + forwards: IHMeg2 B0 B'...
 - forwards : applyty_splitu_inv App2... now constructor*.
   forwards: IHMeg1 B0 B'...
 - (* MergeabilityAx *)
   inverts H; solve_false.
 - (* MergeabilityAx *)
   inverts H; solve_false.
Qed.

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
     *  false.
        forwards~: dispatch A2 A1 V' V; try eassumption.
        forwards~ : distinguishability_valtyp_not_psub V' V.
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

(****************************************************************************)

(* B.15 (1) *)
Lemma applyty_andl_sub_1 : forall (A1 A2 B B1 B2 : typ) (V:Fty),
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
    forwards: applyty_valtyp_psub A1 HS1... 1-2: eauto.
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

(* B.15 (2) *)
Lemma applyty_andl_sub_2 : forall (A1 A2 B B1 : typ) (V:Fty),
    TypeWF nil (A1&A2) -> isValFty V ->
    ApplyTy (A1&A2) V B -> ApplyTy A1 V B1 -> NApplyTy A2 V -> B1 <: B.
Proof with try eassumption; elia; destruct_conj; subst.
  introv WF Val AppA App1 App2.
  indTypFtySize (size_typ A1 + size_typ A2 + size_Fty V).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split_Fty V... now eauto.
  - inverts AppA; solve_false.
    forwards: applyty_unique App1...
    convert2asub. eauto.
  - assert (HS: similar x0 x1). {
      inverts Val. unfold similar; exists; split; eassumption.
    }
    apply sim2similar in HS.
    forwards HS1: sim_psub HS. forwards HS2: sim_psub_2 HS.
    forwards (?&?) : applyty_splitu_arg_inv App1...
    forwards (?&?) : applyty_splitu_arg_inv AppA...
    forwards [?|?] : napplyty_splitu_arg_inv App2...
    1: forwards: IH (fty_StackArg x0) A1 A2... now eauto.
    2: forwards: IH (fty_StackArg x1) A1 A2... 2: now eauto.
    all: inverts WF.
    + forwards: applyty_valtyp_psub A1 HS1... 1-2: eauto.
      forwards: applyty_valtyp_psub (A1 & A2) HS1... 1-3: eauto.
      applys* DSub_Trans x4.
    + forwards: applyty_valtyp_psub A1 HS2... 1-2: eauto.
      forwards: applyty_valtyp_psub (A1 & A2) HS1... 1-3: eauto.
      applys~ DSub_Trans x3.
Qed.

(* B.15 (3) *)
Lemma applyty_andl_sub_3 : forall (A1 A2 B B2 : typ) (V:Fty),
    TypeWF nil (A1&A2) -> isValFty V ->
    ApplyTy (A1&A2) V B -> NApplyTy A1 V -> ApplyTy A2 V B2 -> B2 <: B.
Proof with try eassumption; elia; destruct_conj; subst.
  introv WF Val AppA App1 App2.
  indTypFtySize (size_typ A1 + size_typ A2 + size_Fty V).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split_Fty V... now eauto.
  - inverts AppA; solve_false.
    forwards: applyty_unique App2...
    convert2asub. eauto.
  - assert (HS: similar x0 x1). {
      inverts Val. unfold similar; exists; split; eassumption.
    }
    apply sim2similar in HS.
    forwards HS1: sim_psub HS. forwards HS2: sim_psub_2 HS.
    forwards (?&?) : applyty_splitu_arg_inv App2...
    forwards (?&?) : applyty_splitu_arg_inv AppA...
    forwards [?|?] : napplyty_splitu_arg_inv App1...
    1: forwards: IH (fty_StackArg x0) A1 A2... now eauto.
    2: forwards: IH (fty_StackArg x1) A1 A2... 2: now eauto.
    all: inverts WF.
    + forwards: applyty_valtyp_psub A2 HS1... 1-2: eauto.
      forwards: applyty_valtyp_psub (A1 & A2) HS1... 1-3: eauto.
      applys* DSub_Trans x2.
    + forwards: applyty_valtyp_psub A2 HS2... 1-2: eauto.
      forwards: applyty_valtyp_psub (A1 & A2) HS1... 1-3: eauto.
      applys~ DSub_Trans x3.
Qed.

(* B.15 (4) *)
Lemma applyty_orl_sub : forall (A1 A2 B B1 B2 : typ) (V:Fty),
    ApplyTy (A1|A2) V B -> ApplyTy A1 V B1 -> ApplyTy A2 V B2 -> B <: B1 | B2.
Proof with try eassumption; elia; destruct_conj; subst.
  introv AppA App1 App2.
  forwards : applyty_splitu_inv AppA... now eauto.
  forwards: applyty_unique App1...
  forwards: applyty_unique App2...
  destruct~ H.
Qed.

(******************************************************************************)

(* Two types are sim iff they are splu from a value type *)
Lemma sim_isvaltyp : forall A B,
    sim A B -> isValTyp A /\ isValTyp B.
Proof.
  introv H. induction* H.
Qed.

Lemma sim_split_1 : forall A B A1 A2,
    sim A B -> splu A A1 A2 -> sim A1 A2.
Proof.
  introv H S. apply sim_isvaltyp in H.
  applys sim2similar.
  unfolds. exists*.
Qed.

Lemma sim_split_2 : forall A B A1 A2,
    sim A B -> splu A A1 A2 -> sim A1 B.
Proof.
  introv H S. gen A1 A2.
  induction H; intros.
  - inverts_typ. eauto.
  - inverts* S.
Qed.

Lemma sim_split_3 : forall A B A1 A2,
    sim A B -> splu A A1 A2 -> sim A2 B.
Proof.
  introv H S. gen A1 A2.
  induction H; intros.
  - inverts_typ. eauto.
  - inverts* S.
Qed.

Lemma sim_split_4 : forall A B A1 A2,
    sim B A -> splu A A1 A2 -> sim B A1.
Proof.
  introv H S. gen A1 A2.
  induction H; intros.
  - inverts_typ. eauto.
  - inverts* S.
Qed.

Lemma sim_split_5 : forall A B A1 A2,
    sim B A -> splu A A1 A2 -> sim B A2.
Proof.
  introv H S. gen A1 A2.
  induction H; intros.
  - inverts_typ. eauto.
  - inverts* S.
Qed.

#[local] Hint Immediate sim_split_1 sim_split_2 sim_split_3 sim_split_4 sim_split_5 : core.

Lemma applyty_and_sim_inv : forall A A' B B' x1 x2,
    TypeWF nil (A&A') ->
    sim B B' -> ApplyTy A B x1 -> ApplyTy A' B' x2 ->
    NApplyTy A B' -> NApplyTy A' B -> False.
Proof with auto_lc; elia; try eassumption; destruct_conj; subst.
  introv WF HS App1 App2 Napp1 Napp2.
  indTypSize (size_typ B + size_typ B').
  lets~ [Hu|(?&?&Hu)]: ordu_or_split B. auto_lc.
  lets~ [Hu'|(?&?&Hu')]: ordu_or_split B'. auto_lc.
  - applys sim_no_distinguishability HS. applys dispatch...
    inverts~ WF.
  - forwards : applyty_splitu_arg_inv App2...
    forwards [(?&?)|Napp11]: applyty_total A x... now eauto.
    forwards [(?&?)|Napp12]: applyty_total A x0... now eauto.
    * applys* applyty_contradication A B'.
    * applys IH A A' B x0... eauto.
    * applys IH A A' B x... eauto.
  - forwards : applyty_splitu_arg_inv App1...
    forwards [(?&?)|Napp11]: applyty_total A' x... now eauto.
    forwards [(?&?)|Napp12]: applyty_total A' x0... now eauto.
    * applys* applyty_contradication A' B.
    * applys IH A A' x0 B'... eauto.
    * applys IH A A' x B'... eauto.
Qed.


Lemma lemma_for_B16 : forall A A' V B1 B2 x1 x2,
    TypeWF nil (A&A') -> isValTyp V
    -> splu V B1 B2 -> ApplyTy A B1 x1 -> ApplyTy A' B2 x2 ->
    exists y, ApplyTy A' B1 y \/ ApplyTy A B2 y.
Proof.
  intros.
  forwards* [(?&?)|Napp1]: applyty_total A B2.
  forwards* [(?&?)|Napp2]: applyty_total A' B1.
  false. applys* applyty_and_sim_inv A A' B1 B2.
  applys sim2similar.
  unfold similar. exists*.
Qed.

(* B.16 Inversion of Dispatch on Value Types *)
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

(* B.16 Inversion of Dispatch on Value Types *)
(* Here we only consider V to be StackTypArg. *)
Lemma applyty_inter_inv : forall A1 A2 B C,
    ApplyTy (A1&A2) [|B|] C ->
    exists C', ApplyTy A1 [|B|] C' \/ ApplyTy A2 [|B|] C'.
Proof with destruct_conj; try subst; try solve [exists*].
  introv HA.
  inverts HA; solve_false...
Qed.

Lemma sub_sim_distinguishability_sub_inv : forall A B C D,
    sim A B -> C <<>> D -> A <: C -> B <: D -> False.
Proof with try eassumption.
  intros.
  applys sim_no_distinguishability H.
  applys distinguishability_downward_both...
Qed.

#[export] Hint Immediate sub_sim_distinguishability_sub_inv : FalseHd.

(* Inversion of Disjoint Union Subtyping *)
Lemma sub_inv_distinguishable_union : forall A B1 B2,
    isValTyp A -> A <:: B1 | B2 -> B1 <<>> B2 -> A <:: B1 \/ A <:: B2.
Proof with try eassumption; elia; try solve [false; applys sub_sim_distinguishability_sub_inv; convert2dsub; eassumption ].
  introv Val Sub Dis.
  indTypSize (size_typ A + size_typ (B1|B2)).
  lets~ [Hu|(C1&C2&Hu)]: ordu_or_split A.
  - auto_inv.
  - assert (Sim: sim C1 C2). {
      applys sim2similar. unfold similar. eauto.
    }
    auto_inv. inverts_typ.
    forwards [?|?]: IH C1 B1 B2...
    all: forwards [?|?]: IH C2 B1 B2...
    all: try solve [left; applys ASub_or; [eassumption |..]; eauto].
    all: try solve [right; applys ASub_or; [eassumption |..]; eauto].
    apply DistSym in Dis...
Qed.

(* Some results about negtyp; were proved for the above lemma *)
Lemma distinguishability_negtyp_bot : forall V U,
    Distinguishability V U -> isNegTyp V -> U <:: t_bot.
Proof with solve_false.
  introv Dis Neg.
  indTypSize (size_typ V + size_typ U).
  inverts Neg; inverts Dis; inverts_all_spl; inverts_typ...
  all: try solve [match goal with | H: DistinguishabilityAx _ _ |- _ => inverts~ H end].
  all: repeat match goal with
         | H: _ <<>> _ |- _ => forwards: IH H; [ now eauto | .. ]; elia; clear H
         end.
  all: try solve [solve_algo_sub; try eassumption; auto].
  all: auto.
Qed.

Lemma sub_inv_distinguishable_bot : forall A B1 B2,
    isNegTyp A -> A <: B1 -> B1 <<>> B2 -> B2 <: t_bot.
Proof.
  introv Val Sub Dis.
  forwards: distinguishability_downward_both Dis Sub.
  applys* DSub_Refl.
  convert2asub.
  applys~ distinguishability_negtyp_bot H.
Qed.

#[export] Hint Resolve negtyp_sub_rcd_inv : FalseHd.

Lemma botlike_or_inv_1 : forall A B,
    A | B <:: t_bot -> A <:: t_bot.
Proof.
  introv H. applys algo_trans H. use_left_r. eauto.
Qed.
Lemma botlike_or_inv_2 : forall A B,
    A | B <:: t_bot -> B <:: t_bot.
Proof.
  introv H. applys algo_trans H. use_right_r. eauto.
Qed.

#[export] Hint Immediate botlike_or_inv_1 botlike_or_inv_2 : core.

Lemma botlike_spli_inv : forall C A B,
    C <:: t_bot -> spli C A B -> A <:: t_bot \/ B <:: t_bot.
Proof with inverts_all_spl; solve_false.
  introv Sub Spl.
  inductions Spl...
  - applys~ botlike_inv.
  - forwards* [?|?]: IHSpl.
  - forwards* [?|?]: IHSpl.
Qed.

Lemma botlike_splu_inv : forall A B C,
    C <:: t_bot -> splu C A B -> A <:: t_bot /\ B <:: t_bot.
Proof.
  introv H. split; applys algo_trans H.
  2: use_right_r. 1: use_left_r. 1, 3: eassumption.
  all: eauto.
Qed.

Ltac inv_botlike :=
    repeat try lazymatch goal with
         | H1: ?A <:: t_bot , H2: spli ?A _ _ |- _ =>
           forwards [?|?]: botlike_spli_inv H1 H2; clear H1
         | H1: _ & _ <:: t_bot |- _ =>
           forwards [?|?]: botlike_inv H1; clear H1
         | H1: _ | _ <:: t_bot |- _ =>
           forwards : botlike_or_inv_1 H1; forwards : botlike_or_inv_2 H1; clear H1
         | H1: ?A <:: t_bot , H2: splu ?A _ _ |- _ =>
           forwards (?&?): botlike_splu_inv H1 H2; clear H1
      end.

Lemma negtyp_sub_bot_inv : forall Aneg,
    isNegTyp Aneg -> Aneg <: t_bot -> False.
Proof with try eassumption; solve_false.
  introv Neg Sub. convert2asub.
  induction Neg; inv_botlike...
Qed.

#[export] Hint Immediate negtyp_sub_bot_inv : FalseHd.

Lemma sub_trans_bot : forall A B,
    A <:: t_bot -> lc_typ B -> A <:: B.
Proof.
  introv Sub Lc.
  applys* algo_trans Sub.
Qed.

#[export] Hint Immediate sub_trans_bot : core.

Lemma sub_union_bot_inv : forall A B C,
    A <:: B | C -> B <:: t_bot -> A <:: C.
Proof with try eassumption; elia.
  introv Sub SubB.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets~ [Hu|(C1&C2&Hu)]: ordu_or_split A.
  - assert (lc_typ C) by eauto.
    auto_inv. applys~ algo_trans B.
  - inverts Sub; inverts_all_spl.
    all: auto.
    all: inv_botlike.
    all: try (forwards: IH; [eassumption | eassumption | .. ]; [ now elia | ] ).
    all: auto.
    + applys~ ASub_or.
    + applys~ ASub_and H7. applys IH...
    + use_left_l...
    + use_right_l...
    + clear H1. forwards: IH; [eassumption | eassumption | .. ]; [ now elia | ].
      applys ASub_or...
    + forwards~ : algo_trans H0 SubB.
Qed.
