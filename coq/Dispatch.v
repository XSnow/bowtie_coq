Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
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

(* Lemma B.12 *)
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

(* Dispatch lemma w/o ordu constraints *)
Lemma dispatch_gen : forall (A1 A2 B B' C1 C2' : typ),
    Mergeability A1 A2 ->
    ApplyTy A1 B C1 -> NApplyTy A1 B' -> ApplyTy A2 B' C2' ->
    NApplyTy A2 B -> (* this premise is not on the paper def *)
    Distinguishability B B'.
Proof with try eassumption; elia; destruct_conj; subst.
  introv Meg App1 Napp1 App2 Napp2.
  indTypSize (size_typ B + size_typ B').
  lets~ [Hu|(?&?&Hu)]: ordu_or_split B. auto_lc.
  lets~ [Hu'|(?&?&Hu')]: ordu_or_split B'. auto_lc.
  - applys dispatch...
  - Abort.
(* forwards : applyty_splitu_arg_inv App2... *)
(*     forwards [?|?]: napplyty_splitu_arg_inv Napp1... *)
(*     forwards: IH Napp2 H... applys DistnionL. *)
(* Admitted. *)

Lemma sim_isvaltyp : forall A B,
    sim A B -> isValTyp A /\ isValTyp B.
Proof.
  introv H. induction* H.
Qed.

(* Two types are sim iff they are splu from a value type *)
(* This lemma is equivalent to dispatch_gen *)
Lemma applyty_merge_sim : forall A A' B B' x1 x2,
    TypeWF nil (A&A') -> (* implies Mergeability A A' *)
    sim B B' -> ApplyTy A B x1 -> ApplyTy A' B' x2 ->
    exists y, ApplyTy A' B y \/ ApplyTy A B' y.
Proof with try eassumption.
  introv WF HS HA1 HA2.
  indTypSize (size_typ B + size_typ B').
  forwards* [(?&?)|?]: applyty_total A B'.
  forwards* [(?&?)|?]: applyty_total A' B.
  false.
  inverts WF.
  forwards (?&?): sim_isvaltyp HS.
  forwards Sub1: sim_psub HS...
  forwards Sub2: sim_psub_2 HS...
  forwards: applyty_valtyp_psub Sub1...
  - inverts H1; inverts H2.
    all: solve_false.

  applys sim_no_distinguishability HS.
  applys* dispatch HM.
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

(******************************************************************************)
(******************************************************************************)
(* Lemma B.12 *)
Lemma dispatch_ord : forall A1 A2 B B' C1 C2',
    ordu B -> ordu B' -> Mergeability A1 A2 ->
    ApplyTy A1 B C1 -> NApplyTy A1 B' -> ApplyTy A2 B' C2' ->
    Distinguishability B B'.
Proof.
(*  introv Ord1 Ord2 Meg App1 Napp1 App2. gen B B' C1 C2'.
  induction Meg; intros.

all: try solve [inverts Napp1; inverts App1; inverts App2; solve_false]. *)
(*   - (* arrow *) *)
(*     inverts App1; inverts Napp1; inverts App2. *)
Abort.
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
