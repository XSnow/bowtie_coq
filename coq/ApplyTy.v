Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export DistSubtyping.


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
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].


#[export] Hint Immediate orduFty_lc : core.

Lemma napplyty_lc_1 : forall A B, NApplyTy A B -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma napplyty_lc_2 : forall A B, NApplyTy A B -> lc_Fty B.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate napplyty_lc_1 napplyty_lc_2 : core.

Lemma applyty_lc_1 : forall A B C, ApplyTy A B C -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma applyty_lc_2 : forall A B C, ApplyTy A B C -> lc_Fty B.
Proof.  introv H.  induction* H. Qed.

Lemma applyty_lc_3 : forall A B C, ApplyTy A B C -> lc_typ C.
Proof.  introv H.  induction~ H. inverts H. eauto with lngen. Qed.

#[export] Hint Immediate applyty_lc_1 applyty_lc_2 applyty_lc_3 : core.

(*
Ltac solve_lc_by_regularity A :=
  match goal with
  | H: ApplyTy _ _ _ |- _ => match type of H with context[ A ] => apply applyty_lc in H end
  | H: NApplyTy _ _ _ |- _ => match type of H with context[ A ] => apply napplyty_lc in H end
  end;
  destruct_conj.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_by_regularity A : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress solve_lc_by_regularity A : core.
 *)

Lemma napplyty_splitu_inv : forall A B B1 B2,
    NApplyTy A (fty_StackArg B) -> splu B B1 B2 ->
    NApplyTy A (fty_StackArg B1) \/ NApplyTy A (fty_StackArg B2).
Proof.
  introv HN HS.
  inverts HN; solve_false; auto_unify; eauto.
Qed.

Lemma applyty_contradication : forall A B C,
   ApplyTy A B C -> NApplyTy A B -> False.
Proof with solve_false.
  introv HA HN.
  indTypFtySize (size_typ A + size_Fty B).

  inverts HA;
    match goal with
    | H1: NApplyTy _ (fty_StackArg ?B), H2: splu ?B _ _  |- _ =>
      forwards~ [?|?]: napplyty_splitu_inv H1 H2
    | _ => inverts HN
    end.

  all: repeat match goal with
  | H1: ApplyTy (t_forall _) (fty_StackArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyFunTy
  | H1: ApplyTy (t_arrow _ _) (fty_StackTyArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyTyFunFty
  | H1: ApplyTy ?A ?B _, H2: NApplyTy ?A ?B |- _ => forwards: IH H2 H1; elia
              end.
  all: solve_false.
Qed.

#[export]  Hint Extern 1 => match goal with
                            | H1: ApplyTy ?T _ _, H2: NApplyTy ?T _  |- _ =>
                              applys applyty_contradication H1 H2
                            end : FalseHd.

Lemma applyty_unique : forall A B C1 C2,
    ApplyTy A B C1 -> ApplyTy A B C2 -> C1 = C2.
Proof.
  introv HA1 HA2. gen C1 C2.
  indTypFtySize (size_typ A + size_Fty B).
  inverts HA1; inverts HA2.
  all: auto_unify; repeat match goal with
  | H1: ApplyTy ?A ?B _, H2: ApplyTy ?A ?B _ |- _ => forwards: IH H1 H2; elia; clear H1 H2
              end; subst~.
  all: solve_false.
Qed.

Ltac auto_unify_2 :=
  auto_unify; (* unify split *)
  (* unify applyty *)
  repeat match goal with
         | [ H1: ApplyTy ?A ?B _ , H2: ApplyTy ?A ?B _ |- _ ] =>
           (forwards : applyty_unique H1 H2;
            subst; clear H2)
             end.

Lemma ordu_or_split_Fty: forall F,
    lc_Fty F -> UnionOrdinaryFty F \/ exists A B C, F = fty_StackArg A /\ splu A B C.
Proof.
  introv HL.
  destruct~ HL.
  forwards* [?|(?&?&?)]: ordu_or_split A.
Qed.

Lemma applyty_total : forall A F,
    lc_typ A -> lc_Fty F -> (exists C, ApplyTy A F C) \/ NApplyTy A F.
Proof with (elia; destruct_conj).
  introv.
  indTypFtySize (size_typ A + size_Fty F).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F).
  - destruct* H.
    (* and / or *)
    all: try forwards~ [?|?]: IH F A1...
    all: try forwards~ [?|?]: IH F A2...
    all: eauto.

    (* arrow / forall *)
    all: destruct H0.
    2,3: now right*.

    + destruct* (sub_dec A0 A).
    + eauto.

  - subst.
    forwards~ [?|?]: IH (fty_StackArg x0) A...
    forwards~ [?|?]: IH (fty_StackArg x1) A...
    all: eauto.
Qed.


Lemma applyty_splitu_arg_inv : forall A B B1 B2 C,
    ApplyTy A (fty_StackArg B) C -> splu B B1 B2 ->
    exists C1 C2, C = (t_or C1 C2) /\
    ApplyTy A (fty_StackArg B1) C1 /\ ApplyTy A (fty_StackArg B2) C2.
Proof.
  introv HA HS.
  inverts HA; auto_unify; solve_false; eauto.
Qed.


Lemma applyty_splitu_fun_aux : forall A A1 A2 F,
    (forall C1 C2, ApplyTy A1 F C1 -> ApplyTy A2 F C2 -> splu A A1 A2 ->
     exists C', ApplyTy A F C') /\
    (NApplyTy A1 F \/ NApplyTy A2 F -> splu A A1 A2 -> NApplyTy A F).
Proof with elia; solve_false; try eassumption.
  introv.
  indTypFtySize (size_typ A + size_Fty F).
  split.

  introv HA1 HA2 HS.
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F). eauto.
  - inverts HS...
    + (* or *) exists*.
    + (* and *) inverts HA1...
      * (* interBoth *) inverts HA2... forwards (?&?): proj1 (IH F A0) H1... exists*.
      * (* interR *) exists*. applys* ApplyTyInterR.
        forwards~ : proj2 (IH F A0) H1...
      * (* Both *)  inverts HA2...
        ** exists*. applys* ApplyTyInterR. forwards~ : proj2 (IH F A0) H1...
        ** forwards (?&?): proj1 (IH F A0) H1... exists*.
    + (* and *) inverts HA1...
      * (* interL *) exists*. applys* ApplyTyInterL. forwards~ : proj2 (IH F B) H1...
      * (* interBoth *) inverts HA2... forwards (?&?): proj1 (IH F B) H1... exists*.
      * (* Both *)  inverts HA2...
        ** exists*. applys* ApplyTyInterL. forwards~ : proj2 (IH F B) H1...
        ** forwards (?&?): proj1 (IH F B) H1... exists*.
    (* + (* forall *) inverts HA1... inverts HA2... exists*. *)
    (* + (* rcd *) inverts HA1... *)
  - subst.
    forwards: applyty_splitu_arg_inv HA1 H0. forwards: applyty_splitu_arg_inv HA2 H0.
    destruct_conj. subst.
    forwards (?&?): proj1 (IH (fty_StackArg x0) A) H4 H2...
    forwards (?&?): proj1 (IH (fty_StackArg x1) A) H5 H3...
    exists*.

  -
    intros [HA|HA] HS;
      lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F); subst; eauto.
    + (* ord *) inverts~ HS...
      * (* and *) inverts HA... forwards~ : proj2 (IH F A0) H1...
      * (* and *) inverts HA... forwards~ : proj2 (IH F B) H1...
      (* * (* forall *) inverts HA... constructor~. *)
    + (* split *) forwards* [?|?]: napplyty_splitu_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.
    + (* ord *) inverts~ HS...
      * (* and *) inverts HA... forwards~ : proj2 (IH F A0) H1...
      * (* and *) inverts HA... forwards~ : proj2 (IH F B) H1...
      (* * (* forall *) inverts HA... constructor~. *)
    + (* split *) forwards* [?|?]: napplyty_splitu_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.

   Unshelve. all: apply t_top.
Qed.

Lemma napplyty_splitu_fun : forall A A1 A2 F,
    NApplyTy A1 F \/ NApplyTy A2 F -> splu A A1 A2 -> NApplyTy A F.
Proof.
  intros.
  forwards* (?&?): applyty_splitu_fun_aux.
Qed.

Lemma napplyty_rename : forall A B C,
    NApplyTy A (fty_StackTyArg B) -> lc_typ C -> NApplyTy A (fty_StackTyArg C).
Proof.
  introv H Lc. inductions H; eauto.
Qed.

Lemma applyty_rename : forall A B X C,
    ApplyTy A (fty_StackTyArg (t_tvar_f X)) B -> lc_typ C -> X `notin` [[A]] ->
    ApplyTy A (fty_StackTyArg C) ( [X ~~> C] B).
Proof.
  introv H Lc Fry. inductions H; simpl; simpl in Fry; eauto.
  all: try solve [ simpl_rename_goal; simpl in Fry; solve_notin ].
  - forwards~: napplyty_rename C H1.
  - forwards~: napplyty_rename C H0.
Qed.

Lemma applyty_soundness_1 : forall A B C,
    ApplyTy A (fty_StackArg B) C -> A <: (t_arrow B C).
Proof with try eassumption; try applys ASub_refl; try match goal with |- lc_typ _ => eauto with lngen end.
  introv H. inductions H.
  all: try match goal with
           | H: UnionOrdinaryFty (_ _) |- _ => inverts H
           end.
  1-2: eauto.
  all: try forwards~ : IHApplyTy.
  all: try forwards~ : IHApplyTy1. all: try forwards~ : IHApplyTy2.
  - convert2asub. split_l.
    applys algo_trans H. applys ASub_arrow... use_left_r...
    applys algo_trans H2. applys ASub_arrow... use_right_r...
  - convert2asub.
    applys algo_trans ((t_arrow B1 (B1' | B2'))&(t_arrow B2 (B1' | B2'))).
    applys algo_trans ((t_arrow B1 B1')&(t_arrow B2 B2')). split_r...
    + split_r... * use_left_l... applys ASub_arrow... use_left_r...
      * use_right_l... applys ASub_arrow... use_right_r...
    + applys asub2nsub. applys NSub_and. applys NSpI_arrowUnion...
      applys splu2nsplu H. all: applys asub2nsub.
      * use_left_l... * use_right_l...
  - convert2asub. use_left_l...
  - convert2asub. swap_and_l... use_left_l...
  - convert2asub. split_r; eauto.
Qed.

Lemma applyty_soundness_2 : forall A B C,
    ApplyTy A (fty_StackTyArg B) C ->
    exists C',  C = C'^-^B /\
                forall X, X `notin` [[C]] -> ApplyTy A (fty_StackTyArg (t_tvar_f X)) (C'-^X) /\ A <: (t_forall C').
Proof with simpl in *; try eassumption; try applys ASub_refl; try match goal with |- lc_typ _ => eauto with lngen end; destruct_conj.
  introv H. inductions H.
  all: try match goal with
           | H: UnionOrdinaryFty (_ _) |- _ => inverts H
           end.
  all: try forwards~ : IHApplyTy.
  all: try forwards~ : IHApplyTy1. all: try forwards~ : IHApplyTy2.
  all: destruct_conj.
  - exists t_bot. split~.
  - exists A. split~.
  - exists (x0|x). split~.
    + assert (Heq: forall B C X, (t_or B C) ^-^ X = t_or (B ^-^ X) (C ^-^ X)) by eauto.
      rewrite Heq. congruence.
    + assert (Heq: forall B C X, (t_or B C) -^ X = t_or (B -^ X) (C -^ X)) by eauto.
      intros X Fry... forwards~ : H5 X. forwards~ : H4 X...
      split~.
      * rewrite Heq. applys~ ApplyTyUnion H6 H4.
      * convert2asub.
        (* BROKEN: t_forall x0 | t_forall x <:: t_forall (x0 | x) *)
        admit.
        (* split_l. use_left_r...  use_right_r... *)
  - exists. split... intros X Fry. forwards~ : H2 X...
    split. eapply napplyty_rename in H1. eauto. eauto.
    convert2asub. use_left_l...
  - exists. split... intros X Fry. forwards~ : H2 X...
    split. eapply napplyty_rename in H0. eauto. eauto.
    convert2asub. swap_and_l... use_left_l...
  - exists (x0 & x). split...
    + assert (Heq: forall B C X, (t_and B C) ^-^ X = t_and (B ^-^ X) (C ^-^ X)) by eauto.
      rewrite Heq. congruence.
    + intros X Fry. forwards~ : H4 X... forwards~ : H5 X...
      split.
      * assert (Heq: forall B C X, (t_and B C) -^ X = t_and (B -^ X) (C -^ X)) by eauto.
        rewrite Heq. eauto.
      * convert2asub. split_r; eauto.
  Unshelve. all: apply empty.
Abort.

Lemma applyty_completeness_1 : forall A B D,
    A <: (t_arrow B D) -> ordu B ->
         exists C, ApplyTy A (fty_StackArg B) C /\ (t_arrow B C) <: (t_arrow B D).
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HS Hord. apply dsub2asub in HS.
  indTypFtySize (size_typ A + size_typ D).
  forwards (?&?): algo_sub_lc HS. inverts_all_lc.
  lets~ [?|(?&?&?)]: (ordi_or_split D).
  - destruct H...
    + forwards~ [Ha|Ha]: algo_sub_andlr_inv HS;
        forwards: IH Ha...
      * forwards~ [?|?]: applyty_total A2 (fty_StackArg B)...
        inv_arrow.
        exists (t_and x x0). split~. applys~ DSub_CovArr. applys~ DSub_InterLL.
        eauto with lngen. solve_dsub...
        exists* x.
      * forwards~ [?|?]: applyty_total A1 (fty_StackArg B)...
        inv_arrow.
        exists (t_and x0 x). split~. applys~ DSub_CovArr. applys~ DSub_InterLR.
        eauto with lngen. solve_dsub...
        exists x. split~.
    + apply dsub2asub in HS.
      assert (EASY1: A1 <: (t_arrow B D)) by applys~ DSub_Trans HS. apply dsub2asub in EASY1.
      assert (EASY2: A2 <: (t_arrow B D)) by applys~ DSub_Trans HS. apply dsub2asub in EASY2.
      forwards: IH B EASY1... forwards: IH B EASY2...
      exists (t_or x x0). split~. inv_arrow. applys~ DSub_CovArr.
      convert2dsub. applys~ DSub_UnionL.
    + inv_arrow. convert2dsub. exists B0. split~.
    + exists*.
  -  forwards~ (Ha1&Ha2): algo_sub_and_inv HS. eauto.
     forwards: IH Ha1... forwards: IH Ha2... inv_arrow.
     auto_unify_2. exists x2. split~. applys~ DSub_CovArr.
     convert2asub. eauto.
Qed.

Lemma applyty_completeness_2 : forall A B,
    A <: (t_forall B) ->
         exists C L, forall X, X `notin` L ->
             ApplyTy A (fty_StackTyArg (t_tvar_f X)) (C-^X) /\ (t_forall C) <: (t_forall B).
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HS. apply dsub2asub in HS.
  indTypFtySize (size_typ A + size_typ B).
  lets~ [?|(?&?&?)]: (ordi_or_split (t_forall B)).
  - assert (lc_typ A) by eauto. destruct H0...
    + forwards~ [Ha|Ha]: algo_sub_andlr_inv HS;
        forwards: IH Ha...
      * pick fresh X for ([[A1]] `union` [[A2]] `union` x0 `union` [[x]]). forwards~ : H0 X.
        forwards~ [?|?]: applyty_total A2 (fty_StackTyArg (t_tvar_f X))...
        ** exists. intros Y Fry.
           forwards~ HR1: applyty_rename (t_tvar_f Y) H1. forwards~ HR2: applyty_rename (t_tvar_f Y) H2.
           simpl_rename HR1. simpl_rename HR2.
           assert (Heq: forall Y, (t_and x (close_typ_wrt_typ X x1)) -^ Y = t_and (x -^ Y) (close_typ_wrt_typ X x1 -^ Y)) by eauto. rewrite Heq.
           split~. applys DSub_CovAll. intros X0 Fry2.
           apply dsub2asub in H3. forwards: algo_sub_forall_inv X0 H3.
           rewrite Heq. applys DSub_InterLL. eauto.
           solve_dsub...
           autorewrite with lngen. all: solve_notin.
        ** exists. intros Y Fry.
           forwards~ HR1: applyty_rename (t_tvar_f Y) H1. simpl_rename HR1.
           forwards~ HR2: napplyty_rename (t_tvar_f Y) H2.
           split. applys~ ApplyTyInterL HR1. auto. eauto with lngen.
      * pick fresh X for ([[A1]] `union` [[A2]] `union` x0 `union` [[x]]). forwards~ : H0 X.
        forwards~ [?|?]: applyty_total A1 (fty_StackTyArg (t_tvar_f X))...
        ** exists. intros Y Fry.
           forwards~ HR1: applyty_rename (t_tvar_f Y) H1. forwards~ HR2: applyty_rename (t_tvar_f Y) H2.
           simpl_rename HR1. simpl_rename HR2.
           assert (Heq: forall Y, (t_and (close_typ_wrt_typ X x1) x) -^ Y = t_and (close_typ_wrt_typ X x1 -^ Y) (x -^ Y)) by eauto. rewrite Heq.
           split~. applys DSub_CovAll. intros X0 Fry2.
           apply dsub2asub in H3. forwards: algo_sub_forall_inv X0 H3.
           rewrite Heq. applys DSub_InterLR. eauto.
           solve_dsub...
           autorewrite with lngen.
           all : solve_notin.
        ** exists. intros Y Fry.
           forwards~ HR1: applyty_rename (t_tvar_f Y) H1. simpl_rename HR1.
           forwards~ HR2: napplyty_rename (t_tvar_f Y) H2.
           split. applys~ ApplyTyInterR HR1. auto. eauto with lngen.

    + apply dsub2asub in HS.
      assert (EASY1: A1 <: (t_forall B)) by applys~ DSub_Trans HS. apply dsub2asub in EASY1.
      assert (EASY2: A2 <: (t_forall B)) by applys~ DSub_Trans HS. apply dsub2asub in EASY2.
      forwards: IH B EASY1... forwards: IH B EASY2...
      exists (t_or x x1).
      exists (union x0
                 (union x2
                    (union [[B]]
                           (union [[A1]] (union [[A2]] (union [[x]] [[x1]])))))).
      intros. instantiate_cofinites.
      assert (Heq:forall X, (x | x1 -^ X) = (x -^ X) | (x1-^X)) by eauto. rewrite Heq.
      split~. applys DSub_CovAll. intros. rewrite Heq. inv_forall.
      convert2dsub. applys~ DSub_UnionL H3 H6.
    + exists B0. exists (union [[B]] [[B0]]). convert2dsub. split~.
    + exists t_bot. exists. split~. eauto.
  -  forwards~ (Ha1&Ha2): algo_sub_and_inv HS... inverts H.
     forwards: IH Ha1... forwards: IH Ha2...
     exists x. exists (x0 `union` x2 `union` [[x]] `union` [[x1]]).
     intros. instantiate_cofinites.
     auto_unify_2. forwards~ : open_typ_wrt_typ_inj H5.
     subst. split~.
     convert2asub. applys ASub_forall. intros Y Fry.
     instantiate_cofinites_with Y.
     inv_forall. applys* ASub_and H1.

     Unshelve. all: apply empty.
Qed.


Lemma monotonicity_applyty_1 : forall A A' B C,
    ApplyTy A (fty_StackArg B) C -> A' <: A -> exists C', C' <: C /\ ApplyTy A' (fty_StackArg B) C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  indTypFtySize (size_typ A' + size_typ A + size_typ B).
  lets~ [HF|(?&?&?)]: (ordu_or_split B).
  { forwards Lc: applyty_lc_2 HA. inverts~ Lc. }
  2: { subst. forwards : applyty_splitu_arg_inv HA H. destruct_conj.
       subst. forwards (?&?&?): IH H1... forwards (?&?&?): IH H2...
       exists. split. 2: applys~ ApplyTyUnionArg H...
       applys~ DSub_UnionL. }
  - forwards: applyty_soundness_1 HA.
    forwards HSN: DSub_Trans HS...
    forwards~ : applyty_completeness_1 HSN. destruct_conj.
    inv_arrow. convert2dsub. exists* x.
  (* - forwards: applyty_soundness_2 HA... *)
  (*   pick_fresh Y. forwards~ : H1 Y... *)
  (*   forwards HSN: DSub_Trans HS... *)
  (*   forwards~ : applyty_completeness_2 HSN... *)
  (*   pick fresh X. *)
  (*   forwards~ : H4 X. destruct_conj. *)
  (*   eapply applyty_rename in H5. exists. split... *)
  (*   simpl_rename_goal. subst~. *)
  (*   convert2asub. *)
  (*   forwards : algo_sub_forall_inv X H6. *)
  (*   eapply asub2nsub in H0. *)
  (*   eapply typsubst_typ_new_sub in H0. *)
  (*   rewrite 2 typsubst_typ_spec in H0; rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H0. *)
  (*   apply asub2nsub. apply~ H0. *)
  (*   all: eauto. *)
Qed.

Lemma monotonicity_applyty_2_1 : forall A B B' C,
    ApplyTy A (fty_StackArg B) C -> declarative_subtyping B' B ->
    exists C', declarative_subtyping C' C /\ ApplyTy A (fty_StackArg B') C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  indTypFtySize (size_typ A + size_typ B' + size_typ B).
  lets~ [HF|(?&?&?)]: (ordu_or_split B').
  - forwards: applyty_soundness_1 HA.
    forwards HSN: DSub_Trans H... applys DSub_FunCon HS. eauto.
    forwards~ : applyty_completeness_1 HSN. destruct_conj.
    inv_arrow. convert2dsub. exists* x.
  - assert (S1: x <: B). {
      applys~ DSub_Trans HS.
      convert2asub. use_left_r... applys ASub_refl. eauto.
    }
    forwards: IH S1...
    assert (S2: x0 <: B). {
      applys~ DSub_Trans HS.
      convert2asub. use_right_r... applys ASub_refl. eauto.
    }
    forwards: IH S2...
    exists (x1|x2). split~. applys~ ApplyTyUnionArg H.
Qed.
