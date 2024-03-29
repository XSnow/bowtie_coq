Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.


Definition typ_as_ftyp := fty_StackArg.
Coercion typ_as_ftyp : typ >-> Fty.

Notation "[| A |]"        := (fty_StackTyArg A)
                               (at level 5) : type_scope.

(*****************************************************************************)

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

Lemma lc_fty_inv_1 : forall A:typ , lc_Fty A -> lc_typ A.
Proof. introv H. inverts~ H. Qed.

Lemma lc_fty_inv_2 : forall A:typ , lc_Fty [| A |] -> lc_typ A.
Proof. introv H. inverts~ H. Qed.

#[export] Hint Resolve lc_fty_inv_1 lc_fty_inv_2 : core.

Lemma napplyty_bot : forall A,
    NApplyTy t_bot A -> False.
Proof.
  introv App. inductions App.
  all: eauto.
Qed.

#[export] Hint Immediate napplyty_bot : core.

Lemma napplyty_splitu_arg_inv : forall A B B1 B2,
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
      forwards~ [?|?]: napplyty_splitu_arg_inv H1 H2
    | _ => inverts HN
    end.

  all: repeat match goal with
  | H1: ApplyTy (t_forall _) (fty_StackArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyFunTy
  | H1: ApplyTy (t_arrow _ _) (fty_StackTyArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyTyFunFty
  | H1: ApplyTy ?A ?B _, H2: NApplyTy ?A ?B |- _ => forwards: IH H2 H1; elia
              end.
  all: solve_false.
Qed.

#[export] Hint Extern 1 => lazymatch goal with
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
  repeat lazymatch goal with
         | [ H1: ApplyTy ?A ?B _ , H2: ApplyTy ?A ?B _ |- _ ] =>
           (forwards : applyty_unique H1 H2;
            subst; clear H2)
             end.

Lemma ordu_or_split_Fty: forall F,
    lc_Fty F -> UnionOrdinaryFty F \/ exists A B C, F = fty_StackArg A /\ splu A B C.
Proof.
  introv HL.
  destruct~ HL.
  forwards~ [?|(?&?&?)]: ordu_or_split A. intuition eauto.
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
    + (* forall *) inverts HA1... inverts HA2... exists~.
    + (* rcd *) inverts HA1...
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
      * (* forall *) inverts HA... constructor~.
    + (* split *) forwards* [?|?]: napplyty_splitu_arg_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.
    + (* ord *) inverts~ HS...
      * (* and *) inverts HA... forwards~ : proj2 (IH F A0) H1...
      * (* and *) inverts HA... forwards~ : proj2 (IH F B) H1...
      * (* forall *) inverts HA... constructor~.
    + (* split *) forwards* [?|?]: napplyty_splitu_arg_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.

   Unshelve. all: apply t_top.
Qed.

(* Lemma B.9 *)
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

(*------------------- Soundness Type-Level Dispatch --------------------------*)

(* Soundness of Type-Level Dispatch [1] *)
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

(* Soundness of Type-Level Dispatch [2] *)
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
        split_l. use_left_r...  use_right_r...
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
Qed.


(* Soundness of Type-Level Dispatch [2] *)
Lemma applyty_soundness_2_simple : forall A B C,
    ApplyTy A (fty_StackTyArg B) C ->
    exists A', A <: t_forall A' /\ C <: (A' ^-^ B).
Proof.
  introv H. pick fresh X.
  forwards~ (?&?&?): applyty_soundness_2 H.
  subst. forwards~ (?&?): H1 X.
  exists x. split~. convert2asub. applys* ASub_refl.
Qed.

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

Lemma applyty_completeness_1_all : forall A B D,
    A <: (t_arrow B D) ->
         exists C, ApplyTy A (fty_StackArg B) C /\ (t_arrow B C) <: (t_arrow B D).
Proof with try eassumption; elia.
  introv Sub.
  indTypFtySize (size_Fty B).
  forwards [?|(T&T1&T2&?&?)]: ordu_or_split_Fty B... now eauto.
  - applys applyty_completeness_1... inverts~ H.
  - inverts H.
    assert (Sub1: A <: t_arrow T1 D).
    { applys DSub_Trans Sub. constructor~. convert2asub. eauto. }
    assert (Sub2: A <: t_arrow T2 D).
    { applys DSub_Trans Sub. constructor~. convert2asub. eauto. }
    forwards: IH Sub1... forwards: IH Sub2...
    all: destruct_conj.
    + exists (x0 | x). split. econstructor...
      convert2asub.  auto_inv. constructor*.
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

Lemma napplyty_sub_inv : forall (A B C : typ),
    NApplyTy (t_arrow A B) C -> C <: A -> False.
Proof.
  introv HA Sub.
  indTypSize (size_typ C).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split C...
  - forwards~ : applyty_completeness_1 (t_arrow A B) C B.
    applys~ DSub_FunCon. forwards* : napplyty_lc_1 HA.
    destruct_conj.
    solve_false.
  - forwards [?|?]: napplyty_splitu_arg_inv HA Hu.
    + cut (x <: A).
      * intros Sub'. applys IH H Sub'. elia.
      * applys DSub_Trans Sub. convert2asub. eauto.
    + cut (x0 <: A).
      * intros Sub'. applys IH H Sub'. elia.
      * applys DSub_Trans Sub. convert2asub. eauto.
Qed.

Lemma applyty_forall_inv : forall (A B C : typ),
    ApplyTy (t_forall A) B C -> False.
Proof.
  introv HA. inductions HA. eauto.
Qed.

#[export] Hint Immediate napplyty_sub_inv applyty_forall_inv : FalseHd.

(*------------------------------ Lemma B.10 ----------------------------------*)

(* B.10 [1] *)
Lemma monotonicity_applyty_1 : forall A A' (F : Fty) C,
    ApplyTy A F C -> A' <: A -> exists C', C' <: C /\ ApplyTy A' F C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  indTypFtySize (size_typ A' + size_typ A + size_Fty F).
  lets~ [HF|(?&?&?&?&?)]: (ordu_or_split_Fty F). eauto.
  2: { subst. forwards : applyty_splitu_arg_inv HA H0. destruct_conj.
       subst. forwards (?&?&?): IH H1... forwards (?&?&?): IH H2...
       exists. split. 2: applys~ ApplyTyUnionArg H0...
       applys~ DSub_UnionL. }
  inverts HF.
  - forwards: applyty_soundness_1 HA.
    forwards HSN: DSub_Trans HS...
    forwards~ : applyty_completeness_1 HSN. destruct_conj.
    inv_arrow. convert2dsub. exists* x.
  - forwards: applyty_soundness_2 HA...
    pick_fresh Y. forwards~ : H1 Y...
    forwards HSN: DSub_Trans HS...
    forwards~ : applyty_completeness_2 HSN...
    pick fresh X.
    forwards~ : H4 X. destruct_conj.
    eapply applyty_rename in H5. exists. split...
    simpl_rename_goal. subst~.
    convert2asub.
    forwards : algo_sub_forall_inv X H6.
    eapply asub2nsub in H0.
    eapply typsubst_typ_new_sub in H0.
    rewrite 2 typsubst_typ_spec in H0;
      rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H0.
    apply asub2nsub.
    all: eauto.
Qed.

(* B.10 [2] *)
Lemma monotonicity_applyty_2_1 : forall (A B B' C : typ),
    ApplyTy A B C -> B' <: B ->
    exists C', C' <: C /\ ApplyTy A B' C'.
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

(*---------------------- Inversion of Subtyping on (Co-)Value types ----------*)

(* [5] *)
Lemma applyty_arrow : forall A1 A2 V B,
    ApplyTy (t_arrow A1 A2) V B -> isValFty V -> exists V', V = fty_StackArg V' /\ isValTyp V'.
Proof.
  introv App Val.
  inductions App.
  - inverts* Val.
  - inverts* Val.
Qed.

(* [6] *)
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

(* [7] *)
Lemma apply_top_false_1 : forall V,
    isValTyp V -> NApplyTy t_top [| V |].
  introv Val. constructor*.
Qed.

(* [7] *)
Lemma apply_top_false_2 : forall V,
    isValTyp V -> NApplyTy t_top V.
Proof with eauto.
  introv Val. induction* Val.
Qed.

(* [7] *)
Lemma applyty_top : forall V A,
    ApplyTy t_top V A -> False.
Proof.
  introv App.
  inductions App.
  forwards~ : IHApp1.
Qed.

#[export] Hint Immediate applyty_top : FalseHd.

(* [8] *)
Lemma apply_box_false_1 : forall l V1 V2,
    isValTyp V1 -> isValTyp V2 -> NApplyTy (t_rcd l V1) [| V2 |].
  introv Val. constructor*.
Qed.

(* [8] *)
Lemma apply_box_false_2 : forall l V1 V2,
    isValTyp V1 -> isValTyp V2 -> NApplyTy (t_rcd l V1) V2.
Proof with eauto.
  introv Val. induction* Val.
Qed.

(*------------------------- Inversion of Type-Level Dispatch -----------------*)

(* [1] *)
Lemma applyty_bot : forall B C,
    ApplyTy t_bot B C -> C ~= t_bot.
Proof. introv H. inductions H; eauto using iso_or_2. Qed.

(* [2] the argument must be a type *)
Lemma applyty_arrow_sound_1 : forall A B F D,
    ApplyTy (t_arrow A B) F D -> exists (C:typ), F = C.
Proof. introv H. inverts* H. Qed.

(* [2] *)
Lemma applyty_arrow_sound_2 : forall (A B C D : typ),
    ApplyTy (t_arrow A B) C D -> C <: A /\ B ~= D.
Proof with try eassumption; elia; destruct_conj; auto_unify_2.
  introv HA.
  indTypSize (size_typ C).
  forwards [?|(?&?&?)]: ordu_or_split C. now eauto.
  - forwards Sub: applyty_soundness_1 HA.
    convert2asub. inv_arrow. convert2dsub.
    splits*. split~.
    forwards~ : applyty_completeness_1 (t_arrow A B) C B...
    convert2asub. inv_arrow. convert2dsub. easy.
  - forwards (?&?) : applyty_splitu_arg_inv HA...
    forwards: IH H1...
    forwards: IH H2...
    split.
    + convert2asub. applys ASub_or...
    + subst. applys~ iso_dup_1.
Qed.

(* [3] the argument must be a type argument *)
Lemma applyty_forall_sound_1 : forall A F D,
    ApplyTy (t_forall A) F D -> exists (C:typ), F = [| C |].
Proof. introv H. inductions H.
       - eauto.
       - forwards~ : IHApplyTy1. forwards~ : IHApplyTy2. destruct_conj.
         solve_false.
Qed.

(* [3] *)
Lemma applyty_forall_sound_2 : forall (A B D : typ),
    ApplyTy (t_forall A) [|B|] D -> D ~= (A ^-^ B).
Proof with destruct_conj.
  introv HA. inverts HA.
  applys iso_refl.
  inverts* H1. eauto with lngen.
Qed.

(* [7] *)
Lemma napplyty_splitu_inv : forall A (F: Fty) A1 A2,
    NApplyTy A F -> splu A A1 A2 ->
    NApplyTy A1 F \/ NApplyTy A2 F.
Proof.
  introv HA HS. gen A1 A2.
  induction HA; intros; solve_false; inverts_all_spl; auto_unify.
  all: try (forwards: IHHA; [ eassumption |.. ]).
  all: try (forwards [?|?]: IHHA; [ eassumption |.. ]).
  all: try (forwards [?|?]: IHHA1; [ eassumption |.. ]).
  all: try (forwards [?|?]: IHHA2; [ eassumption |.. ]).
  all: try solve [left*; auto]; try solve [right*; auto].
Qed.

(* [4] *)
Lemma applyty_splitu_inv : forall A (F: Fty) A1 A2 C,
    ApplyTy A F C -> splu A A1 A2 ->
    exists C1 C2, C ~= C1 | C2 /\ ApplyTy A1 F C1 /\ ApplyTy A2 F C2.
Proof with exists; splits.
  introv HA HS. gen A1 A2.
  induction HA; intros; solve_false; inverts_all_spl; auto_unify.
  all: try (forwards: IHHA; [ eassumption |.. ]).
  all: try solve [exists; splits; eauto].
  all: try (forwards: IHHA; [ eassumption |.. ]; destruct_conj).
  all: try (forwards: IHHA1; [ eassumption |.. ]; destruct_conj).
  all: try (forwards: IHHA2; [ eassumption |.. ]; destruct_conj).
  all: try lazymatch goal with
         | H: NApplyTy _ _ |- _ =>
             forwards [?|?]: napplyty_splitu_inv H; [ eassumption | .. ]
         end.
  all: auto_unify_2.
  - instantiate_cofinites...
    forwards HN: splu2nsplu H2. forwards HN': typsubst_typ_splu x B HN.
    now eauto.
    rewrite 3 typsubst_typ_spec in HN'.
    rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in HN'; [ eauto | .. ].
    all: try solve_notin.
  - exists; splits.
    2-3: applys ApplyTyUnionArg; try eassumption.
    applys iso_trans. 2: applys iso_shuffle.
    applys* iso_or_match.
    all: iso_inverts_all_lc; eauto.
  - exists; splits.
    2-3: applys ApplyTyInterL; try eassumption.
    all: eauto.
  - forwards~ [(?&?)|?]: applyty_total B2 Fty5...
    all: try (applys ApplyTyInterBoth; now eassumption).
    all: try (applys ApplyTyInterL; now eassumption).
    all: try (applys ApplyTyInterR; now eassumption).
    all: try applys iso_absorb_1.
    all: try applys* iso_dup_1.
    all: iso_inverts_all_lc; eauto.
  - forwards~ [(?&?)|?]: applyty_total B1 Fty5...
    all: try (applys ApplyTyInterBoth; now eassumption).
    all: try (applys ApplyTyInterL; now eassumption).
    all: try (applys ApplyTyInterR; now eassumption).
    all: try applys iso_absorb_2.
    all: try applys iso_dup_1.
    all: iso_inverts_all_lc; eauto.
  - forwards~ [(?&?)|?]: applyty_total A5 Fty5...
    all: try (applys ApplyTyInterBoth; now eassumption).
    all: try (applys ApplyTyInterL; now eassumption).
    all: try (applys ApplyTyInterR; now eassumption).
    all: try applys iso_absorb_3.
    all: try applys iso_dup_1.
    all: iso_inverts_all_lc; eauto.
  - forwards~ [(?&?)|?]: applyty_total A4 Fty5...
    all: try (applys ApplyTyInterBoth; now eassumption).
    all: try (applys ApplyTyInterL; now eassumption).
    all: try (applys ApplyTyInterR; now eassumption).
    all: try applys iso_absorb_4.
    all: try applys iso_dup_1.
    all: iso_inverts_all_lc; eauto.
  - exists; splits.
    all: try (applys ApplyTyInterBoth; now eassumption).
    all: try (applys ApplyTyInterL; now eassumption).
    all: try (applys ApplyTyInterR; now eassumption).
    all: easy.
  - exists; splits.
    all: try (applys ApplyTyInterBoth; now eassumption).
    all: try (applys ApplyTyInterL; now eassumption).
    all: try (applys ApplyTyInterR; now eassumption).
    applys iso_trans. 2: applys* iso_dist_1.
    applys* iso_and_match.
    all: iso_inverts_all_lc; eauto.
  - exists; splits.
    all: try (applys ApplyTyInterBoth; now eassumption).
    applys iso_trans. 2: applys* iso_dist_2.
    applys* iso_and_match.
    all: iso_inverts_all_lc; eauto.
Qed.

(* [5] *)
Lemma napplyty_spliti_inv : forall A B A1 A2,
    NApplyTy A B -> spli A A1 A2 ->
    NApplyTy A1 B /\ NApplyTy A2 B.
Proof with destruct_conj; try match goal with |- lc_typ _ => eauto end; try eassumption.
  introv HN HS. gen A1 A2.
  induction HN; intros; solve_false; inverts_all_spl; auto_unify.
  all: try (forwards: IHHN; [ eassumption |.. ])...
  all: try solve [split; eauto]...
  - cut (~ B <: A3). cut (~ B <: A4).
    + split; eauto.
    + intro HF. apply H2. convert2asub.
      applys algo_trans HF. applys ASub_orr... eauto.
    + intro HF. apply H2. convert2asub.
      applys algo_trans HF. applys ASub_orl... eauto.
Qed.

(* [6] *)
Lemma apply_top_false : forall A,
    lc_typ A -> NApplyTy t_top A.
Proof with eauto.
  introv Lc. induction* Lc.
Qed.

(*------------------------------ Lemma B.22 -----------------------------------*)

(* B.22 (1) *)
Lemma applyty_arrow_complete : forall A B C,
    C <: A -> lc_typ B -> exists D, ApplyTy (t_arrow A B) C D.
Proof with elia.
  introv Sub HB.
  indTypSize (size_typ C).
  forwards [?|(?&?&?)]: ordu_or_split C. now eauto.
  - forwards: applyty_completeness_1 (t_arrow A B) C B.
    + convert2asub. applys* ASub_arrow.
    + easy.
    + destruct_conj. eauto.
  - cut (x <: A). cut (x0 <: A).
    + introv Sub1 Sub2.
      forwards~ : IH A B Sub1...
      forwards~ : IH A B Sub2...
      destruct_conj.
      exists*.
    + convert2asub. applys* algo_trans Sub.
    + convert2asub. applys* algo_trans Sub.
Qed.

(* B.22 (2) *)
Lemma applyty_forall_complete : forall A B,
    lc_typ (t_forall A) -> lc_typ B -> exists C, ApplyTy (t_forall A) [|B|] C.
Proof with elia.
  intros. exists.
  constructor*.
Qed.

(* B.22 (3) *)
Lemma applyty_inter : forall B A1 A2 C1 C2,
    ApplyTy A1 B C1 -> ApplyTy A2 B C2 ->
    exists C, ApplyTy (A1&A2) B C.
Proof with destruct_conj.
  introv H1 H2.
  indTypFtySize (size_Fty B).
  forwards [?|(?&?&?)]: ordu_or_split_Fty B... now eauto.
  - exists. applys* ApplyTyInterBoth.
  - subst.
    forwards* (?&?) : applyty_splitu_arg_inv H1.
    forwards* (?&?) : applyty_splitu_arg_inv H2...
    forwards: IH (fty_StackArg x0) A1 A2; try eassumption; elia.
    forwards: IH (fty_StackArg x1) A1 A2; try eassumption; elia...
    exists*.
Qed.

(* B.22 (4) *)
Lemma applyty_union : forall B A1 A2 C1 C2,
    ApplyTy A1 B C1 -> ApplyTy A2 B C2 ->
    exists C, ApplyTy (A1 | A2) B C.
Proof with try eassumption; destruct_conj.
  introv H1 H2.
  indTypFtySize (size_Fty B).
  forwards [?|(?&?&?)]: ordu_or_split_Fty B... now eauto.
  - exists. applys ApplyTyUnion...
  - subst.
    forwards* (?&?) : applyty_splitu_arg_inv H1.
    forwards* (?&?) : applyty_splitu_arg_inv H2...
    forwards: IH (fty_StackArg x0) A1 A2; try eassumption; elia.
    forwards: IH (fty_StackArg x1) A1 A2; try eassumption; elia...
    exists*.
Qed.

(*------------------------- Type Substitution --------------------------------*)
Lemma typsubst_iso : forall A B C X,
  A ~= B -> lc_typ C ->
  ([X ~~> C] A) ~= ([X ~~> C] B).
Proof.
  introv (HS1&HS2) Lc. unfold iso.
  split; convert2asub;
    applys~ typsubst_typ_algo_sub.
Qed.

Lemma applyty_iso : forall (A A' B B' C : typ),
    ApplyTy A B C -> A' ~= A -> B' ~= B ->
    exists C', C' <: C /\ ApplyTy A' B' C'.
Proof with try eassumption.
  introv App (HS1&HS1') (HS2&HS2').
  forwards (?&Sub&App'): monotonicity_applyty_1 App...
  forwards (?&Sub'&App''): monotonicity_applyty_2_1 App'...
  exists. split. applys DSub_Trans... apply App''.
Qed.

(* Type Substitution Over Type-Level Dispatch *)
Lemma typsubst_applyty : forall (A B C U : typ) X,
    ApplyTy A B C -> lc_typ U ->
    exists C', ApplyTy ([X ~~> U] A) ([X ~~> U] B) C' /\ C' <: [X ~~> U] C.
Proof with try eassumption.
  introv App Lc.
  apply applyty_soundness_1 in App.
  convert2asub. eapply typsubst_typ_algo_sub in App...
  convert2dsub. simpl in App.
  forwards (?&?&?): applyty_completeness_1_all App.
  exists x; split; convert2asub; auto_inv...
Qed.
