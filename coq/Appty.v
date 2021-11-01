Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Export DistSubtyping.
Require Import LN_Lemmas.

(******** subtyping **********)

#[export] Hint Extern 1 (lc_typ (t_forall _)) =>
let Y:= fresh "Y" in pick_fresh Y; instantiate_cofinites_with Y; applys lc_t_forall_exists Y : core.

Lemma typsubst_typ_algo_sub : forall A B C X,
  algo_sub A B ->
  algo_sub ([X ~~> C] A) ([X ~~> C] B).
Proof with (simpl in *; eauto using typsubst_typ_spli_typ, typsubst_typ_splu_typ).
  introv s.
  Admitted. (*
  induction s; intros...
  - applys~ (ASub_forall (L \u {{X}})).
    introv Fr. forwards* HS: H0 X0 X Y.
    rewrite 2 typsubst_typ_open_typ_wrt_typ in HS...
    case_eq (@eq_dec typevar EqDec_eq_of_X X0 X); intuition...
    rewrite H1 in HS...
Qed.
Admitted. *)

Notation "A <: B" := (declarative_subtyping A B) (at level 0).

Ltac solve_dsub := repeat match goal with
                          | H: declarative_subtyping _ _ |- _ => apply dsub2asub in H
                          | |- declarative_subtyping _ _ => apply dsub2asub
                          end; try solve (solve_algo_sub).

Lemma dsub_lc_1 : forall A B, declarative_subtyping A B -> lc_typ A.
Proof.  introv H.  apply dsub2asub in H.  eauto.  Qed.

Lemma dsub_lc_2 : forall A B, declarative_subtyping A B -> lc_typ B.
Proof.  introv H.  apply dsub2asub in H. eauto.  Qed.

#[export] Hint Immediate dsub_lc_1 dsub_lc_2 : core.

Lemma sub_dec : forall A B,
    lc_typ A -> lc_typ B -> declarative_subtyping A B \/ ~ (declarative_subtyping A B).
Proof.
  intros.
  forwards~ [?|?]: decidability A B.
  left. applys~ dsub2asub.
  right. intro HF. apply dsub2asub in HF. eauto.
Qed.

Lemma nsub_splitu : forall A B B1 B2,
    ~ declarative_subtyping B A -> splu B B1 B2 -> lc_typ A ->
    ~ declarative_subtyping B1 A \/ ~ declarative_subtyping B2 A.
Proof.
  introv HN HS HL.
  destruct (sub_dec B1 A); eauto.
  destruct (sub_dec B2 A); eauto.
  exfalso. applys HN.
  apply dsub2asub in H, H0. applys~ dsub2asub.
Qed.

(******** appty **************)

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

Lemma orduFty_lc : forall Fty, UnionOrdinaryFty Fty -> lc_Fty Fty.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate orduFty_lc : core.

Lemma nappty_lc_1 : forall A B, NApplyTy A B -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma nappty_lc_2 : forall A B, NApplyTy A B -> lc_Fty B.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate nappty_lc_1 nappty_lc_2 : core.

Lemma appty_lc_1 : forall A B C, ApplyTy A B C -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma appty_lc_2 : forall A B C, ApplyTy A B C -> lc_Fty B.
Proof.  introv H.  induction* H. Qed.

Lemma appty_lc_3 : forall A B C, ApplyTy A B C -> lc_typ C.
Proof.  introv H.  induction* H.  eauto with lngen. Qed.

#[export] Hint Immediate appty_lc_1 appty_lc_2 appty_lc_3 : core.

Lemma nappty_splitu_inv : forall A B B1 B2,
    NApplyTy A (fty_StackArg B) -> splu B B1 B2 ->
    NApplyTy A (fty_StackArg B1) \/ NApplyTy A (fty_StackArg B2).
Proof.
  introv HN HS.
  inverts HN; solve_false; auto_unify; eauto.
Qed.

Lemma appty_contradication : forall A B C,
   ApplyTy A B C -> NApplyTy A B -> False.
Proof with solve_false.
  introv HA HN.
  indTypFtySize (size_typ A + size_Fty B).

  inverts HA;
    match goal with
    | H1: NApplyTy _ (fty_StackArg ?B), H2: splu ?B _ _  |- _ =>
      forwards~ [?|?]: nappty_splitu_inv H1 H2
    | _ => inverts HN
    end...

  all: repeat match goal with
  | H1: ApplyTy (t_forall _) (fty_StackArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyFunTy
  | H1: ApplyTy (t_arrow _ _) (fty_StackTyArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyTyFunFty
  | H1: ApplyTy ?A ?B _, H2: NApplyTy ?A ?B |- _ => forwards: IH H2 H1; elia
              end.
Qed.

#[export] Hint Resolve appty_contradication : FalseHd.

Lemma appty_unique : forall A B C1 C2,
    ApplyTy A B C1 -> ApplyTy A B C2 -> C1 = C2.
Proof with solve_false; auto_unify; auto.
  introv HA1 HA2. gen C1 C2.
  indTypFtySize (size_typ A + size_Fty B).
  inverts HA1; inverts HA2...
  all: repeat match goal with
  | H1: ApplyTy ?A ?B _, H2: ApplyTy ?A ?B _ |- _ => forwards: IH H1 H2; elia; clear H1 H2
              end; subst~.
Qed.

Ltac auto_unify_2 :=
  auto_unify; (* unify split *)
  (* unify appty *)
  repeat match goal with
         | [ H1: ApplyTy ?A ?B _ , H2: ApplyTy ?A ?B _ |- _ ] =>
           (forwards : appty_unique H1 H2;
            subst; clear H2)
             end.

Lemma ordu_or_split_Fty: forall F,
    lc_Fty F -> UnionOrdinaryFty F \/ exists A B C, F = fty_StackArg A /\ splu A B C.
Proof.
  introv HL.
  destruct~ HL.
  forwards* [?|(?&?&?)]: ordu_or_split A.
Qed.

Lemma appty_total : forall A F,
    lc_typ A -> lc_Fty F -> exists C, ApplyTy A F C \/ NApplyTy A F.
Proof.
  introv.
  indTypFtySize (size_typ A + size_Fty F).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F).
  - destruct* H.
    (* and / or *)
    all: try forwards~ (?&[?|?]): IH F A1; elia.
    all: try forwards~ (?&[?|?]): IH F A2; elia.
    all: eauto.

    (* arrow / forall *)
    all: destruct H0.
    2,3: solve [exists; right*].

    + destruct* (sub_dec A0 A).
    + eauto.

  - subst.
    forwards~ (?&[?|?]): IH (fty_StackArg x0) A; elia.
    forwards~ (?&[?|?]): IH (fty_StackArg x1) A; elia.
    all: eauto.

  Unshelve. all: apply t_top.
Qed.


Lemma appty_splitu_arg_inv : forall A B B1 B2 C,
    ApplyTy A (fty_StackArg B) C -> splu B B1 B2 ->
    exists C1 C2, C = (t_or C1 C2) /\
    ApplyTy A (fty_StackArg B1) C1 /\ ApplyTy A (fty_StackArg B2) C2.
Proof.
  introv HA HS.
  inverts HA; solve_false; auto_unify; eauto.
Qed.
(*
Lemma appty_inter_both : forall A1 A2 B C1 C2,
    ApplyTy A1 (fty_StackArg B) C1 -> ApplyTy A2 (fty_StackArg B) C2 ->
    exists C, ApplyTy (t_and A1 A2) (fty_StackArg B) C.
Admitted.
*)

Lemma appty_splitu_fun_aux : forall A A1 A2 F,
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
    + (* forall *) inverts HA1... inverts HA2... exists*.
    + (* rcd *) inverts HA1...
  - subst.
    forwards: appty_splitu_arg_inv HA1 H0. forwards: appty_splitu_arg_inv HA2 H0.
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
    + (* split *) forwards* [?|?]: nappty_splitu_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.
    + (* ord *) inverts~ HS...
      * (* and *) inverts HA... forwards~ : proj2 (IH F A0) H1...
      * (* and *) inverts HA... forwards~ : proj2 (IH F B) H1...
      * (* forall *) inverts HA... constructor~.
    + (* split *) forwards* [?|?]: nappty_splitu_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.

   Unshelve. all: apply t_top.
Qed.

Lemma appty_splitu_fun : forall A A1 A2 F C1 C2,
    ApplyTy A1 F C1 -> ApplyTy A2 F C2 -> splu A A1 A2 ->
    exists C', ApplyTy A F C' /\ declarative_subtyping C' (t_or C1 C2).
Proof.
  intros.
  forwards* (?&?): appty_splitu_fun_aux.
Admitted.

Lemma nappty_splitu_fun : forall A A1 A2 F,
    NApplyTy A1 F \/ NApplyTy A2 F -> splu A A1 A2 -> NApplyTy A F.
Proof.
  intros.
  forwards* (?&?): appty_splitu_fun_aux.
Qed.

Lemma nappty_split_inv : forall A A1 A2 F,
    NApplyTy A F -> spli A A1 A2 -> NApplyTy A1 F /\ NApplyTy A2 F.
Proof with elia; try eassumption; eauto.
  introv HN HS.
  indTypFtySize (size_typ A + size_Fty F).
  inverts HN; solve_false.
  - (* rcd *) inverts HS; eauto.
  - (* forall *) inverts HS. split; constructor~.
  - (* arrow sub *) inverts~ HS.
    assert (~ declarative_subtyping B A3). {
      intros HF. apply H2. solve_dsub.
    }
    assert (~ declarative_subtyping B A4). {
      intros HF. apply H2. solve_dsub.
    }
    eauto.
  - (* arrow *) inverts~ HS.
  - (* or *) forwards [ [?|?] | [?|?] ]: double_split HS. eauto.
    all: destruct_conj.
    all: try match goal with
         | H1: NApplyTy ?A _, H2: spli ?A _ _ |- _ => forwards (?&?): IH H1 H2; elia
             end.
    all: split*.
    all: applys nappty_splitu_fun; try eassumption; eauto.
  - (* or *) forwards [ [?|?] | [?|?] ]: double_split HS. eauto.
    all: destruct_conj.
    all: try match goal with
         | H1: NApplyTy ?A _, H2: spli ?A _ _ |- _ => forwards (?&?): IH H1 H2; elia
             end.
    all: split*.
    all: applys nappty_splitu_fun...
  - (* union argL *)
    split.
    all: applys NApplyTyUnionArgL...
    all: applys IH HS...
  - (* union argR *)
    split.
    all: applys NApplyTyUnionArgR...
    all: applys IH HS...
  - auto_unify...

    Unshelve. all: apply t_top.
Qed.

(* this definition cannot work
Lemma appty_split_inv : forall A A1 A2 F C,
    ApplyTy A F C -> spli A A1 A2 -> UnionOrdinaryFty F ->
    exists C1 C2,
    (ApplyTy A1 F C1 /\ C <: C1) \/ ApplyTy A2 F C2.
 *)

Lemma appty_split_inv : forall A A1 A2 F C,
    ApplyTy A F C -> spli A A1 A2 -> UnionOrdinaryFty F ->
    (exists C1 C2, ApplyTy A1 F C1 /\ ApplyTy A2 F C2 /\ (t_and C1 C2) <: C) \/
    (ApplyTy A1 F C \/ ApplyTy A2 F C).
Proof with elia; try eassumption; eauto.
  introv HA HS HU.
  indTypFtySize (size_typ A).
  inverts HA; solve_false; auto_unify...
  - (* forall *) inverts HS; eauto.  Admitted. (*
  - (* arrow sub *) inverts~ HS.
    + left*.
    + inverts keep H0.
      solve_dsub. forwards [?|?]: algo_sub_orlr_inv H1...
      * left. exists. applys~ ApplyTyFun. solve_dsub...
      * right. exists. applys~ ApplyTyFun. solve_dsub...
  - (* or *) forwards [ [?|?] | [?|?] ]: double_split HS. eauto.
    all: destruct_conj.
    all: repeat match goal with
             | H1: ApplyTy ?A _ _, H2: spli ?A _ _ |- _ =>
               forwards [(?&?)|(?&?)]: IH H2 H1; elia; clear H2
             | H1: ApplyTy ?A1 _ _, H2: ApplyTy ?A2 _ _, H3: splu _ ?A1 ?A2 |- _ =>
               forwards* (?&?): appty_splitu_fun H1 H2 H3; elia; clear H3
                end.
    all: eauto.
Qed. *)
(*
The above lemma does not hold without ordu condition

Let B1 B2 be two ordu types

apply (A1, B1) => apply (A1&A2, B1)
apply (A2, B2) => apply (A1&A2, B2)

together we have apply (A1&A2, B1 | B2)

But neither apply (A1, B1|B2) or apply (A2, B1|B2) holds
 *)


Lemma monotonicity_appty_1 : forall A A' F C,
    ApplyTy A F C -> declarative_subtyping A' A -> exists C', declarative_subtyping C' C /\ ApplyTy A' F C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  indTypFtySize (size_typ A + size_Fty F).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F). eauto.
  2: { subst. forwards : appty_splitu_arg_inv HA H0. destruct_conj.
       subst. forwards (?&?&?): IH H1... forwards (?&?&?): IH H2...
       exists. split. 2: applys~ ApplyTyUnionArg H0...
       applys~ DSub_UnionL. applys* DSub_UnionRL. applys* DSub_UnionRR. }
  - (* ordinary F *)
    gen C. apply dsub2asub in HS. induction HS; intros.
    + (* refl *) exists. split. applys* DSub_Refl. easy.
    + (* top *) false. applys* appty_contradication HA.
    + (* bot *) exists* t_bot.
    + (* arrow *) apply dsub2asub in HS1. apply dsub2asub in HS2.
      inverts keep HA... exists A2. split*.
    + (* forall *)
      inverts keep HA... exists (A ^-^ B0).
      pick fresh X for ([[A]] `union` [[B]] `union` L).  instantiate_cofinites.
      split.
      * eapply typsubst_typ_algo_sub in H0.
        applys dsub2asub.
        rewrite 2 (typsubst_typ_intro X _ B0); eauto.
      * eauto with lngen.
    + (* rcd *) inverts HA...
    + (* split *)
      assert (ASSUME: ordu A) by admit.
      destruct B... all: try solve [inverts HA; solve_false].
      * (* and *) auto_unify_2. inverts HA...
        ** forwards: IHHS1...
        ** forwards: IHHS2...
        ** forwards~ (?&?&?): IHHS1...
           forwards~ (?&?&?): IHHS2...
           auto_unify_2.
           exists x0. split~.
      * (* or *) inverts HA...
        assert (EASY: algo_sub A (t_or B3 B4)) by admit.
        forwards [Hd|Hd]: algo_sub_orlr_inv EASY ASSUME. eauto.
        all: apply dsub2asub in Hd.
        all: forwards: IH Hd...
        all: exists x; split~.
        all: admit. (* easy *)
(* without ASSUME cannot prove
        forwards [ [?|?] | [?|?] ]: double_split H0. eauto. all: destruct_conj.
        ** forwards~ [?|?] : appty_split_inv H4 H1...
           *** forwards (?&?&?): appty_splitu_fun H2...
               forwards~ (?&?&?): IHHS1...
               exists x4; split~.
                 admit. admit. admit.
*)
      *
**
        inverts H4...
        appty_splitu_fun


        solve_dsub. applys* ASub_and.

        destruct A.
        eauto. eauto.

        applys* ASub_andr.
        eauto


        simpl in *;
  try solve [applys SpI_and];
  try solve [applys SpU_or];
  try repeat match goal with
             | [ H1: spli (t_and _ _)  _ _  |- _ ] =>
               inverts H1
             | [ H1: splu (t_or _ _)  _ _  |- _ ] =>
               inverts H1
             | [ H1: spli ?A  _ _ , H2: spli ?A _ _ |- _ ] =>
               (forwards (?&?): spli_unique H1 H2;
                subst; clear H2)
             | [ H1: splu ?A  _ _ , H2: splu ?A _ _ |- _ ] =>
               (forwards (?&?): splu_unique H1 H2;
                subst; clear H2)
             end.
        auto_unify_2. inverts H0.
    a+

      Search (open_typ_wrt_typ _ _ = _).

      rewrite 2 typsubst_typ_spec in H2.

      constructor*. applys~ DSub_Trans HS1.



Lemma monotonicity_appty_2 : forall A B B' C,
    ApplyTy A B C -> declarative_subtyping B' B -> exists C', declarative_subtyping C' C /\ ApplyTy A B' C'.
