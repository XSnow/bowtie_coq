Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export DistSubtyping.
Require Import ApplyTy.

(************************ Notations related to types **************************)
Notation "[ z ~~> u ] t" := (typsubst_typ u z t) (at level 0).
Notation "t ^-^ u"       := (open_typ_wrt_typ t u) (at level 67).
Notation "t -^ x"        := (open_typ_wrt_typ t (t_tvar_f x))(at level 67).
Notation "[[ A ]]"       := (typefv_typ A) (at level 0).
Notation "A <: B"        := (declarative_subtyping A B)
                              (at level 65, B at next level, no associativity) : type_scope.


(***** Properties of local closure *****)

Lemma napplytysm_lc_1 : forall A B, NApplyTySimple A B -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma napplytysm_lc_2 : forall A B, NApplyTySimple A B -> lc_Fty B.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate napplytysm_lc_1 napplytysm_lc_2 : core.


Lemma applytysm_lc_1 : forall A B C, ApplyTySimple A B C -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma applytysm_lc_2 : forall A B C, ApplyTySimple A B C -> lc_Fty B.
Proof.  introv H.  induction* H. Qed.

Lemma applytysm_lc_3 : forall A B C, ApplyTySimple A B C -> lc_typ C.
Proof.  introv H.  induction~ H. inverts H. eauto with lngen. Qed.

#[export] Hint Immediate applytysm_lc_1 applytysm_lc_2 applytysm_lc_3 : core.


(************************ Proofs **************************)
(* ApplyTySimple and ApplyTy are exactly the same when the argument type is union
   ordinary. *)
Lemma applyTySimple_applyTy : forall A BFty,
    UnionOrdinaryFty BFty ->
    (forall C, (ApplyTySimple A BFty C <-> ApplyTy A BFty C) /\
                 (NApplyTySimple A BFty <-> NApplyTy A BFty)).
Proof.
  intro A.
  induction A; intros BFTy Hord; repeat split; intro Happ.
  (* Every case is dealt with either by finding a contradiction with the ordu
     constraint, or through a straightforward application of the induction
     hypotheses. *)
  Local Ltac solve_with_IH H Hord IHA1 IHA2 :=
    inverts H;
    now first
      [
        inverts Hord; exfalso; now find_contradiction_on_split
      | constructor; auto; solve [ apply IHA1; auto | apply IHA2; auto ]
      ].
  all: solve [solve_with_IH Happ Hord IHA1 IHA2].
Qed.

Lemma splu_ind AFty P :
    (forall AFty, UnionOrdinaryFty AFty -> P AFty) ->
    (forall A A1 A2, splu A A1 A2 ->
                     P A1 ->
                     P A2
                     -> P (fty_StackArg A)) ->
    P AFty.
Proof.
(* TODO *)
Admitted.

Lemma applyTySimple_excl_mid : forall A B,
    lc_typ A -> lc_typ B -> (exists C, ApplyTySimple A B C) \/
      (NApplyTySimple A B).
Proof with try eassumption; elia.
  introv Lc1 Lc2.
  indTypFtySize (size_typ A + size_Fty B).
  lets~ [?|(T&T1&T2&?&?)]: (ordu_or_split_Fty B).
  - destruct~ Lc1.
    + (* inter *)
      forwards [(?&?)|?]: IH A1 B...
      all: forwards [(?&?)|?]: IH A2 B...
      all: eauto.
    + (* union *)
      forwards [(?&?)|?]: IH A1 B...
      all: forwards [(?&?)|?]: IH A2 B...
      all: eauto.
    + (* arrow *)
      destruct~ H. forwards~ [?|?]: sub_dec A0 A.
      eauto.
    + (* bot *)
      eauto.
  - inverts H.
    forwards~ [(?&?)|?]: IH A T1...
    all: forwards~ [(?&?)|?]: IH A T2...
    all: eauto.
    + left. (* If this case is true, ApplyTySimple is equivalent to ApplyTy? *)
  (* H : ApplyTySimple A T1 x *)
  (* x0 : typ *)
  (* H1 : ApplyTySimple A T2 x0 *)
  (* ============================ *)
  (* exists C, ApplyTySimple A T C *)
Abort.

Lemma applyTySimple_excl_mid : forall A B,
    (exists C, ApplyTySimple A B C) \/
      (NApplyTySimple A B).
Admitted.

Lemma applyTySimple_inter_l : forall A1 A2 B C,
  ApplyTySimple A1 (fty_StackArg B) C ->
  exists C', ApplyTySimple (A1 & A2) (fty_StackArg B) C' /\ C' <: C.
Proof.
  intros A1 A2 B C1 Happ.
  forwards H: applyTySimple_excl_mid A2 (fty_StackArg B).
  destruct H as [ [C2 ?] | ]; eexists; eauto.
Qed.

Lemma applyTySimple_inter_r : forall A1 A2 B C,
  ApplyTySimple A2 (fty_StackArg B) C ->
  exists C', ApplyTySimple (A1 & A2) (fty_StackArg B) C' /\ C' <: C.
Proof.
  intros A1 A2 B C2 Happ.
  forwards H: applyTySimple_excl_mid A1 (fty_StackArg B).
  destruct H as [ [C1 ?] | ]; eexists; eauto.
Qed.

Lemma mono_applyTySimple_argu : forall A B C B',
        ApplyTySimple A (fty_StackArg B) C ->
        B' <: B ->
        exists C',
          ApplyTySimple A (fty_StackArg B') C' /\
          C' <: C.
Proof.
  intros A.
  induction A;
  introv H; try solve [inverts H].
  - intros.
    inverts H;
      try (specializes IHA1;
          [ eassumption | eassumption | destruct IHA1 as [C1' [? ? ]  ] ]);
      try (specializes IHA2;
          [ eassumption | eassumption | destruct IHA2 as [C2' [? ? ]  ] ]).
    + forwards Hinter: applyTySimple_inter_l; [ eassumption | ].
      destruct Hinter as [ C' [? ?] ].
      eauto.
    + forwards Hinter: applyTySimple_inter_r; [ eassumption | ].
      destruct Hinter as [ C' [? ?] ].
      eauto.
    + do 2 eexists; eauto.
  - intros. inverts H.
    specializes IHA1;
          [eassumption | eassumption | destruct IHA1 as [C1' [? ?] ] ].
    specializes IHA2;
          [eassumption | eassumption | destruct IHA2 as [C2' [? ?] ] ].
    do 2 eexists.
    + eauto.
    + convert2asub; solve_algo_sub; eauto.
  - intros. inverts H.
    eexists.
    eauto.
  - intros. inverts H.
    exists t_bot.
    eauto. splits; auto.
Qed.

Lemma inv_applyTySimple_argu : forall A B C B1 B2 ,
        ApplyTySimple A (fty_StackArg B) C ->
        splu B B1 B2 ->
        exists C1 C2,
          ApplyTySimple A (fty_StackArg B1) C1 /\
          ApplyTySimple A (fty_StackArg B2) C2 /\
          C1 <: C /\
          C2 <: C.
Proof.
  introv Happ Hspl.
  lets H: dsub_splu Hspl.
  destruct H as [? ?].
  forwards H1: mono_applyTySimple_argu A B C B1; eauto.
  forwards H2: mono_applyTySimple_argu A B C B2; eauto.
  destruct H1 as [C1' [? ?] ].
  destruct H2 as [C2' [? ?] ].
  do 2 eexists.
  eauto.
Qed.


Lemma applyTySimple_approx : forall A BFty C,
    ApplyTySimple A BFty C ->
    exists C', ApplyTy A BFty C' /\
             C' <: C.
Proof.
  intros A ?.
  applys splu_ind BFty; clear BFty.
  - intros BFty Hord C.
    intros.
    exists C.
    forwards Hiff: applyTySimple_applyTy; [eassumption | ].
    destruct Hiff as [Hiff _].
    split; [apply Hiff | ]; eauto.
  - intros B B1 B2 Hspl IHB1 IHB2 C Happ.
    forwards H: inv_applyTySimple_argu; try eassumption.
    destruct H as [C1 [C2 [HB1 [HB2 [? ?] ] ] ] ].
    specializes IHB1; eauto.
    destruct IHB1 as [C1' [? ? ] ].
    specializes IHB2; eauto.
    destruct IHB2 as [C2' [? ?] ].
    eexists. split.
    eapply ApplyTyUnionArg; eauto.
    convert2asub.
    solve_algo_sub;
    eauto using algo_trans.
Qed.

Lemma applyTySimple_subst : forall A X U B C,
    ApplyTySimple A (fty_StackArg B) C ->
    lc_typ U ->
    exists C', ApplyTySimple ([X ~~> U] A) ([X ~~> U] B) C' /\
           C' <: [X ~~> U] C.
Proof.
  intros A X U.
  induction A; intros B C Happ ?; cbn; inverts Happ; cbn.
  - specializes IHA1; eauto.
    destruct IHA1 as [ C1 [? ?] ].
    forwards Hinter: applyTySimple_inter_l. eauto.
    destruct Hinter as [ C1' [? ?] ].
    eauto.
  - specializes IHA2; eauto.
    destruct IHA2 as [ C2 [? ?] ].
    forwards Hinter: applyTySimple_inter_r. eauto.
    destruct Hinter as [ C2' [? ?] ].
    eauto.
  - specializes IHA1; eauto.
    destruct IHA1 as [ C1 [? ?] ].
    specializes IHA2; eauto.
    destruct IHA2 as [ C2 [? ?] ].
    eexists. splits; eauto.
  - specializes IHA1; eauto.
    destruct IHA1 as [ C1 [? ?] ].
    specializes IHA2; eauto.
    destruct IHA2 as [ C2 [? ?] ].
    eexists. splits.
    + constructor; eauto.
    + convert2asub.
      solve_algo_sub; eauto.
  - eexists. splits.
    constructor.
    + admit. (* TODO lc *)
    + convert2asub.
      apply typsubst_typ_algo_sub; auto.
    + constructor.
      admit. (* TODO lc *)
  - eexists. splits; auto.
    constructor.
    admit. (* TODO lc *)
Admitted.

Lemma applyTy_subst_ordu : forall A X U B C,
    ApplyTy A (fty_StackArg B) C ->
    lc_typ U ->
    ordu B ->
    exists C', ApplyTy ([X ~~> U] A) ([X ~~> U] B) C' /\
           C' <: [X ~~> U] C.
Proof.
  intros A X U B C Happ Hlc Hord.
  forwards H: applyTySimple_applyTy.
  - constructor. exact Hord.
  - destruct H as [H _].
    rewrite <- H in Happ.
    forwards H': applyTySimple_subst; eauto.
    destruct H' as [C' Hsubst].
    forwards H'': applyTySimple_applyTy.
    + admit. (* TODO lc *)
    + destruct H'' as [H'' _].
      rewrite H'' in Hsubst.
      eauto.
Abort.
