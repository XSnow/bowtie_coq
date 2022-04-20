Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export Dispatch.


(***** Properties of local closure *****)

Lemma napplytyls_lc_1 : forall A B, NApplyTyLs A B -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma napplytyls_lc_2 : forall A B, NApplyTyLs A B -> lc_Fty B.
Proof.  introv H.  induction~ H.  Qed.

#[export] Hint Immediate napplytyls_lc_1 napplytyls_lc_2 : core.


Lemma applytyls_lc_1 : forall A B C, ApplyTyLs A B C -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma applytyls_lc_2 : forall A B C, ApplyTyLs A B C -> lc_Fty B.
Proof.  introv H.  induction* H. Qed.

Lemma applytyls_lc_3 : forall A B C, ApplyTyLs A B C -> lc_typ C.
Proof.  introv H.  induction~ H. inverts H. eauto with lngen. Qed.

#[export] Hint Immediate applytyls_lc_1 applytyls_lc_2 applytyls_lc_3 : core.


(***************************** Nick's Proofs **********************************)
(* ApplyTyLs and ApplyTy are exactly the same when the argument type is union
   ordinary. *)
Lemma applyTyLs_applyTy : forall A BFty,
    UnionOrdinaryFty BFty ->
    (forall C, (ApplyTyLs A BFty C <-> ApplyTy A BFty C) /\
                 (NApplyTyLs A BFty <-> NApplyTy A BFty)).
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

Lemma applyTyLs_excl_mid : forall A B,
    lc_typ A -> lc_Fty B -> (exists C, ApplyTyLs A B C) \/
      (NApplyTyLs A B).
Proof with try eassumption; elia.
  introv Lc1 Lc2.
  indTypFtySize (size_typ A + size_Fty B).
  destruct~ Lc1.
    + (* inter *)
      forwards [(?&?)|?]: IH B A1...
      all: forwards [(?&?)|?]: IH B A2...
      all: eauto.
    + (* union *)
      forwards [(?&?)|?]: IH B A1...
      all: forwards [(?&?)|?]: IH B A2...
      all: eauto.
    + (* arrow *)
      destruct~ Lc2.
      forwards~ [?|?]: sub_dec A0 A.
      now left*.
    + (* forall *)
      destruct~ Lc2.
      now left*.
    + (* bot *)
      eauto.
Qed.

Lemma applyTyLs_inter_l : forall A1 A2 B C,
  lc_typ A2 -> ApplyTyLs A1 (fty_StackArg B) C ->
  exists C', ApplyTyLs (A1 & A2) (fty_StackArg B) C' /\ C' <: C.
Proof.
  intros A1 A2 B C1 Lc Happ.
  forwards* H: applyTyLs_excl_mid A2 (fty_StackArg B).
  destruct H as [ [C2 ?] | ]; eexists; eauto.
Qed.

Lemma applyTyLs_inter_r : forall A1 A2 B C,
  lc_typ A1 -> ApplyTyLs A2 (fty_StackArg B) C ->
  exists C', ApplyTyLs (A1 & A2) (fty_StackArg B) C' /\ C' <: C.
Proof.
  intros A1 A2 B C2 Lc Happ.
  forwards* H: applyTyLs_excl_mid A1 (fty_StackArg B).
  destruct H as [ [C1 ?] | ]; eexists; eauto.
Qed.

Lemma mono_applyTyLs_argu : forall A B C B',
        ApplyTyLs A (fty_StackArg B) C ->
        B' <: B ->
        exists C',
          ApplyTyLs A (fty_StackArg B') C' /\
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
    + forwards [ C' [? ?] ]: applyTyLs_inter_l; [ | eassumption | eauto ].
      now eauto.
    + forwards [ C' [? ?] ]: applyTyLs_inter_r; [ | eassumption | eauto ].
      now eauto.
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

Lemma inv_applyTyLs_argu : forall A B C B1 B2 ,
        ApplyTyLs A (fty_StackArg B) C ->
        splu B B1 B2 ->
        exists C1 C2,
          ApplyTyLs A (fty_StackArg B1) C1 /\
          ApplyTyLs A (fty_StackArg B2) C2 /\
          C1 <: C /\
          C2 <: C.
Proof.
  introv Happ Hspl.
  lets H: dsub_splu Hspl.
  destruct H as [? ?].
  forwards H1: mono_applyTyLs_argu A B C B1; eauto.
  forwards H2: mono_applyTyLs_argu A B C B2; eauto.
  destruct H1 as [C1' [? ?] ].
  destruct H2 as [C2' [? ?] ].
  do 2 eexists.
  eauto.
Qed.

Lemma applyTyLs_approx : forall A BFty C,
    ApplyTyLs A BFty C ->
    exists C', ApplyTy A BFty C' /\
             C' <: C.
Proof with elia.
  introv H.
  indTypFtySize (size_Fty BFty).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty BFty). now eauto.
  - exists C.
    forwards Hiff: applyTyLs_applyTy; [eassumption | ].
    destruct Hiff as [Hiff _].
    split; [apply Hiff | ]; eauto.
  - subst.
    forwards [C1 [C2 [HB1 [HB2 [? ?] ] ] ] ] : inv_applyTyLs_argu; try eassumption.
    forwards [C1' [? ? ] ] : IH HB1...
    forwards [C2' [? ? ] ] : IH HB2...
    eexists. split.
    eapply ApplyTyUnionArg; eauto.
    convert2asub. applys algo_trans ( C1 | C2 ).
    match_or; eauto.
    split_l; eauto.
Qed.

Lemma applyTyLs_subst : forall A X U B C,
    ApplyTyLs A (fty_StackArg B) C ->
    lc_typ U ->
    exists C', ApplyTyLs ([X ~~> U] A) ([X ~~> U] B) C' /\
           C' <: [X ~~> U] C.
Proof with try eassumption.
  intros A X U.
  induction A; intros B C Happ ?; cbn; inverts Happ; cbn.
  - specializes IHA1; eauto.
    destruct IHA1 as [ C1 [IHA1 ?] ].
    forwards [ C1' [? ?] ]: applyTyLs_inter_l IHA1.
    2: eauto. 1: eauto with lngen.
  - specializes IHA2; eauto.
    destruct IHA2 as [ C2 [IHA2 ?] ].
    forwards [ C2' [? ?] ]: applyTyLs_inter_r IHA2.
    2: now eauto. 1: eauto with lngen.
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
    + eauto with lngen.
    + convert2asub.
      apply typsubst_typ_algo_sub; auto.
    + constructor.
      eauto with lngen.
  - eexists. splits; auto.
    constructor.
    constructor.
    eauto with lngen.
Qed.

Lemma applyTy_subst_ordu : forall A X U B C,
    ApplyTy A (fty_StackArg B) C ->
    lc_typ U ->
    ordu B ->
    exists C', ApplyTy ([X ~~> U] A) ([X ~~> U] B) C' /\
           C' <: [X ~~> U] C.
Proof.
  intros A X U B C Happ Hlc Hord.
  forwards H: applyTyLs_applyTy.
  - constructor. exact Hord.
  - destruct H as [H _].
    rewrite <- H in Happ.
    forwards H': applyTyLs_subst; eauto.
    destruct H' as [C' [Hsubst ?] ].
    forwards Hapx: applyTyLs_approx.
    + exact Hsubst.
    + destruct Hapx as [C'' [? ?] ].
      eauto.
Qed.

(************************** previously stuck proofs ***************************)
(* (* B.15 (1) *) *)
(* Lemma applyty_andl_sub_1 : forall (A1 A2 B B1 B2 : typ) (V:Fty), *)
(*     TypeWF nil (A1&A2) -> isValFty V -> *)
(*     ApplyTy (A1&A2) V B -> ApplyTy A1 V B1 -> ApplyTy A2 V B2 -> B1&B2 <: B. *)

(* (* B.15 (2) *) *)
(* Lemma applyty_andl_sub_2 : forall (A1 A2 B B1 : typ) (V:Fty), *)
(*     TypeWF nil (A1&A2) -> isValFty V -> *)
(*     ApplyTy (A1&A2) V B -> ApplyTy A1 V B1 -> NApplyTy A2 V -> B1 <: B. *)

(* (* B.15 (3) *) *)
(* Lemma applyty_andl_sub_3 : forall (A1 A2 B B2 : typ) (V:Fty), *)
(*     TypeWF nil (A1&A2) -> isValFty V -> *)
(*     ApplyTy (A1&A2) V B -> NApplyTy A1 V -> ApplyTy A2 V B2 -> B2 <: B. *)

(* (* B.15 (4) *) *)
(* Lemma applyty_orl_sub : forall (A1 A2 B B1 B2 : typ) (V:Fty), *)
(*     ApplyTy (A1|A2) V B -> ApplyTy A1 V B1 -> ApplyTy A2 V B2 -> B <: B1 | B2. *)

  (* apply(A1, Fty) => A1' *)
  (* apply(A2, Fty) => A2' *)
  (* ------------------------------------------ *)
  (* apply(A1 & A2, Fty) => D /\ D <: A1'&A2' *)

Lemma applyty_and_1 : forall (A1 A2 B1 B2 : typ) (V:Fty),
    TypeWF nil (A1&A2) -> isValFty V ->
    ApplyTy A1 V B1 -> ApplyTy A2 V B2 -> exists B, ApplyTy (A1&A2) V B /\ B1&B2 <: B.
Proof with subst; try eassumption.
  introv WF Val App1 App2.
  forwards (?&Sub1&App1'): monotonicity_applyty_1 (A1&A2) App1. convert2asub. now eauto.
  forwards (?&Sub2&App2'): monotonicity_applyty_1 (A1&A2) App2. convert2asub. now eauto.
  forwards: applyty_unique App1' App2'...
  forwards: applyty_andl_sub_1 App1'...
  exists*.
Qed.

Lemma napplytyls_sound : forall A B,
    NApplyTyLs A B -> NApplyTy A B.
Proof with try eassumption; new_elia.
  introv H.
  indTypFtySize (size_typ A + size_Fty B).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty B). now eauto.
  - inverts~ H.
    all: forwards: IH; [eassumption | new_elia | eauto ].
    + clear H2. forwards: IH; [eassumption | new_elia | eauto ].
  - subst. inverts H; solve_false.
    + clear IH SizeInd H1. induction* H0.
    + clear IH SizeInd H1. induction* H0.
    + clear IH SizeInd H1. induction* H0.
    + clear IH SizeInd H1. eauto.
    + forwards~ [?|?]: applyty_total (t_arrow A0 A') (fty_StackArg x).
      destruct_conj.
      forwards: applyty_soundness_1 H.
      false. apply H6. convert2asub. auto_inv.
    + (* unfinished proof *)
Admitted.

Lemma applytyls_sound : forall A B C,
    ApplyTyLs A B C -> exists C' , ApplyTy A B C' /\ C' <: C.
Proof with try eassumption; new_elia.
  introv App.
  indTypFtySize (size_typ A + size_Fty B).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty B). now eauto.
  - (* easy cases *) admit.
    (* inverts App; solve_false. *)
    (* 1: exists; split*. *)
  - Local Ltac applyih IH := forwards: IH; [ | eassumption | |..].
    inverts* App.
    + exists. split~.
Admitted.
(*   - applyih IH... clear H1. *)
(*     applyih IH... destruct_conj. *)
(*     exists. split. eauto. admit. *)
(*   - applyih IH... clear H1. *)
(*     applyih IH... destruct_conj. *)
(*     (* new_splu case *) *)
(*     (* forwards (D1&D2&HDS) : nsplu2splu... forwards HDS' : splu2nsplu HDS. *) *)
(*     (* exists. split. eauto. admit. *) *)
(*     inverts H. (* 5 cases for all new_splu *) *)
(*     + exists. split. eauto. admit. *)
(*     + forwards (D1&D2&HDS) : nsplu2splu... *)
(*       exists. split. applys* ApplyTyUnionArg. *)


(*   intros; applys HL... now eauto. *)
(*   - forwards: IH; [ | eassumption | |..]; new_elia. intros; applys HL... now eauto. *)
(*   - forwards (D1&D2&HDS) : nsplu2splu; [eassumption | ..]; eauto. *)
(*     forwards HDS' : splu2nsplu HDS. *)
(*     eapply NApplyTyAltUnionArgL in H1... *)
(*     forwards [HN|HN]: HL HDS'... *)
(*     all: forwards*: IH HN... *)
(*     all: intros; applys HL... *)
(*   - forwards (D1&D2&HDS) : nsplu2splu; [eassumption | ..]; eauto. *)
(*     forwards HDS' : splu2nsplu HDS. *)
(*     eapply NApplyTyAltUnionArgR in H1... *)
(*     forwards [HN|HN]: HL HDS'... *)
(*     all: forwards*: IH HN... *)
(*     all: intros; applys HL... *)
(*   - forwards: IH H1... all: forwards: IH H2... *)
(*     1-3 : intros; applys HL... *)
(*     now eauto. *)
(* Qed. *)

Lemma typsubst_typ_applytyls : forall (A B C D : typ) X,
  ApplyTyLs A B C -> lc_typ D ->
  ApplyTyLs ([X ~~> D] A) ([X ~~> D] B) ([X ~~> D] C).
Admitted. (* I removed all ordu condition in ApplyTyAlt to make this trivially true *)

(* Lemma typsubst_typ_applyty : forall (A B C D : typ) X, *)
(*   ApplyTy A B C -> lc_typ D -> *)
(*   exists C', ApplyTy ([X ~~> D] A) ([X ~~> D] B) C' /\ C' <: ([X ~~> D] C). *)
(* Proof. *)
(*   introv App Lc. *)
(*   apply applytyalt_complete in App. *)
(*   forwards App': typsubst_typ_applytyalt X App Lc. *)
(*   forwards (?&?&?): applytyalt_sound App'. *)
(*   eauto. *)
(* Qed. *)


Lemma typsubst_applyty_ord : forall (A B C U : typ) X,
    ApplyTy A B C -> lc_typ U -> ordu B ->
    exists C', ApplyTy ([X ~~> U] A) ([X ~~> U] B) C' /\ C' <: [X ~~> U] C .
Proof with try eassumption.
  introv App Lc Ord.
  inverts App. 4: now solve_false.
  all: applys applytyls_sound.
  all: applys typsubst_typ_applytyls.
  all: eauto.
  - (* DOES NOT HAVE ApplyTyLs premises! *)
    (* applys ApplyTyLsUnion... *)
  Admitted.

(* At least we can prove after substitution the application must have a result (applicable): *)
(* Consider two special substitution: *)
(*   (1) use [X/Top] for all positive X and use [X/Bot] for all negative X *)
(*   (2) the reverse *)
(* A subst by (1) = a supertype of A *)
(* A subst by (2) = a subtype of A *)
(* Any normal substitution is between (1) and (2) *)
(* When A is applicable to B, by monotonicity we know A(1) is applicable to B(2). *)
(* --CANNOT PROCEED HERE-- *)

Lemma typsubst_applyty : forall (A B C U : typ) X,
    ApplyTy A B C -> lc_typ U ->
    exists C', ApplyTy ([X ~~> U] A) ([X ~~> U] B) C' /\ C' <: [X ~~> U] C.
Proof with try reflexivity; try eassumption.
  introv App Lc.
  inductions App.
  all: try forwards: IHApp...
  all: try forwards: IHApp1...
  all: try forwards: IHApp2...
  4: { destruct_conj.
       forwards App: ApplyTyUnionArg H0 H1. applys* SpU_or.
       forwards App': applyty_iso App.
       now applys* iso_refl.
       apply splu_iso in H. eapply typsubst_iso in H. simpl in H.
       now applys~ H. now auto. destruct_conj.
       exists. split... simpl. applys DSub_Trans H4.
       convert2asub. match_or...
  }
  all : applys typsubst_applyty_ord...
  all : try solve [inverts~ H].
  all : try solve [inverts~ H0].
Qed.
