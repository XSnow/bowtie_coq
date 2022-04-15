Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export Dispatch.

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

 (*****************************************************************************)
Lemma napplytyls_sound : forall A B,
    NApplyTyLs A B -> NApplyTy A B.
Proof with try eassumption; new_elia.
  introv H.
  indTypFtySize (size_typ A + size_Fty B).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty B). admit.
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
      false. apply H5. convert2asub. auto_inv.
    +
Admitted.

Lemma applytyls_sound : forall A B C,
    ApplyTyLs A B C -> exists C' , ApplyTy A B C' /\ C' <: C.
Proof with try eassumption; new_elia.
  introv App.
  indTypFtySize (size_typ A + size_Fty B).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty B). admit.
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


(* (*     intros; applys HL... now eauto. *) *)
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
