Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Export syntax_ott.
Require Import Duotyping.

Hint Constructors declarative_subtyping osub : core.

Theorem decl_subtyping_sound_duotyping : forall A B,
    declarative_subtyping A B -> osub A m_sub B /\ osub B m_super A.
Proof.
  introv Hs; split; induction Hs; eauto 4.
  + (* and *)
    apply OS_flip. simpl. applys~ OS_and.
  + (* or *)
    apply OS_flip. simpl. applys~ OS_and.
Qed.

Theorem decl_subtyping_complete_duotyping : forall A B m,
    osub A m B -> (m = m_sub /\ declarative_subtyping A B) \/
                  (m = m_super /\ declarative_subtyping B A).
Proof.
  introv Hs.
  induction Hs; destruct mode5;
    try destruct IHHs as [(Heq&IHHs)|(Heq&IHHs)];
    try solve [inverts Heq1];
    try destruct IHHs1 as [(Heq1&IHHs1)|(Heq1&IHHs1)];
    try solve [inverts Heq1];
    try destruct IHHs2 as [(Heq2&IHHs2)|(Heq2&IHHs2)];
    try solve [inverts Heq2];
    eauto 4.
Qed.

Lemma ord_sound : forall A,
    single_ord A -> ord m_sub A
with ordu_sound : forall A,
    ( ordu A -> ord m_super A ).
Proof.
  - introv H.
    induction H; eauto.

  - introv H.
    induction H; eauto.
Qed.

Hint Resolve ord_sound ordu_sound : core.

Lemma split_sound : forall A B C,
    single_spl A B C -> spl m_sub A B C
with splitu_sound : forall A B C,
    splu A B C -> spl m_super A B C.
Proof.
  - introv H.
    induction* H.

  - introv H.
    induction* H.
Qed.

Hint Resolve split_sound splitu_sound : core.

Hint Constructors sub : core.
Hint Resolve sub_orl sub_orr sub_arrow sub_rev sub_rev2 : core.

Theorem algo_subtyping_sound_duotyping : forall A B,
    singlemode_sub A B -> sub A m_sub B /\ sub B m_super A.
Proof.
  introv Hs; split; induction Hs; eauto 4.
  + applys~ sub_arrow. applys~ sub_rev.
  + applys~ sub_arrow. applys~ sub_rev.
Qed.


(* algo: completeness *)
(* algorithmic duotyping -> algorithmic subtyping *)

Hint Constructors single_ord ordu single_spl splu singlemode_sub : core.

Lemma ord_complete : forall A m,
    ord m A -> ( m = m_sub /\ single_ord A )
                \/ ( m = m_super /\ ordu A ).
Proof.
  introv H.
  induction H; try destruct m; eauto;
    try destruct IHord1 as [(Heq1&IH1)|(Heq1&IH1)];
    try solve [inverts Heq1];
    try destruct IHord2 as [(Heq2&IH2)|(Heq2&IH2)];
    try solve [inverts Heq2]; eauto.
Qed.

Lemma ord_complete_1 : forall A,
    ord m_sub A -> single_ord A.
Proof.
  introv H.
  forwards~ [(?&?)|(?&?)]: ord_complete H.
  inverts H0.
Qed.


Lemma ord_complete_2 : forall A,
    ord m_super A -> ordu A.
Proof.
  introv H.
  forwards~ [(?&?)|(?&?)]: ord_complete H.
  inverts H0.
Qed.

Hint Resolve ord_complete_1 ord_complete_2 : core.

Lemma split_complete : forall A B C m,
    spl m A B C -> ( m = m_sub /\ single_spl A B C )
                    \/ ( m = m_super /\ splu A B C ).
Proof.
  introv H.
  induction H; try destruct m; simpl in *; eauto;
    try destruct IHspl as [(Heq&IH)|(Heq&IH)];
    try solve [inverts Heq]; eauto;
   try solve [ forwards* Hord: ord_complete H;
    try destruct Hord as [(Heq'&Hord)|(Heq'&Hord)];
    try solve [inverts Heq']; eauto ].
Qed.

(* alternative formulation *)
Lemma split_complete_1 : forall A B C,
    spl m_sub A B C -> single_spl A B C.
Proof.
  introv H.
  forwards~ [(?&?)|(?&?)]: split_complete H.
  inverts H0.
Qed.

Lemma split_complete_2: forall A B C,
    spl m_super A B C -> splu A B C.
Proof.
  introv H.
  forwards~ [(?&?)|(?&?)]: split_complete H.
  inverts H0.
Qed.

Hint Resolve split_complete_1 split_complete_2 : core.


Ltac rewrite_duo2sub :=
  repeat (
    match goal with
         | [ H: spl m_sub _ _ _ |- _ ] =>
           (forwards : split_complete_1 H; clear H)
         | [ H: spl m_super _ _ _ |- _ ] =>
           (forwards : split_complete_2 H; clear H)
         | [ H: ord m_sub _ |- _ ] =>
           (forwards : ord_complete_1 H; clear H)
         | [ H: ord m_super _ |- _ ] =>
           (forwards : ord_complete_2 H; clear H)
         | [ H: (_/\_)\/(_/\_) |- _ ] =>
           (destruct H as [(?&?)|(?&?)])
         | [ H: m_sub = m_sub |- _ ] =>
           (clear H)
         | [ H: m_super = m_super |- _ ] =>
           (clear H)
         | [ H: m_sub = m_super |- _ ] =>
           (inverts H)
         | [ H: m_super = m_sub |- _ ] =>
           (inverts H)
  end; simpl in *).
