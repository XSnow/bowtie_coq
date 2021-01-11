Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Duotyping.

Hint Constructors declarative_subtyping : core.

Theorem decl_subtyping_sound_duotyping : forall A B,
    declarative_subtyping A B -> osub A m_sub B /\ osub B m_super A.
Proof.
  introv Hs; split; induction Hs; [auto|apply OS_flip]; eauto 4.
  + (* or *)
    apply OS_flip. simpl.
    eauto.
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
    + forwards*: O_or m_sub A B.

  - introv H.
    induction H; eauto.
    + forwards*: O_or m_super A B.
Qed.

Hint Resolve ord_sound ordu_sound : core.

Lemma split_sound : forall A B C,
    single_spl A B C -> spl m_sub A B C
with splitu_sound : forall A B C,
    splu A B C -> spl m_super A B C.
Proof.
  - introv H.
    induction* H.
    + forwards*: Sp_orl m_sub A B.
    + forwards*: Sp_orr m_sub A B.

  - introv H.
    induction* H.
    + forwards*: Sp_orl m_super A B.
    + forwards*: Sp_orr m_super A B.
Qed.

Hint Resolve split_sound splitu_sound : core.

Theorem algo_subtyping_sound_duotyping : forall A B,
    singlemode_sub A B -> sub A m_sub B /\ sub B m_super A.
Proof.
  introv Hs; split; induction Hs; eauto 3.
  + forwards*: S_top.
  + apply rev. forwards*: S_top.
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

Hint Resolve ord_complete : core.

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

Hint Resolve split_complete : core.

Theorem algo_subtyping_complete_duotyping : forall A B m,
    sub A m B -> (m = m_sub /\ singlemode_sub A B) \/
                 (m = m_super /\ singlemode_sub B A).
Proof.
  introv Hs.
  induction Hs; destruct mode5;
    try destruct IHHs as [(Heq&IHHs)|(Heq&IHHs)];
    try solve [inverts Heq]; eauto 4;
  try forwards~ [(Heq'&Hspl)|(Heq'&Hspl)]: split_complete H;
    try solve [inverts Heq']; eauto 4;
    try destruct IHHs1 as [(Heq1&IHHs1)|(Heq1&IHHs1)];
    try solve [inverts Heq1];
    try destruct IHHs2 as [(Heq2&IHHs2)|(Heq2&IHHs2)];
    try solve [inverts Heq2];
    simpl in *;
    eauto 4;
  forwards* [(Heq3&Hord)|(Heq3&Hord)]: ord_complete H;
    try solve [inverts Heq3];
  forwards* [(Heq4&Hord')|(Heq4&Hord')]: ord_complete H0;
  try solve [inverts Heq4].
Qed.
