(*******************************************************************************
*                                                                              *
*   Equivalence.v                                                              *
*   Xuejing Huang 2021                                                         *
*   Distributed under the terms of the GPL-v3 license                          *
*                                                                              *
*   This file is part of DistributingTypes.                                    *
*                                                                              *
*   DistributingTypes is free software: you can redistribute it and/or modify  *
*   it under the terms of the GNU General Public License as published by       *
*   the Free Software Foundation, either version 3 of the License, or          *
*   (at your option) any later version.                                        *
*                                                                              *
*   DistributingTypes is distributed in the hope that it will be useful,       *
*   but WITHOUT ANY WARRANTY; without even the implied warranty of             *
*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *
*   GNU General Public License for more details.                               *
*                                                                              *
*   You should have received a copy of the GNU General Public License          *
*   along with DistributingTypes.  If not, see <https://www.gnu.org/licenses/>.*
*                                                                              *
*******************************************************************************)


Require Import LibTactics.
Require Export Definitions.
Require Import Duotyping.

#[export] Hint Constructors declarative_subtyping osub : core.

(* Theorem 4.2 Equivalence of declarative systems *)
(* part 1 *)
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

(* Theorem 4.2 Equivalence of the declarative systems *)
(* part 2 *)
Theorem decl_subtyping_sound_duotyping : forall A B,
    declarative_subtyping A B -> osub A m_sub B /\ osub B m_super A.
Proof.
  introv Hs; split; induction Hs; eauto 4.
  + (* and *)
    apply OS_flip. simpl. applys~ OS_and.
  + (* or *)
    apply OS_flip. simpl. applys~ OS_and.
Qed.


(************************************************************)
(* Lemma 4.3 Equivalence of ordinary and splittable types *)
(* part 1 and part 2 -> *)
(* ord_sound: A circle only if A< *)
(* ordu_sound: A black_circle only if A> *)
Lemma ord_sound : forall A, single_ord A -> ord m_sub A
with ordu_sound : forall A, ordu A -> ord m_super A.
Proof.
  - introv H.
    induction H; eauto.

  - introv H.
    induction H; eauto.
Qed.

#[export] Hint Resolve ord_sound ordu_sound : core.

#[export] Hint Constructors single_ord ordu single_spl splu singlemode_sub : core.


(* Lemma 4.3 Equivalence of ordinary and splittable types *)
(* part 1 and part 2 <- *)
(* ord_complete_1: A circle if A< *)
(* ord_complete_2: A black_circle if A> *)
Lemma ord_complete : forall A m,
    ord m A -> ( m = m_sub /\ single_ord A ) \/ ( m = m_super /\ ordu A ).
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

#[export] Hint Resolve ord_complete_1 ord_complete_2 : core.

(* Lemma 4.3 Equivalence of ordinary and splittable types *)
(* part 3 and part 4 -> *)

(* split_sound: A is disjunctive splittable (Fig. 5) -> *)
(* A is splittable under subtyping mode (Fig. 8) *)

(* splitu_sound: A is conjunctive splittable (Fig. 5) -> *)
(* A is splittable under supertyping mode (Fig. 8) *)

Lemma split_sound : forall A B C,
    single_spl A B C -> spl m_sub A B C
with splitu_sound : forall A B C,
    splu A B C -> spl m_super A B C.
Proof.
  - introv H. clear split_sound.
    induction* H.

  - introv H. clear splitu_sound.
    induction* H.
Qed.

#[export] Hint Resolve split_sound splitu_sound : core.


(* Lemma 4.3 Equivalence of ordinary and splittable types *)
(* part 3 and part 4 <- *)

(* split_complete_1: A is splittable under subtyping mode (Fig. 8) -> *)
(* A is disjunctive splittable (Fig. 5) *)

(* split_complete_2: A is splittable under supertyping mode (Fig. 8) -> *)
(* A is conjunctive splittable (Fig. 5) *)

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


(************************************************************)
#[export] Hint Resolve split_complete_1 split_complete_2 : core.

#[export] Hint Constructors sub : core.
#[export] Hint Resolve sub_orl sub_orr sub_arrow sub_rev sub_rev2 : core.


Lemma algo_subtyping_sound_duotyping_no_dual_rule : forall A B,
    singlemode_sub A B -> sub A m_sub B /\ sub B m_super A.
Proof.
  introv Hs; split; induction Hs; eauto 4.
  + applys~ sub_arrow. applys~ sub_rev.
  + applys~ sub_arrow. applys~ sub_rev.
Qed.

(* Theorem 4.4 Equivalence of the algorithmic systems *)
(* part 1: algorithmic subtyping -> algorithmic duotyping *)
Theorem algo_subtyping_sound_duotyping : forall A B,
    singlemode_sub A B -> duo A m_sub B /\ duo B m_super A.
Proof.
  introv Hs.
  split; applys duotyping_dual_eqv_to_duotyping_no_dual;
    applys~ algo_subtyping_sound_duotyping_no_dual_rule.
Qed.


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


Require Import Subtyping.

Lemma algo_subtyping_complete_duotyping_no_dual_rule : forall A B m,
    sub A m B -> (m = m_sub /\ singlemode_sub A B) \/
                 (m = m_super /\ singlemode_sub B A).
Proof.
  introv Hs.
  induction Hs; destruct mode5;
    rewrite_duo2sub; eauto 4;
      right; split~.
  (* or *)
  - applys~ singlemode_sub_or H0.
  (* orr ordu B *)
  - applys~ s_sub_orl H1.
  - applys~ s_sub_orr H1.
Qed.

(* Theorem 4.4 Equivalence of the algorithmic systems *)
(* part 2: algorithmic duotyping -> algorithmic subtyping *)
Theorem algo_subtyping_complete_duotyping : forall A B m,
    duo A m B -> (m = m_sub /\ singlemode_sub A B) \/
                 (m = m_super /\ singlemode_sub B A).
Proof.
  introv Hs.
  applys algo_subtyping_complete_duotyping_no_dual_rule.
  applys~ duotyping_dual_eqv_to_duotyping_no_dual.
Qed.
