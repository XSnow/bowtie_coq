(*******************************************************************************
*                                                                              *
*   Duotyping.v                                                                *
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

(** This file is around four duotyping systems:
    1. The declarative one (fig. 7): osub A m B
    2. The algorithmic one (fig. 8): duo A m B
    3. The algorithmic duotyping with no dual rule: sub A m B
    4. The one has no ordinary-type conditions: lsub A m B

   During the development, most of the proof is done on (3).
   We show that the four systems are equivalent:
   (1) <-> (4) Lemma osub2lsub
   (4) <-> (3) Lemma lsub2sub
   (2) <-> (3) Lemma duotyping_dual_eqv_to_duotyping_no_dual
   Then we conclude:
   (2) <-> (1) Theorem duo2osub
 *)

Require Import LibTactics.
Require Import TypeSize.
Require Export Definitions.


#[export] Hint Constructors ord spl : core.

Lemma split_instance1: forall A B,
    spl m_sub (t_and A B) A B.
Proof.
  intros.
  lets: Sp_and m_sub A B.
  simpl in H.
  auto.
Qed.

Lemma split_instance2: forall A B,
    spl m_super (t_or A B) A B.
Proof.
  intros.
  lets: Sp_and m_super A B.
  simpl in H.
  auto.
Qed.

Lemma split_instance3: forall A A1 A2 B,
    spl m_sub A A1 A2 -> spl m_sub (t_or A B) (t_or A1 B) (t_or A2 B).
Proof.
  intros.
  lets: Sp_orl m_sub A B A1 A2.
  simpl in *.
  auto.
Qed.

Lemma split_instance4: forall A A1 A2 B,
    spl m_super A A1 A2 -> spl m_super (t_and A B) (t_and A1 B) (t_and A2 B).
Proof.
  intros.
  lets: Sp_orl m_super A B A1 A2.
  simpl in *.
  auto.
Qed.

Lemma split_instance5: forall A B B1 B2,
    ord m_sub A -> spl m_sub B B1 B2 -> spl m_sub (t_or A B) (t_or A B1) (t_or A B2).
Proof.
  intros.
  lets: Sp_orr m_sub A B B1 B2.
  simpl in *.
  auto.
Qed.

Lemma split_instance6: forall  A B B1 B2,
    ord m_super A -> spl m_super B B1 B2 -> spl m_super (t_and A B) (t_and A B1) (t_and A B2).
Proof.
  intros.
  lets: Sp_orr m_super A B B1 B2.
  simpl in *.
  auto.
Qed.

#[export] Hint Resolve split_instance1 split_instance2 split_instance3 split_instance4 split_instance5 split_instance6: core.

Lemma sub_instance1: forall A,
    sub t_bot m_sub A.
Proof.
  intros.
  lets: S_bot m_sub.
  simpl in *. eauto.
Qed.

Lemma sub_instance2: forall A,
    sub A m_sub t_top.
Proof.
  intros.
  lets: S_top m_sub.
  simpl in *. eauto.
Qed.

Lemma sub_instance3: forall A,
    sub t_top m_super A.
Proof.
  intros.
  lets: S_bot m_super.
  simpl in *. eauto.
Qed.

Lemma sub_instance4: forall A,
    sub A m_super t_bot.
Proof.
  intros.
  lets: S_top m_super.
  simpl in *. eauto.
Qed.

#[export] Hint Resolve sub_instance1 sub_instance2 sub_instance3 sub_instance4 : core.

(* Lemma 4.7 Types are Either Ordinary or Splittable *)
(* part 1 *)
Lemma ord_or_split: forall m A,
    ord m A \/ exists B C, spl m A B C.
Proof with (eauto; intros).
  intros. gen m. induction* A...
  - (* arrow *)
    destruct m...
    + lets [?|(?&?&?)]: IHA2...
      (* ord A2 in A1->A2 *)
      lets* [?|(?&?&?)]: IHA1...
  - (* and *)
    destruct m...
    + lets [?|(?&?&?)]: IHA1 m_super;
        lets [?|(?&?&?)]: IHA2 m_super...
      left. constructor...
  - (* or *)
    destruct m...
    + lets [?|(?&?&?)]: IHA1 m_sub;
        lets [?|(?&?&?)]: IHA2 m_sub...
      left. constructor*...
Qed.

Lemma choose_false_int: forall m A B,
    choose m A B = t_int -> False.
Proof.
  intros.
  destruct m; destruct A; destruct B; simpl in H; inverts H.
Qed.

Lemma choose_false_top: forall m A B,
    choose m A B = t_top -> False.
Proof.
  intros.
  destruct m; destruct A; destruct B; simpl in H; inverts H.
Qed.

Lemma choose_false_bot: forall m A B,
    choose m A B = t_bot -> False.
Proof.
  intros.

  destruct m; destruct A; destruct B; simpl in H; inverts H.
Qed.

Lemma choose_false_arrow: forall m A B C D,
    choose m A B = t_arrow C D -> False.
Proof.
  intros.
  destruct m; destruct A; destruct B; simpl in H; inverts H.
Qed.

Lemma choose_typebymode_false: forall m1 m2 A B,
    typbymode m1 = choose m2 A B -> False.
Proof.
  intros.
  destruct m1; destruct m2; inverts H.
Qed.

Lemma choose_and_sub: forall m A B C D,
    choose m A B = t_and C D -> m = m_sub.
Proof.
  intros.
  destruct m; inverts* H.
Qed.

Lemma choose_or_super: forall m A B C D,
    choose m A B = t_or C D -> m = m_super.
Proof.
  intros.
  destruct m; inverts* H.
Qed.

Lemma and_or_mismatch: forall A B C D,
    t_and A B = t_or C D -> False.
Proof.
  intros.
  inverts H.
Qed.

Lemma ord_sub_and_false : forall A B,
    ord m_sub (t_and A B) -> False.
Proof.
  intros.
  inverts H.
Qed.

Lemma ord_super_or_false : forall A B,
    ord m_super (t_or A B) -> False.
Proof.
  intros.
  inverts H.
Qed.

Lemma ord_both_and_false : forall m A B,
    ord m (t_and A B) -> ord (flipmode m) (t_and A B) -> False.
Proof.
  introv H1 H2.
  destruct m; inverts H1; inverts H2.
Qed.

Lemma ord_both_or_false : forall m A B,
    ord m (t_or A B) -> ord (flipmode m) (t_or A B) -> False.
Proof.
  introv H1 H2.
  destruct m; inverts H1; inverts H2.
Qed.

#[export] Hint Resolve choose_false_int choose_false_top choose_false_bot
     choose_false_arrow choose_and_sub choose_or_super and_or_mismatch
     choose_typebymode_false ord_sub_and_false ord_super_or_false
     ord_both_and_false ord_both_or_false : falseHd.

(* Lemma 4.7 Types are Either Ordinary or Splittable *)
(* part 2 *)
Lemma split_ord_false : forall m A B C,
    spl m A B C -> ord m A -> False.
Proof.
  introv. gen m B C.
  induction A; intros m B C s o;
    try solve [inverts* s];
    try solve [inverts* o];
    destruct m;
    inverts o;
    inverts* s.
Qed.

Lemma split_int : forall m A B,
    spl m t_int A B -> False.
Proof.
  intros. destruct m; inverts H.
Qed.

Lemma split_top : forall m A B,
    spl m t_top A B -> False.
Proof.
  intros. destruct m; inverts H.
Qed.

Lemma split_bot : forall m A B,
    spl m t_bot A B -> False.
Proof.
  intros. destruct m; inverts H.
Qed.

Lemma split_typbymode : forall m A B,
    spl m (typbymode m) A B -> False.
Proof.
  intros. destruct m; inverts H.
Qed.

Lemma split_typbyflippedmode : forall m A B,
    spl m (typbymode (flipmode m)) A B -> False.
Proof.
  intros. destruct m; inverts H.
Qed.

#[export] Hint Resolve split_ord_false split_int split_top split_bot split_typbymode split_typbyflippedmode: falseHd.


Lemma split_keep_ord_f_l : forall m A B C,
    ord (flipmode m) A -> spl m A B C -> ord (flipmode m) B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma split_keep_ord_f_r : forall m A B C,
    ord (flipmode m) A -> spl m A B C -> ord (flipmode m) C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma split_keep_ord_l : forall m A B C,
    ord m A -> spl (flipmode m) A B C -> ord m B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma split_keep_ord_r : forall m A B C,
    ord m A -> spl (flipmode m) A B C -> ord m C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

#[export] Hint Resolve split_keep_ord_l split_keep_ord_r split_keep_ord_f_l split_keep_ord_f_r : core.


(* About Flipping *)
Lemma flip_eqv_false : forall m,
    m = flipmode m -> False.
Proof.
  intros.
  destruct m; inverts H.
Qed.

Lemma flip_eqv_false_2 : forall m,
    flipmode m = m -> False.
Proof.
  intros.
  destruct m; inverts H.
Qed.

#[export] Hint Immediate flip_eqv_false flip_eqv_false_2 : falseHd.

Ltac solve_false := try intro; try solve [false; eauto 3 with falseHd].

Lemma flip_rev : forall m1 m2,
    m1 = flipmode m2 -> m2 = flipmode m1.
Proof.
  intros.
  destruct m2; subst; eauto.
Qed.

(* flip m and remember it as m' *)
Ltac flip m m' :=
  remember (flipmode m) as m' eqn:Heqm'; apply flip_rev in Heqm'; subst.

(* for simplification and unification purpose *)
Lemma flip_flip : forall m,
    flipmode (flipmode m) = m.
Proof.
  intros. destruct~ m.
Qed.

Lemma cal_top : typbymode m_sub = t_top.
Proof.
  intros. eauto.
Qed.

Lemma cal_bot : typbymode m_super = t_bot.
Proof.
  intros. eauto.
Qed.

Hint Rewrite flip_flip : core.


(* Splitting types is deterministic *)
Lemma choose_unique : forall m1 m2 A B C D,
    choose m1 A B = choose m2 C D -> m1 = m2 /\ A = C /\ B = D.
Proof.
  intros.
  destruct m1; destruct m2; inverts* H.
Qed.

Lemma split_choose : forall m A B C D,
    spl m (choose m A B) C D -> A = C /\ B = D.
Proof.
  intros.
  destruct m; simpl in *; inverts* H.
Qed.

Ltac choose_unify :=
  match goal with
         | [ H1: choose _ _ _ = choose _ _ _ |- _ ] =>
           (forwards (?&?&?): choose_unique H1; clear H1)
         | [ H1: spl ?m (choose ?m _ _)  _ _ |- _ ] =>
           (forwards (?&?): split_choose H1; clear H1)
  end;
  subst~.

(********************************************)
(*                                          *)
(*          Lemma split_unique              *)
(*                                          *)
(********************************************)
Ltac split_unique_autoIH :=
  match goal with
  | [ IH: forall A, size_typ A < _ -> _, Hsp: spl ?m ?T _  _, Hsp2: spl ?m ?T _  _ |- _ ] =>
    (forwards (?&?): IH Hsp Hsp2; elia; subst~)
end.

(* Lemma 4.8 Determinism of type splitting *)
Lemma split_unique : forall m T A1 A2 B1 B2,
    spl m T A1 B1 -> spl m T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (solve_false; auto).
  introv. gen m.
  indTypSize (size_typ T).
  inverts H; inverts H0;
    try choose_unify; solve_false;
    try split_unique_autoIH;
    try choose_unify.
Qed.


(********************************************)
(*                                          *)
(*             Ltac auto_unify              *)
(*                                          *)
(*  extends choose_unify                    *)
(*  solve_false at the end                  *)
(*                                          *)
(********************************************)
Ltac auto_unify :=
  simpl in *;
  try repeat choose_unify;
  try repeat match goal with
         | [ H1: spl ?m ?A  _ _ , H2: spl ?m ?A _ _ |- _ ] =>
           (forwards (?&?): split_unique H1 H2;
            subst; clear H2)
         end;
  try rewrite flip_flip in *;
  solve_false;
  try solve [
         match goal with
         | [ m : mode |- _ ] =>
           (destruct m; eauto 2)
         end ].



(*****************************************************************************)
Inductive part : mode -> typ -> typ -> Prop :=
| P_refl  : forall m A, part m A A
| P_spl   : forall m A B C B', spl m A B C -> part m B B' -> part m A B'
| P_spr   : forall m A B C C', spl m A B C -> part m C C' -> part m A C'
.

#[export] Hint Constructors part : core.


Lemma part_spl : forall m A B B1 B2,
    part m A B -> spl m B B1 B2 -> part m A B1 /\ part m A B2.
Proof.
  introv Hp Hspl.
  induction Hp; split*.
Qed.

#[export] Hint Resolve part_spl : core.


Ltac sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- sub ?A ?m ?B ] =>
  (forwards (IH1&IH2): IH A B; try eassumption; elia)
end.


Lemma sub_part : forall m A B,
    (part m A B -> sub A m B)
    /\ (ord m A -> ord m B -> part (flipmode m) B A -> sub A m B).
Proof with (try eassumption; try sub_part_autoIH; eauto 4).
  introv. gen m.
  indTypSize (size_typ A + size_typ B).
  split.

  --
  introv Hp.
  lets [Hi|(?&?&Hi)]: ord_or_split m B.
  - (* ord B *)
    inverts Hp.
    + lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) B.
      * destruct B; auto_unify.
        ** econstructor.
        **(* arrow *)
          constructor...
          destruct m; auto_unify; auto.
          destruct m; auto_unify; auto.
      * applys~ S_or Hu...
    + applys S_andl...
    + applys S_andr...
  - (* spl B *)
    lets~ (?&?): part_spl Hp Hi.
    applys S_and Hi...

    --
    introv Ho1 Ho2 Hp.
    lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
    + inverts Hp; auto_unify.
      * (* ord B *)
      destruct A; auto_unify.
      ** econstructor.
      ** (* arrow case, non-ord types involved *)
        constructor...
        destruct m; auto_unify; auto.
        destruct m; auto_unify; auto.
      * applys* S_orl...
      * applys* S_orr...
    +
      lets~ (?&?): part_spl Hp Hu.
      applys* S_or...
Qed.

(* Theorem 4.6 reflexivity of the algorithmic duotyping *)
Theorem sub_refl : forall A m, sub A m A.
Proof.
  introv.
  pose proof (sub_part m A A).
  destruct* H.
Qed.

Lemma sub_part1 : forall m A B,
    part m A B -> sub A m B.
Proof.
  introv.
  pose proof (sub_part m A B).
  destruct* H.
Qed.

Lemma sub_part2 : forall m A B,
    ord m A -> ord m B -> part (flipmode m) B A -> sub A m B.
Proof.
  introv.
  pose proof (sub_part m A B).
  destruct* H.
Qed.

#[export] Hint Resolve sub_refl sub_part1 sub_part2 : core.

(********************************************)
(*                                          *)
(* Lemma 4.9 Soundness of Splitting         *)
(*                                          *)
(********************************************)
Lemma split_iso: forall m A B C,
    spl m A B C -> sub A m (choose m B C) /\ sub (choose m B C) m A.
Proof.
  introv H.
  split; applys* S_and.
Qed.


#[export] Hint Constructors lsub : core.

Lemma rev : forall A m B,
    lsub B (flipmode m) A <-> lsub A m B.
Proof.
  split; introv H.

  inductions H;
    try solve [constructor*];
    try solve [auto_unify; eauto].

  flip m m'.
  inductions H;
    try solve [constructor*];
    try solve [auto_unify; eauto].
Qed.


Notation "A <: B" := (lsub A m_sub B) (at level 80, right associativity).
Notation "A :> B" := (lsub A m_super B) (at level 80, right associativity).

Lemma rev2 : forall A B,
    A <: B <-> B :> A.
Proof.
  split; intro H;
    apply rev; simpl; auto.
Qed.

#[export] Hint Immediate rev rev2 : core.


(* Lemma 4.1 Inversions on splittable types *)
(* part 1 *)
Lemma rule_and_inv : forall m A B B1 B2,
    sub A m B -> spl m B B1 B2 -> sub A m B1 /\ sub A m B2.
Proof.
  intros.
  induction H; auto_unify.
  - destruct mode5; auto_unify.
Qed.

(* Lemma 4.1 Inversions on splittable types *)
(* part 2 *)
Lemma rule_andlr_inv : forall m A B A1 A2,
     sub A m B -> spl m A A1 A2 -> ord m B -> sub A1 m B \/ sub A2 m B.
Proof with (auto_unify; try eassumption; elia).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; auto_unify; auto.
  (* arrow *)
  inverts Hspl...
Qed.

(* Lemma 4.1 Inversions on splittable types *)
(* part 3 *)
Lemma rule_or_inv : forall m A A1 A2 B,
    sub A m B -> spl (flipmode m) A A1 A2 -> sub A1 m B /\ sub A2 m B.
Proof with (auto_unify; try eassumption; elia).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: ord_or_split m B.
  - inverts Hsub; auto_unify; auto.
    + inverts Hspl...
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards (?&?): IH (choose (flipmode m) A0 A2) A0 A2 B...
        split~. applys* S_andl.
      * forwards (?&?): IH (choose (flipmode m) A1 B1) A1 B1 B...
        split~. applys* S_andl.
      * forwards* (?&?): IH H2 B...
        split; applys* S_andl.
      * split; applys* S_andl.
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards (?&?): IH H1...
        split~. applys* S_andr.
      * forwards (?&?): IH H1...
        split~. applys* S_andr.
      * split; applys* S_andr.
      * forwards (?&?): IH H1...
        split; applys* S_andr.
  - forwards (?&?): rule_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...
    split; applys~ S_and Hi.
Qed.

(* Lemma 4.1 Inversions on splittable types *)
(* part 4 *)
Lemma rule_orlr_inv : forall m A B B1 B2,
     sub A m B -> ord (flipmode m) A -> spl (flipmode m) B B1 B2 -> sub A m B1 \/ sub A m B2.
Proof with (auto_unify; try eassumption; elia).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; try solve [destruct m; auto_unify]...
  + (* double split *)
    inverts Hspl; inverts H...
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
      left. applys* S_and.
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
      right. applys* S_and.
    * forwards [?|?]: IH H2...
      left. applys* S_and.
      right. applys* S_and.
    * forwards [?|?]: IH H1 H3...
      left. applys* S_and.
      right. applys* S_and.
  + forwards [?|?]: IH H1...
    left. applys S_andl...
    right. applys S_andl...
  + forwards [?|?]: IH H1...
    left. applys S_andr...
    right. applys S_andr...
Qed.

(********************************************)
(*                                          *)
(*          Ltac auto_inv                   *)
(*                                          *)
(*  extends choose_unify                    *)
(*  solve_false at the end                  *)
(*                                          *)
(********************************************)
Ltac auto_inv :=
  repeat try match goal with
         | [ H1: sub ?A ?m ?B, H2: spl ?m ?B _ _ |- _ ] =>
           try (forwards~ (?&?): rule_and_inv H1 H2; clear H1)
         | [ H1: sub ?A ?m (choose ?m _ _) |- _ ] =>
           try (forwards~ (?&?): rule_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ord ?m ?B, H1: sub ?A ?m ?B, H2: spl ?m ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: rule_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ord ?m ?B, H1: sub (choose ?m _ _) ?m ?B |- _ ] =>
           try (forwards~ [?|?]: rule_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: sub ?A ?m ?B, H2: spl (flipmode ?m) ?A _ _ |- _ ] =>
           try (forwards~ (?&?): rule_or_inv H1 H2; clear H1)
         | [ H1: sub ?A ?m ?B, H2: spl _ ?A _ _ |- _ ] =>
           try (forwards~ (?&?): rule_or_inv H1 H2; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ord (flipmode ?m) ?A, H1: sub ?A ?m ?B, H2: spl (flipmode ?m) ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: rule_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ord ?m' ?A, H1: sub ?A ?m ?B, H2: spl ?m' ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: rule_orlr_inv H1 Hord H2; clear H1)
      end.


Lemma sub_orl : forall m A B B1 B2,
    spl (flipmode m) B B1 B2 -> sub A m B1 -> sub A m B.
Proof.
  introv Hspl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ord_or_split m A.
  lets [Hi'|(?&?&Hi')]: ord_or_split m B.
  lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
  - applys~ S_orl Hspl.
  - applys S_or; try eassumption. (* relys on rule_or_inv *)
    inverts~ Hs.
    Abort.


Lemma sub_or : forall m A A1 A2 B,
    spl (flipmode m) A A1 A2 -> sub A1 m B -> sub A2 m B -> sub A m B.
Proof with (auto_unify; try eassumption; auto_inv; elia).
  introv Hspl Hs1 Hs2.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ord_or_split m B...
  lets [Hi'|(?&?&Hi')]: ord_or_split m A...
  - applys S_or...
  - (* double split A *)
    inverts keep Hspl; inverts keep Hi'...
    + applys* S_andl... applys IH...
    + applys* S_andr... applys IH...
    + applys* S_andl... applys IH...
    + applys* S_andr... applys IH...
    + applys* S_andl... applys IH...
    + applys* S_andr...
    + applys* S_andr...
    + applys* S_andr...
    + applys* S_andl...
    + applys* S_andl...
    + applys* S_andl...
    + applys* S_andr... applys IH...
  - applys S_and Hi...
    applys IH... applys IH...
Qed.

Ltac trans_autoIH :=
  match goal with
  | [ IH: forall A B C : typ, _ , H1: sub ?A ?m ?B , H2: sub ?B ?m ?C |- sub ?A ?m ?C ] =>
    (applys~ IH H1 H2; elia; auto)
  | [ IH: forall A B C : typ, _ , H1: sub ?A ?m ?B  |- sub ?A ?m ?C ] =>
    (applys~ IH H1; elia; constructor~)
  | [ IH: forall A B C : typ, _ , H2: sub ?B ?m ?C |- sub ?A ?m ?C ] =>
    (applys~ IH H2; elia; constructor~)
  end.

(* Theorem 4.10 Transitivity of the algorithmic duotyping *)
Lemma trans : forall m A B C, sub A m B -> sub B m C -> sub A m C.
Proof with (auto_unify; try eassumption; auto_inv; try solve trans_autoIH).
  introv s1 s2. gen m.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets [Hi|(?&?&Hi)]: ord_or_split m C...
  - lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A...
    + lets [Hi'|(?&?&Hi')]: ord_or_split m B...
      lets [Hu'|(?&?&Hu')]: ord_or_split (flipmode m) B...
      lets [Hi''|(?&?&Hi'')]: ord_or_split m A...
      * (* double ord A B *)
        inverts s1; auto_unify.
        ** (* top *)
          inverts~ s2; try solve [destruct m; auto_unify]...
          *** applys~ S_orl H2...
          *** applys~ S_orr H2...
        ** (* arrow *)
          inverts~ s2; try solve [destruct m; auto_unify]...
          *** applys~ S_arr...
          *** applys~ S_orl H6...
          *** applys~ S_orr H6...
      * applys S_andl...
      * applys S_andr...
    + lets [Hi'|(?&?&Hi')]: ord_or_split m A...
      * applys S_or Hu...
      * assert (sub x m C)...
        assert (sub x0 m C)...
        applys sub_or...
  - applys S_and Hi...
Qed.

#[export] Hint Immediate trans : core.

#[export] Hint Resolve sub_or : core.

Lemma sub_arrow : forall m A1 A2 B1 B2,
    sub A1 (flipmode m) B1 -> sub A2 m B2 -> sub (t_arrow A1 A2) m (t_arrow B1 B2).
Proof with (auto_unify; try eassumption; auto_inv; elia).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m (t_arrow A1 A2).
  lets [Hi2|(?&?&Hi2)]: ord_or_split m (t_arrow B1 B2).
  lets [Hu1|(?&?&Hu1)]: ord_or_split (flipmode m) (t_arrow A1 A2).
  lets [Hu2|(?&?&Hu2)]: ord_or_split (flipmode m) (t_arrow B1 B2).
  - applys~ S_arr; destruct~ m.
  - destruct m... inverts Hu2.
    + forwards [?|?]: rule_orlr_inv Hs2 H1. inverts* Hu1.
      applys S_orl; try eassumption. simpl. eauto. applys~ IH. elia.
      applys S_orr; try eassumption. simpl. eauto. applys~ IH. elia.
    + forwards [?|?]: rule_orlr_inv Hs1 H2. inverts* Hu1.
      applys S_orl; try eassumption. simpl. eauto. applys~ IH. elia.
      applys S_orr; try eassumption. simpl. eauto. applys~ IH. elia.
  - destruct m... inverts Hu1.
    + forwards (?&?): rule_or_inv Hs2 H1.
      applys S_or; try eassumption. simpl; eauto.
      applys~ IH; elia. applys~ IH; elia.
    + forwards (?&?): rule_or_inv Hs1 H2.
      applys S_or; try eassumption. simpl; eauto.
      applys~ IH; elia. applys~ IH; elia.
  - destruct m... inverts Hi2.
    + forwards (?&?): rule_and_inv Hs2 H1.
      applys S_and; try eassumption. simpl; eauto.
      applys~ IH; elia. applys~ IH; elia.
    + forwards (?&?): rule_and_inv Hs1 H2.
      applys S_and; try eassumption. simpl; eauto.
      applys~ IH; elia. applys~ IH; elia.
  - destruct m... inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow B1 B2).
      * forwards~ [?|?]: rule_andlr_inv Hs2 H1. inverts~ Hi2.
        applys S_andl; try eassumption. simpl. eauto. applys~ IH. elia.
        applys S_andr; try eassumption. simpl. eauto. applys~ IH. elia.
      * inverts Hi2.
        ** forwards (?&?): rule_and_inv Hs2 H2.
           applys S_and; try eassumption. simpl; eauto.
           applys~ IH; elia. applys~ IH; elia.
        ** forwards (?&?): rule_and_inv Hs1 H3.
           applys S_and; try eassumption. simpl; eauto.
           applys~ IH; elia. applys~ IH; elia.
    + lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow B1 B2).
      * forwards~ [?|?]: rule_andlr_inv Hs1 H2. inverts~ Hi2.
        applys S_andl; try eassumption. simpl. eauto. applys~ IH. elia.
        applys S_andr; try eassumption. simpl. eauto. applys~ IH. elia.
      * inverts Hi2.
        ** forwards (?&?): rule_and_inv Hs2 H3.
           applys S_and; try eassumption. simpl; eauto.
           applys~ IH; elia. applys~ IH; elia.
        ** forwards (?&?): rule_and_inv Hs1 H4.
           applys S_and; try eassumption. simpl; eauto.
           applys~ IH; elia. applys~ IH; elia.
Qed.

Lemma sub_orl : forall m A B B1 B2,
    spl (flipmode m) B B1 B2 -> sub A m B1 -> sub A m B.
Proof.
  introv Hspl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ord_or_split m B.
  lets [Hi'|(?&?&Hi')]: ord_or_split m A.
  lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
  - applys~ S_orl Hspl.
  - applys~ sub_or Hu; applys IH Hspl; elia; applys trans Hs; applys* sub_part2.
  - forwards~ [?|?]: rule_andlr_inv Hs Hi'. eauto.
      applys~ S_andl Hi'. applys~ IH Hspl. elia.
      applys~ S_andr Hi'. applys~ IH Hspl. elia.
  - inverts Hspl; inverts Hi; auto_unify.
    + applys S_and; eauto.
      applys IH; elia. 2: {eauto. } applys* trans Hs.
      applys IH; elia. 2: {eauto. } applys* trans Hs.
    + applys S_and; eauto.
      applys IH; elia. 2: {eauto. } applys* trans Hs.
      applys IH; elia. 2: {eauto. } applys* trans Hs.
    + auto_inv. applys S_and; eauto.
      applys~ IH H; elia.
    + auto_inv. applys S_and; eauto.
      applys~ IH H0; elia.
Qed.

Lemma sub_orr : forall m A B B1 B2,
    spl (flipmode m) B B1 B2 -> sub A m B2 -> sub A m B.
Proof.
  introv Hspl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ord_or_split m B.
  lets [Hi'|(?&?&Hi')]: ord_or_split m A.
  lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
  - applys~ S_orr Hspl.
  - applys~ sub_or Hu; applys IH Hspl; elia; applys trans Hs; applys* sub_part2.
  - forwards~ [?|?]: rule_andlr_inv Hs Hi'. eauto.
      applys~ S_andl Hi'. applys~ IH Hspl. elia.
      applys~ S_andr Hi'. applys~ IH Hspl. elia.
  - inverts Hspl; inverts Hi; auto_unify.
    + applys S_and; eauto.
      applys IH; elia. eauto. applys* trans Hs.
      applys IH; elia. eauto. applys* trans Hs.
    + applys S_and; eauto.
      applys IH; elia. eauto. applys* trans Hs.
      applys IH; elia. eauto. applys* trans Hs.
    + auto_inv. applys S_and; eauto.
      applys~ IH H; elia.
    + auto_inv. applys S_and; eauto.
      applys~ IH H0; elia.
Qed.



(********************************************)
Lemma lsub2sub : forall m A B,
    lsub A m B <-> sub A m B.
Proof.
  split.

  +
  introv Hs.
  induction Hs;
    try solve [econstructor; eassumption].
  - applys* sub_arrow.
  - applys trans IHHs. applys* sub_part1.
  - applys trans IHHs. applys* sub_part1.
  - applys* sub_or.
  - applys* sub_orl.
  - applys* sub_orr.

  +
  introv Hs.
  induction Hs; try econstructor; eassumption.
Qed.

Lemma lsub_refl : forall m A,
    lsub A m A.
Proof.
  intros. applys* lsub2sub.
Qed.

Lemma lsub_trans : forall m A B C,
    lsub A m B -> lsub B m C -> lsub A m C.
Proof.
  intros. applys lsub2sub. apply lsub2sub in H. apply lsub2sub in H0.
  eauto.
Qed.

#[export] Hint Resolve lsub_refl lsub_trans : core.

(* prove that the dual rule is derivable in system (3) *)
Lemma sub_rev : forall A m B,
    sub B (flipmode m) A <-> sub A m B.
Proof.
  split; intro H;
    apply lsub2sub; apply lsub2sub in H; apply rev; simpl; auto.
Qed.

Lemma sub_rev2 : forall A B,
    sub A m_sub B <-> sub B m_super A.
Proof.
  split; intro H;
    apply lsub2sub; apply lsub2sub in H; apply rev; simpl; auto.
Qed.

#[export] Hint Resolve sub_rev sub_rev2 : core.

Lemma distArrU: forall A B C,
    sub (t_and (t_arrow A C) (t_arrow B C)) m_sub (t_arrow (t_or A B) C).
Proof with (auto_unify; try eassumption).
  introv.
  indTypSize (size_typ C).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m_sub C.
  - applys* S_and.
  - (* split C x x0 *)
    forwards Hs1: IH A B x. elia.
    forwards Hs2: IH A B x0. elia.
    applys S_and. eauto.
    + applys trans Hs1. applys* S_and.
    + applys trans Hs2. applys* S_and.
Qed.


Lemma symm_and: forall m A B,
    sub (choose m A B) m (choose m B A).
Proof.
  introv.
  applys* S_and.
Qed.

Lemma symm_or: forall m A B,
    sub (choose (flipmode m) A B) m (choose (flipmode m) B A).
Proof.
  introv.
  applys* sub_or. applys* sub_orr. applys* sub_orl.
Qed.

#[export] Hint Resolve symm_and symm_or : core.

(* declarative subtyping equivalence *)
#[export] Hint Constructors osub : core.

Lemma osub_spl: forall m A B C,
    spl m A B C -> osub A m B /\ osub A m C.
Proof with intuition.
  introv H.
    induction H; try intuition;
      applys OS_flip; flip m m'; applys* OS_and.
Qed.

Lemma osub_symm_and: forall m A B,
    osub (choose m A B) m (choose m B A).
Proof.
  introv.
  applys* OS_and.
Qed.

Lemma osub_symm_or: forall m A B,
    osub (choose (flipmode m) A B) m (choose (flipmode m) B A).
Proof.
  introv.
  apply OS_flip. applys* osub_symm_and.
Qed.

Lemma osub_distAnd: forall m A B1 B2,
    osub (choose m (choose (flipmode m) B1 B2) A) m (choose (flipmode m) (choose m B1 A) (choose m B2 A)).
Proof with eauto.
  introv.
  applys OS_flip.
  flip m m'.
  applys OS_distOr.
Qed.

#[export] Hint Resolve osub_spl osub_symm_and osub_symm_or osub_distAnd : core.


Lemma osub_spl2: forall m A B C,
    spl m A B C -> osub (choose m B C) m A.
Proof with intuition.
  introv H.
    induction H.
  - applys OS_refl.
  - eauto.
  - forwards: osub_spl H0. eauto.
  - applys OS_trans (choose (flipmode m) (choose m A1 A2) B).
    applys OS_distOr. apply OS_flip. flip m m'. eauto.
  - applys OS_trans (choose (flipmode m) B A)...
    applys OS_trans (choose m (choose (flipmode m) B1 A) (choose (flipmode m) B2 A))...
    applys OS_and.
    applys OS_trans (choose (flipmode m) A B1)...
    applys OS_trans (choose (flipmode m) A B2)...
    applys OS_trans (choose (flipmode m) (choose m B1 B2) A);
    apply OS_flip; flip m m'; eauto.
Qed.


Theorem osub2lsub: forall A m B,
    osub A m B <-> lsub A m B.
Proof with (simpl in *; try eassumption).
  split; introv H.
  - induction H; try solve [constructor~].
    + applys lsub_refl.
    + applys* lsub_trans.
    + applys* LS_and.
    + applys* LS_andl.
    + applys* LS_andr.
    + apply lsub2sub. forwards* (?&?): split_iso m_sub (t_arrow A (t_and B C)).
      destruct mode5; simpl in *; eauto.
      applys~ sub_rev2.
    + apply lsub2sub. destruct~ mode5.
      * applys~ distArrU.
      * applys lsub2sub. applys* LS_or.
    + forwards: Sp_orl mode5 (choose mode5 A1 A2) B A1 A2; eauto.
    + applys~ rev.
  - induction~ H.
    + (* and *)
      applys OS_trans (choose mode5 B1 B2)...
      applys OS_and...
      applys osub_spl2 H.
    + (* andl *)
      forwards (?&?): osub_spl H. applys OS_trans H1...
    + (* andr *)
      forwards (?&?): osub_spl H. applys OS_trans H2...
    +  (* or *)
      applys OS_flip. flip mode5 m'. apply OS_flip in IHlsub1. apply OS_flip in IHlsub2.
      applys OS_trans (choose m' A1 A2)...
      applys OS_and...
      applys osub_spl2 H.
    + (* orl *)
      applys OS_trans IHlsub.
      applys OS_flip. flip mode5 m'. applys osub_spl H.
    + (* orr *)
      applys OS_trans IHlsub.
      applys OS_flip. flip mode5 m'. applys osub_spl H.
Qed.

Lemma arrow_inv : forall A B C D,
   sub (t_arrow A B) m_sub (t_arrow C D) -> (sub A m_super C) /\ (sub B m_sub D).
Proof with (simpl in *; auto_unify; jauto).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m_sub (t_arrow A B).
  - inverts s...
  - inverts keep Hi1;
      forwards~ [?|?]: rule_andlr_inv s Hi1;
      forwards(IH1&IH2): IH H; try solve [elia];
        split; try eassumption; inverts~ Hi2.
    + applys~ S_andl H1.
    + applys~ S_andr H1.
    + applys~ S_andl H2.
    + applys~ S_andr H2.
  - (* uses and_inv_1 and_inv_2 *)
    forwards (?&?): rule_and_inv s Hi2.
    inverts keep Hi2;
      forwards (?&?): IH H; try solve [elia];
        forwards (?&?): IH H0; try solve [elia];
    split~; applys S_and...
Qed.

Lemma arrow_inv_duo : forall m A B C D,
   sub (t_arrow A B) m (t_arrow C D) -> (sub A (flipmode m) C) /\ (sub B m D).
Proof.
  intros.
  destruct m.
  - applys~ arrow_inv.
  - apply sub_rev in H.
    simpl; split; applys sub_rev; simpl; apply arrow_inv in H; jauto.
Qed.

#[export] Hint Constructors sub : core.

(* Theorem 4.11 Decidability of the algorithmic duotyping *)
Theorem decidability : forall m A B,
    sub A m B \/ not (sub A m B).
Proof with (simpl in *; solve_false; jauto; elia; try solve [right; intros HF; auto_inv; inverts HF; simpl in *; solve_false]).
  introv. gen m.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ord_or_split m B.
  - lets [Hi'|(?&?&Hi')]: ord_or_split m A.
    + lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
      * lets [Hu'|(?&?&Hu')]: ord_or_split (flipmode m) B.
        ** (* all ordinary *)
          destruct A; destruct B; destruct m...
          *** forwards [IHA1|IHA1] : IH A1 B1 m_super...
              forwards [IHA2|IHA2] : IH A2 B2 m_sub...
          *** forwards [IHA1|IHA1] : IH A1 B1 m_sub...
              forwards [IHA2|IHA2] : IH A2 B2 m_super...
        ** (* spl > B, S-orl/r *)
          forwards [IHA1|IHA1] : IH A x m...
          forwards [IHA2|IHA2] : IH A x0 m...
      * forwards [IHA1|IHA1] : IH x B m...
        forwards [IHA2|IHA2] : IH x0 B m...
    + (* spl < A, S-andl/r *)
      forwards [IHA1|IHA1] : IH x B m...
      forwards [IHA2|IHA2] : IH x0 B m...
  - (* spl < B, S-and *)
    forwards [IHA1|IHA1] : IH A x m...
    forwards [IHA2|IHA2] : IH A x0 m...
Qed.


(************************************************************)
#[local] Hint Constructors duo : core.

Lemma duotyping_dual_eqv_to_duotyping_no_dual : forall m A B,
    duo A m B <-> sub A m B.
Proof.
  split; introv H.
  - induction~ H; try solve [econstructor; try eassumption; auto].
    + applys~ sub_rev.
  -
    gen m. indTypSize (size_typ A + size_typ B).
    inverts~ H; try solve [econstructor; try eassumption; applys IH; elia; auto].
    + (* bot *)
      lets [Hi1|(?&?&Hi1)]: ord_or_split m B.
      * applys~ SD_dual.
        destruct~ m.
      * applys SD_and; try eassumption; applys IH; elia; auto.
    + (* or *)
      applys~ SD_dual.
      applys SD_and H2; applys IH; elia; auto; applys~ sub_rev.
    + (* orl *)
      applys~ SD_dual.
      applys SD_andl H3; try eassumption; applys IH; elia; auto; applys~ sub_rev.
    + (* orr *)
      applys~ SD_dual.
      applys SD_andr H3; try eassumption; applys IH; elia; auto; applys~ sub_rev.
Qed.

(* Theorem 4.5 Soundness and Completeness of Algorithmic Duotyping *)
(* A ♢a B if and only if A ♢ B *)
Theorem duo2osub : forall m A B,
    duo A m B <-> osub A m B.
Proof.
  split; introv H.
  - applys osub2lsub.
    applys lsub2sub.
    applys~ duotyping_dual_eqv_to_duotyping_no_dual.
  - applys duotyping_dual_eqv_to_duotyping_no_dual.
    applys lsub2sub.
    applys~ osub2lsub.
Qed.
