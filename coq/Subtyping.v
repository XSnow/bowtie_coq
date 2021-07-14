(*******************************************************************************
*                                                                              *
*   Subtyping.v                                                                *
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

(** This file contains lemmas and theorems around the declarative and
    algorithmic subtyping formalization.
    They are very similar to those in Duotyping.v (which are covered by
    the paper) and they are not included in the paper.

   Lemma singlemode_sub_or, Lemma s_sub_orl, and Lemma s_sub_orr are
   used in Equivalence.v
 *)

Require Import LibTactics.
Require Import Definitions.
Require Import TypeSize.


Create HintDb AllHb.
Create HintDb MulHb.
Create HintDb FalseHd.

#[local] Hint Resolve SO_top SO_bot SO_int OU_top OU_bot OU_int OU_arrow SSp_and SpU_or : core.
#[local] Hint Resolve SS_int SS_top SS_bot : MulHb.

(* Types are Either Ordinary or Splittable *)
#[local] Hint Constructors single_ord ordu single_spl splu : AllHd.

Lemma ordu_or_split: forall A,
    ordu A \/ exists B C, splu A B C.
Proof with (eauto with AllHd ; intros).
  intros. induction A...
  - (* and *)
    lets [?|(?&?&?)]: IHA1;
      lets [?|(?&?&?)]: IHA2...
Qed.

Lemma single_ord_or_split: forall A,
    single_ord A \/ exists B C, single_spl A B C.
Proof with (eauto with AllHd ; intros).
  intros. induction A...
  - (* arrow *)
    lets [?|(?&?&?)]: ordu_or_split A1;
      lets [?|(?&?&?)]: IHA2...
  - (* and *)
    lets [?|(?&?&?)]: IHA1;
      lets [?|(?&?&?)]: IHA2...
Qed.


(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)
Ltac solve_false := try intro; try solve [false; eauto 3 with FalseHd].

Lemma and_or_mismatch: forall A B C D,
    t_and A B = t_or C D -> False.
Proof.
  intros.
  inverts H.
Qed.

Lemma single_ord_and_false : forall A B,
    single_ord (t_and A B) -> False.
Proof.
  intros.
  inverts H.
Qed.

Lemma ordu_or_false : forall A B,
    ordu (t_or A B) -> False.
Proof.
  intros.
  inverts H.
Qed.

(* splittable types and disjoint types are not overlapping *)

Lemma splu_ord_false : forall A B C,
    splu A B C -> ordu A -> False.
Proof.
  introv. gen B C.
  induction A; intros B C s o;
    try solve [inverts* s];
    try solve [inverts* o];
    inverts o;
    inverts* s.
Qed.

Lemma single_spl_ord_false : forall A B C,
    single_spl A B C -> single_ord A -> False.
Proof.
  introv. gen B C.
  induction A; intros B C s o;
    try solve [inverts* s];
    try solve [inverts* o];
    inverts o;
    inverts* s.
  applys splu_ord_false; eassumption.
Qed.

#[local] Hint Resolve ordu_or_split and_or_mismatch single_ord_and_false
     ordu_or_false single_spl_ord_false splu_ord_false : FalseHd.


(* lemmas for ordinary *)
Lemma single_spl_keep_ordu_l : forall A B C,
   ordu A -> single_spl A B C -> ordu B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma single_spl_keep_ordu_r : forall A B C,
   ordu A -> single_spl A B C -> ordu C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma splu_keep_ord_l : forall A B C,
   single_ord A -> splu A B C -> single_ord B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma splu_keep_ord_r : forall A B C,
   single_ord A -> splu A B C -> single_ord C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

#[local] Hint Resolve single_spl_keep_ordu_l single_spl_keep_ordu_r
     splu_keep_ord_l splu_keep_ord_r : AllHd.


(* Subtyping *)
Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

#[local] Hint Resolve typ_size_lg_z : core.

Lemma splu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
Qed.

Lemma single_spl_decrease_size: forall A B C,
    single_spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  forwards (?&?): splu_decrease_size H0...
Qed.

Ltac s_spl_size :=
  try repeat match goal with
         | [ H: single_spl _ _ _ |- _ ] =>
           ( lets (?&?): single_spl_decrease_size H; clear H)
         | [ H: splu _ _ _ |- _ ] =>
           ( lets (?&?): splu_decrease_size H; clear H)
             end.

(********************************************)
(*                                          *)
(*               Ltac elia                 *)
(*  enhanced lia with split_decrease_size *)
(*                                          *)
(********************************************)
Ltac s_elia :=
  try solve [pose proof (typ_size_lg_z);
             s_spl_size; simpl in *; try lia].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

(* Splitting types is deterministic *)
(********************************************)
(*                                          *)
(*          Lemma split_unique              *)
(*                                          *)
(********************************************)
Lemma splu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (try eassumption; solve_false; subst~).
  intro T.
  induction T; intros;
    inverts H; inverts H0...
  - forwards (?&?): IHT1 H4 H5...
  - forwards (?&?): IHT2 H6 H7...
Qed.

Lemma single_spl_unique : forall T A1 A2 B1 B2,
    single_spl T A1 B1 -> single_spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (try eassumption; solve_false; subst~).
  intro T.
  induction T; intros;
    inverts H; inverts H0...
  - forwards (?&?): IHT2 H4 H5...
  - forwards (?&?): splu_unique H6 H7...
  - forwards (?&?): IHT1 H4 H5...
  - forwards (?&?): IHT2 H6 H7...
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_unify              *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end                *)
(*                                          *)
(********************************************)
Ltac s_auto_unify :=
  simpl in *;
  try repeat match goal with
         | [ H1: single_spl ?A  _ _ , H2: single_spl ?A _ _ |- _ ] =>
           (forwards (?&?): single_spl_unique H1 H2;
            subst; clear H2)
         | [ H1: splu ?A  _ _ , H2: splu ?A _ _ |- _ ] =>
           (forwards (?&?): splu_unique H1 H2;
            subst; clear H2)
         end.


(*****************************************************************************)
Inductive single_part : typ -> typ -> Prop :=
| SP_refl  : forall A, single_part A A
| SP_spl   : forall A B C B', single_spl A B C -> single_part B B' -> single_part A B'
| SP_spr   : forall A B C C', single_spl A B C -> single_part C C' -> single_part A C'
.

Inductive u_part : typ -> typ -> Prop :=
| UP_refl  : forall A, u_part A A
| UP_spl   : forall A B C B', splu A B C -> u_part B B' -> u_part A B'
| UP_spr   : forall A B C C', splu  A B C -> u_part C C' -> u_part A C'
.

#[local] Hint Constructors single_part u_part : AllHd.
#[local] Hint Resolve SP_refl UP_refl : MulHd.

Lemma single_part_spl : forall A B B1 B2,
    single_part A B -> single_spl B B1 B2 -> single_part A B1 /\ single_part A B2.
Proof with (eauto with AllHb).
  introv Hp Hspl.
  induction Hp; try forwards~ (?&?): IHHp; split;
    eauto with AllHd.
Qed.

Lemma u_part_spl : forall A B B1 B2,
    u_part A B -> splu B B1 B2 -> u_part A B1 /\ u_part A B2.
Proof with (eauto with AllHb).
  introv Hp Hspl.
  induction Hp; try forwards~ (?&?): IHHp; split;
    eauto with AllHd.
Qed.

#[local] Hint Resolve single_part_spl u_part_spl : AllHd.

#[local] Hint Constructors singlemode_sub : AllHd.

Ltac s_sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- singlemode_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; auto 4 with *; eauto 4 with AllHd; s_elia)
end.

Lemma s_sub_part : forall A B,
    (single_part A B -> singlemode_sub A B)
    /\ (single_ord A -> single_ord B -> u_part B A -> singlemode_sub A B).
Proof with (try eassumption; auto 4 with *; try solve [s_sub_part_autoIH]; eauto 3 with *).
  introv.
  indTypSize (size_typ A + size_typ B).
  split.

  --
  introv Hp.
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  - (* ord B *)
    inverts Hp.
    + lets [Hu|(?&?&Hu)]: ordu_or_split B.
      * destruct B; s_auto_unify; solve_false...
        **(* arrow *)
          constructor...
      * applys~ SS_or Hu...
    + applys SS_andl...
    + applys SS_andr...
  - (* spl B *)
    lets~ (?&?): single_part_spl Hp Hi.
    applys SS_and Hi...

    --
    introv Ho1 Ho2 Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A.
    + inverts Hp; s_auto_unify.
      * (* ord B *)
      destruct A; s_auto_unify; auto; solve_false...
      ** (* arrow case, non-ord types involved *)
        constructor...
      * applys SS_orl...
      * applys SS_orr...
    +
      lets~ (?&?): u_part_spl Hp Hu.
      applys SS_or...
Qed.

Theorem s_sub_refl : forall A, singlemode_sub A A.
Proof.
  introv.
  pose proof (s_sub_part A A).
  destruct H; auto with *.
Qed.

Lemma s_sub_part1 : forall A B,
    single_part A B -> singlemode_sub A B.
Proof.
  introv.
  pose proof (s_sub_part A B).
  destruct* H.
Qed.

Lemma s_sub_part2 : forall A B,
    single_ord A -> single_ord B -> u_part B A -> singlemode_sub A B.
Proof.
  introv.
  pose proof (s_sub_part A B).
  destruct* H.
Qed.

#[local] Hint Resolve s_sub_refl : MulHd.
#[local] Hint Resolve s_sub_part1 s_sub_part2 : AllHd.

(* algorithm correctness *)
Lemma s_rule_and_inv : forall A B B1 B2,
    singlemode_sub A B -> single_spl B B1 B2 -> singlemode_sub A B1 /\ singlemode_sub A B2.
Proof.
  intros.
  induction H; solve_false; s_auto_unify; jauto; auto with *.
Qed.

(* previous and_inv spl_inv *)
Lemma s_rule_andlr_inv : forall A B A1 A2,
    singlemode_sub A B -> single_spl A A1 A2 -> single_ord B ->
    singlemode_sub A1 B \/ singlemode_sub A2 B.
Proof.
  introv Hsub Hord Hspl.
  inverts Hsub; solve_false; s_auto_unify; auto with *.
Qed.


Lemma s_rule_or_inv : forall A A1 A2 B,
    singlemode_sub A B -> splu A A1 A2 ->
    singlemode_sub A1 B /\ singlemode_sub A2 B.
Proof with (s_auto_unify; try eassumption; s_elia; eauto 4 with AllHd).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  - inverts Hsub; solve_false; s_auto_unify; auto with *.
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A0 A2) A0 A2 B...
      * forwards* (?&?): IH (t_or A1 B1) A1 B1 B...
      * forwards* (?&?): IH H2 B...
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH H1...
      * forwards* (?&?): IH H1...
      * forwards* (?&?): IH H1...
  - forwards (?&?): s_rule_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...
Qed.

Lemma s_rule_orlr_inv : forall A B B1 B2,
    singlemode_sub A B -> ordu A -> splu B B1 B2 ->
    singlemode_sub A B1 \/ singlemode_sub A B2.
Proof with (solve_false; s_auto_unify; try eassumption; s_elia; eauto 3 with AllHd).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub...
  + (* double split *)
    inverts Hspl; inverts H...
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
    * forwards [?|?]: IH H2...
    * forwards [?|?]: IH H1 H3...
  + forwards [?|?]: IH H1... eauto 4 with AllHd. eauto 4 with AllHd.
  + forwards* [?|?]: IH H1...  eauto 4 with AllHd. eauto 4 with AllHd.
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_inv                *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no solve_false at the end               *)
(*                                          *)
(********************************************)
Ltac s_auto_inv :=
  repeat try match goal with
         | [ H1: singlemode_sub ?A ?B, H2: single_spl ?B _ _ |- _ ] =>
           try (forwards~ (?&?): s_rule_and_inv H1 H2; clear H1)
         | [ H1: singlemode_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): s_rule_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: single_ord ?B, H1: singlemode_sub ?A ?B, H2: single_spl ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: s_rule_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: single_ord ?B, H1: singlemode_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: s_rule_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: singlemode_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): s_rule_or_inv H1 H2; clear H1)
         | [ H1: singlemode_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): s_rule_or_inv H1; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: singlemode_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: s_rule_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: singlemode_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: s_rule_orlr_inv H1 Hord; clear H1)
             end.


Lemma singlemode_sub_or : forall A A1 A2 B,
    splu A A1 A2 -> singlemode_sub A1 B -> singlemode_sub A2 B -> singlemode_sub A B.
Proof with (s_auto_unify; try eassumption; s_auto_inv; s_elia).
  introv Hsingle_spl Hs1 Hs2.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B...
  lets [Hi'|(?&?&Hi')]: single_ord_or_split A...
  - applys SS_or...
  - (* double single_split A *)
    inverts keep Hsingle_spl; inverts keep Hi'...
    + applys~ SS_andl Hi'... applys IH; eauto; try eassumption; s_elia.
    + applys~ SS_andr Hi'... applys IH; eauto; try eassumption; s_elia.
    + applys~ SS_andl Hi'... applys IH; eauto; try eassumption; s_elia.
    + applys~ SS_andr Hi'... applys IH; eauto; try eassumption; s_elia.
    + applys~ SS_andl Hi'... applys IH; eauto; try eassumption; s_elia.
    + applys~ SS_andr Hi'...
    + applys~ SS_andr Hi'...
    + applys~ SS_andr Hi'...
    + applys~ SS_andl Hi'...
    + applys~ SS_andl Hi'...
    + applys~ SS_andl Hi'...
    + applys~ SS_andr Hi'... applys IH; eauto; try eassumption; s_elia.
  - applys~ SS_and Hi...
    applys IH... applys IH...
Qed.

#[local] Hint Resolve singlemode_sub_or : AllHd.

Ltac s_trans_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ , H1: singlemode_sub ?A  ?B , H2: singlemode_sub ?B  ?C |- singlemode_sub ?A  ?C ] =>
    (applys~ IH H1 H2; s_elia; auto)
  | [ IH: forall A B : typ, _ , H1: singlemode_sub ?A  ?B  |- singlemode_sub ?A  ?C ] =>
    (applys~ IH H1; s_elia; constructor~)
  | [ IH: forall A B : typ, _ , H2: singlemode_sub ?B  ?C |- singlemode_sub ?A  ?C ] =>
    (applys~ IH H2; s_elia; constructor~)
  end.

Lemma s_trans : forall A B C, singlemode_sub A B -> singlemode_sub B C -> singlemode_sub A C.
Proof with (solve_false; s_auto_unify; try eassumption; auto with *; s_auto_inv; try solve s_trans_autoIH).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets [Hi|(?&?&Hi)]: single_ord_or_split C...
  - lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + lets [Hi'|(?&?&Hi')]: single_ord_or_split B...
      lets [Hu'|(?&?&Hu')]: ordu_or_split B...
      lets [Hi''|(?&?&Hi'')]: single_ord_or_split A...
      * (* double ord A B *)
        inverts s1; s_auto_unify...
        ** (* top *)
          inverts~ s2...
          *** applys~ SS_orl H2...
          *** applys~ SS_orr H2...
        ** (* arrow *)
          inverts~ s2...
          *** applys~ SS_arrow...
          *** applys~ SS_orl H6...
          *** applys~ SS_orr H6...
      * applys SS_andl...
      * applys SS_andr...
    + lets [Hi'|(?&?&Hi')]: single_ord_or_split A...
      * applys SS_or Hu...
      * assert (singlemode_sub x C)...
        assert (singlemode_sub x0 C)...
        applys singlemode_sub_or...
  - applys SS_and Hi...
Qed.

#[local] Hint Resolve s_trans : AllHd.

Lemma s_sub_arrow : forall A1 A2 B1 B2,
    singlemode_sub B1 A1 -> singlemode_sub A2 B2 -> singlemode_sub (t_arrow A1 A2) (t_arrow B1 B2).
Proof with (try eassumption; s_auto_unify; s_auto_inv; solve_false; s_elia; try solve [constructor; auto with AllHb]).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: single_ord_or_split (t_arrow A1 A2)...
  lets [Hi2|(?&?&Hi2)]: single_ord_or_split (t_arrow B1 B2)...
  lets [Hu1|(?&?&Hu1)]: ordu_or_split (t_arrow A1 A2)...
  lets [Hu2|(?&?&Hu2)]: ordu_or_split (t_arrow B1 B2)...
  - inverts Hi2.
    + forwards (?&?): s_rule_and_inv Hs2 H3...
      applys SS_and.
      econstructor; try eassumption.
      applys~ IH. s_elia.
      applys~ IH. s_elia.
    + forwards (?&?): s_rule_or_inv Hs1 H4.
      applys SS_and. applys SSp_arrowUnion; try eassumption.
      applys~ IH; s_elia. applys~ IH; s_elia.
  - inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: single_ord_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: s_rule_andlr_inv Hs2 H3. inverts~ Hi2.
        applys SS_andl; try eassumption.
        econstructor. apply H3.
        applys~ IH. s_elia.
        applys SS_andr; try eassumption.
        econstructor. apply H3.
        applys~ IH. s_elia.
      * inverts Hi2.
        ** forwards (?&?): s_rule_and_inv Hs2 H4.
           applys SS_and. econstructor; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
        ** forwards (?&?): s_rule_or_inv Hs1 H5.
           applys SS_and. applys SSp_arrowUnion; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
    + lets [Hi2|(?&?&Hi2)]: single_ord_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: s_rule_orlr_inv Hs1 H4. inverts~ Hi2.
        1: { applys SS_andl; try eassumption.
        applys SSp_arrowUnion; try eassumption.
        applys~ IH. s_elia. }
        1: { applys SS_andr; try eassumption.
        applys SSp_arrowUnion; try eassumption.
        applys~ IH. s_elia. }
      * inverts Hi2.
        ** forwards (?&?): s_rule_and_inv Hs2 H5.
           applys SS_and. econstructor; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
        ** forwards (?&?): s_rule_or_inv Hs1 H6.
           applys SS_and. applys SSp_arrowUnion; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
Qed.

Lemma s_sub_orl : forall A B B1 B2,
    splu B B1 B2 -> singlemode_sub A B1 -> singlemode_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hsingle_spl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  lets [Hi'|(?&?&Hi')]: single_ord_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ SS_orl Hsingle_spl.
  - applys~ singlemode_sub_or Hu; applys IH Hsingle_spl; s_elia; applys s_trans Hs; applys s_sub_part2...
  - forwards~ [?|?]: s_rule_andlr_inv Hs Hi'...
      applys~ SS_andl Hi'. applys~ IH Hsingle_spl. s_elia.
      applys~ SS_andr Hi'. applys~ IH Hsingle_spl. s_elia.
  - inverts Hsingle_spl; inverts Hi; solve_false; s_auto_unify.
    + applys SS_and...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
    + applys SS_and...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
    + s_auto_inv.
      applys SS_and. eauto.
      applys~ IH H; s_elia.
      try eassumption.
    + s_auto_inv.
      applys SS_and. eauto.
      try eassumption.
      applys~ IH H0; s_elia.
Qed.

Lemma s_sub_orr : forall A B B1 B2,
    splu B B1 B2 -> singlemode_sub A B2 -> singlemode_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hsingle_spl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  lets [Hi'|(?&?&Hi')]: single_ord_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ SS_orr Hsingle_spl.
  - applys~ singlemode_sub_or Hu; applys IH Hsingle_spl; s_elia; applys s_trans Hs; applys s_sub_part2...
  - forwards~ [?|?]: s_rule_andlr_inv Hs Hi'...
      applys~ SS_andl Hi'. applys~ IH Hsingle_spl. s_elia.
      applys~ SS_andr Hi'. applys~ IH Hsingle_spl. s_elia.
  - inverts Hsingle_spl; inverts Hi; solve_false; s_auto_unify.
    + applys SS_and...
      applys IH; s_elia. eauto. applys s_trans Hs...
      applys IH; s_elia. eauto. applys s_trans Hs...
    + applys SS_and...
      applys IH; s_elia. eauto. applys s_trans Hs...
      applys IH; s_elia. eauto. applys s_trans Hs...
    + s_auto_inv.
      applys SS_and. eauto.
      applys~ IH H; s_elia.
      try eassumption.
    + s_auto_inv.
      applys SS_and. eauto.
      try eassumption.
      applys~ IH H0; s_elia.
Qed.

Lemma s_sub_distArrU: forall A B C,
    singlemode_sub (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_or A B) C).
Proof with (s_auto_unify; try eassumption).
  introv.
  indTypSize (size_typ C).
  lets [Hi1|(?&?&Hi1)]: single_ord_or_split C.
  - applys SS_and; eauto with *.
  - (* split C x x0 *)
    forwards Hs1: IH A B x. s_elia.
    forwards Hs2: IH A B x0. s_elia.
    applys SS_and. eauto with *.
    + applys s_trans Hs1. applys SS_and; eauto with *.
    + applys s_trans Hs2. applys SS_and; eauto with *.
Qed.

#[local] Hint Resolve s_sub_arrow s_sub_orl s_sub_orr s_sub_distArrU : AllHd.

Lemma arrow_inv : forall A B C D,
    singlemode_sub (t_arrow A B) (t_arrow C D) -> (singlemode_sub C A) /\ (singlemode_sub B D).
Proof with (simpl in *; solve_false; s_auto_unify; try eassumption; s_auto_inv; eauto 3 with AllHd).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: single_ord_or_split (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: single_ord_or_split (t_arrow A B).
  - inverts s...
  - inverts keep Hi1;
      forwards~ [?|?]: s_rule_andlr_inv s Hi1;
      forwards(IH1&IH2): IH H; try solve [s_elia];
        split; try eassumption; inverts~ Hi2...
  - (* uses and_inv_1 and_inv_2 *)
    forwards (?&?): s_rule_and_inv s Hi2.
    inverts keep Hi2;
      forwards (?&?): IH H; try solve [s_elia];
        forwards (?&?): IH H0; try solve [s_elia];
          split...
Qed.

Theorem decidability : forall A B,
    singlemode_sub A B \/ not (singlemode_sub A B).
Proof with (simpl in *; solve_false; jauto; s_elia; try solve [right; intros HF; s_auto_inv; inverts HF; simpl in *; solve_false]; eauto 3 with AllHd).
  introv.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  - lets [Hi'|(?&?&Hi')]: single_ord_or_split A.
    + lets [Hu|(?&?&Hu)]: ordu_or_split A.
      * lets [Hu'|(?&?&Hu')]: ordu_or_split B.
        ** (* all ordinary *)
          destruct A; destruct B...
          *** forwards [IHA1|IHA1] : IH B1 A1...
              forwards [IHA2|IHA2] : IH A2 B2...
        ** (* spl > B, S-orl/r *)
          forwards [IHA1|IHA1] : IH A x...
          forwards [IHA2|IHA2] : IH A x0...
      * forwards [IHA1|IHA1] : IH x B...
        forwards [IHA2|IHA2] : IH x0 B...
    + (* spl < A, S-andl/r *)
      forwards [IHA1|IHA1] : IH x B...
      forwards [IHA2|IHA2] : IH x0 B...
  - (* spl < B, S-and *)
    forwards [IHA1|IHA1] : IH A x...
    forwards [IHA2|IHA2] : IH A x0...
Qed.

#[local] Hint Constructors declarative_subtyping : AllHb.
#[local] Hint Resolve s_sub_refl : core.

Lemma dsub_splu: forall A B C,
    splu A B C -> declarative_subtyping B A /\ declarative_subtyping C A.
Proof with intuition.
  introv H.
  induction H; try intuition; eauto 3 with AllHb.
Qed.

Lemma dsub_spl: forall A B C,
    single_spl A B C -> declarative_subtyping A B /\ declarative_subtyping A C.
Proof with intuition.
  introv H.
  induction H; try forwards: dsub_splu H0; try intuition; eauto 4 with AllHb.
Qed.

#[local] Hint Resolve dsub_splu dsub_spl : AllDb.

Lemma dsub_symm_and: forall A B,
    declarative_subtyping (t_and A B) (t_and B A).
Proof.
  introv.
  applys DS_and; eauto with *.
Qed.

Lemma dsub_symm_or: forall A B,
    declarative_subtyping (t_or A B) (t_or B A).
Proof.
  introv.
  applys DS_or; eauto with *.
Qed.

#[local] Hint Resolve dsub_symm_and dsub_symm_or : AllHd.

Lemma dsub_or: forall A B C,
    splu A B C -> declarative_subtyping A (t_or B C).
Proof with (eauto 3 with AllHb).
  introv H.
  induction H; try intuition; eauto 3 with AllHb.
  - applys DS_trans.
    2: { applys DS_distAnd. }
    eauto 3 with AllHb.
  - applys DS_trans. applys dsub_symm_and.
    applys DS_trans (t_or (t_and B1 A) (t_and B2 A)).
    1: { applys DS_trans.
        2: { applys DS_distAnd. }
        eauto 3 with AllHb. }
    applys DS_or.
    applys DS_trans (t_and A B1)...
    applys DS_trans (t_and A B2)...
Qed.

Lemma dsub_and: forall A B C,
    single_spl A B C -> declarative_subtyping (t_and B C) A.
Proof with (eauto 3 with AllHb).
  introv H.
  induction H; try intuition...
  - forwards: dsub_or H0...
  - applys DS_trans.
    1: { applys DS_distOr. }
    eauto 3 with AllHb.
  - applys DS_trans. 2: { applys dsub_symm_or. }
    applys DS_trans (t_and (t_or B1 A) (t_or B2 A)).
    2: { applys DS_trans.
         applys DS_distOr.
        eauto 3 with AllHb. }
    applys DS_and.
    applys DS_trans (t_or A B1)...
    applys DS_trans (t_or A B2)...
Qed.

#[local] Hint Resolve dsub_and dsub_or : AllHd.

Theorem dsub2asub: forall A B,
    declarative_subtyping A B <-> singlemode_sub A B.
Proof with (simpl in *; try eassumption; eauto 3 with *).
  split; introv H.
  - induction H; try solve [constructor; eauto 3 with AllHb]; eauto.
    + applys s_trans...
    + applys s_sub_arrow...
    + applys* SS_and.
    + applys s_sub_part1...
    + applys s_sub_part1...
    + applys singlemode_sub_or. eauto 4 with *. auto. auto.
    + applys s_sub_orl...
    + applys s_sub_orr...
    + applys SS_and...
    + applys SS_and... eauto 4 with *. eauto 4 with *.
    + applys s_sub_distArrU.
    + applys* SS_and...
    + applys singlemode_sub_or. eauto 4 with *.
      applys SS_and... applys s_sub_orl... applys s_sub_orr...
    + applys singlemode_sub_or. eauto 4 with *.
      applys s_sub_orl... applys s_sub_orr...
  - induction H; auto with *.
    + (* and *)
      applys DS_trans (t_and B1 B2)...
    + (* andl *)
      forwards (?&?): dsub_spl H0. applys DS_trans IHsinglemode_sub...
    + (* andr *)
      forwards (?&?): dsub_spl H0. applys DS_trans IHsinglemode_sub...
    +  (* or *)
      applys DS_trans (t_or A1 A2)...
    + (* orl *)
      forwards (?&?): dsub_splu H2. applys DS_trans IHsinglemode_sub...
    + (* orr *)
      forwards (?&?): dsub_splu H2. applys DS_trans IHsinglemode_sub...
Qed.
