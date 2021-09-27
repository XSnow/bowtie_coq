(*******************************************************************************
*                                                                              *
*   DistSubtyping.v                                                            *
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

(** This file contains the declarative and algorithmic subtyping formalization.
    The algorithmic system is proved to be sound and complete w.r.t the
    declarative one (in Thereoem dsub2asub).
    Some inversion lemmas (end with _inv) are provided to justify the algorithm.
    The formulation is the same as ../coq/syntax_ott.v.
    We hope this stand-alone file can make your work simpler if you are going to
    use the subtyping part (but not the duotyping) only.
 *)

Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import Definitions.


Create HintDb AllHd.
Create HintDb SizeHd.
Create HintDb FalseHd.

(** * Size *)
Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_or A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  end.

Lemma size_typ_min :
  forall A1, 1 <= size_typ A1.
Proof.
  induction A1; simpl in *; eauto; try lia.
Qed.

#[local] Hint Resolve OI_top OI_bot OI_int OU_top OU_bot OU_int OU_arrow SpI_and SpU_or : core.
#[local] Hint Resolve AS_int AS_top AS_bot : AllHd.

(* Types are Either Ordinary or Splittable *)
#[local] Hint Constructors ordi ordu spli splu : FalseHd AllHd.

Lemma ordu_or_split: forall A,
    ordu A \/ exists B C, splu A B C.
Proof with (eauto with * ; intros).
  intros. induction A...
  - (* and *)
    lets [?|(?&?&?)]: IHA1;
      lets [?|(?&?&?)]: IHA2...
Qed.

Lemma ordi_or_split: forall A,
    ordi A \/ exists B C, spli A B C.
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
Ltac solve_false := try intro; try solve [false; eauto 4 with FalseHd].

Lemma and_or_mismatch: forall A B C D,
    t_and A B = t_or C D -> False.
Proof.
  intros.
  inverts H.
Qed.

Lemma ordi_and_false : forall A B,
    ordi (t_and A B) -> False.
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

Lemma spli_ord_false : forall A B C,
    spli A B C -> ordi A -> False.
Proof.
  introv. gen B C.
  induction A; intros B C s o;
    try solve [inverts* s];
    try solve [inverts* o];
    inverts o;
    inverts* s.
  applys splu_ord_false; eassumption.
Qed.

#[local] Hint Resolve ordu_or_split and_or_mismatch ordi_and_false
     ordu_or_false spli_ord_false splu_ord_false : FalseHd.


(* lemmas for ordinary *)
Lemma spli_keep_ordu_l : forall A B C,
   ordu A -> spli A B C -> ordu B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

Lemma spli_keep_ordu_r : forall A B C,
   ordu A -> spli A B C -> ordu C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

Lemma splu_keep_ord_l : forall A B C,
   ordi A -> splu A B C -> ordi B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

Lemma splu_keep_ord_r : forall A B C,
   ordi A -> splu A B C -> ordi C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts Hord; eauto with *.
Qed.

#[local] Hint Resolve spli_keep_ordu_l spli_keep_ordu_r
     splu_keep_ord_l splu_keep_ord_r : AllHd.


(* Subtyping *)
Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

#[local] Hint Resolve typ_size_lg_z : SizeHd.

Lemma splu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
Qed.

Lemma spli_decrease_size: forall A B C,
    spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  forwards (?&?): splu_decrease_size H0...
Qed.

Ltac s_spl_size :=
  try repeat match goal with
         | [ H: spli _ _ _ |- _ ] =>
           ( lets (?&?): spli_decrease_size H; clear H)
         | [ H: splu _ _ _ |- _ ] =>
           ( lets (?&?): splu_decrease_size H; clear H)
             end.

(********************************************)
(*                                          *)
(*               Ltac eomg2                 *)
(*  enhanced lia with split_decrease_size   *)
(*                                          *)
(********************************************)
Ltac s_elia :=
  try solve [pose proof (typ_size_lg_z);
             s_spl_size; simpl in *; try lia].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto with SizeHd;
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

Lemma spli_unique : forall T A1 A2 B1 B2,
    spli T A1 B1 -> spli T A2 B2 -> A1 = A2 /\ B1 = B2.
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
  try solve [applys SpI_and];
  try solve [applys SpU_or];
  try repeat match goal with
         | [ H1: spli ?A  _ _ , H2: spli ?A _ _ |- _ ] =>
           (forwards (?&?): spli_unique H1 H2;
            subst; clear H2)
         | [ H1: splu ?A  _ _ , H2: splu ?A _ _ |- _ ] =>
           (forwards (?&?): splu_unique H1 H2;
            subst; clear H2)
         end.


(*****************************************************************************)
Inductive single_part : typ -> typ -> Prop :=
| SP_refl  : forall A, single_part A A
| SP_spl   : forall A B C B', spli A B C -> single_part B B' -> single_part A B'
| SP_spr   : forall A B C C', spli A B C -> single_part C C' -> single_part A C'
.

Inductive u_part : typ -> typ -> Prop :=
| UP_refl  : forall A, u_part A A
| UP_spl   : forall A B C B', splu A B C -> u_part B B' -> u_part A B'
| UP_spr   : forall A B C C', splu  A B C -> u_part C C' -> u_part A C'
.

#[local] Hint Constructors single_part u_part : AllHd.
#[local] Hint Resolve SP_refl UP_refl : AllHd.

Lemma single_part_spl : forall A B B1 B2,
    single_part A B -> spli B B1 B2 -> single_part A B1 /\ single_part A B2.
Proof with (eauto with AllHd).
  introv Hp Hspl.
  induction Hp; try forwards~ (?&?): IHHp; split;
    eauto with AllHd.
Qed.

Lemma u_part_spl : forall A B B1 B2,
    u_part A B -> splu B B1 B2 -> u_part A B1 /\ u_part A B2.
Proof with (eauto with AllHd).
  introv Hp Hspl.
  induction Hp; try forwards~ (?&?): IHHp; split;
    eauto with AllHd.
Qed.

#[local] Hint Resolve single_part_spl u_part_spl : AllHd.

#[local] Hint Constructors algorithmic_sub : AllHd.

Ltac s_sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- algorithmic_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; auto 4 with *; eauto 4 with AllHd; s_elia)
end.

Lemma s_sub_part : forall A B,
    (single_part A B -> algorithmic_sub A B)
    /\ (ordi A -> ordi B -> u_part B A -> algorithmic_sub A B).
Proof with (try eassumption; auto 4 with *; try solve [s_sub_part_autoIH]; eauto 3 with *).
  introv.
  indTypSize (size_typ A + size_typ B).
  split.

  --
  introv Hp.
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - (* ord B *)
    inverts Hp.
    + lets [Hu|(?&?&Hu)]: ordu_or_split B.
      * destruct B; s_auto_unify; solve_false...
        **(* arrow *)
          constructor...
      * applys~ AS_or Hu...
    + applys AS_andl...
    + applys AS_andr...
  - (* spl B *)
    lets~ (?&?): single_part_spl Hp Hi.
    applys AS_and Hi...

    --
    introv Ho1 Ho2 Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A.
    + inverts Hp; s_auto_unify.
      * (* ord B *)
      destruct A; s_auto_unify; auto; solve_false...
      ** (* arrow case, non-ord types involved *)
        constructor...
      * applys AS_orl...
      * applys AS_orr...
    +
      lets~ (?&?): u_part_spl Hp Hu.
      applys AS_or...
Qed.

Theorem s_sub_refl : forall A, algorithmic_sub A A.
Proof.
  introv.
  pose proof (s_sub_part A A).
  destruct H; auto with *.
Qed.

Lemma s_sub_part1 : forall A B,
    single_part A B -> algorithmic_sub A B.
Proof.
  introv.
  pose proof (s_sub_part A B).
  destruct* H.
Qed.

Lemma s_sub_part2 : forall A B,
    ordi A -> ordi B -> u_part B A -> algorithmic_sub A B.
Proof.
  introv.
  pose proof (s_sub_part A B).
  destruct* H.
Qed.

#[local] Hint Resolve s_sub_refl : MulHd.
#[local] Hint Resolve s_sub_part1 s_sub_part2 : AllHd.

(* algorithm correctness *)
Lemma s_rule_and_inv : forall A B B1 B2,
    algorithmic_sub A B -> spli B B1 B2 -> algorithmic_sub A B1 /\ algorithmic_sub A B2.
Proof.
  intros.
  induction H; solve_false; s_auto_unify; jauto; auto with *.
Qed.

(* previous and_inv spl_inv *)
Lemma s_rule_andlr_inv : forall A B A1 A2,
    algorithmic_sub A B -> spli A A1 A2 -> ordi B ->
    algorithmic_sub A1 B \/ algorithmic_sub A2 B.
Proof.
  introv Hsub Hord Hspl.
  inverts Hsub; solve_false; s_auto_unify; auto with *.
Qed.


Lemma s_rule_or_inv : forall A A1 A2 B,
    algorithmic_sub A B -> splu A A1 A2 ->
    algorithmic_sub A1 B /\ algorithmic_sub A2 B.
Proof with (s_auto_unify; try eassumption; s_elia; eauto 4 with AllHd ).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - inverts Hsub; solve_false; s_auto_unify; auto with AllHd.
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A0 A2) A0 A2 B...
      * forwards* (?&?): IH (t_or A1 B1) A1 B1 B...
      * forwards* (?&?): IH H2 B...
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A5 A2) A5 A2 B...
      * forwards* (?&?): IH (t_or A1 B2) A1 B2 B...
      * forwards* (?&?): IH H1...
  - forwards (?&?): s_rule_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...
Qed.

Lemma s_rule_orlr_inv : forall A B B1 B2,
    algorithmic_sub A B -> ordu A -> splu B B1 B2 ->
    algorithmic_sub A B1 \/ algorithmic_sub A B2.
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
         | [ H1: algorithmic_sub ?A ?B, H2: spli ?B _ _ |- _ ] =>
           try (forwards~ (?&?): s_rule_and_inv H1 H2; clear H1)
         | [ H1: algorithmic_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): s_rule_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ordi ?B, H1: algorithmic_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: s_rule_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algorithmic_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: s_rule_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: algorithmic_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): s_rule_or_inv H1 H2; clear H1)
         | [ H1: algorithmic_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): s_rule_or_inv H1; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: algorithmic_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: s_rule_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: algorithmic_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: s_rule_orlr_inv H1 Hord; clear H1)
             end.


Lemma algorithmic_sub_or : forall A A1 A2 B,
    splu A A1 A2 -> algorithmic_sub A1 B -> algorithmic_sub A2 B -> algorithmic_sub A B.
Proof with (s_auto_unify; try eassumption; s_auto_inv; s_elia).
  introv Hspli Hs1 Hs2.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B...
  lets [Hi'|(?&?&Hi')]: ordi_or_split A...
  - applys AS_or...
  - (* double spliit A *)
    inverts keep Hspli; inverts keep Hi'...
    + applys~ AS_andl Hi'... applys IH...
    + applys~ AS_andr Hi'... applys IH...
    + applys~ AS_andl Hi'... applys IH...
    + applys~ AS_andr Hi'... applys IH...
    + applys~ AS_andl Hi'... applys IH...
    + applys~ AS_andr Hi'...
    + applys~ AS_andr Hi'...
    + applys~ AS_andr Hi'...
    + applys~ AS_andl Hi'...
    + applys~ AS_andl Hi'...
    + applys~ AS_andl Hi'...
    + applys~ AS_andr Hi'... applys IH; eauto; try eassumption; s_elia.
  - applys~ AS_and Hi...
    applys IH... applys IH...
Qed.

#[local] Hint Resolve algorithmic_sub_or : AllHd.

Ltac s_trans_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ , H1: algorithmic_sub ?A  ?B , H2: algorithmic_sub ?B  ?C |- algorithmic_sub ?A  ?C ] =>
    (applys~ IH H1 H2; s_elia; auto)
  | [ IH: forall A B : typ, _ , H1: algorithmic_sub ?A  ?B  |- algorithmic_sub ?A  ?C ] =>
    (applys~ IH H1; s_elia; constructor~)
  | [ IH: forall A B : typ, _ , H2: algorithmic_sub ?B  ?C |- algorithmic_sub ?A  ?C ] =>
    (applys~ IH H2; s_elia; constructor~)
  end.

Lemma s_trans : forall A B C, algorithmic_sub A B -> algorithmic_sub B C -> algorithmic_sub A C.
Proof with (solve_false; s_auto_unify; try eassumption; auto with *; s_auto_inv; try solve s_trans_autoIH).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets [Hi|(?&?&Hi)]: ordi_or_split C...
  - lets [Hu|(?&?&Hu)]: ordu_or_split A...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split B...
      lets [Hu'|(?&?&Hu')]: ordu_or_split B...
      lets [Hi''|(?&?&Hi'')]: ordi_or_split A...
      * (* double ord A B *)
        inverts s1; s_auto_unify...
        ** (* top *)
          inverts~ s2...
          *** applys~ AS_orl H2...
          *** applys~ AS_orr H2...
        ** (* arrow *)
          inverts~ s2...
          *** applys~ AS_arrow...
          *** applys~ AS_orl H6...
          *** applys~ AS_orr H6...
      * applys AS_andl...
      * applys AS_andr...
    + lets [Hi'|(?&?&Hi')]: ordi_or_split A...
      * applys AS_or Hu...
      * assert (algorithmic_sub x C)...
        assert (algorithmic_sub x0 C)...
        applys algorithmic_sub_or...
  - applys AS_and Hi...
Qed.

#[local] Hint Resolve s_trans : AllHd.

Lemma s_sub_arrow : forall A1 A2 B1 B2,
    algorithmic_sub B1 A1 -> algorithmic_sub A2 B2 -> algorithmic_sub (t_arrow A1 A2) (t_arrow B1 B2).
Proof with (try eassumption; s_auto_unify; s_auto_inv; solve_false; s_elia; try solve [constructor; auto with AllHd]).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow A1 A2)...
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2)...
  lets [Hu1|(?&?&Hu1)]: ordu_or_split (t_arrow A1 A2)...
  lets [Hu2|(?&?&Hu2)]: ordu_or_split (t_arrow B1 B2)...
  - inverts Hi2.
    + forwards (?&?): s_rule_and_inv Hs2 H3...
      applys AS_and.
      econstructor; try eassumption.
      applys~ IH. s_elia.
      applys~ IH. s_elia.
    + forwards (?&?): s_rule_or_inv Hs1 H4.
      applys AS_and. applys SpI_arrowUnion; try eassumption.
      applys~ IH; s_elia. applys~ IH; s_elia.
  - inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: s_rule_andlr_inv Hs2 H3. inverts~ Hi2.
        applys AS_andl; try eassumption.
        econstructor. apply H3.
        applys~ IH. s_elia.
        applys AS_andr; try eassumption.
        econstructor. apply H3.
        applys~ IH. s_elia.
      * inverts Hi2.
        ** forwards (?&?): s_rule_and_inv Hs2 H4.
           applys AS_and. econstructor; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
        ** forwards (?&?): s_rule_or_inv Hs1 H5.
           applys AS_and. applys SpI_arrowUnion; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: s_rule_orlr_inv Hs1 H4. inverts~ Hi2.
        1: { applys AS_andl; try eassumption.
        applys SpI_arrowUnion; try eassumption.
        applys~ IH. s_elia. }
        1: { applys AS_andr; try eassumption.
        applys SpI_arrowUnion; try eassumption.
        applys~ IH. s_elia. }
      * inverts Hi2.
        ** forwards (?&?): s_rule_and_inv Hs2 H5.
           applys AS_and. econstructor; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
        ** forwards (?&?): s_rule_or_inv Hs1 H6.
           applys AS_and. applys SpI_arrowUnion; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
Qed.

Lemma s_sub_orl : forall A B B1 B2,
    splu B B1 B2 -> algorithmic_sub A B1 -> algorithmic_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hspli Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ AS_orl Hspli.
  - applys~ algorithmic_sub_or Hu; applys IH Hspli; s_elia; applys s_trans Hs; applys s_sub_part2...
  - forwards~ [?|?]: s_rule_andlr_inv Hs Hi'...
      applys~ AS_andl Hi'. applys~ IH Hspli. s_elia.
      applys~ AS_andr Hi'. applys~ IH Hspli. s_elia.
  - inverts Hspli; inverts Hi; solve_false; s_auto_unify.
    + applys AS_and...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
    + applys AS_and...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
      applys IH; s_elia. 2: {eauto. } applys s_trans Hs...
    + s_auto_inv.
      applys AS_and. eauto.
      applys~ IH H; s_elia.
      try eassumption.
    + s_auto_inv.
      applys AS_and. eauto.
      try eassumption.
      applys~ IH H0; s_elia.
Qed.

Lemma s_sub_orr : forall A B B1 B2,
    splu B B1 B2 -> algorithmic_sub A B2 -> algorithmic_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hspli Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ AS_orr Hspli.
  - applys~ algorithmic_sub_or Hu; applys IH Hspli; s_elia; applys s_trans Hs; applys s_sub_part2...
  - forwards~ [?|?]: s_rule_andlr_inv Hs Hi'...
      applys~ AS_andl Hi'. applys~ IH Hspli. s_elia.
      applys~ AS_andr Hi'. applys~ IH Hspli. s_elia.
  - inverts Hspli; inverts Hi; solve_false; s_auto_unify.
    + applys AS_and...
      applys IH; s_elia. eauto. applys s_trans Hs...
      applys IH; s_elia. eauto. applys s_trans Hs...
    + applys AS_and...
      applys IH; s_elia. eauto. applys s_trans Hs...
      applys IH; s_elia. eauto. applys s_trans Hs...
    + s_auto_inv.
      applys AS_and. eauto.
      applys~ IH H; s_elia.
      try eassumption.
    + s_auto_inv.
      applys AS_and. eauto.
      try eassumption.
      applys~ IH H0; s_elia.
Qed.

Lemma s_sub_distArrU: forall A B C,
    algorithmic_sub (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_or A B) C).
Proof with (s_auto_unify; try eassumption).
  introv.
  indTypSize (size_typ C).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split C.
  - applys AS_and; eauto with *.
  - (* split C x x0 *)
    forwards Hs1: IH A B x. s_elia.
    forwards Hs2: IH A B x0. s_elia.
    applys AS_and. eauto with *.
    + applys s_trans Hs1. applys AS_and; eauto with *.
    + applys s_trans Hs2. applys AS_and; eauto with *.
Qed.

#[local] Hint Resolve s_sub_arrow s_sub_orl s_sub_orr s_sub_distArrU : AllHd.

Lemma arrow_inv : forall A B C D,
    algorithmic_sub (t_arrow A B) (t_arrow C D) -> (algorithmic_sub C A) /\ (algorithmic_sub B D).
Proof with (simpl in *; solve_false; s_auto_unify; try eassumption; s_auto_inv; eauto 3 with AllHd).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow A B).
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
    algorithmic_sub A B \/ not (algorithmic_sub A B).
Proof with (simpl in *; solve_false; jauto; s_elia; try solve [right; intros HF; s_auto_inv; inverts HF; simpl in *; solve_false]; eauto 3 with AllHd).
  introv.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - lets [Hi'|(?&?&Hi')]: ordi_or_split A.
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

#[local] Hint Constructors declarative_subtyping : AllHd.
#[local] Hint Resolve s_sub_refl : core.

Lemma dsub_splu: forall A B C,
    splu A B C -> declarative_subtyping B A /\ declarative_subtyping C A.
Proof with intuition.
  introv H.
  induction H; try intuition; eauto 3 with AllHd.
Qed.

Lemma dsub_spl: forall A B C,
    spli A B C -> declarative_subtyping A B /\ declarative_subtyping A C.
Proof with intuition.
  introv H.
  induction H; try forwards: dsub_splu H0; try intuition; eauto 4 with AllHd.
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
Proof with (eauto 3 with AllHd).
  introv H.
  induction H; try intuition; eauto 3 with AllHd.
  - applys DS_trans.
    2: { applys DS_distAnd. }
    eauto 3 with AllHd.
  - applys DS_trans. applys dsub_symm_and.
    applys DS_trans (t_or (t_and B1 A) (t_and B2 A)).
    1: { applys DS_trans.
        2: { applys DS_distAnd. }
        eauto 3 with AllHd. }
    applys DS_or.
    applys DS_trans (t_and A B1)...
    applys DS_trans (t_and A B2)...
Qed.

Lemma dsub_and: forall A B C,
    spli A B C -> declarative_subtyping (t_and B C) A.
Proof with (eauto 3 with AllHd).
  introv H.
  induction H; try intuition...
  - forwards: dsub_or H0...
  - applys DS_trans.
    1: { applys DS_distOr. }
    eauto 3 with AllHd.
  - applys DS_trans. 2: { applys dsub_symm_or. }
    applys DS_trans (t_and (t_or B1 A) (t_or B2 A)).
    2: { applys DS_trans.
         applys DS_distOr.
        eauto 3 with AllHd. }
    applys DS_and.
    applys DS_trans (t_or A B1)...
    applys DS_trans (t_or A B2)...
Qed.

#[local] Hint Resolve dsub_and dsub_or : AllHd.

Theorem dsub2asub: forall A B,
    declarative_subtyping A B <-> algorithmic_sub A B.
Proof with (simpl in *; try eassumption; eauto 3 with *).
  split; introv H.
  - induction H; try solve [constructor; eauto 3 with AllHd]; eauto.
    + applys s_trans...
    + applys s_sub_arrow...
    + applys* AS_and.
    + applys s_sub_part1...
    + applys s_sub_part1...
    + applys algorithmic_sub_or. eauto 4 with *. auto. auto.
    + applys s_sub_orl...
    + applys s_sub_orr...
    + applys AS_and...
    + applys AS_and... eauto 4 with *. eauto 4 with *.
    + applys s_sub_distArrU.
    + applys* AS_and...
    + applys algorithmic_sub_or. eauto 4 with *.
      applys AS_and... applys s_sub_orl... applys s_sub_orr...
    + applys algorithmic_sub_or. eauto 4 with *.
      applys s_sub_orl... applys s_sub_orr...
  - induction H; auto with *.
    + (* and *)
      applys DS_trans (t_and B1 B2)...
    + (* andl *)
      forwards (?&?): dsub_spl H0. applys DS_trans IHalgorithmic_sub...
    + (* andr *)
      forwards (?&?): dsub_spl H0. applys DS_trans IHalgorithmic_sub...
    +  (* or *)
      applys DS_trans (t_or A1 A2)...
    + (* orl *)
      forwards (?&?): dsub_splu H2. applys DS_trans IHalgorithmic_sub...
    + (* orr *)
      forwards (?&?): dsub_splu H2. applys DS_trans IHalgorithmic_sub...
Qed.
