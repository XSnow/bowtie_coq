Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import rules_inf.
Require Import Duotyping.
Require Import Subtyping.
Require Import Omega.


(* Types are Either Ordinary or Splittable *)
Hint Constructors single_ord ordu spl : core.

Lemma single_ord_or_split: forall A,
    single_ord A \/ exists B C, single_spl A B C.
Proof with rewrite_duo2sub.
  intros.
  forwards~ [?|(?&?&?)]: ord_or_split m_sub A...
  eauto.
Qed.

Lemma ordu_or_split: forall A,
    ordu A \/ exists B C, splu A B C.
Proof with rewrite_duo2sub.
  intros.
  forwards~ [?|(?&?&?)]: ord_or_split m_super A...
  eauto.
Qed.

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

Lemma single_spl_ord_false : forall A B C,
    single_spl A B C -> single_ord A -> False.
Proof.
  intros.
  applys* split_ord_false m_sub A.
Qed.

Lemma splu_ord_false : forall A B C,
    splu A B C -> ordu A -> False.
Proof.
  intros.
  applys* split_ord_false m_super A.
Qed.

Hint Resolve ordu_or_split and_or_mismatch single_ord_and_false
     ordu_or_false single_spl_ord_false splu_ord_false : falseHd.

(*
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
 *)

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

Hint Resolve single_spl_keep_ordu_l single_spl_keep_ordu_r
     splu_keep_ord_l splu_keep_ord_r : core.


(* Subtyping *)
Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

Hint Resolve typ_size_lg_z : core.

Lemma splu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try omega).
  introv H.
  induction H; simpl in *; eauto...
Qed.

Lemma single_spl_decrease_size: forall A B C,
    single_spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try omega).
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
(*               Ltac eomg2                 *)
(*  enhanced omega with split_decrease_size *)
(*                                          *)
(********************************************)
Ltac s_eomg2 :=
  try solve [pose proof (typ_size_lg_z);
             s_spl_size; simpl in *; try omega].

(* Splitting types is deterministic *)
(********************************************)
(*                                          *)
(*          Lemma split_unique              *)
(*                                          *)
(********************************************)
Lemma single_spl_unique : forall T A1 A2 B1 B2,
    single_spl T A1 B1 -> single_spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (solve_false; auto).
  intros.
  apply split_sound in H.
  apply split_sound in H0.
  applys split_unique; aauto.
Qed.

Lemma splu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (solve_false; auto).
  intros.
  apply splitu_sound in H.
  apply splitu_sound in H0.
  applys split_unique; aauto.
Qed.


(********************************************)
(*                                          *)
(*             Ltac auto_unify              *)
(*                                          *)
(*  extends choose_unify                    *)
(*  solve_false at the end                  *)
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

Hint Constructors single_part u_part : core.

Lemma single_part_spl : forall A B B1 B2,
    single_part A B -> single_spl B B1 B2 -> single_part A B1 /\ single_part A B2.
Proof.
  introv Hp Hspl.
  induction Hp; split*.
Qed.

Lemma u_part_spl : forall A B B1 B2,
    u_part A B -> splu B B1 B2 -> u_part A B1 /\ u_part A B2.
Proof.
  introv Hp Hspl.
  induction Hp; split*.
Qed.

Hint Resolve single_part_spl u_part_spl : core.

Hint Constructors singlemode_sub : core.

Ltac s_sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- singlemode_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; aauto; s_eomg2)
end.

Lemma s_sub_part : forall A B,
    (single_part A B -> singlemode_sub A B)
    /\ (single_ord A -> single_ord B -> u_part B A -> singlemode_sub A B).
Proof with (aauto; try s_sub_part_autoIH; eauto 4).
  introv.
  indTypSize (size_typ A + size_typ B).
  split.

  --
  introv Hp.
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  - (* ord B *)
    inverts Hp.
    + lets [Hu|(?&?&Hu)]: ordu_or_split B.
      * destruct B; s_auto_unify; auto; solve_false.
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
      destruct A; s_auto_unify; auto; solve_false.
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
  destruct* H.
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


Hint Resolve s_sub_refl s_sub_part1 s_sub_part2 : core.


(* algorithm correctness *)
Lemma s_rule_and_inv : forall A B B1 B2,
    singlemode_sub A B -> single_spl B B1 B2 -> singlemode_sub A B1 /\ singlemode_sub A B2.
Proof.
  intros.
  induction H; solve_false; s_auto_unify; jauto.
Qed.

(* previous and_inv spl_inv *)
Lemma s_rule_andlr_inv : forall A B A1 A2,
    singlemode_sub A B -> single_spl A A1 A2 -> single_ord B ->
    singlemode_sub A1 B \/ singlemode_sub A2 B.
Proof.
  introv Hsub Hord Hspl.
  inverts Hsub; solve_false; s_auto_unify; auto.
Qed.


Lemma s_rule_or_inv : forall A A1 A2 B,
    singlemode_sub A B -> splu A A1 A2 ->
    singlemode_sub A1 B /\ singlemode_sub A2 B.
Proof with (s_auto_unify; aauto; s_eomg2).
  introv Hsub Hspl.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  - inverts Hsub; solve_false; s_auto_unify; auto.
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A0 A2) A0 A2 B...
      * forwards* (?&?): IH (t_or A1 B1) A1 B1 B...
      * forwards* (?&?): IH H2 B...
      * split; applys* SS_andl.
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH H1...
      * forwards* (?&?): IH H1...
      * split; applys* SS_andr.
      * forwards* (?&?): IH H1...
  - forwards (?&?): s_rule_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...
    split; applys~ SS_and Hi.
Qed.

Lemma s_rule_orlr_inv : forall A B B1 B2,
    singlemode_sub A B -> ordu A -> splu B B1 B2 ->
    singlemode_sub A B1 \/ singlemode_sub A B2.
Proof with (solve_false; s_auto_unify; aauto; s_eomg2; auto).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub...
  + (* double split *)
    inverts Hspl; inverts H...
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
      left. applys* SS_and.
    * forwards [?|?]: IH H0...
      forwards [?|?]: IH H1...
      right. applys* SS_and.
    * forwards [?|?]: IH H2...
      left. applys* SS_and.
      right. applys* SS_and.
    * forwards [?|?]: IH H1 H3...
      left. applys* SS_and.
      right. applys* SS_and.
  + forwards* [?|?]: IH H1...
  + forwards* [?|?]: IH H1...
Qed.


(********************************************)
(*                                          *)
(*             Ltac auto_inv                *)
(*                                          *)
(*  extends choose_unify                    *)
(*  solve_false at the end                  *)
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
         | [ Hord: ord ?A, H1: singlemode_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: s_rule_orlr_inv H1 Hord; clear H1)
             end.


Lemma singlemode_sub_or : forall A A1 A2 B,
    splu A A1 A2 -> singlemode_sub A1 B -> singlemode_sub A2 B -> singlemode_sub A B.
Proof with (s_auto_unify; aauto; s_auto_inv; s_eomg2).
  introv Hsingle_spl Hs1 Hs2.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B...
  lets [Hi'|(?&?&Hi')]: single_ord_or_split A...
  - applys SS_or...
  - (* double single_split A *)
    inverts keep Hsingle_spl; inverts keep Hi'...
    + applys~ SS_andl Hi'... applys IH; eauto; aauto; s_eomg2.
    + applys~ SS_andr Hi'... applys IH; eauto; aauto; s_eomg2.
    + applys~ SS_andl Hi'... applys IH; eauto; aauto; s_eomg2.
    + applys~ SS_andr Hi'... applys IH; eauto; aauto; s_eomg2.
    + applys~ SS_andl Hi'... applys IH; eauto; aauto; s_eomg2.
    + applys~ SS_andr Hi'...
    + applys~ SS_andr Hi'...
    + applys~ SS_andr Hi'...
    + applys~ SS_andl Hi'...
    + applys~ SS_andl Hi'...
    + applys~ SS_andl Hi'...
    + applys~ SS_andr Hi'... applys IH; eauto; aauto; s_eomg2.
  - applys~ SS_and Hi...
    applys IH... applys IH...
Qed.


Ltac s_trans_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ , H1: singlemode_sub ?A  ?B , H2: singlemode_sub ?B  ?C |- singlemode_sub ?A  ?C ] =>
    (applys~ IH H1 H2; s_eomg2; auto)
  | [ IH: forall A B : typ, _ , H1: singlemode_sub ?A  ?B  |- singlemode_sub ?A  ?C ] =>
    (applys~ IH H1; s_eomg2; constructor~)
  | [ IH: forall A B : typ, _ , H2: singlemode_sub ?B  ?C |- singlemode_sub ?A  ?C ] =>
    (applys~ IH H2; s_eomg2; constructor~)
  end.

Lemma s_trans : forall A B C, singlemode_sub A B -> singlemode_sub B C -> singlemode_sub A C.
Proof with (solve_false; s_auto_unify; aauto; s_auto_inv; try solve s_trans_autoIH).
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
        ** (* bot *)
          auto.
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

Hint Immediate trans : core.


Lemma singlemode_sub_orl : forall A B B1 B2,
    splu B B1 B2 -> singlemode_sub A B1 -> singlemode_sub A B.
Proof.
  introv Hsingle_spl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  lets [Hi'|(?&?&Hi')]: single_ord_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ SS_orl Hsingle_spl.
  - applys~ singlemode_sub_or Hu; applys IH Hsingle_spl; s_eomg2; applys s_trans Hs; applys* s_sub_part2.
  - forwards~ [?|?]: s_rule_andlr_inv Hs Hi'. eauto.
      applys~ SS_andl Hi'. applys~ IH Hsingle_spl. s_eomg2.
      applys~ SS_andr Hi'. applys~ IH Hsingle_spl. s_eomg2.
  - inverts Hsingle_spl; inverts Hi; solve_false; s_auto_unify.
    + applys SS_and. eauto; aauto.
      applys IH; s_eomg2. 2: {eauto. } applys* s_trans Hs.
      applys IH; s_eomg2. 2: {eauto. } applys* s_trans Hs.
    + applys SS_and. eauto; aauto.
      applys IH; s_eomg2. 2: {eauto. } applys* s_trans Hs.
      applys IH; s_eomg2. 2: {eauto. } applys* s_trans Hs.
    + s_auto_inv.
      applys SS_and. eauto.
      applys~ IH H; s_eomg2.
      aauto.
    + s_auto_inv.
      applys SS_and. eauto.
      aauto.
      applys~ IH H0; s_eomg2.
Qed.


Lemma singlemode_sub_orr : forall A B B1 B2,
    splu B B1 B2 -> singlemode_sub A B2 -> singlemode_sub A B.
Proof.
  introv Hsingle_spl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: single_ord_or_split B.
  lets [Hi'|(?&?&Hi')]: single_ord_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ SS_orr Hsingle_spl.
  - applys~ singlemode_sub_or Hu; applys IH Hsingle_spl; s_eomg2; applys s_trans Hs; applys* s_sub_part2.
  - forwards~ [?|?]: s_rule_andlr_inv Hs Hi'. eauto.
      applys~ SS_andl Hi'. applys~ IH Hsingle_spl. s_eomg2.
      applys~ SS_andr Hi'. applys~ IH Hsingle_spl. s_eomg2.
  - inverts Hsingle_spl; inverts Hi; solve_false; s_auto_unify.
    + applys SS_and. eauto; aauto.
      applys IH; s_eomg2. eauto. applys* s_trans Hs.
      applys IH; s_eomg2. eauto. applys* s_trans Hs.
    + applys SS_and. eauto; aauto.
      applys IH; s_eomg2. eauto. applys* s_trans Hs.
      applys IH; s_eomg2. eauto. applys* s_trans Hs.
    + s_auto_inv.
      applys SS_and. eauto.
      applys~ IH H; s_eomg2.
      aauto.
    + s_auto_inv.
      applys SS_and. eauto.
      aauto.
      applys~ IH H0; s_eomg2.
Qed.


Theorem algo_subtyping_complete_duotyping : forall A B m,
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
  - applys~ singlemode_sub_orl H1.
  - applys~ singlemode_sub_orr H1.
Qed.
