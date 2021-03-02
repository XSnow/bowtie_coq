Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Export syntax_ott.
Require Export rules_inf.
Require Import Omega.


(* Types are Either Ordinary or Splittable *)
Hint Constructors ord spl : core.

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

Hint Resolve split_instance1 split_instance2 split_instance3 split_instance4 split_instance5 split_instance6: core.

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

Hint Resolve sub_instance1 sub_instance2 sub_instance3 sub_instance4 : core.

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

Hint Resolve choose_false_int choose_false_top choose_false_bot
     choose_false_arrow choose_and_sub choose_or_super and_or_mismatch
     choose_typebymode_false ord_sub_and_false ord_super_or_false
     ord_both_and_false ord_both_or_false : falseHd.

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

Hint Resolve split_ord_false split_int split_top split_bot split_typbymode split_typbyflippedmode: falseHd.


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

Hint Resolve split_keep_ord_l split_keep_ord_r split_keep_ord_f_l split_keep_ord_f_r : core.


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

Hint Immediate flip_eqv_false flip_eqv_false_2 : falseHd.

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

(* Subtyping *)

Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

Lemma choose_decrease_size : forall m A B,
    size_typ (choose m A B) = size_typ A + size_typ B + 1.
Proof.
  intros; destruct m; simpl in *; omega.
Qed.

Hint Resolve typ_size_lg_z : core.
Hint Rewrite choose_decrease_size : core.

Lemma split_decrease_size: forall m A B C,
    spl m A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try omega).
  - introv H.
    induction H; try rewrite choose_decrease_size in *; simpl in *;eauto...
    destruct m; eauto...
    destruct m; eauto...
Qed.

Ltac spl_size :=
  try repeat match goal with
         | [ H: spl _ _ _ _ |- _ ] =>
           ( lets (?&?): split_decrease_size H; clear H)
             end;
  try rewrite choose_decrease_size in *.

(********************************************)
(*                                          *)
(*               Ltac eomg2                 *)
(*  enhanced omega with split_decrease_size *)
(*                                          *)
(********************************************)
Ltac eomg2 :=
  try solve [pose proof (typ_size_lg_z);
             spl_size; simpl in *; try omega].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

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
    (forwards (?&?): IH Hsp Hsp2; eomg2; subst~)
end.

Lemma split_unique : forall m T A1 A2 B1 B2,
    spl m T A1 B1 -> spl m T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (solve_false; auto).
  introv. gen m.
  indTypSize (size_typ T).
  inverts H; inverts H0;
    try choose_unify; try solve_false;
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

(*
         | [ H1: spl m_sub (t_and _ _) _ _ |- _ ] =>
           inverts H1
         | [ H1: spl m_super (t_or _ _) _ _ |- _ ] =>
           inverts H1 *)

Ltac aauto := try eassumption.

(*****************************************************************************)
Inductive part : mode -> typ -> typ -> Prop :=
| P_refl  : forall m A, part m A A
| P_spl   : forall m A B C B', spl m A B C -> part m B B' -> part m A B'
| P_spr   : forall m A B C C', spl m A B C -> part m C C' -> part m A C'
.

Hint Constructors part : core.

(*
delete
Lemma ord_part_inv : forall m A B A1 A2,
    part m A B -> spl m A A1 A2 -> ord m B -> part m A1 B \/ part m A2 B.
Proof.
  introv Hp Hspl Ho.
  destruct Hp; auto_unify; jauto.
Qed.

Hint Resolve ord_part_inv : core. (* useless? *) *)

Lemma part_spl : forall m A B B1 B2,
    part m A B -> spl m B B1 B2 -> part m A B1 /\ part m A B2.
Proof.
  introv Hp Hspl.
  induction Hp; split*.
Qed.
(*
delete
Lemma part_spl_flip : forall m A B A1 A2,
    part m A B ->  spl (flipmode m) A A1 A2 -> part m A1 B /\ part m A2 B.
Proof.
  introv Hp Hspl.
  induction Hp; split*.
Abort.*)

Hint Resolve part_spl : core.


Ltac sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- sub ?A ?m ?B ] =>
  (forwards (IH1&IH2): IH A B; aauto; eomg2)
end.


Lemma sub_part : forall m A B,
    (part m A B -> sub A m B)
    /\ (ord m A -> ord m B -> part (flipmode m) B A -> sub A m B).
Proof with (aauto; try sub_part_autoIH; eauto 4).
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

Hint Resolve sub_refl sub_part1 sub_part2 : core.

(********************************************)
(*                                          *)
(*             Lemma split_iso              *)
(*                                          *)
(********************************************)
Lemma split_iso: forall m A B C,
    spl m A B C -> sub A m (choose m B C) /\ sub (choose m B C) m A.
Proof.
  introv H.
  split; applys* S_and.
Qed.

(* delete
Lemma s_andl_relaxed : forall (A:typ) (m:mode) (B A1 A2:typ),
     spl m A A1 A2 -> sub A1 m B -> sub A m B.
Proof with aauto.
  introv Hspl Hs.
  indTypSize (size_typ A).
  lets [Hi|(?&?&Hi)]: ord_or_split m B.
  - applys S_andl...
  - applys S_and...
    (* stuck *)
    (* need other lemmas *)
    (* completeness needs to be proved together *)
Abort.
 *)

Hint Constructors lsub : core.

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

Hint Immediate rev rev2 : core.


(* algorithm correctness *)
Lemma rule_and_inv : forall m A B B1 B2,
    sub A m B -> spl m B B1 B2 -> sub A m B1 /\ sub A m B2.
Proof.
  intros.
  induction* H; auto_unify.
  - destruct mode5; auto_unify.
Qed.

(* previous and_inv spl_inv *)
Lemma rule_andlr_inv : forall m A B A1 A2,
     sub A m B -> spl m A A1 A2 -> ord m B -> sub A1 m B \/ sub A2 m B.
Proof with (auto_unify; aauto; eomg2).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; auto_unify; auto.
  (* arrow *)
  inverts Hspl...
Qed.

Lemma double_split : forall m A B1 B2 C1 C2,
    spl m A B1 B2 -> spl (flipmode m) A C1 C2 -> sub C1 m B1 /\ sub C2 m B1 /\ sub C2 m B1 /\ sub C2 m B2.
Abort.

(* delete why failed
Ltac rule_or_inv_autoIH :=
  match goal with
  | [ IH: forall _, _ |- _ ] =>
    (forwards (?&?): IH; eassumption; eomg2; subst~)
  | [ IH: forall A A1 A2 : typ, spl _  A A1 A2 -> forall B : typ, _ , Hs: sub _ _ _ |- _ ] =>
    (forwards (?&?): IH Hs; eassumption; eomg2; subst~)
  end.
 *)

Lemma rule_or_inv : forall m A A1 A2 B,
    sub A m B -> spl (flipmode m) A A1 A2 -> sub A1 m B /\ sub A2 m B.
Proof with (auto_unify; aauto; eomg2).
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

(* previous or_inv splu_inv *)
Lemma rule_orlr_inv : forall m A B B1 B2,
     sub A m B -> ord (flipmode m) A -> spl (flipmode m) B B1 B2 -> sub A m B1 \/ sub A m B2.
Proof with (auto_unify; aauto; eomg2).
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
(*             Ltac auto_inv                *)
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
(*
(* it is subsumed by Lemma rule_or_inv *)
Lemma orl_trans : forall m A A1 A2 B,
    spl (flipmode m) A A1 A2 -> sub A m B -> sub A1 m B.
Proof with (auto_unify; aauto; try solve eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub; auto_unify; auto.
  - inverts Hspl...
    +  (* m:=sub A1:=I1\/C1 A2:=I2\/C2 B1:=I1&(I2\/C2) B2:=C1&(I2\/C2) *)
      inverts H...
      * applys S_andl... applys IH H0... eauto. destruct m; eomg2.
      * applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in H. inverts H.
    + flip m m'. simpl in H. inverts H.
    + auto_unify. applys S_andl. eauto.
      applys IH H1... destruct m; eomg2.
    + auto_unify. applys~ S_andl.
  - inverts Hspl...
    + inverts H...
      * applys S_andr... applys IH H0... eauto. destruct m; eomg2.
      * applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in H. inverts H.
    + flip m m'. simpl in H. inverts H.
    + auto_unify. applys~ S_andr.
    + auto_unify. applys S_andr. eauto.
      applys IH H2... destruct m; eomg2.
  - inverts keep Hspl...
    + applys S_orl... applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + flip m m'. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + applys S_orl. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orl. applys* IH H0... eomg2.
  - inverts keep Hspl...
    + applys S_orr... applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + flip m m'. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + applys S_orr. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orr. applys* IH H0... eomg2.
  - inverts Hspl...
  - applys* S_and. applys* IH H0... eomg2. applys* IH Hspl... eomg2.
Qed.

Lemma orr_trans : forall m A A1 A2 B,
    spl (flipmode m) A A1 A2 -> sub A m B -> sub A2 m B.
Proof with (auto_unify; aauto; try solve eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub; auto_unify; auto.
  - inverts Hspl...
    +
      inverts H...
      * applys IH H0... eauto. destruct m; eomg2.
      * applys S_andl... applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in H. inverts H.
    + flip m m'. simpl in H. inverts H.
    + auto_unify. applys S_andl. eauto.
      applys IH H1... destruct m; eomg2.
    + auto_unify. applys~ S_andl.
  - inverts Hspl...
    + inverts H...
      * applys IH H0... eauto. destruct m; eomg2.
      * applys S_andr... applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in H. inverts H.
    + flip m m'. simpl in H. inverts H.
    + auto_unify. applys~ S_andr.
    + auto_unify. applys S_andr. eauto.
      applys IH H2... destruct m; eomg2.
  - inverts keep Hspl...
    + applys S_orl... applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + flip m m'. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + applys S_orl. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orl. applys* IH H0... eomg2.
  - inverts keep Hspl...
    + applys S_orr... applys IH H0... eauto. destruct m; eomg2.
    + flip m m'. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + flip m m'. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + applys S_orr. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orr. applys* IH H0... eomg2.
  - inverts Hspl...
  - applys* S_and. applys* IH H0... eomg2. applys* IH Hspl... eomg2.
Qed.

Hint Resolve orl_trans orr_trans : core.
 *)

(* Add ordu T -> because counter-example A\/B <: A\/B *)
(* previous name: and_meet_or *)
Lemma or_inv : forall m A B T,
    ord (flipmode m) T -> sub T m (choose (flipmode m) A B) -> sub T m A \/ sub T m B.
Proof with (auto_unify; auto).
  introv Hu Hs.
  indTypSize (size_typ T + size_typ (choose m A B)).
  inverts Hs...
  +  Abort. (* destruct m...
  + forwards* [?|?]: IH H0. destruct m; eomg2.
  + forwards* [?|?]: IH H0. destruct m; eomg2.
  + inverts~ H...
    * forwards~ [?|?]: IH H0. destruct m; eomg2.
      forwards~ [?|?]: IH H1. destruct m; eomg2.
      left*.
    * forwards~ [?|?]: IH H0. destruct m; eomg2.
      forwards~ [?|?]: IH H1. destruct m; eomg2.
      right*.
Qed.

Lemma splu_inv : forall m A B C T,
    ord (flipmode m) T -> spl (flipmode m) C A B -> sub T m C -> sub T m A \/ sub T m B.
Proof with (auto_unify; auto).
  introv Hu Hs.
  indTypSize (size_typ T + size_typ C).
  - inverts H; try solve [destruct m; auto_unify]...
    + forwards* [?|?]: IH H1; eomg2.
    + forwards* [?|?]: IH H1; eomg2.
    + inverts H0; try solve [inverts Hs]...
      (* analyze the derivation of spl C *)
      * inverts Hs...
        ** forwards Res: IH H3 H1; aauto. destruct m; eomg2.
           destruct* Res.
        ** forwards Res: IH H4 H2; aauto. destruct m; eomg2.
           destruct* Res.
      * forwards~ [Res|Res]: or_inv H1.
        forwards~ [Res'|Res']: or_inv H2.
        left*.
      * forwards~ [Res|Res]: or_inv H1.
        forwards~ [Res'|Res']: or_inv H2.
        right*.
Qed.

(* the following two lemmas should be equivalent to the above two *)
Lemma and_inv : forall m A B T,
    ord m T -> sub (choose m A B) m T -> sub A m T \/ sub B m T.
Proof with (auto_unify; auto).
  introv Hu Hs.
  indTypSize (size_typ T + size_typ (choose m A B)).
  inverts Hs...
  + forwards* [?|?]: IH H0. destruct m; eomg2.
  + forwards* [?|?]: IH H0. destruct m; eomg2.
  + inverts~ H...
    * forwards~ [?|?]: IH H0. destruct m; eomg2.
      forwards~ [?|?]: IH H1. destruct m; eomg2.
      left*.
    * forwards~ [?|?]: IH H0. destruct m; eomg2.
      forwards~ [?|?]: IH H1. destruct m; eomg2.
      right*.
Qed.

Lemma spl_inv : forall m A B C T,
    ord m T -> spl m C A B -> sub C m T -> sub A m T \/ sub B m T.
Proof with (auto_unify; auto).
  introv Hu Hs.
  indTypSize (size_typ T + size_typ C).
  - inverts H; try solve [destruct m; auto_unify]...
    + forwards* [?|?]: IH H1; eomg2.
    + forwards* [?|?]: IH H1; eomg2.
    + flip m m'. inverts H0; try solve [inverts Hs]...
      (* analyze the derivation of spl C *)
      * flip m' m. inverts Hs...
        ** forwards Res: IH H3 H1; aauto. destruct m; eomg2.
           destruct* Res.
        ** forwards Res: IH H4 H2; aauto. destruct m; eomg2.
           destruct* Res.
      * forwards~ [Res|Res]: and_inv H1.
        forwards~ [Res'|Res']: and_inv H2.
        flip m' m. left*.
      * forwards~ [Res|Res]: and_inv H1.
        forwards~ [Res'|Res']: and_inv H2.
        flip m' m. right*.
Qed.
*)

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
Proof with (auto_unify; aauto; auto_inv; eomg2).
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
    (applys~ IH H1 H2; eomg2; auto)
  | [ IH: forall A B C : typ, _ , H1: sub ?A ?m ?B  |- sub ?A ?m ?C ] =>
    (applys~ IH H1; eomg2; constructor~)
  | [ IH: forall A B C : typ, _ , H2: sub ?B ?m ?C |- sub ?A ?m ?C ] =>
    (applys~ IH H2; eomg2; constructor~)
  end.

Lemma trans : forall m A B C, sub A m B -> sub B m C -> sub A m C.
Proof with (auto_unify; aauto; auto_inv; try solve trans_autoIH).
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

Hint Immediate trans : core.

Hint Resolve sub_or : core.

(*
Lemma split_sub_l : forall m T A B,
    spl m T A B -> sub T m A.
Proof  with (aauto; simpl in *; auto_unify).
  introv Hsp.
  applys S_andl...
  eauto.
Qed.

Lemma split_sub_r : forall m T A B,
    spl m T A B -> sub T m B.
Proof  with (aauto; simpl in *; auto_unify).
  introv Hsp.
  applys S_andr...
  eauto.
Qed.

Lemma split_sub_flip_l: forall m T A B,
    spl m T A B -> sub A (flipmode m) T.
Proof  with (aauto; simpl in *; auto_unify).
  introv Hsp.
  applys* S_orl...
  eauto.
Qed.

Lemma split_sub_flip_r : forall m T A B,
    spl m T A B -> sub B (flipmode m) T.
Proof  with (aauto; simpl in *; auto_unify).
  introv Hsp.
  applys* S_orr...
  eauto.
Qed.

Hint Resolve split_sub_l split_sub_r split_sub_flip_l split_sub_flip_r : core.
*)

Lemma sub_arrow : forall m A1 A2 B1 B2,
    sub A1 (flipmode m) B1 -> sub A2 m B2 -> sub (t_arrow A1 A2) m (t_arrow B1 B2).
Proof with (auto_unify; aauto; auto_inv; eomg2).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m (t_arrow A1 A2).
  lets [Hi2|(?&?&Hi2)]: ord_or_split m (t_arrow B1 B2).
  lets [Hu1|(?&?&Hu1)]: ord_or_split (flipmode m) (t_arrow A1 A2).
  lets [Hu2|(?&?&Hu2)]: ord_or_split (flipmode m) (t_arrow B1 B2).
  - applys~ S_arr; destruct~ m.
  - destruct m... inverts Hu2.
    + forwards [?|?]: rule_orlr_inv Hs2 H1. inverts* Hu1.
      applys S_orl; aauto. simpl. eauto. applys~ IH. eomg2.
      applys S_orr; aauto. simpl. eauto. applys~ IH. eomg2.
    + forwards [?|?]: rule_orlr_inv Hs1 H2. inverts* Hu1.
      applys S_orl; aauto. simpl. eauto. applys~ IH. eomg2.
      applys S_orr; aauto. simpl. eauto. applys~ IH. eomg2.
  - destruct m... inverts Hu1.
    + forwards (?&?): rule_or_inv Hs2 H1.
      applys S_or; aauto. simpl; eauto.
      applys~ IH; eomg2. applys~ IH; eomg2.
    + forwards (?&?): rule_or_inv Hs1 H2.
      applys S_or; aauto. simpl; eauto.
      applys~ IH; eomg2. applys~ IH; eomg2.
  - destruct m... inverts Hi2.
    + forwards (?&?): rule_and_inv Hs2 H1.
      applys S_and; aauto. simpl; eauto.
      applys~ IH; eomg2. applys~ IH; eomg2.
    + forwards (?&?): rule_and_inv Hs1 H2.
      applys S_and; aauto. simpl; eauto.
      applys~ IH; eomg2. applys~ IH; eomg2.
  - destruct m... inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow B1 B2).
      * forwards~ [?|?]: rule_andlr_inv Hs2 H1. inverts~ Hi2.
        applys S_andl; aauto. simpl. eauto. applys~ IH. eomg2.
        applys S_andr; aauto. simpl. eauto. applys~ IH. eomg2.
      * inverts Hi2.
        ** forwards (?&?): rule_and_inv Hs2 H2.
           applys S_and; aauto. simpl; eauto.
           applys~ IH; eomg2. applys~ IH; eomg2.
        ** forwards (?&?): rule_and_inv Hs1 H3.
           applys S_and; aauto. simpl; eauto.
           applys~ IH; eomg2. applys~ IH; eomg2.
    + lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow B1 B2).
      * forwards~ [?|?]: rule_andlr_inv Hs1 H2. inverts~ Hi2.
        applys S_andl; aauto. simpl. eauto. applys~ IH. eomg2.
        applys S_andr; aauto. simpl. eauto. applys~ IH. eomg2.
      * inverts Hi2.
        ** forwards (?&?): rule_and_inv Hs2 H3.
           applys S_and; aauto. simpl; eauto.
           applys~ IH; eomg2. applys~ IH; eomg2.
        ** forwards (?&?): rule_and_inv Hs1 H4.
           applys S_and; aauto. simpl; eauto.
           applys~ IH; eomg2. applys~ IH; eomg2.
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
  - applys~ sub_or Hu; applys IH Hspl; eomg2; applys trans Hs; applys* sub_part2.
  - forwards~ [?|?]: rule_andlr_inv Hs Hi'. eauto.
      applys~ S_andl Hi'. applys~ IH Hspl. eomg2.
      applys~ S_andr Hi'. applys~ IH Hspl. eomg2.
  - inverts Hspl; inverts Hi; auto_unify.
    + applys S_and; eauto.
      applys IH; eomg2. 2: {eauto. } applys* trans Hs.
      applys IH; eomg2. 2: {eauto. } applys* trans Hs.
    + applys S_and; eauto.
      applys IH; eomg2. 2: {eauto. } applys* trans Hs.
      applys IH; eomg2. 2: {eauto. } applys* trans Hs.
    + auto_inv. applys S_and; eauto.
      applys~ IH H; eomg2.
    + auto_inv. applys S_and; eauto.
      applys~ IH H0; eomg2.
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
  - applys~ sub_or Hu; applys IH Hspl; eomg2; applys trans Hs; applys* sub_part2.
  - forwards~ [?|?]: rule_andlr_inv Hs Hi'. eauto.
      applys~ S_andl Hi'. applys~ IH Hspl. eomg2.
      applys~ S_andr Hi'. applys~ IH Hspl. eomg2.
  - inverts Hspl; inverts Hi; auto_unify.
    + applys S_and; eauto.
      applys IH; eomg2. eauto. applys* trans Hs.
      applys IH; eomg2. eauto. applys* trans Hs.
    + applys S_and; eauto.
      applys IH; eomg2. eauto. applys* trans Hs.
      applys IH; eomg2. eauto. applys* trans Hs.
    + auto_inv. applys S_and; eauto.
      applys~ IH H; eomg2.
    + auto_inv. applys S_and; eauto.
      applys~ IH H0; eomg2.
Qed.



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

Hint Resolve lsub_refl lsub_trans : core.

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

Hint Resolve sub_rev sub_rev2 : core.

Lemma distArrU: forall A B C,
    sub (t_and (t_arrow A C) (t_arrow B C)) m_sub (t_arrow (t_or A B) C).
Proof with (auto_unify; aauto).
  introv.
  indTypSize (size_typ C).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m_sub C.
  - applys* S_and.
  - (* split C x x0 *)
    forwards Hs1: IH A B x. eomg2.
    forwards Hs2: IH A B x0. eomg2.
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

Hint Resolve symm_and symm_or : core.

(*
Lemma distAnd: forall A B1 B2,
    sub (t A (t_or B1 B2)) m_sub (t_or (t_and A B1) (t_and A B2)).
Proof.
  introv.
  applys* S_and.
  applys trans. applys symm_and.
  applys trans (t_or (t_and A B2) B1)...
  applys S_and...
Qed.
*)
(*
Lemma distOr: forall A1 A2 B,
    sub (t_and (t_or A1 B) (t_or A2 B)) m_sub (t_or (t_and A1 A2) B).
Proof with eauto.
  introv.
  forwards: Sp_orl m_sub (t_and A1 A2) B A1 A2; eauto.
Qed.

Hint Resolve arrow distArrU distOr : core.
*)

(* declarative subtyping equivalence *)
Hint Constructors osub : core.

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

Hint Resolve osub_spl osub_symm_and osub_symm_or osub_distAnd : core.


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

(* Hint Resolve osub_spl osub_spl2: core. *)


Theorem osub2lsub: forall A m B,
    osub A m B <-> lsub A m B.
Proof with (simpl in *; aauto).
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

(* delete
Lemma sub_1 : forall A,
    sub A m_sub t_top.
Proof.
  intros. forwards*: S_top.
Qed.

Lemma sub_2 : forall A,
    sub A m_super t_bot.
Proof.
  intros. forwards*: S_top.
Qed.

Lemma sub_3 : forall A,
    sub t_bot m_sub A.
Proof.
  intros. forwards*: S_bot.
Qed.

Lemma sub_4 : forall A,
    sub t_top m_super A.
Proof.
  intros. forwards*: S_bot.
Qed.

Lemma ord_1 : forall A B,
    ord m_sub A -> ord m_sub B -> ord m_sub (t_or A B).
Proof.
  intros. forwards*: O_or A B.
Qed.

Lemma ord_2 : forall A B,
    ord m_super A -> ord m_super B -> ord m_super (t_and A B).
Proof.
  intros. forwards*: O_or A B.
Qed.

Lemma spl_1 : forall A A1 A2 B,
    spl m_sub A A1 A2 -> spl m_sub (t_or A B) (t_or A1 B) (t_or A2 B).
Proof.
  intros. forwards*: Sp_orl A B.
Qed.

Lemma spl_2 : forall A A1 A2 B,
    spl m_super A A1 A2 -> spl m_super (t_and A B) (t_and A1 B) (t_and A2 B).
Proof.
  intros. forwards*: Sp_orl A B.
Qed.

Lemma spl_3 : forall A B B1 B2,
    ord m_sub A -> spl m_sub B B1 B2 -> spl m_sub (t_or A B) (t_or A B1) (t_or A B2).
Proof.
  intros. forwards*: Sp_orr A B.
Qed.

Lemma spl_4 : forall A B B1 B2,
    ord m_super A -> spl m_super B B1 B2 -> spl m_super (t_and A B) (t_and A B1) (t_and A B2).
Proof.
  intros. forwards*: Sp_orr A B.
Qed.

Hint Resolve sub_1 sub_2 sub_3 sub_4 ord_1 ord_2 spl_1 spl_2 spl_3 spl_4 : core.

Lemma andl_trans : forall m A B C T,
    spl m C A B -> sub T m C -> sub T m A.
Proof.
  intros. apply split_sub_l in H. eauto.
Qed.

Lemma andr_trans : forall m A B C T,
    spl m C A B -> sub T m C -> sub T m B.
Proof.
  intros.  apply split_sub_r in H. eauto.
Qed.

Hint Resolve andl_trans andr_trans : core.

Lemma rev_2 : forall A m B,
    sub A m B -> sub B (flipmode m) A.
Proof.
  intros. flip m m'. applys* rev.
Qed.
*)
(* another way to prove spl_inv
Lemma spl_inv : forall m A B C T,
    ord m T -> spl m C A B -> sub C m T -> sub A m T \/ sub B m T.
Proof.
  intros.
  flip m m'. apply rev in H1.
  forwards [Hr|Hr]: splu_inv H H0 H1;
    apply rev_2 in Hr; jauto.
Qed.
*)

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
      forwards(IH1&IH2): IH H; try solve [eomg2];
        split; try eassumption; inverts~ Hi2.
    + applys~ S_andl H1.
    + applys~ S_andr H1.
    + applys~ S_andl H2.
    + applys~ S_andr H2.
  - (* uses and_inv_1 and_inv_2 *)
    forwards (?&?): rule_and_inv s Hi2.
    inverts keep Hi2;
      forwards (?&?): IH H; try solve [eomg2];
        forwards (?&?): IH H0; try solve [eomg2];
    split~; applys S_and...
Qed.

Hint Constructors sub : core.

Theorem decidability : forall m A B,
    sub A m B \/ not (sub A m B).
Proof with (simpl in *; solve_false; jauto; eomg2; try solve [right; intros HF; auto_inv; inverts HF; simpl in *; solve_false]).
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


(* algorithm correctness *)
(* potential improvements *)
(* add try solve in eomg2 *)
(* mode in arrow_inv *)
(* better encode of aux functions *)
(* move rev_2 to top *)
