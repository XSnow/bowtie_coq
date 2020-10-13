Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Export syntax_ott.
Require Import rules_inf.
Require Import Omega.


(* ordinary & splittable types *)
Hint Constructors ord spl ordu splu : core.

Lemma ord_or_split: forall A,
    (ord A \/ exists B C, spl A B C) /\
    (ordu A \/ exists B C, splu A B C).
Proof.
  intros A. induction* A.
  split.
  - (* ord VS spl *)
    lets* (?&[?|(?&?&?)]): IHA1.
    + (* ordu A1 in A1->A2 *)
      lets* ([?|(?&?&?)]&?): IHA2.
  - (* ordu VS splu *)
    lets* ([?|(?&?&?)]&?): IHA1.
    + (* ord A1 in A1->A2 *)
      lets* (?&[?|(?&?&?)]): IHA2.
Qed.

Lemma split_ord_false : forall A B C,
    (spl A B C /\ ord A) \/ (splu A B C /\ ordu A) -> False.
Proof.
  intro A.
  induction A; intros B C [(s&o) | (s&o) ];
    try solve [inverts* s];
    try solve [inverts* o];
    inverts o;
    inverts* s.
Qed.

Hint Resolve split_ord_false : falseHd.

Ltac solve_false := try intro; try solve [false; eauto with falseHd].

Ltac destructT A := lets [?|(?&?&?)]: (ord_or_split A).


Ltac split_unify :=
  repeat match goal with
  | [ H: spl (t_and _ _) _ _ |- _ ] => inverts H
  | [ H: spl (t_arrow _ _) _ _ |- _ ] => inverts H
(*  | [ H: spl (t_rcd _ _) _ _ |- _ ] => inverts H *)
         end;
  auto.


(* R *)
Inductive R : typ -> Prop :=
| Rord : forall A, ord A -> R A
| Rspl : forall B C A, spl A B C -> R B -> R C -> R A.

Inductive Ru : typ -> Prop :=
| Ruord : forall A, ordu A -> Ru A
| Ruspl : forall B C A, splu A B C -> Ru B -> Ru C -> Ru A.

Hint Constructors R Ru : core.


Lemma decideR : forall A, R A /\ Ru A.
Proof.
  introv. induction* A.
  - destruct IHA1; destruct IHA2. admit.
Admitted.

Ltac inductionR A := assert (r: R A) by apply (decideR A); induction r.


(* topLike *)
Lemma topLike_arrow_inv : forall A B,
    topLike (t_arrow A B) -> topLike B.
Proof.
  introv H. inverts~ H.
Qed.

Lemma topLike_and_l_inv : forall A B,
    topLike (t_and A B) -> topLike A.
Proof.
  introv H. inverts~ H.
Qed.

Lemma topLike_and_r_inv : forall A B,
    topLike (t_and A B) -> topLike B.
Proof.
  introv H. inverts~ H.
Qed.

Lemma topLike_or_inv : forall A B,
    topLike (t_or A B) -> topLike A \/ topLike B.
Proof.
  introv H. inverts~ H.
Qed.

Hint Immediate topLike_arrow_inv topLike_and_l_inv topLike_and_r_inv topLike_or_inv: core.

Hint Constructors topLike: core.

Lemma topLike_combine: forall A B C,
    spl C A B -> topLike A -> topLike B -> topLike C.
Proof.
  introv s tl1 tl2. induction* s.
Qed.

Lemma topLike_combine_union: forall A B C,
    splu C A B -> topLike A \/ topLike B -> topLike C.
Proof.
  introv s [tl1 | tl2]; induction* s.
Qed.

Lemma topLike_split_l: forall A B C,
    topLike C -> spl C A B -> topLike A.
Proof.
  introv tl s. induction* s.
Qed.

Lemma topLike_split_r: forall A B C,
    topLike C -> spl C A B -> topLike B.
Proof.
  introv tl s. induction* s.
Qed.

Lemma topLike_split_union: forall A B C,
    topLike C -> splu C A B -> topLike A \/ topLike B.
Proof.
  introv tl s. induction* s.
  inverts* tl.
Qed.

Hint Immediate topLike_combine topLike_combine_union topLike_split_l topLike_split_r topLike_split_union : core.

Hint Constructors sub : core.

(* topLike specification *)
Lemma topLike_super_top: forall A,
    topLike A <-> sub t_top A.
Proof with eauto.
  split; intros H.
  - inductionR A; iauto.
  - inductionR A; iauto.
Abort.

(* Hint Immediate topLike_super_top : core. *)


(* subtyping *)
Lemma sub_l_andl : forall A B C, sub A C -> sub (t_and A B) C.
Proof.
  introv s. induction* s.
Qed.

Lemma sub_l_andr : forall A B C, sub B C -> sub (t_and A B) C.
Proof.
  introv s. induction* s.
Qed.

Lemma sub_fun : forall A B C D,
    sub B D -> sub C A -> sub (t_arrow A B) (t_arrow C D).
Proof.
  introv s. induction* s.
Qed.

Lemma sub_rcd : forall A B l,
    sub A B -> sub (t_rcd l A) (t_rcd l B).
Proof.
  introv H.
  induction* H.
Defined.

Hint Resolve sub_l_andl sub_l_andr sub_fun sub_rcd: core.


Lemma refl : forall A, sub A A.
Proof.
  introv. induction* A.
Qed.

Hint Resolve refl : core.


Lemma spl_sub_l : forall A B C,
    spl A B C -> sub A B.
Proof.
  introv H. induction* H.
Qed.

Lemma spl_sub_r : forall A B C,
    spl A B C -> sub A C.
Proof.
  introv H. induction* H.
Qed.

Lemma sub_r_spl_l : forall T A B C,
    sub T A -> spl A B C -> sub T B.
Proof.
  introv Hsub Hspl.
  inverts Hsub; solve_false.
  split_unify.
Qed.

Lemma sub_r_spl_r : forall T A B C,
    sub T A -> spl A B C -> sub T C.
Proof.
  introv Hsub Hspl.
  inverts Hsub; solve_false.
  split_unify.
Qed.

Hint Immediate spl_sub_l spl_sub_r sub_r_spl_l sub_r_spl_r : core.

Example sub_spl_demo : forall A B C,
    sub t_top A -> spl A B C -> sub A B /\ sub A C /\ sub t_top B /\ sub t_top C.
Proof.
  jauto.
Qed.


Lemma andr_l_inv : forall A B C,
    sub A (t_and B C) -> sub A B.
Proof.
  introv H. inductions H ; eauto; solve_false.
  split_unify.
Qed.

Lemma andr_r_inv : forall A B C,
    sub A (t_and B C) -> sub A C.
Proof.
  introv H. inductions H ; eauto; solve_false.
  split_unify.
Qed.

Lemma andl_inv : forall A B C,
    sub (t_and A B) C -> ord C -> sub A C \/ sub B C.
Proof.
  introv s o. inductions s; eauto; solve_false.
Qed.

Hint Immediate andr_l_inv andr_r_inv andl_inv : core.


Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

Lemma exp_size_lg_z : forall e, size_exp e > 0.
Proof.
  introv.
  pose proof (size_exp_min) e.
  inverts~ H.
Qed.

Ltac eomg :=
  pose proof (typ_size_lg_z);
  pose proof (exp_size_lg_z);
  try omega; auto; simpl in *; try omega.


Lemma split_decrease_size: forall A B C,
    spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof.
  introv H. induction* H; eomg.
Qed.

Lemma topLike_super_any: forall T A,
    topLike T -> sub A T.
Proof.
  introv H. assert (exists i, (size_typ T) < i) by eauto.
  inverts H0. gen T.
  induction x; intros; auto.
  - inverts H1.
  -
    destructT T; eauto.
    +
      forwards (?&?): split_decrease_size H0.
      forwards*: IHx x0. eomg.
      forwards*: IHx x1. eomg.
Qed.

Hint Immediate topLike_super_any : core.


Ltac wapply H := eapply H; try eassumption.

Hint Extern 0 => match goal with
                 | [ H1: topLike (t_arrow _ ?D), H2: ~topLike ?D |- False ] => (
                     inverts H1;
                       contradiction)
                 | [ H: topLike t_int |- False ] => (
                     inverts H )
                 | [ H1: ord ?A, H2: spl (t_arrow _ ?A) _ _ |- False ] => (
                     inverts H2;
                       auto with falseHd)
                 end : falseHd.


Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].


Section sub_trans.

Lemma splitl_inv : forall A A1 A2 C,
    spl A A1 A2 -> sub A C -> ord C -> sub A1 C \/ sub A2 C.
Proof.
  intros A A1 A2 C s. gen C. induction s; intros.
  - applys* andl_inv.
  - inverts~ H; solve_false.
    lets~ [?|?]: (IHs D0).
  - inverts~ H; solve_false.
    lets~ [?|?]: (IHs D0).
Qed.

Hint Extern 0 =>
  match goal with
  | [ IH: forall _ , _ , H1: sub  ?A ?B , H2: sub ?B ?C |- sub ?A ?C ] =>
    (forwards: IH H1 H2; eomg)
  end : core.

Lemma trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof.
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  destructT C.
  - (* ord C *)
    destructT B.
    + (* ord B *)
      inverts keep s2 as s2_1 s2_2 s2_3;
        inverts s1 as s1_1 s1_2 s1_3; solve_false; auto.
      * (* topLike B *)
        applys~ S_top. applys TL_arr. applys topLike_super_top.
        inverts s1_2. applys* IH C0. eomg.
      *
        applys~ S_top. applys TL_rcd. applys topLike_super_top.
        inverts s1_2. applys* IH C0. eomg.
    + (* spl B x x0 *)
      (* splitl_inv turns B into x or x0 *)
      lets (?&?): split_decrease_size B. eauto.
      forwards~ [s2' |s2']: splitl_inv s2. eauto.
      applys* IH s2'. eomg.
      applys* IH s2'. eomg.
  - (* spl C x x0 *)
    (* inversion turns C into x and x0 *)
    lets (?&?): split_decrease_size C. eauto.
    forwards~ g1: IH s1 x. eauto. eomg.
    forwards~ g2: IH s1 x0. eauto. eomg.
    applys~ S_and H.
Qed.

End sub_trans.


Hint Immediate trans : core.

Lemma split_sub: forall A B C,
    spl A B C -> sub A (t_and B C) /\ sub (t_and B C) A.
Proof with eauto.
  intros A B C H.
  split.
  - lets~: spl_sub_l H. lets~: spl_sub_r H.
    apply~ S_and...
  - induction H...
Qed.


Hint Extern 0 => match goal with
                 | [ |- sub (t_and ?A ?B) ?A ] => apply sub_l_andl
                 | [ |- sub (t_and ?A ?B) ?B ] => apply sub_l_andr
                 | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?B ] => eapply (trans _ (t_and B C))
                 | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?C ] => eapply (trans _ (t_and B C))
                 end : core.


Ltac auto_sub :=
  repeat (auto ;
          match goal with
          | [ |- sub (t_and ?C ?D) (t_and ?A ?B) ] => (eapply S_and; try apply Sp_and)
          | [ |- sub (t_and (t_arrow ?A ?B) (t_arrow ?A ?C)) (t_arrow ?A (t_and ?B ?C)) ] => (eapply S_and)
          | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] =>
            (forwards: trans H1 H2; auto)
          | [ H: sub t_top ?A |- sub _ ?A ] =>
            (apply topLike_super_top in H; apply S_top; auto)
          | [ H: topLike ?A |- sub _ (t_arrow _ ?A) ] =>
            (apply TL_arr in H; apply S_top; auto)

          | [ H1: spl ?A ?B ?C, H2: ord ?D, H3: sub ?A ?D |- _ ] => (
              forwards [?|?]: splitl_inv H1 H2 H3;
              clear H3)
          | [ H1: spl ?A ?B ?C |- _ ] => (
              forwards : split_sub H1;
              forwards : spl_sub_l H1;
              forwards : spl_sub_r H1;
              clear H1)
          | [ |- sub (t_arrow ?A ?B) (t_arrow ?C ?D) ] => apply sub_fun
          | [ H1: sub ?A ?B |- sub ?A ?C ] =>
            assert ( sub B C ) by auto
          end).



(* declarative subtyping equivalence *)
Theorem dsub_eq: forall A B,
    dsub A B <-> sub A B.
Proof.
  split; introv H;
  induction* H.
Qed.
