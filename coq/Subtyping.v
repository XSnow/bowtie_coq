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

Lemma split_int : forall A B,
    spl t_int A B -> False.
Proof.
  intros. inverts H.
Qed.

Lemma split_top : forall A B,
    spl t_top A B -> False.
Proof.
  intros. inverts H.
Qed.

Lemma split_bot : forall A B,
    spl t_bot A B -> False.
Proof.
  intros. inverts H.
Qed.

Lemma splitu_int : forall A B,
    splu t_int A B -> False.
Proof.
  intros. inverts H.
Qed.

Lemma splitu_top : forall A B,
    splu t_top A B -> False.
Proof.
  intros. inverts H.
Qed.

Lemma splitu_bot : forall A B,
    splu t_bot A B -> False.
Proof.
  intros. inverts H.
Qed.

Hint Resolve split_ord_false split_int split_top split_bot splitu_int splitu_top splitu_bot: falseHd.

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

(* subtyping *)
Hint Constructors sub : core.

Lemma sub_spl_spl : forall A B C B' C' D,
    spl A B C -> spl A B' C' -> sub D B -> sub D C -> sub D B' /\ sub D C'.
Proof.
  introv Hsp1 Hsp2 S1 S2.
Admitted.

Lemma sub_spl : forall A B,
    sub A B ->
    (forall C D, spl B C D -> sub A C /\ sub A D) /\
    (forall C D, splu A C D -> sub C B /\ sub D B).
Proof.
  introv S.
  induction S; split; introv Sp; try solve_false; eauto.
  Abort.
  (*
    lets* (IHS1a&IHS1b): IHS1;
    lets* (IHS2a&IHS2b): IHS2.
  -
    inverts Sp; try solve_false.
    try solve [forwards*: IHS1b].

  -
    inverts Sp; try solve_false.
    + try solve [forwards*: IHS2b].
    + try solve [forwards*: IHS1a].
  - admit.
*)

Lemma sub_l_andl : forall A B C, sub A C -> sub (t_and A B) C.
Proof.
  introv s. induction* s; eauto.
Abort.

Lemma sub_l_andr : forall A B C, sub B C -> sub (t_and A B) C.
Proof.
  introv s. induction* s.
Abort.

Lemma sub_fun : forall A B C D,
    sub B D -> sub C A -> sub (t_arrow A B) (t_arrow C D).
Proof.
  introv s. induction* s.
Abort.

(*
Lemma refl : forall A, sub A A.
Proof.
  introv. inductionR A.
  - induction* H.
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
*)

Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

Ltac eomg :=
  pose proof (typ_size_lg_z);
  try omega; auto; simpl in *; try omega.

Lemma split_decrease_size: forall A B C,
    spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A
with splitu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with eomg.
  - introv H. clear split_decrease_size.
    induction* H...
    forwards* (?&?): splitu_decrease_size H...
  - introv H. clear splitu_decrease_size.
    induction* H...
    forwards* (?&?): split_decrease_size H...
Qed.

Hint Resolve splitu_decrease_size : sizeTypHd.

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

(* apply IH on every types *)
Hint Extern 0 =>
  match goal with
  | [ A : typ, IH : forall A, size_typ A < _ -> _ |-  _ ] => (forwards*: IH A; eomg)
  end : sizeTypHd.

Lemma refl : forall A, sub A A.
Proof with (auto with sizeTypHd).
  introv.
  indTypSize (size_typ A).
  lets ([Hi|(?&?&Hi)]&[Hu|(?&?&Hu)]): ord_or_split A.
  - (* A ord & ordu *)
    inverts* Hi; inverts* Hu.
    + (* arr *)
      applys S_arr...
  - (* ord A & splu A *)
    lets* (?&?): splitu_decrease_size Hu.
    inverts* Hi.
    + (* arr *)
      applys S_arr...
    + (* or *)
      applys S_or...
  - (* ordu A & spl A *)
    lets* (?&?): split_decrease_size Hi.
    inverts* Hu.
    + (* arr *)
      applys S_arr...
    + (* and *)
      applys S_and...
  - (* spl A & splu A *)
    lets* (?&?): splitu_decrease_size Hu.
    lets* (?&?): split_decrease_size Hi.
    inverts* Hi.
    + (* and *)
      applys S_and...
    + (* arr *)
      applys S_arr...
    + (* arr *)
      applys S_arr...
Qed.


Section sub_trans.

Lemma splitl_inv : forall A A1 A2 C,
    spl A A1 A2 -> sub A C -> ord C -> sub A1 C \/ sub A2 C.
Proof.
  intros A A1 A2 C s. gen C. induction s; intros. (*
  - applys* andl_inv.
  - inverts~ H; solve_false.
    lets~ [?|?]: (IHs D0).
  - inverts~ H; solve_false.
    lets~ [?|?]: (IHs D0). *)
Abort.

Hint Extern 0 =>
  match goal with
  | [ IH: forall _ , _ , H1: sub  ?A ?B , H2: sub ?B ?C |- sub ?A ?C ] =>
    (forwards: IH H1 H2; eomg)
  end : core.

Lemma trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof with eomg.
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts keep s1.
  - (* int *)
    inverts~ s2.
    + (* and *)
      applys~ S_and H.
    + (* or *)
      applys~ S_or H.
  - (* top *)
    inverts~ s2; try solve_false.
    + (* and *)
      lets (?&?): split_decrease_size H.
      applys~ S_and H;
        applys~ IH...
  - (* bot *)
    applys~ S_bot.
  - (* andl *)
    applys~ S_andl.
  - (* andr *)
    applys~ S_andr.
  - (* orl *)
    inverts~ s2; try solve_false.
    + lets (?&?): split_decrease_size H0.
      applys~ S_and H0.
    + (* or *)
      inverts H0.
      applys~ IH H H1...
  - (* orr *)
    inverts~ s2; try solve_false.
    + lets (?&?): split_decrease_size H0.
      applys~ S_and H0.
    + (* or *)
      inverts H0.
      applys~ IH H H2...
  - (* arr *)
    inverts~ s2; try solve_false.
    + (* and *)
      lets (?&?): split_decrease_size H1.
      applys~ S_and H1.
    + (* or *)
      inverts H1.
      admit. admit.
  - (* and *)
    inverts~ s2; try solve_false.
    + (* andl *)
      inverts H.
      applys~ IH H2...
    + (* andr *)
      inverts H.
      applys~ IH H2...
    + (* arrow *)
      admit.
    + (* and *)
      lets (?&?): split_decrease_size H2.
      applys~ S_and H2.
    + (* or *)
      admit.
  - (* or *)
    lets (?&?): splitu_decrease_size H.
    applys~ S_or H.
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
