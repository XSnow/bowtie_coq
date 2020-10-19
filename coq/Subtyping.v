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
    lets* ([?|(?&?&?)]&?): IHA2.
    + (* ord A2 in A1->A2 *)
      lets* (?&[?|(?&?&?)]): IHA1.
  - (* ordu VS splu *)
    lets* (?&[?|(?&?&?)]): IHA2.
    + (* ordu A2 in A1->A2 *)
      lets* ([?|(?&?&?)]&?): IHA1.
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

(*
(* Cannot guess decreasing argument of fix. *)
Lemma split_unique : forall T A1 A2 B1 B2,
    spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2
with splitu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with solve_false.
  + introv s1 s2. gen A2 B2.
    induction s1; intros.
  - clear split_unique splitu_unique. inverts* s2.
  - clear splitu_unique.
    inverts s2...
    forwards*: split_unique s1 H3.
  - clear split_unique.
    inverts s2...
    forwards* (?&?): splitu_unique H0 H6.
    subst*.

  + introv s1 s2. gen A2 B2.
    induction s1; intros.
  - clear split_unique splitu_unique.
    inverts* s2.
  - clear split_unique.
    inverts s2...
    forwards*: splitu_unique s1 H3.
  - clear splitu_unique.
    inverts s2...
    forwards* (?&?): split_unique H0 H6.
    subst*.
Qed.
*)


(* subtyping *)
Hint Constructors sub : core.

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
    forwards* (?&?): splitu_decrease_size H0...
  - introv H. clear splitu_decrease_size.
    induction* H...
    forwards* (?&?): split_decrease_size H0...
Qed.

Hint Extern 0 =>
match goal with
| [ H: splu _ _ _ |- _ ] =>
  (lets (?&?): splitu_decrease_size H)
| [ H: spl _ _ _ |- _ ] =>
  (lets (?&?): split_decrease_size H)
end : sizeTypHd.

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].


(* split/u is unique *)
Hint Extern 0 =>
  match goal with
  | [ IH: forall A, size_typ A < _ -> _, A: typ, Hsp: spl ?A _  _|- _ ] =>
    (forwards (?&?): IH A; eomg)
  | [ IH: forall A, size_typ A < _ -> _, A: typ, Hsp: splu ?A _  _|- _ ] =>
    (forwards (?&?): IH A; eomg)
  end : sizeTypHd.

Hint Extern 0 =>
  match goal with
  | [ T: typ, B: typ, B2: typ, H : forall A B C D, spl ?T _ _  -> _, Hsp: spl ?T _  _, Hsp2: spl ?T _  _ |- _ ] =>
    (forwards (?&?): H Hsp Hsp2; subst~)
  | [ T: typ, B: typ, B2: typ, H : forall A B C D, splu ?T _ _  -> _, Hsp: splu ?T _  _, Hsp2: splu ?T _  _ |- _ ] =>
    (forwards (?&?): H Hsp Hsp2; subst~)
  end : sizeTypHd.

Lemma split_unique_aux : forall T,
    (forall A1 A2 B1 B2,
        spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2)
    /\ (forall A1 A2 B1 B2,
           splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2).
Proof with (solve_false; auto with sizeTypHd).
  introv.
  indTypSize (size_typ T).
  split; introv s1 s2.
  + inverts s1.
    - inverts* s2.
    - inverts s2...
    - inverts s2...
  + inverts s1.
    - inverts* s2.
    - inverts s2...
    - inverts s2...
Qed.

Lemma split_unique : forall T A1 A2 B1 B2,
    spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof.
  intro T.
  forwards~ (?&?): split_unique_aux T.
Qed.

Lemma splitu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof.
  intro T.
  forwards~ (?&?): split_unique_aux T.
Qed.

Hint Resolve split_unique splitu_unique : core.

Ltac split_unify :=
  repeat match goal with
  | [ H1: spl ?A _ _ , H2: spl ?A _ _ |- _ ] =>
           (forwards (?&?): split_unique H1 H2;
            subst; clear H2)
  | [ H1: splu ?A _ _ , H2: splu ?A _ _ |- _ ] =>
           (forwards (?&?): splitu_unique H1 H2;
            subst; clear H2)
         end;
  solve_false.

(* reflexivity *)
Hint Extern 0 =>
  match goal with
  | [ IH : forall A, size_typ A < _ -> _ |- sub ?A ?A ] => (forwards: IH A; eomg)
  end : sizeTypHd.

Lemma refl : forall A, sub A A.
Proof with (auto with sizeTypHd).
  introv.
  indTypSize (size_typ A).
  lets ([Hi|(?&?&Hi)]&Hu'): ord_or_split A.
  lets [Hu|(?&?&Hu)]: Hu'. clear Hu'.
  - (* ord A & ordu A *)
    inverts* Hi; inverts* Hu.
    + (* arr *)
      applys S_arr...
  - (* ord A & splu A *)
    inverts* Hi.
    + applys~ S_arr...
    + applys~ S_or. applys~ S_orl... apply~ S_orr...
  - (* spl A *)
    applys~ S_and Hi...
    applys~ S_andl Hi...
    applys~ S_andr Hi...
Qed.

Hint Resolve refl : core.

(* transitivity *)
Hint Extern 0 =>
match goal with
| [ IH: forall _ , _ , H1: sub  ?A ?B , H2: sub ?B ?C |- sub ?A ?C ] =>
  (forwards: IH H1 H2; eomg)
end : sizeTypHd.

Hint Extern 0 =>
match goal with
| [ H: spl (t_and _ _) _ _ |- _ ] => (inverts H)
| [ H: splu (t_or _ _) _ _ |- _ ] => (inverts H)
end : sizeTypHd.

Lemma trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof with (solve_false; auto with sizeTypHd).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts keep s1.
  - (* int *)
    inverts~ s2...
    + applys~ S_and H.
  - (* top *)
    inverts~ s2...
    + applys~ S_and H...
  - (* bot *)
    applys~ S_bot.
  - (* andl *)
    applys~ S_andl H...
  - (* andr *)
    applys~ S_andr H...
  - (* or *)
    applys~ S_or...
  - (* orl *)
    inverts~ s2...
    + applys~ S_and H0...
  - (* orr *)
    inverts~ s2...
    + applys~ S_and H0...
  - (* arr *)
    inverts~ s2...
    + applys~ S_and H3...
  - (* and *)
    inverts~ s2; split_unify...
    + applys~ S_and H2...
Qed.


Hint Immediate trans : core.

Lemma split_sub: forall A B C,
    spl A B C -> sub A (t_and B C) /\ sub (t_and B C) A.
Proof with eauto.
  intros A B C H.
  split.
  - applys~ S_and. applys~ S_andl H. applys~ S_andr H.
  - applys S_and H. applys~ S_andl. applys~ S_andr.
Qed.

Hint Constructors osub : core.

(* declarative subtyping equivalence *)
Theorem dsub_eq: forall A B,
    osub A B <-> sub A B.
Proof.
  split; introv H.
  - induction* H.
    + (* arrow *)
      clear H H0. indTypSize (size_typ (t_arrow A C) + size_typ (t_arrow B D)).
      lets ([Hi2|(?&?&Hi2)]&Hu'2): ord_or_split (t_arrow B D).
      lets ([Hi1|(?&?&Hi1)]&Hu'1): ord_or_split (t_arrow A C).
      * (* ord, ord *)
        applys~ S_arr.
      * (* ord, spl *)
        admit.
      * applys~ S_and Hi2; admit.
    + indTypSize (size_typ C).
      lets ([Hi2|(?&?&Hi2)]&Hu'2): ord_or_split C.
      * applys~ S_and. applys~ S_andl. applys~ S_andr.
      * lets (?&?): split_decrease_size Hi2.
        applys S_and.
        applys~ Sp_arrow Hi2.
        ** forwards* Hs: IH A x B; eomg. applys~ trans Hs.
           applys* S_and.
        ** forwards* Hs: IH A x0 B; eomg. applys~ trans Hs.
           applys* S_and.
  - induction~ H.
    + (* and l*)
      gen C. inductions H; intros.
      * applys~ OS_trans IHsub.
      * Abort.


Lemma sub_fun : forall A B C D,
    sub B D -> sub C A -> sub (t_arrow A B) (t_arrow C D).
Abort.

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
