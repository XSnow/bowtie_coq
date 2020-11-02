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
   - (* and *)
     lets ([?|(?&?&?)]&[?|(?&?&?)]): IHA1;
       lets ([?|(?&?&?)]&[?|(?&?&?)]): IHA2;
       split*.
  - (* or *)
     lets ([?|(?&?&?)]&[?|(?&?&?)]): IHA1;
       lets ([?|(?&?&?)]&[?|(?&?&?)]): IHA2;
       split*.
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
Qed.

Hint Extern 0 =>
match goal with
| [ H: spl _ _ _ |- _ ] =>
  (lets (?&?): split_decrease_size H)
| [ H: splu _ _ _ |- _ ] =>
  (lets (?&?): splitu_decrease_size H)
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
  split; introv s1 s2...
  - inverts s1.
    + inverts* s2.
    + inverts s2...
    + inverts s2...
    + inverts s2...
    + inverts s2...
  - inverts s1.
    + inverts* s2.
    + inverts s2...
    + inverts s2...
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


Lemma andl_trans : forall A B B1 B2,
    spl B B1 B2 -> sub A B -> sub A B1.
Proof with (solve_false; split_unify; auto with sizeTypHd).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub...
  - (* or *)
    forwards*: IH H; eomg...
    forwards*: IH H0; eomg...
  - (* orl *)
    inverts Hspl.
    + forwards*: IH H; eomg...
    + eauto.
  - (* orr *)
    inverts Hspl.
    + eauto.
    + forwards*: IH H; eomg...
Qed.

Lemma andr_trans : forall A B B1 B2,
    spl B B1 B2 -> sub A B -> sub A B2.
Proof with (solve_false; split_unify; auto with sizeTypHd).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub...
  - (* or *)
    forwards*: IH H; eomg...
    forwards*: IH H0; eomg...
  - (* orl *)
    inverts Hspl.
    + forwards*: IH H; eomg...
    + eauto.
  - (* orr *)
    inverts Hspl.
    + eauto.
    + forwards*: IH H; eomg...
Qed.

Lemma andl : forall A B C D,
    spl D A B -> sub A C -> sub D C.
Proof with (solve_false; split_unify; auto with sizeTypHd).
  introv Hspl Hsub.
  indTypSize (size_typ C).
  lets ([Hi|(?&?&Hi)]&Hu'): ord_or_split C.
  - applys* S_andl.
  - assert (S1: sub A x) by applys* andl_trans Hi.
    assert (S2: sub A x0) by applys* andr_trans Hi.
    lets (?&?): split_decrease_size Hi.
    applys S_and Hi.
    applys IH S1 Hspl; eomg...
    applys IH S2 Hspl; eomg...
Qed.

Lemma andr : forall A B C D,
    spl D A B -> sub B C -> sub D C.
Proof with (solve_false; split_unify; auto with sizeTypHd).
  introv Hspl Hsub.
  indTypSize (size_typ C).
  lets ([Hi|(?&?&Hi)]&Hu'): ord_or_split C.
  - applys* S_andr.
  - assert (S1: sub B x) by applys* andl_trans Hi.
    assert (S2: sub B x0) by applys* andr_trans Hi.
    lets (?&?): split_decrease_size Hi.
    applys S_and Hi.
    applys IH S1 Hspl; eomg...
    applys IH S2 Hspl; eomg...
Qed.

(* andl, andr are used in refl proof *)
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
    inverts* Hi; inverts Hu.
    + applys~ S_or. applys~ S_orl... apply~ S_orr...
  - (* spl A *)
    applys~ S_and Hi...
    applys~ andl Hi...
    applys~ andr Hi...
Qed.

Hint Resolve andl andr refl : core.


(* T1\/T3 <| T1&T2 \/ T3 |> T2\/T3 *)
(* T1&T2 <: D *)
(* T3 <: D *)
(* A <: T1\/T3 *)
(* A <: T2\/T3 *)
Lemma split_union: forall A B C1 C2,
    spl (t_or A B) C1 C2 -> (sub A C1 /\ sub C2 A).
Proof.
  introv H.
Abort.

Lemma split_keep_ordu_l : forall A B C,
    ordu A -> spl A B C -> ordu B.
Proof.
  introv Hord Hspl.
  induction Hspl; inverts* Hord.
Qed.

Lemma split_keep_ordu_r : forall A B C,
    ordu A -> spl A B C -> ordu C.
Proof.
  introv Hord Hspl.
  induction Hspl; inverts* Hord.
Qed.

Hint Resolve split_keep_ordu_l split_keep_ordu_r : core.

(* Add ordu T -> because counter-example A\/B <: A\/B *)
Lemma and_meet_or : forall A B T,
    ordu T -> sub T (t_or A B) -> sub T A \/ sub T B.
Proof with (solve_false; split_unify; auto with sizeTypHd).
  introv Hu Hs.
  indTypSize (size_typ T + size_typ (t_or A B)).
  lets ([Hord|(?&?&Hspl)]&Hu'): ord_or_split (t_or A B).
  - inverts Hs...
    + lets (?&?): split_decrease_size H0.
      forwards* [?|?]: IH H1; eomg...
    + lets (?&?): split_decrease_size H0.
      forwards* [?|?]: IH H1; eomg...
  - inverts Hspl.
    + inverts~ Hs...
      *
        inverts H...
        lets (?&?): split_decrease_size H3.
        forwards~ [?|?]: IH H0; eomg...
        forwards~ [?|?]: IH H1; eomg...
        eauto.
    + inverts~ Hs... (* used when ord is not added in andl/r
      *
        lets (?&?): split_decrease_size H.
        forwards* [?|?]: IH H0; eomg...
      *
        lets (?&?): split_decrease_size H.
        forwards* [?|?]: IH H0; eomg... *)
      *
        inverts H...
        lets (?&?): split_decrease_size H4.
        forwards~ [?|?]: IH H0; eomg...
        forwards~ [?|?]: IH H2; eomg...
        eauto.
Qed.

(* transitivity *)
Hint Extern 0 =>
match goal with
| [ IH: forall _ , _ , H1: sub  ?A ?B , H2: sub ?B ?C |- sub ?A ?C ] =>
  (forwards: IH H1 H2; eomg)
end : sizeTypHd.

Hint Extern 0 =>
match goal with
| [ H: spl (t_and _ _) _ _ |- _ ] => (inverts H)
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
    applys andl H0...
  - (* andr *)
    applys andr H0...
  - (* or *)
    applys~ S_or...
  - (* orl *)
    inverts~ s2...
    +
      lets (Hi&[Hord|(?&?&Hspl)]): ord_or_split A.
      * forwards~: and_meet_or s1.
        inverts keep H1. (* spl or *)
      admit.
      admit.
      * admit.
    + admit.
    + applys~ S_and H0...
  - (* orr *)
    admit. (*
    inverts~ s2...
    + applys~ S_and H0... *)
  - (* arr *)
    inverts~ s2...
    + applys~ S_and H3...
  - (* and *)
    inverts~ s2; split_unify...
    + (* or *)
      (* left splitu property ? *)
      inverts H.
      *
    + applys~ S_and H2...
Qed.


Hint Immediate trans : core.

(* how could they be isomophic before splitu is removed? *)
Lemma split_iso: forall A B C,
    spl A B C -> sub A (t_and B C) /\ sub (t_and B C) A.
Proof with eauto.
  intros A B C H.
  split.
  - applys~ S_and. applys~ S_andl H. applys~ S_andr H.
  - applys S_and H. applys~ S_andl. applys~ S_andr.
Qed.

Lemma split_subl: forall A B C,
    spl A B C -> sub A B.
Proof.
  introv H.
  induction* H.
Qed.

Lemma split_subr: forall A B C,
    spl A B C -> sub A C.
Proof.
  introv H.
  induction* H.
Qed.

Hint Resolve split_subl split_subr : core.


Lemma split_subord_inv : forall A B C D,
    spl A B C -> ord D -> sub A D -> sub B D \/ sub C D.
Proof.
  introv Hspl Hord Hs. gen B C.
  induction* Hs; intros; split_unify; solve_false; iauto.
  - inverts Hspl.
    + forwards* [?|?]: IHHs1 H3.
    + forwards* [?|?]: IHHs2 H4.
  - inverts* Hord. forwards* [?|?]: IHHs Hspl.
  - inverts* Hord. forwards* [?|?]: IHHs Hspl.
  (* counter-example resolved in this version *)
  (* counter-example: A&B <: A&B \/ C *)
Qed.

Hint Constructors osub : core.

Lemma sub_fun : forall A B C D,
    sub B D -> sub C A -> sub (t_arrow A B) (t_arrow C D).
Proof with (auto with sizeTypHd).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets ([Hi2|(?&?&Hi2)]&Hu'2): ord_or_split (t_arrow C D).
  lets ([Hi1|(?&?&Hi1)]&Hu'1): ord_or_split (t_arrow A B).
  - applys~ S_arr.
  - (* subtype splittable ; supertype ordinary *)
    inverts keep Hi2.
    + (* split return type *)
      forwards* (?&?): split_decrease_size H4.
      applys~ S_andl Hi2;
        applys* IH.
        try applys* trans s;
        eomg.
    + (* split output type *)
      applys~ S_and Hi1;
        applys* IH;
        try applys* trans H;
        eomg.
  - (* supertype splittable *)
    inverts keep Hi2.
    + (* split return type *)
      forwards* (?&?): split_decrease_size H4.
      applys~ S_and Hi2;
        applys* IH;
        try applys* trans s;
        eomg.
    + (* split output type *)
      applys~ S_and Hi2;
        applys* IH;
        try applys* trans H;
        eomg.
Qed.

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
