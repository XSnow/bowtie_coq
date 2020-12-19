Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Export syntax_ott.
Require Import rules_inf.
Require Import Omega.


(* ordinary & splittable types *)
Hint Constructors ord spl : core.

Lemma ord_or_split: forall m A,
    ord m A \/ exists B C, spl m A B C.
Proof.
  intros. gen m. induction* A; intros.
  - (* arrow *)
    destruct m.
    + lets* [?|(?&?&?)]: IHA2.
      (* ord A2 in A1->A2 *)
      lets* [?|(?&?&?)]: IHA1.
    + left*.
  - (* and *)
    destruct m.
    + right*. exists*. applys* Sp_and.
    + lets [?|(?&?&?)]: IHA1 m_super;
        lets [?|(?&?&?)]: IHA2 m_super.
      left. constructor*.
      right*. exists*. applys* Sp_orr.
      right*. exists*. applys* Sp_orl.
      right*. exists*. applys* Sp_orl.
  - (* or *)
    destruct m.
    + lets [?|(?&?&?)]: IHA1 m_sub;
        lets [?|(?&?&?)]: IHA2 m_sub.
      left. constructor*.
      right*. exists*. applys* Sp_orr.
      right*. exists*. applys* Sp_orl.
      right*. exists*. applys* Sp_orl.
    + right*. exists*. applys* Sp_and.
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

Hint Resolve choose_false_int choose_false_top choose_false_bot choose_false_arrow choose_and_sub choose_or_super and_or_mismatch choose_typebymode_false: falseHd.

Lemma split_ord_false : forall m A B C,
    (spl m A B C /\ ord m A)  -> False.
Proof.
  introv. gen m B C.
  induction A; intros m B C (s&o);
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

Lemma flip_eqv_false : forall m,
    m = flipmode m -> False.
Proof.
  intros.
  destruct m; inverts H.
Qed.

Hint Resolve flip_eqv_false : falseHd.

Ltac solve_false := try intro; try solve [false; eauto with falseHd].

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

Hint Rewrite flip_flip cal_top cal_bot : core.

(* Subtyping *)
Hint Constructors sub : core.

Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

Lemma typ_size_choose_l : forall m A B,
    size_typ A < size_typ (choose m A B).
Proof.
  intros.
  destruct m; simpl in *; omega.
Qed.

Lemma typ_size_choose_r : forall m A B,
    size_typ B < size_typ (choose m A B).
Proof.
  intros.
  destruct m; simpl in *; omega.
Qed.

Hint Resolve typ_size_choose_l typ_size_choose_r : core.

Ltac eomg :=
  pose proof (typ_size_lg_z);
  simpl in *; try omega.

Lemma split_decrease_size: forall m A B C,
    spl m A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with eomg.
  - introv H.
    induction* H...
    destruct m; eauto...
    destruct m; eauto...
Qed.

Ltac spl_size :=
  repeat match goal with
  | [ H: spl _ _ _ _ |- _ ] =>
    (lets (?&?): split_decrease_size H; clear H)
  end.

(* enhanced eomg with split_decrease_size *)
Ltac eomg2 :=
  pose proof (typ_size_lg_z);
  try spl_size; simpl in *; try omega.

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].

(* split/u is unique *)
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

Hint Extern 0 =>
match goal with
| [ IH: forall A, size_typ A < _ -> _, A: typ, Hsp: spl ?m ?T _  _, Hsp2: spl ?m ?T _  _ |- _ ] =>
  (forwards (?&?): IH Hsp Hsp2; eomg2; subst~)
end : split_unique.

Lemma split_unique : forall m T A1 A2 B1 B2,
    spl m T A1 B1 -> spl m T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (solve_false; auto with split_unique).
  introv. gen m.
  indTypSize (size_typ T).
  inverts H; try destruct m; inverts H0...
  Unshelve.
  econstructor. eauto.
Qed.

(* replace solve_false *)
Ltac auto_unify :=
  repeat match goal with
         | [ H1: choose _ _ _ = choose _ _ _ |- _ ] =>
           (forwards (?&?&?): choose_unique H1;
            subst; clear H1)
         | [ H1: spl ?m ?A  _ _ , H2: spl ?m ?A _ _ |- _ ] =>
           (forwards (?&?): split_unique H1 H2;
            subst; clear H2)
         | [ H1: spl m_sub (t_and _ _) _ _ |- _ ] =>
           inverts H1
         | [ H1: spl m_super (t_or _ _) _ _ |- _ ] =>
           inverts H1
         | [ H1: spl ?m (choose ?m _ _) _ _ |- _ ] =>
           (forwards (?&?): split_choose H1;
            subst; clear H1)
         end;
  try rewrite flip_flip in *;
  try rewrite cal_top in *;
  try rewrite cal_bot in *;
  solve_false.

Ltac aauto := try eassumption.


Notation "A <: B" := (sub A m_sub B) (at level 80, right associativity).
Notation "A :> B" := (sub A m_super B) (at level 80, right associativity).


Lemma flip_rev : forall m1 m2,
    m1 = flipmode m2 -> m2 = flipmode m1.
Proof.
  intros.
  destruct m2; subst; eauto.
Qed.


(* flip m and remember it as m' *)
Ltac flip m:=
  remember (flipmode m) as m' eqn:Heqm'; apply flip_rev in Heqm'; subst.


Lemma rev : forall A m B,
    sub A m B -> sub B (flipmode m) A.
Proof.
  intros.
  induction H; try solve [flip mode5; constructor*].
  - flip mode5.
    applys* S_orl.
  - flip mode5.
    applys* S_orr.
  - flip mode5.
    applys* S_andl.
  - flip mode5.
    applys* S_andr.
  - flip mode5.
    applys* S_and.
  - flip mode5.
    applys* S_or.
Qed.

Lemma rev2 : forall A B,
    A <: B <-> B :> A.
Proof.
  split; intro H;
    apply rev in H; simpl in H; auto.
Qed.

Hint Immediate rev rev2 : core.

(* reflexivity *)
Hint Extern 0 =>
match goal with
| [ IH : forall A, size_typ A < _ -> _ |- sub ?A _ ?A ] => (forwards*: IH A; eomg2)
end : refl.

Lemma refl : forall A m, sub A m A.
Proof with (auto_unify; simpl in *; auto with refl).
  introv. gen m.
  indTypSize (size_typ A).
  lets [Hi|(?&?&Hi)]: ord_or_split m A.
  lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
  - (* ord A & ordu A *)
    destruct A; destruct m...
    + lets: S_top t_top m_sub...
    + lets: S_bot m_super t_top...
    + lets: S_bot m_sub t_bot...
    + lets: S_top t_bot m_super...
  - (* ord A & splu A *)
    applys S_or; aauto.
    applys S_orl Hu...
    applys S_orr Hu...
  (* flip m. applys* split_sub_flip_l.
    flip m. applys* split_sub_flip_r. *)
  - (* spl A *)
    applys~ S_and Hi...
    applys S_andl Hi...
    applys S_andr Hi...
    (* applys* split_sub_l.
       applys* split_sub_r. *)
    Unshelve. econstructor. eauto.
Qed.

Hint Resolve refl : core.

Lemma split_keep_ord_l : forall m A B C,
    ord (flipmode m) A -> spl m A B C -> ord (flipmode m) B.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Lemma split_keep_ord_r : forall m A B C,
    ord (flipmode m) A -> spl m A B C -> ord (flipmode m) C.
Proof.
  introv Hord Hspl.
  inductions Hspl; try destruct m; inverts* Hord.
Qed.

Hint Resolve split_keep_ord_l split_keep_ord_r : core.


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
    + flip m. simpl in H. inverts H.
    + flip m. simpl in H. inverts H.
    + auto_unify. applys S_andl. eauto.
      applys IH H1... destruct m; eomg2.
    + auto_unify. applys~ S_andl.
  - inverts Hspl...
    + inverts H...
      * applys S_andr... applys IH H0... eauto. destruct m; eomg2.
      * applys IH H0... eauto. destruct m; eomg2.
    + flip m. simpl in H. inverts H.
    + flip m. simpl in H. inverts H.
    + auto_unify. applys~ S_andr.
    + auto_unify. applys S_andr. eauto.
      applys IH H2... destruct m; eomg2.
  - inverts keep Hspl...
    + applys S_orl... applys IH H0... eauto. destruct m; eomg2.
    + flip m. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + flip m. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + applys S_orl. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orl. applys* IH H0... eomg2.
  - inverts keep Hspl...
    + applys S_orr... applys IH H0... eauto. destruct m; eomg2.
    + flip m. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + flip m. simpl in *. applys* S_orr. applys* IH H0... eomg2.
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
    + flip m. simpl in H. inverts H.
    + flip m. simpl in H. inverts H.
    + auto_unify. applys S_andl. eauto.
      applys IH H1... destruct m; eomg2.
    + auto_unify. applys~ S_andl.
  - inverts Hspl...
    + inverts H...
      * applys IH H0... eauto. destruct m; eomg2.
      * applys S_andr... applys IH H0... eauto. destruct m; eomg2.
    + flip m. simpl in H. inverts H.
    + flip m. simpl in H. inverts H.
    + auto_unify. applys~ S_andr.
    + auto_unify. applys S_andr. eauto.
      applys IH H2... destruct m; eomg2.
  - inverts keep Hspl...
    + applys S_orl... applys IH H0... eauto. destruct m; eomg2.
    + flip m. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + flip m. simpl in *. applys* S_orl. applys* IH H0... eomg2.
    + applys S_orl. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orl. applys* IH H0... eomg2.
  - inverts keep Hspl...
    + applys S_orr... applys IH H0... eauto. destruct m; eomg2.
    + flip m. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + flip m. simpl in *. applys* S_orr. applys* IH H0... eomg2.
    + applys S_orr. eauto.
      applys IH Hspl... destruct m; eomg2.
    + applys* S_orr. applys* IH H0... eomg2.
  - inverts Hspl...
  - applys* S_and. applys* IH H0... eomg2. applys* IH Hspl... eomg2.
Qed.

Hint Resolve orl_trans orr_trans : core.

(* Add ordu T -> because counter-example A\/B <: A\/B *)
(* previous name: and_meet_or *)
Lemma or_inv : forall m A B T,
    ord (flipmode m) T -> sub T m (choose (flipmode m) A B) -> sub T m A \/ sub T m B.
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

(* the following two lemmas should be equivalent to the above two
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
*)

(* transitivity *)
Hint Extern 0 =>
match goal with
| [ IH: forall _ , _ , H1: sub ?A ?m ?B , H2: sub ?B ?m ?C |- sub ?A ?m ?C ] =>
  (forwards: IH H1 H2; eomg2)
end : trans.

Lemma trans : forall m A B C, sub A m B -> sub B m C -> sub A m C.
Proof with (auto_unify; aauto; auto with trans).
  introv s1 s2. gen m.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts keep s1.
  - (* int *)
    inverts~ s2...
    + applys~ S_orl H.
    + applys~ S_orr H.
    + applys~ S_and H.
  - (* top *)
    inverts~ s2; try solve [destruct m; auto_unify]...
    + applys~ S_orl H...
    + applys~ S_orr H...
    + applys~ S_and H...
  - (* bot *)
    applys~ S_bot.
  - (* andl *)
    applys S_andl H...
  - (* andr *)
    applys S_andr H...
  - (* orl *)
    assert (sub A0 m C). applys* orl_trans s2...
    applys IH... eomg2.
  - (* orr *)
    assert (sub B0 m C). applys* orr_trans s2...
    applys IH... eomg2.
  - (* arr *)
    inverts~ s2; try solve [destruct m; auto_unify]...
    + applys~ S_orl H3...
    + applys~ S_orr H3...
    (* additional ordinary constraints save this case
    + (* get splitted *)
      inverts H5...
      * flip m. simpl in *.
        admit.
      * flip m. simpl in *.
        admit. *)
    + applys~ S_and H3...
  - (* or *)
    applys~ S_or H...
  - (* and *)
    inverts keep s2...
    + applys~ S_orl H2...
    + applys~ S_orr H2...
    + inverts H...
    + lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
      * forwards* [Res|Res]: splu_inv s1;
          applys~ IH Res; eomg2.
      * applys S_or Hu.
        assert (sub x m B). applys* orl_trans s1...
        applys IH... eomg2.
        assert (sub x0 m B). applys* orr_trans s1...
        applys IH... eomg2.
    + applys~ S_and H2...
Qed.

Hint Immediate trans : core.


(* how could they be isomophic before splitu is removed? *)
Lemma split_iso: forall m A B C,
    spl m A B C -> sub A m (choose m B C) /\ sub (choose m B C) m A.
Proof with eauto.
  introv H.
  split.
  - applys S_and...
  - applys S_and H. applys~ S_andl. applys~ S_andr.
Qed.

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

Lemma split_two_way : forall m T A1 A2 B1 B2,
    spl m T A1 A2 -> spl (flipmode m) T B1 B2 ->
    sub A1 (flipmode m) B1 /\ sub A1 (flipmode m) B2 /\ sub B1 m A2 /\ sub B2 m A2.
Proof with (aauto; simpl in *; auto_unify).
  introv Hsp1 Hsp2.
  - inverts Hsp1.
    +  (* m:=sub A1:=I1\/C1 A2:=I2\/C2 B1:=I1&(I2\/C2) B2:=C1&(I2\/C2) *)
      inverts Hsp2...
      * repeat split.
        ** applys S_orl... eauto. forwards*: split_sub_l H1.
        ** applys S_orl... eauto. forwards*: split_sub_r H1.
        ** applys* split_sub_r.
        ** applys* split_sub_r.
      * repeat split.
        ** applys* split_sub_flip_l.
        ** applys* split_sub_flip_l.
        ** applys S_andr... eauto. flip m. applys split_sub_flip_l H2...
        ** applys S_andr... eauto. flip m. applys split_sub_flip_r H2...
    + (* arrow for sub only *)
      inverts Hsp2...
    + (* arrow for sub only *)
      inverts Hsp2...
    +
      inverts Hsp2...
      * repeat split.
        ** applys S_orl... eauto. applys* split_sub_l.
        ** applys* split_sub_r.
        ** applys S_orl... eauto. applys* split_sub_r.
        ** flip m. applys* split_sub_flip_r.
    + (* T = A\/B *)
      inverts Hsp2...
      * repeat split.
        ** applys* split_sub_l.
        ** applys S_orl... eauto. applys* split_sub_r.
        ** flip m. applys* split_sub_flip_l.
        ** applys S_orr... eauto. applys* split_sub_r.
Qed.


Hint Resolve split_sub_l split_sub_r split_sub_flip_l split_sub_flip_r : core.

(*
Lemma split_subord_inv : forall A B C D,
    spl A B C -> ord D -> sub A D -> sub B D \/ sub C D.
Proof with (aauto; eauto).
  introv Hspl Hord Hs. gen B C.
  induction Hs; intros; unify; intuition.
  - forwards [?|?]: IHHs...
  - forwards [?|?]: IHHs...
    (* counter-example resolved in this version *)
    (* counter-example: A&B <: A&B \/ C *)
Qed.

Lemma splitu_ordusub_inv : forall A B C D,
    splu A B C -> ordu D -> sub D A -> sub D B \/ sub D C.
Proof with (aauto; eauto).
  introv Hspl Hord Hs. gen B C.
  induction Hs; intros; unify; intuition.
  - forwards [?|?]: IHHs...
  - forwards [?|?]: IHHs...
  - (* spl D and splu D *)
    inverts Hspl; unify.
    + inverts H.
      * forwards [?|?]: H0... forwards [?|?]: H1...
      * forwards [?|?]: H0... forwards [?|?]: H1...
    + forwards [?|?]: H0...
    + forwards [?|?]: H1...
Qed.
 *)

Lemma arrow : forall A B C D,
    B <: D -> C <: A -> (t_arrow A B) <: (t_arrow C D).
Proof with (simpl in *; auto_unify; aauto).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m_sub (t_arrow A B).
  - applys~ S_arr.
  - (* subtype splittable ; supertype ordinary *)
    inverts keep Hi1.
    + (* split return type B *)
      apply rev in s...
      forwards [?|?]: splu_inv s... inverts~ Hi2.
      * applys~ S_andl Hi1.
        applys IH... applys~ rev2. eomg2.
      * applys~ S_andr Hi1.
        applys IH... applys~ rev2. eomg2.
    + (* splitu input type A *)
      forwards [?|?]: splu_inv H... inverts~ Hi2.
      * applys~ S_andl Hi1.
        applys IH... eomg2.
      * applys~ S_andr Hi1.
        applys IH... eomg2.
  - (* supertype splittable *)
    inverts keep Hi2.
    + (* split return type *)
      applys~ S_and Hi2.
      * applys IH... apply rev2 in s. apply rev2.
        applys orl_trans... eomg2.
      * applys IH... apply rev2 in s. apply rev2.
        applys orr_trans s... eomg2.
    + (* split input type *)
      applys~ S_and Hi2; clear Hi2.
      * applys IH... eomg2.
        applys orl_trans...
      * applys IH... eomg2.
        applys orr_trans...
Qed.

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

Hint Resolve split_instance1 split_instance2 : core.

Lemma distArrU: forall A B C,
    (t_and (t_arrow A C) (t_arrow B C)) <: (t_arrow (t_or A B) C).
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
      Unshelve.
      constructor. eauto.
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
  applys* S_or.
Qed.

Hint Resolve symm_and symm_or : core.

(*
Lemma distAnd: forall A B1 B2,
    sub (t_and A (t_or B1 B2)) m_sub (t_or (t_and A B1) (t_and A B2)).
Proof with eauto.
  introv.
  applys S_and...
  applys trans. applys symm_and.
  applys trans (t_or (t_and A B2) B1)...
  applys S_and...
Qed.
*)

Lemma distOr: forall A1 A2 B,
    sub (t_and (t_or A1 B) (t_or A2 B)) m_sub (t_or (t_and A1 A2) B).
Proof with eauto.
  introv.
  forwards: Sp_orl m_sub (t_and A1 A2) B A1 A2; eauto.
Qed.

Hint Resolve arrow distArrU distOr : core.

(* declarative subtyping equivalence *)
Hint Constructors osub : core.

Lemma osub_spl: forall m A B C,
    spl m A B C -> osub A m B /\ osub A m C.
Proof with intuition.
  introv H.
    induction H...
  - applys* OS_or.
  - applys* OS_or.
  - applys* OS_or.
  - applys* OS_or.
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


Lemma osub_distAnd: forall A B1 B2,
    osub (t_and (t_or B1 B2) A) m_sub (t_or (t_and B1 A) (t_and B2 A)).
Proof with eauto.
  introv.
  applys OS_trans.
  2:{ applys OS_distOr. }
  - applys OS_and.
    + applys OS_trans (t_or (t_and B2 A) B1).
      2: { apply OS_flip. simpl. lets: osub_symm_and m_super. simpl in H. applys H. }
      * applys OS_trans.
        2: { applys OS_distOr. }
        ** applys OS_and. lets H: OS_andl (t_or B1 B2) m_sub A.
           simpl in H. applys OS_trans H.
           lets: osub_symm_or m_sub. simpl in H0. applys H0.
           applys OS_trans. lets: OS_andr m_sub. simpl in H. apply H.
           lets: OS_orl m_sub. simpl in H. apply H.
    + eauto.
Qed.

Hint Resolve osub_symm_and osub_symm_or osub_distAnd : core.


Lemma osub_and: forall m A B C,
    spl m A B C -> osub (choose m B C) m A.
Proof with intuition.
  introv H.
    induction H.
  - applys OS_refl.
  - eauto.
  - forwards: osub_spl H0. eauto.
  - applys OS_trans (choose (flipmode m) (choose m A1 A2) B).
  - applys OS_trans (t_or B A)...
    applys OS_trans (t_and (t_or B1 A) (t_or B2 A))...
    applys OS_and.
    applys OS_trans (t_or A B1)...
    applys OS_trans (t_or A B2)...
    applys* OS_trans (t_or (t_and B1 B2) A).
    + introv H.
      induction H.
  - applys OS_refl.
  - clear osub_and osub_or.
    applys* OS_trans (t_and (t_or A1 A2) B).
  - clear osub_and osub_or.
    applys OS_trans (t_and B A)...
    applys* OS_trans (t_and (t_or B1 B2) A).
Qed.

Hint Resolve osub_spl osub_splu osub_and osub_or: core.

Theorem dsub_eq: forall A B,
    osub A B <-> sub A B.
Proof with (aauto; eauto).
  split; introv H.
  - induction* H.
  -
    induction~ H.
    + (* andl *)
      forwards (?&?): osub_spl H0. applys OS_trans H2...
    + (* andr *)
      forwards (?&?): osub_spl H0. applys OS_trans H3...
    + applys OS_trans IHsub...
    + applys OS_trans IHsub...
    + applys OS_trans (t_and B C)...
Qed.
