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
  - (* ord VS spl *)
    lets* [?|(?&?&?)]: IHA2.
    + (* ord A2 in A1->A2 *)
      lets* [?|(?&?&?)]: IHA1 (flipmode m).
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

Hint Resolve choose_false_int choose_false_top choose_false_bot choose_false_arrow choose_and_sub choose_or_super and_or_mismatch: falseHd.

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

Ltac solve_false := try intro; try solve [false; eauto with falseHd].

(* duotyping related lemmas *)
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

(* subtyping *)
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

Create HintDb sizeTypHd.

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
  match goal with
  | [ H: spl _ _ _ _ |- _ ] =>
    (lets (?&?): split_decrease_size H)
  end.

(* enhanced eomg with split_decrease_size *)
Ltac eomg2 :=
  pose proof (typ_size_lg_z);
  simpl in *; try spl_size; try omega.

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
    spl m (choose m A B) C D -> A=C /\ B = D.
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
  inverts H; destruct m; inverts H0...
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
           forwards (?&?): split_choose H1
         end;
  try rewrite flip_flip in *;
  try rewrite cal_top in *;
  try rewrite cal_bot in *;
  solve_false.

Ltac aauto := try eassumption.


Notation "A <: B" := (sub A m_sub B) (at level 80, right associativity).


Lemma refl : forall A m, sub A m A.
Admitted.

Lemma choose_false : forall m A B C D,
    choose m A B = choose (flipmode m) C D -> False.
Admitted.

Lemma flip_eqv_false : forall m,
    m = flipmode m -> False.
Proof.
  intros.
  destruct m; inverts H.
Qed.

Hint Resolve flip_eqv_false : falseHd.

Lemma split_sub : forall m T A B,
    spl m T A B -> sub T m A /\ sub T m B.
Proof  with (aauto; simpl in *; auto_unify).
  introv Hsp.
  split.
  applys S_andl...
  (* rely on refl for A/B *)
Admitted.

Lemma split_sub_flip : forall m T A B,
    spl m T A B -> sub A (flipmode m) T /\ sub B (flipmode m) T.
Proof  with (aauto; simpl in *; auto_unify).
  introv Hsp.
  split.
  applys S_orl...
  (* rely on refl for A/B *)
Admitted.

Lemma spl_two_way : forall m T A1 A2 B1 B2,
    spl m T A1 A2 -> spl (flipmode m) T B1 B2 ->
    sub A1 (flipmode m) B1 /\ sub A1 (flipmode m) B2 /\ sub B1 m A2 /\ sub B2 m A2.
Proof with (aauto; simpl in *; auto_unify).
  introv Hsp1 Hsp2.
  - inverts Hsp1.
    +  (* m:=sub A1:=I1\/C1 A2:=I2\/C2 B1:=I1&(I2\/C2) B2:=C1&(I2\/C2) *)
      inverts Hsp2...
      * repeat split.
        ** applys S_orl... eauto. forwards*: split_sub H1.
        ** applys S_orl... eauto. forwards*: split_sub H1.
        ** applys S_andr... eauto. admit. (* refl on A2 *)
        ** applys S_andr... eauto. admit. (* refl on A2 *)
      * repeat split.
        ** applys S_orl... eauto.  admit. (* refl on A1 *)
        ** applys S_orl... eauto.  admit. (* refl on A1 *)
        ** applys S_andr... eauto. forwards*: split_sub_flip H2... jauto.
        ** applys S_andr... eauto. forwards*: split_sub_flip H2... jauto.
    + (* arrow *)



           forwards*: split_sub_flip H1.


           forwards*: Sp_and m_sub A0 A2. aauto.
        ** split*.
           *** applys S_orl. forwards*: Sp_and m_sub A0 A2. aauto.
           *** split*. applys S_andr...
               forwards*: Sp_and m_sub A0 A2.
               apply refl.
               applys S_andr...
               forwards*: Sp_and m_sub A3 A2.
               apply refl.
  destruct m.
  - inverts Hsp1...
    +  (* m:=sub A1:=I1\/C1 A2:=I2\/C2 B1:=I1&(I2\/C2) B2:=C1&(I2\/C2) *)
      inverts Hsp2...
      * forwards (?&?): split_sub H4.
        split.
        ** applys S_orl.
           forwards*: Sp_and m_sub A0 A2. aauto.
        ** split*.
           *** applys S_orl. forwards*: Sp_and m_sub A0 A2. aauto.
           *** split*. applys S_andr...
               forwards*: Sp_and m_sub A0 A2.
               apply refl.
               applys S_andr...
               forwards*: Sp_and m_sub A3 A2.
               apply refl.



Lemma orl : forall m A B C D,
    ord (flipmode m) D -> spl (flipmode m) C A B -> sub D m A -> sub D m C.
Proof with (aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ C).
  lets [Hi|(?&?&Hi)]: ord_or_split m C.
  - eauto.
  - applys S_and...
Admitted.

Lemma andl_trans : forall m A B B1 B2,
    spl m B B1 B2 -> sub A m B -> sub A m B1.
Proof with (aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub; unify; auto with sizeTypHd.
  forwards~: IH B0 Hspl. eomg2.
  applys orl.
  destruct m; simpl in *; inverts Hspl.
  destruct m; simpl in *; inverts Hspl.
Qed.

Lemma andr_trans : forall m A B B1 B2,
    spl m B B1 B2 -> sub A m B -> sub A m B2.
Proof with (aauto; eomg).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub; unify; auto with sizeTypHd.
  destruct m; simpl in *; inverts Hspl.
Qed.

Lemma orl_trans : forall m A A1 A2 B,
    spl (flipmode m) A A1 A2 -> sub A m B -> sub A1 m B.
Proof with (unify; aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub; unify; auto with sizeTypHd.
  - destruct m; simpl in *; inverts Hspl.
  - assert (sub A1 m B0). applys IH Hspl...
    assert (sub A1 m C). applys IH Hspl...
    applys S_and...
Qed.

Lemma orr_trans : forall m A A1 A2 B,
    spl (flipmode m) A A1 A2 -> sub A m B -> sub A2 m B.
Proof with (unify; aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts~ Hsub; unify; auto with sizeTypHd.
  - destruct m; simpl in *; inverts Hspl.
  - assert (sub A2 m B0). applys IH Hspl...
    assert (sub A2 m C). applys IH Hspl...
    applys S_and...
Qed.

Hint Resolve andl_trans andr_trans orl_trans orr_trans : core.

Lemma andl : forall m A B C D,
    ord (flipmode m) D -> spl m D A B -> sub A m C -> sub D m C.
Proof with (aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ C).
  lets [Hi|(?&?&Hi)]: ord_or_split m C.
(*  lets [Hi2|(?&?&Hi2)]: ord_or_split (flipmode m) D. *)
  - applys* S_andl.
 (* assert (S1: sub x m C) by applys* orl_trans Hi.
    assert (S2: sub x0 m C) by applys* andr_trans Hi.
    applys S_or Hi.
    applys IH S1 Hspl...
    applys IH S2 Hspl... *)
  - assert (S1: sub A m x) by applys* andl_trans Hi.
    assert (S2: sub A m x0) by applys* andr_trans Hi.
    applys S_and Hi.
    applys IH S1...
    applys IH S2...
  Unshelve. aauto. eauto.
Qed.


Lemma andr : forall m A B C D,
    spl m D A B -> sub B m C -> sub D m C.
Proof with (unify; aauto; eomg2).
  introv Hspl Hsub.
Admitted.

Lemma rev : forall A m B,
    sub A m B -> sub B (flipmode m) A.
Proof.
  intros.
  induction H; try constructor*.
  - rewrite <- (flip_flip mode5) at 1.
    econstructor.
  - remember (flipmode mode5) as m.
    applys* S_or.
Abort.

Lemma split_subl_flip: forall m A B C,
    spl m A B C -> sub B (flipmode m) A.
Proof.
  introv H.
  lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) B.
Admitted.

(* andl, andr are used in refl proof *)
(* reflexivity *)
Hint Extern 0 =>
match goal with
| [ IH : forall A, size_typ A < _ -> _ |- sub ?A _ ?A ] => (forwards*: IH A; eomg2)
end : refl.

Lemma refl : forall A m, sub A m A.
Proof with (unify; simpl in *; auto with refl).
  introv. gen m.
  indTypSize (size_typ A).
  lets [Hi|(?&?&Hi)]: ord_or_split m A;
    lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
  - (* ord A & ordu A *)
    destruct A; try solve [destruct m; solve_false]...
    +  destruct m.
       lets: S_top t_top m_sub...
       lets: S_bot m_super t_top...
    +  destruct m.
       lets: S_bot m_sub t_bot...
       lets: S_top t_bot m_super...
  - (* ord A & splu A *)
    applys S_or; aauto. applys S_orl Hu; aauto. admit. admit. admit. (* apply~ S_orr... *)
  - (* spl A *)
    applys~ S_and Hi...
    applys~ andl Hi...
    applys~ andr Hi...
  - (* spl A & splu A *)
    destruct m; inverts Hi; inverts Hu.
    applys~ S_and Hi...
Qed.

Hint Resolve andl andr refl : core.

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
Proof with (unify; auto).
  introv Hu Hs.
  indTypSize (size_typ T + size_typ (t_or A B)).
  lets ([Hord|(?&?&Hspl)]&Hu'): ord_or_split (t_or A B).
  - inverts Hs...
    + forwards* [?|?]: IH H1; eomg2.
    + forwards* [?|?]: IH H1; eomg2.
  - inverts Hspl.
    + inverts~ Hs...
      *
        inverts H...
        forwards~ [?|?]: IH H0; eomg2.
        forwards~ [?|?]: IH H1; eomg2.
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
        forwards~ [?|?]: IH H0; eomg2.
        forwards~ [?|?]: IH H2; eomg2.
        eauto.
Qed.


Lemma orl_trans : forall A A1 A2 B,
    splu A A1 A2 -> sub A B -> sub A1 B.
Proof with (unify; aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts keep Hsub; auto...
  - (* andl *)
    inverts H0; (* spl *)
      try solve [inverts Hspl; applys~ andl; applys* IH H1; eomg2].
    (* spl A&B *) (* spl A->B *) (* spl A->B *)
    + (* spl A\/B *)
      inverts Hspl. applys* andl.
      applys* IH H1...
    + (* spl A\/B *)
      inverts keep Hspl.
      applys* IH H1...
  - (* andr *)
    inverts H0; (* spl *)
      try solve [inverts Hspl; applys~ andr; applys* IH H1; eomg2].
    (* spl A&B *) (* spl A->B *) (* spl A->B *)
    + (* spl A\/B *)
      inverts Hspl. applys* andr.
      applys* IH H1...
    + (* spl A\/B *)
      inverts keep Hspl.
      applys* IH H1...
  - (* orl rhs *)
    applys~ S_orl.
    applys* IH H0...
  - (* orr rhs *)
    applys~ S_orr.
    applys* IH H0...
  - (* and *)
    applys~ S_and H;
      applys IH...
Qed.

Lemma orr_trans : forall A A1 A2 B,
    splu A A1 A2 -> sub A B -> sub A2 B.
Proof with (unify; aauto; eomg2).
  introv Hspl Hsub.
  indTypSize (size_typ A + size_typ B).
  inverts keep Hsub; auto...
  - (* andl *)
    inverts H0; (* spl *)
      try solve [inverts Hspl; applys~ andl; applys* IH H1; eomg2].
    (* spl A&B *) (* spl A->B *) (* spl A->B *)
    + (* spl A\/B *)
      inverts keep Hspl.
      applys* IH H1...
    + (* spl A\/B *)
      inverts Hspl. applys* andl.
      applys* IH H1...
  - (* andr *)
    inverts H0; (* spl *)
      try solve [inverts Hspl; applys~ andr; applys* IH H1; eomg2].
    (* spl A&B *) (* spl A->B *) (* spl A->B *)
    + (* spl A\/B *)
      inverts keep Hspl.
      applys* IH H1...
    + (* spl A\/B *)
      inverts Hspl. applys* andr.
      applys* IH H1...
  - (* orl rhs *)
    applys~ S_orl.
    applys* IH H0...
  - (* orr rhs *)
    applys~ S_orr.
    applys* IH H0...
  - (* and *)
    applys~ S_and H;
      applys IH...
Qed.

(* transitivity *)
Hint Extern 0 =>
match goal with
| [ IH: forall _ , _ , H1: sub  ?A ?B , H2: sub ?B ?C |- sub ?A ?C ] =>
  (forwards: IH H1 H2; eomg2)
end : trans.

Lemma trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof with (unify; aauto; auto with trans).
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
    assert (sub B0 C) by applys* orl_trans s2...
  - (* orr *)
    assert (sub C0 C) by applys* orr_trans s2...
  - (* arr *)
    inverts~ s2...
    + applys~ S_and H3...
  - (* and *)
    inverts~ s2...
    + applys~ S_and H2...
Qed.

Hint Immediate trans : core.

(* how could they be isomophic before splitu is removed? *)
Lemma split_iso: forall A B C,
    spl A B C -> sub A (t_and B C) /\ sub (t_and B C) A.
Proof with eauto.
  intros A B C H.
  split.
  - applys~ S_and. applys~ andl H. applys~ andr H.
  - applys S_and H. applys~ andl. applys~ andr.
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


Lemma splitu_lsub: forall A B C,
    splu A B C -> sub B A.
Proof.
  introv H.
  induction* H.
  applys orl_trans; try applys refl. eauto.
Qed.

Lemma splitu_rsub: forall A B C,
    splu A B C -> sub C A.
Proof.
  introv H.
  induction* H.
  applys orr_trans; try applys refl. eauto.
Qed.


Hint Resolve split_subl split_subr splitu_lsub splitu_rsub: core.

Lemma splitu_keep_ord_l : forall A B C,
    ord A -> splu A B C -> ord B.
Proof.
  introv Hord Hspl.
  induction Hspl; inverts* Hord.
Qed.

Lemma splitu_keep_ord_r : forall A B C,
    ord A -> splu A B C -> ord C.
Proof.
  introv Hord Hspl.
  induction Hspl; inverts* Hord.
Qed.

Hint Resolve splitu_keep_ord_l splitu_keep_ord_r : core.

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

Lemma arrow : forall A B C D,
    sub B D -> sub C A -> sub (t_arrow A B) (t_arrow C D).
Proof with (unify; aauto; eomg2).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets ([Hi2|(?&?&Hi2)]&Hu'2): ord_or_split (t_arrow C D).
  lets ([Hi1|(?&?&Hi1)]&Hu'1): ord_or_split (t_arrow A B).
  - applys~ S_arr.
  - (* subtype splittable ; supertype ordinary *)
    inverts keep Hi1.
    + (* split return type B *)
      forwards [?|?]: split_subord_inv B s... inverts~ Hi2.
      * applys~ S_andl Hi1.
        applys IH...
      * applys~ S_andr Hi1.
        applys IH...
    + (* splitu input type A *)
      forwards [?|?]: splitu_ordusub_inv A... inverts~ Hi2.
      * applys~ S_andl Hi1.
        applys IH...
      * applys~ S_andr Hi1.
        applys IH...
  - (* supertype splittable *)
    inverts keep Hi2.
    + (* split return type *)
      applys~ S_and Hi2.
      * applys IH...
        applys andl_trans s...
      * applys IH...
        applys andr_trans s...
    + (* split input type *)
      applys~ S_and Hi2; clear Hi2.
      * applys IH...
        applys orl_trans H5...
      * applys IH...
        applys orr_trans H5...
Qed.

Lemma splu_lhs : forall A B C D,
    splu A B C -> sub B D -> sub C D -> sub A D.
Proof with (unify; aauto; eomg2).
  introv Hspl Hs1 Hs2.
  indTypSize (size_typ A + size_typ D).
  lets ([Hi1|(?&?&Hi1)]&Hu'1): ord_or_split D.
  - (* ord D *)
    lets ([Hi2|(?&?&Hi2)]&Hu'2): ord_or_split A.
    inverts Hspl...
    + applys S_or...
    + inverts Hspl...
      * (* A = B\/C *)
        inverts Hi2...
        ** forwards~ [?|?]: split_subord_inv Hs1...
           *** applys S_andl. auto. eauto.
               applys* IH...
           *** applys S_andr. auto. eauto.
               applys* IH...
        ** forwards~ [?|?]: split_subord_inv Hs2...
           *** applys S_andl. auto. eauto.
               applys* IH...
           *** applys S_andr. auto. eauto.
               applys* IH...
      * (* A = x&x0 *)
        forwards~ [?|?]: split_subord_inv Hs1...
        forwards~ [?|?]: split_subord_inv Hs2...
        ** applys andl. eauto.
           applys IH...
        ** applys andr. eauto. auto.
        ** applys andr. eauto. auto.
      * (* A = x&x0 *)
        forwards~ [?|?]: split_subord_inv Hs1...
        ** applys andl. eauto. auto.
        ** forwards~ [?|?]: split_subord_inv Hs2...
           applys andl. eauto. auto.
           applys andr. eauto. applys IH...
  - applys S_and...
    * applys IH...
      applys~ andl_trans Hi1.
      applys~ andl_trans Hi1.
    * applys IH...
      applys~ andr_trans Hi1.
      applys~ andr_trans Hi1.
Qed.

Lemma distArrU: forall A B C,
    sub (t_and (t_arrow A C) (t_arrow B C)) (t_arrow (t_or A B) C).
Proof with (unify; aauto; eomg2).
  introv.
  indTypSize (size_typ C).
  lets ([Hi1|(?&?&Hi1)]&Hu'1): ord_or_split C.
  - applys* S_and.
  - (* split C x x0 *)
    forwards Hs1: IH A B x...
    forwards Hs2: IH A B x0...
    applys S_and. eauto.
    + applys trans Hs1. applys* S_and.
    + applys trans Hs2. applys* S_and.
Qed.

Lemma symm_and: forall A B,
    sub (t_and A B) (t_and B A).
Proof.
  introv.
  applys* S_and.
Qed.

Lemma symm_or: forall A B,
    sub (t_or A B) (t_or B A).
Proof.
  introv.
  applys* splu_lhs.
Qed.

Hint Resolve symm_and symm_or : core.

Lemma distAnd: forall A B1 B2,
    sub (t_and A (t_or B1 B2)) (t_or (t_and A B1) (t_and A B2)).
Proof with eauto.
  introv.
  applys S_and...
  applys trans. applys symm_and.
  applys trans (t_or (t_and A B2) B1)...
  applys S_and...
Qed.


Lemma distOr: forall A B1 B2,
    sub (t_and (t_or A B1) (t_or A B2)) (t_or A (t_and B1 B2)).
Proof with eauto.
  introv.
  applys trans. applys symm_and.
  applys trans (t_or (t_and B1 B2) A)...
Qed.

Hint Resolve arrow splu_lhs distArrU distAnd distOr : core.

(* declarative subtyping equivalence *)
Hint Constructors osub : core.

Lemma osub_spl: forall A B C,
    spl A B C -> osub A B /\ osub A C
with osub_splu: forall A B C,
    splu A B C -> osub B A /\ osub C A.
Proof with intuition.
  + introv H.
    induction H...
  - apply osub_splu in H0...
  - apply osub_splu in H0...
  - applys* OS_or.
  - applys* OS_or.
  - applys* OS_or.
  - applys* OS_or.

  +  introv H.
     induction H...
  - applys* OS_and.
  - applys* OS_and.
  - applys* OS_and.
  - applys* OS_and.
Qed.

Lemma osub_symm_and: forall A B,
    osub (t_and A B) (t_and B A).
Proof.
  introv.
  applys* OS_and.
Qed.

Lemma osub_symm_or: forall A B,
    osub (t_or A B) (t_or B A).
Proof.
  introv.
  applys* OS_or.
Qed.


Lemma osub_distAnd: forall A B1 B2,
    osub (t_and (t_or B1 B2) A) (t_or (t_and B1 A) (t_and B2 A)).
Proof with eauto.
  introv.
  applys OS_trans.
  2:{ applys OS_distOr. }
  - applys OS_and.
    + applys OS_trans (t_or (t_and B2 A) B1).
      2: { applys osub_symm_or. }
      * applys OS_trans.
        2: { applys OS_distOr. }
        ** applys* OS_and.
    + eauto.
Qed.

Hint Resolve osub_symm_and osub_symm_or osub_distAnd : core.


Lemma osub_and: forall A B C,
    spl A B C -> osub (t_and B C) A
with osub_or: forall A B C,
    splu A B C -> osub A (t_or B C).
Proof with intuition.
  + introv H.
    induction H.
  - applys OS_refl.
  - clear osub_and osub_or. eauto.
  - forwards: osub_or H0.
    clear osub_and osub_or. eauto.
  - clear osub_and osub_or.
    applys* OS_trans (t_or (t_and A1 A2) B).
  - clear osub_and osub_or.
    applys OS_trans (t_or B A)...
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
