Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Export syntax_ott.
Require Import rules_inf.
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

Hint Resolve split_instance1 split_instance2 : ord.

Lemma ord_or_split: forall m A,
    ord m A \/ exists B C, spl m A B C.
Proof with (eauto with ord; intros).
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
      right. exists... applys* Sp_orr.
      right*. exists*. applys* Sp_orl.
      right*. exists*. applys* Sp_orl.
  - (* or *)
    destruct m...
    + lets [?|(?&?&?)]: IHA1 m_sub;
        lets [?|(?&?&?)]: IHA2 m_sub.
      left. constructor*.
      right*. exists*. applys* Sp_orr.
      right*. exists*. applys* Sp_orl.
      right*. exists*. applys* Sp_orl.
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
    size_typ A < size_typ (choose m A B) /\ size_typ B < size_typ (choose m A B).
Proof.
  split; intros;
    destruct m; simpl in *; omega.
Qed.

Hint Resolve typ_size_lg_z choose_decrease_size : core.

Lemma split_decrease_size: forall m A B C,
    spl m A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try omega).
  - introv H.
    induction* H...
    destruct m; eauto...
    destruct m; eauto...
Qed.

Ltac spl_size :=
  try repeat match goal with
         | [ H: spl _ _ _ _ |- _ ] =>
           ( lets (?&?): split_decrease_size H; clear H)
             end;
  try match goal with
         | [ H: size_typ (choose ?m ?A ?B) < _ |- _ ] =>
           ( lets (?&?): choose_decrease_size m A B)
             end.

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
  | [ IH: forall A, size_typ A < _ -> _, A: typ, Hsp: spl ?m ?T _  _, Hsp2: spl ?m ?T _  _ |- _ ] =>
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
  solve_false.

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
        ** destruct m.
          lets: S_top t_top m_sub...
          lets: S_bot m_super t_top...
        ** destruct m.
          lets: S_bot m_sub t_bot...
          lets: S_top t_bot m_super...
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
      ** destruct m.
          lets: S_top t_top m_sub...
          lets: S_bot m_super t_top...
      ** destruct m.
          lets: S_bot m_sub t_bot...
          lets: S_top t_bot m_super...
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

(* reflexivity *)

Lemma refl : forall A m, sub A m A.
Proof with (auto_unify; try solve [constructor; aauto; eauto 3];  try refl_autoIH).
  introv. gen m.
  indTypSize (size_typ A).
  lets [Hi|(?&?&Hi)]: ord_or_split m A.
  lets [Hu|(?&?&Hu)]: ord_or_split (flipmode m) A.
  - (* ord A *)
    destruct A; auto_unify.
    admit. admit. admit.
    + (* arrow *)
      constructor; aauto; destruct m; auto_unify; auto; refl_autoIH.
  - (* ord A & ordu A *)
    applys S_or; aauto.
    admit. admit. (*
    applys S_orl Hu...
    applys S_orr Hu... *)
  - (* spl A *)
    applys~ S_and Hi...
    applys S_andl Hi...
    applys S_andr Hi...
  -
    destruct A; destruct m...
    + lets: S_bot m_super... eauto.
    + lets: S_bot m_sub t_bot... eauto.
    + constructor~. refl_autoIH.
    + lets: S_top t_top m
                  _sub...
    + lets: S_bot m_super t_top...
    + lets: S_top t_bot m_super...
  - (* ord A & splu A *)
    applys S_or; aauto.
    applys S_orl Hu...
    applys S_orr Hu...
  (* flip m m'. applys* split_sub_flip_l.
    flip m m'. applys* split_sub_flip_r. *)
  - (* spl A *)
    applys~ S_and Hi...
    applys S_andl Hi...
    applys S_andr Hi...
    (* applys* split_sub_l.
       applys* split_sub_r. *)
    Unshelve. econstructor. eauto.
Qed.

Hint Resolve refl : core.

Lemma split_iso: forall m A B C,
    spl m A B C -> sub A m (choose m B C) /\ sub (choose m B C) m A.
Proof with eauto.
  introv H.
  split.
  - applys S_and...
  - applys S_and H. applys~ S_andl. applys~ S_andr.
Qed.

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
      * flip m m'. simpl in *.
        admit.
      * flip m m'. simpl in *.
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


Lemma arrow : forall A B C D,
   A :> C -> B <: D -> (t_arrow A B) <: (t_arrow C D).
Proof with (simpl in *; auto_unify; aauto).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m_sub (t_arrow A B).
  - applys~ S_arr...
  - (* subtype splittable ; supertype ordinary *)
    inverts keep Hi1.
    + (* split return type B *)
      apply rev2 in H...
      forwards [?|?]: splu_inv H... inverts~ Hi2.
      * applys~ S_andl Hi1.
        applys IH... eomg2. applys~ rev2.
      * applys~ S_andr Hi1.
        applys IH... eomg2. applys~ rev2.
    + (* splitu input type A *)
      apply rev2 in s...
      forwards [?|?]: splu_inv s... inverts~ Hi2.
      * applys~ S_andl Hi1.
        applys IH... applys~ rev2. eomg2.
      * applys~ S_andr Hi1.
        applys IH... applys~ rev2. eomg2.
  - (* supertype splittable *)
    inverts keep Hi2.
    + (* split return type *)
      applys~ S_and Hi2.
      * applys IH... eomg2. apply rev2 in H. apply rev2.
        applys orl_trans...
      * applys IH... eomg2. apply rev2 in H. apply rev2.
        applys orr_trans...
    + (* split input type *)
      applys~ S_and Hi2; clear Hi2.
      * applys IH... apply rev2 in s. apply rev2.
        applys orl_trans... eomg2.
      * applys IH... apply rev2 in s. apply rev2.
        applys orr_trans... eomg2.
Qed.

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


Lemma osub_and: forall m A B C,
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

Hint Resolve osub_spl osub_and: core.

Theorem dsub_eq: forall A m B,
    osub A m B <-> sub A m B.
Proof with (simpl in *; aauto).
  split; introv H.
  - induction* H.
    + destruct mode5.
      * simpl in *. eauto.
      * apply rev2. apply rev2 in IHosub1. apply rev2 in IHosub2.
        simpl in *. eauto.
    + destruct mode5.
      * eauto.
      * applys S_or; eauto; apply rev; eauto.
    + destruct mode5.
      * eauto.
      * applys S_or; eauto; apply rev; eauto.
  - induction~ H.
    + (* andl *)
      forwards (?&?): osub_spl H. applys OS_trans H1...
    + (* andr *)
      forwards (?&?): osub_spl H. applys OS_trans H2...
    + applys OS_trans IHsub... forwards*: osub_spl H...
    + applys OS_trans IHsub... forwards*: osub_spl H...
    + applys OS_trans (choose (flipmode mode5) B C)...
      forwards Hf: osub_and H. apply OS_flip in Hf.
      eauto. applys OS_flip. flip mode5 m'. eauto.
    + applys OS_trans (choose mode5 B C)...
      forwards Hf: osub_and H.
      eauto. eauto.
Qed.

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
   (t_arrow A B) <: (t_arrow C D) -> (A :> C) /\ (B <: D).
Proof with (simpl in *; auto_unify; jauto).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ord_or_split m_sub (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ord_or_split m_sub (t_arrow A B).
  - inverts s...
  - inverts keep Hi1;
      forwards~ [?|?]: spl_inv Hi1 s;
      forwards(IH1&IH2): IH H; try solve [eomg2];
        split; try eassumption.
    + applys~ S_andl H1.
    + applys~ S_andr H1.
    + applys~ S_andl H2.
    + applys~ S_andr H2.
  - (* uses and_inv_1 and_inv_2 *)
    assert (t_arrow A B <: x) by eauto.
    assert (t_arrow A B <: x0) by eauto.
    inverts keep Hi2;
      forwards (?&?): IH H; try solve [eomg2];
      forwards (?&?): IH H0; try solve [eomg2];
      eauto.
Qed.

Theorem decidability : forall m A B,
    sub A m B \/ not (sub A m B).
Proof with (simpl in *; solve_false; jauto).
  introv. gen m.
  indTypSize (size_typ A + size_typ B).
  lets [HAu|(?&?&HAu)]: ord_or_split (flipmode m) A.
  - (* ordinary > A *)
    lets [HBi|(?&?&HBi)]: ord_or_split m B.
    + (* ord < B *)
      lets [HAi|(?&?&HAi)]: ord_or_split m A.
      * (* ordinary < A *)
        lets [HBu|(?&?&HBu)]: ord_or_split (flipmode m) B.
        ** (* ord > B *)
          destruct m; inverts HAu; inverts HAi;
            inverts HBu; inverts HBi; auto with falseHd;
              try solve [right; intros HF; inverts HF; auto_unify].
          *** (* arrow *)
            forwards [IH1|IH1] : IH A0 A m_super; try solve [eomg2];
              forwards [IH2|IH2] : IH B0 B1 m_sub; try solve [eomg2];
                try solve [right; intros HF; forwards* (?&?): arrow_inv HF]; eauto.
          *** (* arrow *)
            forwards [IH1|IH1] : IH A0 A m_sub; try solve [eomg2];
              forwards [IH2|IH2] : IH B0 B1 m_super; try solve [eomg2];
                try solve [right; intros HF; apply rev2 in HF; forwards* (?&?): arrow_inv HF].
            left. apply rev2. eauto.
        ** (* spl > B *)
          forwards [IHB1|IHB1] : IH A x m; try solve [eomg2]...
          forwards [IHB2|IHB2] : IH A x0 m; try solve [eomg2]...
          right. intro HF. forwards*: splu_inv HF.
      * (* spl < A *)
        forwards [IHA1|IHA1] : IH x B m; try solve [eomg2]...
        forwards [IHA2|IHA2] : IH x0 B m; try solve [eomg2]...
        right. intro HF. forwards*: spl_inv HF.
    + (* spl < B *)
      forwards [IHB1|IHB1] : IH A x m; try solve [eomg2].
      * forwards [IHB2|IHB2] : IH A x0 m; try solve [eomg2]...
      * right...
  - (* spl > A *)
    forwards [IHA1|IHA1] : IH x B m; try solve [eomg2].
    + forwards [IHA2|IHA2] : IH x0 B m; try solve [eomg2]...
    + right...
Qed.

(* algorithm correctness *)
Lemma rule_and_inv : forall m A B B1 B2,
    sub A m B -> spl m B B1 B2 -> sub A m B1 /\ sub A m B2.
Proof.
  intros.
  induction* H.
Qed.

Lemma rule_or_inv : forall m A A1 A2 B,
    sub A m B -> spl (flipmode m) A A1 A2 -> sub A1 m B /\ sub A2 m B.
Proof.
  intros.
  induction* H.
  Unshelve. eauto.
Qed.


(* potential improvements *)
(* add try solve in eomg2 *)
(* mode in arrow_inv *)
(* better encode of aux functions *)
(* move rev_2 to top *)
