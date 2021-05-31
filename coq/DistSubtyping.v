(** This variant replaces the old distributivity rule by the two
 (A1 /\ A2) -> (B1 \/ B2) <: (A1 -> B1) \/ (A2 -> B2)
 (A1 -> B1) /\ (A2 -> B2) <: (A1 \/ A2) -> (B1 /\ B2)
*)

Require Import LibTactics.
Require Export Coq.micromega.Lia.
Require Export Definitions.


Create HintDb AllHd.
Create HintDb SizeHd.
Create HintDb FalseHd.

(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)
Ltac solve_false := try intro; try solve [false; eauto 2 with FalseHd].

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

(******************************************************************************)
(* Types are Either Ordinary or Splittable *)

#[local] Hint Constructors ordi ordu spli splu : FalseHd AllHd.

Lemma ordi_or_split: forall A,
    ordi A \/ exists B C, spli A B C
with ordu_or_split: forall A,
    ordu A \/ exists B C, splu A B C.
Proof with (eauto with * ; intros).
  - intros. clear ordi_or_split. induction A...
    + (* arrow *)
      lets [?|(?&?&?)]: ordu_or_split A1;
        lets [?|(?&?&?)]: IHA2...
    + (* or *)
      lets [?|(?&?&?)]: IHA1;
        lets [?|(?&?&?)]: IHA2...
  - intros. clear ordu_or_split. induction A...
    + (* arrow *)
      lets [?|(?&?&?)]: ordi_or_split A1;
        lets [?|(?&?&?)]: IHA2...
    + (* and *)
      lets [?|(?&?&?)]: IHA1;
        lets [?|(?&?&?)]: IHA2...
Qed.

(******************************************************************************)
(* false *)

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
Lemma spli_ord_false : forall A B C,
    spli A B C -> ordi A -> False
with splu_ord_false : forall A B C,
    splu A B C -> ordu A -> False.
Proof.
  - introv. clear spli_ord_false. gen B C.
    induction A; intros B C s o;
      try solve [inverts* s];
      try solve [inverts* o];
      inverts o;
      inverts* s.
  - introv. clear splu_ord_false. gen B C.
    induction A; intros B C s o;
      try solve [inverts* s];
      try solve [inverts* o];
      inverts o;
      inverts* s.
Qed.

#[local] Hint Resolve ordu_or_split and_or_mismatch ordi_and_false
     ordu_or_false spli_ord_false splu_ord_false : FalseHd.

(******************************************************************************)
(* lemmas for ordinary *)
Lemma splu_keep_ordi : forall A B C,
   ordi A -> splu A B C -> ordi B /\ ordi C
with spli_keep_ordu : forall A B C,
   ordu A -> spli A B C -> ordu B /\ ordu C.
Proof.
  - introv Hord Hspl. clear splu_keep_ordi.
    inductions Hspl; try inverts~ Hord; eauto.
    + split; constructor*; forwards~ (?&?): spli_keep_ordu H.
    + split; constructor*.
    + split; constructor*; forwards~ (?&?): spli_keep_ordu H0.
  - introv Hord Hspl. clear spli_keep_ordu.
    inductions Hspl; try inverts~ Hord; eauto.
    + split; constructor*; forwards~ (?&?): splu_keep_ordi H.
    + split; constructor*; forwards~ (?&?): splu_keep_ordi H.
Qed.

Lemma splu_keep_ordi_l : forall A B C,
  splu A B C ->  ordi A -> ordi B.
Proof.
  intros. applys~ splu_keep_ordi H.
Qed.

Lemma splu_keep_ordi_r : forall A B C,
   splu A B C -> ordi A -> ordi C.
Proof.
  intros. applys~ splu_keep_ordi H.
Qed.

Lemma spli_keep_ordu_l : forall A B C,
   spli A B C -> ordu A -> ordu B.
Proof.
  intros. applys~ spli_keep_ordu H.
Qed.

Lemma spli_keep_ordu_r : forall A B C,
   spli A B C -> ordu A -> ordu C.
Proof.
  intros. applys~ spli_keep_ordu H.
Qed.

#[local] Hint Resolve spli_keep_ordu_l spli_keep_ordu_r
     splu_keep_ordi_l splu_keep_ordi_r : AllHd.


(* Subtyping *)

Lemma spli_decrease_size: forall A B C,
    spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A
with splu_decrease_size: forall A B C,
    splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  - introv H. clear spli_decrease_size.
    induction H; simpl in *; try forwards: splu_decrease_size H;
      try forwards: splu_decrease_size H0; eauto...
  - introv H. clear splu_decrease_size.
    induction H; simpl in *; try forwards: spli_decrease_size H;
      try forwards: spli_decrease_size H0; eauto...
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
(*               Ltac elia                  *)
(*  enhanced lia with split_decrease_size   *)
(*                                          *)
(********************************************)
Ltac s_elia :=
  try solve [pose proof (size_typ_min);
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
Lemma spli_unique : forall T A1 A2 B1 B2,
    spli T A1 B1 -> spli T A2 B2 -> A1 = A2 /\ B1 = B2
with splu_unique : forall T A1 A2 B1 B2,
    splu T A1 B1 -> splu T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof with (try eassumption; solve_false; subst~).
  -
    intro T. clear spli_unique.
    induction T; intros;
      inverts H; inverts H0;
        try match goal with
          [ H1: splu ?A _ _, H2: splu ?A _ _ |- _ ] => (
            forwards* (?&?): splu_unique H1 H2;
            subst)
        end;
        try repeat match goal with
          [ H1: spli ?A _ _, H2: spli ?A _ _, IH: forall A1 A2 B1 B2 : typ,
                spli ?A _ _ -> _ |- _ ] => (
            forwards* (?&?): IH H1 H2; clear H1 H2;
            subst)
        end...
  -
    intro T. clear splu_unique.
    induction T; intros;
      inverts H; inverts H0;
        try match goal with
          [ H1: spli ?A _ _, H2: spli ?A _ _ |- _ ] => (
            forwards* (?&?): spli_unique H1 H2;
            subst)
        end;
        try repeat match goal with
          [ H1: splu ?A _ _, H2: splu ?A _ _, IH: forall A1 A2 B1 B2 : typ,
                splu ?A _ _ -> _ |- _ ] => (
            forwards* (?&?): IH H1 H2; clear H1 H2;
            subst)
        end...
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
Inductive i_part : typ -> typ -> Prop :=
| IP_refl  : forall A, i_part A A
| IP_spl   : forall A B C B', spli A B C -> i_part B B' -> i_part A B'
| IP_spr   : forall A B C C', spli A B C -> i_part C C' -> i_part A C'
.

Inductive u_part : typ -> typ -> Prop :=
| UP_refl  : forall A, u_part A A
| UP_spl   : forall A B C B', splu A B C -> u_part B B' -> u_part A B'
| UP_spr   : forall A B C C', splu  A B C -> u_part C C' -> u_part A C'
.

#[local] Hint Constructors i_part u_part : core.
#[local] Hint Resolve IP_refl UP_refl : core.

Lemma i_part_spl : forall A B B1 B2,
    i_part A B -> spli B B1 B2 -> i_part A B1 /\ i_part A B2.
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

#[local] Hint Resolve i_part_spl u_part_spl : core.

#[local] Hint Constructors algorithmic_sub : core.

Ltac sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- algorithmic_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; auto 4 with *; eauto 4 with AllHd; s_elia)
end.

Lemma sub_part : forall A B,
    (i_part A B -> algorithmic_sub A B)
    /\ (u_part B A -> algorithmic_sub A B).
Proof with (try eassumption; auto 4 with *; try solve [sub_part_autoIH]; eauto 3 with *).
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
    lets~ (?&?): i_part_spl Hp Hi.
    applys AS_and Hi...

  --
  introv Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - (* ord A *)
    inverts Hp.
    + lets [Hi|(?&?&Hi)]: ordi_or_split A.
      * destruct A; s_auto_unify; solve_false...
        **(* arrow *)
          constructor...
      * applys~ AS_and Hi...
    + applys AS_orl...
    + applys AS_orr...
  - (* spl B *)
    lets~ (?&?): u_part_spl Hp Hu.
    applys AS_or Hu...
Qed.

Theorem sub_refl : forall A, algorithmic_sub A A.
Proof.
  introv.
  pose proof (sub_part A A).
  destruct H; auto with *.
Qed.

Lemma sub_part1 : forall A B,
    i_part A B -> algorithmic_sub A B.
Proof.
  introv.
  pose proof (sub_part A B).
  destruct* H.
Qed.

Lemma sub_part2 : forall A B,
    u_part B A -> algorithmic_sub A B.
Proof.
  introv.
  pose proof (sub_part A B).
  destruct* H.
Qed.

#[local] Hint Resolve sub_refl : MulHd.
#[local] Hint Resolve sub_part1 sub_part2 : AllHd.

(**********************************************************************)
(* algorithm correctness *)

Lemma sub_or_l_inv : forall A A1 A2 B,
    algorithmic_sub A B -> splu A A1 A2 ->
    algorithmic_sub A1 B /\ algorithmic_sub A2 B
with sub_and_r_inv : forall A B B1 B2,
    algorithmic_sub A B -> spli B B1 B2 ->
    algorithmic_sub A B1 /\ algorithmic_sub A B2
with sub_and_l_inv : forall A B A1 A2,
    algorithmic_sub A B -> spli A A1 A2 -> ordi B ->
    algorithmic_sub A1 B \/ algorithmic_sub A2 B
with  sub_or_r_inv : forall A B B1 B2,
    algorithmic_sub A B -> splu B B1 B2 -> ordu A ->
    algorithmic_sub A B1 \/ algorithmic_sub A B2.
Proof with (s_auto_unify; s_elia).
  introv Hsub Hspl. clear sub_or_l_inv.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - inverts Hsub; solve_false; s_auto_unify; auto with AllHd.
    + (* AS_arrow *)
      inverts Hspl.
      *  (*  A4->B0 <<| A0->A3 |>> A5->B3 *)
        split;
          applys AS_arrow; try applys sub_and_r_inv H H3;
            forwards*: IH H0...
      * (*  A0->B0 <<| A0->A3 |>> A0->B3 *)
        split; applys AS_arrow; forwards*: IH H0...
      * (*  A4->A3 <<| A0->A3 |>> A5->A3 *)
        split; applys~ AS_arrow; try applys~ sub_and_r_inv H H6.
    + (* AS_andl *)
      inverts keep Hspl; inverts keep H; try solve [forwards*: IH H0; s_elia];
        try solve [split*]...
      (* t_arrow A5 B1 <<| t_arrow A0 B0 |>> t_arrow A6 B2 *)
      (* t_arrow A0 B0 <| t_arrow A0 B0 |> t_arrow A0 B5 *)
      * inverts H2; inverts H8;
          try solve [ forwards~ (?&?): IH H0; try applys* SpU_arrow; try s_elia;
                      split~; applys AS_andl; try applys* SpI_arrowI; eauto with AllHd; auto ].

      *
        split*.


Lemma sub_or_inv : forall A A1 A2 B,
    algorithmic_sub A B -> splu A A1 A2 ->
    algorithmic_sub A1 B /\ algorithmic_sub A2 B
with sub_and_inv : forall A B B1 B2,
    algorithmic_sub A B -> spli B B1 B2 ->
    algorithmic_sub A B1 /\ algorithmic_sub A B2.
Proof with (s_auto_unify; s_elia).
  introv Hsub Hspl. clear sub_or_inv.
  indTypSize (size_typ A + size_typ B).
   lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - inverts Hsub; solve_false; s_auto_unify; auto with AllHd.
    + (* AS_arrow *)
      inverts Hspl.
      * (*  A4->B0 <<| A0->A3 |>> A5->B3 *)
        split;
          applys AS_arrow; try applys sub_and_inv H H3;
            forwards*: IH H0...
      * (*  A0->B0 <<| A0->A3 |>> A0->B3 *)
        split; applys AS_arrow; forwards*: IH H0.
      * (*  A4->A3 <<| A0->A3 |>> A5->A3 *)
        split; applys~ AS_arrow; try applys~ sub_and_inv H H6.
    + (* AS_andl *)
      Admitted. (*
      inverts Hspl; inverts H; try solve [forwards*: IH H0; s_elia];
        try solve [split*]...
      admit.
      * (* ord B *)
        inverts* H0.
      * (*  A4->B0 <<| A0->A3 |>> A5->B3 *)
        split.
          applys AS_arrow. try applys sub_and_inv H H3;
            forwards*: IH H0...
        lets [Hi|(?&?&Hi)]: ordi_or_split B4.

        split*. ; applys* AS_andl.
      * forwards* (?&?): sub_and_inv (t_or A1 A2) A0 A2 B...

      applys* IH (t_or A0 A2).
      applys~ sub_and_inv H5.
      * forwards* (?&?): IH (t_or A1 A2) A0 A2 B...
      * forwards* (?&?): IH (t_or A1 B1) A1 B1 B...
      * forwards* (?&?): IH H2 B...
    + (* double split A *)
      inverts Hspl; inverts H0...
      * forwards* (?&?): IH (t_or A5 A2) A5 A2 B...
      * forwards* (?&?): IH (t_or A1 B2) A1 B2 B...
      * forwards* (?&?): IH H1...
  - forwards (?&?): sub_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...

  intros.
  induction H; solve_false; s_auto_unify; jauto; auto with *.
  - inverts H0.
Qed.
                 *)

Lemma double_spl : forall A A1 A2 B1 B2,
    spli A A1 A2 -> splu A B1 B2 -> True.
Proof.
  introv Hsp1 Hsp2.
  inverts keep Hsp1; inverts keep Hsp2.
  - (* and *)
(* previous and_inv spl_inv *)
Lemma sub_andlr_inv : forall A B A1 A2,
    algorithmic_sub A B -> spli A A1 A2 -> ordi B ->
    algorithmic_sub A1 B \/ algorithmic_sub A2 B
with  sub_orlr_inv : forall A B B1 B2,
    algorithmic_sub A B -> splu B B1 B2 -> ordu A ->
    algorithmic_sub A B1 \/ algorithmic_sub A B2.
Proof with s_elia.
  clear sub_andlr_inv.
  introv Hsub Hspl Hord.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub; solve_false; s_auto_unify; auto with *.
  - (* AS_arrow *) inverts Hord. inverts Hspl.
    + (* A0->B0 <| A0->A3 |> A0->B3 *) forwards*: IH H0 H8...
    + (* A4->A3 <| A0->A3 |> A5->A3 *) forwards*: sub_orlr_inv H H7...
  - (* AS_andl *) inverts

Admitted.

(*
Lemma sub_or_inv : forall A A1 A2 B,
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
  - forwards (?&?): sub_and_inv Hsub Hi.
    forwards (?&?): IH H...
    forwards (?&?): IH H0...
Qed.
*)
Lemma sub_orlr_inv : forall A B B1 B2,
    algorithmic_sub A B -> ordu A -> splu B B1 B2 ->
    algorithmic_sub A B1 \/ algorithmic_sub A B2.
Proof with (solve_false; s_auto_unify; try eassumption; s_elia; eauto 3 with AllHd).
  introv Hsub Hord Hspl.
  indTypSize (size_typ A + size_typ B).
  inverts Hsub...
Admitted. (*
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
*)
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
           try (forwards~ (?&?): sub_and_inv H1 H2; clear H1)
         | [ H1: algorithmic_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): sub_and_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ordi ?B, H1: algorithmic_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: sub_andlr_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algorithmic_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: sub_andlr_inv H1 Hord; clear H1)
      end;
  repeat try match goal with
         | [ H1: algorithmic_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): sub_or_inv H1 H2; clear H1)
         | [ H1: algorithmic_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): sub_or_inv H1; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: algorithmic_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: sub_orlr_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: algorithmic_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: sub_orlr_inv H1 Hord; clear H1)
             end.

(* no need in this version (ord conditions removed)
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
Proof with (solve_false; s_auto_unify; try eassumption; auto with *; auto_inv; try solve s_trans_autoIH).
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
          *** applys~ AS_orl H...
          *** applys~ AS_orr H...
        ** (* arrow *)
          inverts~ s2...
          *** applys~ AS_arrow...
          *** applys~ AS_orl H1...
          *** applys~ AS_orr H1...
      * applys AS_andl... (* ordu A spli A *) admit.
      * (* ordi B splu B *) admit.
      * (* spli B *) admit.
     (* * applys AS_andr... admit. *)
    + lets [Hi'|(?&?&Hi')]: ordi_or_split A...
      * applys AS_or Hu...
        ** (* ordi A splu A *) admit.
        ** (* ordi B splu B *) admit.
      * assert (algorithmic_sub x C)...
        (* splu A spli A *) admit.
        assert (algorithmic_sub x0 C)...
        admit.
        applys AS_or...
  - applys AS_and Hi...
    (* spli C *) admit. admit.
Qed.

#[local] Hint Resolve s_trans : AllHd.

Lemma sub_arrow : forall A1 A2 B1 B2,
    algorithmic_sub B1 A1 -> algorithmic_sub A2 B2 -> algorithmic_sub (t_arrow A1 A2) (t_arrow B1 B2).
Proof with (try eassumption; s_auto_unify; s_auto_inv; solve_false; s_elia; try solve [constructor; auto with AllHd]).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow A1 A2)...
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2)...
  lets [Hu1|(?&?&Hu1)]: ordu_or_split (t_arrow A1 A2)...
  lets [Hu2|(?&?&Hu2)]: ordu_or_split (t_arrow B1 B2)...
  - inverts Hi2.
    + forwards (?&?): sub_and_inv Hs2 H3...
      applys AS_and.
      econstructor; try eassumption.
      applys~ IH. s_elia.
      applys~ IH. s_elia.
    + forwards (?&?): sub_or_inv Hs1 H4.
      applys AS_and. applys SpI_arrowUnion; try eassumption.
      applys~ IH; s_elia. applys~ IH; s_elia.
  - inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: sub_andlr_inv Hs2 H3. inverts~ Hi2.
        applys AS_andl; try eassumption.
        econstructor. apply H3.
        applys~ IH. s_elia.
        applys AS_andr; try eassumption.
        econstructor. apply H3.
        applys~ IH. s_elia.
      * inverts Hi2.
        ** forwards (?&?): sub_and_inv Hs2 H4.
           applys AS_and. econstructor; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
        ** forwards (?&?): sub_or_inv Hs1 H5.
           applys AS_and. applys SpI_arrowUnion; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: sub_orlr_inv Hs1 H4. inverts~ Hi2.
        1: { applys AS_andl; try eassumption.
        applys SpI_arrowUnion; try eassumption.
        applys~ IH. s_elia. }
        1: { applys AS_andr; try eassumption.
        applys SpI_arrowUnion; try eassumption.
        applys~ IH. s_elia. }
      * inverts Hi2.
        ** forwards (?&?): sub_and_inv Hs2 H5.
           applys AS_and. econstructor; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
        ** forwards (?&?): sub_or_inv Hs1 H6.
           applys AS_and. applys SpI_arrowUnion; try eassumption.
           applys~ IH; s_elia. applys~ IH; s_elia.
Qed.

Lemma sub_orl : forall A B B1 B2,
    splu B B1 B2 -> algorithmic_sub A B1 -> algorithmic_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hspli Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ AS_orl Hspli.
  - applys~ algorithmic_sub_or Hu; applys IH Hspli; s_elia; applys s_trans Hs; applys sub_part2...
  - forwards~ [?|?]: sub_andlr_inv Hs Hi'...
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

Lemma sub_orr : forall A B B1 B2,
    splu B B1 B2 -> algorithmic_sub A B2 -> algorithmic_sub A B.
Proof with (eauto 3 with AllHd).
  introv Hspli Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ AS_orr Hspli.
  - applys~ algorithmic_sub_or Hu; applys IH Hspli; s_elia; applys s_trans Hs; applys sub_part2...
  - forwards~ [?|?]: sub_andlr_inv Hs Hi'...
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

Lemma sub_distArrU: forall A B C,
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

#[local] Hint Resolve sub_arrow sub_orl sub_orr sub_distArrU : AllHd.

Lemma arrow_inv : forall A B C D,
    algorithmic_sub (t_arrow A B) (t_arrow C D) -> (algorithmic_sub C A) /\ (algorithmic_sub B D).
Proof with (simpl in *; solve_false; s_auto_unify; try eassumption; s_auto_inv; eauto 3 with AllHd).
  introv s.
  indTypSize (size_typ (t_arrow A B) + size_typ (t_arrow C D)).
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow C D).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow A B).
  - inverts s...
  - inverts keep Hi1;
      forwards~ [?|?]: sub_andlr_inv s Hi1;
      forwards(IH1&IH2): IH H; try solve [s_elia];
        split; try eassumption; inverts~ Hi2...
  - (* uses and_inv_1 and_inv_2 *)
    forwards (?&?): sub_and_inv s Hi2.
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
#[local] Hint Resolve sub_refl : core.

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
    + applys sub_arrow...
    + applys* AS_and.
    + applys sub_part1...
    + applys sub_part1...
    + applys algorithmic_sub_or. eauto 4 with *. auto. auto.
    + applys sub_orl...
    + applys sub_orr...
    + applys AS_and...
    + applys AS_and... eauto 4 with *. eauto 4 with *.
    + applys sub_distArrU.
    + applys* AS_and...
    + applys algorithmic_sub_or. eauto 4 with *.
      applys AS_and... applys sub_orl... applys sub_orr...
    + applys algorithmic_sub_or. eauto 4 with *.
      applys sub_orl... applys sub_orr...
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
