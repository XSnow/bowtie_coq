(** This variant replaces the old distributivity rule by the two
 (A1 /\ A2) -> (B1 \/ B2) <: (A1 -> B1) \/ (A2 -> B2)
 (A1 -> B1) /\ (A2 -> B2) <: (A1 \/ A2) -> (B1 /\ B2)
*)

Require Import LibTactics.
Require Export Coq.micromega.Lia.
Require Export Definitions.


Create HintDb AllHd.
Create HintDb FalseHd.

(********************************************)
(*                                          *)
(*                   FalseHd                *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)

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

#[local] Hint Constructors ordi ordu spli splu : AllHd.

Lemma ordi_or_split: forall A,
    ordi A \/ exists B C, spli A B C
with ordu_or_split: forall A,
    ordu A \/ exists B C, splu A B C.
Proof with (eauto with *; intros).
  - intros. clear ordi_or_split. induction A...
    + (* arrow *)
      forwards [?|(?&?&?)]: IHA2...
      forwards* [?|(?&?&?)]: ordu_or_split A1...
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
(* FalseHd *)

(* splittable types and ordinary types are not overlapping *)
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

#[export]
Hint Extern 1 =>
  match goal with
  | H: t_and _ _ = t_or _ _ |- _ => inverts H
  | H: ordi (t_and _ _) |- _ => inverts H
  | H: ordu (t_or _ _) |- _ => inverts H
  | H: spli t_int _ _ |- _ => inverts H
  | H: splu t_int _ _ |- _ => inverts H
  | H: spli t_top _ _ |- _ => inverts H
  | H: splu t_top _ _ |- _ => inverts H
  | H: spli t_bot _ _ |- _ => inverts H
  | H: splu t_bot _ _ |- _ => inverts H
  | H: spli ?A _ _, H': ordi ?A |- _ => false; applys spli_ord_false H H'
  | H: splu ?A _ _, H': ordu ?A |- _ => false; applys splu_ord_false H H'
  | [H1: ordi ?B , H2: spli (t_arrow _ ?B) _ _ |- _ ] => (inverts H2; false; applys spli_ord_false H1; eassumption)
  | [H1: ordu ?B , H2: splu (t_arrow _ ?B) _ _ |- _ ] => (inverts H2; false; applys spli_ord_false H1; eassumption)
  | [H1: ordi (t_arrow _ ?B) , H2: spli ?B _ _ |- _ ] => (inverts H1; false; applys spli_ord_false H2; trivial)
  | [H1: ordu (t_arrow _ ?B) , H2: splu ?B _ _ |- _ ] => (inverts H1; false; applys spli_ord_false H2; trivial)
end : FalseHd.

(******************************************************************************)
(* lemmas for ordinary *)
Lemma splu_keep_ordi : forall A B C,
   ordi A -> splu A B C -> ordi B /\ ordi C
with spli_keep_ordu : forall A B C,
   ordu A -> spli A B C -> ordu B /\ ordu C.
Proof.
  - introv Hord Hspl. clear splu_keep_ordi.
    inductions Hspl; try inverts~ Hord; eauto.
    + split; constructor*; forwards~ (?&?): spli_keep_ordu H0.
    + split; constructor*; forwards~ (?&?): spli_keep_ordu H.
  - introv Hord Hspl. clear spli_keep_ordu.
    inductions Hspl; try inverts~ Hord; eauto.
    + split; constructor*; forwards~ (?&?): splu_keep_ordi H.
    + forwards~ (?&?): splu_keep_ordi H0.
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

#[export] Hint Immediate spli_keep_ordu_l spli_keep_ordu_r
     splu_keep_ordi_l splu_keep_ordi_r : core.


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
  assert (SizeInd: exists i, s < i) by eauto;
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
Proof.
  -
    intro T. clear spli_unique.
    induction T; intros;
      inverts H; inverts H0; auto with FalseHd;
        try match goal with
          [ H1: splu ?A _ _, H2: splu ?A _ _ |- _ ] => (
            forwards* (?&?): splu_unique H1 H2;
            subst~)
        end;
        try repeat match goal with
          [ H1: spli ?A _ _, H2: spli ?A _ _, IH: forall A1 A2 B1 B2 : typ,
                spli ?A _ _ -> _ |- _ ] => (
            forwards* (?&?): IH H1 H2; clear H1 H2;
            subst~)
        end.
  -
    intro T. clear splu_unique.
    induction T; intros;
      inverts H; inverts H0; auto with FalseHd;
        try match goal with
          [ H1: spli ?A _ _, H2: spli ?A _ _ |- _ ] => (
            forwards* (?&?): spli_unique H1 H2;
            subst~)
        end;
        try repeat match goal with
          [ H1: splu ?A _ _, H2: splu ?A _ _, IH: forall A1 A2 B1 B2 : typ,
                splu ?A _ _ -> _ |- _ ] => (
            forwards* (?&?): IH H1 H2; clear H1 H2;
            subst~)
        end.
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_unify              *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no auto with FalseHd at the end                *)
(*                                          *)
(********************************************)
Ltac s_auto_unify :=
  simpl in *;
  try solve [applys SpI_and];
  try solve [applys SpU_or];
  try repeat match goal with
         | [ H1: spli (t_and _ _) _ _ |- _ ] =>
            inverts H1
         | [ H1: splu (t_or _ _) _ _ |- _ ] =>
            inverts H1
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

#[local] Hint Constructors algorithmic_sub : AllHd.

Ltac sub_part_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ < _ -> _ |- algorithmic_sub ?A ?B ] =>
  (forwards (IH1&IH2): IH A B; auto 4 with *; eauto 4 with AllHd; s_elia)
end.

Lemma sub_part : forall A B,
    (i_part A B -> algorithmic_sub A B)
    /\ (ordi A -> ordi B -> u_part B A -> algorithmic_sub A B).
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
      * destruct B; s_auto_unify; auto with FalseHd...
        **(* arrow *)
          constructor...
      * applys~ AS_or Hu...
    + applys AS_andl...
    + applys AS_andr...
  - (* spl B *)
    lets~ (?&?): i_part_spl Hp Hi.
    applys AS_and Hi...

  --
  introv Ho1 Ho2 Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - (* ord A *)
    inverts Hp.
    + lets [Hi|(?&?&Hi)]: ordi_or_split A.
      * destruct A; s_auto_unify; auto with FalseHd...
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

Lemma sub_part_spli_1 : forall A B C,
    spli A B C -> algorithmic_sub A B.
Proof.
  introv.
  pose proof (sub_part A B).
  destruct* H.
Qed.

Lemma sub_part_spli_2 : forall A B C,
    spli A B C -> algorithmic_sub A C.
Proof.
  introv.
  pose proof (sub_part A C).
  destruct* H.
Qed.

Lemma sub_part_splu_1 : forall A B C,
    splu A B C -> ordi A -> algorithmic_sub B A.
Proof.
  intros.
  assert (ordi B) by eauto.
  pose proof (sub_part B A).
  destruct* H2.
Qed.

Lemma sub_part_splu_2 : forall A B C,
    splu A B C -> ordi A -> algorithmic_sub C A.
Proof.
  intros.
  assert (ordi B) by eauto.
  pose proof (sub_part C A).
  destruct* H2.
Qed.

#[local] Hint Resolve sub_refl : AllHd.
#[local] Hint Resolve sub_part_spli_1 sub_part_spli_2 sub_part_splu_1 sub_part_splu_2 : AllHd.
#[local] Hint Immediate sub_part_spli_1 sub_part_spli_2 sub_part_splu_1 sub_part_splu_2 : core.

(***********************************************************************)
(* ordinary & split hints *)

#[export]
 Hint Extern 1 (ordi ?t) =>
  match goal with
  | H: ordi (t_or t _) |- _ => inverts H; trivial
  | H: ordi (t_or _ t) |- _ => inverts H; trivial
  | H: ordi (t_arrow _ t) |- _ => inverts H; trivial
  | H: ordu (t_arrow t _) |- _ => inverts H; trivial
  end : core.

#[export]
 Hint Extern 1 (ordu ?t) =>
  match goal with
  | H: ordu (t_and t _) |- _ => inverts H; trivial
  | H: ordu (t_and _ t) |- _ => inverts H; trivial
  | H: ordu (t_arrow _ t) |- _ => inverts H; trivial
  | H: ordi (t_arrow t _) |- _ => inverts H; trivial
  end : core.

(*********** editing ***************)
#[export]
 Hint Extern 1 (ordi ?t) =>
  repeat match goal with
         | H: ordi (t_or _ _) |- _ => inverts H
         | H: ordi (t_or _ _) |- _ => inverts H
         | H: ordu (t_arrow _ _) |- _ => inverts H
         | H: ordi (t_arrow _ _) |- _ => inverts H
         end; constructor; eauto 2 using splu_keep_ordi_l, splu_keep_ordi_r, spli_keep_ordu_l, spli_keep_ordu_r: core.

#[export]
 Hint Extern 1 (ordu ?t) =>
  repeat match goal with
         | H: ordu (t_and _ _) |- _ => inverts H
         | H: ordu (t_and _ _) |- _ => inverts H
         | H: ordu (t_arrow _ _) |- _ => inverts H
         | H: ordi (t_arrow _ _) |- _ => inverts H
         end; constructor; eauto 2 using splu_keep_ordi_l, splu_keep_ordi_r, spli_keep_ordu_l, spli_keep_ordu_r : core.

#[export] Hint Immediate SpI_and SpI_orl SpI_arrowU SpU_or SpU_andl SpU_arrowU : core.

Hint Extern 1 (spli _ _ _) =>
match goal with
  | H: spli ?t _ _ |- spli (t_or ?t _) _ _ => applys SpI_orl H
  | H: spli ?t _ _ |- spli (t_arrow _ ?t) _ _ => applys SpI_arrowI H
  | H: splu ?t _ _ |- spli (t_arrow ?t _) _ _ => applys~ SpI_arrowU H
  | H: spli ?t _ _ |- spli (t_or _ ?t) _ _ => applys~ SpI_orr H
end : core.

Hint Extern 1 (splu _ _ _) =>
match goal with
  | H: splu ?t _ _ |- splu (t_or ?t _) _ _ => applys SpU_andl H
  | H: splu ?t _ _ |- splu (t_arrow _ ?t) _ _ => applys SpU_arrowU H
  | H: spli ?t _ _ |- splu (t_arrow ?t _) _ _ => applys~ SpU_arrowI H
  | H: splu ?t _ _ |- splu (t_or _ ?t) _ _ => applys~ SpU_andr H
end : core.


(**********************************************************************)
(* algorithm correctness *)

Lemma sub_and_r_inv : forall A B B1 B2,
    algorithmic_sub A B -> spli B B1 B2 -> algorithmic_sub A B1 /\ algorithmic_sub A B2.
Proof.
  intros.
  induction H; intros; s_auto_unify; auto with *.
Qed.

Lemma sub_and_l_inv : forall A B A1 A2,
    algorithmic_sub A B -> spli A A1 A2 -> ordi B ->
    algorithmic_sub A1 B \/ algorithmic_sub A2 B.
Proof.
  introv Hsub Hord Hspl.
  inverts Hsub; intros; s_auto_unify; auto with *.
Qed.


Lemma sub_or_r_inv : forall A B B1 B2,
    algorithmic_sub A B -> splu B B1 B2 -> ordu A -> ordi A -> ordi B ->
    algorithmic_sub A B1 \/ algorithmic_sub A B2.
Proof.
  introv HS HsuB HouA HoiA HoiB. gen B1 B2.
  induction HS; intros; s_auto_unify; auto with *.
Qed.

Lemma sub_or_l_inv : forall A A1 A2 B,
    algorithmic_sub A B -> splu A A1 A2 -> ordi A -> ordi B ->
    algorithmic_sub A1 B /\ algorithmic_sub A2 B.
Proof.
  introv HS HsuA HoiA HoiB. gen A1 A2.
  induction HS; intros; s_auto_unify; auto with *.
Qed.

(********************************************)
(*                                          *)
(*             Ltac auto_inv                *)
(*                                          *)
(*  extends choose_unify                    *)
(*  no auto with FalseHd at the end         *)
(*                                          *)
(********************************************)
Ltac s_auto_inv :=
  repeat try match goal with
         | [ H1: algorithmic_sub ?A ?B, H2: spli ?B _ _ |- _ ] =>
           try (forwards~ (?&?): sub_and_r_inv H1 H2; clear H1)
         | [ H1: algorithmic_sub ?A (t_and _ _) |- _ ] =>
           try (forwards~ (?&?): sub_and_r_inv H1; clear H1)
      end;
  repeat try match goal with
         | [ Hord: ordi ?B, H1: algorithmic_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: sub_and_l_inv H1 H2 Hord; clear H1)
         | [ Hord: ordi ?B, H1: algorithmic_sub (t_and  _ _)  ?B |- _ ] =>
           try (forwards~ [?|?]: sub_and_l_inv H1 Hord; clear H1)
         | [ H1: algorithmic_sub ?A ?B, H2: spli ?A _ _ |- _ ] =>
           try (forwards~ [?|?]: sub_and_l_inv H1 H2; clear H1)
      end;
  repeat try match goal with
         | [ H1: algorithmic_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): sub_or_l_inv H1 H2; clear H1)
         | [ H1: algorithmic_sub (t_or _ _) ?B |- _ ] =>
           try (forwards~ (?&?): sub_or_l_inv H1; clear H1)
         (* aggressive *)
         | [ H1: algorithmic_sub ?A ?B, H2: splu ?A _ _ |- _ ] =>
           try (forwards~ (?&?): sub_or_l_inv H1 H2; clear H1)
         end;
  repeat try match goal with
         | [ Hord: ordu ?A, H1: algorithmic_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: sub_or_r_inv H1 Hord H2; clear H1)
         | [ Hord: ordu ?A, H1: algorithmic_sub ?A (t_or _ _) |- _ ] =>
           try (forwards~ [?|?]: sub_or_r_inv H1 Hord; clear H1)
         (* aggressive *)
         | [ H1: algorithmic_sub ?A ?B, H2: splu ?B _ _ |- _ ] =>
           try (forwards~ [?|?]: sub_or_r_inv H1 H2; clear H1)
             end.


Lemma algorithmic_sub_or : forall A A1 A2 B,
    splu A A1 A2 -> algorithmic_sub A1 B -> algorithmic_sub A2 B -> algorithmic_sub A B.
Proof with (s_auto_unify; try eassumption; s_auto_inv; s_elia; auto).
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
      Abort. (*
    + applys~ AS_andl Hi'...
  - applys~ AS_and Hi...
    applys IH... applys IH...
Qed.

#[local] Hint Resolve algorithmic_sub_or : AllHd.
*)

Ltac s_trans_autoIH :=
  match goal with
  | [ IH: forall A B : typ, _ , H1: algorithmic_sub ?A  ?B , H2: algorithmic_sub ?B  ?C |- algorithmic_sub ?A  ?C ] =>
    (applys~ IH H1 H2; s_elia; auto)
  | [ IH: forall A B : typ, _ , H1: algorithmic_sub ?A  ?B  |- algorithmic_sub ?A  ?C ] =>
    (applys~ IH H1; s_elia; constructor~)
  | [ IH: forall A B : typ, _ , H2: algorithmic_sub ?B  ?C |- algorithmic_sub ?A  ?C ] =>
    (applys~ IH H2; s_elia; constructor~)
  end.

Lemma s_trans_ordi : forall A B C, ordi B -> ordi C -> algorithmic_sub A B -> algorithmic_sub B C -> algorithmic_sub A C.
Proof.
  introv Hord1 Hord2 Hsub1 Hsub2. gen A.
  induction~ Hsub2; intros.
  - (* bot *) admit.
  - (* arrow *) inverts~ Hsub1.
Abort. (* depends on ordu lemma in arrow case *)


Lemma s_trans : forall A B C, algorithmic_sub A B -> algorithmic_sub B C -> algorithmic_sub A C.
Proof with (s_auto_unify; auto with *; s_auto_inv; try solve s_trans_autoIH).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets [HiC|(?&?&HiC)]: ordi_or_split C...
  lets [HiB|(?&?&HiB)]: ordi_or_split B...
  lets [HiA|(?&?&HiA)]: ordi_or_split A...
  - (* all ordi *)
    lets [HuA|(?&?&HuA)]: ordu_or_split A...
    2: applys~ AS_or HuA...
    lets [HuB|(?&?&HuB)]: ordu_or_split B...
    2: (* ordu A, splu B *)
      forwards~ [HS|HS]: sub_or_r_inv s1 HuB...
    lets [HuC|(?&?&HuC)]: ordu_or_split C...
    2: {
      forwards~ [HS|HS]: sub_or_r_inv s2 HuC...
      + applys~ AS_orl HuC...
      + applys~ AS_orr HuC...
    }
  (* all ordi and ordu *)
    inverts s1; s_auto_unify...
    + (* top *)
      inverts~ s2...
    + (* arrow *)
      inverts~ s2...
      * applys~ AS_arrow...
  - applys~ AS_andl HiA...
  - applys~ AS_andr HiA...
  - applys~ AS_and HiC...
Qed.

#[local] Hint Resolve s_trans : AllHd.


#[export] Hint Immediate OI_top OI_bot OI_int OI_arrow OI_or
 OU_top OU_bot OU_int OU_arrow OU_and
 SpI_and SpI_orl SpI_orr SpI_arrowI SpI_arrowU
 SpU_or SpU_andl SpU_andr SpU_arrowI SpU_arrowU : core.

#[local] Hint Constructors i_part : core.

Lemma spli_splu : forall A A1 A2 B B1 B2 C,
    spli A A1 A2 -> splu A B C -> spli B B1 B2 -> u_part A1 B1.
Proof with s_auto_unify.
  intros. gen B C B1 B2.
  induction H; intros...
  - inverts* H0... eauto. eauto.
  - eauto.
  - forwards~: IHspli H0 H2.

    right. intuition eauto.
  - left~.
  - inverts H0.
    + right. exists. split*.
    + forwards [?|(?&?&?&?)]: IHspli H5.
      * admit.
      * right. exists. split*. admit. (* provable *)
  - inverts H1.
    + right. exists. split*.

      inverts H1. inverts* H0.

Lemma spli_splu : forall A A1 A2 B C,
    spli A A1 A2 -> splu A B C -> ordi B \/ exists B1 B2, spli B B1 B2 /\ u_part A1 B1.
Proof.
  intros. gen B C.
  induction H; intros; s_auto_unify.
  - inverts* H0.
  - right. intuition eauto.
  - left~.
  - inverts H0.
    + right. exists. split*.
    + forwards [?|(?&?&?&?)]: IHspli H5.
      * admit.
      * right. exists. split*. admit. (* provable *)
  - inverts H1.
    + right. exists. split*.

      inverts H1. inverts* H0.
  - inverts* H0.


Lemma sub_part_2 : forall A B,
    u_part B A -> algorithmic_sub A B.
Proof with (try eassumption; auto 4 with *).
  introv.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split A.
  - assert (ordi B) by admit. pose proof (sub_part A B). intuition eauto.
  - (* ord B *)
    inverts Hp.
    + lets [Hu|(?&?&Hu)]: ordu_or_split B.
      * destruct B; s_auto_unify; auto with FalseHd...
        **(* arrow *)
          constructor...
      * applys~ AS_or Hu...
    + applys AS_andl...
    + applys AS_andr...
  - (* spl B *)
    lets~ (?&?): i_part_spl Hp Hi.
    applys AS_and Hi...

  --
  introv Ho1 Ho2 Hp.
    lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - (* ord A *)
    inverts Hp.
    + lets [Hi|(?&?&Hi)]: ordi_or_split A.
      * destruct A; s_auto_unify; auto with FalseHd...
        **(* arrow *)
          constructor...
      * applys~ AS_and Hi...
    + applys AS_orl...
    + applys AS_orr...
  - (* spl B *)
    lets~ (?&?): u_part_spl Hp Hu.
    applys AS_or Hu...
Qed.

Lemma sub_part_splu_1_p : forall A B C,
    splu A B C -> algorithmic_sub B A.
Proof.
  intros.
  indTypSize (size_typ A).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split A.
  - eauto.
  - applys* AS_and. inverts H.
    + assert (algorithmic_sub (t_or B C) x) by eauto.
  pose proof (sub_part B A).
  destruct* H2.
Qed.

Lemma sub_arrow : forall A1 A2 B1 B2,
    algorithmic_sub B1 A1 -> algorithmic_sub A2 B2 -> algorithmic_sub (t_arrow A1 A2) (t_arrow B1 B2).
Proof with (try eassumption; s_auto_unify; s_auto_inv; auto with FalseHd; s_elia).
  introv Hs1 Hs2.
  indTypSize (size_typ (t_arrow A1 A2) + size_typ (t_arrow B1 B2)).
  lets [Hi1|(?&?&Hi1)]: ordi_or_split (t_arrow B1 B2).
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow A1 A2).
  lets [Hu1|(?&?&Hu1)]: ordu_or_split (t_arrow A1 A2).
  lets [Hu2|(?&?&Hu2)]: ordu_or_split (t_arrow B1 B2).
  - (* all ord *) constructor~.
  - (* splu B1->B2 *) inverts Hu2...
    + (* spli B1 *)
      applys AS_orl (t_arrow A0 B2)... applys IH...
    + (* spli B1 *)
      applys* AS_orr. applys IH...
    + (* splu B2 *)
      applys AS_orl (t_arrow B1 B0) (t_arrow B1 B3)... applys IH...
    + (* splu B2 *)
      applys AS_orr (t_arrow B1 B0) (t_arrow B1 B3)... applys IH...
  - (* splu A1->A2 *) inverts Hu1...
    + applys AS_or... applys IH... applys IH...
    + applys AS_or... applys IH... applys IH...
  - (* spli A1-> A2 *) inverts Hi2.
    + forwards~ [?|?]: sub_and_l_inv Hs2 H3.
      * applys* AS_andl. applys~ IH...
      * applys* AS_andr. applys~ IH...
    + forwards~ [?|?]: sub_or_r_inv Hs1.


    + forwards (?&?): sub_and_r_inv Hs2 H3...
      applys AS_and... applys~ IH... applys~ IH...
    + forwards (?&?): sub_or_l_inv Hs1 H4.
      applys AS_and. applys SpI_arrowUnion; try eassumption.
      applys~ IH; s_elia. applys~ IH; s_elia.
  - inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: sub_and_l_inv Hs2 H3. inverts~ Hi2.
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
  -


  2: { applys AS_and Hi2.
       - inverts Hi2.
         + applys~ IH...
         + applys~ IH. applys s_trans Hs1. }
  2: { applys }
  lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2)...
  lets [Hu1|(?&?&Hu1)]: ordu_or_split (t_arrow A1 A2)...
  lets [Hu2|(?&?&Hu2)]: ordu_or_split (t_arrow B1 B2)...
  - inverts Hu2...
    + (* spli B1 *)
      applys* AS_orl (t_arrow A0 B2). constructor*. constructor~.
      admit.
    + (* splu B2 *)
      applys* AS_orl (t_arrow B1 B0) (t_arrow B1 B3). constructor*.
      applys IH Hs1 H...
    + (* splu B2 *)
      applys* AS_orr (t_arrow B1 B0) (t_arrow B1 B3). constructor*.
      applys IH Hs1 H...
  - inverts Hu1.
    + forwards (?&?): sub_and_r_inv Hs2 H3...
      applys AS_and.
      econstructor; try eassumption.
      applys~ IH. s_elia.
      applys~ IH. s_elia.
    + forwards (?&?): sub_or_inv Hs1 H4.
      applys AS_and. applys SpI_arrowUnion; try eassumption.
      applys~ IH; s_elia. applys~ IH; s_elia.
  - inverts Hi1.
    + lets [Hi2|(?&?&Hi2)]: ordi_or_split (t_arrow B1 B2).
      * forwards~ [?|?]: sub_and_l_inv Hs2 H3. inverts~ Hi2.
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
  introv Hspl Hs.
  indTypSize (size_typ A + size_typ B).
  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  - applys* s_trans Hs.
  - applys AS_and Hi.
    + applys~ s_trans B1.
      applys* s_trans B.
      assert ( algorithmic_sub)

  lets [Hi|(?&?&Hi)]: ordi_or_split B.
  lets [Hi'|(?&?&Hi')]: ordi_or_split A.
  lets [Hu|(?&?&Hu)]: ordu_or_split A.
  - applys~ AS_orl Hspli.
  - applys~ AS_or Hu; applys IH Hspli; s_elia; applys s_trans Hs...
  - forwards~ [?|?]: sub_and_l_inv Hs Hi'...
  - inverts Hspli; inverts Hi; auto with FalseHd; s_auto_unify;
    try solve [applys~ AS_and;
        applys~ IH; s_elia; applys~ s_trans; eauto with AllHd].
    + s_auto_inv. applys* AS_and.
      applys~ IH H; s_elia.
    + s_auto_inv. applys* AS_and.
      applys~ IH H0; s_elia.
    + applys~ IH Hs; s_elia.
Qed.


*)
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
  - forwards~ [?|?]: sub_and_l_inv Hs Hi'...
      applys~ AS_andl Hi'. applys~ IH Hspli. s_elia.
      applys~ AS_andr Hi'. applys~ IH Hspli. s_elia.
  - inverts Hspli; inverts Hi; auto with FalseHd; s_auto_unify.
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
  - inverts Hspli; inverts Hi; auto with FalseHd; s_auto_unify.
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
Proof with (simpl in *; auto with FalseHd; s_auto_unify; try eassumption; s_auto_inv; eauto 3 with AllHd).
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
Proof with (simpl in *; auto with FalseHd; jauto; s_elia; try solve [right; intros HF; s_auto_inv; inverts HF; simpl in *; auto with FalseHd]; eauto 3 with AllHd).
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
