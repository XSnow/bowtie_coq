Require Import LibTactics.
Require Import TypeSize.
Require Import Duotyping.
Require Export syntax_ott.

#[local] Hint Constructors duo : core.

(* Theorem 4.5 Soundness and Completeness of Algorithmic Duotyping *)
(* A ♢a B if and only if A ♢ B *)
Theorem duotyping_dual_eqv_to_duotyping : forall m A B,
    duo A m B <-> sub A m B.
Proof.
  split; introv H.
  - induction~ H; try solve [econstructor; try eassumption; auto].
    + applys~ sub_rev.
  -
    gen m. indTypSize (size_typ A + size_typ B).
    inverts~ H; try solve [econstructor; try eassumption; applys IH; elia; auto].
    + (* bot *)
      lets [Hi1|(?&?&Hi1)]: ord_or_split m B.
      * applys~ SD_dual.
        destruct~ m.
      * applys SD_and; try eassumption; applys IH; elia; auto.
    + (* or *)
      applys~ SD_dual.
      applys SD_and H2; applys IH; elia; auto; applys~ sub_rev.
    + (* orl *)
      applys~ SD_dual.
      applys SD_andl H3; try eassumption; applys IH; elia; auto; applys~ sub_rev.
    + (* orr *)
      applys~ SD_dual.
      applys SD_andr H3; try eassumption; applys IH; elia; auto; applys~ sub_rev.
Qed.
