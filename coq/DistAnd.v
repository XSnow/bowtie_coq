(*****************************************************)
(* This file is to prove rule DS-distAnd in Fig. 4   *)
(* can be derived by the rest rules                  *)
(* So removing it does not affect the expressiveness *)
(* of the declarative system                         *)
(*****************************************************)

Require Import LibTactics.
Require Import syntax_ott.

#[local]
 Hint Constructors declarative_subtyping_distor : core.

Lemma distor_symm_or : forall A1 A2,
    declarative_subtyping_distor (t_or A1 A2) (t_or A2 A1).
Proof.
  introv.
  applys~ DSO_or.
Qed.

Theorem distor_eqv_distand : forall A1 A2 B,
    declarative_subtyping_distor (t_and (t_or A1 A2) B) (t_or (t_and A1 B) (t_and A2 B)).
Proof.
  introv.
  applys DSO_trans.
  2: { applys DSO_distOr. }
  applys DSO_and.
  1: { applys DSO_trans (t_or (t_and A2 B) A1).
       applys DSO_trans.
       2: { applys DSO_distOr. }
       applys~ DSO_and.
       1: { applys DSO_trans. applys~ DSO_andl. applys~ DSO_or.
       }
       2: { applys~ DSO_or. }
       applys DSO_trans. applys~ DSO_andr. applys~ DSO_orl.
  }
  applys DSO_trans. applys~ DSO_andr. applys~ DSO_orl.
Qed.
