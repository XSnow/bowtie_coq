Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.

(* Previous proved properties of distinguishability *)

Lemma distinguishability_splu_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, splu A A1 A2 -> Distinguishability A1 B /\ Distinguishability A2 B) /\
    (forall B1 B2, splu B B1 B2 -> Distinguishability A B1 /\ Distinguishability A B2).
Admitted.

Lemma distinguishability_spli_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, spli A A1 A2 -> ordu B -> Distinguishability A1 B \/ Distinguishability A2 B) /\
    (forall B1 B2, spli B B1 B2 -> ordu A -> Distinguishability A B1 \/ Distinguishability A B2).
Admitted.

Ltac inverts_all_distinguishability :=
  repeat lazymatch goal with
         | Dis: Distinguishability ?A (_ & _), Ord: ordu ?A |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_spli_inv Dis;
           forwards [?|?]: HB Ord; [ eauto | | ]; clear Dis
         | Dis: Distinguishability (_ & _) ?B, Ord: ordu ?B |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_spli_inv Dis;
           forwards [?|?]: HA Ord; [ eauto | | ]; clear Dis
         | Dis: Distinguishability ?A ?B, Ord: ordu ?A, Spl: spli ?B _ _ |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_spli_inv Dis;
           forwards [?|?]: HB Spl Ord; clear Dis
         | Dis: Distinguishability ?A (_ | _) |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HB; [ eauto | ]; clear Dis
         | Dis: Distinguishability (_ | _) ?B |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HA; [ eauto | ]; clear Dis
         | Dis: Distinguishability ?A ?B, Spl: splu ?B _ _ |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HB Spl; clear Dis
         | Dis: Distinguishability ?A ?B, Spl: splu ?A _ _ |- _ =>
           let HA := fresh "HA" in
           let HB := fresh "HB" in
           forwards (HA&HB): distinguishability_splu_inv Dis;
           forwards (?&?): HA Spl; clear Dis
         end.

Notation "A <<>> B"        := (Distinguishability A B)
                                (at level 65, B at next level, no associativity) : type_scope.

Definition typ_as_ftyp := fty_StackArg.
Coercion typ_as_ftyp : typ >-> Fty.

Ltac inverts_neg_false :=
  try match goal with
  | H: isNegTyp (_ & _) |- _ => inverts H
  | H: isNegTyp (_ | _) |- _ => inverts H
  end;
  match goal with
  | H: isNegTyp (t_rcd _ _) |- _ => inverts H
  | H: isNegTyp t_bot |- _ => inverts H
  end; fail.

#[export]
Hint Extern 0 => inverts_neg_false : FalseHd.

#[export]
 Hint Extern 1 =>
   match goal with
  | H1: isValTyp (_ & _) |- _ => inverts H1
  | H1: isValTyp (_ | _) |- _ => inverts H1
  | H1: isValTyp _ |- _ => inverts H1
   end; inverts_neg_false : FalseHd.

#[export]
Hint Extern 0 =>
match goal with
| H : binds _ _ nil |- _ => inverts H; fail
end : FalseHd.

#[export]
 Hint Extern 1 => match goal with
                 | H: DistinguishabilityAx _ _ |- _ => inverts~ H; fail
                  end : FalseHd.


Lemma distinguishability_rcd_inv : forall l A B,
    (t_rcd l A) <<>> (t_rcd l B) -> A <<>> B.
Admitted.
(******************************************************************************)

(* B.14 *)
Lemma distinguishability_on_valtyp : forall A B V,
    Distinguishability A B -> isValTyp V -> V <p A -> V <p B -> False.
Proof with solve_false.
  introv Dis Val SubA SubB.
  indTypSize (size_typ A + size_typ B).
  lets~ [Hu|(?&?&Hu)]: ordu_or_split A. now eauto.
  lets~ [Hu'|(?&?&Hu')]: ordu_or_split B. now eauto.
  - (* ordu A & ordu B *)
    inverts~ SubA...
    all: inverts~ SubB...

    Local Ltac first_match := try match goal with
                                  | |- _ <<>>  _ => try eassumption
                                  end.
    Local Ltac match_psub := try match goal with
                                 | |- _ <p  _ => eassumption
                                 | H: _ <p _ |- _ <p _ => applys PSub_In H
                                 end.
    Local Ltac inverts_disax := try match goal with
                                    | H: DistinguishabilityAx _ _ |- _ => inverts H; fail
                                    end.

    + apply distinguishability_rcd_inv in Dis.
      applys IH Dis; try eassumption; elia.
    + inverts Dis...
    + inverts Dis...
      all: applys IH; try eassumption; elia; eauto.
    + destruct H2... all: inverts Dis...
      all: applys IH; try eassumption; elia; eauto.
    + inverts Dis...
    + inverts Dis...
    + inverts_all_distinguishability.
      all: applys IH; try eassumption; elia; eauto.
    + destruct H1... all: inverts Dis...
      all: applys IH; try eassumption; elia; eauto.
    + inverts_all_distinguishability.
      applys IH H0; try eassumption; elia; eauto.
      applys IH H1; try eassumption; elia; eauto.
    + inverts_all_distinguishability.
      all: applys IH; try eassumption; elia; eauto.
    + inverts_all_distinguishability.
      all: applys IH; try eassumption; elia; eauto.
    + inverts_all_distinguishability.
      all: applys IH; try eassumption; elia; eauto.
    + try match goal with
          | H: isNegTyp _ |- _ => destruct H; inverts Dis; inverts_disax; solve_false;
                                    applys IH; first_match; match_psub; try eassumption; elia; eauto
          end.
    + try match goal with
          | H: isNegTyp _ |- _ => destruct H; inverts Dis; inverts_disax; solve_false;
                                    applys IH; first_match; match_psub; try eassumption; elia; eauto
          end.
    + try lazymatch goal with
          | H: isNegTyp _ |- _ => destruct H; inverts Dis; inverts_disax; solve_false;
                                    applys IH; first_match; match_psub; try eassumption; elia; eauto
          end.
    + destruct H0; destruct H2.
      all: inverts Dis; inverts_disax; solve_false;
        applys IH; first_match; match_psub; try eassumption; elia; eauto.
  - inverts_all_distinguishability.
    forwards~ [?|?]: psub_splu_inv Hu' SubB. clear SubB.
    applys IH H SubA; first_match; try eassumption; elia; eauto.
    applys IH H0 SubA; first_match; try eassumption; elia; eauto.
  - inverts_all_distinguishability.
    forwards~ [?|?]: psub_splu_inv Hu SubA. clear SubA.
    applys IH H SubB; first_match; try eassumption; elia; eauto.
    applys IH H0 SubB; first_match; try eassumption; elia; eauto.
Qed.
