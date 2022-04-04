Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export ApplyTy.


Lemma matchty_total : forall l A,
    lc_typ A -> (exists B, MatchTy l A B) \/ NMatchTy l A.
Proof with destruct_conj.
  introv Lc.
  induction* Lc.
  - (* rcd *) case_eq (@eq_dec _ label_dec l5 l); intros.
     now subst*.
     now right*.
  - (* and *)
    forwards [?|?]: IHLc1... forwards [?|?]: IHLc2...
    all: now eauto.
  - (* or *)
    forwards [?|?]: IHLc1... all: forwards [?|?]: IHLc2...
    all: now eauto.
Qed.

Ltac case_matchty l A := forwards [(?&?)|?]: matchty_total l A; auto.

Lemma matchty_contradication : forall l A B,
   MatchTy l A B -> NMatchTy l A -> False.
Proof.
  introv HM HN.
  induction HM; inverts~ HN.
Qed.

#[export] Hint Extern 0 =>
match goal with
| H1: MatchTy ?l ?A _ , H2: NMatchTy ?l ?A |- _ => false; applys matchty_contradication H1 H2
| H: MatchTy _ _ _ |- _ => inverts H; fail
| H: NMatchTy _ _ |- _ => inverts H; fail
end : FalseHd.

Lemma matchty_unique : forall l A B C,
    MatchTy l A B -> MatchTy l A C -> B = C.
Proof.
  introv HM1 HM2. gen B C.
  induction A; intros; inverts HM1; inverts~ HM2; solve_false.
  repeat match goal with
              | H1: MatchTy ?l A1 _ , H2: MatchTy ?l A1 _ |- _ =>
                forwards: IHA1 H1 H2; try eassumption; clear H1 H2
              | H1: MatchTy ?l A2 _ , H2: MatchTy ?l A2 _ |- _ =>
                forwards: IHA2 H1 H2; try eassumption; clear H1 H2
              end; subst~.
  repeat match goal with
              | H1: MatchTy ?l A1 _ , H2: MatchTy ?l A1 _ |- _ =>
                forwards: IHA1 H1 H2; try eassumption; clear H1 H2
              | H1: MatchTy ?l A2 _ , H2: MatchTy ?l A2 _ |- _ =>
                forwards: IHA2 H1 H2; try eassumption; clear H1 H2
         end; subst~.
Qed.

Ltac matchty_unify :=
  repeat match goal with
         | [ H1: MatchTy ?A ?B _ , H2: MatchTy ?A ?B _ |- _ ] =>
           (forwards : matchty_unique H1 H2;
            subst; clear H2)
             end.

Lemma nmatchty_lc : forall l A, NMatchTy l A -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Extern 1 (lc_typ _) => applys nmatchty_lc ; eassumption : core.

Lemma matchty_lc_1 : forall l A B, MatchTy l A B -> lc_typ A.
Proof.  introv H.  induction* H. Qed.

Lemma matchty_lc_2 : forall l A B, MatchTy l A B -> lc_typ B.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Extern 1 (lc_typ _) => applys matchty_lc_1 ; eassumption : core.
#[export] Hint Extern 1 (lc_typ _) => applys matchty_lc_2 ; eassumption : core.

Ltac matchty_inv :=
  repeat match goal with
      | H: MatchTy _ (_ | _) _ |- _ => inverts H
      | H: MatchTy _ (_ & _) _ |- _ => inverts H
      | H: NMatchTy _ (_ | _) |- _ => inverts H
      | H: NMatchTy _ (_ & _) |- _ => inverts H
      | H: MatchTy _ (t_rcd _ _) _ |- _ => inverts H
      | H: NMatchTy _ (t_rcd _ _) |- _ => inverts H
         end.

Lemma nmatchty_spli_1 : forall l A B C,
    spli A B C -> NMatchTy l B -> NMatchTy l A.
Proof.
  introv Spl NM.
  induction* Spl; matchty_inv; eauto.
Qed.

Lemma nmatchty_spli_2 : forall l A B C,
    spli A B C -> NMatchTy l C -> NMatchTy l A.
Proof.
  introv Spl NM.
  induction* Spl; matchty_inv; eauto.
Qed.

#[export] Hint Immediate nmatchty_spli_1 nmatchty_spli_2 : core.

(* B.9 *)
Lemma matchty_spli : forall l A B B' C C',
    spli A B C -> MatchTy l B B' -> MatchTy l C C' ->
    exists A', MatchTy l A A' /\ (B' & C') <: A'.
(*    match l [ (Box_l A) & (B1->B2) ] | (Box_l C) => C *)
(*  XXX  /\ (spli A' B' C' \/ (A' = B' /\ B' = C')) XXX *)
Proof with destruct_conj; subst.
  introv Spl Mch1 Mch2. gen B' C'.
  induction Spl; intros; try solve [exists*]; solve_false.
  - matchty_inv; matchty_unify; solve_false.
    all: try solve [
               forwards ? ? ? : IHSpl; try eassumption;
               exists; splits; [eauto | auto 3] ].
    all: try solve [ exists; splits; eauto ].
    + forwards ? ? ? : IHSpl; try eassumption.
      exists; splits; [eauto | auto 3].
      applys DSub_Trans. { applys~ DSub_CovDistIUnionL. }
      convert2asub. match_or; auto.
  - matchty_inv; matchty_unify; solve_false.
    all: try solve [
               forwards ? ? ? : IHSpl; try eassumption;
               exists; splits; [eauto | auto 3] ].
    all: try solve [ exists; splits; eauto ].
    + forwards ? ? ? : IHSpl; try eassumption.
      exists; splits; [eauto | auto 3].
      applys DSub_Trans. { applys~ DSub_CovDistIUnionR. }
      convert2asub. match_or; auto.
  - matchty_inv; matchty_unify; solve_false.
    exists. split~. convert2asub. applys* ASub_and Spl.
Qed.


Lemma matchty_spli_1 : forall l A A' B C,
    spli A B C -> MatchTy l A A' ->
    exists B', MatchTy l B B' /\ A' <: B'.
Proof with try eassumption; eauto.
  introv Spl Mat. gen A'.
  induction Spl; intros; try solve [exists*]; solve_false; matchty_inv.
  all: try solve [ forwards ? ? ? : IHSpl; try eassumption; eauto].
  1: now exists*.
  1: { case_matchty l A1; exists*. }
  1: { case_matchty l B1; exists*. }
  1: { exists. splits~.
       convert2asub. use_left_l... }
Qed.


Lemma matchty_spli_2 : forall l A A' B C,
    spli A B C -> MatchTy l A A' ->
    exists C', MatchTy l C C' /\ A' <: C'.
Proof with try eassumption; eauto.
  introv Spl Mat. gen A'.
  induction Spl; intros; try solve [exists*]; solve_false; matchty_inv.
  all: try solve [ forwards ? ? ? : IHSpl; try eassumption; eauto].
  1: now exists*.
  1: { case_matchty l A2; exists*. }
  1: { case_matchty l B2; exists*. }
  1: { exists. splits~.
       convert2asub. use_right_l... }
Qed.

(* NOT PRECISE ENOUGH; CANNOT SOLVE THE CASE BY THIS LEMMA
Lemma matchty_splu : forall l A A' B C,
    splu A B C -> MatchTy l A A' ->
    (exists B', MatchTy l B B' /\ B' <: A') \/
    (exists C', MatchTy l C C' /\ C' <: A').
Proof with try eassumption; eauto.
  introv Spl Mat. gen A'.
  induction Spl; intros; try solve [exists*]; solve_false; matchty_inv.
  1,3: try solve [left; now exists*].
  1: right; now exists*.
  1-2: try forwards [?|?]: IHSpl; try eassumption; destruct_conj.
  1,3: left; now exists*.
  1,2: right; now exists*.
  1: (* rcd *){
       left; exists. split~.
       convert2asub. use_left_r... }
Qed. *)

Lemma matchty_splu_1 : forall l A B B' C,
    splu A B C -> MatchTy l B B' ->
    exists A', MatchTy l A A' /\ B' <: A'.
Proof with try eassumption; eauto.
  introv Spl Mat. gen B'.
  induction Spl; intros; try solve [exists*]; solve_false; matchty_inv.
  1: { case_matchty l B; exists*. }
  all: try solve [ forwards ? ? ? : IHSpl; try eassumption; eauto].
  1: { exists. splits~.
       convert2asub. use_left_r... }
Qed.

Lemma matchty_splu_2 : forall l A B C C',
    splu A B C -> MatchTy l C C' ->
    exists A', MatchTy l A A' /\ C'  <: A'.
Proof with try eassumption; eauto.
  introv Spl Mat. gen C'.
  induction Spl; intros; try solve [exists*]; solve_false; matchty_inv.
  1: { case_matchty l A; exists*. }
  all: try solve [ forwards ? ? ? : IHSpl; try eassumption; eauto].
  1: { exists. splits~.
       convert2asub. use_right_r... }
Qed.

(* B.10 *)
(*  match l [ (Box_l A) & (B1->B2) ] | (Box_l C) => C *)
(*  match l [ (Box_l A) | (Box_l C) ] & [ (B1->B2) | (Box_l C) ] => (A|C) & C *)
Lemma monotonicity_matchty : forall l A A' B,
    MatchTy l A A' -> declarative_subtyping A B ->
    exists B', MatchTy l B B' /\ declarative_subtyping A' B'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HM HS.
  indTypFtySize (size_typ A + size_typ B).
  lets~ [OrdB|(?&?&?)]: (ordi_or_split B).
  lets~ [OrdA|(?&?&?)]: (ordi_or_split A).
  - convert2asub. inverts HS; matchty_inv; matchty_unify; solve_false; convert2dsub.
    1-3 : now eauto.
    + (* forwards [?|?]: matchty_splu HM... CANNOT SOLVE BY THIS WAY *)
      inverts H; matchty_inv; solve_false.
      * forwards: IH A1...
      * forwards: IH A2...
      * (* both in union match *) forwards: IH A1... forwards: IH A2...
        matchty_unify. eauto.
      * (* rcd dist *)
        forwards ~: IH H0... forwards ~: IH H1...
        matchty_unify. exists. split... convert2asub. split_l...
    + forwards: IH HM... forwards: matchty_splu_1...
      exists*.
    + forwards: IH HM... forwards: matchty_splu_2...
      exists*.
  - convert2asub. forwards [HS1|HS2] : algo_sub_andlr_inv HS... all: convert2dsub.
    + forwards A1' ? : matchty_spli_1... forwards: IH x A1'... exists*.
    + forwards A2' ? : matchty_spli_2... forwards: IH x0 A2'... exists*.
  - convert2asub. forwards (HS1&HS2) : algo_sub_and_inv HS...
    convert2dsub. forwards: IH HS1... forwards: IH HS2...
    forwards: matchty_spli H...
    exists. split... applys* DSub_Trans H5.
Qed.
