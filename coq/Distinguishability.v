Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.

(* Previous proved properties of distinguishability *)

Notation "A <<>> B"        := (Distinguishability A B)
                                (at level 65, B at next level, no associativity) : type_scope.

Lemma distinguishability_forall_r : forall A B1 C,
    A <<>> (t_forall B1) -> lc_typ C -> A <<>> C
with distinguishability_forall_l : forall A B1 C,
    (t_forall B1) <<>> A -> lc_typ C -> C <<>> A.
Admitted.

Lemma distinguishability_spl_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, splu A A1 A2 -> Distinguishability A1 B /\ Distinguishability A2 B) /\
    (forall B1 B2, splu B B1 B2 -> Distinguishability A B1 /\ Distinguishability A B2) /\
    (forall A1 A2, spli A A1 A2 -> ordu B -> Distinguishability A1 B \/ Distinguishability A2 B) /\
    (forall B1 B2, spli B B1 B2 -> ordu A -> Distinguishability A B1 \/ Distinguishability A B2).
Proof with try match goal with |- lc_typ _ => eauto end.

  Local Ltac get_IH IH IHH IHH1 IHH2 :=
    match goal with
    | H1 : Distinguishability _ _, H2 : Distinguishability _ _ |- _ =>
      forwards IHH1: IH H1; elia; forwards IHH2: IH H2; elia;
      destruct IHH1 as (IHDis11 & IHDis12 & IHDis13 & IHDis14);
      destruct IHH2 as (IHDis21 & IHDis22 & IHDis23 & IHDis24)
    end + match goal with
          | H : Distinguishability ?A ?B |- _ =>
            forwards IHH: IH H; elia;
            destruct IHH as (IHDis1 & IHDis2 & IHDis3 & IHDis4)
          end.

  introv Dis.
  indTypSize( size_typ A + size_typ B ).
  inverts Dis; intros.
  all: splits; introv Spl; try intro Ord; inverts_all_ord; inverts_all_spl; solve_false; try split.
  all: (* Ax cases *) try match type of H with (DistinguishabilityAx _ _) => induction* H; inverts* Spl end.
  all: try get_IH IH IHH IHH1 IHH2.
  all: try ( forwards (?&?): IHDis1; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis2; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis11; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis12; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis21; [ eassumption | ] ).
  all: try ( forwards (?&?): IHDis22; [ eassumption | ] ).
  all: try solve [constructor~].
  all: try solve [assumption].
  all: try ( forwards [?|?]: IHDis13; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis14; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis23; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis24; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis3; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis4; [ eassumption | eassumption | | ] ).
  all: try solve [left~].
  all: try solve [right~].
  (* Distributive cases require the inversion lemma from the other splitting relation
     and IH from induction on Dis is not enough so I have to use indTypSize *)
  all: auto_unify. all: eauto.
  - destruct H...
    + inverts Spl.
      forwards [ ? | ? ]: IHDis13; [ now eauto | now eauto | | ].
      now left*. now right*.
      forwards [ ? | ? ]: IHDis23; [ now eauto | now eauto | | ].
      now left*. now right*.
    + inverts~ Spl.
      forwards [ ? | ? ]: IHDis13; [ now eauto | now eauto | | ].
      all: forwards [ ? | ? ]: IHDis23; [ now eauto | now eauto | | ].
      all: try now left*. all: try now right*.
    + inverts~ Spl.
      forwards [ ? | ? ]: IHDis13; [ now eauto | now eauto | | ].
      all: forwards [ ? | ? ]: IHDis23; [ now eauto | now eauto | | ].
      all: try now left*. all: try now right*.
    + left. applys* distinguishability_forall_l.
    + inverts Spl.
        inverts H0; inverts H2. now left*.
    +
  forwards [ [?|?] | [?|?] ]: double_split; try eassumption.
  destruct_conj.
  forwards [ ? | ? ]: IHDis13; [ now eauto | now eauto | | ].
  all: try forwards [?|(?&?&?)]: ordu_or_split A...
  1-4: forwards (?&?): IHDis12; [ now eauto | ];
       forwards (?&?): IHDis22; [ now eauto | ];
         now eauto.
  1-4: forwards : IHDis14; [ now eauto | now eauto | ];
    forwards : IHDis24; [ now eauto | now eauto | ].
  1-8: repeat match goal with | H : _ \/ _ |- _ => destruct H end.
  1-16: now eauto.

  all: try forwards [?|(?&?&?)]: ordu_or_split B...
  1-4: forwards (?&?): IHDis11; [ now eauto | ];
       forwards (?&?): IHDis21; [ now eauto | ];
         now eauto.
  all: forwards : IHDis13; [ now eauto | now eauto | ];
    forwards : IHDis23; [ now eauto | now eauto | ].
  all: repeat match goal with | H : _ \/ _ |- _ => destruct H end.
  all: eauto.
Qed.

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

(* B.41 *)
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
