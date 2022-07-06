Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export SimpleSub.



Notation "A <<>> B"        := (Distinguishability A B)
                                (at level 65, B at next level, no associativity) : type_scope.

Ltac basic_auto :=
  destruct_conj; auto_unify;
  try exists; try splits;
  try reflexivity;
  try lazymatch goal with
      | |- lc_typ _ => eauto
      | |- spli _ _ _ => try eapply spli_rename_open; try eassumption; econstructor; try eassumption;
                         eauto
      | |- splu _ _ _ => try eapply splu_rename_open; try eassumption; econstructor; try eassumption;
                         eauto
      end; try eassumption; elia.

Lemma distinguishabilityax_rcd_inv : forall l A B,
    DistinguishabilityAx (t_rcd l A) (t_rcd l B) -> False.
Proof.
  intros. inverts~ H.
Qed.

#[export] Hint Immediate distinguishabilityax_rcd_inv : FalseHd.

Lemma distinguishability_top_neg_false : forall Aneg,
    Distinguishability Aneg t_top -> isNegTyp Aneg -> False.
Proof with solve_false; eauto 3.
  introv Dis Neg.
  inductions Dis; inverts_typ; auto_lc;
    try forwards(?&?): distinguishability_lc Dis;
    try forwards(?&?): distinguishability_lc Dis1;
    try forwards(?&?): distinguishability_lc Dis2...
  inverts H...
  all: auto_lc.
Qed.

#[export] Hint Immediate distinguishability_top_neg_false : FalseHd.

Lemma distinguishability_neg_rcd_false : forall Aneg l A,
    Distinguishability Aneg (t_rcd l A) -> isNegTyp Aneg -> False.
Proof with solve_false; eauto 3.
  introv Dis Neg.
  inductions Dis; inverts_typ; auto_lc;
    try forwards(?&?): distinguishability_lc Dis;
    try forwards(?&?): distinguishability_lc Dis1;
    try forwards(?&?): distinguishability_lc Dis2...
  all: inverts H...
Qed.

#[export] Hint Immediate distinguishability_neg_rcd_false : FalseHd.

Lemma distinguishability_top_rcd_false : forall l A,
    Distinguishability (t_rcd l A) t_top -> False.
Proof with solve_false; eauto 3.
  introv Dis.
  inductions Dis; inverts_all_spl.
  - inverts H...
  - forwards* : IHDis1.
  - inverts H.
Qed.

#[export] Hint Immediate distinguishability_top_rcd_false : FalseHd.

Lemma distinguishability_top_val_false : forall V,
    Distinguishability V t_top -> isValTyp V -> False.
Proof with solve_false; eauto 3.
  introv Dis Val.
  inductions Dis; inverts_typ; auto_lc;
    try forwards(?&?): distinguishability_lc Dis;
    try forwards(?&?): distinguishability_lc Dis1;
    try forwards(?&?): distinguishability_lc Dis2...
  inverts H...
Qed.

#[export] Hint Immediate distinguishability_top_val_false : FalseHd.


Lemma distinguishability_forall_false: forall A B,
    Distinguishability (t_forall A) (t_forall B) -> False.
  introv H. inductions H; inverts_all_spl; solve_false.
Qed.

#[export] Hint Immediate distinguishability_forall_false : FalseHd.

Lemma distinguishabilityAx_lc : forall A B,
    DistinguishabilityAx A B -> lc_typ A /\ lc_typ B.
Proof. induction 1; destruct_conj; split; eauto. Qed.

Lemma distinguishability_lc : forall A B,
    Distinguishability A B -> lc_typ A /\ lc_typ B.
Proof. induction 1; destruct_conj; eauto.
       all: forwards~ (?&?): distinguishabilityAx_lc H.
Qed.

Lemma distinguishability_lc_1 : forall A B,
    Distinguishability A B -> lc_typ A.
Proof. intros. applys distinguishability_lc H. Qed.

Lemma distinguishability_lc_2 : forall A B,
    Distinguishability A B -> lc_typ B.
Proof. intros. applys distinguishability_lc H. Qed.

#[export] Hint Resolve distinguishability_lc_1 distinguishability_lc_2 : core.

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
  all: try auto_unify.
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
  all: try forwards [?|(?&?&?)]: ordu_or_split A...
  all: try auto_unify; solve_false.
  all: try solve [applys DistUnion; eassumption].
  all: eauto.
  1: forwards [ [?|?] | [?|?] ]: double_split A; try eassumption; destruct_conj.
  5: forwards [ [?|?] | [?|?] ]: double_split B; try eassumption; destruct_conj.
  all: try ( forwards [?|?]: IHDis13; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis14; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis23; [ eassumption | eassumption | | ] ).
  all: try ( forwards [?|?]: IHDis24; [ eassumption | eassumption | | ] ).
  all: eauto.
Qed.

Lemma distinguishability_splu_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, splu A A1 A2 -> Distinguishability A1 B /\ Distinguishability A2 B) /\
    (forall B1 B2, splu B B1 B2 -> Distinguishability A B1 /\ Distinguishability A B2).
Proof.
  introv Dis.
  forwards* : distinguishability_spl_inv Dis.
Qed.

Lemma distinguishability_spli_inv : forall A B,
    Distinguishability A B ->
    (forall A1 A2, spli A A1 A2 -> ordu B -> Distinguishability A1 B \/ Distinguishability A2 B) /\
    (forall B1 B2, spli B B1 B2 -> ordu A -> Distinguishability A B1 \/ Distinguishability A B2).
Proof.
  introv Dis.
  forwards* : distinguishability_spl_inv Dis.
Qed.


Ltac inverts_all_distinguishability :=
  repeat match goal with
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

Lemma DistAxSym : forall A B,
    DistinguishabilityAx A B -> DistinguishabilityAx B A.
Proof.
  introv H. inverts~ H.
Qed.

#[export] Hint Immediate DistAxSym : core.

Lemma DistSym : forall A B,
    A <<>> B -> B <<>> A.
Proof.
  introv H. induction~ H.
  all: eauto using DistUnion, DistUnionSym.
Qed.

#[export] Hint Immediate DistSym : core.

Lemma distinguishability_arrow_r : forall A B1 B2 C1 C2,
    A <<>> (t_arrow B1 B2) -> lc_typ (t_arrow C1 C2) -> A <<>> (t_arrow C1 C2).
Proof.
    introv Dis. gen C1 C2.
    inductions Dis; intros; eauto.
    all: inverts* H.
Qed.

Lemma distinguishability_arrow_l : forall A B1 B2 C1 C2,
    (t_arrow B1 B2) <<>> A -> lc_typ (t_arrow C1 C2) -> (t_arrow C1 C2) <<>> A.
Proof.
    introv Dis. gen C1 C2.
    inductions Dis; intros; eauto.
    all: inverts* H.
Qed.

Lemma distinguishability_forall_r : forall A B1 C1,
    A <<>> (t_forall B1) -> lc_typ (t_forall C1) -> A <<>> (t_forall C1)
with distinguishability_forall_l : forall A B1 C1,
    (t_forall B1) <<>> A -> lc_typ (t_forall C1) -> (t_forall C1) <<>> A.
Proof.
  +
    introv Dis. gen C1. clear distinguishability_forall_r.
    inductions Dis; intros; try solve [clear distinguishability_forall_l; eauto].
  - clear distinguishability_forall_l. inverts* H.
  - inverts* H.
  +
    introv Dis. gen C1. clear distinguishability_forall_l.
    inductions Dis; intros; try solve [clear distinguishability_forall_r; eauto].
  - clear distinguishability_forall_r. inverts* H.
  - inverts* H.
Qed.

#[export] Hint Immediate distinguishability_arrow_l distinguishability_arrow_r
     distinguishability_forall_l distinguishability_forall_r : core.

Lemma part_split_1 : forall A A1 A2 B1 B2,
    spli A A1 A2 -> splu A1 B1 B2 ->
    (exists C1 C2, splu A C1 C2 /\ spli C1 B1 A2 /\ spli C2 B2 A2)
    \/ (exists C1 C2, splu A C1 B2 /\ spli C1 B1 C2 /\ splu A2 C2 B2)
    \/ (exists C1 C2, splu A B1 C2  /\ spli C2 B2 C1 /\ splu A2 B1 C1).
Proof with basic_auto.
  introv SI SU. gen B1 B2.
  induction SI; intros; inverts_all_spl.
  - left...
  - right; left...
  - right; right...
  - instantiate_cofinites.
    forwards [?| [?|?] ] : H0 H2...
    1: left... 4: right; left... 7: right; right...
    all: intros.
    all: try ( lazymatch goal with
         | H: splu (?A -^ _) _ _ |- splu (?A -^ _ ) _ _ =>
             forwards R1: rename_splu x X H
         | H: spli ?A _ _ |- spli (close_typ_wrt_typ _ ?A -^ _ ) _ _ =>
               forwards R1: rename_spli x X H
           end;
               simpl in R1; try (rewrite 3 typsubst_typ_spec in R1 ||
               rewrite 2 typsubst_typ_spec in R1) ;
               try rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in R1;
               try rewrite close_typ_wrt_typ_open_typ_wrt_typ in R1;
               try apply R1; try solve_notin ).
  - forwards [?| [?|?] ] : IHSI H3...
    + left... + right; left... + right; right...
  Unshelve. all: eauto.
Qed.

Lemma part_split_2 : forall A A1 A2 B1 B2,
    spli A A1 A2 -> ordu A1 -> splu A2 B1 B2 ->
    (exists C1 C2, spli C1 A1 B1 /\ spli C2 A1 B2 /\ splu A C1 C2).
    (* \/ (exists C1 C2, splu A C1 B2 /\ spli C1 B1 C2 /\ splu A2 C2 B2) *)
    (* \/ (exists C1 C2, splu A B1 C2  /\ spli C2 B2 C1 /\ splu A2 B1 C1). *)
Proof with basic_auto.
  introv SI OU SU. gen B1 B2.
  induction SI; intros; inverts_all_ord; inverts_all_spl; solve_false.
  - exists...
    (* left... *)
  - instantiate_cofinites. forwards* : H0 H2. destruct_conj.
    exists; splits; try applys SpI_forall; try applys SpU_forall; intros.
    all: try ( lazymatch goal with
         | H: splu (?A -^ _) _ _ |- splu (?A -^ _ ) _ _ =>
             forwards R1: rename_splu x X H
         | H: spli _ (?A -^ _) (?B -^ _) |- spli _ (?A -^ _ ) (?B -^ _) =>
             forwards R1: rename_spli x X H
         | H: spli ?A _ _ |- spli (close_typ_wrt_typ _ ?A -^ _ ) _ _ =>
               forwards R1: rename_spli x X H
               end).
     all: simpl in R1.
     all: try (rewrite 3 typsubst_typ_spec in R1 ||
            rewrite 2 typsubst_typ_spec in R1 ||
            rewrite typsubst_typ_spec in R1).
     all: try (rewrite 3 close_typ_wrt_typ_open_typ_wrt_typ in R1 ||
            rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in R1 ||
            rewrite close_typ_wrt_typ_open_typ_wrt_typ in R1).
     all: try apply R1; try solve_notin.
  - forwards~ : IHSI; [ eassumption | .. ].
    destruct_conj.
    exists; splits.
    3: applys* SpU_in.
    all: eauto.
    Unshelve. all: eauto.
Qed.

Lemma distinguishability_spli_r_1 : forall A B B1 B2,
      spli B B1 B2 -> Distinguishability A B1 -> Distinguishability A B.
Proof with basic_auto.
  introv Spl Dis.
  indTypSize (size_typ A + size_typ B).
  inverts Spl; intros; inverts_all_distinguishability.
  1: applys~ DistIntersectLSym.
  1-2: applys~ DistUnionSym.
  all: try solve [applys IH; [ | | eassumption]; eauto; elia].
  1-3: (* arrow/forall *) eauto using
                                distinguishability_arrow_l, distinguishability_arrow_r,
                                distinguishability_forall_l, distinguishability_forall_r.
  - (* rcd *)
    inverts Dis; solve_false.
    1: now inverts* H0.
    1: applys DistIn.
    2: applys DistUnion; [ eassumption | | ].
    all: inverts_all_spl.
    4: { forwards [?| [?|?] ] : part_split_1 H H7; destruct_conj; eauto.
         all: applys DistUnionSym...
         all: applys IH...
    }
    4: applys~ DistIntersectL.
    5: applys~ DistIntersectR.
    all: applys IH...
Qed.

Lemma distinguishability_spli_l_1 : forall A B B1 B2,
      spli B B1 B2 -> Distinguishability B1 A -> Distinguishability B A.
Proof.
  introv Spl Dis.
  applys DistSym. apply DistSym in Dis.
  applys* distinguishability_spli_r_1.
Qed.

Lemma distinguishability_spli_r_2 : forall A B B1 B2,
      spli B B1 B2 -> Distinguishability A B2 -> Distinguishability A B.
Proof with basic_auto.
  introv Spl Dis.
  indTypSize (size_typ A + size_typ B).
  inverts Spl; intros; inverts_all_distinguishability.
  1: applys~ DistIntersectRSym.
  1-2: applys~ DistUnionSym.
  all: try solve [applys IH; [ | eassumption | ]; eauto; elia].
  1-3: (* arrow/forall *) eauto using
                                distinguishability_arrow_l, distinguishability_arrow_r,
                                distinguishability_forall_l, distinguishability_forall_r.
  - (* rcd *)
    inverts Dis; solve_false.
    1: now inverts* H0.
    1: applys DistIn.
    2: applys DistUnion; [ eassumption | | ].
    all: inverts_all_spl.
    4: {
      lets~ [Hu|(?&?&Hu)]: ordu_or_split A1.
      - forwards : part_split_2 H H7; destruct_conj; eauto.
        all: applys DistUnionSym...
        all: applys IH...
      - forwards [?| [?|?] ] : part_split_1 H Hu; destruct_conj; eauto.
         all: applys DistUnionSym...
         all: applys IH...
         all: applys DistUnionSym...
    }
    4: applys~ DistIntersectL.
    5: applys~ DistIntersectR.
    all: applys IH...
Qed.

Lemma distinguishability_spli_l_2 : forall A B B1 B2,
      spli B B1 B2 -> (Distinguishability B2 A -> Distinguishability B A).
Proof.
Proof.
  introv Spl Dis.
  applys DistSym. apply DistSym in Dis.
  applys* distinguishability_spli_r_2.
Qed.

Lemma distinguishability_splu_r : forall A B B1 B2,
    splu B B1 B2 -> Distinguishability A B1 -> Distinguishability A B2 ->
    Distinguishability A B.
Proof.
  intros. eauto.
Qed.

Lemma distinguishability_splu_l : forall A B B1 B2,
    splu B B1 B2 -> Distinguishability B1 A -> Distinguishability B2 A ->
    Distinguishability B A.
Proof.
  intros. eauto.
Qed.

Lemma distinguishability_rcd_inv : forall l A B,
    (t_rcd l A) <<>> (t_rcd l B) -> A <<>> B.
Proof with basic_auto.
  introv H. inductions H; inverts_all_spl; solve_false; try easy.
  - forwards: IHDistinguishability1...
    forwards: IHDistinguishability2...
    applys DistUnion...
  - forwards: IHDistinguishability1...
    forwards: IHDistinguishability2...
    applys DistUnionSym...
Qed.

Lemma distinguishabilityAx_downward_r : forall A B B',
    DistinguishabilityAx A B -> B' <: B -> Distinguishability A B'.
Proof with try reflexivity; elia; auto.
  introv Dis Sub.
  inverts~ Dis; convert2asub;
    inductions Sub; solve_false; inverts_all_spl; auto.
  - forwards: IHSub1...
  - forwards: IHSub... applys~ distinguishability_spli_r_1 H.
  - forwards: IHSub... applys~ distinguishability_spli_r_2 H.
  - forwards: IHSub1... forwards: IHSub2...
    applys DistUnionSym; basic_auto.
  - forwards: IHSub...
  - forwards: IHSub...
  - forwards: IHSub... applys* distinguishability_spli_r_1...
  - forwards: IHSub... applys distinguishability_spli_r_2... eauto.
  - forwards: IHSub1... forwards: IHSub2...
    applys DistUnionSym; try eassumption.
Qed.

(* Lemma Downward Closure of Distinguishability *)
Lemma distinguishability_downward : forall A B B',
    Distinguishability A B -> B' <: B -> Distinguishability A B'.
Proof with try reflexivity; elia; auto.
  introv Dis Sub. convert2asub.
  indTypSize (size_typ A + size_typ B + size_typ B').
  forwards [?|(?&?&?)]: ordu_or_split A. now eauto.
  forwards [?|(?&?&?)]: ordu_or_split B. now eauto.
  - inverts Dis; solve_false.
    + convert2dsub. applys distinguishabilityAx_downward_r; basic_auto.
    + inverts Sub; inverts_all_spl...
      all: try (applys distinguishability_spli_r_1; [ solve [basic_auto] | applys IH;  [ | eassumption | .. ] | .. ]).
      all: try (applys distinguishability_spli_r_2; [ solve [basic_auto] | applys IH;  [ | eassumption | .. ] | .. ]).
      all: try (applys distinguishability_spli_l_1; [ solve [basic_auto] | applys IH;  [ | eassumption | .. ] | .. ]).
      all: try (applys distinguishability_spli_l_2; [ solve [basic_auto] | applys IH;  [ | eassumption | .. ] | .. ]).
      all: inverts_all_distinguishability.
      all: elia.
      all: try solve [applys~ DistIn].
      1: applys DistIn;
        try solve [applys IH; basic_auto].
      all: try (
               lazymatch goal with
               | H: spli _ _ _ |- _ => eapply (SpI_in l5) in H
        (* | H: splu _ _ _ |- _ => eapply (SpU_in l5) in H *)
               end;
               lazymatch goal with
               | H: _ <<>> _ |- _ => eapply (DistIn l5) in H
               end ;
        inverts_all_distinguishability; applys IH; basic_auto).
      all: try (applys DistUnionSym; [ solve [basic_auto] | ..]; applys IH).
      all: try applys DistIn.
      all: basic_auto.
      all: applys IH; basic_auto; applys~ DistIn.
    + forwards~ : IH H2 Sub...
    + forwards~ : IH H2 Sub...
    + cut (B' <:: A0).
      * intros Sub'. forwards~ : IH H2 Sub'...
      * applys algo_trans Sub. applys~ ASub_andl.
    + cut (B' <:: A').
      * intros Sub'. forwards~ : IH H2 Sub'...
      * applys algo_trans Sub. applys~ ASub_andr.
  - forwards [?|(?&?&?)]: ordu_or_split B'. now eauto.
    + auto_inv; inverts_all_distinguishability.
      all: applys IH; [ | eassumption | .. ]; try eassumption...
    + applys DistUnionSym; try eassumption.
      all: applys IH; [ eassumption | .. ]; elia.
      all: applys algo_trans Sub.
      * applys* ASub_orl.
      * applys* ASub_orr.
  - inverts_all_distinguishability.
    applys DistUnion; try eassumption.
    all: applys IH; try eassumption...
Qed.

(******************************************************************************)
(* similarity relation *)

(* Lemma Properties of the Union-Split Results of a Value Type (Similar Types) [2] *)
Lemma sim_no_distinguishability : forall A B,
    sim A B -> Distinguishability A B -> False.
Proof with auto_lc; inverts_all_spl; solve_false.
  introv Sim Dis.
  induction Sim; intros.
  - induction Dis; try inverts_typ...
    + inverts H1...
  - forwards* : distinguishability_rcd_inv Dis.
Qed.

(******************************************************************************)
(* Lemma B.13 *)
Lemma distinguishability_valtyp_not_psub : forall V U,
    Distinguishability V U -> isValTyp V -> isValTyp U -> V <p U -> False.
Proof with try eassumption; elia.
  introv Dis Val1 Val2 Sub.
  indTypSize (size_typ V + size_typ U).
  forwards [?|(?&?&?)]: ordu_or_split U. now eauto.
  forwards [?|(?&?&?)]: ordu_or_split V. now eauto.
  - inverts Dis; solve_false.
    + inverts H1; try solve [inverts Sub; solve_false].
    + inverts Sub; inverts_typ; solve_false.
      * applys* IH A B...
    + inverts_typ. inverts_all_psub. applys* IH A U...
    + inverts_typ. inverts_all_psub. applys* IH A' U...
    + inverts_typ. inverts_all_psub. applys* IH V A...
    + inverts_typ. inverts_all_psub. applys* IH V A'...
  - inverts_all_distinguishability.
    inverts_all_psub.
    applys* IH x U. elia.
  - inverts_typ. inverts_all_distinguishability.
    forwards [?|?]: psub_splu_inv Sub...
    all: applys IH; [ | | | eassumption | ..]...
Qed.

Lemma distinguishability_negtyp_false : forall V U,
    Distinguishability V U -> isValTyp V -> isNegTyp U -> False.
Proof.
  intros.
  applys* distinguishability_valtyp_not_psub H.
Qed.

#[export] Hint Extern 1 False =>
  lazymatch goal with
  | Dis: Distinguishability ?V ?U, Neg: isNegTyp ?U |- _ =>
      applys distinguishability_negtyp_false Dis Neg
  | Dis: Distinguishability ?V ?U, Neg: isNegTyp ?V |- _ =>
      apply DistSym in Dis; applys distinguishability_negtyp_false Dis Neg
  end : FalseHd.

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

    Local Ltac first_match := try lazymatch goal with
                                  | |- _ <<>>  _ => try eassumption
                                  end.
    Local Ltac match_psub := try lazymatch goal with
                                 | |- _ <p  _ => eassumption
                                 | H: _ <p _ |- _ <p _ => applys PSub_In H
                                 end.
    Local Ltac inverts_disax := try lazymatch goal with
                                    | H: DistinguishabilityAx _ _ |- _ => inverts H; fail
                                  end.

    all: try solve [
             inverts_all_distinguishability;
             applys IH; try eassumption; elia; eauto].
    + apply distinguishability_rcd_inv in Dis.
      applys IH Dis; try eassumption; elia.
    + destruct H2... all: inverts Dis...
      all: applys IH; try eassumption; elia; eauto.
    + inverts_all_distinguishability.
      applys IH H0; try eassumption; elia; eauto.
      applys IH H1; try eassumption; elia; eauto.
  - inverts_all_distinguishability.
    forwards~ [?|?]: psub_splu_inv Hu' SubB. clear SubB.
    applys IH H SubA; first_match; try eassumption; elia; eauto.
    applys IH H0 SubA; first_match; try eassumption; elia; eauto.
  - inverts_all_distinguishability.
    forwards~ [?|?]: psub_splu_inv Hu SubA. clear SubA.
    applys IH H SubB; first_match; try eassumption; elia; eauto.
    applys IH H0 SubB; first_match; try eassumption; elia; eauto.
Qed.
