Require Import LibTactics.
Require Import Coq.micromega.Lia.
Require Import LN_Lemmas.
Require Export DistSubtyping.

#[export] Hint Extern 1 (lc_typ (t_forall _)) =>
let Y:= fresh "Y" in pick_fresh Y; instantiate_cofinites_with Y; applys lc_t_forall_exists Y : core.


Ltac inv_arrow :=
  repeat match goal with
         | H: algo_sub (t_arrow _ _) (t_arrow _ _) |- _ => forwards (?&?): algo_sub_arrow_inv H; clear H
         | H: declarative_subtyping (t_arrow _ _) (t_arrow _ _) |- _ => apply dsub2asub in H
         end.

Ltac inv_forall :=
  repeat match goal with
         | H: algo_sub (t_forall _) (t_forall _) |- _ => forwards : algo_sub_forall_inv H; clear H
         | H: declarative_subtyping (t_forall _) (t_forall _) |- _ => apply dsub2asub in H
         end.


Ltac convert2asub :=
  repeat match goal with
           H: declarative_subtyping _ _ |- _ => apply dsub2asub in H
           | |- declarative_subtyping _ _ => apply dsub2asub
         end.

Ltac convert2dsub :=
  repeat match goal with
           | H: algo_sub _ _ |- _ => apply dsub2asub in H
           | |- algo_sub _ _ => apply dsub2asub
         end.

Lemma sub_inv_1 : forall X B D,
    algo_sub (t_tvar_f X) (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_2 : forall l5 A B D,
    algo_sub (t_rcd l5 A) (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_rcd l5 A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_3 : forall B D,
    algo_sub t_top (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_4 : forall A B D,
    algo_sub (t_forall A) (t_arrow B D) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_5 : forall X B,
    algo_sub (t_tvar_f X) (t_forall B) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_6 : forall l5 A B,
    algo_sub (t_rcd l5 A) (t_forall B) -> False.
Proof.
  introv H. indTypSize (size_typ (t_rcd l5 A) + size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_7 : forall B,
    algo_sub t_top (t_forall B) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall B)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

Lemma sub_inv_8 : forall A B D,
    algo_sub (t_arrow B D) (t_forall A) -> False.
Proof.
  introv H. indTypSize (size_typ (t_forall A) + size_typ (t_arrow B D)).
  inverts H; solve_false.
  all: inverts H0; applys IH; try eassumption; elia.
Qed.

#[export] Hint Extern 1 => match goal with
   | H: algo_sub (t_tvar_f _) (t_arrow _ _) |- _ => applys sub_inv_1 H
   | H: algo_sub (t_rcd _ _) (t_arrow _ _) |- _ => applys sub_inv_2 H
   | H: algo_sub t_top (t_arrow _ _) |- _ => applys sub_inv_3 H
   | H: algo_sub (t_forall _) (t_arrow _ _) |- _ => applys sub_inv_4 H
   | H: algo_sub (t_tvar_f _) (t_forall _) |- _ => applys sub_inv_5 H
   | H: algo_sub (t_rcd _ _) (t_forall _) |- _ => applys sub_inv_6 H
   | H: algo_sub t_top (t_forall _) |- _ => applys sub_inv_7 H
   | H: algo_sub (t_arrow _ _) (t_forall _) |- _ => applys sub_inv_8 H
                            end : FalseHd.

(******** nondeterministic split & alternative subtyping definition *******)

Lemma new_splu_decrease_size: forall A B C,
    new_splu A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  pick fresh X. forwards* (?&?): H0.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
  rewrite 2 size_typ_open_typ_wrt_typ_var in H2.
  eauto...
Qed.

Lemma new_spli_decrease_size: forall A B C,
    new_spli A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (size_typ_min); simpl in *; try lia).
  introv H.
  induction H; simpl in *; eauto...
  - forwards (?&?): new_splu_decrease_size H0...
  - pick fresh X. forwards* (?&?): H0.
    rewrite 2 size_typ_open_typ_wrt_typ_var in H3.
    rewrite 2 size_typ_open_typ_wrt_typ_var in H2.
    eauto...
Qed.

Ltac new_spl_size :=
  repeat match goal with
         | [ H: new_splu _ _ _ |- _ ] =>
           ( lets (?&?): new_splu_decrease_size H; clear H)
         | [ H: new_spli _ _ _ |- _ ] =>
           ( lets (?&?): new_spli_decrease_size H; clear H)
         end.

Ltac new_elia :=
  try solve [pose proof (size_typ_min);
             let x := fresh "x" in
             pick fresh x; instantiate_cofinites_with x; (* forall x, x `notin` .. -> spli .. *)
             spl_size; new_spl_size; simpl in *; simpl;
             try repeat rewrite size_typ_open_typ_wrt_typ_var in *; (* spl A-^X ... *)
             try lia].

(******* relates to original definitions ********)

Lemma splu2nsplu : forall A B1 B2,
    splu A B1 B2 -> new_splu A B1 B2.
Proof.
  introv H. induction* H.
Qed.

Lemma spli2nspli : forall A B1 B2,
    spli A B1 B2 -> new_spli A B1 B2.
Proof.
  introv H. induction~ H.
  - apply splu2nsplu in H0. eauto.
  - econstructor. intros. instantiate_cofinites. easy.
Qed.

#[export] Hint Resolve splu2nsplu spli2nspli : core.

Notation "A <:: B" := (algo_sub A B) (at level 15).
Notation "A ~~ B" := ((algo_sub A B) /\ (algo_sub B A)) (at level 15).
Notation "A & B" := (t_and A B) (at level 10).
Notation "A | B" := (t_or A B) (at level 11).

Lemma nsplu2splu : forall A B1 B2,
    new_splu A B1 B2 ->
    exists C1 C2, splu A C1 C2.
Proof with destruct_conj; eauto.
  introv H. induction H...
  - destruct* (ordu_or_split A)...
  - pick fresh Y for (L `union` [[A]]). instantiate_cofinites. exists.
    applys splu_forall_exists Y...
Qed.

Lemma nspli2spli : forall A B1 B2,
    new_spli A B1 B2 ->
    exists C1 C2, spli A C1 C2.
Proof with destruct_conj; eauto.
  introv H. induction H...
  - destruct* (ordi_or_split A)...
  - destruct* (ordi_or_split B)...
    + apply nsplu2splu in H0...
  - pick fresh Y for (L `union` [[A]]). instantiate_cofinites. exists.
    applys spli_forall_exists Y...
Qed.

Ltac gets_all_lc :=
  repeat match goal with
         | H: ordi _ |- _ => lets: ordi_lc H; assumption
         | H: ordu _ |- _ => lets: ordi_lc H; assumption
         | H: splu _ _ _ |- _ => lets (?&?&?): splu_lc H; assumption
         | H: spli _ _ _ |- _ => lets (?&?&?): spli_lc H; assumption
         | H: algo_sub _ _ |- _ => lets (?&?): algo_sub_lc H; assumption
         end.

Lemma open_into_var : forall X Y, t_tvar_f Y -^ X = t_tvar_f Y.
Proof. eauto. Qed.

Hint Rewrite open_into_var : open.

Lemma nsplu_isomorphic : forall A B1 B2,
    new_splu A B1 B2 -> A ~~ B1|B2.
Proof with try applys ASub_refl; try match goal with |- lc_typ _ => eauto with lngen end.
  introv H. split; induction~ H.
  - split_r.
    + swap_or_r... split_r.
      swap_or_r... applys* ASub_andl. applys* ASub_andr.
    + applys* ASub_orl.
  - swap_and_l... split_r.
    + applys* ASub_orl.
    + swap_or_r... split_r. applys* ASub_andr.
      swap_or_r... applys* ASub_andl.
  - applys algo_trans; [ | applys dsub2asub; applys DSub_CovDistUAll ]...
    econstructor. intros. instantiate_cofinites.
    applys algo_trans H0. autorewrite with open.
    auto.
  - applys algo_trans; [ | applys dsub2asub; applys DSub_CovDistUIn ]...
    econstructor. easy.
  - split_l.
    + split_r.
      * use_left_l. applys algo_trans IHnew_splu. use_left_r...
      * use_right_l...
    + split_r.
      * use_left_l. applys algo_trans IHnew_splu. use_right_r...
      * use_right_l...
  - split_l.
    + split_r.
      * use_left_l...
      * applys algo_trans IHnew_splu. use_left_r... use_right_l...
    + split_r.
      * use_left_l...
      * applys algo_trans IHnew_splu. use_right_r... use_right_l...
  - applys algo_trans (t_forall (A1|A2))...
    + split_l; applys ASub_forall; intros; instantiate_cofinites;
       autorewrite with open...
      use_left_r... use_right_r...
    + applys ASub_forall; intros; instantiate_cofinites;
       autorewrite with open... easy.
  - applys algo_trans (t_rcd l5 (A1|A2))...
    + split_l; applys ASub_rcd. use_left_r... use_right_r...
    + applys ASub_rcd. easy.
Qed.

Lemma nspli_isomorphic : forall A B1 B2,
    new_spli A B1 B2 -> A ~~ B1&B2.
Proof with eauto using ASub_refl.
  introv Hs. induction Hs.
  - split*.
  - destruct IHHs.
    split; applys algo_trans ((A1&A2)|B).
    + match_or...
    + match_and...
    + match_and...
    + match_or...
  - destruct IHHs. split.
    + applys algo_trans (A|B1&B2).
      * match_or...
      * swap_or_l... split_l.
        use_right_r. swap_and_r...
        use_right_r.
        match_and_rev...
        use_left_r. swap_and_r... use_left_r.
        split_r...
    + applys algo_trans (A|B1&B2).
      * swap_or_r...
        split_l. swap_and_l... split_l.
        use_right_r. use_left_l...
        use_right_l. use_right_r...
        swap_and_l... split_l.
        use_left_l. use_right_r...
        use_left_r. match_and_rev...
      * match_or...
  - destruct IHHs. split; applys algo_trans (t_arrow A (B1&B2)).
    + econstructor...
    + match_and...
    + split_r. eauto.
      use_left_l...
      use_right_l...
    + econstructor...
  - apply nsplu_isomorphic in H0.
    destruct H0. split; applys algo_trans (t_arrow (A1|A2) B).
    + econstructor...
    + split_r; constructor~. use_left_r... use_right_r...
    + convert2dsub. applys* DSub_FunDistI.
    + constructor~.
  - split; applys algo_trans (t_forall (A1&A2)).
    + econstructor. intros. instantiate_cofinites. autorewrite with open. easy.
    + split_r; econstructor; intros; autorewrite with open. use_left_l... use_right_l...
    + convert2dsub. applys* DSub_CovDistIAll.
    + econstructor. intros. instantiate_cofinites. autorewrite with open. easy.
  - destruct IHHs. split; applys algo_trans (t_rcd l5 (A1&A2)).
    + econstructor...
    + match_and...
    + split_r. eauto.
      use_left_l...
      use_right_l...
    + econstructor...
Qed.

Lemma asub2nsub : forall A B,
    algo_sub A B <-> new_sub A B.
Proof with new_elia; try easy.
  introv; split; intro H.
  - induction H.
    all: now eauto.
  - indTypSize (size_typ A + size_typ B). inverts H.
    1-3: eauto.
    1,3-9: repeat match goal with
                | H: new_sub _ _ |- _ => forwards~ : IH H; new_elia; clear H
                  end.
    + (* and *) applys~ algo_trans (B1&B2).
      split_r...
      forwards~ (?&?): nspli_isomorphic H0.
    + (* andl *) applys~ algo_trans (A1&A2).
      forwards~ (?&?): nspli_isomorphic H0.
      use_left_l...
    + (* andr *) applys~ algo_trans (A1&A2). forwards~ (?&?): nspli_isomorphic H0.
      use_right_l...
    + (* or *) applys~ algo_trans (A1|A2).
      forwards~ (?&?): nsplu_isomorphic H0.
      split_l...
    + (* orl *) applys~ algo_trans (B1|B2). use_left_r...
      forwards~ (?&?): nsplu_isomorphic H0.
    + (* orr *) applys~ algo_trans (B1|B2). use_right_r...
      forwards~ (?&?): nsplu_isomorphic H0.
    + applys ASub_forall (L `union` [[A0]] `union` [[B0]]). intros X Fry.
      instantiate_cofinites. applys~ IH; elia.
Qed.

(*********************** binding ********************************)

Ltac close_typ_var X :=
  repeat match goal with
         | H: ?A = ?B -^ X |- _ =>
           let H' := fresh "Heq" in
           forwards~ H': close_typ_wrt_typ_open_typ_wrt_typ B;
           rewrite <- H in H'; clear H
         end.

Ltac simpl_rename H :=
  match type of H with
  | context [ [?X ~~> _] (_ -^ ?X) ] =>
    rewrite typsubst_typ_spec in H; rewrite close_typ_wrt_typ_open_typ_wrt_typ in H
  | context [ [?X ~~> _] ?A ] =>
    rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ A X) in H;
    rewrite typsubst_typ_spec in H; rewrite close_typ_wrt_typ_open_typ_wrt_typ in H
  end.

Ltac simpl_rename_goal :=
  match goal with
  | |- context [ [?X ~~> _] (_ -^ ?X) ] =>
    rewrite typsubst_typ_spec; rewrite close_typ_wrt_typ_open_typ_wrt_typ
  | |- context [ [?X ~~> _] ?A ] =>
    rewrite <- (open_typ_wrt_typ_close_typ_wrt_typ A X);
    rewrite typsubst_typ_spec; rewrite close_typ_wrt_typ_open_typ_wrt_typ
  end.

(* Aborted
Lemma typsubst_typ_splu : forall A B C X U,
    X `notin` [[A]] `union` [[B]] `union` [[C]] -> lc_typ U ->
    new_splu ( A -^ X ) ( B -^ X ) ( C -^ X ) ->
    new_splu ( A ^-^ U ) ( B ^-^ U ) ( C ^-^ U ).
Proof with eauto with lngen.
  introv Fry Lc Hs. inductions Hs; simpl.
  - assert (Heq: (t_or B C) -^ X = t_or (B -^ X) (C -^ X)) by eauto.
    rewrite <- Heq in x.
    lets~ Heq2: open_typ_wrt_typ_inj x.
    assert (Heq3: (t_or B C) ^-^ U = t_or (B ^-^ U) (C ^-^ U)) by eauto.
    subst. rewrite Heq3. applys NSpU_or...
  - close_typ_var X. subst.
Abort. (* the following alternative definition is simpler *)
*)
Lemma typsubst_typ_splu : forall A B C X U,
    new_splu A B C -> lc_typ U ->
    new_splu ([X ~~> U] A) ([X ~~> U] B) ([X ~~> U] C).
Proof with eauto with lngen.
  introv spl lc. induction spl; simpl.
  all: auto...
  -
    applys NSpU_forall (L `union` [[A]] `union` [[A1]] `union` [[A2]] `union` {{X}}).
    intros Y Fry. instantiate_cofinites_with Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in H0...
    rewrite (typsubst_typ_fresh_eq (t_tvar_f Y) U X) in H0...
Qed.

Lemma typsubst_typ_spli : forall A B C X U,
    new_spli A B C -> lc_typ U ->
    new_spli ([X ~~> U] A) ([X ~~> U] B) ([X ~~> U] C).
Proof with eauto using typsubst_typ_splu with lngen.
  introv spl lc. induction spl; simpl.
  1-4, 7: auto...
  - applys NSpI_arrowUnion...
  - applys NSpI_forall (L `union` [[A]] `union` [[A1]] `union` [[A2]] `union` {{X}}).
    intros Y Fry. instantiate_cofinites_with Y.
    rewrite 3 typsubst_typ_open_typ_wrt_typ in H0...
    rewrite (typsubst_typ_fresh_eq (t_tvar_f Y) U X) in H0...
Qed.

Lemma typsubst_typ_new_sub : forall A B C X,
  new_sub A B -> lc_typ C ->
  new_sub ([X ~~> C] A) ([X ~~> C] B).
Proof with (simpl in *; eauto with lngen; eauto using typsubst_typ_lc_typ, typsubst_typ_spli, typsubst_typ_splu).
  introv s lc.
  indTypSize (size_typ A + size_typ B).
  inverts s; simpl.
  - applys NSub_refl...
  - applys~ NSub_top...
  - applys~ NSub_bot...
  - applys~ NSub_arrow... all: applys IH; elia...
  - applys~ NSub_forall (L `union` {{X}} `union` [[C]])...
    intros Y HF. instantiate_cofinites_with Y.
    rewrite 2 typsubst_typ_open_typ_wrt_typ_var...
    applys IH; elia...
  - applys~ NSub_rcd... applys IH; new_elia...
  - applys~ NSub_and. applys typsubst_typ_spli H...
    all: applys IH; new_elia...
  - applys~ NSub_andl. applys typsubst_typ_spli H...
    all: applys IH; new_elia...
  - applys~ NSub_andr. applys typsubst_typ_spli H...
    all: applys IH; new_elia...
  - applys~ NSub_or. applys typsubst_typ_splu H...
    all: applys IH; new_elia...
  - applys~ NSub_orl. applys typsubst_typ_splu H...
    all: applys IH; new_elia...
  - applys~ NSub_orr. applys typsubst_typ_splu H...
    all: applys IH; new_elia...
Qed.

(******** subtyping **********)


Lemma typsubst_typ_algo_sub : forall A B C X,
  algo_sub A B -> lc_typ C ->
  algo_sub ([X ~~> C] A) ([X ~~> C] B).
Proof.
  intros.
  apply asub2nsub. apply asub2nsub in H.
  applys~ typsubst_typ_new_sub.
Qed.

Ltac solve_dsub := repeat match goal with
                          | H: declarative_subtyping _ _ |- _ => apply dsub2asub in H
                          | |- declarative_subtyping _ _ => apply dsub2asub
                          end; try solve (solve_algo_sub).

(*
Lemma dsub_lc_1 : forall A B, declarative_subtyping A B -> lc_typ A.
Proof.  introv H.  apply dsub2asub in H.  eauto.  Qed.

Lemma dsub_lc_2 : forall A B, declarative_subtyping A B -> lc_typ B.
Proof.  introv H.  apply dsub2asub in H. eauto.  Qed.

#[export] Hint Immediate dsub_lc_1 dsub_lc_2 : core.
 *)

Lemma sub_dec : forall A B,
    lc_typ A -> lc_typ B -> declarative_subtyping A B \/ ~ (declarative_subtyping A B).
Proof.
  intros.
  forwards~ [?|?]: decidability A B.
  left. applys~ dsub2asub.
  right. intro HF. apply dsub2asub in HF. eauto.
Qed.

Lemma nsub_splitu : forall A B B1 B2,
    ~ declarative_subtyping B A -> splu B B1 B2 -> lc_typ A ->
    ~ declarative_subtyping B1 A \/ ~ declarative_subtyping B2 A.
Proof.
  introv HN HS HL.
  destruct (sub_dec B1 A); eauto.
  destruct (sub_dec B2 A); eauto.
  exfalso. applys HN.
  apply dsub2asub in H, H0. applys~ dsub2asub.
  split_l; eassumption.
Qed.

(******** appty **************)

#[export]
Hint Extern 0 =>
match goal with
| H: UnionOrdinaryFty (fty_StackArg _) |- _ => inverts H
end : FalseHd.

Ltac indTypFtySize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  repeat match goal with | [ h : Fty |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].


#[export] Hint Immediate orduFty_lc : core.

Lemma nappty_lc_1 : forall A B, NApplyTy A B -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma nappty_lc_2 : forall A B, NApplyTy A B -> lc_Fty B.
Proof.  introv H.  induction* H.  Qed.

#[export] Hint Immediate nappty_lc_1 nappty_lc_2 : core.

Lemma appty_lc_1 : forall A B C, ApplyTy A B C -> lc_typ A.
Proof.  introv H.  induction* H.  Qed.

Lemma appty_lc_2 : forall A B C, ApplyTy A B C -> lc_Fty B.
Proof.  introv H.  induction* H. Qed.

Lemma appty_lc_3 : forall A B C, ApplyTy A B C -> lc_typ C.
Proof.  introv H.  induction~ H. inverts H. eauto with lngen. Qed.

#[export] Hint Immediate appty_lc_1 appty_lc_2 appty_lc_3 : core.

(*
Ltac solve_lc_by_regularity A :=
  match goal with
  | H: ApplyTy _ _ _ |- _ => match type of H with context[ A ] => apply appty_lc in H end
  | H: NApplyTy _ _ _ |- _ => match type of H with context[ A ] => apply nappty_lc in H end
  end;
  destruct_conj.

#[export] Hint Extern 1 (lc_typ ?A ) => progress solve_lc_by_regularity A : core.
#[export] Hint Extern 1 (lc_typ (?A -^ _) ) => progress solve_lc_by_regularity A : core.
 *)

Lemma nappty_splitu_inv : forall A B B1 B2,
    NApplyTy A (fty_StackArg B) -> splu B B1 B2 ->
    NApplyTy A (fty_StackArg B1) \/ NApplyTy A (fty_StackArg B2).
Proof.
  introv HN HS.
  inverts HN; solve_false; auto_unify; eauto.
Qed.

Lemma appty_contradication : forall A B C,
   ApplyTy A B C -> NApplyTy A B -> False.
Proof with solve_false.
  introv HA HN.
  indTypFtySize (size_typ A + size_Fty B).

  inverts HA;
    match goal with
    | H1: NApplyTy _ (fty_StackArg ?B), H2: splu ?B _ _  |- _ =>
      forwards~ [?|?]: nappty_splitu_inv H1 H2
    | _ => inverts HN
    end.

  all: repeat match goal with
  | H1: ApplyTy (t_forall _) (fty_StackArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyFunTy
  | H1: ApplyTy (t_arrow _ _) (fty_StackTyArg _) _ |- _ => forwards: IH H1; elia; applys~ NApplyTyFunFty
  | H1: ApplyTy ?A ?B _, H2: NApplyTy ?A ?B |- _ => forwards: IH H2 H1; elia
              end.
  all: solve_false.
Qed.

#[export]  Hint Extern 1 => match goal with
                            | H1: ApplyTy ?T _ _, H2: NApplyTy ?T _  |- _ =>
                              applys appty_contradication H1 H2
                            end : FalseHd.

Lemma appty_unique : forall A B C1 C2,
    ApplyTy A B C1 -> ApplyTy A B C2 -> C1 = C2.
Proof.
  introv HA1 HA2. gen C1 C2.
  indTypFtySize (size_typ A + size_Fty B).
  inverts HA1; inverts HA2.
  all: auto_unify; repeat match goal with
  | H1: ApplyTy ?A ?B _, H2: ApplyTy ?A ?B _ |- _ => forwards: IH H1 H2; elia; clear H1 H2
              end; subst~.
  all: solve_false.
Qed.

Ltac auto_unify_2 :=
  auto_unify; (* unify split *)
  (* unify appty *)
  repeat match goal with
         | [ H1: ApplyTy ?A ?B _ , H2: ApplyTy ?A ?B _ |- _ ] =>
           (forwards : appty_unique H1 H2;
            subst; clear H2)
             end.

Lemma ordu_or_split_Fty: forall F,
    lc_Fty F -> UnionOrdinaryFty F \/ exists A B C, F = fty_StackArg A /\ splu A B C.
Proof.
  introv HL.
  destruct~ HL.
  forwards* [?|(?&?&?)]: ordu_or_split A.
Qed.

Lemma appty_total : forall A F,
    lc_typ A -> lc_Fty F -> exists C, ApplyTy A F C \/ NApplyTy A F.
Proof.
  introv.
  indTypFtySize (size_typ A + size_Fty F).
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F).
  - destruct* H.
    (* and / or *)
    all: try forwards~ (?&[?|?]): IH F A1; elia.
    all: try forwards~ (?&[?|?]): IH F A2; elia.
    all: eauto.

    (* arrow / forall *)
    all: destruct H0.
    2,3: solve [exists; right*].

    + destruct* (sub_dec A0 A).
    + eauto.

  - subst.
    forwards~ (?&[?|?]): IH (fty_StackArg x0) A; elia.
    forwards~ (?&[?|?]): IH (fty_StackArg x1) A; elia.
    all: eauto.

  Unshelve. all: apply t_top.
Qed.


Lemma appty_splitu_arg_inv : forall A B B1 B2 C,
    ApplyTy A (fty_StackArg B) C -> splu B B1 B2 ->
    exists C1 C2, C = (t_or C1 C2) /\
    ApplyTy A (fty_StackArg B1) C1 /\ ApplyTy A (fty_StackArg B2) C2.
Proof.
  introv HA HS.
  inverts HA; auto_unify; solve_false; eauto.
Qed.


Lemma appty_splitu_fun_aux : forall A A1 A2 F,
    (forall C1 C2, ApplyTy A1 F C1 -> ApplyTy A2 F C2 -> splu A A1 A2 ->
     exists C', ApplyTy A F C') /\
    (NApplyTy A1 F \/ NApplyTy A2 F -> splu A A1 A2 -> NApplyTy A F).
Proof with elia; solve_false; try eassumption.
  introv.
  indTypFtySize (size_typ A + size_Fty F).
  split.

  introv HA1 HA2 HS.
  lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F). eauto.
  - inverts HS...
    + (* or *) exists*.
    + (* and *) inverts HA1...
      * (* interBoth *) inverts HA2... forwards (?&?): proj1 (IH F A0) H1... exists*.
      * (* interR *) exists*. applys* ApplyTyInterR.
        forwards~ : proj2 (IH F A0) H1...
      * (* Both *)  inverts HA2...
        ** exists*. applys* ApplyTyInterR. forwards~ : proj2 (IH F A0) H1...
        ** forwards (?&?): proj1 (IH F A0) H1... exists*.
    + (* and *) inverts HA1...
      * (* interL *) exists*. applys* ApplyTyInterL. forwards~ : proj2 (IH F B) H1...
      * (* interBoth *) inverts HA2... forwards (?&?): proj1 (IH F B) H1... exists*.
      * (* Both *)  inverts HA2...
        ** exists*. applys* ApplyTyInterL. forwards~ : proj2 (IH F B) H1...
        ** forwards (?&?): proj1 (IH F B) H1... exists*.
    + (* forall *) inverts HA1... inverts HA2... exists*.
    + (* rcd *) inverts HA1...
  - subst.
    forwards: appty_splitu_arg_inv HA1 H0. forwards: appty_splitu_arg_inv HA2 H0.
    destruct_conj. subst.
    forwards (?&?): proj1 (IH (fty_StackArg x0) A) H4 H2...
    forwards (?&?): proj1 (IH (fty_StackArg x1) A) H5 H3...
    exists*.

  -
    intros [HA|HA] HS;
      lets~ [?|(?&?&?&?&?)]: (ordu_or_split_Fty F); subst; eauto.
    + (* ord *) inverts~ HS...
      * (* and *) inverts HA... forwards~ : proj2 (IH F A0) H1...
      * (* and *) inverts HA... forwards~ : proj2 (IH F B) H1...
      * (* forall *) inverts HA... constructor~.
    + (* split *) forwards* [?|?]: nappty_splitu_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.
    + (* ord *) inverts~ HS...
      * (* and *) inverts HA... forwards~ : proj2 (IH F A0) H1...
      * (* and *) inverts HA... forwards~ : proj2 (IH F B) H1...
      * (* forall *) inverts HA... constructor~.
    + (* split *) forwards* [?|?]: nappty_splitu_inv HA.
      * forwards~ : proj2 (IH (fty_StackArg x0) A) HS... eauto.
      * forwards~ : proj2 (IH (fty_StackArg x1) A) HS... eauto.

   Unshelve. all: apply t_top.
Qed.

Lemma appty_splitu_fun : forall A A1 A2 F C1 C2,
    ApplyTy A1 F C1 -> ApplyTy A2 F C2 -> splu A A1 A2 ->
    exists C', ApplyTy A F C' /\ declarative_subtyping C' (t_or C1 C2).
Proof.
  intros.
  forwards* (?&?): appty_splitu_fun_aux.
Abort.

Lemma nappty_splitu_fun : forall A A1 A2 F,
    NApplyTy A1 F \/ NApplyTy A2 F -> splu A A1 A2 -> NApplyTy A F.
Proof.
  intros.
  forwards* (?&?): appty_splitu_fun_aux.
Qed.
(*
Lemma nappty_split_inv : forall A A1 A2 F,
    NApplyTy A F -> spli A A1 A2 -> NApplyTy A1 F /\ NApplyTy A2 F.
Proof with elia; try eassumption; eauto.
  introv HN HS.
  indTypFtySize (size_typ A + size_Fty F).
  inverts HN; solve_false.
  - (* rcd *) inverts HS; eauto.
  - (* forall *) inverts HS. split; constructor~.
  - (* arrow sub *) inverts~ HS.
    assert (~ declarative_subtyping B A3). {
      intros HF. apply H2. solve_dsub.
    }
    assert (~ declarative_subtyping B A4). {
      intros HF. apply H2. solve_dsub.
    }
    eauto.
  - (* arrow *) inverts~ HS.
  - (* or *) forwards [ [?|?] | [?|?] ]: double_split HS. eauto.
    all: destruct_conj.
    all: try match goal with
             | H1: NApplyTy ?A _, H2: spli ?A _ _ |- _ => forwards (?&?): IH H1 H2; elia
             end.
    all: split*.
    all: applys nappty_splitu_fun; try eassumption; eauto.
  - (* or *) forwards [ [?|?] | [?|?] ]: double_split HS. eauto.
    all: destruct_conj.
    all: try match goal with
             | H1: NApplyTy ?A _, H2: spli ?A _ _ |- _ => forwards (?&?): IH H1 H2; elia
             end.
    all: split*.
    all: applys nappty_splitu_fun...
  - (* union argL *)
    split.
    all: applys NApplyTyUnionArgL...
    all: applys IH HS...
  - (* union argR *)
    split.
    all: applys NApplyTyUnionArgR...
    all: applys IH HS...
  - auto_unify...

    Unshelve. all: apply t_top.
Abort.
*)
(* this definition cannot work
Lemma appty_split_inv : forall A A1 A2 F C,
    ApplyTy A F C -> spli A A1 A2 -> UnionOrdinaryFty F ->
    exists C1 C2,
    (ApplyTy A1 F C1 /\ C <: C1) \/ ApplyTy A2 F C2.
 *)

Lemma appty_split_inv : forall A A1 A2 F C,
    ApplyTy A F C -> spli A A1 A2 -> UnionOrdinaryFty F ->
    (exists C1 C2, ApplyTy A1 F C1 /\ ApplyTy A2 F C2 /\ (t_and C1 C2) <: C) \/
    ApplyTy A1 F C \/ ApplyTy A2 F C.
(*    (ApplyTy A1 F C /\ NApplyTy A2 F \/ ApplyTy A2 F C /\ NApplyTy A2 F ). *)
Proof with elia; try eassumption; eauto.
  introv HA HS HU.
  indTypFtySize (size_typ A).
  inverts HA; solve_false; auto_unify...
  - (* forall *) inverts HS; eauto.  Abort. (*
  - (* arrow sub *) inverts~ HS.
    + left*.
    + inverts keep H0.
      solve_dsub. forwards [?|?]: algo_sub_orlr_inv H1...
      * left. exists. applys~ ApplyTyFun. solve_dsub...
      * right. exists. applys~ ApplyTyFun. solve_dsub...
  - (* or *) forwards [ [?|?] | [?|?] ]: double_split HS. eauto.
    all: destruct_conj.
    all: repeat match goal with
             | H1: ApplyTy ?A _ _, H2: spli ?A _ _ |- _ =>
               forwards [(?&?)|(?&?)]: IH H2 H1; elia; clear H2
             | H1: ApplyTy ?A1 _ _, H2: ApplyTy ?A2 _ _, H3: splu _ ?A1 ?A2 |- _ =>
               forwards* (?&?): appty_splitu_fun H1 H2 H3; elia; clear H3
                end.
    all: eauto.
Qed. *)
(*
The above lemma does not hold without ordu condition

Let B1 B2 be two ordu types

apply (A1, B1) => apply (A1&A2, B1)
apply (A2, B2) => apply (A1&A2, B2)

together we have apply (A1&A2, B1 | B2)

But neither apply (A1, B1|B2) or apply (A2, B1|B2) holds
 *)


Lemma nappty_rename : forall A B C,
    NApplyTy A (fty_StackTyArg B) -> lc_typ C -> NApplyTy A (fty_StackTyArg C).
Proof.
  introv H Lc. inductions H; eauto.
Qed.

Lemma appty_rename : forall A B X C,
    ApplyTy A (fty_StackTyArg (t_tvar_f X)) B -> lc_typ C -> X `notin` [[A]] ->
    ApplyTy A (fty_StackTyArg C) ( [X ~~> C] B).
Proof.
  introv H Lc Fry. inductions H; simpl; simpl in Fry; eauto.
  all: try solve [ simpl_rename_goal; simpl in Fry; solve_notin ].
  - forwards~: nappty_rename C H1.
  - forwards~: nappty_rename C H0.
Qed.

Lemma appty_soundness_1 : forall A B C,
    ApplyTy A (fty_StackArg B) C -> A <: (t_arrow B C).
Proof with try eassumption; try applys ASub_refl; try match goal with |- lc_typ _ => eauto with lngen end.
  introv H. inductions H.
  all: try match goal with
           | H: UnionOrdinaryFty (_ _) |- _ => inverts H
           end.
  1-2: eauto.
  all: try forwards~ : IHApplyTy.
  all: try forwards~ : IHApplyTy1. all: try forwards~ : IHApplyTy2.
  - convert2asub. split_l.
    applys algo_trans H. applys ASub_arrow... use_left_r...
    applys algo_trans H2. applys ASub_arrow... use_right_r...
  - convert2asub.
    applys algo_trans ((t_arrow B1 (B1' | B2'))&(t_arrow B2 (B1' | B2'))).
    applys algo_trans ((t_arrow B1 B1')&(t_arrow B2 B2')). split_r...
    + split_r... * use_left_l... applys ASub_arrow... use_left_r...
      * use_right_l... applys ASub_arrow... use_right_r...
    + applys asub2nsub. applys NSub_and. applys NSpI_arrowUnion...
      applys splu2nsplu H. all: applys asub2nsub.
      * use_left_l... * use_right_l...
  - convert2asub. use_left_l...
  - convert2asub. swap_and_l... use_left_l...
  - convert2asub. split_r; eauto.
Qed.

Lemma appty_soundness_2 : forall A B C,
    ApplyTy A (fty_StackTyArg B) C ->
    exists C',  C = C'^-^B /\
                forall X, X `notin` [[C]] -> ApplyTy A (fty_StackTyArg (t_tvar_f X)) (C'-^X) /\ A <: (t_forall C').
Proof with simpl in *; try eassumption; try applys ASub_refl; try match goal with |- lc_typ _ => eauto with lngen end; destruct_conj.
  introv H. inductions H.
  all: try match goal with
           | H: UnionOrdinaryFty (_ _) |- _ => inverts H
           end.
  all: try forwards~ : IHApplyTy.
  all: try forwards~ : IHApplyTy1. all: try forwards~ : IHApplyTy2.
  all: destruct_conj.
  - exists t_bot. split~.
  - exists A. split~.
  - exists (x0|x). split~.
    + assert (Heq: forall B C X, (t_or B C) ^-^ X = t_or (B ^-^ X) (C ^-^ X)) by eauto.
      rewrite Heq. congruence.
    + assert (Heq: forall B C X, (t_or B C) -^ X = t_or (B -^ X) (C -^ X)) by eauto.
      intros X Fry... forwards~ : H5 X. forwards~ : H4 X...
      split~.
      * rewrite Heq. applys~ ApplyTyUnion H6 H4.
      * convert2asub.
        split_l. use_left_r...  use_right_r...
  - exists. split... intros X Fry. forwards~ : H2 X...
    split. eapply nappty_rename in H1. eauto. eauto.
    convert2asub. use_left_l...
  - exists. split... intros X Fry. forwards~ : H2 X...
    split. eapply nappty_rename in H0. eauto. eauto.
    convert2asub. swap_and_l... use_left_l...
  - exists (x0 & x). split...
    + assert (Heq: forall B C X, (t_and B C) ^-^ X = t_and (B ^-^ X) (C ^-^ X)) by eauto.
      rewrite Heq. congruence.
    + intros X Fry. forwards~ : H4 X... forwards~ : H5 X...
      split.
      * assert (Heq: forall B C X, (t_and B C) -^ X = t_and (B -^ X) (C -^ X)) by eauto.
        rewrite Heq. eauto.
      * convert2asub. split_r; eauto.
  Unshelve. all: apply empty.
Qed.

Lemma appty_completeness_1 : forall A B D,
    A <: (t_arrow B D) -> ordu B ->
         exists C, ApplyTy A (fty_StackArg B) C /\ (t_arrow B C) <: (t_arrow B D).
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HS Hord. apply dsub2asub in HS.
  indTypFtySize (size_typ A + size_typ D).
  forwards (?&?): algo_sub_lc HS. inverts_all_lc.
  lets~ [?|(?&?&?)]: (ordi_or_split D).
  - destruct H...
    + forwards~ [Ha|Ha]: algo_sub_andlr_inv HS;
        forwards: IH Ha...
      * forwards~ (?&[?|?]): appty_total A2 (fty_StackArg B).
        inv_arrow.
        exists (t_and x x0). split~. applys~ DSub_CovArr. applys~ DSub_InterLL.
        eauto with lngen. solve_dsub...
        exists* x.
      * forwards~ (?&[?|?]): appty_total A1 (fty_StackArg B).
        inv_arrow.
        exists (t_and x0 x). split~. applys~ DSub_CovArr. applys~ DSub_InterLR.
        eauto with lngen. solve_dsub...
        exists x. split~.
    + apply dsub2asub in HS.
      assert (EASY1: A1 <: (t_arrow B D)) by applys~ DSub_Trans HS. apply dsub2asub in EASY1.
      assert (EASY2: A2 <: (t_arrow B D)) by applys~ DSub_Trans HS. apply dsub2asub in EASY2.
      forwards: IH B EASY1... forwards: IH B EASY2...
      exists (t_or x x0). split~. inv_arrow. applys~ DSub_CovArr.
      convert2dsub. applys~ DSub_UnionL.
    + inv_arrow. convert2dsub. exists B0. split~.
    + exists*.
  -  forwards~ (Ha1&Ha2): algo_sub_and_inv HS. eauto.
     forwards: IH Ha1... forwards: IH Ha2... inv_arrow.
     auto_unify_2. exists x2. split~. applys~ DSub_CovArr.
     convert2asub. eauto.
Qed.

(* hard to define with current definition *)
(*)
Lemma appty_completeness_2 : forall A B,
    A <: (t_forall B) ->
         exists C, ApplyTy A (fty_StackTyArg B) C /\ C[B~>X]?? <: (t_forall B).
*)

(* no determinism if defined in this way

  ------------------------------------ :: ApplyFunTy
  apply(forall X . A, [B]) => A
 *)


Lemma appty_completeness_2 : forall A B,
    A <: (t_forall B) ->
         exists C L, forall X, X `notin` L ->
             ApplyTy A (fty_StackTyArg (t_tvar_f X)) (C-^X) /\ (t_forall C) <: (t_forall B).
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HS. apply dsub2asub in HS.
  indTypFtySize (size_typ A + size_typ B).
  lets~ [?|(?&?&?)]: (ordi_or_split (t_forall B)).
  - assert (lc_typ A) by eauto. destruct H0...
    + forwards~ [Ha|Ha]: algo_sub_andlr_inv HS;
        forwards: IH Ha...
      * pick fresh X for ([[A1]] `union` [[A2]] `union` x0 `union` [[x]]). forwards~ : H0 X.
        forwards~ (?&[?|?]): appty_total A2 (fty_StackTyArg (t_tvar_f X)); destruct_conj.
        ** exists. intros Y Fry.
           forwards~ HR1: appty_rename (t_tvar_f Y) H1. forwards~ HR2: appty_rename (t_tvar_f Y) H2.
           simpl_rename HR1. simpl_rename HR2.
           assert (Heq: forall Y, (t_and x (close_typ_wrt_typ X x1)) -^ Y = t_and (x -^ Y) (close_typ_wrt_typ X x1 -^ Y)) by eauto. rewrite Heq.
           split~. applys DSub_CovAll. intros X0 Fry2.
           apply dsub2asub in H3. forwards: algo_sub_forall_inv X0 H3.
           rewrite Heq. applys DSub_InterLL. eauto.
           solve_dsub...
           autorewrite with lngen. all: solve_notin.
        ** exists. intros Y Fry.
           forwards~ HR1: appty_rename (t_tvar_f Y) H1. simpl_rename HR1.
           forwards~ HR2: nappty_rename (t_tvar_f Y) H2.
           split. applys~ ApplyTyInterL HR1. auto. eauto with lngen.
      * pick fresh X for ([[A1]] `union` [[A2]] `union` x0 `union` [[x]]). forwards~ : H0 X.
        forwards~ (?&[?|?]): appty_total A1 (fty_StackTyArg (t_tvar_f X)); destruct_conj.
        ** exists. intros Y Fry.
           forwards~ HR1: appty_rename (t_tvar_f Y) H1. forwards~ HR2: appty_rename (t_tvar_f Y) H2.
           simpl_rename HR1. simpl_rename HR2.
           assert (Heq: forall Y, (t_and (close_typ_wrt_typ X x1) x) -^ Y = t_and (close_typ_wrt_typ X x1 -^ Y) (x -^ Y)) by eauto. rewrite Heq.
           split~. applys DSub_CovAll. intros X0 Fry2.
           apply dsub2asub in H3. forwards: algo_sub_forall_inv X0 H3.
           rewrite Heq. applys DSub_InterLR. eauto.
           solve_dsub...
           autorewrite with lngen.
           all : solve_notin.
        ** exists. intros Y Fry.
           forwards~ HR1: appty_rename (t_tvar_f Y) H1. simpl_rename HR1.
           forwards~ HR2: nappty_rename (t_tvar_f Y) H2.
           split. applys~ ApplyTyInterR HR1. auto. eauto with lngen.

    + apply dsub2asub in HS.
      assert (EASY1: A1 <: (t_forall B)) by applys~ DSub_Trans HS. apply dsub2asub in EASY1.
      assert (EASY2: A2 <: (t_forall B)) by applys~ DSub_Trans HS. apply dsub2asub in EASY2.
      forwards: IH B EASY1... forwards: IH B EASY2...
      exists (t_or x x1).
      exists (union x0
                 (union x2
                    (union [[B]]
                           (union [[A1]] (union [[A2]] (union [[x]] [[x1]])))))).
      intros. instantiate_cofinites.
      assert (Heq:forall X, (x | x1 -^ X) = (x -^ X) | (x1-^X)) by eauto. rewrite Heq.
      split~. applys DSub_CovAll. intros. rewrite Heq. inv_forall.
      convert2dsub. applys~ DSub_UnionL H3 H6.
    + exists B0. exists (union [[B]] [[B0]]). convert2dsub. split~.
    + exists t_bot. exists. split~. eauto.
  -  forwards~ (Ha1&Ha2): algo_sub_and_inv HS... inverts H.
     forwards: IH Ha1... forwards: IH Ha2...
     exists x. exists (x0 `union` x2 `union` [[x]] `union` [[x1]]).
     intros. instantiate_cofinites.
     auto_unify_2. forwards~ : open_typ_wrt_typ_inj H5.
     subst. split~.
     convert2asub. applys ASub_forall. intros Y Fry.
     instantiate_cofinites_with Y.
     inv_forall. applys* ASub_and H1.

     Unshelve. all: apply empty.
Qed.


Lemma monotonicity_appty_1 : forall A A' F C,
    ApplyTy A F C -> A' <: A -> exists C', C' <: C /\ ApplyTy A' F C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  indTypFtySize (size_typ A' + size_typ A + size_Fty F).
  lets~ [HF|(?&?&?&?&?)]: (ordu_or_split_Fty F). eauto.
  2: { subst. forwards : appty_splitu_arg_inv HA H0. destruct_conj.
       subst. forwards (?&?&?): IH H1... forwards (?&?&?): IH H2...
       exists. split. 2: applys~ ApplyTyUnionArg H0...
       applys~ DSub_UnionL. }
  inverts HF.
  - forwards: appty_soundness_1 HA.
    forwards HSN: DSub_Trans HS...
    forwards~ : appty_completeness_1 HSN. destruct_conj.
    inv_arrow. convert2dsub. exists* x.
  - forwards: appty_soundness_2 HA...
    pick_fresh Y. forwards~ : H1 Y...
    forwards HSN: DSub_Trans HS...
    forwards~ : appty_completeness_2 HSN...
    pick fresh X.
    forwards~ : H4 X. destruct_conj.
    eapply appty_rename in H5. exists. split...
    simpl_rename_goal. subst~.
    convert2asub.
    forwards : algo_sub_forall_inv X H6.
    eapply asub2nsub in H0.
    eapply typsubst_typ_new_sub in H0.
    rewrite 2 typsubst_typ_spec in H0; rewrite 2 close_typ_wrt_typ_open_typ_wrt_typ in H0.
    apply asub2nsub. apply~ H0.
    all: eauto.
Qed.

Lemma monotonicity_appty_2_1 : forall A B B' C,
    ApplyTy A (fty_StackArg B) C -> declarative_subtyping B' B ->
    exists C', declarative_subtyping C' C /\ ApplyTy A (fty_StackArg B') C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  indTypFtySize (size_typ A + size_typ B' + size_typ B).
  lets~ [HF|(?&?&?)]: (ordu_or_split B').
  - forwards: appty_soundness_1 HA.
    forwards HSN: DSub_Trans H... applys DSub_FunCon HS. eauto.
    forwards~ : appty_completeness_1 HSN. destruct_conj.
    inv_arrow. convert2dsub. exists* x.
  - assert (S1: x <: B). {
      applys~ DSub_Trans HS.
      convert2asub. use_left_r... applys ASub_refl. eauto.
    }
    forwards: IH S1...
    assert (S2: x0 <: B). {
      applys~ DSub_Trans HS.
      convert2asub. use_right_r... applys ASub_refl. eauto.
    }
    forwards: IH S2...
    exists (x1|x2). split~. applys~ ApplyTyUnionArg H.
Qed.

Lemma monotonicity_subtyping : forall A B C D X,
  algo_sub A B -> algo_sub C D ->
  algo_sub ([X ~~> C] A) ([X ~~> D] B).
Proof with (simpl in *; eauto with lngen; eauto using typsubst_typ_lc_typ, typsubst_typ_spli, typsubst_typ_splu).
  introv HS1 HS2.
  applys algo_trans [X ~~> C] (B).
  { applys* typsubst_typ_algo_sub. }
  assert (Lc: lc_typ B) by eauto.
  clear HS1.
  convert2dsub.
  induction Lc; simpl; auto.
  - case_if; auto.
  - applys DSub_Trans (t_arrow [X ~~> C] (A0) [X ~~> D] (B)).
    + applys~ DSub_CovArr.
    + applys~ DSub_FunCon.
      (* incorrect lemma: breaks in function case *)
Abort.
(*   IHLc1 : [X ~~> C] (A0) <: [X ~~> D] (A0)
  IHLc2 : [X ~~> C] (B) <: [X ~~> D] (B)
  ============================
  [X ~~> D] (A0) <: [X ~~> C] (A0)
 *)

Lemma monotonicity_appty_2_2 : forall A B B' C,
    ApplyTy A (fty_StackTyArg B) C -> declarative_subtyping B' B ->
    exists C', declarative_subtyping C' C /\ ApplyTy A (fty_StackTyArg B') C'.
Proof with try eassumption; elia; solve_false; destruct_conj.
  introv HA HS.
  forwards: appty_soundness_2 HA. destruct_conj.
  subst.
  pick fresh X. forwards~ (?&HS2): H0 X.
  { forwards Hless: typefv_typ_open_typ_wrt_typ_upper x B.
    rewrite Hless. solve_notin. }
  forwards (y&?&?): appty_completeness_2 HS2.
  exists (y ^-^ B').
  pick fresh Y. forwards~ (Happ&?): H1 Y.
  forwards~ HG: appty_rename B' Happ.
  simpl_rename HG. split~.
  { convert2asub. forwards: algo_sub_forall_inv Y H2.
    Abort. (*
    forwards: monotonicity_subtyping Y H3 HS.
    repeat simpl_rename H4. all: auto. }
  solve_notin.
Qed. *)

(*
C <: B

apply ( forall X . X -> A  , [ B ] ) => B -> A

apply ( forall X . X -> A  , [ C ] ) => C -> A

=======================================================

XXX   C -> A <: B -> A   XXX
*)
