(* generated by Ott 0.31, locally-nameless lngen from: ../spec/rules.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition typevar : Set := var.
Definition I : Set := nat.

Inductive l : Set :=
 | lbl_TagIndex (i:I)
 | lbl_TagLeft : l
 | lbl_TagRight : l.

Inductive typ : Set :=  (*r value type *)
 | t_tvar_b (_:nat)
 | t_tvar_f (X:typevar)
 | t_rcd (l5:l) (A:typ)
 | t_and (A1:typ) (A2:typ)
 | t_or (A1:typ) (A2:typ)
 | t_arrow (A:typ) (B:typ)
 | t_forall (B:typ)
 | t_top : typ
 | t_bot : typ.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_typ_wrt_typ_rec (k:nat) (A_5:typ) (A__6:typ) {struct A__6}: typ :=
  match A__6 with
  | (t_tvar_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_tvar_b nat
        | inleft (right _) => A_5
        | inright _ => t_tvar_b (nat - 1)
      end
  | (t_tvar_f X) => t_tvar_f X
  | (t_rcd l5 A) => t_rcd l5 (open_typ_wrt_typ_rec k A_5 A)
  | (t_and A1 A2) => t_and (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
  | (t_or A1 A2) => t_or (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
  | (t_arrow A B) => t_arrow (open_typ_wrt_typ_rec k A_5 A) (open_typ_wrt_typ_rec k A_5 B)
  | (t_forall B) => t_forall (open_typ_wrt_typ_rec (S k) A_5 B)
  | t_top => t_top
  | t_bot => t_bot
end.

Definition open_typ_wrt_typ A_5 A__6 := open_typ_wrt_typ_rec 0 A__6 A_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_typ *)
Inductive lc_typ : typ -> Prop :=    (* defn lc_typ *)
 | lc_t_tvar_f : forall (X:typevar),
     (lc_typ (t_tvar_f X))
 | lc_t_rcd : forall (l5:l) (A:typ),
     (lc_typ A) ->
     (lc_typ (t_rcd l5 A))
 | lc_t_and : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ (t_and A1 A2))
 | lc_t_or : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ (t_or A1 A2))
 | lc_t_arrow : forall (A B:typ),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_typ (t_arrow A B))
 | lc_t_forall : forall (B:typ),
      ( forall X , lc_typ  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     (lc_typ (t_forall B))
 | lc_t_top :
     (lc_typ t_top)
 | lc_t_bot :
     (lc_typ t_bot).
(** free variables *)
Fixpoint typefv_typ (A_5:typ) : vars :=
  match A_5 with
  | (t_tvar_b nat) => {}
  | (t_tvar_f X) => {{X}}
  | (t_rcd l5 A) => (typefv_typ A)
  | (t_and A1 A2) => (typefv_typ A1) \u (typefv_typ A2)
  | (t_or A1 A2) => (typefv_typ A1) \u (typefv_typ A2)
  | (t_arrow A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_forall B) => (typefv_typ B)
  | t_top => {}
  | t_bot => {}
end.

(** substitutions *)
Fixpoint typsubst_typ (A_5:typ) (X5:typevar) (A__6:typ) {struct A__6} : typ :=
  match A__6 with
  | (t_tvar_b nat) => t_tvar_b nat
  | (t_tvar_f X) => (if eq_var X X5 then A_5 else (t_tvar_f X))
  | (t_rcd l5 A) => t_rcd l5 (typsubst_typ A_5 X5 A)
  | (t_and A1 A2) => t_and (typsubst_typ A_5 X5 A1) (typsubst_typ A_5 X5 A2)
  | (t_or A1 A2) => t_or (typsubst_typ A_5 X5 A1) (typsubst_typ A_5 X5 A2)
  | (t_arrow A B) => t_arrow (typsubst_typ A_5 X5 A) (typsubst_typ A_5 X5 B)
  | (t_forall B) => t_forall (typsubst_typ A_5 X5 B)
  | t_top => t_top
  | t_bot => t_bot
end.


(** definitions *)

(* defns DSub *)
Inductive DeclarativeSubtyping : typ -> typ -> Prop :=    (* defn DeclarativeSubtyping *)
 | DSub_Refl : forall (A:typ),
     lc_typ A ->
     DeclarativeSubtyping A A
 | DSub_Trans : forall (A1 A3 A2:typ),
     DeclarativeSubtyping A1 A2 ->
     DeclarativeSubtyping A2 A3 ->
     DeclarativeSubtyping A1 A3
 | DSub_CovIn : forall (l5:l) (A B:typ),
     DeclarativeSubtyping A B ->
     DeclarativeSubtyping (t_rcd l5 A) (t_rcd l5 B)
 | DSub_CovArr : forall (C A B:typ),
     lc_typ C ->
     DeclarativeSubtyping A B ->
     DeclarativeSubtyping (t_arrow C A) (t_arrow C B)
 | DSub_CovAll : forall (L:vars) (A B:typ),
      ( forall X , X \notin  L  -> DeclarativeSubtyping  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     DeclarativeSubtyping (t_forall A) (t_forall B)
 | DSub_CovInterL : forall (A C B:typ),
     lc_typ C ->
     DeclarativeSubtyping A B ->
     DeclarativeSubtyping (t_and A C) (t_and B C)
 | DSub_CovInterR : forall (C A B:typ),
     lc_typ C ->
     DeclarativeSubtyping A B ->
     DeclarativeSubtyping (t_and C A) (t_and C B)
 | DSub_CovUnionL : forall (A C B:typ),
     lc_typ C ->
     DeclarativeSubtyping A B ->
     DeclarativeSubtyping (t_or A C) (t_or B C)
 | DSub_CovUnionR : forall (C A B:typ),
     lc_typ C ->
     DeclarativeSubtyping A B ->
     DeclarativeSubtyping (t_or C A) (t_or C B)
 | DSub_FunCon : forall (A1 B A2:typ),
     lc_typ B ->
     DeclarativeSubtyping A2 A1 ->
     DeclarativeSubtyping (t_arrow A1 B) (t_arrow A2 B)
 | DSub_CovDistIIn : forall (l5:l) (A B:typ),
     lc_typ A ->
     lc_typ B ->
     DeclarativeSubtyping (t_and  (t_rcd l5 A)   (t_rcd l5 B) ) (t_rcd l5  (t_and A B) )
 | DSub_CovDistIArr : forall (C A B:typ),
     lc_typ C ->
     lc_typ A ->
     lc_typ B ->
     DeclarativeSubtyping (t_and  (t_arrow C A)   (t_arrow C B) )  (t_arrow C (t_and A B))
 | DSub_CovDistIUnionL : forall (A C B:typ),
     lc_typ A ->
     lc_typ B ->
     lc_typ C ->
     DeclarativeSubtyping (t_and  (t_or A C)   (t_or B C) ) (t_or  (t_and A B)  C)
 | DSub_CovDistIUnionR : forall (C A B:typ),
     lc_typ C ->
     lc_typ A ->
     lc_typ B ->
     DeclarativeSubtyping (t_and  (t_or C A)   (t_or C B) ) (t_or C  (t_and A B) )
 | DSub_CovDistIAll : forall (A B:typ),
     lc_typ (t_forall A) ->
     lc_typ (t_forall B) ->
     DeclarativeSubtyping (t_and  (t_forall A)   (t_forall B) )  (t_forall (t_and A B))
 | DSub_CovDistUIn : forall (l5:l) (A B:typ),
     lc_typ A ->
     lc_typ B ->
     DeclarativeSubtyping (t_rcd l5  (t_or A B) ) (t_or  (t_rcd l5 A)   (t_rcd l5 B) )
 | DSub_CovDistUAll : forall (A B:typ),
     lc_typ (t_forall  (t_or A B) ) ->
     lc_typ (t_forall  (t_or A B) ) ->
     DeclarativeSubtyping (t_forall  (t_or A B) ) (t_or  (t_forall A)   (t_forall B) )
 | DSub_CovDistUInterL : forall (A B C:typ),
     lc_typ A ->
     lc_typ B ->
     lc_typ C ->
     DeclarativeSubtyping (t_and  (t_or A B)  C) (t_or  (t_and A C)   (t_and B C) )
 | DSub_CovDistUInterR : forall (C A B:typ),
     lc_typ A ->
     lc_typ C ->
     lc_typ B ->
     DeclarativeSubtyping (t_and C  (t_or A B) ) (t_or  (t_and C A)   (t_and C B) )
 | DSub_FunDistI : forall (A1 B A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     lc_typ B ->
     DeclarativeSubtyping (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow  (t_or A1 A2)  B)
 | DSub_InterLL : forall (A1 A2 B:typ),
     lc_typ A2 ->
     DeclarativeSubtyping A1 B ->
     DeclarativeSubtyping (t_and A1 A2) B
 | DSub_InterLR : forall (A1 A2 B:typ),
     lc_typ A1 ->
     DeclarativeSubtyping A2 B ->
     DeclarativeSubtyping (t_and A1 A2) B
 | DSub_InterR : forall (A B1 B2:typ),
     DeclarativeSubtyping A B1 ->
     DeclarativeSubtyping A B2 ->
     DeclarativeSubtyping A (t_and B1 B2)
 | DSub_UnionL : forall (A1 A2 B:typ),
     DeclarativeSubtyping A1 B ->
     DeclarativeSubtyping A2 B ->
     DeclarativeSubtyping (t_or A1 A2) B
 | DSub_UnionRL : forall (A B1 B2:typ),
     lc_typ B2 ->
     DeclarativeSubtyping A B1 ->
     DeclarativeSubtyping A (t_or B1 B2)
 | DSub_UnionRR : forall (A B1 B2:typ),
     lc_typ B1 ->
     DeclarativeSubtyping A B2 ->
     DeclarativeSubtyping A (t_or B1 B2)
 | DSub_Empty : forall (B:typ),
     lc_typ B ->
     DeclarativeSubtyping t_bot B
 | DSub_Top : forall (A:typ),
     lc_typ A ->
     DeclarativeSubtyping A t_top.

(* defns Ordinary *)
Inductive ordu : typ -> Prop :=    (* defn ordu *)
 | OrdU_var : forall (X:typevar),
     ordu (t_tvar_f X)
 | OrdU_top :
     ordu t_top
 | OrdU_bot :
     ordu t_bot
 | OrdU_arrow : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     ordu (t_arrow A B)
 | OrdU_and : forall (A B:typ),
     ordu A ->
     ordu B ->
     ordu (t_and A B)
 | OrdU_rcd : forall (l5:l) (A:typ),
     ordu A ->
     ordu (t_rcd l5 A)
 | OrdU_forall : forall (L:vars) (A:typ),
      ( forall X , X \notin  L  -> ordu  ( open_typ_wrt_typ A (t_tvar_f X) )  )  ->
     ordu (t_forall A)
with ordi : typ -> Prop :=    (* defn ordi *)
 | OrdI_var : forall (X:typevar),
     ordi (t_tvar_f X)
 | OrdI_top :
     ordi t_top
 | OrdI_bot :
     ordi t_bot
 | OrdI_arrow : forall (A B:typ),
     ordu A ->
     ordi B ->
     ordi (t_arrow A B)
 | OrdI_or : forall (A B:typ),
     ordi A ->
     ordi B ->
     ordi (t_or A B)
 | OrdI_rcd : forall (l5:l) (A:typ),
     ordi A ->
     ordi (t_rcd l5 A)
 | OrdI_forall : forall (L:vars) (A:typ),
      ( forall X , X \notin  L  -> ordi  ( open_typ_wrt_typ A (t_tvar_f X) )  )  ->
     ordi (t_forall A).

(* defns Split *)
Inductive spli : typ -> typ -> typ -> Prop :=    (* defn spli *)
 | SpI_and : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     spli (t_and A B) A B
 | SpI_orl : forall (A B A1 A2:typ),
     lc_typ B ->
     spli A A1 A2 ->
     spli (t_or A B) (t_or A1 B) (t_or A2 B)
 | SpI_orr : forall (A B B1 B2:typ),
     ordi A ->
     spli B B1 B2 ->
     spli (t_or A B) (t_or A B1) (t_or A B2)
 | SpI_arrow : forall (A B B1 B2:typ),
     lc_typ A ->
     spli B B1 B2 ->
     spli (t_arrow A B) (t_arrow A B1) (t_arrow A B2)
 | SpI_arrowUnion : forall (A B A1 A2:typ),
     ordi B ->
     splu A A1 A2 ->
     spli (t_arrow A B) (t_arrow A1 B) (t_arrow A2 B)
 | SpI_forall : forall (L:vars) (A A1 A2:typ),
      ( forall X , X \notin  L  -> spli  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ A1 (t_tvar_f X) )   ( open_typ_wrt_typ A2 (t_tvar_f X) )  )  ->
     spli (t_forall A) (t_forall A1) (t_forall A2)
 | SpI_in : forall (l5:l) (A A1 A2:typ),
     spli A A1 A2 ->
     spli (t_rcd l5 A) (t_rcd l5 A1) (t_rcd l5 A2)
with splu : typ -> typ -> typ -> Prop :=    (* defn splu *)
 | SpU_or : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     splu (t_or A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     lc_typ B ->
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2)
 | SpU_forall : forall (L:vars) (A A1 A2:typ),
      ( forall X , X \notin  L  -> splu  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ A1 (t_tvar_f X) )   ( open_typ_wrt_typ A2 (t_tvar_f X) )  )  ->
     splu (t_forall A) (t_forall A1) (t_forall A2)
 | SpU_in : forall (l5:l) (A A1 A2:typ),
     splu A A1 A2 ->
     splu (t_rcd l5 A) (t_rcd l5 A1) (t_rcd l5 A2).

(* defns AlgorithmicSubtyping *)
Inductive algo_sub : typ -> typ -> Prop :=    (* defn algo_sub *)
 | ASub_var : forall (X:typevar),
     algo_sub (t_tvar_f X) (t_tvar_f X)
 | ASub_top : forall (A:typ),
     lc_typ A ->
     algo_sub A t_top
 | ASub_bot : forall (A:typ),
     lc_typ A ->
     algo_sub t_bot A
 | ASub_arrow : forall (A1 A2 B1 B2:typ),
     ordi (t_arrow A1 A2) ->
     ordi (t_arrow B1 B2) ->
     algo_sub B1 A1 ->
     algo_sub A2 B2 ->
     algo_sub (t_arrow A1 A2) (t_arrow B1 B2)
 | ASub_forall : forall (L:vars) (A B:typ),
      ( forall X , X \notin  L  -> ordi  ( open_typ_wrt_typ A (t_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> ordi  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> ordu  ( open_typ_wrt_typ A (t_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> ordu  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> algo_sub  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     algo_sub (t_forall A) (t_forall B)
 | ASub_rcd : forall (l5:l) (A B:typ),
     ordi A ->
     ordi B ->
     ordu A ->
     ordu B ->
     algo_sub A B ->
     algo_sub (t_rcd l5 A) (t_rcd l5 B)
 | ASub_and : forall (A B B1 B2:typ),
     spli B B1 B2 ->
     algo_sub A B1 ->
     algo_sub A B2 ->
     algo_sub A B
 | ASub_andl : forall (A B A1 A2:typ),
     ordi B ->
     spli A A1 A2 ->
     algo_sub A1 B ->
     algo_sub A B
 | ASub_andr : forall (A B A1 A2:typ),
     ordi B ->
     spli A A1 A2 ->
     algo_sub A2 B ->
     algo_sub A B
 | ASub_or : forall (A B A1 A2:typ),
     ordi A ->
     ordi B ->
     splu A A1 A2 ->
     algo_sub A1 B ->
     algo_sub A2 B ->
     algo_sub A B
 | ASub_orl : forall (A B B1 B2:typ),
     ordi A ->
     ordi B ->
     ordu A ->
     splu B B1 B2 ->
     algo_sub A B1 ->
     algo_sub A B
 | ASub_orr : forall (A B B1 B2:typ),
     ordi A ->
     ordi B ->
     ordu A ->
     splu B B1 B2 ->
     algo_sub A B2 ->
     algo_sub A B.


(** infrastructure *)
Hint Constructors DeclarativeSubtyping ordu ordi spli splu lc_typ : core.
