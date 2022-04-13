(* generated by Ott 0.31, locally-nameless lngen from: ../spec/rules.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition typevar : Set := var.
Definition I : Set := nat.

Inductive l : Set := 
 | lbl_TagIndex (i:I)
 | lbl_TagLeft : l
 | lbl_TagRight : l.

Inductive typ : Set :=  (*r type *)
 | t_tvar_b (_:nat)
 | t_tvar_f (X:typevar)
 | t_rcd (l5:l) (A:typ)
 | t_and (A1:typ) (A2:typ)
 | t_or (A1:typ) (A2:typ)
 | t_arrow (A:typ) (B:typ)
 | t_forall (B:typ)
 | t_top : typ
 | t_bot : typ.

Inductive Fty : Set :=  (*r elimination type *)
 | fty_StackArg (A:typ)
 | fty_StackTyArg (A:typ).

Definition tctx : Set := list ( atom * typ ).

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

Definition open_Fty_wrt_typ_rec (k:nat) (A5:typ) (FVty5:Fty) : Fty :=
  match FVty5 with
  | (fty_StackArg A) => fty_StackArg (open_typ_wrt_typ_rec k A5 A)
  | (fty_StackTyArg A) => fty_StackTyArg (open_typ_wrt_typ_rec k A5 A)
end.

Definition open_Fty_wrt_typ A5 FVty5 := open_Fty_wrt_typ_rec 0 FVty5 A5.

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

(* defns LC_Fty *)
Inductive lc_Fty : Fty -> Prop :=    (* defn lc_Fty *)
 | lc_fty_StackArg : forall (A:typ),
     (lc_typ A) ->
     (lc_Fty (fty_StackArg A))
 | lc_fty_StackTyArg : forall (A:typ),
     (lc_typ A) ->
     (lc_Fty (fty_StackTyArg A)).
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

Definition typefv_Fty (FVty5:Fty) : vars :=
  match FVty5 with
  | (fty_StackArg A) => (typefv_typ A)
  | (fty_StackTyArg A) => (typefv_typ A)
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

Definition typsubst_Fty (A5:typ) (X5:typevar) (FVty5:Fty) : Fty :=
  match FVty5 with
  | (fty_StackArg A) => fty_StackArg (typsubst_typ A5 X5 A)
  | (fty_StackTyArg A) => fty_StackTyArg (typsubst_typ A5 X5 A)
end.


(** definitions *)

(* defns DSub *)
Inductive declarative_subtyping : typ -> typ -> Prop :=    (* defn declarative_subtyping *)
 | DSub_Refl : forall (A:typ),
     lc_typ A ->
     declarative_subtyping A A
 | DSub_Trans : forall (A1 A3 A2:typ),
     declarative_subtyping A1 A2 ->
     declarative_subtyping A2 A3 ->
     declarative_subtyping A1 A3
 | DSub_CovIn : forall (l5:l) (A B:typ),
     declarative_subtyping A B ->
     declarative_subtyping (t_rcd l5 A) (t_rcd l5 B)
 | DSub_CovArr : forall (C A B:typ),
     lc_typ C ->
     declarative_subtyping A B ->
     declarative_subtyping (t_arrow C A) (t_arrow C B)
 | DSub_CovAll : forall (L:vars) (A B:typ),
      ( forall X , X \notin  L  -> declarative_subtyping  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     declarative_subtyping (t_forall A) (t_forall B)
 | DSub_CovInterL : forall (A C B:typ),
     lc_typ C ->
     declarative_subtyping A B ->
     declarative_subtyping (t_and A C) (t_and B C)
 | DSub_CovInterR : forall (C A B:typ),
     lc_typ C ->
     declarative_subtyping A B ->
     declarative_subtyping (t_and C A) (t_and C B)
 | DSub_CovUnionL : forall (A C B:typ),
     lc_typ C ->
     declarative_subtyping A B ->
     declarative_subtyping (t_or A C) (t_or B C)
 | DSub_CovUnionR : forall (C A B:typ),
     lc_typ C ->
     declarative_subtyping A B ->
     declarative_subtyping (t_or C A) (t_or C B)
 | DSub_FunCon : forall (A1 B A2:typ),
     lc_typ B ->
     declarative_subtyping A2 A1 ->
     declarative_subtyping (t_arrow A1 B) (t_arrow A2 B)
 | DSub_CovDistIIn : forall (l5:l) (A B:typ),
     lc_typ A ->
     lc_typ B ->
     declarative_subtyping (t_and  (t_rcd l5 A)   (t_rcd l5 B) ) (t_rcd l5  (t_and A B) )
 | DSub_CovDistIArr : forall (C A B:typ),
     lc_typ C ->
     lc_typ A ->
     lc_typ B ->
     declarative_subtyping (t_and  (t_arrow C A)   (t_arrow C B) )  (t_arrow C (t_and A B)) 
 | DSub_CovDistIUnionL : forall (A C B:typ),
     lc_typ A ->
     lc_typ B ->
     lc_typ C ->
     declarative_subtyping (t_and  (t_or A C)   (t_or B C) ) (t_or  (t_and A B)  C)
 | DSub_CovDistIUnionR : forall (C A B:typ),
     lc_typ C ->
     lc_typ A ->
     lc_typ B ->
     declarative_subtyping (t_and  (t_or C A)   (t_or C B) ) (t_or C  (t_and A B) )
 | DSub_CovDistIAll : forall (A B:typ),
     lc_typ (t_forall A) ->
     lc_typ (t_forall B) ->
     declarative_subtyping (t_and  (t_forall A)   (t_forall B) )  (t_forall (t_and A B)) 
 | DSub_CovDistUIn : forall (l5:l) (A B:typ),
     lc_typ A ->
     lc_typ B ->
     declarative_subtyping (t_rcd l5  (t_or A B) ) (t_or  (t_rcd l5 A)   (t_rcd l5 B) )
 | DSub_CovDistUAll : forall (A B:typ),
     lc_typ (t_forall  (t_or A B) ) ->
     lc_typ (t_forall  (t_or A B) ) ->
     declarative_subtyping (t_forall  (t_or A B) ) (t_or  (t_forall A)   (t_forall B) )
 | DSub_CovDistUInterL : forall (A B C:typ),
     lc_typ A ->
     lc_typ B ->
     lc_typ C ->
     declarative_subtyping (t_and  (t_or A B)  C) (t_or  (t_and A C)   (t_and B C) )
 | DSub_CovDistUInterR : forall (C A B:typ),
     lc_typ A ->
     lc_typ C ->
     lc_typ B ->
     declarative_subtyping (t_and C  (t_or A B) ) (t_or  (t_and C A)   (t_and C B) )
 | DSub_FunDistI : forall (A1 B A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     lc_typ B ->
     declarative_subtyping (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow  (t_or A1 A2)  B)
 | DSub_InterLL : forall (A1 A2 B:typ),
     lc_typ A2 ->
     declarative_subtyping A1 B ->
     declarative_subtyping (t_and A1 A2) B
 | DSub_InterLR : forall (A1 A2 B:typ),
     lc_typ A1 ->
     declarative_subtyping A2 B ->
     declarative_subtyping (t_and A1 A2) B
 | DSub_InterR : forall (A B1 B2:typ),
     declarative_subtyping A B1 ->
     declarative_subtyping A B2 ->
     declarative_subtyping A (t_and B1 B2)
 | DSub_UnionL : forall (A1 A2 B:typ),
     declarative_subtyping A1 B ->
     declarative_subtyping A2 B ->
     declarative_subtyping (t_or A1 A2) B
 | DSub_UnionRL : forall (A B1 B2:typ),
     lc_typ B2 ->
     declarative_subtyping A B1 ->
     declarative_subtyping A (t_or B1 B2)
 | DSub_UnionRR : forall (A B1 B2:typ),
     lc_typ B1 ->
     declarative_subtyping A B2 ->
     declarative_subtyping A (t_or B1 B2)
 | DSub_Empty : forall (B:typ),
     lc_typ B ->
     declarative_subtyping t_bot B
 | DSub_Top : forall (A:typ),
     lc_typ A ->
     declarative_subtyping A t_top.

(* defns NegTyp *)
Inductive isNegTyp : typ -> Prop :=    (* defn isNegTyp *)
 | NTypFun : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     isNegTyp (t_arrow A B)
 | NTypForall : forall (A:typ),
     lc_typ (t_forall A) ->
     isNegTyp (t_forall A)
 | NTypIntersection : forall (A B:typ),
     isNegTyp A ->
     isNegTyp B ->
     isNegTyp (t_and A B)
 | NTypUnionL : forall (A B:typ),
     lc_typ B ->
     isNegTyp A ->
     isNegTyp (t_or A B)
 | NTypUnionR : forall (A B:typ),
     lc_typ A ->
     isNegTyp B ->
     isNegTyp (t_or A B)
 | NTypTop : 
     isNegTyp t_top.

(* defns ValTyp *)
Inductive isValTyp : typ -> Prop :=    (* defn isValTyp *)
 | VTypIn : forall (l5:l) (V:typ),
     isValTyp V ->
     isValTyp (t_rcd l5 V)
 | VTypNeg : forall (A:typ),
     isNegTyp A ->
     isValTyp A.

(* defns ValFty *)
Inductive isValFty : Fty -> Prop :=    (* defn isValFty *)
 | VFtyTypArg : forall (A:typ),
     lc_typ A ->
     isValFty (fty_StackTyArg A)
 | VFtyArg : forall (V:typ),
     isValTyp V ->
     isValFty (fty_StackArg V).

(* defns PSub *)
Inductive PositiveSubtyping : typ -> typ -> Prop :=    (* defn PositiveSubtyping *)
 | PSub_In : forall (l5:l) (V A:typ),
     PositiveSubtyping V A ->
     PositiveSubtyping (t_rcd l5 V) (t_rcd l5 A)
 | PSub_UnionL : forall (V A B:typ),
     lc_typ B ->
     PositiveSubtyping V A ->
     PositiveSubtyping V (t_or A B)
 | PSub_UnionR : forall (V A B:typ),
     lc_typ A ->
     PositiveSubtyping V B ->
     PositiveSubtyping V (t_or A B)
 | PSub_Intersect : forall (V A B:typ),
     PositiveSubtyping V A ->
     PositiveSubtyping V B ->
     PositiveSubtyping V (t_and A B)
 | PSub_Neg : forall (V Aneg:typ),
     lc_typ V ->
     isNegTyp Aneg ->
     PositiveSubtyping V Aneg.

(* defns NSub *)
Inductive NegativeSubtyping : typ -> Fty -> Prop :=    (* defn NegativeSubtyping *)
 | NSub_Fun : forall (A B V:typ),
     lc_typ B ->
     isValTyp V ->
     PositiveSubtyping V A ->
     NegativeSubtyping (t_arrow A B) (fty_StackArg V)
 | NSub_TyFun : forall (A B:typ),
     lc_typ (t_forall A) ->
     lc_typ B ->
     NegativeSubtyping (t_forall A) (fty_StackTyArg B)
 | NSub_Union : forall (Aneg1 Aneg2:typ) (Ftyalt:Fty),
     NegativeSubtyping Aneg1 Ftyalt ->
     NegativeSubtyping Aneg2 Ftyalt ->
     NegativeSubtyping (t_or Aneg1 Aneg2) Ftyalt
 | NSub_IntersectL : forall (Aneg1 Aneg2:typ) (Ftyalt:Fty),
     lc_typ Aneg2 ->
     NegativeSubtyping Aneg1 Ftyalt ->
     NegativeSubtyping (t_and Aneg1 Aneg2) Ftyalt
 | NSub_IntersectR : forall (Aneg1 Aneg2:typ) (Ftyalt:Fty),
     lc_typ Aneg1 ->
     NegativeSubtyping Aneg2 Ftyalt ->
     NegativeSubtyping (t_and Aneg1 Aneg2) Ftyalt.

(* defns MatchTy *)
Inductive MatchTy : l -> typ -> typ -> Prop :=    (* defn MatchTy *)
 | MatchTyTop : forall (l5:l),
     MatchTy l5 t_top t_top
 | MatchTyIn : forall (l5:l) (A:typ),
     lc_typ A ->
     MatchTy l5 (t_rcd l5 A) A
 | MatchTyUnionL : forall (l5:l) (A1 A2 B1:typ),
     MatchTy l5 A1 B1 ->
     NMatchTy l5 A2 ->
     MatchTy l5 (t_or A1 A2) B1
 | MatchTyUnionR : forall (l5:l) (A1 A2 B2:typ),
     NMatchTy l5 A1 ->
     MatchTy l5 A2 B2 ->
     MatchTy l5 (t_or A1 A2) B2
 | MatchTyUnion : forall (l5:l) (A1 A2 B1 B2:typ),
     MatchTy l5 A1 B1 ->
     MatchTy l5 A2 B2 ->
     MatchTy l5 (t_or A1 A2) (t_or B1 B2)
 | MatchTyIntersection : forall (l5:l) (A1 A2 B1 B2:typ),
     MatchTy l5 A1 B1 ->
     MatchTy l5 A2 B2 ->
     MatchTy l5 (t_and A1 A2) (t_and B1 B2)
with NMatchTy : l -> typ -> Prop :=    (* defn NMatchTy *)
 | NMatchTyEmpty : forall (l5:l),
     NMatchTy l5 t_bot
 | NMatchTyVar : forall (l5:l) (X:typevar),
     NMatchTy l5 (t_tvar_f X)
 | NMatchTyFun : forall (l5:l) (A B:typ),
     lc_typ A ->
     lc_typ B ->
     NMatchTy l5 (t_arrow A B)
 | NMatchTyAll : forall (l5:l) (B:typ),
     lc_typ (t_forall B) ->
     NMatchTy l5 (t_forall B)
 | NMatchTyIn : forall (l1 l2:l) (A:typ),
     lc_typ A ->
      l1  <>  l2  ->
     NMatchTy l1 (t_rcd l2 A)
 | NMatchTyUnion : forall (l5:l) (A1 A2:typ),
     NMatchTy l5 A1 ->
     NMatchTy l5 A2 ->
     NMatchTy l5 (t_or A1 A2)
 | NMatchTyIntersectionL : forall (l5:l) (A1 A2:typ),
     lc_typ A2 ->
     NMatchTy l5 A1 ->
     NMatchTy l5 (t_and A1 A2)
 | NMatchTyIntersectionR : forall (l5:l) (A1 A2:typ),
     lc_typ A1 ->
     NMatchTy l5 A2 ->
     NMatchTy l5 (t_and A1 A2).

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
 | ASub_refl : forall (A:typ),
     lc_typ A ->
     algo_sub A A
 | ASub_top : forall (A:typ),
     lc_typ A ->
     algo_sub A t_top
 | ASub_bot : forall (A:typ),
     lc_typ A ->
     algo_sub t_bot A
 | ASub_arrow : forall (A1 A2 B1 B2:typ),
     algo_sub B1 A1 ->
     algo_sub A2 B2 ->
     algo_sub (t_arrow A1 A2) (t_arrow B1 B2)
 | ASub_forall : forall (L:vars) (A B:typ),
      ( forall X , X \notin  L  -> algo_sub  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     algo_sub (t_forall A) (t_forall B)
 | ASub_rcd : forall (l5:l) (A B:typ),
     algo_sub A B ->
     algo_sub (t_rcd l5 A) (t_rcd l5 B)
 | ASub_and : forall (A B B1 B2:typ),
     spli B B1 B2 ->
     algo_sub A B1 ->
     algo_sub A B2 ->
     algo_sub A B
 | ASub_andl : forall (A B A1 A2:typ),
     spli A A1 A2 ->
     algo_sub A1 B ->
     algo_sub A B
 | ASub_andr : forall (A B A1 A2:typ),
     spli A A1 A2 ->
     algo_sub A2 B ->
     algo_sub A B
 | ASub_or : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     algo_sub A1 B ->
     algo_sub A2 B ->
     algo_sub A B
 | ASub_orl : forall (A B B1 B2:typ),
     splu B B1 B2 ->
     algo_sub A B1 ->
     algo_sub A B
 | ASub_orr : forall (A B B1 B2:typ),
     splu B B1 B2 ->
     algo_sub A B2 ->
     algo_sub A B.

(* defns OrduFty *)
Inductive UnionOrdinaryFty : Fty -> Prop :=    (* defn UnionOrdinaryFty *)
 | OrdUArg : forall (A:typ),
     ordu A ->
     UnionOrdinaryFty (fty_StackArg A)
 | OrdUTypeArg : forall (A:typ),
     lc_typ A ->
     UnionOrdinaryFty (fty_StackTyArg A).

(* defns Appty *)
Inductive ApplyTy : typ -> Fty -> typ -> Prop :=    (* defn ApplyTy *)
 | ApplyTyEmpty : forall (Fty5:Fty),
     UnionOrdinaryFty Fty5 ->
     ApplyTy t_bot Fty5 t_bot
 | ApplyFunTy : forall (A B:typ),
     lc_typ (t_forall A) ->
     lc_typ B ->
     ApplyTy (t_forall A) (fty_StackTyArg B)  (open_typ_wrt_typ  A B ) 
 | ApplyTyFun : forall (A A' B:typ),
     lc_typ A' ->
     UnionOrdinaryFty (fty_StackArg B) ->
     declarative_subtyping B A ->
     ApplyTy (t_arrow A A') (fty_StackArg B) A'
 | ApplyTyUnion : forall (A1 A2:typ) (Fty5:Fty) (A1' A2':typ),
     UnionOrdinaryFty Fty5 ->
     ApplyTy A1 Fty5 A1' ->
     ApplyTy A2 Fty5 A2' ->
     ApplyTy (t_or A1 A2) Fty5 (t_or A1' A2')
 | ApplyTyUnionArg : forall (A B B1' B2' B1 B2:typ),
     splu B B1 B2 ->
     ApplyTy A (fty_StackArg B1) B1' ->
     ApplyTy A (fty_StackArg B2) B2' ->
     ApplyTy A (fty_StackArg B) (t_or B1' B2')
 | ApplyTyInterL : forall (A1 A2:typ) (Fty5:Fty) (A1':typ),
     UnionOrdinaryFty Fty5 ->
     ApplyTy A1 Fty5 A1' ->
     NApplyTy A2 Fty5 ->
     ApplyTy (t_and A1 A2) Fty5 A1'
 | ApplyTyInterR : forall (A1 A2:typ) (Fty5:Fty) (A2':typ),
     UnionOrdinaryFty Fty5 ->
     NApplyTy A1 Fty5 ->
     ApplyTy A2 Fty5 A2' ->
     ApplyTy (t_and A1 A2) Fty5 A2'
 | ApplyTyInterBoth : forall (A1 A2:typ) (Fty5:Fty) (A1' A2':typ),
     UnionOrdinaryFty Fty5 ->
     ApplyTy A1 Fty5 A1' ->
     ApplyTy A2 Fty5 A2' ->
     ApplyTy (t_and A1 A2) Fty5 (t_and A1' A2')
with NApplyTy : typ -> Fty -> Prop :=    (* defn NApplyTy *)
 | NApplyTyTop : forall (Fty5:Fty),
     lc_Fty Fty5 ->
     NApplyTy t_top Fty5
 | NApplyTyVar : forall (X:typevar) (Fty5:Fty),
     lc_Fty Fty5 ->
     NApplyTy (t_tvar_f X) Fty5
 | NApplyTyIn : forall (l5:l) (A:typ) (Fty5:Fty),
     lc_typ A ->
     lc_Fty Fty5 ->
     NApplyTy (t_rcd l5 A) Fty5
 | NApplyTyAll : forall (A B:typ),
     lc_typ (t_forall A) ->
     lc_typ B ->
     NApplyTy (t_forall A) (fty_StackArg B)
 | NApplyTyFun : forall (A A' B:typ),
     lc_typ A' ->
      lc_typ  A  ->
     UnionOrdinaryFty (fty_StackArg B) ->
      not (  declarative_subtyping B A  )  ->
     NApplyTy (t_arrow A A') (fty_StackArg B)
 | NApplyTyFunFty : forall (A A' B:typ),
     lc_typ A ->
     lc_typ A' ->
     lc_typ B ->
     NApplyTy (t_arrow A A') (fty_StackTyArg B)
 | NApplyTyUnionL : forall (A1 A2:typ) (Fty5:Fty),
     lc_typ A2 ->
     UnionOrdinaryFty Fty5 ->
     NApplyTy A1 Fty5 ->
     NApplyTy (t_or A1 A2) Fty5
 | NApplyTyUnionR : forall (A1 A2:typ) (Fty5:Fty),
     lc_typ A1 ->
     UnionOrdinaryFty Fty5 ->
     NApplyTy A2 Fty5 ->
     NApplyTy (t_or A1 A2) Fty5
 | NApplyTyUnionArgL : forall (A B B1 B2:typ),
     splu B B1 B2 ->
     NApplyTy A (fty_StackArg B1) ->
     NApplyTy A (fty_StackArg B)
 | NApplyTyUnionArgR : forall (A B B1 B2:typ),
     splu B B1 B2 ->
     NApplyTy A (fty_StackArg B2) ->
     NApplyTy A (fty_StackArg B)
 | NApplyTyInter : forall (A1 A2:typ) (Fty5:Fty),
     UnionOrdinaryFty Fty5 ->
     NApplyTy A1 Fty5 ->
     NApplyTy A2 Fty5 ->
     NApplyTy (t_and A1 A2) Fty5.

(* defns NewSplit *)
Inductive new_spli : typ -> typ -> typ -> Prop :=    (* defn new_spli *)
 | NSpI_and : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     new_spli (t_and A B) A B
 | NSpI_orl : forall (A B A1 A2:typ),
     lc_typ B ->
     new_spli A A1 A2 ->
     new_spli (t_or A B) (t_or A1 B) (t_or A2 B)
 | NSpI_orr : forall (A B B1 B2:typ),
     lc_typ A ->
     new_spli B B1 B2 ->
     new_spli (t_or A B) (t_or A B1) (t_or A B2)
 | NSpI_arrow : forall (A B B1 B2:typ),
     lc_typ A ->
     new_spli B B1 B2 ->
     new_spli (t_arrow A B) (t_arrow A B1) (t_arrow A B2)
 | NSpI_arrowUnion : forall (A B A1 A2:typ),
     lc_typ B ->
     new_splu A A1 A2 ->
     new_spli (t_arrow A B) (t_arrow A1 B) (t_arrow A2 B)
 | NSpI_forall : forall (L:vars) (A A1 A2:typ),
      ( forall X , X \notin  L  -> new_spli  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ A1 (t_tvar_f X) )   ( open_typ_wrt_typ A2 (t_tvar_f X) )  )  ->
     new_spli (t_forall A) (t_forall A1) (t_forall A2)
 | NSpI_in : forall (l5:l) (A A1 A2:typ),
     new_spli A A1 A2 ->
     new_spli (t_rcd l5 A) (t_rcd l5 A1) (t_rcd l5 A2)
with new_splu : typ -> typ -> typ -> Prop :=    (* defn new_splu *)
 | NSpU_or : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     new_splu (t_or A B) A B
 | NSpU_andl : forall (A B A1 A2:typ),
     lc_typ B ->
     new_splu A A1 A2 ->
     new_splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | NSpU_andr : forall (A B B1 B2:typ),
     lc_typ A ->
     new_splu B B1 B2 ->
     new_splu (t_and A B) (t_and A B1) (t_and A B2)
 | NSpU_forall : forall (L:vars) (A A1 A2:typ),
      ( forall X , X \notin  L  -> new_splu  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ A1 (t_tvar_f X) )   ( open_typ_wrt_typ A2 (t_tvar_f X) )  )  ->
     new_splu (t_forall A) (t_forall A1) (t_forall A2)
 | NSpU_in : forall (l5:l) (A A1 A2:typ),
     new_splu A A1 A2 ->
     new_splu (t_rcd l5 A) (t_rcd l5 A1) (t_rcd l5 A2).

(* defns NewAlgorithmicSubtyping *)
Inductive new_sub : typ -> typ -> Prop :=    (* defn new_sub *)
 | NSub_refl : forall (A:typ),
     lc_typ A ->
     new_sub A A
 | NSub_top : forall (A:typ),
     lc_typ A ->
     new_sub A t_top
 | NSub_bot : forall (A:typ),
     lc_typ A ->
     new_sub t_bot A
 | NSub_arrow : forall (A1 A2 B1 B2:typ),
     new_sub B1 A1 ->
     new_sub A2 B2 ->
     new_sub (t_arrow A1 A2) (t_arrow B1 B2)
 | NSub_forall : forall (L:vars) (A B:typ),
      ( forall X , X \notin  L  -> new_sub  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     new_sub (t_forall A) (t_forall B)
 | NSub_rcd : forall (l5:l) (A B:typ),
     new_sub A B ->
     new_sub (t_rcd l5 A) (t_rcd l5 B)
 | NSub_and : forall (A B B1 B2:typ),
     new_spli B B1 B2 ->
     new_sub A B1 ->
     new_sub A B2 ->
     new_sub A B
 | NSub_andl : forall (A B A1 A2:typ),
     new_spli A A1 A2 ->
     new_sub A1 B ->
     new_sub A B
 | NSub_andr : forall (A B A1 A2:typ),
     new_spli A A1 A2 ->
     new_sub A2 B ->
     new_sub A B
 | NSub_or : forall (A B A1 A2:typ),
     new_splu A A1 A2 ->
     new_sub A1 B ->
     new_sub A2 B ->
     new_sub A B
 | NSub_orl : forall (A B B1 B2:typ),
     new_splu B B1 B2 ->
     new_sub A B1 ->
     new_sub A B
 | NSub_orr : forall (A B B1 B2:typ),
     new_splu B B1 B2 ->
     new_sub A B2 ->
     new_sub A B.

(* defns NotDistinguishableTypes *)
Inductive NotDistinguishableTypes : typ -> Prop :=    (* defn NotDistinguishableTypes *)
 | NDArr : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     NotDistinguishableTypes (t_arrow A B)
 | NDAll : forall (A:typ),
     lc_typ (t_forall A) ->
     NotDistinguishableTypes (t_forall A)
 | NDTop : 
     NotDistinguishableTypes t_top
 | NDVar : forall (X:typevar),
     NotDistinguishableTypes (t_tvar_f X).

(* defns NotDistinguishable *)
Inductive NotDistinguishable : typ -> typ -> Prop :=    (* defn NotDistinguishable *)
 | NDistIn : forall (l5:l) (A B:typ),
     NotDistinguishable A B ->
     NotDistinguishable (t_rcd l5 A) (t_rcd l5 B)
 | NDistAxIn : forall (A:typ) (l5:l) (B:typ),
     lc_typ B ->
     NotDistinguishableTypes A ->
     NotDistinguishable A (t_rcd l5 B)
 | NDistInAx : forall (l5:l) (B A:typ),
     lc_typ B ->
     NotDistinguishableTypes A ->
     NotDistinguishable (t_rcd l5 B) A
 | NDistAxAx : forall (A B:typ),
     NotDistinguishableTypes A ->
     NotDistinguishableTypes B ->
     NotDistinguishable A B
 | NDistUnionL : forall (A A' B:typ),
     lc_typ A' ->
     NotDistinguishable A B ->
     NotDistinguishable (t_or A A') B
 | NDistUnionR : forall (A A' B:typ),
     lc_typ A ->
     NotDistinguishable A' B ->
     NotDistinguishable (t_or A A') B
 | NDistUnionLSymm : forall (B A A':typ),
     lc_typ A' ->
     NotDistinguishable B A ->
     NotDistinguishable B (t_or A A')
 | NDistUnionRSymm : forall (B A A':typ),
     lc_typ A ->
     NotDistinguishable B A' ->
     NotDistinguishable B (t_or A A')
 | NDistInter : forall (A A' B:typ),
     NotDistinguishable A B ->
     NotDistinguishable A' B ->
     NotDistinguishable (t_and A A') B
 | NDistInterSymm : forall (B A A':typ),
     NotDistinguishable B A ->
     NotDistinguishable B A' ->
     NotDistinguishable B (t_and A A').

(* defns DistinguishabilityAx *)
Inductive DistinguishabilityAx : typ -> typ -> Prop :=    (* defn DistinguishabilityAx *)
 | DistAxIn : forall (l1:l) (A:typ) (l2:l) (B:typ),
     lc_typ A ->
     lc_typ B ->
      l1  <>  l2  ->
     DistinguishabilityAx (t_rcd l1 A) (t_rcd l2 B)
 | DistAxEmptyL : forall (B:typ),
     lc_typ B ->
     DistinguishabilityAx t_bot B
 | DistAxEmptyR : forall (A:typ),
     lc_typ A ->
     DistinguishabilityAx A t_bot.

(* defns Distinguishability *)
Inductive Distinguishability : typ -> typ -> Prop :=    (* defn Distinguishability *)
 | DistAx : forall (A B:typ),
     DistinguishabilityAx A B ->
     Distinguishability A B
 | DistIn : forall (l5:l) (A B:typ),
     Distinguishability A B ->
     Distinguishability (t_rcd l5 A) (t_rcd l5 B)
 | DistUnion : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     Distinguishability A1 B ->
     Distinguishability A2 B ->
     Distinguishability A B
 | DistUnionSym : forall (B A A1 A2:typ),
     splu A A1 A2 ->
     Distinguishability B A1 ->
     Distinguishability B A2 ->
     Distinguishability B A
 | DistIntersectL : forall (A A' B:typ),
     lc_typ A' ->
     Distinguishability A B ->
     Distinguishability (t_and A A') B
 | DistIntersectR : forall (A A' B:typ),
     lc_typ A ->
     Distinguishability A' B ->
     Distinguishability (t_and A A') B
 | DistIntersectLSym : forall (B A A':typ),
     lc_typ A' ->
     Distinguishability B A ->
     Distinguishability B (t_and A A')
 | DistIntersectRSym : forall (B A A':typ),
     lc_typ A ->
     Distinguishability B A' ->
     Distinguishability B (t_and A A').

(* defns DistinguishabilityAlt *)
Inductive DistinguishabilityAlt : typ -> typ -> Prop :=    (* defn DistinguishabilityAlt *)
 | DA_DistAx : forall (A B:typ),
     DistinguishabilityAx A B ->
     DistinguishabilityAlt A B
 | DA_DistIn : forall (l5:l) (A B:typ),
     DistinguishabilityAlt A B ->
     DistinguishabilityAlt (t_rcd l5 A) (t_rcd l5 B)
 | DA_DistUnion : forall (A1 A2 B:typ),
     DistinguishabilityAlt A1 B ->
     DistinguishabilityAlt A2 B ->
     DistinguishabilityAlt (t_or A1 A2) B
 | DA_DistUnionSym : forall (B A1 A2:typ),
     DistinguishabilityAlt B A1 ->
     DistinguishabilityAlt B A2 ->
     DistinguishabilityAlt B (t_or A1 A2)
 | DA_DistIntersectL : forall (A A' B:typ),
     lc_typ A' ->
     DistinguishabilityAlt A B ->
     DistinguishabilityAlt (t_and A A') B
 | DA_DistIntersectR : forall (A A' B:typ),
     lc_typ A ->
     DistinguishabilityAlt A' B ->
     DistinguishabilityAlt (t_and A A') B
 | DA_DistIntersectLSym : forall (B A A':typ),
     lc_typ A' ->
     DistinguishabilityAlt B A ->
     DistinguishabilityAlt B (t_and A A')
 | DA_DistIntersectRSym : forall (B A A':typ),
     lc_typ A ->
     DistinguishabilityAlt B A' ->
     DistinguishabilityAlt B (t_and A A')
 | DA_DistMono : forall (A2 B A1:typ),
     DistinguishabilityAlt A1 B ->
     declarative_subtyping A2 A1 ->
     DistinguishabilityAlt A2 B
 | DA_DistMonoSym : forall (B A2 A1:typ),
     DistinguishabilityAlt B A1 ->
     declarative_subtyping A2 A1 ->
     DistinguishabilityAlt B A2.

(* defns MergeabilityAx *)
Inductive MergeabilityAx : typ -> typ -> Prop :=    (* defn MergeabilityAx *)
 | MergeAxTopL : forall (B:typ),
     lc_typ B ->
     MergeabilityAx t_top B
 | MergeAxFunTyp : forall (A A' B:typ),
     lc_typ A ->
     lc_typ A' ->
     lc_typ (t_forall B) ->
     MergeabilityAx (t_arrow A A') (t_forall B).

(* defns Mergeability *)
Inductive Mergeability : typ -> typ -> Prop :=    (* defn Mergeability *)
 | MergeFunL : forall (A A' B B':typ),
     lc_typ A' ->
     lc_typ B' ->
     Distinguishability A B ->
     Mergeability (t_arrow A A') (t_arrow B B')
 | MergeFunR : forall (A B B':typ),
     lc_typ A ->
     Mergeability B B' ->
     Mergeability (t_arrow A B) (t_arrow A B')
 | MergeForall : forall (L:vars) (A B:typ),
      ( forall X , X \notin  L  -> Mergeability  ( open_typ_wrt_typ A (t_tvar_f X) )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     Mergeability (t_forall A) (t_forall B)
 | MergeIntersect : forall (A A' B:typ),
     Mergeability A B ->
     Mergeability A' B ->
     Mergeability (t_and A A') B
 | MergeIntersectSym : forall (B A A':typ),
     Mergeability B A ->
     Mergeability B A' ->
     Mergeability B (t_and A A')
 | MergeUnion : forall (A A' B:typ),
     Mergeability A B ->
     Mergeability A' B ->
     Mergeability (t_or A A') B
 | MergeUnionSym : forall (B A A':typ),
     Mergeability B A ->
     Mergeability B A' ->
     Mergeability B (t_or A A')
 | MergeAx : forall (A B:typ),
     MergeabilityAx A B ->
     Mergeability A B
 | MergeAxSym : forall (A B:typ),
     MergeabilityAx B A ->
     Mergeability A B.

(* defns TypeWellformedness *)
Inductive TypeWF : tctx -> typ -> Prop :=    (* defn TypeWF *)
 | TyWfVar : forall (D:tctx) (X:typevar),
      binds  X t_top D  ->
     TypeWF D (t_tvar_f X)
 | TyWfIn : forall (D:tctx) (l5:l) (A:typ),
     TypeWF D A ->
     TypeWF D (t_rcd l5 A)
 | TyWfInter : forall (D:tctx) (A1 A2:typ),
     TypeWF D A1 ->
     TypeWF D A2 ->
     Mergeability A1 A2 ->
     TypeWF D (t_and A1 A2)
 | TyWfUnion : forall (D:tctx) (A1 A2:typ),
     TypeWF D A1 ->
     TypeWF D A2 ->
     Distinguishability A1 A2 ->
     TypeWF D (t_or A1 A2)
 | TyWfFun : forall (D:tctx) (A B:typ),
     TypeWF D A ->
     TypeWF D B ->
     TypeWF D (t_arrow A B)
 | TyWfTyFun : forall (L:vars) (D:tctx) (B:typ),
      ( forall X , X \notin  L  -> TypeWF  (cons ( X ,t_top)  D )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     TypeWF D (t_forall B)
 | TyWfTop : forall (D:tctx),
     TypeWF D t_top
 | TyWfEmpty : forall (D:tctx),
     TypeWF D t_bot.

(* defns Similarity *)
Inductive sim : typ -> typ -> Prop :=    (* defn sim *)
 | Sim_NegL : forall (A B:typ),
     lc_typ B ->
     isNegTyp A ->
     sim A B
 | Sim_NegR : forall (A B:typ),
     lc_typ A ->
     isNegTyp B ->
     sim A B
 | Sim_In : forall (l5:l) (V1 V2:typ),
     sim V1 V2 ->
     sim (t_rcd l5 V1) (t_rcd l5 V2).


(** infrastructure *)
Hint Constructors declarative_subtyping isNegTyp isValTyp isValFty PositiveSubtyping NegativeSubtyping MatchTy NMatchTy ordu ordi spli splu algo_sub UnionOrdinaryFty ApplyTy NApplyTy new_spli new_splu new_sub NotDistinguishableTypes NotDistinguishable DistinguishabilityAx Distinguishability DistinguishabilityAlt MergeabilityAx Mergeability TypeWF sim lc_typ lc_Fty : core.


