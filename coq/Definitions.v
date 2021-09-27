(* generated by Ott 0.31, locally-nameless lngen from: ../spec/rules.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition typevar : Set := var.
Definition I : Set := nat.

Inductive l : Set := 
 | lbl_TagIndex (i:I)
 | lbl_TagLeft : l
 | lbl_TagRight : l.

Inductive A : Set :=  (*r value type *)
 | t_tvar_b (_:nat)
 | t_tvar_f (X:typevar)
 | t_rcd (l5:l) (A5:A)
 | t_and (A1:A) (A2:A)
 | t_or (A1:A) (A2:A)
 | t_arrow (A5:A) (B:A)
 | t_forall (B:A)
 | t_top : A
 | t_bot : A.

Inductive Tcov : Set :=  (*r covariant type context *)
 | ty_ctx_covTcovIn (l5:l)
 | ty_ctx_covTcovArr (A5:A)
 | ty_ctx_covTcovAll : Tcov
 | ty_ctx_covTCovInterL (A5:A)
 | ty_ctx_covTCovInterR (A5:A)
 | ty_ctx_covTCovUnionL (A5:A)
 | ty_ctx_covTCovUnionR (A5:A).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_A_wrt_A_rec (k:nat) (B5:A) (B_6:A) {struct B_6}: A :=
  match B_6 with
  | (t_tvar_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_tvar_b nat
        | inleft (right _) => B5
        | inright _ => t_tvar_b (nat - 1)
      end
  | (t_tvar_f X) => t_tvar_f X
  | (t_rcd l5 A5) => t_rcd l5 (open_A_wrt_A_rec k B5 A5)
  | (t_and A1 A2) => t_and (open_A_wrt_A_rec k B5 A1) (open_A_wrt_A_rec k B5 A2)
  | (t_or A1 A2) => t_or (open_A_wrt_A_rec k B5 A1) (open_A_wrt_A_rec k B5 A2)
  | (t_arrow A5 B) => t_arrow (open_A_wrt_A_rec k B5 A5) (open_A_wrt_A_rec k B5 B)
  | (t_forall B) => t_forall (open_A_wrt_A_rec (S k) B5 B)
  | t_top => t_top 
  | t_bot => t_bot 
end.

Definition open_Tcov_wrt_A_rec (k:nat) (B5:A) (Tcov5:Tcov) : Tcov :=
  match Tcov5 with
  | (ty_ctx_covTcovIn l5) => ty_ctx_covTcovIn l5
  | (ty_ctx_covTcovArr A5) => ty_ctx_covTcovArr (open_A_wrt_A_rec k B5 A5)
  | ty_ctx_covTcovAll => ty_ctx_covTcovAll 
  | (ty_ctx_covTCovInterL A5) => ty_ctx_covTCovInterL (open_A_wrt_A_rec k B5 A5)
  | (ty_ctx_covTCovInterR A5) => ty_ctx_covTCovInterR (open_A_wrt_A_rec k B5 A5)
  | (ty_ctx_covTCovUnionL A5) => ty_ctx_covTCovUnionL (open_A_wrt_A_rec k B5 A5)
  | (ty_ctx_covTCovUnionR A5) => ty_ctx_covTCovUnionR (open_A_wrt_A_rec k B5 A5)
end.

Definition open_Tcov_wrt_A B5 Tcov5 := open_Tcov_wrt_A_rec 0 Tcov5 B5.

Definition open_A_wrt_A B5 B_6 := open_A_wrt_A_rec 0 B_6 B5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_A *)
Inductive lc_A : A -> Prop :=    (* defn lc_A *)
 | lc_t_tvar_f : forall (X:typevar),
     (lc_A (t_tvar_f X))
 | lc_t_rcd : forall (l5:l) (A5:A),
     (lc_A A5) ->
     (lc_A (t_rcd l5 A5))
 | lc_t_and : forall (A1 A2:A),
     (lc_A A1) ->
     (lc_A A2) ->
     (lc_A (t_and A1 A2))
 | lc_t_or : forall (A1 A2:A),
     (lc_A A1) ->
     (lc_A A2) ->
     (lc_A (t_or A1 A2))
 | lc_t_arrow : forall (A5 B:A),
     (lc_A A5) ->
     (lc_A B) ->
     (lc_A (t_arrow A5 B))
 | lc_t_forall : forall (B:A),
      ( forall X , lc_A  ( open_A_wrt_A B (t_tvar_f X) )  )  ->
     (lc_A (t_forall B))
 | lc_t_top : 
     (lc_A t_top)
 | lc_t_bot : 
     (lc_A t_bot).

(* defns LC_Tcov *)
Inductive lc_Tcov : Tcov -> Prop :=    (* defn lc_Tcov *)
 | lc_ty_ctx_covTcovIn : forall (l5:l),
     (lc_Tcov (ty_ctx_covTcovIn l5))
 | lc_ty_ctx_covTcovArr : forall (A5:A),
     (lc_A A5) ->
     (lc_Tcov (ty_ctx_covTcovArr A5))
 | lc_ty_ctx_covTcovAll : 
     (lc_Tcov ty_ctx_covTcovAll)
 | lc_ty_ctx_covTCovInterL : forall (A5:A),
     (lc_A A5) ->
     (lc_Tcov (ty_ctx_covTCovInterL A5))
 | lc_ty_ctx_covTCovInterR : forall (A5:A),
     (lc_A A5) ->
     (lc_Tcov (ty_ctx_covTCovInterR A5))
 | lc_ty_ctx_covTCovUnionL : forall (A5:A),
     (lc_A A5) ->
     (lc_Tcov (ty_ctx_covTCovUnionL A5))
 | lc_ty_ctx_covTCovUnionR : forall (A5:A),
     (lc_A A5) ->
     (lc_Tcov (ty_ctx_covTCovUnionR A5)).
(** free variables *)
Fixpoint typefv_A (B5:A) : vars :=
  match B5 with
  | (t_tvar_b nat) => {}
  | (t_tvar_f X) => {{X}}
  | (t_rcd l5 A5) => (typefv_A A5)
  | (t_and A1 A2) => (typefv_A A1) \u (typefv_A A2)
  | (t_or A1 A2) => (typefv_A A1) \u (typefv_A A2)
  | (t_arrow A5 B) => (typefv_A A5) \u (typefv_A B)
  | (t_forall B) => (typefv_A B)
  | t_top => {}
  | t_bot => {}
end.

Definition typefv_Tcov (Tcov5:Tcov) : vars :=
  match Tcov5 with
  | (ty_ctx_covTcovIn l5) => {}
  | (ty_ctx_covTcovArr A5) => (typefv_A A5)
  | ty_ctx_covTcovAll => {}
  | (ty_ctx_covTCovInterL A5) => (typefv_A A5)
  | (ty_ctx_covTCovInterR A5) => (typefv_A A5)
  | (ty_ctx_covTCovUnionL A5) => (typefv_A A5)
  | (ty_ctx_covTCovUnionR A5) => (typefv_A A5)
end.

(** substitutions *)
Fixpoint typsubst_A (B5:A) (X5:typevar) (B_6:A) {struct B_6} : A :=
  match B_6 with
  | (t_tvar_b nat) => t_tvar_b nat
  | (t_tvar_f X) => (if eq_var X X5 then B5 else (t_tvar_f X))
  | (t_rcd l5 A5) => t_rcd l5 (typsubst_A B5 X5 A5)
  | (t_and A1 A2) => t_and (typsubst_A B5 X5 A1) (typsubst_A B5 X5 A2)
  | (t_or A1 A2) => t_or (typsubst_A B5 X5 A1) (typsubst_A B5 X5 A2)
  | (t_arrow A5 B) => t_arrow (typsubst_A B5 X5 A5) (typsubst_A B5 X5 B)
  | (t_forall B) => t_forall (typsubst_A B5 X5 B)
  | t_top => t_top 
  | t_bot => t_bot 
end.

Definition typsubst_Tcov (B5:A) (X5:typevar) (Tcov5:Tcov) : Tcov :=
  match Tcov5 with
  | (ty_ctx_covTcovIn l5) => ty_ctx_covTcovIn l5
  | (ty_ctx_covTcovArr A5) => ty_ctx_covTcovArr (typsubst_A B5 X5 A5)
  | ty_ctx_covTcovAll => ty_ctx_covTcovAll 
  | (ty_ctx_covTCovInterL A5) => ty_ctx_covTCovInterL (typsubst_A B5 X5 A5)
  | (ty_ctx_covTCovInterR A5) => ty_ctx_covTCovInterR (typsubst_A B5 X5 A5)
  | (ty_ctx_covTCovUnionL A5) => ty_ctx_covTCovUnionL (typsubst_A B5 X5 A5)
  | (ty_ctx_covTCovUnionR A5) => ty_ctx_covTCovUnionR (typsubst_A B5 X5 A5)
end.

(** context application *)
Definition appctx_Tcov (Tcov5:Tcov) (A_6:A) : A :=
  match Tcov5 with
  | (ty_ctx_covTcovIn l5) => (t_rcd l5 A_6)
  | (ty_ctx_covTcovArr A5) => (t_arrow A5 A_6)
  | (ty_ctx_covTcovAll) => (t_forall A_6)
  | (ty_ctx_covTCovInterL A5) => (t_and A_6 A5)
  | (ty_ctx_covTCovInterR A5) => (t_and A5 A_6)
  | (ty_ctx_covTCovUnionL A5) => (t_or A_6 A5)
  | (ty_ctx_covTCovUnionR A5) => (t_or A5 A_6)
end.


(** definitions *)

(* defns DSub *)
Inductive DeclarativeSubtyping : A -> A -> Prop :=    (* defn DeclarativeSubtyping *)
 | DSub_Refl : forall (A5:A),
     lc_A A5 ->
     DeclarativeSubtyping A5 A5
 | DSub_Trans : forall (A1 A3 A2:A),
     DeclarativeSubtyping A1 A2 ->
     DeclarativeSubtyping A2 A3 ->
     DeclarativeSubtyping A1 A3
 | DSub_CovIn : forall (l5:l) (A5 B:A),
     DeclarativeSubtyping A5 B ->
     DeclarativeSubtyping (t_rcd l5 A5) (t_rcd l5 B)
 | DSub_CovArr : forall (C A5 B:A),
     lc_A C ->
     DeclarativeSubtyping A5 B ->
     DeclarativeSubtyping (t_arrow C A5) (t_arrow C B)
 | DSub_CovAll : forall (L:vars) (A5 B:A),
      ( forall X , X \notin  L  -> DeclarativeSubtyping  ( open_A_wrt_A A5 (t_tvar_f X) )   ( open_A_wrt_A B (t_tvar_f X) )  )  ->
     DeclarativeSubtyping (t_forall A5) (t_forall B)
 | DSub_CovInterL : forall (A5 C B:A),
     lc_A C ->
     DeclarativeSubtyping A5 B ->
     DeclarativeSubtyping (t_and A5 C) (t_and B C)
 | DSub_CovInterR : forall (C A5 B:A),
     lc_A C ->
     DeclarativeSubtyping A5 B ->
     DeclarativeSubtyping (t_and C A5) (t_and C B)
 | DSub_CovUnionL : forall (A5 C B:A),
     lc_A C ->
     DeclarativeSubtyping A5 B ->
     DeclarativeSubtyping (t_or A5 C) (t_or B C)
 | DSub_CovUnionR : forall (C A5 B:A),
     lc_A C ->
     DeclarativeSubtyping A5 B ->
     DeclarativeSubtyping (t_or C A5) (t_or C B)
 | DSub_FunCon : forall (A1 B A2:A),
     lc_A B ->
     DeclarativeSubtyping A2 A1 ->
     DeclarativeSubtyping (t_arrow A1 B) (t_arrow A2 B)
 | DSub_CovDistIIn : forall (l5:l) (A5 B:A),
     lc_A A5 ->
     lc_A B ->
     DeclarativeSubtyping (t_and  (t_rcd l5 A5)   (t_rcd l5 B) ) (t_rcd l5  (t_and A5 B) )
 | DSub_CovDistIArr : forall (C A5 B:A),
     lc_A C ->
     lc_A A5 ->
     lc_A B ->
     DeclarativeSubtyping (t_and  (t_arrow C A5)   (t_arrow C B) )  (t_arrow C (t_and A5 B)) 
 | DSub_CovDistIUnionL : forall (A5 C B:A),
     lc_A A5 ->
     lc_A B ->
     lc_A C ->
     DeclarativeSubtyping (t_and  (t_or A5 C)   (t_or B C) ) (t_or  (t_and A5 B)  C)
 | DSub_CovDistIUnionR : forall (C A5 B:A),
     lc_A C ->
     lc_A A5 ->
     lc_A B ->
     DeclarativeSubtyping (t_and  (t_or C A5)   (t_or C B) ) (t_or C  (t_and A5 B) )
 | DSub_CovDistIAll : forall (A5 B:A),
     lc_A (t_forall A5) ->
     lc_A (t_forall B) ->
     DeclarativeSubtyping (t_and  (t_forall A5)   (t_forall B) )  (t_forall (t_and A5 B)) 
 | DSub_CovDistUIn : forall (l5:l) (A5 B:A),
     lc_A A5 ->
     lc_A B ->
     DeclarativeSubtyping (t_rcd l5  (t_or A5 B) ) (t_or  (t_rcd l5 A5)   (t_rcd l5 B) )
 | DSub_CovDistUAll : forall (A5 B:A),
     lc_A (t_forall  (t_or A5 B) ) ->
     lc_A (t_forall  (t_or A5 B) ) ->
     DeclarativeSubtyping (t_forall  (t_or A5 B) ) (t_or  (t_forall A5)   (t_forall B) )
 | DSub_CovDistUInterL : forall (A5 B C:A),
     lc_A A5 ->
     lc_A B ->
     lc_A C ->
     DeclarativeSubtyping (t_and  (t_or A5 B)  C) (t_or  (t_and A5 C)   (t_and B C) )
 | DSub_CovDistUInterR : forall (C A5 B:A),
     lc_A A5 ->
     lc_A C ->
     lc_A B ->
     DeclarativeSubtyping (t_and C  (t_or A5 B) ) (t_or  (t_and C A5)   (t_and C B) )
 | DSub_FunDistI : forall (A1 B A2:A),
     lc_A A1 ->
     lc_A A2 ->
     lc_A B ->
     DeclarativeSubtyping (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow  (t_or A1 A2)  B)
 | DSub_InterLL : forall (A1 A2 B:A),
     lc_A A2 ->
     DeclarativeSubtyping A1 B ->
     DeclarativeSubtyping (t_and A1 A2) B
 | DSub_InterLR : forall (A1 A2 B:A),
     lc_A A1 ->
     DeclarativeSubtyping A2 B ->
     DeclarativeSubtyping (t_and A1 A2) B
 | DSub_InterR : forall (A5 B1 B2:A),
     DeclarativeSubtyping A5 B1 ->
     DeclarativeSubtyping A5 B2 ->
     DeclarativeSubtyping A5 (t_and B1 B2)
 | DSub_UnionL : forall (A1 A2 B:A),
     DeclarativeSubtyping A1 B ->
     DeclarativeSubtyping A2 B ->
     DeclarativeSubtyping (t_or A1 A2) B
 | DSub_UnionRL : forall (A5 B1 B2:A),
     lc_A B2 ->
     DeclarativeSubtyping A5 B1 ->
     DeclarativeSubtyping A5 (t_or B1 B2)
 | DSub_UnionRR : forall (A5 B1 B2:A),
     lc_A B1 ->
     DeclarativeSubtyping A5 B2 ->
     DeclarativeSubtyping A5 (t_or B1 B2)
 | DSub_Empty : forall (B:A),
     lc_A B ->
     DeclarativeSubtyping t_bot B
 | DSub_Top : forall (A5:A),
     lc_A A5 ->
     DeclarativeSubtyping A5 t_top.

(* defns Ordinary *)
Inductive UnionOrdinary : A -> Prop :=    (* defn UnionOrdinary *)
 | OrdU_top : 
     UnionOrdinary t_top
 | OrdU_bot : 
     UnionOrdinary t_bot
 | OrdU_arrow : forall (A5 B:A),
     lc_A A5 ->
     lc_A B ->
     UnionOrdinary (t_arrow A5 B)
 | OrdU_and : forall (A5 B:A),
     UnionOrdinary A5 ->
     UnionOrdinary B ->
     UnionOrdinary (t_and A5 B)
 | OrdU_rcd : forall (l5:l) (A5:A),
     UnionOrdinary A5 ->
     UnionOrdinary (t_rcd l5 A5)
 | OrdU_forall : forall (L:vars) (A5:A),
      ( forall X , X \notin  L  -> UnionOrdinary  ( open_A_wrt_A A5 (t_tvar_f X) )  )  ->
     UnionOrdinary (t_forall A5)
with IntersectionOrdinary : A -> Prop :=    (* defn IntersectionOrdinary *)
 | OrdI_top : 
     IntersectionOrdinary t_top
 | OrdI_bot : 
     IntersectionOrdinary t_bot
 | OrdI_arrow : forall (A5 B:A),
     UnionOrdinary A5 ->
     IntersectionOrdinary B ->
     IntersectionOrdinary (t_arrow A5 B)
 | OrdI_or : forall (A5 B:A),
     IntersectionOrdinary A5 ->
     IntersectionOrdinary B ->
     IntersectionOrdinary (t_or A5 B)
 | OrdI_rcd : forall (l5:l) (A5:A),
     IntersectionOrdinary A5 ->
     IntersectionOrdinary (t_rcd l5 A5)
 | OrdI_forall : forall (L:vars) (A5:A),
      ( forall X , X \notin  L  -> IntersectionOrdinary  ( open_A_wrt_A A5 (t_tvar_f X) )  )  ->
     IntersectionOrdinary (t_forall A5).

(* defns Split *)
Inductive SplitIntersection : A -> A -> A -> Prop :=    (* defn SplitIntersection *)
 | SpI_and : forall (A5 B:A),
     lc_A A5 ->
     lc_A B ->
     SplitIntersection (t_and A5 B) A5 B
 | SpI_orl : forall (A_5 B A1 A2:A),
     lc_A B ->
     SplitIntersection A_5 A1 A2 ->
     SplitIntersection (t_or A_5 B) (t_or A1 B) (t_or A2 B)
 | SpI_orr : forall (A5 B B1 B2:A),
     lc_A A5 ->
     SplitIntersection B B1 B2 ->
     SplitIntersection (t_or A5 B) (t_or A5 B1) (t_or A5 B2)
 | SpI_arrow : forall (A5 B B1 B2:A),
     lc_A A5 ->
     SplitIntersection B B1 B2 ->
     SplitIntersection (t_arrow A5 B) (t_arrow A5 B1) (t_arrow A5 B2)
 | SpI_arrowUnion : forall (A_5 B A1 A2:A),
     IntersectionOrdinary B ->
     SplitUnion A_5 A1 A2 ->
     SplitIntersection (t_arrow A_5 B) (t_arrow A1 B) (t_arrow A2 B)
 | SpI_forall : forall (L:vars) (A_5 A1 A2:A),
      ( forall X , X \notin  L  -> SplitIntersection  ( open_A_wrt_A A_5 (t_tvar_f X) )   ( open_A_wrt_A A1 (t_tvar_f X) )   ( open_A_wrt_A A2 (t_tvar_f X) )  )  ->
     SplitIntersection (t_forall A_5) (t_forall A1) (t_forall A2)
 | SpI_in : forall (l5:l) (A_5 A1 A2:A),
     SplitIntersection A_5 A1 A2 ->
     SplitIntersection (t_rcd l5 A_5) (t_rcd l5 A1) (t_rcd l5 A2)
with SplitUnion : A -> A -> A -> Prop :=    (* defn SplitUnion *)
 | SpU_or : forall (A5 B:A),
     lc_A A5 ->
     lc_A B ->
     SplitUnion (t_or A5 B) A5 B
 | SpU_andl : forall (A_5 B A1 A2:A),
     lc_A B ->
     SplitUnion A_5 A1 A2 ->
     SplitUnion (t_and A_5 B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A5 B B1 B2:A),
     lc_A A5 ->
     SplitUnion B B1 B2 ->
     SplitUnion (t_and A5 B) (t_and A5 B1) (t_and A5 B2)
 | SpU_forall : forall (L:vars) (A_5 A1 A2:A),
      ( forall X , X \notin  L  -> SplitUnion  ( open_A_wrt_A A_5 (t_tvar_f X) )   ( open_A_wrt_A A1 (t_tvar_f X) )   ( open_A_wrt_A A2 (t_tvar_f X) )  )  ->
     SplitUnion (t_forall A_5) (t_forall A1) (t_forall A2)
 | SpU_in : forall (l5:l) (A_5 A1 A2:A),
     SplitUnion A_5 A1 A2 ->
     SplitUnion (t_rcd l5 A_5) (t_rcd l5 A1) (t_rcd l5 A2).

(* defns AlgorithmicSubtyping *)
Inductive algo_sub : A -> A -> Prop :=    (* defn algo_sub *)
 | ASub_var : forall (X:typevar),
     algo_sub (t_tvar_f X) (t_tvar_f X)
 | ASub_top : forall (A5:A),
     lc_A A5 ->
     algo_sub A5 t_top
 | ASub_bot : forall (A5:A),
     lc_A A5 ->
     algo_sub t_bot A5
 | ASub_arrow : forall (A1 A2 B1 B2:A),
     algo_sub B1 A1 ->
     algo_sub A2 B2 ->
     algo_sub (t_arrow A1 A2) (t_arrow B1 B2)
 | ASub_and : forall (A5 B B1 B2:A),
     SplitIntersection B B1 B2 ->
     algo_sub A5 B1 ->
     algo_sub A5 B2 ->
     algo_sub A5 B
 | ASub_andl : forall (A_5 B A1 A2:A),
     SplitIntersection A_5 A1 A2 ->
     algo_sub A1 B ->
     algo_sub A_5 B
 | ASub_andr : forall (A_5 B A1 A2:A),
     SplitIntersection A_5 A1 A2 ->
     algo_sub A2 B ->
     algo_sub A_5 B
 | ASub_or : forall (A_5 B A1 A2:A),
     SplitUnion A_5 A1 A2 ->
     algo_sub A1 B ->
     algo_sub A2 B ->
     algo_sub A_5 B
 | ASub_orl : forall (A5 B B1 B2:A),
     SplitUnion B B1 B2 ->
     algo_sub A5 B1 ->
     algo_sub A5 B
 | ASub_orr : forall (A5 B B1 B2:A),
     SplitUnion B B1 B2 ->
     algo_sub A5 B2 ->
     algo_sub A5 B.


(** infrastructure *)
Hint Constructors DeclarativeSubtyping UnionOrdinary IntersectionOrdinary SplitIntersection SplitUnion algo_sub lc_A lc_Tcov : core.


