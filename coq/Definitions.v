(* generated by Ott 0.31 from: ../spec/rules.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.



Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top type *)
 | t_bot : typ (*r bottom type *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_and (A:typ) (B:typ) (*r intersection *)
 | t_or (A:typ) (B:typ) (*r union *).

Inductive mode : Set := 
 | m_sub : mode
 | m_super : mode.
(** definitions *)

(* defns DSub *)
Inductive declarative_subtyping : typ -> typ -> Prop :=    (* defn declarative_subtyping *)
 | DS_refl : forall (A:typ),
     declarative_subtyping A A
 | DS_trans : forall (A C B:typ),
     declarative_subtyping A B ->
     declarative_subtyping B C ->
     declarative_subtyping A C
 | DS_top : forall (A:typ),
     declarative_subtyping A t_top
 | DS_bot : forall (A:typ),
     declarative_subtyping t_bot A
 | DS_arrow : forall (A C B D:typ),
     declarative_subtyping B A ->
     declarative_subtyping C D ->
     declarative_subtyping (t_arrow A C) (t_arrow B D)
 | DS_and : forall (A B C:typ),
     declarative_subtyping A B ->
     declarative_subtyping A C ->
     declarative_subtyping A (t_and B C)
 | DS_andl : forall (A B:typ),
     declarative_subtyping (t_and A B) A
 | DS_andr : forall (A B:typ),
     declarative_subtyping (t_and A B) B
 | DS_or : forall (A B C:typ),
     declarative_subtyping A C ->
     declarative_subtyping B C ->
     declarative_subtyping (t_or A B) C
 | DS_orl : forall (A B:typ),
     declarative_subtyping A (t_or A B)
 | DS_orr : forall (B A:typ),
     declarative_subtyping B (t_or A B)
 | DS_distOr : forall (A1 B A2:typ),
     declarative_subtyping (t_and  (t_or A1 B)   (t_or A2 B) ) (t_or  (t_and A1 A2)  B)
 | DS_distAnd : forall (A1 A2 B:typ),
     declarative_subtyping (t_and  (t_or A1 A2)  B) (t_or  (t_and A1 B)   (t_and A2 B) )
 | DS_distArrRI : forall (A B1 B2:typ),
     declarative_subtyping (t_and  (t_arrow A B1)   (t_arrow A B2) ) (t_arrow A (t_and B1 B2))
 | DS_distArrRU : forall (A1 B A2:typ),
     declarative_subtyping (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow (t_or A1 A2) B)
 | DS_distArrLI : forall (A1 A2 B:typ),
     declarative_subtyping (t_arrow  (t_and A1 A2)  B) (t_or  (t_arrow A1 B)   (t_arrow A2 B) )
 | DS_distArrLU : forall (A B1 B2:typ),
     declarative_subtyping (t_arrow A  (t_or B1 B2) ) (t_or  (t_arrow A B1)   (t_arrow A B2) ).
(** definitions *)

(* defns Ordinary *)
Inductive ordi : typ -> Prop :=    (* defn ordi *)
 | OI_top : 
     ordi t_top
 | OI_bot : 
     ordi t_bot
 | OI_int : 
     ordi t_int
 | OI_arrow : forall (A B:typ),
     ordu A ->
     ordi B ->
     ordi (t_arrow A B)
 | OI_or : forall (A B:typ),
     ordi A ->
     ordi B ->
     ordi (t_or A B)
with ordu : typ -> Prop :=    (* defn ordu *)
 | OU_top : 
     ordu t_top
 | OU_bot : 
     ordu t_bot
 | OU_int : 
     ordu t_int
 | OU_arrow : forall (A B:typ),
     ordi A ->
     ordu B ->
     ordu (t_arrow A B)
 | OU_and : forall (A B:typ),
     ordu A ->
     ordu B ->
     ordu (t_and A B).
(** definitions *)

(* defns Split *)
Inductive spli : typ -> typ -> typ -> Prop :=    (* defn spli *)
 | SpI_and : forall (A B:typ),
     spli (t_and A B) A B
 | SpI_orl : forall (A B A1 A2:typ),
     spli A A1 A2 ->
     spli (t_or A B) (t_or A1 B) (t_or A2 B)
 | SpI_orr : forall (A B B1 B2:typ),
     ordi A ->
     spli B B1 B2 ->
     spli (t_or A B) (t_or A B1) (t_or A B2)
 | SpI_arrowI : forall (A B B1 B2:typ),
     spli B B1 B2 ->
     spli (t_arrow A B) (t_arrow A B1) (t_arrow A B2)
 | SpI_arrowU : forall (A B A1 A2:typ),
     ordi B ->
     splu A A1 A2 ->
     spli (t_arrow A B) (t_arrow A1 B) (t_arrow A2 B)
with splu : typ -> typ -> typ -> Prop :=    (* defn splu *)
 | SpU_or : forall (A B:typ),
     splu (t_or A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2)
 | SpU_arrowI : forall (A B A1 A2:typ),
     ordu B ->
     spli A A1 A2 ->
     splu (t_arrow A B) (t_arrow A1 B) (t_arrow A2 B)
 | SpU_arrowU : forall (A B B1 B2:typ),
     splu B B1 B2 ->
     splu (t_arrow A B) (t_arrow A B1) (t_arrow A B2).
(** definitions *)

(* defns ASub *)
Inductive algorithmic_sub : typ -> typ -> Prop :=    (* defn algorithmic_sub *)
 | AS_int : 
     algorithmic_sub t_int t_int
 | AS_top : forall (A:typ),
     algorithmic_sub A t_top
 | AS_bot : forall (A:typ),
     algorithmic_sub t_bot A
 | AS_arrow : forall (A1 A2 B1 B2:typ),
     ordi (t_arrow A1 A2) ->
     ordi (t_arrow B1 B2) ->
     algorithmic_sub B1 A1 ->
     algorithmic_sub A2 B2 ->
     algorithmic_sub (t_arrow A1 A2) (t_arrow B1 B2)
 | AS_and : forall (A B B1 B2:typ),
     spli B B1 B2 ->
     algorithmic_sub A B1 ->
     algorithmic_sub A B2 ->
     algorithmic_sub A B
 | AS_andl : forall (A B A1 A2:typ),
     ordi B ->
     spli A A1 A2 ->
     algorithmic_sub A1 B ->
     algorithmic_sub A B
 | AS_andr : forall (A B A1 A2:typ),
     ordi B ->
     spli A A1 A2 ->
     algorithmic_sub A2 B ->
     algorithmic_sub A B
 | AS_or : forall (A B A1 A2:typ),
     ordi A ->
     ordi B ->
     splu A A1 A2 ->
     algorithmic_sub A1 B ->
     algorithmic_sub A2 B ->
     algorithmic_sub A B
 | AS_orl : forall (A B B1 B2:typ),
     ordi A ->
     ordi B ->
     ordu A ->
     splu B B1 B2 ->
     algorithmic_sub A B1 ->
     algorithmic_sub A B
 | AS_orr : forall (A B B1 B2:typ),
     ordi A ->
     ordi B ->
     ordu A ->
     splu B B1 B2 ->
     algorithmic_sub A B2 ->
     algorithmic_sub A B.


