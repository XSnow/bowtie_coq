(*******************************************************************************
*                                                                              *
*   TypeSize.v                                                                 *
*   Xuejing Huang 2021                                                         *
*   Distributed under the terms of the GPL-v3 license                          *
*                                                                              *
*   This file is part of DistributingTypes.                                    *
*                                                                              *
*   DistributingTypes is free software: you can redistribute it and/or modify  *
*   it under the terms of the GNU General Public License as published by       *
*   the Free Software Foundation, either version 3 of the License, or          *
*   (at your option) any later version.                                        *
*                                                                              *
*   DistributingTypes is distributed in the hope that it will be useful,       *
*   but WITHOUT ANY WARRANTY; without even the implied warranty of             *
*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *
*   GNU General Public License for more details.                               *
*                                                                              *
*   You should have received a copy of the GNU General Public License          *
*   along with DistributingTypes.  If not, see <https://www.gnu.org/licenses/>.*
*                                                                              *
*******************************************************************************)

(* This file defines size on types and proves some related
lemmas. It aims to make later proofs easier if they do
induction on the size of types *)

Require Import LibTactics.
Require Export Coq.micromega.Lia.
Require Export Definitions.

(* The hint database contains type size related lemmas *)
Create HintDb typSize.

(* define size of types *)
Fixpoint size_typ (A1 : typ) : nat :=
  match A1 with
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_or A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  end.

Lemma size_typ_min : forall A1, 1 <= size_typ A1.
Proof.
  intro A. induction A; simpl; lia.
Qed.

#[export] Hint Resolve size_typ_min : typSize.


Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

#[export] Hint Resolve typ_size_lg_z : typSize.

Lemma choose_decrease_size : forall m A B,
    size_typ (choose m A B) = size_typ A + size_typ B + 1.
Proof.
  intros; destruct m; simpl in *; lia.
Qed.

Hint Rewrite choose_decrease_size : typSize.

Lemma split_decrease_size: forall m A B C,
    spl m A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof with (pose proof (typ_size_lg_z); simpl in *; try lia).
  - introv H.
    induction H; try rewrite choose_decrease_size in *; simpl in *; eauto...
    destruct m; eauto...
    destruct m; eauto...
Qed.

Ltac spl_size :=
  try repeat match goal with
         | [ H: spl _ _ _ _ |- _ ] =>
           ( lets (?&?): split_decrease_size H; clear H)
             end;
  try rewrite choose_decrease_size in *.

(********************************************)
(*                                          *)
(*               Ltac elia                  *)
(*  enhanced lia with split_decrease_size   *)
(*                                          *)
(********************************************)
Ltac elia :=
  try solve [pose proof (typ_size_lg_z);
             spl_size; simpl in *; try lia].

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto with typSize;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
    intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
  | intros ].
