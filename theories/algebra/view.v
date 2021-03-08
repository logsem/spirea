From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Import auth gmap numbers.

Notation time := nat.

Notation view := (gmap loc time).

Instance join_view : Join view := (union_with (λ (x1 x2 : nat), Some (x1 `max` x2))).

Infix "!!0" := (λ m i, default 0 (m !! i)) (at level 80).

(* Resource algebra for views. *)
Definition viewUR := gmapUR loc max_natUR.

Definition view_to_ra (v : view) : viewUR := MaxNat <$> v.

Global Instance view_core_id (v : viewUR) : CoreId v.
Proof. apply _. Qed.