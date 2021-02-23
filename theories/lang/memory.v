(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.

Notation loc := Z.

Notation time := nat.

Notation view := (gmap loc time).

Section memory.

  Inductive atomicity := Atomic | NonAtomic.

End memory.