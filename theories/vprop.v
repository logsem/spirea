(* In this file we define [vProp], the type of propositions in the high-level
logic. *)

From iris.bi Require Export monpred big_op.
From iris.proofmode Require Import tactics monpred modality_instances.
From iris.base_logic.lib Require Import fancy_updates.

From self Require Import view.

(* We define a canonical [biIndex] structure for [view]. All fields except for
[bi_index_type] can be infered by Coq. *)
Canonical Structure view_bi_index : biIndex :=
  {| bi_index_type := view |}.

(* Uncomment this to see the fields that Coq infer. *)
(* Print view_bi_index. *)

Instance view_bi_index_bot (V : view) : BiIndexBottom ∅ := view_empty_least.

(* Types of view predicates. *)
Definition vProp Σ := monPred view_bi_index (uPredI (iResUR Σ)). (* FIXME: use iPropI here. *)
Definition vPropO Σ := monPredO view_bi_index (uPredI (iResUR Σ)).
Definition vPropI Σ := monPredI view_bi_index (uPredI (iResUR Σ)).
