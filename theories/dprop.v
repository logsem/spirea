(* In this file we define [dProp], the type of propositions in the high-level
logic. *)

From iris.bi Require Export monpred big_op.
From iris.proofmode Require Import tactics monpred modality_instances.
From iris.base_logic.lib Require Import fancy_updates.

From self Require Import view memory.

(* We define a canonical [biIndex] structure for [thread_view]. All fields except for
[bi_index_type] can be infered by Coq. *)
Canonical Structure thread_view_bi_index : biIndex :=
  {| bi_index_type := thread_view; |}.

(* Uncomment this to see the fields that Coq infer. *)
(* Print thread_view_bi_index. *)

Instance view_bi_index_bot (TV : thread_view) : BiIndexBottom (ε : thread_view).
Proof.
  rewrite /BiIndexBottom. intros [[??] ?]. rewrite !subseteq_prod'.
  rewrite !subseteq_view_incl.
  split; first split; apply: ucmra_unit_least.
Qed.

(* Types of view predicates. *)
Definition dProp Σ := monPred thread_view_bi_index (uPredI (iResUR Σ)). (* FIXME: use iPropI here. *)
Definition dPropO Σ := monPredO thread_view_bi_index (uPredI (iResUR Σ)).
Definition dPropI Σ := monPredI thread_view_bi_index (uPredI (iResUR Σ)).

