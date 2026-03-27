From stdpp Require Export countable.

From self Require Import extra.

Class AbstractState ST `{Countable ST} := {
  (* NOTE: The definition makes use of [relation2] as using [relation] (or
  anything that refers to it such as [SqSubsetEq] causes universe issues due to
  Iris. *)
  abs_state_relation :> relation2 ST;
  #[global] abs_state_preorder :: PreOrder abs_state_relation;
}.

#[global] Hint Mode AbstractState ! - - : typeclass_instances.

#[global] Instance abstract_state_sqsubseteq `{AbstractState ST} : SqSubsetEq ST :=
  abs_state_relation.
