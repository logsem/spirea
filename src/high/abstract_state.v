From stdpp Require Export countable.

From self Require Import extra.

Class AbstractState ST `{Countable ST} := {
  abs_state_relation : relation2 ST;
  abs_state_preorder :> PreOrder abs_state_relation;
}.

Global Hint Mode AbstractState ! - - : typeclass_instances.

Instance abstract_state_sqsubseteq `{AbstractState ST} : SqSubsetEq ST :=
  abs_state_relation.
