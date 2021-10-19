From stdpp Require Export countable.

From self Require Import extra.

Class AbstractState ST `{Countable ST} := {
  abs_state_relation : relation2 ST;
  abs_state_preorder :> PreOrder abs_state_relation;
}.

Instance abstract_state_sqsubseteq `{AbstractState ST} : SqSubsetEq ST :=
  abs_state_relation.

(** We define abstract state for some common types. *)

(* Abstract state for booleans. *)
Instance sqsubseteq_bool : SqSubsetEq bool := λ b1 b2,
    if b1 then b2 = true else True.

Instance subseteq_bool_preorder : PreOrder (⊑@{bool}).
Proof. split; repeat intros [|]; done. Qed.

Instance bool_abstract_state : AbstractState bool.
Proof. esplit; apply _. Defined.

(* Abstract state for natural numbers. *)
Instance sqsubseteq_nat : SqSubsetEq nat := λ v w, v ≤ w.

Instance subseteq_nat_preorder : PreOrder (⊑@{nat}).
Proof. apply _. Qed.

Instance nat_abstract_state : AbstractState nat.
Proof. esplit; apply _. Defined.

Lemma subseteq_nat_le (n m : nat) : n ⊑ m = (n ≤ m).
Proof. done. Qed.
