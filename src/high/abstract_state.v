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

(* Abstract state for unit. *)

Instance sqsubseteq_unit : SqSubsetEq unit := λ u1 u2, True.

Instance subseteq_unit_preorder : PreOrder (⊑@{unit}).
Proof. done. Qed.

Instance unit_abstract_state : AbstractState unit.
Proof. esplit; apply _. Defined.

(** * Discrete abstract state. *)

Record discrete A := mk_discrete { get_discrete : A }.

Arguments mk_discrete {_} _.
Arguments get_discrete {_} _.

Section discrete_abstract_state.
  Context {A : Type}.

  Global Program Instance discrete_eq_dec `{EqDecision A} : EqDecision (discrete A).
  Next Obligation.
    intros dec ??. unfold Decision.
    decide equality. apply dec.
  Qed.

  Global Program Instance discrete_countable `{Countable A} : Countable (discrete A) :=
    {| encode da := encode da.(get_discrete);
       decode p := mk_discrete <$> decode p;
    |}.
  Next Obligation. intros ??[?]. rewrite decode_encode. done. Qed.

  Global Instance discrete_sqsubseteq : SqSubsetEq (discrete A) := λ a1 a2, a1 = a2.

  Global Instance subseteq_discrete_preorder : PreOrder (⊑@{discrete A}).
  Proof. apply _. Qed.

  Global Instance discrete_abstract_state `{Countable A} : AbstractState (discrete A).
  Proof. esplit; apply _. Defined.

End discrete_abstract_state.
