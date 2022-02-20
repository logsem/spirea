From stdpp Require Export countable.

From self Require Import extra.
From self.high Require Import abstract_state.

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

(* Abstract state where all elements are included in each other. *)
Record singl (A : Type) := mk_singl { get_singl : A }.
Arguments mk_singl {A}.
Arguments get_singl {A}.

Instance sqsubseteq_singl A : SqSubsetEq (singl A) := λ u1 u2, True.

Instance subseteq_singl_preorder A : PreOrder (⊑@{singl A}).
Proof. done. Qed.

Instance singl_eqdecision A `{EqDecision A} : EqDecision (singl A).
Proof. 
  unfold EqDecision in *. unfold Decision in *. decide equality.
Qed.

Instance singl_countable A `{Countable A} : Countable (singl A).
Proof.
  refine (inj_countable' get_singl mk_singl _).
  intros [x]. reflexivity.
Qed.

Instance singl_abstract_state A `{Countable A} : AbstractState (singl A).
Proof. esplit; apply _. Defined.

(* Abstract state for unit. *)

Instance sqsubseteq_unit : SqSubsetEq unit := λ u1 u2, True.

Instance subseteq_unit_preorder : PreOrder (⊑@{unit}).
Proof. done. Qed.

Instance unit_abstract_state : AbstractState unit.
Proof. esplit; apply _. Defined.

(** * discreteState abstract state. *)

Record discreteState A := mk_discrete { get_discrete : A }.

Arguments mk_discrete {_} _.
Arguments get_discrete {_} _.

Section discrete_abstract_state.
  Context {A : Type}.

  Global Program Instance discrete_eq_dec `{EqDecision A} : EqDecision (discreteState A).
  Next Obligation.
    intros dec ??. unfold Decision.
    decide equality. apply dec.
  Qed.

  Global Program Instance discrete_countable `{Countable A} : Countable (discreteState A) :=
    {| encode da := encode da.(get_discrete);
       decode p := mk_discrete <$> decode p;
    |}.
  Next Obligation. intros ??[?]. rewrite decode_encode. done. Qed.

  Global Instance discrete_sqsubseteq : SqSubsetEq (discreteState A) := λ a1 a2, a1 = a2.

  Global Instance subseteq_discrete_preorder : PreOrder (⊑@{discreteState A}).
  Proof. apply _. Qed.

  Global Instance discrete_abstract_state `{Countable A} : AbstractState (discreteState A).
  Proof. esplit; apply _. Defined.

End discrete_abstract_state.
