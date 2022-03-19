From stdpp Require Export countable.

From self Require Import extra.
From self.algebra Require Import view.
From self.high Require Import abstract_state.

(** We define abstract state for some common types. *)

(* Abstract state for booleans. *)

Program Instance bool_abstract_state : AbstractState bool :=
  { abs_state_relation b1 b2 := if b1 then b2 = true else True }.
Next Obligation. split; repeat intros [|]; done. Qed.

Program Instance nat_abstract_state : AbstractState nat :=
  { abs_state_relation := (≤) }.

Program Instance Z_abstract_state : AbstractState Z :=
  { abs_state_relation := (≤)%Z }.

Lemma subseteq_nat_le (n m : nat) : n ⊑ m = (n ≤ m).
Proof. done. Qed.

(* Abstract state where all elements are included in each other. *)
Record singl (A : Type) := mk_singl { get_singl : A }.
Arguments mk_singl {A}.
Arguments get_singl {A}.

Instance singl_eqdecision A `{EqDecision A} : EqDecision (singl A).
Proof. 
  unfold EqDecision in *. unfold Decision in *. decide equality.
Qed.

Instance singl_countable A `{Countable A} : Countable (singl A).
Proof.
  apply (inj_countable' get_singl mk_singl).
  intros [x]. reflexivity.
Qed.

Instance singl_abstract_state A `{Countable A} : AbstractState (singl A).
Proof. esplit; apply _. Defined.

(* Abstract state for unit. *)

Instance unit_abstract_state : AbstractState unit.
Proof. esplit; apply _. Defined.

(** Discrete abstract state (only reflexivity). *)

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

  Global Instance discrete_abstract_state `{Countable A} : AbstractState (discreteState A).
  Proof. esplit; apply _. Defined.

End discrete_abstract_state.

(** Numbered abstract state. *)

Inductive numbered (A : Type) := mk_numbered : nat → A → numbered A.

Arguments mk_numbered {A} n a.

Section numbered_abstract_state.
  Context `{Countable A}.

  Global Instance numbered_discreteeq : EqDecision (numbered A).
  Proof.
    unfold EqDecision in *. unfold Decision in *.
    decide equality. decide equality.
  Qed.

  Global Instance numbered_countable : Countable (numbered A).
  Proof.
    apply (inj_countable' (λ '(mk_numbered n a), (n, a))
                          (λ '(n, a), mk_numbered n a)).
    intros [??]. reflexivity.
  Qed.

  Global Program Instance numbered_abstract_state : AbstractState (numbered A) :=
    {
      abs_state_relation '(mk_numbered n1 a1) '(mk_numbered n2 a2) :=
        n1 < n2 ∨ (n1 = n2 ∧ a1 = a2)
    }.
  Next Obligation.
    constructor.
    - intros [??]. right. done.
    - intros [??] [??] [??] [?|[??]] [?|[??]]; try (left; naive_solver lia).
      right. split; congruence.
  Qed.

  Global Instance numbered_antisym : AntiSymm (=) (⊑@{numbered A}).
  Proof. intros [??] [??] [?|[??]] [?|[??]]; lia || congruence. Qed.

  Lemma numbered_le n1 n2 a1 a2 :
    n1 < n2 →
    mk_numbered n1 a1 ⊑ mk_numbered n2 a2.
  Proof. intros ?. left. done. Qed.

End numbered_abstract_state.

(** Product abstract state. *)

Section prod_abstract_state.

  Global Instance prod_abstract_state `{AbstractState A} `{AbstractState B} :
    AbstractState (A * B) := {}.

End prod_abstract_state.
