(* In this file we define [dProp], the type of propositions in the high-level
logic. *)

From iris.bi Require Export monpred.
From iris.proofmode Require Import monpred tactics.
From iris.base_logic.lib Require Import iprop.

From self Require Export view memory.

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
Definition dProp Σ := monPred thread_view_bi_index (iPropI Σ).
Definition dPropO Σ := monPredO thread_view_bi_index (iPropI Σ).
Definition dPropI Σ := monPredI thread_view_bi_index (iPropI Σ).

Ltac iModel := iStartProof (iProp _); iIntros (TV).

(* [bi_scope] is the scope associated with the scope key [I] from Iris. We bind
it to the [dProp] type such that we avoid having to type `%I` to get the right
scope when writing definitions of type [dProp]. *)
Bind Scope bi_scope with dProp.

Section definitions.
  Context {Σ : gFunctors}.

  Program Definition have_SV ℓ t : dProp Σ :=
    MonPred (λ TV, ⌜ t ≤ (store_view TV) !!0 ℓ ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_SV_persistent ℓ t : Persistent (have_SV ℓ t).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Program Definition have_FV ℓ t : dProp Σ :=
    MonPred (λ TV, ⌜ t ≤ (flush_view TV) !!0 ℓ ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_FV_persistent ℓ t : Persistent (have_FV ℓ t).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  (* This is stronger than [have_FV] when the timestamp is [0]. *)
  Definition have_FV_strong (ℓ : loc) (t : nat) : dProp Σ :=
    monPred_in (∅, {[ ℓ := MaxNat t ]}, ∅).

  Lemma have_SV_0 ℓ : ⊢ have_SV ℓ 0.
  Proof. iModel. iPureIntro. lia. Qed.

  Lemma have_FV_0 ℓ : ⊢ have_FV ℓ 0.
  Proof. iModel. iPureIntro. lia. Qed.

  Definition have_FV_strong_weaken ℓ t :
    have_FV_strong ℓ t -∗ have_FV ℓ t.
  Proof.
    iModel. iPureIntro.
    destruct TV as [[? FV]?].
    intros [[_ incl] _].
    rewrite /lookup_zero /=.
    apply view_le_singleton in incl as (t2 & -> & le).
    done.
  Qed.

  Lemma monPred_in_have_SV SV PV BV ℓ t :
    t ≤ SV !!0 ℓ →
    monPred_in (SV, PV, BV) -∗
    have_SV ℓ t.
  Proof.
    intros le.
    iStartProof (iProp _). iPureIntro. intros [[SV' ?] ?] [[incl ?]?].
    etrans; first done. f_equiv. done.
  Qed.

  Lemma monPred_in_bottom : ⊢@{dPropI Σ} monPred_in (∅, ∅, ∅).
  Proof.
    iStartProof (iProp _). iPureIntro.
    intros [[??]?].
    repeat split; apply view_empty_least.
  Qed.

 End definitions.
