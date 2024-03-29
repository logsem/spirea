(* In this file we define [dProp], the type of propositions in the high-level
logic. *)

From iris.bi Require Import lib.fractional.
From iris.bi Require Export monpred.
From iris.proofmode Require Import monpred tactics.
From iris.base_logic.lib Require Import iprop.

From self Require Export view memory.
From self.high Require Export resources.

Instance subseteq_nvmdeltag : SqSubsetEq nvmDeltaG := λ v w, v = w.

Instance nvmDeltaG_inhabited : Inhabited (nvmDeltaG).
Proof. repeat split; apply 1%positive. Qed.

(* Our propositions are parameterized by a thread view and a record of ghost names.
   For now we call this type [index] and use [i] to range over it.
 *)
Notation index := (thread_view * nvmDeltaG)%type.

(* We define a canonical [biIndex] structure for [thread_view]. All fields except for
[bi_index_type] can be infered by Coq. *)
Canonical Structure thread_view_bi_index : biIndex :=
  {| bi_index_type := index; |}.

(* Uncomment this to see the fields that Coq infer. *)
(* Print thread_view_bi_index. *)

(*
Instance view_bi_index_bot (TV : thread_view) : BiIndexBottom (ε : thread_view).
Proof.
  rewrite /BiIndexBottom. intros [[??] ?]. rewrite !subseteq_prod'.
  rewrite !subseteq_view_incl.
  split; first split; apply: ucmra_unit_least.
Qed.
*)

(* Types of view predicates. *)
Definition dProp Σ := monPred thread_view_bi_index (iPropI Σ).
Definition dPropO Σ := monPredO thread_view_bi_index (iPropI Σ).
Definition dPropI Σ := monPredI thread_view_bi_index (iPropI Σ).

Ltac iModel := iStartProof (iProp _); iIntros ([TV gnames]).

Tactic Notation "introsIndex" simple_intropattern(x) simple_intropattern(y) :=
  iIntros ([x ?] [y [= <-]]).

(* [bi_scope] is the scope associated with the scope key [I] from Iris. We bind
it to the [dProp] type such that we avoid having to type `%I` to get the right
scope when writing definitions of type [dProp]. *)
Bind Scope bi_scope with dProp.

Section definitions.
  Context {Σ : gFunctors}.

  (* An easier way to define a monotone predicate where the names and the thread
  view are given as two different argument and where monotonicity only needs to
  be shown for the the thread view. *)
  Program Definition MonPredCurry
    (P : nvmDeltaG → thread_view → iProp Σ)
    (mono : ∀ names, Proper ((⊑) ==> (⊢)) (P names))
      : dProp Σ :=
    MonPred (λ i, P i.2 i.1) _.
  Next Obligation.
    intros ? ?.
    intros [??] [??] [? [= ->]].
    solve_proper.
  Qed.

  Program Definition have_thread_view (TV : thread_view) : dProp Σ:=
    MonPredCurry (λ _ i, ⌜ TV ⊑ i ⌝%I) _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_thread_view_persistent TV1 :
    Persistent (have_thread_view TV1).
  Proof. rewrite /Persistent. iModel. auto. Qed.

  Program Definition have_SV ℓ t : dProp Σ :=
    MonPredCurry (λ _ i, ⌜ t ≤ (store_view i) !!0 ℓ ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_SV_persistent ℓ t : Persistent (have_SV ℓ t).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Program Definition have_FV ℓ t : dProp Σ :=
    MonPred (λ i, ⌜ t ≤ (flush_view i.1) !!0 ℓ ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_FV_persistent ℓ t : Persistent (have_FV ℓ t).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  (* This is stronger than [have_FV] when the timestamp is [0]. *)
  Program Definition have_FV_strong (ℓ : loc) (t : nat) : dProp Σ :=
    have_thread_view (∅, {[ ℓ := MaxNat t ]}, ∅).
    (* MonPred (λ i, ⌜ {[ ℓ := MaxNat t ]} ⊑ (flush_view i.1) ⌝)%I _. *)
  (* Next Obligation. solve_proper. Qed. *)
    (* monPred_in (∅, {[ ℓ := MaxNat t ]}, ∅). *)

  Lemma have_SV_0 ℓ : ⊢ have_SV ℓ 0.
  Proof. iModel. iPureIntro. lia. Qed.

  Lemma have_FV_0 ℓ : ⊢ have_FV ℓ 0.
  Proof. iModel. iPureIntro. lia. Qed.

  Definition have_FV_strong_weaken ℓ t :
    have_FV_strong ℓ t -∗ have_FV ℓ t.
  Proof.
    iModel. iPureIntro.
    destruct TV as [[? FV] ?].
    intros [[_ incl] _].
    rewrite /lookup_zero /=.
    apply view_le_singleton in incl as (t2 & -> & le).
    done.
  Qed.

  Lemma monPred_in_have_SV SV PV BV ℓ t :
    t ≤ SV !!0 ℓ →
    have_thread_view (SV, PV, BV) -∗
    have_SV ℓ t.
  Proof.
    intros le.
    iStartProof (iProp _). iPureIntro. intros [[[SV' ?] ?] ?] [[incl ?]?].
    etrans; first done. f_equiv. done.
  Qed.

  Lemma monPred_in_bottom : ⊢@{dPropI Σ} have_thread_view (∅, ∅, ∅).
  Proof.
    iStartProof (iProp _). iPureIntro.
    intros [[[??]?] ?].
    repeat split; apply view_empty_least.
  Qed.

  Program Definition with_gnames (P : nvmDeltaG → dProp Σ) : dProp Σ :=
    MonPred (λ i, P i.2 i) _.
  Next Obligation.
    intros ? [? ?].
    introsIndex ? ?.
    simpl.
    apply monPred_mono.
    done.
  Qed.

  Global Instance with_gnames_ne n :
    Proper (((=) ==> dist n) ==> dist n) with_gnames.
  Proof.
    rewrite /with_gnames.
    intros ?? eq.
    split.
    intros [??].
    simpl.
    f_equiv.
    apply eq.
    done.
  Qed.

  Global Instance with_gnames_mono : Proper (((=) ==> (⊢)) ==> (⊢)) with_gnames.
  Proof.
    intros ?? impl.
    iModel.
    iApply impl.
    done.
  Qed.

  Definition know_gnames (gnames : nvmDeltaG) : dProp Σ :=
    with_gnames (λ gnames', ⌜ gnames = gnames' ⌝)%I.

  Lemma with_gnames_intro (P : _ → dProp Σ) : (∀ nD, P nD) -∗ with_gnames P.
  Proof. iModel. iIntros "H". iApply "H". Qed.

  Lemma with_gnames_intro_independent (P : dProp Σ) : P ⊢ with_gnames (λ nD, P).
  Proof. done. Qed.

  Global Instance with_gnames_persistent `{∀ nD, Persistent (P nD)} :
    Persistent (with_gnames P).
  Proof.
    rewrite /Persistent.
    iModel.
    simpl.
    iIntros "#P !>".
    done.
  Qed.

  Global Instance with_gnames_fractional (P : _ → _ → dProp Σ) :
    (∀ nD, Fractional (P nD)) →
    Fractional (λ q, with_gnames (λ nD, P nD q)).
  Proof.
    intros f p q.
    iModel. simpl.
    rewrite f.
    rewrite monPred_at_sep.
    auto.
  Qed.

  Global Instance with_gnames_as_fractional (P : _ → dProp Σ) Q q :
    (∀ nD, AsFractional (P nD) (Q nD) q) →
    AsFractional (with_gnames P) (λ q, with_gnames (λ nD, Q nD q)) q.
  Proof.
    intros f.
    split.
    - iModel. simpl.
      rewrite 1!(@as_fractional _ (P gnames) (Q gnames)).
      auto.
    - apply with_gnames_fractional. intros ?. apply f.
  Qed.

End definitions.
