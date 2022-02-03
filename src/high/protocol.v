From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import encode_relation.
From self.high Require Import dprop resources modalities post_crash_modality
      monpred_simpl or_lost.
From self.lang Require Import lang.
From self.high.modalities Require Import no_buffer.

(* A handy alias for the type of location predicates. *)
Definition loc_pred `{nvmFixedG Σ} ST `{AbstractState ST} := ST → val → nvmDeltaG Σ → dProp Σ.

(* A protocol consists of
  - A predicate [pred] that holds for each write and corresponding state of the
    location.
  - A function [bumper] that specifies how the state of a location changes
    after a crash. *)
Record LocationProtocol ST `{AbstractState ST, nvmFixedG Σ} := {
  pred : loc_pred ST;
  bumper : ST → ST;
  bumper_mono : Proper ((⊑@{ST}) ==> (⊑))%signature bumper;
  pred_condition :
    (⊢ ∀ (hD : nvmDeltaG Σ) s v,
      pred s v hD -∗ <PCF> hD', pred (bumper s) v hD' : dProp Σ)%I;
  pred_nobuf :> (∀ hD s v, IntoNoBuffer (pred s v hD) (pred s v hD));
}.

Global Arguments pred {ST} {_} {_} {_} {_} {_} _.
Global Arguments bumper {ST} {_} {_} {_} {_} {_} _.

Existing Instance bumper_mono.
Existing Instance pred_nobuf.

(** [know_protocol] represents the knowledge that a location is associated with a
specific protocol. It's defined simply using more "primitive" assertions. *)
Definition know_protocol `{AbstractState ST, nvmFixedG Σ, nvmDeltaG Σ}
           ℓ (prot : LocationProtocol ST) : iProp Σ :=
  "#knowPred" ∷ know_pred ℓ prot.(pred) ∗
  "#knowPreorder" ∷ know_preorder_loc ℓ (⊑@{ST}) ∗
  "#knowBumper" ∷ know_bumper ℓ prot.(bumper).

Lemma encode_bumper_bump_mono `{AbstractState ST}
      (bumper : ST → ST) `{!Proper ((⊑@{ST}) ==> (⊑))%signature bumper}
      (x y x' y' : positive) :
  encode_bumper bumper x = Some x' →
  encode_bumper bumper y = Some y' →
  encode_relation (⊑@{ST}) x y →
  encode_relation (⊑@{ST}) x' y'.
Proof.
  rewrite /encode_bumper. rewrite /encode_relation.
  intros (sx & -> & <-)%encode_bumper_Some_decode.
  intros (sy & -> & <-)%encode_bumper_Some_decode.
  rewrite !decode_encode /=.
  solve_proper.
Qed.

Section protocol.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}.

  Implicit Types (prot : LocationProtocol ST).

  Lemma post_crash_know_protocol ℓ prot :
    ⎡ know_protocol ℓ prot ⎤ -∗ <PC> hD, or_lost ℓ (⎡ know_protocol ℓ prot ⎤).
  Proof.
    iIntros "(a & b & c)". iCrash.
    iCombine "a b c" as "a".
    rewrite ?or_lost_sep.
    iApply (or_lost_mono with "[] a").
    iIntros "($ & $ & $)".
  Qed.

  Global Instance know_protocol_into_crash ℓ prot :
    IntoCrash
      (⎡ know_protocol ℓ prot ⎤)%I
      (λ hG', or_lost ℓ (⎡ know_protocol ℓ prot ⎤))%I.
  Proof.
    rewrite /IntoCrash. iIntros "P". by iApply post_crash_know_protocol.
  Qed.

End protocol.
