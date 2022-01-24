From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import encode_relation.
From self.high Require Import dprop resources modalities post_crash_modality monpred_simpl.
From self.lang Require Import lang.
From self.high.modalities Require Import no_buffer.

(* A handy alias for the type of location predicates. *)
Definition loc_pred `{nvmFixedG Σ} ST `{AbstractState ST} := ST → val → nvmDeltaG Σ → dProp Σ.

(* A protocol consists of
  - A predicate [ϕ] that holds for each write and corresponding state of the
    location.
  - A function [bumper] that specifies how the state of a location changes
    after a crash. *)
Class LocationProtocol `{AbstractState ST, nvmFixedG Σ} (ϕ : loc_pred ST) := {
  bumper : ST → ST;
  bumper_mono :> Proper ((⊑@{ST}) ==> (⊑))%signature bumper;
  phi_condition :
    (⊢ ∀ (hD : nvmDeltaG Σ) s v,
      ϕ s v hD -∗ <PCF> hD', ϕ (bumper s) v hD' : dProp Σ)%I;
  phi_nobuf :> (∀ hD s v, IntoNoBuffer (ϕ s v hD) (ϕ s v hD));
}.

(** [know_protocol] represents the knowledge that a location is associated with a
specific protocol. It's defined simply using more "primitive" assertions. *)
Definition know_protocol `{AbstractState ST, nvmFixedG Σ, nvmDeltaG Σ}
           ℓ (ϕ : loc_pred ST) `{!LocationProtocol ϕ} : dProp Σ :=
  "#knowPred" ∷ ⎡ know_pred ℓ ϕ ⎤ ∗
  "#knowPreorder" ∷ ⎡ know_preorder_loc ℓ (⊑@{ST}) ⎤ ∗
  "#knowBumper" ∷ ⎡ know_bumper ℓ bumper ⎤%I.

Lemma encode_bumper_bump_mono `{LocationProtocol ST} (x y x' y' : positive) :
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

  Implicit Types (ϕ : loc_pred ST).

  Lemma post_crash_know_protocol ℓ ϕ `{!LocationProtocol ϕ} :
    know_protocol ℓ ϕ -∗ <PC> hD, or_lost ℓ (know_protocol ℓ ϕ).
  Proof.
    iIntros "(? & ? & ?)". iCrash.
    rewrite /know_protocol. rewrite -?or_lost_sep.
    iFrame.
  Qed.

  Global Instance know_protocol_into_crash ℓ ϕ `{!LocationProtocol ϕ} :
    IntoCrash
      (know_protocol ℓ ϕ)%I
      (λ hG', or_lost ℓ (know_protocol ℓ ϕ))%I.
  Proof.
    rewrite /IntoCrash. iIntros "P". by iApply post_crash_know_protocol.
  Qed.

End protocol.
