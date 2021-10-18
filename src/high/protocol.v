From iris.base_logic.lib Require Import own ghost_map.
From iris.proofmode Require Import reduction monpred tactics.

From self.high Require Import dprop resources post_crash_modality monpred_simpl.
(* From self.high Require Import proofmode wpc_proofmode. *)
From self.lang Require Import lang.


(* A handy alias for the type of location predicates. *)
Definition loc_pred {Σ} ST `{AbstractState ST} := ST → val → nvmDeltaG Σ → dProp Σ.

(* A protocol consists of
  - A predicate [ϕ] that holds for each write and corresponding state of the
    location.
  - A function [bumper] that specifies how the state of a location changes
    after a crash. *)
Class LocationProtocol `{AbstractState ST, nvmFixedG Σ} (ϕ : loc_pred ST) := {
  bumper : ST → ST;
  bumper_mono :> Proper ((⊑@{ST}) ==> (⊑))%signature bumper;
  phi_condition :
    (⊢ ∀ (hD : nvmDeltaG Σ) s v, ϕ s v hD -∗ <PCF> hD', ϕ (bumper s) v hD' : dProp Σ)%I
}.

(** [know_protocol] represents the knowledge that a location is associated with a
specific protocol. It's defined simply using more "primitive" assertions. *)
Definition know_protocol `{AbstractState ST, nvmFixedG Σ, nvmDeltaG Σ}
           ℓ ϕ `{!LocationProtocol ϕ} : dProp Σ :=
  ⎡ know_pred ℓ ϕ ⎤ ∗
  ⎡ know_preorder_loc ℓ (⊑@{ST}) ⎤ ∗
  ⎡ know_bumper ℓ bumper ⎤%I.

Section protocol.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.
  Context `{AbstractState ST}.

  (* Context (ϕ : loc_pred (Σ := Σ) ST) (ℓ : loc). *)
  (* Context `{!LocationProtocol ϕ}. *)

  Lemma post_crash_know_protocol ℓ ϕ `{!LocationProtocol ϕ} :
    know_protocol ℓ ϕ -∗ <PC> hD, or_lost ℓ (know_protocol ℓ ϕ).
  Proof.
    iIntros "(a & b & c)".
    iCrash.
    rewrite /know_protocol.
    rewrite -?or_lost_sep.
    iFrame.
  Qed.

  Global Instance know_protocol_into_crash ℓ ϕ `{!LocationProtocol ϕ} :
    IntoCrash
      (know_protocol ℓ ϕ)%I
      (λ hG', or_lost ℓ (know_protocol ℓ ϕ))%I.
  Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_know_protocol. Qed.

End protocol.
