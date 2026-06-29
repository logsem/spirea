(** This file defines all modalities[1] introduced in high-level Spirea logic.
 ** Their individual typeclass instances and lemmas are moved to individual files
 ** in this folder.
 ** with the exception of [<fence_sync_atomic>], which depends on [protocol.v],
 ** which depends on [<nobuf>] and [<NG>]. *)
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import proofmode.

From self.high Require Import dprop generational_resources abstract_state.
From self.nextgen Require Export nextgen_promises.

Program Definition post_fence {Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, P (store_view TV,
                    (flush_view TV ⊔ buffer_view TV),
                    buffer_view TV)) _.
  (* MonPred (λ '(s, p, b), P (s, (p ⊔ b), ∅)) _. *)
Next Obligation.
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<fence>' P" :=
  (post_fence P) (at level 20, right associativity) : bi_scope.

Program Definition post_fence_sync `{!nvmBaseGS Σ Ω}
        (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    bi_wand
      (persisted (buffer_view TV))
      (P (store_view TV,
          (flush_view TV ⊔ buffer_view TV),
           buffer_view TV))
  ) _.
Next Obligation.
  intros Σ ?? P. intros [[??]?] [[??]?] [[??]?]. simpl.
  assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
  iIntros "pers P".
  iApply monPred_mono; last iApply "pers".
  { repeat split; done. }
  iApply (persisted_anti_mono with "P").
  done.
Qed.

Notation "'<fence_sync>' P" :=
  (post_fence_sync P) (at level 20, right associativity) : bi_scope.

Program Definition no_buffer `{Σ : gFunctors} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, P (store_view TV, flush_view TV, ∅)) _.
Next Obligation.
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<nobuf>' P" :=
  (no_buffer P) (at level 20, right associativity) : bi_scope.

Program Definition no_flush `{Σ : gFunctors} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, P (store_view TV, ∅, ∅)) _.
Next Obligation.
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<noflush>' P" :=
  (no_flush P) (at level 20, right associativity) : bi_scope.

(** [nextgen] modality for high-Spirea
 ** NOTE: we need to know a state exist even though it might survive anyway.
 ** This is used to obtain the decode/encode relation, which in turns tell us that
 ** decoding the crash state will succeed. *)
Definition know_crash_frag_history_loc `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}: iProp Σ :=
  □ (∀ ℓ t (ST: Type) (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
       (bumper: ST → ST) (OV OCV: view.view) (σ: ST),
       crashed_at_both OV OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗ (* that we know location [ℓ] survives *)
       lastgen_know_preorder_loc ℓ (⊑@{ST}) -∗ (* and we know the preorder *)
       lastgen_know_frag_history_loc ℓ t σ -∗ (* and we know a state exists. *)
       lastgen_know_bumper ℓ bumper -∗ (* and we know the bumper *)
       (* we know a crashed timestamp exists. *)
       ∃ (σ_c: ST) v_c, crashed_in_loc ℓ σ_c ∗ know_frag_history_loc ℓ (OCV !!0 ℓ) (bumper σ_c) ∗
                        know_phys_hist_msg ℓ (OCV !!0 ℓ) (Msg v_c ∅ ∅ ∅) ∗
                        (* and any state we know are "persisted" will be ordered earlier than [σ_c] *)
                        (* TODO: the first half of this knowledge should really be part of the [crashed_at] rely *)
                        ⌜ t - (OV !!0 ℓ) ≤ (OCV !!0 ℓ) - (OV !!0 ℓ) → OV !!0 ℓ ≤ OCV !!0 ℓ ∧ σ ⊑ σ_c ⌝).

(* Definition crashed_in_impl OCV `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}: iProp Σ := *)
(*   [∗ map] ℓ ↦ t ∈ OCV, *)
(*     □ (∀ (ST: Type) (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST) (bumper: ST → ST), *)
(*          know_preorder_loc ℓ (abs_state_relation (ST := ST)) -∗ *)
(*          know_bumper ℓ bumper -∗ *)
(*          ∃ (σ: ST), crashed_in_loc ℓ σ ∗ know_frag_history_loc ℓ (max_nat_car t) (bumper σ)). *)

Definition nextgen `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω} (P: dProp Σ): dProp Σ :=
  MonPred (λ TV, ⚡==> know_crash_frag_history_loc -∗ P (∅, ∅, ∅))%I _.

Notation base_IntoNextgen := (nextgen_promises_model.IntoNextgen).
Notation base_nextgen := (nextgen_promises_model.nextgen).
Notation "'<NG>' P" := (nextgen P)
  (at level 200, right associativity) : bi_scope.

Program Definition nextgen_flush `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (<NG> ∀ (CV : view.view),
       ⌜ flush_view TV ⊑ CV ⌝ ∗
       ⎡ persisted (view_to_zero (flush_view TV)) ⎤ ∗
       ⎡ crashed_at CV ⎤ -∗
       P) (∅, ∅, ∅))%I _.
Next Obligation.
  intros ????????.
  apply nextgen_mono.
  do 7 f_equiv; first solve_proper.
  iIntros "#H"; iApply (persisted_weak with "H").
  solve_proper.
Qed.

Notation "'<NGF>' P" :=
  (nextgen_flush P)
  (at level 200, right associativity) : bi_scope.

(** [if_rec] *)
(* The predicate [P] holds for [ℓ] or [ℓ] has been lost. *)
(* I believe the [persisted_loc] component is unnecessary
 * (implied by CV, at least in the context of a valid state interpretation),
 * but in case it's necessary in some unforseen way, I'm keeping it for now. *)

(* Yixuan: I'm moving to use [crashed_at_offset] instead of [crashed_at] as much as possible. *)
Definition if_rec `{!nvmBaseGS Σ Ω} (ℓ : loc) (P : dProp Σ) : dProp Σ :=
  ∀ (OCV : view.view),
  ⌜ is_Some (OCV !! ℓ) ⌝ -∗ ⎡ crashed_at_offset OCV ⎤ -∗ ⎡ persisted_loc ℓ 0 ⎤ -∗ P.

Notation base_if_rec := self.base.modalities.if_rec.if_rec.
