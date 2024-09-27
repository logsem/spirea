(* This file defines the generalized version of [ghost_map] that accepts camera
 * this is used in two locations: physical maps and predicates . *)

From Equations Require Import Equations.
From iris.algebra Require Import gmap_view.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises.
From self.algebra Require Import view.
From self.base Require Import generational_resources.

From self.lang Require Import lang.

viewR

Definition predicateR Σ :=
  agreeR (positive -d> val -d> laterO (optionO (thread_view -d> iPropO Σ))).
Definition predicatesR Σ := gmap_viewR loc (predicateR Σ).
Notation predicates_inG Σ Ω := (genInDepsG Σ Ω (predicatesR Σ) [#crashed_atR]).

Section ownership.
  Context `{!nvmBaseG Σ Ω, !predicates_inG Σ Ω}.
  Implicit Type (OCV: view) (PRs: gmap loc (predicateR Σ)) (PR: predicateR Σ).

  Definition drop_OCV OCV ℓ PR :=
    if (decide (ℓ ∈ dom OCV)) then Some PR else None.

  Definition predicates_relyT := rel_over [#crashed_atR] (predicatesR Σ).

  Definition predicates_rel: predicates_relyT :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = map_entry_lift_gmap_view $ drop_OCV OCV.

  Definition own_all_preds_ra γ dq PRs: iProp Σ :=
    ∃ OCV,
      "own_auth" ∷ gen_own γ (gmap_view_auth dq PRs) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      "#rely" ∷ rely γ [#crashed_at_name] predicates_rel True_pred.

  Definition know_pred_ra γ ℓ dq PR: iProp Σ :=
    ∃ OCV,
      "own_frag" ∷ gen_own γ (gmap_view_frag ℓ dq PR) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      "#rely" ∷ rely γ [#crashed_at_name] predicates_rel True_pred.

  (* TODO: put relevant lemmas here *)
End ownership.

Arguments predicateR {Σ}.
Arguments predicatesR {Σ}.
