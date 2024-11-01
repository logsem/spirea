(* This file defines the resource to share the knowledge of protocol predicates. *)

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
From self.base.modalities Require Import if_rec.

From self.lang Require Import lang.

Definition predicateR Σ :=
  agreeR (positive -d> val -d> laterO (optionO (thread_view -d> iPropO Σ))).
Definition predicatesR Σ := authR (gmapUR loc (predicateR Σ)).
Notation predicates_inG Σ Ω := (genInDepsG Σ Ω (predicatesR Σ) [#crashed_atR]).

Section ownership.
  Context `{!nvmBaseG Σ Ω, !predicates_inG Σ Ω}.
  Implicit Type (OCV: view) (PRs: gmap loc (predicateR Σ)) (PR: predicateR Σ).

  (* TODO: both this definition and the lemma below are duplicates *)
  Definition drop_OCV OCV ℓ PR :=
    if (decide (ℓ ∈ dom OCV)) then Some PR else None.

  Definition predicates_relyT := rel_over [#crashed_atR] (predicatesR Σ).

  Definition predicates_rel: predicates_relyT :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = fmap_auth $ map_imap $ drop_OCV OCV.

  Definition own_all_preds_ra γ dq PRs: iProp Σ :=
    "own_auth" ∷ gen_own γ (●{dq} PRs) ∗
    "#rely" ∷ rely γ [#crashed_at_name] predicates_rel True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition know_pred_ra γ ℓ PR: iProp Σ :=
    "own_frag" ∷ gen_own γ (◯ {[ ℓ := PR ]}) ∗
    "#rely" ∷ rely γ [#crashed_at_name] predicates_rel True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Lemma map_imap_drop_OCV_restrict OCV m:
    map_imap (drop_OCV OCV) m = restrict (dom OCV) m.
  Proof.
    apply map_eq => i.
    rewrite /drop_OCV map_lookup_imap /=.
    destruct (decide (i ∈ dom OCV)).
    - rewrite restrict_lookup_elem_of; last done.
      by destruct (m !! i).
    - rewrite restrict_lookup_not_elem_of; last done.
      by destruct (m !! i).
  Qed.

  Global Instance own_all_preds_auth_into_nextgen γ dq PRs:
    IntoNextgen
      (own_all_preds_ra γ dq PRs)
      (∃ OCV,
          own_all_preds_ra γ dq (restrict (dom OCV) PRs) ∗
          picked_in crashed_at_name (crashed_at_trans OCV)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct ("own_auth") as (t) "[#picked own_auth]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iExists OCV'.
    rewrite fmap_auth_auth.
    iDestruct "own_auth" as "[own_auth _]".
    iDestruct "crashed" as (??) "[pickedC' #crashed_at]".
    iPickedInAgree "pickedC pickedC'".
    iEval (simpl) in "crashed_at".
    rewrite map_imap_drop_OCV_restrict.
    iFrame "∗#".
    iExists _, _.
    iApply "crashed_at".
  Qed.

  Global Instance ghost_map_elem_into_nextgen γ k PR:
    IntoNextgen
      (know_pred_ra γ k PR)
      (if_rec k (know_pred_ra γ k PR)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct "own_frag" as (t) "[#picked frag]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iIntros (CV [[t] ?]) "#crashed_at #persisted_loc".
    iAssert ⌜ k ∈ dom OCV' ⌝%I as "%".
    { iDestruct "crashed_at" as (??? Hview) "[crashed_at _]".
      iDestruct "crashed" as (??) "[pickedC' #crashed_at']".
      iPickedInAgree "pickedC pickedC'".
      iDestruct (gen_own_valid_2 with "crashed_at' crashed_at") as %[_ <-%to_agree_op_valid_L]%pair_valid.
      iPureIntro.
      rewrite -(view_sub_dom_eq _ OV) Hview.
      rewrite elem_of_dom.
      by eexists.
    }
    rewrite fmap_auth_frag.
    (* TODO: move to separate lemma *)
    rewrite -{1}insert_empty.
    erewrite map_imap_insert_Some;
      first rewrite map_imap_empty insert_empty //;
        last rewrite /drop_OCV decide_True //.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at']".
    iPickedInAgree "pickedC pickedC'".
    iFrame "∗#".
    iIntros.
    iExists _, _.
    iApply "crashed_at'".
  Qed.
End ownership.

Arguments predicateR {Σ}.
Arguments predicatesR {Σ}.
