From iris.algebra Require Import gmap_view view.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import classes ltac_tactics.
From iris_named_props Require Import named_props.

From self Require Import extra.
From self.lang Require Import lang.
From self.algebra Require Import view.
From self.nextgen Require Import nextgen_promises gmap_view_transformation.
From self.base Require Import generational_resources if_rec.
From self.high.resources Require Import gen_ghost_map_ofe.

Definition predicateO Σ: ofe :=
  positive -d> val -d> laterO (optionO (thread_view -d> iPropO Σ)).

Class predicatesGpreS Σ Ω `{!nvmBaseGS Σ Ω} := {
  predicatesGpreS_ghost_mapO :: ghost_mapOGpreS loc (predicateO Σ) Σ Ω
}.
Section predicates.
  Context `{!nvmBaseGS Σ Ω, !predicatesGpreS Σ Ω}.
  Implicit Type (OCV: view.view) (PRs: gmap loc (predicateO Σ)) (PR: predicateO Σ).

  #[local] Definition drop_OCV OCV ℓ v: option (predicateO Σ) :=
    if (decide (ℓ ∈ dom OCV)) then Some v else None.

  #[global] Instance drop_OCV_maptrans OCV: MapTrans (drop_OCV OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_OCV; intros; destruct (decide _); done.
  Qed.

  Lemma loc_map_cmra_morphism OCV:
    CmraMorphism (ghost_mapO_trans drop_OCV OCV).
  Proof. apply _. Qed.

  (* We keep these assertions for backward compatibility. *)
  Definition own_all_preds_ra γ dq PRs: iProp Σ :=
    ghost_mapO_auth γ drop_OCV dq PRs.
  
  Definition know_pred_ra γ ℓ PR: iProp Σ :=
    ghost_mapO_elem γ drop_OCV ℓ DfracDiscarded PR.

  Lemma preds_lookup γ dq PRs ℓ PR:
    own_all_preds_ra γ dq PRs -∗ know_pred_ra γ ℓ PR -∗ PRs !! ℓ ≡ Some PR.
  Proof. apply ghost_mapO_lookup. Qed.

  Lemma preds_insert γ PRs ℓ PR:
    PRs !! ℓ = None →
    own_all_preds_ra γ (DfracOwn 1) PRs ==∗
    own_all_preds_ra γ (DfracOwn 1) (<[ ℓ := PR]> PRs) ∗ know_pred_ra γ ℓ PR.
  Proof. apply ghost_mapO_insert_persist. Qed.

  Lemma pred_agree γ ℓ PR1 PR2:
    know_pred_ra γ ℓ PR1 -∗
    know_pred_ra γ ℓ PR2 -∗
    PR1 ≡ PR2.
  Proof. apply ghost_mapO_elem_agree. Qed.
  
  #[local] Lemma map_imap_drop_OCV_restrict OCV m:
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

  #[local] Lemma elem_of_drop_OCV_gmap_view_frag OCV ℓ dq v :
    ℓ ∈ dom OCV →
    (map_entry_lift_gmap_view (drop_OCV OCV) (gmap_view_frag ℓ dq (to_agree v))) =
    (gmap_view_frag ℓ dq (to_agree v)).
  Proof.
    intros.
    rewrite map_entry_lift_gmap_view_frag /drop_OCV decide_True //.
  Qed.
  
  #[global] Instance own_all_preds_auth_into_nextgen γ dq PRs:
    IntoNextgen
      (own_all_preds_ra γ dq PRs)
      (∀ OCV,
         crashed_at_offset OCV -∗
          own_all_preds_ra γ dq (restrict (dom OCV) PRs)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_auth" as (tH') "[#pickedH' own_auth]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iEval (simpl) in "own_auth".
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite /ghost_mapO_trans.
    iFrame "rely".
    iSplit; last by iExists _, _.
    rewrite map_entry_lift_gmap_view_auth.
    rewrite map_imap_drop_OCV_restrict.
    iFrame.
  Qed.

  #[global] Instance ghost_map_elem_into_nextgen γ k PR:
    IntoNextgen
      (know_pred_ra γ k PR)
      (if_rec k (know_pred_ra γ k PR)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct "own_elem" as (t) "[#picked elem]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iIntros (OCV'' ?) "#crashed_at_offset _".
    iAssert ⌜ OCV'' = OCV' ⌝%I as %->.
    { iDestruct "crashed_at_offset" as (OV) "crashed_at_both".
      iDestruct "crashed" as (??) "[pickedC' #crashed_at_both']".
      iPickedInAgree "pickedC pickedC'".
      iDestruct (crashed_at_both_agree with "crashed_at_both crashed_at_both'") as %[-> ->].
      iPureIntro.
      done. }
    rewrite /ghost_mapO_trans elem_of_drop_OCV_gmap_view_frag; last rewrite elem_of_dom //.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at']".
    iPickedInAgree "pickedC pickedC'".
    iFrame "∗#".
  Qed.
End predicates.
Opaque own_all_preds_ra know_pred_ra.
