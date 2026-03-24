(** generational resource for [authR (gsetUR loc)]. **)
From Equations Require Import Equations.
From iris.algebra Require Import gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises.
From self.algebra Require Import view.
From self.base Require Import generational_resources.

From self.lang Require Import lang.

(* similar to [gen_ghost_map], the transformer depends on the [crashed_at] resrouce.
 * since there is only one transformer we need, I'm not generalizing the definitions.
 * I hope it will not cause troubles later... *)
Section gen_alocs.
  Implicit Type (OCV: view) (ℓs: gset loc).

  Definition gen_alocsR: cmra := authR (gsetUR loc).
  Notation gen_alocsR_inG Σ Ω := (genInDepsG Σ Ω (gen_alocsR) [#crashed_atR]).

  Definition drop_OCV_locs OCV ℓs :=
    ℓs ∩ dom OCV.

  Definition gen_alocs_rel: rel_over [#crashed_atR] gen_alocsR :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = fmap_auth $ drop_OCV_locs OCV.

  #[local] Existing Instance nvmBaseGS_crashed_at_inG.
  #[local] Existing Instance crashed_atGpreS_crashed_at.

  Context `{!nvmBaseGS Σ Ω} `{!gen_alocsR_inG Σ Ω}.

  Definition gen_alocs_auth γ ℓs: iProp Σ :=
    "own_auth" ∷ gen_own γ (● ℓs) ∗
    "#rely" ∷ rely γ [#crashed_at_name] gen_alocs_rel (λ _, true) ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition gen_alocs_frag γ ℓs: iProp Σ :=
    "own_frag" ∷ gen_own γ (◯ ℓs) ∗
    "#rely" ∷ rely γ [#crashed_at_name] gen_alocs_rel (λ _, true) ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  #[global] Instance gen_alocs_auth_into_nextgen {γ} ℓs:
    IntoNextgen
      (gen_alocs_auth γ ℓs)
      (∀ OCV,
         crashed_at_offset OCV -∗
         gen_alocs_auth γ (ℓs ∩ dom OCV)).
  Proof using Type.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_auth" as (tH') "[#pickedH' own_auth]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite fmap_auth_auth /drop_OCV_locs.
    iDestruct "own_auth" as "[$ _]".
    iFrame "#".
    by iExists _.
  Qed.

  #[global] Instance gen_alocs_frag_into_nextgen {γ} ℓs:
    IntoNextgen
      (gen_alocs_frag γ ℓs)
      (∃ OCV,
          gen_alocs_frag γ (ℓs ∩ dom OCV) ∗
          picked_in crashed_at_name (crashed_at_trans OCV)).
  Proof using Type.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct ("own_frag") as (t) "[#picked own_frag]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iExists OCV'.
    rewrite fmap_auth_frag /drop_OCV_locs.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at]".
    iPickedInAgree "pickedC pickedC'".
    iFrame "∗#".
    iExists _, _.
    iApply "crashed_at".
  Qed.

  Lemma gen_alocs_update {γ} locs ℓ :
    gen_alocs_auth γ locs ==∗ gen_alocs_auth γ (locs ∪ {[ ℓ ]}) ∗ gen_alocs_frag γ {[ ℓ ]}.
  Proof.
    iNamed 1.
    iDestruct (@gen_own_update with "own_auth") as ">[auth frag]".
    { apply auth_update_alloc. apply gset_local_update.
      apply (union_subseteq_r {[ ℓ ]}). }
    rewrite /gen_alocs_auth /gen_alocs_frag.
    iFrame "#".
    iEval (rewrite -gset_op) in "frag". iDestruct "frag" as "[$ _]".
    rewrite (comm (∪)).
    iFrame.
    done.
  Qed.
End gen_alocs.

Notation gen_alocsR_inG Σ Ω := (genInDepsG Σ Ω (gen_alocsR) [#crashed_atR]).
