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

  Context `{!nvmBaseG Σ Ω, !gen_alocsR_inG Σ Ω}.

  Definition gen_alocs_auth γ ℓs: iProp Σ :=
    ∃ OCV,
      "own_auth" ∷ gen_own γ (● ℓs) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      "#rely" ∷ rely γ [#crashed_at_name] gen_alocs_rel (λ _, true).

  Definition gen_alocs_frag γ ℓs: iProp Σ :=
    ∃ OCV,
      "own_frag" ∷ gen_own γ (◯ ℓs) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      "#rely" ∷ rely γ [#crashed_at_name] gen_alocs_rel (λ _, true).

  Instance gen_alocs_auth_into_nextgen {γ} ℓs:
    IntoNextgen
      (gen_alocs_auth γ ℓs)
      (∃ OCV,
          gen_alocs_auth γ (ℓs ∩ dom OCV) ∗
          picked_in crashed_at_name (crashed_at_trans OCV)).
  Proof using Type.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct ("own_auth") as (t) "[#picked own_auth]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iExists OCV'.
    rewrite fmap_auth_auth /drop_OCV_locs.
    iDestruct "own_auth" as "[own_auth _]".
    iDestruct "crashed" as (??) "[pickedC' #crashed_at]".
    iPickedInAgree "pickedC pickedC'".
    iFrame "#".
    iExists _.
    iFrame.
    iExists OCV.
    iApply "crashed_at".
  Qed.

  Instance gen_alocs_frag_into_nextgen {γ} ℓs:
    IntoNextgen
      (gen_alocs_frag γ ℓs)
      (∃ OCV,
          gen_alocs_frag γ (ℓs ∩ dom OCV) ∗
          picked_in crashed_at_name (crashed_at_trans OCV)).
  Proof using Type.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct ("own_frag") as (t) "[#picked own_frag]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iExists OCV'.
    rewrite fmap_auth_frag /drop_OCV_locs.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at]".
    iPickedInAgree "pickedC pickedC'".
    iFrame "#".
    iExists _.
    iFrame.
    iExists OCV.
    iApply "crashed_at".
  Qed.
End gen_alocs.

Notation gen_alocsR_inG Σ Ω := (genInDepsG Σ Ω (gen_alocsR) [#crashed_atR]).
