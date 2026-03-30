(** generational resource for [authR (gsetUR loc)]. **)
From Equations Require Import Equations.
From iris.algebra Require Import gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import classes ltac_tactics.
From iris_named_props Require Import named_props.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises.
From self.algebra Require Import view.
From self.base Require Import generational_resources if_rec.

From self.lang Require Import lang.

Definition gen_alocsR: cmra := authR (gsetUR loc).
Notation gen_alocsR_inG Σ Ω := (genInDepsG Σ Ω (gen_alocsR) [#crashed_atR]).

(* similar to [gen_ghost_map], the transformer depends on the [crashed_at] resrouce.
 * since there is only one transformer we need, I'm not generalizing the definitions.
 * I hope it will not cause troubles later... *)
Section gen_alocs.
  Implicit Type (OCV: view) (ℓs: gset loc).

  Definition drop_OCV_locs OCV ℓs :=
    ℓs ∩ dom OCV.

  Definition gen_alocs_rel: rel_over [#crashed_atR] gen_alocsR :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = fmap_auth $ drop_OCV_locs OCV.

  #[local] Instance drop_OCV_locs_cmra_morphism OCV:
    CmraMorphism (fmap_auth (drop_OCV_locs OCV)).
  Proof.
    apply: fmap_auth_gentrans.
    split; try done.
    - intros n locs1 locs2.
      rewrite -?discrete_iff.
      fold_leibniz.
      congruence.
    - intros.
      fold_leibniz.
      rewrite /drop_OCV_locs gset_op.
      set_solver.
  Qed.
  
  Context `{!nvmBaseGS Σ Ω} `{!gen_alocsR_inG Σ Ω}.

  Definition gen_alocs_auth γ ℓs: iProp Σ :=
    "own_auth" ∷ gen_own γ (● ℓs) ∗
    "#rely" ∷ rely γ [#crashed_at_name] gen_alocs_rel (λ _, true) ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition gen_alocs_frag γ ℓs: iProp Σ :=
    "own_frag" ∷ gen_own γ (◯ ℓs) ∗
    "#rely" ∷ rely γ [#crashed_at_name] gen_alocs_rel (λ _, true) ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

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

  Lemma gen_alocs_agree {γ} locs1 locs2 :
    gen_alocs_auth γ locs1 -∗ gen_alocs_frag γ locs2 -∗ ⌜ locs2 ⊆ locs1 ⌝.
  Proof.
    iNamed 1.
    iDestruct 1 as "[own_frag _]".
    iDestruct (gen_own_valid_2 with "own_auth [$]") as %[H%gset_included _]%auth_both_valid_discrete.
    done.
  Qed.

  Lemma gen_alocs_alloc locs OCV OPV:
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, gen_alocs_auth γ locs ∗ gen_alocs_frag γ locs.
  Proof.
    iIntros "#OCV #rely".
    iMod (own_gen_alloc
                  (DS := [#crashed_atR])
                  (● locs ⋅ ◯ locs)
                  [#crashed_at_name]
                  [##_] with "[]") as (γ) "[[$ $] tok]".
    { apply auth_both_valid_2; done. }
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iAssumption. }
    iFrame "#".
    iMod (token_strengthen_promise
            (DS := [#crashed_atR])
            _ [#_] [##_] _ (gen_alocs_rel) _ True_pred
           with "[] tok") as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    2: {
      iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely". }
    (* TODO: this subgoal requires me to prove that for any transformer picked for
     * [crashed_atR], there exists a transformer for the map that satisfy [R].
     * this can only be proven given specific [R]. I should move this lemma around. *)
    { intros ts crashedPred.
      dependent elimination ts as [hcons tC hnil].
      destruct crashedPred as ((OCV2 & ? & ->) & _).
      exists (fmap_auth $ drop_OCV_locs OCV2).
      split; first apply _.
      simpl.
      exists OCV2. done. }
    by iDestruct (token_to_rely with "tok") as "#$".
  Qed.
    
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
  Qed.

  #[global] Instance gen_alocs_frag_into_nextgen {γ} ℓs:
    IntoNextgen
      (gen_alocs_frag γ ℓs)
      (∀ OCV, crashed_at_offset OCV -∗ gen_alocs_frag γ (ℓs ∩ dom OCV)).
  Proof using Type.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_frag" as (tH') "[#pickedH' own_frag]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite fmap_auth_frag /drop_OCV_locs.
    iFrame "∗#".
  Qed.
End gen_alocs.

Opaque gen_alocs_auth gen_alocs_frag.
