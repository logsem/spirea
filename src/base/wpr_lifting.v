From stdpp Require Import numbers.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth dfrac.
(* From Perennial.base_logic.lib Require Import proph_map. *)
(* From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy. *)
From self.program_logic Require Import recovery_weakestpre recovery_adequacy.

From self.nextgen Require Import omega.
From self Require Import extra map_extra ipm_tactics if_non_zero view_slice.
From self.lang Require Import lang.
From self.base Require Import generational_resources primitive_laws.
From self.nextgen Require Import nextgen_promises.

Set Default Proof Using "Type".

Definition wpr `{!nvmBaseG Σ Ω, !extraStateInterp Σ, !PerennialG Σ}
           (s : stuckness) (E : coPset)
           (e : thread_state) (recv : thread_state) (Φ : thread_val → iProp Σ)
           (Φinv : iProp Σ)
           (Φr : thread_val → iProp Σ) :=
  wpr
    nvm_crash_lang s E e recv Φ
    (Φinv)%I
    (λ v, Φr v)%I.

Section wpr.
  Context {Σ : gFunctors} {Ω: gGenCmras Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types Φc : iProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Lemma wpr_strong_mono `{!nvmBaseG Σ Ω, !extraStateInterp Σ, !PerennialG Σ}
        s E e rec Φ Ψ Φinv Ψinv Φr Ψr :
    wpr s E e rec Φ Φinv Φr -∗
    (* TODO: what is this modality? *)
    ■ ((∀ v, Φ v ==∗ Ψ v) ∧ ((Φinv -∗ Ψinv) ∧ (∀ v, Φr v ==∗ Ψr v))) -∗
    wpr s E e rec Ψ Ψinv Ψr.
  Proof.
    rewrite /wpr. iIntros "Hwpr Himpl".
    iApply (wpr_strong_mono with "Hwpr [Himpl]").
    repeat iSplit.
    - by iDestruct "Himpl" as "($ & _)".
    - by iDestruct "Himpl" as "(_ & $ & _)".
    - by iDestruct "Himpl" as "(_ & _ & $)".
  Qed.

  Definition persist_auth `{!nvmBaseG Σ Ω} (σ : mem_config): iProp Σ :=
    ∃ OCV, persisted_auth (OCV `view_add` σ.2) ∗ crashed_at_offset OCV.

  (* Lemma nvm_heap_reinit σ PV CV `{!nvmBaseG} *)
  (*       (γcrash : gname) : *)
  (*   (* The first two assumptions are the content of [crash_step σ σ'] *) *)
  (*   PV ⊑ CV → *)
  (*   consistent_cut CV σ → *)
  (*   valid_heap σ → *)
  (*   ⊢ gen_heap_interp (hG := _) σ -∗ *)
  (*     persist_auth (σ, PV) *)
  (*     ==∗ *)
  (*     ∃ (hGD' : nvmBaseDeltaG), *)
  (*       ⌜ @crash_token_name hGD' = γcrash ⌝ ∗ *)
  (*       validV (hGD := hGD') ∅ ∗ *)
  (*       post_crash_mapsto_map σ hGD hGD' ∗ *)
  (*       nvm_heap_ctx (hGD := hGD') (slice_of_store CV σ, view_to_zero CV) ∗ *)
  (*       persisted_impl hGD hGD' ∗ *)
  (*       persisted (hGD := hGD') (view_to_zero CV) ∗ *)
  (*       crashed_at (hGD := hGD') CV. *)
  (* Proof using Σ. *)
  (*   iIntros (pIncl cut invs) "heapIntrp pers". *)
  (*   rewrite /nvm_heap_ctx. simpl. *)
  (*   (* Allocate a new heap at a _new_ ghost name. *) *)
  (*   iMod (gen_heap_init_names (slice_of_store CV σ)) as (γh γm) "(heapNew & ptsMap & _)". *)
  (*   (* We persist/freeze the old persist view. *) *)
  (*   iMod (own_update with "pers") as "pers". *)
  (*   { apply auth_update_auth_persist. } *)
  (*   iDestruct "pers" as "#oldPers". *)
  (*   (* Allocate a new persist view. *) *)
  (*   iMod (own_alloc (● (view_to_zero CV) ⋅ ◯ (view_to_zero CV))) as (persistG) "[pers #persFrag]". *)
  (*   { apply auth_both_valid_2; [apply view_valid|done]. } *)
  (*   (* Allocate the store view at a _new_ ghost name. *) *)
  (*   iMod (own_alloc (● max_view (slice_of_store CV σ) ⋅ ◯ ∅)) as (storeG) "[store fragStore]". *)
  (*   { apply auth_both_valid_2; [apply view_valid | apply: ucmra_unit_least]. } *)
  (*   (* Allocate the crashed at view at a _new_ ghost name. *) *)
  (*   iMod (own_alloc (to_agree CV : agreeR viewO)) as (crashedAtG) "#crashed". *)
  (*   { done. } *)
  (*   iModIntro. *)
  (*   set names := {| heap_names_name := Build_nvm_heap_names γh γm; *)
  (*                   crash_token_name := γcrash; *)
  (*                   store_view_name := storeG; *)
  (*                   persist_view_name := persistG; *)
  (*                   crashed_at_view_name := crashedAtG |}. *)
  (*   iExists names. *)
  (*   iSplitPure; first done. *)
  (*   rewrite /crashed_at_view_name. simpl. *)
  (*   iFrame. *)
  (*   iFrame "crashed persFrag". *)
  (*   (* We show the ghost crash relation. *) *)
  (*   iSplitL "ptsMap heapIntrp". *)
  (*   { rewrite /post_crash_mapsto_map. *)
  (*     iSplitL "heapIntrp". *)
  (*     { iIntros (???) "pts". *)
  (*       (* Set Printing All. *) *)
  (*       iApply (gen_heap_valid with "heapIntrp pts"). } *)
  (*     iDestruct (big_sepM_impl_strong _ _ _ σ with "ptsMap []") as "[$ _]". *)
  (*     iModIntro. *)
  (*     iIntros (ℓ hist) "pts". iIntros (look). *)
  (*     iApply soft_disj_intro_r. *)
  (*     iExists _. iFrame "crashed". *)
  (*     destruct (slice_of_store CV σ !! ℓ) as [?|] eqn:look'; last first. *)
  (*     * iRight. iPureIntro. *)
  (*       eapply consistent_cut_lookup_slice; done. *)
  (*     * iLeft. *)
  (*       rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'. *)
  (*       rewrite map_fmap_zip_with in look'. *)
  (*       apply map_lookup_zip_with_Some in look'. *)
  (*       destruct look' as ([t] & ? & ? & CVLook & ?). *)
  (*       rewrite /consistent_cut in cut. *)
  (*       pose proof (map_Forall_lookup_1 _ _ _ _ cut CVLook) as (? & ? & ? & ? & map). *)
  (*       simplify_eq. *)
  (*       iExists _, _. *)
  (*       iSplit; first done. *)
  (*       rewrite H2. *)
  (*       rewrite map_fmap_singleton. *)
  (*       iFrame "pts". *)
  (*       iPureGoal; first done. *)
  (*       iPureIntro. *)
  (*       eapply (map_Forall_lookup_1 _ _ _ _ map). *)
  (*       rewrite /drop_above. *)
  (*       apply map_filter_lookup_Some_2; [done| reflexivity]. } *)
  (*   iSplit. *)
  (*   * simpl. *)
  (*     iSplit. { iPureIntro. apply store_inv_cut; done. } *)
  (*     iExists CV. iFrame "crashed". *)
  (*     (* TODO: Factor this out into a lemma (needs [cut] only). *) *)
  (*     apply consistent_cut_subseteq_dom in cut. *)
  (*     rewrite /slice_of_store /slice_of_hist map_fmap_zip_with. *)
  (*     rewrite map_fmap_zip_with. *)
  (*     rewrite dom_map_zip_with_eq_l; try done. *)
  (*   * iModIntro. *)
  (*     iIntros (V) "pers". *)
  (*     rewrite /persisted. *)
  (*     iDestruct (persisted_auth_included with "oldPers pers") as %incl. *)
  (*     assert (V ⊑ CV) as incl'. { etrans; done. } *)
  (*     iSplit. *)
  (*     { edestruct (view_to_zero_mono) as [? ->]; first apply incl'. *)
  (*       iDestruct "persFrag" as "[$ _]". } *)
  (*     iExists CV. iFrame "#%". *)
  (* Qed. *)

  (* Lemma nvm_heap_reinit_alt σ σ': *)
  (*   crash_step σ σ' → *)
  (*   ⊢ nvm_heap_ctx σ -∗ *)
  (*      |==> ⚡==> |==> *)
  (*       nvm_heap_ctx (hGD := names) σ' ∗ *)
  (*       Pg names. *)
  (* Proof. *)
  (*   iIntros ([store p p' pIncl cut]). *)
  (*   iIntros "(heap & authStor & %inv & pers & recov) Pg". *)
  (*   iMod (nvm_heap_reinit _ _ _ _ _ γcrash with "heap pers") *)
  (*     as (hGD') "(%crEq & _ & map & interp' & #persImpl & rec)"; try done. *)
  (*   rewrite /post_crash. *)
  (*   (* set newBundle : nvmBaseDeltaG := *) *)
  (*   (*   {| nvmBaseDeltaG' := hnames |}. *) *)
  (*   iSpecialize ("Pg" $! store hGD'). *)
  (*   (* rewrite /newBundle. *) *)
  (*   iDestruct ("Pg" with "persImpl map") as "(map & Pg)". *)
  (*   iExists _. iModIntro. *)
  (*   iSplitPure; first done. iFrame. *)
  (* Qed. *)

  (* Is this the only thing I need to prove for high spirea (other than views of course)? *)
  Lemma extra_state_nextgen `{!nvmBaseG Σ Ω, !extraStateInterp Σ, !PerennialG Σ}:
    extra_state_interp ⊢ |==> ⚡==> |==> extra_state_interp.
  Proof.
  Admitted.

  Lemma idempotence_wpr `{!nvmBaseG Σ Ω, !extraStateInterp Σ, !PerennialG Σ}
      s E1 e e_rec Φ Φinv Φr Φc :
    ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
    (* TODO: have an expert double check this modality *)
    ■ (Φc -∗ ▷ ⚡==> (Φinv ∧ WPC e_rec @ s ; E1 {{ Φr }} {{ Φc }})) -∗
      wpr s E1 e e_rec Φ Φinv Φr.
  Proof.
    iIntros "Hwpc #Hidemp".
    iApply (idempotence_wpr nvm_crash_lang s E1 e e_rec _ _ _ Φc
                            with "[$Hwpc] [Hidemp]").
    (* { iApply (wpc_crash_mono with "[] Hwpc"). *)
    (*   iIntros "HΦcx". iExists _. destruct nG. by iFrame. } *)
    { iApply (plainly_mono with "[$]").
      iIntros "Hidemp" (σ_pre_crash g σ_post_crash Hcrash ns mj D κs ?) "ϕc".
      (* iMod (NC_alloc_strong) as (γcrash) "HNC". *)
      iSpecialize ("Hidemp" with "ϕc").
      (* rewrite eq. *)
      iIntros "[interp extra] g".
      (* iMod (nvm_heap_reinit_alt _ _ _ _ γcrash _ Hcrash with "interp Hidemp") *)
      (*   as (hnames) "(%cEq & map & interp' & idemp)". *)
      iMod (heap_ctx_next_generation _ _ Hcrash with "interp") as "interp".
      iMod (extra_state_nextgen with "extra") as "extra".
      do 3 iModIntro. iMod "interp". iMod "extra".
      iAssert (global_state_interp g (step_count_next ns) mj D κs)%I as "$". { admit. }
      (* iMod (global_state_interp_le (Λ := nvm_lang) _ _ () _ _ κs with "[$]") as "$"; *)
      (*   first (rewrite /step_count_next; simpl; lia). *)
      iModIntro.
      rewrite /state_interp //=.
      iFrame.
  Admitted.
End wpr.
