From stdpp Require Import numbers.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth dfrac.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.

From self Require Import extra map_extra ipm_tactics if_non_zero view_slice.
From self.lang Require Import lang.
From self.base Require Import primitive_laws post_crash_modality.

Set Default Proof Using "Type".

Definition wpr `{nvmBaseFixedG Σ, !extraStateInterp Σ, hG : nvmBaseDeltaG} `{hC : !crashGS Σ}
           (s : stuckness) (E : coPset)
           (e : thread_state) (recv : thread_state) (Φ : thread_val → iProp Σ)
           (Φinv : nvmBaseDeltaG → iProp Σ)
           (Φr : nvmBaseDeltaG → thread_val → iProp Σ) :=
  wpr
    nvm_crash_lang s _ E e recv Φ
    (λ hGen, ∃ nvmD, ⌜hGen = nvmBase_generationGS (hGD := nvmD)⌝ ∗ Φinv nvmD)%I
    (λ hGen v, ∃ nvmD, ⌜hGen = nvmBase_generationGS (hGD := nvmD)⌝ ∗ Φr nvmD v)%I.

Section wpr.
  Context {Σ : gFunctors}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types Φc : iProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Lemma wpr_strong_mono `{hG : !nvmBaseFixedG Σ, !extraStateInterp Σ, nvmBaseDeltaG}
        s E e rec Φ Ψ Φinv Ψinv Φr Ψr :
    wpr s E e rec Φ Φinv Φr -∗
    (∀ v, Φ v ==∗ Ψ v) ∧
    ((∀ hG, Φinv hG -∗ Ψinv hG) ∧ (∀ hG v, Φr hG v ==∗ Ψr hG v)) -∗
    wpr s E e rec Ψ Ψinv Ψr.
  Proof.
    rewrite /wpr. iIntros "Hwpr Himpl".
    iApply (wpr_strong_mono with "Hwpr [Himpl]").
    repeat iSplit.
    - by iDestruct "Himpl" as "($ & _)".
    - iIntros "% (% & % & ?)".
      iDestruct "Himpl" as "(_ & H)".
      iExists _. iSplit; first done. by iApply "H".
    - iIntros "%% (% & % & ?)".
      iDestruct "Himpl" as "(_ & H)".
      iExists _. iSplitR; first done. by iApply "H".
  Qed.

  Lemma store_inv_cut `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG} store p :
    consistent_cut p store →
    valid_heap store → valid_heap (slice_of_store p store).
  Proof.
    rewrite /valid_heap /valid_heap_lub.
    intros cut val.
    intros ℓ h look'.
    rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'.
    rewrite map_fmap_zip_with in look'.
    apply map_lookup_zip_with_Some in look'.
    destruct look' as ([t] & hist & ? & pLook & ?).
    eapply map_Forall_lookup_1 in val; last done.
    destruct val as [hi ho].
    split.
    - (* Extract info from consistent cut. *)
      rewrite /consistent_cut in cut.
      setoid_rewrite map_Forall_lookup in cut.
      pose proof (cut ℓ (MaxNat t) pLook) as (? & ? & ? & eq & ?).
      simplify_eq.
      rewrite eq.
      naive_solver.
    - rewrite H0.
      destruct (hist !! t);
        [rewrite map_fmap_singleton|rewrite fmap_empty];
        simpl; last apply map_Forall_empty.
      simplify_eq.
      apply map_Forall_singleton.
      apply view_empty_least.
  Qed.

  Definition persist_auth `{nvmBaseFixedG, hGD : nvmBaseDeltaG}
             (σ : mem_config) :=
    own persist_view_name (● σ.2).

  Lemma nvm_heap_reinit (hG : nvmBaseFixedG Σ) (hGD : nvmBaseDeltaG) σ PV CV
        (γcrash : gname) :
    (* The first two assumptions are the content of [crash_step σ σ'] *)
    PV ⊑ CV →
    consistent_cut CV σ →
    valid_heap σ →
    ⊢ gen_heap_interp (hG := _) σ -∗
      persist_auth (σ, PV)
      ==∗
      ∃ (hGD' : nvmBaseDeltaG),
        ⌜ @crash_token_name hGD' = γcrash ⌝ ∗
        validV (hGD := hGD') ∅ ∗
        post_crash_mapsto_map σ hGD hGD' ∗
        nvm_heap_ctx (hGD := hGD') (slice_of_store CV σ, view_to_zero CV) ∗
        persisted_impl hGD hGD' ∗
        persisted (hGD := hGD') (view_to_zero CV) ∗
        crashed_at (hGD := hGD') CV.
  Proof using Σ.
    iIntros (pIncl cut invs) "heapIntrp pers".
    rewrite /nvm_heap_ctx. simpl.
    (* Allocate a new heap at a _new_ ghost name. *)
    iMod (gen_heap_init_names (slice_of_store CV σ)) as (γh γm) "(heapNew & ptsMap & _)".
    (* We persist/freeze the old persist view. *)
    iMod (own_update with "pers") as "pers".
    { apply auth_update_auth_persist. }
    iDestruct "pers" as "#oldPers".
    (* Allocate a new persist view. *)
    iMod (own_alloc (● (view_to_zero CV) ⋅ ◯ (view_to_zero CV))) as (persistG) "[pers #persFrag]".
    { apply auth_both_valid_2; [apply view_valid|done]. }
    (* Allocate the store view at a _new_ ghost name. *)
    iMod (own_alloc (● max_view (slice_of_store CV σ) ⋅ ◯ ∅)) as (storeG) "[store fragStore]".
    { apply auth_both_valid_2; [apply view_valid | apply: ucmra_unit_least]. }
    (* Allocate the crashed at view at a _new_ ghost name. *)
    iMod (own_alloc (to_agree CV : agreeR viewO)) as (crashedAtG) "#crashed".
    { done. }
    iModIntro.
    set names := {| heap_names_name := Build_nvm_heap_names γh γm;
                    crash_token_name := γcrash;
                    store_view_name := storeG;
                    persist_view_name := persistG;
                    crashed_at_view_name := crashedAtG |}.
    iExists names.
    iSplitPure; first done.
    rewrite /crashed_at_view_name. simpl.
    iFrame.
    iFrame "crashed persFrag".
    (* We show the ghost crash relation. *)
    iSplitL "ptsMap heapIntrp".
    { rewrite /post_crash_mapsto_map.
      iSplitL "heapIntrp".
      { iIntros (???) "pts".
        (* Set Printing All. *)
        iApply (gen_heap_valid with "heapIntrp pts"). }
      iDestruct (big_sepM_impl_strong _ _ _ σ with "ptsMap []") as "[$ _]".
      iModIntro.
      iIntros (ℓ hist) "pts". iIntros (look).
      iApply soft_disj_intro_r.
      iExists _. iFrame "crashed".
      destruct (slice_of_store CV σ !! ℓ) as [?|] eqn:look'; last first.
      * iRight. iPureIntro.
        eapply consistent_cut_lookup_slice; done.
      * iLeft.
        rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'.
        rewrite map_fmap_zip_with in look'.
        apply map_lookup_zip_with_Some in look'.
        destruct look' as ([t] & ? & ? & CVLook & ?).
        rewrite /consistent_cut in cut.
        pose proof (map_Forall_lookup_1 _ _ _ _ cut CVLook) as (? & ? & ? & ? & map).
        simplify_eq.
        iExists _, _.
        iSplit; first done.
        rewrite H2.
        rewrite map_fmap_singleton.
        iFrame "pts".
        iPureGoal; first done.
        iPureIntro.
        eapply (map_Forall_lookup_1 _ _ _ _ map).
        rewrite /drop_above.
        apply map_filter_lookup_Some_2; [done| reflexivity]. }
    iSplit.
    * simpl.
      iSplit. { iPureIntro. apply store_inv_cut; done. }
      iExists CV. iFrame "crashed".
      (* TODO: Factor this out into a lemma (needs [cut] only). *)
      apply consistent_cut_subseteq_dom in cut.
      rewrite /slice_of_store /slice_of_hist map_fmap_zip_with.
      rewrite map_fmap_zip_with.
      rewrite dom_map_zip_with_eq_l; try done.
    * iModIntro.
      iIntros (V) "pers".
      rewrite /persisted.
      iDestruct (persisted_auth_included with "oldPers pers") as %incl.
      assert (V ⊑ CV) as incl'. { etrans; done. }
      iSplit.
      { edestruct (view_to_zero_mono) as [? ->]; first apply incl'.
        iDestruct "persFrag" as "[$ _]". }
      iExists CV. iFrame "#%".
  Qed.

  Lemma nvm_heap_reinit_alt (hG : nvmBaseFixedG Σ) (hGD : nvmBaseDeltaG) σ σ'
        (γcrash : gname) Pg :
    crash_step σ σ' →
    ⊢ nvm_heap_ctx σ -∗
      post_crash Pg ==∗
      ∃ names : nvmBaseDeltaG,
        ⌜ @crash_token_name names = γcrash ⌝ ∗
        post_crash_mapsto_map σ.1 hGD names ∗
        nvm_heap_ctx (hGD := names) σ' ∗
        Pg names.
  Proof.
    iIntros ([store p p' pIncl cut]).
    iIntros "(heap & authStor & %inv & pers & recov) Pg".
    iMod (nvm_heap_reinit _ _ _ _ _ γcrash with "heap pers")
      as (hGD') "(%crEq & _ & map & interp' & #persImpl & rec)"; try done.
    rewrite /post_crash.
    (* set newBundle : nvmBaseDeltaG := *)
    (*   {| nvmBaseDeltaG' := hnames |}. *)
    iSpecialize ("Pg" $! store hGD').
    (* rewrite /newBundle. *)
    iDestruct ("Pg" with "persImpl map") as "(map & Pg)".
    iExists _. iModIntro.
    iSplitPure; first done. iFrame.
  Qed.

  Lemma idempotence_wpr `{!ffi_interp_adequacy}
        `{hG : nvmBaseFixedG Σ, !extraStateInterp Σ, hGD : nvmBaseDeltaG} s E1 e rec Φx Φinv Φrx Φcx :
    ⊢ WPC e @ s; E1 {{ Φx }} {{ Φcx hGD }} -∗
    (□ ∀ (hG1 : nvmBaseDeltaG)
         (* (Hpf : @nvmBaseG_invGS Σ (@nvm_base_inG _ hG) = *)
         (*          @nvmBaseG_invGS Σ (@nvm_base_inG _ hG1)) *) σ σ'
         (HC : crash_prim_step (nvm_crash_lang) σ σ'),
         Φcx hG1 -∗ ▷ post_crash (λ hG2, (Φinv hG2 ∧ WPC rec @ s ; E1 {{ Φrx hG2 }} {{ Φcx hG2 }}))) -∗
      wpr s E1 e rec Φx Φinv Φrx.
  Proof.
    iIntros "Hwpc #Hidemp".
    iApply (
      idempotence_wpr nvm_crash_lang s E1 e rec _ _ _
                      (λ hGen, ∃ nvmD, ⌜hGen = nvmBase_generationGS (hGD := nvmD)⌝ ∗ Φcx nvmD)%I
                      with "[Hwpc] [Hidemp]"); first auto.
    { iApply (wpc_crash_mono with "[] Hwpc").
      iIntros "HΦcx". iExists _. destruct hG. by iFrame. }
    { iModIntro. iIntros (HG' σ_pre_crash g σ_post_crash Hcrash ns mj D κs ?) "(%nvmD & %eq & phi)".
      iMod (NC_alloc_strong) as (γcrash) "HNC".
      iSpecialize ("Hidemp" $! _ _ _ Hcrash with "phi").
      rewrite eq.
      iIntros "[interp extra] g !> !>".
      iMod (nvm_heap_reinit_alt _ _ _ _ γcrash _ Hcrash with "interp Hidemp")
        as (hnames) "(%cEq & map & interp' & idemp)".
      set (hGD' := hnames).
      iExists (nvmBase_generationGS (hGD := hGD')).
      iMod (global_state_interp_le (Λ := nvm_lang) _ _ () _ _ κs with "[$]") as "$";
        first (rewrite /step_count_next; simpl; lia).
      iModIntro.
      rewrite /state_interp //=.
      rewrite cEq.
      iFrame.
      iSplit.
      - iExists (hGD'). iDestruct "idemp" as "[$ _]". done.
      - iDestruct "idemp" as "[_ H]". iApply (wpc_mono with "H"); eauto. }
  Qed.

End wpr.
