From stdpp Require Import numbers.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth dfrac.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
(* From Perennial.goose_lang Require Import proofmode notation. *)
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
(* From Perennial.goose_lang Require Import crash_modality typing adequacy lang. *)

From self Require Import extra ipm_tactics.
From self.lang Require Import lang.
From self.base Require Import primitive_laws post_crash_modality.

Set Default Proof Using "Type".

Definition nvm_get_heap_names {V Σ} (hG : gen_heapGS loc V Σ) : nvm_heap_names :=
  {| name_gen_heap := gen_heap_name hG ;
     name_gen_meta := gen_meta_name hG |}.

(* Definition nvm_heap_update {Σ} (h : gen_heapGS loc history Σ) (names : nvm_heap_names) := *)
(*   {| gen_heap_inG := gen_heap_inG; *)
(*      gen_heap_name := names.(name_gen_heap); *)
(*      gen_meta_name := names.(name_gen_meta) |}. *)

Definition nvm_base_get_names Σ (hG : nvmBaseDeltaG Σ) : nvm_base_names :=
  nvm_base_names'.

Canonical Structure nvm_base_namesO := leibnizO nvm_base_names.

(** Given an [hG : nvmBaseFixedG Σ, !extraStateInterp Σ, nvmBaseDeltaG Σ], update the fields per the information in the
rest of the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG].
TOOD: See if we can get rid of the [invGS] and [crashGS] argument.
 *)

(* Lemma heap_update_eq {Σ} heapGS' (heapGS : gen_heapGS loc history Σ) : *)
(*   (@nvm_heap_update Σ heapGS' (@nvm_get_heap_names (@gmap nat nat_eq_dec nat_countable message) Σ heapGS)) *)
(*     = *)
(*   heapGS. *)
(* Proof. *)
(*   destruct heapGS'. *)
(*   destruct heapGS. *)
(*   rewrite /nvm_get_heap_names. simpl. *)
(*   rewrite /nvm_heap_update. simpl. *)
(*   f_equal. *)
(* Abort. *)
(* (*   gen_heapGpreS *) *)
(* (*   auto. *) *)
(* (* Qed. *) *)

(* Lemma nvm_update_id {Σ} (hGD : nvmBaseDeltaG Σ) (hG : nvmBaseFixedG Σ) : *)
(*   hGD = {| nvm_base_crashGS := nvm_base_crashGS; *)
(*            nvm_base_names' := *)
(*              nvm_base_get_names Σ {| nvm_base_inG := hG; nvmBaseDeltaG' := hGD |} *)
(*         |}. *)
(* Proof. destruct hGD. done. Qed. *)

Program Global Instance nvmBaseG_perennialG `{!nvmBaseFixedG Σ, !extraStateInterp Σ} :
  perennialG nvm_lang nvm_crash_lang nvm_base_namesO Σ := {
  perennial_irisG :=
    λ Hcrash hnames,
      nvmBaseG_irisGS (hGD := MkNvmBaseDeltaG _ Hcrash (@pbundleT _ _ hnames));
  perennial_crashG := λ _ _, eq_refl;
  perennial_num_laters_per_step := (λ n, 3 ^ (n + 1))%nat;
  perennial_step_count_next := (λ n, 10 * (n + 1))%nat;
}.
Next Obligation. eauto. Qed.
Next Obligation. eauto. Qed.
Next Obligation. eauto. Qed.

Definition wpr `{nvmBaseFixedG Σ, !extraStateInterp Σ, hG : nvmBaseDeltaG Σ} `{hC : !crashGS Σ}
           (s : stuckness) (k : nat) (E : coPset)
           (e : thread_state) (recv : thread_state) (Φ : thread_val → iProp Σ)
           (Φinv : nvmBaseDeltaG Σ → iProp Σ)
           (Φr : nvmBaseDeltaG Σ → thread_val → iProp Σ) :=
  wpr s k hC ({| pbundleT := nvm_base_get_names Σ _ |}) E e recv
              Φ
              (λ Hc names, Φinv (MkNvmBaseDeltaG _ Hc (@pbundleT _ _ names)))
              (λ Hc names v, Φr (MkNvmBaseDeltaG _ Hc (@pbundleT _ _ names)) v).

Section wpr.
  Context {Σ : gFunctors}.
  Implicit Types s : stuckness.
  Implicit Types k : nat.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types Φc : iProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Lemma wpr_strong_mono `{hG : !nvmBaseFixedG Σ, !extraStateInterp Σ, nvmBaseDeltaG Σ}
        s k E e rec Φ Ψ Φinv Ψinv Φr Ψr :
    wpr s k E e rec Φ Φinv Φr -∗
    (∀ v, Φ v ==∗ Ψ v) ∧
    ((∀ hG, Φinv hG -∗ Ψinv hG) ∧ (∀ hG v, Φr hG v ==∗ Ψr hG v)) -∗
    wpr s k E e rec Ψ Ψinv Ψr.
  Proof.
    rewrite /wpr. iIntros "Hwpr Himpl".
    iApply (wpr_strong_mono with "Hwpr [Himpl]").
    repeat iSplit.
    - by iDestruct "Himpl" as "($&_)".
    - iIntros.
      iDestruct "Himpl" as "(_&H)".
      iIntros. by iApply "H".
    - iIntros.
      iDestruct "Himpl" as "(_&H)".
      iIntros. by iApply "H".
  Qed.

  Lemma store_inv_cut `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ} store p :
    consistent_cut p store →
    valid_heap store → valid_heap (slice_of_store p store).
  Proof.
    rewrite /valid_heap /valid_heap_lub.
    intros cut val.
    intros ℓ h look'.
    rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'.
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

  Definition persist_auth `{nvmBaseFixedG, hGD : nvmBaseDeltaG Σ}
             (σ : mem_config) :=
    own persist_view_name (● σ.2).

  Lemma nvm_heap_reinit (hG : nvmBaseFixedG Σ) (hGD : nvmBaseDeltaG Σ) σ p p'
        (Hcrash : crashGS Σ) :
    (* The first two assumptions are the content of [crash_step σ σ'] *)
    p ⊑ p' →
    consistent_cut p' σ →
    valid_heap σ →
    ⊢ gen_heap_interp (hG := _) σ -∗
      persist_auth (σ, p)
      ==∗
      ∃ names : nvm_base_names,
        validV (hGD := MkNvmBaseDeltaG Σ Hcrash names) ∅ ∗
        post_crash_map σ _ (MkNvmBaseDeltaG Σ Hcrash names) ∗
        nvm_heap_ctx (hGD := MkNvmBaseDeltaG Σ Hcrash names)
                     (slice_of_store p' σ, view_to_zero p') ∗
        persisted_impl _ (MkNvmBaseDeltaG _ Hcrash names) ∗
        own (@crashed_at_view_name (names)) (to_agree p' : agreeR viewO).
  Proof using Σ.
    iIntros (pIncl cut invs) "heapIntrp pers".
    rewrite /nvm_heap_ctx. simpl.
    (* Allocate a new heap at a _new_ ghost name. *)
    iMod (gen_heap_init_names (slice_of_store p' σ)) as (γh γm) "(heapNew & ptsMap & _)".
    (* We persist/freeze the old persist view. *)
    iMod (own_update with "pers") as "pers".
    { apply auth_update_auth_persist. }
    iDestruct "pers" as "#oldPers".
    (* Allocate a new persist view. *)
    iMod (own_alloc (● (view_to_zero p') ⋅ ◯ (view_to_zero p'))) as (persistG) "[pers #persFrag]".
    { apply auth_both_valid_2; [apply view_valid|done]. }
    (* Allocate the store view at a _new_ ghost name. *)
    iMod (own_alloc (● max_view (slice_of_store p' σ) ⋅ ◯ ∅)) as (storeG) "[store fragStore]".
    { apply auth_both_valid_2; [apply view_valid | apply: ucmra_unit_least]. }
    (* Allocate the crashed at view at a _new_ ghost name. *)
    iMod (own_alloc (to_agree p' : agreeR viewO)) as (crashedAtG) "#crashed".
    { done. }
    iModIntro.
    iExists {| heap_names_name := Build_nvm_heap_names γh γm;
               store_view_name := storeG;
               persist_view_name := persistG;
               crashed_at_view_name := crashedAtG |}.
    rewrite /crashed_at_view_name. simpl.
    iFrame.
    iFrame "crashed".
    (* We show the ghost crash relation. *)
    iSplitL "ptsMap heapIntrp".
    { rewrite /post_crash_map.
      iSplitL "heapIntrp".
      { iIntros (???) "pts".
        iApply (gen_heap_valid with "heapIntrp pts"). }
      iDestruct (big_sepM_impl_strong _ _ _ σ with "ptsMap []") as "[$ _]".
      iModIntro.
      iIntros (ℓ hist) "pts". iIntros (look).
      (* Note: The first value below is just a fancy way of writing [0]. *)
      iExists (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)), 1%Qc.
      rewrite if_non_zero_1. simpl. rewrite if_non_zero_0. simpl.
      iSplit; first done. iSplit; last done.
      iExists _. iFrame "crashed".
      destruct (slice_of_store p' σ !! ℓ) as [?|] eqn:look'; last first.
      * iRight. iPureIntro.
        eapply consistent_cut_lookup_slice; done.
      * iLeft.
        rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'.
        apply map_lookup_zip_with_Some in look'.
        destruct look' as ([t] & ? & ? & p'Look & ?).
        rewrite /consistent_cut in cut.
        pose proof (map_Forall_lookup_1 _ _ _ _ cut p'Look) as (? & ? & ? & ? & map).
        simplify_eq.
        iExists _, _.
        iSplit; first done.
        rewrite H2.
        rewrite map_fmap_singleton.
        iFrame "pts".
        iPureGoal; first done.
        iPureIntro.
        eapply (map_Forall_lookup_1 _ _ _ _ map).
        rewrite /cut_history.
        apply map_filter_lookup_Some_2; [done| reflexivity]. }
    iSplit.
    * simpl.
      iSplit. { iPureIntro. apply store_inv_cut; done. }
      iExists p'. iFrame "crashed".
      (* TODO: Factor this out into a lemma (needs [cut] only). *)
      apply consistent_cut_subseteq_dom in cut.
      rewrite /slice_of_store /slice_of_hist map_fmap_zip_with.
      rewrite map_zip_with_dom_eq_l; try done.
    * iModIntro.
      iIntros (V) "pers".
      rewrite /persisted.
      iDestruct (persisted_auth_included with "oldPers pers") as %incl.
      assert (V ⊑ p') as incl'. { etrans; done. }
      iSplit.
      { edestruct (view_to_zero_mono) as [? ->]; first apply incl'.
        iDestruct "persFrag" as "[$ _]". }
      iExists p'. iFrame "#%".
  Qed.

  Lemma nvm_heap_reinit_alt (hG : nvmBaseFixedG Σ) (hGD : nvmBaseDeltaG Σ) σ σ'
        (Hcrash : crashGS Σ) Pg :
    crash_step σ σ' →
    ⊢ nvm_heap_ctx σ -∗
      post_crash Pg ==∗
      ∃ names : nvm_base_names,
        post_crash_map σ.1 _ (MkNvmBaseDeltaG Σ Hcrash names) ∗
        nvm_heap_ctx (hGD := MkNvmBaseDeltaG Σ Hcrash names) σ' ∗
        Pg (MkNvmBaseDeltaG Σ Hcrash names).
  Proof.
    iIntros ([store p p' pIncl cut]).
    iIntros "(heap & authStor & %inv & pers & recov) Pg".
    iMod (nvm_heap_reinit _ _ _ _ _ Hcrash with "heap pers")
      as (hnames) "(_ & map & interp' & #persImpl & rec)"; try done.
    rewrite /post_crash.
    set newBundle : nvmBaseDeltaG Σ :=
      {| nvm_base_crashGS := Hcrash; nvm_base_names' := hnames |}.
    iSpecialize ("Pg" $! (store, p') newBundle).
    rewrite /newBundle.
    iDestruct ("Pg" with "persImpl map") as "(map & Pg)".
    iExists _. iFrame.
    done.
  Qed.

  Lemma idempotence_wpr `{!ffi_interp_adequacy}
        `{hG : nvmBaseFixedG Σ, !extraStateInterp Σ, hGD : nvmBaseDeltaG Σ} s k E1 e rec Φx Φinv Φrx Φcx :
    ⊢ WPC e @ s ; k ; E1 {{ Φx }} {{ Φcx hGD }} -∗
    (□ ∀ (hG1 : nvmBaseDeltaG Σ)
         (* (Hpf : @nvmBaseG_invGS Σ (@nvm_base_inG _ hG) = *)
         (*          @nvmBaseG_invGS Σ (@nvm_base_inG _ hG1)) *) σ σ'
         (HC : crash_prim_step (nvm_crash_lang) σ σ'),
         Φcx hG1 -∗ ▷ post_crash (λ hG2, (Φinv hG2 ∧ WPC rec @ s ; k; E1 {{ Φrx hG2 }} {{ Φcx hG2 }}))) -∗
      wpr s k E1 e rec Φx Φinv Φrx.
  Proof.
    iIntros "Hwpc #Hidemp".
    iApply (idempotence_wpr s k E1 e rec _ _ _
                            (λ Hc names, Φcx (MkNvmBaseDeltaG _ Hc (@pbundleT _ _ names)))
                                                      with "[Hwpc] [Hidemp]"); first auto.
    { destruct hGD. iFrame. }
    { iModIntro. iIntros (? [names] σ_pre_crash g σ_post_crash Hcrash ns mj D κs ?) "H".
      iSpecialize ("Hidemp" $! (MkNvmBaseDeltaG _ _ names) with "[//] H").
      iIntros "[interp extra] g !> !>".
      iIntros (Hc' ?) "HNC".
      iMod (nvm_heap_reinit_alt _ _ _ _ Hc' _ Hcrash with "interp Hidemp") as (hnames) "(map & interp' & idemp)".
      iExists {| pbundleT := hnames |}, (reflexivity _), (reflexivity _).
      iMod (global_state_interp_le (Λ := nvm_lang) _ _ () _ _ κs with "[$]") as "$";
        first (simpl; lia).
      iModIntro.
      rewrite /state_interp //=.
      rewrite /nvm_heap_ctx.
      iFrame. }
  Qed.

End wpr.
