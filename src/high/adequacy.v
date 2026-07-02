From iris.proofmode Require Import ltac_tactics.
From iris.algebra Require Import auth.
From iris_named_props Require Import named_props.

From self Require Import ipm_tactics extra view_slice encode_relation.
From self.high.lib Require Import increasing_map.
From self.program_logic Require Import recovery_adequacy.
From self.base Require Import wpr_lifting primitive_laws generational_resources cred_frag.
From self.high Require Import
  crash_weakestpre generational_resources state_interpretation protocol locations adequacy_alloc.
From self.high.modalities Require Import nextgen.
From self.nextgen Require Import nextgen_promises.

From self.high.resources Require Import
  gen_ghost_map gen_ghost_map_ofe gen_ghost_map_map gen_alocs gen_predicates auth_map_map.

(* I'm still not quite sure what's the proper way to handle these ghost resources,
 * For what I can see,
 * [invGpreS Σ]: the standard Iris invariant resources, which will be solved by [subG] eventually.
 * [ngInvG Σ Ω]: a list of resources created by Aina for invariants across generations. It's not really
 * being used in high-level Spirea, but they are tied in Perennial's adequacy proof so very difficult to remove.
 * [credit_preG Σ]: the resources for a second set of later credits, also not being used at all. *)
Class Perennial_preG Σ Ω := {
  P_invGpreS :: wsat.invGS.invGpreS Σ;
  P_preG_credit :: credit_preG Σ;
  P_ngInvG :: ngInvG Σ Ω;
}.

Definition Build_credit_G Σ `{!Perennial_preG Σ Ω} (cred_names: cr_names): creditGS Σ :=
  creditGS_update_pre Σ P_preG_credit cred_names.

Notation LocInfos H := (gmap loc (@LocInfo _ _ _ H)).

Section high_adequacy.
  (* Turns [gmap loc val] to [gmap loc history] *)
  Definition initial_heap (σ : gmap loc val) : store :=
    (λ (v : val), {[ 0 := Msg v ∅ ∅ ∅ ]} : history ) <$> σ.

  Lemma valid_heap_initial_heap σ : valid_heap (initial_heap σ).
  Proof.
    rewrite /valid_heap.
    intros ℓ hist.
    rewrite /initial_heap. simpl.
    intros (v & <- & ?)%lookup_fmap_Some.
    split. { done. }
    intros ?? (<- & <-)%lookup_singleton_Some.
    simpl.
    apply view_le_lookup.
    done.
  Qed.

  (* This lemma that builds [nvmHighGS], allocates the heap, and collects the individual location assertions. *)
  Lemma init_state_alloc `{baseG: !nvmBaseGS Σ Ω, preG: !nvmHighGpreS Σ Ω}
    (σ__at σ__na: gmap loc val) PV OCV OPV:
    dom σ__at ## dom σ__na →
    dom OCV = ∅ →
    dom (σ__at ∪ σ__na) ⊆ dom PV →
    ([∗ map] l ↦ h ∈ initial_heap (σ__at ∪ σ__na), l ↦fh h) -∗
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) -∗
    persisted PV ==∗
    ∃ (Hhigh: nvmHighGS Σ Ω), ∀ (locs__at locs__na : LocInfos Hhigh) (P: iProp Σ),
    ⌜ dom locs__at = dom σ__at ⌝ -∗ ⌜dom locs__na = dom σ__na ⌝ -∗
    (init_at_assertions σ__at locs__at ⊥ -∗
     init_na_assertions σ__na locs__na ⊥ -∗
     init_prots σ__at locs__at ⊥ ∗
     init_prots σ__na locs__na ⊥ ∗ P) ==∗
    extra_state_interp ∗ P.
  Proof.
    iIntros (Hdisj HOCVdom HPVdom) "fmapstos #OCV #rely #PV".
    rewrite /extra_state_interp /highExtraStateInterp.
    (* We choose to allocate in empty config, and use update to allocate new entries. *)
    iMod (gen_alocs_alloc ∅ OCV OPV  with "OCV rely") as (new_locs_name) "[newLocs newLocsFrags]".
    iMod (auth_map_map_alloc OCV OPV with "OCV rely") as (phy_history_name) "physHists".
    iMod (ghost_map_alloc (V := positive → option positive) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (bumpers_name) "[allBumpers _]"; first done.
    iMod (full_map_alloc bumpers_name OPV OCV ∅ with "[] OCV rely") as (abs_history_name) "[history _]".
    { by rewrite big_sepS_empty. }
    iMod (ghost_mapO_alloc (t := gen_predicates.drop_OCV) (V := predicateO Σ) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (full_predicates_name) "[full_predicates _]"; first done.
    iMod (ghost_mapO_alloc (t := gen_predicates.drop_OCV) (V := predicateO Σ) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (read_predicates_name) "[read_predicates _]"; first done.
    iMod (ghost_mapO_alloc (t := gen_predicates.drop_OCV) (V := predicateO Σ) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (pers_predicates_name) "[pers_predicates _]"; first done.
    iMod (ghost_map_alloc (V := extra.relation2 positive) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (preorders_name) "[allOrders _]"; first done.
    iMod (gen_alocs_alloc ∅ OCV OPV with "OCV rely") as (exclusive_locs_name) "[naLocs _]".
    iMod (gen_alocs_alloc ∅ OCV OPV with "OCV rely") as (shared_locs_name) "[atLocs _]".
    iMod (ghost_map_alloc (V := view.view) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (non_atomic_views_gname) "[naView _]"; first done.
    set (H := NvmHighG Σ Ω baseG preG full_predicates_name read_predicates_name pers_predicates_name
                abs_history_name phy_history_name non_atomic_views_gname
                preorders_name exclusive_locs_name shared_locs_name new_locs_name bumpers_name).
    iExists H.
    iIntros "!>" (?????) "exchange".

    iAssert (interp_pre ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅)
      with "[newLocs physHists allBumpers history full_predicates
             read_predicates pers_predicates allOrders naLocs atLocs naView]"
      as "interp".
    { rewrite /interp_pre.
      iFrame "physHists history full_predicates read_predicates pers_predicates
              allOrders naLocs atLocs naView allBumpers".
      iSplitR; first by rewrite big_sepM_empty.
      iSplitL "newLocs".
      { iExists OCV. iFrame "newLocs OCV". iPureIntro. set_solver. }
      iSplitR.
      { iExists OPV. iFrame "rely". }
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first by rewrite big_sepM_empty.
      iSplitR; first (iPureIntro; set_solver).
      iSplitR; first (iPureIntro; set_solver).
      iSplitR; first (iPureIntro; set_solver).
      iSplitR; first (iPureIntro; rewrite restrict_empty; apply map_Forall_empty).
      iSplitR; first by rewrite restrict_empty big_sepM_empty.
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first (iPureIntro; set_solver).
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first (iPureIntro; done).
      iSplitR; first (iPureIntro; done).
      iSplitR; first (iPureIntro; done).
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first (iPureIntro; apply map_Forall_empty).
      iSplitR; first by rewrite big_sepM2_empty.
      iSplitR; first by rewrite big_sepM_empty.
      by rewrite big_sepM2_empty. }

    iEval (rewrite /initial_heap big_sepM_fmap /=) in "fmapstos".
    rewrite big_sepM_union; last set_solver.
    iDestruct "fmapstos" as "[atfmapstos nafmapstos]".
    iMod (interp_pre_alloc_at_all OCV PV σ__at locs__at with "OCV PV interp atfmapstos") as
      "(interp & init_at)"; [ done | set_solver | done | ].
    iMod (interp_pre_alloc_na_all OCV PV σ__na locs__na with "OCV PV interp nafmapstos") as
      "(interp & init_na)"; [ done | set_solver | done | set_solver | set_solver | ].
    iDestruct ("exchange" with "init_at init_na") as "(init_at_prots & init_na_prots & P)".


    iEval (rewrite /init_prots monPred_at_big_sepM2) in "init_na_prots".
    iEval (rewrite /init_prots monPred_at_big_sepM2) in "init_at_prots".
    iDestruct (big_sepM2_union with "init_na_prots init_at_prots") as "init_prots".
    { apply map_disjoint_dom. set_solver. }
    iFrame "P".
    iModIntro.
    iApply (interp_intro with "interp").
    rewrite /init_prots -!map_fmap_union.
    iEval (setoid_rewrite monPred_at_sep) in "init_prots".
    iDestruct (big_sepM2_sep with "init_prots") as "[fulls perss]".
    iSplitL "fulls".
    - (* all_full_read_preds_hold *)
      rewrite big_sepM2_fmap.
      iApply (big_sepM2_impl with "fulls").
      iIntros "!>" (ℓ v li Hσℓ Hlocℓ) "Hp".
      rewrite /encoded_full_read_predicates_hold.
      iExists (encode_predicate (li.(li_prot).(p_full))),
                (encode_predicate (li.(li_prot).(p_read))), 0.
      iSplitPure. { rewrite lookup_fmap Hlocℓ //. }
      iSplitPure. { rewrite lookup_fmap Hlocℓ //. }
      iSplitPure. { rewrite lookup_fmap Hσℓ //. }
      rewrite !big_sepM2_singleton /=.
      rewrite right_id_L.
      rewrite lookup_singleton_ne //.
      destruct (decide _); last naive_solver.
      iPoseProof (no_buffer.into_no_buffer_at with "Hp") as "Hp".
      rewrite !lookup_fmap /=.
      assert (default ∅ ((λ _ : val, ∅) <$> σ__na !! ℓ) = (∅: view.view)) as -> by by destruct (σ__na !! ℓ).
      iApply (predicate_holds_phi_decode_2 with "[] Hp"); first apply decode_encode.
      done.
    - (* all_pers_preds_hold *)
      rewrite big_sepM2_fmap.
      iApply (big_sepM2_impl with "perss").
      iIntros "!>" (ℓ v li Hσℓ Hlocℓ) "Hp".
      rewrite /encoded_pers_predicate_holds.
      iExists (encode_predicate (li.(li_prot).(p_pers))), 0, 0,
                (encode li.(li_σ0)), (Msg v ∅ ∅ ∅).
      iSplitPure. { rewrite lookup_fmap Hlocℓ //. }
      iSplitPure. { rewrite lookup_fmap Hσℓ //. }
      iSplitPure. { rewrite lookup_singleton_eq //. }
      iSplitPure. { rewrite lookup_singleton_eq //. }
      iSplitPure. { rewrite /lookup_zero lookup_empty //. }
      rewrite lookup_empty /=.
      iSplitR "Hp"; first done.
      iPoseProof (objective_at with "Hp") as "Hp".
      iApply (predicate_holds_phi_decode_2 with "[] Hp"); first apply decode_encode.
      done.
      (* TODO: these are unused [ℓ] argument in [full_nobuf] or [pers_obj].
       * It's probably better to restate those classes.  *)
      Unshelve. all: done.
  Qed.

  (* FIXME: this should be treated by the [solve_inG] equivalent for [Ω]. *)
  Context (Build_nvmHighGpreS: ∀ Σ Ω (nvmBase: nvmBaseGS Σ Ω), nvmHighGpreS Σ Ω).

  (* [σ] is now the map of *initial values*; the store is [initial_heap σ].
   * The caller provides [valid_config] (the obligation that the protocol
   * predicates hold for the chosen initial states) and the program [Hwp] is
   * handed the per-location starting assertions [persist_lb ∗ ↦_AT]. *)
  Theorem high_recv_adequacy Σ Ω `{!nvmBaseGpreS Σ Ω, !Perennial_preG Σ Ω}
    s e r (σ__at σ__na : gmap loc val) (PV : view.view) g φ φr φinv Φinv :
    (dom σ__at ## dom σ__na) →
    dom (σ__at ∪ σ__na) ⊆ dom PV →
    (∀ (Hbase : nvmBaseGS Σ Ω) (Hhigh : nvmHighGS Σ Ω) (HP : PerennialG Σ),
       ⊢ |==> ∃ (locs__at locs__na : LocInfos Hhigh),
        ⌜ dom locs__at = dom σ__at ⌝ ∗ ⌜dom locs__na = dom σ__na ⌝ ∗
        (init_at_assertions σ__at locs__at ⊥ -∗
         init_na_assertions σ__na locs__na ⊥ -∗
         validV ∅ -∗
         init_prots σ__at locs__at ⊥ ∗
         init_prots σ__na locs__na ⊥ ∗
         ■ (∀ σ nt, state_interp σ nt -∗ |={⊤,∅}=> ⌜ φinv σ ⌝) ∗
         ■ (Φinv -∗ □ ∀ σ nt, state_interp σ nt -∗ |={⊤,∅}=> ⌜ φinv σ ⌝) ∗
         wpr s ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ v, ⌜φr v⌝))) →
        recv_adequate (CS := nvm_crash_lang) s e r (initial_heap (σ__at ∪ σ__na), PV) g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
  Proof using Build_nvmHighGpreS.
    intros Hdisj HPVdom Hwp.
    eapply (wp_recv_adequacy_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    iIntros (? ?) "".
    iStartProof.
    assert (∃ name_credit: cr_names, True) as [name_credit _].
    { by exists (Build_cr_names (xH) (xH)). }
    iPoseProof (nvm_heap_ctx_alloc (initial_heap (σ__at ∪ σ__na)) PV) as "heap";
      first apply valid_heap_initial_heap.
    iMod "heap" as (nvm_base_GS)
      "(interp & pts & #validV & crashedAt & #crashedOffset & #pers)".
    (* Only extract [rely]; discarding [crashed_at_both] avoids [iFrame] later *)
    (*    * pinning the goal's [nvm_heap_ctx] crash view to this [OCV] (≠ ∅). *)
    iDestruct "crashedAt" as (OV OCV OPV) "(%veq & _ & rely)".

    set (highPreG := Build_nvmHighGpreS _ _ nvm_base_GS).
    set (PG := Build_PerennialG Σ Hinv (Build_credit_G Σ name_credit)).

    iMod (init_state_alloc σ__at σ__na PV ∅ OPV
            with "pts crashedOffset rely pers")
      as (nvm_high_GS) "init".
    { set_solver. }
    { set_solver. }
    { set_solver. }
    iExists state_interp, global_state_interp, fork_post.
    iExists _, _.
    iExists (λ inv, Φinv)%I.

    iMod (Hwp nvm_base_GS nvm_high_GS PG) as (locs__at locs__na ? ?) "Hwp".
    iMod ("init" $! locs__at locs__na _ with "[//] [//] [Hwp]") as "Hwp".
    { iIntros "init_at init_na".
      iDestruct ("Hwp" with "init_at init_na [//]") as "($ & $ & Hwp)".
      iAccu. }
    iDestruct "Hwp" as "(extra & #H1 & #H2 & Hwp)".
    iModIntro.
    iSplitR.
    { iApply "H1". }
    iSplitR.
    { iApply "H2". }
    iFrame.
    iFrame "#".
    by iExistsN.
    Unshelve.
    refine 0.
  Qed.

  (* Similar to the [recv_adequate] in Perennial except that:
    1. The invariant is removed.
    2. We ignore the global state (which is [unit] for nvm_lang). *)
  Record recv_adequate (s : stuckness) (e1 r1 : thread_state) (σ1 : state nvm_lang)
        (φ φr: thread_val → state nvm_lang → Prop) := {
    recv_adequate_result_normal t2 σ2 v2 :
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1, ())) (* NOTE: The unit is the unused global state. *)
                    (thread_of_val v2 :: t2, (σ2, ())) Normal →
      φ v2 σ2;
    recv_adequate_result_crashed t2 σ2 v2 :
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1, ()))
                    (thread_of_val v2 :: t2, (σ2, ())) Crashed →
      φr v2 σ2;
    recv_adequate_not_stuck t2 σ2 e2 stat :
      s = NotStuck →
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1,())) (t2, (σ2,())) stat →
      e2 ∈ t2 → (is_Some (thread_to_val e2) ∨ reducible (Λ := nvm_lang) e2 σ2 ());
  }.

  Lemma adequacy_impl (s : stuckness) (e1 r1: thread_state) (σ1 : state nvm_lang)
        (φ φr: thread_val → state nvm_lang → Prop) :
    recovery_adequacy.recv_adequate (CS := nvm_crash_lang)
                                    s e1 r1 σ1 () (λ v σ _, φ v σ) (λ v σ _, φr v σ) (λ _ _, True) →
    recv_adequate s e1 r1 σ1 φ φr.
  Proof. intros [????]. split; try naive_solver. Qed.

  Theorem high_recv_adequacy_simple Σ Ω `{!nvmBaseGpreS Σ Ω, !Perennial_preG Σ Ω}
    s (e e_rec : expr) (σ__at σ__na : gmap loc val) (PV : view.view) (φ φr : val → Prop) :
    dom σ__at ## dom σ__na →
    dom (σ__at ∪ σ__na) ⊆ dom PV →
    (∀ (Hbase : nvmBaseGS Σ Ω) (Hhigh : nvmHighGS Σ Ω) (HP : PerennialG Σ),
       ⊢ |==> ∃ (locs__at locs__na : LocInfos Hhigh),
        ⌜ dom locs__at = dom σ__at ⌝ ∗ ⌜dom locs__na = dom σ__na ⌝ ∗
        (init_at_assertions σ__at locs__at ⊥ -∗
         init_na_assertions σ__na locs__na ⊥ -∗
         validV ∅ -∗
         init_prots σ__at locs__at ⊥ ∗
         init_prots σ__na locs__na ⊥ ∗
         wpr s ⊤ (e `at` ⊥) (e_rec `at` ⊥)
           (λ v, ⌜ φ v.(val_val) ⌝)%I True%I (λ v, ⌜ φr v.(val_val) ⌝)%I)) →
    recv_adequate s (e `at` ⊥) (e_rec `at` ⊥) (initial_heap (σ__at ∪ σ__na), PV)
      (λ v _, φ v.(val_val)) (λ v _, φr v.(val_val)).
  Proof using Build_nvmHighGpreS.
    intros Hdisj HPVdom Hwp.
    apply adequacy_impl.
    eapply (high_recv_adequacy Σ Ω); [ set_solver | set_solver | ].
    intros.
    specialize (Hwp Hbase Hhigh HP).
    iMod Hwp as (locs__at locs__na) "($ & $ & Hwp)".
    iIntros "!> init_at ini_na validV".
    iDestruct ("Hwp" with "[$] [$] [$]") as "($ & $ & $)".
    iSplit.
    - iIntros "!>" (? ?) "_". iApply fupd_mask_intro; naive_solver.
    - iIntros "!> ? !>". iIntros (? ?) "?".
      iApply fupd_mask_intro; naive_solver.
  Qed.
End high_adequacy.
