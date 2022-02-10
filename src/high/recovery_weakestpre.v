(* Implementation of the recovery weakest precondition for NVMLang. *)

From Coq Require Import QArith Qcanon.

From stdpp Require Import sets.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gset.
From iris_named_props Require Import named_props.
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require Import recovery_weakestpre.
From Perennial.program_logic Require Import recovery_adequacy.

From self.algebra Require Import ghost_map.
From self Require Import view extra ipm_tactics if_non_zero.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop resources crash_weakestpre
     post_crash_modality or_lost.

Set Default Proof Using "Type".

(* Notation pbundleG := recovery_weakestpre.pbundleG. *)

(* Notation perennialG := recovery_weakestpre.perennialG. *)

Definition get_crashG {Σ} (hD : nvmDeltaG Σ) :=
  @nvm_base_crashGS Σ (@nvm_delta_base Σ hD).

(** The recovery WP is parameterized by two predicates: [Φ], the postcondition
 for normal non-crashing execution and [Φr], the postcondition satisfied upon
 termination after one ore more crashes.

 This definition of the recovery weakest precondition is defined on top of our
 crash weakest precondition following the same pattern that is used in Perennial
 to define Perennial's wpr on top of Perennial's wpc. *)
Definition wpr_pre `{nvmFixedG Σ} (s : stuckness)
    (wpr : nvmDeltaG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (nvmDeltaG Σ -d> val -d> dPropO Σ) -d> dPropO Σ) :
  nvmDeltaG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (nvmDeltaG Σ -d> val -d> dPropO Σ) -d> dPropO Σ :=
  λ hGD E e e_rec Φ Φr,
  (WPC e @ s ; E
    {{ Φ }}
    {{ ∀ σ mj D σ' (HC : crash_prim_step nvm_crash_lang σ σ') ns n, (* The [n] here actually doesn't matter. *)
      ⎡ (* interp -∗ *)
        state_interp σ n -∗
        global_state_interp (Λ := nvm_lang) () ns mj D []
      ={E}=∗ ▷ ∀ (Hc1 : crashGS Σ) q, NC q ={E}=∗
        ∃ (hD' : nvmDeltaG Σ), (* Maybe state that [hD'] contains [Hc1] *)
          ⌜ Hc1 = get_crashG hD' ⌝ ∗
          (* let hG := (nvm_update Σ hG _ Hc1 names) in *)
          (* interp ∗ *)
          state_interp σ' 0 ∗
          global_state_interp (Λ := nvm_lang) () (step_count_next ns) mj D [] ∗
          validV ∅ ∗
          (monPred_at (wpr hD' E e_rec e_rec (λ v, Φr hD' v) Φr) (∅, ∅, ∅)) ∗
          NC q ⎤
    }})%I.

Local Instance wpr_pre_contractive `{nvmFixedG Σ} s : Contractive (wpr_pre s).
Proof.
  rewrite /wpr_pre. intros ??? Hwp ??????.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{nvmFixedG Σ} (s : stuckness) := fixpoint (wpr_pre s).
Definition wpr_aux `{nvmFixedG Σ} : seal (@wpr_def Σ). by eexists. Qed.
Definition wpr' `{nvmFixedG Σ} := (wpr_aux).(unseal).
Definition wpr_eq `{nvmFixedG Σ} : wpr' = @wpr_def _ := wpr_aux.(seal_eq).
(* Lemma wpr_eq `{nvmFixedG Σ} : @wpr' Σ = @wpr_def Σ. *)
(* Proof. rewrite /wpr'. rewrite wpr_aux.(seal_eq). done. Qed. *)

Lemma wpr_unfold `{nvmFixedG Σ, hGD : nvmDeltaG Σ} st E e rec Φ Φc :
  wpr' _ st hGD E e rec Φ Φc ⊣⊢ wpr_pre st (wpr' _ st) hGD E e rec Φ Φc.
Proof.
  rewrite wpr_eq. rewrite /wpr_def.
  apply (fixpoint_unfold (wpr_pre st)).
Qed.

(** If we have a map of points-to predicates prior to a crash and know what view
we crashed at, then we can get a map of points-to predicates for the new
heap. *)
Lemma map_points_to_to_new `{nvmBaseFixedG Σ} logHists store CV (hG hG' : nvmBaseDeltaG Σ) :
  consistent_cut CV store →
  own (@crashed_at_view_name (@nvm_base_names' _ hG')) (to_agree CV) -∗
  base.post_crash_modality.post_crash_mapsto_map store hG hG' -∗
  ([∗ map] ℓ ↦ hist ∈ logHists, let hG := hG in ℓ ↦h hist) -∗
  ([∗ map] ℓ ↦ hist ∈ (slice_of_store CV logHists), let hG := hG' in ℓ ↦h hist).
Proof.
  iIntros (cut) "#rec [impl map] pts".
  iAssert (⌜logHists ⊆ store⌝)%I as %sub.
  { rewrite map_subseteq_spec.
    iIntros (ℓ msg look).
    iApply "impl".
    iApply (big_sepM_lookup with "pts"); first done. }
  iAssert (⌜dom (gset _) logHists ⊆ dom _ store⌝)%I as %histSubStore.
  { rewrite elem_of_subseteq. iIntros (ℓ).
    rewrite !elem_of_dom. iIntros ([hist look]).
    iDestruct (big_sepM_lookup with "pts") as "pts"; first apply look.
    iExists _. iApply "impl"; done. }
  (* Throw away the points-to predicates that did not survive the crash. *)
  iDestruct (big_sepM_subseteq with "map") as "map".
  { apply sub. }
  iDestruct (big_sepM_subseteq with "pts") as "pts".
  { apply (restrict_subseteq (dom (gset _) CV)). }
  iDestruct (big_sepM_subseteq with "map") as "map".
  { apply (restrict_subseteq (dom (gset _) CV)). }
  iDestruct (big_sepM_sep_2 with "pts map") as "map".
  iDestruct (big_sepM_impl_dom_subseteq _ _ _ (slice_of_store _ _) with "map []") as "[$ _]".
  { rewrite /slice_of_store /slice_of_hist.
    rewrite dom_fmap.
    rewrite !dom_map_zip_with.
    rewrite restrict_dom.
    set_solver. }
  iIntros "!>" (ℓ hist hy look look') "[pts disj]".

  iDestruct (soft_disj_exchange_l with "[] disj pts") as "[disj right]".
  { iIntros "!>" (?) "H".
    setoid_rewrite <- dfrac_valid_own.
    iApply (mapsto_valid with "H"). }

  iDestruct "right" as (CV') "[crashed [right | %left]]";
  iDestruct (crashed_at_agree with "crashed rec") as %->.
  2: {
    iExFalso.
    rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'.
    apply elem_of_dom_2 in look'.
    setoid_rewrite dom_map_zip_with in look'.
    setoid_rewrite elem_of_intersection in look'.
    destruct look' as [look' _].
    apply elem_of_dom in look'.
    destruct look' as [[t] ?].
    simplify_eq. }
  iDestruct "right" as (t msg look'' lookm ?) "newPts".
  apply restrict_lookup_Some in look.
  destruct look as [lookStore ?].
  rewrite /slice_of_store /slice_of_hist map_fmap_zip_with in look'.
  apply map_lookup_zip_with_Some in look'.
  destruct look' as ([t'] & physHist & eq & ?look & ?look).

  setoid_rewrite map_subseteq_spec in sub.
  simplify_eq.
  rewrite lookm.
  rewrite map_fmap_singleton.
  iFrame "newPts".
Qed.

Definition wpr `{nvmFixedG Σ, nvmDeltaG Σ} s := wpr' _ s _.

Lemma view_to_zero_lookup V ℓ x :
  V !! ℓ = Some x → (view_to_zero V) !! ℓ = Some (MaxNat 0).
Proof.
  intros look. rewrite /view_to_zero. rewrite lookup_fmap. rewrite look. done.
Qed.

Lemma or_lost_post_crash_full `{nvmBaseFixedG Σ, hG : nvmBaseDeltaG Σ} CV :
  crashed_at CV -∗
  persisted (view_to_zero CV) -∗
  ∀ ℓ P, (∀ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ -∗ P t) -∗ or_lost_post_crash ℓ P.
Proof.
  iIntros "crash pers" (ℓ P) "impl".
  iExists _. iFrame "crash".
  destruct (CV !! ℓ) as [[m]|] eqn:lookP'; last naive_solver.
  iLeft.
  iExists _. iSplit; first done.
  iDestruct (persisted_persisted_loc with "pers") as "$".
  { eapply view_to_zero_lookup. done. }
  iApply "impl". done.
Qed.

Section wpr.
  Context `{nvmFixedG Σ}.

  (* Computes the new abstract history based on the old history, the crash
  view, and the bumpers. *)
  Definition new_abs_hist (abs_hists : gmap loc (gmap time positive))
             (CV : view) (bumpers : gmap loc (positive → option positive))
    : gmap loc (gmap time positive) :=
    map_zip_with
      (λ (hist : gmap time positive) bumper,
        (default (1%positive) ∘ bumper) <$> hist)
      (slice_of_hist CV abs_hists)
      bumpers.

  Lemma new_abs_hist_dom abs_hists CV bumpers :
    dom (gset loc) (new_abs_hist abs_hists CV bumpers) =
    (dom _ abs_hists ∩ dom _ CV ∩ dom _ bumpers).
  Proof. rewrite 2!dom_map_zip_with_L. set_solver. Qed.

  Lemma new_abs_hist_lookup_simpl_inv abs_hists CV bumpers ℓ hist :
    (new_abs_hist abs_hists CV bumpers) !! ℓ = Some hist →
    hist = ∅ ∨ ∃ s, hist = {[ 0 := s ]}.
  Proof.
    rewrite /new_abs_hist /slice_of_hist.
    do 2 setoid_rewrite map_lookup_zip_with_Some.
    intros ([?] & ? & -> & ([t] & hist' & -> & ? & ?) & ?).
    destruct (hist' !! t).
    - right. eexists _. apply map_fmap_singleton.
    - left. apply fmap_empty.
  Qed.

  Lemma new_abs_hist_lookup CV ℓ t abs_hists hist bumpers bumper :
    map_Forall (λ _ e, is_Some (bumper e)) hist →
    valid_slice CV abs_hists →
    CV !! ℓ = Some (MaxNat t) →
    abs_hists !! ℓ = Some hist →
    bumpers !! ℓ = Some bumper →
    ∃ s' e,
      hist !! t = Some s' ∧
      bumper s' = Some e ∧
      new_abs_hist abs_hists CV bumpers !! ℓ = Some {[ 0 := e ]}.
  Proof.
    intros bumperToValid val CVlook absHistLook bumpersLook.
    eapply map_Forall_lookup_1 in val.
    2: { apply map_lookup_zip_with_Some. eexists _, _. done. }
    destruct val as [s histLook].
    eapply map_Forall_lookup_1 in bumperToValid as [bumped eq]; last done.
    exists s, bumped.
    split_and!; try done.
    rewrite /new_abs_hist.
    apply map_lookup_zip_with_Some.
    eexists {[0 := s]}, _.
    simpl.
    split_and!; try done.
    { rewrite map_fmap_singleton. simpl. rewrite eq. done. }
    eapply slice_of_hist_lookup_Some; done.
  Qed.

  Lemma holo (CV : view) ℓ t (σ : store) :
    CV !! ℓ = Some $ MaxNat t →
    consistent_cut CV σ →
    ∃ (msg : message) (hist : history),
      σ !! ℓ = Some hist ∧
      hist !! t = Some msg ∧
      slice_of_store CV σ !! ℓ = Some {[ 0 := discard_msg_views msg ]}.
  Proof.
  Admitted.

  (* FIXME: This lemmas needs more assumptions. *)
  Lemma new_abs_hist_lookup_inv abs_hists CV bumpers ℓ hist :
    (new_abs_hist abs_hists CV bumpers) !! ℓ = Some hist →
    ∃ t s s' bumper abs_hist,
      CV !! ℓ = Some (MaxNat t) ∧
      abs_hists !! ℓ = Some abs_hist ∧
      abs_hist !! t = Some s ∧
      bumpers !! ℓ = Some bumper ∧
      bumper s = Some s' ∧
      hist = {[ 0 := s' ]}.
  Proof.
    rewrite /new_abs_hist.
    rewrite map_lookup_zip_with_Some.
    intros (newHist & bumper & hi & ho & hip).
    (* slice_of_hist lemma *)
    rewrite /slice_of_hist in ho.
    setoid_rewrite map_lookup_zip_with_Some in ho.
    destruct ho as ([t] & ? & ? & ? & ?).
  Admitted.

  (* TODO: Could maybe be upstreamed. *)
  Lemma map_subseteq_lookup_eq (m1 m2 : store) v1 v2 k :
    m1 ⊆ m2 → m1 !! k = Some v1 → m2 !! k = Some v2 → v1 = v2.
  Proof. rewrite map_subseteq_spec. naive_solver. Qed.

  (* TODO: Could maybe be upstreamed. *)
  Lemma map_Forall_subseteq `{Countable K} {B} P (n m : gmap K B) :
    m ⊆ n →
    map_Forall P n →
    map_Forall P m.
  Proof. rewrite map_subseteq_spec. rewrite /map_Forall. naive_solver. Qed.

  (** The invariant for shared locations holds trivially for all locations after
  a crash. *)
  Lemma shared_locs_inv_slice_of_store (shared : gset loc) CV phys_hists :
    shared_locs_inv (restrict shared (slice_of_store CV phys_hists)).
  Proof.
    eapply map_Forall_subseteq. { apply restrict_subseteq. }
    intros ℓ hist look. intros t msg histLook.
    epose proof (slice_of_store_lookup_Some _ _ _ _ _ _ look histLook)
      as (? & ? & [????] & ? & ? & ? & ? & -> & ?).
    naive_solver.
  Qed.

  (* Given the state interpretations _before_ a crash we reestablish the
  interpretations _after_ a crash. *)
  Lemma nvm_reinit (hGD : nvmDeltaG Σ) n Pg tv σ σ' (Hinv : invGS Σ) (Hcrash : crashGS Σ) :
    crash_step σ σ' →
    ⊢ (* interp -∗ *)
      state_interp σ n -∗
      (post_crash Pg) tv ==∗
      ∃ (hD' : nvmDeltaG Σ),
        (* let hG := nvm_update Σ hG' Hinv Hcrash names in *)
        ⌜ Hcrash = get_crashG hD' ⌝ ∗
        validV ∅ ∗
        interp (hGD := hD') ∗
        nvm_heap_ctx (hG := _) σ' ∗
        Pg hD' (∅, ∅, ∅).
  Proof.
    iIntros ([store PV CV pIncl cut]).
    iIntros "[H1 H2] Pg".
    iNamed "H1". iNamed "H2".
    (* iIntros "(heap & authStor & %inv & pers & recov) Pg". *)

    (* Our [phys_hist] may contain only a subset of all the locations in
    [store]. But, those that are in [phys_hist] agree with what is in
    [store]. *)
    iAssert (⌜phys_hists ⊆ store⌝)%I as %physHistsSubStore.
    { rewrite map_subseteq_spec.
      iIntros (ℓ hist look).
      iDestruct (big_sepM_lookup with "ptsMap") as "pts"; first eassumption.
      iApply (gen_heap_valid with "Hσ pts"). }

    (* We need to first re-create the ghost state for the base
    interpretation. *)
    iMod (nvm_heap_reinit _ _ _ _ _ Hcrash with "Hσ Hpers")
      as (baseNames hGD') "(% & valView & map' & baseInterp & #persImpl & #pers &
                            #newCrashedAt)";
      try done.

    iDestruct (or_lost_post_crash_full with "newCrashedAt pers") as "#orLost".

    iDestruct (big_sepM2_dom with "ordered") as %domHistsEqOrders.
    iDestruct (big_sepM2_dom with "bumpMono") as %domOrdersEqBumpers.
    iDestruct (big_sepM2_dom with "bumperSome") as %domHistsEqBumpers.
    iDestruct (big_sepM2_dom with "predPostCrash") as %domPredsEqBumpers.
    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistsEqAbsHists.

    (* A name for the set of recovered locations. Per the above equalities this
    set could be expressed in a number of other ways (for instance by using
    [phys_hists] instead of [abs_hists].)*)
    set (recLocs := dom (gset _) CV ∩ dom _ abs_hists).

    set (newAbsHists := new_abs_hist abs_hists CV bumpers).
    iMod (own_full_history_alloc newAbsHists)
      as (new_abs_history_name new_know_abs_history_name)
           "(hists' & #histFrags & knowHistories)".
    assert (recLocs = (dom (gset _) newAbsHists)) as domNewAbsHists.
    { rewrite new_abs_hist_dom.
      rewrite -domHistsEqBumpers.
      set_solver. }
    (* Allocate new ghost state for the logical histories. *)
    rewrite /interp.

    (* We freeze/persist the old authorative resource algebra. *)
    iMod (ghost_map_auth_persist with "allOrders") as "#allOrders".
    iMod (own_update with "atLocs") as "atLocs".
    { apply auth_update_auth_persist. }
    iDestruct "atLocs" as "#atLocs".
    iMod (own_update with "naLocs") as "naLocs".
    { apply auth_update_auth_persist. }
    iDestruct "naLocs" as "#naLocs".
    iMod (own_all_bumpers_persist with "allBumpers") as "#oldBumpers".
    iMod (own_update with "predicates") as "allPredicates".
    { apply auth_update_auth_persist. }
    iDestruct "allPredicates" as "#allPredicates".
    iDestruct "history" as "[fullHist1 fullHist2]".
    iMod (ghost_map_auth_persist with "fullHist1") as "#oldFullHist1".
    iMod (own_update with "fullHist2") as "oldFullHist2".
    { apply auth_update_auth_persist. }
    iDestruct "oldFullHist2" as "#oldFullHist2".
    (* Ghost state for physical history. *)
    iMod (own_update with "physHist") as "oldPhysHist".
    { apply auth_update_auth_persist. }
    iDestruct "oldPhysHist" as "#oldPhysHist".
    iMod (ghost_map_auth_persist with "naView") as "#oldNaView".

    (* Some locations may be lost after a crash. For these we need to
    forget/throw away the predicate and preorder that was choosen for the
    location. *)
    set newOrders := restrict recLocs orders.
    iMod (own_all_preorders_gname_alloc newOrders)
      as (new_orders_name) "[newOrders #fragOrders]".

    set newPreds := restrict recLocs predicates.
    iMod (know_predicates_alloc newPreds) as
      (new_predicates_name) "[newPreds #newPredsFrag]".

    set newSharedLocs := recLocs ∩ at_locs.
    iMod (own_alloc (● (newSharedLocs : gsetUR _) ⋅ ◯ _))
      as (new_shared_locs_name) "[newSharedLocs atLocsFrag]".
    { apply auth_both_valid. done. }
    iDestruct "atLocsFrag" as "#atLocsFrag".

    set newNaLocs := recLocs ∩ na_locs.
    iMod (own_alloc (● (newNaLocs : gsetUR _) ⋅ ◯ _))
      as (new_exclusive_locs_name) "[newNaLocs naLocsFrag]".
    { apply auth_both_valid. done. }
    iDestruct "naLocsFrag" as "#naLocsFrag".

    set (newNaViews := gset_to_gmap (∅ : view) newNaLocs).
    iMod (ghost_map_alloc newNaViews) as (new_na_views_name) "[naView naViewPts]".

    (* Allocate the new map of bumpers. *)
    set newBumpers := restrict recLocs bumpers.
    iMod (own_all_bumpers_alloc newBumpers)
         as (new_bumpers_name) "[newBumpers #bumpersFrag]".

    iMod (auth_map_map_alloc (A := leibnizO _) (slice_of_store CV phys_hists))
      as (new_phys_hist_name) "[newPhysHist #newPhysHistFrag]".

    (* We show a few results that will be useful below. *)
    iAssert (
      □ ∀ `(AbstractState ST) ℓ (bumper : ST → ST), ⌜ is_Some (CV !! ℓ) ⌝ -∗
        know_bumper ℓ bumper -∗
        ⌜ bumpers !! ℓ = Some _ ⌝ ∗
        own_know_bumper new_bumpers_name ℓ bumper)%I as "#bumperImpl".
    { iIntros "!>" (???? ℓ bumper (t & cvLook)) "[mono pts]".
      iFrame "mono".
      iDestruct (ghost_map_lookup with "oldBumpers pts") as %bumpersLook.
      iFrame (bumpersLook).
      iApply (big_sepM_lookup with "bumpersFrag").
      apply restrict_lookup_Some.
      split; first done.

      apply elem_of_dom_2 in cvLook.
      apply elem_of_dom_2 in bumpersLook.
      apply elem_of_intersection.
      rewrite domHistsEqBumpers.
      split; done. }

    iAssert (
      □ ∀ `(AbstractState ST) ℓ,
        ⌜ is_Some (CV !! ℓ) ⌝ -∗
        know_preorder_loc ℓ (abs_state_relation (ST := ST)) -∗
        ⌜ orders !! ℓ = Some _ ⌝ ∗
        own_know_preorder_loc new_orders_name ℓ (abs_state_relation (ST := ST)))%I
      as "#orderImpl".
    { iIntros "!>" (???? ℓ (t & cvLook)) "order".
      iDestruct (ghost_map_lookup with "allOrders order") as %ordersLook.
      iFrame (ordersLook).
      iApply (big_sepM_lookup with "fragOrders").
      apply restrict_lookup_Some.
      split; first done.
      apply elem_of_dom_2 in cvLook.
      apply elem_of_dom_2 in ordersLook.
      rewrite elem_of_intersection.
      rewrite domHistsEqOrders.
      split; done. }

    (* The physical and abstract history has the same timestamps for all
    locations. We will need this when we apply [valid_slice_transfer] below. *)
    iAssert (
      ⌜(∀ ℓ h1 h2, phys_hists !! ℓ = Some h1 → abs_hists !! ℓ = Some h2 → dom (gset _) h1 = dom _ h2)⌝
    )%I as %physAbsHistTimestamps.
    { iIntros (?????).
      iDestruct (big_sepM2_lookup with "predsHold") as (??) "sep"; try eassumption.
      iApply (big_sepM2_dom with "sep"). }

    (* [CV] is a valid slice of the physical and abstract history. *)
    assert (valid_slice CV phys_hists) as cvSlicesPhysHists.
    { apply consistent_cut_valid_slice in cut.
      eapply valid_slice_mono_l in cut; last apply physHistsSubStore.
      done. }
    assert (valid_slice CV abs_hists) as cvSlicesAbsHists.
    { eapply valid_slice_transfer; done. }

    (* We are done allocating ghost state and can now present a new bundle of
    ghost names. *)
    iModIntro.
    set (hD' := {|
      abs_history_name := new_abs_history_name;
      know_abs_history_name := new_know_abs_history_name;
      know_phys_history_name := new_phys_hist_name;
      non_atomic_views_gname := new_na_views_name;
      predicates_name := new_predicates_name;
      preorders_name := new_orders_name;
      exclusive_locs_name := new_exclusive_locs_name;
      shared_locs_name := new_shared_locs_name;
      bumpers_name := new_bumpers_name;
    |}).
    iExists (NvmDeltaG _ hGD' hD').

    iFrame "baseInterp".
    rewrite /nvm_heap_ctx. rewrite /post_crash.
    iEval (simpl) in "Pg".
    iDestruct ("Pg" $! _ abs_hists bumpers na_views (store, _) _
                with "persImpl map'") as "(map' & Pg)".
    iDestruct
      (map_points_to_to_new _ _ _ _ hGD'
         with "newCrashedAt map' ptsMap") as "ptsMap"; first done.
    (* We show the assumption for the post crash modality. *)
    iDestruct ("Pg" with "[knowHistories naViewPts]") as "[$ WHAT]".
    { rewrite /post_crash_resource.

      (* "post_crash_frag_history_impl" - Fragmental history implication. *)
      iSplit.
      { (* We show that fragments of the histories may survive a crash. *)
        iModIntro.
        iIntros (???? ℓ t s ?) "order oldBumper frag".
        iApply "orLost". iIntros (? look).
        iDestruct "frag" as (temp eq) "oldFrag".
        rewrite map_fmap_singleton in eq.
        apply map_fmap_singleton_inv in eq.
        destruct eq as (encX & decEq & ->).

        iDestruct ("bumperImpl" $! ST with "[//] oldBumper")
          as "[%bumpersLook newBumper]".
        iDestruct ("orderImpl" $! ST with "[//] order")
          as "[%ordersLook newOrder]".

        iDestruct (auth_map_map_auth_frag with "oldFullHist2 oldFrag")
          as %(h & lookH & hLook).

        iDestruct (big_sepM2_lookup with "bumperSome") as %?; try done.

        eassert _ as temp; first (apply new_abs_hist_lookup; done).
        destruct temp as (recEncS & ? & ? & encBumper & newHistLook).

        apply encode_bumper_Some_decode in encBumper as (recS & decEq2 & <-).
        iExists recS.
        iFrame "newOrder newBumper".
        iSplit.
        { (* We need info about ordered. *)
          iDestruct (big_sepM2_lookup with "ordered") as %incr; try done.
          iPureIntro.
          rewrite /increasing_map in incr.
          intros [lt | ->]%le_lt_or_eq.
          2: {
            assert (s = recS) as ->; last reflexivity.
            apply (inj Some).
            rewrite -decEq2.
            rewrite decEq.
            f_equiv.
            (* Why congruence no solve this? :'( *)
            apply (inj Some).
            rewrite -H5.
            rewrite -hLook.
            done. }
          eapply encode_relation.encode_relation_decode_iff_1; try done.
          eapply incr; done. }
        rewrite /know_frag_history_loc.
        rewrite /own_frag_history_loc.
        iExists {[ 0 := encode (bumper recS) ]}.
        iSplitPure. {
          rewrite 2!map_fmap_singleton.
          rewrite decode_encode.
          done. }
        iDestruct (auth_map_map_frag_lookup with "histFrags") as "$".
        { done. }
        { apply lookup_singleton. } }

      (* The preorder implication. We show that the preorders may survive a
      crash. *)
      iSplit.
      { iModIntro.
        iIntros (? ? ? ? ?) "order".
        iApply "orLost". iIntros (t look).
        iDestruct ("orderImpl" $! ST with "[//] order") as "[_ $]". }

      (* "post_crash_pred_impl" - We show that the predicates survives a
      crash. *)
      iSplit.
      { rewrite /post_crash_pred_impl.
        iModIntro. iIntros (??? ℓ ϕ) "knowPred".
        iApply "orLost". iIntros (t look).
        iDestruct (own_all_preds_pred with "allPredicates knowPred") as (? predsLook) "#H".
        iApply (predicates_frag_lookup with "newPredsFrag").
        rewrite /newPreds.
        (* FIXME: There is a later in the way. *)
        admit. }
      (* "post_crash_shared_loc_impl" - Shared locations. *)
      iSplit. {
        rewrite /post_crash_shared_loc_impl.
        iIntros "!>" (ℓ) "sh".
        iApply "orLost". iIntros (t look).
        rewrite /is_at_loc.
        iDestruct (own_valid_2 with "atLocs sh")
          as %[_ [elem _]]%auth_both_dfrac_valid_discrete.
        iApply (own_mono with "atLocsFrag").
        exists (◯ newSharedLocs).
        rewrite -auth_frag_op.
        rewrite gset_op.
        f_equiv.
        apply gset_included in elem.
        symmetry.
        eapply subseteq_union_1.
        rewrite /newSharedLocs.
        apply elem_of_subseteq_singleton.
        apply elem_of_intersection.
        split; last set_solver.
        rewrite /newAbsHists.
        apply elem_of_intersection.
        split; last first.
        { rewrite histDomLocs. set_solver+ elem. }
        apply elem_of_dom.
        naive_solver. }
      (* "post_crash_exclusive_loc_impl" - Exclusive locations. *)
      iSplit. {
        rewrite /post_crash_exclusive_loc_impl.
        iIntros "!>" (ℓ) "sh".
        iApply "orLost". iIntros (t look).
        rewrite /is_na_loc.
        iDestruct (own_valid_2 with "naLocs sh")
          as %[_ [elem _]]%auth_both_dfrac_valid_discrete.
        iApply (own_mono with "naLocsFrag").
        exists (◯ newNaLocs).
        rewrite -auth_frag_op.
        rewrite gset_op.
        f_equiv.
        apply gset_included in elem.
        symmetry.
        eapply subseteq_union_1.
        rewrite /newNaLocs.
        apply elem_of_subseteq_singleton.
        apply elem_of_intersection.
        split; last set_solver + elem.
        apply elem_of_dom_2 in look.
        set_solver+ look histDomLocs elem. }
      (* "post_crash_map_map_phys_history_impl" *)
      iSplit. {
        rewrite /map_map_phys_history_impl.
        iIntros "!>" (ℓ tStore msg) "oldPhysHistMsg".
        iApply "orLost". iIntros (t cvLook).
        (* We need the old fragment to conclude that the location is in
        [phys_hist]. *)
        iDestruct (auth_map_map_auth_frag with "oldPhysHist oldPhysHistMsg")
          as (hist physHistLook) "%histLook".
        eapply slice_of_hist_Some in cvSlicesPhysHists as ([v ?] & look & sliceLook); try done.
        (* [msg] is of course not neccessarily the recovered message. Let' find
        that one. *)
        iDestruct (auth_map_map_frag_lookup with "newPhysHistFrag") as "frag".
        { rewrite /slice_of_store. rewrite lookup_fmap.
          erewrite sliceLook. simpl. rewrite map_fmap_singleton. reflexivity. }
        { apply lookup_singleton. }
        iExists v.
        iFrame "frag". }
      (* "post_crash_bumper_impl" *)
      iSplitL "".
      { iIntros "!>" (? ? ? ? ℓ bumper) "oldBumper".
        iApply "orLost". iIntros (t cvLook).
        iDestruct ("bumperImpl" $! ST with "[//] oldBumper")
          as "[%bumpersLook newBumper]".
        iFrame "newBumper". }
      iSplitL "naViewPts".
      { rewrite /post_crash_na_view_map.
        iSplitL "".
        { iIntros (ℓ q SV). iApply (ghost_map_lookup with "oldNaView"). }
        iDestruct (big_sepM_impl_strong with "naViewPts []") as "[$ H]".
        iIntros "!>" (ℓ V).
        destruct (newNaViews !! ℓ) as [newV|] eqn:eq.
        - iIntros "newPts look".
          rewrite /newNaViews in eq.
          apply lookup_gset_to_gmap_Some in eq as [hup <-].
          iApply soft_disj_intro_r.
          iApply "orLost". iIntros (t look).
          iApply "newPts".
        - iIntros "_ %naViewsLook".
          iApply soft_disj_intro_r.
          iExists _. iFrame "newCrashedAt".
          iRight. iPureIntro.
          move: eq.
          rewrite /newNaViews.
          rewrite lookup_gset_to_gmap_None.
          rewrite /newNaLocs.
          rewrite not_elem_of_intersection.
          intros [elem|elem].
          2: { exfalso. apply elem. rewrite -naViewsDom. eapply elem_of_dom_2.
               apply naViewsLook. }
          rewrite /newAbsHists in elem.
          admit. }
      admit. }
    iFrame "valView".
    iSplitPure. { subst. done. }
    (* We show the state interpretation for the high-level logic. *)
    iExists _.
    repeat iExists _.
    rewrite /own_full_history.
    iFrame "ptsMap".
    iFrame "newOrders newPreds hists' newSharedLocs newCrashedAt".
    iFrame "newNaLocs".
    iFrame "newPhysHist".
    iFrame "newBumpers".
    (* [locsDisjoint] *)
    iSplit.
    { iPureIntro. set_solver. }
    (* [histDomLocs] *)
    iSplit.
    { iPureIntro. rewrite -domNewAbsHists. set_solver+ histDomLocs. }
    (* [naView] *)
    iSplitR. { admit. }
    (* [naPredsHold] *)
    iSplitR. { admit. }
    (* mapShared. We show that the shared location still satisfy that
    heir two persist-views are equal. *)
    iSplit. { iPureIntro. apply shared_locs_inv_slice_of_store. }
    (* atLocsHistories *)
    iSplitR.
    { admit. }
    (* [ordered]: We show that the abstract states are still ordered. *)
    iSplitR.
    { iApply big_sepM2_intro.
      - setoid_rewrite <- elem_of_dom.
        apply set_eq.
        rewrite restrict_dom_subset_L; first done.
        rewrite -domHistsEqOrders.
        set_solver+.
      - iModIntro.
        iIntros (ℓ hist order [->|[? ->]]%new_abs_hist_lookup_simpl_inv slice) "!%".
        * apply increasing_map_empty.
        * apply increasing_map_singleton. }
    (* [predsHold] We show that the encoded predicates still hold for the new abstract
    history. *)
    iSplitR "". {
      (* We use the old predsHold to show the new predsHold. There are more
      locations in the old abstract state so the new predsHold is over a subset
      of locations. *)
      iDestruct (big_sepM2_impl_dom_subseteq with "predsHold []") as "$".
      { admit. (* Lemma for this. *) }
      { admit. }
      (* iDestruct (big_sepM_impl_dom_subseteq with "predsHold []") as "[$ temp]". *)
      (* { rewrite new_abs_hist_dom. set_solver. } *)
      iModIntro.
      iIntros (ℓ physHist encHist newPhysHist newAbsHist physHistsLook
               absHistLook newPhysHistsLook newAbsHistLook).
      (* iIntros (ℓ encHist newEncHist absHistLook newAbsHistLook). *)

      pose proof (new_abs_hist_lookup_inv _ _ _ _ _ newAbsHistLook)
        as (t & s & s' & bumper & hist & CVLook & absHistsLook & histLook &
            bumpersLook & bumperAp & histEq).
      (* Can we avoid introducing [encHist] altogether? *)
      assert (encHist = hist) as -> by congruence.

      (* iIntros "(%pred & %physHist & %physHistLook & %predsLook & encs)". *)
      iIntros "(%pred & %predsLook & encs)".
      (* assert (is_Some (CV !! ℓ)) as [[t] CVLook]. *)
      (* { apply elem_of_dom_2 in newAbsHistLook. *)
      (*   rewrite /newAbsHists in newAbsHistLook. *)
      (*   setoid_rewrite new_abs_hist_dom in newAbsHistLook. *)
      (*   apply elem_of_dom. *)
      (*   set_solver. } *)
      epose proof (holo _ _ _ _ CVLook cut) as (msg & physHist' & storeLook & hi & ho).
      (* FIXME: Can we avoid introducting [physHist] altogether? *)
      assert (physHist = physHist') as <- by eauto using map_subseteq_lookup_eq.
      (* iExists pred, {[ 0 := discard_msg_views msg]}. *)
      iExists pred.
      (* iPureGoal. { *)
      (*   rewrite /slice_of_store /slice_of_hist map_fmap_zip_with. *)
      (*   apply slice_of_store_lookup_Some_singleton in ho. *)
      (*   destruct ho as (tt & ?tempHist & eq & ? & ?). *)
      (*   assert (physHist = tempHist) as <- by eauto using map_subseteq_lookup_eq. *)
      (*   apply map_lookup_zip_with_Some. *)
      (*   exists (MaxNat tt), physHist. *)
      (*   rewrite -lookup_fmap in H1. *)
      (*   apply lookup_fmap_Some in H1. *)
      (*   destruct H1 as (msg' & eq' & ->). *)
      (*   split_and!; [| done | done]. *)
      (*   destruct msg, msg'. rewrite /discard_msg_views. simpl. *)
      (*   simpl in eq'. *)
      (*   rewrite map_fmap_singleton. *)
      (*   simpl. *)
      (*   congruence. } *)
      iPureGoal.
      { rewrite /newPreds.
        apply restrict_lookup_Some_2; first done.
        apply elem_of_dom_2 in CVLook.
        apply elem_of_dom_2 in absHistsLook.
        set_solver+ CVLook absHistsLook. }
      rewrite histEq.
      iDestruct (big_sepM2_dom with "encs") as %domEq.
      assert (newPhysHist = {[ 0 := discard_msg_views msg ]}).
      {
        (* apply (inj Some). *)
        (* rewrite -ho. *)
        (* rewrite -newPhysHistsLook. *)
        (* done. *)
        assert (is_Some (physHist !! t)) as [msg' physHistLook].
        { apply elem_of_dom. rewrite domEq. apply elem_of_dom. naive_solver. }
        (* eapply slice_of_store_lookup_Some in newPhysHistsLook. *)
        apply slice_of_store_lookup_Some_singleton in ho.
        destruct ho as (tt & ?tempHist & eq & ? & ?).
        assert (physHist = tempHist) as <- by eauto using map_subseteq_lookup_eq.
      (*   apply map_lookup_zip_with_Some. *)
      (*   exists (MaxNat tt), physHist. *)
        rewrite -lookup_fmap in H2.
        apply lookup_fmap_Some in H2.
        (* destruct H1 as (msg' & eq' & eq2). *)
        admit.
        (* eapply slice_of_store_lookup_Some in newPhysHistsLook. *)
        (* 2: { done. } *)
        (* split_and!; [| done | done]. *)
        (* destruct msg, msg'. rewrite /discard_msg_views. simpl. *)
        (* simpl in eq'. *)
        (* rewrite map_fmap_singleton. *)
        (* simpl. *)
        (* congruence. } *)
      }
      rewrite H1.
      rewrite big_sepM2_singleton.

      (* We look up the relevant predicate in [encs]. *)
      iDestruct (big_sepM2_lookup with "encs") as "flip"; [done | done | ].

      (* We now looks up in [predPostCrash]. *)
      iDestruct (big_sepM2_lookup with "predPostCrash") as "#hi";
        [apply predsLook | apply bumpersLook | ].
      iSpecialize ("hi" $! s (msg_val msg)).

      rewrite /encoded_predicate_holds.
      iDestruct "flip" as (P) "[eq PHolds]".

      admit. }

    (* Show that the bumpers are still monotone. *)
    iSplitR "".
    { iApply (big_sepM2_impl_subseteq with "bumpMono").
      { apply restrict_subseteq. }
      { apply restrict_subseteq. }
      { rewrite /newOrders /newBumpers.
        rewrite 2!restrict_dom.
        rewrite -domOrdersEqBumpers.
        set_solver. } }
    iSplitR "". {
      iApply (big_sepM2_impl_subseteq with "predPostCrash").
      { apply restrict_subseteq. }
      { apply restrict_subseteq. }
      { rewrite /newOrders /newBumpers.
        rewrite 2!restrict_dom.
        rewrite -domPredsEqBumpers.
        set_solver. } }
    (* bumperSome *)
    { iApply big_sepM2_forall.
      iSplit.
      { iPureIntro.
        setoid_rewrite <- elem_of_dom.
        apply set_eq.
        rewrite restrict_dom_subset_L; first done.
        rewrite /recLocs.
        rewrite domHistsEqBumpers.
        set_solver+. }
      (* iIntros (ℓ hist bumper [empty | (s' & histEq)]%new_abs_hist_lookup_simpl_inv look2). *)
      iIntros (ℓ hist bumper look look2).
      apply new_abs_hist_lookup_inv in look.
      destruct look as (? & ? & ? & ? & hist' & ? & ? & ? & ? & ? & histEq).
      (* We handle the empty case here, but we should be able to rule it out. *)
      (* { rewrite empty. iPureIntro. apply map_Forall_empty. } *)
      rewrite histEq.
      iEval (rewrite -map_Forall_singleton).
      assert (bumpers !! ℓ = Some bumper). { admit. }
      iDestruct (big_sepM2_lookup with "bumperSome") as %i; [done|done|].
      (* Note: We probably have to use [bumpMono] as well. *)
      admit. }
  Admitted.

  (*
  Lemma nvm_reinit' (hG' : nvmFixedG Σ, nvmDeltaG Σ) n σ σ' (Hinv : invGS Σ) (Hcrash : crashGS Σ) Pg :
    crash_step σ σ' →
    ⊢ ⎡interp⎤ -∗
      ⎡state_interp σ n⎤ -∗
      post_crash Pg ==∗
      ∃ names : nvm_names,
        let hG := nvm_update Σ hG' Hinv Hcrash names in
          ⎡interp (hG := hG)⎤ ∗
          ⎡nvm_heap_ctx (hG := _) σ'⎤ ∗
          Pg hG.
  Proof.
    iIntros (step) "interp baseInterp".
    iMod (nvm_heap_reinit_alt _ _ _ _ Hcrash _ step with "baseInterp []") as (hnames) "(map & baseInterp & idemp)".
  Admitted.
  *)

  (* _The_ lemma for showing a recovery weakest precondition. *)
  Lemma idempotence_wpr `{hGD : nvmDeltaG Σ} s E1 e rec Φ Φr Φc `{∀ hG, Objective (Φc hG)} :
    ⊢ WPC e @ s ; E1 {{ Φ }} {{ Φc _ }} -∗
      (<obj> □ ∀ (hG' : nvmDeltaG Σ),
            Φc hG' -∗ ▷ post_crash (λ hG', (WPC rec @ s ; E1 {{ Φr hG' }} {{ Φc hG' }}))) -∗
      wpr s E1 e rec Φ Φr.
  Proof.
    iStartProof (iProp _).
    iLöb as "IH" forall (e Φ hGD).

    iIntros (?). monPred_simpl.
    iIntros "wpc".
    iIntros (? ?).
    iIntros "#Hidemp".
    rewrite /wpr.
    rewrite wpr_unfold.
    rewrite /wpr_pre.
    iApply (wpc_strong_mono' with  "wpc"); try reflexivity.
    iSplit. { iIntros (?). monPred_simpl. setoid_rewrite monPred_at_fupd. auto. }
    monPred_simpl.
    iIntros (??).
    iIntros "phiC".
    iModIntro.
    iIntros (???? step ns ?).
    iDestruct ("Hidemp" with "phiC") as "idemp'".
    iIntros "state global".
    iModIntro (|={E1}=> _)%I.

    (* iDestruct (nvm_reinit _ _ _ _ _ _ _ _ with "state idemp'") *)
    (*   as (names) "HI". *)
    (* { apply step. } *)
    (* iApply bi.later_forall_2. iIntros (?). *)
    (* iApply bi.later_forall_2. iIntros (?). *)
    (* iApply bi.later_wand. *)
    iNext.
    iIntros (??) "NC".

    (* Allocate the new ghost state. *)
    iMod (nvm_reinit _ _ _ _ _ _ _ _ with "state idemp'")
      as (names) "(% & val & stateInterp & HIHI & idemp)".
    { apply step. }

    iDestruct "global" as "($ & Hc & $ & $)".
    assert (exists k, ns + k = step_count_next ns) as [k' eq].
    { simpl. eexists _. rewrite -assoc. reflexivity. }
    iMod (cred_frag.cred_interp_incr_k _ k' with "Hc") as "(Hc & _)".
    rewrite eq.

    iModIntro (|={E1}=> _)%I.
    iExists names.
    iSplit; first done.
    iFrame.
    monPred_simpl.
    iSpecialize ("IH" $! _ _ names (∅, ∅, ∅) with "idemp [Hidemp]").
    { monPred_simpl. done. }
    iApply "IH".
  Qed.

End wpr.
