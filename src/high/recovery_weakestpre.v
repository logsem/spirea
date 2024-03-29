(* Implementation of the recovery weakest precondition for NVMLang. *)

From Coq Require Import QArith Qcanon.

From stdpp Require Import sets.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gset.
From iris_named_props Require Import named_props.
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require Import recovery_weakestpre.
From Perennial.program_logic Require Import recovery_adequacy.

From self.algebra Require Import ghost_map ghost_map_map.
From self Require Import view extra ipm_tactics if_non_zero view_slice solve_view_le.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop dprop_liftings resources crash_weakestpre
     post_crash_modality or_lost.

Set Default Proof Using "Type".

Definition get_crash_name (hD : nvmDeltaG) :=
  @crash_token_name (@nvm_delta_base hD).

(* A wrapper around [NC] where the ghost name is explicit. *)
Definition NC_name `{crashGpreS Σ} γcrash :=
  @NC _ ({| crash_inG := _; crash_name := γcrash |}).
Global Arguments NC_name {_ _} _ _%Qp.

(** The recovery WP is parameterized by two predicates: [Φ], the postcondition
 for normal non-crashing execution and [Φr], the postcondition satisfied upon
 termination after one ore more crashes.

 This definition of the recovery weakest precondition is defined on top of our
 crash weakest precondition following the same pattern that is used in Perennial
 to define Perennial's wpr on top of Perennial's wpc. *)
Definition wpr_pre `{nvmG Σ} (s : stuckness)
    (wpr : coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (val -d> dPropO Σ) -d> dPropO Σ) :
  coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (val -d> dPropO Σ) -d> dPropO Σ :=
  λ E e e_rec Φ Φr,
  (WPC e @ s ; E
    {{ Φ }}
    {{ ∀ σ mj D σ' (HC : crash_prim_step nvm_crash_lang σ σ') ns n, (* The [n] here actually doesn't matter. *)
      lift_d (λ _, (* interp -∗ *)
        state_interp σ n -∗
        global_state_interp (Λ := nvm_lang) () ns mj D [] -∗
        ∀ (γcrash : gname) q,
        NC_name γcrash q ={E}=∗
        ∃ (hD' : nvmDeltaG),
          ⌜ get_crash_name hD' = γcrash ⌝ ∗
          (* let hG := (nvm_update Σ hG _ Hc1 names) in *)
          (* interp ∗ *)
          ▷ state_interp σ' 0 ∗
          global_state_interp (Λ := nvm_lang) () (step_count_next ns) mj D [] ∗
          validV ∅ ∗
          ▷ (monPred_at (wpr E e_rec e_rec (λ v, Φr v) Φr) (∅, ∅, ∅, hD')) ∗
          NC q)
    }})%I.

Local Instance wpr_pre_contractive `{nvmG Σ} s : Contractive (wpr_pre s).
Proof.
  rewrite /wpr_pre. intros ??? Hwp ?????.
  apply wpc_ne; eauto; first done.
  repeat f_equiv.
  intros ?? ->.
  repeat (f_contractive || f_equiv).
  apply Hwp.
Qed.

Definition wpr_def `{nvmG Σ} (s : stuckness) := fixpoint (wpr_pre s).
Definition wpr_aux `{nvmG Σ} : seal (@wpr_def Σ). by eexists. Qed.
Definition wpr' `{nvmG Σ} := (wpr_aux).(unseal).
Definition wpr_eq `{nvmG Σ} : wpr' = @wpr_def _ := wpr_aux.(seal_eq).
(* Lemma wpr_eq `{nvmG Σ} : @wpr' Σ = @wpr_def Σ. *)
(* Proof. rewrite /wpr'. rewrite wpr_aux.(seal_eq). done. Qed. *)

Lemma wpr_unfold `{nvmG Σ} st E e rec Φ Φc :
  wpr' _ st E e rec Φ Φc ⊣⊢ wpr_pre st (wpr' _ st) E e rec Φ Φc.
Proof.
  rewrite wpr_eq. rewrite /wpr_def.
  apply (fixpoint_unfold (wpr_pre st)).
Qed.

(** If we have a map of points-to predicates prior to a crash and know what view
we crashed at, then we can get a map of points-to predicates for the new
heap. *)
Lemma map_points_to_to_new `{nvmBaseFixedG Σ} logHists store CV (hG hG' : nvmBaseDeltaG) :
  consistent_cut CV store →
  crashed_at (hGD := hG') CV -∗
  base.post_crash_modality.post_crash_mapsto_map store hG hG' -∗
  ([∗ map] ℓ ↦ hist ∈ logHists, let hG := hG in ℓ ↦h hist) -∗
  base.post_crash_modality.post_crash_mapsto_map store hG hG' ∗
  ([∗ map] ℓ ↦ hist ∈ (slice_of_store CV logHists), let hG := hG' in ℓ ↦h hist).
Proof.
  iIntros (cut) "#crashed map pts".
  iAssert (⌜logHists ⊆ store⌝)%I as %sub.
  { iDestruct "map" as "[impl _]".
    rewrite map_subseteq_spec.
    iIntros (ℓ msg look).
    iApply "impl".
    iApply (big_sepM_lookup with "pts"). done. }
  iDestruct (big_sepM_impl_dom_subseteq_with_resource with "map pts []") as "($ & $ & H)".
  { apply slice_of_store_dom_subset. }
  iIntros "!>" (ℓ oldHist newHist look1 look2) "map pts".
  iDestruct (post_crash_modality.post_crash_map_exchange with "map pts") as "[$ pts]".
  apply slice_of_store_lookup_inv in look2 as (? & ? & ? & ? & ? & ? & ?).
  2: {
    eapply valid_slice_mono_l; first done.
    apply consistent_cut_valid_slice.
    done. }
  iDestruct "pts" as (CV') "[crashed' [right | %left]]";
    iDestruct (crashed_at_agree with "crashed' crashed") as %->;
    last congruence.
  iDestruct "right" as (t msg look'' lookm ?) "newPts".
  simplify_eq.
  iFrame.
Qed.

Definition wpr `{nvmG Σ} s := wpr' _ s.

Lemma wpr_mono `{nvmG Σ} s E e rec Φ Ψ Φr Ψr :
  wpr s E e rec Φ Φr -∗
      ((∀ v, Φ v ==∗ Ψ v) ∧ <obj> (∀ v, Φr v ==∗ Ψr v)) -∗
  wpr s E e rec Ψ Ψr.
Proof.
  iModel.
  iLöb as "IH" forall (TV gnames e E Φ Ψ Φr Ψr).
  iIntros "H" ([TV1 gnames'] incl).
  assert (gnames = gnames') as <- by apply incl.
  iIntros "HΦ".
  rewrite /wpr !wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono' with "H"); auto.
  iSplit.
  { iDestruct "HΦ" as "(H & _)".
    iIntros (v ? le) "Hi".
    iSpecialize ("H" $! v).
    monPred_simpl.
    iMod ("H" $! _ le with "Hi").
    done. }
  iIntros ([??] [? [= <-]]) "H".
  iModIntro.
  iIntros (???????).
  simpl.
  rewrite monPred_at_embed.
  iIntros "Hσ Hg".
  iIntros (??) "NC".
  setoid_rewrite monPred_at_embed.
  iSpecialize ("H" with "[//]").
  iMod ("H" $! _ _ with "Hσ Hg NC") as "H".
  iModIntro.
  iDestruct "H" as (nD') "(HNC & ? & ? & ? & H & ?)".
  iExists nD'. iFrame.
  iNext.
  iApply ("IH" with "[H] [HΦ]").
  { iApply monPred_mono; last iApply "H".
    split; last done.
    solve_view_le. }
  iDestruct "HΦ" as "[_ HΦ]".
  rewrite monPred_at_objectively.
  iSplit.
  - iIntros (v).
    iSpecialize ("HΦ" $! (∅, ∅, ∅, nD') v).
    iApply monPred_mono; last iApply "HΦ".
    split; last done.
    solve_view_le.
  - rewrite monPred_at_objectively.
    done.
Qed.

Lemma view_to_zero_lookup V ℓ x :
  V !! ℓ = Some x → (view_to_zero V) !! ℓ = Some (MaxNat 0).
Proof.
  intros look. rewrite /view_to_zero. rewrite lookup_fmap. rewrite look. done.
Qed.

Lemma or_lost_post_crash_full `{nvmBaseFixedG Σ, hG : nvmBaseDeltaG} CV :
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
  Context `{nvmG Σ}.

  (* Computes the new abstract history based on the old history, the crash
  view, and the bumpers. *)
  Definition new_abs_hist (abs_hists : gmap loc (gmap time positive))
             (offsets : gmap loc nat) (bumpers : gmap loc (positive → option positive))
    : gmap loc (gmap time positive) :=
    map_zip_with
      (λ (hist : gmap time positive) bumper,
        omap bumper hist)
      (drop_all_above offsets abs_hists)
      bumpers.

  Lemma new_abs_hist_dom abs_hists CV bumpers :
    dom (new_abs_hist abs_hists CV bumpers) =
    (dom abs_hists ∩ dom CV ∩ dom bumpers).
  Proof. rewrite !dom_map_zip_with_L. set_solver. Qed.

  (* Lemma new_abs_hist_lookup_simpl_inv abs_hists CV bumpers ℓ hist : *)
  (*   (new_abs_hist abs_hists CV bumpers) !! ℓ = Some hist → *)
  (*   hist = ∅ ∨ ∃ s, hist = {[ 0 := s ]}. *)
  (* Proof. *)
  (*   rewrite /new_abs_hist /slice_of_hist. *)
  (*   setoid_rewrite map_lookup_zip_with_Some. *)
  (*   setoid_rewrite map_fmap_zip_with. *)
  (*   setoid_rewrite map_lookup_zip_with_Some. *)
  (*   intros ([?] & ? & -> & ([t] & hist' & -> & ? & ?) & ?). *)
  (*   destruct (hist' !! t). *)
  (*   - right. eexists _. apply map_fmap_singleton. *)
  (*   - left. apply fmap_empty. *)
  (* Qed. *)

  Lemma new_abs_hist_lookup offsets off ℓ abs_hists hist bumpers bumper :
    (* oldOffsets !! ℓ = Some offset → *)
    (* map_Forall (λ _ e, is_Some (bumper e)) hist → *)
    (* valid_slice offset abs_hists → *)
    (* CV !! ℓ = Some (MaxNat t) → *)
    abs_hists !! ℓ = Some hist →
    bumpers !! ℓ = Some bumper →
    offsets !! ℓ = Some off →
    new_abs_hist abs_hists offsets bumpers !! ℓ = Some (new_hist off bumper hist).
      (* new_abs_hist abs_hists CV bumpers !! ℓ = Some {[ 0 := e ]}. *)
  Proof.
    intros l1 l2 l3.
    apply map_lookup_zip_with_Some.
    eexists _, _.
    split_and!; last done.
    2: { rewrite /drop_all_above. apply map_lookup_zip_with_Some.
         eexists _, _. split_and!; done. }
    done.
  Qed.

  (* Lemma new_abs_hist_lookup CV ℓ t abs_hists hist bumpers bumper : *)
  (*   map_Forall (λ _ e, is_Some (bumper e)) hist → *)
  (*   valid_slice CV abs_hists → *)
  (*   CV !! ℓ = Some (MaxNat t) → *)
  (*   abs_hists !! ℓ = Some hist → *)
  (*   bumpers !! ℓ = Some bumper → *)
  (*   ∃ s' e, *)
  (*     hist !! t = Some s' ∧ *)
  (*     bumper s' = Some e ∧ *)
  (*     new_abs_hist abs_hists CV bumpers !! ℓ = Some {[ 0 := e ]}. *)
  (* Proof. *)
  (*   intros bumperToValid val CVlook absHistLook bumpersLook. *)
  (*   eapply map_Forall_lookup_1 in val. *)
  (*   2: { apply map_lookup_zip_with_Some. eexists _, _. done. } *)
  (*   destruct val as [s histLook]. *)
  (*   eapply map_Forall_lookup_1 in bumperToValid as [bumped eq]; last done. *)
  (*   exists s, bumped. *)
  (*   split_and!; try done. *)
  (*   rewrite /new_abs_hist. *)
  (*   apply map_lookup_zip_with_Some. *)
  (*   eexists {[0 := s]}, _. *)
  (*   simpl. *)
  (*   split_and!; try done. *)
  (*   { rewrite map_fmap_singleton. simpl. rewrite eq. done. } *)
  (*   eapply slice_of_hist_lookup_Some; done. *)
  (* Qed. *)

  Lemma new_abs_hist_lookup_Some abs_hists offsets bumpers ℓ hist :
    (* valid_slice CV abs_hists → *)
    new_abs_hist abs_hists offsets bumpers !! ℓ = Some hist →
    ∃ bumper abs_hist offset,
      offsets !! ℓ = Some offset ∧
      abs_hists !! ℓ = Some abs_hist ∧
      (* abs_hist !! t = Some s ∧ *)
      hist = omap bumper (drop_above offset abs_hist) ∧
      bumpers !! ℓ = Some bumper
      (* hist = {[ 0 := default 1%positive (bumper s) ]} *)
        .
  Proof.
    (* intros val. *)
    rewrite /new_abs_hist.
    rewrite map_lookup_zip_with_Some.
    setoid_rewrite map_lookup_zip_with_Some.
    intros (oldHist & bumper & hi & (offset & hist' & ? & ? & ?) & bumpersLook).
    repeat eexists _.
    split_and!; try done.
    congruence.
    (* apply slice_of_hist_lookup_inv in sliceLook *)
    (*   as (t & ? & ? & ? & ? & ? & newHistEq); last done. *)
    (* rewrite newHistEq in hi. *)
    (* rewrite map_fmap_singleton in hi. *)
    (* simpl in hi. *)
    (* naive_solver. *)
  Qed.

  (* Lemma new_abs_hist_lookup_Some abs_hists CV bumpers ℓ hist : *)
  (*   valid_slice CV abs_hists → *)
  (*   new_abs_hist abs_hists CV bumpers !! ℓ = Some hist → *)
  (*   ∃ t s bumper abs_hist, *)
  (*     CV !! ℓ = Some (MaxNat t) ∧ *)
  (*     abs_hists !! ℓ = Some abs_hist ∧ *)
  (*     abs_hist !! t = Some s ∧ *)
  (*     bumpers !! ℓ = Some bumper ∧ *)
  (*     hist = {[ 0 := default 1%positive (bumper s) ]}. *)
  (* Proof. *)
  (*   intros val. *)
  (*   rewrite /new_abs_hist. *)
  (*   rewrite map_lookup_zip_with_Some. *)
  (*   intros (newHist & bumper & hi & sliceLook & bumpersLook). *)
  (*   apply slice_of_hist_lookup_inv in sliceLook *)
  (*     as (t & ? & ? & ? & ? & ? & newHistEq); last done. *)
  (*   rewrite newHistEq in hi. *)
  (*   rewrite map_fmap_singleton in hi. *)
  (*   simpl in hi. *)
  (*   naive_solver. *)
  (* Qed. *)

  Lemma new_abs_hist_lookup_None abs_hists offsets bumpers bumper ℓ hist :
    abs_hists !! ℓ = Some hist →
    bumpers !! ℓ = Some bumper →
    new_abs_hist abs_hists offsets bumpers !! ℓ = None →
    offsets !! ℓ = None.
  Proof.
    intros absHistLook bumpersLook.
    rewrite /new_abs_hist.
    intros [look|?]%map_lookup_zip_with_None; last congruence.
    apply map_lookup_zip_with_None in look as [?|?]; congruence.
  Qed.
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
    rewrite /atomic_loc_inv.
    naive_solver.
  Qed.

  (* Given the state interpretations _before_ a crash we reestablish the
  interpretations _after_ a crash. *)
  Lemma nvm_reinit (hGD : nvmDeltaG) n P TV σ σ' (Hinv : invGS Σ) γcrash :
    crash_step σ σ' →
    ⊢ state_interp σ n -∗
      ((post_crash P) (TV, hGD)) ==∗
      ∃ (hD' : nvmDeltaG),
        ⌜ γcrash = get_crash_name hD' ⌝ ∗
        validV ∅ ∗
        ▷ interp (nD := hD') ∗
        nvm_heap_ctx (hG := _) σ' ∗
        ▷ P (∅, ∅, ∅, hD').
  Proof.
    iIntros ([store PV CV pIncl cut]).
    iIntros "[H1 H2] P".
    iNamed "H1". iNamed "H2".

    (* Our [phys_hist] may contain only a subset of all the locations in
    [store]. But, those that are in [phys_hist] agree with what is in
    [store]. *)
    iAssert (⌜ map_zip_with drop_prefix phys_hists offsets ⊆ store  ⌝)%I
      as %physHistsSubStore.
    { rewrite map_subseteq_spec.
      iIntros (ℓ hist look).
      iDestruct (big_sepM_lookup with "ptsMap") as "pts"; first eassumption.
      iApply (gen_heap_valid with "Hσ pts"). }

    (* We need to first re-create the ghost state for the base
    interpretation. *)
    iMod (nvm_heap_reinit _ _ _ _ _ γcrash with "Hσ Hpers")
      as (hGD') "(%crEq & valView & baseMap & baseInterp & #persImpl & #pers &
                            #newCrashedAt)";
      try done.

    iDestruct (or_lost_post_crash_full with "newCrashedAt pers") as "#orLost".

    iDestruct (big_sepM2_dom with "ordered") as %domHistsEqOrders.
    iDestruct (big_sepM2_dom with "bumpMono") as %domOrdersEqBumpers.
    iDestruct (big_sepM2_dom with "bumperSome") as %domHistsEqBumpers.
    iDestruct (big_sepM2_dom with "predPostCrash") as %domPredsEqBumpers.
    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistsEqAbsHists.
    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetDom.

    (* A name for the set of recovered locations. Per the above equalities this
    set could be expressed in a number of other ways (for instance by using
    [phys_hists] instead of [abs_hists].)*)
    set (recLocs := dom CV ∩ dom abs_hists).

    set newOffsets := offsets_add offsets CV.

    (* The new offsets is a valid slice of the abstract history. This should
    follow from the relationship between [phys_hists] and the points-to
    predicates and the fact that [CV] is a valid slice of these. *)

    set (newAbsHists := new_abs_hist abs_hists newOffsets bumpers).

    iMod (full_map_alloc newAbsHists)
      as (new_abs_history_name) "(hists' & knowHistories & #fragHistories)".

    assert (recLocs = (dom newOffsets)) as domNewOffsets.
    { rewrite dom_map_zip_with_L.
      rewrite -offsetDom. rewrite domPhysHistsEqAbsHists. set_solver+. }
    assert (recLocs = (dom newAbsHists)) as domNewAbsHists.
    { rewrite new_abs_hist_dom.
      rewrite -domHistsEqBumpers.
      rewrite domNewOffsets.
      set_solver. }
    (* Allocate new ghost state for the logical histories. *)
    rewrite /interp.

    (* We freeze/persist the old authorative resource algebra. *)
    iMod (ghost_map_auth_persist with "allOrders") as "#allOrders".
    iMod (ghost_map_auth_persist with "offsets") as "#oldOffsets".
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
    (* iDestruct "history" as "[fullHist1 fullHist2]". *)
    iMod (full_map_persist with "history") as "#oldFullHist".
    (* iMod (own_update with "fullHist2") as "oldFullHist2". *)
    (* { apply auth_update_auth_persist. } *)
    (* iDestruct "oldFullHist2" as "#oldFullHist2". *)
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

    iMod (ghost_map_alloc_persistent newOffsets) as
      (new_offset_name) "[offsets #offsetPts]".

    set newPreds := restrict recLocs predicates.
    iMod (know_predicates_alloc newPreds) as
      (new_predicates_name) "[newPreds #newPredsFrag]".

    set newAtLocs := recLocs ∩ at_locs.
    iMod (own_alloc (● (newAtLocs : gsetUR _) ⋅ ◯ _))
      as (new_shared_locs_name) "[newAtLocs atLocsFrag]".
    { apply auth_both_valid. done. }
    iDestruct "atLocsFrag" as "#atLocsFrag".

    set newNaLocs := recLocs ∩ na_locs.
    iMod (own_alloc (● (newNaLocs : gsetUR _) ⋅ ◯ _))
      as (new_exclusive_locs_name) "[newNaLocs naLocsFrag]".
    { apply auth_both_valid. done. }
    iDestruct "naLocsFrag" as "#naLocsFrag".

    pose (newNaViews := gset_to_gmap (∅ : view) newNaLocs).
    iMod (ghost_map_alloc newNaViews) as (new_na_views_name) "[naView naViewPts]".

    iMod (ghost_map_alloc_persistent
            (default 1%positive <$> slice_hist (MaxNat <$> newOffsets) abs_hists))
      as (new_crashed_in_name) "[crashedInAuth #crashedInPts]".
    iMod (ghost_map_auth_persist with "crashedInAuth") as "#crashedInAuth".

    (* Allocate the new map of bumpers. *)
    set newBumpers := restrict recLocs bumpers.
    iMod (own_all_bumpers_alloc newBumpers)
         as (new_bumpers_name) "[newBumpers #bumpersFrag]".

    set newPhysHists :=
      (λ (hist : gmap _ _), discard_msg_views <$> hist) <$>
        (drop_all_above newOffsets phys_hists).
    iMod (auth_map_map_alloc (A := leibnizO _) newPhysHists)
      as (new_phys_hist_name) "[newPhysHists #newPhysHistFrag]".

    (* We show a few results that will be useful below. *)
    iAssert (
      □ ∀ `(AbstractState ST) ℓ (bumper : ST → ST), ⌜ is_Some (CV !! ℓ) ⌝ -∗
        own_know_bumper (get_bumpers_name hGD) ℓ bumper -∗
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
      ⌜∀ ℓ h1 h2, phys_hists !! ℓ = Some h1 → abs_hists !! ℓ = Some h2 → dom h1 = dom h2⌝
    )%I as %physAbsHistTimestamps.
    { iIntros (?????).
      iDestruct (big_sepM2_lookup with "predsHold") as (??) "sep"; try eassumption.
      iApply (big_sepM2_dom with "sep"). }

    (* [CV] is a valid slice of the physical and abstract history. *)
    assert (valid_slice CV (map_zip_with drop_prefix phys_hists offsets))
      as cvSlicesPhysHists.
    { apply consistent_cut_valid_slice in cut.
      eapply valid_slice_mono_l in cut; last apply physHistsSubStore.
      done. }
    assert (valid_slice (MaxNat <$> offsets_add offsets CV) abs_hists) as cvSlicesAbsHists.
    { apply valid_slice_drop_prefix in cvSlicesPhysHists.
      eapply valid_slice_transfer; done. }

    (* We are done allocating ghost state and can now present a new bundle of
    ghost names. *)
    iModIntro.
    set (hD' := {|
      abs_history_name := new_abs_history_name;
      phys_history_name := new_phys_hist_name;
      non_atomic_views_gname := new_na_views_name;
      crashed_in_name := new_crashed_in_name;
      predicates_name := new_predicates_name;
      preorders_name := new_orders_name;
      offset_name := new_offset_name;
      exclusive_locs_name := new_exclusive_locs_name;
      shared_locs_name := new_shared_locs_name;
      bumpers_name := new_bumpers_name;
    |}).
    iExists (NvmDeltaG hGD' hD').

    assert (newNaLocs ## newAtLocs) as newLocsDisjoint.
    { rewrite /newNaLocs /newAtLocs. set_solver+ locsDisjoint. }
    assert (dom newAbsHists = newNaLocs ∪ newAtLocs) as newHistDomLocs.
    { rewrite /newAbsHists /newNaLocs /newAtLocs /recLocs.
      rewrite -domNewAbsHists.
      rewrite /recLocs.
      rewrite histDomLocs.
      set_solver+. }
    assert (newAbsHists = restrict newNaLocs newAbsHists ∪
                          restrict newAtLocs newAbsHists) as split.
    { apply restrict_disjoint_union. done. }
    iEval (rewrite split) in "knowHistories".
    rewrite big_sepM_union.
    2: { apply restrict_disjoint. done. }
    iDestruct "knowHistories" as "[naHistories atHistories]".

    iFrame "baseInterp".
    rewrite /nvm_heap_ctx. rewrite /post_crash.
    simpl.
    iDestruct ("P" $! _ (restrict na_locs abs_hists) bumpers na_views store _
                with "persImpl baseMap") as "(baseMap & P)".
    iDestruct
      (map_points_to_to_new _ _ _ _ hGD'
         with "newCrashedAt baseMap ptsMap") as "[baseMap ptsMap]"; first done.

    iAssert (
      post_crash_resource_persistent hGD {| nvm_delta_base := hGD'; nvm_delta_high := hD' |}
    ) as "#pcResPers".
    { iSplit.
      { (* We show that fragments of the histories may survive a crash. *)
        iModIntro.
        iIntros (???? ℓ t offset s bumper) "order oldOffset oldBumper frag".
        iApply "orLost". iIntros (tC look).

        iDestruct "frag" as (encX decEq) "oldFrag".

        iDestruct ("bumperImpl" $! ST with "[//] oldBumper")
          as "[%bumpersLook newBumper]".
        iDestruct ("orderImpl" $! ST with "[//] order")
          as "[%ordersLook newOrder]".
        iDestruct (ghost_map_lookup with "oldOffsets oldOffset") as %offsetsLook.

        assert (newOffsets !! ℓ = Some (offset + tC)) as newOffsetsLook.
        { rewrite /newOffsets.
          apply map_lookup_zip_with_Some.
          eexists _, (MaxNat _).
          split_and!; done. }

        assert (ℓ ∈ recLocs).
        { rewrite /recLocs.
          rewrite domHistsEqOrders.
          apply elem_of_intersection.
          split; apply elem_of_dom; done. }

        iDestruct (big_sepM_lookup _ _ ℓ with "offsetPts") as "offset".
        { rewrite /newOffsets.
          apply map_lookup_zip_with_Some.
          eexists _, (MaxNat _).
          split_and!; done. }

        iDestruct (full_map_frag_entry with "oldFullHist oldFrag")
          as %(oldAbsHist & lookH & hLook).

        eassert _ as newHistLook. { apply new_abs_hist_lookup; done. }

        eassert (is_Some (oldAbsHist !! (offset + tC))) as [sOld oldAbsHistLook].
        { eapply valid_slice_lookup; try done.
          rewrite lookup_fmap. rewrite /offsets_add.
          rewrite map_lookup_zip_with.
          rewrite look. rewrite offsetsLook. simpl.
          done. }

        (* TODO: Make this a lemma. *)
        iDestruct (big_sepM2_lookup with "bumperSome")
          as %bumperSome; [done|done|].
        eassert _ as applyBumper.
        { eapply map_Forall_lookup_1.
          apply bumperSome.
          apply oldAbsHistLook. }
        destruct applyBumper as (? & temp).
        assert _ as encodeBumper by apply temp.
        apply encode_bumper_Some_decode in temp as (recS & decEq2 & <-).

        assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
        { rewrite -elem_of_dom domPhysHistsEqAbsHists elem_of_dom. done. }

        eassert (is_Some (physHist !! _)) as [msg physHistLook].
        { apply elem_of_dom.
          erewrite physAbsHistTimestamps; [ | done | done].
          apply elem_of_dom.
          done. }

        eassert _ as applyBumper.
        { eapply map_Forall_lookup_1.
          apply bumperSome.
          apply hLook. }
        destruct applyBumper as (? & temp).
        assert _ as encodeBumper2 by apply temp.
        apply encode_bumper_Some_decode in temp as (? & decEq' & <-).
        simplify_eq.

        iExists _, _.

        iDestruct (big_sepM_lookup with "crashedInPts") as "#crashedIn".
        { rewrite lookup_fmap.
          erewrite slice_hist_lookup_Some; try done.
          rewrite lookup_fmap.
          erewrite newOffsetsLook.
          done. }

        iSplit.
        { iExists sOld. iFrame "crashedIn". iPureIntro. apply decEq2. }
        iAssert (frag_entry_unenc new_abs_history_name ℓ (offset + tC) (bumper recS))%I as "#frag".
        { iDestruct (big_sepM_lookup with "fragHistories") as "HI"; try done.
          iDestruct (big_sepM_lookup with "HI") as "HI2"; try done.
          { rewrite /new_hist.
            rewrite lookup_omap.
            erewrite drop_above_lookup_t.
            rewrite oldAbsHistLook /=.
            rewrite encodeBumper.
            done. }
          rewrite /know_frag_history_loc.
          rewrite /frag_entry_unenc.
          iExists _.
          iFrame "HI2".
          rewrite decode_encode. done. }
        iFrameF "frag".

        iDestruct (auth_map_map_frag_lookup_singleton with "newPhysHistFrag") as "$".
        { rewrite /newPhysHists. rewrite lookup_fmap. rewrite /drop_all_above.
          rewrite map_lookup_zip_with.
          rewrite newOffsetsLook /=. rewrite physHistsLook /=.
          done. }
        { rewrite lookup_fmap drop_above_lookup_t physHistLook. done. }

        iIntros ([lt | ->]%Nat.lt_eq_cases).
        2: { assert (s = recS) as -> by congruence. iFrame "frag". done. }

        iDestruct (big_sepM_lookup with "fragHistories") as "HI"; try done.
        iDestruct (big_sepM_lookup with "HI") as "HI2"; try done.
        { rewrite /new_hist.
          rewrite lookup_omap.
          erewrite drop_above_lookup_le; last (apply Nat.lt_le_incl; apply lt).
          rewrite hLook.
          simpl.
          rewrite encodeBumper2.
          done. }
        iDestruct (big_sepM2_lookup with "ordered") as %incr; try done.
        iSplitPure.
        { eapply encode_relation.encode_relation_decode_iff_1; try done.
          eapply incr; done. }
        iExists _.
        iFrame "HI2".
        rewrite decode_encode.
        done. }

      (* The preorder implication. We show that the preorders may survive a
        crash. *)
      iSplit.
      { iModIntro.
        iIntros (? ? ? ? ?) "order".
        iApply "orLost". iIntros (t look).
        iDestruct ("orderImpl" $! ST with "[//] order") as "[_ $]". }

      (* "post_crash_pred_impl" - We show that the predicates survives a
      crash. *)
      iSplitL "".
      { rewrite /post_crash_pred_impl.
        iModIntro.
        iIntros (??? ℓ ϕ) "oldPred".
        iApply "orLost". iIntros (t look).
        iDestruct (own_all_preds_pred with "allPredicates oldPred")
          as (encPred predsLook) "#equiv".
        iNext.
        rewrite /know_pred.
        iDestruct (predicates_frag_lookup with "newPredsFrag") as "newPred".
        { rewrite /newPreds.
          apply restrict_lookup_Some.
          split; try done.
          apply elem_of_dom_2 in look.
          apply elem_of_dom_2 in predsLook.
          rewrite /recLocs.
          rewrite domHistsEqBumpers -domPredsEqBumpers.
          set_solver+ look predsLook. }
        rewrite /predicates_name. simpl.
        iApply (
          internal_eq_rewrite _ _
            (λ (r : enc_predicateO),
              own new_predicates_name (◯ {[ℓ := pred_to_ra r]})) with "equiv");
          last done.
        solve_proper. }
      (* "post_crash_at_loc_impl" - Shared locations. *)
      iSplit. {
        rewrite /post_crash_at_loc_impl.
        iIntros "!>" (ℓ) "sh".
        iApply "orLost". iIntros (t look).
        iDestruct (own_valid_2 with "atLocs sh")
          as %[_ [elem _]]%auth_both_dfrac_valid_discrete.
        iApply (own_mono with "atLocsFrag").
        exists (◯ newAtLocs).
        rewrite -auth_frag_op.
        rewrite gset_op.
        f_equiv.
        apply gset_included in elem.
        symmetry.
        eapply subseteq_union_1.
        rewrite /newAtLocs.
        apply elem_of_subseteq_singleton.
        apply elem_of_intersection.
        split; last set_solver.
        rewrite /newAbsHists.
        apply elem_of_intersection.
        split; last first.
        { rewrite histDomLocs. set_solver+ elem. }
        apply elem_of_dom.
        naive_solver. }
      iSplit. {
        rewrite /post_crash_na_loc_impl.
        iIntros "!>" (ℓ) "sh".
        iApply "orLost". iIntros (t look).
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
      (* "post_crash_offsets_impl" *)
      iSplit. {
        rewrite /offsets_impl.
        iIntros "!>" (ℓ oldOffset) "oldOffset".
        iApply "orLost". iIntros (t cvLook).
        iDestruct (ghost_map_lookup with "oldOffsets oldOffset") as %look.
        iApply (big_sepM_lookup with "offsetPts").
        rewrite /newOffsets.
        apply map_lookup_zip_with_Some.
        eexists _, (MaxNat _).
        split; first reflexivity.
        split; done. }
      (* "post_crash_bumper_impl" *)
      { iIntros "!>" (? ? ? ? ℓ bumper) "oldBumper".
        iApply "orLost". iIntros (t cvLook).
        iDestruct ("bumperImpl" $! ST with "[//] oldBumper")
          as "[%bumpersLook newBumper]".
        iFrame "newBumper". } }

    (* We show the assumption for the post crash modality. *)
    iDestruct ("P" with "[atLocsHistories naHistories naViewPts]") as "[$ pcRes]".
    { rewrite /post_crash_resource.
      iFrame "pcResPers".
      (* "post_crash_na_view_map" *)
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
          rewrite /recLocs in elem.
          apply not_elem_of_dom.
          apply elem_of_dom_2 in naViewsLook.
          rewrite histDomLocs in elem.
          rewrite naViewsDom in naViewsLook.
          set_solver+ elem naViewsLook. }
      (* "post_crash_full_history_map" *)
      rewrite /post_crash_full_history_map.
      iSplitL "atLocsHistories".
      { iIntros (ℓ q hist) "hist".
        iDestruct (full_map_full_entry with "oldFullHist hist") as %look.
        destruct (decide (ℓ ∈ at_locs)) as [?|notElem].
        { iDestruct (big_sepM_lookup with "atLocsHistories") as "H".
          { apply restrict_lookup_Some; done. }
          iCombine "H hist" as "H2".
          iDestruct (full_entry_valid with "H2") as %val.
          iPureIntro. exfalso.
          apply (Qp.not_add_le_l 1 q).
          apply val. }
        iPureIntro.
        apply restrict_lookup_Some.
        split; first done.
        apply elem_of_dom_2 in look.
        set_solver+ notElem histDomLocs look. }
      iSplitL "".
      { iIntros (ℓ bumper). iApply (ghost_map_lookup with "oldBumpers"). }
      iDestruct (big_sepM_impl_strong with "naHistories []") as "[$ H]".
      iIntros "!>" (ℓ oldAbsHist) "pts".
      iIntros ([absHistLook elem]%restrict_lookup_Some).
      assert (is_Some (bumpers !! ℓ)) as [bumper ?].
      { apply elem_of_dom.
        rewrite -domHistsEqBumpers.
        apply elem_of_dom.
        eexists _. apply absHistLook. }
      assert (is_Some (offsets !! ℓ)) as [offset ?].
      { apply elem_of_dom.
        rewrite -offsetDom domPhysHistsEqAbsHists.
        apply elem_of_dom.
        eexists _. apply absHistLook. }
      assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
      { rewrite -elem_of_dom domPhysHistsEqAbsHists elem_of_dom. done. }
      iExists bumper. iSplitPure; first done.
      iApply soft_disj_intro_r.
      iApply "orLost". iIntros (tC cvLook).
      assert (newOffsets !! ℓ = Some (offset + tC)) as newOffsetsLook.
      { rewrite /newOffsets.
        apply map_lookup_zip_with_Some.
        eexists _, (MaxNat _).
        split_and!; done. }

      rewrite restrict_lookup_elem_of.
      2: { rewrite /newNaLocs.
        apply elem_of_dom_2 in cvLook.
        apply elem_of_dom_2 in absHistLook.
        set_solver+ elem cvLook absHistLook. }
      eassert (new_abs_hist abs_hists newOffsets bumpers !! ℓ = Some _)
        as newAbsHistLook.
      { apply map_lookup_zip_with_Some.
        eexists _, _.
        split_and!; try done.
        rewrite /drop_all_above.
        apply map_lookup_zip_with_Some.
        eexists _, _.
        split_and!; done. }
      rewrite newAbsHistLook.
      eassert (is_Some (oldAbsHist !! (offset + tC))) as [sOld ?].
      { eapply valid_slice_lookup; try done.
        rewrite lookup_fmap. rewrite /offsets_add.
        rewrite map_lookup_zip_with.
        rewrite cvLook. rewrite H1. simpl.
        done. }
      eassert (is_Some (physHist !! _)) as [msg physHistLook].
      { apply elem_of_dom.
        erewrite physAbsHistTimestamps; [ | done | done].
        apply elem_of_dom.
        done. }
      iDestruct (big_sepM2_lookup with "bumperSome") as %bv; [done|done|].
      eassert _ as temp.
      { eapply map_Forall_lookup_1; [eapply bv|done]. }
      destruct temp as [sNew ?].
      iExists _, sOld, _, msg.(msg_val).
      iDestruct (big_sepM_lookup with "offsetPts") as "$"; first done.
      iSplitPure; first done.
      iSplitPure; first done.
      iSplit.
      { iApply (big_sepM_lookup with "crashedInPts").
        rewrite lookup_fmap.
        erewrite slice_hist_lookup_Some; try done.
        rewrite lookup_fmap.
        rewrite newOffsetsLook.
        simpl.
        f_equiv. }
      iFrame "pts".
      iDestruct (big_sepM_lookup with "fragHistories") as "frags"; first done.
      (* Note: At this point we could easily give all the fractional entries. *)
      iDestruct (big_sepM_lookup with "frags") as "$".
      { apply lookup_omap_Some. eexists _.
        split; first done. rewrite drop_above_lookup_t. done. }
      iDestruct (auth_map_map_frag_lookup_singleton with "newPhysHistFrag") as "$".
      { rewrite /newPhysHists. rewrite lookup_fmap. rewrite /drop_all_above.
        rewrite map_lookup_zip_with.
        rewrite newOffsetsLook /=. rewrite physHistsLook /=.
        done. }
      { rewrite lookup_fmap drop_above_lookup_t physHistLook. done. }
    }
    iFrame "valView".
    iSplitPure. { subst. done. }
    (* We show the state interpretation for the high-level logic. *)
    iExistsN.
    rewrite /full_map.

    iFrame "offsets".
    iFrame "newPhysHists".
    rewrite /newPhysHists /newOffsets.

    rewrite slice_of_store_drop.

    iFrame "ptsMap".
    (* iFrame "offsets". *)
    iFrame "newOrders newPreds hists' newAtLocs newCrashedAt".
    iFrame "newNaLocs".
    (* iFrame "newPhysHists". *)
    iFrame "newBumpers".
    iFrame "naView".
    iFrame "fragHistories".
    (* [oldViewsDiscarded] *)
    iSplit.
    { (* Showing this is easy as we have indeed discarded all views. *)
      iIntros "!>". iApply big_sepM2_forall.
      iSplitPure.
      { apply dom_eq_alt_L.
        rewrite dom_fmap_L.
        rewrite /offsets_add /drop_all_above !dom_map_zip_with_L.
        rewrite -offsetDom.
        set_solver+. }
      iPureIntro.
      intros ??? (? & ? & ?)%lookup_fmap_Some ???? look.
      simplify_eq.
      apply lookup_fmap_Some in look as (? & <- & ?).
      done. }

    iSplitPure.
    { set_solver. }
    (* [histDomLocs] *)
    iSplitPure. { rewrite -domNewAbsHists. set_solver+ histDomLocs. }
    (* [naView] *)
    iSplitPure. { rewrite /newNaViews. apply dom_gset_to_gmap. }
    (* mapShared. We show that the shared location still satisfy that
    their two persist-views are equal. *)
    iSplitPure.
    { rewrite /shared_locs_inv.
      rewrite /map_map_Forall.
      eapply map_Forall_subseteq. { apply restrict_subseteq. }
      intros ℓ hist look t newMsg histLook.
      apply map_lookup_zip_with_Some in look as (hist' & off & -> & look & offsetsLook).
      apply lookup_fmap_Some in look as (origHist & <- & look).
      apply drop_all_above_lookup_Some in look as (? & ? & -> & ? & ?).
      rewrite drop_above_fmap in histLook.
      simplify_eq.
      apply drop_prefix_drop_above in histLook as (-> & look).
      apply lookup_fmap_Some in look as (? & <- & ? ).
      split; last done.
      destruct x1. simpl. apply view_lookup_zero_empty. }
    (* atLocsHistories *)
    iSplitL "atHistories".
    { iNext.
      iApply (big_sepM_impl with "atHistories").
      iIntros "!>" (ℓ ? [??]%restrict_lookup_Some) "$". }
    (* [ordered]: We show that the abstract states are still ordered. *)
    iSplitR.
    { iApply big_sepM2_intro.
      { setoid_rewrite <- elem_of_dom.
        apply set_eq.
        rewrite restrict_dom_subset_L; first done.
        rewrite -domHistsEqOrders.
        set_solver+. }
      iModIntro.
      iModIntro.
      iIntros (ℓ newHist order ih [ordersLook ?]%restrict_lookup_Some).
      apply new_abs_hist_lookup_Some in ih
          as (bumper & hist & ? & ? & ? & ? & ?).
      simplify_eq.
      iDestruct (big_sepM2_lookup with "ordered") as %incr; [done|done| ].
      iDestruct (big_sepM2_lookup with "bumpMono") as %mono; [done|done| ].
      iPureIntro.

      intros ?????.
      intros (? & ? & [??]%map_filter_lookup_Some)%lookup_omap_Some
             (? & ? & [??]%map_filter_lookup_Some)%lookup_omap_Some.
      eapply mono; [done | done |].
      eapply incr; [ |done|done].
      lia. }

    (* [predsHold] We show that the encoded predicates still hold for the new abstract
    history. *)
    iSplitL "predsHold baseMap pcRes". {
      iApply big_sepM2_later_2.
      (* We use the old predsHold to show the new predsHold. There are more
      locations in the old abstract state so the new predsHold is over a subset
      of locations. *)
      iDestruct (big_sepM2_impl_dom_subseteq_with_resource with "[baseMap pcRes] predsHold []") as "[H $]".
      { rewrite dom_fmap_L.
        rewrite /drop_all_above /offsets_add !dom_map_zip_with_L.
        set_solver+. }
      { rewrite -domNewAbsHists.
        rewrite dom_fmap_L.
        rewrite /drop_all_above /offsets_add !dom_map_zip_with_L.
        rewrite /recLocs.
        rewrite -domPhysHistsEqAbsHists.
        rewrite -offsetDom.
        set_solver+. }
      { iAccu. }

      iModIntro.
      iIntros (ℓ physHist encHist newPhysHist newAbsHist physHistsLook
               absHistsLook newPhysHistsLook newAbsHistLook).
      iIntros "[baseMap pcRes]".

      (* (* Infer what we can from the lookup in the new physical history. *) *)
      apply lookup_fmap_Some in newPhysHistsLook as (? & ? & look).
      apply drop_all_above_lookup_Some in look as (newOffset & ? & -> & newOffsetLook & ?).
      simplify_eq.
      eassert _ as eq by apply newOffsetLook.
      apply map_lookup_zip_with_Some in eq as (oldOffset & [tC] &?&?& cvLook).

      (* Infer what we can from the lookup in the new abstract history. *)
      apply new_abs_hist_lookup_Some in newAbsHistLook
        as (bumper & ? & ? & offsetLook & ? & ? & bumpersLook).
      rewrite /newOffsets in offsetLook.
      simplify_eq.

      iIntros "(%pred & %predsLook & encs)".

      rewrite -bi.later_exist_2.
      rewrite bi.sep_exist_l.
      iExists pred.
      iAssert (⌜newPreds !! ℓ = Some pred⌝)%I as "$".
      { iPureIntro.
        rewrite /newPreds.
        apply restrict_lookup_Some_2; first done.
        apply elem_of_dom_2 in cvLook.
        apply elem_of_dom_2 in absHistsLook.
        set_solver+ cvLook absHistsLook. }

      iDestruct (big_sepM2_dom with "encs") as %physEncDomEq.
      iDestruct (big_sepM2_lookup with "bumperSome") as %map; [done|done|].
      rewrite -big_sepM2_later_2.
      iApply (big_sepM2_impl_dom_subseteq_with_resource with "[baseMap pcRes] encs []").
      { rewrite dom_fmap_L.
        rewrite /drop_above.
        apply dom_filter_subseteq. }
      { rewrite dom_fmap_L.
        erewrite drop_above_dom_eq; last apply physEncDomEq.
        rewrite dom_omap_id_L; first done.
        eapply map_Forall_subseteq; last apply map.
        apply map_filter_subseteq. }
      { iFrame. }
      iIntros "!>" (? msg oldS ? newS ? histLook (? & <- & look)%lookup_fmap_Some bumperLook).
      apply map_filter_lookup_Some in look as [??].
      apply lookup_omap_Some in bumperLook as (? & ? & (? & ?)%map_filter_lookup_Some).
      simplify_eq.
      simpl.
      iIntros "[baseMap pcRes] predHolds".

      iEval (simpl).

      assert (default ∅ (newNaViews !! ℓ) = ∅) as ->.
      { rewrite /newNaViews.
        destruct (gset_to_gmap ∅ newNaLocs !! ℓ) eqn:eq.
        - apply lookup_gset_to_gmap_Some in eq as [_ ->]. done.
        - done. }

      (* We now looks up in [predPostCrash]. *)
      iDestruct (big_sepM2_lookup with "predPostCrash") as "#postCrash";
        [apply predsLook | apply bumpersLook | ].
      iSpecialize ("postCrash" $! oldS (msg_val msg)).

      rewrite /encoded_predicate_holds.
      iDestruct "predHolds" as (?P) "[#eq PHolds]".
      iDestruct ("postCrash" with "[$PHolds $eq //]") as (?pred) "[%eq2 pred]".
      setoid_rewrite <- bi.later_exist_2.
      rewrite bi.sep_exist_l.
      iExists _.

      rewrite /post_crash_flush. rewrite /post_crash.
      iEval (simpl) in "pred".
      iDestruct ("pred" $! _ _ bumpers na_views store _
                  with "persImpl baseMap") as "(baseMap & pred)".
      iDestruct ("pred" with "[$pcResPers $pcRes]") as "[H pcRes]".
      iFrame "baseMap pcRes".
      iSplit. { rewrite eq2. done. }
      iNext.
      iApply "H".
      simpl.
      iFrame "newCrashedAt".
      iDestruct (big_sepM2_lookup with "oldViewsDiscarded") as %disc; [done|done|].
      assert (msg_persisted_after_view msg ⊑ CV).
      { assert (k < oldOffset ∨ oldOffset ≤ k) as [?|le] by lia.
        { eassert _ as eq. { eapply disc; done. }
          rewrite -eq.
          apply view_empty_least. }
        apply Nat.le_exists_sub in le as (tt & eq & ?).
        eapply consistent_cut_extract; first done.
        - done.
        - eapply lookup_weaken; last done.
          apply map_lookup_zip_with_Some.
          eexists _, _. split_and!; done.
        - apply drop_prefix_lookup_Some_2.
          erewrite <- eq.
          done.
        - lia. }
      iSplitPure; first done.
      iApply (persisted_weak with "pers").
      f_equiv.
      done. }
    (* [bumpMono] - Show that the bumpers are still monotone. *)
    iSplitR "".
    { iApply (big_sepM2_impl_subseteq with "bumpMono").
      { apply restrict_subseteq. }
      { apply restrict_subseteq. }
      { rewrite /newOrders /newBumpers.
        rewrite 2!restrict_dom_L.
        rewrite -domOrdersEqBumpers.
        done. } }
    iSplitR "". {
      iApply (big_sepM2_impl_subseteq with "predPostCrash").
      { apply restrict_subseteq. }
      { apply restrict_subseteq. }
      { rewrite /newOrders /newBumpers.
        rewrite 2!restrict_dom_L.
        rewrite -domPredsEqBumpers.
        set_solver. } }
    (* bumperBumpToValid *)
    iSplitPure.
    { eapply map_Forall_subseteq; last done.
      apply restrict_subseteq. }
    (* bumperSome *)
    { iApply big_sepM2_forall.
      iSplitPure.
      { apply dom_eq_alt_L.
        rewrite restrict_dom_subset_L; first done.
        rewrite /recLocs.
        rewrite domHistsEqBumpers.
        set_solver+. }
      iIntros (ℓ hist bumper look look2).
      apply new_abs_hist_lookup_Some in look.
      destruct look as (bumper' & s & ? & hist' & ? & ? & ?).
      simplify_eq.
      assert (bumper = bumper') as <-.
      { eapply lookup_weaken_inv; [done| |done]. apply restrict_subseteq. }
      iNext. iIntros (?? look).
      iDestruct (big_sepM2_lookup with "bumperSome") as %i; [done|done|].
      apply lookup_omap_Some in look as (? & ? & (? & ?)%map_filter_lookup_Some).
      eapply map_Forall_lookup_1 in i as [bumpedS eq]; last done.
      simplify_eq.
      eapply map_Forall_lookup_1 in bumperBumpToValid as [spa equi]; last done; first done.
      rewrite equi.
      done. }
  Qed.

  (* _The_ lemma for showing a recovery weakest precondition. *)
  Lemma idempotence_wpr s E1 e rec Φ Φr (Φc : dProp Σ) `{!ViewObjective Φc} :
    ⊢ WPC e @ s ; E1 {{ Φ }} {{ Φc }} -∗
      (<obj> □ (Φc -∗ post_crash (WPC rec @ s ; E1 {{ Φr }} {{ Φc }}))) -∗
      wpr s E1 e rec Φ Φr.
  Proof.
    iModel.
    iLöb as "IH" forall (e Φ gnames TV).

    monPred_simpl.
    iIntros "wpc".
    introsIndex ? ?.
    iIntros "#Hidemp".
    rewrite /wpr.
    rewrite wpr_unfold.
    rewrite /wpr_pre.
    assert ((TV, gnames) ⊑ (p, gnames)). { split; last done. solve_view_le. }
    iApply (wpc_strong_mono' with  "wpc"); try reflexivity.
    iSplit. { iIntros (?). monPred_simpl. setoid_rewrite monPred_at_fupd. auto. }
    monPred_simpl.
    introsIndex ? ?.
    iIntros "phiC".
    iModIntro.
    iIntros (???? step ns ?).
    iDestruct ("Hidemp" with "phiC") as "idemp'".
    rewrite lift_d_at.
    iIntros "state global".
    iIntros (γcrash ?) "NC".
    (* Allocate the new ghost state. *)
    iMod (nvm_reinit _ _ _ _ _ _ _ γcrash with "state idemp'")
      as (names) "(%crEq & val & stateInterp & HIHI & idemp)".
    { apply step. }
    iDestruct "global" as "($ & Hc & $ & $)".
    assert (exists k, ns + k = step_count_next ns) as [k' eq].
    { eexists _. rewrite /step_count_next. simpl. rewrite -assoc. reflexivity. }
    iMod (cred_frag.cred_interp_incr_k _ k' with "Hc") as "(Hc & _)".
    rewrite eq.

    iModIntro (|={E1}=> _)%I.
    iExists names.
    iSplit; first done.
    simpl.
    rewrite /get_crash_name in crEq. rewrite -crEq.
    iFrame "NC".
    iFrame.
    monPred_simpl.
    iSpecialize ("IH" $! _ _ names with "idemp [Hidemp]").
    { monPred_simpl. done. }
    iApply "IH".
  Qed.

End wpr.
