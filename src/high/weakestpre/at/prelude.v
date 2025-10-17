(* Common lemmas shared by most atomic operations *)
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice ipm_tactics.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import wrappers monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state increasing_map.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_at.
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).
  
  (* These are specialized definitions for atomic locations. *)
  Definition at_encoded_full_read_predicates_hold
    (abs_hist: gmap time positive) (phys_hist: gmap time message)
    offset (encp_full encp_read: enc_predicate) : iProp Σ :=
      (* The predicate holds for "exclusive-write" message in the history. *)
      ([∗ map] t ↦ msg; encS ∈ phys_hist; abs_hist,
         if (decide (offset ≤ t ∧ phys_hist !! (S t) = None)) then (* full predicate *)
           encoded_predicate_holds
             encp_full
             encS
             msg.(msg_val)
             (msg.(msg_store_view), msg.(msg_persisted_after_view), ∅)
         else (* read predicate *)
           encoded_predicate_holds
             encp_read
             encS
             msg.(msg_val)
             (msg.(msg_store_view), msg.(msg_persisted_after_view), ∅)).

  (* It's still more hassle to replace [global_pview] with thread local version. *)
  Definition at_encoded_pers_predicate_holds
    ℓ (abs_hist: gmap time positive) (phys_hist: gmap time message)
    (pview: option nat) (offset: nat) (encp_pers: enc_predicate): iProp Σ :=
    ∃ (t: nat) encσ msg,
      ⌜ abs_hist !! t = Some encσ ⌝ ∗
      ⌜ phys_hist !! t = Some msg ⌝ ∗
      (* if a location has never been [fence_sync]ed, it will not have any [persisted] knowledge,
       * in which case we can always use [offset] *)
      ⌜ Nat.add offset (default 0 pview) = t ⌝ ∗
      (* It's easier to work with a per-location assertion. *)
      default emp (persisted_loc ℓ <$> pview) ∗            
      (* [p_pers] are objective anyway, might as well make it easy here. *)
      encoded_predicate_holds encp_pers encσ msg.(msg_val) (∅, ∅, ∅).
  
  Definition loc_info ℓ prot encp_full encp_read encp_pers phys_hists phys_hist abs_hist offset pview : iProp Σ :=
    "physHists" ∷ auth_map_map_auth phy_history_name phys_hists ∗
    "%physHistsLook" ∷ ⌜ phys_hists !! ℓ = Some phys_hist ⌝ ∗
    "%domEq" ∷ ⌜ dom phys_hist = dom abs_hist ⌝ ∗
    "%increasing" ∷ ⌜ increasing_map (encode_relation (⊑@{ST})) abs_hist ⌝ ∗
    "%atInvs" ∷
      ⌜ map_Forall (λ t msg, atomic_loc_inv ℓ t msg) (drop_prefix phys_hist offset) ⌝ ∗
    "#predFullEquiv" ∷ ▷ (encp_full ≡ encode_predicate (p_full prot)) ∗
    "#predReadEquiv" ∷ ▷ (encp_read ≡ encode_predicate (p_read prot)) ∗
    "#predPersEquiv" ∷ ▷ (encp_pers ≡ encode_predicate (p_pers prot)) ∗
    "#frags" ∷ ([∗ map] t ↦ encσ ∈ abs_hist, frag_entry bumpers_name abs_history_name ℓ t encσ) ∗
    "predFullReadHolds" ∷ at_encoded_full_read_predicates_hold abs_hist phys_hist offset encp_full encp_read ∗
    "predPersHolds" ∷ at_encoded_pers_predicate_holds ℓ abs_hist phys_hist pview offset encp_pers ∗
    "#predFullReadSplit" ∷ (∀ encσ v TV, ■ (encoded_predicate_holds encp_full encσ v TV -∗ encoded_predicate_holds encp_read encσ v TV)) ∗
    "fullHist" ∷ know_full_encoded_history_loc ℓ 1 abs_hist ∗
    "pts" ∷ ℓ ↦fh phys_hist.

  Definition insert_impl ℓ encp_full encp_read encp_pers phys_hists phys_hist abs_hist offset pview: iProp Σ :=
    ∀ t (σ: ST) encσ msg,
      ⌜ offset ≤ t ⌝ -∗
      ⌜ encode σ = encσ ⌝ -∗
      ⌜ phys_hist !! t = None ⌝ -∗
      ⌜ msg_store_view msg !!0 ℓ = t - offset ⌝ -∗
      ⌜ msg_persist_view msg = msg_persisted_after_view msg ⌝ -∗
      auth_map_map_auth phy_history_name phys_hists -∗
      at_encoded_full_read_predicates_hold (<[ t := encσ ]>abs_hist) (<[ t := msg ]>phys_hist) offset encp_full encp_read -∗
      at_encoded_pers_predicate_holds ℓ (<[ t := encσ ]> abs_hist) (<[ t := msg ]>phys_hist) pview offset encp_pers -∗
      know_full_encoded_history_loc ℓ 1 abs_hist -∗
      ⌜ increasing_map (encode_relation (⊑@{ST})) (<[ t := encσ ]>abs_hist) ⌝ -∗
      ℓ ↦fh (<[t := msg ]> phys_hist) ==∗
      know_frag_history_loc ℓ t σ ∗
      auth_map_map_frag_singleton phy_history_name ℓ t msg ∗
      interp.

  Definition lookup_impl ℓ encp_full encp_read encp_pers phys_hists phys_hist abs_hist offset pview: iProp Σ :=
    auth_map_map_auth phy_history_name phys_hists -∗
    at_encoded_full_read_predicates_hold abs_hist phys_hist offset encp_full encp_read -∗
    at_encoded_pers_predicate_holds ℓ abs_hist phys_hist pview offset encp_pers -∗
    know_full_encoded_history_loc ℓ 1 abs_hist -∗
    ℓ ↦fh phys_hist -∗
    interp.

  (* Get all information inside [interp] related to the location [ℓ]. *)
  Lemma interp_get_at_loc ℓ prot offset TV :
    interp -∗
    is_at_loc ℓ -∗
    know_protocol ℓ prot TV -∗
    offset_loc ℓ offset -∗
    ∃ phys_hists phys_hist (abs_hist : gmap nat positive) encp_full encp_read encp_pers pview,
      loc_info ℓ prot encp_full encp_read encp_pers phys_hists phys_hist abs_hist offset pview ∗
      (insert_impl ℓ encp_full encp_read encp_pers phys_hists phys_hist abs_hist offset pview ∧
        lookup_impl ℓ encp_full encp_read encp_pers phys_hists phys_hist abs_hist offset pview).
  Proof.
    iNamed 1.
    iIntros "isAt".
    rewrite know_protocol_unfold.
    iNamed 1.
    iIntros "offset".
    iDestruct (own_all_full_preds_pred with "full_predicates knowFullPred")
      as (encp_full encPFullLook) "#encPFullEquiv".
    iDestruct (own_all_read_preds_pred with "read_predicates knowReadPred")
      as (encp_read encPReadLook) "#encPReadEquiv".
    iDestruct (own_all_pers_preds_pred with "pers_predicates knowPersPred")
      as (encp_pers ecpPPersLook) "#encPPersEquiv".
    (* iDestruct (full_map_frag_singleton_agreee with "history hist") *)
    (*   as %(absHist & enc & absHistLook & lookTS & decodeEnc). *)
    (* iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom. *)
    iDestruct (offset_loc_offset_auth_agree with "offset offsets") as %offsetLook.
    iDestruct (location_sets_singleton_included with "atLocs isAt") as %ℓSh.

    iDestruct (big_sepM2_dom with "predsFullReadHold") as %domPhysHistEqAbsHist.
    assert (is_Some (abs_hists !! ℓ)) as [abs_hist absHistLook].
    { rewrite -elem_of_dom. set_solver. }
    assert (is_Some (phys_hists !! ℓ)) as [phys_hist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    assert (na_views !! ℓ = None) as naViewLook. { apply not_elem_of_dom. set_solver. }

    iDestruct (big_sepM2_delete with "predsFullReadHold") as "[predFullReadHolds allPredsFullReadHold]";
      [done|done|].
    iDestruct "predFullReadHolds" as (encp_full' encp_read' offset' ? ? ?) "predFullReadHolds".
    simplify_map_eq.

    iDestruct (big_sepM2_delete with "predsPersHold") as "[predPersHolds allPredsPersHold]";
      [done|done|].
    iEval (rewrite /encoded_pers_predicate_holds /lookup_zero) in "predPersHolds".
    set (pview := global_pview !! ℓ).
    iDestruct "predPersHolds" as (encp_pers' t_p offset' encσ_p msg_p ? ? ? ? ?) "[HpviewTemp predPersHolds]".

    (* TODO: Maybe have a typeclass to make this assertion persistent? *)
    iAssert  (□ (default emp (persisted_loc ℓ <$> (max_nat_car <$> pview))))%I  with "[HpviewTemp]" as "#Hpview".
    { destruct pview; last done.
      simpl.
      by iDestruct "HpviewTemp" as "#?". }
    iClear "HpviewTemp".
    simplify_map_eq.
    
    iDestruct (big_sepM2_delete_l with "ordered")
      as (order) "(%ordersLook & %increasingMap & #ordered2)";
      first apply absHistLook.

    iDestruct (orders_lookup with "allOrders knowPreorder") as %orderEq;
      first apply ordersLook.
    rewrite orderEq in increasingMap.

    iDestruct (big_sepM2_dom with "predFullReadHolds") as %domEq.

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]".
    { naive_solver. }

    eassert _ as invs.
    { eapply map_Forall_lookup_1; first apply mapShared.
      apply restrict_lookup_Some_2; last done.
      apply map_lookup_zip_with_Some.
      eexists _, _. split_and!; done. }
    simpl in invs.

    iDestruct (big_sepM_delete with "atLocsHistories") as
      "(fullHist & atLocsHistories)".
    { apply restrict_lookup_Some_2; done. }

    iDestruct (big_sepM_lookup with "historyFragments") as "#histFrags"; first done.

    iExists phys_hists, phys_hist, abs_hist, encp_full, encp_read, encp_pers, (max_nat_car <$> pview).
    (* Give resources. *)
    Opaque insert_impl lookup_impl.
    iFrame (domEq increasingMap). iFrame (invs).
    iFrame "encPFullEquiv".
    iFrame "encPReadEquiv".
    iFrame "encPPersEquiv".
    iFrame "predFullReadHolds".
    iFrame "histFrags".
    iFrame "physHists".
    iFrame "pts".
    iFrame "fullHist".
    rewrite -bi.sep_assoc. iSplitPure; first apply physHistsLook.
    rewrite -bi.sep_assoc. iSplitL "predPersHolds".
    { iExists _, encσ_p, msg_p. by iFrame "∗#". }
    iSplit.
    { iPoseProof (big_sepM2_lookup with "predFullReadSplit") as "split";
        [ done | done | ].
      iAssumption. }
    (* We show the two different implications. *)
    iSplit.
    { Transparent insert_impl.
      (* Get back resources. *)
      iIntros (t_i σ encσ msg HAfterOffset Hencodeσ HphysLook HMsgStoreViewLook HMsgPersistViewLook)
        "physHists predFullReadHolds predPersHolds fullHist order pts".

      assert (abs_hist !! t_i = None)%I as HAbsHistLookNone.
      { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom. done. }

      iMod (full_map_full_entry_insert _ _ _ _ _ encσ with "history fullHist")
        as "(history & fullHist & #histFrag)"; first done.

      iDestruct (big_sepM_insert_delete with "[$atLocsHistories $fullHist]")
        as "atLocsHistories".
      iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".

      iPoseProof (big_sepM2_insert_delete with "[$allPredsFullReadHold predFullReadHolds]")
        as "allPredsFullReadHold".
      { iExists encp_full, encp_read, offset. rewrite naViewLook. iFrame. done. }
      iPoseProof (big_sepM2_insert_delete _ _ _ _ (<[t_i:=msg]> phys_hist) (<[t_i:=encσ]> abs_hist) with "[$allPredsPersHold predPersHolds]")
        as "allPredsPersHold".
      { iExists encp_pers, _, offset, encσ_p, msg_p.
        assert ((offset + default 0 (max_nat_car <$> pview)) ≠ t_i) by congruence.
        iDestruct "predPersHolds" as (t_p encσ_p' msg_p' ? ? ? ) "(Hpview' & predPersHolds)".
        assert (msg_p = msg_p') as <- by (by simplify_map_eq).
        assert (encσ_p = encσ_p') as <- by (by simplify_map_eq).
        iFrame.
        rewrite ?lookup_insert_ne //. }
      iMod (auth_map_map_insert with "physHists") as "(physHists & _ & physHistFrag)"; [try done|try done|].

      iDestruct (big_sepM2_insert_delete with "[$ordered2 $order]") as "ordered3".
      rewrite (insert_id orders). (* last congruence. *)
      2: { rewrite ordersLook. f_equal.
          rewrite orderEq.
          reflexivity. }

      iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

      iModIntro.
      iSplit; first (iApply frag_history_equiv; rewrite -Hencodeσ; iFrame "histFrag").
      iFrameF "physHistFrag".
      (* We re-establish [interp]. *)
      iExistsN.
      iFrameNamedF.
      iSplitPure; first set_solver.
      iFrameNamedF.
      iFrame "allOrders".
      iFrame "ordered3".
      iFrame "allPredsFullReadHold allPredsPersHold".
      iFrame "full_predicates read_predicates pers_predicates".
      iFrame "atLocs".
      iFrame "naView naLocs allBumpers bumpMono".
      (* historyFragments *)
      iSplit.
      { iApply (big_sepM_insert_2 with "[] historyFragments").
        iApply (big_sepM_insert_2 with "histFrag []").
        iApply (big_sepM_lookup with "historyFragments").
        done. }
      (* [locsDisjoint] *)
      iSplitPure; first apply locsDisjoint.
      (* [histDomLocs] *)
      iSplit. { iPureIntro. set_solver. }
      (* [naViewsDom] *)
      iSplitPure; first done.
      (* [mapShared] - We need to show that the newly inserted message satisfied *)
      (* the restriction on shared locations that their persist view and their *)
      (* persisted after view is equal. *)
      iSplit.
      { iPureIntro.
        erewrite <- (insert_id offsets); last done.
        rewrite -map_insert_zip_with.
        setoid_rewrite (restrict_insert ℓ); last done.
        rewrite /shared_locs_inv.
        apply Nat.le_exists_sub in HAfterOffset as (tE & -> & ?).
        rewrite -drop_prefix_insert.
        apply map_map_Forall_insert_2.
        - apply restrict_lookup_Some_2; last done.
          apply map_lookup_zip_with_Some. naive_solver.
        - simpl.
          rewrite /atomic_loc_inv.
          split; last done.
          rewrite HMsgStoreViewLook. lia.
        - done. }
      iSplitL "atLocsHistories".
      {
        rewrite /know_full_encoded_history_loc.
        (* NOTE: This rewrite is mega-slow. *)
        iEval (setoid_rewrite (restrict_insert ℓ at_locs (<[t_i:=encσ]> abs_hist) abs_hists ℓSh)).
        iFrame. }
      (* [histPViewDoms] *)
      iSplitPure. etrans; [ done | apply dom_insert_subseteq].
      (* [FullBumpersDoms] *)
      iSplitPure; first done.
      (* [ReadBumpersDoms] *)
      iSplitPure; first done.
      (* [PersBumpersDoms] *)
      iSplitPure; first done.
      (* iFrameF "predFullPostCrash". *)
      iSplit; first iAssumption.
      iSplit; first iAssumption.
      iFrame (bumperBumpToValid).
      (* "bumperSome" *)
      iApply (big_sepM2_update_left with "bumperSome"); eauto.
      iPureIntro. intros bumperSome.
      apply map_Forall_insert_2; eauto.
      rewrite /encode_bumper. rewrite -Hencodeσ decode_encode. done. }
    (* [lookup_impl] *)
    { Transparent lookup_impl.
      iIntros "physHists predFullReadHolds predPersHolds fullHist pts".
      iDestruct (big_sepM_insert_delete with "[$atLocsHistories $fullHist]")
        as "atLocsHistories".
      iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".
      iDestruct (big_sepM2_insert_delete with "[$ordered2]") as "ordered3";
        first done.
      iDestruct (big_sepM2_insert_delete with "[$allPredsFullReadHold predFullReadHolds]")
        as "predsFullReadHold".
      { iExistsN. rewrite naViewLook. iFrame "predFullReadHolds". done. }
      iDestruct (big_sepM2_insert_delete with "[$allPredsPersHold predPersHolds]")
        as "predsPersHold".
      { iExistsN.
        iDestruct "predPersHolds" as (? ? ? ? ? ?) "[Hpview' predPersHolds]".
        simplify_map_eq.
        iFrame.
        done. }
      rewrite (insert_id orders); last congruence.
      rewrite (insert_id phys_hists); last congruence.
      rewrite (insert_id abs_hists); last congruence.
      rewrite (insert_id (restrict at_locs abs_hists)).
      2: { apply restrict_lookup_Some_2; done. }

      (* We re-establish [interp]. *)
      iExistsN.
      iFrameNamedF.
      iSplit; first iAssumption.
      iSplit; first iAssumption.
      iFrame "bumperSome".
      done. }
  Qed.

    Lemma read_atomic_location_no_inv t_i t_l (physHist : history) absHist vm SVm FVm
        PVm ℓ (e_i : positive) (s_i : ST) :
    t_i ≤ t_l →
    dom physHist = dom absHist →
    absHist !! t_i = Some e_i →
    decode e_i = Some s_i →
    increasing_map (encode_relation (⊑@{ST})) absHist →
    physHist !! t_l = Some (Msg vm SVm FVm PVm) →
    ∃ s_l e_l,
      absHist !! t_l = Some e_l ∧
      decode e_l = Some s_l ∧
      (* SVm !!0 ℓ = t_l ∧ *)
      (* FVm = PVm ∧ *)
      s_i ⊑ s_l.
  Proof.
    intros le domEq ? decodeEnc ? ?.
    assert (is_Some (absHist !! t_l)) as (e_l & ?).
    { apply elem_of_dom. rewrite <- domEq. apply elem_of_dom. naive_solver. }
    (* The loaded state must be greater than [s_i]. *)
    assert (encode_relation (⊑@{ST}) e_i e_l) as orderRelated.
    { eapply increasing_map_increasing_base; try done.
      rewrite /encode_relation. rewrite decodeEnc. simpl. done. }
    epose proof (encode_relation_inv _ _ _ orderRelated)
      as (? & s_l & eqX & decodeS' & s3InclS').
    assert (x = s_i) as -> by congruence.
   exists s_l, e_l. done.
  Qed.
  
  Lemma read_atomic_location t_i t_l offset (physHist : history) absHist vm SVm FVm
        PVm ℓ (e_i : positive) (s_i : ST) :
    t_i ≤ t_l →
    offset ≤ t_l →
    dom physHist = dom absHist →
    absHist !! t_i = Some e_i →
    decode e_i = Some s_i →
    increasing_map (encode_relation (⊑@{ST})) absHist →
    map_Forall (λ (t : nat) (msg : message), atomic_loc_inv ℓ t msg)
               (drop_prefix physHist offset) →
    physHist !! (t_l) = Some (Msg vm SVm FVm PVm) →
    ∃ s_l e_l,
      absHist !! (t_l) = Some e_l ∧
      decode e_l = Some s_l ∧
      SVm !!0 ℓ = t_l - offset ∧
      FVm = PVm ∧
      s_i ⊑ s_l.
  Proof.
    intros le le' domEq ? decodeEnc ? atInvs ?.
    eassert _ as temp.
    { replace t_l with ((t_l - offset) + offset) in H4 by lia.
      eapply map_Forall_lookup_1; first apply atInvs.
      rewrite drop_prefix_lookup.
      done. }
    rewrite /atomic_loc_inv /= in temp. destruct temp as [SV'lookup <-].
    assert (is_Some (absHist !! (t_l))) as (e_l & ?).
    { apply elem_of_dom. rewrite <- domEq. apply elem_of_dom. naive_solver. }
    (* The loaded state must be greater than [s_i]. *)
    assert (encode_relation (⊑@{ST}) e_i e_l) as orderRelated.
    { eapply (increasing_map_increasing_base _ _ t_i t_l); try (done || lia).
      rewrite /encode_relation. rewrite decodeEnc. simpl. done. }
    epose proof (encode_relation_inv _ _ _ orderRelated)
      as (? & s_l & eqX & decodeS' & s3InclS').
    assert (x = s_i) as -> by congruence.
   exists s_l, e_l. done.
  Qed.
End wp_at.
