(* Implementation of the recovery weakest precondition for NVMLang. *)

From Coq Require Import QArith Qcanon.

From stdpp Require Import sets.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris_named_props Require Import named_props.
From self.program_logic Require Import crash_weakestpre recovery_weakestpre recovery_adequacy.

From self.high Require Import dprop generational_resources wrappers protocol.
From self Require Import view map_extra extra ipm_tactics if_non_zero view_slice solve_view_le.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import generational_resources crash_weakestpre.
From self.high.modalities Require Import or_lost nextgen.
From self.nextgen Require Import nextgen_promises.

Set Default Proof Using "Type*".

Section wpr.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → dProp Σ.
  Implicit Types Φc : dProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Set Nested Proofs Allowed.

  Lemma crashed_at_big_sepM `{Countable K, V: Type} (P: K → V → iProp Σ) m:
    ([∗map] i ↦ x ∈ m, ∀ OCV, crashed_at_offset OCV -∗ P i x) ⊢
    (∀ OCV, crashed_at_offset OCV -∗ [∗map] i ↦ x ∈ m, P i x).
  Proof.
    iIntros "map %OCV #crashed_at".
    iApply (big_sepM_impl with "map").
    iIntros "!>" (???) "H".
    by iSpecialize ("H" with "[#$]").
  Qed.

  Lemma nextgen_big_sepM2 {A B C: Type} `{!EqDecision A} `{!Countable A} (P : A → B → C → iProp Σ) m1 m2 :
    ([∗ map] i↦x; y ∈ m1; m2, ⚡==> P i x y) ⊢ ⚡==> [∗ map] i↦x; y ∈ m1; m2, P i x y.
  Proof.
    rewrite ?big_sepM2_alt.
    iIntros "[% H]".
    iPoseProof (nextgen_big_sepM with "H") as "H".
    iModIntro.
    iSplit; done.
  Qed.

  Lemma crashed_at_big_sepM2 `{Countable K, V1: Type, V2: Type} (P: K → V1 → V2 → iProp Σ) m1 m2:
    ([∗map] i ↦ x; y ∈ m1; m2, ∀ OCV, crashed_at_offset OCV -∗ P i x y) ⊢
    (∀ OCV, crashed_at_offset OCV -∗ [∗map] i ↦ x; y ∈ m1; m2, P i x y).
  Proof.
    rewrite big_sepM2_alt.
    iIntros "[% map] %OCV #crashed_at".
    rewrite big_sepM2_alt.
    iSplit; first done.
    by iApply (crashed_at_big_sepM with "map").
  Qed.

  Lemma nvm_heap_ctx_OCV_dom σ OCV:
    crashed_at_offset OCV -∗
    nvm_heap_ctx σ -∗
    ⌜ dom OCV ⊆ dom σ.2 ∧ dom OCV ⊆ dom σ.1 ⌝.
  Proof.
    iIntros "#offset". iNamed 1.
    iAssert ⌜ OCV0 = OCV ⌝%I as %->.
    { iDestruct (crashed_at_offset_agree with "[crashed] offset") as %<-; last done.
      by iExists _. }
    done.
  Qed.
  
  Lemma nvm_heap_ctx_mapsto σ OCV phys_hists:
    crashed_at_offset OCV -∗
    nvm_heap_ctx σ -∗
    ([∗ map] ℓ↦hist ∈ phys_hists, ℓ ↦fh hist) -∗
    ⌜ dom phys_hists ⊆ dom σ.1 ⌝ ∗ ⌜ map_Forall (λ ℓ phys_hist, Some $ drop_prefix phys_hist (OCV !!0 ℓ) = σ.1 !! ℓ) phys_hists ⌝.
  Proof.
    iIntros "#offset". iNamed 1. iIntros "mapsto".
    iAssert ⌜ OCV0 = OCV ⌝%I as %->.
    { iDestruct (crashed_at_offset_agree with "[crashed] offset") as %<-; last done.
      by iExists _. }
    iAssert ⌜ map_Forall (λ ℓ phys_hist, Some $ drop_prefix phys_hist (OCV !!0 ℓ) = σ.1 !! ℓ) phys_hists ⌝%I as %H.
    { iApply big_sepM_pure_1.
      iPoseProof (big_sepM_impl_dom_subseteq_with_resource _ _ _ _ phys_hists
                   with "Hσ mapsto []") as "[Hσ [$ _]]"; first done.
      iIntros "!>" (??? look ?) "Hσ mapsto".
      iDestruct (fmapsto_heap_valid with "Hσ mapsto") as %look'.
      pose proof look' as ?H%elem_of_dom_2.
      iFrame.
      iPureIntro.
      pose proof (dom_store_drop_prefix OCV full_hist) as eq.
      rewrite full_hist_eq //.
      simplify_map_eq.
      rewrite store_drop_prefix_alt look' /= //. }
    iAssert ⌜ map_Forall (λ ℓ _, ℓ ∈ dom σ.1) phys_hists ⌝%I as %H'.
    { iApply big_sepM_pure_1.
      iPoseProof (big_sepM_impl_dom_subseteq_with_resource _ _ _ _ phys_hists
                   with "Hσ mapsto []") as "[Hσ [$ _]]"; first done.
      iIntros "!>" (??? look ?) "Hσ mapsto".
      iDestruct (fmapsto_heap_valid with "Hσ mapsto") as %look'.
      pose proof look' as ?H%elem_of_dom_2.
      iFrame.
      iPureIntro.
      pose proof (dom_store_drop_prefix OCV full_hist) as eq.
      rewrite full_hist_eq eq //. }
    iPureIntro.
    split; last done.
    rewrite elem_of_subseteq.
    intros ℓ look.
    apply elem_of_dom in look as [].
    eapply (map_Forall_lookup_1 _ _ _ _ H'); done.
  Qed.
  Opaque nvm_heap_ctx.
  
  Lemma extra_state_nextgen CV σ1 σ2:
    CV_crash_step CV σ1 σ2 →
    crashed_at_offset OCV -∗
    nvm_heap_ctx σ1 →
    picked_out crashed_at_name (crashed_at_trans (OCV `view_add` CV)) -∗
    extra_state_interp -∗
    |==> ▷ ⚡==> |==> extra_state_interp ∗ (∃ OCV, crashed_at_offset OCV ∗ crashed_in_impl OCV).
  Proof.
    intros Hcrash.
    iIntros "#crashed_at_offset heap #mainpicked".
    iNamed 1.
    (* basic pure information *)
    iDestruct (big_sepM2_dom with "bumperSome") as %domAbsHistsBumpers.
    iDestruct (big_sepM2_dom with "predsFullReadHold") as %domPhysHistsAbsHists.
    iDestruct (big_sepM2_dom with "ordered") as %domAbsHistsOrders.
    iAssert ⌜ ∀ ℓ : loc, ℓ ∈ dom offsets → offsets !! ℓ = Some (OCV !!0 ℓ) ⌝%I with "[offsets]" as %HOffsetOCV.
    { iNamed "offsets".
      iDestruct (crashed_at_offset_agree with "crashed_at_offset crashed") as %->.
      done. }
    (* information that requires the base interp to extract. *)
    iDestruct (nvm_heap_ctx_OCV_dom with "crashed_at_offset heap") as %[domOCVPV domOCVStore].
    iDestruct (nvm_heap_ctx_mapsto with "crashed_at_offset heap ptsMap") as %[domCVPhysHists physHistsEq].
    simpl in domCVPhysHists.

    iPoseProof (offset_auth_picked_out with "mainpicked offsets") as "offsets".

    (* some resources require manually [nextgen] proof *)
    iDestruct (full_map_nextgen with "history allBumpers") as "[allBumpers history]".
    iDestruct (all_loc_frag_entry_nextgen with "historyFragments allBumpers") as "[allBumpers historyFragmentsNG]"; first done.
    iDestruct (all_loc_full_entry_nextgen with "atLocsHistories allBumpers") as "[allBumpers atLocsHistories]".
    { rewrite restrict_dom_L. set_solver. }

    set OCV' := (OCV `view_add` CV).
    set offsets' := (max_nat_car <$> restrict (dom offsets) OCV').

    assert (dom (drop_above_map OCV' phys_hists) = dom (abs_hist_trans bumpers OCV' abs_hists)).
    { rewrite dom_abs_hist_trans; last set_solver.
      rewrite /drop_above_map.
      apply dom_imap_L.
      intros ℓ. split.
      - intros [elemOfOCV elemOfAbsHists]%elem_of_intersection.
        assert (is_Some (phys_hists !! ℓ)) as [? ?].
        { rewrite -elem_of_dom domPhysHistsAbsHists //. }
        eexists. split; first done.
        rewrite /drop_above_hist.
        apply elem_of_dom in elemOfOCV as [? ->].
        simpl.
        by eexists.
      - intros (abs_hist & look & look').
        apply elem_of_dom_2 in look.
        apply elem_of_intersection. split; last set_solver.
        rewrite /drop_above_hist in look'.
        apply elem_of_dom.
        destruct (OCV' !! ℓ); first done.
        simpl in look'. destruct look'. congruence. }
    
    iAssert (nvm_heap_ctx σ1 ∗
             |==> ⚡==> ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ drop_above_map OCV' phys_hists;abs_hist_trans bumpers OCV' abs_hists,
                      encoded_full_read_predicates_hold ℓ abs_hist phys_hist (const ∅ <$> restrict (dom OCV') na_views) offsets'
                        (restrict (dom OCV') predicates_full) (restrict (dom OCV') predicates_read) ∗
                      encoded_pers_predicate_holds ℓ abs_hist phys_hist ∅ offsets'
                        (restrict (dom OCV') predicates_pers)))%I with "[heap predsFullReadHold predsPersHold]" as "predsHold".
    { rewrite -nextgen_big_sepM2 -big_sepM2_bupd.
      iPoseProof (big_sepM2_sep with "[$predsFullReadHold $predsPersHold]") as "predsHold".
      iDestruct (big_sepM2_impl_dom_subseteq_with_resource _ _
                _ _ (drop_above_map OCV' phys_hists) (abs_hist_trans bumpers OCV' abs_hists)
                with "heap predsHold []") as "[$ $]".
      { rewrite /drop_above_map.
        etrans; first apply dom_imap_subseteq.
        done. }
      { done. }
      iIntros "!>" (ℓ phys_hist abs_hist phys_hist' abs_hist' physHistsLook absHistsLook physHistsLook' absHistsLook')
        "heap [predFR predP]".
      assert (is_Some (bumpers !! ℓ)) as [bumper bumpersLook].
      { rewrite -elem_of_dom -domAbsHistsBumpers elem_of_dom. by eexists. }
      assert (is_Some (orders !! ℓ)) as [order ordersLook].
      { rewrite -elem_of_dom -domAbsHistsOrders elem_of_dom. by eexists. }
      (* we only care about locations that survives *)
      destruct (decide (ℓ ∈ dom OCV')) as [ elemOfOCV | ];
        last (rewrite restrict_lookup_not_elem_of // in absHistsLook').
      assert (drop_bump_map ℓ bumper OCV' abs_hist = abs_hist') as <-.
      { rewrite /abs_hist_trans in absHistsLook'.
        rewrite restrict_lookup_elem_of // map_lookup_imap absHistsLook /= /per_loc_trans bumpersLook in absHistsLook'.
        by simplify_eq. }
      pose proof elemOfOCV as [[t_c] OCVLook' ]%elem_of_dom.
      assert (discard_msg_views <$> drop_above t_c phys_hist = phys_hist') as <-.
      { rewrite /drop_above_map map_lookup_imap physHistsLook /= in physHistsLook'.
        rewrite /drop_above_hist in physHistsLook'.
        rewrite OCVLook' /= in physHistsLook'.
        by simplify_eq. }
      iDestruct "predFR" as (encp_full encp_read offset predFullLook predReadLook offsetLook) "predFR".
      iEval (rewrite /encoded_pers_predicate_holds) in "predP".
      iDestruct "predP" as (encp_pers t_p offset' encσ_p msg_p predPersLook offsetLook' encσPLook msgPLook <-) "[persisted predP]".
      assert (offset' = offset) as -> by by simplify_map_eq.
      assert ((OCV `view_add` CV) !!0 ℓ = t_c) as OCVLook0'.
      { rewrite /lookup_zero OCVLook' //. }
      assert (offset ≤ t_c).
      { subst OCV'.
        rewrite view_add_lookup_zero in OCVLook0'.
        rewrite HOffsetOCV in offsetLook'; last (apply elem_of_dom; by eexists).
        simplify_eq.
        lia. }
      assert (offset = OCV !!0 ℓ) as OCVLook0.
      { apply Some_inj.
        rewrite -HOffsetOCV //; apply elem_of_dom; by eexists. }
      (* we know there must be a [CV !! ℓ = OCV' !! ℓ]. *)
      assert (is_Some (CV !! ℓ)) as [[t_c'] tCLook'].
      { subst OCV'.
        rewrite lookup_merge in OCVLook'.
        destruct (OCV !! ℓ) eqn:Heqn; rewrite Heqn /= in OCVLook'.
        + rewrite -elem_of_dom.
          destruct Hcrash as [store PV pIncl cut]. simpl in *.
          pose proof (elem_of_subseteq (dom PV) (dom CV)) as [Hsubset _].
          specialize (Hsubset ltac:(apply view_le_dom_subseteq; done)).
          apply Hsubset.
          pose proof (elem_of_subseteq (dom OCV) (dom PV)) as [Hsubset' _].
          apply Hsubset'; first done.
          rewrite elem_of_dom. by eexists.
        + destruct (CV !! ℓ); done. }
      iAssert ⌜ offset + (global_pview !!0 ℓ) ≤ t_c ⌝%I as %pViewLb.
      { rewrite /lookup_zero.
        destruct (global_pview !! ℓ) as [[pview] | ]; simpl; last (iPureIntro; lia).
        Transparent nvm_heap_ctx.
        iNamed "heap".
        destruct Hcrash as [store PV pIncl cut]. simpl in *.
        iAssert ⌜ OCV0 = OCV ⌝%I as %->.
        { iDestruct (crashed_at_offset_agree with "[crashed] crashed_at_offset") as %<-; last done.
          by iExists _. }
        iDestruct (persisted_auth_included with "crashed_at_offset pers persisted") as %incl.
        iPureIntro.
        assert ({[ℓ := MaxNat pview]} ⊑ OCV `view_add` CV `view_sub` OCV) as incl'.
        { etrans; first apply incl.
          apply view_sub_mono.
          apply view_add_mono; done. }
        rewrite view_included in incl'.
        specialize (incl' ℓ).
        rewrite lookup_singleton in incl'.
        rewrite /view_add /view_sub map_lookup_imap /= lookup_merge /lookup_zero in incl'.
        move: incl'.
        rewrite tCLook'.
        destruct (OCV !! ℓ) as [[] | ] eqn:Heq; rewrite ?Heq /=.
        - intros incl'%Some_MaxNat_included.
          simplify_map_eq.
          rewrite view_add_lookup_zero /lookup_zero tCLook' Heq /=.
          lia.
        - intros incl'%Some_MaxNat_included.
          simplify_map_eq.
          rewrite view_add_lookup_zero /lookup_zero tCLook' Heq /=.
          lia. }
      iFrame "heap".
      iClear "persisted".
      
      destruct Hcrash as [store PV pIncl cut]. simpl in *.
      (* we should be able to find a message exactly at [t_c]. *)
      assert (is_Some (phys_hist !! t_c)) as [msg_c msgCLook].
      { simpl in physHistsEq.
        apply consistent_cut_valid_slice in cut as valid.
        apply (valid_slice_lookup _ ℓ t_c' _ (drop_prefix phys_hist (OCV !!0 ℓ))) in valid; [ | done | ].
        - rewrite drop_prefix_lookup in valid.
          replace t_c with (t_c' + (OCV !!0 ℓ)); first done.
          rewrite view_add_lookup_zero {2}/lookup_zero tCLook' /= in OCVLook0'.
          lia.
        - symmetry.
          eapply (map_Forall_lookup_1 _ _ _ _ physHistsEq); done. }
      (* we can also derive that an (encoded) abstract state also exist at the timestamp. *)
      iDestruct (big_sepM2_dom with "predFR") as %domPhysHistAbsHist.
      assert (is_Some (abs_hist !! t_c)) as [encσ_c encσCLook].
      { rewrite -elem_of_dom -domPhysHistAbsHist elem_of_dom. by eexists. }
      iPoseProof (big_sepM2_delete _ _ _ t_c msg_c encσ_c with "predFR") as "[predF predFRRest]".
      { done. } { done. }
      (* we know that [encσ_p ⊑ encσ_c] always holds. *)
      iAssert ⌜ order encσ_p encσ_c ∨ encσ_p = encσ_c ⌝%I as %orderPC.
      { destruct (decide (offset + (global_pview !!0 ℓ) = t_c)) as [ <- | ].
        - simplify_map_eq.
          by iRight.
        - iLeft.
          iDestruct (big_sepM2_lookup _ _ _ ℓ with "ordered") as %incrMap.
          { done. } { done. }
          iPureIntro.
          eapply (incrMap _); try done.
          lia. }
      (* we know that bumper always return [Some _] *)
      iAssert ⌜ ∃ encσ_c', bumper encσ_c = Some encσ_c' ⌝%I as %[encσ_c' bumperSome].
      { iDestruct (big_sepM2_lookup _ _ _ ℓ with "bumperSome") as %bumperSome.
        { done. } { done. }
        iPureIntro.
        eapply (map_Forall_lookup_1 _ _ _ _ bumperSome); done. }
      destruct (phys_hist !! S t_c) as [msgSC | ] eqn:msgSCLook.
      - (* the crash timestamp is not exclusive, we need to apply the second case of [predFullNextgen] *)
        admit.
      - (* the crash timestamp is exclusive, we can apply the first case of [predFullNextgen]. *)
        rewrite decide_True; last done.
        iDestruct (big_sepM2_lookup _ _ _ ℓ with "predFullNextgen") as (encp_full' encp_read' encp_pers' ? ? ?) "nextgen".
        { done. }
        { done. }
        clear OCVLook0'.
        simplify_map_eq.
        iDestruct (plainly_elim with "nextgen") as "NG".
        iDestruct ("NG" with "[//] predP predF") as "[fullNG _]".
        iDestruct ("fullNG" with "[//]") as ">(%P_full' & %P_pers' & #PFullEquiv' & #PPersEquiv' & fullNG)".
        (* For the rest of the predicates, we split them into two facts: *)
    (*      * the persistent knowledge about predicate equivalence, *)
    (*      * and the resource under [⚡==>] modality. *)
        iPoseProof (big_sepM2_impl
                     _
                     (λ t msg_r encσ_r,
                        (⚡==> ∀ (P: dProp Σ) encσ_r',
                           ⌜ bumper encσ_r = Some encσ_r' ⌝ -∗
                           encp_read encσ_r' msg_r.(msg_val) ≡ Some P -∗
                           (⎡ persisted (view_to_zero (msg_persisted_after_view (msg_r))) ⎤ ∗ ⎡ crashed_at CV ⎤ -∗
                            P) (∅, ∅, ∅))
                        )%I
                     with "predFRRest []") as "predFRRest".
        { iIntros "!>" (t msg_r encσ_r [? msgRLook]%lookup_delete_Some [_ encσRLook]%lookup_delete_Some) "predR".
          iAssert (encoded_predicate_holds encp_read encσ_r (msg_val msg_r)
                     (default (msg_store_view msg_r) (na_views !! ℓ), msg_persisted_after_view msg_r, ∅))%I with "[predR]" as "predR".
          { destruct (decide _); last done.
            iDestruct (big_sepM2_lookup with "predFullReadSplit") as "split".
            { done. } { done. }
            iDestruct ("split" with "predR") as "$". }
          iDestruct (big_sepM2_lookup _ _ _ ℓ with "predReadNextgen") as "nextgen'".
          { done. } { done. }
          iAssert ⌜ ∃ encσ_r', bumper encσ_r = Some encσ_r' ⌝%I as %[encσ_r' bumperSomeR].
          { iDestruct (big_sepM2_lookup _ _ _ ℓ with "bumperSome") as %bumperSomeR.
            { done. } { done. }
            iPureIntro.
            eapply (map_Forall_lookup_1 _ _ _ _ bumperSomeR); done. }
          iDestruct ("nextgen'" $! encσ_r encσ_r' with "[//] predR") as (P) "[#encpReadEquiv' ReadNG]".
          iModIntro.
          iSpecialize ("ReadNG" $! CV with "[]").
          { iSplitPure; first admit.
            iSplit; first admit. (* FIXME: this one seems problematic. *)
            admit. }
          -
          iApply "ReadNG".
        }
    }

    
    (* we now pick the [crashed_at] resource using base logic nextgen lemma. *)
    iDestruct (heap_ctx_next_generation _ _ _ Hcrash with "heap")
      as ">[(%OCV' & #crashed_at_offset' & #picked_out) heap]".
    iDestruct (crashed_at_offset_agree with "crashed_at_offset crashed_at_offset'") as %<-.
    iClear "crashed_at_offset'".
    destruct Hcrash as [store PV pIncl cut]. simpl in *.
    
    subst OCV'.
    iModIntro. iModIntro.
    iModIntro.

    iDestruct "crashed_at_offset" as (OV' t) "[picked crashed]".
    iPickedInAgree "mainpicked picked".
    iAssert (crashed_at_offset (OCV `view_add` CV))%I as "#crashed_at_offset".
    { by iExists _. }
    iSpecialize ("ptsMap" with "crashed_at_offset").
    iSpecialize ("history" with "crashed_at_offset").
    iDestruct ("historyFragmentsNG" with "crashed_at_offset") as "historyFragments".
    iSpecialize ("atLocsHistories" with "crashed_at_offset").
    iDestruct "full_predicates" as (OCV') "[full_predicates picked]".
    iAssert ⌜ OCV' = OCV `view_add` CV ⌝%I as %->.
    { iDestruct (gen_picked_in_agree with "mainpicked picked") as %eq.
      by simplify_eq. }
    iClear "picked".
    iSpecialize ("physHists" with "crashed_at_offset").
    iDestruct "read_predicates" as (OCV') "[read_predicates picked]".
    iAssert ⌜ OCV' = OCV `view_add` CV ⌝%I as %->.
    { iDestruct (gen_picked_in_agree with "mainpicked picked") as %eq.
      by simplify_eq. }
    iClear "picked".
    iDestruct "pers_predicates" as (OCV') "[pers_predicates picked]".
    iAssert ⌜ OCV' = OCV `view_add` CV ⌝%I as %->.
    { iDestruct (gen_picked_in_agree with "mainpicked picked") as %eq.
      by simplify_eq. }
    iClear "picked".
    iSpecialize ("allOrders" with "crashed_at_offset").
    iDestruct "naLocs" as (OCV') "[naLocs picked]".
    iAssert ⌜ OCV' = OCV `view_add` CV ⌝%I as %->.
    { iDestruct (gen_picked_in_agree with "mainpicked picked") as %eq.
      by simplify_eq. }
    iClear "picked".
    iDestruct "atLocs" as (OCV') "[atLocs picked]".
    iAssert ⌜ OCV' = OCV `view_add` CV ⌝%I as %->.
    { iDestruct (gen_picked_in_agree with "mainpicked picked") as %eq.
      by simplify_eq. }
    iClear "picked".
    iSpecialize ("naView" with "crashed_at_offset").
    iSpecialize ("allBumpers" with "crashed_at_offset").
    iDestruct (big_sepM2_sep with "predsHold") as "[predsFullReadHold predsPersHold]".
    iModIntro.
    iExistsN.
    iFrame "ptsMap physHists history historyFragments full_predicates read_predicates pers_predicates allOrders naLocs atLocs naView allBumpers offsets".
    iFrame "predsFullReadHold predsPersHold".
    iSplit. (* [#crashedRely] *)
    { iDestruct "crashedRely" as (?) "[rely ?]". iExists _. iApply "rely". }
    iSplitPure.
    { rewrite dom_fmap_L restrict_dom_L -offsetsDom.
      apply dom_imap_L.
      intros ℓ; split; intros H.
      - apply elem_of_intersection in H.
        rewrite /drop_above_hist.
        destruct H as [[hist ?]%elem_of_dom [[t] ->]%elem_of_dom].
        exists hist. split; first done.
        by simpl.
      - destruct H as (hist & Hdom%elem_of_dom_2 & Hdrop%fmap_is_Some%elem_of_dom).
        set_solver. }
    iSplitPure; first set_solver.
    iSplitPure.
    { rewrite dom_abs_hist_trans; set_solver. }
    iSplitPure; first (rewrite restrict_dom_L; set_solver).
    iSplitPure; first admit. (* [shared_locs_inv] *)
    iSplitL "atLocsHistories".
    { rewrite -restrict_abs_hist_trans.
      iDestruct (big_sepM_impl_dom_subseteq _ _ _
                   (restrict (at_locs ∩ dom (OCV `view_add` CV))
                      (abs_hist_trans bumpers (OCV `view_add` CV) abs_hists))
                  with "atLocsHistories []") as "[$ _]".
      - rewrite ?restrict_dom_L. set_solver.
      - iIntros "!>" (ℓ abs_hist abs_hist' absHistsLook absHistsLook') "full_entry".
        assert (abs_hist = abs_hist') as ->; last done.
        destruct (decide (ℓ ∈ dom (OCV `view_add` CV)));
          last (rewrite restrict_lookup_not_elem_of // in absHistsLook'; set_solver).
        destruct (decide (ℓ ∈ at_locs));
          last (rewrite restrict_lookup_not_elem_of // in absHistsLook'; set_solver).
        move: absHistsLook absHistsLook'.
        rewrite ?restrict_lookup_elem_of //; last set_solver.
        congruence. }
    iSplit; first admit. (* [ordered] *)
    iSplit; first admit. (* [histPViewDoms] *)

    (* TODO: hard parts *)
    (*  * [predicatesHold]: *)
  Admitted.
  
  Lemma idempotence_wpr
      s E1 e e_rec Φ Φr Φc:
    ⊢ validV (store_view e.(ts_view)) -∗
    (WPC e.(ts_expr) @ s; E1 {{ Φ }} {{ Φc }}) e.(ts_view)-∗
    (* TODO: have an expert double check this modality *)
    ■ ((Φc -∗ ▷ <NG> (WPC e_rec @ s ; E1 {{ Φr }} {{ Φc }})) ⊥) -∗
      wpr s E1 e (e_rec `at` ⊥) (λ v, Φ v.(val_val) v.(val_view)) True%I (λ v, Φr v.(val_val) v.(val_view)).
  Proof.
    iIntros "#validV Hwpc #Hidemp".
    iApply (idempotence_wpr
              (λ OCV, crashed_at_offset OCV ∗ crashed_in_impl OCV)%I
              extra_state_nextgen
              s E1 e (e_rec `at` ⊥) _ _ _ (Φc ⊥)
                            with "[Hwpc] [Hidemp]").
    { iClear "Hidemp".
      rewrite wpc_eq /wpc_def /wpc /=.
      iSpecialize ("Hwpc" $! (e.(ts_view)) with "[//] [$]").
      destruct e.
      simpl.
      (* Set Printing All. *)
      iApply (program_logic.crash_weakestpre.wpc_mono' with "[] [] Hwpc").
      { iIntros ([v TV']) "(% & _ & $)". }
      { iIntros. iAccu. } }
    (* { iApply (wpc_crash_mono with "[] Hwpc"). *)
    (*   iIntros "HΦcx". iExists _. destruct nG. by iFrame. } *)
    iApply (plainly_mono with "[$]").
    iIntros "Hidemp Φc".
    iSpecialize ("Hidemp" with "Φc").
    iModIntro.
    rewrite /nextgen.nextgen /=.
    iIntros "!> %OCV [? ?] validV".
    iDestruct ("Hidemp" $! OCV with "[$] [$]") as "Hwpc".
    (* rewrite monPred_at_and monPred_at_embed. *)
    iSplit; first done.
    rewrite wpc_eq /wpc_def /wpc /=.
    iSpecialize ("Hwpc" $! ⊥ with "[//] [$]").
    iApply (program_logic.crash_weakestpre.wpc_mono' with "[] [] Hwpc").
    { iIntros ([v TV']) "(_ & _ & $)". }
    { iIntros. iAccu. }
  Qed.
End wpr.
