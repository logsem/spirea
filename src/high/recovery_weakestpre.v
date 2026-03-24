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
From self.high.modalities Require Import nextgen.
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
    nvm_heap_ctx σ1 -∗
    extra_state_interp -∗
    |==> ▷ ⚡==> |==> frag_history_at_crash ∗ nvm_heap_ctx σ2 ∗ extra_state_interp.
  Proof.
    intros Hcrash.
    iIntros "heap".
    iNamed 1.
    (* basic pure information *)
    iDestruct (big_sepM2_dom with "bumperSome") as %domAbsHistsBumpers.
    iDestruct (big_sepM2_dom with "predsFullReadHold") as %domPhysHistsAbsHists.
    iDestruct (big_sepM2_dom with "ordered") as %domAbsHistsOrders.
    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
    iAssert (∃ OCV, crashed_at_offset OCV)%I with "[offsets]" as (OCV) "#crashed_at_offset".
    { iNamed "offsets".
      by iExists _. }
    iAssert ⌜ ∀ ℓ : loc, ℓ ∈ dom offsets → offsets !! ℓ = Some (OCV !!0 ℓ) ⌝%I with "[offsets]" as %HOffsetOCV.
    { iNamed "offsets".
      iDestruct (crashed_at_offset_agree with "crashed_at_offset crashed") as %->.
      done. }
    (* we know that individual [phys_hist] and [abs_hist] has the same domain. *)
    iAssert ⌜ map_Forall (λ _ '(phys_hist, abs_hist), dom phys_hist = dom abs_hist) (map_zip phys_hists abs_hists) ⌝%I as %domAbsHistPhysHist.
    { iDestruct (big_sepM2_alt with "predsFullReadHold") as "[_ ?]".
      iApply big_sepM_pure_1.
      iApply (big_sepM_impl with "[$]").
      iIntros "!>" (ℓ [phys_hist abs_hist] [? ?]%map_lookup_zip_Some).
      iIntros "(% & % & % & % & % & % & ?)".
      simpl in *.
      iDestruct (big_sepM2_dom with "[$]") as %?.
      done. }
    (* information that requires the base interp to extract. *)
    iDestruct (nvm_heap_ctx_OCV_dom with "crashed_at_offset heap") as %[domOCVPV domOCVStore].
    iDestruct (nvm_heap_ctx_mapsto with "crashed_at_offset heap ptsMap") as %[domCVPhysHists physHistsEq].
    simpl in domCVPhysHists.

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

    (* relation between persisted view and crash view. *)
    iAssert ⌜ ∀ ℓ offset, offsets !! ℓ = Some offset → offset + (global_pview !!0 ℓ) ≤ OCV' !!0 ℓ ⌝%I as %pViewLb.
    { iIntros (ℓ offset ?).
      assert (ℓ ∈ dom offsets) by by apply elem_of_dom.
      assert (ℓ ∈ dom phys_hists) as [phys_hist ?]%elem_of_dom by set_solver.
      assert (ℓ ∈ dom abs_hists) as [abs_hist ?]%elem_of_dom by set_solver.
      iDestruct (big_sepM2_lookup _ _ _ ℓ with "predsPersHold") as "predP".
      { done. } { done. }
      iDestruct "predP" as (encp_pers t_p offset' encσ_p msg_p predPersLook offsetLook' encσPLook msgPLook <-) "[persisted predP]".
      assert (offset' = offset) as -> by by simplify_map_eq.
      subst OCV'.
      rewrite view_add_lookup_zero.
      specialize (HOffsetOCV ℓ ltac:(done)).
      simplify_map_eq.
      rewrite /lookup_zero.
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
      destruct (OCV !! ℓ) as [[] | ] eqn:Heq1;
        destruct (CV !! ℓ) as [[] | ] eqn:Heq2;
        rewrite ?Heq1 ?Heq2 /=.
      - intros incl'%Some_MaxNat_included.
        lia.
      - intros incl'%Some_MaxNat_included.
        lia.
      - intros incl'%Some_MaxNat_included.
        lia.
      - intros incl'. apply option_not_included_None in incl'. done. }
    
    (* obtain the assertions after crash. *)    
    iAssert (|==> ⚡==>
             (crashed_at CV ∗ persisted (view_to_zero OCV') ∗ frag_history_at_crash) -∗
             ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ drop_above_map OCV' phys_hists;abs_hist_trans bumpers OCV' abs_hists,
                encoded_full_read_predicates_hold ℓ abs_hist phys_hist (map_imap (drop_OCV_clear OCV') na_views) offsets'
                  (restrict (dom OCV') predicates_full) (restrict (dom OCV') predicates_read) ∗
                encoded_pers_predicate_holds ℓ abs_hist phys_hist (restrict (dom OCV') $ view_to_zero global_pview) offsets'
                  (restrict (dom OCV') predicates_pers)))%I with "[predsFullReadHold predsPersHold]" as ">predsHold".
    { (* TODO: make the lemma behave better *)
      rewrite -bupd_mono; last rewrite -nextgen_mono; last iApply big_sepM2_impl_persist; last done.
      rewrite -nextgen_big_sepM2 -big_sepM2_bupd.
      iPoseProof (big_sepM2_sep with "[$predsFullReadHold $predsPersHold]") as "predsHold".
      iDestruct (big_sepM2_impl_dom_subseteq _ _
                   _ _ (drop_above_map OCV' phys_hists) (abs_hist_trans bumpers OCV' abs_hists)
                   with "predsHold []") as "$".
      { rewrite /drop_above_map.
        etrans; first apply dom_imap_subseteq.
        done. }
      { done. }
      iIntros "!>" (ℓ phys_hist abs_hist phys_hist' abs_hist' physHistsLook absHistsLook physHistsLook' absHistsLook')
        "[predFR predP]".
      (* some pure facts *)
      assert (ℓ ∈ dom abs_hists) by (apply elem_of_dom; by eexists).
      assert (ℓ ∈ dom bumpers) as [bumper bumpersLook]%elem_of_dom by set_solver.
      assert (ℓ ∈ dom orders) as [order ordersLook]%elem_of_dom by set_solver.
      (* we only care about locations that survives *)
      destruct (decide (ℓ ∈ dom OCV')) as [ elemOfOCV' | ];
        last (rewrite restrict_lookup_not_elem_of // in absHistsLook').
      assert (drop_bump_map ℓ bumper OCV' abs_hist = abs_hist') as <-.
      { rewrite /abs_hist_trans in absHistsLook'.
        rewrite restrict_lookup_elem_of // map_lookup_imap absHistsLook /= /per_loc_trans bumpersLook in absHistsLook'.
        by simplify_eq. }
      pose proof elemOfOCV' as [[t_c] OCVLook' ]%elem_of_dom.
      assert (discard_msg_views <$> drop_above t_c phys_hist = phys_hist') as <-.
      { rewrite /drop_above_map map_lookup_imap physHistsLook /= in physHistsLook'.
        rewrite /drop_above_hist in physHistsLook'.
        rewrite OCVLook' /= in physHistsLook'.
        by simplify_eq. }
      assert (dom (discard_msg_views <$> drop_above t_c phys_hist) = dom (drop_bump_map ℓ bumper OCV' abs_hist)).
      { rewrite dom_fmap_L /drop_above /drop_bump_map /drop_above_map /drop_above_bump.
        rewrite set_eq.
        intros t.
        rewrite ?elem_of_dom.
        rewrite map_filter_lookup map_lookup_imap.
        apply (map_Forall_lookup_1 _ _ ℓ (phys_hist, abs_hist)) in domAbsHistPhysHist;
          last rewrite map_lookup_zip_Some //.
        simpl in domAbsHistPhysHist.
        destruct (abs_hist !! t) eqn:Hlook.
        - assert (is_Some (phys_hist !! t)) as [? ->] by (rewrite -elem_of_dom domAbsHistPhysHist elem_of_dom //).
          simpl.
          rewrite /lookup_zero OCVLook' /=.
          destruct (decide (t ≤ t_c)).
          + rewrite option_guard_True //.
          + rewrite option_guard_False //.
            split; by intros ?%is_Some_None.
        - assert (phys_hist !! t = None) as -> by (rewrite -not_elem_of_dom domAbsHistPhysHist not_elem_of_dom //).
          simpl.
          split; by intros ?%is_Some_None. }
      
      iDestruct "predFR" as (encp_full encp_read offset predFullLook predReadLook offsetLook) "predFR".
      iEval (rewrite /encoded_pers_predicate_holds) in "predP".
      iDestruct "predP" as (encp_pers t_p offset' encσ_p msg_p predPersLook offsetLook' encσPLook msgPLook <-) "[persisted predP]".
      assert (offset' = offset) as -> by by simplify_map_eq.
      assert (OCV' !!0 ℓ = t_c) as OCVLook0'.
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
      specialize (pViewLb ℓ offset ltac:(done)).
      iClear "persisted".
      
      destruct Hcrash as [store PV pIncl cut]. simpl in *.
      (* we should be able to find a message exactly at [t_c]. *)
      assert (is_Some (phys_hist !! t_c)) as [msg_c msgCLook].
      { apply consistent_cut_valid_slice in cut as valid.
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

      (* we extract the predicate held at crash timestamp. *)
      iPoseProof (big_sepM2_delete _ _ _ t_c msg_c encσ_c with "predFR") as "[predFR predFRRest]".
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

      (* specialize the implication as much as possible *)
      iDestruct (big_sepM2_lookup _ _ _ ℓ with "predFullNextgen") as (encp_full' encp_read' encp_pers' ? ? ?) "nextgen".
      { done. }
      { done. }
      destruct (phys_hist !! S t_c) as [msgSC | ] eqn:msgSCLook.
      - (* the crash timestamp is not exclusive, we need to apply the second case of [predFullNextgen] *)
        admit.
      - (* the crash timestamp is exclusive, we can apply the first case of [predFullNextgen]. *)
        rewrite decide_True; last done.
        clear OCVLook0'.
        simplify_map_eq.
        iDestruct (plainly_elim with "nextgen") as "NG".
        iDestruct ("NG" with "[//] predP predFR") as "[fullNG _]".
        iDestruct ("fullNG" with "[//]") as ">(%P_full' & %P_pers' & #PFullEquiv' & #PPersEquiv' & fullNG)".
        
        iDestruct (big_sepM2_impl_dom_subseteq _
                     (λ t msg_r encσ_r, ⚡==> (persisted (view_to_zero OCV') ∗ crashed_at CV ∗ frag_history_at_crash) -∗
                                        encoded_predicate_holds encp_read encσ_r
                                          (msg_val msg_r)
                                          (∅, ∅, ∅))%I
                     _ _ (delete t_c $ discard_msg_views <$> drop_above t_c phys_hist) (delete t_c $ drop_bump_map ℓ bumper OCV' abs_hist)
                     with "predFRRest []") as "predFRRest".
        { rewrite ?dom_delete dom_fmap /drop_above.
          apply difference_mono_r, dom_filter_subseteq. }
        { rewrite !dom_delete_L.
          by f_equiv. }
        { iIntros "!>" (t msg_r encσ_r msg_r' encσ_r' [? msgRLook]%lookup_delete_Some [_ encσRLook]%lookup_delete_Some [? msgRLook']%lookup_delete_Some [_ encσRLook']%lookup_delete_Some) "predR".
          assert (msg_r' = discard_msg_views msg_r) as ->.
          { apply lookup_fmap_Some in msgRLook' as (? & <- & msgRLook').
            f_equiv.
            apply map_filter_lookup_Some_1_1 in msgRLook'.
            by simplify_map_eq. }
          assert (t ≤ t_c).
          { apply lookup_fmap_Some in msgRLook' as (? & _ & msgRLook').
            by apply map_filter_lookup_Some_1_2 in msgRLook'. }
          iAssert ⌜ Some encσ_r' = bumper encσ_r ⌝%I as %bumperSomeR.
          { rewrite map_lookup_imap encσRLook /= /drop_above_bump in encσRLook'.
            destruct (decide _); last done.
            rewrite /safe_bumper in encσRLook'.
            iDestruct (big_sepM2_lookup _ _ _ ℓ with "bumperSome") as %bumperSomeR.
            { done. } { done. }
            iPureIntro.
            move: encσRLook'.
            eapply map_Forall_lookup_1 in bumperSomeR as [? -> ]; last done.
            done. }
          iAssert (encoded_predicate_holds encp_read encσ_r (msg_val msg_r)
                     (default (msg_store_view msg_r) (na_views !! ℓ), msg_persisted_after_view msg_r, ∅))%I with "[predR]" as "predR".
          { destruct (decide _); last done.
            iDestruct (big_sepM2_lookup with "predFullReadSplit") as "split".
            { done. } { done. }
            iDestruct ("split" with "predR") as "$". }
          iDestruct (big_sepM2_lookup _ _ _ ℓ with "predReadNextgen") as "nextgen'".
          { done. } { done. }
          iDestruct ("nextgen'" $! encσ_r encσ_r' with "[//] predR") as (P) "[#encpReadEquiv' ReadNG]".
          iModIntro.
          iIntros "#(persisted & CV & frag_impl)".
          iSpecialize ("ReadNG" with "frag_impl").
          iDestruct (big_sepM2_lookup _ _ _ ℓ with "oldViewsDiscarded") as %discarded.
          { done. } { done. }
          iSpecialize ("ReadNG" $! CV with "[]").
          (* [<NGF>] header *)
          { simpl.
            iFrame "CV".
            assert (msg_persisted_after_view msg_r ⊑ CV).
            { (* we need a different proof for messages from older generation. *)
              destruct (decide (t < OCV !!0 ℓ)).
              - rewrite -(discarded t _ ltac:(done) ltac:(done)) /=.
                solve_view_le.
              - eapply consistent_cut_extract.
                +  done.
                + done.
                + apply (map_Forall_lookup_1 _ phys_hists ℓ phys_hist) in physHistsEq; last done.
                  rewrite -physHistsEq //.
                + rewrite drop_prefix_lookup.
                  erewrite Nat.sub_add; first done.
                  lia.
                + rewrite PeanoNat.Nat.le_sub_le_add_l.
                  subst OCV'.
                  replace t_c' with (CV !!0 ℓ) by (rewrite /lookup_zero tCLook' //).
                  rewrite -view_add_lookup_zero /lookup_zero OCVLook' /=.
                  done. }
            iSplitPure; first done.
            iApply persisted_weak; last done.
            f_equiv.
            rewrite /OCV'.
            replace (msg_persisted_after_view msg_r) with (∅ `view_add` msg_persisted_after_view msg_r)
                                                          by apply view_add_empty.
            f_equiv; solve_view_le. }
          iExists P.
          iFrame "∗#".}
        rewrite nextgen_big_sepM2.
        iIntros "!>!> #(CV & persisted & frag_impl)".

        (* restore [p_full] and [p_pers] *)
        iSpecialize ("fullNG" with "frag_impl").
        iDestruct ("fullNG" $! CV with "[]") as "[F P]".
        (* [<NGF>] header *)
        { simpl.
          iFrame "CV".
          assert (msg_persisted_after_view msg_c ⊑ CV).
          { eapply consistent_cut_extract.
            +  done.
            + done.
            + apply (map_Forall_lookup_1 _ phys_hists ℓ phys_hist) in physHistsEq; last done.
              rewrite -physHistsEq //.
            + rewrite drop_prefix_lookup.
              erewrite Nat.sub_add; first done.
              lia.
            + rewrite PeanoNat.Nat.le_sub_le_add_l.
              subst OCV'.
              replace t_c' with (CV !!0 ℓ) by (rewrite /lookup_zero tCLook' //).
              rewrite -view_add_lookup_zero /lookup_zero OCVLook' /=.
              done. }
          iSplitPure; first done.
          iApply persisted_weak; last done.
          f_equiv.
          rewrite /OCV'.
          replace (msg_persisted_after_view msg_c) with (∅ `view_add` msg_persisted_after_view msg_c)
                                                        by apply view_add_empty.
          f_equiv; solve_view_le. }
        iSplitL "F predFRRest".
        + iExists encp_full, encp_read, t_c.
          iSplitPure; first rewrite restrict_lookup_elem_of //.
          iSplitPure; first rewrite restrict_lookup_elem_of //.
          iSplitPure.
          { subst offsets'.
            rewrite lookup_fmap restrict_lookup_elem_of; first rewrite OCVLook' //.
            rewrite elem_of_dom //. }
          iApply (big_sepM2_delete _ _ _ t_c with "[F predFRRest]").
          { rewrite lookup_fmap (map_filter_lookup_Some_2 _ _ _ msg_c) //. }
          { rewrite map_lookup_imap encσCLook /= /drop_above_bump decide_True //.
            rewrite /lookup_zero.
            by simplify_map_eq. }
          iSplitL "F"; first rewrite decide_True.
          * iExists P_full'.
            simpl.
            rewrite bumperSome.
            iFrame "PFullEquiv'".
            iApply (monPred_mono with "F").
            solve_view_le.
          * split; first done.
            rewrite lookup_fmap fmap_None /drop_above.
            apply map_filter_lookup_None_2.
            right.
            lia.
          * iApply (big_sepM2_impl with "predFRRest").
            iIntros "!>" (t msg_r encσ_r [? msgRLook]%lookup_delete_Some [_ encσRLook]%lookup_delete_Some) "predR".
            iSpecialize ("predR" with "[$]").
            assert (t ≤ t_c).
            { apply lookup_fmap_Some in msgRLook as (? & _ & msgRLook).
              by apply map_filter_lookup_Some_1_2 in msgRLook. }
            rewrite decide_False; last (rewrite not_and_l; left; lia).
            iApply (encoded_predicate_holds_mono with "predR").
            solve_view_le.
        + iExists encp_pers, t_c, t_c, encσ_c', (discard_msg_views msg_c).
          iSplitPure; first rewrite restrict_lookup_elem_of //.
          iSplitPure.
          { subst offsets'.
            rewrite lookup_fmap restrict_lookup_elem_of; first rewrite OCVLook' //.
            rewrite elem_of_dom //. }
          iSplitPure.
          { rewrite map_lookup_imap encσCLook /= /drop_above_bump decide_True //.
            - rewrite /safe_bumper bumperSome //.
            - rewrite /lookup_zero.
              by simplify_map_eq. }
          iSplitPure.
          { rewrite lookup_fmap (map_filter_lookup_Some_2 _ _ _ msg_c) //. }
          rewrite assoc.
          iSplitR.
          * rewrite /lookup_zero.
            rewrite ?restrict_lookup_elem_of //.
            rewrite /view_to_zero lookup_fmap.
            destruct (global_pview !! ℓ); last done.
            simpl.
            iSplitPure; first done.
            iApply persisted_persisted_loc; last done.
            by eapply view_to_zero_lookup.
          * iExists P_pers'.
            iFrame "∗#". }

    (* invoke base logic nextgen begins *)
    iDestruct (heap_ctx_next_generation _ _ _ Hcrash with "heap") as ">(% & OCV' & #mainpicked & heap)".
    iDestruct (crashed_at_offset_agree with "crashed_at_offset OCV'") as %<-.
    iClear "OCV'".
    iPoseProof (offset_auth_picked_out with "mainpicked offsets") as "offsets".
    (* invoke base logic nextgen ends *)

    (* [ |==> ] *)
    iModIntro.
    (* [ ▷ ] *)
    iModIntro.
    (* [ ⚡==> ] *)
    iModIntro.
    iDestruct "crashed_at_offset" as (? ?) "[picked_in OVOCV]".
    iPickedInAgree "mainpicked picked_in".
    iDestruct "allBumpers" as "[last_all_bumpers allBumpers]".
    iDestruct "allOrders" as "[last_all_orders allOrders]".
    iDestruct "history" as "[last_history history]".
    iDestruct "historyFragmentsNG" as "[#lastHistoryFragments historyFragmentsNG]".
    
    iMod (lastgen_ghost_map_auth_persist with "last_all_bumpers") as "#last_all_bumpers".
    iMod (lastgen_ghost_map_auth_persist with "last_all_orders") as "#last_all_orders".
    iMod (lastgen_full_map_persist with "last_history") as "#last_history".

    (* multiple places need [frag_history_at_crash] *)
    iAssert (frag_history_at_crash)%I as "#frag_impl".
    { iIntros (??????????).
      iDestruct ("historyFragmentsNG" with "[OVOCV]") as "#historyFragmentsNG".
      { by iExists _. }
      iModIntro.
      iIntros "OVOCV' %OCVLook' knowOrder knowBumper fragHist %".
      iDestruct (crashed_at_both_agree with "OVOCV OVOCV'") as %[ <- <- ].
      (* lookup bumper *)
      iDestruct "knowBumper" as "[% knowBumper]".
      iDestruct (lastgen_ghost_map_lookup with "last_all_bumpers knowBumper") as %?.
      (* lookup (encoded) state *)
      pose (tC := OCV' !!0 ℓ).
      assert (ℓ ∈ dom bumpers) by (apply elem_of_dom; by eexists).
        assert (ℓ ∈ dom phys_hists) as [phys_hist ?]%elem_of_dom by set_solver.
      assert (ℓ ∈ dom abs_hists) as [abs_hist ?]%elem_of_dom by set_solver.
      assert (∃ eσ_c, abs_hist !! tC = Some eσ_c)
        as (eσ_c & ?).
      { destruct Hcrash as [store PV pIncl cut]. simpl in *.
        assert (is_Some (CV !! ℓ)) as [[t_c'] tCLook'].
        { rewrite elem_of_dom lookup_merge in OCVLook'.
          destruct (OCV !! ℓ) eqn:Heqn; rewrite Heqn /= in OCVLook'.
          + rewrite -elem_of_dom.
            pose proof (elem_of_subseteq (dom PV) (dom CV)) as [Hsubset _].
            specialize (Hsubset ltac:(apply view_le_dom_subseteq; done)).
            apply Hsubset.
            pose proof (elem_of_subseteq (dom OCV) (dom PV)) as [Hsubset' _].
            apply Hsubset'; first done.
            rewrite elem_of_dom. by eexists.
          + destruct (CV !! ℓ); done. }
        (* for the timestamp, we need to go through physical history first *)
        assert (tC ∈ dom phys_hist) as physHistLook.
        { simpl in physHistsEq.
          apply consistent_cut_valid_slice in cut as valid.
          apply (valid_slice_lookup _ ℓ t_c' _ (drop_prefix phys_hist (OCV !!0 ℓ))) in valid; [ | done | ].
          - rewrite drop_prefix_lookup in valid.
            subst tC.
            rewrite view_add_lookup_zero {2}/lookup_zero tCLook' /=.
            rewrite elem_of_dom comm //.
          - symmetry.
            eapply (map_Forall_lookup_1 _ _ _ _ physHistsEq); done. }
        apply (map_Forall_lookup_1 _ _ ℓ (phys_hist, abs_hist)) in domAbsHistPhysHist;
          last rewrite map_lookup_zip_Some //.
        rewrite domAbsHistPhysHist in physHistLook.
        by apply elem_of_dom. }
      iDestruct (big_sepM_lookup _ _ ℓ with "historyFragmentsNG") as "ℓhistory".
      { rewrite /abs_hist_trans restrict_lookup_elem_of // map_lookup_imap /per_loc_trans.
        simplify_map_eq.
        done. }
      iDestruct (big_sepM_lookup _ _ tC with "ℓhistory") as "knowFragC".
      { rewrite /drop_bump_map map_lookup_imap.
        simplify_map_eq.
        rewrite /drop_above_bump decide_True //. }
      assert (OCV !!0 ℓ ≤ OCV' !!0 ℓ).
      { rewrite view_add_lookup_zero.
        lia. }
      iSplit; first done.
      assert (t ≤ OCV' !!0 ℓ) by (subst OCV'; lia).
      (* lookup [bumperSome] *)
      iDestruct (big_sepM2_lookup _ _ _ ℓ with "bumperSome") as %bumperSome.
      { done. } { done. }
      apply (map_Forall_lookup_1 _ _ tC eσ_c) in bumperSome as [eσ_c' bumperSome]; last done.
      (* lookup order *)
      iDestruct (lastgen_ghost_map_lookup with "last_all_orders knowOrder") as %?.
      iDestruct (big_sepM2_lookup _ _ _ ℓ with "ordered") as %ordered.
      { done. } { done. }
      (* lookup [σ] *)
      iDestruct "fragHist" as (eσ ?) "last_entry".
      iDestruct (lastgen_full_map_frag_entry with "[$] [$]") as %(? & ? & ?).
      simplify_map_eq.
      assert (∃ σ_c, decode eσ_c = Some σ_c ∧ σ ⊑ σ_c) as (σ_c & ? & ?).
      { destruct (decide (t = tC)) as [-> | ].
        + exists σ. by simplify_map_eq.
        + specialize (ordered t tC eσ eσ_c ltac:(lia) ltac:(done) ltac:(done)).
          apply encode_relation.encode_relation_inv in ordered as (σ' & σ_c & ? & ? & ?).
          exists σ_c.
          by simplify_map_eq. }
      iExists σ_c.
      iSplit; first done.
      iSplit.
      + iExists eσ_c, _.
        iSplit; first by iExists _.
        iSplit; first done.
        iDestruct (big_sepM_lookup _ _ ℓ with "lastHistoryFragments") as "lastHist".
        { done. }
        iDestruct (big_sepM_lookup _ _ tC with "lastHist") as "crashFrag".
        { done. }
        done.
      + iExists eσ_c'.
        apply encode_bumper_Some_decode in bumperSome as (σ_c' & ? & ?).
        simplify_map_eq.
        rewrite decode_encode.
        iSplit; first done.
        done. }

    iMod "heap" as "[#persisted heap]".
    
    iSpecialize ("predsHold" with "[]").
    { iFrame "frag_impl persisted".
      iExists OCV, OCV'.
      iDestruct "crashedRely" as (OPV) "[rely _]".
      iExists OPV.
      iFrame "rely OVOCV".
      iPureIntro.
      subst OCV'.
      rewrite map_eq_iff.
      intros ℓ.
      rewrite view_sub_lookup /lookup_zero /view_add lookup_merge.
      destruct (OCV !! ℓ) as [[] | ] eqn:Heq1; destruct (CV !! ℓ) as [[] | ] eqn:Heq2;
        rewrite ?Heq1 ?Heq2 /= //; try (do 2 f_equiv; lia).
      (* this is impossible because [dom OCV ⊆ dom PV ⊆ dom CV]. *)
      destruct Hcrash as [store PV pIncl cut]. simpl in *.
      assert (ℓ ∈ dom CV) as [? ?]%elem_of_dom; last congruence.
      apply (elem_of_weaken _ (dom PV)); last by apply dom_included.
      apply (elem_of_weaken _ (dom OCV)); last done.
      rewrite elem_of_dom //. }
    iDestruct (big_sepM2_sep with "predsHold") as "[predsFullReadHold predsPersHold]".
    (* [ |==> ] *)
    iModIntro.

    iAssert (crashed_at_offset OCV')%I as "OCV'".
    { by iExists _. }

    iDestruct "naView" as "[_ naView]".
    
    Ltac solve_crashed_at hyps :=
      match hyps with
      | nil => idtac
      | cons ?H ?hyps' => 
          (* Try to apply your tactic to the head of the list *)
          (iSpecialize (H with "OCV'")); 
          solve_crashed_at hyps'
      end.
    
    solve_crashed_at ["ptsMap"; "physHists"; "full_predicates"; "read_predicates"; "pers_predicates"; "naView";
                      "allOrders"; "naLocs"; "atLocs"; "history"; "historyFragmentsNG"; "allBumpers"; "atLocsHistories"].

    iFrame "frag_impl heap".
    iExists (drop_above_map OCV' phys_hists), (abs_hist_trans bumpers OCV' abs_hists), (restrict (dom OCV') $ view_to_zero global_pview),
            (restrict (dom OCV') predicates_full), (restrict (dom OCV') predicates_read), (restrict (dom OCV') predicates_pers),
            (restrict (dom OCV') orders), (restrict (dom OCV') bumpers).
    iExists (na_locs ∩ dom OCV'), (at_locs ∩ dom OCV'), offsets', (const ∅ <$> restrict (dom OCV') na_views).

    iFrame "ptsMap physHists full_predicates read_predicates pers_predicates naView offsets
            allOrders naLocs atLocs history historyFragmentsNG allBumpers predsPersHold".
    iSplit. (* [#crashedRely] *)
    { iDestruct "crashedRely" as (?) "[rely ?]". iExists _. iApply "rely". }
    iSplit. (* oldViewsDiscarded *)
    { iApply (big_sepM2_impl_dom_subseteq with "oldViewsDiscarded").
      { rewrite /drop_above_map.
        etrans; first apply dom_imap_subseteq.
        done. }
      { subst offsets'.
        rewrite dom_drop_above_map dom_fmap_L restrict_dom_L.
        set_solver. }
      iIntros "!>" (ℓ phys_hist offset phys_hist' offset' pLook oLook pLook' oLook' discarded t msg ? msgLook).
      iPureIntro.
      assert (ℓ ∈ dom offsets) by by apply elem_of_dom.
      assert (discard_msg_views <$> drop_above offset' phys_hist = phys_hist') as <-.
      { rewrite /drop_above_map map_lookup_imap pLook /= in pLook'.
        rewrite /drop_above_hist in pLook'.
        subst offsets'.
        apply lookup_fmap_Some in oLook' as ([] & <- & oLook').
        rewrite restrict_lookup_elem_of // in oLook'.
        rewrite oLook' /= in pLook'.
        by simplify_eq. }
      apply lookup_fmap_Some in msgLook as (? & <- & ?).
      rewrite /discard_msg_views /= //. }
    (* iSplitPure. *)
    (* { rewrite dom_fmap_L restrict_dom_L -offsetsDom. *)
    (*   apply dom_imap_L. *)
    (*   intros ℓ; split; intros H. *)
    (*   - apply elem_of_intersection in H. *)
    (*     rewrite /drop_above_hist. *)
    (*     destruct H as [[hist ?]%elem_of_dom [[t] ->]%elem_of_dom]. *)
    (*     exists hist. split; first done. *)
    (*     by simpl. *)
    (*   - destruct H as (hist & Hdom%elem_of_dom_2 & Hdrop%fmap_is_Some%elem_of_dom). *)
    (*     set_solver. } *)
    (* locsDisjoint *)
    iSplitPure; first set_solver.
    iSplitPure. (* histDomLocs *)
    { rewrite dom_abs_hist_trans; set_solver. }
    (* naViewsDom *)
    iSplitPure; first (rewrite dom_fmap_L restrict_dom_L; set_solver).
    (* [shared_locs_inv] *)
    iSplitPure.
    { rewrite /shared_locs_inv.
      rewrite /map_map_Forall.
      eapply map_Forall_subseteq. { apply restrict_subseteq. }
      intros ℓ hist look t newMsg histLook.
      apply map_lookup_zip_with_Some in look as (hist' & off & -> & look & offsetsLook).
      rewrite map_lookup_imap in look.
      apply bind_Some in look as (hist & ? & look).
      assert (discard_msg_views <$> drop_above off hist = hist') as <-.
      { rewrite /drop_above_hist -lookup_fmap in look.
        apply lookup_fmap_Some in look as ([] & <- & look).
        f_equiv.
        f_equiv.
        subst offsets' OCV'.
        simplify_map_eq.
        rewrite -lookup_fmap in offsetsLook.
        apply lookup_fmap_Some in offsetsLook as (? & <- & offsetsLook).
        apply restrict_lookup_Some in offsetsLook as [offsetsLook _].
        by simplify_map_eq. }
      rewrite drop_prefix_fmap in histLook.
      apply lookup_fmap_Some in histLook as ([] & <- & histLook). 
      apply drop_prefix_drop_above in histLook as [? ?].
      split; last done.
      rewrite /discard_msg_views /= view_lookup_zero_empty //. }
    iSplitL "atLocsHistories".
    { rewrite -restrict_abs_hist_trans.
      iDestruct (big_sepM_impl_dom_subseteq _ _ _
                   (restrict (at_locs ∩ dom OCV')
                      (abs_hist_trans bumpers OCV' abs_hists))
                  with "atLocsHistories []") as "[$ _]".
      - rewrite ?restrict_dom_L. set_solver.
      - iIntros "!>" (ℓ abs_hist abs_hist' absHistsLook absHistsLook') "full_entry".
        assert (abs_hist = abs_hist') as ->; last done.
        destruct (decide (ℓ ∈ dom OCV'));
          last (rewrite restrict_lookup_not_elem_of // in absHistsLook'; set_solver).
        destruct (decide (ℓ ∈ at_locs));
          last (rewrite restrict_lookup_not_elem_of // in absHistsLook'; set_solver).
        move: absHistsLook absHistsLook'.
        rewrite ?restrict_lookup_elem_of //; last set_solver.
        congruence. }
    iSplit; first admit. (* [ordered] *)
    (* [histPViewDoms] *)
    iSplitPure.
    { rewrite dom_abs_hist_trans; last set_solver.
      rewrite restrict_dom_L /view_to_zero dom_fmap_L.
      set_solver. }
    iSplitL "predsFullReadHold"; first rewrite map_imap_drop_OCV_clear_restrict //.
    
    
    
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
              (frag_history_at_crash)
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
    rewrite /nextgen.nextgen /=.
    iIntros "!> !> Hfrag".
    iSpecialize ("Hidemp" with "Hfrag").
    iIntros "validV".
    iDestruct "Hidemp" as "Hwpc".
    (* rewrite monPred_at_and monPred_at_embed. *)
    iSplit; first done.
    rewrite wpc_eq /wpc_def /wpc /=.
    iSpecialize ("Hwpc" $! ⊥ with "[//] [$]").
    iApply (program_logic.crash_weakestpre.wpc_mono' with "[] [] Hwpc").
    { iIntros ([v TV']) "(_ & _ & $)". }
    { iIntros. iAccu. }
  Qed.
End wpr.
