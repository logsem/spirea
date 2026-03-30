From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice ipm_tactics.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state increasing_map.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_na.
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).

  Lemma wp_store_na ℓ prot ss v s__last s st E `{!ProtocolConditions prot} :
    last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_na ℓ prot 1 ss ∗ prot.(p_full) s v }}}
      #ℓ <-_NA v @ st; E
                         {{{ RET #(); mapsto_na ℓ prot 1 (ss ++ [s]) }}}.
  Proof.
    intros last stateGt Φ.
    iModel.
    iIntros "(pts & phi)".
    rewrite /mapsto_na.
    iDestruct "pts" as (?tP ?tS offset SV absHist msg) "pts". iNamed "pts".
    assert (a = s__last) as -> by congruence.
    iNamed "locationProtocol".
    iDestruct "inThreadView" as %inThreadView.

    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV' PV] BV] incl2) "#val".

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. } { by apply prim_step_store_no_fork. }
    iNamed 1.
    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.


    assert (SV ⊑ SV') as svInclSv'.
    { destruct TV as [[??]?]. destruct TV' as [[??]?].
      etrans; first apply inThreadView.
      etrans; first apply incl.
      apply incl2. }

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "full_predicates knowFullPred")
      as (predFull predsFullLook) "#predFullEquiv".
    iDestruct (own_all_preds_pred with "read_predicates knowReadPred")
      as (predRead predsReadLook) "#predReadEquiv".
    
    iDestruct (ghost_map_lookup with "allOrders knowPreorder")
      as %ordersLook.

    iDestruct (full_map_full_entry with "history hist") as %absHistsLook.

    iDestruct (offset_loc_offset_auth_agree with "offset offsets") as %?.

    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook]
                                            by by eapply map_dom_eq_lookup_Some.
    iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]"; first done.

    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ OCV !!0 ℓ = offset ⌝)%I as (OCV) "[#crashed_at_offset <-]".
    { iDestruct "offset" as (?) "(? & ? & %)".
      iExists _.
      by iFrame "#". }

    iApply (wp_store_alt with "[$crashed_at_offset $pts $val]").
    iIntros "!>" (tT) "(%look & %gt & #valNew & pts)".
    simpl in gt.
    
    iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".

    iAssert (⌜ absHist !! (tT)%nat = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_lookup_acc with "predsFullReadHold") as "[predMap predsHold]".
      { done. } { done. }
      iDestruct "predMap" as (pred' offset' ????) "predMap".

      iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite -!not_elem_of_dom. rewrite domEq. rewrite dom_fmap. done. }

    iDestruct (
        location_sets_singleton_included with "naLocs isNaLoc"
      ) as %ℓEx.
    assert (ℓ ∉ at_locs) as ℓnotSh by set_solver.
    (* Update the ghost state for the abstract history. *)
    iMod (full_map_full_entry_insert _ _ _ _ _ (encode s) with "history hist")
      as "(history & hist & #newHistFrag)".
    { rewrite lookup_fmap. erewrite absHistLook. done. }

    (* Update ghost state. *)
    set (newMsg := Msg v ∅ ∅ PV).
    iMod (auth_map_map_insert _ _ _ _ _ _ newMsg with "physHists")
      as "(physHists & #physHistFrag)".
    { done. } { done. }

    iDestruct (ghost_map_lookup with "naView knowSV") as %ℓnaView.

    iMod (ghost_map_update (<[ℓ:=MaxNat (tT - (OCV !!0 ℓ))]>SV') with "naView knowSV")
      as "[naView knowSV]".

    assert (tS - (OCV !!0 ℓ) ≤ SV' !!0 ℓ) as tSle.
    { etrans; first done. by f_equiv. }
    assert (tS < tT) as tSLttT by lia.

    rewrite /validV.
    iModIntro.
    iFrame "valNew".
    rewrite -assoc.
    iSplit.
    { iPureIntro. repeat split; [|done|done]. apply view_insert_le. simpl. lia. }
    simpl.
    iSplitL "Φpost isNaLoc hist knowSV".
    { iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".
      { iPureIntro. etrans; first done.
        solve_view_le. }
      iExists _, (tT), (OCV !!0 ℓ), _, _, _, _.
      iSplitPure. { rewrite last_snoc. reflexivity. }
      iSplit. { iFrameNamed. }
      iFrame "physHistFrag".
      rewrite /know_full_history_loc.
      rewrite /full_entry_unenc.
      rewrite /history_full_entry_encoded.
      iEval (rewrite -fmap_insert) in "hist".
      iFrame "hist".
      iFrame "∗#".
      (* [incrMap] *)
      iSplitPure. { apply: increasing_map_insert_last; eauto. }
      (* [lookupV] *)
      iSplitPure. { rewrite lookup_insert_eq. done. }
      (* [nolater] *)
      iSplitPure.
      { eapply map_no_later_insert; last done.
        lia. }
      (* etrans; first apply haveTStore. *)
      (* apply Nat.lt_le_incl. eapply Nat.le_lt_trans; last apply gt. *)
      (* f_equiv. *)
      (* apply svInclSv'. } *)
      (* [histFrag] *)
      iSplit.
      { iExists _. iFrame "newHistFrag". by rewrite decode_encode. }
      (* [knowSV] *)
      iSplit.
      { Transparent know_na_view. done. }
      (* [slice] *)
      iSplit. {
        iPureIntro. eapply map_sequence_insert_snoc; [|done|done].
        lia. }
      (* [inThreadView] *)
      iSplit. {
        iPureIntro. repeat split.
        - done.
        - done.
        - apply view_empty_least. }
      (* [haveTSore] *)
      iPureIntro. rewrite lookup_zero_insert. split; lia. }
    iExistsN.
    iFrame "physHists naView history
            full_predicates read_predicates pers_predicates
            allOrders naLocs atLocs allBumpers".
    iFrame "ptsMap crashedRely offsets".
    (* [offsetsDom] *)
    iSplitPure.
    { rewrite dom_insert_L.
      assert (ℓ ∈ dom phys_hists) by by apply elem_of_dom.
      set_solver. }
    (* (* [oldViewsDiscarded] *) *)
    (* iSplit. *)
    (* { iApply (big_sepM2_insert_2 with "[] oldViewsDiscarded"). *)
    (*   iIntros (t2 ?). *)
    (*   iDestruct (big_sepM2_lookup _ _ _ ℓ with "oldViewsDiscarded") as %hi; *)
    (*     [done|done|]. *)
    (*   destruct (decide (tT + offset = t2)) as [<-|neq]. *)
    (*   - iIntros (?). lia. *)
    (*   - rewrite lookup_insert_ne; last done. *)
    (*     iPureIntro. apply hi. } *)
    (* [historyFragments] *)
    iSplit.
    { erewrite <- (insert_id offsets); last done.
      iApply (big_sepM_insert_2 with "[] historyFragments").
      iDestruct (big_sepM_lookup with "historyFragments") as "F"; first done.
      iApply (big_sepM_insert_2 with "newHistFrag F"). }
    repeat (rewrite dom_insert_lookup_L; last (rewrite -elem_of_dom; set_solver)).
    rewrite restrict_insert_not_elem; last set_solver.
    iFrame "atLocsHistories".
    repeat (iSplitL "";
            first solve [
                iPureIntro; done |
                iAssumption ]).
    (* [mapShared] *)
    iSplitPure.
    { rewrite -(insert_id offsets ℓ (OCV !!0 ℓ)) //.
      rewrite -map_insert_zip_with restrict_insert_not_elem; last set_solver.
      done. }
    iSplit.
    (* [ordered] *)
    { iApply (big_sepM2_update_left with "ordered"); eauto.
      iIntros (orderedForall).
      iPureIntro.
      apply: increasing_map_insert_last.
      - eauto.
      - apply map_no_later_fmap. done.
      - lia.
      (* eapply Nat.le_lt_trans; last apply gt. *)
      (* etrans; first apply haveTStore. *)
      (* f_equiv. done. *)
      - rewrite lookup_fmap. rewrite lookupV. done.
      - eapply encode_relation_decode_iff; eauto using decode_encode. }
    iSplitPure; first done.
    (* deal with the case analysis part last *)
    rewrite (comm bi_sep ("predsFullReadHold" ∷ _)) -!(assoc bi_sep).
    iSplitL "predsPersHold".
    { iApply (big_sepM2_impl with "[predsPersHold]").
      - iApply (big_sepM2_update with "predsPersHold"); [ done | done | ].
        repeat (iApply bi.exist_mono; intros).
        f_equiv. f_equiv.
        iIntros "(%absLook & %physLook & $)".
        pose proof absLook.
        apply elem_of_dom_2 in absLook.
        rewrite dom_fmap in absLook.
        assert (tT ∉ dom absHist) by rewrite not_elem_of_dom //.
        assert (a0 ≠ tT) by set_solver.
        repeat (rewrite lookup_insert_ne; last done).
        iFrame "%".
      - naive_solver. }
    repeat (iSplitL "";
            first solve [
                iPureIntro; done |
                iAssumption ]).
    (* [bumperSome] *)
    iSplit.
    { iEval (erewrite <- (insert_id bumpers ℓ); last done).
      iApply (big_sepM2_update with "bumperSome"); [ done | done | ].
      iPureIntro.
      apply map_Forall_insert_2.
      rewrite encode_bumper_encode //. }
    (* [predsFullReadHold] *)
    iDestruct (big_sepM2_delete with "predsFullReadHold") as "[predFR predsHold]".
    { done. } { done. }
    (* grow [na_views] in [predsHold]
     * [<[ℓ:= <[ℓ:= MaxNat (tT - (OCV !!0 ℓ))]> SV']> na_views] *)
    iDestruct (big_sepM2_impl with "predsHold []") as "predsHold".
    { iIntros "!>" (??? Hlook ?) "H".
      iApply (encoded_full_read_predicates_hold_equiv _ _ _ _ (<[ℓ:= <[ℓ:= MaxNat (tT - (OCV !!0 ℓ))]> SV']> na_views) with "H"); [ | done | done | done ].
      rewrite lookup_insert_ne; first done.
      simplify_map_eq.
      apply lookup_delete_Some in Hlook.
      naive_solver. }
    iDestruct (big_sepM2_insert_delete with "[phi predFR $predsHold]") as "$".
    iDestruct "predFR" as (??????) "predFR".
    iAssert ⌜ dom physHist = dom absHist ⌝%I as %domEq.
    { iDestruct (big_sepM2_dom with "predFR") as "%domEq".
      iPureIntro. rewrite dom_fmap_L // in domEq. }
    iDestruct (big_sepM2_lookup with "predFullReadSplit") as "split".
    { done. } { done. }
    iExists _, _, (OCV !!0 ℓ).
    iFrame "%".
    iDestruct (big_sepM2_insert _ physHist (encode <$> absHist) tT newMsg (encode s) with "[phi predFR]") as "$".
    { done. } { rewrite lookup_fmap absHistLook //. }
    iSplitL "phi"; last first.
    - iApply (big_sepM2_impl with "predFR").
      iIntros "!>" (t' msg_old encσ_old physHistLook absHistLook') "pred".
      rewrite lookup_insert_eq /=.
      destruct (decide (tT = S t')) as [-> | ].
      + rewrite lookup_insert_eq.
        iEval (rewrite decide_False; last naive_solver).
        case: (decide _) => [ [? ?] | ?].
        * iDestruct ("split" with "pred") as "pred".
          iApply (encoded_predicate_holds_mono with "pred").
          simplify_map_eq.
          solve_view_le.
        * iApply (encoded_predicate_holds_mono with "pred").
          simplify_map_eq.
          solve_view_le.
      + rewrite lookup_insert_ne; last done.
        simplify_map_eq.
        case: (decide _) => [ [? ?] | ?].
        * iApply (encoded_predicate_holds_mono with "pred").
          simplify_map_eq.
          solve_view_le.
        * iApply (encoded_predicate_holds_mono with "pred").
          simplify_map_eq.
          solve_view_le.
    - rewrite decide_True.
      + simplify_map_eq.
        destruct (TV) as [[??]?].
        destruct (TV') as [[??]?].
        iDestruct (into_no_buffer_at with "phi") as "phi".
        rewrite -encoded_predicate_holds_mono.
        iApply (predicate_holds_phi_decode_2 with "predFullEquiv phi"); first apply decode_encode.
        split; last solve_view_le.
        split; solve_view_le.
      + split; first lia.
        rewrite lookup_insert_ne; last done.
        rewrite -not_elem_of_dom domEq not_elem_of_dom.
        apply nolater.
        lia.
  Qed.
End wp_na.
