From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self.algebra Require Export ghost_map.
From self Require Export extra ipm_tactics solve_view_le.
From self.high Require Export dprop dprop_liftings.
From self Require Export view.
From self Require Export lang.
From self.base Require Import primitive_laws.
From self.lang Require Import syntax tactics lemmas.
From self.high Require Import resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol locations.

From self.high Require Import weakestpre.

Section wp_rules.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (ϕ : ST → val → nvmDeltaG → dProp Σ) (prot: LocationProtocol ST).
  (* let's try a single location modality, just to make it easier on first attempt *)

  Definition R_progress ℓ prot s Q: dProp Σ :=
    ∀ s_p v_p v, ∃ p_pers_obj p_read_obj,
             (prot.(p_pers) s_p v_p -∗ □ <obj> p_pers_obj) ∗
             (prot.(p_read) s v -∗ □ <obj> p_read_obj) ∗
             (p_pers_obj -∗ p_read_obj -∗
              (⌜ s_p ⊑ s ⌝ ==∗ prot.(p_pers) s v ∗ Q) ∧
              (⌜ s ⊑ s_p ⌝ ==∗ Q)).

  Definition post_fence_sync_l i ℓ prot (P : dProp Σ): iProp Σ :=
    let nD := i.2 in
    ∃ Q, ⌜ Objective Q ⌝ ∗
      (∃ offset t s, ⌜ {[ ℓ := MaxNat (t - offset) ]} ≼ buffer_view i.1 ⌝ ∗
                     offset_loc ℓ offset ∗
                     is_at_loc ℓ ∗
                     know_protocol ℓ prot ∗
                     ⎡ know_frag_history_loc ℓ t s ⎤ ∗
                     R_progress ℓ prot s Q) (∅, ∅, ∅, i.2) ∗
      (persisted (buffer_view i.1) -∗ (* comes from [fence_sync] instruction *)
       Q (∅, ∅, ∅, i.2) -∗ (* comes from atomic resrouce exchange at [fence_sync] *)
       P ((store_view i.1, (flush_view i.1 ⊔ buffer_view i.1), buffer_view i.1), i.2)).

  Program Definition post_fence_sync
    (ℓ: loc) prot (P : dProp Σ) : dProp Σ :=
    MonPred (λ i, post_fence_sync_l i ℓ prot P) _.
  Next Obligation.
    intros ???.
    do 2 intros [[[??]?]?].
    intros [[[??]?] [= ->]].
    simpl.
    assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
    rewrite /post_fence_sync_l //=.
    iIntros "(%Q & % & progress & impl)".
    iExists Q.
    iSplit; first done.
    iSplitL "progress".
    { iDestruct "progress" as (offset t s) "(%Hincluded & ?)".
      iExists offset, t, s.
      iFrame. iPureIntro.
      etrans; done. }
    iIntros "persisted Q".
    iApply monPred_mono; last iApply ("impl" with "[persisted]").
    { repeat split; done. }
    { iApply (persisted_anti_mono with "persisted"). done. }
    { done. }
  Qed.

  Lemma wp_flush_lb ℓ prot s st E Q `{!Objective Q}:
    {{{ store_lb ℓ prot s ∗
        is_at_loc ℓ ∗
        <obj> R_progress ℓ prot s Q }}}
      Flush #ℓ @ st; E
    {{{ RET #();
      post_fence_sync ℓ prot (persist_lb ℓ prot s ∗ Q)
    }}}.
  Proof.
    intros Φ.
    iModel.
    destruct TV as [[? ?] ?].
    iIntros "(#lb & #is_at_loc & progress)".
    iDestruct "lb" as (tS offset) "H". iNamed "H". iNamed "lbBase".
    iDestruct "tSLe" as %tSLe.

    iIntros ([[[??]?] ?] [? [= <-]]) "HΦ".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_flush_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* Get the points-to predicate. *)
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(_ & _ & _ & order & _)".
    (* TODO: this is weird *)
    rewrite /know_preorder_loc_d lift_d_at.
    iDestruct (ghost_map_lookup with "allOrders order") as %look.
    iDestruct (big_sepM2_dom with "ordered") as %domEq.
    iDestruct (big_sepM2_dom with "predsFullHold") as %domEq2.
    assert (is_Some (phys_hists !! ℓ)) as [physHist ?].
    { apply elem_of_dom. rewrite domEq2 domEq. apply elem_of_dom. naive_solver. }
    rewrite /offset_loc /is_at_loc /know_frag_history_loc_d 3!lift_d_at.
    iDestruct (ghost_map_lookup with "offsets offset") as %?.
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]".
    { apply map_lookup_zip_with_Some. naive_solver. }

    iApply (wp_flush (extra := {| extra_state_interp := True |}) with "pts").
    iNext. iIntros "pts".
    iDestruct ("ptsMap" with "pts") as "ptsMap".

    assert (tS - offset ≤ SV !!0 ℓ) as tSLe2.
    { etrans; first apply tSLe. simpl.
      f_equiv. etrans; first apply H1. apply incl. }
    rewrite -assoc.
    iSplitPure.
    { repeat split; try done. apply view_le_lub_r. done. }
    iFrame "val".
    iSplitL "HΦ progress".
    { iEval (monPred_simpl) in "HΦ". iApply "HΦ".
      { iPureIntro. split; last done. solve_view_le. }
      rewrite /post_fence_sync /post_fence_sync_l.
      iSimpl.
      iExists Q.
      iSplit; first done.
      iSplitL "progress".
      { iExists offset, tS, s.
        iSplitPure.
        { etrans; last apply view_le_l.
          apply (singleton_mono ℓ (MaxNat (tS - offset)) (MaxNat (SV !!0 ℓ))).
          rewrite max_nat_included //. }
        iEval (rewrite /offset_loc lift_d_at).
        iSplitR; first iApply "offset".
        iSplitR; first (rewrite /is_at_loc; simpl; iApply "is_at_loc").
        iSplitR.
        { rewrite /know_full_pred_d ?lift_d_at.
          iNamed "locationProtocol".
          iFrame "#".
        }
        iSplitR; first iApply "knowFragHist".
        rewrite monPred_at_objectively. iApply "progress". }
      iIntros "#pers Q".
      rewrite /persist_lb.
      repeat (rewrite bi.sep_exist_r; iExists _).
      simpl. rewrite !monPred_at_embed.
      iFrame "locationProtocol".
      iFrame "knowFragHist".
      iFrame "offset".
      rewrite -?bi.sep_assoc.
      iSplitPure; first done.
      simpl.
      iSplitR.
      { simpl. iPureIntro.
        rewrite !lookup_zero_lub.
        rewrite lookup_zero_singleton.
        lia. }
      iSplitR.
      2: {
        iApply monPred_mono; last iApply "Q".
        solve_view_le.
        repeat first [ apply view_empty_least | split ].
      }
      destruct (BV !! ℓ) as [[?]|] eqn:bvLook.
      * iApply (persisted_persisted_loc_weak with "pers").
        { apply lookup_join; last done.
          rewrite lookup_singleton. done. }
        lia.
      * iApply (persisted_persisted_loc_weak with "pers").
        { rewrite lookup_op.
          rewrite bvLook.
          rewrite right_id.
          rewrite lookup_singleton. done. }
        lia. }
    iExistsN.
    iFrame "#∗%".
  Qed.

  Lemma wp_fence_sync (ℓ: loc) (prot: LocationProtocol ST) `{!ProtocolConditions prot} (st : stuckness) (E : coPset) (P : dProp Σ) :
    {{{ post_fence_sync ℓ prot P }}} FenceSync @ st; E {{{ RET #(); P }}}.
  Proof.
    intros Φ.
    iModel. destruct TV as [[sv pv] bv].
    iIntros "H".

    iIntros ([[[??]?] ?] [view_incl [= <-]]) "HΦ".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] view_incl') "#val".
    iApply wp_extra_state_interp. { done. } { apply prim_step_fence_sync_no_fork. }
    iNamed 1.

    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    (* since the agreement on predicate content is under a later modality, we need to *)
    iPoseProof (own_all_full_preds_pred with "[$] [-]") as (predFull predsFullLook) "#predFullEquiv".
    { iDestruct "H" as (??) "[(% & % & % & _ & _ & _ & (? & ? & ? & _) & _) _]". rewrite ?lift_d_at //=. }
    iPoseProof (own_all_read_preds_pred with "[$] [-]") as (predRead predsReadLook) "#predReadEquiv".
    { iDestruct "H" as (??) "[(% & % & % & _ & _ & _ & (? & ? & ? & _) & _) _]". rewrite ?lift_d_at //=. }
    iPoseProof (own_all_pers_preds_pred with "[$] [-]") as (predPers predsPersLook) "#predPersEquiv".
    { iDestruct "H" as (??) "[(% & % & % & _ & _ & _ & (? & ? & ? & _) & _) _]". rewrite ?lift_d_at //=. }

    iApply (primitive_laws.wp_fence_sync (extra := {| extra_state_interp := True |}) with "[//]").
    simpl.
    monPred_simpl.
    iNext. iIntros "#pers".
    cbn.
    iDestruct "H" as (Q?) "[(%offset & %tS & %s & (%HtS & #offset & #atLoc & #knowProtocol & (%encS & %Hencode & knowHistFrag) & progress)) H]".
    simpl in HtS.
    rewrite /offset_loc lift_d_at.
    iPoseProof (ghost_map_lookup with "offsets offset") as "%".
    iPoseProof (ghost_map_map.full_map_frag_entry with "history knowHistFrag") as (absHist) "[% %absHistLook]".
    (* gather the physical value for the modal timestamp *)
    iAssert ⌜ is_Some (phys_hists !! ℓ) ⌝%I as (physHist) "%physHistsLook". {
      iDestruct (big_sepM2_dom with "predsFullHold") as %domEq.
      iPureIntro.
      rewrite -elem_of_dom domEq elem_of_dom.
      by eexists.
    }
    iAssert ⌜ is_Some (physHist !! tS) ⌝%I as (msg) "%physHistLook". {
      iDestruct (big_sepM2_lookup with "predsFullHold") as "(% & % & ? & ? & Hlook)";
        [ exact: physHistsLook | done | ].
      iDestruct (big_sepM2_dom with "Hlook") as %domEq.
      iPureIntro.
      rewrite -elem_of_dom domEq elem_of_dom.
      by eexists.
    }

    (* We now extract the old [p_pers] assertion *)
    iDestruct (big_sepM2_delete with "predsPersHold")
      as "[(%predPers' & %tP & %encSP & %msgP & % & %localPView & % & % & predPersHolds) predsPersRest]";
      [ exact physHistsLook | done | ].
    replace (predPers') with (predPers); last by simplify_map_eq.
    iAssert (⌜ ∃ SP, decode encSP = Some SP ⌝)%I as (SP) "%eqP". {
      iDestruct "predPersHolds" as (PP) "[#eqP _]".
      iEval (rewrite discrete_fun_equivI) in "predPersEquiv".
      iSpecialize ("predPersEquiv" $! encSP).
      iEval (rewrite discrete_fun_equivI) in "predPersEquiv".
      iSpecialize ("predPersEquiv" $! (msg_val msgP)).
      iRewrite "predPersEquiv" in "eqP".
      iPoseProof (encode_predicate_decode (p_pers prot) encSP (msg_val msgP) PP with "eqP") as (SP) "%decodeSP".
      iExists _. done.
    }
    iPoseProof (predicate_holds_phi_decode with "predPersEquiv predPersHolds") as "pred_pers_holds";
      first done.
    (* before anything, we first construct the updated [global_pview] *)
    set global_pview' := (global_pview ⋅ {[ ℓ := MaxNat (tS - offset) ]}).
    (* proof that we know [global_pview'] is persisted. *)
    iAssert (persisted global_pview')%I with "[]" as "#globalPViewPersisted'". {
      rewrite /global_pview' /persisted.
      iCombine "globalPViewPersisted pers" as "newGlobalPViewPersisted".
      iApply (own_mono with "newGlobalPViewPersisted").
      apply auth_frag_mono, cmra_mono_l.
      etrans; last apply view_incl'.
      etrans; last apply view_incl.
      done.
    }
    (* since we are dealing with the persisted view here, might as well simplify the modality resource *)
    iDestruct ("H" with "[pers]") as "H".
    { iApply persisted_weak; last iApply "pers". etrans; [ apply view_incl | apply view_incl' ]. }

    set predsFullHold := (([∗map] _ ↦ _; _ ∈ _; _, ∃ _ _, ⌜ predicates_full !! _ = _ ⌝ ∗ _))%I.
    set predsReadHold := (([∗map] _ ↦ _; _ ∈ _; _, ∃ _ _, ⌜ predicates_read !! _ = _ ⌝ ∗ _))%I.
    set predReadHolds := (encoded_predicate_holds
                            predRead
                            encS
                            (msg_val msg)
                            ((default
                                (msg_store_view msg)
                                (na_views !! ℓ),
                                msg_persisted_after_view msg, ∅, gnames)))%I.
    (* TODO: refactor this part into a separate lemma as I recall several places requires
     * this proof in one form or another. *)
    iAssert (predReadHolds ∗ (predReadHolds -∗ predsFullHold ∗ predsReadHold))%I
      with "[predsReadHold predsFullHold]" as "[predReadHolds predRest]". {
      iDestruct (big_sepM2_lookup_acc with "predsReadHold") as "[(%predRead' & %offset' & % & % & predReadHolds) predsReadRest]";
        [ exact: physHistsLook | done | ].
      assert (offset' = offset) as -> by by simplify_map_eq.
      assert (predRead' = predRead) as -> by by simplify_map_eq.
      iDestruct (big_sepM2_lookup_acc with "predsFullHold") as "[(%predFull' & %offset' & % & % & predFullHolds) predsFullRest]";
        [ exact: physHistsLook | done | ].
      replace predFull' with predFull; last by simplify_map_eq.
      replace offset' with offset; last by simplify_map_eq.
      iPoseProof (big_sepM2_sep with "[$predReadHolds $predFullHolds]") as "predBothHolds".
      iDestruct (big_sepM2_lookup_acc with "predBothHolds") as "[predBothHolds predBothRest]";
        [ exact: physHistLook | done | ].
      destruct (decide (offset ≤ tS ∧ physHist !! S tS = None)) as [[] | Hneg ].
      - iDestruct "predBothHolds" as "[_ predFullHolds]".
        iSpecialize ("predFullHolds" with "[//] [//]").
        iPoseProof (predicate_holds_phi_decode with "predFullEquiv predFullHolds") as "pred_full_holds";
          first done.
        iEval (rewrite full_read_split) in "pred_full_holds".
        iDestruct "pred_full_holds" as "[pred_read_holds p_remaining]".
        iPoseProof (predicate_holds_phi_decode with "predReadEquiv pred_read_holds") as "PredReadHolds";
          first done.
        iFrame.
        iIntros "predReadHolds".
        iPoseProof (predicate_holds_phi_decode with "predReadEquiv predReadHolds") as "pred_read_holds";
          first done.
        iSpecialize ("p_remaining" with "pred_read_holds").
        iPoseProof (predicate_holds_phi_decode with "predFullEquiv p_remaining") as "predFullHolds";
          first done.
        iSpecialize ("predBothRest" with "[predFullHolds]").
        { iSplitL ""; first (iIntros ([ | [? ?] ]); [ lia | by simplify_eq ]).
          iIntros (_ _).
          iFrame. }
        iPoseProof (big_sepM2_sep with "predBothRest") as "[predReadHolds predFullHolds]".
        iSpecialize ("predsReadRest" with "[predReadHolds]").
        { iExists _, _. by iFrame. }
        iSpecialize ("predsFullRest" with "[predFullHolds]").
        { iExists _, _. by iFrame. }
        iFrame.
      - iDestruct "predBothHolds" as "[predReadHolds _]".
        iSpecialize ("predReadHolds" with "[%]").
        { rewrite not_and_l in Hneg.
          destruct Hneg as [ | ].
          - left. lia.
          - right. rewrite -not_eq_None_Some //=. }
        iFrame.
        iIntros "predReadHolds".
        iSpecialize ("predBothRest" with "[predReadHolds]").
        { iSplitR ""; first (iIntros (_); iFrame).
          iIntros (? ?).
          tauto. }
        iPoseProof (big_sepM2_sep with "predBothRest") as "[predReadHolds predFullHolds]".
        iSpecialize ("predsReadRest" with "[predReadHolds]").
        { iExists _, _. by iFrame. }
        iSpecialize ("predsFullRest" with "[predFullHolds]").
        { iExists _, _. by iFrame. }
        iFrame.
    }
    iPoseProof (predicate_holds_phi_decode with "predReadEquiv predReadHolds") as "pred_read_holds";
      first done.
    (* we now have enough resrouce to specialize the progress resource *)
    iDestruct ("progress" $! SP (msg_val msgP) (msg_val msg))
      as (pred_pers_obj pred_read_obj) "(persExtract & readExtract & progress)".
    iEval (rewrite ?monPred_at_wand) in "persExtract".
    iDestruct ("persExtract" with "[%] pred_pers_holds") as "#persExtract".
    { simpl. split; [ solve_view_le | done ]. }
    iEval (rewrite ?monPred_at_objectively) in "persExtract".
    iEval (rewrite ?monPred_at_wand) in "readExtract".
    iDestruct ("readExtract" with "[%] pred_read_holds") as "#readExtract".
    { simpl. split; [ solve_view_le | done ]. }
    iEval (rewrite ?monPred_at_objectively) in "readExtract".
    iEval (rewrite monPred_at_wand) in "progress".
    set new_pers_view := (default (msg_store_view msg) (na_views !! ℓ), msg_persisted_after_view msg, ∅, gnames).
    iSpecialize ("progress" $! new_pers_view with "[%] persExtract").
    { simpl. split; [ solve_view_le | done ]. }
    iEval (rewrite monPred_wand_force) in "progress".
    iSpecialize ("progress" with "readExtract").
    iEval (rewrite monPred_at_and) in "progress".
    (* now we restore the read predicates *)
    iPoseProof (predicate_holds_phi_decode with "predReadEquiv pred_read_holds") as "predReadHolds";
      first done.
    iDestruct ("predRest" with "[$]") as "[predsFullHold predsReadHold]".
    (* we need to extract the encoded relation from state interpretation *)
    iAssert ⌜∃ order, (orders !! ℓ = Some order) ∧ increasing_map order absHist⌝%I
        as %(order & ordersLook & increasing). {
      iAssert ⌜is_Some (orders !! ℓ)⌝%I as %[order ordersLook]. {
        iPoseProof (big_sepM2_dom with "ordered") as "%domEq".
        rewrite -elem_of_dom -domEq elem_of_dom //.
      }
      iPoseProof (big_sepM2_lookup with "ordered") as "%orderLook";
        [ done | done | by iExists _ ].
    }
    iPoseProof (orders_lookup with "[$] []") as "%orderDecode";
      [ exact ordersLook | | ].
    { iNamed "knowProtocol". iEval (rewrite lift_d_at) in "knowPreorder". iFrame "#". }
    subst order.
    (* to merge proofs after the case analysis *)
    (* I don't want to do it, but I found no choice... *)
    iAssert (|==> ([∗map] k↦y1;y2 ∈ phys_hists;abs_hists,
                   ∃ (pred_pers : positive → val → optionO (dPropO Σ)) (t : nat) (encS0 : positive) (msg0 : message),
                     ⌜predicates_pers !! k = Some pred_pers⌝ ∗
                     ⌜view_slice.offsets_add offsets global_pview' !! k = Some t ∨
                      global_pview' !! k = None ∧ offsets !! k = Some t⌝ ∗
                     ⌜y2 !! t = Some encS0⌝ ∗ ⌜y1 !! t = Some msg0⌝ ∗
                     encoded_predicate_holds pred_pers encS0
                       (msg_val msg0)
                       (default (msg_store_view msg0) (na_views !! k),
                        msg_persisted_after_view msg0, ∅, gnames)) ∗ Q new_pers_view)%I
      with "[predsPersRest pred_pers_holds progress]" as "> [predsPersHold Q]". {
      (* we are at the point to distinguish whether the flushed state [tS ↦ s, msg] comes later or
       * the current global persistent timestamp [tP ↦ sP, msgP] comes later.
       * this is "decidable" since the history is strictly increasing, and comparison between
       * [tS] and [tP] gives up the answer. *)
      destruct (decide (tS ≤ tP)).
      - (* [tS ≤ tP], persistent view unchanged. *)
        assert (s ⊑ SP). {
          destruct (decide (tS = tP)) as [ -> | ].
          - by simplify_map_eq.
          - specialize (increasing tS tP encS encSP ltac:(lia) ltac:(done) ltac:(done)).
            by eapply (encode_relation.encode_relation_decode_iff_1) in increasing.
        }
        iDestruct "progress" as "[_ progress]".
        iSpecialize ("progress" with "[//]").
        iMod "progress". iFrame.
        iPoseProof (predicate_holds_phi_decode with "predPersEquiv pred_pers_holds") as "predPersHolds";
          first done.
        iPoseProof (big_sepM2_insert_delete with "[predsPersRest predPersHolds]") as "predsPersHold".
        { iFrame. iExistsN. iFrame. iFrame "%". }
        do 2 (rewrite insert_id; last done).
        iModIntro.
        iApply (big_sepM2_impl with "predsPersHold").
        iIntros (ℓ' absHist' physHist' ??) "!> (% & % & % & % & ? & %localPView' & ? & ?)".
        iExists _, _, _, _.
        iFrame.
        iPureIntro.
        destruct (decide (ℓ = ℓ')) as [<- | ].
        + simpl.
          destruct localPView as [ localPView | [ pViewLook offsetLook' ] ].
          * left.
            rewrite map_lookup_zip_with_Some in localPView.
            destruct localPView as (offset' & [pview] & ? & ? & eq).
            simplify_eq.
            destruct localPView' as [ <- | [] ]; last congruence.
            rewrite ?map_lookup_zip_with lookup_op lookup_singleton //=.
            replace (offsets !! ℓ) with (Some offset) by done.
            rewrite eq //=.
            f_equal.
            lia.
          * simplify_eq.
            left.
            rewrite map_lookup_zip_with lookup_op pViewLook lookup_singleton //=.
            replace (offsets !! ℓ) with (Some offset) by done.
            simpl.
            replace (tS - offset) with 0 by lia.
            rewrite map_lookup_zip_with_Some in localPView'.
            destruct localPView' as [ (offset' & [pview] & ? & ? & eq) | [] ]; first congruence.
            simplify_eq.
            f_equal.
            lia.
        + rewrite map_lookup_zip_with lookup_op lookup_singleton_ne ?op_None_right_id //=.
          rewrite map_lookup_zip_with in localPView'.
          apply localPView'.
      - (*we have [tS ≥ tP], which means the new persistent view will be updated. *)
        specialize (increasing tP tS encSP encS ltac:(lia) ltac:(done) ltac:(done)).
        eapply (encode_relation.encode_relation_decode_iff_1) in increasing;
          [ | done | done ].
        iDestruct "progress" as "[progress _]".
        iDestruct ("progress" with "[//]") as "> [new_pred_pers_holds $]".
        iPoseProof (predicate_holds_phi_decode with "predPersEquiv new_pred_pers_holds") as "predPersHolds";
          first done.
        iApply (big_sepM2_delete);
          [ done | done | ].
        iSplitL "predPersHolds".
        { iExistsN. iFrame. iFrame "%".
          iPureIntro. left.
          destruct localPView as [ localPView | [ pViewLook offsetLook' ] ].
          - rewrite map_lookup_zip_with_Some in localPView.
            destruct localPView as (offset' & [pview] & ? & ? & eq).
            simplify_eq.
            rewrite ?map_lookup_zip_with lookup_op lookup_singleton //=.
            replace (offsets !! ℓ) with (Some offset) by done.
            rewrite eq //=.
            f_equal.
            lia.
          - simplify_eq.
            rewrite map_lookup_zip_with lookup_op pViewLook lookup_singleton //=.
            replace (offsets !! ℓ) with (Some offset) by done.
            simpl.
            f_equal.
            lia. }
        iApply (big_sepM2_impl with "predsPersRest").
        iModIntro.
        iIntros (ℓ' absHist' physHist' ??) "!> (% & % & % & % & ? & %localPView' & ? & ?)".
        iExistsN.
        iFrame.
        iPureIntro.
        assert (ℓ ≠ ℓ') by (pose proof (lookup_delete phys_hists ℓ); congruence).
        rewrite map_lookup_zip_with lookup_op lookup_singleton_ne ?op_None_right_id //=.
        rewrite map_lookup_zip_with in localPView'.
        apply localPView'.
    }

    iModIntro.
    iEval (rewrite -?bi.sep_assoc -and_assoc).
    iSplit; first solve_view_le.
    iSplit; first done.
    iSplitL "HΦ H Q". {
      iApply "HΦ".
      - iPureIntro.
        rewrite -?and_assoc.
        solve_view_le.
      - iEval (simpl) in "H".
        iApply (monPred_mono); last iApply "H".
        { repeat (first [ apply join_mono | by solve_view_le | split ]). }
        iApply (objective_at with "Q").
    }
    rewrite /interp.
    iExistsN.
    iClear "globalPViewPersisted".
    iFrame "ptsMap offsets physHist oldViewsDiscarded crashedAt history historyFragments".
    iFrame "full_predicates read_predicates pers_predicates".
    iFrame "allOrders globalPViewPersisted' naLocs atLocs naView atLocsHistories".
    iFrame "ordered predsFullHold predsReadHold predsPersHold allBumpers bumpMono bumperSome".
    repeat (iSplitPure; first done).
    iSplitPure.
    { rewrite dom_op.
      apply union_least; first done.
      rewrite dom_singleton_L singleton_subseteq_l elem_of_dom //. }
    repeat (iSplitPure; first done).
    repeat (iSplit; first iAssumption).
    done.
  Qed.
End wp_rules.
