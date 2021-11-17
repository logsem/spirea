(* Weakest precondition rules for atomic locations. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self Require Export extra ipm_tactics encode_relation.
From self.high Require Export dprop.
From self Require Export view.
From self Require Export lang lemmas.
From self.base Require Import tactics.
From self.base Require Import primitive_laws.
From self.lang Require Import syntax.
From self.high Require Import resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol.

Section wp_at_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (ϕ : ST → val → nvmDeltaG Σ → dProp Σ).

  (** * Shared points-to predicate *)

  Lemma predicate_holds_phi_decode ϕ s encS (encϕ : predO) v TV :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v TV ∗-∗ ϕ s v _ TV).
  Proof.
    iIntros (eq') "predsEquiv".
    iSplit.
    - iDestruct 1 as (P') "[eq PH]".
      iDestruct (discrete_fun_equivI with "predsEquiv") as "HI".
      iDestruct ("HI" $! encS) as "HIP". (* iClear "HI". *)
      iEval (rewrite discrete_fun_equivI) in "HIP".
      iDestruct ("HIP" $! v) as "HI". (* iClear "HIP". *)
      rewrite /encode_predicate.
      rewrite eq'.
      simpl.
      iRewrite "eq" in "HI".
      rewrite option_equivI.
      iEval (setoid_rewrite discrete_fun_equivI) in "HI".
      iSpecialize ("HI" $! hG).
      by iRewrite "HI" in "PH".
    - iIntros "phi".
      rewrite /encoded_predicate_holds.
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate. rewrite eq'.
      simpl.
      destruct (encϕ encS v); rewrite option_equivI; last done.
      iExists _. iSplit; first done.
      iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! hG).
      by iRewrite "predsEquiv".
  Qed.

  Lemma pred_encode_Some ϕ (s : ST) (v : val) (pred : predO) :
    (pred ≡ encode_predicate ϕ : iProp Σ) -∗
    (pred (encode s) v ≡ Some (ϕ s v) : iProp Σ).
  Proof.
    iIntros "eq".
    iEval (setoid_rewrite discrete_fun_equivI) in "eq".
    iEval (setoid_rewrite discrete_fun_equivI) in "eq".
    iSpecialize ("eq" $! (encode s) v).
    Unshelve. 2: { done. } 2: { done. }
    rewrite /encode_predicate. rewrite decode_encode /=.
    (* iRewrite "eq". *) (* Why this no work? *)
    done.
  Qed.

  Lemma msg_persisted_views_eq
        (ℓ : loc) (hists : gmap loc (gmap time (message * positive)))
        (hist : gmap time (message * positive)) (msg : message)
        (sharedLocs : gset loc) (t : time) (s' : positive) :
    map_Forall
      (λ _ : loc,
        map_Forall
          (λ _ '(msg, _), msg_persist_view msg = msg_persisted_after_view msg))
      (restrict sharedLocs hists) →
    hists !! ℓ = Some hist →
    hist !! t = Some (msg, s') →
    own shared_locs_name (● (sharedLocs : gsetUR loc)) -∗
    own shared_locs_name (◯ {[ℓ]}) -∗
    ⌜msg.(msg_persist_view) = msg.(msg_persisted_after_view)⌝.
  Proof.
    iIntros (m look look') "A B".
    iDestruct (location_sets_singleton_included with "A B") as %V.
    iPureIntro.
    assert (restrict sharedLocs hists !! ℓ = Some hist) as look2.
    - apply restrict_lookup_Some. done.
    - setoid_rewrite map_Forall_lookup in m.
      specialize (m ℓ hist look2).
      setoid_rewrite map_Forall_lookup in m.
      specialize (m t (msg, s') look').
      simpl in m.
      done.
  Qed.

  Lemma wp_load_shared ℓ s Q ϕ `{!LocationProtocol ϕ} positive E :
    {{{
      "knowProt" ∷ know_protocol ℓ ϕ ∗
      "isSharedLoc" ∷ ⎡ is_shared_loc ℓ ⎤ ∗
      "storeLB" ∷ know_store_lb ℓ s ∗
      "pToQ" ∷ <obj> (∀ s' v, ⌜ s ⊑ s' ⌝ -∗ ϕ s' v _ -∗ Q s' v ∗ ϕ s' v _)
    }}}
      !{acq} #ℓ @ positive; E
    {{{ s' v, RET v;
      "storeLB" ∷ know_store_lb ℓ s' ∗
      post_fence (Q s' v) }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros (TV).
    iNamed 1.
    iDestruct "knowProt" as "(knowPred & _ & _)".
    iNamed "storeLB".
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    rewrite wp_eq /wp_def wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.

    iApply wp_extra_state_interp. { done. } { by apply prim_step_load_acq_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    iApply (wp_fupd (irisGS0 := (@nvmBaseG_irisGS _ _ _ (Build_extraStateInterp _ _)))).

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    (* We need to get the points-to predicate for [ℓ] which is is inside
    [interp].  We want to look up the points-to predicate in [ptsMap]. To this
    end, we combine our fragment of the history with the authorative element. *)
    iDestruct (
        own_frag_history_agree_singleton with "history knowFragHist") as %look.
    destruct look as (absHist & enc & absHistLook & lookTS & decodeEnc).

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (
        location_sets_singleton_included with "sharedLocs isSharedLoc"
      ) as %ℓSh.
    iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    clear predsLook'.

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    (* iApply wp_fupd. *)
    iApply (wp_load_acquire (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (t' v' SV' PV' _PV') "(%look & %gt & #val' & pts)".

    rewrite /store_view.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val'".

    eassert _ as temp.
    { eapply map_map_Forall_lookup_1; eauto using mapShared.
        apply restrict_lookup_Some_2; done. }
    simpl in temp. destruct temp as [SV'lookup <-].

    assert (tS ≤ t') as lte.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      etrans; first done.
      etrans; last done.
      rewrite /store_view /=.
      f_equiv.
      etrans. apply incl. apply incl2. }

    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    assert (is_Some (absHist !! t')) as (encSL & HI).
    { apply elem_of_dom. rewrite <- domEq. apply elem_of_dom. naive_solver. }
    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      [done|done| ].
    simpl.

    (* The loaded state must be greater than [s]. *)
    iDestruct (big_sepM2_lookup_l with "ordered")
      as (order) "[%ordersLook %increasingMap]".
    { apply absHistLook. }
    iDestruct (orders_lookup with "allOrders order") as %orderEq;
      first apply ordersLook.
    epose proof (increasingMap tS t' (encode s) encSL) as hihi.
    assert (order enc encSL) as orderRelated.
    { destruct (le_lt_or_eq _ _ lte) as [le|tSEq].
      - eapply increasingMap.
        * apply le.
        * subst. done.
        * done.
      - (* We can conclude that [enc] is equal to [t']. *)
        assert (enc = encSL) as ->.
        2: { rewrite orderEq. rewrite /encode_relation.
             rewrite decodeEnc. simpl. done. }
        congruence. }
    rewrite orderEq in orderRelated.
    epose proof (encode_relation_inv _ _ _ orderRelated)
      as (? & sL & eqX & decodeS' & s3InclS').
    assert (x = s) as -> by congruence.

    iDestruct (predicate_holds_phi_decode with "predsEquiv predHolds") as "PH";
      first done.
    iSpecialize ("pToQ" $! (SV', PV', ∅) sL v').
    monPred_simpl.
    iEval (setoid_rewrite monPred_at_wand) in "pToQ".
    iDestruct ("pToQ" $! (SV', PV', ∅) with "[//] [%] [//] PH") as "[Q phi]".
    { done. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iFrame "%".
      iApply (predicate_holds_phi_decode with "predsEquiv phi").
      done. }
    (* Reinsert into the map. *)
    iDestruct ("predsHold" with "[predMap]") as "predsHold".
    { iExists _. naive_solver. }

    (* Note: This allocation was commented out. Do we need it? *)
    iMod (own_full_history_alloc_frag with "history") as "[history histS]"; try done.
    iModIntro.
    (* We re-establish [interp]. *)
    iSplitR "ptsMap physHist allOrders ordered predsHold history predicates
             crashedAt sharedLocs allBumpers bumpMono predPostCrash sharedLocsHistories"; last first.
    { repeat iExists _. iFrameNamed. }
    iSplit. { iPureIntro. repeat split; try done; apply view_le_l. }
    iSpecialize ("Φpost" $! sL v').
    monPred_simpl.
    iApply "Φpost".
    { iPureIntro.
      etrans. eassumption.
      repeat split; try done; try apply view_le_l. }
    (* The thread view we started with [TV] is smaller than the view we ended
    with. *)
    assert (TV ⊑ (SV ⊔ SV', PV, BV ⊔ PV')).
    { do 2 (etrans; first done). repeat split; auto using view_le_l. }
    iSplitR "Q".
    - iFrameNamed.
      iExists t'.
      iFrame "∗#".
      iPureIntro.
      rewrite -SV'lookup. rewrite /store_view /=.
      rewrite lookup_zero_lub. lia.
    - simpl.
      rewrite /store_view /flush_view /=.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      * apply view_le_r.
      * rewrite assoc. apply view_le_r.
      * apply view_empty_least.
  Qed.

  (* Rule for store on an atomic. *)
  Lemma wp_store_at ℓ s_i s_t v_t ϕ `{!LocationProtocol ϕ} positive E :
    {{{
       "%targetGt" ∷ ⌜ s_i ⊑ s_t ⌝ ∗
      "knowProt" ∷ know_protocol ℓ ϕ ∗
      "isSharedLoc" ∷ ⎡ is_shared_loc ℓ ⎤ ∗
      "storeLB" ∷ know_store_lb ℓ s_i ∗
      (* "phi" ∷ (∀ v_i, ϕ s_i v_i _ -∗ ϕ s_t v_t _ ∗ ϕ s_i v_i _) ∗ *)
      "phi" ∷ <nobuf> (ϕ s_t v_t _) ∗
      (* The new state must be greater than the possible current states. *)
      "greater" ∷
        (∀ v_i s_c v_c,
          ϕ s_i v_i _ ∗ ϕ s_t v_t _ ∗ ϕ s_c v_c _ -∗ ⌜ s_t ⊑ s_c ∧ s_c ⊑ s_t ⌝)
    }}}
      #ℓ <-{rel} v_t @ positive; E
    {{{ RET #();
      know_store_lb ℓ s_t
    }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV). iNamed 1.

    iNamed "knowProt".
    iDestruct "storeLB" as (t_i) "temp". iNamed "temp".
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    rewrite wp_eq /wp_def wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val".

    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.
    (* iApply wp_fupd. *)

    iApply wp_extra_state_interp. { done. }
    { apply prim_step_store_rel_no_fork. }

    iNamed 1.
    iApply (wp_fupd (irisGS0 := (@nvmBaseG_irisGS _ _ _ (Build_extraStateInterp _ _)))).

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    (* We need to get the points-to predicate for [ℓ] which is is inside
    [interp]. We want to look up the points-to predicate in [ptsMap]. To this
    end, we combine our fragment of the history with the authorative element. *)
    iDestruct (
        own_frag_history_agree_singleton with "history knowFragHist") as %look.
    destruct look as (absHist & enc & absHistsLook & lookTS & decodeEnc).

    iDestruct (
        location_sets_singleton_included with "sharedLocs isSharedLoc"
      ) as %ℓSh.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (big_sepM2_delete with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    clear predsLook'.

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]"; first done.

    iApply (wp_store_release (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (t_t) "(%look & %gt & #valNew & pts)".

    (* We can conclude that [t_t] is strictly greater than [t_i]. *)
    assert (t_i < t_t) as tILtTt.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      rewrite /store_view in tSLe, gt.
      simpl in tSLe. simpl in gt.
      destruct incl as [[??]?].
      destruct incl2 as [[??]?].
      eapply gt_le_trans; first done.
      etrans; first done.
      f_equiv.
      etrans; done. }

    iDestruct (own_all_preorders_singleton_frag with "allOrders knowPreorder")
      as %ordersLook.

    iFrame "valNew".

    iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

    (* We've inserted a new message at time [t_t] in the physical
    history. Hence, we must accordingly insert a new state in the abstract
    history. *)

    iDestruct (big_sepS_delete with "sharedLocsHistories") as
      "[(%abs_hist' & %absHistLook' & absHist) sharedLocsHistories]"; first done.
    simplify_eq.

    iAssert (⌜ absHist !! t_t = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite fmap_None.
      rewrite -!not_elem_of_dom.
      rewrite domEq.
      done. }

    (* Update the ghost state for the abstract history. *)
    iMod (own_full_history_insert _ _ _ _ _ _ (encode s_t) with "history absHist")
      as "(history & absHist & histFrag)". { done. }

    iMod (auth_map_map_insert with "physHist") as "[physHist unusedFrag]".
    { done. }
    { eapply fmap_None. done. }

    (* We are done updating ghost state. *)
    iModIntro.
    iEval (rewrite -assoc).
    iSplit. { iPureIntro. repeat split; try done. apply view_insert_le. lia. }

    iSplitL "Φpost histFrag".
    { iApply "Φpost".
      - iPureIntro. destruct TV' as [[??]?].
        repeat split.
        * etrans; first apply incl2. apply view_insert_le. lia.
        * apply incl2.
        * apply incl2.
      - iExists _.
        iDestruct (own_frag_equiv _ _ {[ t_t := s_t ]} with "[histFrag]") as "histFrag".
        { rewrite map_fmap_singleton. iFrame "histFrag". }
        iFrame "histFrag knowPreorder".
        iPureIntro.
        rewrite /store_view. simpl.
        rewrite /lookup_zero.
        rewrite lookup_insert.
        done. }

    (* Maybe add a lemma for this lookup *)
    iDestruct (
        own_frag_history_agree_singleton with "history knowFragHist") as %look'.
    destruct look' as (hist' & enc' & absHistsLook' & hip & hop).
    rewrite lookup_insert in absHistsLook'.
    apply (inj Some) in absHistsLook'.
    iDestruct (big_sepM2_dom with "predMap") as %physHistAbsHistDom.
    assert (is_Some (physHist !! t_i)) as [vI physHistLook].
    { rewrite -elem_of_dom physHistAbsHistDom elem_of_dom. done. }
    assert (enc = enc') as <-.
    { apply (inj Some). rewrite -hip. rewrite -lookTS. rewrite -absHistsLook'.
      rewrite lookup_insert_ne; [done| lia]. }

    (* We must extract the phi for the inserted state from "phi". *)
    iDestruct (big_sepM2_delete with "predMap") as "[phiI predMap]".
    { apply physHistLook. } { done. }
    iDestruct (predicate_holds_phi_decode with "predsEquiv phiI") as "phiI";
      first done.

    iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".
    repeat iExists _.
    iFrame "ptsMap physHist crashedAt history predicates allOrders sharedLocs
            allBumpers bumpMono".

    (* [sharedLocsSubseteq] *)
    iSplit. { iPureIntro. etrans; first done. apply dom_insert_subseteq. }

    (* [mapShared] - We need to show that the newly inserted message satisfied
    the restriction on shared locations that their persist view and their
    persisted after view is equal. *)
    iSplit.
    { iPureIntro.
      setoid_rewrite (restrict_insert ℓ); last done.
      rewrite /shared_locs_inv.
      apply map_map_Forall_insert_2.
      - apply restrict_lookup_Some; done.
      - simpl.
        rewrite /lookup_zero.
        rewrite lookup_insert.
        simpl.
        done.
      - done. }

    (* [sharedLocsHistories] *)
    iSplitL "sharedLocsHistories absHist".
    {
      rewrite /know_full_encoded_history_loc.
      iApply (big_sepS_delete_2 with "[absHist] [sharedLocsHistories]").
      - iExists _. iFrame "absHist". by rewrite lookup_insert.
      - iApply (big_sepS_impl with "sharedLocsHistories").
        iIntros "!>" (ℓ' [elm neq%not_elem_of_singleton_1]%elem_of_difference) "?".
        iEval (setoid_rewrite (lookup_insert_ne abs_hists ℓ ℓ' _); last done).
        iFrame. }

    (* [ordered] *)
    iSplit. {
      iDestruct (big_sepM2_forall with "ordered") as %[? orderedForall].
      iApply big_sepM2_forall.
      iSplit.
      { iPureIntro.
        apply dom_eq_alt_L.
        rewrite dom_insert_lookup_L; last naive_solver.
        apply dom_eq_alt_L.
        done. }
      iIntros (ℓ').
      (* If ℓ' is not equal to ℓ then the history is unchanged. *)
      destruct (decide (ℓ' = ℓ)) as [->|neq]; last first.
      { iPureIntro. simpl.
        setoid_rewrite lookup_insert_ne; [apply orderedForall | done]. }
      iIntros (absHist' order). rewrite lookup_insert. iIntros ([= <-] ordersLook').
      specialize (orderedForall _ _ _ absHistsLook ordersLook).
      eassert (order = _) as ->.
      { apply (inj Some). rewrite -ordersLook'. apply ordersLook. }

      epose proof
        (increasing_map_insert_after _ _ _ _ _ (encode s_t) orderedForall
                                      lookTS _ tILtTt) as h.
      Unshelve.
      2: { eapply encode_relation_decode_iff; eauto using decode_encode. }

      iApply (bi.pure_mono); first apply h.
      iIntros (t_c encSC ? ?).
      epose proof (orderedForall _ _ _ _ a0 lookTS a) as related.
      epose proof (encode_relation_inv _ _ _ related)
        as (s_i' & s_c & eqX & decodeS' & incl3).
      assert (s_i = s_i') as <-. { congruence. }
      simpl.
      rewrite /encode_relation.
      rewrite decode_encode.
      rewrite decodeS'.
      simpl.

      assert (is_Some (physHist !! t_c)) as [vC physHistLook'].
      { rewrite -elem_of_dom physHistAbsHistDom elem_of_dom. done. }

      iDestruct (big_sepM2_delete with "predMap") as "[phiC predMap]".
      { rewrite lookup_delete_ne; [apply physHistLook' | lia]. }
      { rewrite lookup_delete_ne; [apply a | lia]. }
      iDestruct (predicate_holds_phi_decode with "predsEquiv phiC") as "phiC";
        first done.

      iSpecialize ("greater" $! _ _ _).
      iEval (monPred_simpl) in "greater".
      iEval (setoid_rewrite monPred_at_pure) in "greater".

      iApply ("greater" $! (TV' ⊔ (msg_to_tv vC) ⊔ (msg_to_tv vI))).
      { iPureIntro. etrans; first apply incl.
        rewrite -assoc.
        apply thread_view_le_l. }
      monPred_simpl.
      iFrame.
      iSplitL "phiI".
      { iApply monPred_mono; last iApply "phiI".
        apply thread_view_le_r. }
      iSplitL "phi".
      { iApply monPred_mono; last iApply "phi".
        etrans; last apply thread_view_le_l.
        etrans; last apply thread_view_le_l.
        destruct TV as [[??]?].
        destruct TV' as [[??]?].
        rewrite /store_view /flush_view. simpl.
        repeat split.
        - apply incl.
        - apply incl.
        - apply view_empty_least. }

      iApply monPred_mono; last iApply "phiC".
      rewrite (comm _ TV').
      rewrite -assoc.
      apply thread_view_le_l. }

    (* [predsHold] *)
    (* We show that the invariant hold for all messages in all histories. The
    non-trivial part of this is to show that the invariant hold for the newly
    inserted store message. *)
    iSplitL "predsHold predMap phiI phi". {
      iDestruct (big_sepM2_insert_delete with "[$predMap phiI]") as "predMap".
      {
        iApply predicate_holds_phi_decode; [done|done|].
        iApply monPred_mono; last iApply "phiI". done. }
      iDestruct (big_sepM2_insert_delete with "[predMap $predsHold]") as "predsHold".
      { iExists _. iSplit; first done. iApply "predMap". }
      rewrite (insert_id physHist); last done.
      rewrite (insert_id phys_hists); last done.
      rewrite (insert_id absHist); last done.
      rewrite (insert_id abs_hists); last done.
      iApply (big_sepM2_insert_override_2 with "predsHold"); [done|done|].
      simpl.
      iDestruct 1 as (pred' predsLook') "H".
      assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
      clear predsLook'.
      iExists _.
      iSplit; first done.
      iApply (big_sepM2_insert_2 with "[phi] H").
      rewrite /msg_to_tv /store_view. simpl.
      rewrite /encoded_predicate_holds.
      iExists (ϕ s_t v_t).
      iSplit.
      { iApply pred_encode_Some. done. }
      iApply monPred_mono; last iFrame.
      destruct TV as [[??]?].
      destruct TV' as [[??]?].
      repeat split; last done.
      - simpl. etrans; first apply incl. etrans; first apply incl2.
        rewrite /store_view in gt. simpl in gt.
        apply view_insert_le'; [done|lia].
      - simpl. rewrite /flush_view. simpl.
        etrans; first apply incl.
        apply incl2.
    }
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq.

    iFrame "predPostCrash".
    iFrame (bumperBumpToValid).

    (* "bumperSome" *)
    iApply big_sepM2_forall. iSplit.
    { iPureIntro. iIntros (ℓ'). setoid_rewrite <- elem_of_dom.
      rewrite dom_insert_lookup_L; last done. rewrite domEq. done. }

    iIntros (ℓ' absHist' bumper' look1 look2).
    iDestruct (big_sepM2_forall with "bumperSome") as %[notneeded bumperSome].
    iPureIntro.
    destruct (decide (ℓ = ℓ')) as [->|neq].
    - rewrite lookup_insert in look1.
      simplify_eq.
      apply map_Forall_insert_2; last first.
      { eapply bumperSome; try done. }
      (* This is where we show the "actually interesting" part or the new
      obligation that we have (the only thing that doesn't follow from the
      existing fact.. *)
      rewrite /encode_bumper. rewrite decode_encode. done.
    - eapply bumperSome; try done.
      rewrite lookup_insert_ne in look1; done.
  Qed.

End wp_at_rules.
