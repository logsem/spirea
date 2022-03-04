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

From self.algebra Require Export ghost_map ghost_map_map.
From self Require Export extra ipm_tactics encode_relation view.
From self.lang Require Export lang lemmas tactics syntax.
From self.base Require Import primitive_laws.
From self.high Require Export dprop resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol locations.
From self.high Require Import locations protocol.
From self.high.modalities Require Import no_buffer.

Section wp_at_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (prot : LocationProtocol ST).

  (** * Shared points-to predicate *)

  Lemma msg_persisted_views_eq
        (ℓ : loc) (hists : gmap loc (gmap time (message * positive)))
        (hist : gmap time (message * positive)) (msg : message)
        (atLocs : gset loc) (t : time) (s' : positive) :
    map_Forall
      (λ _ : loc,
        map_Forall
          (λ _ '(msg, _), msg_persist_view msg = msg_persisted_after_view msg))
      (restrict atLocs hists) →
    hists !! ℓ = Some hist →
    hist !! t = Some (msg, s') →
    own shared_locs_name (● (atLocs : gsetUR loc)) -∗
    own shared_locs_name (◯ {[ℓ]}) -∗
    ⌜msg.(msg_persist_view) = msg.(msg_persisted_after_view)⌝.
  Proof.
    iIntros (m look look') "A B".
    iDestruct (location_sets_singleton_included with "A B") as %V.
    iPureIntro.
    assert (restrict atLocs hists !! ℓ = Some hist) as look2.
    - apply restrict_lookup_Some. done.
    - setoid_rewrite map_Forall_lookup in m.
      specialize (m ℓ hist look2).
      setoid_rewrite map_Forall_lookup in m.
      specialize (m t (msg, s') look').
      simpl in m.
      done.
  Qed.

  Lemma interp_insert_loc_at ℓ prot s SV PV BV TV v :
    SV !!0 ℓ = 0 →
    interp -∗
    pred prot s v hG (SV, PV, BV) -∗
    ℓ ↦h initial_history AT SV PV v ==∗
    store_lb ℓ prot s TV ∗ is_at_loc ℓ ∗ interp.
  Proof.
    iIntros (svLook).
    iNamed 1.
    iIntros "pred pts".

    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { iDestruct (big_sepM_lookup with "ptsMap") as "pts'"; first done.
      iDestruct (mapsto_valid_2 with "pts pts'") as (?) "_".
      done. }

    iDestruct (big_sepM2_dom with "predsHold") as %domEq.
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq2.
    iDestruct (big_sepM2_dom with "predPostCrash") as %domEq3.
    iDestruct (big_sepM2_dom with "bumpMono") as %domEq4.

    assert (abs_hists !! ℓ = None) as absHistsLook.
    { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom.
      assumption. }
    assert (ℓ ∉ dom (gset _) abs_hists) as absHistsDomElem.
    { apply not_elem_of_dom. done. }

    (* We update ghost state. *)

    (* Update ghost state for physical history. *)
    iMod (auth_map_map_insert_top with "physHist") as "[physHist doWeNeedThis]".
    { done. }

    (* Add the predicate to the ghost state of predicates. *)
    iMod (own_all_preds_insert with "predicates") as "[predicates knowPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite domEq3. congruence. }

    (* Allocate the abstract history for the location. *)
    iMod (full_map_insert _ _ _ {[0 := encode s]} with "history")
      as "(history & ownHist & #fragHist)".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iEval (rewrite big_sepM_singleton) in "fragHist".

    (* Add the bumper to the ghost state of bumper. *)
    iMod (own_all_bumpers_insert _ _ _ (prot.(bumper)) with "allBumpers")
      as "[allBumpers knowBumper]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Add the preorder to the ghost state of bumper. *)
    iMod (ghost_map_insert_persist with "allOrders") as "[allOrders #knowOrder]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite /relation2. congruence. }

    (* Add the allocated location to the set of atomic locations. *)
    iMod (own_update with "atLocs") as "[atLocs fragSharedLocs]".
    { apply auth_update_alloc. apply gset_local_update.
      apply (union_subseteq_r {[ ℓ ]}). }
    iEval (rewrite -gset_op) in "fragSharedLocs". iDestruct "fragSharedLocs" as "[#isShared _]".

    iAssert (know_protocol ℓ prot) as "#prot".
    { rewrite /know_protocol. iFrame "knowPred knowBumper knowOrder". }

    iModIntro.
    iSplitL "knowPred knowBumper".
    { rewrite /store_lb.
      iExists 0.
      iFrame "prot".
      iSplit.
      { iApply (frag_history_equiv with "fragHist"). }
      iPureIntro.
      apply lookup_zero_gt_zero. }
    iSplit; first iFrame "isShared".

    repeat iExists _.
    iSplitL "ptsMap pts".
    { erewrite big_sepM_insert; first iFrame "pts ptsMap". assumption. }
    iFrame "physHist crashedAt history predicates allOrders naLocs atLocs".

    (* historyFragments *)
    iSplit.
    { iApply (big_sepM_insert_2 with "[] historyFragments");
      simpl; rewrite big_sepM_singleton; iFrame "fragHist". }
    (* locsDisjoint *)
    iSplitPure. {
      assert (ℓ ∉ dom (gset loc) abs_hists).
      { rewrite -domEq. apply not_elem_of_dom. done. }
      set_solver. }
    (* histDomLocs *)
    iSplitPure. { rewrite dom_insert_L. set_solver+ histDomLocs. }
    (* naViewsDom *)
    iSplitPure; first done.
    iFrame "naView".
    (* mapShared *)
    iSplitPure. {
      rewrite restrict_insert_union.
      rewrite /shared_locs_inv.
      rewrite /map_map_Forall.
      apply map_Forall_insert_2; last done.
      rewrite /initial_history.
      apply map_Forall_singleton.
      done. }
    iSplitL "atLocsHistories ownHist".
    { rewrite restrict_insert_union big_sepM_insert.
      2: { apply restrict_lookup_None_lookup. assumption. }
      iFrame "ownHist atLocsHistories". }
    (* "ordered" *)
    iSplit.
    { iApply (big_sepM2_insert_2); last done.
      iPureIntro. apply increasing_map_singleton. }
    (* predsHold *)
    iSplitL "predsHold pred".
    { iApply (big_sepM2_insert_2 with "[pred] [predsHold]").
      - iExists _. rewrite lookup_insert.
        iSplit; first done.
        rewrite /initial_history.
        simpl.
        rewrite big_sepM2_singleton /=.
        assert (na_views !! ℓ = None) as ->.
        { apply not_elem_of_dom in physHistsLook.
          apply not_elem_of_dom.
          rewrite naViewsDom.
          eapply not_elem_of_weaken; first apply physHistsLook.
          rewrite domEq histDomLocs.
          set_solver. }
        simpl.
        iDestruct (predicate_holds_phi with "[]") as "HH".
        { done. }
        { done. }
        iApply "HH".
        destruct TV as [[??]?].
        iApply (into_no_buffer_at with "pred").
      - iApply (big_sepM2_impl with "predsHold").
        iModIntro. iIntros (ℓ' ????) "(%pred & %look & ?)".
        iExists (pred).
        assert (ℓ ≠ ℓ') by congruence.
        rewrite lookup_insert_ne; last done.
        iSplit; first done.
        iFrame. }
    iFrame "allBumpers".
    (* bumpMono *)
    iSplit.
    { iApply (big_sepM2_insert_2 with "[] bumpMono").
      iPureIntro. simpl.
      apply encode_bumper_bump_mono. apply bumper_mono. }
    (* predPostCrash *)
    iSplit.
    { iApply (big_sepM2_insert_2 with "[] predPostCrash").
    (*   rewrite /post_crash_flush. rewrite /post_crash. done. iFrame "predPostCrash". *)
    (* iSplitL. *)
      iModIntro. iIntros (??????) "(%eq & eq2 & P)".
      iEval (rewrite /encode_predicate).
      apply encode_bumper_Some_decode in eq.
      destruct eq as (s3 & eq' & eq2').
      rewrite -eq2'.
      rewrite decode_encode.
      iExists _.
      iSplit. { iPureIntro. simpl. reflexivity. }
      iDestruct (encode_predicate_extract with "eq2 P") as "pred".
      { done. }
      iApply (pred_condition with "pred"). }
    (* bumperBumpToValid *)
    iSplitPure.
    { rewrite map_Forall_insert.
      2: { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
      split; last done.
      apply encode_bumper_bump_to_valid. }
    iApply (big_sepM2_insert_2 with "[] bumperSome").
    iPureIntro.
    apply map_Forall_singleton.
    rewrite encode_bumper_encode.
    done.
  Qed.

  Lemma wp_alloc_at v s prot st E :
    {{{ prot.(pred) s v _ }}}
      ref_AT v @ st; E
    {{{ ℓ, RET #ℓ;
        store_lb ℓ prot s ∗ ⎡ is_at_loc ℓ ⎤ }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV). iIntros "phi".
    iIntros (TV' incl) "Φpost".
    (* Unfold the wp *)
    rewrite wp_eq /wp_def wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.
    iApply wp_extra_state_interp. { done. } { by apply prim_step_ref_no_fork. }
    iIntros "interp".
    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.
    iApply (wp_alloc (extra := {| extra_state_interp := True |})); first done.
    iNext.
    iIntros (ℓ CV') "(crashedAt' & % & % & pts)".
    simpl.
    iFrame "val".
    destruct TV as [[??]?].
    iMod (interp_insert_loc_at with "interp [phi] pts")
      as "(storeLb & atLoc & interp)"; first done.
    { iApply monPred_mono; last iApply "phi". etrans; done. }
    iModIntro.
    rewrite -assoc. iSplit; first done.
    iFrame "interp". iApply "Φpost".
    iFrame "storeLb atLoc".
  Qed.

  Lemma wp_load_at ℓ s Q prot st E :
    {{{
      ⎡ is_at_loc ℓ ⎤ ∗
      store_lb ℓ prot s ∗
      <obj> (∀ s' v, ⌜ s ⊑ s' ⌝ -∗ prot.(pred) s' v _ -∗ Q s' v ∗ prot.(pred) s' v _)
    }}}
      !{acq} #ℓ @ st; E
    {{{ s' v, RET v;
      store_lb ℓ prot s' ∗
      post_fence (Q s' v) }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros (TV).
    iDestruct 1 as "(isSharedLoc & storeLB & pToQ)".
    iDestruct (store_lb_protocol with "storeLB") as "#temp". iNamed "temp".
    rewrite /store_lb.
    iDestruct "storeLB" as (tS) "(#prot & #hist & %tSLe)".

    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    rewrite wp_eq /wp_def wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.

    iApply wp_extra_state_interp. { done. } { by apply prim_step_load_acq_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    (* We need to get the points-to predicate for [ℓ] which is is inside
    [interp].  We want to look up the points-to predicate in [ptsMap]. To this
    end, we combine our fragment of the history with the authorative element. *)
    iDestruct (
      full_map_frag_singleton_agreee with "history hist") as %look.
    destruct look as (absHist & enc & absHistLook & lookTS & decodeEnc).

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (
        location_sets_singleton_included with "atLocs isSharedLoc"
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
    iDestruct (orders_lookup with "allOrders knowPreorder") as %orderEq;
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
    iEval (monPred_simpl) in "pToQ".
    iEval (setoid_rewrite monPred_at_wand) in "pToQ".
    assert (na_views !! ℓ = None) as ->.
    { apply not_elem_of_dom. set_solver + ℓSh locsDisjoint naViewsDom. }
    iDestruct ("pToQ" $! (SV', PV', ∅) with "[//] [%] [//] PH") as "[Q phi]".
    { done. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iApply (predicate_holds_phi_decode with "predsEquiv phi"). assumption. }
    (* Reinsert into the map. *)
    iDestruct ("predsHold" with "[predMap]") as "predsHold".
    { iExists _. iFrame "predMap". done. }

    iModIntro.
    (* We re-establish [interp]. *)
    iSplitR "ptsMap physHist allOrders ordered predsHold history predicates
             crashedAt atLocs naView naLocs allBumpers bumpMono
             predPostCrash atLocsHistories"; last first.
    { repeat iExists _. iFrameNamed.
      rewrite /post_crash_flush /post_crash.
      iFrame "predPostCrash". }
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
      iFrame "knowPred knowPreorder knowBumper".
      iSplit.
      { iExists _.
        iDestruct (big_sepM_lookup with "historyFragments") as "F"; first done.
        iDestruct (big_sepM_lookup with "F") as "$"; first done.
        done. }
      iPureIntro.
      rewrite -SV'lookup.
      rewrite lookup_zero_lub. lia.
    - simpl.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      * apply view_le_r.
      * rewrite assoc. apply view_le_r.
      * apply view_empty_least.
  Qed.

  (* Rule for store on an atomic. *)
  Lemma wp_store_at ℓ s_i s_t v_t (prot : LocationProtocol ST) st E :
    {{{
       "%targetGt" ∷ ⌜ s_i ⊑ s_t ⌝ ∗
      "isSharedLoc" ∷ ⎡ is_at_loc ℓ ⎤ ∗
      "storeLB" ∷ store_lb ℓ prot s_i ∗
      "phi" ∷ <nobuf> (prot.(pred) s_t v_t _) ∗
      (* NOTE: This does _not_ work. *)
      (* "phi" ∷ (∀ v_i, ϕ s_i v_i _ -∗ ϕ s_t v_t _ ∗ ϕ s_i v_i _) ∗ *)
      (* NOTE: This should work and be more general. *)
      (* "phi" ∷ (∀ v_i, (<obj> (ϕ s_i v_i -∗ ϕ s_i_v ∗ R)) ∗ (R -∗ ϕ s_t v_t)) ∗ *)
      (* The new state must be greater than the possible current states. *)
      "greater" ∷
        (∀ v_i s_c v_c,
          prot.(pred) s_i v_i _ ∗ prot.(pred) s_t v_t _ ∗ prot.(pred) s_c v_c _ -∗
            ⌜ s_t ⊑ s_c ∧ s_c ⊑ s_t ⌝)
    }}}
      #ℓ <-{rel} v_t @ st; E
    {{{ RET #(); store_lb ℓ prot s_t }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV). iNamed 1.
    iDestruct (store_lb_protocol with "storeLB") as "#temp". iNamed "temp".

    rewrite /store_lb.
    iDestruct "storeLB" as (t_i) "(#prot & #hist & %tSLe)".
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
    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (predi predsLook) "#predsEquiv".

    (* We need to get the points-to predicate for [ℓ] which is is inside
    [interp]. We want to look up the points-to predicate in [ptsMap]. To this
    end, we combine our fragment of the history with the authorative element. *)
    iDestruct (
        full_map_frag_singleton_agreee with "history hist") as %look.
    destruct look as (absHist & enc & absHistsLook & lookTS & decodeEnc).

    iDestruct (
        location_sets_singleton_included with "atLocs isSharedLoc"
      ) as %ℓSh.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (big_sepM2_delete with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (predi = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
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
      simpl in tSLe. simpl in gt.
      destruct incl as [[??]?].
      destruct incl2 as [[??]?].
      eapply gt_le_trans; first done.
      etrans; first done.
      f_equiv.
      etrans; done. }

    iDestruct (ghost_map_lookup with "allOrders knowPreorder")
      as %ordersLook.

    iFrame "valNew".

    iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

    (* We've inserted a new message at time [t_t] in the physical
    history. Hence, we must accordingly insert a new state in the abstract
    history. *)

    iDestruct (big_sepM_delete with "atLocsHistories") as
      "(absHist & atLocsHistories)".
    { apply restrict_lookup_Some_2; done. }

    (* iDestruct (big_sepM_delete with "atLocsHistories") as *)
    (*   "[(%abs_hist' & %absHistLook' & absHist) atLocsHistories]"; first done. *)
    (* simplify_eq. *)

    iAssert (⌜ absHist !! t_t = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite fmap_None.
      rewrite -!not_elem_of_dom.
      rewrite domEq.
      done. }

    (* Update the ghost state for the abstract history. *)
    iMod (full_map_full_entry_insert _ _ _ _ (encode s_t) with "history absHist")
      as "(history & absHist & #histFrag)".
    { done. }

    iMod (auth_map_map_insert with "physHist") as "[physHist unusedFrag]".
    { done. }
    { eapply fmap_None. done. }

    (* We are done updating ghost state. *)
    iModIntro.
    iEval (rewrite -assoc).
    iSplit. { iPureIntro. repeat split; try done. apply view_insert_le. lia. }

    iSplitL "Φpost".
    { iApply "Φpost".
      - iPureIntro. destruct TV' as [[??]?].
        repeat split.
        * etrans; first apply incl2. apply view_insert_le. lia.
        * apply incl2.
        * apply incl2.
      - iExists _.
        iDestruct (frag_history_equiv with "histFrag") as  "$".
        iFrame "knowPreorder knowPred knowBumper".
        iPureIntro.
        rewrite /lookup_zero.
        rewrite lookup_insert.
        done. }

    (* Maybe add a lemma for this lookup *)
    iDestruct (
        full_map_frag_singleton_agreee with "history hist") as %look'.
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
    iFrame "ptsMap physHist crashedAt history predicates allOrders atLocs
            naLocs naView allBumpers bumpMono".
    iFrame (locsDisjoint naViewsDom).

    (* historyFragments *)
    iSplit.
    { iApply (big_sepM_insert_2 with "[] historyFragments").
      iApply (big_sepM_insert_2 with "histFrag []").
      iApply (big_sepM_lookup with "historyFragments").
      done. }
    (* [histDomLocs] *)
    iSplit. { iPureIntro. set_solver. }

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

    (* [atLocsHistories] *)
    iSplitL "atLocsHistories absHist".
    {
      rewrite /know_full_encoded_history_loc.
      (* NOTE: This rewrite is mega-slow. *)
      iEval (setoid_rewrite (restrict_insert ℓ at_locs (<[t_t:=encode s_t]> absHist) abs_hists ℓSh)).
      iApply big_sepM_insert_delete.
      iFrame. }

    (* [ordered] *)
    iSplit. {
      iApply (big_sepM2_update_left with "ordered"); eauto.
      iIntros (orderedForall).
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
      assert (na_views !! ℓ = None) as ->. { apply not_elem_of_dom. set_solver. }
      iSplitL "phiI".
      { iApply monPred_mono; last iApply "phiI".
        apply thread_view_le_r. }
      iSplitL "phi".
      { iApply monPred_mono; last iApply "phi".
        etrans; last apply thread_view_le_l.
        etrans; last apply thread_view_le_l.
        destruct TV as [[??]?].
        destruct TV' as [[??]?].
        (* rewrite /store_view /flush_view. simpl. *)
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
      iApply (big_sepM2_update with "predsHold"); [done|done|].
      simpl.
      iDestruct 1 as (pred' predsLook') "H".
      assert (predi = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
      clear predsLook'.
      iExists _.
      iSplit; first done.
      iApply (big_sepM2_insert_2 with "[phi] H").
      rewrite /msg_to_tv.  (* /store_view. simpl. *)
      rewrite /encoded_predicate_holds.
      iExists (prot.(pred) s_t v_t).
      iSplit.
      { iApply pred_encode_Some. done. }
      assert (na_views !! ℓ = None) as ->. { apply not_elem_of_dom. set_solver. }
      iApply monPred_mono; last iFrame.
      destruct TV as [[??]?].
      destruct TV' as [[??]?].
      repeat split; last done.
      - simpl. etrans; first apply incl. etrans; first apply incl2.
        (* rewrite /store_view in gt. *)
        simpl in gt.
        apply view_insert_le'; [done|lia].
      - simpl.
        etrans; first apply incl.
        apply incl2.
    }
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq.

    iFrame "predPostCrash".
    iFrame (bumperBumpToValid).

    (* "bumperSome" *)
    iApply (big_sepM2_update_left with "bumperSome"); eauto.
    iPureIntro. intros bumperSome.
    apply map_Forall_insert_2; eauto.
    rewrite /encode_bumper decode_encode. done.
  Qed.

  (** [Q1] is the resource we want to extract in case of success and and [Q2] is
  the resource we want to extract in case of failure. *)
  Lemma wp_cas_at Q1 Q2 Q3 ℓ prot s_i v_i v_t R s_t st E :
    {{{
      ⎡ is_at_loc ℓ ⎤ ∗
      store_lb ℓ prot s_i ∗
      (* in case of success *)
      ((∀ s_a, ⌜ s_i ⊑ s_a ⌝ -∗
        (<obj> (prot.(pred) s_a v_i _ -∗ prot.(pred) s_a v_i _ ∗ R s_a)) ∗ (R s_a -∗ prot.(pred) s_t v_t _ ∗ Q1 s_a)) ∧
        (* in case of failure *)
        (∀ s_a, ⌜ s_i ⊑ s_a ⌝ -∗
          (<obj> (prot.(pred) s_a v_i _ -∗ prot.(pred) s_a v_i _ ∗ Q2 s_a)) ∗ Q3))
    }}}
      CAS #ℓ v_i v_t @ st; E
    {{{ b, RET #b;
      (⌜ b = true ⌝ ∗ Q1 s_t ∗ store_lb ℓ prot s_t) ∨
      (∃ s_a, ⌜ b = false ⌝ ∗ ⌜ s_i ⊑ s_a ⌝ ∗ Q2 s_a ∗ Q3)
    }}}.
  Proof.
  Admitted.

End wp_at_rules.
