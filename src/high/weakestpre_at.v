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

From self Require Export extra ipm_tactics.
From self.high Require Export dprop.
From self Require Export view.
From self Require Export lang.
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
    - iDestruct 1 as (P') "[%eq PH]".
      iDestruct (discrete_fun_equivI with "predsEquiv") as "HI".
      iDestruct ("HI" $! encS) as "HIP". (* iClear "HI". *)
      iEval (rewrite discrete_fun_equivI) in "HIP".
      iDestruct ("HIP" $! v) as "HI". (* iClear "HIP". *)
      rewrite /encode_predicate.
      rewrite eq'.
      simpl.
      rewrite option_equivI.
      rewrite eq.
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

  Lemma msg_persisted_views_eq'
        (ℓ : loc) (hists : gmap loc (gmap time message))
        (hist : gmap time message) (msg : message)
        (sharedLocs : gset loc) (t : time) :
    map_Forall
      (λ _ : loc,
        map_Forall
          (λ _ msg, msg_persist_view msg = msg_persisted_after_view msg))
      (restrict sharedLocs hists) →
    ℓ ∈ sharedLocs →
    hists !! ℓ = Some hist →
    hist !! t = Some msg →
    msg.(msg_persist_view) = msg.(msg_persisted_after_view).
  Proof.
  Admitted.

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

    iApply wp_extra_state_interp_fupd.
    { done. }
    { (* Try and simplify this with lemmas/automation. *)
      clear.
      intros ??????? [Ki [??] [??] ? ? step].
      subst.
      simpl in *.
      induction Ki using rev_ind.
      { simpl in *. subst. inv_impure_thread_step; try done.
        rewrite list_fmap_singleton.
        subst.
        congruence. }
      move: H.
      rewrite fill_app.
      simpl.
      destruct x; try done.
      simpl.
      rewrite /thread_fill_item.
      simpl.
      inversion 1.
      simpl in *.
      rewrite -nvm_fill_fill in H2.
      simpl in *.
      destruct Ki using rev_ind; try done.
      { simpl in *. subst. inv_impure_thread_step; try done. }
      simpl in *.
      rewrite fill_app in H2.
      simpl in *.
      destruct x; try done. }
    (* We open [interp]. *)
    iNamed 1.

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

    iDestruct (
        location_sets_singleton_included with "sharedLocs isSharedLoc"
      ) as %ℓSh.
    iDestruct (big_sepM_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. }
    iDestruct "predMap" as
        (pred' physHist physHistLook predsLook') "predMap".
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

    (* We show that [PV'] is equal to [_PV']. *)
    assert (PV' = _PV') as <-.
    { eapply msg_persisted_views_eq' in mapShared; try done. done. }

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
    epose proof (encode_relation_related _ _ _ orderRelated)
      as (? & sL & eqX & decodeS' & s3InclS').
    assert (x = s') as -> by congruence.

    iDestruct (predicate_holds_phi_decode with "predsEquiv predHolds") as "PH";
      first done.
    iSpecialize ("pToQ" $! (SV', PV', ∅) sL v').
    monPred_simpl.
    iEval (setoid_rewrite monPred_at_wand) in "pToQ".
    iDestruct ("pToQ" $! (SV', PV', ∅) with "[//] [%] [//] PH") as "[Q phi]".
    { etrans; done. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iFrame "%".
      iApply (predicate_holds_phi_decode with "predsEquiv phi").
      done. }
    (* Reinsert into the map. *)
    iDestruct ("predsHold" with "[predMap]") as "predsHold".
    { iExists _, _. naive_solver. }

    (* Note: This allocation was commented out. Do we need it? *)
    (* iMod (own_full_history_alloc_frag with "history") as "[history histS]"; try done. *)
    (* iModIntro. *)
    (* We re-establish [interp]. *)
    iSplitR "ptsMap allOrders ordered predsHold history predicates
             crashedAt sharedLocs allBumpers bumpMono predPostCrash sharedLocsHistories"; last first.
    { repeat iExists _. iModIntro. iFrameNamed. }
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
      iExists t', sL.
      iFrame "∗#".
      iSplit; first done.
      (* FIXME: Intuitively the lhs. should be included in because we read [t']
      and a write includes its own timestamp. But, we don't remember this fact,
      yet. *)
      admit.
    - simpl.
      rewrite /store_view /flush_view /=.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      * apply view_le_r.
      * rewrite assoc. apply view_le_r.
      * apply view_empty_least.
  Admitted.

  Lemma wp_store_rel ℓ v s1 s2 ϕ `{!LocationProtocol ϕ} positive E :
    {{{
      "knowProt" ∷ know_protocol ℓ ϕ ∗
      "isSharedLoc" ∷ ⎡ is_shared_loc ℓ ⎤ ∗
      "storeLB" ∷ know_store_lb ℓ s1 ∗
      "phi" ∷ <nobuf> (ϕ s2 v _) ∗
      (* The new state must be greater than the possible current states. *)
      "greater" ∷ (∀ s' v', ⌜ s1 ⊑ s' ⌝ ∗ ϕ s' v' _ -∗ ⌜ s' ⊑ s2 ⌝)
    }}}
      #ℓ <-{rel} v @ positive; E
    {{{ RET #();
      know_store_lb ℓ s2
    }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV). iNamed 1.

    iNamed "knowProt".
    iNamed "storeLB".
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    rewrite wp_eq /wp_def wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val".

    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.
    (* iApply wp_fupd. *)

    iApply wp_extra_state_interp. { done. }
    { (* Try and simplify this with lemmas/automation. *)
      clear.
      intros ??????? [Ki [??] [??] ? ? step].
      subst.
      simpl in *.
      induction Ki using rev_ind.
      { simpl in *. subst. inv_impure_thread_step; try done.
        rewrite list_fmap_singleton.
        subst.
        congruence. }
      move: H.
      rewrite fill_app.
      simpl.
      destruct x; try done.
      - simpl.
        rewrite /thread_fill_item.
        simpl.
        inversion 1.
        simpl in *.
        rewrite -nvm_fill_fill in H2.
        simpl in *.
        destruct Ki using rev_ind; try done.
        { simpl in *. subst. inv_impure_thread_step; try done. }
        simpl in *.
        rewrite fill_app in H2.
        simpl in *.
        destruct x; try done.
      - simpl.
        rewrite /thread_fill_item.
        simpl.
        inversion 1.
        simpl in *.
        rewrite -nvm_fill_fill in H3.
        simpl in *.
        destruct Ki using rev_ind; try done.
        { simpl in *. subst. inv_impure_thread_step; try done. }
        simpl in *.
        rewrite fill_app in H3.
        simpl in *.
        destruct x; try done. }

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
    iDestruct (big_sepM_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. }
    iDestruct "predMap" as
        (pred' physHist physHistLook predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    clear predsLook'.

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]"; first done.

    iApply (wp_store_release (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (tNew) "(%look & %gt & #valNew & pts)".

    iFrame "valNew".

    (* We've inserted a new message at time [tNew] in the physical
    history. Hence, we must accordingly insert a new state in the abstract
    history. *)

    iDestruct (big_sepS_delete with "sharedLocsHistories") as
      "[(%abs_hist' & %absHistLook' & absHist) sharedLocsHistories]"; first done.
    simplify_eq.

    iAssert (⌜ absHist !! tNew = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite fmap_None.
      rewrite -!not_elem_of_dom.
      rewrite domEq.
      done. }

    (* Update the ghost state for the abstract history. *)
    iMod (own_full_history_insert _ _ _ _ _ _ (encode s2) with "history absHist")
      as "(history & absHist & histFrag)". { done. }

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
      - iExists _, _.
        iDestruct (own_frag_equiv _ _ {[ tNew := s2 ]} with "[histFrag]") as "histFrag".
        { rewrite map_fmap_singleton. iFrame "histFrag". }
        iFrame "histFrag knowPreorder".
        iPureIntro.
        split; first done.
        rewrite /store_view. simpl.
        rewrite /lookup_zero.
        rewrite lookup_insert.
        done. }


    iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".
    repeat iExists _.
    iFrame "ptsMap".
    iFrameNamed.

    iSplit. { iPureIntro. etrans; first done. apply dom_insert_subseteq. }

  Admitted.
  (*   "history absHist" *)
  (* Qed. *)

  (* Definition insert_hist {A} (ℓ : loc) (a : A) (m : gmap ℓ (gmap nat A)) := *)
  (*   <[]>m *)
    
  (* Insert a new message into an abstract history. *)
  (* Lemma foo ℓ t abs_hist abs_hists encS : *)
  (*   (* abs_hists !! ℓ = abs_hist *) *)
  (*   abs_hist !! t = None → *)
  (*   own_full_history abs_history_name know_abs_history_name abs_hists -∗ *)
  (*   know_full_encoded_history_loc ℓ abs_hist -∗ *)
  (*     own_full_history abs_history_name know_abs_history_name <[t := encS]abs_hists ∗ *)
  (*     own_frag_encoded_history_loc γ ℓ <[t := encS]>enc. *)

End wp_at_rules.
