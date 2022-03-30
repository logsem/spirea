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
From self Require Import solve_view_le.
From self.high Require Export dprop resources crash_weakestpre weakestpre
     lifted_modalities monpred_simpl modalities protocol locations.
From self.high Require Import locations protocol.
From self.high.modalities Require Import no_buffer.

Section wp_at_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG}.

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
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
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

  Definition encoded_predicate_hold physHist (absHist : gmap nat positive) pred : iProp Σ :=
    ([∗ map] msg;encS ∈ physHist;absHist,
      encoded_predicate_holds pred encS
                              (msg_val msg)
                              (msg_store_view msg,
                              msg_persisted_after_view msg, ∅)).

  Definition loc_info ℓ prot (pred : predO) physHist absHist : iProp Σ :=
    "%domEq" ∷ ⌜ dom (gset _) physHist = dom _ absHist ⌝ ∗
    "%increasing" ∷ ⌜ increasing_map (encode_relation (⊑@{ST})) absHist ⌝ ∗
    "%atInvs" ∷ ⌜ map_Forall (λ t msg, atomic_loc_inv ℓ t msg) physHist ⌝ ∗
    "#predEquiv" ∷ ▷ (pred ≡ encode_predicate (protocol.pred prot)) ∗
    "#frags" ∷ ([∗ map] k2 ↦ v ∈ absHist, frag_entry abs_history_name ℓ k2 v) ∗
    "predHolds" ∷ encoded_predicate_hold physHist absHist pred ∗
    "fullHist" ∷ know_full_encoded_history_loc ℓ 1 absHist ∗
    "pts" ∷ ℓ ↦h physHist.

  Definition insert_impl ℓ prot pred physHist absHist : iProp Σ :=
    ∀ t s es msg,
      ⌜ encode s = es ⌝ -∗
      ⌜ physHist !! t = None ⌝ -∗
      ⌜ msg_store_view msg !!0 ℓ = t ⌝ -∗
      ⌜ msg_persist_view msg = msg_persisted_after_view msg ⌝ -∗
      encoded_predicate_hold (<[ t := msg ]>physHist) (<[ t := es ]>absHist) pred -∗
      know_full_encoded_history_loc ℓ 1 absHist -∗
      ⌜ increasing_map (encode_relation (⊑@{ST})) (<[ t := es ]>absHist) ⌝ -∗
      ℓ ↦h <[t := msg ]>physHist ==∗
      know_frag_history_loc ℓ t s ∗ interp.

  Definition lookup_impl ℓ prot pred physHist absHist : iProp Σ :=
    encoded_predicate_hold physHist absHist pred -∗
    know_full_encoded_history_loc ℓ 1 absHist -∗
    ℓ ↦h physHist -∗
    interp.

  (* Get all information inside [interp] related to the location [ℓ]. *)
  Lemma interp_get_at_loc ℓ s prot t :
    interp -∗
    is_at_loc ℓ -∗
    know_protocol ℓ prot -∗
    know_frag_history_loc ℓ t s -∗
    ∃ physHist (absHist : gmap nat positive) pred,
      loc_info ℓ prot pred physHist absHist ∗
      (insert_impl ℓ prot pred physHist absHist ∧
        lookup_impl ℓ prot pred physHist absHist).
  Proof.
    iNamed 1.
    iIntros "isAt".
    rewrite /know_protocol. iNamed 1.
    iIntros "hist".

    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    iDestruct (full_map_frag_singleton_agreee with "history hist")
      as %(absHist & enc & absHistLook & lookTS & decodeEnc).

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (location_sets_singleton_included with "atLocs isAt") as %ℓSh.

    iDestruct (big_sepM2_delete with "predsHold") as "[predHolds allPredsHold]";
      [done|done|].

    iDestruct "predHolds" as (pred' predsLook') "predHolds".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    clear predsLook'.
    assert (na_views !! ℓ = None) as naViewLook. { apply not_elem_of_dom. set_solver. }
    iEval (rewrite naViewLook; simpl) in "predHolds".

    iDestruct (big_sepM2_delete_l with "ordered")
      as (order) "(%ordersLook & %increasingMap & #ordered2)";
      first apply absHistLook.

    iDestruct (orders_lookup with "allOrders knowPreorder") as %orderEq;
      first apply ordersLook.
    rewrite orderEq in increasingMap.

    iDestruct (big_sepM2_dom with "predHolds") as %domEq.

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]"; first done.

    eassert _ as invs.
    { eapply map_Forall_lookup_1; first apply mapShared.
        apply restrict_lookup_Some_2; done. }
    simpl in invs.

    iDestruct (big_sepM_delete with "atLocsHistories") as
      "(fullHist & atLocsHistories)".
    { apply restrict_lookup_Some_2; done. }

    iDestruct (big_sepM_lookup with "historyFragments") as "#histFrags"; first done.

    iExists physHist, absHist, pred.
    (* Give resources. *)
    iFrame (domEq increasingMap invs).
    iFrame "predsEquiv".
    iFrame "predHolds".
    iFrame "histFrags".
    iFrame "pts".
    iFrame "fullHist".

    (* We show the two different implications. *)
    iSplit.
    { (* Get back resources. *)
      iIntros (t_i s2 es msg encEs lookNone ? ?) "predHolds fullHist order pts".

      assert (absHist !! t_i = None)%I as absHistLookNone.
      { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom. done. }

      iMod (full_map_full_entry_insert _ _ _ _ es with "history fullHist")
        as "(history & fullHist & #histFrag)"; first done.

      iDestruct (big_sepM_insert_delete with "[$atLocsHistories $fullHist]")
        as "atLocsHistories".
      iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".

      iDestruct (big_sepM2_insert_delete with "[$allPredsHold predHolds]")
        as "allPredsHold".
      { iExists pred. rewrite naViewLook. iFrame "predHolds". done. }

      iMod (auth_map_map_insert with "physHist") as "[physHist unusedFrag]";
        [try done|try done|].

      iDestruct (big_sepM2_insert_delete with "[$ordered2 $order]") as "ordered3".
      rewrite (insert_id orders); last congruence.

      iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

      iModIntro.
      iSplit; first (iApply frag_history_equiv; rewrite -encEs; iFrame "histFrag").
      (* We re-establish [interp]. *)
      repeat iExists _.
      iFrame "ptsMap".
      iFrame "physHist".
      iFrame "allOrders".
      iFrame "ordered3".
      iFrame "allPredsHold".
      iFrame "history predicates".
      iFrame "crashedAt".
      iFrame "atLocs".
      iFrame "naView naLocs allBumpers bumpMono".
      iFrame "predPostCrash".
      (* historyFragments *)
      iSplit.
      { iApply (big_sepM_insert_2 with "[] historyFragments").
        iApply (big_sepM_insert_2 with "histFrag []").
        iApply (big_sepM_lookup with "historyFragments").
        done. }
      iSplitPure; first apply locsDisjoint.
      (* [histDomLocs] *)
      iSplit. { iPureIntro. set_solver. }
      (* [naViewsDom] *)
      iSplitPure; first done.
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
          rewrite /atomic_loc_inv.
          split; done.
        - done. }
      iSplitL "atLocsHistories".
      {
        rewrite /know_full_encoded_history_loc.
        (* NOTE: This rewrite is mega-slow. *)
        iEval (setoid_rewrite (restrict_insert ℓ at_locs (<[t_i:=es]> absHist) abs_hists ℓSh)).
        iFrame. }
      iFrame (bumperBumpToValid).
      (* "bumperSome" *)
      iApply (big_sepM2_update_left with "bumperSome"); eauto.
      iPureIntro. intros bumperSome.
      apply map_Forall_insert_2; eauto.
      rewrite /encode_bumper. rewrite -encEs decode_encode. done. }
    {
      iIntros "predHolds fullHist pts".

      iDestruct (big_sepM_insert_delete with "[$atLocsHistories $fullHist]")
        as "atLocsHistories".
      iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".
      iDestruct (big_sepM2_insert_delete with "[$ordered2]") as "ordered3";
        first done.
      iDestruct (big_sepM2_insert_delete with "[$allPredsHold predHolds]")
        as "allPredsHold".
      { iExists pred. rewrite naViewLook. iFrame "predHolds". done. }

      rewrite (insert_id orders); last congruence.
      rewrite (insert_id phys_hists); last congruence.
      rewrite (insert_id abs_hists); last congruence.
      rewrite (insert_id (restrict at_locs abs_hists)).
      2: { apply restrict_lookup_Some_2; done. }

      (* We re-establish [interp]. *)
      repeat iExists _.
      iFrame "ptsMap".
      iFrame "physHist".
      iFrame "allOrders".
      iFrame "ordered".
      iFrame "allPredsHold".
      iFrame "history predicates".
      iFrame "crashedAt".
      iFrame "atLocs".
      iFrame "naView naLocs allBumpers bumpMono predPostCrash atLocsHistories".
      iFrame "bumperSome".
      iFrame "historyFragments".
      iFrame "%". }
  Qed.

  Lemma read_atomic_location t_i t_l (physHist : history) absHist vm SVm FVm
        PVm ℓ (e_i : positive) (s_i : ST) :
    t_i ≤ t_l →
    dom (gset _) physHist = dom _ absHist →
    absHist !! t_i = Some e_i →
    decode e_i = Some s_i →
    increasing_map (encode_relation (⊑@{ST})) absHist →
    map_Forall (λ (t : nat) (msg : message), atomic_loc_inv ℓ t msg) physHist →
    physHist !! t_l = Some (Msg vm SVm FVm PVm) →
    ∃ s_l e_l,
      absHist !! t_l = Some e_l ∧
      decode e_l = Some s_l ∧
      SVm !!0 ℓ = t_l ∧
      FVm = PVm ∧
      s_i ⊑ s_l.
  Proof.
    intros le domEq ? decodeEnc ? atInvs ?.
    eassert _ as temp.
    { eapply map_Forall_lookup_1; [apply atInvs|done]. }
    rewrite /atomic_loc_inv /= in temp. destruct temp as [SV'lookup <-].

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

  Lemma wp_load_at ℓ s Q prot st E :
    {{{
      ⎡ is_at_loc ℓ ⎤ ∗
      store_lb ℓ prot s ∗
      <obj> (∀ s' v, ⌜ s ⊑ s' ⌝ -∗ prot.(pred) s' v _ -∗ Q s' v ∗ prot.(pred) s' v _)
    }}}
      !_AT #ℓ @ st; E
    {{{ s' v, RET v;
      store_lb ℓ prot s' ∗
      post_fence (Q s' v) }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros (TV).
    iDestruct 1 as "(isAt & storeLb & pToQ)".
    iDestruct (store_lb_protocol with "storeLb") as "#knowProt".
    iDestruct (know_protocol_extract with "knowProt")
      as "(#knowPred & #knowPreorder & #knowBumper)".
    rewrite /store_lb.
    iDestruct "storeLb" as (tS) "(#prot & #hist & %tSLe)".

    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_load_acq_no_fork. }

    (* We open [interp]. *)
    iIntros "interp".
    iDestruct (interp_get_at_loc with "interp isAt knowProt hist")
      as (physHist absHist pred) "(R & [_ reins])".
    iNamed "R".

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iDestruct (history_full_entry_frag_lookup with "fullHist hist") as %look.
    destruct look as (enc & lookTS & decodeEnc).

    iApply (wp_load_acquire (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (t' v' SV' PV' _PV') "(%look & %gt & #val' & pts)".

    iFrame "val'".

    assert (tS ≤ t') as lte.
    { etrans; first done. etrans; last done. f_equiv. solve_view_le. }

    eassert _ as  temp. { eapply read_atomic_location; done. }
    destruct temp as (sL & encSL & ? & ? & ? & <- & orderRelated).

    iDestruct (big_sepM2_lookup_acc with "predHolds") as "[predHolds predMap]";
      [done|done|].
    simpl.

    iDestruct (predicate_holds_phi_decode with "predEquiv predHolds") as "PH";
      first done.
    iSpecialize ("pToQ" $! (SV', PV', ∅) sL v').
    iEval (monPred_simpl) in "pToQ".
    iEval (setoid_rewrite monPred_at_wand) in "pToQ".

    iDestruct ("pToQ" $! (SV', PV', ∅) with "[//] [%] [//] PH") as "[Q phi]".
    { done. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iApply (predicate_holds_phi_decode with "predEquiv phi"). assumption. }

    iModIntro.

    (* We re-establish [interp]. *)
    iDestruct ("reins" with "[$] [$] [$]") as "$".

    iSplit. { iPureIntro. solve_view_le. }
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
        iSplitPure; first done.
        iApply (big_sepM_lookup with "frags"). done. }
      iPureIntro.
      subst. rewrite lookup_zero_lub. lia.
    - simpl.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      * apply view_le_r.
      * rewrite assoc. apply view_le_r.
      * apply view_empty_least.
  Qed.

  Lemma wp_store_at ℓ s_i s_t v_t (prot : LocationProtocol ST) st E :
    {{{
      ⌜ s_i ⊑ s_t ⌝ ∗
      ⎡ is_at_loc ℓ ⎤ ∗
      store_lb ℓ prot s_i ∗
      prot.(pred) s_t v_t _ ∗
      (* NOTE: This does _not_ work. *)
      (* "phi" ∷ (∀ v_i, ϕ s_i v_i _ -∗ ϕ s_t v_t _ ∗ ϕ s_i v_i _) ∗ *)
      (* NOTE: This should work and be more general. *)
      (* "phi" ∷ (∀ v_i, (<obj> (ϕ s_i v_i -∗ ϕ s_i_v ∗ R)) ∗ (R -∗ ϕ s_t v_t)) ∗ *)
      (* The new state must be greater than the possible current states. *)
      (∀ v_i s_c v_c, ⌜ s_i ⊑ s_c ⌝ -∗
        prot.(pred) s_i v_i _ ∗ prot.(pred) s_t v_t _ ∗ prot.(pred) s_c v_c _ -∗
          ⌜ s_t ⊑ s_c ∧ s_c ⊑ s_t ⌝)
    }}}
      #ℓ <-_AT v_t @ st; E
    {{{ RET #(); store_lb ℓ prot s_t }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV).
    iIntros "(%targetGt & isAt & storeLb & phi & greater)".
    iDestruct (store_lb_protocol with "storeLb") as "#knowProt".
    iDestruct (know_protocol_extract with "knowProt")
      as "(#knowPred & #knowPreorder & #knowBumper)".

    rewrite /store_lb.
    iDestruct "storeLb" as (t_i) "(#prot & #hist & %tSLe)".
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. }
    { apply prim_step_store_rel_no_fork. }

    iIntros "interp".
    iDestruct (interp_get_at_loc with "interp isAt knowProt hist")
      as (physHist absHist pred) "(R & [reins _])".
    iNamed "R".

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iApply (wp_store_release with "[$pts $val]").
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

    iFrame "valNew".

    iDestruct (history_full_entry_frag_lookup with "fullHist hist") as %look'.
    destruct look' as (e_i & absHistLook' & hip).
    assert (is_Some (physHist !! t_i)) as [vI physHistLook].
    { rewrite -elem_of_dom domEq elem_of_dom. done. }

    (* We must extract the phi for the initial state from "phi". *)
    iDestruct (big_sepM2_delete with "predHolds") as "[phiI predHolds]".
    { apply physHistLook. } { done. }
    iDestruct (predicate_holds_phi_decode with "predEquiv phiI") as "phiI";
      first done.

    iAssert (
      ⌜increasing_map (encode_relation sqsubseteq) (<[t_t:=encode s_t]> absHist)⌝
                      )%I as %incri.
    { iApply (bi.pure_mono).
      { apply
         (increasing_map_insert_after _ _ _ _ _ (encode s_t) increasing
                                      absHistLook'); last done.
        eapply encode_relation_decode_iff; eauto using decode_encode. }
      iIntros (t_c e_c ? iLeC).

      assert (is_Some (physHist !! t_c)) as [[????] look2].
      { rewrite -elem_of_dom domEq elem_of_dom. done. }

      eassert _ as  temp. { eapply (read_atomic_location t_i t_c); done || lia. }
      destruct temp as (s_c & encSC & ? & decodeS' & ? & <- & orderRelated).
      simplify_eq.
      rewrite /encode_relation. rewrite decode_encode. rewrite decodeS'.

      iDestruct (big_sepM2_delete with "predHolds") as "[phiC predHolds]".
      { rewrite lookup_delete_ne; [apply look2 | lia]. }
      { rewrite lookup_delete_ne; [apply a | lia]. }

      iDestruct (predicate_holds_phi_decode with "predEquiv phiC") as "phiC";
        first done.

      iSpecialize ("greater" $! _ s_c _).
      iEval (monPred_simpl) in "greater".

      iSpecialize ("greater" $! TV with "[%] [%]"); [done|done|].
      iEval (monPred_simpl) in "greater".
      iEval (setoid_rewrite monPred_at_pure) in "greater".

      iApply ("greater" $! (TV' ⊔ (_) ⊔ (msg_to_tv vI))).
      { iPureIntro. etrans; first apply incl.
        rewrite -assoc.
        apply thread_view_le_l. }
      monPred_simpl.
      iFrame.
      iSplitL "phiI".
      { iApply monPred_mono; last iApply "phiI". apply thread_view_le_r. }
      iSplitL "phi".
      {
        iApply monPred_mono; last iApply "phi".
        rewrite -assoc.
        etrans; last apply thread_view_le_l. done. }

      iApply monPred_mono; last iApply "phiC".
      rewrite (comm _ TV').
      rewrite -assoc.
      apply thread_view_le_l. }

    iDestruct (big_sepM2_insert_delete with "[phiI $predHolds]") as "predHolds".
    { iApply predicate_holds_phi_decode; [done|done|].
      iApply monPred_mono; last iApply "phiI". done. }
    rewrite (insert_id physHist t_i); last done.
    rewrite (insert_id absHist t_i); last done.

    iMod ("reins" $! t_t s_t
      with "[//] [//] [] [] [predHolds phi] fullHist [//] pts") as "(#frag & $)".
    { iPureIntro. simpl. apply lookup_zero_insert. }
    { done. }
    { iApply (big_sepM2_insert_2 with "[phi] predHolds").
      simpl.
      rewrite /encoded_predicate_holds.
      iExists (prot.(protocol.pred) s_t v_t).
      iSplit.
      { iApply pred_encode_Some. done. }
      destruct TV as [[??]?].
      iDestruct (into_no_buffer_at with "phi") as "phi".
      iApply monPred_mono; last iFrame.
      destruct TV' as [[??]?].
      repeat split; last done.
      - simpl. etrans; first apply incl. etrans; first apply incl2.
        simpl in gt.
        apply view_insert_le'; [done|lia].
      - simpl.
        etrans; first apply incl.
        apply incl2. }
    (* We are done updating ghost state. *)
    iModIntro.
    iSplit. { iPureIntro. repeat split; try done. apply view_insert_le. lia. }

    iEval (rewrite monPred_at_wand) in "Φpost".
    iApply "Φpost".
    - iPureIntro. destruct TV' as [[??]?].
      repeat split.
      * etrans; first apply incl2. apply view_insert_le. lia.
      * apply incl2.
      * apply incl2.
    - iExists _.
      iFrame "frag".
      iFrame "knowProt".
      iPureIntro.
      rewrite lookup_zero_insert.
      done.
  Qed.

  (** [Q1] is the resource we want to extract in case of success and and [Q2] is
  the resource we want to extract in case of failure. *)
  Lemma wp_cmpxchg_at Q1 Q2 Q3 ℓ prot s_i (v_i : val) v_t R s_t st E :
    {{{
      ⎡ is_at_loc ℓ ⎤ ∗
      store_lb ℓ prot s_i ∗
      (∀ s_l v_l, ⌜ s_i ⊑ s_l ⌝ -∗
        ((▷ prot.(pred) s_l v_l _) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (((* in case of success *)
          (* The state we write fits in the history. *)
          ⌜ s_l ⊑ s_t ⌝ ∗
          (∀ s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ prot.(pred) s_l v_l _ -∗
            prot.(pred) s_n v_n _ -∗ ⌜ s_t ⊑ s_n ⌝) ∗
          (* Extract from the location we load. *)
          (<obj> (prot.(pred) s_l v_l _ -∗ prot.(pred) s_l v_l _ ∗ R s_l)) ∗
          (* Establish the invariant for the value we store. *)
          (R s_l -∗ prot.(pred) s_t v_t _ ∗ Q1 s_l))
        ∧ (* in case of failure *)
          ((<obj> (prot.(pred) s_l v_l _ -∗ prot.(pred) s_l v_l _ ∗ Q2 s_l)) ∗ Q3)
        ))
    }}}
      CmpXchg #ℓ v_i v_t @ st; E
    {{{ v b s_l, RET (v, #b);
      (⌜ b = true ⌝ ∗ <fence> Q1 s_l ∗ store_lb ℓ prot s_t) ∨
      (⌜ b = false ⌝ ∗ ⌜ s_i ⊑ s_l ⌝ ∗ <fence> (Q2 s_l) ∗ Q3)
    }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV).
    iIntros "(isAt & storeLb & impl)".
    iDestruct (store_lb_protocol with "storeLb") as "#knowProt".
    iDestruct (know_protocol_extract with "knowProt")
      as "(#knowPred & #knowPreorder & #knowBumper)".
    rewrite /store_lb.
    iDestruct "storeLb" as (t_i) "(#prot & #hist & %tSLe)".
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
    iApply wp_extra_state_interp. { done. }
    { apply prim_step_cmpxchg_no_fork. }

    iIntros "interp".
    iDestruct (interp_get_at_loc with "interp isAt knowProt hist")
      as (physHist absHist pred) "(R & reins)".
    iNamed "R".

    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iDestruct (history_full_entry_frag_lookup with "fullHist hist")
      as %(enc & lookTS & decodeEnc).

    iApply (wp_cmpxchg with "[#] [$pts $val]").
    { iIntros (t_l [vM SVm PVm BVm] leT physHistLook).

      assert (t_i ≤ t_l) as le.
      { etrans; first done. etrans; last done. f_equiv. solve_view_le. }

      eassert _ as  temp. { eapply read_atomic_location; done. }
      destruct temp as (s_l & encSL & ? & ? & ? & <- & orderRelated).

      iDestruct ("impl" $! _ vM orderRelated) as "(safe & _)".
      iEval (monPred_simpl) in "safe".
      iEval (setoid_rewrite monPred_at_pure) in "safe".
      simpl.
      iApply ("safe" $! (TV ⊔ (SVm, PVm, ∅)) with "[%]").
      { solve_view_le. }

      iDestruct (big_sepM2_lookup_acc with "predHolds") as "[predHolds predMap]";
        [done|done|].
      simpl.
      iNext.
      iDestruct (predicate_holds_phi_decode with "predEquiv predHolds") as "PH";
        first done.
      iApply monPred_mono; last iApply "PH". solve_view_le. }
    iEval (simpl).
    iIntros "!>" (t_l v_l ???? succ) "(%le & #val2 & % & % & disj)".
    iFrame "val2".
    iDestruct "disj" as "[H|H]"; iDestruct "H" as "(-> & -> & pts)".
    - (* success *)
      iDestruct "reins" as "[reins _]".

      (* The loaded timestamp is greater or equal to the one we know of. *)
      assert (t_i ≤ t_l) as lte.
      { etrans; first done. etrans; last done. f_equiv. solve_view_le. }

      eassert _ as  temp. { eapply read_atomic_location; done. }
      destruct temp as (s_l & encSL & ? & ? & ? & <- & orderRelated).

      iDestruct (big_sepM2_delete with "predHolds") as "[predL predMap]";
        [done|done|].
      simpl.

      iDestruct (predicate_holds_phi_decode with "predEquiv predL") as "PH";
        first done.

      iDestruct ("impl" $! _ _ orderRelated) as "[hi [(%above & below & impl1 & impl2) _]]".
      rewrite monPred_at_objectively.

      iDestruct ("impl1" with "PH") as "[PH R]".
      iEval (monPred_simpl) in "impl2".
      iDestruct ("impl2" $! (TV ⊔ (SVm, FVm, ∅)) with "[] [R]") as "[HI Q]".
      { iPureIntro. apply thread_view_le_l. }
      { iApply monPred_mono; last iApply "R". apply thread_view_le_r. }

      iAssert (
        ⌜increasing_map (encode_relation sqsubseteq) (<[(t_l + 1)%nat := encode s_t]> absHist)⌝
      )%I as %incri.
      {

        iApply (bi.pure_mono).
        { apply
            (increasing_map_insert_succ _ _ _ _ (encode s_t) increasing
                                          H3).
          eapply encode_relation_decode_iff; eauto using decode_encode. }
        iIntros (t_c e_c ? ?).

        assert (is_Some (physHist !! t_c)) as [[v_c cSV cFV ?] look2].
        { rewrite -elem_of_dom domEq elem_of_dom. done. }

        eassert _ as  temp. { eapply (read_atomic_location t_l t_c); done || lia. }
        destruct temp as (s_c & encSC & ? & decodeS' & ? & <- & orderRelated2).
        simplify_eq.
        rewrite /encode_relation. rewrite decode_encode. rewrite decodeS'.
        simpl.

        iDestruct (big_sepM2_delete with "predMap") as "[predC predMap]".
        { rewrite lookup_delete_ne; [apply look2 | lia]. }
        { rewrite lookup_delete_ne; [apply a | lia]. }

        iDestruct (predicate_holds_phi_decode with "predEquiv predC") as "predC";
          first done.
        simpl.

        iSpecialize ("below" $! s_c v_c orderRelated2).
        iEval (monPred_simpl) in "below".
        iApply ("below" $! (TV ⊔ (SVm, FVm, ∅) ⊔ (_, _, _)) with "[%] [PH] [predC]").
        { rewrite -assoc. apply thread_view_le_l. }
        2: { iApply monPred_mono; last iApply "predC". apply thread_view_le_r. }
        { iApply monPred_mono; last iApply "PH".
          destruct TV as [[??]?].
          rewrite thread_view_lub.
          solve_view_le. } }

      iDestruct (big_sepM2_insert_delete _ _ _ _ (Msg _ _ _ _) with "[PH $predMap]") as "predMap".
      { iApply predicate_holds_phi_decode; [done|done|].
        iApply monPred_mono; last iApply "PH". simpl. done. }
      rewrite (insert_id physHist t_l); last done.
      rewrite (insert_id absHist t_l); last done.

      iMod ("reins" $! (t_l + 1) s_t
        with "[//] [//] [] [] [HI predMap] fullHist [//] pts") as "(#frag & $)".
      { iPureIntro. simpl. apply lookup_zero_insert. }
      { done. }
      {
        iApply (big_sepM2_insert_2 with "[HI] predMap").
        simpl.
        rewrite /encoded_predicate_holds.
        iExists (prot.(protocol.pred) s_t v_t).
        iSplit.
        { iApply pred_encode_Some. done. }
        destruct TV as [[??]?].
        iDestruct (into_no_buffer_at with "HI") as "HI".

        iApply monPred_mono; last iFrame.
        destruct TV' as [[??]?].
        repeat split; last done.
        - eapply view_lub_le; solve_view_le.
        - solve_view_le. }

      iModIntro.

      iSplitPure. { solve_view_le. }

      iSpecialize ("Φpost" $! _ true s_l).
      iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".
      { iPureIntro. solve_view_le. }
      iLeft.
      iSplitPure; first done.
      iSplitL "Q".
      { rewrite /post_fence. simpl.
        iApply monPred_mono; last iApply "Q".
        repeat destruct_thread_view; repeat destruct_thread_view_le.
        rewrite thread_view_lub.
        assert (SV ⊔ SVm ⊑ <[ℓ:=MaxNat (t_l + 1)]> (SV ⊔ SVm)) as le2.
        { apply view_insert_le. rewrite lookup_zero_lub. lia. }
        apply thread_view_le.
        - etrans; last apply le2. solve_view_le.
        - apply view_lub_le; solve_view_le.
        - simpl_view. solve_view_le. }
      iExists _.
      iFrame "#".
      simpl. iPureIntro. rewrite lookup_zero_insert. done.
    - (* failure *)
      iDestruct "reins" as "[_ reins]".
      iModIntro.

      (* The loaded timestamp is greater or equal to the one we know of. *)
      assert (t_i ≤ t_l) as lte.
      { etrans; first done. etrans; last done. f_equiv. solve_view_le. }

      eassert _ as  temp. { eapply read_atomic_location; done. }
      destruct temp as (s_l & encSL & ? & ? & ? & <- & orderRelated).

      iDestruct (big_sepM2_lookup_acc with "predHolds") as "[predHolds predMap]";
        [done|done|].
      simpl.

      iDestruct (predicate_holds_phi_decode with "predEquiv predHolds") as "PH";
        first done.

      iDestruct ("impl" $! _ _ orderRelated) as "[HI [_ [impl Q3]]]".
      rewrite monPred_at_objectively.
      iSpecialize ("impl" $! (∅, ∅, ∅)).
      iEval (monPred_simpl) in "impl".
      iDestruct ("impl" $! _ with "[%] PH") as "[PH Q2]".
      { solve_view_le. }

      iSpecialize ("predMap" with "[PH]").
      { iApply predicate_holds_phi_decode; done. }

      iDestruct ("reins" with "[$] [$] [$]") as "$".

      iSplitPure. { repeat split; try done; apply view_le_l. }

      iSpecialize ("Φpost" $! _ false s_l).
      iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".

      { iPureIntro.
        etrans; first done. repeat split; auto using view_le_l. }
      iRight.
      iSplitPure; first done.
      iSplitPure; first done.
      rewrite /post_fence. simpl.
      iSplitL "Q2"; iApply monPred_mono; try iFrame.
      { repeat split; eauto using view_le_r, view_empty_least.
        rewrite assoc. apply view_le_r. }
      { etrans; first done. etrans; first done. repeat split; auto using view_le_l. }
    Qed.

  (** [Q1] is the resource we want to extract in case of success and and [Q2] is
  the resource we want to extract in case of failure. *)
  Lemma wp_cas_at Q1 Q2 Q3 ℓ prot s_i (v_i v_t : val) R s_t st E :
    {{{
      ⎡ is_at_loc ℓ ⎤ ∗
      store_lb ℓ prot s_i ∗
      (∀ s_l v_l, ⌜ s_i ⊑ s_l ⌝ -∗
        ((▷ prot.(pred) s_l v_l _) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (((* in case of success *)
          (* The state we write fits in the history. *)
          ⌜ s_l ⊑ s_t ⌝ ∗
          (∀ s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ prot.(pred) s_l v_l _ -∗
            prot.(pred) s_n v_n _ -∗ ⌜ s_t ⊑ s_n ⌝) ∗
          (* Extract from the location we load. *)
          (<obj> (prot.(pred) s_l v_l _ -∗ prot.(pred) s_l v_l _ ∗ R s_l)) ∗
          (* Establish the invariant for the value we store. *)
          (R s_l -∗ prot.(pred) s_t v_t _ ∗ Q1 s_l))
        ∧ (* in case of failure *)
          ((<obj> (prot.(pred) s_l v_l _ -∗ prot.(pred) s_l v_l _ ∗ Q2 s_l)) ∗ Q3)
        ))
    }}}
      CAS #ℓ v_i v_t @ st; E
    {{{ b s_l, RET #b;
      (⌜ b = true ⌝ ∗ <fence> Q1 s_l ∗ store_lb ℓ prot s_t) ∨
      (⌜ b = false ⌝ ∗ ⌜ s_i ⊑ s_l ⌝ ∗ <fence> (Q2 s_l) ∗ Q3)
    }}}.
  Proof.
    intros Φ.
    iIntros "H Φpost".
    iApply (wp_bind ([SndCtx])).
    iApply (wp_cmpxchg_at with "H").
    iIntros "!>" (v b s_l) "disj /=".
    iApply wp_pure_step_later; first done.
    iNext.
    iApply wp_value.
    iApply "Φpost".
    iApply "disj".
  Qed.

End wp_at_rules.
