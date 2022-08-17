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
From self Require Export extra ipm_tactics encode_relation view view_slice.
From self.lang Require Export lang lemmas tactics syntax.
From self.base Require Import primitive_laws.
From self Require Import solve_view_le.
From self.high Require Export dprop resources crash_weakestpre weakestpre
     lifted_modalities monpred_simpl modalities protocol locations.
From self.high Require Import locations protocol.
From self.high.modalities Require Import no_buffer.

Section wp_at_rules.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (prot : LocationProtocol ST).

  (** * Shared points-to predicate *)

  Lemma msg_persisted_views_eq
        (ℓ : loc) (hists : gmap loc (gmap time (message * positive)))
        (hist : gmap time (message * positive)) (msg : message)
        (atLocs : gset loc) (t : time) (s' : positive) γ :
    map_Forall
      (λ _ : loc,
        map_Forall
          (λ _ '(msg, _), msg_persist_view msg = msg_persisted_after_view msg))
      (restrict atLocs hists) →
    hists !! ℓ = Some hist →
    hist !! t = Some (msg, s') →
    own γ (● (atLocs : gsetUR loc)) -∗
    own γ (◯ {[ℓ]}) -∗
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

  Lemma interp_insert_loc_at ℓ prot s SV PV BV nG v :
    SV !!0 ℓ = 0 →
    interp -∗
    pred prot s v (SV, PV, BV, nG) -∗
    ℓ ↦h initial_history AT SV PV v ==∗
    (ℓ ↦_AT^{prot} [s]) (SV, PV, BV, nG) ∗ interp.
  Proof.
    iIntros (svLook).
    iNamed 1.
    iIntros "pred pts".

    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { assert (is_Some (offsets !! ℓ)) as (? & ?).
      { apply elem_of_dom. rewrite -offsetsDom. apply elem_of_dom. done. }
      iDestruct (big_sepM_lookup with "ptsMap") as "pts'".
      { apply map_lookup_zip_with_Some. naive_solver. }
      iDestruct (mapsto_valid_2 with "pts pts'") as (?) "_".
      done. }

    iDestruct (big_sepM2_dom with "predsHold") as %domEq.
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq2.
    iDestruct (big_sepM2_dom with "predPostCrash") as %domEq3.
    iDestruct (big_sepM2_dom with "bumpMono") as %domEq4.

    assert (offsets !! ℓ = None) as offsetsLook.
    { apply not_elem_of_dom. rewrite -offsetsDom. apply not_elem_of_dom. done. }
    assert (abs_hists !! ℓ = None) as absHistsLook.
    { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom.
      assumption. }
    assert (ℓ ∉ dom (gset _) abs_hists) as absHistsDomElem.
    { apply not_elem_of_dom. done. }

    (* We update ghost state. *)

    (* Update ghost state for physical history. *)
    iMod (auth_map_map_insert_top with "physHist") as "[physHist #physHistFrag]".
    { done. }

    (* Add the predicate to the ghost state of predicates. *)
    iMod (own_all_preds_insert with "predicates") as "[predicates knowPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite domEq3. congruence. }

    (* Add a new offset to the ghost state of offfsets. *)
    iMod (ghost_map_insert_persist _ 0 with "offsets") as "[offsets #offset]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

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

    iAssert (know_protocol ℓ prot (SV, PV, BV, nG)) as "#prot".
    { rewrite /know_protocol.
      monPred_simpl.
      simpl.
      rewrite !monPred_at_embed.
      iFrame "knowPred knowBumper knowOrder". }

    iModIntro.
    iSplitL "knowPred knowBumper".
    { rewrite /mapsto_at.
      iExists _, {[ 0 := (Msg v SV PV PV) ]}, 0, 0, 0, s, _.
      iSplitPure; first done.
      iSplitPure; first apply map_sequence_singleton.
      iSplitPure; first apply map_sequence_singleton.
      iSplitPure. { apply map_no_later_singleton. }
      iSplitPure. { set_solver+. }
      simpl. rewrite monPred_at_embed.
      iFrame "prot offset isShared".
      iSplitPure. { apply increasing_map_singleton. }
      iEval (rewrite 2!big_sepM_singleton).
      simpl.
      rewrite monPred_at_sep.
      simpl.
      rewrite !monPred_at_embed.
      iDestruct (frag_history_equiv with "fragHist") as "$".
      iFrame "physHistFrag".
      iPureIntro. solve_view_le. }
      simpl.

    repeat iExists _.
    iSplitL "ptsMap pts".
    { erewrite <- map_insert_zip_with. erewrite big_sepM_insert.
      - iFrame "ptsMap". erewrite view_slice.drop_prefix_zero. iFrame "pts".
      - apply map_lookup_zip_with_None. naive_solver. }
    iFrameF "offsets". iFrameF "physHist".
    iFrame "crashedAt history predicates allOrders naLocs atLocs".

    (* oldViewsDiscarded *)
    iSplit.
    { iApply big_sepM2_insert; [done|done|].
      iFrame "oldViewsDiscarded".
      iPureIntro. rewrite /initial_history.
      intros ??? [<- ?]%lookup_singleton_Some. lia. }
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
    iSplitPure.
    { rewrite -map_insert_zip_with.
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
        (* destruct TV as [[??]?]. *)
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
    {{{ prot.(pred) s v }}}
      ref_AT v @ st; E
    {{{ ℓ, RET #ℓ; ℓ ↦_AT^{prot} [s] }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "phi".
    iIntros ([TV' ?] [incl [= <-]]) "Φpost".
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
      as "(pts & interp)"; first done.
    { iApply monPred_mono; last iApply "phi". split; last done. etrans; done. }
    iModIntro.
    rewrite -assoc. iSplit; first done.
    iFrame "interp".
    iSpecialize ("Φpost" $! ℓ).
    monPred_simpl. 
    iApply ("Φpost" with "[] pts").
    { done. }
  Qed.

  Definition encoded_predicate_hold nG physHist (absHist : gmap nat positive) pred : iProp Σ :=
    ([∗ map] msg;encS ∈ physHist;absHist,
      encoded_predicate_holds pred encS
                              (msg_val msg)
                              (msg_store_view msg,
                              msg_persisted_after_view msg, ∅, nG)).

  Definition loc_info nG ℓ prot (pred : enc_predicateO) physHists physHist absHist offset : iProp Σ :=
    "physHists" ∷ auth_map_map_auth phys_history_name physHists ∗
    "%physHistsLook" ∷ ⌜ physHists !! ℓ = Some physHist ⌝ ∗
    "%domEq" ∷ ⌜ dom (gset _) physHist = dom _ absHist ⌝ ∗
    "%increasing" ∷ ⌜ increasing_map (encode_relation (⊑@{ST})) absHist ⌝ ∗
    "%atInvs" ∷
      ⌜ map_Forall (λ t msg, atomic_loc_inv ℓ t msg) (drop_prefix physHist offset) ⌝ ∗
    "#predEquiv" ∷ ▷ (pred ≡ encode_predicate (protocol.pred prot)) ∗
    "#frags" ∷ ([∗ map] k2 ↦ v ∈ absHist, frag_entry abs_history_name ℓ k2 v) ∗
    "predHolds" ∷ encoded_predicate_hold nG physHist absHist pred ∗
    "fullHist" ∷ know_full_encoded_history_loc ℓ 1 absHist ∗
    "pts" ∷ ℓ ↦h drop_prefix physHist offset.

  Definition insert_impl nG ℓ prot pred physHists physHist absHist offset : iProp Σ :=
    ∀ t s es msg,
      ⌜ offset ≤ t ⌝ -∗
      ⌜ encode s = es ⌝ -∗
      ⌜ physHist !! t = None ⌝ -∗
      ⌜ msg_store_view msg !!0 ℓ = t - offset ⌝ -∗
      ⌜ msg_persist_view msg = msg_persisted_after_view msg ⌝ -∗
      auth_map_map_auth phys_history_name physHists -∗
      encoded_predicate_hold nG (<[ t := msg ]>physHist) (<[ t := es ]>absHist) pred -∗
      know_full_encoded_history_loc ℓ 1 absHist -∗
      ⌜ increasing_map (encode_relation (⊑@{ST})) (<[ t := es ]>absHist) ⌝ -∗
      ℓ ↦h (drop_prefix (<[t := msg ]> physHist) offset) ==∗
      know_frag_history_loc ℓ t s ∗
      auth_map_map_frag_singleton phys_history_name ℓ t msg ∗
      interp.

  Definition lookup_impl nG ℓ prot pred physHists physHist absHist offset : iProp Σ :=
    auth_map_map_auth phys_history_name physHists -∗
    encoded_predicate_hold nG physHist absHist pred -∗
    know_full_encoded_history_loc ℓ 1 absHist -∗
    ℓ ↦h drop_prefix physHist offset -∗
    interp.

  (* Get all information inside [interp] related to the location [ℓ]. *)
  Lemma interp_get_at_loc nG ℓ prot offset :
    interp -∗
    is_at_loc ℓ -∗
    know_protocol ℓ prot (⊥, nG) -∗
    ℓ ↪[ offset_name ]□ offset -∗
    ∃ physHists physHist (absHist : gmap nat positive) pred,
      loc_info nG ℓ prot pred physHists physHist absHist offset ∗
      (insert_impl nG ℓ prot pred physHists physHist absHist offset ∧
        lookup_impl nG ℓ prot pred physHists physHist absHist offset).
  Proof.
    iNamed 1.
    iIntros "isAt".
    rewrite /know_protocol.
    iDestruct 1 as "(#knowPred & #knowPreorder & #knowBumper)".
    rewrite /know_pred_d /know_preorder_loc_d /know_bumper_d.
    rewrite !lift_d_at.
    iIntros "offset".

    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    (* iDestruct (full_map_frag_singleton_agreee with "history hist") *)
    (*   as %(absHist & enc & absHistLook & lookTS & decodeEnc). *)
    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
    iDestruct (ghost_map_lookup with "offsets offset") as %?.
    iDestruct (location_sets_singleton_included with "atLocs isAt") as %ℓSh.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (abs_hists !! ℓ)) as [absHist absHistLook].
    { rewrite -elem_of_dom. set_solver. }
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

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
    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]".
    { apply map_lookup_zip_with_Some. naive_solver. }

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

    iExists phys_hists, physHist, absHist, pred.
    (* Give resources. *)
    iFrame (domEq increasingMap). iFrame (invs).
    iFrame "predsEquiv".
    iFrame "predHolds".
    iFrame "histFrags".
    iFrame "pts".
    iFrame "fullHist".
    iFrame "physHist".
    iSplitPure; first apply physHistsLook.

    (* We show the two different implications. *)
    iSplit.
    { (* Get back resources. *)
      iIntros (t_i s2 es msg ? encEs lookNone viewLook ?)
        "physHists predHolds fullHist order pts".

      assert (absHist !! t_i = None)%I as absHistLookNone.
      { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom. done. }

      iMod (full_map_full_entry_insert _ _ _ _ es with "history fullHist")
        as "(history & fullHist & #histFrag)"; first done.

      iDestruct (big_sepM_insert_delete with "[$atLocsHistories $fullHist]")
        as "atLocsHistories".
      iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".
      iEval (rewrite map_insert_zip_with) in "ptsMap".
      iEval (rewrite (insert_id offsets); last done) in "ptsMap".

      iDestruct (big_sepM2_insert_delete with "[$allPredsHold predHolds]")
        as "allPredsHold".
      { iExists pred. rewrite naViewLook. iFrame "predHolds". done. }

      iMod (auth_map_map_insert with "physHists") as "(physHists & _ & physHistFrag)"; [try done|try done|].

      iDestruct (big_sepM2_insert_delete with "[$ordered2 $order]") as "ordered3".
      rewrite (insert_id orders). (* last congruence. *)
      2: { rewrite ordersLook. f_equal.
          rewrite orderEq.
          reflexivity. }

      iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

      iModIntro.
      iSplit; first (iApply frag_history_equiv; rewrite -encEs; iFrame "histFrag").
      iFrameF "physHistFrag".
      (* We re-establish [interp]. *)
      repeat iExists _.
      iFrameF "ptsMap".
      iFrameF "offsets".
      iFrameF "physHists".
      iFrame "allOrders".
      iFrame "ordered3".
      iFrame "allPredsHold".
      iFrame "history predicates".
      iFrame "crashedAt".
      iFrame "atLocs".
      iFrame "naView naLocs allBumpers bumpMono".
      (* oldViewsDiscarded *)
      iSplit.
      { iEval (erewrite <- (insert_id offsets); last done).
        iApply (big_sepM2_insert_2 with "[] oldViewsDiscarded").
        iIntros (t2 ?).
        iDestruct (big_sepM2_lookup _ _ _ ℓ with "oldViewsDiscarded") as %hi;
          [done|done|].
        destruct (decide (t_i = t2)) as [->|neq].
        - iIntros (?). lia.
        - rewrite lookup_insert_ne; last done.
          iPureIntro. apply hi. }
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
      (* [mapShared] - We need to show that the newly inserted message satisfied *)
  (*     the restriction on shared locations that their persist view and their *)
  (*     persisted after view is equal. *)
      iSplit.
      { iPureIntro.
        erewrite <- (insert_id offsets); last done.
        rewrite -map_insert_zip_with.
        setoid_rewrite (restrict_insert ℓ); last done.
        rewrite /shared_locs_inv.
        apply Nat.le_exists_sub in H2 as (tE & -> & ?).
        rewrite -drop_prefix_insert.
        apply map_map_Forall_insert_2.
        - apply restrict_lookup_Some_2; last done.
          apply map_lookup_zip_with_Some. naive_solver.
        - simpl.
          rewrite /atomic_loc_inv.
          split; last done.
          rewrite viewLook. lia.
        - done. }
      iSplitL "atLocsHistories".
      {
        rewrite /know_full_encoded_history_loc.
        (* NOTE: This rewrite is mega-slow. *)
        iEval (setoid_rewrite (restrict_insert ℓ at_locs (<[t_i:=es]> absHist) abs_hists ℓSh)).
        iFrame. }
      iFrameF "predPostCrash".
      iFrame (bumperBumpToValid).
      (* "bumperSome" *)
      iApply (big_sepM2_update_left with "bumperSome"); eauto.
      iPureIntro. intros bumperSome.
      apply map_Forall_insert_2; eauto.
      rewrite /encode_bumper. rewrite -encEs decode_encode. done. }
      { iIntros "physHists predHolds fullHist pts".
        iDestruct (big_sepM_insert_delete with "[$atLocsHistories $fullHist]")
          as "atLocsHistories".
        iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".
        iDestruct (big_sepM2_insert_delete with "[$ordered2]") as "ordered3";
          first done.
        iDestruct (big_sepM2_insert_delete with "[$allPredsHold predHolds]")
          as "allPredsHold".
        { iExists pred. rewrite naViewLook. iFrame "predHolds". done. }

        rewrite (insert_id orders); last congruence.
        iEval (rewrite map_insert_zip_with) in "ptsMap".
        iEval (rewrite (insert_id offsets); last done) in "ptsMap".
        rewrite (insert_id phys_hists); last congruence.
        rewrite (insert_id abs_hists); last congruence.
        rewrite (insert_id (restrict at_locs abs_hists)).
        2: { apply restrict_lookup_Some_2; done. }

        (* We re-establish [interp]. *)
        repeat iExists _.
        iFrameF "ptsMap".
        iFrameF "offsets".
        iFrameF "physHists".
        iFrameF "oldViewsDiscarded".
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

  Lemma read_atomic_location_no_inv t_i t_l (physHist : history) absHist vm SVm FVm
        PVm ℓ (e_i : positive) (s_i : ST) :
    t_i ≤ t_l →
    dom (gset _) physHist = dom _ absHist →
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
    t_i ≤ t_l + offset →
    dom (gset _) physHist = dom _ absHist →
    absHist !! t_i = Some e_i →
    decode e_i = Some s_i →
    increasing_map (encode_relation (⊑@{ST})) absHist →
    map_Forall (λ (t : nat) (msg : message), atomic_loc_inv ℓ t msg)
               (drop_prefix physHist offset) →
    physHist !! (t_l + offset) = Some (Msg vm SVm FVm PVm) →
    ∃ s_l e_l,
      absHist !! (t_l + offset) = Some e_l ∧
      decode e_l = Some s_l ∧
      SVm !!0 ℓ = t_l ∧
      FVm = PVm ∧
      s_i ⊑ s_l.
  Proof.
    intros le domEq ? decodeEnc ? atInvs ?.
    eassert _ as temp.
    { eapply map_Forall_lookup_1; first apply atInvs.
      rewrite drop_prefix_lookup. done. }
    rewrite /atomic_loc_inv /= in temp. destruct temp as [SV'lookup <-].
    assert (is_Some (absHist !! (t_l + offset))) as (e_l & ?).
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

  Lemma map_sequence_big_sepM_sepL {A} (m : gmap nat A) lo hi ss (ϕ : A  → iProp Σ) :
    map_sequence m lo hi ss →
    ([∗ map] k ↦ y ∈ m, ϕ y) -∗
    ([∗ list] y ∈ ss, ϕ y) ∗ (([∗ list] y ∈ ss, ϕ y) -∗ [∗ map] k ↦ y ∈ m, ϕ y).
  Proof.
    generalize dependent m.
    generalize dependent lo.
    induction ss as [|x ss' IH]; first done.
    iIntros (lo m seq) "M".
    destruct ss' as [|x2 ss''].
    { destruct seq as [look ->]. rewrite /= right_id.
      iApply (big_sepM_lookup_acc with "M"). done. }
    simpl.
    destruct seq as (look & lo2 & ? & ? & ?).
    iDestruct (big_sepM_delete with "M") as "[$ M]"; first done.
    iDestruct (IH lo2 with "M") as "[horse bing]".
    { apply map_sequence_delete_below; done. }
    simpl.
    iFrame "horse".
    iIntros "[Hx Hx2]".
    iDestruct ("bing" with "Hx2") as "H2".
    iApply big_sepM_delete; first done.
    iFrame.
  Qed.

  Lemma map_sequence_big_sepM2_sepL2 {A B}
    (m1 : gmap nat A) (m2 : gmap nat B) tLo tHi ss ms
    (ϕ : A  → B → iProp Σ) :
    map_sequence m1 tLo tHi ss →
    map_sequence m2 tLo tHi ms →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, ϕ y1 y2) -∗
    ([∗ list] y1;y2 ∈ ss;ms, ϕ y1 y2) ∗
    (([∗ list] y1;y2 ∈ ss;ms, ϕ y1 y2) -∗ [∗ map] k ↦ y1;y2 ∈ m1;m2, ϕ y1 y2).
  Proof.
    iIntros (seq1 seq2).
    rewrite big_sepM2_alt.
    rewrite big_sepL2_alt.
    iIntros "(%domEq & M)".
    apply dom_eq_alt_L in domEq.
    assert (length ss = length ms) as lenEq.
    { eapply map_sequence_dom_length; done. }
    iFrame (lenEq).
    iDestruct (map_sequence_big_sepM_sepL with "M") as "[L Lreins]".
    { apply map_sequence_zip; done. }
    iFrame "L".
    iIntros "[_ L]".
    iDestruct ("Lreins" with "L") as "$".
    iPureIntro. apply dom_eq_alt_L. done.
  Qed.

  (* Lemma bingo {A B} (m1 : gmap nat A) (m2 : gmap nat B) tLo tHi ss ms *)
  (*   (ϕ : A  → B → dProp Σ) : *)
  (*   map_sequence m1 tLo tHi ss → *)
  (*   map_sequence m2 tLo tHi ms → *)
  (*   ⊢ ([∗ list] y1;y2 ∈ ss;ms, ϕ y1 y2) ∗-∗ ([∗ map] k ↦ y1;y2 ∈ m1;m2, ϕ y1 y2). *)
  (* Proof. *)
  (*   iIntros (seq1 seq2). *)
  (* Qed. *)

  (* Lemma big_sepM2_union {A B} (Φ : nat → A → B → iProp Σ) (m1 m2 : gmap nat A) *)
  (*     (n1 n2 : gmap nat B) : *)
  (*   m1 ##ₘ m2 → *)
  (*   n1 ##ₘ n2 → *)
  (*   ([∗ map] k↦y1;y2 ∈ (m1 ∪ m2);(n1 ∪ n2), Φ k y1 y2) *)
  (*   ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;n1, Φ k y1 y2) ∗ ([∗ map] k↦y1;y2 ∈ m2;n2, Φ k y1 y2). *)
  (* Proof. *)
  (*   intros disj1 disj2. *)
  (*   rewrite !big_sepM2_alt. *)
  (*   rewrite big_sepM_union. *)
  (*   apply big_opM_union. *)
  (* Qed. *)

  (* Lemma bingobongo (ϕ : ST → _) (pred : enc_predicateO) physHist absHist *)
  (*     encAbsHist fullEncAbsHist : *)
  (*   absHist = omap decode encAbsHist → *)
  (*   encAbsHist ⊆ fullEncAbsHist → *)
  (*   (pred ≡ encode_predicate ϕ) -∗ *)
  (*   encoded_predicate_hold physHist fullEncAbsHist pred -∗ *)
  (*   ([∗ map] msg;s ∈ physHist;absHist, *)
  (*     ϕ s (msg_val msg) _ (msg_store_view msg, msg_persisted_after_view msg, ∅)). *)

  Lemma extract_list_of_preds hG abs_hist (phys_hist : history) tLo tS ss ms prot
    ℓ encAbsHist (pred : enc_predicateO) TV :
    abs_hist = omap decode encAbsHist →
    map_sequence abs_hist tLo tS ss →
    map_sequence phys_hist tLo tS ms →
    map_Forall (λ t msg,
      msg_store_view msg ⊑ store_view TV ∧
        msg_persisted_after_view msg ⊑ flush_view TV) phys_hist →
    dom (gset nat) abs_hist = dom (gset nat) phys_hist →
    (pred ≡ encode_predicate (protocol.pred prot)) -∗
    encoded_predicate_hold hG phys_hist encAbsHist pred -∗
    ([∗ list] s;v ∈ ss;(msg_val <$> ms), protocol.pred prot s v) (TV, hG).
  Proof.
    iIntros (-> seqAbs seqPhys msgIncl domEq) "#equiv P".
    rewrite /encoded_predicate_hold.
    iDestruct (big_sepM2_impl_dom_subseteq _ _ _ _ phys_hist (omap decode encAbsHist) with "P []") as "P1".
    { done. }
    { done. }
    { iIntros "!>" (t m es m2 s ? encLook ? look) "H".
      apply lookup_omap_Some in look as (? & ? & ?).
      assert (m = m2) as <- by congruence.
      assert (es = x) as <- by congruence.
      iDestruct (predicate_holds_phi_decode_1 with "equiv H") as "H"; first done.
      iApply "H". }
    iDestruct (map_sequence_big_sepM2_sepL2 with "P1") as "[P1 Lreins]"; first done.
    { done. }
    rewrite big_sepL2_flip.
    rewrite monPred_at_big_sepL2.
    rewrite big_sepL2_fmap_r.
    iApply (big_sepL2_impl with "P1").
    iIntros "!>" (idx s msg ? msLook) "pred".
    iApply monPred_mono; last iApply "pred".
    destruct TV as [[??]?].
    eapply map_sequence_list_lookup in msLook as (? & ? & look); last apply seqPhys.
    apply msgIncl in look as [??].
    repeat split; try done. apply view_empty_least.
  Qed.

  Lemma wp_load_at ℓ ss s Q1 Q2 prot st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s]) ∗
      (* The case where we read an already known write. *)
      ((∀ vs vL, ∃ P,
        ⌜ last vs = Some vL ⌝ -∗
        (* Extract knowledge from all the predicates. *)
        (* NOTE: Maybe demand that [P] is persistent instead of pers. mod. *)
        (([∗ list] s; v ∈ ss ++ [s];vs, prot.(pred) s v) -∗ □ P) ∗
        (* Using the [P] and the predicate for the loaded location show [Q1]. *)
        (P -∗ <obj> (prot.(pred) s vL -∗ Q1 vL ∗ prot.(pred) s vL))) ∧
      (* The case where we read a new write. *)
      (∀ vs vL sL, ∃ P,
        ⌜ s ⊑ sL ⌝ -∗
        (* Extract knowledge from all the predicates. *)
        (([∗ list] s; v ∈ (ss ++ [s]) ++ [sL];vs ++ [vL], prot.(pred) s v) -∗ □ P) ∗
        (P -∗ <obj> (prot.(pred) sL vL -∗ Q2 sL vL ∗ prot.(pred) sL vL))))
    }}}
      !_AT #ℓ @ st; E
    {{{ vL, RET vL;
      (∃ sL, ℓ ↦_AT^{prot} ((ss ++ [s]) ++ [sL]) ∗ <fence> Q2 sL vL) ∨
      (* We didn't have to give the points-to predicate back here, but doing
       * that is useful for users of the lemma. *)
      (ℓ ↦_AT^{prot} (ss ++ [s]) ∗ <fence> Q1 vL)
    }}}.
  Proof.
    intros Φ.
    iModel.
    iDestruct 1 as "(#pts & pToQ)".
    iAssert (_) as "ptsCopy". { iApply "pts". }
    iDestruct "pts" as (abs_hist phys_hist tLo tS offset s' ms) "H". iNamed "H".
    assert (s' = s) as ->. { apply (inj Some). rewrite -lastEq. apply last_snoc. }
    iDestruct "tSLe" as %tSLe.
    (* iDestruct (store_lb_protocol with "storeLb") as "#knowProt". *)
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(#knowPred & #knowPreorder & #knowBumper)".
    (* rewrite /store_lb. *)
    (* iDestruct "storeLb" as (tS offset) "(#prot & #hist & #offset & %tSLe)". *)

    (* We unfold the WP. *)
    iIntros ([TV' ?] [incl [= <-]]) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_load_acq_no_fork. }

    (* We open [interp]. *)
    iIntros "interp".
    simpl.
    setoid_rewrite monPred_at_embed.
    iDestruct (interp_get_at_loc gnames ℓ with "interp isAtLoc [locationProtocol] offset")
      as (physHists physHist absHist pred) "(R & [_ reins])".
    { rewrite /know_protocol.
      iEval (monPred_simpl).
      simpl.
      rewrite !monPred_at_embed.
      iFrame "locationProtocol". }
    iNamed "R".
    iEval (rewrite monPred_at_big_sepM) in "physHist".

    iEval (rewrite monPred_at_big_sepM) in "absHist".
    iEval (setoid_rewrite monPred_at_sep) in "physHist".
    simpl.
    setoid_rewrite monPred_at_embed.

    iAssert (⌜ phys_hist ⊆ physHist ⌝)%I as %sub.
    { rewrite map_subseteq_spec.
      iIntros (?? physHistLook).
      iDestruct (big_sepM_lookup with "physHist") as "[hi frag]"; first done.
      iDestruct (auth_map_map_auth_frag with "physHists frag") as %(physHist' & ? & ?).
      assert (physHist = physHist') as <-.
      { apply (inj Some). rewrite -physHistsLook. done. }
      done. }

    iDestruct (history_full_entry_frag_lookup_big with "fullHist absHist")
      as %(encAbsHist & subset & domEq2 & eqeq & map).

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iApply (wp_load_acquire (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (tL vL SV' PV' _PV') "(%look & %gt & #val' & pts)".

    iFrame "val'".

    assert (tS - offset ≤ tL) as lte.
    { etrans; first done. etrans; last done. f_equiv. solve_view_le. }
    assert (tS ≤ tL + offset) as lte2 by lia.
    rewrite drop_prefix_lookup in look.

    assert (abs_hist !! tS = Some s).
    { rewrite -lastEq. eapply map_sequence_lookup_hi; done. }
    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.
    iDestruct (history_full_entry_frag_lookup with "fullHist hist")
      as %(enc & lookTS & decodeEnc).

    rewrite <- pure_sep_l; last solve_view_le.

    (* The final view under the post fence modality where we will have to show
     * [Q]. *)
    set (TVfinal := (SV ⊔ SV', PV ⊔ (BV ⊔ PV'), BV ⊔ PV')).
    assert (TV ⊑ TVfinal).
    { etrans; first apply incl. etrans; first apply incl2.
      rewrite /TVfinal.
      solve_view_le. }
    (* All the messages in the physical history are included in [TVfinal]. *)
    iAssert (
      ⌜ map_Forall
        (λ (_ : nat) (msg : message),
           msg_store_view msg ⊑ store_view TVfinal
           ∧ msg_persisted_after_view msg ⊑ flush_view TVfinal) phys_hist ⌝
    )%I as %inTVFinal.
    { iIntros (? msg looki).
      iDestruct (big_sepM_lookup with "physHist") as "[[%have %have2] _]"; first done.
      iPureIntro.
      split.
      - solve_view_le.
      - etrans; first apply have2. rewrite /TVfinal.
        simpl.
        destruct TV as [[??]?].
        destruct TV' as [[??]?].
        simpl.
        apply view_lub_le.
        * solve_view_le.
        * solve_view_le. }

    destruct (decide (tS = tL + offset)) as [eq|neq].
    - iDestruct "pToQ" as "[pToQ _]".
      subst.

      assert (last (msg_val <$> ms) = Some vL).
      { rewrite fmap_last.
        apply map_sequence_lookup_hi_alt in slicePhys
          as (msg & physHistLook & ->).
        eapply map_subseteq_spec in sub; last done.
        rewrite -sub. rewrite look. done. }

      iDestruct ("pToQ" $! (msg_val <$> ms) vL) as (P) "pToQ".
      iDestruct ("pToQ" with "[]") as "[getP getQ]".
      { iPureIntro. done. }

      iEval (monPred_simpl) in "getP".
      iDestruct ("getP" $! (TVfinal, _) with "[//] [-]") as "#P".
      { iDestruct (extract_list_of_preds _ _ _ _ _ _ _ _ _ _ _ TVfinal
          with "predEquiv [predHolds]") as "L"; try done.
        iApply big_sepM2_impl_subseteq; try done.
        rewrite  -domEq2.
        rewrite absPhysHistDomEq.
        done. }
      iEval (monPred_simpl) in "getQ".
      iDestruct ("getQ" with "[%] P") as "bing"; first done.
      rewrite monPred_at_objectively.

      eassert _ as temp.
      { eapply map_Forall_lookup_1; first apply atInvs.
        rewrite drop_prefix_lookup. done. }
      simpl.
      destruct temp as (? & pvEq).
      simpl in pvEq.

      iDestruct (big_sepM2_lookup_acc with "predHolds") as "[predHolds predMap]";
        [done|apply lookTS|].
      simpl.

      iDestruct (predicate_holds_phi_decode with "predEquiv predHolds") as "PH";
        first done.
      iDestruct ("bing" $! _ with "PH") as "[Q predHolds]".

      iDestruct ("predMap" with "[predHolds]") as "predMap".
      { iApply (predicate_holds_phi_decode with "predEquiv predHolds").
        assumption. }

      iModIntro.

      (* We re-establish [interp]. *)
      iDestruct ("reins" with "[$] [$] [$] [$]") as "$".

      iSpecialize ("Φpost" $! vL).
      monPred_simpl.
      iApply "Φpost".
      { iPureIntro.
        split; last done.
        etrans. eassumption.
        repeat split; try done; try apply view_le_l. }
      (* The thread view we started with [TV] is smaller than the view we ended
      with. *)
      (*
      assert (TV ⊑ (SV ⊔ SV', PV, BV ⊔ PV')).
      { clear H4. do 2 (etrans; first done). repeat split; auto using view_le_l. }
       *)
      iRight. simpl.
      iSplit. {
        (* We show what is, essentially, the points-to predicate that we started with. *)
        iExistsN.
        iFrameF (lastEq).
        iFrameF (slice).
        iFrameF (slicePhys).
        iFrameF (nolater).
        iFrameF (absPhysHistDomEq).
        iFrameF "isAtLoc".
        rewrite 3!monPred_at_embed.
        iFrameF "locationProtocol".
        iSplitPure; first done.
        rewrite /know_frag_history_loc_d.
        rewrite monPred_at_big_sepM.
        iEval (setoid_rewrite lift_d_at).
        iFrameF "absHist".
        iSplit.
        { iApply (monPred_mono _ (TV, _)).
          { split; last done.
            etrans; first apply incl.
            etrans; first apply incl2.
            solve_view_le. }
            rewrite monPred_at_big_sepM.
            setoid_rewrite monPred_at_sep.
            simpl.
            setoid_rewrite monPred_at_embed.
            iApply "physHist". }
        iFrameF "offset".
        iPureIntro.
        etrans; first apply tSLe.
        f_equiv.
        solve_view_le. }
      iApply monPred_mono; last iFrame "Q".
      rewrite -pvEq.
      split; last done.
      solve_view_le.
    - iDestruct "pToQ" as "[_ pToQ]".

      iMod (auth_map_map_lookup with "physHists") as "[physHists #physHistFrag]".
      { done. } { done. }

      eassert _ as temp. { eapply read_atomic_location; try done. }
      destruct temp as (sL & encSL & ? & ? & ? & <- & orderRelated).

      iDestruct ("pToQ" $! (msg_val <$> ms) vL sL) as (P) "pToQ".
      iDestruct ("pToQ" with "[//]") as "[getP getQ]".
      iEval (monPred_simpl) in "getP".
      iDestruct ("getP" $! (TVfinal, _) with "[//] [-]") as "#P".
      { iDestruct (big_sepM2_delete with "predHolds") as "[phiI predHolds]".
        { apply look. } { done. }
        iDestruct (predicate_holds_phi_decode with "predEquiv phiI") as "phiI";
          first done.
        simpl.
        rewrite big_sepL2_snoc.
        iSplitR "phiI".
        - iDestruct (extract_list_of_preds _
            (delete (tL + offset) abs_hist)
            (delete (tL + offset) phys_hist) tLo tS _ _ _ _ _ _ TVfinal
            with "predEquiv [predHolds]") as "$".
          * rewrite -eqeq. rewrite -omap_delete. reflexivity.
          * rewrite -eqeq.
            apply map_sequence_delete_above; first lia.
            rewrite eqeq.
            done.
          * apply map_sequence_delete_above; [lia|done].
          * eapply map_Forall_subseteq; last done.
            apply delete_subseteq.
          * rewrite 2!dom_delete_L.
            rewrite absPhysHistDomEq.
            set_solver+.
          * iApply big_sepM2_impl_subseteq; last iApply "predHolds".
            + apply delete_mono. done.
            + apply delete_mono. done.
            + rewrite 2!dom_delete_L.
              rewrite -absPhysHistDomEq.
              rewrite -domEq2.
              done.
        - iApply monPred_mono; last iApply "phiI".
          rewrite /TVfinal.
          split; last done.
          solve_view_le. }
      iEval (monPred_simpl) in "getQ".
      iDestruct ("getQ" with "[%] P") as "bing".
      { done. }
      rewrite monPred_at_objectively.

      eassert _ as temp.
      { eapply map_Forall_lookup_1; first apply atInvs.
        rewrite drop_prefix_lookup. done. }
      destruct temp as (? & pvEq).
      simpl in pvEq.

      iDestruct (big_sepM2_lookup_acc with "predHolds") as "[predHolds predMap]";
        [apply look|done|].

      iDestruct (predicate_holds_phi_decode with "predEquiv predHolds") as "PH";
        first done.
      iDestruct ("bing" $! _ with "PH") as "[Q predHolds]".

      iDestruct ("predMap" with "[predHolds]") as "predMap".
      { iApply (predicate_holds_phi_decode with "predEquiv predHolds").
        assumption. }

      iModIntro.

      (* We re-establish [interp]. *)
      iDestruct ("reins" with "[$] [$] [$] [$]") as "$".

      iSpecialize ("Φpost" $! vL).
      monPred_simpl.
      iApply "Φpost".
      { iPureIntro.
        split; last done.
        etrans. eassumption.
        repeat split; try done; try apply view_le_l. }
      iLeft. iExists (sL).
      iSplitR "Q"; last first.
      { simpl. iApply monPred_mono; last iFrame "Q".
        split; last done. solve_view_le. }
      iExists (<[ tL + offset := sL ]>abs_hist). iExistsN.
      iSplitPure. { rewrite last_snoc. reflexivity. }
      iSplitPure. { eapply map_sequence_insert_snoc; try done. lia. }
      iSplitPure.
      { eapply map_sequence_insert_snoc; last done; first lia.
        eapply map_no_later_dom; last apply nolater.
        done. }
      iSplitPure.
      { eapply map_no_later_insert; last done. lia. }
      iSplitPure.
      { rewrite 2!dom_insert_L. rewrite absPhysHistDomEq. done. }
      rewrite /is_at_loc_d lift_d_at.
      iFrameF "isAtLoc".
      rewrite big_sepM_insert. 2: { apply nolater. lia. }
      rewrite big_sepM_insert.
      2: {
        eapply map_dom_eq_lookup_None; first done.
        apply nolater. lia. }
      rewrite /know_pred_d /know_preorder_loc_d /know_bumper_d.
      rewrite 3!lift_d_at.
      iFrameF "locationProtocol".
      iSplitPure.
      { apply: increasing_map_insert_last; try done. lia. }
      rewrite /know_frag_history_loc_d.
      rewrite monPred_at_sep.
      rewrite monPred_at_big_sepM.
      setoid_rewrite lift_d_at.
      iFrame "absHist".
      iSplit.
      { iExists _.
        iSplitPure; first done.
        iApply (big_sepM_lookup with "frags"). done. }
      iFrame "#".
      iSplit; last first.
      { simpl. iPureIntro.
        rewrite lookup_zero_lub.
        rewrite H5. lia. }
      simpl.
      iSplit.
      { rewrite lift_d_at. simpl.
        iFrame "physHistFrag". solve_view_le. }
      iApply (monPred_mono _ (TV, _)).
      { split; last done.
        etrans; first apply incl.
        etrans; first apply incl2.
        solve_view_le. }
      rewrite monPred_at_big_sepM.
      setoid_rewrite monPred_at_sep.
      setoid_rewrite lift_d_at.
      simpl.
      iFrame "physHist".
      Unshelve. done.
      Unshelve. done.
  Qed.

  Lemma wp_load_at_simple ℓ sI Q prot st E :
      {{{
        ℓ ↦_AT^{prot} [sI] ∗
        <obj> (∀ sL vL, ⌜ sI ⊑ sL ⌝ -∗ prot.(pred) sL vL -∗ Q sL vL ∗ prot.(pred) sL vL)
      }}}
        !_AT #ℓ @ st; E
      {{{ sL vL, RET vL;
        ℓ ↦_AT^{prot} [sL] ∗
        post_fence (Q sL vL) }}}.
    Proof.
      iIntros (Φ) "[pts impl] post".
      iApply (wp_load_at _ [] _ (λ v, Q sI v) Q with "[$pts impl]").
      { iSplit.
        * iIntros (??).
          iExists True%I.
          iIntros (?).
          iSplitL ""; first naive_solver.
          iIntros "_".
          iApply (monPred_objectively_mono with "impl").
          iIntros "impl P".
          iApply ("impl" with "[//] P").
        * iIntros (???).
          iExists True%I.
          iIntros (?).
          iSplitL ""; first naive_solver.
          iIntros "_".
          iApply (monPred_objectively_mono with "impl").
          iIntros "impl P".
          iApply ("impl" with "[//] P"). }
      iNext.
      iIntros (?).
      iIntros "[L|R]".
      - iDestruct "L" as (?) "[pts Q]".
        iApply "post".
        iFrame "Q".
        iApply mapsto_na_drop.
        done.
      - iApply "post".
        iApply "R".
    Qed.

  (* Definition open_subjective (I P : dProp Σ) := <obj> I -∗ P ∗ I. *)

  (* This is a load lemma that allows for a sort of "threading" of resources
   * though all the invariants. The idea has some flaws (the order is arbitrary
   * for instance) but maybe it can be used to come up witha stronger load lemma. *)
  Lemma wp_load_at_strong ℓ ss s (QS : list (val → dProp Σ)) Q1 Q2 prot st E :
    length QS = length ss →
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s]) ∗
      (* Based on all the existing writes we can show [Q1]. *)
      ((∀ vs,
        ([∗ list] i ↦ s; v ∈ ss ++ [s];vs, ∃ Q Q',
          ⌜ QS !! i = Some Q ⌝ -∗
          ⌜ (QS ++ [Q1]) !! (S i) = Some Q' ⌝ -∗
          <obj> prot.(pred) s v -∗ Q v -∗  prot.(pred) s v ∗ Q' v)) ∧
      (* In case of a new write we can show [Q2] *)
      <obj> (∀ v v' s',
        ⌜ s ⊑ s' ⌝ -∗
        prot.(pred) s' v -∗
        Q1 v -∗
        prot.(pred) s' v' ∗ Q2 s' v'))
    }}}
      !_AT #ℓ @ st; E
    {{{ v, RET v;
      (∃ s', ℓ ↦_AT^{prot} (ss ++ [s] ++ [s']) ∗ <fence> Q2 s' v) ∨
      <fence> Q1 v
    }}}.
  Proof. Abort.

  Lemma wp_store_at ℓ ss s_i s_t v_t (prot : LocationProtocol ST) st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗
      prot.(pred) s_t v_t ∗
      (* NOTE: This does _not_ work. *)
      (* "phi" ∷ (∀ v_i, ϕ s_i v_i _ -∗ ϕ s_t v_t _ ∗ ϕ s_i v_i _) ∗ *)
      (* NOTE: This should work and be more general. *)
      (* "phi" ∷ (∀ v_i, (<obj> (ϕ s_i v_i -∗ ϕ s_i_v ∗ R)) ∗ (R -∗ ϕ s_t v_t)) ∗ *)
      ⌜ s_i ⊑ s_t ⌝ ∗
      (* The new state must be concurrent with possible other states. *)
      (∀ v_i s_c v_c, ⌜ s_i ⊑ s_c ⌝ -∗
        (* NOTE: We could give predicates for all states in ss here. *)
        prot.(pred) s_i v_i ∗ prot.(pred) s_t v_t ∗ prot.(pred) s_c v_c -∗
          ⌜ s_t ⊑ s_c ∧ s_c ⊑ s_t ⌝)
    }}}
      #ℓ <-_AT v_t @ st; E
    {{{ RET #(); ℓ ↦_AT^{prot} ((ss ++ [s_i]) ++ [s_t]) }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "(pts & phi & %targetGt & greater)".
    iDestruct "pts" as (abs_hist phys_hist tLo t_i offset s' ms) "H". iNamed "H".
    iDestruct "tSLe" as %tSLe.
    (* iDestruct (store_lb_protocol with "storeLb") as "#knowProt". *)
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(#knowPred & #knowPreorder & #knowBumper)".

    rewrite /store_lb.
    (* iDestruct "storeLb" as (t_i offset) "(#prot & #hist & #offset & %tSLe)". *)
    (* We unfold the WP. *)
    iIntros ([TV' ?] [incl [= <-]]) "Φpost".
    (* iIntros (TV' incl) "Φpost". *)
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. }
    { apply prim_step_store_rel_no_fork. }

    iIntros "interp".
  Admitted.
  (*
    iDestruct (interp_get_at_loc with "interp isAtLoc locationProtocol offset")
      as (physHists physHist absHist pred) "(R & [reins _])".
    iNamed "R".

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iApply (wp_store_release with "[$pts $val]").
    iIntros "!>" (t_t) "(%look & %gt & #valNew & pts)".
    simpl in gt.
    simpl in tSLe.
    rewrite drop_prefix_lookup in look.

    (* We can conclude that [t_t] is strictly greater than [t_i]. *)
    assert (t_i - offset < t_t) as tILtTt.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      destruct incl as [[??]?].
      destruct incl2 as [[??]?].
      eapply gt_le_trans; first done.
      etrans; first done.
      f_equiv.
      etrans; done. }
    assert (t_i < t_t + offset) as ? by lia.

    iFrame "valNew".

    assert (abs_hist !! t_i = Some s_i).
    { eapply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      apply slice. }
    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.

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
      ⌜increasing_map (encode_relation sqsubseteq) (<[(t_t+offset)%nat:=encode s_t]> absHist)⌝
                      )%I as %incri.
    { iApply (bi.pure_mono).
      { apply
         (increasing_map_insert_after _ _ _ _ _ (encode s_t) increasing
                                      absHistLook'); last done.
        eapply encode_relation_decode_iff; eauto using decode_encode. }
      iIntros (t_c e_c ? iLeC).

      assert (is_Some (physHist !! t_c)) as [[????] look2].
      { rewrite -elem_of_dom domEq elem_of_dom. done. }

      eassert _ as  temp. { eapply (read_atomic_location_no_inv t_i t_c); done || lia. }
      destruct temp as (s_c & encSC & ? & decodeS' & orderRelated).
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

    rewrite drop_prefix_insert.

    iMod ("reins" $! (t_t + offset) s_t
      with "[%] [//] [//] [] [] [$] [predHolds phi] fullHist [//] pts")
        as "(#frag & #physHistFrag & $)".
    { lia. }
    { iPureIntro. simpl.
      replace (t_t + offset - offset) with t_t by lia.
      apply lookup_zero_insert. }
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
        apply view_insert_le'; [done|lia].
      - simpl.
        etrans; first apply incl.
        apply incl2. }
    (* We are done updating ghost state. *)
    iModIntro.
    iSplit. { iPureIntro. simpl. solve_view_le. }

    iEval (rewrite monPred_at_wand) in "Φpost".
    iApply "Φpost".
    - iPureIntro. solve_view_le.
    - iExistsN.

      iSplitPure. { rewrite last_snoc. reflexivity. }
      iSplitPure. { eapply map_sequence_insert_snoc; done. }
      iSplitPure.
      { eapply map_sequence_insert_snoc; last done; first lia.
        eapply map_no_later_dom; last apply nolater.
        done. }
      iSplitPure.
      { eapply map_no_later_insert; last done. lia. }
      iSplitPure.
      { rewrite 2!dom_insert_L. rewrite absPhysHistDomEq. done. }
      iFrameF "isAtLoc".
      rewrite big_sepM_insert. 2: { apply nolater. lia. }
      rewrite big_sepM_insert.
      2: {
        eapply map_dom_eq_lookup_None; first done.
        apply nolater. lia. }
      iFrameF "locationProtocol".
      iSplitPure.
      { apply: increasing_map_insert_last; done. }
      iSplit. { iFrame "frag absHist". }
      iFrame "offset".
      (* iSplit. *)
      (* { iExists _. *)
      (*   iSplitPure; first done. *)
      (*   iApply (big_sepM_lookup with "frags"). done. } *)
      iSplit; last first.
      { simpl. iPureIntro.
        rewrite lookup_zero_insert.
        lia. }
      simpl.
      (* rewrite -assoc. *)

      iSplit.
      { iFrame "physHistFrag". solve_view_le. }
      (* iEval (rewrite -monPred_at_big_sepM) in "physHist". *)
      iApply monPred_mono; last iApply "physHist".
      etrans; first apply incl.
      etrans; first apply incl2.
      repeat split; solve_view_le.
  Qed.
*)

  (* Rule for store on an atomic. *)
  Lemma wp_store_at_strong R Q ℓ ss s_i s_t v_t (prot : LocationProtocol ST) st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗
      (* [s_l] is the state of the store that ours end up just after in the
      history. *)
      (∀ s_l v_l, ⌜ s_i ⊑ s_l ⌝ -∗ ∃ s_t,
        (* The state we picked fits in the history. *)
        (∀ v_i s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗
          prot.(pred) s_i v_i -∗
          prot.(pred) s_l v_l -∗
          prot.(pred) s_n v_n -∗
          ⌜ s_l ⊑ s_t ⌝ ∗ ⌜ s_t ⊑ s_n ⌝) ∧
        (* Extract from the location we load. *)
        (<obj> (prot.(pred) s_l v_l -∗ prot.(pred) s_l v_l ∗ R s_l)) ∗
        (* Establish the invariant for the value we store. *)
        (R s_l -∗ prot.(pred) s_t v_t ∗ Q s_t))
    }}}
      #ℓ <-_AT v_t @ st; E
    {{{ RET #(); store_lb ℓ prot s_t ∗ Q s_t }}}.
  Proof.
  Abort.

  (** [Q1] is the resource we want to extract in case of success and and [Q2] is
  the resource we want to extract in case of failure. *)
  Lemma wp_cmpxchg_at Q1 Q2 Q3 ℓ prot ss s_i (v_i : val) v_t R s_t st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗
      (∀ s_l v_l, ⌜ s_i ⊑ s_l ⌝ -∗
        ((▷ prot.(pred) s_l v_l) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (((* in case of success *)
          (* The state we write fits in the history. *)
          ⌜ s_l ⊑ s_t ⌝ ∗
          (∀ s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ prot.(pred) s_l v_l -∗
            prot.(pred) s_n v_n -∗ ⌜ s_t ⊑ s_n ⌝) ∗
          (* Extract from the location we load. *)
          (<obj> (prot.(pred) s_l v_l -∗ prot.(pred) s_l v_l ∗ R s_l)) ∗
          (* Establish the invariant for the value we store. *)
          (R s_l -∗ prot.(pred) s_t v_t ∗ Q1 s_l))
        ∧ (* in case of failure *)
          ((<obj> (prot.(pred) s_l v_l -∗ prot.(pred) s_l v_l ∗ Q2 s_l)) ∗ Q3)
        ))
    }}}
      CmpXchg #ℓ v_i v_t @ st; E
    {{{ v b s_l, RET (v, #b);
      (⌜ b = true ⌝ ∗ <fence> Q1 s_l ∗ ℓ ↦_AT^{prot} ((ss ++ [s_i]) ++ [s_t])) ∨
      (⌜ b = false ⌝ ∗ ⌜ s_i ⊑ s_l ⌝ ∗ ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗ <fence> (Q2 s_l) ∗ Q3)
    }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "(pts & impl)".

    iDestruct "pts" as (abs_hist phys_hist tLo t_i offset s' ms) "H". iNamed "H".
    iDestruct "tSLe" as %tSLe.

    (* We unfold the WP. *)
    iIntros ([TV' ?] [incl [= <-]]) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
    iApply wp_extra_state_interp. { done. }
    { apply prim_step_cmpxchg_no_fork. }

    iIntros "interp".
   Admitted.
  (*
    iDestruct (interp_get_at_loc with "interp isAtLoc locationProtocol offset")
      as (physHists physHist absHist pred) "(R & reins)".
    iNamed "R".

    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    assert (abs_hist !! t_i = Some s_i).
    { eapply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      apply slice. }

    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.
    iDestruct (history_full_entry_frag_lookup with "fullHist hist")
      as %(enc & lookTS & decodeEnc).

    iApply (wp_cmpxchg with "[#] [$pts $val]").
    { iIntros (t_l [vM SVm PVm BVm] leT physHistLook).

      assert (t_i - offset ≤ t_l) as le.
      { etrans; first done. etrans; last done. f_equiv. solve_view_le. }
      assert (t_i ≤ t_l + offset) as ?le by lia.
      rewrite drop_prefix_lookup in physHistLook.

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
      assert (t_i - offset ≤ t_l) as lte.
      { etrans; first done. etrans; last done. f_equiv. solve_view_le. }
      assert (t_i ≤ t_l + offset) as ? by lia.
      rewrite drop_prefix_lookup in H2.
      rewrite drop_prefix_lookup in H3.

      eassert _ as  temp. { eapply read_atomic_location; done. }
      destruct temp as (s_l & encSL & absHistLook & ? & ? & <- & orderRelated).

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
        ⌜increasing_map (encode_relation sqsubseteq) (<[(t_l + offset + 1)%nat := encode s_t]> absHist)⌝
      )%I as %incri.
      {
        iApply (bi.pure_mono).
        { apply
            (increasing_map_insert_succ _ _ _ _ (encode s_t) increasing
                                          absHistLook).
          eapply encode_relation_decode_iff; eauto using decode_encode. }
        iIntros (t_c e_c ? ?).

        assert (is_Some (physHist !! t_c)) as [[v_c cSV cFV ?] look2].
        { rewrite -elem_of_dom domEq elem_of_dom. done. }

        eassert _ as  temp. { eapply (read_atomic_location_no_inv (t_l + offset) t_c); try done || lia. }
        destruct temp as (s_c & encSC & ? & decodeS' & orderRelated2).
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
      rewrite (insert_id physHist); last done.
      rewrite (insert_id absHist); last done.

      rewrite drop_prefix_insert.
      assert (t_l + 1 + offset = t_l + offset + 1) as eq by lia.
      rewrite eq in H3. rewrite eq.
      iMod ("reins" $! (t_l + offset + 1) s_t
        with "[%] [//] [//] [] [] physHists [HI predMap] fullHist [//] pts")
          as "(#frag & #physHistFrag & $)".
      { lia. }
      { iPureIntro. simpl. rewrite lookup_zero_insert. lia. }
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
      iExists _, _, _, (t_l + offset + 1). iExistsN.
      iSplitPure. { rewrite last_snoc. reflexivity. }
      iSplitPure. { eapply map_sequence_insert_snoc; try done. lia. }
      iSplitPure.
      { eapply map_sequence_insert_snoc; last done; first lia.
        eapply map_no_later_dom; last apply nolater.
        done. }

      iSplitPure.
      { eapply map_no_later_insert; last done. lia. }
      iSplitPure.
      { rewrite 2!dom_insert_L. rewrite absPhysHistDomEq. done. }
      iFrameF "isAtLoc".
      rewrite big_sepM_insert. 2: { apply nolater. lia. }
      rewrite big_sepM_insert.
      2: {
        eapply map_dom_eq_lookup_None; first done.
        apply nolater. lia. }
      iFrameF "locationProtocol".
      iSplitPure.
      { apply: increasing_map_insert_last; try done. lia.
        etrans; done. }
      iSplit. { iFrame "frag absHist". }
      iFrame "offset".
      iSplit; last first.
      { simpl. iPureIntro.
        rewrite lookup_zero_insert.
        lia. }
      simpl.

      iSplit.
      { iFrame "physHistFrag". solve_view_le. }
      iApply monPred_mono; last iApply "physHist".
      etrans; first apply incl.
      etrans; first apply incl2.
      repeat split; solve_view_le.

    - (* failure *)
      iDestruct "reins" as "[_ reins]".
      iModIntro.

      (* The loaded timestamp is greater or equal to the one we know of. *)
      assert (t_i - offset ≤ t_l) as lte.
      { etrans; first done. etrans; last done. f_equiv. solve_view_le. }
      assert (t_i ≤ t_l + offset) as ? by lia.

      rewrite drop_prefix_lookup in H2.
      rewrite drop_prefix_lookup in H3.
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

      iDestruct ("reins" with "[$] [$] [$] [$]") as "$".

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
      iSplit.
      { (* We show what is, essentially, the points-to predicate that we started with. *)
        iExistsN.
        iFrameF (lastEq).
        iFrameF (slice).
        iFrameF (slicePhys).
        iFrameF (nolater).
        iFrameF (absPhysHistDomEq).
        iFrameF "isAtLoc".
        iFrameF "locationProtocol".
        iSplitPure; first done.

        iFrameF "absHist".
        iSplit.
        { iApply monPred_mono; last iApply "physHist".
          etrans; first apply incl.
          etrans; first apply incl2.
          solve_view_le. }
        iFrameF "offset".
        iPureIntro.
        etrans; first apply tSLe.
        f_equiv.
        solve_view_le. }
      iSplitL "Q2"; iApply monPred_mono; try iFrame.
      { repeat split; eauto using view_le_r, view_empty_least.
        rewrite assoc. apply view_le_r. }
      { etrans; first done. etrans; first done. repeat split; auto using view_le_l. }
  Qed.
*)

  (** [Q1] is the resource we want to extract in case of success and and [Q2] is
  the resource we want to extract in case of failure. *)
  Lemma wp_cas_at Q1 Q2 Q3 ℓ prot ss s_i (v_i v_t : val) R s_t st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗
      (∀ s_l v_l, ⌜ s_i ⊑ s_l ⌝ -∗
        ((▷ prot.(pred) s_l v_l) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (((* in case of success *)
          (* The state we write fits in the history. *)
          ⌜ s_l ⊑ s_t ⌝ ∗
          (∀ s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ prot.(pred) s_l v_l -∗
            prot.(pred) s_n v_n -∗ ⌜ s_t ⊑ s_n ⌝) ∗
          (* Extract from the location we load. *)
          (<obj> (prot.(pred) s_l v_l -∗ prot.(pred) s_l v_l ∗ R s_l)) ∗
          (* Establish the invariant for the value we store. *)
          (R s_l -∗ prot.(pred) s_t v_t ∗ Q1 s_l))
        ∧ (* in case of failure *)
          ((<obj> (prot.(pred) s_l v_l -∗ prot.(pred) s_l v_l ∗ Q2 s_l)) ∗ Q3)
        ))
    }}}
      CAS #ℓ v_i v_t @ st; E
    {{{ b s_l, RET #b;
      (⌜ b = true ⌝ ∗ <fence> Q1 s_l ∗ ℓ ↦_AT^{prot} ((ss ++ [s_i]) ++ [s_t])) ∨
      (⌜ b = false ⌝ ∗ ⌜ s_i ⊑ s_l ⌝ ∗ ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗ <fence> (Q2 s_l) ∗ Q3)
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

