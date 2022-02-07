(* Weakest precondition rules for non-atomic locations. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self.algebra Require Import ghost_map.
From self Require Export extra ipm_tactics encode_relation view.
From self.lang Require Export lang lemmas tactics syntax.
From self.base Require Import primitive_laws.
From self.high Require Import dprop resources crash_weakestpre lifted_modalities
     monpred_simpl modalities locations protocol.
From self.high.modalities Require Import no_buffer.

Section wp_na_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (prot : LocationProtocol ST).

  Lemma wp_alloc_na v s prot st E :
    {{{ prot.(pred) s v _ }}}
      ref_NA v @ st; E
    {{{ ℓ, RET #ℓ; ℓ ↦_{prot} [s] }}}.
  Proof.
    intros Φ. iStartProof (iProp _). iIntros (TV). iIntros "phi".
    iIntros (TV' incl) "Φpost".

    (* Unfold the wp *)
    rewrite wp_eq /wp_def wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.

    iApply wp_extra_state_interp. { done. } { by apply prim_step_ref_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iApply (wp_alloc (extra := {| extra_state_interp := True |})); first done.
    iNext.
    iIntros (ℓ CV') "(crashedAt' & % & % & pts)".
    simpl.
    iFrame "val".

    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { iDestruct (big_sepM_lookup with "ptsMap") as "pts'"; first done.
      iDestruct (mapsto_valid_2 with "pts pts'") as (?) "_".
      done. }

    iDestruct (big_sepM2_dom with "predsHold") as %domEq.
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq2.
    iDestruct (big_sepM2_dom with "predPostCrash") as %domEq3.
    iDestruct (big_sepM2_dom with "bumpMono") as %domEq4.

    (* We update ghost state. *)

    (* Update ghost state for physical history. *)
    iMod (auth_map_map_insert_top with "physHist") as "[physHist ownPhysHist]".
    { done. }

    (* Add the predicate to the ghost state of predicates. *)
    iMod (own_all_preds_insert with "predicates") as "[predicates knowPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Allocate the abstract history for the location. *)
    iMod (own_full_history_history_insert_loc _ _ _ _ {[0 := encode s]} with "history")
      as "(history & ownHist & #fragHist)".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Add the bumper to the ghost state of bumper. *)
    iMod (own_all_bumpers_insert _ _ _ (prot.(bumper)) with "allBumpers") as "[allBumper knowBumper]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Add the preorder to the ghost state of bumper. *)
    iMod (ghost_map_insert_persist with "allOrders") as "[allOrders #knowOrder]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite /relation2. congruence. }

    assert (ℓ ∉ at_locs). {
      setoid_rewrite <- not_elem_of_dom in physHistsLook.
      eapply not_elem_of_weaken; first apply physHistsLook.
      rewrite domEq. set_solver. }
    assert (ℓ ∉ na_locs). {
      setoid_rewrite <- not_elem_of_dom in physHistsLook.
      eapply not_elem_of_weaken; first apply physHistsLook.
      rewrite domEq. set_solver. }

    (* Add the allocated location to the set of non-atomic locations. *)
    iMod (own_update with "naLocs") as "[naLocs fragExclusiveLoc]".
    { apply auth_update_alloc. apply gset_local_update.
      apply (union_subseteq_r {[ ℓ ]}). }
    iEval (rewrite -gset_op) in "fragExclusiveLoc".
    iDestruct "fragExclusiveLoc" as "[#isExclusive _]".
    (* Insert in na views *)
    iMod (ghost_map_insert _ SV with "naView") as "[naView ownNaView]".
    { rewrite -not_elem_of_dom.
      setoid_rewrite <- not_elem_of_dom in physHistsLook.
      eapply not_elem_of_weaken; first apply physHistsLook.
      rewrite domEq. set_solver. }

    iModIntro.
    rewrite -assoc. iSplit; first done.
    iSplitL "Φpost knowPred knowBumper knowOrder ownHist ownNaView ownPhysHist".
    { iApply "Φpost".
      iExists _, _, _, _, (Msg v ∅ ∅ PV).
      iFrame "knowPred knowOrder knowBumper isExclusive".
      repeat iExists _.
      rewrite -map_fmap_singleton. iFrame "ownHist".
      iFrame "ownNaView".
      iFrame "ownPhysHist".
      simpl.
      iSplitPure; first apply increasing_list_singleton.
      iSplitPure; first apply lookup_singleton.
      iSplitPure; first apply map_no_later_singleton.
      iSplitPure; first (split; [apply lookup_singleton | reflexivity]).
      iSplitPure; first repeat split; auto using view_empty_least.
      iSplitPure; first lia.
      iRight. done. }
    repeat iExists _.
    iFrame "physHist crashedAt history predicates allOrders naLocs
      atLocs".
    iFrame.
    iFrame "#".
    iFrame "%".
    (* We split up some of the big seps s.t. we can frame things away
    immediately. *)
    rewrite !big_sepM_insert; try done.
    rewrite !big_sepM2_insert;
      try (eapply map_dom_eq_lookup_None; last apply physHistsLook;
           rewrite /relation2; congruence).
    rewrite !(restrict_insert_not_elem _ _ _ _ H3).
    iFrame "pts ptsMap ordered bumperSome bumpMono".
    iFrame (mapShared).
    (* locsDisjoint *)
    iSplit. {
      iPureIntro.
      assert (ℓ ∉ dom (gset loc) abs_hists).
      { rewrite -domEq. apply not_elem_of_dom. done. }
      set_solver. }
    (* histDomLocs *)
    iSplit. { iPureIntro. rewrite dom_insert_L. set_solver. }
    (* naViewsDom *)
    iSplitPure. { rewrite dom_insert_L. rewrite naViewsDom. done. }
    iFrame "atLocsHistories".
    (* increasingMap *)
    iSplitPure; first apply increasing_map_singleton.
    (* predsHold *)
    iSplitL "predsHold phi".
    { iSplitL "phi".
      - iExists _. rewrite !lookup_insert.
        iSplit; first done.
        rewrite /initial_history.
        simpl.
        rewrite big_sepM2_singleton /=.
        simpl.
        iDestruct (predicate_holds_phi with "[]") as "HH".
        { done. }
        { done. }
        iApply "HH".
        destruct TV as [[??]?]. destruct TV' as [[??]?].
        iDestruct (into_no_buffer_at with "phi") as "phi".
        iApply (monPred_mono with "phi").
        repeat split; last done.
        * etrans; first apply incl. apply incl2.
        * etrans; first apply incl. apply incl2.
      - iApply (big_sepM2_impl with "predsHold").
        iModIntro. iIntros (ℓ' ????) "(%pred & %look & ?)".
        iExists (pred).
        assert (ℓ ≠ ℓ') by congruence.
        rewrite lookup_insert_ne; last done.
        rewrite lookup_insert_ne; last done.
        iSplit; first done.
        iFrame. }
    (* bumpMono *)
    iSplitL.
    { iPureIntro. simpl. apply encode_bumper_bump_mono. apply bumper_mono. }
    (* predPostCrash *)

    rewrite /post_crash_flush /post_crash. iFrame "predPostCrash".
    iSplitL.
    { iModIntro. iIntros (??????) "(%eq & %eq2 & P)".
      rewrite /encode_predicate.
      apply encode_bumper_Some_decode in eq.
      destruct eq as (s3 & eq' & eq2').
      rewrite -eq2'.
      rewrite decode_encode.
      iExists _.
      iSplit. { iPureIntro. simpl. reflexivity. }
      iDestruct (encode_predicate_extract with "P") as "phi".
      { done. } { done. }
      iApply (pred_condition with "phi"). }
    (* bumperSome *)
    iPureIntro.
    apply map_Forall_singleton.
    rewrite encode_bumper_encode.
    done.
  Qed.

  Lemma wp_load_na ℓ q ss s Q prot positive E :
    last ss = Some s →
    {{{ mapsto_na ℓ prot q ss ∗
        (<obj> (∀ v, prot.(pred) s v _ -∗ Q v ∗ prot.(pred) s v _)) }}}
      Load (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ v, RET v; mapsto_na ℓ prot q ss ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "(pts & pToQ)".
    (* rewrite /mapsto_na. simpl. *)
    (* iNamed "pts". *)
    rewrite /mapsto_na.
    iDestruct "pts" as (?tP ?tS SV absHist msg) "pts". iNamed "pts".
    iNamed "locationProtocol".
    iDestruct "inThreadView" as %inThreadView.
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV' PV] BV] incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. }
    { by apply prim_step_load_no_fork. }
    iNamed 1.
    iDestruct (own_all_preds_pred with "predicates knowPred") as
      (pred predsLook) "#predsEquiv".
    iDestruct (own_full_history_agree with "[$] [$]") as %absHistlook.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    clear predsLook'.

    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply (wp_load (extra := {| extra_state_interp := True |}) with "[$pts $val]").
    iNext. iIntros (tT v' msg') "[pts (%look & %msgVal & %gt)]".
    simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val".

    assert (SV ⊑ SV') as svInclSv'. (* This will come in handy. *)
    { destruct TV as [[??]?]. destruct TV' as [[??]?].
      etrans; first apply inThreadView.
      etrans; first apply incl; apply incl2. }

    (* We need to conclude that the only write we could read is [tS]. I.e., that
    [tT = tS]. *)
    assert (tS ≤ SV' !!0 ℓ) as tSle.
    { etrans; first done. f_equiv. done. }
    assert (tS ≤ tT) as lte.
    { etrans; first done. apply gt. }
    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    assert (is_Some (absHist !! tT)) as HI.
    { apply elem_of_dom.
      erewrite <- dom_fmap_L.
      erewrite <- domEq.
      apply elem_of_dom.
      naive_solver. }
    assert (tT = tS) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      pose proof (nolater tT lt) as eq.
      rewrite eq in HI. inversion HI as [? [=]]. }
    assert (absHist !! tS = Some s) as lookS.
    { rewrite -sLast.
      apply map_slice_lookup_hi in slice.
      rewrite slice.
      done. }
    clear lte HI.

    iDestruct (auth_map_map_lookup_agree with "[$] [$]") as %eq.
    { done. } { done. }
    subst.

    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      first done.
    { rewrite lookup_fmap. rewrite lookS. done. }
    iDestruct (ghost_map_lookup with "naView knowSV") as %->.
    simpl.
    iDestruct (predicate_holds_phi with "predsEquiv predHolds") as "phi";
      first done.
    rewrite monPred_at_objectively.
    iSpecialize ("pToQ" $! (SV, msg_persisted_after_view msg, ∅) (msg_val msg)).
    rewrite monPred_at_wand.
    iDestruct ("pToQ" with "[] phi") as "[Q phi]".
    { iPureIntro. reflexivity. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iApply (predicate_holds_phi with "predsEquiv phi"). done. }
    (* Reinsert into the map. *)
    iDestruct ("predsHold" with "[predMap]") as "predsHold". { naive_solver. }

    iSplitR "ptsMap physHist allOrders ordered predsHold history predicates
             atLocs naLocs crashedAt allBumpers bumpMono predPostCrash
             atLocsHistories naView"; last first.
    { repeat iExists _. iFrameNamed.
      rewrite /post_crash_flush /post_crash.
      iFrame "predPostCrash". done. }
    iSplit; first done.
    iApply "Φpost".
    iSplitR "Q".
    2: {
      simplify_eq.
      rewrite /msg_to_tv.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      - done.
      - destruct TV as [[??]?]. destruct TV' as [[??]?].
        etrans; first apply inThreadView.
        etrans; first apply incl.
        apply incl2.
      - apply view_empty_least. }
    iExists _, _, _, _, _.
    iFrameNamed.
    iSplit. { iFrame "knowPred knowPreorder knowBumper". }
    iPureIntro. etrans. eassumption. etrans. eassumption. eassumption.
  Qed.

  Lemma wp_store_na ℓ prot ss v s__last s st E :
    last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_na ℓ prot 1 ss ∗ prot.(pred) s v _ }}}
      #ℓ <- v @ st; E
    {{{ RET #(); mapsto_na ℓ prot 1 (ss ++ [s]) }}}.
  Proof.
    intros last stateGt Φ.
    iStartProof (iProp _). iIntros (TV).
    iIntros "(pts & phi)".
    rewrite /mapsto_na.
    iDestruct "pts" as (?tP ?tS SV absHist msg) "pts". iNamed "pts".
    iNamed "locationProtocol".
    iDestruct "inThreadView" as %inThreadView.

    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV' PV] BV] incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. } { by apply prim_step_store_no_fork. }
    iNamed 1.
    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    assert (SV ⊑ SV') as svInclSv'.
    { destruct TV as [[??]?]. destruct TV' as [[??]?].
      etrans; first apply inThreadView.
      etrans; first apply incl.
      apply incl2. }

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    iDestruct (ghost_map_lookup with "allOrders knowPreorder")
      as %ordersLook.

    iDestruct (own_full_history_agree with "history hist") as %absHistsLook.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.

    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook]
      by by eapply map_dom_eq_lookup_Some.
    iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]"; first done.

    iApply (wp_store (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (tT) "(%look & %gt & #valNew & pts)".
    simpl in gt.

    iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".

    iAssert (⌜ absHist !! tT = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
      { done. } { done. }
      iDestruct "predMap" as (pred' predsLook') "predMap".

      iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite -!not_elem_of_dom. rewrite domEq. rewrite dom_fmap. done. }

    iDestruct (
        location_sets_singleton_included with "naLocs isNaLoc"
      ) as %ℓEx.
    assert (ℓ ∉ at_locs) as ℓnotSh by set_solver.
    (* Update the ghost state for the abstract history. *)
    iMod (own_full_history_insert _ _ _ _ _ _ s with "history hist")
      as "(history & hist & histFrag)"; first done.

    (* Update ghost state. *)
    set (newMsg := Msg v ∅ ∅ PV).
    iMod (auth_map_map_insert _ _ _ _ _ newMsg with "physHist") as "[physHist #physHistFrag]".
    { done. } { done. }

    iDestruct (ghost_map_lookup with "naView knowSV") as %ℓnaView.

    iMod (ghost_map_update (<[ℓ:=MaxNat tT]>SV') with "naView knowSV") as "[naView knowSV]".
    (* iMod (ghost_map.ghost_map_update (SV ⊔ SV') with "naView knowSV") as "[naView knowSV]". *)

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
        repeat split; try done.
        apply view_insert_le. lia. }
      iExists _, _, _, _, _.
      iFrame "∗#".
      (* [incrList] *)
      iSplit. { iPureIntro. eapply increasing_list_snoc; eauto. }
      (* [lookupV] *)
      iSplit. { iPureIntro. by rewrite lookup_insert last_snoc. }
      (* [nolater] *)
      iSplit. {
        iPureIntro. eapply map_no_later_insert; last done.
        etrans; first apply haveTStore.
        apply Nat.lt_le_incl. eapply Nat.le_lt_trans; last apply gt.
        f_equiv.
        apply svInclSv'. }
      (* [slice] *)
      iSplit. {
        iPureIntro. eapply map_slice_insert_snoc; [|done|done].
        eapply Nat.le_lt_trans; last apply gt.
        etrans; first done.
        f_equiv.
        apply svInclSv'. }
      (* [inThreadView] *)
      iSplit. {
        iPureIntro. repeat split.
        - done.
          (* etrans. *)
          (* { apply view_lub_le; last reflexivity. done. } *)
          (* apply view_insert_le. *)
          (* lia. *)
        - done.
        - apply view_empty_least. }
      (* [haveTSore] *)
      iPureIntro. by rewrite lookup_zero_insert. }
    repeat iExists _.
    iFrame "history". iFrame "ptsMap". iFrame "#". iFrame"naView". iFrameNamed.
    rewrite /post_crash_flush /post_crash. iFrame "predPostCrash".
    iSplit. { iPureIntro. set_solver. }
    (* [naViewsDom] *)
    iSplit.
    { iPureIntro. rewrite dom_insert_lookup_L; naive_solver. }
    (* [mapShared] *)
    iSplit.
    { iPureIntro. setoid_rewrite restrict_insert_not_elem; done. }

    (* [atLocsHistories] *)
    iSplitL "atLocsHistories".
    { setoid_rewrite restrict_insert_not_elem. done. done. }

    iSplit.
    (* [ordered] *)
    { iApply (big_sepM2_update_left with "ordered"); eauto.
      iIntros (orderedForall).
      iPureIntro.
      rewrite fmap_insert.
      apply: increasing_map_insert_last.
      - eauto.
      - apply map_no_later_fmap. done.
      - eapply Nat.le_lt_trans; last apply gt.
        etrans; first apply haveTStore.
        f_equiv. done.
      - rewrite lookup_fmap. rewrite lookupV. rewrite last. done.
      - eapply encode_relation_decode_iff; eauto using decode_encode. }
    iSplit.
    (* [predsHold] *)
    { iApply (big_sepM2_update with "[predsHold]"); [done|done| |].
      { iApply (big_sepM2_impl with "predsHold").
        iIntros "!>" (ℓ' physHist' absHist' physHist2 absHist2).
        (* We consider two cases, either [ℓ] is the location where we've inserted
        an element or it is a different location. The latter case is trivial. *)
        destruct (decide (ℓ = ℓ')) as [<-|neq]; last first.
        { rewrite !lookup_insert_ne; naive_solver. }
        rewrite !lookup_insert.
        iDestruct 1 as (pred' predLook') "H".
        simplify_eq.
        assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
        clear predLook'.
        iExists _; iSplit; first done.
        iApply (big_sepM2_impl with "H").
        iIntros "!>" (?????).
        iApply encoded_predicate_holds_mono.
        repeat split; eauto.
        rewrite ℓnaView. simpl.
        etrans; first done.
        apply view_insert_le. lia. }
      iDestruct 1 as (pred' predLook') "H".
      simplify_eq.
      assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
      clear predLook'.
      iExists _; iSplit; first done.
      rewrite fmap_insert.
      iApply big_sepM2_insert.
      { done. } { rewrite lookup_fmap absHistLook. done. }
      simpl. iFrame.
      iApply predicate_holds_phi; auto.
      rewrite lookup_insert /=.
      destruct TV as [[??]?]. destruct TV' as [[??]?].
      iDestruct (into_no_buffer_at with "phi") as "phi".
      iApply (monPred_mono with "phi").
      repeat split; last done.
      - simpl. etrans; first apply incl. etrans; first apply incl2.
        apply view_insert_le. lia.
      - simpl. etrans; first apply incl. apply incl2. }
    (* [bumperSome] *)
    iApply (big_sepM2_update_left with "bumperSome"); eauto.
    iPureIntro. intros bumperSome.
    rewrite fmap_insert.
    apply map_Forall_insert_2; eauto.
    rewrite /encode_bumper decode_encode. done.
  Qed.

End wp_na_rules.
