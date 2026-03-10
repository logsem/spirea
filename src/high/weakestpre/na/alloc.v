From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice ipm_tactics.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import wrappers monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state increasing_map.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_na.
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).

  Lemma wp_alloc_na v s prot `{!ProtocolConditions prot} st E :
    {{{ prot.(p_full) s v ∗ prot.(p_pers) s v }}}
      ref_NA v @ st; E
    {{{ ℓ, RET #ℓ; ℓ ↦_{prot} ([] ++ [s]) }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "[predFull predPers]" (TV' incl) "Φpost".

    (* Unfold the wp *)
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_ref_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.
    
    iApply (wp_alloc (extra := {| extra_state_interp := True |})); first done.
    iNext.
    iIntros (ℓ CV') "(crashedAt' & % & % & pts)".
    simpl.
    iFrame "val".
    
    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { assert (is_Some (offsets !! ℓ)) as (? & ?).
      { apply elem_of_dom. rewrite -offsetsDom. apply elem_of_dom. done. }
      iDestruct (big_sepM_lookup with "ptsMap") as "pts'".
      { naive_solver. }
      iDestruct (fmapsto_valid_2 with "pts pts'") as (?) "_".
      done. }
    iDestruct (big_sepM2_dom with "predsFullReadHold") as %domEq.
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq2.
    iDestruct (big_sepM2_dom with "bumpMono") as %domEq4.
    assert (offsets !! ℓ = None) as offsetsLook.
    { apply not_elem_of_dom. rewrite -offsetsDom. apply not_elem_of_dom. done. }
    assert (abs_hists !! ℓ = None) as absHistsLook.
    { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom.
      assumption. }
    assert (ℓ ∉ dom abs_hists) as absHistsDomElem.
    { apply not_elem_of_dom. done. }

    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ ℓ ∉ dom OCV ⌝)%I with "[crashedAt']" as (OCV) "[#crashed_at %domOCV]".
    { iNamed "crashedAt'".
      iExists _.
      iSplit; first by iExists _.
      rewrite -(view_sub_dom_eq _ OV).
      by simplify_eq. }
    
    (* We update ghost state. *)

    (* Update ghost state for physical history. *)
    iMod (auth_map_map_insert_top with "physHists") as "[physHists ownPhysHist]".
    { done. }

    (* Add the predicate to the ghost state of predicates. *)
    iMod (own_all_preds_insert with "full_predicates") as "[full_predicates knowFullPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (own_all_preds_insert with "read_predicates") as "[read_predicates knowReadPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (own_all_preds_insert with "pers_predicates") as "[pers_predicates knowPersPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    (* add offset to offsets *)
    iMod (offset_auth_insert with "crashed_at offsets") as "[offsets #offset]".
    { done. } { apply not_elem_of_dom. done. }

    (* Allocate the abstract history for the location. *)
    iMod (own_all_bumpers_insert _ _ _ (prot.(p_bumper)) with "allBumpers")
      as "[allBumpers #knowBumper]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (full_map_insert _ _ _ _ _ {[0 := encode s]} with "crashedRely [knowBumper] history")
      as "(history & ownHist & #fragHist)".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    { iDestruct "knowBumper" as "[? $]". }
    iEval (rewrite big_sepM_singleton) in "fragHist".

    (* Add the preorder to the ghost state of bumper. *)
    iMod (ghost_map_insert_persist with "allOrders") as "[allOrders #knowOrder]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite /relation2. congruence. }

    assert (ℓ ∉ at_locs).
    { set_solver+ locsDisjoint histDomLocs absHistsDomElem. }
    assert (ℓ ∉ na_locs).
    { set_solver+ locsDisjoint histDomLocs absHistsDomElem. }

    (* Add the allocated location to the set of non-atomic locations. *)
    iMod (gen_alocs_update _ ℓ with "naLocs") as "[naLocs #fragExclusiveLoc]".
    
    (* Insert in na views *)
    iMod (ghost_map_insert _ SV with "naView") as "[naView ownNaView]".
    { rewrite -not_elem_of_dom. rewrite naViewsDom. done. }
      (* set_solver. *)
      (* setoid_rewrite <- not_elem_of_dom in physHistsLook. *)
      (* eapply not_elem_of_weaken; first apply physHistsLook. *)
      (* rewrite domEq. set_solver. } *)

    iModIntro.
    rewrite -assoc. iSplit; first done.
    iSplitL "Φpost knowFullPred knowReadPred knowPersPred knowBumper knowOrder ownHist ownNaView ownPhysHist".
    { setoid_rewrite monPred_at_wand.
      iApply "Φpost"; first done.
      rewrite /mapsto_na.
      iExists _, _, _, _, _, (Msg v ∅ ∅ PV), _.
      iSplitPure; first done.
      simpl.
      iSplit.
      { iFrame "knowFullPred knowReadPred knowPersPred knowOrder knowBumper". }
      iFrame "fragExclusiveLoc".
      repeat iExists _.
      rewrite -map_fmap_singleton. iFrame "ownHist".
      (* FIXME: don't hack *)
      Transparent know_na_view.
      rewrite /know_na_view.
      Opaque know_na_view.
      iFrame "ownNaView".
      iFrame "ownPhysHist".
      iFrame "offset".
      simpl.
      iSplitPure; first apply increasing_map_singleton.
      iSplitPure; first apply lookup_singleton.
      iSplitPure; first apply map_no_later_singleton.
      iSplit.
      { iExists _.
        iFrame "fragHist".
        rewrite decode_encode. done. }
      iSplitPure; first (split; [apply lookup_singleton | reflexivity]).
      iSplitPure; first repeat split; auto using view_empty_least.
      iSplitPure; first lia.
      iSplitPure; first lia.
      iRight. done. }
    iExistsN.
    iSplitL "ptsMap pts".
    { iDestruct (big_sepM_insert with "[pts $ptsMap]") as "$"; done. }
    iFrameNamedF.
    iSplitPure; first set_solver.
    iFrameNamedF.
    iFrame "full_predicates read_predicates pers_predicates allOrders naLocs atLocs".
    (* I couldn't figure out how to use [comm] typeclass. *)
    replace (na_locs ∪ {[ ℓ ]}) with ({[ ℓ ]} ∪ na_locs); last set_solver.
    
    (* historyFragments *)
    iSplit.
    { iApply (big_sepM_insert_2 with "[] historyFragments");
      simpl; rewrite big_sepM_singleton; iFrame "fragHist". }
    (* locsDisjoint *)

    iSplitPure. {
      assert (ℓ ∉ dom abs_hists).
      { rewrite -domEq. apply not_elem_of_dom. done. }
      set_solver. }
    (* histDomLocs *)
    iSplitPure. { rewrite dom_insert_L. set_solver+ histDomLocs. }
    (* naViewsDom *)
    iSplitPure. { setoid_rewrite dom_insert_L; last apply SV. f_equal. done. }
    iFrame "naView".
    (* mapShared *)
    iSplitPure.
    { rewrite -map_insert_zip_with (restrict_insert_not_elem ℓ at_locs) //. }
    iSplitL "atLocsHistories".
    { rewrite (restrict_insert_not_elem ℓ at_locs) //. }
    (* "ordered" *)
    iSplit.
    { iApply (big_sepM2_insert_2); last done.
      iPureIntro. apply increasing_map_singleton. }
    (* histPViewDoms *)
    iSplitPure.
    { rewrite dom_insert.
      apply union_subseteq_r', histPViewDoms. }
    (* predsFullHold *)
    iSplitL "predsFullReadHold predFull".
    { iApply (big_sepM2_insert with "[predFull predsFullReadHold]").
      { done. } { done. }
      iSplitL "predFull".
      - iExistsN. rewrite ?lookup_insert.
        iSplitPure; first done.
        iSplitPure; first done.
        iSplitPure; first done.
        rewrite /initial_history.
        rewrite big_sepM2_singleton /=.
        simpl.
        rewrite lookup_singleton_ne; last done.
        destruct (decide _) as [ | contra ].
        + destruct (TV) as [[??]?].
          iPoseProof (into_no_buffer_at with "predFull") as "predFull".
          iApply (predicate_holds_phi_decode_2 with "[%] [predFull]").
          * apply decode_encode.
          * f_equal.
          * iApply (monPred_mono with "predFull").
            solve_view_le.
        + exfalso.
          by apply contra.
      - iApply (big_sepM2_impl with "predsFullReadHold").
        iIntros "!>" (ℓ' ????) "H".
        assert (ℓ ≠ ℓ') by congruence.
        iApply (encoded_full_read_predicates_hold_equiv with "H");
          try (rewrite lookup_insert_ne; last done);
          done. }
    (* predsPersHold *)
    iSplitL "predsPersHold predPers".
    { iApply (big_sepM2_insert with "[predPers predsPersHold]").
      { done. } { done. }
      iSplitL "predPers".
      - iExistsN. rewrite ?lookup_insert.
        iSplitPure; first done.
        iSplitPure; first done.
        iSplitPure; first apply lookup_singleton.
        iSplitPure; first done.
        iSplitPure.
        { rewrite /lookup_zero not_elem_of_dom_1 //. set_solver. }
        iSplitL "".
        { rewrite not_elem_of_dom_1 /= //. set_solver. }
        iPoseProof (objective_at with "predPers") as "predPers".
        iApply (predicate_holds_phi_decode_2 with "[//] predPers").
        apply decode_encode.
      - iApply (big_sepM2_impl with "predsPersHold").
        iIntros "!>" (ℓ' ????) "H".
        assert (ℓ ≠ ℓ') by congruence.
        iApply (encoded_pers_predicate_holds_equiv with "H");
          try (rewrite lookup_insert_ne; last done);
          done. }
    iFrame "allBumpers".
    (* bumpMono *)
    iSplit.
    { iApply (big_sepM2_insert_2 with "[] bumpMono").
      iPureIntro. simpl.
      apply encode_bumper_bump_mono. apply bumper_mono. }
    (* bumper = three domains *)
    iSplitPure; first set_solver.
    iSplitPure; first set_solver.
    iSplitPure; first set_solver.
    (* [full_nextgen] *)
    iSplit. {
      iApply (big_sepM2_insert_2 with "[]").
      - iExists _, _, _.
        rewrite ?lookup_insert.
        do 3 (iSplitPure; first done).
        iApply (plainly_intro emp); last done.
        iIntros (_ ?????) "%HorderPF (%P_pers & #eqPers & persHolds) (%P_full & #eqFull & fullHolds)".
        iDestruct (encode_predicate_decode with "eqPers") as (σ_p) "%Hdecodeσ_p".
        iDestruct (encode_predicate_decode with "eqFull") as (σ_f) "%Hdecodeσ_f".
        iPoseProof (encode_predicate_extract with "eqPers persHolds") as "predPers".
        { done. }
        iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
        { done. }
        iDestruct ((pred_full_nextgen) $! MsgV_f σ_p v_p σ_f v_f) as "impl".
        iEval (rewrite ?monPred_wand_force) in "impl".
        iDestruct ("impl" with "[%] [predPers] predFull") as "NGF".
        { destruct HorderPF; last by simplify_eq.
          eapply encode_relation_decode_iff_1; done. }
        { iApply (objective_at with "predPers"). }
        iSplit.
        + iDestruct "NGF" as "[>NGF _]".
          iIntros (?) "%bumperEq".
          apply encode_bumper_Some_decode in bumperEq.
          destruct bumperEq as (σ_f' & bumperEq & bumperEq').
          simplify_eq.
          iEval (rewrite /encode_predicate).
          rewrite decode_encode.
          iModIntro.
          iExists _, _.
          iSplit. { iPureIntro. simpl. reflexivity. }
          iSplit. { iPureIntro. simpl. reflexivity. }
          iAssumption.
        + iIntros (???? bumperEq HorderPC HorderCF) "(%P_read & #eqRead & readHolds)".
          iDestruct "NGF" as "[_ NGF]".
          (* we need to instantiate the universal, but we cannot find the *)
          (* instance for [s_c], because we don't know whether [decode e_c] *)
          (* yields anything, not until after we instantiate [s_c]. but we can *)
          (* get around it by case distinction. *)
          destruct (@decode ST _ _ encσ_c) as [ σ_c | ] eqn:Heqn.
          * iPoseProof (encode_predicate_extract with "eqRead readHolds") as "predRead".
            { done. }
            iDestruct ("NGF" $! σ_c v_c) as "NGF".
            iEval (rewrite monPred_at_objectively) in "NGF".
            iMod ("NGF" with "predRead [%] [%]") as "NGF".
            { destruct HorderPC; last by simplify_eq.
              eapply encode_relation_decode_iff_1; done. }
            { eapply encode_relation_decode_iff_1; done. }
            iModIntro.
            apply encode_bumper_Some_decode in bumperEq.
            destruct bumperEq as (σ_c' & bumperEq & bumperEq').
            simplify_eq.
            iEval (rewrite /encode_predicate).
            rewrite decode_encode.
            iExists _, _.
            iSplit. { iPureIntro. simpl. reflexivity. }
            iSplit. { iPureIntro. simpl. reflexivity. }
            iAssumption.
          * (* this is the spurious case, we will see that once we get hold of *)
            (* [encode_bumper], we will just feed some random [ST] *)
            apply encode_bumper_Some_decode in bumperEq.
            destruct bumperEq as (s3' & bumperEq & bumperEq').
            rewrite Heqn in bumperEq.
            discriminate.
      - iApply (big_sepM2_impl with "predFullNextgen").
        iIntros "!> %ℓ' %order %bumper %orderLook %bumperLook
                 (%pred_full & %pred_read & %pred_pers &
                  %predFullLook & %predReadLook & %predPersLook & PostCrash)".
        iExists pred_full, pred_read, pred_pers.
        assert (ℓ' ∈ dom abs_hists). {
          apply elem_of_dom_2 in bumperLook.
          congruence.
        }
        assert (ℓ ≠ ℓ') by congruence.
        do ? (rewrite lookup_insert_ne; last done).
        do 3 (iSplitPure; first done).
        iApply "PostCrash".
    }
    (* [read_nextgen] *)
    iSplit. {
      iApply (big_sepM2_insert_2 with "[] predReadNextgen").
      iIntros (????) "%bumperEq".
      iApply (plainly_intro emp); last done.
      iIntros "_ (%Pread & #eqRead & ReadHolds)".
      apply encode_bumper_Some_decode in bumperEq.
      destruct bumperEq as (s3 & bumperEq & bumperEq').
      iEval (rewrite /encode_predicate).
      rewrite -bumperEq'.
      rewrite decode_encode.
      iExists _.
      iSplit. { iPureIntro. simpl. reflexivity. }
      iPoseProof (encode_predicate_extract with "eqRead ReadHolds") as "predRead".
      { done. }
      iPoseProof (pred_read_nextgen with "predRead") as "nextgen".
      iApply "nextgen". }
    (* [full_read_split] *)
    iSplit. {
      iApply (big_sepM2_insert_2 with "[] predFullReadSplit").
      iIntros (???).
      iApply (plainly_intro emp); last done.
      iIntros "_ (%P_full & #eqFull & fullHolds)".
      iDestruct (encode_predicate_decode with "eqFull") as (s4) "%s4DecodeEq".
      iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
      { done. }
      iPoseProof (full_read_split with "predFull") as "[predRead _]".
      iExists _.
      iEval (rewrite /encode_predicate s4DecodeEq).
      iSplit; done.
    }
    (* bumperBumpToValid *)
    iSplitPure.
    { rewrite map_Forall_insert.
      2: { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
      split; last done.
      apply encode_bumper_bump_to_valid. }
    (* bumperSome *)
    iApply (big_sepM2_insert_2 with "[] bumperSome").
    iPureIntro.
    apply map_Forall_singleton.
    rewrite encode_bumper_encode.
    done.
    (* For some reason, during proof the [ProtocolConditoins prot] can not be found? *)
    Unshelve. all: done.
  Qed.
End wp_na.
