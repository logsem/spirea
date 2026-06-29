From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice ipm_tactics.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.resources Require Import
  gen_ghost_map gen_ghost_map_map gen_alocs gen_predicates auth_map_map.
From self.high.lib Require Import abstract_state increasing_map.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_at_alloc.
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).

  (** * Shared points-to predicate *)
  #[local] Existing Instance nvmHighGS_inG.
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
    gen_alocs_auth γ atLocs -∗
    gen_alocs_frag γ {[ ℓ ]} -∗
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
  
  Lemma interp_insert_loc_at ℓ OCV prot `{!ProtocolConditions prot} s SV PV BV v :
    ℓ ∉ dom OCV →
    SV !!0 ℓ = 0 →
    crashed_at_offset OCV -∗
    interp -∗
    p_full prot s v (SV, PV, BV) -∗
    p_pers prot s v (SV, PV, BV) -∗
    (* persisted {[ ℓ := MaxNat 0 ]} -∗ *)
    ℓ ↦fh initial_history AT SV PV v ==∗
    (ℓ ↦_AT^{prot} [s]) (SV, PV, BV) ∗ interp.
  Proof.
    iIntros (domOCV svLook) "crashed_at".
    iNamed 1.
    iIntros "predFull predPers pts".
    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
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

    (** We update ghost state. **)
    (* add offset to offsets *)
    iMod (offset_auth_insert with "crashed_at offsets") as "[offsets #offset]".
    { done. } { apply not_elem_of_dom. done. }
    (* Allocate new physical history for the location. *)
    (* Definition initial_history (a : memory_access) SV FV v : history := *)
    (*   {[0 := Msg v (view_access a SV) (view_access a FV) FV]}. *)
    iMod (auth_map_map_insert_top _ _ _ _ 0 (Msg v (view_access AT SV) (view_access AT PV) PV) with "physHists") as "[physHists #physHistFrag]".
    { done. }

    (* Add the predicate for the location. *)
    iMod (own_all_preds_insert _ _ _ prot.(p_full) with "full_predicates") as "[full_predicates knowFullPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      congruence. }
    iMod (own_all_preds_insert _ _ _ prot.(p_read) with "read_predicates") as "[read_predicates knowReadPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      congruence. }
    iMod (own_all_preds_insert _ _ _ prot.(p_pers) with "pers_predicates") as "[pers_predicates knowPersPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      congruence. }
    
    (* Unlike Spirea 1.0, the abstract history now depends on knowing the bumper first. *)
    (* Add the bumper for the location. *)
    iMod (own_all_bumpers_insert _ _ (prot.(p_bumper)) with "allBumpers")
      as "[allBumpers #knowBumper]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    (* Allocate the abstract history for the location. *)
    iMod (full_map_insert _ _ _ _ _ {[0 := encode s]} with "crashedRely [knowBumper] history")
      as "(history & ownHist & #fragHist)".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    { iDestruct "knowBumper" as "[? $]". }
    iEval (rewrite big_sepM_singleton) in "fragHist".

    (* Add the preorder for the location. (I don't know what) *)
    iMod (ghost_map_insert_persist with "allOrders") as "[allOrders #knowOrder]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite /relation2. congruence. }

    (* Add the allocated location to the set of atomic locations. *)
    iMod (gen_alocs_update _ ℓ with "atLocs") as "[atLocs #isAtLoc]".

    iAssert  (know_protocol ℓ prot)%I as "#prot".
    { rewrite /know_protocol.
      iFrame "knowFullPred knowReadPred knowPersPred knowBumper knowOrder". }

    iModIntro.
    iSplitL "knowFullPred knowReadPred knowPersPred knowBumper".
    { rewrite /mapsto_at.
      iExists _, {[ 0 := (Msg v SV PV PV) ]}, 0, 0, 0, s, _.
      iSplitPure; first done.
      iSplitPure; first apply map_extra.map_sequence_singleton.
      iSplitPure; first apply map_sequence_singleton.
      iSplitPure. { apply map_no_later_singleton. }
      iSplitPure. { set_solver+. }
      iSplit; first iAssumption.
      iSplit; first iAssumption.
      iSplitPure. { apply increasing_map_singleton. }
      iEval (rewrite 2!big_sepM_singleton).
      iDestruct (know_frag_history_loc_decode with "fragHist") as "$".
      iFrame "physHistFrag".
      simpl.
      iSplitPure; first done.
      iSplitL; last (iPureIntro; lia).
      done. }
    iExistsN.
    iSplitL "ptsMap pts".
    { iDestruct (big_sepM_insert with "[pts $ptsMap]") as "$"; done. }
    iFrameNamedF.
    (* [oldViewsDiscarded] *)
    iSplit.
    { rewrite big_sepM2_insert; try done.
      iFrame "#".
      iPureIntro.
      lia. }
    
    iFrameNamedF.
    iFrame "full_predicates read_predicates pers_predicates allOrders naLocs atLocs".

    (* I couldn't figure out how to use [comm] typeclass. *)
    replace (at_locs ∪ {[ ℓ ]}) with ({[ ℓ ]} ∪ at_locs); last set_solver.
    
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
      simpl.
      rewrite drop_prefix_zero.
      rewrite map_Forall_singleton.
      done. }
    iSplitL "atLocsHistories ownHist".
    { rewrite restrict_insert_union big_sepM_insert.
      2: { apply restrict_lookup_None_lookup. assumption. }
      iFrame "ownHist atLocsHistories". }
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
      - iExistsN. rewrite ?lookup_insert_eq.
        iSplitPure; first done.
        iSplitPure; first done.
        iSplitPure; first done.
        rewrite /initial_history.
        rewrite big_sepM2_singleton /=.
        assert (na_views !! ℓ = None) as ->.
        { apply not_elem_of_dom in physHistsLook.
          apply not_elem_of_dom.
          rewrite naViewsDom.
          eapply not_elem_of_weaken; first apply physHistsLook.
          rewrite domEq histDomLocs.
          set_solver. }
        simpl.
        rewrite lookup_singleton_ne; last done.
        destruct (decide _) as [ | contra ].
        + iPoseProof (no_buffer.into_no_buffer_at with "predFull") as "predFull".
          iApply (predicate_holds_phi_decode_2 with "[] predFull"); first apply decode_encode.
          done.
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
      - iExistsN. rewrite ?lookup_insert_eq.
        iSplitPure; first done.
        iSplitPure; first done.
        iSplitPure; first apply lookup_singleton_eq.
        iSplitPure; first done.
        iSplitPure.
        { rewrite /lookup_zero not_elem_of_dom_1 //. set_solver. }
        iSplitL "".
        { rewrite not_elem_of_dom_1 /= //. set_solver. }
        iPoseProof (objective_at with "predPers") as "predPers".
        iApply (predicate_holds_phi_decode_2 with "[] predPers"); first apply decode_encode.
        done.
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
        rewrite ?lookup_insert_eq.
        do 3 (iSplitPure; first done).
        iApply (plainly_intro emp); last done.
        iIntros (_ ?????) "%HorderPF (%P_pers & #eqPers & persHolds) (%P_full & #eqFull & fullHolds)".
        iDestruct (encode_predicate_decode with "eqPers") as (σ_p) "%Hdecodeσ_p".
        iDestruct (encode_predicate_decode with "eqFull") as (σ_f) "%Hdecodeσ_f".
        iPoseProof (encode_predicate_extract with "eqPers persHolds") as "predPers".
        { done. }
        iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
        { done. }
        (* FIXME: why does typeclass resolution break here? *)
        iDestruct (pred_full_nextgen (prot := prot) $! MsgV_f σ_p v_p σ_f v_f) as "impl".
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

  Lemma wp_alloc_at v s prot `{!ProtocolConditions prot} st E :
    {{{ prot.(p_full) s v ∗ prot.(p_pers) s v }}}
      ref_AT v @ st; E
    {{{ ℓ, RET #ℓ; ℓ ↦_AT^{prot} [s] }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "[ϕ_full ϕ_pers]".
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
    iApply wp_extra_state_interp. { done. } { by apply prim_step_ref_no_fork. }
    iIntros "interp".
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
    destruct TV as [[??]?].
    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ ℓ ∉ dom OCV ⌝)%I with "[crashedAt']" as (OCV) "[#crashed_at %domOCV]".
    { iNamed "crashedAt'".
      iExists _.
      iSplit; first by iExists _.
      rewrite -(view_sub_dom_eq _ OV).
      by simplify_eq. }
    iMod (interp_insert_loc_at ℓ OCV prot _ _ _ BV with "crashed_at interp [ϕ_full] [ϕ_pers] pts")
      as "(pts & interp)"; [done | done | | | ].
    { iApply monPred_mono; last iApply "ϕ_full". solve_view_le. }
    { iApply monPred_mono; last iApply "ϕ_pers". solve_view_le. }
    iModIntro.
    rewrite -assoc. iSplit; first done.
    iFrame "interp".
    iSpecialize ("Φpost" $! ℓ).
    monPred_simpl. 
    iApply ("Φpost" with "[] pts").
    { done. }
  Qed.

  Context (prots: loc → LocationProtocol ST) `{∀ (ℓ: loc), ProtocolConditions (prots ℓ)}.

  Lemma wp_alloc_at_strong v s st E :
    {{{ ∀ ℓ, (prots ℓ).(p_full) s v ∗ (prots ℓ).(p_pers) s v }}}
      ref_AT v @ st; E
    {{{ ℓ, RET #ℓ; ℓ ↦_AT^{prots ℓ} [s] }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "ϕ".
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
    iApply wp_extra_state_interp. { done. } { by apply prim_step_ref_no_fork. }
    iIntros "interp".
    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.
    iApply (wp_alloc (extra := {| extra_state_interp := True |})); first done.
    iNext.
    iIntros (ℓ CV') "(crashedAt' & % & % & pts)".
    iDestruct ("ϕ" $! ℓ) as "[ϕ_full ϕ_pers]".
    simpl.
    iFrame "val".
    destruct TV as [[??]?].
    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ ℓ ∉ dom OCV ⌝)%I with "[crashedAt']" as (OCV) "[#crashed_at %domOCV]".
    { iNamed "crashedAt'".
      iExists _.
      iSplit; first by iExists _.
      rewrite -(view_sub_dom_eq _ OV).
      by simplify_eq. }
    iMod (interp_insert_loc_at ℓ OCV (prots ℓ) _ _ _ BV with "crashed_at interp [ϕ_full] [ϕ_pers] pts")
      as "(pts & interp)"; [done | done | | | ].
    { iApply monPred_mono; last iApply "ϕ_full". solve_view_le. }
    { iApply monPred_mono; last iApply "ϕ_pers". solve_view_le. }
    iModIntro.
    rewrite -assoc. iSplit; first done.
    iFrame "interp".
    iSpecialize ("Φpost" $! ℓ).
    monPred_simpl. 
    iApply ("Φpost" with "[] pts").
    { done. }
  Qed.
  
End wp_at_alloc.
