From iris.proofmode Require Import ltac_tactics.
From iris.algebra Require Import auth.
From iris_named_props Require Import named_props.

From self Require Import ipm_tactics extra view_slice encode_relation.
From self.high.lib Require Import increasing_map.
From self.program_logic Require Import recovery_adequacy.
From self.base Require Import wpr_lifting primitive_laws generational_resources cred_frag.
From self.high Require Import
  crash_weakestpre recovery_weakestpre generational_resources state_interpretation protocol locations.
From self.high.modalities Require Import nextgen.
From self.nextgen Require Import nextgen_promises.

From self.high.resources Require Import
  gen_ghost_map gen_ghost_map_ofe gen_ghost_map_map gen_alocs gen_predicates auth_map_map.

Section adequacy_alloc.
  (* Turns [gmap loc val] to [gmap loc history] *)
  Definition initial_heap (σ : gmap loc val) : store :=
    (λ (v : val), {[ 0 := Msg v ∅ ∅ ∅ ]} : history ) <$> σ.

  Lemma valid_heap_initial_heap σ : valid_heap (initial_heap σ).
  Proof.
    rewrite /valid_heap.
    intros ℓ hist.
    rewrite /initial_heap. simpl.
    intros (v & <- & ?)%lookup_fmap_Some.
    split. { done. }
    intros ?? (<- & <-)%lookup_singleton_Some.
    simpl.
    apply view_le_lookup.
    done.
  Qed.

  (* Our protocol definition depends on [nvmHighGS], which we are going to build in
   * [init_state_alloc]. Thus I make [nvmHighGS] an explicit argument. *)
  Record LocInfo `{nvmBaseGS} {H: nvmHighGS Σ Ω} := MkLocInfo {
    li_ST: Type;
    li_ST_eqdec :: EqDecision li_ST;
    li_ST_countable :: Countable li_ST;
    li_ST_is_abstract :: AbstractState li_ST;
    li_prot: LocationProtocol li_ST;
    li_prot_conds :: ProtocolConditions li_prot;
    li_σ0: li_ST;
  }.
  Notation LocInfos H := (gmap loc (@LocInfo _ _ _ H)).

  (* The initial resources given to the user *)
  Definition init_at_assertions `{Hhigh: nvmHighGS}
    (σ: gmap loc val) (locinfos: LocInfos Hhigh): dProp Σ :=
    ([∗map] ℓ ↦ v; li ∈ σ; locinfos,
       persist_lb ℓ li.(li_prot) li.(li_σ0) ∗ ℓ ↦_AT^{li.(li_prot)} [li.(li_σ0)]).

  Definition init_na_assertions `{Hhigh: nvmHighGS}
    (σ: gmap loc val) (locinfos: LocInfos Hhigh): dProp Σ :=
    ([∗map] ℓ ↦ v; li ∈ σ; locinfos,
       persist_lb ℓ li.(li_prot) li.(li_σ0) ∗ ℓ ↦_{li.(li_prot)} [li.(li_σ0)]).

  (* The initial protocol predicates user needs to establish in return. *)

  Definition init_prots `{Hhigh: nvmHighGS}
    (σ: gmap loc val) (locinfos: LocInfos Hhigh): dProp Σ :=
    ([∗map] ℓ ↦ v; li ∈ σ; locinfos,
      li.(li_prot).(p_full) li.(li_σ0) v ∗ li.(li_prot).(p_pers) li.(li_σ0) v).

  #[local] Instance init_at_assertions_persistent `{Hhigh: nvmHighGS}
    (σ: gmap loc val) (locinfos: LocInfos Hhigh): Persistent (init_at_assertions σ locinfos).
  Proof.
    apply big_sepM2_persistent'.
    intros.
    apply bi.sep_persistent.
    - apply persist_lb_persistent.
    - apply mapsto_at_persistent.
  Qed.

  #[local] Existing Instance nvmHighGS_inG.

  Definition interp_pre `{nvmHighGS}
    (phys_hists : gmap loc (gmap time message))
    (abs_hists : gmap loc (gmap time positive))
    (global_pview : view.view)
    (predicates_full : gmap loc enc_predicate)
    (predicates_read : gmap loc enc_predicate)
    (predicates_pers : gmap loc enc_predicate)
    (orders : gmap loc (relation2 positive))
    (bumpers : gmap loc (positive → option positive))
    (na_locs : gset loc)
    (at_locs : gset loc)
    (offsets : gmap loc nat)
    (na_views : gmap loc view.view) : iProp Σ :=
    "ptsMap" ∷ ([∗ map] ℓ ↦ hist ∈ phys_hists, ℓ ↦fh hist) ∗
    "offsets" ∷ offset_auth offsets ∗
    "#crashedRely" ∷ (∃ OPV, rely_self crashed_at_name (crashed_at_pred OPV)) ∗
    "physHists" ∷ auth_map_map_auth histories_rel phy_history_name phys_hists ∗
    "#oldViewsDiscarded" ∷
      ([∗ map] ℓ ↦ hist;offset ∈ phys_hists;offsets,
         ⌜ ∀ t msg, t < offset → hist !! t = Some msg → discard_msg_views msg = msg ⌝) ∗
    "history" ∷ full_map bumpers_name abs_history_name (DfracOwn 1) abs_hists ∗
    "#historyFragments" ∷
      ([∗ map] ℓ ↦ abs_hist ∈ abs_hists,
         [∗ map] t ↦ encσ ∈ abs_hist, frag_entry bumpers_name abs_history_name ℓ t encσ) ∗
    "full_predicates" ∷ own_all_full_preds (DfracOwn 1) predicates_full ∗
    "read_predicates" ∷ own_all_read_preds (DfracOwn 1) predicates_read ∗
    "pers_predicates" ∷ own_all_pers_preds (DfracOwn 1) predicates_pers ∗
    "allOrders" ∷ own_all_preorders preorders_name orders ∗
    "%locsDisjoint" ∷ ⌜ na_locs ## at_locs ⌝ ∗
    "%histDomLocs" ∷ ⌜ dom abs_hists = na_locs ∪ at_locs ⌝ ∗
    "naLocs" ∷ gen_alocs_auth exclusive_locs_name na_locs ∗
    "atLocs" ∷ gen_alocs_auth shared_locs_name at_locs ∗
    "%naViewsDom" ∷ ⌜ dom na_views = na_locs ⌝ ∗
    "naView" ∷ ghost_map_auth non_atomic_views_gname drop_OCV_clear (DfracOwn 1) na_views ∗
    "%mapShared" ∷ ⌜ shared_locs_inv (restrict at_locs (map_zip_with drop_prefix phys_hists offsets)) ⌝ ∗
    "atLocsHistories" ∷
      ([∗ map] ℓ ↦ abs_hist ∈ (restrict at_locs abs_hists),
         know_full_encoded_history_loc ℓ 1 abs_hist) ∗
    "#ordered" ∷ ([∗ map] ℓ ↦ hist; order ∈ abs_hists; orders,
                    ⌜ increasing_map order hist ⌝) ∗
    "%histPViewDoms" ∷ ⌜ dom global_pview ⊆ dom abs_hists ⌝ ∗
    "allBumpers" ∷ own_all_bumpers bumpers_name bumpers ∗
    "#bumpMono" ∷ ([∗ map] ℓ ↦ order; bump ∈ orders; bumpers,
                     ∀ e1 e2 e1' e2', ⌜bump e1 = Some e1'⌝ → ⌜bump e2 = Some e2'⌝ →
                                      ⌜order e1 e2⌝ → ⌜order e1' e2'⌝) ∗
    "%FullBumperDoms" ∷
      ⌜ dom predicates_full = dom bumpers ⌝ ∗
    "%ReadBumperDoms" ∷
      ⌜ dom predicates_read = dom bumpers ⌝ ∗
    "%PersBumperDoms" ∷
      ⌜ dom predicates_pers = dom bumpers ⌝ ∗
    "#predFullNextgen" ∷ ([∗ map] ℓ ↦ order; bump ∈ orders; bumpers,
                            ∃ encp_full encp_read encp_pers,
                              ⌜ predicates_full !! ℓ = Some encp_full ⌝ ∗
                              ⌜ predicates_read !! ℓ = Some encp_read ⌝ ∗
                              ⌜ predicates_pers !! ℓ = Some encp_pers ⌝ ∗
                              ■ (∀ encσ_p v_p encσ_f v_f MsgV_f,
                                   ⌜ order encσ_p encσ_f ∨ encσ_p = encσ_f ⌝ -∗
                                   encoded_predicate_holds encp_pers encσ_p v_p (∅, ∅, ∅) -∗
                                   encoded_predicate_holds encp_full encσ_f v_f MsgV_f -∗
                                   (∀ encσ_f',
                                      ⌜ bump encσ_f = Some encσ_f' ⌝ ==∗
                                      ∃ P_full' P_pers',
                                        encp_full encσ_f' v_f ≡ Some P_full' ∗ encp_pers encσ_f' v_f ≡ Some P_pers' ∗
                                        (nextgen_flush (P_full' ∗ P_pers': dPropO Σ)) MsgV_f) ∧
                                   (∀ encσ_c encσ_c' v_c MsgV_c,
                                      ⌜ bump encσ_c = Some encσ_c' ⌝ -∗
                                      ⌜ order encσ_p encσ_c ∨ encσ_p = encσ_c ⌝ -∗
                                      ⌜ order encσ_c encσ_f ⌝ -∗
                                      encoded_predicate_holds encp_read encσ_c v_c MsgV_c ==∗
                                      ∃ P_full' P_pers',
                                        encp_full encσ_c' v_c ≡ Some P_full' ∗ encp_pers encσ_c' v_c ≡ Some P_pers' ∗
                                        (nextgen_flush (P_full' ∗ P_pers': dPropO Σ)) MsgV_c))) ∗
    "#predReadNextgen" ∷ ([∗ map] ℓ ↦ pred_read; bumper ∈ predicates_read; bumpers,
                            ∀ e e' v TV, ■ (⌜ bumper e = Some e' ⌝ -∗ encoded_predicate_holds pred_read e v TV -∗
                                            ∃ (P: dPropO Σ), pred_read e' v ≡ Some P ∗ (nextgen_flush (P: dProp Σ)) TV)) ∗
    "#predFullReadSplit" ∷ ([∗ map] ℓ ↦ pred_full; pred_read ∈ predicates_full; predicates_read,
                              ∀ e v TV, ■ (encoded_predicate_holds pred_full e v TV -∗ encoded_predicate_holds pred_read e v TV)) ∗
    "%bumperBumpToValid" ∷
      ⌜ map_Forall
      (λ _ bumper, ∀ e e', bumper e = Some e' → is_Some (bumper e'))
      bumpers⌝ ∗
    "#bumperSome" ∷ ([∗ map] ℓ ↦ abs_hist; bumper ∈ abs_hists; bumpers,
                       ⌜ map_Forall (λ _ e, is_Some (bumper e)) abs_hist ⌝).

  (* Reassemble [interp] from [interp_pre] plus the two predicate-holds
   * components. *)
  Lemma interp_intro `{nvmHighGS}
    phys_hists abs_hists global_pview predicates_full predicates_read
    predicates_pers orders bumpers na_locs at_locs offsets na_views :
    interp_pre phys_hists abs_hists global_pview predicates_full predicates_read
      predicates_pers orders bumpers na_locs at_locs offsets na_views -∗
    (all_full_read_preds_hold phys_hists abs_hists na_views offsets predicates_full predicates_read ∗
     all_pers_preds_hold phys_hists abs_hists global_pview offsets predicates_pers) -∗
    interp.
  Proof.
    iIntros "Hpre [predsFullReadHold predsPersHold]".
    rewrite /interp.
    iFrame "predsFullReadHold predsPersHold".
    iNamed "Hpre".
    iExists orders, bumpers, na_locs, at_locs.
    repeat iFrameNamedF.
    done.
  Qed.

  Lemma interp_pre_insert_loc_at `{AbstractState ST, nvmHighGS}
      ℓ OCV (prot : LocationProtocol ST) `{!ProtocolConditions prot}
      σ SV PV v
      phys_hists abs_hists global_pview predicates_full predicates_read predicates_pers
      orders bumpers na_locs at_locs offsets na_views :
    ℓ ∉ dom OCV →
    SV !!0 ℓ = 0 →
    dom phys_hists = dom abs_hists →
    crashed_at_offset OCV -∗
    interp_pre phys_hists abs_hists global_pview predicates_full predicates_read
      predicates_pers orders bumpers na_locs at_locs offsets na_views -∗
    persisted_loc ℓ 0 -∗
    ℓ ↦fh initial_history AT SV PV v ==∗
    (persist_lb ℓ prot σ) (SV, PV, PV) ∗
    (ℓ ↦_AT^{prot} [σ]) (SV, PV, PV) ∗
    interp_pre
      (<[ℓ := initial_history AT SV PV v]> phys_hists)
      (<[ℓ := {[0 := encode σ]}]> abs_hists)
      global_pview
      (<[ℓ := encode_predicate (prot.(p_full))]> predicates_full)
      (<[ℓ := encode_predicate (prot.(p_read))]> predicates_read)
      (<[ℓ := encode_predicate (prot.(p_pers))]> predicates_pers)
      (<[ℓ := encode_relation (⊑@{ST})]> orders)
      (<[ℓ := encode_bumper (prot.(p_bumper))]> bumpers)
      na_locs
      (at_locs ∪ {[ℓ]})
      (<[ℓ := 0]> offsets)
      na_views.
  Proof.
    iIntros (domOCV svLook domEq) "crashed_at".
    iNamed 1.
    iIntros "#persisted_loc pts".
    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { assert (is_Some (offsets !! ℓ)) as (? & ?).
      { apply elem_of_dom. rewrite -offsetsDom. apply elem_of_dom. done. }
      iDestruct (big_sepM_lookup with "ptsMap") as "pts'".
      { naive_solver. }
      iDestruct (fmapsto_valid_2 with "pts pts'") as (?) "_".
      done. }

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
    iMod (full_map_insert _ _ _ _ _ {[0 := encode σ]} with "crashedRely [knowBumper] history")
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
    iDestruct (know_frag_history_loc_decode with "fragHist") as "#knowFrag".
    iSplitR.
    { (* persist_lb [s] at the bottom state: tP = offset = 0. *)
      rewrite /persist_lb /lb_base. iExists 0, 0.
      iFrame "prot knowFrag offset persisted_loc".
      iSplit; iPureIntro; lia. }
    iSplitL "knowFullPred knowReadPred knowPersPred knowBumper".
    { rewrite /mapsto_at.
      iExists _, {[ 0 := (Msg v SV PV PV) ]}, 0, 0, 0, σ, _.
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

    iFrame "full_predicates read_predicates pers_predicates allOrders naLocs atLocs history".

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
  Qed.

  Lemma interp_pre_insert_loc_na `{AbstractState ST, nvmHighGS}
      ℓ OCV (prot : LocationProtocol ST) `{!ProtocolConditions prot}
      σ SV PV v
      phys_hists abs_hists global_pview predicates_full predicates_read predicates_pers
      orders bumpers na_locs at_locs offsets na_views :
    ℓ ∉ dom OCV →
    SV !!0 ℓ = 0 →
    dom phys_hists = dom abs_hists →
    crashed_at_offset OCV -∗
    interp_pre phys_hists abs_hists global_pview predicates_full predicates_read
      predicates_pers orders bumpers na_locs at_locs offsets na_views -∗
    persisted_loc ℓ 0 -∗
    ℓ ↦fh initial_history NA SV PV v ==∗
    (persist_lb ℓ prot σ) (SV, PV, PV) ∗
    (ℓ ↦_{prot} [σ]) (SV, PV, PV) ∗
    interp_pre
      (<[ℓ := initial_history NA SV PV v]> phys_hists)
      (<[ℓ := {[0 := encode σ]}]> abs_hists)
      global_pview
      (<[ℓ := encode_predicate (prot.(p_full))]> predicates_full)
      (<[ℓ := encode_predicate (prot.(p_read))]> predicates_read)
      (<[ℓ := encode_predicate (prot.(p_pers))]> predicates_pers)
      (<[ℓ := encode_relation (⊑@{ST})]> orders)
      (<[ℓ := encode_bumper (prot.(p_bumper))]> bumpers)
      (na_locs ∪ {[ℓ]})
      at_locs
      (<[ℓ := 0]> offsets)
      (<[ℓ := SV]> na_views).
  Proof.
    iIntros (domOCV svLook domEq) "crashed_at".
    iNamed 1.
    iIntros "#persisted_loc pts".

    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { assert (is_Some (offsets !! ℓ)) as (? & ?).
      { apply elem_of_dom. rewrite -offsetsDom. apply elem_of_dom. done. }
      iDestruct (big_sepM_lookup with "ptsMap") as "pts'".
      { naive_solver. }
      iDestruct (fmapsto_valid_2 with "pts pts'") as (?) "_".
      done. }

    iDestruct (big_sepM2_dom with "bumperSome") as %domEq2.
    iDestruct (big_sepM2_dom with "bumpMono") as %domEq4.
    assert (offsets !! ℓ = None) as offsetsLook.
    { apply not_elem_of_dom. rewrite -offsetsDom. apply not_elem_of_dom. done. }
    assert (abs_hists !! ℓ = None) as absHistsLook.
    { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom.
      assumption. }
    assert (ℓ ∉ dom abs_hists) as absHistsDomElem.
    { apply not_elem_of_dom. done. }

    (* We update ghost state. *)
    (* Update ghost state for physical history. *)
    iMod (auth_map_map_insert_top with "physHists") as "[physHists ownPhysHist]".
    { done. }

    (* Add the predicate to the ghost state of predicates. *)
    iMod (own_all_preds_insert (ST := ST) with "full_predicates") as "[full_predicates knowFullPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (own_all_preds_insert (ST := ST) with "read_predicates") as "[read_predicates knowReadPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (own_all_preds_insert (ST := ST) with "pers_predicates") as "[pers_predicates knowPersPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    (* add offset to offsets *)
    iMod (offset_auth_insert with "crashed_at offsets") as "[offsets #offset]".
    { done. } { apply not_elem_of_dom. done. }

    (* Allocate the abstract history for the location. *)
    iMod (own_all_bumpers_insert _ _ (prot.(p_bumper)) with "allBumpers")
      as "[allBumpers #knowBumper]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (full_map_insert _ _ _ _ _ {[0 := encode σ]} with "crashedRely [knowBumper] history")
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

    iAssert (know_protocol ℓ prot)%I as "#prot".
    { rewrite /know_protocol.
      iFrame "knowFullPred knowReadPred knowPersPred knowBumper knowOrder". }

    iModIntro.
    iDestruct (know_frag_history_loc_decode with "fragHist") as "#knowFrag".
    iSplitR.
    { rewrite /persist_lb /lb_base. iExists 0, 0.
      iFrame "prot knowFrag offset persisted_loc".
      iSplit; iPureIntro; lia. }
    iSplitL "knowFullPred knowReadPred knowPersPred knowBumper knowOrder ownHist ownNaView ownPhysHist".
    { rewrite /mapsto_na.
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
      iSplitPure; first apply lookup_singleton_eq.
      iSplitPure; first apply map_no_later_singleton.
      iSplit.
      { iExists _.
        iFrame "fragHist".
        rewrite decode_encode. done. }
      iSplitPure; first (split; [apply lookup_singleton_eq | reflexivity]).
      iSplitPure; first repeat split; auto using view_empty_least.
      iSplitPure; first lia.
      iSplitPure; first lia.
      iRight. done. }
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
    iSplitPure. { rewrite dom_insert_L. f_equal. done. }
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
  Qed.

  Lemma interp_pre_alloc_at_all `{Hhigh: nvmHighGS}
    OCV PV (σ: gmap loc val) (locinfos: LocInfos Hhigh) :
    dom OCV = ∅ →
    dom σ ⊆ dom PV →
    dom locinfos = dom σ →
    crashed_at_offset OCV -∗
    persisted PV -∗
    interp_pre ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ ∅ -∗
    ([∗ map] ℓ ↦ v ∈ σ, ℓ ↦fh {[ 0 := Msg v ∅ ∅ ∅ ]}) ==∗
    interp_pre
      ((λ v, {[ 0 := Msg v ∅ ∅ ∅ ]}) <$> σ)
      ((λ li, {[ 0 := encode li.(li_σ0) ]}) <$> locinfos)
      ∅
      ((λ li, encode_predicate (li.(li_prot).(p_full))) <$> locinfos)
      ((λ li, encode_predicate (li.(li_prot).(p_read))) <$> locinfos)
      ((λ li, encode_predicate (li.(li_prot).(p_pers))) <$> locinfos)
      ((λ li, encode_relation (⊑@{li.(li_ST)})) <$> locinfos)
      ((λ li, encode_bumper (li.(li_prot).(p_bumper))) <$> locinfos)
      ∅
      (dom σ)
      ((λ _ : val, 0) <$> σ)
      ∅ ∗
    init_at_assertions σ locinfos ⊥.
  Proof.
    unfold init_at_assertions.
    iIntros (HOCV HPVdom domEq) "#OCV #persisted interp fmapstos".
    iInduction σ as [|ℓ v σ' Hℓ IH] using map_ind
      forall (locinfos domEq HPVdom) "interp fmapstos".
    - assert (locinfos = ∅) as ->.
      { apply dom_empty_inv_L. rewrite domEq dom_empty_L //. }
      iModIntro.
      rewrite !fmap_empty dom_empty_L.
      iFrame "interp".
      rewrite big_sepM2_empty //.
    - rewrite dom_insert_L in domEq, HPVdom |- *.
      assert (ℓ ∉ dom σ') as Hℓdom by (apply not_elem_of_dom; done).
      assert (is_Some (locinfos !! ℓ)) as [li Hlookup].
      { apply elem_of_dom. rewrite domEq. set_solver. }
      assert (is_Some (PV !! ℓ)) as [[t2] HPVℓ].
      { apply elem_of_dom. set_solver. }
      iDestruct (persisted_persisted_loc_weak PV ℓ 0 t2 HPVℓ (Nat.le_0_l t2)
                  with "persisted") as "#persisted_loc".
      rewrite big_sepM_insert //.
      iDestruct "fmapstos" as "[ℓpts fmapstos]".
      assert (locinfos = <[ℓ := li]> (delete ℓ locinfos)) as locsEq.
      { apply map_eq. intros ℓ'.
        destruct (decide (ℓ' = ℓ)) as [ -> | Hne ]; by simplify_map_eq. }
      iMod ("IH" $! (delete ℓ locinfos) with "[] [] interp fmapstos") as "[interp init_prot]".
      { iPureIntro. rewrite dom_delete_L. set_solver. }
      { iPureIntro. set_solver. }
      iMod (interp_pre_insert_loc_at ℓ OCV (li.(li_prot)) (li.(li_σ0)) ∅ ∅ v
             with "OCV interp persisted_loc ℓpts") as "(ℓPer & ℓpts & interp)".
      { set_solver. }
      { done. }
      { rewrite !dom_fmap_L dom_delete_L domEq. set_solver. }
      iModIntro.
      iSplitL "interp".
      + rewrite !fmap_delete ?insert_delete_id ?lookup_fmap ?Hlookup /= //.
        rewrite !fmap_insert union_comm_L.
        iExact "interp".
      + rewrite {2}locsEq.
        rewrite !monPred_at_big_sepM2.
        iApply (big_sepM2_insert_2 with "[ℓPer ℓpts] init_prot").
        iFrame.
  Qed.

  Lemma interp_pre_alloc_na_all `{baseG : !nvmBaseGS Σ Ω} `{hH : !nvmHighGS Σ Ω}
      OCV PV (σ : gmap loc val) (locinfos : gmap loc (@LocInfo _ _ _ hH))
      phys_hists abs_hists full_predicates read_predicates pers_predicates
      orders bumpers na_locs at_locs offsets na_views:
    dom OCV = ∅ →
    dom σ ⊆ dom PV →
    dom locinfos = dom σ →
    dom σ ## dom phys_hists →
    dom phys_hists = dom abs_hists →
    crashed_at_offset OCV -∗
    persisted PV -∗
    interp_pre phys_hists abs_hists ∅ full_predicates read_predicates pers_predicates
      orders bumpers na_locs at_locs offsets na_views -∗
    ([∗ map] ℓ ↦ v ∈ σ, ℓ ↦fh {[ 0 := Msg v ∅ ∅ ∅ ]}) ==∗
      interp_pre
        (((λ v, {[ 0 := Msg v ∅ ∅ ∅ ]}) <$> σ) ∪ phys_hists)
        (((λ li, {[ 0 := encode li.(li_σ0) ]}) <$> locinfos) ∪ abs_hists)
        ∅
        (((λ li, encode_predicate (li.(li_prot).(p_full))) <$> locinfos) ∪ full_predicates)
        (((λ li, encode_predicate (li.(li_prot).(p_read))) <$> locinfos) ∪ read_predicates)
        (((λ li, encode_predicate (li.(li_prot).(p_pers))) <$> locinfos) ∪ pers_predicates)
        (((λ li, encode_relation (⊑@{li.(li_ST)})) <$> locinfos) ∪ orders)
        (((λ li, encode_bumper (li.(li_prot).(p_bumper))) <$> locinfos) ∪ bumpers)
        (na_locs ∪ dom σ)
        at_locs
        (((λ _ : val, 0) <$> σ) ∪ offsets)
        (((λ _ : val, (∅:view.view)) <$> σ) ∪ na_views) ∗
      init_na_assertions σ locinfos ⊥.
  Proof.
    unfold init_na_assertions.
    iIntros (HOCV HPVdom domEq Hdisj domHists) "#OCV #persisted interp fmapstos".
    iInduction σ as [|ℓ v σ' Hℓ IH] using map_ind
      forall (locinfos domEq HPVdom Hdisj) "interp fmapstos".
    - assert (locinfos = ∅) as ->.
      { apply dom_empty_inv_L. rewrite domEq dom_empty_L //. }
      iModIntro.
      rewrite !fmap_empty dom_empty_L !map_empty_union right_id_L.
      iFrame "interp".
      rewrite big_sepM2_empty //.
    - rewrite dom_insert_L in domEq, HPVdom |- *.
      assert (ℓ ∉ dom σ') as Hℓdom by (apply not_elem_of_dom; done).
      assert (is_Some (locinfos !! ℓ)) as [li Hlookup].
      { apply elem_of_dom. rewrite domEq. set_solver. }
      assert (is_Some (PV !! ℓ)) as [[t2] HPVℓ].
      { apply elem_of_dom. set_solver. }
      iDestruct (persisted_persisted_loc_weak PV ℓ 0 t2 HPVℓ (Nat.le_0_l t2)
                  with "persisted") as "#persisted_loc".
      rewrite big_sepM_insert //.
      iDestruct "fmapstos" as "[ℓpts fmapstos]".
      assert (locinfos = <[ℓ := li]> (delete ℓ locinfos)) as locsEq.
      { apply map_eq. intros ℓ'.
        destruct (decide (ℓ' = ℓ)) as [ -> | Hne ]; by simplify_map_eq. }
      iMod ("IH" $! (delete ℓ locinfos) with "[] [] [] interp fmapstos") as "[interp init_prot]".
      { iPureIntro. rewrite dom_delete_L. set_solver. }
      { iPureIntro. set_solver. }
      { iPureIntro. set_solver. }
      iMod (interp_pre_insert_loc_na ℓ OCV (li.(li_prot)) (li.(li_σ0)) ∅ ∅ v
             with "OCV interp persisted_loc ℓpts") as "(ℓPer & ℓpts & interp)".
      { set_solver. }
      { done. }
      { rewrite !dom_union_L !dom_fmap_L dom_delete_L.
        set_solver. }
      iModIntro.
      iSplitL "interp".
      + iEval (rewrite locsEq !fmap_insert -!insert_union_l).
        replace (na_locs ∪ ({[ℓ]} ∪ dom σ')) with ((na_locs ∪ dom σ') ∪ {[ℓ]}) by set_solver.
        iExact "interp".
      + rewrite {2}locsEq.
        rewrite !monPred_at_big_sepM2.
        iApply (big_sepM2_insert_2 with "[ℓPer ℓpts] init_prot").
        iFrame.
  Qed.
End adequacy_alloc.
