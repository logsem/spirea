From iris.proofmode Require Import proofmode monpred.
From iris_named_props Require Import named_props.
From self Require Export extra ipm_tactics solve_view_le.

From self.high Require Export dprop.
From self.base Require Import generational_resources primitive_laws.
From self.high Require Import
  generational_resources wrappers crash_weakestpre monpred_simpl modalities protocol locations weakestpre.
From self.high.lib Require Import abstract_state.

From self.lang Require Import syntax tactics lemmas.
From self Require Export lang.

Section post_fence_sync.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.
  Implicit Types (ℓ : loc).
  (* For every location we [flush], we will keep the follow tuple,
   * - [ℓ], the location
   * - [σ], the abstract state we flush,
   * - [σ_xchg], the "exchange" state we want to extract resources from,
   * - [seen ℓ σ_xchg], so that we have the necessary view,
   * and we also keep enough resource to make three consecutive exchanges/updates with
   * the protocol in the future and obtain final post condition [R] (when we [flush_sync]),
   * - [<obj> p_read σ v -∗ □ <obj> P], for getting some basic facts about the physical value,
   * - [P -∗ <obj> (p_pers σ_old v_old ==∗ <obj> Q ∗ p_pers σ v)] roughly, for the persistent state update,
   * - [Q -∗ <obj> (p_read σ_xchg v_xchg ==∗ R ∗ p_read σ_xchg v_xchg)] for the read only exchange. *)
  
  Definition exchange_3 `{AbstractState ST} ℓ (σ_xchg: ST) (prot: LocationProtocol ST) Q: dProp Σ :=
    ∀ v_xchg, <obj> (prot.(p_read) σ_xchg v_xchg ==∗ Q ∗ prot.(p_read) σ_xchg v_xchg).

  (* TODO: include the other case as well *)
  Definition exchange_2 `{AbstractState ST} ℓ (σ_xchg σ: ST) v (prot: LocationProtocol ST) Q: dProp Σ :=
    ∀ σ_old v_old,
    <obj> ((⌜ σ_old ⊑ σ ⌝ -∗ prot.(p_pers) σ_old v_old ==∗
           prot.(p_pers) σ v ∗ exchange_3 ℓ σ_xchg prot Q) ∧
           (⌜ σ ⊑ σ_old ⌝ -∗ prot.(p_pers) σ_old v_old ==∗
           prot.(p_pers) σ_old v_old ∗ exchange_3 ℓ σ_xchg prot Q)).

  Definition exchange_1 `{AbstractState ST} ℓ (σ_xchg σ: ST) (prot: LocationProtocol ST) Q: dProp Σ :=
    ∀ v,
    <obj> (prot.(p_read) σ v -∗ prot.(p_read) σ v ∗ exchange_2 ℓ σ_xchg σ v prot Q).

  Record FlushInfo := MkFlushInfo {
    fi_ℓ: loc;
    fi_ST: Type;
    fi_ST_eqdec :> EqDecision fi_ST;
    fi_ST_countable :> Countable fi_ST;
    fi_ST_is_abstract :> AbstractState fi_ST;
    fi_prot: LocationProtocol fi_ST;
    fi_prot_conds :> ProtocolConditions fi_prot;
    fi_σ: fi_ST;
    fi_σ_xchg: fi_ST;
    fi_post: dProp Σ
  }.

  #[local] Definition internal_flush_lb `{AbstractState ST} ℓ (prot: LocationProtocol ST) (s : ST) : dProp Σ :=
    ∃ (t : nat) offset,
      "#lbBase" ∷ lb_base ℓ prot offset t s ∗
      (* this assertion is only ever to be used internally, we can safely assert over
       *  about buffer views. *)
      "%haveBV" ∷ have_thread_view (∅, ∅, {[ ℓ := MaxNat (t - offset) ]}).

  Program Definition post_fence_sync'
    (P : dProp Σ) : dProp Σ :=
    MonPred (λ TV,
      ∃ (fi_list: list FlushInfo),
        ([∗ list] fi ∈ fi_list,
           ⎡ is_at_loc fi.(fi_ℓ) ⎤ ∗
           know_protocol fi.(fi_ℓ) fi.(fi_prot) ∗
           (* this can probably be promoted to [flush_lb], but doens't seem necessary? *)
           internal_flush_lb fi.(fi_ℓ) fi.(fi_prot) fi.(fi_σ) ∗
           seen_state fi.(fi_ℓ) fi.(fi_prot) fi.(fi_σ_xchg) ∗
           exchange_1 fi.(fi_ℓ) fi.(fi_σ_xchg) fi.(fi_σ) fi.(fi_prot) fi.(fi_post))
          TV ∗
        ((persisted (buffer_view TV)) -∗
         (([∗ list] fi ∈ fi_list, fi.(fi_post)) -∗ P)
           (store_view TV, (flush_view TV ⊔ buffer_view TV), buffer_view TV))
      )%I _.
  Next Obligation.
    intros P. intros [[??]?] [[??]?] [[??]?]. simpl.
    assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
    iIntros "(%fi_list & Hfi & P)".
    iExists fi_list.
    iSplitL "Hfi".
    - iApply monPred_mono; last done.
      solve_view_le.
    - iIntros "pers".
      iPoseProof (persisted_anti_mono with "pers") as "pers";
        (* use the special reasoning to figure out the view automatically. *)
        last iSpecialize ("P" with "pers"); first done.
      iApply monPred_mono; last done.
      solve_view_le.
  Qed.
End post_fence_sync.

Section weakestpre.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, AbstractState ST}.
  
  Implicit Types (ℓ : loc) (prot: LocationProtocol ST) (σ σ_e: ST) (P Q: dProp Σ).
  Lemma wp_flush' ℓ prot `{!ProtocolConditions prot} σ_xchg σ st E Q:
    {{{ ⎡ is_at_loc ℓ ⎤ ∗
        store_lb ℓ prot σ ∗
        seen_state ℓ prot σ_xchg ∗
        exchange_1 ℓ σ_xchg σ prot Q }}}
      Flush #ℓ @ st; E
    {{{ RET #();
      post_fence_sync' (persist_lb ℓ prot σ ∗ Q)
    }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "(#isAtLoc & #storeLb & #seen & exchange)".
    iNamed "seen". rename a into t_xchg. rename a0 into offset. rename a1 into msg_xchg. 
    iDestruct "lbBase" as "(_ & fragHistXchg & #offsetXchg & %tSLeXchg)".
    iNamed "storeLb". rename a into t. rename a0 into offset'.
    iNamed "lbBase".
    iDestruct "tSLe" as %tSLe.
    (* remove duplicate offset *)
    iDestruct (offset_loc_agree with "offset offsetXchg") as %->. iClear "offsetXchg".
    iIntros (TV' incl) "HΦ".
    iApply wp_unfold_at.
    iIntros ([[SV'' PV''] BV''] incl') "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_flush_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* offset lookup *)
    iDestruct (offset_loc_crashed_at_agree with "[$] [$]") as %offsetLook.
    
    (* lookup [msg_xchg] early for for [wp_flush] *)
    iAssert ⌜ ∃ pHist, phys_hists !! ℓ = Some pHist ∧ pHist !! t_xchg = Some msg_xchg ⌝%I as %[pHist [HphysHistLook HpHistLookXchg]].
    { iPoseProof (auth_map_map_auth_frag with "[$] [$knowPhysMsg]") as "$". }
    
    (* obtain mapsto assertion from [interp] to apply base Spirea [wp_flush]. *)
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]".
    { naive_solver. }

    iApply (wp_flush_alt (extra := {| extra_state_interp := True |}) with "pts").
    iNext. iIntros "pts".
    iSpecialize ("ptsMap" with "pts").

    (* view related pure facts. *)
    assert (t - offset ≤ SV'' !!0 ℓ) as tSLe2.
    { etrans; first apply tSLe. simpl.
      f_equiv. solve_view_le. }
    assert (t_xchg - offset ≤ SV'' !!0 ℓ) as tSLeXchg2.
    { etrans; first apply tSLeXchg. simpl.
      f_equiv. solve_view_le. }
    rewrite -assoc.
    iSplitPure.
    { repeat split; try done. apply view_le_lub_r. done. }
    iFrame "val".

    iSplitL "HΦ exchange".
    { iEval (monPred_simpl) in "HΦ". iApply "HΦ".
      { iPureIntro. solve_view_le. }
      iSimpl.
      iExists ([MkFlushInfo ℓ _ _ _ _ prot _ σ σ_xchg Q]).
      iSimpl.
      iSplitR "".
      - rewrite right_id.
        iSplitR; first done. (* [is_at_loc] *)
        iSplitR; first done. (* [know_protocol] *)
        iSplitR. (* [internal_flush_lb] *)
        { iExists t, offset. iFrameNamed.
          iSplitPure; first done.
          iPureIntro.
          split; first (split; solve_view_le).
          apply view_le_lub_l.
          apply view_le_singleton.
          eexists.
          rewrite lookup_singleton.
          split; first done.
          lia. }
        iSplitR. (* [seen_state] *)
        { iExists t_xchg, offset, msg_xchg. iFrameNamed. iFrame "#".
          iSplitPure; first done.
          iApply monPred_mono; last done.
          pose proof (view_le_r PV'' {[ ℓ := MaxNat (SV'' !!0 ℓ) ]}).
          solve_view_le.
          (split; first split); solve_view_le. }
        rewrite /exchange_1.
        iIntros (v). iSpecialize ("exchange" $! v).
        iPoseProof (objective_at with "exchange") as "exchange".
        iApply "exchange".
      - iIntros "persisted".
        rewrite right_id.
        iIntros ([[SV''' PV'''] BV'''] [[? ?] ?]) "$".
        iExists t, offset.
        iFrameNamed.
        iSplitPure.
        { etrans; first apply tSLe2. simpl.
          f_equiv. solve_view_le. }
        iSplitPure.
        (* TODO: improve this proof? *)
        { etrans; first apply tSLe2. simpl.
          assert ({[ℓ := MaxNat (SV'' !!0 ℓ)]} ⊑ PV''') as Hflush by solve_view_le.
          apply view_le_singleton in Hflush as [? [Hlook ?]].
          rewrite /lookup_zero Hlook //. }
        rewrite /persisted_loc.
        destruct (BV'' !! ℓ) as [[?]|] eqn:bvLook.
        * iApply (persisted_persisted_loc_weak with "persisted").
          { apply lookup_join; last done.
            rewrite lookup_singleton. done. }
          lia.
        * iApply (persisted_persisted_loc_weak with "persisted").
          { rewrite lookup_op.
            rewrite bvLook.
            rewrite right_id.
            rewrite lookup_singleton. done. }
          lia. }
    (* restore [interp] *)
    iExistsN.
    iFrameNamed.
  Qed.
End weakestpre.

Section weakestpre.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.

  (* View summary:
   * [SV PV BV]: the thead view before [fence_sync] *)
  Lemma wp_fence_sync' (st : stuckness) (E : coPset) (P : dProp Σ) :
    {{{ post_fence_sync' P }}} FenceSync @ st; E {{{ RET #(); P }}}.
  Proof.
    intros Φ.
    iModel.
    destruct TV as [[SV PV] BV].
    iIntros "PFS".
    iIntros ([[SV' PV'] BV'] [[? ?] ?]) "HΦ".
    iApply wp_unfold_at.
    iIntros ([[SV'' PV''] BV''] [[? ?] ?]) "#val".
    (* TODO: move to a separate lemma to prove this for wp alone. *)
    iApply wp_extra_state_interp. { done. } { by apply prim_step_fence_sync_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* TODO: move to a separate lemma *)
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.
    iDestruct "PFS" as (fi_list) "[fi_exchange_list Hpost]".
    
    iEval (rewrite monPred_at_big_sepL) in "fi_exchange_list".
    (* Here comes the difficult part: since we have multiple locations, we need to obtain a [∗ list] of
     * equivalences under later modality. *)
    iAssert (▷ [∗ list] fi ∈ fi_list,
               (∃ encp_full encp_read encp_pers : enc_predicateO,
                  ⌜predicates_full !! fi.(fi_ℓ) = Some encp_full⌝ ∗ (encp_full ≡ encode_predicate fi.(fi_prot).(p_full)) ∗
                  ⌜predicates_read !! fi.(fi_ℓ) = Some encp_read⌝ ∗ (encp_read ≡ encode_predicate fi.(fi_prot).(p_read)) ∗
                  ⌜predicates_pers !! fi.(fi_ℓ) = Some encp_pers⌝ ∗ (encp_pers ≡ encode_predicate fi.(fi_prot).(p_pers))))%I
      as "#predicatesEquiv".
    { iApply big_sepL_later.
      iDestruct (big_sepL_impl_with_resource with "[full_predicates read_predicates pers_predicates] fi_exchange_list []") as "[_ $]".
      { iNamedAccu. }
      iIntros "!>" (k fi ?). iNamed 1.
      iIntros "(_ & knowProtocol & _)".
      iNamed "knowProtocol".
      iPoseProof (own_all_full_preds_pred with "[$] [$]") as (? ?) "#p_fullEquiv".
      iPoseProof (own_all_read_preds_pred with "[$] [$]") as (? ?) "#p_readEquiv".
      iPoseProof (own_all_pers_preds_pred with "[$] [$]") as (? ?) "#p_persEquiv".
      iFrame.
      iNext.
      iExistsN. iFrame "#%". }
    
    iApply (primitive_laws.wp_fence_sync (extra := {| extra_state_interp := True |}) with "[//]").
    simpl.
    iNext. iIntros "#persisted".
    (* before we apply the exchanges, we need to first combine [p_pers] with [global_pview] assertion.
     * TODO: make it better? ... *)
    iAssert (∃ global_pview', ⌜ dom global_pview' ⊆ dom abs_hists ⌝ ∗
            ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ phys_hists;abs_hists,
               ∃ encp_pers (t offset: nat) encσ msg,
                 ⌜ predicates_pers !! ℓ = Some encp_pers ⌝ ∗
                 ⌜ offsets !! ℓ = Some offset ⌝ ∗
                 ⌜ abs_hist !! t = Some encσ ⌝ ∗
                 ⌜ phys_hist !! t = Some msg ⌝ ∗
                 ⌜ Nat.add offset (global_pview' !!0 ℓ) = t ⌝ ∗
                 default emp (persisted_loc ℓ <$> (max_nat_car <$> (global_pview' !! ℓ))) ∗
                 encoded_predicate_holds encp_pers encσ msg.(msg_val) (∅, ∅, ∅)))%I with "[predsPersHold]" as "predsP".
    { iExists global_pview.
      iFrame "∗#%". }
    clear histPViewDoms global_pview.
    (* Let's deal with the exchanges *)
    iDestruct (big_sepL_fupd_with_resource _ (λ _ fi, fi.(fi_post) (SV, PV ⊔ BV, BV))%I with
                "[-fi_exchange_list] fi_exchange_list []") as ">[R Hfi_post]".
    { iNamedAccu. }
    { iIntros "!>" (k fi HfiLook). iNamed 1.
      iIntros "(#isAtLoc & #knowProtocol & #flushLb & #seen & exchange)".
      iNamed "seen". rename a into t_xchg. rename a0 into offset. rename a1 into msg_xchg.
      iDestruct "lbBase" as "(_ & fragHistXchg & #offsetXchg & %tSLeXchg)".
      iNamed "flushLb". rename a into t. rename a0 into offset'.
      destruct haveBV as [_ haveBV].
      iNamed "lbBase".
      iDestruct "tSLe" as %tSLe.
      (* Extract the precious equality we obtained earlier. *)
      iDestruct (big_sepL_lookup _ _ k with "predicatesEquiv")
        as (encp_full encp_read encp_pers) "(% & pFullEquiv & % & pReadEquiv & % & pPersEquiv)"; first done.
      
      (* remove duplicate offset *)
      iDestruct (offset_loc_agree with "offset offsetXchg") as %->. iClear "offsetXchg".
      (* also obtain offset lookup equality *)
      iAssert ⌜ offsets !! fi.(fi_ℓ) = Some offset ⌝%I with "[offsets]" as "%".
      {  iDestruct "offset" as (OCV) "[offsets' %Heq]". 
        iDestruct (crashed_at_offset_agree with "offsets offsets'") as "%".
        iPureIntro.
        simplify_map_eq.
        rewrite lookup_fmap_Some in Heq.
        destruct Heq as [? [? ?]].
        by simplify_eq. }
      (* [ℓ] is atomic location. *)
      iPoseProof (location_sets_singleton_included with "[$] [$]") as "%isAtLoc".
      (* lookup [msg_xchg] *)
      iAssert ⌜ ∃ pHist, phys_hists !! fi.(fi_ℓ) = Some pHist ∧ pHist !! t_xchg = Some msg_xchg ⌝%I
          as %[pHist [HphysHistLook HpHistLookXchg]].
      { iPoseProof (auth_map_map_auth_frag with "[$] [$knowPhysMsg]") as "$". }
      (* lookup [σ_xchg] *)
      iAssert ⌜ ∃ aHist encσ_xchg, abs_hists !! fi.(fi_ℓ) = Some aHist ∧ aHist !! t_xchg = Some encσ_xchg ∧ decode encσ_xchg = Some fi.(fi_σ_xchg) ⌝%I
          as %(aHist & encσ_xchg & HabsHistLook & HaHistLookXchg & HdecodeXchg).
      { iPoseProof (full_map_frag_singleton_agreee with "[$] [$fragHistXchg]") as "$". }
      (* lookup [σ] *)
      iAssert ⌜ ∃ aHist encσ, abs_hists !! fi.(fi_ℓ) = Some aHist ∧ aHist !! t = Some encσ ∧ decode encσ = Some fi.(fi_σ) ⌝%I
          as %(aHist' & encσ & HabsHistLook' & HaHistLook & Hdecode).
      { iPoseProof (full_map_frag_singleton_agreee with "[$] [$knowFragHist]") as "$". }
      (* extracts [ℓ] from order *)
      iDestruct (big_sepM2_dom with "ordered") as "%domOrders".
      assert (fi.(fi_ℓ) ∈ dom orders) as [enc_order HordersLook]%elem_of_dom.
      { set_solver. }
      iDestruct (orders_lookup with "allOrders []") as "%HorderEncode"; first done.
      { iNamed "knowProtocol". iAssumption. }
      
      (* extract [ℓ] from [predsFR] *)
      iDestruct (big_sepM2_lookup_acc _ _ _ fi.(fi_ℓ) with "predsFullReadHold") as
        "[(%encp_full' & %encp_read' & %offset' & %predFullLook' & %predReadLook' & %offsetLook' & predFR) predFRRest]".
      { done. } { done. }
      (* extract [ℓ] from [predsP] *)
      iDestruct ("predsP") as (global_pview) "(%histPViewDoms & predsP)".
      iDestruct (big_sepM2_delete _ _ _ fi.(fi_ℓ) with "predsP") as
        "[(%encp_pers' & %t_p_old & %offset'' & %encσ_p_old & %msg_p_old & % & % & % & % & %globalPViewLook & persistedOld & predP) predPRest]".
      { done. } { done. }
      (* Try to remove the context as much as possible to make my life easier. *)
      iFrameNamed.
      simplify_map_eq.

      (* since we are atomic, remove all [na_views] references *)
      assert (na_views !! fi.(fi_ℓ) = None) as ->.
      { rewrite -not_elem_of_dom. set_solver. }
      simpl default.
      (* there also exists [msg] *)
      iAssert ⌜ t ∈ dom pHist ⌝%I
          as %[msg HpHistLook]%elem_of_dom.
      { iPoseProof (big_sepM2_dom with "predFR") as "->".
        iPureIntro. apply elem_of_dom. by eexists. }
      
      (* first exchange *)
      iPoseProof (objective_at _ _ (msg_store_view msg, msg_persisted_after_view msg, ∅) with "exchange") as "exchange".
      iDestruct (big_sepM2_lookup_acc _ _ _ t with "predFR") as "[predFR predFRAcc]".
      { done. } { done. }
      set (predFR := if (decide _) then _ else _).
      iAssert (predFR ∗ (exchange_2 (fi_ℓ fi) (fi_σ_xchg fi) (fi_σ fi) msg.(msg_val) (fi_prot fi) (fi_post fi)) (∅, ∅, ∅))%I
        with "[predFR exchange]" as "[predFR exchange]".
      { iEval (monPred_simpl) in "exchange".
        subst predFR.
        destruct (decide _).
        - iPoseProof (predicate_holds_phi_decode_1 with "[$pFullEquiv] [$]") as "pFull"; first done.
          (* why is typeclass not working? *)
          iPoseProof (fi.(fi_prot_conds).(full_read_split) with "pFull") as "[pRead pFullAcc]".
          (* [exchange_2] unfolds here for some reason? *)
          Opaque exchange_2.
          iDestruct ("exchange" with "pRead") as "[pRead exchange]".
          iSpecialize ("pFullAcc" with "pRead").
          iPoseProof (predicate_holds_phi_decode_2 with "[$pFullEquiv] [$]") as "pFull"; first done.
          iFrame.
          Transparent exchange_2.
          iApply (objective_at with "exchange").
        - iPoseProof (predicate_holds_phi_decode_1 with "[$pReadEquiv] [$]") as "pRead"; first done.
          (* [exchange_2] unfolds here for some reason? *)
          Opaque exchange_2.
          iDestruct ("exchange" with "pRead") as "[pRead exchange]".
          iPoseProof (predicate_holds_phi_decode_2 with "[$pReadEquiv] [$]") as "pRead"; first done.
          iFrame.
          Transparent exchange_2.
          iApply (objective_at with "exchange"). }

      iDestruct ("predFRAcc" with "predFR") as "predFR".

      (* second exchange and update [global_pview] *)
      iEval (rewrite /exchange_2) in "exchange".
      (* look into [encoded_predicate_holds] to justify decoding of [encσ_p_old] *)
      iAssert (⌜ ∃ σ_p_old, decode encσ_p_old = Some σ_p_old ⌝)%I as (σ_p_old) "%HdecodePOld".
      { iDestruct "predP" as (PP) "[#eqP _]".
        iEval (rewrite discrete_fun_equivI) in "pPersEquiv".
        iSpecialize ("pPersEquiv" $! encσ_p_old).
        iEval (rewrite discrete_fun_equivI) in "pPersEquiv".
        iSpecialize ("pPersEquiv" $! (msg_val msg_p_old)).
        iRewrite "pPersEquiv" in "eqP".
        iPoseProof (encode_predicate_decode fi.(fi_prot).(p_pers) encσ_p_old msg_p_old.(msg_val) PP with "eqP") as (σp) "%".
        iExists _. done. }
      iDestruct ("exchange" $! σ_p_old msg_p_old.(msg_val)) as "exchange".
      iEval (monPred_simpl) in "exchange".
      (* we are not taking any subjective resource anyway, might as well choose the simplest view. *)
      iDestruct ("exchange" $! (∅, ∅, ∅)) as "exchange".
      (* attempt to not duplicate third exchange proof *)
      set t_p_old := (offset + (global_pview !!0 fi_ℓ fi)).
      iAssert (|==> exchange_3 (fi_ℓ fi) (fi_σ_xchg fi) (fi_prot fi) (fi_post fi) (∅, ∅, ∅) ∗
                    if decide (t_p_old ≤ t) then
                      encoded_predicate_holds encp_pers encσ (msg_val msg) (∅, ∅, ∅)
                    else
                      encoded_predicate_holds encp_pers encσ_p_old (msg_val msg_p_old) (∅, ∅, ∅))%I
        with "[predP exchange]" as ">[exchange predP]".
      { iPoseProof (big_sepM2_lookup with "ordered") as "%Hinc".
        { done. } { done. }
        destruct (decide (t_p_old ≤ t)).
        - iDestruct "exchange" as "[exchange _]".
          iPoseProof (predicate_holds_phi_decode_1 _ with "[$pPersEquiv] [$]") as "pPers"; first done.
          Opaque exchange_3.
          iDestruct ("exchange" with "[] pPers") as ">[pPers exchange]".
          { destruct (decide (t_p_old = t)) as [ | ]; first by simplify_map_eq.
            specialize (Hinc t_p_old t _ _ ltac:(lia) ltac:(done) ltac:(done)).
            eapply encode_relation.encode_relation_decode_iff_1 in Hinc; done. }
          Transparent exchange_3.
          iPoseProof (predicate_holds_phi_decode_2 with "[$pPersEquiv] [$]") as "pPers"; first done.
          iFrame.
          done.
        - iDestruct "exchange" as "[_ exchange]".
          iPoseProof (predicate_holds_phi_decode_1 _ with "[$pPersEquiv] [$]") as "pPers"; first done.
          Opaque exchange_3.
          iDestruct ("exchange" with "[] pPers") as ">[pPers exchange]".
          { specialize (Hinc t t_p_old _ _ ltac:(lia) ltac:(done) ltac:(done)).
            eapply encode_relation.encode_relation_decode_iff_1 in Hinc; done. }
          Transparent exchange_3.
          iPoseProof (predicate_holds_phi_decode_2 with "[$pPersEquiv] [$]") as "pPers"; first done.
          iFrame.
          done. }
      
      (* final exchange *)
      iDestruct (big_sepM2_lookup_acc _ _ _ t_xchg with "predFR") as "[predFR predFRAcc]".
      { done. } { done. }
      clear predFR.
      set (predFR := if (decide (_ ∧ _)) then _ else _).
      iAssert (|==> predFR ∗ fi.(fi_post) (msg_store_view msg_xchg, msg_persisted_after_view msg_xchg, ∅))%I
        with "[predFR exchange]" as ">[predFR Hfi_post]".
      { rewrite /exchange_3.
        iSpecialize ("exchange" $! msg_xchg.(msg_val)).
        subst predFR.
        destruct (decide _).
        - iPoseProof (predicate_holds_phi_decode_1 with "[$pFullEquiv] [$]") as "pFull"; first done.
          (* why is typeclass not working? *)
          iPoseProof (fi.(fi_prot_conds).(full_read_split) with "pFull") as "[pRead pFullAcc]".
          iEval (monPred_simpl) in "exchange".
          iDestruct ("exchange" with "pRead") as ">[Hfi_post pRead]".
          iSpecialize ("pFullAcc" with "pRead").
          iPoseProof (predicate_holds_phi_decode_2 with "[$pFullEquiv] [$]") as "pFull"; first done.
          by iFrame.
          
        - iPoseProof (predicate_holds_phi_decode_1 with "[$pReadEquiv] [$]") as "pRead"; first done.
          iEval (monPred_simpl) in "exchange".
          iDestruct ("exchange" with "pRead") as ">[Hfi_post pRead]".
          iPoseProof (predicate_holds_phi_decode_2 with "[$pReadEquiv] [$]") as "pRead"; first done.
          by iFrame. }
      iModIntro.
      (* deal with postcondition first *)
      iSplitR "Hfi_post"; last first.
      { iDestruct "haveMsg" as %[? ?].
        iApply (monPred_mono with "Hfi_post").
        solve_view_le. }
      iDestruct ("predFRAcc" with "predFR") as "predFR".
      iDestruct ("predFRRest" with "[predFR]") as "$".
      { iExistsN. iFrame. done. }
      (* depends on timestamps, we have two different choices for [global_pview] *)
      destruct (decide (t_p_old ≤ t)).
      - set global_pview' := (global_pview ⊔ {[ fi.(fi_ℓ) := MaxNat (t - offset) ]}).
        iExists global_pview'.
        iSplitR.
        { subst global_pview'.
          rewrite dom_op dom_singleton.
          iPureIntro.
          set_solver. }
        iApply (big_sepM2_delete _ _ _ fi.(fi_ℓ) with "[-]").
        { done. } { done. }
        iSplitL "predP".
        + iExistsN.
          iFrame "∗#%".
          subst global_pview' t_p_old.
          rewrite lookup_zero_lub lookup_op lookup_singleton lookup_zero_singleton -Nat.add_max_distr_l.
          iSplitPure.
          * replace (offset + (t - offset)) with (t) by lia.
            apply Nat.max_r.
            done.
          * unfold lookup_zero in *.
            (* why goal is not substituted automatically? *)
            destruct (global_pview !! fi.(fi_ℓ)) eqn:Heqn; rewrite Heqn; simpl in *.
            -- rewrite Nat.max_r; last lia.
               iApply (persisted_weak with "persisted").
               etrans; first apply haveBV.
               etrans; eassumption.
            -- iApply (persisted_weak with "persisted").
               etrans; first apply haveBV.
               etrans; eassumption.
        + iApply (big_sepM2_impl with "predPRest").
          iIntros "!>" (ℓ' pHist' aHist' Hlook ?) "H".
          assert (global_pview' !!0 ℓ' = global_pview !!0 ℓ') as ->.
          { subst global_pview'.
            rewrite lookup_zero_lub [ {[ _ := _ ]} !!0 _ ]/lookup_zero lookup_singleton_ne; first apply Nat.max_0_r.
            apply lookup_delete_Some in Hlook as [? ?]. done. }
          assert (global_pview' !! ℓ' = global_pview !! ℓ') as ->.
          { subst global_pview'.
            rewrite lookup_op lookup_singleton_ne; first by rewrite right_id.
            apply lookup_delete_Some in Hlook as [? ?]. done. }
          done.
      - iExists global_pview.
        iFrame "#%".
        iApply (big_sepM2_delete _ _ _ fi.(fi_ℓ) with "[predP persistedOld $predPRest]").
        { done. } { done. }
        iExistsN.
        iFrame "∗#%".
        done. }
    iModIntro.
    iNamed "R".
    iSpecialize ("Hpost" with "[] [Hfi_post]").
    { iApply (persisted_weak with "[$]"). by etrans. }
    { by iApply monPred_at_big_sepL. }
    iEval (rewrite monPred_at_wand) in "HΦ".
    iDestruct ("HΦ" with "[] [Hpost]") as "$".
    { iPureIntro. solve_view_le. }
    { iApply monPred_mono; last done.
      split; last solve_view_le.
      split; first solve_view_le.
      f_equiv; solve_view_le. }
    iFrame "val".
    iSplitPure; first solve_view_le.
    rewrite /interp.
    iDestruct "predsP" as (global_pview') "[%histPViewDoms predsPersHold]".
    iExistsN.
    iFrameNamed.
  Qed.
End weakestpre.
