From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import agree auth gset.
From iris.base_logic Require Import ghost_map.
From iris_named_props Require Import named_props.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require crash_weakestpre.

From self Require Import extra.
From self.base Require Import primitive_laws class_instances.
From self.high Require Export dprop resources lifted_modalities monpred_simpl
     post_crash_modality.

Section wpc.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ}.

  (* NOTE: The definition uses [i < j] and not [i ≤ j] in order to make the
  lemma [increasing_map_singleton] provable. When we use [increasing_map] the
  relation [R] will always be reflexive, and hence this does not matter. The
  _knowledge_ that [R] is reflexive may not always be available however (since
  we may not know that [R] is in fact the encoding of some preorder, and hence
  this definition works best. *)
  Definition increasing_map (ss : gmap nat positive) (R : relation2 positive) :=
    ∀ i j (s s' : positive),
      i < j → (ss !! i = Some s) → (ss !! j = Some s') → R s s'.
    (* NB: Add s ≠ s' in the conclusion to make the map strictly increasing. *)

  Lemma increasing_map_singleton t s R : increasing_map {[ t := s ]} R.
  Proof. intros ????? ?%lookup_singleton_Some ?%lookup_singleton_Some. lia. Qed.

  Lemma increasing_map_empty  R : increasing_map ∅ R.
  Proof. intros ????? [=]. Qed.

  (* Convert a message to a thread_view corresponding to what is stored in the
  message. *)
  Definition msg_to_tv (m : message) : thread_view :=
    (* NOTE: We use the [msg_persisted_after_view] and _not_ the
    [msg_persist_view]. This is because the [msg_persisted_after] can be
    transfered to the recovery program after a crash and the predicate then
    still holds. *)
    (m.(msg_store_view), m.(msg_persisted_after_view), ∅).

  Definition encoded_predicate_holds
             (enc_pred : positive → val → option (dProp Σ))
             (enc_state : positive)
             (v : val)
             (TV : thread_view) : iProp Σ :=
    (∃ (P : dProp Σ), ⌜enc_pred enc_state v = Some P⌝ ∗ P TV).

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)
  Definition interp : iProp Σ :=
    (∃ (hists : gmap loc (gmap time (message * positive)))
       (preds : gmap loc (positive → val → option (dProp Σ)))
       (rec_preds : gmap loc (positive → val → option (dProp Σ)))
       (CV : view)
       (orders : gmap loc (relation2 positive))
       (exclusive_locs : gset loc)
       (shared_locs : gset loc),
      (* We keep the points-to predicates to ensure that we know that the keys
      in the abstract history correspond to the physical history. This ensures
      that at a crash we know that the value recoreved after a crash has a
      corresponding abstract value. *)
      "ptsMap" ∷ ([∗ map] ℓ ↦ hist ∈ hists, ℓ ↦h (fst <$> hist)) ∗
      "#crashedAt" ∷ crashed_at CV ∗
      (* Agreement on the preorders and the ordered/sorted property. *)
      "allOrders" ∷ own_all_preorders orders ∗
      "ordered" ∷ ([∗ map] ℓ ↦ hist; order ∈ hists; orders,
                    ⌜increasing_map (snd <$> hist) order⌝) ∗
      (* The predicates hold for all the locations. *)
      "map" ∷
        ([∗ map] ℓ ↦ hist; pred ∈ hists; preds,
          (* The predicate holds for each message in the history. *)
          ([∗ map] t ↦ p ∈ hist, let '(msg, encS) := p in
            encoded_predicate_holds pred encS msg.(msg_val) (msg_to_tv msg))) ∗
      (* The predicates hold for the shared locations. *)
      (*
      "mapShared" ∷
        ([∗ map] ℓ ↦ hist ∈ (restrict shared_locs hists), ∃ pred recPred,
          ⌜preds !! ℓ = Some pred⌝ ∗
          ⌜rec_preds !! ℓ = Some recPred⌝ ∗
          (* The predicate holds for each message in the history. *)
          ([∗ map] t ↦ p ∈ hist, let '(msg, encState) := p in
            (* The recovery predicate holds or the normal perdicate holds. *)
            (⌜t = 0⌝ ∗ ⌜ℓ ∈ dom (gset _) CV⌝ ∗ ∃ (P : dProp Σ),
               ⌜recPred encState msg.(msg_val) = Some P⌝ ∗ P (∅, ∅, ∅)) ∨
            ((⌜t ≠ 0⌝ ∨ ⌜ℓ ∉ dom (gset _) CV⌝) ∗ ∃ (P : dProp Σ),
              ⌜pred encState msg.(msg_val) = Some P⌝ ∗ P (msg_to_tv msg)))) ∗
      *)
      (* Ownership over the full knowledge of the abstract history of _all_
      locations. *)
      "history" ∷ own_full_history ((λ (h : (gmap _ _)), snd <$> h) <$> hists) ∗
      (* Knowledge of all the predicates. *)
      "preds" ∷ own predicates_name (● (preds_to_ra preds)) ∗
      (* Knowledge of all the recovery predicates. *)
      "recPreds" ∷ own recovery_predicates_name (● (preds_to_ra rec_preds)) ∗
      (* We have a recovery predicate for exactly the shared locations. *)
      "%recPredsDom" ∷ ⌜dom _ rec_preds = shared_locs⌝ ∗
      "mapRecPredsImpl" ∷
        ([∗ map] ℓ ↦ recPred ∈ rec_preds, ∃ pred,
          ⌜ preds !! ℓ = Some pred ⌝ ∗
          ∀ encS v, ∃ (P : dProp Σ),
            ⌜pred encS v = Some P⌝ -∗
            ∃ PR, ∀ TV, ⌜recPred encS v = Some PR⌝ ∗ (P -∗ (<PCCC> (λ _, PR))) TV
        ) ∗
      (* Shared locations. *)
      "sharedLocs" ∷ own shared_locs_name (● shared_locs) ∗
      (* Exclusive locations. *)
      (* "exclusiveLocs" ∷ own exclusive_locs_name (● exclusive_locs) ∗ *)
      "%mapShared" ∷
        ⌜map_Forall (λ _, map_Forall
          (* For shared locations the two persist views are equal. This enforces
          that shared locations can only be written to using release load and
          RMW operations. *)
          (λ _ '(msg, _), msg.(msg_persist_view) = msg.(msg_persisted_after_view)))
          (restrict shared_locs hists)⌝).

  Program Definition wpc_def s k E e (Φ : val → dProp Σ) (Φc : dProp Σ) : dProp Σ :=
    (* monPred_objectively Φc ∗ *)
    MonPred (λ V,
      ∀ TV,
        ⌜V ⊑ TV⌝ -∗
        validV (store_view TV) -∗
        interp -∗
        WPC (ThreadState e TV) @ s; k; E {{ λ res,
          let '(ThreadVal v TV') := res return _ in
            ⌜TV ⊑ TV'⌝ ∗ (* The operational semantics always grow the thread
            view, encoding this in the WPC is convenient. *)
            validV (store_view TV') ∗ (Φ v TV') ∗ interp
          }}{{ Φc (∅, ∅, ∅) }}
    )%I _.
  Next Obligation. solve_proper. Qed.

  (* This sealing follows the same ritual as the [wp] in Iris. *)
  Definition wpc_aux : seal (@wpc_def). by eexists. Qed.

  Global Instance expr_wpc : Wpc expr_lang (dProp Σ) stuckness nat :=
    wpc_aux.(unseal).

  Lemma wpc_eq : wpc = wpc_def.
  Proof. rewrite -wpc_aux.(seal_eq). done. Qed.

  Global Instance wpc_ne s k E1 e n :
    Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc s k E1 e).
  Proof.
    rewrite wpc_eq. constructor => V. solve_proper.
  Qed.

  Global Instance wpc_proper s k E1 e :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc s k E1 e).
  Proof.
    rewrite wpc_eq. constructor => V. solve_proper.
  Qed.

  (** The weakest precondition is defined in terms of the crash weakest
  precondition. *)
  Definition wp_def : Wp expr_lang (dProp Σ) stuckness :=
    λ s E e Φ, (WPC e @ s ; 0 ; E {{ Φ }} {{ True }})%I.
  Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
  Definition wp' := wp_aux.(unseal).
  (* Global Arguments wp' {Λ Σ _}. *)
  (* Check wp'. *)
  Global Existing Instance wp'.
  Lemma wp_eq : wp = @wp_def.
  Proof. rewrite -wp_aux.(seal_eq) //. Qed.

  Lemma wpc_bind K s k E1 (e : expr) Φ Φc :
    WPC e @ s; k; E1 {{ v, WPC fill K (of_val v) @ s; k; E1 {{ Φ }} {{ Φc }} }} {{ Φc }}
    ⊢ WPC fill K e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (V).
    iIntros "WP".
    iIntros (TV) "%incl val interp".
    iDestruct ("WP" with "[% //] val interp") as "HI".
    rewrite nvm_fill_fill.
    iApply crash_weakestpre.wpc_bind.
    { apply: ectx_lang_ctx. }
    iApply (wpc_mono with "HI").
    2: { done. }
    iIntros ([v TV']) "(%cinl & val & wpc & interp)".
    iDestruct ("wpc" $! TV' with "[//] val interp") as "HI".
    rewrite nvm_fill_fill.
    simpl. rewrite /thread_of_val.
    iApply (wpc_strong_mono' with "HI"); try auto.
    iSplit.
    2: { iModIntro. iIntros "$". eauto. }
    iIntros ([??]) "[%incl' $]".
    iPureIntro. etrans; eassumption.
  Qed.

  Lemma wp_wpc s k E1 e Φ:
    WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ s ; k ; E1 {{ Φ }} {{ True }}.
  Proof.
    iStartProof (iProp _).
    rewrite wp_eq /wp_def wpc_eq /wpc_def.
    iIntros (?) "H /=". iIntros (TV ?) "??".
    setoid_rewrite (monPred_at_pure ⊥).
    rewrite /crash_weakestpre.wpc_def crash_weakestpre.wpc_eq.
    iIntros (n).
    iApply wpc0_change_k.
    iApply ("H" $! TV with "[% //] [$] [$]").
  Qed.

  (*
  Lemma wpc_wp s k E1 e Φ Φc:
    WPC e @ s ; k ; E1 {{ Φ }} {{ Φc }} ⊢ WP e @ s ; E1 {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def wpc_eq. iIntros "H" (?).
    iApply wpc0_change_k.
    iApply (wpc0_strong_mono with "H"); auto. by apply omega_le_refl.
  Qed.
  *)

  Lemma wpc_strong_mono s1 s2 k1 k2 E1 E2 e Φ Ψ Φc Ψc
        `{!Objective Φc, !Objective Ψc} :
    s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 →
    WPC e @ s1; k1; E1 {{ Φ }} {{ Φc }} -∗
    (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ <disc> (Φc -∗ |C={E2}_k2=> Ψc) -∗
    WPC e @ s2; k2; E2 {{ Ψ }} {{ Ψc }}.
  Proof.
    intros ?? HE.
    rewrite wpc_eq.
    rewrite /wpc_def.
    iStartProof (iProp _). iIntros (tv).
    monPred_simpl. simpl.
    iIntros "wpc".
    iIntros (tv' ?) "conj".
    iIntros (TV ?) "??".
    iSpecialize ("wpc" $! TV with "[%] [$] [$]"); try eassumption.
    { etrans; eassumption. }
    iApply (wpc_strong_mono with "wpc"); try eassumption.
    iSplit.
    - iIntros ([??]) "(%incl & val & phi & int)".
      monPred_simpl.
      iDestruct "conj" as "[conj _]".
      iSpecialize ("conj" $! _).
      monPred_simpl.
      iSpecialize ("conj" $! _ with "[%] phi").
      { etrans. eassumption. eassumption. }
      rewrite ncfupd_unfold_at.
      iMod "conj" as "conj".
      iModIntro.
      iFrame "∗%".
    - monPred_simpl.
      iDestruct ("conj") as "[_ conj]".
      rewrite disc_unfold_at.
      iModIntro.
      iIntros "phi".
      monPred_simpl.
      iSpecialize ("conj" $! tv' with "[% //]").
      rewrite /cfupd.
      iIntros "HC".
      monPred_simpl.
      iSpecialize ("conj" with "[phi]").
      { iApply objective_at. iApply "phi". }
      iSpecialize ("conj" $! tv' with "[% //] [HC]").
      { iApply monPred_at_embed. done. }
      rewrite fupd_level_unfold_at.
      iApply fupd_level_mono; last iApply "conj".
      iApply objective_at.
  Qed.

  Lemma wpc_strong_mono' s1 s2 k1 k2 E1 E2 e Φ Ψ Φc Ψc
        `{!Objective Φc, !Objective Ψc} :
    s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 →
    WPC e @ s1; k1; E1 {{ Φ }} {{ Φc }} -∗
    (∀ v, Φ v ={E2}=∗ Ψ v) ∧ <disc> (Φc -∗ |k2={E2}=> Ψc) -∗
    WPC e @ s2; k2; E2 {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros (???) "? H".
    iApply (wpc_strong_mono with "[$] [-]"); auto.
    iSplit.
    - iDestruct "H" as "(H&_)". iIntros. iMod ("H" with "[$]"). auto.
    - iDestruct "H" as "(_&H)". iModIntro.
      iIntros "HΦc C". iApply "H". iAssumption.
  Qed.

  Lemma ncfupd_wpc s k E1 e Φ Φc `{!Objective Φc} :
    <disc> (cfupd k E1 Φc) ∧ (|NC={E1}=> WPC e @ s; k; E1 {{ Φ }} {{ Φc }}) ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    iIntros "H".
    simpl.
    iIntros (?) "%incl val interp".
    iApply ncfupd_wpc.
    iSplit.
    - iDestruct "H" as "[H _]".
      rewrite disc_unfold_at.
      iModIntro.
      rewrite cfupd_unfold_at.
      iDestruct "H" as ">H".
      iModIntro.
      iApply objective_at.
      iApply "H".
    - iDestruct "H" as "[_ H]".
      rewrite ncfupd_unfold_at.
      iDestruct "H" as ">H".
      iModIntro.
      iApply ("H" with "[//] val interp").
  Qed.

  Lemma wpc_atomic_crash_modality s k E1 e Φ Φc
        `{!AtomicBase StronglyAtomic e, !Objective Φc} :
    <disc> (cfupd k E1 (Φc)) ∧
    (WP e @ s; E1 {{ v, |={E1}=> (|={E1}=>Φ v) ∧ <disc> cfupd k E1 (Φc) }}) ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    iIntros "H".
    simpl.
    iIntros (?) "%incl val interp".
    iApply wpc_atomic_crash_modality.
    iSplit; [iDestruct "H" as "[H _]"|iDestruct "H" as "[_ H]"].
    - rewrite disc_unfold_at. iModIntro.
      rewrite cfupd_unfold_at.
      iMod "H".
      iModIntro.
      iApply objective_at.
      iApply "H".
    - rewrite wp_eq. rewrite /wp_def.
      rewrite wpc_eq. rewrite /wpc_def.
      simpl.
      rewrite crash_weakestpre.wp_eq /crash_weakestpre.wp_def.
      iSpecialize ("H" with "[//] val interp").
      monPred_simpl.
      iApply (wpc_mono with "H"); last done.
      simpl.
      iIntros ([??]) "(? & ? & H & interp)".
      rewrite monPred_at_fupd.
      monPred_simpl.
      iDestruct "H" as ">H".
      (* rewrite monPred_at_and. *)
      iModIntro.
      iSplit; [iDestruct "H" as "[H _]"|iDestruct "H" as "[_ H]"].
      * rewrite monPred_at_fupd.
        iMod "H".
        iModIntro. iSplit; first done. iFrame.
      * rewrite disc_unfold_at.
        iModIntro.
        rewrite cfupd_unfold_at.
        iMod "H".
        iModIntro.
        iApply objective_at.
        iApply "H".
  Qed.

  Lemma wpc_value s k E1 (Φ : val → dProp Σ) (Φc : dProp Σ)
        `{!Objective Φc} (v : val) :
    ((|NC={E1}=> Φ v) : dProp _) ∧
    (<disc> |C={E1}_k=> Φc) ⊢ WPC of_val v @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    simpl.
    iIntros "H".
    iIntros (TV') "%lec hv i".
    iApply (wpc_value _ _ _ _ _ (ThreadVal _ _)).
    iSplit.
    - iFrame. iDestruct "H" as "(H & _)".
      rewrite ncfupd_unfold_at.
      iMod "H" as "H".
      iModIntro.
      iFrame.
      done.
    - iDestruct "H" as "(_ & HO)".
      rewrite disc_unfold_at.
      iModIntro.
      rewrite cfupd_unfold_at.
      rewrite objective_at.
      iFrame.
  Qed.

  Lemma wpc_value' s k E1 Φ Φc `{!Objective Φc} v :
    Φ v ∧ <disc> Φc ⊢ WPC of_val v @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply wpc_value.
    iSplit.
    - iModIntro. iDestruct "H" as "($&_)".
    - iDestruct "H" as "(_&H)". iModIntro. iModIntro. iFrame.
  Qed.

  (** * Derived rules *)

  Lemma wpc_mono s k E1 e Φ Ψ Φc Ψc `{!Objective Φc, !Objective Ψc} :
    (∀ v, Φ v ⊢ Ψ v) →
    (Φc ⊢ Ψc) →
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }} ⊢
    WPC e @ s; k; E1 {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono' with "H"); auto.
    iSplit.
    - iIntros (v) "?". by iApply HΦ.
    - iIntros "!> ? !>". by iApply HΦc.
  Qed.

  Lemma wp_mono s E e Φ Ψ :
    (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
  Proof. intros Hpost. rewrite wp_eq. apply: wpc_mono; done. Qed.

  Lemma wpc_atomic s k E1 e Φ Φc `{!AtomicBase StronglyAtomic e, !Objective Φc} :
    <disc> (|k={E1}=> Φc) ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ <disc> |k={E1}=> Φc }} ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply (wpc_atomic_crash_modality). iApply (bi.and_mono with "H").
    {
      f_equiv.
      iIntros "H HC".
      iFrame "H". }
    iIntros "H".
    iApply (wp_mono with "H"). iIntros (?).
    iIntros "H". iModIntro.
    iApply (bi.and_mono with "H"); auto.
    { f_equiv. iIntros "H HC". eauto. }
  Qed.

  (* Note that this also reverses the postcondition and crash condition, so we
  prove the crash condition first *)
  Lemma wpc_atomic_no_mask s k E1 e Φ Φc
        `{!AtomicBase StronglyAtomic e, !Objective Φc} :
    <disc> Φc ∧ WP e @ s; E1 {{ v, <disc> (|k={E1}=> Φc) ∧ (|={E1}=> Φ v) }} ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
   Proof.
    iIntros "Hc_wp".
    iApply wpc_atomic.
    iSplit.
    - iDestruct "Hc_wp" as "(?&_)". by do 2 iModIntro.
    - iDestruct "Hc_wp" as "[_ Hwp]".
      iApply (wp_mono with "Hwp").
      iIntros (x) "HΦ".
      iSplit.
      + iDestruct "HΦ" as "[_  >HΦc]". eauto.
      + iDestruct "HΦ" as "[HΦ _]". iModIntro. iMod "HΦ". by iModIntro.
  Qed.

End wpc.

