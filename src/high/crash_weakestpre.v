From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import agree auth gset.
From iris_named_props Require Import named_props.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require crash_weakestpre.

From self.algebra Require Import ghost_map.
From self Require Import extra.
From self.base Require Import primitive_laws class_instances.
From self.high Require Export dprop viewobjective resources lifted_modalities monpred_simpl
     post_crash_modality increasing_map state_interpretation wpc_notation.

Section wpc.
  Context `{nvmG Σ}.

  Implicit Types (TV : thread_view).

  Program Definition wpc_def s E e (Φ : val → dProp Σ) (Φc : dProp Σ) : dProp Σ :=
    (* monPred_objectively Φc ∗ *)
    MonPred (λ i,
      let nD := i.2 in
      ∀ TV,
        ⌜ i.1 ⊑ TV ⌝ -∗
        validV (store_view TV) -∗
        crash_weakestpre.wpc s E (ThreadState e TV) (λ res,
          (let '(ThreadVal v TV') := res return _ in
            ⌜TV ⊑ TV'⌝ ∗ (* The operational semantics always grow the thread
            view, encoding this in the WPC is convenient. *)
            validV (store_view TV') ∗ Φ v (TV', nD))
        ) (* interp ∗ *) (Φc (⊥, nD))
        (* WPC (ThreadState e TV) @ s; E {{ λ res, *)
        (*   (let '(ThreadVal v TV') := res return _ in *)
        (*     ⌜TV ⊑ TV'⌝ ∗ (* The operational semantics always grow the thread *)
        (*     view, encoding this in the WPC is convenient. *) *)
        (*     validV (store_view TV') ∗ Φ v TV') *)
        (* }}{{ (* interp ∗ *) Φc ⊥ }} *)
    )%I _.
  Next Obligation.
  Admitted.
    (* solve_proper. Qed. *)

  (* This sealing follows the same ritual as the [wp] in Iris. *)
  Definition wpc_aux : seal (@wpc_def). by eexists. Qed.

  Global Instance expr_wpc : Wpc expr_lang (dProp Σ) stuckness :=
    wpc_aux.(unseal).

  Lemma wpc_eq : wpc = wpc_def.
  Proof. rewrite -wpc_aux.(seal_eq). done. Qed.

  Global Instance wpc_ne s E1 e n :
    Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc s E1 e).
  Proof.
    rewrite wpc_eq. constructor => V. solve_proper.
  Qed.

  Global Instance wpc_proper s E1 e :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc s E1 e).
  Proof.
    rewrite wpc_eq. constructor => V. solve_proper.
  Qed.

  (** The weakest precondition is defined in terms of the crash weakest
  precondition. *)
  Definition wp_def : Wp (dProp Σ) expr val stuckness :=
    λ s E e Φ, (WPC e @ s; E {{ Φ }} {{ True }})%I.
  Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
  Definition wp' := wp_aux.(unseal).
  (* Global Arguments wp' {Λ Σ _}. *)
  (* Check wp'. *)
  Global Existing Instance wp'.
  Lemma wp_eq : wp = @wp_def.
  Proof. rewrite -wp_aux.(seal_eq) //. Qed.

  Lemma wpc_bind K s E1 (e : expr) Φ Φc :
    WPC e @ s; E1 {{ v, WPC fill K (of_val v) @ s; E1 {{ Φ }} {{ Φc }} }}
                     {{ Φc }}
    ⊢ WPC fill K e @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (V).
    iIntros "WP".
    iIntros (TV) "%incl val".
    iDestruct ("WP" with "[% //] val") as "HI".
    rewrite nvm_fill_fill.
    iApply crash_weakestpre.wpc_bind.
    { apply: ectx_lang_ctx. }
    iApply (wpc_mono with "HI").
    2: { done. }
    iIntros ([v TV']) "(%cinl & val & wpc)".
    iDestruct ("wpc" $! TV' with "[//] val") as "HI".
    rewrite nvm_fill_fill.
    simpl. rewrite /thread_of_val.
    iApply (wpc_strong_mono' with "HI"); try auto.
    iSplit.
    2: { iIntros "$". done. }
    iIntros ([??]) "[%inl' $]".
    iPureIntro. etrans; eassumption.
  Qed.

  Lemma wpc_pure_step_later s E1 e1 e2 φ Φ Φc `{!ViewObjective Φc} :
    PureExecBase φ 1 e1 e2 →
    φ →
    ▷ WPC e2 @ s; E1 {{ Φ }} {{ Φc }} ∧ Φc
    ⊢ WPC e1 @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    intros Hexec ?.
    rewrite wpc_eq /wpc_def.
    iModel.
    simpl.
    iIntros "WP".
    iIntros (TV') "%incl val".
    simpl.
    rewrite -crash_weakestpre.wpc_pure_step_later; last done.
    iSplit.
    - iNext. iApply ("WP" with "[//] val").
    - iFrame. iApply view_objective_at. iDestruct "WP" as "[_ $]".
  Qed.

  Lemma wp_wpc s E1 e Φ:
    WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ s ; E1 {{ Φ }} {{ True }}.
  Proof.
    iStartProof (iProp _).
    rewrite wp_eq /wp_def wpc_eq /wpc_def.
    iIntros (?) "H /=". iIntros (TV ?) "?".
    setoid_rewrite (monPred_at_pure ⊥).
    rewrite /crash_weakestpre.wpc_def crash_weakestpre.wpc_eq.
    iIntros (n).
    iApply ("H" $! TV with "[% //] [$]").
  Qed.

  (*
  Lemma wpc_wp s E1 e Φ Φc:
    WPC e @ s ; E1 {{ Φ }} {{ Φc }} ⊢ WP e @ s ; E1 {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def wpc_eq. iIntros "H" (?).
    iApply wpc0_change_k.
    iApply (wpc0_strong_mono with "H"); auto. by apply omega_le_refl.
  Qed.
  *)

  Lemma wpc_strong_mono s1 s2 E1 E2 (e : expr) (Φ Ψ : val → dProp Σ) (Φc Ψc : dProp Σ)
        `{!ViewObjective Φc, !ViewObjective Ψc} :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
    (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ (Φc -∗ |C={E2}=> Ψc) -∗
    WPC e @ s2; E2 {{ Ψ }} {{ Ψc }}%I.
  Proof.
    intros ? HE.
    rewrite wpc_eq.
    rewrite /wpc_def.
    iModel.
    monPred_simpl. simpl.
    iIntros "wpc".
    iIntros ([TV1 ?] [? [= <-]]) "conj".
    simpl.
    iIntros (TV2 ?) "val".
    iSpecialize ("wpc" $! TV2 with "[%] val"); try eassumption.
    { etrans; eassumption. }
    iApply (wpc_strong_mono with "wpc"); try eassumption.
    iSplit.
    - iIntros ([??]) "(%incl & val & phi)".
      monPred_simpl.
      iDestruct "conj" as "[conj _]".
      iSpecialize ("conj" $! _).
      monPred_simpl.
      iSpecialize ("conj" $! _ with "[%] phi").
      { split; last done.
        etrans. eassumption. eassumption. }
      rewrite ncfupd_unfold_at.
      iMod "conj" as "conj".
      iModIntro.
      iFrame "∗%".
    - monPred_simpl.
      iDestruct ("conj") as "[_ conj]".
      iIntros "phi".
      monPred_simpl.
      iSpecialize ("conj" $! (TV1, _) with "[% //]").
      rewrite /cfupd.
      iIntros "HC".
      (* iFrame "interp". *)
      simpl.
      monPred_simpl.
      iSpecialize ("conj" with "[phi]").
      { iApply view_objective_at. iApply "phi". }
      iSpecialize ("conj" $! (TV1, _) with "[% //] [HC]").
      { iApply monPred_at_embed. done. }
      iApply view_objective_at.
      done.
  Qed.

  Lemma wpc_strong_mono' s1 s2 E1 E2 e Φ Ψ Φc Ψc
        `{!ViewObjective Φc, !ViewObjective Ψc} :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WPC e @ s1; E1 {{ Φ }} {{ Φc }} -∗
    (∀ v, Φ v ={E2}=∗ Ψ v) ∧ (Φc ={E2}=∗ Ψc) -∗
    WPC e @ s2; E2 {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros (??) "? H".
    iApply (wpc_strong_mono with "[$] [-]"); auto.
    iSplit.
    - iDestruct "H" as "(H & _)". iIntros. iMod ("H" with "[$]"). auto.
    - iDestruct "H" as "(_ & H)".
      iIntros "HΦc C". simpl. iApply "H". iAssumption.
  Qed.

  Lemma ncfupd_wpc s E1 e Φ Φc `{!ViewObjective Φc} :
    (cfupd E1 Φc) ∧ (|NC={E1}=> WPC e @ s; E1 {{ Φ }} {{ Φc }}) ⊢
    WPC e @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros ([TV ?]).
    iIntros "H".
    simpl.
    iIntros (?) "%incl val".
    iApply ncfupd_wpc.
    iSplit.
    - iDestruct "H" as "[H _]".
      rewrite cfupd_unfold_at.
      iDestruct "H" as ">H".
      iModIntro.
      iFrame.
      iApply view_objective_at.
      iApply "H".
    - iDestruct "H" as "[_ H]".
      rewrite ncfupd_unfold_at.
      iDestruct "H" as ">H".
      iModIntro.
      iApply ("H" with "[//] val").
  Qed.

  Lemma wpc_atomic_crash_modality s E1 e Φ Φc
        `{!AtomicBase StronglyAtomic e, !ViewObjective Φc} :
    (cfupd E1 (Φc)) ∧
    (WP e @ s; E1 {{ v, |={E1}=> (|={E1}=>Φ v) ∧ cfupd E1 (Φc) }}) ⊢
    WPC e @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros ([TV ?]).
    iIntros "H".
    simpl.
    iIntros (?) "%incl val".
    iApply wpc_atomic_crash_modality.
    iSplit; [iDestruct "H" as "[H _]"|iDestruct "H" as "[_ H]"].
    - rewrite cfupd_unfold_at.
      iMod "H".
      iModIntro.
      iFrame.
      iApply view_objective_at.
      iApply "H".
    - rewrite wp_eq. rewrite /wp_def.
      rewrite wpc_eq. rewrite /wpc_def.
      simpl.
      rewrite crash_weakestpre.wp_eq /crash_weakestpre.wp_def.
      iSpecialize ("H" with "[//] val").
      monPred_simpl.
      iApply (wpc_mono with "H"); last naive_solver.
      simpl.
      iIntros ([??]) "(? & ? & H)".
      rewrite monPred_at_fupd.
      monPred_simpl.
      iDestruct "H" as ">H".
      iModIntro.
      iSplit; [iDestruct "H" as "[H _]"|iDestruct "H" as "[_ H]"].
      * rewrite monPred_at_fupd.
        iMod "H".
        iModIntro. iFrame.
      * rewrite cfupd_unfold_at.
        iMod "H".
        iModIntro.
        iFrame.
        iApply view_objective_at.
        iApply "H".
  Qed.

  Lemma wpc_value s E1 (Φ : val → dProp Σ) (Φc : dProp Σ)
        `{!ViewObjective Φc} (v : val) :
    ((|NC={E1}=> Φ v) : dProp _) ∧
    (|C={E1}=> Φc) ⊢ WPC of_val v @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iModel.
    simpl.
    iIntros "H".
    iIntros (TV') "%lec hv".
    iApply (wpc_value _ _ _ _ (ThreadVal _ _)).
    iSplit.
    - iFrame. iDestruct "H" as "(H & _)".
      rewrite ncfupd_unfold_at.
      iMod "H" as "H".
      iModIntro.
      iSplit; first done.
      iApply monPred_mono; last iApply "H".
      done.
    - iDestruct "H" as "(_ & HO)".
      rewrite cfupd_unfold_at.
      rewrite view_objective_at.
      iFrame.
  Qed.

  Lemma wpc_value' s E1 Φ Φc `{!ViewObjective Φc} v :
    Φ v ∧ Φc ⊢ WPC of_val v @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply wpc_value.
    iSplit.
    - iModIntro. iDestruct "H" as "($&_)".
    - iDestruct "H" as "(_&H)". iModIntro. iFrame.
  Qed.

  (** * Derived rules *)

  Lemma wpc_crash_mono stk E1 e Φ Φc Φc' `{!ViewObjective Φc, !ViewObjective Φc'} :
    (Φc' -∗ Φc) -∗
    WPC e @ stk; E1 {{ Φ }} {{ Φc' }} -∗
    WPC e @ stk; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "Hweaken Hwpc".
    iApply (wpc_strong_mono' with "Hwpc"); eauto.
    iSplit; eauto.
    iIntros "Hc'".
    by iApply "Hweaken".
  Qed.

  Lemma wpc_mono s E1 e Φ Ψ Φc Ψc `{!ViewObjective Φc, !ViewObjective Ψc} :
    (∀ v, Φ v ⊢ Ψ v) →
    (Φc ⊢ Ψc) →
    WPC e @ s; E1 {{ Φ }} {{ Φc }} ⊢
    WPC e @ s; E1 {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono' with "H"); auto.
    iSplit.
    - iIntros (v) "?". by iApply HΦ.
    - iIntros "? !>". by iApply HΦc.
  Qed.

  Lemma wpc_mono' s E1 e Φ Ψ Φc Ψc `{!ViewObjective Φc, !ViewObjective Ψc} :
    (∀ v, Φ v -∗ Ψ v) -∗ (Φc -∗ Ψc) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
    WPC e @ s; E1  {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros "H1 H2 H3"; iApply (wpc_strong_mono' with "H3"); auto.
    iSplit.
    - iIntros (v) "?". by iApply "H1".
    - iIntros "? !>". by iApply "H2".
  Qed.

  Lemma wp_mono s E e Φ Ψ :
    (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
  Proof. intros Hpost. rewrite wp_eq. apply: wpc_mono; done. Qed.

  Lemma wpc_atomic s E1 e (Φ : val → dProp Σ) Φc `{!AtomicBase StronglyAtomic e, !ViewObjective Φc} :
    (|={E1}=> Φc) ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ |={E1}=> Φc }} ⊢
    WPC e @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply (wpc_atomic_crash_modality). iApply (bi.and_mono with "H").
    { iIntros "H HC". iFrame "H". }
    iIntros "H".
    iApply (wp_mono with "H"). iIntros (?).
    iIntros "H". iModIntro.
    iApply (bi.and_mono with "H"); auto.
    { iIntros "H HC". eauto. }
  Qed.

  (* Note that this also reverses the postcondition and crash condition, so we
  prove the crash condition first *)
  Lemma wpc_atomic_no_mask s E1 e Φ Φc
        `{!AtomicBase StronglyAtomic e, !ViewObjective Φc} :
    Φc ∧ WP e @ s; E1 {{ v, (|={E1}=> Φc) ∧ (|={E1}=> Φ v) }} ⊢
    WPC e @ s; E1 {{ Φ }} {{ Φc }}.
   Proof.
    iIntros "Hc_wp".
    iApply wpc_atomic.
    iSplit.
    - iDestruct "Hc_wp" as "(?&_)". by iModIntro.
    - iDestruct "Hc_wp" as "[_ Hwp]".
      iApply (wp_mono with "Hwp").
      iIntros (x) "HΦ".
      iSplit.
      + iDestruct "HΦ" as "[_  >HΦc]". eauto.
      + iDestruct "HΦ" as "[HΦ _]". iMod "HΦ". done.
  Qed.

End wpc.
