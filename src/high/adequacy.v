(* The adequacy result for our recovery weakest precondition [wpr]. *)

(* Notes: Our [wpr] is defined on top of our [wpc] which is defined on top of
Perennial's [wpc]. As such, our [wpr] is not an instantiation of Perennial's
[wpr]. Therefore we can't use adequacy of Perennial's [wpr] to show adequacy of
our [wpr]. *)

From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.

From Perennial.program_logic Require Import recovery_adequacy.
From Perennial.program_logic Require Import step_fupd_extra crash_lang crash_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.

From self Require Import ipm_tactics.
From self.lang Require Import lang.
From self.base Require Import adequacy. (* To get [recv_adequace]. *)
From self.high Require Import weakestpre resources monpred_simpl.
From self.high Require Import recovery_weakestpre.
(* From Perennial.program_logic Require Export crash_lang recovery_weakestpre. *)

Notation steps_sum := crash_adequacy.steps_sum.

Definition nrsteps := nrsteps (CS := nvm_crash_lang).
Arguments nrsteps _%TE _ _%TE _ _ _.

Lemma nrsteps_crashed_length_status r ns ρ1 κ ρ2 s:
  nrsteps r ns ρ1 κ ρ2 s → (length ns ≥ 2 ↔ s = Crashed).
Proof.
 inversion 1.
 - simpl. split; [lia| done].
 - split; first done.
    match goal with
    | [ H : crash_lang.nrsteps _ _ _ _ _ _ |- _ ] => inversion H
    end; simpl; lia.
Qed.

Lemma nrsteps_crashed_length r ns ρ1 κ ρ2:
  nrsteps r ns ρ1 κ ρ2 Crashed → length ns ≥ 2.
Proof. intros ?%nrsteps_crashed_length_status. naive_solver. Qed.

Section recovery_adequacy.

  Context `{!nvmFixedG Σ}.
  Implicit Types s : stuckness.
  Implicit Types k : nat.
  (* Implicit Types P : iProp Σ. *)
  Implicit Types Φ : val → dProp Σ.
  Implicit Types Φinv : nvmDeltaG Σ → dProp Σ.
  Implicit Types Φr : nvmDeltaG Σ → val → dProp Σ.
  Implicit Types v : val.
  Implicit Types te : thread_state.
  Implicit Types e : expr.

  (* The assertion [P] holds after [lenght ns] crashes where each execution is
  [ns !! i] many steps.

  Note: The new [crashGS] that is created after each crash may note be handles
  correctly, yet, in this definition. Maybe we should state that the [nvmDeltaG]
  must use the given [crashGS]. Maybe we can avoid mentioning a crashGS and just
  use nvmDeltaG. *)
  Fixpoint step_fupdN_fresh ncurrent (ns : list nat) (Hc0 : crashGS Σ) (hD : nvmDeltaG Σ)
          (P : nvmDeltaG Σ → iProp Σ) {struct ns} :=
    match ns with
    | [] => P hD
    | n :: ns =>
      (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum (perennial_num_laters_per_step) (perennial_step_count_next)
                                      ncurrent (S n)) ||={∅|∅, ⊤|⊤}=>
      ||={⊤|⊤,∅|∅}=> ||▷=>^2 ||={∅|∅, ⊤|⊤}=>
      ∀ Hc', NC 1 ={⊤}=∗ (∃ hD' : nvmDeltaG Σ, step_fupdN_fresh ((Nat.iter (S n) step_count_next ncurrent)) ns Hc' hD' P))%I
    end.

  Lemma step_fupdN_fresh_wand ncurr1 ncurr2 (ns : list nat) Hc0 hD Q Q' :
    ncurr1 = ncurr2 →
    step_fupdN_fresh ncurr1 (ns) Hc0 hD Q -∗
    (∀ hD, Q hD -∗ Q' hD) -∗
    step_fupdN_fresh ncurr2 ns Hc0 hD Q'.
  Proof.
    revert Hc0 hD ncurr1 ncurr2.
    induction ns => ?????.
    - iIntros "H Hwand". iApply "Hwand". eauto.
    - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
      iApply (step_fupd2N_inner_wand with "H"); try auto.
      { subst. auto. }
      iIntros "H".
      iMod "H". iModIntro. iApply (step_fupd2N_wand with "H"). iIntros "H".
      iMod "H". iModIntro.
      iIntros (Hc') "HNC". iSpecialize ("H" $! Hc' with "[$]"). iMod "H" as (?) "H".
      iExists _. iModIntro. iApply (IHns with "H").
      { subst. auto. }
      eauto.
  Qed.

  Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

  Lemma wptp_recv_strong_normal_adequacy `{!nvmDeltaG Σ} Φ Φr κs' s k n (ncurr : nat) mj D r1 e1
        TV1 (t1 : list thread_state) κs t2 σ1 g1 σ2 g2 :
    nrsteps (r1 `at` ⊥) [n] ((e1 `at` TV1) :: t1, (σ1, g1))%TE κs (t2, (σ2, g2)) Normal →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    crash_weakestpre.interp -∗
    validV (store_view TV1) -∗
    ((wpr s k (* Hc t *) ⊤ e1 r1 Φ (* Φinv *) Φr) ⊥) -∗
    wptp s k t1 -∗
    NC 1-∗ (
      (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
      ∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      ▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ncurr))))
          (⌜ ∀ te2, s = NotStuck → te2 ∈ t2 → not_stuck te2 σ2 g2 ⌝) ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
      from_option (λ v, Φ v TV2) True (to_val e2) ∗
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *) (* FIXME *)
      NC 1
    )%I).
  Proof.
    iIntros (Hstep) "Hσ Hg Hi Hv He Ht HNC".
    inversion Hstep. subst.
    (* Find the WPC inside the WPR. *)
    rewrite /wpr wpr_unfold /wpr_pre.
    (* Find the WPC inside the WPC. *)
    iEval (rewrite crash_weakestpre.wpc_eq /=) in "He".
    iSpecialize ("He" $! TV1 with "[%] Hv Hi").
    { destruct TV1 as [[??]?]. repeat split; apply view_empty_least. }
    iDestruct (wptp_strong_adequacy with "Hσ Hg He Ht") as "H".
    { eauto. }
    iSpecialize ("H" with "HNC").
    iApply (step_fupd2N_wand with "H"); first auto.
    iApply fupd2_mono.
    iIntros "(%ts2 & % & % & PIZ & ZA & PEPPERONI & HI & horse & NC)".
    destruct ts2 as [e2 TV2].
    iExists e2, TV2, _.
    iFrame.
    iSplit. { iPureIntro. done. }
    simpl.
    rewrite /thread_to_val.
    simpl.
    destruct (to_val e2); last done.
    simpl.
    iDestruct "HI" as "(_ & _ & _ & $)".
  Qed.

  Lemma wptp_recv_strong_crash_adequacy Φ Φr κs' s k t ncurr mj D (ns : list nat) n r1 e1
        TV1 t1 κs t2 σ1 g1 σ2 g2 :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%E :: t1, (σ1, g1)) κs (t2, (σ2, g2)) Crashed →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    crash_weakestpre.interp -∗
    validV (store_view TV1) -∗
    ((wpr s k (* Hc t *) ⊤ e1 r1 Φ Φr) ⊥) -∗
    wptp s k t1 -∗ NC 1 -∗
    step_fupdN_fresh ncurr ns _ t (λ hD,
      let ntot := (steps_sum perennial_num_laters_per_step perennial_step_count_next
                            (Nat.iter (sum_crash_steps ns) perennial_step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) perennial_step_count_next ncurr)) in
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      ▷^(S (S (num_laters_per_step $ ntot')))
          (⌜ ∀ te, s = NotStuck → te ∈ t2 → not_stuck te σ2 g2⌝) ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 ntot' mj D κs' ∗
      from_option (λ v, Φr hD v TV2) True (to_val e2) ∗
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *)
      NC 1))).
  Proof.
    (* We do induction on the length of [ns]. *)
    revert t e1 TV1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    induction ns as [|n' ns' IH] => hD e1 TV1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    { (* In the base case we've taken [n] steps but there is no crash, this is a
      contradiction as we assume the status is [Crashed]. *)
      rewrite app_nil_l.
      intros Hgt%nrsteps_crashed_length.
      simpl in Hgt. lia. }
    iIntros (Hsteps) "Hσ Hg Hi Hv He Ht HNC".
    inversion_clear Hsteps as [|?? [t1' ?] ????? s0].
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    destruct ρ2 as (?&[σ2_pre_crash []]).
    iEval (rewrite -assoc) in "Hg".

    iEval (rewrite /wpr wpr_unfold /wpr_pre) in "He".
    iEval (rewrite crash_weakestpre.wpc_eq) in "He".
    iSpecialize ("He" $! TV1 with "[%] Hv Hi").
    { destruct TV1 as [[??]?]. repeat split; apply view_empty_least. }
    rewrite Nat_iter_S.
    iDestruct (wptp_strong_crash_adequacy with "Hσ Hg He Ht") as "H"; eauto.
    iSpecialize ("H" with "HNC").
    iMod "H". iModIntro.
    iApply (step_fupd2N_wand with "H").
    iIntros "H".
    iMod "H".
    iModIntro. iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
    iModIntro. iModIntro. iNext.
    iMod ("Hclo") as "_".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo";
      [apply empty_subseteq | apply empty_subseteq|].
    iMod ("Hclo") as "_".
    iDestruct "H" as (e2 t2' ?) "(H & Hσ & Hg & HC)".
    iDestruct "H" as "[interp H]".
    iEval (repeat setoid_rewrite monPred_at_forall) in "H".
    iEval (setoid_rewrite monPred_at_embed) in "H".
    iMod ("H" $! _ _ _ _ _ _ 0 with "interp Hσ Hg") as "H".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo";
      [apply empty_subseteq | apply empty_subseteq|].
    do 2 iModIntro. iNext.
    iModIntro.
    iMod ("Hclo") as "_".
    iModIntro.

    destruct s0. (* Could we do induction on [ns'] instead? *)
    - (* The remaining execution also crashed. *)
      iIntros (Hc') "HNC".
      iMod ("H" $! Hc' with "[$]") as (hD') "(interp & Hσ & Hg & Hv & Hr & HNC)".
      assert (Hc' = @nvm_base_crashGS Σ (@nvm_delta_base Σ hD')) as eq.
      { admit. }
        (* We need [Hc' = @nvm_base_crashGS Σ (@nvm_delta_base Σ hD')] *)
      iPoseProof (IH with "Hσ Hg interp [Hv] Hr [] [HNC]") as "H"; eauto.
      { Set Printing Implicit.
        rewrite eq. iFrame.
        Unset Printing Implicit. }
      iExists _. iModIntro.
      rewrite /sum_crash_steps.
      rewrite Nat_iter_S.
      rewrite eq.
      iApply (step_fupdN_fresh_wand with "H").
      { done. }
      iIntros (?) "H".
      iMod "H". iModIntro.
      rewrite {1}plus_comm Nat_iter_add.
      rewrite -Nat_iter_S Nat_iter_S_r.
      iApply step_fupd2N_le; last iApply (step_fupd2N_wand with "H").
      { apply Nat.eq_le_incl. f_equal.
        rewrite {1}plus_comm ?Nat_iter_add.
        f_equal. rewrite -Nat_iter_S_r //. }
      iIntros ">H".
      rewrite {1}plus_comm ?Nat_iter_add.
      iDestruct "H" as (??? Heq) "(H1 & ? & Hg & ? & ?)".
      iExists _, _, _. iFrame "∗".
      iSplitL ""; first eauto.
      iSplitL "H1".
      { iModIntro. iNext. iNext. iApply (bi.laterN_le with "H1"); auto.
        apply Nat.eq_le_incl. f_equal.
        rewrite -?Nat_iter_S_r -?Nat_iter_add.
        f_equal. lia. }
      iMod (global_state_interp_le with "Hg") as "$".
      { apply Nat.eq_le_incl.
        rewrite -?Nat_iter_S_r -?Nat_iter_add.
        f_equal. lia. }
      iModIntro; done.
    - (* The remaining execution did not crash. This is a "base case" of sorts. *)
      iIntros (Hc') "HNC".
      iMod ("H" $! Hc' with "[$]") as (hD') "(interp & Hσ & Hg & Hv & Hr & HNC)".
      iExists hD'.
      assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; auto).
      iDestruct (wptp_recv_strong_normal_adequacy with "Hσ Hg interp [Hv] Hr [] [HNC]") as "H"; eauto.
      { admit. }
      iModIntro.
      rewrite /sum_crash_steps.
      rewrite plus_0_r.
      rewrite Nat_iter_S.
      iApply (step_fupd2N_inner_wand with "H"); try set_solver+.
      iIntros "H".
      rewrite -Nat_iter_S Nat_iter_S_r.
      rewrite Nat_iter_add Nat_iter_S_r.
      eauto.
  Admitted.

  (* In this lemma we combine [wptp_recv_strong_normal_adequacy] and
  [wptp_recv_strong_crash_adequacy] into a lemma that applies both in the
  absence and presence of crashes. *)
  Lemma wptp_recv_strong_adequacy Φ Φr κs' s k hD ns mj D n r1 e1 TV1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%TE :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    crash_weakestpre.interp -∗
    validV (store_view TV1) -∗
    ((wpr s k (* Hc t *) ⊤ e1 r1 Φ Φr) ⊥) -∗
    (* □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗ *)
    wptp s k t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns _ hD (λ hD',
      let ntot := (steps_sum perennial_num_laters_per_step perennial_step_count_next
                            (Nat.iter (sum_crash_steps ns) perennial_step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) perennial_step_count_next ncurr)) in
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      ▷^(S (S (num_laters_per_step $ ntot')))
          (⌜ ∀ te, s = NotStuck → te ∈ t2 → not_stuck te σ2 g2 ⌝) ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 ntot' mj D κs' ∗
      (match stat with
       | Normal =>
          ⌜ (* Hc' = Hc ∧ *) hD' = hD ⌝ ∗
          (* from_option Φ True (to_val e2) *)
          from_option (λ v, Φ v TV2) True (to_val e2)
       | Crashed =>
          from_option (λ v, Φr hD' v TV2) True (to_val e2)
           (* from_option (Φr Hc' t') True (to_val e2) ∗ □ Φinv' Hc' t' *)
      end)  ∗
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *) (* FIXME: Fix this *)
      NC 1))).
  Proof.
    intros. destruct stat.
    - iIntros.
      iDestruct (wptp_recv_strong_crash_adequacy
                  with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
      iDestruct ("H" with "[$]") as "H".
      iApply (step_fupdN_fresh_wand with "H"); first auto.
      iIntros (?) "H".
      iApply (step_fupd2N_wand with "H"); auto.
      (* iIntros "H". *)
      (* iMod "H" as (???) "(#? & H & ? & ? & ? & ?)". iExists _, _, _. *)
      (* repeat (iSplitL ""; try iFrame; eauto). *)
      (* Set Printing Implicit. *)
      (* admit. *)
    - iIntros.
      assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; auto).
      rewrite Nat.add_0_r.
      iDestruct (wptp_recv_strong_normal_adequacy
                  with "[$] [$] [$] [$] [$] [$] [$]") as "H"; eauto.
      iMod "H". iModIntro.
      iApply (step_fupd2N_wand with "H").
      setoid_rewrite (bi.pure_True (hD = hD) eq_refl).
      setoid_rewrite (left_id (True%I) _ _).
      naive_solver.
  Qed.

End recovery_adequacy.

(* An alternative representation of [recv_adequate] that can be more convenient
to show. *)
Lemma recv_adequate_alt s e1 r1 σ1 (φ φr : thread_val → _ → Prop) :
  recv_adequate s e1 r1 σ1 φ φr ↔ ∀ t2 σ2 stat,
    erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1,())) (t2, (σ2,())) stat →
      (∀ v2 t2', t2 = thread_of_val v2 :: t2' →
                 match stat with
                   | Normal => φ v2 σ2
                   | Crashed => φr v2 σ2
                 end) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (thread_to_val e2) ∨ reducible e2 σ2 ())).
Proof.
  split.
  - intros [] ?? []; try naive_solver.
  - constructor; naive_solver.
Qed.

(* This adequacy lemma is similar to the adequacy lemma for [wpr] in Perennial:
[wp_recv_adequacy_inv]. *)
Lemma high_recv_adequacy (Σ : gFunctors) s k e r σ (φ φr : val → Prop) :
  valid_heap σ.1 →
  (∀ `{nF : !nvmFixedG Σ, nD : !nvmDeltaG Σ},
    ⊢ (* ⎡ ([∗ map] l ↦ v ∈ σ.1, l ↦h v) ⎤ -∗ *)
      (wpr s k ⊤ e r (λ v, ⌜φ v⌝) (λ _ v, ⌜φr v⌝))) →
  recv_adequate s (ThreadState e ε) (ThreadState r ε) σ
                (λ v _, φ v.(val_val)) (λ v _, φr v.(val_val)).
Proof.
  intros val.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 stat.
  intros [n [κs nstep]]%erased_rsteps_nrsteps.
  destruct (nrsteps_snoc _ _ _ _ _ _ nstep) as (ns' & n' & ->).
  set (n := 0).
  set (nsinit := (n * 4 + crash_borrow_ginv_number)).
  (* We apply soundness of Perennial/Iris. *)
(* Notation "||={ E1a | E1b }=> Q" := (uPred_fupd2 E1a E1b E1a E1b Q) : bi_scope *)
  eapply (step_fupdN_fresh_soundness (Λ := nvm_lang) (CS := nvm_crash_lang) (Σ := Σ)
              _ ns' nsinit
              (crash_adequacy.steps_sum _ _ (Nat.iter (sum_crash_steps ns') _ nsinit) n')
               (S (S (_ (Nat.iter (n' + sum_crash_steps ns') _ nsinit)))))
         => Hinv Hc.
  (* iStartProof (dProp _). *)
  (* iStartProof (iProp _). *)
  iIntros "HNC".
  iDestruct (Hwp _ _ ) as "-#Hwp".
  (* rewrite /wpr /wpr'. *)
  iDestruct ("Hwp" $! (∅, ∅, ∅)) as "Hwpr".
  iModIntro.
  (* set (pG := PerennialG _ _ nvm_base_names). *)
  (* iExists pG. *)
Admitted.
