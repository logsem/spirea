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

From self Require Import ipm_tactics extra.
From self.lang Require Import lang.
From self.algebra Require Import ghost_map ghost_map_map.
From self.base Require Import cred_frag adequacy. (* To get [recv_adequace]. *)
From self.high Require Import crash_weakestpre resources monpred_simpl.
From self.high Require Import recovery_weakestpre.
(* From Perennial.program_logic Require Export crash_lang recovery_weakestpre. *)
Import uPred.

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

  Context {Σ : gFunctors}.
  Implicit Types s : stuckness.
  Implicit Types Φ : val → dProp Σ.
  Implicit Types Φinv : nvmDeltaG → dProp Σ.
  Implicit Types Φr : nvmDeltaG → val → dProp Σ.
  Implicit Types v : val.
  Implicit Types te : thread_state.
  Implicit Types e : expr.

  (* The assertion [P] holds after [lenght ns] crashes where each execution is
  [ns !! i] many steps. *)
  Fixpoint step_fupdN_fresh `{!nvmG Σ}
           ncurrent (ns : list nat) (hD : nvmDeltaG)
          (P : nvmDeltaG → iProp Σ) {struct ns} :=
    match ns with
    | [] => P hD
    | n :: ns =>
      (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum (num_laters_per_step) (step_count_next)
                                      ncurrent (S n)) ||={∅|∅, ⊤|⊤}=>
      ||={⊤|⊤,∅|∅}=> ||▷=>^1 ||={∅|∅, ⊤|⊤}=>
      ∀ γcrash, NC_name γcrash 1 -∗
      ||={⊤|⊤,∅|∅}=> ||▷=>^1 ||={∅|∅, ⊤|⊤}=>
      |={⊤}=> (∃ hD' : nvmDeltaG,
        ⌜ γcrash = get_crash_name hD' ⌝ ∗
        step_fupdN_fresh ((Nat.iter (S n) step_count_next ncurrent)) ns hD' P))%I
    end.

  Lemma step_fupdN_fresh_wand `{!nvmG Σ} ncurr1 ncurr2 (ns : list nat) hD P Q :
    ncurr1 = ncurr2 →
    step_fupdN_fresh ncurr1 (ns) hD P -∗
    (∀ hD, P hD -∗ Q hD) -∗
    step_fupdN_fresh ncurr2 ns hD Q.
  Proof.
    revert hD ncurr1 ncurr2.
    induction ns => ????.
    - iIntros "H Hwand". iApply "Hwand". eauto.
    - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
      iApply (step_fupd2N_inner_wand with "H"); try auto.
      { subst. auto. }
      iIntros "H".
      iMod "H". iModIntro.
      iApply (step_fupd2N_wand with "H"). iIntros "H".
      iMod "H". iModIntro.
      iIntros (Hc') "HNC". iSpecialize ("H" $! Hc' with "[$]").
      iMod "H". iModIntro.
      iApply (step_fupd2N_wand with "H"). iIntros "H".
      iMod "H". iModIntro.
      iMod "H" as (?) "[? H]".
      iExists _. iModIntro. iFrame. iApply (IHns with "H"). { congruence. }
      iFrame.
  Qed.

  Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

  Lemma wptp_recv_strong_normal_adequacy `{!nvmG Σ, nD : !nvmDeltaG}
        Φ Φr κs' s n (ncurr : nat) mj D r1 e1
        TV1 (t1 : list thread_state) κs t2 σ1 g1 σ2 g2 :
    nrsteps (r1 `at` ⊥) [n] ((e1 `at` TV1) :: t1, (σ1, g1))%TE κs (t2, (σ2, g2)) Normal →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    (* crash_weakestpre.interp -∗ *)
    validV (store_view TV1) -∗
    ((wpr s (* Hc t *) ⊤ e1 r1 Φ (* Φinv *) Φr) ⊥) -∗
    wptp s t1 -∗
    NC 1-∗ (
      (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
      ∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      ▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ncurr))))
          (⌜ ∀ te2, s = NotStuck → te2 ∈ t2 → not_stuck te2 σ2 g2 ⌝) ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
      from_option (λ v, Φ v TV2) True (to_val e2) ∗
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *) (* We don't have post
      conditions for forked threads. *)
      NC 1
    )%I).
  Proof.
    iIntros (Hstep) "Hσ Hg Hv He Ht HNC".
    inversion Hstep. subst.
    (* Find the WPC inside the WPR. *)
    rewrite /wpr wpr_unfold /wpr_pre.
    (* Find the WPC inside the WPC. *)
    iEval (rewrite crash_weakestpre.wpc_eq /=) in "He".
    iSpecialize ("He" $! TV1 with "[%] Hv").
    { destruct TV1 as [[??]?]. repeat split; apply view_empty_least. }
    iDestruct (wptp_strong_adequacy (irisGS0 := (@nvmBase_irisGS Σ (@nvmG_baseG Σ nvmG0)
                   (@nvm_delta_base nD)
                   (@highExtraStateInterp Σ nvmG0 nD))) with "Hσ Hg He Ht") as "H".
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
    iDestruct "HI" as "(_ & _ & $)".
  Qed.

  Lemma wptp_recv_strong_crash_adequacy `{!nvmG Σ}
        Φ Φr κs' s t ncurr mj D (ns : list nat) n r1 e1
        TV1 t1 κs t2 σ1 g1 σ2 g2 :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%E :: t1, (σ1, g1)) κs (t2, (σ2, g2)) Crashed →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    (* crash_weakestpre.interp -∗ *)
    validV (store_view TV1) -∗
    (wpr s ⊤ e1 r1 Φ Φr) ⊥ -∗
    wptp s t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns t (λ hD,
      let ntot := (steps_sum num_laters_per_step step_count_next
                            (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
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
    iIntros (Hsteps) "Hσ Hg Hv He Ht HNC".
    inversion_clear Hsteps as [|? ? [t1' ?] ρ2 ? ? ? ? ? ? step].
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    destruct ρ2 as (? & [σ2_pre_crash []]).
    iEval (rewrite -assoc) in "Hg".

    iEval (rewrite /wpr wpr_unfold /wpr_pre) in "He".
    iEval (rewrite crash_weakestpre.wpc_eq) in "He".
    iSpecialize ("He" $! TV1 with "[%] Hv").
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
    (* iDestruct "H" as "[interp H]". *)
    iEval (repeat setoid_rewrite monPred_at_forall) in "H".
    iEval (setoid_rewrite monPred_at_embed) in "H".
    iDestruct ("H" $! _ _ _ _ step _ 0 with "Hσ Hg") as "H".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo";
      [apply empty_subseteq | apply empty_subseteq|].
    iModIntro.
    iMod ("Hclo") as "_".
    iModIntro.
    iIntros (Hc') "HNC".
    iMod ("H" $! Hc' with "[$]") as (hD') "(%crEq & Hσ & Hg & Hv & Hr & HNC)".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo";
      [apply empty_subseteq | apply empty_subseteq|].
    iModIntro.
    iModIntro.
    iNext.
    iModIntro.
    iMod ("Hclo") as "_".
    iModIntro.
    iModIntro.

    destruct s0. (* Could we do induction on [ns'] instead? *)
    - (* The remaining execution also crashed. *)
      iPoseProof (IH with "Hσ Hg [Hv] Hr [//] HNC") as "H".
      { eauto. }
      { eauto. }
      iExists _. (* iModIntro. *)
      rewrite /sum_crash_steps.
      rewrite Nat_iter_S.
      iSplit; first done.
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
      iExists hD'.
      assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; auto).
      iDestruct (wptp_recv_strong_normal_adequacy with "Hσ Hg [Hv] Hr [] HNC") as "H"; eauto.
      (* iModIntro. *)
      iSplit; first done.
      rewrite /sum_crash_steps.
      rewrite plus_0_r.
      rewrite Nat_iter_S.
      iApply (step_fupd2N_inner_wand with "H"); try set_solver+.
      iIntros "H".
      rewrite -Nat_iter_S Nat_iter_S_r.
      rewrite Nat_iter_add Nat_iter_S_r.
      eauto.
  Qed.

  (* In this lemma we combine [wptp_recv_strong_normal_adequacy] and
  [wptp_recv_strong_crash_adequacy] into a lemma that applies both in the
  absence and presence of crashes. *)
  Lemma wptp_recv_strong_adequacy `{!nvmG Σ} Φ Φr κs' s hD ns mj D n r1 e1 TV1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%TE :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    (* crash_weakestpre.interp -∗ *)
    validV (store_view TV1) -∗
    ((wpr s (* Hc t *) ⊤ e1 r1 Φ Φr) ⊥) -∗
    (* □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗ *)
    wptp s t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns hD (λ hD',
      let ntot := (steps_sum num_laters_per_step step_count_next
                            (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
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
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *)
      NC 1))).
  Proof.
    intros. destruct stat.
    - iIntros.
      iDestruct (wptp_recv_strong_crash_adequacy
                  with "[$] [$] [$] [$] [$]") as "H"; eauto.
      iDestruct ("H" with "[$]") as "H".
      iApply (step_fupdN_fresh_wand with "H"); first auto.
      iIntros (?) "H".
      iApply (step_fupd2N_wand with "H"); auto.
    - iIntros.
      assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; auto).
      rewrite Nat.add_0_r.
      iDestruct (wptp_recv_strong_normal_adequacy
                  with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
      iMod "H". iModIntro.
      iApply (step_fupd2N_wand with "H").
      setoid_rewrite (bi.pure_True (hD = hD) eq_refl).
      setoid_rewrite (left_id (True%I) _ _).
      naive_solver.
  Qed.

End recovery_adequacy.

Lemma step_fupdN_fresh_pattern_fupd' `{H: invGS Σ} n (Q Q': iProp Σ):
  (||={⊤|⊤,∅|∅}=> ||▷=>^n ||={∅|∅, ⊤|⊤}=> Q) -∗ (Q -∗ ||={⊤|⊤, ⊤|⊤}=> Q') -∗
  (||={⊤|⊤,∅|∅}=> ||▷=>^n ||={∅|∅, ⊤|⊤}=> Q').
Proof.
  iIntros "H Hwand". simpl.
  iApply (step_fupd2N_wand with "H").
  iIntros "H".
  iMod "H".
  by iApply "Hwand".
Qed.

(* [step_fupd2N_inner_fupd] from Perennial gives [P] under [k + 1] laters. This
version add an except zero instead of a later which is better and neccessary for
our use case. *)
Lemma step_fupd2N_inner_plain_better `{H: invGS Σ} (k: nat) P D `{PLAIN: !Plain P} :
  (||={⊤|D, ∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|D}=> P) -∗
  ||={⊤|D, ⊤|D}=> ▷^k ◇ P.
Proof.
  iInduction k as [| k] "IH" forall (P PLAIN).
  - rewrite //=. iIntros "H".
    iApply fupd2_plain_mask. do 2 iMod "H".
    by iModIntro.
  - iIntros "H".
    iApply fupd2_plain_mask.
    iMod "H".
    iMod (step_fupd2N_plain with "H") as "H".
    iModIntro. rewrite -!later_laterN !laterN_later.
    iNext. iNext. by iMod "H".
Qed.

(* If you can prove a plain proposition [P] under [step_fupdN_fresh] then the *)
(* proposition holds under only under a number of laters. *)
Lemma step_fupdN_fresh_plain `{!nvmG Σ, hD : nvmDeltaG} P `{!Plain P} ns ncurr k :
  (step_fupdN_fresh ncurr ns _
                 (λ _, ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|⊤}=> P)) -∗
  ||={⊤|⊤, ⊤|⊤}=> ▷ ▷^(k + fresh_later_count num_laters_per_step step_count_next ncurr ns) P.
Proof.
  iIntros "H".
  iInduction ns as [|n' ns] "IH" forall (ncurr hD).
  - rewrite /step_fupdN_fresh Nat.add_0_r.
    by iApply step_fupd2N_inner_plain.
  - iMod NC_alloc_strong as (γcrash) "NC".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    set (num :=
        k + fresh_later_count num_laters_per_step step_count_next
                      (Nat.iter (S n') step_count_next ncurr) ns).
    iDestruct (step_fupdN_fresh_pattern_fupd _ _ _ (▷ ▷^(S num) P)%I with "H [IH NC]") as "H".
    { iIntros "H".
      iSpecialize ("H" with "NC").
      set (num2 := (k +
             fresh_later_count num_laters_per_step step_count_next
               (Nat.iter (S n') step_count_next ncurr) ns)).
      iDestruct (step_fupdN_fresh_pattern_fupd' _ _ (▷^ (S num2) P)%I with "H [IH]") as "H".
      { iIntros "H".
        iMod "H".
        iDestruct "H" as (hD' eq) "H".
        iMod ("IH" with "H") as "H".
        iModIntro.
        iApply "H". }
      iPoseProof (step_fupd2N_inner_plain_better with "H") as "H".
      iMod "H". iModIntro.
      rewrite except_0_later.
      rewrite -later_laterN.
      iApply "H". }
    rewrite step_fupd2N_inner_plus.
    iPoseProof (step_fupd2N_inner_plain_better with "H") as "H".
    iMod "H". iModIntro.
    rewrite except_0_later.
    rewrite -?laterN_later.
    rewrite -?laterN_plus.
    rewrite -later_laterN.
    iApply (laterN_le with "H").
    { rewrite /num. simpl. lia. }
Qed.

Lemma step_fupdN_fresh_soundness `{!nvmGpreS Σ} φ ns ncurr k k2 :
  (⊢ ∀ (Hi : invGS Σ),
    |={⊤}=> ∃ (nF : nvmG Σ) (nD : nvmDeltaG),
      (* ⌜ num_laters_per_step = f ⌝ ∗ *)
      (* ⌜ step_count_next = g ⌝ ∗ *)
      ⌜ nvmBaseG_invGS = Hi ⌝ ∗
      step_fupdN_fresh ncurr ns _
        (λ _, ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|⊤}=> ▷^k2 ⌜φ⌝))%I →
  φ.
Proof.
  intros iter.
  eapply (soundness (M := iResUR Σ) _ (S (_) + k2)).
  iApply (fupd2_plain_soundness ⊤ ⊤ ⊤ ⊤).
  iIntros (inv).
  rewrite laterN_plus.
  iMod (iter $! inv) as (nF nD (* _ _ *) eqInv) "it".
  iDestruct (step_fupdN_fresh_plain _ ns ncurr k) as "H".
  Set Printing All.
  rewrite -eqInv.
  simpl.
  assert ((@iris_invGS nvm_lang Σ (@nvmBase_irisGS Σ (@nvmG_baseG Σ nF)
                                  (@nvm_delta_base _) _)) =
          (@nvmBaseG_invGS Σ (@nvmG_baseG Σ nF))) as ->.
  { done. }
  Unset Printing All.
  iApply "H".
  iApply "it".
  Unshelve.
  apply _.
Qed.

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

Lemma allocate_high_state_interp `{!nvmGpreS Σ} Hinv σ PV κs :
  valid_heap σ →
  ⊢ |={⊤}=> ∃ (nF : nvmG Σ) (nD : nvmDeltaG),
      ⌜ nvmBaseG_invGS = Hinv ⌝ ∗
      interp ∗
      validV ∅ ∗
      NC 1 ∗
      global_state_interp (Λ := nvm_lang) () crash_borrow_ginv_number 1%Qp ∅ κs ∗
      nvm_heap_ctx (σ, PV).
Proof.
  intros valid.
  iMod NC_alloc_strong as (γcrash) "NC".
  (* assert (hi : cr_names). first apply _. *)

  set (n := 0).
  iMod (credit_name_init (n * 4 + crash_borrow_ginv_number)) as
      (name_credit) "([credfull credfrag] & Hcred & Htok)".
  iDestruct (cred_frag_split with "Hcred") as "(Hpre&Hcred)".
  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }

  iMod (allocate_state_interp Hinv _ γcrash σ PV name_credit)
    as (names) "(%crEq & ctx & Ha & #valid & crashedAt & Hc)";
    first eassumption.
  (* set (base := (NvmFixedG _ (nvm_build_base _ _ Hinv _) _)). *)
  set (fixed := NvmFixedG _ (nvm_build_base _ _ Hinv _ name_credit) nvmPreG_high).
  iExists (fixed).
  (* Unshelve. *)
  (* Allocate abstract history. *)
  iMod (full_map_alloc ∅)
    as (abs_history_name) "(hists' & _ & _)".
  (* Allocate predicates. *)
  iMod (know_predicates_alloc ∅) as (predicates_name) "[preds #predsFrag]".
  (* Allocate preorders. *)
  iMod (own_all_preorders_gname_alloc ∅) as (orders_name) "[orders #fragOrders]".
  (* Allocate set of atomic locations. *)
  iMod (own_alloc (● (∅ : gsetUR _))) as (shared_locs_name) "atLocs".
  { apply auth_auth_valid. done. }
  (* Allocate set of non-atomic locations.. *)
  iMod (own_alloc (● (∅ : gsetUR _))) as (exclusive_locs_name) "naLocs".
  { apply auth_auth_valid. done. }
  (* iMod ghost_map.ghost_map_alloc_empty as (na_views_name) "na_views". *)
  iMod (ghost_map_alloc (∅ : gmap loc view)) as (na_views_name) "(na_views & _)".
  iMod (ghost_map_alloc (∅ : gmap loc positive)) as (crashed_in_name) "(crashedIn & _)".
  iMod (own_all_bumpers_alloc ∅) as (bumpers_name) "[bumpers #bumpersFrag]".
  iMod (auth_map_map_alloc ∅) as (phys_hist_name) "[physHist _]".

  set (hD := {|
               abs_history_name := abs_history_name;
               know_phys_history_name := phys_hist_name;
               non_atomic_views_gname := na_views_name;
               crashed_in_name := crashed_in_name;
               predicates_name := predicates_name;
               preorders_name := orders_name;
               shared_locs_name := shared_locs_name;
               exclusive_locs_name := exclusive_locs_name;
               bumpers_name := bumpers_name;
             |}).
  iExists (NvmDeltaG _ hD).
  iModIntro.
  iPureGoal. { done. }
  simpl.
  iFrame "valid ctx Hinv".
  rewrite crEq. iFrame "NC".
  iFrame.
  rewrite /cred_interp.
  iPureGoal; first done.
  rewrite /interp.
  repeat iExists ∅.
  simpl.
  iFrame.
  iEval (rewrite !big_sepM2_empty).
  iEval (rewrite !big_sepM_empty).
  rewrite !left_id.

  iPureIntro.
  split_and!; try done; set_solver.
Qed.

(* This adequacy lemma is similar to the adequacy lemma for [wpr] in Perennial:
[wp_recv_adequacy_inv]. *)
Lemma high_recv_adequacy Σ `{hPre : !nvmGpreS Σ} s e r σ PV (φ φr : val → Prop) :
  valid_heap σ →
  (∀ `{nF : !nvmG Σ, nD : !nvmDeltaG},
    ⊢ (* ⎡ ([∗ map] l ↦ v ∈ σ.1, l ↦h v) ⎤ -∗ *)
      (* Note: We need to add the resources that can be used to prove the [wpr]
      includin [pre_borrow]. These should require the user to decide which
      locations should be shared/exclusive, location invariants, etc. *)
      (wpr s ⊤ e r (λ v, ⌜ φ v ⌝) (λ _ v, ⌜ φr v ⌝))) →
  recv_adequate s (ThreadState e ⊥) (ThreadState r ⊥) (σ, PV)
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
  (* Very beautiful! *)
  eset (n'' :=
          S (S (3 ^ (Nat.iter (n' + sum_crash_steps ns')
                    (λ n0 : nat,
                       n0 + 1 +
                       (n0 + 1 +
                        (n0 + 1 +
                         (n0 + 1 +
                          (n0 + 1 +
                           (n0 + 1 +
                            (n0 + 1 + (n0 + 1 + (n0 + 1 + (n0 + 1 + 0))))))))))
                    nsinit + 1)))).
  (* We apply soundness of Perennial/Iris. *)
  eapply (step_fupdN_fresh_soundness _ ns' nsinit _ n'').
  iIntros (inv).

  iMod (credit_name_init (n * 4 + crash_borrow_ginv_number)) as
      (name_credit) "(Hcred_auth&Hcred&Htok)".
  iDestruct (cred_frag_split with "Hcred") as "(Hpre&Hcred)".
  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  
  iMod (allocate_high_state_interp inv σ PV [])
    as (nF nD eq) "(high & validV & nc & global & int)"; first done.

  iDestruct (Hwp _ _ ) as "-#Hwp".
  iDestruct ("Hwp" $! (∅, ∅, ∅)) as "Hwpr".
  iModIntro.
  iExists _, _.
  iPureGoal. { done. }
  iDestruct (wptp_recv_strong_adequacy _ _ [] with "[$int $high] global") as "HIP".
  { done. }
  iSpecialize ("HIP" with "validV Hwpr [//] nc").

  iApply (step_fupdN_fresh_wand with "HIP").
  { auto. }
  iIntros (hD).
  iIntros "H".
  rewrite -eq.
  iMod "H".
  simpl.
  iApply (step_fupd2N_wand with "H"); auto.
  iModIntro. iIntros "H".
  iMod "H" as (v2 TV2 ts2 ->) "(stuck & interp & global & HIP & nc)".
  destruct stat.
  - iDestruct "HIP" as "#HIP".
    iModIntro.
    do 3 iNext.
    iSplit; last naive_solver.
    by iIntros (? ? [= ->]).
  - iDestruct "HIP" as "[%eq'' #HIP]".
    iModIntro.
    do 3 iNext.
    iSplit; last naive_solver.
    by iIntros (? ? [= ->]).
Qed.
