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
From Perennial.Helpers Require Import ipm.

From self Require Import ipm_tactics extra encode_relation view_slice.
From self.lang Require Import lang.
From self.algebra Require Import ghost_map ghost_map_map.
From self.base Require Import cred_frag crash_borrow adequacy. (* To get [recv_adequace]. *)
From self.high Require Import dprop_liftings crash_borrow.
From self.high Require Import crash_weakestpre resources monpred_simpl.
From self.high Require Import recovery_weakestpre locations protocol.
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
  Implicit Types Φinv : dProp Σ.
  Implicit Types Φr : val → dProp Σ.
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
      (£ (steps_sum (num_laters_per_step) (step_count_next) ncurrent (S n)) -∗
       ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum (num_laters_per_step) (step_count_next)
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
    induction ns => ??? Hncurr.
    - iIntros "H Hwand". iApply "Hwand". eauto.
    - iIntros "H Hwand Hlc". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
      rewrite {1}Hncurr.
      iSpecialize ("H" with "Hlc").
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
    ((wpr s (* Hc t *) ⊤ e1 r1 Φ (* Φinv *) Φr) (⊥, nD)) -∗
    wptp s t1 -∗
    NC 1 -∗ (
      (£ (steps_sum num_laters_per_step step_count_next ncurr n) -∗
       ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
      ∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      (* ▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ncurr)))) *)
      (*     (⌜ ∀ te2, s = NotStuck → te2 ∈ t2 → not_stuck te2 σ2 g2 ⌝) ∗ *)
      state_interp σ2 (length t2') ∗
      global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
      from_option (λ v, Φ v (TV2, nD)) True (to_val e2) ∗
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *) (* We don't have post
      conditions for forked threads. *)
      NC 1
    )%I).
  Proof.
    iIntros (Hstep) "Hσ Hg Hv He Ht HNC Hcred".
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
    iSpecialize ("H" with "HNC Hcred").
    iApply (step_fupd2N_wand with "H"); first auto.
    iApply fupd2_mono.
    iIntros "(%ts2 & % & % & PIZ & ZA & HI & ? & NC)".
    destruct ts2 as [e2 TV2].
    iExists e2, TV2, _.
    iFrame.
    iSplit. { iPureIntro. done. }
    (* iIntros "Hlc". iSpecialize ("H" with "Hlc"). *)
    simpl.
    rewrite /thread_to_val.
    simpl.
    destruct (to_val e2); last done.
    simpl.
    iDestruct "HI" as "(_ & _ & $)".
  Qed.

  Lemma wptp_recv_strong_crash_adequacy `{!nvmG Σ}
        Φ Φr κs' s t ncurr mj D (ns : list nat) n r1 e1 TV1 t1 κs t2 σ1 g1 σ2 g2 :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%E :: t1, (σ1, g1)) κs (t2, (σ2, g2)) Crashed →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    (* crash_weakestpre.interp -∗ *)
    validV (store_view TV1) -∗
    (wpr s ⊤ e1 r1 Φ Φr) (⊥, _) -∗
    wptp s t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns t (λ hD,
      let ntot := (steps_sum num_laters_per_step step_count_next
                            (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ ntot -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      (* ▷^(S (S (num_laters_per_step $ ntot'))) *)
      (*     (⌜ ∀ te, s = NotStuck → te ∈ t2 → not_stuck te σ2 g2⌝) ∗ *)
      state_interp σ2 (length t2') ∗
      global_state_interp g2 ntot' mj D κs' ∗
      from_option (λ v, Φr v (TV2, hD)) True (to_val e2) ∗
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
    rewrite Nat.iter_succ.
    iIntros "Hlc".
    iDestruct (wptp_strong_crash_adequacy with "Hσ Hg He Ht HNC Hlc") as "H"; eauto.
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
    iSpecialize ("H" $! _ _ _ _ step _ 0).
    rewrite lift_d_at.
    iDestruct ("H" with "Hσ Hg") as "H".
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
      rewrite Nat.iter_succ.
      iSplit; first done.
      iApply (step_fupdN_fresh_wand with "H").
      { done. }
      iIntros (?) "H Hlc".
      iSpecialize ("H" with "[Hlc]").
      { rewrite {1}Nat.add_comm ?Nat.iter_add //. }
      iMod "H". iModIntro.
      rewrite {1}plus_comm Nat.iter_add.
      rewrite -Nat.iter_succ Nat.iter_succ_r.
      iApply step_fupd2N_le; last iApply (step_fupd2N_wand with "H").
      { apply Nat.eq_le_incl. f_equal.
        rewrite {1}plus_comm ?Nat.iter_add.
        f_equal. rewrite -Nat.iter_succ_r //. }
      iIntros ">H".
      rewrite {1}plus_comm ?Nat.iter_add.
      iDestruct "H" as (??? Heq) "(H1 & Hg & ? & ?)".
      iExists _, _, _. iFrame "∗".
      iSplitL ""; first eauto.
      (* iSplitL "H1". *)
      (* { iModIntro. iNext. iNext. iApply (bi.laterN_le with "H1"); auto. *)
      (*   apply Nat.eq_le_incl. f_equal. *)
      (*   rewrite -?Nat.iter_succ_r -?Nat.iter_add. *)
      (*   f_equal. lia. } *)
      iMod (global_state_interp_le with "Hg") as "$".
      { apply Nat.eq_le_incl.
        rewrite -?Nat.iter_succ_r -?Nat.iter_add.
        f_equal. lia. }
      iModIntro; done.
    - (* The remaining execution did not crash. This is a "base case" of sorts. *)
      iExists hD'.
      assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; auto).
      iDestruct (wptp_recv_strong_normal_adequacy with "Hσ Hg [Hv] Hr [] HNC") as "H"; eauto.
      (* iModIntro. *)
      iSplit; first done.
      iIntros "Hlc".
      rewrite /sum_crash_steps.
      rewrite plus_0_r.
      rewrite Nat.iter_succ.
      iSpecialize ("H" with "[Hlc]").
      { iExactEq "Hlc". f_equal. }
      iApply (step_fupd2N_inner_wand with "H"); try set_solver+.
      iIntros "H".
      rewrite -Nat.iter_succ Nat.iter_succ_r.
      rewrite Nat.iter_add Nat.iter_succ_r.
      eauto.
  Qed.

  (* In this lemma we combine [wptp_recv_strong_normal_adequacy] and
  [wptp_recv_strong_crash_adequacy] into a lemma that applies both in the
  absence and presence of crashes. *)
  Lemma wptp_recv_strong_adequacy `{!nvmG Σ} Φ Φr κs' s hD ns mj D n r1 e1 TV1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%TE :: t1, (σ1, g1)) κs (t2, (σ2,g2)) stat →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    (* crash_weakestpre.interp -∗ *)
    validV (store_view TV1) -∗
    ((wpr s (* Hc t *) ⊤ e1 r1 Φ Φr) (⊥, _)) -∗
    (* □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗ *)
    wptp s t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns hD (λ hD',
      let ntot := (steps_sum num_laters_per_step step_count_next
                            (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ ntot -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 TV2 t2',
      ⌜ t2 = (e2 `at` TV2)%TE :: t2' ⌝ ∗
      (* ▷^(S (S (num_laters_per_step $ ntot'))) *)
      (*     (⌜ ∀ te, s = NotStuck → te ∈ t2 → not_stuck te σ2 g2 ⌝) ∗ *)
      state_interp σ2 (length t2') ∗
      global_state_interp g2 ntot' mj D κs' ∗
      (match stat with
       | Normal =>
          ⌜ (* Hc' = Hc ∧ *) hD' = hD ⌝ ∗
          (* from_option Φ True (to_val e2) *)
          from_option (λ v, Φ v (TV2, _)) True (to_val e2)
       | Crashed =>
          from_option (λ v, Φr v (TV2, hD')) True (to_val e2)
           (* from_option (Φr Hc' t') True (to_val e2) ∗ □ Φinv' Hc' t' *)
      end)  ∗
      (* ([∗ list] v ∈ omap to_val t2', fork_post v) ∗ *)
      NC 1))).
  Proof.
    intros. destruct stat.
    - iIntros "ST GS VAL ? ? NC".
      iDestruct (wptp_recv_strong_crash_adequacy
        with "ST GS VAL [$] [$] NC") as "H"; eauto.
    - iIntros.
      assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; auto).
      rewrite Nat.add_0_r.
      iIntros "Hlc".
      iDestruct (wptp_recv_strong_normal_adequacy
                  with "[$] [$] [$] [$] [$] [$] Hlc") as "H"; eauto.
      iMod "H". iModIntro.
      iApply (step_fupd2N_wand with "H").
      setoid_rewrite (bi.pure_True (hD = hD) eq_refl).
      setoid_rewrite (left_id (True%I) _ _).
      naive_solver.
  Qed.

  Lemma wptp_recv_normal_progress `{nvmG Σ} {Φ Φr κs' HG} n ns ncurr mj D r1 e1 TV1 t1 κs t2 σ1 g1 σ2 g2 te2 :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%E :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
    te2 ∈ t2 →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    validV (store_view TV1) -∗
    wpr NotStuck ⊤ e1 r1 Φ Φr (⊥, _) -∗
    wptp NotStuck t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns HG (λ HG',
      ⌜ HG' = HG ⌝ ∗
      (£ (steps_sum num_laters_per_step step_count_next ncurr (S n)) -∗
      ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅, ∅|∅}=>
      ||▷=>^(num_laters_per_step (Nat.iter n step_count_next ncurr) + 1)
            ⌜ not_stuck te2 σ2 g2 ⌝ )).
  Proof.
    iIntros (Hstep Hel) "Hσ Hg #Hval He Ht HNC".
    inversion Hstep. subst.
    iPoseProof (wptp_progress with "Hσ Hg [He] Ht") as "H".
    { eauto. }
    { done. }
    { rewrite /wpr wpr_unfold /wpr_pre.
      iEval (rewrite crash_weakestpre.wpc_eq /=) in "He".
      iApply ("He" $! TV1 with "[%] Hval").
      destruct TV1 as [[??]?]. repeat split; apply view_empty_least. }
    iSpecialize ("H" with "[$]").
    assert (ns = []) as ->;
      first by (eapply nrsteps_normal_empty_prefix; eauto).
    inversion H0. subst.
    rewrite /step_fupdN_fresh.
    iSplitL ""; first by eauto.
    iIntros "Hlc". iSpecialize ("H" with "Hlc").
    iApply (step_fupd2N_wand with "H"); auto.
  Qed.

  Lemma nat_iter_equality ns' g (ncurr : nat) (n' : nat) :
    Nat.iter (sum_crash_steps ns') g (g (Nat.iter n' g ncurr)) =
    Nat.iter (sum_crash_steps (n' :: ns')) g ncurr.
  Proof.
    simpl.
    rewrite {1}Nat.add_comm ?Nat.iter_add.
    f_equal. rewrite -Nat.iter_succ -Nat.iter_succ_r //.
  Qed.

  Lemma steps_sum_equality f g n' ns' ncurr n :
    steps_sum f g
      (Nat.iter (sum_crash_steps (n' :: ns')) g ncurr) n +
    f (Nat.iter (n + sum_crash_steps (n' :: ns')) g ncurr) =
    steps_sum f g
      (Nat.iter (sum_crash_steps ns') g
        (g (Nat.iter n' g ncurr))) n +
    f
      (Nat.iter (n + sum_crash_steps ns') g
        (g (Nat.iter n' g ncurr))).
  Proof.
    rewrite nat_iter_equality.
    simpl.
    f_equal.
    rewrite -?Nat.iter_succ_r -?Nat.iter_add.
    f_equal. f_equal.
    simpl.
    lia.
  Qed.

  Lemma wptp_recv_crash_progress `{nvmG Σ} {Φ Φinv Φinv' Φr κs' HG} ncurr mj D ns n r1 e1 TV1 t1 κs t2 σ1 g1 σ2 g2 ee2 :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%E :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
    ee2 ∈ t2 →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    validV (store_view TV1) -∗
    wpr NotStuck ⊤ e1 r1 Φ Φr (⊥, _) -∗
    (* □ (∀ HG', Φinv HG' -∗ □ Φinv' HG') -∗ *)
    wptp NotStuck t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns HG (λ HG',
      let ntot := (steps_sum num_laters_per_step step_count_next
                            (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ (ntot + num_laters_per_step ntot' + 1) -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ∅|∅}=> ||▷=>^(num_laters_per_step ntot' + 1)
      ⌜ not_stuck ee2 σ2 g2 ⌝)).
  Proof.
    revert HG e1 TV1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    induction ns as [|n' ns' IH] => HG e1 TV1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    { rewrite app_nil_l.
      intros Hgt%nrsteps_crashed_length.
      simpl in Hgt. lia. }
    iIntros (Hsteps Hel) "Hσ Hg Hval He Ht HNC".
    inversion_clear Hsteps as [|?? [t1' ?] ????? s0 ? HCS].
    rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
    destruct ρ2 as (?&[σ2_pre_crash g2_pre_crash]).

    rewrite -assoc.
    rewrite /wpr wpr_unfold /wpr_pre.
    iEval (rewrite crash_weakestpre.wpc_eq /=) in "He".
    iSpecialize ("He" $! TV1 with "[%] Hval").
    { destruct TV1 as [[??]?]. repeat split; apply view_empty_least. }
  (*   rewrite -assoc wpr_unfold /wpr_pre. *)
    rewrite Nat.iter_succ.
    iIntros "Hlc".
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
    iMod "H". iModIntro.
    iApply (step_fupd2N_wand (steps_sum num_laters_per_step step_count_next ncurr (S n'))
              with "H").
    iIntros "H".
    iMod "H".
    iModIntro. iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
    iModIntro. iModIntro. iNext.
    iMod ("Hclo") as "_".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
    iMod ("Hclo") as "_".
    iDestruct "H" as (e2 t2' ?) "(H & Hσ & Hg & HC)".
    iSpecialize ("H" $! _ _ _ _ HCS _ 0).
    setoid_rewrite lift_d_at.
    iSpecialize ("H" with "Hσ Hg").
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo";
      [apply empty_subseteq | apply empty_subseteq|].
    iModIntro.
    (* iModIntro. do 2 iModIntro. iNext. *)
    (* iModIntro. *)
    iMod ("Hclo") as "_".
    iModIntro.
    iIntros (Hc) "HNC".
    iMod ("H" with "HNC") as (hD') "(%crEq & Hσ & Hg & Hv & Hr & HNC)".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo";
      [apply empty_subseteq | apply empty_subseteq|].
    iModIntro.
    iModIntro.
    iNext.
    iModIntro.
    iMod ("Hclo") as "_".
    iModIntro.
    iModIntro.
    destruct s0.
    - iPoseProof (IH with "Hσ Hg [Hv] Hr [//] HNC") as "H".
      { eauto. }
      { eauto. }
      { eauto. }
      iExists _.
      iSplit; first done.
      iApply (step_fupdN_fresh_wand with "H").
      { auto. }
      iIntros (HG'') "H Hlc".
      iSpecialize ("H" with "[Hlc]").
      { iExactEq "Hlc".
        f_equal. f_equal.
        rewrite steps_sum_equality.
        reflexivity. }
      iMod "H". iModIntro.
      iApply step_fupd2N_le; last iApply (step_fupd2N_wand with "H").
      { apply Nat.eq_le_incl.
        rewrite nat_iter_equality.
        reflexivity. } (* FIXME: Figure out why things are so slow. *)
      iIntros ">H".
      iModIntro. iApply (step_fupd2N_le with "H"); auto.
      apply Nat.eq_le_incl.
      rewrite 2!Nat.iter_add.
      rewrite nat_iter_equality.
      reflexivity.
    - iExists _.
      iSplit; first done.
      iDestruct (wptp_recv_normal_progress with "Hσ Hg [Hv] Hr [] HNC") as "H"; eauto.
      iApply (step_fupdN_fresh_wand with "H").
      { simpl. reflexivity. }
      iIntros (HG'') "H".
      iDestruct "H" as (->) "H".
      rewrite steps_sum_S_r.
      iClear "HC". simpl.
      assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
      iIntros "Hlc".
      iSpecialize ("H" with "[Hlc]").
      { simpl. rewrite Nat.add_0_r. iExactEq "Hlc". f_equal.
        rewrite -assoc. f_equal.
        rewrite ![_ + 1]comm. f_equal.
        rewrite -Nat.iter_succ Nat.iter_succ_r.
        rewrite Nat.iter_add Nat.iter_succ_r. done. }
      simpl. iMod "H".
      iApply (step_fupd2N_inner_wand with "H"); try set_solver+.
      { rewrite Nat.add_0_r. auto. }
      iIntros "H".
      rewrite Nat.add_0_r.
      rewrite -Nat.iter_succ Nat.iter_succ_r.
      rewrite Nat.iter_add.
      rewrite Nat.iter_add.
      rewrite Nat.iter_add.
      simpl.
      rewrite 1!(comm _ _ 1).
      rewrite 1!(comm _ _ 1).
      rewrite -Nat.iter_succ_r.
      simpl.
      done.
      Unshelve. done. done.
  Qed.

  Lemma wptp_recv_progress `{!nvmG Σ} {Φ Φr κs'} hD ns mj D n r1 e1 TV1 t1 κs t2
      σ1 g1 ncurr σ2 g2 stat te :
    nrsteps (r1 `at` ⊥) (ns ++ [n]) ((e1 `at` TV1)%E :: t1, (σ1, g1)) κs (t2, (σ2, g2)) stat →
    te ∈ t2 →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    validV (store_view TV1) -∗
    (wpr NotStuck ⊤ e1 r1 Φ Φr) (⊥, _) -∗
    wptp NotStuck t1 -∗
    NC 1 -∗
    step_fupdN_fresh ncurr ns hD (λ HG',
      let ntot := (steps_sum num_laters_per_step step_count_next
                            (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                            n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ (ntot + num_laters_per_step ntot' + 1) -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ∅|∅}=> ||▷=>^(num_laters_per_step ntot' + 1)
      ⌜ not_stuck te σ2 g2 ⌝)).
  Proof.
    intros.
    destruct stat.
    - iIntros "A B val D E NC".
      iDestruct (wptp_recv_crash_progress with "A B val D E NC") as "H"; eauto.
    - iIntros "A B val D E NC".
      iDestruct (wptp_recv_normal_progress with "A B val D E NC") as "H"; eauto.
      iApply (step_fupdN_fresh_wand with "H"); first auto.
      iIntros (?) "H Hlc".
      iDestruct "H" as (->) "H".
      assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
      rewrite steps_sum_S_r.
      simpl. rewrite Nat.add_0_r.
      iMod ("H" with "[Hlc]") as "H".
      { iExactEq "Hlc". f_equal. lia. }
      iModIntro.
      iApply (step_fupd2N_wand with "H"); auto.
      Unshelve. apply (True)%I. apply (True)%I. (* FIXME *)
  Qed.

End recovery_adequacy.

(*
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
*)

Lemma step_fupdN_fresh_rearrange `{!nvmG Σ, nD : nvmDeltaG} φ ns ncurr k k2 :
  (|={⊤}=> step_fupdN_fresh ncurr ns _
              (λ _, £ (k + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝)) -∗
  £ (fresh_later_count num_laters_per_step step_count_next ncurr ns + k + k2) -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(fresh_later_count num_laters_per_step step_count_next ncurr ns + S k + k2) ⌜φ⌝.
Proof.
  iIntros "H Hlc".
  iInduction ns as [| n' ns] "IH" forall (nD ncurr).
  - rewrite /step_fupdN_fresh.
    iMod "H". iMod ("H" with "Hlc") as "H". iModIntro.
    rewrite fresh_later_count_nil.
    replace (0 + S k) with (k + 1) by lia.
    rewrite -!assoc -step_fupd2N_add.
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    rewrite -step_fupd2N_add.
    iMod "H". iApply (fupd2_mask_intro); [done..|]. iIntros "_".
    done.
  - iMod NC_alloc_strong as (γcrash) "NC".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iMod "H".
    rewrite fresh_later_count_cons.
    iEval (rewrite !lc_split -assoc) in "Hlc".
    iDestruct "Hlc" as "[[[Hlc1 _] Hlc2] Hlck]".
    iMod ("H" with "Hlc1") as "H". iModIntro.
    rewrite -!assoc -step_fupd2N_add.
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    iApply step_fupd2_fupd2N; first lia.
    do 2 iMod "H". iModIntro.
    rewrite -step_fupd2N_add. replace 3 with (2+1) by lia.
    rewrite -step_fupd2N_add.
    iApply (step_fupd2N_wand with "H").
    iIntros ">H".
    iMod ("H" $! _ with "NC") as ">H".
    do 2 iModIntro.
    do 2 iMod "H".
    iMod "H" as (nD') "[-> H]".
    iMod ("IH" $! nD' with "H [Hlc2 Hlck]") as "H".
    { iEval rewrite !lc_split. by iFrame. }
    do 3 iModIntro. rewrite assoc. done.
Qed.

Lemma step_fupdN_fresh_soundness `{!nvmGpreS Σ} φ ns ncurr k k2 f g :
  (⊢ ∀ (Hi : invGS Σ),
    |={⊤}=> ∃ (nF : nvmG Σ) (nD : nvmDeltaG) (Hc : crashGS Σ),
      ⌜ iris_invGS = Hi ⌝ ∗
      ⌜ num_laters_per_step = f ⌝ ∗
      ⌜ step_count_next = g ⌝ ∗
      ⌜ iris_crashGS = Hc ⌝ ∗
      ⌜ nvmBaseG_invGS = Hi ⌝ ∗
      (|={⊤}=> step_fupdN_fresh ncurr ns _ (λ _,
        £ (k + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (step_fupd2N_soundness
            (fresh_later_count f g ncurr ns + S k + k2) (fresh_later_count f g ncurr ns + k + k2)).
  iIntros (Hinv) "Hlc".
  iMod NC_alloc as (Hc) "HNC".
  iMod (Hiter $! Hinv) as (nF nD eqInv <- <- <- <- <-) "H".
  iApply (step_fupdN_fresh_rearrange φ ns ncurr k k2 with "H Hlc").
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

Lemma allocate_empty_high_state_interp `{!nvmGpreS Σ} Hinv σ PV κs n :
  valid_heap σ →
  ⊢ |={⊤}=> ∃ (nF : nvmG Σ) (nD : nvmDeltaG),
      ⌜ nvmBaseG_invGS = Hinv ⌝ ∗
      validV ∅ ∗
      NC 1 ∗
      pre_borrowN n ∗
      ([∗ map] ℓ ↦ hist ∈ σ, ℓ ↦h hist) ∗
      persisted PV ∗
      global_state_interp (Λ := nvm_lang) () (n * 4 + crash_borrow_ginv_number) 1%Qp ∅ κs ∗
      nvm_heap_ctx (σ, PV) ∗
      interp.
Proof.
  intros valid.
  iMod NC_alloc_strong as (γcrash) "NC".
  iMod (credit_name_init (n * 4 + crash_borrow_ginv_number)) as
      (name_credit) "(credAuth & Hcred & Htok)".
  iDestruct (cred_frag_split with "Hcred") as "(Hpre & Hcred)".
  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  iMod (allocate_state_interp Hinv _ γcrash σ PV name_credit)
    as (names) "(%crEq & ctx & Ha & #valid & crashedAt & Hc)";
    first eassumption.
  set (fixed := NvmFixedG _ (nvm_build_base _ _ Hinv _ name_credit) nvmPreG_high).
  iExists (fixed).
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
  (* Allocate set of non-atomic locations. *)
  iMod (own_alloc (● (∅ : gsetUR _))) as (exclusive_locs_name) "naLocs".
  { apply auth_auth_valid. done. }
  iMod (ghost_map_alloc (∅ : gmap loc nat)) as (offsets_name) "(offsets & _)".
  iMod (ghost_map_alloc (∅ : gmap loc view)) as (na_views_name) "(na_views & _)".
  iMod (ghost_map_alloc (∅ : gmap loc positive)) as (crashed_in_name) "(crashedIn & _)".
  iMod (own_all_bumpers_alloc ∅) as (bumpers_name) "[bumpers #bumpersFrag]".
  iMod (auth_map_map_alloc ∅) as (phys_hist_name) "[physHist _]".
  set (hD := {|
               abs_history_name := abs_history_name;
               phys_history_name := phys_hist_name;
               non_atomic_views_gname := na_views_name;
               crashed_in_name := crashed_in_name;
               predicates_name := predicates_name;
               preorders_name := orders_name;
               offset_name := offsets_name;
               shared_locs_name := shared_locs_name;
               exclusive_locs_name := exclusive_locs_name;
               bumpers_name := bumpers_name;
             |}).
  iExists (NvmDeltaG _ hD).
  iModIntro.
  iSplitPure; first done.
  iFrameF "valid".
  simpl. rewrite crEq. iFrameF "NC".
  iDestruct (@cred_frag_to_pre_borrowN _ _ _ _ n with "[ Hpre ]") as "Hpre".
  { rewrite /fixed. iFrame "Hpre". }
  iFrameF "Hpre". iFrameF "Ha".
  iFrame "Hinv".
  rewrite /cred_interp.
  iPureGoal; first done.
  iFrame "credAuth Htok".
  iFrame.
  rewrite /interp.
  repeat iExists ∅.
  simpl.
  iFrame.
  rewrite map_zip_with_empty.
  iEval (rewrite !big_sepM2_empty).
  iEval (rewrite !big_sepM_empty).
  rewrite !left_id.
  iPureIntro.
  split_and!; try done; set_solver.
Qed.

(* This adequacy lemma is similar to the adequacy lemma for [wpr] in Perennial:
[wp_recv_adequacy_inv]. *)
Lemma high_recv_adequacy Σ `{hPre : !nvmGpreS Σ} s e r σ PV (φ φr : val → Prop) n :
  valid_heap σ →
  (∀ `{nF : !nvmG Σ, nD : nvmDeltaG},
    ⊢ ⎡ pre_borrowN n ⎤ -∗
      (* Note: We need to add the resources that can be used to prove the [wpr].
       These should require the user to decide which locations should be
       shared/exclusive, location invariants, etc. *)
      (wpr s ⊤ e r (λ v, ⌜ φ v ⌝) (λ  v, ⌜ φr v ⌝))) →
  recv_adequate s (ThreadState e ⊥) (ThreadState r ⊥) (σ, PV)
                (λ v _, φ v.(val_val)) (λ v _, φr v.(val_val)).
Proof.
  intros val.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 stat.
  intros [ns [κs nstep]]%erased_rsteps_nrsteps.
  set (nsinit := (n * 4 + crash_borrow_ginv_number)).
  set (f1 := (λ n, 3 ^ (n + 1))%nat). (* [num_laters_per_step] *)
  set (f2 := (λ n, 10 * (n + 1))%nat). (* [step_count_next] *)
  split.
  - destruct (nrsteps_snoc _ _ _ _ _ _ nstep) as (ns' & n' & ->).
    eapply (step_fupdN_fresh_soundness _ ns' nsinit
                (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
                (S (S (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit))))).
    iIntros (inv).
    iMod (allocate_empty_high_state_interp inv σ PV [] n)
      as (nF nD eq) "(validV & nc & pre & ptsMap & pers & global & int & high)"; first done.
    iDestruct (Hwp _ _ ) as "-#Hwp".
    iDestruct ("Hwp" $! (∅, ∅, ∅) with "pre") as "Hwpr".
    iModIntro.
    iExists _, _.
    iPureGoal. { done. }
    iDestruct (wptp_recv_strong_adequacy _ _ [] with "[$int $high] global") as "HIP".
    { done. }
    iSpecialize ("HIP" with "validV Hwpr [//] nc").
    iExists _.
    iSplitPure; first done.
    iSplitPure. { simpl. reflexivity. }
    iSplitPure. {
      rewrite /step_count_next.
      simpl.
      reflexivity. }
    iSplitPure. { done. }
    iApply (step_fupdN_fresh_wand with "HIP").
    { rewrite /nsinit. rewrite /crash_borrow_ginv_number. done. }
    iModIntro.
    iIntros (hD).
    iIntros "H [Hlc1 Hlc2]".
    rewrite -eq.
    iMod ("H" with "Hlc1") as "H".
    iApply (step_fupd2N_wand with "H"); auto.
    iModIntro. iIntros "H".
    iMod "H" as (v2 TV2 ts2 ->) "(interp & global & Hv & nc)".
    destruct stat.
    * iDestruct "Hv" as "#Hv".
      iApply (@fupd2_mask_intro); [done..|].
      iIntros "_".
      iApply @step_fupd2N_later.
      repeat iNext.
      iIntros (v2' ? Heq). subst. inversion Heq; subst.
      rewrite to_of_val. naive_solver.
    * iDestruct "Hv" as "[-> #Hv]".
      iApply (@fupd2_mask_intro); [done..|].
      iIntros "_".
      iApply @step_fupd2N_later.
      repeat iNext.
      iIntros (v2' ? Heq). subst. inversion Heq; subst.
      rewrite to_of_val. naive_solver.

  - intros e2 -> He2.
    destruct (nrsteps_snoc _ _ _ _ _ _ nstep) as (ns' & n' & ->).
    eapply (step_fupdN_fresh_soundness _ ns' nsinit
                (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
                (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit) + 1)).
    iIntros (inv).

    iMod (allocate_empty_high_state_interp inv σ PV [] n)
      as (nF nD eq) "(validV & nc & pre & ptsMap & pers & global & int & high)"; first done.

    iDestruct (Hwp _ _ ) as "-#Hwp".
    iDestruct ("Hwp" $! (∅, ∅, ∅) with "pre") as "Hwpr".
    iModIntro.
    iExists _, _.
    iPureGoal. { done. }
    iDestruct (wptp_recv_progress with "[$int $high] global [validV] Hwpr [] nc") as "H";
      eauto.
    iExists _.
    iSplitPure; first done.
    iSplitPure. { simpl. reflexivity. }
    iSplitPure. { rewrite /step_count_next. simpl. reflexivity. }
    iSplitPure. { done. }
    iApply (step_fupdN_fresh_wand with "H").
    { auto. }
    iModIntro.
    iIntros (hD).
    iIntros "H Hlc".
    rewrite -eq.
    rewrite /nsinit.

    iApply "H". iExactEq "Hlc". f_equiv.
    rewrite assoc. done.
    Unshelve. apply [].
Qed.

Definition initial_heap (σ : gmap loc val) : store :=
  (λ (v : val), {[ 0 := Msg v ∅ ∅ ∅ ]} : history ) <$> σ.

(* A record that contains all the information we need for a new location. *)
Record loc_info `{nvmG Σ} := {
    (* Type for the location. *)
    loc_state : Type;
    loc_state_eqdecision : EqDecision loc_state;
    loc_state_countable : Countable loc_state;
    loc_state_abstractstate : AbstractState loc_state;
    loc_prot : LocationProtocol loc_state;
    (* Initial state. *)
    loc_init : loc_state;
  }.

Existing Instance loc_state_eqdecision.
Existing Instance loc_state_countable.
Existing Instance loc_state_abstractstate.

Section loc_info.
  Context `{nvmG Σ}.
  Implicit Types (lif : gmap loc loc_info).

  Definition encode_li (li : loc_info) := encode (li.(loc_init)).

  Definition mk_abs_hist lif : gmap loc (gmap time positive) :=
    (λ li, {[ 0 := encode li.(loc_init) ]}) <$> lif.

  Definition mk_preds lif : gmap loc (enc_predicate) :=
    (λ li, encode_predicate (li.(loc_prot).(pred))) <$> lif.

  Definition mk_bumpers lif : gmap loc _ :=
    (λ li, encode_bumper (li.(loc_prot).(bumper))) <$> lif.

  Definition mk_offsets lif : gmap loc nat :=
    (const 0) <$> lif.

  Definition mk_order lif : gmap loc (relation2 positive) :=
    (λ li, encode_relation (@abs_state_relation _ _ _ (li.(loc_state_abstractstate)))) <$> lif.

  Definition mk_na_views (na : gset loc) lif : gmap loc view :=
    (λ li, ∅ : view) <$> (restrict na lif).

  Lemma mk_na_views_default_lookup (ℓ : loc) (na_locs : gset loc) lif :
    default (∅ : view) (mk_na_views na_locs lif !! ℓ) = ∅.
  Proof.
    rewrite /mk_na_views. rewrite lookup_fmap.
    destruct (restrict na_locs lif !! ℓ); done.
  Qed.

End loc_info.

Lemma map_zip_with_drop_prefix_const {A B} (m1 : gmap loc (gmap nat A)) (m2 : gmap loc B) :
  dom m1 = dom m2 →
  map_zip_with drop_prefix m1 (const 0 <$> m2) = m1.
Proof.
  intros domEq.
  apply map_eq. intros ℓ.
  rewrite map_lookup_zip_with.
  destruct (m1 !! ℓ) eqn:eq; simpl; last done.
  rewrite lookup_fmap.
  assert (is_Some (m2 !! ℓ)) as (? & ->).
  { apply elem_of_dom. rewrite -domEq. apply elem_of_dom. done. }
  simpl.
  rewrite drop_prefix_zero. done.
Qed.

Lemma shared_locs_inv_initial_heap {A} (at_locs : gset loc) init_heap (lif : gmap loc A) :
  dom lif = dom init_heap →
  shared_locs_inv
    (restrict at_locs
       (map_zip_with drop_prefix (initial_heap init_heap) ((const 0) <$> lif))).
Proof.
  intros domEq.
  eapply map_Forall_subseteq. { apply restrict_subseteq. }
  rewrite map_zip_with_drop_prefix_const.
  2: { rewrite /initial_heap. rewrite dom_fmap_L. done. }
  intros ℓ hist (v & <- & hihi)%lookup_fmap_Some.
  apply map_Forall_singleton.
  rewrite /atomic_loc_inv. simpl.
  split; last done.
  rewrite /lookup_zero.
  done.
Qed.

Lemma valid_heap_initial_heap init_heap : valid_heap (initial_heap init_heap).
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

Definition pre_borrowN_d `{nvmG Σ} (n : nat) :=
  lift_d (λ _, pre_borrowN n).

Lemma high_recv_adequacy_2 Σ `{hPre : !nvmGpreS Σ} st e r (φ φr : val → Prop) n
      (init_heap : gmap loc val) (na_locs at_locs : gset loc) :
  na_locs ## at_locs →
  dom init_heap = na_locs ∪ at_locs →
  (∀ (nF : nvmG Σ),
   ∃ (lif : gmap loc loc_info), dom lif = dom init_heap ∧
   (* ∀ (nD : nvmDeltaG), *)
    ⊢ (* Resources for NA locations. *)
      ([∗ map] ℓ ↦ v ∈ restrict na_locs init_heap, ∃ li,
        ⌜ lif !! ℓ = Some li ⌝ ∗
        persist_lb ℓ (loc_prot li) (loc_init li) ∗
        ℓ ↦_{loc_prot li} [loc_init li]) -∗
      (* Resources for AT locations. *)
      ([∗ map] ℓ ↦ v ∈ restrict at_locs init_heap, ∃ li,
        ⌜ lif !! ℓ = Some li ⌝ ∗
        is_at_loc_d ℓ ∗
        persist_lb ℓ (loc_prot li) (loc_init li)) -∗
      pre_borrowN_d n -∗
      ([∗ map] ℓ ↦ v; li ∈ init_heap; lif,
        (pred (loc_prot li)) (loc_init li) v) ∗
      (wpr st ⊤ e r (λ v, ⌜ φ v ⌝) (λ v, ⌜ φr v ⌝))) →
  recv_adequate st
                (e `at` ⊥) (r `at` ⊥)
                (initial_heap init_heap, const (MaxNat 0) <$> init_heap)
                (λ v _, φ v.(val_val)) (λ v _, φr v.(val_val)).
Proof.
  intros disj locsEq. simpl.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 stat.
  intros [ns [κs nstep]]%erased_rsteps_nrsteps.

  set (nsinit := (n * 4 + crash_borrow_ginv_number)).
  set (f1 := (λ n, 3 ^ (n + 1))%nat). (* [num_laters_per_step] *)
  set (f2 := (λ n, 10 * (n + 1))%nat). (* [step_count_next] *)

  split.
  -
    destruct (nrsteps_snoc _ _ _ _ _ _ nstep) as (ns' & n' & ->).

    (* We apply soundness of Perennial/Iris. *)
    eapply (step_fupdN_fresh_soundness _ ns' nsinit
                (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
                (S (S (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit))))).
    (* eapply (step_fupdN_fresh_soundness _ ns' nsinit _ n''). *)
    iIntros (inv).

    set (σ := initial_heap init_heap).
    set (PV := (const (MaxNat 0) <$> init_heap)).

    (***** Begin allocate ghost state. *)

    iMod NC_alloc_strong as (γcrash) "NC".
    iMod (credit_name_init (n * 4 + crash_borrow_ginv_number)) as
        (name_credit) "(credAuth & Hcred & Htok)".
    iDestruct (cred_frag_split with "Hcred") as "(Hpre & Hcred)".
    iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
    { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
    iMod (allocate_state_interp inv _ γcrash σ PV name_credit)
      as (names) "(%crEq & ctx & Ha & #valid & #crashedAt & #pers)".
    { apply valid_heap_initial_heap. }
    rewrite <- crEq in *.
    set (fixed := NvmFixedG _ (nvm_build_base _ _ inv _ name_credit) nvmPreG_high).
    iExists (fixed).

    (* We can now get all the protocols. *)
    specialize (Hwp fixed) as (lif & domEq & Hwp).

    (* Allocate abstract history. *)
    set (absHist := mk_abs_hist lif).
    iMod (full_map_alloc absHist)
      as (abs_history_name) "(hists' & histPts & #histFrag)".

    (* Allocate predicates. *)
    set (preds := mk_preds lif).
    iMod (know_predicates_alloc preds) as (predicates_name) "[preds #predsFrag]".
    (* Allocate preorders. *)
    iMod (own_all_preorders_gname_alloc (mk_order lif)) as (orders_name) "[orders #fragOrders]".
    (* Allocate set of atomic locations. *)
    iMod (own_alloc (● (at_locs : gsetUR _) ⋅ (◯ at_locs)))
      as (shared_locs_name) "[atLocs #atLocsF]".
    { apply auth_both_valid. done. }
    (* Allocate set of non-atomic locations. *)
    iMod (own_alloc (● (na_locs : gsetUR _) ⋅ (◯ na_locs)))
      as (exclusive_locs_name) "[naLocs #naLocsF]".
    { apply auth_both_valid. done. }
    iMod (ghost_map_alloc (mk_na_views na_locs lif)) as (na_views_name) "(na_views & naViewsF)".
    iMod (ghost_map_alloc_persistent (mk_offsets lif)) as (offsets_name) "(offsets & #offsetsPts)".
    iMod (ghost_map_alloc (∅ : gmap loc positive)) as (crashed_in_name) "(crashedIn & _)".
    iMod (own_all_bumpers_alloc (mk_bumpers lif)) as (bumpers_name) "[bumpers #bumpersFrag]".
    iMod (auth_map_map_alloc σ) as (phys_hist_name) "[physHist #physHistF]".
    set (hD := {|
                abs_history_name := abs_history_name;
                phys_history_name := phys_hist_name;
                non_atomic_views_gname := na_views_name;
                crashed_in_name := crashed_in_name;
                predicates_name := predicates_name;
                preorders_name := orders_name;
                offset_name := offsets_name;
                shared_locs_name := shared_locs_name;
                exclusive_locs_name := exclusive_locs_name;
                bumpers_name := bumpers_name;
              |}).
    iExists (NvmDeltaG names hD).

    assert (dom init_heap = dom absHist) as domEq2.
    { rewrite /absHist. rewrite /mk_abs_hist. rewrite dom_fmap_L. done. }
    assert (dom σ = dom (mk_offsets lif)) as domEq3.
    { rewrite /mk_offsets. rewrite dom_fmap_L. rewrite domEq.
      rewrite /σ /initial_heap. apply dom_fmap_L. }
    (* End allocate ghost state. *)
    eassert (absHist = _ ∪ _) as split.
    { eapply restrict_disjoint_union. rewrite -domEq2. symmetry. apply locsEq. }
    iEval (rewrite split) in "histPts".
    rewrite big_sepM_union. 2: { apply restrict_disjoint. done. }
    iDestruct ("histPts") as "[naHistPts atHistPts]".

    set (gnames := (NvmDeltaG names hD)).
    (* iDestruct (Hwp (NvmDeltaG names hD)) as "-#Hwp". *)
    iDestruct (@cred_frag_to_pre_borrowN _ _ _ _ n with "[Hpre]") as "Hpre".
    { rewrite /fixed. iFrame "Hpre". }
    iDestruct (Hwp $! ((∅, ∅, ∅), gnames)) as "-#Hwp".
    iDestruct ("Hwp" with "[naHistPts naViewsF] [] [Hpre]") as "[predsHold Hwpr]".
    { (* Non-atomic locations. *)
      rewrite monPred_at_big_sepM.
      iDestruct (big_sepM_sep_zip with "[$naHistPts $naViewsF]") as "na".
      { apply dom_eq_alt_L.
        rewrite /mk_abs_hist /mk_na_views.
        rewrite restrict_dom_L.
        rewrite 2!dom_fmap_L.
        rewrite restrict_dom_L.
        done. }
      iDestruct (big_sepM_impl_dom_subseteq with "na []") as "[$ H]".
      { rewrite /mk_abs_hist /mk_na_views.
        rewrite dom_map_zip_with.
        rewrite !restrict_dom.
        rewrite !dom_fmap_L.
        rewrite !restrict_dom.
        rewrite domEq.
        set_solver+. }
      iModIntro.
      iIntros (ℓ [??] v [l1 l2]%map_lookup_zip_Some).
      apply restrict_lookup_Some in l1 as [look inNa].
      apply lookup_fmap_Some in look as (li & <- & lifLook).
      rewrite /mk_na_views in l2.
      apply lookup_fmap_Some in l2 as (li' & <- & [??]%restrict_lookup_Some).
      simplify_eq.
      iIntros ([? _]%restrict_lookup_Some) "[E naView]".
      iExists li.
      simpl.
      iSplitPure; first done. rewrite /persist_lb. rewrite /mapsto_na.
      iSplit.
      { iExists 0, 0.
        rewrite !monPred_at_embed.
        iDestruct (persisted_persisted_loc with "pers") as "$".
        { rewrite /PV. rewrite lookup_fmap. rewrite H. done. }
        simpl.
        rewrite /know_protocol.
        rewrite /know_pred.
        iDestruct (predicates_frag_lookup with "[$predsFrag]") as "$".
        { rewrite /preds /mk_preds. rewrite lookup_fmap. rewrite lifLook. done. }
        iDestruct (big_sepM_lookup with "fragOrders") as "$".
        { rewrite /mk_order. rewrite lookup_fmap. rewrite lifLook. done. }
        rewrite /know_bumper.
        iDestruct (big_sepM_lookup with "bumpersFrag") as "$".
        { rewrite /mk_bumpers. rewrite lookup_fmap lifLook. done. }
        iDestruct (big_sepM_lookup with "offsetsPts") as "$".
        { rewrite /mk_offsets. rewrite lookup_fmap lifLook. done. }
        rewrite -!assoc.
        iSplitPure. { apply bumper_mono. }
        iSplit.
        { iExists (encode _).
          iSplitPure. { setoid_rewrite decode_encode. done. }
          iDestruct (big_sepM_lookup _ _ ℓ with "histFrag") as "hf".
          { rewrite /mk_abs_hist. rewrite lookup_fmap lifLook. done. }
          rewrite big_sepM_singleton.
          iFrame "hf". }
        rewrite view_lookup_zero_empty.
        done. }
      iExists 0, 0, 0, _, _, _, _.
      rewrite !monPred_at_embed.
      iSplitPure; first done.
      iSplit.
      { rewrite /know_pred.
        iDestruct (predicates_frag_lookup _ _ ℓ with "[$predsFrag]") as "$".
        { rewrite /preds /mk_preds. rewrite lookup_fmap. rewrite lifLook. done. }
        iDestruct (big_sepM_lookup with "fragOrders") as "$".
        { rewrite /mk_order. rewrite lookup_fmap. rewrite lifLook. done. }
        rewrite /know_bumper.
        iDestruct (big_sepM_lookup with "bumpersFrag") as "$".
        { rewrite /mk_bumpers. rewrite lookup_fmap lifLook. done. }
        iPureIntro. apply bumper_mono. }
      iSplitPure. { apply increasing_map_singleton. }
      iSplit. { iApply location_sets_lookup; done. }
      iSplitPure. { apply lookup_singleton. }
      iSplitPure. { apply map_no_later_singleton. }
      iSplitL "E".
      { rewrite /know_full_history_loc /full_entry_unenc /=.
        rewrite map_fmap_singleton. iFrame "E". }
      iSplit.
      { iExists (encode _).
        iSplitPure. { setoid_rewrite decode_encode. done. }
        iDestruct (big_sepM_lookup _ _ ℓ with "histFrag") as "hf".
        { rewrite /mk_abs_hist. rewrite lookup_fmap lifLook. done. }
        rewrite big_sepM_singleton. iFrame "hf". }
      iDestruct (big_sepM_lookup with "offsetsPts") as "$".
      { rewrite /mk_offsets. rewrite lookup_fmap lifLook. done. }
      iFrameF "naView".
      iSplitPure; first done.
      iDestruct (auth_map_map_frag_lookup_singleton with "physHistF") as "$".
      { rewrite /σ. rewrite lookup_fmap. rewrite H. simpl. done. }
      { rewrite lookup_singleton. done. }
      simpl.
      iSplitPure. { done. }
      iSplitPure. { done. }
      iSplitPure. { done. }
      iRight. done. }
    { (* Atomic locations. *)
      rewrite monPred_at_big_sepM.
      iApply big_sepM_forall.
      iIntros (ℓ ? [? inAt]%restrict_lookup_Some).
      assert (is_Some (lif !! ℓ)) as (li & lifLook).
      { apply elem_of_dom. rewrite domEq. apply elem_of_dom. done. }
      iExists li. iSplitPure; first done.
      rewrite /persist_lb. simpl.
      rewrite !monPred_at_embed.
      iSplit. { iApply location_sets_lookup; done. }
      iExists 0, 0.
      iDestruct (persisted_persisted_loc with "pers") as "$".
      { rewrite /PV. rewrite lookup_fmap. rewrite H. done. }
      simpl.
      rewrite /know_protocol.
      rewrite /know_pred.
      iDestruct (predicates_frag_lookup with "[$predsFrag]") as "$".
      { rewrite /preds /mk_preds. rewrite lookup_fmap. rewrite lifLook. done. }
      iDestruct (big_sepM_lookup with "fragOrders") as "$".
      { rewrite /mk_order. rewrite lookup_fmap. rewrite lifLook. done. }
      rewrite /know_bumper.
      iDestruct (big_sepM_lookup with "bumpersFrag") as "$".
      { rewrite /mk_bumpers. rewrite lookup_fmap lifLook. done. }
      rewrite -!assoc.
      iSplitPure. { apply bumper_mono. }
      iDestruct (big_sepM_lookup with "offsetsPts") as "$".
      { rewrite /mk_offsets. rewrite lookup_fmap lifLook. done. }
      iSplit.
      { iExists (encode _).
        iSplitPure. { setoid_rewrite decode_encode. done. }
        iDestruct (big_sepM_lookup _ _ ℓ with "histFrag") as "hf".
        { rewrite /absHist /mk_abs_hist. rewrite lookup_fmap lifLook. done. }
        rewrite big_sepM_singleton.
        iFrame "hf". }
      rewrite view_lookup_zero_empty.
      done. }
    { simpl. rewrite monPred_at_embed. iFrame "Hpre". }
    iModIntro.
    iExists _.
    iSplitPure; first done.
    iSplitPure. { simpl. reflexivity. }
    iSplitPure. { rewrite /step_count_next. simpl. reflexivity. }
    iSplitPure. { done. }
    iSplitPure; first done.
    iDestruct (wptp_recv_strong_adequacy _ _ [] _ (NvmDeltaG names hD)
      with "[predsHold bumpers ctx Ha hists' atLocs naLocs physHist offsets
            crashedIn atHistPts preds orders na_views] [credAuth Htok]") as "HIP".
    { done. }
    { (* Show the state interpretaion. *)
      simpl.
      iFrame "ctx".
      iExists _, _, preds, _, _, _, na_locs, at_locs. iExists (mk_offsets lif), _.
      iFrame "physHist".
      iFrame "offsets".
      iSplitL "Ha".
      {
        assert (map_zip_with view_slice.drop_prefix σ (mk_offsets lif) = σ).
        { rewrite /mk_offsets.
          apply map_eq. intros ℓ.
          rewrite map_lookup_zip_with.
          destruct (σ !! ℓ) eqn:look; simpl; last done.
          rewrite lookup_fmap.
          assert (is_Some (lif !! ℓ)) as [? ->].
          { apply elem_of_dom. rewrite domEq.
            apply lookup_fmap_Some in look as (? & ? & ?).
            apply elem_of_dom. done. }
          simpl.
          rewrite drop_prefix_zero. done. }
        rewrite H.
        iFrame "Ha". }
      iFrame.
      (* oldViewsDiscarded *)
      iSplit.
      { iApply big_sepM2_forall.
        iSplitPure. { apply dom_eq_alt_L. apply domEq3. }
        rewrite /mk_offsets.
        iIntros (???? (? & <- & ?)%lookup_fmap_Some ?? lt). simpl in lt. lia. }
      iFrameF "crashedAt".
      iFrameF "histFrag".
      iSplitPure; first done.
      iSplitPure. { rewrite -domEq2. done. }
      iSplitPure.
      { rewrite /mk_na_views. rewrite dom_fmap_L.
        eapply restrict_dom_subset_L.
        rewrite domEq. set_solver. }
      iSplitPure. { rewrite /σ. apply shared_locs_inv_initial_heap. done. }
      iSplit.
      { iApply big_sepM2_forall.
        iPureIntro. split.
        { rewrite dom_eq_alt_L. set_solver. }
        intros ??? (? & <- & ?)%lookup_fmap_Some ?.
        apply increasing_map_singleton. }
      iSplitL "predsHold".
      { rewrite monPred_at_big_sepM2.
        iApply (big_sepM2_impl_dom_subseteq with "predsHold []").
        { rewrite /σ. rewrite /initial_heap. rewrite dom_fmap_L. done. }
        { rewrite /σ /mk_abs_hist. rewrite /initial_heap. rewrite !dom_fmap_L.
          done. }
        iModIntro.
        iIntros (ℓ v li hist ??? (hip & <- & ?)%lookup_fmap_Some
                  (li' & <- & ?)%lookup_fmap_Some) "pred".
        simplify_eq.
        iExists _.
        iSplitPure.
        { rewrite /preds. rewrite /mk_preds. rewrite lookup_fmap.
          rewrite H0. simpl. done. }
        iApply big_sepM2_singleton. simpl.
        iApply predicate_holds_phi.
        { done. }
        { done. }
        rewrite mk_na_views_default_lookup.
        iApply "pred". }
      (* bumpMono *)
      iSplit.
      { iApply big_sepM2_forall. iPureIntro. simpl. split.
        { apply dom_eq_alt_L. rewrite /mk_order /mk_bumpers.
          rewrite 2!dom_fmap_L. done. }
        intros ???.
        intros (li & ? & ?)%lookup_fmap_Some.
        intros (? & ? & ?)%lookup_fmap_Some.
        simplify_eq.
        apply: encode_bumper_bump_mono. }
      (* predPostCrash *)
      iSplit.
      { iApply big_sepM2_forall. iSplitPure.
        { apply dom_eq_alt_L. rewrite /mk_order /mk_bumpers.
          rewrite 2!dom_fmap_L. done. }
        iIntros (ℓ ?? (li &?&?)%lookup_fmap_Some (? & ? & ?)%lookup_fmap_Some) "!>".
        simplify_eq.

        iIntros (??????) "(%eq & eq2 & P)".
        iEval (rewrite /encode_predicate).
        apply encode_bumper_Some_decode in eq.
        destruct eq as (s & eq' & eq2').
        rewrite -eq2'.
        rewrite decode_encode.
        iExists _.
        iSplitPure.
        { simpl. reflexivity. }
        iDestruct (encode_predicate_extract with "eq2 P") as "pred".
        { done. }
        iApply (pred_condition with "pred"). }
      iSplitPure.
      { intros ?? (li & ? & ?)%lookup_fmap_Some.
        simplify_eq.
        apply encode_bumper_bump_to_valid. }

      iApply big_sepM2_forall. iPureIntro. simpl. split.
      { apply dom_eq_alt_L. rewrite /mk_order /mk_bumpers.
        rewrite 2!dom_fmap_L. done. }
      intros ???.
      intros (li & ? & ?)%lookup_fmap_Some.
      intros (? & ? & ?)%lookup_fmap_Some.
      simplify_eq.
      apply map_Forall_singleton.
      rewrite encode_bumper_encode. done. }
    { iFrame "Hinv". iFrame. done. }

    iClear "physHistF".
    iSpecialize ("HIP" with "valid Hwpr [//] NC").

    iApply (step_fupdN_fresh_wand with "HIP").
    { rewrite /nsinit. rewrite /crash_borrow_ginv_number. done. }
    iModIntro. iIntros (hD').
    iIntros "H [Hlc1 Hlc2]".
    iMod ("H" with "[Hlc1]") as "H".
    { done. }
    iApply (step_fupd2N_wand with "H"); auto.
    iModIntro. iIntros "H".
    iMod "H" as (v2 TV2 ts2 ->) "(interp & global & HIP & nc)".
    destruct stat.
    * iDestruct "valid" as "#Hv".
      iApply (@fupd2_mask_intro); [done..|].
      iIntros "_".
      iApply @step_fupd2N_later.
      repeat iNext.
      iIntros (v2' ? Heq). subst. inversion Heq; subst.
      rewrite to_of_val. naive_solver.
    * iDestruct "HIP" as "[-> #Hv]".
      iApply (@fupd2_mask_intro); [done..|].
      iIntros "_".
      iApply @step_fupd2N_later.
      repeat iNext.
      iIntros (v2' ? Heq). subst. inversion Heq; subst.
      rewrite to_of_val. naive_solver.
  -
    intros e2 -> He2.
    destruct (nrsteps_snoc _ _ _ _ _ _ nstep) as (ns' & n' & ->).

    eapply (step_fupdN_fresh_soundness _ ns' nsinit
                (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
                (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit) + 1)).
    iIntros (inv).

    set (σ := initial_heap init_heap).
    set (PV := (const (MaxNat 0) <$> init_heap)).

    (***** Begin allocate ghost state. *)
    iMod NC_alloc_strong as (γcrash) "NC".
    iMod (credit_name_init (n * 4 + crash_borrow_ginv_number)) as
        (name_credit) "(credAuth & Hcred & Htok)".
    iDestruct (cred_frag_split with "Hcred") as "(Hpre & Hcred)".
    iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
    { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
    iMod (allocate_state_interp inv _ γcrash σ PV name_credit)
      as (names) "(%crEq & ctx & Ha & #valid & #crashedAt & #pers)".
    { apply valid_heap_initial_heap. }
    rewrite <- crEq in *.
    set (fixed := NvmFixedG _ (nvm_build_base _ _ inv _ name_credit) nvmPreG_high).
    iExists (fixed).

    (* We can now get all the protocols. *)
    specialize (Hwp fixed) as (lif & domEq & Hwp).

    (* Allocate abstract history. *)
    set (absHist := mk_abs_hist lif).
    iMod (full_map_alloc absHist)
      as (abs_history_name) "(hists' & histPts & #histFrag)".

    (* Allocate predicates. *)
    set (preds := mk_preds lif).
    iMod (know_predicates_alloc preds) as (predicates_name) "[preds #predsFrag]".
    (* Allocate preorders. *)
    iMod (own_all_preorders_gname_alloc (mk_order lif)) as (orders_name) "[orders #fragOrders]".
    (* Allocate set of atomic locations. *)
    iMod (own_alloc (● (at_locs : gsetUR _) ⋅ (◯ at_locs)))
      as (shared_locs_name) "[atLocs #atLocsF]".
    { apply auth_both_valid. done. }
    (* Allocate set of non-atomic locations. *)
    iMod (own_alloc (● (na_locs : gsetUR _) ⋅ (◯ na_locs)))
      as (exclusive_locs_name) "[naLocs #naLocsF]".
    { apply auth_both_valid. done. }
    iMod (ghost_map_alloc (mk_na_views na_locs lif)) as (na_views_name) "(na_views & naViewsF)".
    iMod (ghost_map_alloc_persistent (mk_offsets lif)) as (offsets_name) "(offsets & #offsetsPts)".
    iMod (ghost_map_alloc (∅ : gmap loc positive)) as (crashed_in_name) "(crashedIn & _)".
    iMod (own_all_bumpers_alloc (mk_bumpers lif)) as (bumpers_name) "[bumpers #bumpersFrag]".
    iMod (auth_map_map_alloc σ) as (phys_hist_name) "[physHist #physHistF]".
    set (hD := {|
                abs_history_name := abs_history_name;
                phys_history_name := phys_hist_name;
                non_atomic_views_gname := na_views_name;
                crashed_in_name := crashed_in_name;
                predicates_name := predicates_name;
                preorders_name := orders_name;
                offset_name := offsets_name;
                shared_locs_name := shared_locs_name;
                exclusive_locs_name := exclusive_locs_name;
                bumpers_name := bumpers_name;
              |}).
    iExists (NvmDeltaG names hD).

    assert (dom init_heap = dom absHist) as domEq2.
    { rewrite /absHist. rewrite /mk_abs_hist. rewrite dom_fmap_L. done. }
    assert (dom σ = dom (mk_offsets lif)) as domEq3.
    { rewrite /mk_offsets. rewrite dom_fmap_L. rewrite domEq.
      rewrite /σ /initial_heap. apply dom_fmap_L. }
    (* End allocate ghost state. *)
    eassert (absHist = _ ∪ _) as split.
    { eapply restrict_disjoint_union. rewrite -domEq2. symmetry. apply locsEq. }
    iEval (rewrite split) in "histPts".
    rewrite big_sepM_union. 2: { apply restrict_disjoint. done. }
    iDestruct ("histPts") as "[naHistPts atHistPts]".

    set (gnames := (NvmDeltaG names hD)).
    (* iDestruct (Hwp (NvmDeltaG names hD)) as "-#Hwp". *)
    iDestruct (@cred_frag_to_pre_borrowN _ _ _ _ n with "[Hpre]") as "Hpre".
    { rewrite /fixed. iFrame "Hpre". }
    iDestruct (Hwp $! ((∅, ∅, ∅), gnames)) as "-#Hwp".
    iDestruct ("Hwp" with "[naHistPts naViewsF] [] [Hpre]") as "[predsHold Hwpr]".
    { (* Non-atomic locations. *)
      rewrite monPred_at_big_sepM.
      iDestruct (big_sepM_sep_zip with "[$naHistPts $naViewsF]") as "na".
      { apply dom_eq_alt_L.
        rewrite /mk_abs_hist /mk_na_views.
        rewrite restrict_dom_L.
        rewrite 2!dom_fmap_L.
        rewrite restrict_dom_L.
        done. }
      iDestruct (big_sepM_impl_dom_subseteq with "na []") as "[$ H]".
      { rewrite /mk_abs_hist /mk_na_views.
        rewrite dom_map_zip_with.
        rewrite !restrict_dom.
        rewrite !dom_fmap_L.
        rewrite !restrict_dom.
        rewrite domEq.
        set_solver+. }
      iModIntro.
      iIntros (ℓ [??] v [l1 l2]%map_lookup_zip_Some).
      apply restrict_lookup_Some in l1 as [look inNa].
      apply lookup_fmap_Some in look as (li & <- & lifLook).
      rewrite /mk_na_views in l2.
      apply lookup_fmap_Some in l2 as (li' & <- & [??]%restrict_lookup_Some).
      simplify_eq.
      iIntros ([? _]%restrict_lookup_Some) "[E naView]".
      iExists li.
      simpl.
      iSplitPure; first done. rewrite /persist_lb. rewrite /mapsto_na.
      iSplit.
      { iExists 0, 0.
        rewrite !monPred_at_embed.
        iDestruct (persisted_persisted_loc with "pers") as "$".
        { rewrite /PV. rewrite lookup_fmap. rewrite H. done. }
        simpl.
        rewrite /know_protocol.
        rewrite /know_pred.
        iDestruct (predicates_frag_lookup with "[$predsFrag]") as "$".
        { rewrite /preds /mk_preds. rewrite lookup_fmap. rewrite lifLook. done. }
        iDestruct (big_sepM_lookup with "fragOrders") as "$".
        { rewrite /mk_order. rewrite lookup_fmap. rewrite lifLook. done. }
        rewrite /know_bumper.
        iDestruct (big_sepM_lookup with "bumpersFrag") as "$".
        { rewrite /mk_bumpers. rewrite lookup_fmap lifLook. done. }
        iDestruct (big_sepM_lookup with "offsetsPts") as "$".
        { rewrite /mk_offsets. rewrite lookup_fmap lifLook. done. }
        rewrite -!assoc.
        iSplitPure. { apply bumper_mono. }
        iSplit.
        { iExists (encode _).
          iSplitPure. { setoid_rewrite decode_encode. done. }
          iDestruct (big_sepM_lookup _ _ ℓ with "histFrag") as "hf".
          { rewrite /mk_abs_hist. rewrite lookup_fmap lifLook. done. }
          rewrite big_sepM_singleton.
          iFrame "hf". }
        rewrite view_lookup_zero_empty.
        done. }
      iExists 0, 0, 0, _, _, _, _.
      rewrite !monPred_at_embed.
      iSplitPure; first done.
      iSplit.
      { rewrite /know_pred.
        iDestruct (predicates_frag_lookup _ _ ℓ with "[$predsFrag]") as "$".
        { rewrite /preds /mk_preds. rewrite lookup_fmap. rewrite lifLook. done. }
        iDestruct (big_sepM_lookup with "fragOrders") as "$".
        { rewrite /mk_order. rewrite lookup_fmap. rewrite lifLook. done. }
        rewrite /know_bumper.
        iDestruct (big_sepM_lookup with "bumpersFrag") as "$".
        { rewrite /mk_bumpers. rewrite lookup_fmap lifLook. done. }
        iPureIntro. apply bumper_mono. }
      iSplitPure. { apply increasing_map_singleton. }
      iSplit. { iApply location_sets_lookup; done. }
      iSplitPure. { apply lookup_singleton. }
      iSplitPure. { apply map_no_later_singleton. }
      iSplitL "E".
      { rewrite /know_full_history_loc /full_entry_unenc /=.
        rewrite map_fmap_singleton. iFrame "E". }
      iSplit.
      { iExists (encode _).
        iSplitPure. { setoid_rewrite decode_encode. done. }
        iDestruct (big_sepM_lookup _ _ ℓ with "histFrag") as "hf".
        { rewrite /mk_abs_hist. rewrite lookup_fmap lifLook. done. }
        rewrite big_sepM_singleton. iFrame "hf". }
      iDestruct (big_sepM_lookup with "offsetsPts") as "$".
      { rewrite /mk_offsets. rewrite lookup_fmap lifLook. done. }
      iFrameF "naView".
      iSplitPure; first done.
      iDestruct (auth_map_map_frag_lookup_singleton with "physHistF") as "$".
      { rewrite /σ. rewrite lookup_fmap. rewrite H. simpl. done. }
      { rewrite lookup_singleton. done. }
      simpl.
      iSplitPure. { done. }
      iSplitPure. { done. }
      iSplitPure. { done. }
      iRight. done. }
    { (* Atomic locations. *)
      rewrite monPred_at_big_sepM.
      iApply big_sepM_forall.
      iIntros (ℓ ? [? inAt]%restrict_lookup_Some).
      assert (is_Some (lif !! ℓ)) as (li & lifLook).
      { apply elem_of_dom. rewrite domEq. apply elem_of_dom. done. }
      iExists li. iSplitPure; first done.
      rewrite /persist_lb. simpl.
      rewrite !monPred_at_embed.
      iSplit. { iApply location_sets_lookup; done. }
      iExists 0, 0.
      iDestruct (persisted_persisted_loc with "pers") as "$".
      { rewrite /PV. rewrite lookup_fmap. rewrite H. done. }
      simpl.
      rewrite /know_protocol.
      rewrite /know_pred.
      iDestruct (predicates_frag_lookup with "[$predsFrag]") as "$".
      { rewrite /preds /mk_preds. rewrite lookup_fmap. rewrite lifLook. done. }
      iDestruct (big_sepM_lookup with "fragOrders") as "$".
      { rewrite /mk_order. rewrite lookup_fmap. rewrite lifLook. done. }
      rewrite /know_bumper.
      iDestruct (big_sepM_lookup with "bumpersFrag") as "$".
      { rewrite /mk_bumpers. rewrite lookup_fmap lifLook. done. }
      rewrite -!assoc.
      iSplitPure. { apply bumper_mono. }
      iDestruct (big_sepM_lookup with "offsetsPts") as "$".
      { rewrite /mk_offsets. rewrite lookup_fmap lifLook. done. }
      iSplit.
      { iExists (encode _).
        iSplitPure. { setoid_rewrite decode_encode. done. }
        iDestruct (big_sepM_lookup _ _ ℓ with "histFrag") as "hf".
        { rewrite /absHist /mk_abs_hist. rewrite lookup_fmap lifLook. done. }
        rewrite big_sepM_singleton.
        iFrame "hf". }
      rewrite view_lookup_zero_empty.
      done. }
    { simpl. rewrite monPred_at_embed. iFrame "Hpre". }

    iModIntro.
    iExists _.
    iSplitPure; first done.
    iSplitPure. { simpl. reflexivity. }
    iSplitPure. { rewrite /step_count_next. simpl. reflexivity. }
    iSplitPure. { done. }
    iSplitPure; first done.

    iDestruct (wptp_recv_progress (NvmDeltaG names hD)
      with "[predsHold bumpers ctx Ha hists' atLocs naLocs physHist offsets
            crashedIn atHistPts preds orders na_views] [credAuth Htok]") as "HIP".
    { done. }
    { eauto. }
    { (* Show the state interpretaion. *)
      simpl.
      iFrame "ctx".
      iExists _, _, preds, _, _, _, na_locs, at_locs. iExists (mk_offsets lif), _.
      iFrame "physHist".
      iFrame "offsets".
      iSplitL "Ha".
      {
        assert (map_zip_with view_slice.drop_prefix σ (mk_offsets lif) = σ).
        { rewrite /mk_offsets.
          apply map_eq. intros ℓ.
          rewrite map_lookup_zip_with.
          destruct (σ !! ℓ) eqn:look; simpl; last done.
          rewrite lookup_fmap.
          assert (is_Some (lif !! ℓ)) as [? ->].
          { apply elem_of_dom. rewrite domEq.
            apply lookup_fmap_Some in look as (? & ? & ?).
            apply elem_of_dom. done. }
          simpl.
          rewrite drop_prefix_zero. done. }
        rewrite H.
        iFrame "Ha". }
      iFrame.
      (* oldViewsDiscarded *)
      iSplit.
      { iApply big_sepM2_forall.
        iSplitPure. { apply dom_eq_alt_L. apply domEq3. }
        rewrite /mk_offsets.
        iIntros (???? (? & <- & ?)%lookup_fmap_Some ?? lt). simpl in lt. lia. }
      iFrameF "crashedAt".
      iFrameF "histFrag".
      iSplitPure; first done.
      iSplitPure. { rewrite -domEq2. done. }
      iSplitPure.
      { rewrite /mk_na_views. rewrite dom_fmap_L.
        eapply restrict_dom_subset_L.
        rewrite domEq. set_solver. }
      iSplitPure. { rewrite /σ. apply shared_locs_inv_initial_heap. done. }
      iSplit.
      { iApply big_sepM2_forall.
        iPureIntro. split.
        { rewrite dom_eq_alt_L. set_solver. }
        intros ??? (? & <- & ?)%lookup_fmap_Some ?.
        apply increasing_map_singleton. }
      iSplitL "predsHold".
      { rewrite monPred_at_big_sepM2.
        iApply (big_sepM2_impl_dom_subseteq with "predsHold []").
        { rewrite /σ. rewrite /initial_heap. rewrite dom_fmap_L. done. }
        { rewrite /σ /mk_abs_hist. rewrite /initial_heap. rewrite !dom_fmap_L.
          done. }
        iModIntro.
        iIntros (ℓ v li hist ??? (hip & <- & ?)%lookup_fmap_Some
                  (li' & <- & ?)%lookup_fmap_Some) "pred".
        simplify_eq.
        iExists _.
        iSplitPure.
        { rewrite /preds. rewrite /mk_preds. rewrite lookup_fmap.
          rewrite H0. simpl. done. }
        iApply big_sepM2_singleton. simpl.
        iApply predicate_holds_phi.
        { done. }
        { done. }
        rewrite mk_na_views_default_lookup.
        iApply "pred". }
      (* bumpMono *)
      iSplit.
      { iApply big_sepM2_forall. iPureIntro. simpl. split.
        { apply dom_eq_alt_L. rewrite /mk_order /mk_bumpers.
          rewrite 2!dom_fmap_L. done. }
        intros ???.
        intros (li & ? & ?)%lookup_fmap_Some.
        intros (? & ? & ?)%lookup_fmap_Some.
        simplify_eq.
        apply: encode_bumper_bump_mono. }
      (* predPostCrash *)
      iSplit.
      { iApply big_sepM2_forall. iSplitPure.
        { apply dom_eq_alt_L. rewrite /mk_order /mk_bumpers.
          rewrite 2!dom_fmap_L. done. }
        iIntros (ℓ ?? (li &?&?)%lookup_fmap_Some (? & ? & ?)%lookup_fmap_Some) "!>".
        simplify_eq.

        iIntros (??????) "(%eq & eq2 & P)".
        iEval (rewrite /encode_predicate).
        apply encode_bumper_Some_decode in eq.
        destruct eq as (s & eq' & eq2').
        rewrite -eq2'.
        rewrite decode_encode.
        iExists _.
        iSplitPure.
        { simpl. reflexivity. }
        iDestruct (encode_predicate_extract with "eq2 P") as "pred".
        { done. }
        iApply (pred_condition with "pred"). }
      iSplitPure.
      { intros ?? (li & ? & ?)%lookup_fmap_Some.
        simplify_eq.
        apply encode_bumper_bump_to_valid. }

      iApply big_sepM2_forall. iPureIntro. simpl. split.
      { apply dom_eq_alt_L. rewrite /mk_order /mk_bumpers.
        rewrite 2!dom_fmap_L. done. }
      intros ???.
      intros (li & ? & ?)%lookup_fmap_Some.
      intros (? & ? & ?)%lookup_fmap_Some.
      simplify_eq.
      apply map_Forall_singleton.
      rewrite encode_bumper_encode. done. }
    { iFrame "Hinv". iFrame. done. }

    iSpecialize ("HIP" with "valid Hwpr [//] NC").

    iModIntro.
    iApply (step_fupdN_fresh_wand with "HIP").
    { auto. }
    iIntros (hD').
    iIntros "H Hlc".
    rewrite /nsinit.

    iApply "H". iExactEq "Hlc". f_equiv.
    done.
    rewrite assoc. done.
    Unshelve. apply [].
Qed.
