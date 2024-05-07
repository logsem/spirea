From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang.
Import uPred.

From self.nextgen Require Import nextgen_promises.
From self.base Require Import generational_resources.
From self.nextgen Require Import inv_ng.
From self.program_logic Require Export crash_adequacy recovery_weakestpre.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

(* Alternative lc allocation that remembers the inG, since
lc_soundness will not be applicable in the proof strategy of
adequacy *)
Local Existing Instance lcGpreS_inG.
Local Lemma lc_alloc `{!lcGpreS Σ} n :
  ⊢ |==> ∃ (_ : lcGS Σ) (Hlc : lcGS_inG = lcGpreS_inG), later_credits.lc_supply n ∗ £ n.
Proof.
  rewrite later_credits.lc_unseal /later_credits.lc_def
    later_credits.lc_supply_unseal /later_credits.lc_supply_def.
  iMod (own_alloc (● n ⋅ ◯ n)) as (γLC) "[H● H◯]";
    first (apply auth_both_valid; split; done).
  pose (C := LcGS _ _ γLC).
  iModIntro. iExists C, eq_refl. iFrame.
Qed.

Section recovery_adequacy.
  Context {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ Ω}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types Φinv : iProp Σ.
  Implicit Types Φr : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

  Notation steps_sum := crash_adequacy.steps_sum.

  (* The assertion [P] holds after [lenght ns] crashes where each execution is
  [ns !! i] many steps. *)
  Fixpoint step_fupdN_fresh ncurrent (ns: list nat)
           (P : iProp Σ) {struct ns} :=
    match ns with
    | [] => P
    | (n :: ns) =>
      £ (steps_sum num_laters_per_step step_count_next ncurrent (S n)) -∗
        ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum (num_laters_per_step) (step_count_next)
                                       ncurrent (S n)) ||={∅|∅, ⊤|⊤}=>
        ||={⊤|⊤,∅|∅}=> ||▷=>^2 ||={∅|∅, ⊤|⊤}=> ⚡==>
        |={⊤}=>
          step_fupdN_fresh ((Nat.iter (S n) step_count_next ncurrent)) ns P
    end%I.

  Lemma step_fupdN_fresh_wand ncurr1 ncurr2 (ns: list nat) Q Q':
    ncurr1 = ncurr2 →
    step_fupdN_fresh ncurr1 ns Q -∗
    ■ (Q -∗ Q') -∗
    step_fupdN_fresh ncurr2 ns Q'.
  Proof.
    revert ncurr1 ncurr2.
    induction ns => ?? Hncurr.
    - iIntros "H Hwand". iApply "Hwand". eauto.
    - iIntros "H Hwand Hlc". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
      rewrite {1}Hncurr.
      iSpecialize ("H" with "Hlc").
      iApply (step_fupd2N_inner_wand with "H"); try auto.
      { subst. auto. }
      iIntros "H".
      iMod "H". iModIntro. iApply (step_fupd2N_wand with "H"). iIntros "H".
      iMod "H". iModIntro. iModIntro.
      iMod "H" as "H".
      iModIntro. iApply (IHns with "H").
      { subst. auto. }
      eauto.
  Qed.

  Lemma wptp_recv_strong_normal_adequacy {CS Φ Φinv Φr κs' s} n ncurr mj D r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
    nrsteps (CS := CS) r1 [n] (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    wpr CS s ⊤ e1 r1 Φ Φinv Φr -∗
    wptp s t1 -∗ (
      £ (steps_sum num_laters_per_step step_count_next ncurr n) -∗
      ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
      ∃ e2 t2',
        ⌜ t2 = e2 :: t2' ⌝ ∗
        state_interp σ2 (length t2') ∗
        global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
        from_option Φ True (to_val e2) ∗
        ([∗ list] v ∈ omap to_val t2', fork_post v)).
  Proof.
    iIntros (Hstep) "Hσ Hg He Ht".
    inversion Hstep. subst.
    iPoseProof (wptp_strong_adequacy with "Hσ Hg [He] Ht") as "H".
    { eauto. }
    {rewrite wpr_unfold /wpr_pre. iApply "He". }
    iIntros "Hlc". iSpecialize ("H" with "Hlc").
    iApply (step_fupd2N_wand with "H"); auto.
  Qed.

  Lemma wptp_recv_normal_progress {CS Φ Φinv Φr κs'}
      n ncurr mj D r1 e1 t1 κs t2 σ1 g1 σ2 g2 e2 :
    nrsteps (CS := CS) r1 [n] (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
    e2 ∈ t2 →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    wpr CS NotStuck ⊤ e1 r1 Φ Φinv Φr -∗
    wptp NotStuck t1 -∗
    step_fupdN_fresh ncurr [] (
      £ (steps_sum num_laters_per_step step_count_next ncurr (S n)) -∗
      ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅, ∅|∅}=>
      ||▷=>^(num_laters_per_step (Nat.iter n step_count_next ncurr) + 1)
      ⌜ not_stuck e2 σ2 g2 ⌝ ).
  Proof.
    iIntros (Hstep Hel) "Hσ Hg He Ht".
    inversion Hstep. subst.
    iPoseProof (wptp_progress with "Hσ Hg [He] Ht") as "H".
    { eauto. } { done. }
    { rewrite wpr_unfold /wpr_pre. iApply "He". }
    rewrite /step_fupdN_fresh.
    iIntros "Hlc". iSpecialize ("H" with "Hlc").
    iApply (step_fupd2N_wand with "H"); auto.
  Qed.

  Fixpoint sum_crash_steps ns :=
    match ns with
    | [] => 0
    | n :: ns => S n + sum_crash_steps ns
    end.

  Lemma wptp_recv_strong_crash_adequacy {CS Φ Φinv Φinv' Φr κs' s} ncurr mj D ns n r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
    nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    wpr CS s ⊤ e1 r1 Φ Φinv Φr -∗
    ■ (Φinv -∗ □ Φinv') -∗
    wptp s t1 -∗
    step_fupdN_fresh ncurr ns (
      let ntot :=
        (steps_sum num_laters_per_step step_count_next
                   (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                   n)  in
      let ntot' := (Nat.iter (n + sum_crash_steps ns) step_count_next ncurr) in
      £ ntot -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 t2',
      ⌜ t2 = e2 :: t2' ⌝ ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 ntot' mj D κs' ∗
      from_option (Φr) True (to_val e2) ∗
      □ Φinv' ∗
      ([∗ list] v ∈ omap to_val t2', fork_post v)
      (* ∗ NC 1 *)
      ))).
  Proof.
    revert e1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    induction ns as [|n' ns' IH] => e1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    { rewrite app_nil_l.
      inversion 1.
      match goal with
      | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
      end.
    }
    iIntros (Hsteps) "Hσ Hg He #Hinv Ht".
    inversion_clear Hsteps as [|?? [t1' ?] ????? s0].
    rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
    destruct ρ2 as (?&[σ2_pre_crash g2_pre_crash]).
    rewrite -assoc wpr_unfold /wpr_pre.
    rewrite Nat.iter_succ.
    iIntros "Hlc".
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iMod "H". iModIntro.
    iApply (step_fupd2N_wand (steps_sum num_laters_per_step step_count_next ncurr (S n'))
              with "H").
    iIntros "H".
    iMod "H".
    iModIntro. iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|].
    iModIntro. iModIntro. iNext.
    iMod ("Hclo") as "_".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|].
    iMod ("Hclo") as "_".
    iDestruct "H" as (e2 t2' ?) "(H&Hσ&Hg)".
    iMod ("H" with "[//] Hσ Hg") as "H".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|]. do 2 iModIntro. iNext.
    iModIntro.
    iMod ("Hclo") as "_".
    iModIntro.
    iModIntro.
    destruct s0.
    - iMod "H" as "(Hσ&Hg&Hr)".
      iDestruct "Hr" as "(_&Hr)".
      simpl in *.
      iPoseProof (IH with "[Hσ] [Hg] Hr [] []") as "H"; eauto.
      (* iExists _. *)
      iModIntro. simpl. eauto.
      iApply (step_fupdN_fresh_wand with "H").
      { auto. }
      iModIntro.
      iIntros "H Hlc".
      iSpecialize ("H" with "[Hlc]").
      { iExactEq "Hlc". f_equal.
        rewrite {1}Nat.add_comm ?Nat.iter_add.
        f_equal. rewrite -Nat.iter_succ -Nat.iter_succ_r //. }
      iMod "H". iModIntro.
      iEval rewrite -Nat.iter_succ Nat.iter_succ_r.
      iApply step_fupd2N_le; last iApply (step_fupd2N_wand with "H").
      { apply Nat.eq_le_incl. f_equal.
        rewrite {1}Nat.add_comm ?Nat.iter_add.
        f_equal. rewrite -Nat.iter_succ -Nat.iter_succ_r //. }
      iIntros ">H".
      rewrite {1}Nat.add_comm ?Nat.iter_add.
      iDestruct "H" as (?? Heq) "(H1&Hg&?&?)".
      iExists _, _. iFrame "∗".
      iSplitL ""; first eauto.
      iMod (global_state_interp_le with "Hg") as "$".
      { apply Nat.eq_le_incl.
        rewrite -?Nat.iter_succ_r -?Nat.iter_add Nat.add_assoc.
        f_equal. lia. }
      iModIntro; done.
    - iMod "H" as "(Hσ&Hg&Hr)".
      (* iExists HG'. *)
      iAssert (□Φinv')%I as "#Hinv'".
      { iDestruct "Hr" as "(Hr&_)".
        iApply "Hinv". eauto.
      }
      iDestruct "Hr" as "(_&Hr)".
      assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
      iDestruct (wptp_recv_strong_normal_adequacy with "[Hσ] [Hg] [Hr] []") as "H"; eauto.
      iModIntro.
      iIntros "Hlc".
      simpl.
      iSpecialize ("H" with "[Hlc]").
      { iExactEq "Hlc". f_equal. rewrite Nat.add_0_r. done. }
      iApply (step_fupd2N_inner_wand with "H"); try set_solver+.
      { rewrite Nat.add_0_r. auto. }
      iIntros "H".
      iFrame "Hinv'". rewrite Nat.add_0_r.
      rewrite -Nat.iter_succ Nat.iter_succ_r.
      rewrite Nat.iter_add Nat.iter_succ_r.
      eauto.
  Qed.

  (* unfortunately this duplicates the large induction above.
  There is probably some way to factor this... *)
  Lemma wptp_recv_crash_progress {CS Φ Φinv Φinv' Φr κs'} ncurr mj D ns n r1 e1 t1 κs t2 σ1 g1 σ2 g2 ee2 :
    nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
    ee2 ∈ t2 →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    wpr CS NotStuck ⊤ e1 r1 Φ Φinv Φr -∗
    ■ (Φinv -∗ □ Φinv') -∗
    wptp NotStuck t1 -∗ (* NC 1-∗ *)
    step_fupdN_fresh ncurr ns (
      let ntot := (steps_sum num_laters_per_step step_count_next
                             (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                             n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ (ntot + num_laters_per_step ntot' + 1) -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ∅|∅}=> ||▷=>^(num_laters_per_step ntot' + 1)
      ⌜ not_stuck ee2 σ2 g2 ⌝)).
  Proof.
    revert e1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    induction ns as [|n' ns' IH] => e1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
    { rewrite app_nil_l.
      inversion 1.
      match goal with
      | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
      end.
    }
    iIntros (Hsteps Hel) "Hσ Hg He #Hinv Ht".
    inversion_clear Hsteps as [|?? [t1' ?] ????? s0].
    rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
    destruct ρ2 as (?&[σ2_pre_crash g2_pre_crash]).
    rewrite -assoc wpr_unfold /wpr_pre.
    rewrite Nat.iter_succ.
    iIntros "Hlc".
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iMod "H". iModIntro.
    iApply (step_fupd2N_wand (steps_sum num_laters_per_step step_count_next ncurr (S n'))
              with "H").
    iIntros "H".
    iMod "H".
    iModIntro. iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|].
    iModIntro. iModIntro. iNext.
    iMod ("Hclo") as "_".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|].
    iMod ("Hclo") as "_".
    iDestruct "H" as (e2 t2' ?) "(H&Hσ&Hg)".
    iMod ("H" with "[//] Hσ Hg") as "H".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|]. do 2 iModIntro. iNext.
    iModIntro.
    iMod ("Hclo") as "_".
    iModIntro.
    iModIntro.
    destruct s0.
    - iMod "H" as "(Hσ&Hg&Hr)".
      iDestruct "Hr" as "(_&Hr)".
      simpl in *.
      iPoseProof (IH with "[Hσ] [Hg] Hr [] []") as "H"; eauto.
      iModIntro. simpl. eauto.
      iApply (step_fupdN_fresh_wand with "H").
      { auto. }
      iModIntro.
      iIntros "H Hlc".
      iSpecialize ("H" with "[Hlc]").
      { iExactEq "Hlc". f_equal. f_equal. f_equal.
        - rewrite {1}Nat.add_comm ?Nat.iter_add.
          f_equal. rewrite -Nat.iter_succ -Nat.iter_succ_r //.
        - rewrite -?Nat.iter_succ_r -?Nat.iter_add.
          f_equal. f_equal. lia. }
      iMod "H". iModIntro.
      iEval rewrite -Nat.iter_succ Nat.iter_succ_r.
      iApply step_fupd2N_le; last iApply (step_fupd2N_wand with "H").
      { apply Nat.eq_le_incl. f_equal.
        rewrite {1}Nat.add_comm ?Nat.iter_add.
        f_equal. rewrite -Nat.iter_succ -Nat.iter_succ_r //. }
      iIntros ">H".
      rewrite {1}[n + _]Nat.add_comm ?Nat.iter_add.
      iModIntro. iApply (step_fupd2N_le with "H"); auto.
      apply Nat.eq_le_incl. f_equal.
      rewrite -?Nat.iter_succ_r -?Nat.iter_add Nat.add_assoc.
      f_equal. lia.
    - iMod "H" as "(Hσ & Hg & Hr)".
      iAssert (□Φinv')%I as "#Hinv'".
      { iDestruct "Hr" as "(Hr&_)".
        iApply "Hinv". eauto.
      }
      iDestruct "Hr" as "(_&Hr)".
      assert (ns' = []) as -> by (eapply nrsteps_normal_empty_prefix; eauto).
      iDestruct (wptp_recv_normal_progress with "[Hσ] [Hg] [Hr] []") as "H"; eauto.
      iModIntro. (* this [iModIntro] is later in Perennial's but it doesn't seem to matter. *)
      iApply (step_fupdN_fresh_wand with "H").
      { simpl. lia. }
      iClear "Hinv'". iModIntro.
      iIntros "H".
      rewrite steps_sum_S_r.
      simpl.
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
      rewrite ![_ + 1]comm. simpl.
      rewrite Nat.iter_add Nat.iter_succ_r.
      eauto.
  Qed.

  Lemma wptp_recv_strong_adequacy {CS Φ Φinv Φinv' Φr κs' s} ns mj D n r1 e1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat :
    nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    wpr CS s ⊤ e1 r1 Φ Φinv Φr -∗
    ■ (Φinv -∗ □ Φinv') -∗
    wptp s t1 -∗
    step_fupdN_fresh ncurr ns (
      let ntot := (steps_sum num_laters_per_step step_count_next
                             (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                             n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ ntot -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 t2',
      ⌜ t2 = e2 :: t2' ⌝ ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 ntot' mj D κs' ∗
      (match stat with
       | Normal => from_option Φ True (to_val e2)
       | Crashed => from_option (Φr) True (to_val e2) ∗ □ Φinv'
       end)  ∗
      ([∗ list] v ∈ omap to_val t2', fork_post v)))).
  Proof.
    intros. destruct stat.
    - iIntros.
      iDestruct (wptp_recv_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
      iApply (step_fupdN_fresh_wand with "H"); first auto.
      iModIntro.
      iIntros "H Hlc". iSpecialize ("H" with "Hlc").
      iApply (step_fupd2N_wand with "H"); auto.
      iIntros "H".
      iMod "H" as (???) "(?&H&?&?&?)". iExists _, _.
      repeat (iSplitL ""; try iFrame; eauto).
    - iIntros.
      assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
      iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$] [$]") as "H"; eauto.
      iIntros "Hlc".
      simpl. rewrite Nat.add_0_r. iSpecialize ("H" with "Hlc").
      iMod "H". iModIntro.
      iApply (step_fupd2N_wand with "H"); auto.
      (* iIntros "H". *)
      (* iMod "H" as (???) "(?&H&?&?&?)". iExists _, _. *)
      (* iSplitL ""; first eauto. iFrame. eauto. *)
  Qed.

  Lemma wptp_recv_progress {CS Φ Φinv Φinv' Φr κs'} ns mj D n r1 e1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat e2 :
    nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
    e2 ∈ t2 →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    wpr CS NotStuck ⊤ e1 r1 Φ Φinv Φr -∗
    ■ (Φinv -∗ □ Φinv') -∗
    wptp NotStuck t1 -∗ (* NC 1-∗ *)
    step_fupdN_fresh ncurr ns (
      let ntot := (steps_sum num_laters_per_step step_count_next
                             (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                             n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
      £ (ntot + num_laters_per_step ntot' + 1) -∗
      (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ∅|∅}=> ||▷=>^(num_laters_per_step ntot' + 1)
      ⌜ not_stuck e2 σ2 g2 ⌝)).
  Proof.
    intros. destruct stat.
    - iIntros.
      iDestruct (wptp_recv_crash_progress with "[$] [$] [$] [$] [$]") as "H"; eauto.
    - iIntros.
      assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
      iDestruct (wptp_recv_normal_progress with "[$] [$] [$] [$]") as "H"; eauto.
      iApply (step_fupdN_fresh_wand with "H"); first auto.
      iModIntro.
      iIntros "H Hlc".
      (* iDestruct "H" as (->) "H". *)
      rewrite steps_sum_S_r.
      simpl. rewrite Nat.add_0_r.
      iMod ("H" with "[Hlc]") as "H".
      { iExactEq "Hlc". f_equal. lia. }
      iModIntro.
      iApply (step_fupd2N_wand with "H"); auto.
  Qed.

End recovery_adequacy.


(* Lemma step_fupdN_fresh_rearrange {Λ Σ Ω} *)
(*     `{!irisGS Λ Σ} φ ns ncurr k k2 : *)
(*   (|={⊤}=> *)
(*     step_fupdN_fresh (Ω := Ω) ncurr ns *)
(*       (£ (k + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝)) -∗ *)
(*   £ (fresh_later_count num_laters_per_step step_count_next ncurr ns + k + k2) -∗ *)
(*   ||={⊤|⊤,∅|∅}=> ||▷=>^(fresh_later_count num_laters_per_step step_count_next ncurr ns + S k + k2) ⌜φ⌝. *)
(* Proof. *)
(*   iIntros "H Hlc". *)
(*   iInduction ns as [| n' ns] "IH" forall (ncurr). *)
(*   - rewrite /step_fupdN_fresh. *)
(*     iMod "H". iMod ("H" with "Hlc") as "H". iModIntro. *)
(*     rewrite fresh_later_count_nil. *)
(*     replace (0 + S k) with (k + 1) by lia. *)
(*     rewrite -!assoc -step_fupd2N_add. *)
(*     iApply (step_fupd2N_wand with "H"). iIntros "H". *)
(*     rewrite -step_fupd2N_add. *)
(*     iMod "H". iApply (fupd2_mask_intro); [done..|]. iIntros "_". *)
(*     done. *)
(*   - *)
(*     (* iMod NC_alloc as (Hc') "HNC". *) *)
(*     rewrite /step_fupdN_fresh -/step_fupdN_fresh. *)
(*     iMod "H". *)
(*     rewrite fresh_later_count_cons. *)
(*     iEval (rewrite !lc_split -assoc) in "Hlc". *)
(*     iDestruct "Hlc" as "[[[Hlc1 _] Hlc2] Hlck]". *)
(*     iMod ("H" with "Hlc1") as "H". iModIntro. *)
(*     rewrite -!assoc -step_fupd2N_add. *)
(*     iApply (step_fupd2N_wand with "H"). iIntros "H". *)
(*     iApply step_fupd2_fupd2N; first lia. *)
(*     do 2 iMod "H". iModIntro. *)
(*     rewrite -step_fupd2N_add. replace 3 with (2+1) by lia. *)
(*     rewrite -step_fupd2N_add. *)
(*     iApply (step_fupd2N_wand with "H"). iIntros "H". *)
(*     iMod "H". *)
(* Abort. *)
    (* rewrite nextgen _plain *)
(*     iMod "H" as "H". *)
(*     iMod ("IH" $! with "H [Hlc2 Hlck]") as "H". *)
(*     { iEval rewrite !lc_split. by iFrame. } *)
(*     do 3 iModIntro. rewrite assoc. done. *)
(* Qed. *)
 
(* Lemma nextgen_lc_test {Σ} {Ω : gGenCmras Σ} `{!invGS Σ Ω} `{!ngLcGpreS Σ Ω} k : *)
(*   £ k ⊢ ⚡==> £ k. *)
(* Proof. iIntros "Hk". by iModIntro. Qed. *)

(* Lemma step_fupd2N_soundness_strong `{ip : !invGpreS Σ} n m φ : *)
(*   (∀ `{Hinv: !invGS Σ}, *)
(*     @inv_inG _ Hinv = ip → *)
(*     @lcGS_inG (@lcGS_inG Hinv) = lcGpreS_inG (inv_lcPreG ip) → *)
(*   £ m ⊢@{iPropI Σ} ||={⊤|⊤,∅|∅}=> ||▷=>^n ⌜ φ ⌝) → *)
(*   φ. *)
(* Proof. *)
(*   intros Hiter. eapply (fupd2_soundness (m+n)). *)
(*   intros Hinv. iIntros "[Hm Hn]". *)
(*   iMod (Hiter with "Hm") as "Hupd". clear Hiter. *)
(*   iInduction n as [|n] "IH"; simpl. *)
(*   - iModIntro. done.  *)
(*   - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]". *)
(*     iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd". *)
(*     by iApply ("IH" with "Hn Hupd"). *)
(* Qed. *)

Lemma bupd_laterN_plain_interweave {PROP : bi}
    `{BiBUpd PROP} `{BiPlainly PROP} `{BiBUpdPlainly PROP}
    (P : PROP) (n : nat) `{!Plain P} :
  Nat.iter n (λ P, |==> ▷ P) P ⊢ ▷^n P.
Proof.
  iIntros "Hn". iInduction n as [|n] "IH"; first done.
  simpl. iMod "Hn". iNext. iApply "IH". iFrame.
Qed.

Lemma interweave_iter_intro {PROP : bi}
    `{BiBUpd PROP} `{BiPlainly PROP} `{BiBUpdPlainly PROP}
    (P : PROP) (n : nat) :
  P ⊢ Nat.iter n (λ P, |==> ▷ P) P.
Proof.
  iIntros "Hn". iInduction n as [|n] "IH"; first done.
  simpl. iModIntro. iNext. iApply "IH". auto.
Qed.

Lemma interweave_iter_weaken {PROP : bi}
    `{BiBUpd PROP} `{BiPlainly PROP} `{BiBUpdPlainly PROP}
    (P : PROP) (n1 n2 : nat) :
  n1 <= n2 ->
  Nat.iter n1 (λ P, |==> ▷ P) P ⊢ Nat.iter n2 (λ P, |==> ▷ P) P.
Proof.
  iIntros (Hle) "Hn".
  iInduction n2 as [|n2] "IH"
forall (n1 Hle).
  - destruct n1;[|lia]. auto.
  - simpl. destruct n1.
    + simpl.
      iApply interweave_iter_intro.
      iModIntro. by iNext.
    + simpl.
      iMod "Hn". iModIntro. iNext.
      iApply "IH";[|iFrame]. iPureIntro.
      lia.
Qed.

Lemma laterN_weaken {PROP : bi}
    `{BiBUpd PROP} `{BiPlainly PROP} `{BiBUpdPlainly PROP}
    (P : PROP) (n1 n2 : nat) :
  n1 <= n2 ->
  ▷^n1 P ⊢ ▷^n2 P.
Proof.
  iIntros (Hle) "Hn".
  iInduction n2 as [|n2] "IH"
forall (n1 Hle).
  - destruct n1;[|lia]. auto.
  - simpl. destruct n1.
    + simpl. iModIntro. iModIntro.
      auto.
    + simpl. iNext.
      iApply "IH";[|iFrame]. iPureIntro.
      lia.
Qed.

(* Old proof that doesn't work. We keep it here for reference. *)
(* Lemma step_fupdN_fresh_soundness {Λ Σ} {Ω : gGenCmras Σ} `{!invGpreS Σ} (φ : Prop) ns ncurr k k2 f g: *)
(*   (∀ (Hi: invGS Σ), ⊢ |={⊤}=> *)
(*     ∃ (HI: irisGS Λ Σ) (Hpf1: iris_invGS = Hi) *)
(*      (Hpf2: num_laters_per_step = f) (Hpf2: step_count_next = g), *)
(*       (|={⊤}=> step_fupdN_fresh ncurr ns ( *)
(*        £ (k + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝))%I) → *)
(*   φ. *)
(* Proof. *)
(*   intros Hiter. *)
(*   set (step1 := (fresh_later_count f g ncurr ns + S k + k2)). *)
(*   set (step2 := (fresh_later_count f g ncurr ns + k + k2)). *)
(*   eapply (step_fupd2N_soundness step1 step2). *)
(*   iIntros (Hinv) "Hlc". *)
(*   iMod (Hiter Hinv) as (Hiris <- <- <-) "H". *)
(*   clear Hiter. *)
(*   (* poor mans iInduction. *) *)
(*   iRevert "Hlc H". *)
(*   iStopProof. *)
(*   generalize dependent ncurr. simpl. *)
(*   induction ns as [|n' ns IH]; iIntros (ncurr) "_ Hlc H". *)
(*   - rewrite /step_fupdN_fresh. *)
(*     iMod "H". iMod ("H" with "Hlc") as "H". iModIntro. *)
(*     rewrite fresh_later_count_nil. *)
(*     replace (0 + S k) with (k + 1) by lia. *)
(*     rewrite -!assoc -step_fupd2N_add. *)
(*     iApply (step_fupd2N_wand with "H"). iIntros "H". *)
(*     rewrite -step_fupd2N_add. *)
(*     iMod "H". iApply (fupd2_mask_intro); [done..|]. iIntros "_". *)
(*     done. *)
(*   - iAssert (emp)%I as "#IH"; first done. *)
(*     rewrite plainly_emp_2 IH. clear IH. *)
(*     rewrite /step_fupdN_fresh -/step_fupdN_fresh. *)
(*     iMod "H". *)
(*     rewrite fresh_later_count_cons. *)
(*     iEval (rewrite !lc_split -assoc) in "Hlc". *)
(*     iDestruct "Hlc" as "[[[Hlc1 _] Hlc2] Hlck]". *)
(*     iMod ("H" with "Hlc1") as "H". iModIntro. *)
(*     iEval (rewrite -!assoc -step_fupd2N_add). *)
(*     iApply (step_fupd2N_wand with "H"). iIntros "H". *)
(*     iApply step_fupd2_fupd2N; first lia. *)
(*     do 2 iMod "H". *)
(*     iModIntro. *)
(*     iEval rewrite -step_fupd2N_add. replace 3 with (2 + 1) by lia. *)
(*     iEval (rewrite -step_fupd2N_add). *)
(*     iApply (step_fupd2N_wand with "H"). iIntros "H". *)
(*     iMod "H". *)
(*     (* iSpecialize ("IH" $! _). *) *)
(*     rewrite (nextgen_intro_plain (■ _)). *)
(*     rewrite plainly_elim. *)
(*     iDestruct (nextgen_wand with "IH [Hlc2 Hlck]") as "IH2". *)
(*     { iModIntro. iEval rewrite !lc_split. by iFrame. } *)
(*     iClear "IH". *)
(*     iDestruct (nextgen_wand with "IH2 H") as "IH". *)
(*     (* iMod "H" as "H". *) *)
(*     (* iMod ("IH" $! with "H [Hlc2 Hlck]") as "H". *) *)
(*     (* { iEval rewrite !lc_split. by iFrame. } *) *)
(*     (* do 3 iModIntro. rewrite assoc. done. *) *)
(* Abort. *)



Definition fupd_res `{!invGS Σ} `{Ω : gGenCmras Σ} E1 E2 n : iProp Σ :=
  later_credits.lc_supply n ∗ wsat_all ∗
  ownE (AlwaysEn ∪ MaybeEn1 E1 ∪ MaybeEn2 E2).

Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn2 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (MaybeEn1 _ ## MaybeEn2 _) => apply MaybeEn12_disj : core.

Notation "'|==£>' P" := (later_credits.le_upd.le_upd P%I) (at level 99, P at level 200, format "|==£>  P") : bi_scope.

Lemma fupd_to_bupd_res_credit_gen `{!invGS Σ} `{Ω : gGenCmras Σ} E1 E2 E n m P :
  m <= n ->
  fupd_res E1 E m -∗
  £ n -∗
  (|={E1,E2}=> P) -∗
  |==> ◇ (fupd_res E2 E m ∗ £ n ∗ P).
Proof.
  intros Hle.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iIntros "(H● & Hw & HE) Hlc H".
  rewrite ownE_op. 2: { apply disjoint_union_l. auto. }
  iDestruct "HE" as "(HE & HE2)".
  iSpecialize ("H" with "[$Hw HE]").
  { iApply (ownE_weaken with "HE"). set_solver. }
  rewrite later_credits.le_upd.le_upd_unfold.
  iMod ("H" with "H●") as "[(H● & >(? & HE & ?)) | noway]"; last first.
  { iDestruct "noway" as (? ?) "[H● ?]".
    iDestruct (lc_supply_bound with "H● [$]") as "%".
    lia. }
  iModIntro.
  iModIntro.
  iFrame.
  iCombine "HE HE2" as "HH".
  rewrite -ownE_op. 2: { apply disjoint_union_l. auto. }
  done.
Qed.

Lemma fupd_to_bupd_res_credit `{!invGS Σ} `{Ω : gGenCmras Σ} E1 E2 E n P :
  fupd_res E1 E n -∗
  £ n -∗
  (|={E1,E2}=> P) -∗
  |==> ◇ (fupd_res E2 E n ∗ £ n ∗ P).
Proof.
  iApply fupd_to_bupd_res_credit_gen.
  lia.
Qed.

Lemma fupd2_to_bupd_res_credit_gen `{!invGS Σ} `{Ω : gGenCmras Σ} E1a E1b E2a E2b n m P :
  m <= n ->
  fupd_res E1a E1b m -∗
  £ n -∗
  (||={E1a|E1b,E2a|E2b}=> P) -∗
  |==> ◇ (fupd_res E2a E2b m ∗ £ n ∗ P).
Proof.
  (* rewrite uPred_fupd2_eq /uPred_fupd2_def. *)
  intros Hle.
  rewrite uPred_fupd2_eq /uPred_fupd2_def.
  iIntros "(H● & Hw & HE) ? H".
  iSpecialize ("H" with "[$Hw $HE]").
  rewrite later_credits.le_upd.le_upd_unfold.
  iMod ("H" with "H●") as "[(H● & >(? & HE & ?)) | noway]"; last first.
  { iDestruct "noway" as (? ?) "[H● ?]".
    iDestruct (lc_supply_bound with "H● [$]") as "%".
    lia. }
  iModIntro.
  iModIntro.
  iFrame.
Qed.

Lemma fupd2_to_bupd_res_credit `{!invGS Σ} `{Ω : gGenCmras Σ} E1a E1b E2a E2b n P :
  fupd_res E1a E1b n -∗
  £ n -∗
  (||={E1a|E1b,E2a|E2b}=> P) -∗
  |==> ◇ (fupd_res E2a E2b n ∗ £ n ∗ P).
Proof.
  iApply fupd2_to_bupd_res_credit_gen.
  lia.
Qed.

(* Lemma fupd2_to_bupd_res `{!invGS Σ} E1a E1b E2a E2b n P : *)
(*   fupd_res E1a E1b n -∗ *)
(*   (||={E1a|E1b,E2a|E2b}=> P) -∗ *)
(*   ∃ k, ⌜ k ≤ n ⌝ /\  Nat.iter (S k) (λ Q, |==> ▷ Q) (fupd_res E2a E2b k ∗ P). *)
(* Proof. *)
(*   (* rewrite uPred_fupd2_eq /uPred_fupd2_def. *) *)
(*   rewrite uPred_fupd2_eq /uPred_fupd2_def. *)
(*   iIntros "(H● & Hw & HE) H". *)
(*   iSpecialize ("H" with "[$Hw $HE]"). *)
(*   iDestruct (le_upd.le_upd_elim with "H● H") as "H". *)
(*   rewrite -Nat.add_1_r. rewrite Nat.iter_add. *)
(*   iApply (iter_modal_mono with "[] H"). *)
(*   { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. } *)
(*   iIntros "H". simpl. iMod "H" as ">H". *)
(*   iDestruct "H" as (m Hle) "[? >[? [? ?]]]". *)
(*   iModIntro. iNext. rewrite /fupd_res. iFrame. *)
(*   iExists m. iFrame. auto. *)
(* Qed. *)

Lemma fupd2_to_bupd_res_complete `{!invGS Σ} `{Ω : gGenCmras Σ} E1a E1b E2a E2b n P :
  fupd_res E1a E1b n -∗
  (||={E1a|E1b,E2a|E2b}=> P) -∗
  Nat.iter (S n) (λ Q, |==> ▷ Q) (◇ (wsat_all ∗ ownE (AlwaysEn ∪ MaybeEn1 E2a ∪ MaybeEn2 E2b) ∗ P)).
Proof.
  (* rewrite uPred_fupd2_eq /uPred_fupd2_def. *)
  rewrite uPred_fupd2_eq /uPred_fupd2_def.
  iIntros "(H● & Hw & HE) H".
  iSpecialize ("H" with "[$Hw $HE]").
  iDestruct (le_upd.le_upd_elim_complete with "H● H") as "H".
  iFrame.
Qed.



Lemma fupd2_to_bupd_res `{!invGS Σ} `{Ω : gGenCmras Σ} (k n : nat) P :
  fupd_res ∅ ∅ n -∗
  (||▷=>^k P) -∗
    Nat.iter (k * (2 * n + 2))
    (λ Q, |==> ▷ Q) (∃ k', ⌜ k' ≤ n ⌝ ∧ fupd_res ∅ ∅ k' ∗ P).
Proof.
  revert n; induction k; intros n.
  - rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.
    simpl. iIntros "(H● & Hw & HE) H".
    iFrame. eauto.
  - rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.
    iIntros "(H● & Hw & HE) H". iSimpl in "H".
    iSpecialize ("H" with "[$Hw $HE]").
    iDestruct (le_upd.le_upd_elim with "H● H") as "H".
    assert (S k * (2 * n + 2) = n + S (n + (1 + k * (2 * n + 2)))) as ->;[lia|].
    rewrite Nat.iter_add.
    iApply (iter_modal_mono with "[] H").
    { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
    iIntros "H". rewrite Nat.iter_succ.
    iMod "H" as ">H".
    iDestruct "H" as (k' Hle) "(Hs & >Hr & >[Hc HH])".
    iModIntro. iNext. rewrite uPred_fupd2_eq /uPred_fupd2_def.
    iSpecialize ("HH" with "[$Hr $Hc]").
    iDestruct (le_upd.le_upd_elim with "Hs HH") as "H".
    rewrite Nat.iter_add.
    iApply interweave_iter_weaken;[apply Hle|].
    iApply (iter_modal_mono with "[] H").
    { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
    iIntros "H". rewrite Nat.iter_succ.
    iMod "H" as ">H".
    iDestruct "H" as (k'' Hle') "(Hs & >Hr & >[Hc HH])".
    iDestruct (IHk with "[$Hs $Hr $Hc] [HH]") as "t".
    { rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.
      rewrite {1}uPred_fupd2_eq /uPred_fupd2_def. auto. }
    iModIntro. iNext.
    assert (k * (2 * k'' + 2) <= k * (2 * n + 2)) as Hle3.
    { apply PeanoNat.Nat.mul_le_mono_l. lia. }
    iApply interweave_iter_weaken;[apply Hle3|].
    iApply (iter_modal_mono with "[] t").
    { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
    iIntros "(%k0 & %Hk0 & Hres)".
    iExists _. iFrame. iPureIntro.
    lia.
Qed.

Definition steps_sum_base (k1 k2 n : nat) :=
  (n + 1 + n + 1 + (k1 * (2 * n + 2)) + n + 1 + (k2 * (2 * n + 2))).

Lemma fupd2_fupd2_to_bupd_res `{!invGS Σ} `{Ω : gGenCmras Σ} (k1 k2 n: nat) P :
  fupd_res ⊤ ⊤ n -∗
  (|={⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k1 ||={∅|∅,∅|∅}=> ||▷=>^k2 P) -∗
  Nat.iter (steps_sum_base k1 k2 n) (λ Q, |==> ▷ Q) (∃ k', ⌜ k' ≤ n ⌝ ∧ fupd_res ∅ ∅ k' ∗ P).                                                      
Proof.
  rewrite {1}uPred_fupd_eq /uPred_fupd_def /steps_sum_base.
  iIntros "(H● & Hw & HE) H".
  rewrite ownE_op;cycle 1.
  { rewrite /AlwaysEn /MaybeEn1 /MaybeEn2.
    apply disjoint_union_l. split.
    - apply coPset_inl_inr_disj.
    - apply MaybeEn12_disj. }
  iDestruct "HE" as "[HE HE']".
  rewrite -!(Nat.add_assoc n) Nat.iter_add.
  iSpecialize ("H" with "[$Hw $HE]").
  iDestruct (le_upd.le_upd_frame_l with "[$H HE']") as "H";[iExact "HE'"|].
  iDestruct (le_upd.le_upd_elim with "H● H") as "H".
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite {1}Nat.add_1_l !Nat.add_succ_l Nat.iter_succ.
  iMod "H" as ">H". iDestruct "H" as (h Hleh) "(Hs & HE' & >Hr & >[Hc HH])".
  iModIntro. iNext.
  iCombine "Hc" "HE'" as "Hc".
  rewrite -ownE_op;cycle 1.
  { rewrite /AlwaysEn /MaybeEn1 /MaybeEn2.
    apply disjoint_union_l. split.
    - apply coPset_inl_inr_disj.
    - apply MaybeEn12_disj. }
  
  rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.
  rewrite -!(Nat.add_assoc n) Nat.iter_add.
  iSpecialize ("HH" with "[$Hr $Hc]").
  iDestruct (le_upd.le_upd_elim with "Hs HH") as "H".
  iApply interweave_iter_weaken;[apply Hleh|].
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite {1}Nat.add_1_l !Nat.add_succ_l Nat.iter_succ.
  iMod "H" as ">H". iDestruct "H" as (k' Hle) "(Hs & >Hr & >[Hc HH])".
  iModIntro. iNext. assert (n + (n + (0 + 2)) = 2 * n + 2) as ->;[lia|].
  iDestruct (fupd2_to_bupd_res with "[$Hs $Hr $Hc] HH") as "HH".
  rewrite -!(Nat.add_assoc (k1 * (2 * n + 2))) Nat.iter_add.
  assert (k1 * (2 * k' + 2) <= k1 * (2 * n + 2)) as Hle1.
  { apply PeanoNat.Nat.mul_le_mono_l. lia. }
  iApply interweave_iter_weaken;[apply Hle1|].
  iApply (iter_modal_mono with "[] HH").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite -!(Nat.add_assoc n) Nat.iter_add.
  rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.  
  iDestruct "H" as (k'' Hle2) "((Hs&?&?) & Hr)".
  iSpecialize ("Hr" with "[$]").
  iDestruct (le_upd.le_upd_elim with "Hs Hr") as "H".
  iApply (interweave_iter_weaken _ k'');[lia|].
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite {1}Nat.add_1_l Nat.iter_succ.
  iMod "H" as ">H".
  iDestruct "H" as (k''' Hle3) "(Hs & >Hr & >[Hc HH])".
  iModIntro. iNext.
  iDestruct (fupd2_to_bupd_res with "[$Hs $Hr $Hc] HH") as "HH".
  iApply (interweave_iter_weaken _ (k2 * (2 * k''' + 2))).
  { apply PeanoNat.Nat.mul_le_mono_l. lia. }
  iApply (iter_modal_mono with "[] HH").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "(%k0 & %Hk0 & Hres)".
  iExists _. iFrame. iPureIntro.
  lia.
Qed.

Definition steps_sum_layer (k1 k2 n : nat) :=
  (n + 1 + n + 1 + (k1 * (2 * n + 2)) + n + 1 + n + 1 + (k2 * (2 * n + 2)) + n + 1).
  
Lemma fupd2_fupd2_fupd2_to_bupd_res `{!invGS Σ} `{Ω : gGenCmras Σ} (k1 k2 n: nat) P :
  fupd_res ⊤ ⊤ n -∗
  (|={⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k1 ||={∅|∅,⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k2 ||={∅|∅,⊤|⊤}=> P) -∗
  Nat.iter (steps_sum_layer k1 k2 n) (λ Q, |==> ▷ Q) (∃ k', ⌜ k' ≤ n ⌝ ∧ fupd_res ⊤ ⊤ k' ∗ P).                                                      
Proof.
  rewrite {1}uPred_fupd_eq /uPred_fupd_def /steps_sum_layer.
  iIntros "(H● & Hw & HE) H".
  rewrite ownE_op;cycle 1.
  { rewrite /AlwaysEn /MaybeEn1 /MaybeEn2.
    apply disjoint_union_l. split.
    - apply coPset_inl_inr_disj.
    - apply MaybeEn12_disj. }
  iDestruct "HE" as "[HE HE']".
  rewrite -!(Nat.add_assoc n) Nat.iter_add.
  iSpecialize ("H" with "[$Hw $HE]").
  iDestruct (le_upd.le_upd_frame_l with "[$H HE']") as "H";[iExact "HE'"|].
  iDestruct (le_upd.le_upd_elim with "H● H") as "H".
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite {1}Nat.add_1_l !Nat.add_succ_l Nat.iter_succ.
  iMod "H" as ">H". iDestruct "H" as (h Hleh) "(Hs & HE' & >Hr & >[Hc HH])".
  iModIntro. iNext.
  iCombine "Hc" "HE'" as "Hc".
  rewrite -ownE_op;cycle 1.
  { rewrite /AlwaysEn /MaybeEn1 /MaybeEn2.
    apply disjoint_union_l. split.
    - apply coPset_inl_inr_disj.
    - apply MaybeEn12_disj. }
  
  rewrite {1}uPred_fupd2_eq /uPred_fupd2_def /steps_sum_layer.
  rewrite -!(Nat.add_assoc n) Nat.iter_add.
  iSpecialize ("HH" with "[$Hr $Hc]").
  iDestruct (le_upd.le_upd_elim with "Hs HH") as "H".
  iApply interweave_iter_weaken;[apply Hleh|].
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite {1}Nat.add_1_l !Nat.add_succ_l Nat.iter_succ.
  iMod "H" as ">H". iDestruct "H" as (k' Hle) "(Hs & >Hr & >[Hc HH])".
  iModIntro. iNext. assert (n + (n + (0 + 2)) = 2 * n + 2) as ->;[lia|].
  iDestruct (fupd2_to_bupd_res with "[$Hs $Hr $Hc] HH") as "HH".
  rewrite -!(Nat.add_assoc (k1 * (2 * n + 2))) Nat.iter_add.
  assert (k1 * (2 * k' + 2) <= k1 * (2 * n + 2)) as Hle1.
  { apply PeanoNat.Nat.mul_le_mono_l. lia. }
  iApply interweave_iter_weaken;[apply Hle1|].
  iApply (iter_modal_mono with "[] HH").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite -!(Nat.add_assoc n) Nat.iter_add.
  rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.  
  iDestruct "H" as (k'' Hle2) "((Hs&?&?) & Hr)".
  iSpecialize ("Hr" with "[$]").
  iDestruct (le_upd.le_upd_elim with "Hs Hr") as "H".
  iApply (interweave_iter_weaken _ k'');[lia|].
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite Nat.add_1_l !Nat.add_succ_l Nat.iter_succ.
  iMod "H" as ">H".
  iDestruct "H" as (k''' Hle3) "(Hs & >Hr & >[Hc HH])".
  iModIntro. iNext. rewrite -!(Nat.add_assoc n) Nat.iter_add.
  rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.
  iSpecialize ("HH" with "[$]").
  iDestruct (le_upd.le_upd_elim with "Hs HH") as "H".
  iApply (interweave_iter_weaken _ k''');[lia|].
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". rewrite Nat.add_1_l !Nat.add_succ_l Nat.iter_succ.
  iMod "H" as ">H".
  iDestruct "H" as (k4 Hle4) "(Hs & >Hr & >[Hc HH])".
  iModIntro. iNext. rewrite -(Nat.add_assoc _ n 1).
  rewrite Nat.iter_add.
  iDestruct (fupd2_to_bupd_res with "[$Hs $Hr $Hc] HH") as "HH".
  iApply (interweave_iter_weaken _ (k2 * (2 * k4 + 2))).
  { apply PeanoNat.Nat.mul_le_mono_l. lia. }  
  iApply (iter_modal_mono with "[] HH").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "(%k0 & %Hk0 & [(Hlc&?&?) HP])".
  rewrite {1}uPred_fupd2_eq /uPred_fupd2_def.
  iSpecialize ("HP" with "[$]").
  iDestruct (le_upd.le_upd_elim with "Hlc HP") as "H".
  rewrite Nat.iter_add.
  iApply (interweave_iter_weaken _ k0);[lia|].
  iApply (iter_modal_mono with "[] H").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "H". simpl.
  iMod "H" as ">H".
  iDestruct "H" as (m Hm) "(Hs & >Hall & >H1 & >Hp)".
  iModIntro. iNext. iExists _. iFrame.
  iPureIntro. lia.
Qed.

Lemma fupd2_iter_frame `{!invGS Σ} `{Ω : gGenCmras Σ} (k1 : nat) P Q :
  P -∗
  (||▷=>^k1 Q) -∗
  (||▷=>^k1 P ∗ Q).
Proof.
  induction k1; iIntros "HP HQ".
  - simpl. iFrame.
  - simpl. 
    iDestruct (fupd2_frame_l _ _ _ _ P with "[$HP $HQ]") as "HP".
    iApply (fupd2_mono with "HP").
    iIntros "[HP HQ]".
    iNext. iApply (IHk1 with "HP"). auto.
Qed.
    
Lemma fupd2_fupd2_fupd2_frame `{!invGS Σ} `{Ω : gGenCmras Σ} (k1 k2 : nat) P Q :
  P -∗
  (||={⊤|⊤,∅|∅}=> ||▷=>^k1 ||={∅|∅,⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k2 ||={∅|∅,⊤|⊤}=> Q) -∗
  (||={⊤|⊤,∅|∅}=> ||▷=>^k1 ||={∅|∅,⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k2 ||={∅|∅,⊤|⊤}=> P ∗ Q).
Proof.
  iIntros "HP HQ".
  iDestruct (fupd2_frame_l _ _ _ _ P with "[$HP $HQ]") as "HP".
  iApply (fupd2_mono with "HP").
  iIntros "[HP HQ]".
  iDestruct (fupd2_iter_frame with "HP HQ") as "HP".
  iApply (iter_modal_mono with "[] HP").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "[HP HQ]".
  iDestruct (fupd2_frame_l _ _ _ _ P with "[$HP $HQ]") as "HP".
  iApply (fupd2_mono with "HP").
  iIntros "[HP HQ]".
  iDestruct (fupd2_frame_l _ _ _ _ P with "[$HP $HQ]") as "HP".
  iApply (fupd2_mono with "HP").
  iIntros "[HP HQ]".
  iDestruct (fupd2_iter_frame with "HP HQ") as "HP".
  iApply (iter_modal_mono with "[] HP").
  { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
  iIntros "[HP HQ]".
  iDestruct (fupd2_frame_l _ _ _ _ P with "[$HP $HQ]") as "HP".
  auto.
Qed.

Fixpoint fresh_later_count f g ncurr (ns: list nat) :=
  match ns with
  | [] => 0
  | n :: ns' => (crash_adequacy.steps_sum f g ncurr (S n)) + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'
  end.

Lemma fresh_later_count_nil f g ncurr :
  fresh_later_count f g ncurr nil = 0.
Proof. simpl. lia. Qed.
Lemma fresh_later_count_cons f g ncurr n (ns': list nat) :
  fresh_later_count f g ncurr (n::ns') = (crash_adequacy.steps_sum f g ncurr (S n))
                 + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'.
Proof. simpl. lia. Qed.

Lemma steps_sum_base_mono k1 k2 n1 n2 :
  n1 <= n2 ->
  steps_sum_base k1 k2 n1 <= steps_sum_base k1 k2 n2.
Proof.
  rewrite /steps_sum_base.
  intros.
  apply Nat.add_le_mono; [|apply Nat.mul_le_mono_l;lia].
  repeat (apply Nat.add_le_mono;auto).
  apply Nat.mul_le_mono_l;lia.
Qed.

Lemma steps_sum_layer_mono k1 k2 k1' n1 n2 :
  n1 <= n2 ->
  k1 <= k1' ->
  steps_sum_layer k1 k2 n1 <= steps_sum_layer k1' k2 n2.
Proof.
  rewrite /steps_sum_layer.
  intros.
  repeat (apply Nat.add_le_mono;try done).
  all: apply Nat.mul_le_mono;auto;lia.
Qed.

Local Existing Instances ngLc_inG.

Lemma step_fupdN_fresh_soundness {Λ Σ} {Ω : gGenCmras Σ}
    `{Hinvpre: !invGpreS Σ} `{!ngInvG Σ Ω}
    (φ : Prop) ns ncurr k1 k2 f g :
  (∀ (Hi : invGS Σ)
     (* (Hpf1: inv_inG = Hinvpre) *)
     (* (Hpf1: lcGS_inG = lcGpreS_inG) *), ⊢ |={⊤}=>
    ∃ (HI : irisGS Λ Σ Ω)
      (Hpf1: iris_invGS = Hi)
      (Hpf2 : num_laters_per_step = f) (Hpf2: step_count_next = g),
      (|={⊤}=> step_fupdN_fresh ncurr ns (
       £ (k1 + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k1 ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  set (stepih := (fresh_later_count f g ncurr ns)).
  set (step2 := (stepih + (k1 + k2))).
  assert (∃ MAX, step2 <= MAX) as [MAX HMAX];[eauto|].
  set (stepb := steps_sum_base k1 k2 MAX).
  set (step1 := ((length ns * steps_sum_layer stepih 2 MAX) + S stepb)).
  apply (pure_soundness (M := iResUR Σ)).
  apply (laterN_soundness _ step1).
  iMod (lc_alloc MAX) as (C Hlceq) "[H● Hlc]".
  iMod wsat_alloc as (Hw ? Hpre) "[Hw HE]".
  rewrite H in Hlceq. rewrite H.
  iApply bupd_plain.
  iDestruct (Hiter _) as "H". clear Hiter.
  rewrite /step1 -PeanoNat.Nat.add_succ_comm.
  iDestruct (fupd_to_bupd_res_credit ⊤ ⊤ ⊤ with "[$H● $Hw HE] Hlc H") as ">>H'".
  { iApply (ownE_weaken with "HE"). set_solver. }
  iClear "H".
  iDestruct "H'" as "((H● & Hw & HE) & Hlc & H)".
  iDestruct "H" as (Hiris <- <- <-) "H".
  iModIntro. simpl. iNext.
  iDestruct (lc_weaken with "Hlc") as "Hlc";[eauto|].
  
  (* poor mans iInduction. *)
  iRevert "Hw HE Hlc H H●".
  iStopProof.
  generalize dependent ncurr.
  generalize dependent MAX.
  induction ns as [|n' ns IH]; iIntros (MAX stepb ncurr stepih step2 ??) "_ Hw HE Hlc H H●".
  - rewrite /step1 /step2 /stepb /=.
    iDestruct (fupd_frame_l with "[$H Hlc]") as "H";[iExact "Hlc"|].
    rewrite wand_elim_r.
    iDestruct (fupd2_fupd2_to_bupd_res with "[$H● $Hw $HE] H") as "Hres".
    iApply bupd_laterN_plain_interweave.
    iApply (iter_modal_mono with "[] Hres").
    { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
    iIntros "(%k0 & %Hk0 & Hres & HP)". auto.
  - rewrite {1}/step_fupdN_fresh.
    set (n := crash_adequacy.steps_sum num_laters_per_step step_count_next ncurr (S n')).
    set (m := fresh_later_count num_laters_per_step step_count_next (Nat.iter (S n') step_count_next ncurr) ns).
    rewrite -/step_fupdN_fresh.
    rewrite {1}/step2 {1}/stepih fresh_later_count_cons -/m -/n.
    rewrite -!(Nat.add_assoc n).
    iDestruct "Hlc" as "[Hn Hsum]".
    iDestruct (fupd_frame_l with "[$H Hn]") as "H";[iExact "Hn"|].
    rewrite wand_elim_r.
    iDestruct (fupd2_fupd2_fupd2_frame with "Hsum H") as "H'".
    iDestruct (fupd2_fupd2_fupd2_to_bupd_res with "[$H● $Hw $HE] H'") as "H".
    simpl length.
    replace (S (length ns) * (steps_sum_layer stepih 2 MAX) + stepb) with
      (steps_sum_layer stepih 2 MAX + ((length ns) * steps_sum_layer stepih 2 MAX + stepb));[|lia].
    iApply laterN_add.
    iApply bupd_laterN_plain_interweave.
    assert (steps_sum_layer n 2 MAX <= steps_sum_layer stepih 2 MAX) as Hle.
    { apply steps_sum_layer_mono;auto. rewrite /n /stepih.
      rewrite fresh_later_count_cons. lia. }
    iApply (interweave_iter_weaken);[apply Hle|].
    iApply (iter_modal_mono with "[] H").
    { iIntros (? ?) "H >H'". iModIntro. iNext. iApply "H";auto. }
    iIntros "H".
    iDestruct "H" as (k'' Hlek) "((Hs & Hw & He) & Hc & Hih)".
    iApply nextgen_plain_plain.
    (* TODO: see if the following can be fixed *)
    assert (@ngLcGS Σ Ω lcGS_inG) as Hnglc; [rewrite H Hlceq;apply _|].
    rewrite H in Hnglc. rewrite -Hpre in ngInvG0.
    iModIntro.
    iDestruct (lc_supply_bound with "Hs Hc") as %Hbound.
    specialize (IH k'' (Nat.iter (S n') step_count_next ncurr)).
    rewrite -/m in IH. simpl in IH.
    iDestruct (IH with "[] Hw He Hc Hih Hs") as "t";[done|done|..].
    iApply (laterN_weaken with "t").
    rewrite /stepb. apply Nat.add_le_mono.
    + apply Nat.mul_le_mono_l.
      apply steps_sum_layer_mono;auto.
      rewrite /m /stepih fresh_later_count_cons. lia.
    + apply steps_sum_base_mono;auto.
Qed.
  
Record recv_adequate {Λ CS} (s : stuckness) (e1 r1: expr Λ) (σ1 : state Λ) (g1 : global_state Λ)
    (φ φr: val Λ → state Λ → global_state Λ → Prop) (φinv: state Λ → global_state Λ → Prop)  := {
  recv_adequate_result_normal t2 σ2 g2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (of_val v2 :: t2, (σ2,g2)) Normal →
   φ v2 σ2 g2;
  recv_adequate_result_crashed t2 σ2 g2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (of_val v2 :: t2, (σ2,g2)) Crashed →
   φr v2 σ2 g2;
  recv_adequate_not_stuck t2 σ2 g2 e2 stat :
   s = NotStuck →
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2 g2);
  recv_adequate_inv t2 σ2 g2 stat :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
   φinv σ2 g2
}.

Lemma recv_adequate_alt {Λ CS} s e1 r1 σ1 g1 (φ φr : val Λ → state Λ → global_state Λ → Prop) φinv :
  recv_adequate (CS := CS) s e1 r1 σ1 g1 φ φr φinv ↔ ∀ t2 σ2 g2 stat,
    erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2 g2)) ∧
      (∀ v2 t2', t2 = of_val v2 :: t2' →
                 match stat with
                   | Normal => φ v2 σ2 g2
                   | Crashed => φr v2 σ2 g2
                 end) ∧
      (φinv σ2 g2).
Proof.
  split.
  - intros [] ??? []; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wp_recv_adequacy_inv Σ {Ω : gGenCmras Σ} Λ CS
  `{!invGpreS Σ} `{!ngInvG Σ Ω}
  nsinit s e r σ g φ φr φinv f1 f2:
  (∀ `(Hinv : !invGS Σ) κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → iProp Σ) (* for the initial generation *)
         (global_stateI : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ) Hpf1a Hpf1b
         Φinv,
        let HI :=
          Perennial.program_logic.crash_weakestpre.IrisGS Λ Σ Ω Hinv global_stateI
            fork_post f1 f2 Hpf1a Hpf1b in
        let HI2 := IrisGS Λ Σ Ω HI stateI in
       ■ (∀ σ nt, stateI σ nt -∗ |={⊤, ∅}=> ⌜ φinv σ ⌝) ∗ (* φinv for initial gen. *)
       ■ (Φinv Hinv -∗ □ ∀ σ nt, stateI σ nt -∗ |={⊤, ∅}=> ⌜ φinv σ ⌝) ∗ (* φinv for later generations *)
       stateI σ 0 ∗ global_stateI g nsinit 1%Qp ∅ κs ∗
       wpr CS s ⊤ e r (λ v, ⌜φ v⌝) (Φinv Hinv) (λ v, ⌜φr v⌝)) →
  recv_adequate (CS := CS) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 g2 stat [n [κs H]]%erased_rsteps_nrsteps.
  (* we apply adequacy twice, for not_stuck and the rest.
     probably we can somehow avoid all this code duplication... *)
  split; last first.
  { destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns' nsinit
              (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
               (S (S (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit)))))
         => Hinv.
  iMod (Hwp Hinv κs) as (stateI global_stateI fork_post Hpf1a Hpf1b) "H".
  iDestruct "H" as (Φinv) "(#Hinv1&#Hinv2&Hσ&Hg&H)".
  iModIntro.
  set (HI := Perennial.program_logic.crash_weakestpre.IrisGS
    Λ Σ Ω Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b).
  set (HI2 := IrisGS Λ Σ Ω HI stateI).
  iExists HI2.
  iDestruct (wptp_recv_strong_adequacy
               (Φinv' := (∀ σ nt, state_interp σ nt -∗ |={⊤, ∅}=> ⌜ φinv σ ⌝)%I)
               (κs' := []) with "[Hσ] [Hg] [H] [] []") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  do 3 iExists eq_refl. 
  iModIntro.
  iApply (step_fupdN_fresh_wand with "H").
  { auto. }
  iModIntro.
  iIntros "H [Hlc1 Hlc2]".
  iMod ("H" with "Hlc1") as "H".
  iApply (step_fupd2N_wand with "H"); auto.
  iModIntro. iIntros "H".
  iMod "H" as (v2 ??) "(Hσ&Hg&Hv&Hfpost)".
  destruct stat.
  - iDestruct "Hv" as "(Hv&#Hinv)".
    rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv" with "[$]") as "Hp".
    iApply fupd2_mask_intro; [done..|]. iIntros "_".
    iApply step_fupd2N_later.
    repeat iModIntro. iSplit; last done.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  - rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv1" with "[$]") as "Hp".
    iApply fupd2_mask_intro; [done..|]. iIntros "_".
    iApply step_fupd2N_later.
    repeat iModIntro. iSplit; last done.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  }
  { intros e2 -> He2.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns' nsinit
              (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
                (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit) + 1))
         => Hinv.
  (* iIntros "HNC". *)
  iMod (Hwp Hinv κs) as (stateI global_stateI fork_post Hpf1a Hpf1b) "H".
  iDestruct "H" as (Φinv) "(#Hinv1&#Hinv2&Hσ&Hg&H)".
  iModIntro.
  set (HI := Perennial.program_logic.crash_weakestpre.IrisGS
    Λ Σ Ω Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b).
  set (HI2 := IrisGS Λ Σ Ω HI stateI).
  iExists HI2.
  iDestruct (wptp_recv_progress
    (Φinv' := (∀ σ nt, state_interp σ nt -∗ |={⊤, ∅}=> ⌜ φinv σ ⌝)%I)
               (κs' := []) with "[Hσ] [Hg] [H] [] []") as "H"; [eauto..|].
  { rewrite app_nil_r. auto. }
  do 3 iExists eq_refl. iModIntro.
  iApply (step_fupdN_fresh_wand with "H"); first done.
  iModIntro.
  (* iIntros (?). *)
  iIntros "H Hlc".
  iApply "H". iExactEq "Hlc". f_equiv; first done.
  rewrite assoc. f_equiv. done. }
Qed.
