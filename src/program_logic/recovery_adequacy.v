From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang.
Import uPred.

From self.nextgen Require Import nextgen_promises.
From self.program_logic Require Export crash_adequacy recovery_weakestpre.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section recovery_adequacy.
  Context {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ}.
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
      (£ (steps_sum num_laters_per_step step_count_next ncurr n) -∗
       ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
      ∃ e2 t2',
      ⌜ t2 = e2 :: t2' ⌝ ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
      from_option Φ True (to_val e2) ∗
      ([∗ list] v ∈ omap to_val t2', fork_post v))).
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
      let ntot := (steps_sum num_laters_per_step step_count_next
                             (Nat.iter (sum_crash_steps ns) step_count_next ncurr )
                             n)  in
      let ntot' := ((Nat.iter (n + sum_crash_steps ns) step_count_next ncurr)) in
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

Fixpoint fresh_later_count f g ncurr (ns: list nat) :=
  match ns with
  | [] => 0
  | n :: ns' => S (S (S (crash_adequacy.steps_sum f g ncurr (S n))))
                 + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'
  end.

Lemma fresh_later_count_nil f g ncurr :
  fresh_later_count f g ncurr nil = 0.
Proof. simpl. lia. Qed.
Lemma fresh_later_count_cons f g ncurr n (ns': list nat) :
  fresh_later_count f g ncurr (n::ns') = crash_adequacy.steps_sum f g ncurr (S n) + 3
                 + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'.
Proof. simpl. lia. Qed.

Lemma step_fupdN_fresh_rearrange {Λ Σ Ω}
    `{!irisGS Λ Σ} φ ns ncurr k k2 :
  (|={⊤}=>
    step_fupdN_fresh (Ω := Ω) ncurr ns
      (£ (k + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝)) -∗
  £ (fresh_later_count num_laters_per_step step_count_next ncurr ns + k + k2) -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(fresh_later_count num_laters_per_step step_count_next ncurr ns + S k + k2) ⌜φ⌝.
Proof.
  iIntros "H Hlc".
  iInduction ns as [| n' ns] "IH" forall (ncurr).
  - rewrite /step_fupdN_fresh.
    iMod "H". iMod ("H" with "Hlc") as "H". iModIntro.
    rewrite fresh_later_count_nil.
    replace (0 + S k) with (k + 1) by lia.
    rewrite -!assoc -step_fupd2N_add.
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    rewrite -step_fupd2N_add.
    iMod "H". iApply (fupd2_mask_intro); [done..|]. iIntros "_".
    done.
  -
    (* iMod NC_alloc as (Hc') "HNC". *)
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
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    iMod "H".
Admitted.
    (* rewrite nextgen _plain *)
(*     iMod "H" as "H". *)
(*     iMod ("IH" $! with "H [Hlc2 Hlck]") as "H". *)
(*     { iEval rewrite !lc_split. by iFrame. } *)
(*     do 3 iModIntro. rewrite assoc. done. *)
(* Qed. *)

Lemma nextgen_lc {Σ} {Ω : gGenCmras Σ} `{!invGS Σ} k :
  £ k ⊢ ⚡==> £ k.
Proof. Admitted. (* We can bake this into [nextgen]. *)

#[global]
Instance into_nextgen_lc {Σ} {Ω : gGenCmras Σ} `{!invGS Σ} k :
  IntoNextgen _ _ := nextgen_lc k.

Lemma step_fupdN_fresh_soundness {Λ Σ} {Ω : gGenCmras Σ} `{!invGpreS Σ} (φ : Prop) ns ncurr k k2 f g:
  (∀ (Hi: invGS Σ), ⊢ |={⊤}=>
    ∃ (HI: irisGS Λ Σ) (Hpf1: iris_invGS = Hi)
     (Hpf2: num_laters_per_step = f) (Hpf2: step_count_next = g),
      (|={⊤}=> step_fupdN_fresh ncurr ns (
       £ (k + k2) -∗ ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅,∅|∅}=> ||▷=>^k2 ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (step_fupd2N_soundness (fresh_later_count f g ncurr ns + S k + k2) (fresh_later_count f g ncurr ns + k + k2)).
  iIntros (Hinv) "Hlc".
  iMod (Hiter Hinv) as (Hiris <- <- <-) "H".
  clear Hiter.
  (* poor mans iInduction. *)
  iRevert "Hlc H".
  iStopProof.
  revert ncurr.
  induction ns as [|n' ns IH]; iIntros (ncurr) "_ Hlc H".
  - rewrite /step_fupdN_fresh.
    iMod "H". iMod ("H" with "Hlc") as "H". iModIntro.
    rewrite fresh_later_count_nil.
    replace (0 + S k) with (k + 1) by lia.
    rewrite -!assoc -step_fupd2N_add.
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    rewrite -step_fupd2N_add.
    iMod "H". iApply (fupd2_mask_intro); [done..|]. iIntros "_".
    done.
  - iAssert (emp)%I as "#IH"; first done.
    rewrite plainly_emp_2 IH. clear IH.
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iMod "H".
    rewrite fresh_later_count_cons.
    iEval (rewrite !lc_split -assoc) in "Hlc".
    iDestruct "Hlc" as "[[[Hlc1 _] Hlc2] Hlck]".
    iMod ("H" with "Hlc1") as "H". iModIntro.
    iEval (rewrite -!assoc -step_fupd2N_add).
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    iApply step_fupd2_fupd2N; first lia.
    do 2 iMod "H".
    iModIntro.
    iEval rewrite -step_fupd2N_add. replace 3 with (2 + 1) by lia.
    iEval (rewrite -step_fupd2N_add).
    iApply (step_fupd2N_wand with "H"). iIntros "H".
    iMod "H".
    (* iSpecialize ("IH" $! _). *)
    rewrite (nextgen_intro_plain (■ _)).
    rewrite plainly_elim.
    iDestruct (nextgen_wand with "IH [Hlc2 Hlck]") as "IH2".
    { iModIntro. iEval rewrite !lc_split. by iFrame. }
    iClear "IH".
    iDestruct (nextgen_wand with "IH2 H") as "IH".
    (* iMod "H" as "H". *)
    (* iMod ("IH" $! with "H [Hlc2 Hlck]") as "H". *)
    (* { iEval rewrite !lc_split. by iFrame. } *)
    (* do 3 iModIntro. rewrite assoc. done. *)
Admitted.

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
    `{!invGpreS Σ} nsinit s e r σ g φ φr φinv f1 f2:
  (∀ `(Hinv : !invGS Σ) κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → iProp Σ) (* for the initial generation *)
         (global_stateI : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ) Hpf1a Hpf1b
         Φinv,
        let HI :=
          Perennial.program_logic.crash_weakestpre.IrisGS Λ Σ Hinv global_stateI
            fork_post f1 f2 Hpf1a Hpf1b in
        let HI2 := IrisGS Λ Σ HI stateI in
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
    Λ Σ Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b).
  set (HI2 := IrisGS Λ Σ HI stateI).
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
    Λ Σ Hinv (global_stateI) (fork_post) f1 f2 Hpf1a Hpf1b).
  set (HI2 := IrisGS Λ Σ HI stateI).
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

