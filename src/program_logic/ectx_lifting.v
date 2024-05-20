(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export ectx_language.
From self.program_logic Require Import lifting crash_weakestpre.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ Ω}.
Context {Hinh : Inhabited (state Λ)} {Hginh : Inhabited (global_state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant e := reducible_not_val e inhabitant.
Local Hint Resolve reducible_not_val_inhabitant : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma wp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E}=∗
    ⌜head_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜head_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1". iMod ("H" with "Hσ1 Hg1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext. iIntros (e2 σ2 g2 efs Hstep).
  iIntros "Hlc".
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E}=∗
    ⌜head_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜head_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 nt ∗ global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1". iMod ("H" $! σ1 with "Hσ1 Hg1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 g2 efs Hstep).
  iMod ("H" $! v2 σ2 g2 efs with "[//]") as "(-> & ? & ? & ?) /=". by iFrame.
Qed.
End wp.
