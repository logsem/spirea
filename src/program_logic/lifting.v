(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import tactics.
From self.program_logic Require Export crash_weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ Ω}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

(* Lemma wp_lift_step_ncfupdN s E Φ e1 : *)
(*   to_val e1 = None → *)
(*   (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |={E,∅}=> *)
(*     |={∅}▷=>^(S $ num_laters_per_step ns) *)
(*     ⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗ *)
(*     ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ *)
(*       £ (S $ num_laters_per_step ns) *)
(*        -∗ |NC={∅,E}=> *)
(*       state_interp σ2 (length efs + nt) ∗ *)
(*       global_state_interp g2 (step_count_next ns) mj D κs ∗ *)
(*       WP e2 @ s; E {{ Φ }} ∗ *)
(*       [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}) *)
(*   ⊢ WP e1 @ s; E {{ Φ }}. *)
(* Proof. *)
(*   rewrite wp_eq /wp_def !wpc_unfold /wpc_pre=>->. *)
(*   iIntros "H" (mj). iSplit; last first. *)
(*   { iIntros. iApply step_fupd_extra.step_fupd2N_inner_later; auto. iNext; iFrame. } *)
(*   iIntros (????????) "Hσ Hg HNC Hlc". *)
(*   iSpecialize ("H" with "[$] [$]"). *)
(*   rewrite ncfupd_eq. *)
(*   iMod ("H" with "[$]") as "(H&HNC)". *)
(*   iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver+..|]. *)
(*   iModIntro. iApply step_fupd_extra.step_fupdN_step_fupd2N. *)
(*   iApply (step_fupdN_wand with "H"). iIntros "($&H)". *)
(*   iIntros. iMod "Hclo". iMod ("H" with "[//] Hlc [$]") as "(($ & $ & He & Hef)&HNC)". *)
(*   iModIntro. iFrame. iSplitL "He". *)
(*   - iApply wpc0_wpc. *)
(*     iApply (wpc_strong_mono' with "[$]"); auto. *)
(*     destruct (to_val); set_solver. *)
(*   - iApply (big_sepL_mono with "Hef")=>???/=. iApply wpc0_wpc. *)
(* Qed. *)

Lemma wp_lift_step_fupdN s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |={E,∅}=>
    |={∅}▷=>^(S $ num_laters_per_step ns)
    ⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗
      £ (S $ num_laters_per_step ns)
       -∗ |={∅,E}=>
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
Admitted.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E,∅}=∗ ▷
    (⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗
      £ (S $ num_laters_per_step ns)
      ={∅,E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros ?. rewrite -wp_lift_step_fupdN; [|done]. simpl.
  iIntros "H". iIntros (????????) "Hσ Hg".
  iMod ("H" with "[$] [$]") as "(Hr&N)".
  iModIntro.
  iApply step_fupdN_intro; first done.
  iModIntro. iNext. iModIntro. iNext. eauto.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗
      £ (S (num_laters_per_step ns))
      ={E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1".
  iMod ("H" with "[$] [$]") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose". iNext.
  iIntros (e2 ???) "%Hstep Hlater". iMod "Hclose". iMod ("H" with "[//] [$]") as "($ & $ & H & ?)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iFrame. iModIntro. iApply wp_value; last done. by apply of_to_val.
Qed.

End lifting.
