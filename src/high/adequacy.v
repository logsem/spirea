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

From self.lang Require Import lang.
From self.base Require Import adequacy. (* To get [recv_adequace]. *)
From self.high Require Import weakestpre resources.
From self.high Require Import recovery_weakestpre.
(* From Perennial.program_logic Require Export crash_lang recovery_weakestpre. *)
(* From Perennial.program_logic Require Import crash_adequacy. *)

Notation steps_sum := crash_adequacy.steps_sum.

Section recovery_adequacy.

  Context `{Σ : gFunctors}.
  Implicit Types s : stuckness.
  Implicit Types k : nat.
  (* Implicit Types P : iProp Σ. *)
  Implicit Types Φ : val → dProp Σ.
  Implicit Types Φinv : nvmDeltaG Σ → dProp Σ.
  Implicit Types Φc : nvmDeltaG Σ → val → dProp Σ.
  Implicit Types v : val.
  Implicit Types te : thread_state.
  Implicit Types e : expr.

  Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

  (*
  Lemma wptp_recv_strong_normal_adequacy Φ Φr κs' s k Hc t n ns ncurr mj D r1 e1 TV1 t1 κs t2 σ1 g1 σ2 g2 :
    nrsteps (CS := nvm_crash_lang) (ThreadState r1 ∅) (ns ++ [n]) ((ThreadState e1 TV1) :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
    state_interp σ1 (length t1) -∗
    global_state_interp g1 ncurr mj D (κs ++ κs') -∗
    ((wpr s k (* Hc t *) ⊤ e1 r1 Φ (* Φinv *) Φr) ∅) -∗
    wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
      ⌜ Hc' = Hc ∧ t' = t ⌝ ∗
      (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
      ∃ e2 TV2 t2',
      ⌜ t2 = (ThreadState e2 TV2) :: t2' ⌝ ∗
      ▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ncurr))))
          (⌜ ∀ te2, s = NotStuck → te2 ∈ t2 → not_stuck te2 σ2 g2 ⌝) ∗
      state_interp σ2 (length t2') ∗
      global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
      from_option (λ v, Φ v TV2) True (to_val e2) ∗
      ([∗ list] v ∈ omap to_val (ts_expr <$> t2'), fork_post v) ∗
      NC 1)).
  Proof.
  Admitted.
  *)
  (*   iIntros (Hstep) "Hσ Hg He Ht HNC". *)
  (*   inversion Hstep. subst. *)
  (*   iPoseProof (wptp_strong_adequacy with "Hσ Hg [He] Ht") as "H". *)
  (*   { eauto. } *)
  (*   {rewrite wpr_unfold /wpr_pre. iApply "He". } *)
  (*   rewrite perennial_crashG. *)
  (*   iSpecialize ("H" with "[$]"). *)
  (*   assert (ns = []) as ->; *)
  (*     first by (eapply nrsteps_normal_empty_prefix; eauto). *)
  (*   inversion H. subst. *)
  (*   rewrite /step_fupdN_fresh. *)
  (*   iSplitL ""; first by eauto. *)
  (*   iApply (step_fupd2N_wand with "H"); auto. *)
  (* Qed. *)

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

