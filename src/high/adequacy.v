From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.

From Perennial.program_logic Require Import recovery_adequacy.

From self.base Require Import adequacy. (* To get [recv_adequace]. *)
From self.high Require Import weakestpre resources.
From self.high Require Import recovery_weakestpre.
(* From Perennial.program_logic Require Export crash_lang recovery_weakestpre. *)
(* From Perennial.program_logic Require Import crash_adequacy. *)

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
  set (nsinit := (n * 4 + crash_borrow_ginv_number)).
  eapply (step_fupdN_fresh_soundness _ ns' nsinit
              (crash_adequacy.steps_sum _ _ (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
               (S (S (_ (Nat.iter (n' + sum_crash_steps ns') _ nsinit)))))
         => Hinv Hc.
Admitted.
