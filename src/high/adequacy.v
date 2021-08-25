From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.

From Perennial.program_logic Require Import recovery_adequacy.

From self.base Require Import adequacy. (* To get [recv_adequace]. *)
From self.high Require Import weakestpre resources.
From self.high Require Import recovery_weakestpre.
(* From Perennial.program_logic Require Export crash_lang recovery_weakestpre. *)
(* From Perennial.program_logic Require Import crash_adequacy. *)

Lemma high_recv_adequacy (Σ : gFunctors) s k e r σ g (φ φr : val → Prop) :
  valid_heap σ.1 →
  (∀ `{nF : !nvmFixedG Σ, nD : !nvmDeltaG Σ},
    ⊢ ⎡ ([∗ map] l ↦ v ∈ σ.1, l ↦h v) ⎤ -∗
      (wpr s k ⊤ e r (λ v, ⌜φ v⌝) (λ _ v, ⌜φr v⌝))) →
  recv_adequate s (ThreadState e ε) (ThreadState r ε) σ g
                (λ v _ _, φ v.(val_val)) (λ v _ _, φr v.(val_val)).
Proof.
  intros val.
Admitted.
