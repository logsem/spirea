From iris.algebra Require Import gmap numbers.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import base tactics classes.

From Perennial.base_logic.lib Require Import ncfupd.

From self.algebra Require Import view.
From self.lang Require Import memory.
From self.base Require Import primitive_laws.
From self.high Require Import dprop resources.

Program Definition post_fence {Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, P (store_view TV,
                    (flush_view TV ⊔ buffer_view TV),
                    buffer_view TV)) _.
  (* MonPred (λ '(s, p, b), P (s, (p ⊔ b), ∅)) _. *)
Next Obligation.
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<fence>' P" :=
  (post_fence P) (at level 20, right associativity) : bi_scope.

Program Definition post_fence_sync `{nvmBaseFixedG Σ, nvmBaseDeltaG Σ}
        (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    bi_wand
      (persisted (buffer_view TV))
      (P (store_view TV,
          (flush_view TV ⊔ buffer_view TV),
           buffer_view TV))
  ) _.
Next Obligation.
  intros Σ ?? P. intros [[??]?] [[??]?] [[??]?]. simpl.
  assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
  iIntros "pers P".
  iApply monPred_mono; last iApply "pers".
  { repeat split; done. }
  iApply (persisted_anti_mono with "P").
  done.
Qed.

Notation "'<fence_sync>' P" :=
  (post_fence_sync P) (at level 20, right associativity) : bi_scope.

Program Definition no_buffer `{Σ : gFunctors} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, P (store_view TV, flush_view TV, ∅)) _.
Next Obligation.
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<nobuf>' P" :=
  (no_buffer P) (at level 20, right associativity) : bi_scope.

Program Definition no_flush `{Σ : gFunctors} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, P (store_view TV, ∅, ∅)) _.
Next Obligation.
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<noflush>' P" :=
  (no_flush P) (at level 20, right associativity) : bi_scope.
