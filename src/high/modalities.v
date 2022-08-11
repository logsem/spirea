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
  MonPred (λ i, P ((store_view (i.1),
                     (flush_view i.1 ⊔ buffer_view i.1),
                     buffer_view i.1), i.2)) _.
  (* MonPred (λ '(s, p, b), P (s, (p ⊔ b), ∅)) _. *)
Next Obligation.
  intros Σ P.
  do 2 intros [[[??]?]?].
  intros [[[??]?] [= ->]].
  assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<fence>' P" :=
  (post_fence P) (at level 20, right associativity) : bi_scope.

Program Definition post_fence_sync `{nvmBaseFixedG Σ, nvmBaseDeltaG}
        (P : dProp Σ) : dProp Σ :=
  MonPred (λ i,
    bi_wand
      (persisted (buffer_view i.1))
      (P ((store_view i.1,
          (flush_view i.1 ⊔ buffer_view i.1),
           buffer_view i.1), i.2))
  ) _.
Next Obligation.
  intros Σ ?? P.
  do 2 intros [[[??]?]?].
  intros [[[??]?] [= ->]].
  simpl.
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
  MonPred (λ i, P (store_view i.1, flush_view i.1, ∅, i.2)) _.
Next Obligation.
  intros Σ P.
  do 2 intros [[[??]?]?]. intros [[[??]?] [= ->]].
  simpl.
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<nobuf>' P" :=
  (no_buffer P) (at level 20, right associativity) : bi_scope.

Program Definition no_flush `{Σ : gFunctors} (P : dProp Σ) : dProp Σ :=
  MonPred (λ i, P (store_view i.1, ∅, ∅, i.2)) _.
Next Obligation.
  intros Σ P.
  do 2 intros [[[??]?]?]. intros [[[??]?] [= ->]].
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<noflush>' P" :=
  (no_flush P) (at level 20, right associativity) : bi_scope.
