From iris.algebra Require Import agree.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.

From self Require Import generation_update_next.
From self.algebra Require Import view.
From self Require Import hvec.
From iris_named_props Require Import named_props.

Definition crashed_at_inG Σ Ω := genInG Σ Ω (agreeR viewO) [].

Instance genInSelgG_empty Σ Ω :
  ∀ i : fin 0, genInSelfG Σ Ω ([]%IL !!! i).
Proof. intros i. inversion i. Qed.

Section crashed_at.
  Context `{i : !genInDepsG Σ Ω (agreeR viewO) [] }.

  Definition crashed_at γ (CV : view) : iProp Σ :=
    "agree" ∷ gen_own (i := genInDepsG_gen i) γ (to_agree CV) ∗
    "rely" ∷ rely_self (g := genInG_genInSelfG (genInDepsG_gen i))
      γ (λ t, ∃ (CV2 : view), t = const (to_agree CV2))%type%stdpp.

  Lemma crashed_at_nextgen γ CV :
    crashed_at γ CV ⊢ ⚡==> ∃ CV2, crashed_at γ CV2.
  Proof.
    iNamed 1.
    iModIntro.
    iDestruct "agree" as (t) "[picked1 agree]".
    iDestruct "rely" as "[rely (%t' & %HP & picked2)]".
    iDestruct (gen_picked_in_agree with "picked1 picked2") as %<-.
    destruct HP as (CV2 & eq).
    iExists CV2.
    rewrite eq. simpl.
    iFrame.
  Qed.

End crashed_at.
