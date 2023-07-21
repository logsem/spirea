From Equations Require Import Equations.
From iris.algebra Require Import agree.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.

From self Require Import generation_update_next.
From self Require Import hvec.
From self Require Import cmra_morphism_extra.
From self.algebra Require Import view.
From self.nextgen Require Import types. (* FIXME: Should not need this *)

Definition crashed_at_inG Σ Ω := genInG Σ Ω (agreeR viewO) [].

Instance genInSelgG_empty Σ Ω :
  ∀ i : fin 0, genInSelfG Σ Ω ([]%IL !!! i).
Proof. intros i. inversion i. Qed.

Instance genInSelgG_one Σ Ω n A (DS : ivec n cmra):
  genInG Σ Ω A DS →
  ∀ i : fin 1, genInSelfG Σ Ω ([A]%IL !!! i).
Proof.
  intros ? i.
  dependent elimination i.
Qed.

Section crashed_at.
  Context `{i : !genInDepsG Σ Ω (agreeR viewO) [] }.

  Definition crashed_at_pred (PV : view) : pred_over (agreeR viewO) :=
    λ t, ∃ (CV : view), PV ⊑ CV ∧ t = const (to_agree CV).

  (* Definition pred : pred_over (agreeR viewO) := *)
  (*   λ t, ∃ (CV2 : view), t = const (to_agree CV2). *)

  Definition crashed_at_rel PV : rel_over [] (agreeR viewO) :=
    crashed_at_pred PV.

  Definition crashed_at γ (CV : view) : iProp Σ :=
    "agree" ∷ gen_own (i := genInDepsG_gen i) γ (to_agree CV) ∗
    "rely" ∷ rely γ [] (crashed_at_rel ∅) (crashed_at_pred ∅).
    (* "rely" ∷ rely_self (g := genInG_genInSelfG (genInDepsG_gen i)) γ pred. *)

  Lemma crashed_at_alloc CV :
    ⊢ |==> ∃ γ, crashed_at γ CV.
  Proof.
    iMod (own_gen_alloc (DS := []) (to_agree CV) [] [] with "[]") as (γ) "(HO & tok)".
    { done. }
    { iIntros (i'). inversion i'. }
    iMod (
      token_strengthen_promise (DS := [])
        _ [] [] _ (crashed_at_rel ∅) _ (crashed_at_pred ∅) with "[] tok").
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      exists (const (to_agree ∅)).
      split; first apply _.
      exists ∅. done. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iExists (γ). iFrame "HO".
    iApply token_to_rely. done.
  Qed.

  Lemma crashed_at_nextgen γ CV :
    crashed_at γ CV ⊢ ⚡==> ∃ CV2, crashed_at γ CV2.
  Proof.
    iNamed 1.
    iModIntro.
    iDestruct "agree" as (t) "[picked1 agree]".
    iDestruct "rely" as "[rely (%t' & % & (? & %HP) & picked2 & ?)]".
    iDestruct (gen_picked_in_agree with "picked1 picked2") as %<-.
    destruct HP as (CV2 & ? & eq).
    iExists CV2.
    rewrite eq. simpl.
    iFrame.
  Qed.

End crashed_at.

Definition persisted_genInG Σ Ω := genInG Σ Ω (authR viewUR) [agreeR viewO].

Section persisted.
  Context `{!genInDepsG Σ Ω (agreeR viewO) [] }.
  (* Context `{EqDecision loc}. *)
  Context `{i : !genInDepsG Σ Ω (authR viewUR) [agreeR viewO] }.
  Context (persist_view_name : gname).
  Context (crashedγ : gname).

  Local Definition persisted_rel : rel_over [agreeR viewO] (authR viewUR) :=
    λ tC tP,
      ∃ CV, tC = const (to_agree CV) ∧ tP = fmap_auth (const (view_to_zero CV)).

  Definition persisted_auth PV : iProp Σ :=
    gen_own persist_view_name (● PV) ∗
    rely_self crashedγ (crashed_at_pred PV).

  Definition persisted PV : iProp Σ :=
    gen_own persist_view_name (◯ PV) ∗
    rely_self crashedγ (crashed_at_pred PV).

  Lemma post_crash_persisted PV :
    persisted PV -∗
    ⚡==> persisted (view_to_zero PV) ∗
          ∃ CV, ⌜ PV ⊑ CV ⌝ ∗ crashed_at crashedγ CV.
  Proof.
  Admitted.

End persisted.
