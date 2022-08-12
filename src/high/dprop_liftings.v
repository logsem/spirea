From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From self Require Import extra.
From self.algebra Require Import ghost_map ghost_map_map.
From self.base Require Import primitive_laws.
From self.high Require Import dprop monpred_simpl predicates.

Definition lift_d {Σ} P : dProp Σ := with_gnames (λ nD, ⎡ P nD ⎤)%I.

Section lift_d_lemmas.
  Context {Σ : gFunctors}.

  Lemma lift_wand (P Q : _ → iProp Σ) :
    (lift_d (λ nD, Q nD -∗ P nD)) -∗
    (lift_d Q -∗ lift_d P).
  Proof.
    iModel. simpl.
    monPred_simpl.
    iIntros "impl".
    iIntros ([??] [? [= <-]]).
    simpl.
    monPred_simpl.
    done.
  Qed.

  Lemma lift_wand_pure (Q : _ → iProp Σ) P :
    lift_d (λ nD, Q nD -∗ ⌜ P ⌝) -∗
    lift_d Q -∗ ⌜ P ⌝.
  Proof.
    iModel. simpl.
    monPred_simpl.
    iIntros "impl".
    iIntros ([??] [? [= <-]]).
    simpl.
    monPred_simpl.
    done.
  Qed.

  Lemma lift_intros (P : _ → iProp Σ) :
    ⎡ ∀ nD, P nD ⎤ -∗ lift_d P.
  Proof.
    iModel. simpl.
    monPred_simpl.
    iIntros "impl".
    iApply "impl".
  Qed.

End lift_d_lemmas.

(* This tactic eases the proof of lemmas for definitions involving [lift_d].
   It applies structural rules to turn the goal into one consisting only of assertions in [iProp]. *)
Ltac lift_d_extract :=
  iStartProof;
  rewrite -?lift_wand_pure;
  rewrite -?lift_wand;
  rewrite -?lift_intros;
  iModIntro;
  iIntros (nD).

Definition crashed_at_d `{nvmBaseFixedG Σ} CV : dProp Σ :=
  lift_d (λ nD, crashed_at CV)%I.

Definition persisted_loc_d `{nvmBaseFixedG Σ} ℓ t : dProp Σ :=
  lift_d (λ nD, persisted_loc ℓ t)%I.

Lemma crashed_at_d_agree `{nvmBaseFixedG Σ} CV CV' :
  crashed_at_d CV -∗ crashed_at_d CV' -∗ ⌜CV = CV'⌝.
Proof. lift_d_extract. iApply crashed_at_agree. Qed.

Section lemmas.
  Context `{nvmBaseFixedG Σ}.

  Lemma persisted_loc_d_weak ℓ t1 t2 :
    t2 ≤ t1 → persisted_loc_d ℓ t1 -∗ persisted_loc_d ℓ t2.
  Proof.
    intros le.
    lift_d_extract.
    iApply persisted_loc_weak.
    done.
  Qed.

End lemmas.

Section post_crash_interact.
  Context `{nvmG Σ}.

  Context `{AbstractState ST}.

  Definition know_preorder_loc_d `{Countable ST} ℓ (preorder : relation2 ST) : dProp Σ :=
    lift_d (λ nD, know_preorder_loc ℓ (abs_state_relation (ST := ST)))%I.

  Definition know_pred_d `{Countable ST} ℓ (ϕ : predicate ST) : dProp Σ :=
    lift_d (λ nD, know_pred ℓ ϕ)%I.

  Definition is_at_loc_d ℓ : dProp Σ :=
    lift_d (λ nD, own shared_locs_name (◯ {[ ℓ ]}))%I.

  Definition is_na_loc_d ℓ : dProp Σ :=
    lift_d (λ nD, own exclusive_locs_name (◯ {[ ℓ ]}))%I.

  Definition offset_loc ℓ (t : nat) : dProp Σ :=
    lift_d (λ nD, ℓ ↪[offset_name]□ t)%I.

  Definition know_na_view_d ℓ q (SV : view) : dProp Σ :=
    lift_d (λ nD, ℓ ↪[non_atomic_views_gname]{#q} SV)%I.

  Definition know_bumper_d ℓ (bumper : ST → ST) : dProp Σ :=
    lift_d (λ nD, know_bumper ℓ bumper)%I.

  Definition know_full_history_loc_d `{Countable ST}
             ℓ q (abs_hist : gmap time ST) : dProp Σ :=
    lift_d (λ nD, full_entry_unenc abs_history_name ℓ q abs_hist)%I.

  Definition crashed_in_mapsto_d `{Countable ST} ℓ (s : ST) : dProp Σ :=
    lift_d (λ nD,
      ∃ es, ⌜ decode es = Some s ⌝ ∗ ℓ ↪[crashed_in_name]□ es)%I.

  Definition know_frag_history_loc_d `{Countable ST} ℓ t (s : ST) : dProp Σ :=
    lift_d (λ nD, know_frag_history_loc ℓ t s)%I.

  Lemma know_full_entry_frag_entry_unenc ℓ q abs_hist t s :
    know_full_history_loc_d ℓ q abs_hist -∗
    know_frag_history_loc_d ℓ t s -∗
    ⌜ abs_hist !! t = Some s ⌝.
  Proof.
    rewrite /know_full_history_loc_d.
    rewrite /know_frag_history_loc_d.
    lift_d_extract.
    iApply full_entry_frag_entry_unenc.
  Qed.

  Lemma offset_loc_agree ℓ t1 t2 :
    offset_loc ℓ t1 -∗
    offset_loc ℓ t2 -∗
    ⌜ t1 = t2 ⌝.
  Proof.
    rewrite /offset_loc.
    iStartProof.
    lift_d_extract.
    iApply (ghost_map_elem_agree _ _ _ _ t1).
  Qed.

End post_crash_interact.
