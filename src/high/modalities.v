From iris.algebra Require Import gmap numbers.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import base tactics classes.

From Perennial.base_logic.lib Require Import ncfupd.

From self.algebra Require Import view.
From self.lang Require Import memory.
From self.high Require Import dprop resources.

Program Definition post_fence {Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ tv, P (store_view tv,
                    (flush_view tv ⊔ wb_buffer_view tv),
                    wb_buffer_view tv)) _.
  (* MonPred (λ '(s, p, b), P (s, (p ⊔ b), ∅)) _. *)
Next Obligation.
  (* FIXME: Figure out if there is a way to make [solve_proper] handle this,
  perhaps by using [pointwise_relatio]. *)
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<fence>' P" := (post_fence P) (at level 20, right associativity) : bi_scope.

Class IntoFence {Σ} (P: dProp Σ) (Q : dProp Σ) :=
  into_crash : P -∗ <fence> Q.

Section post_fence.
  Context `{Σ : iprop.gFunctors}.

  Implicit Types (P : dProp Σ).

  Lemma post_fence_at P tv :
    ((<fence> P) tv = P (store_view tv, (flush_view tv ⊔ wb_buffer_view tv), wb_buffer_view tv))%I.
  Proof. done. Qed.

  Lemma post_fence_at_alt P SV PV BV :
    ((<fence> P) (SV, PV, BV) = P (SV, PV ⊔ BV, BV))%I.
  Proof. done. Qed.

  Lemma post_fence_sep P Q : <fence> P ∗ <fence> Q ⊣⊢ <fence> (P ∗ Q).
  Proof.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    cbn.
    rewrite monPred_at_sep.
    iSplit; iIntros "$".
  Qed.

  Lemma post_fence_mono P Q : (P -∗ Q) -∗ post_fence P -∗ post_fence Q.
  Proof.
    iStartProof (iProp _).
    iIntros (TV) "pToQ".
    rewrite 2!monPred_at_wand.
    simpl.
    iIntros (TV' ?).
    iApply "pToQ".
    iPureIntro.
    destruct TV as [[??]?].
    destruct TV' as [[??]?].
    repeat split.
    - apply H.
    - apply view_le_lub_l. apply H.
    - apply H.
  Qed.

  Lemma post_fence_objective' P : post_fence (<obj> P) ⊢ P.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite post_fence_at.
    rewrite monPred_at_objectively.
    naive_solver.
  Qed.

  Lemma post_fence_objective P `{!Objective P} : post_fence P ⊢ P.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite post_fence_at. iApply objective_at.
  Qed.

  Global Instance post_fence_persistent P :
    Persistent P → Persistent (post_fence P).
  Proof.
    rewrite /Persistent.
    intros pers.
    iStartProof (iProp _).
    iIntros (TV) "H".
    rewrite post_fence_at.
    iApply pers.
    iApply "H".
  Qed.

  Lemma post_fence_extract P Q :
    post_fence P -∗ (P -∗ <pers> <obj> Q) -∗ post_fence P ∗ Q.
  Proof.
    iIntros "P pToQ".
    iEval (rewrite -(post_fence_objective' Q)).
    rewrite post_fence_sep.
    iApply (post_fence_mono with "[pToQ] P").
    iIntros "P".
    iDestruct ("pToQ" with "P") as "#Q".
    iFrame "∗#".
  Qed.

  Lemma post_fence_extract' P `{!Persistent Q, !Objective Q} :
    post_fence P -∗ (P -∗ Q) -∗ post_fence P ∗ Q.
  Proof.
    iIntros "P pToQ".
    iEval (rewrite -(post_fence_objective Q)).
    rewrite post_fence_sep.
    iApply (post_fence_mono with "[pToQ] P").
    iIntros "P".
    iDestruct ("pToQ" with "P") as "#Q".
    iFrame "∗#".
  Qed.

End post_fence.

Program Definition no_buffer {Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ tv, P (store_view tv, flush_view tv, ∅)) _.
Next Obligation.
  (* FIXME: Figure out if there is a way to make [solve_proper] handle this,
  perhaps by using [pointwise_relation]. *)
  intros Σ P. intros [[??]?] [[??]?] [[??]?]. simpl.
  apply monPred_mono.
  rewrite !subseteq_prod'.
  done.
Qed.

Notation "'<nobuf>' P" :=
  (no_buffer P) (at level 20, right associativity) : bi_scope.

Section no_buffer.
End no_buffer.
