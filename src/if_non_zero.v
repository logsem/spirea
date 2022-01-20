From iris.bi Require Import fractional.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import agree.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From self Require Import extra.
From self.base Require Import primitive_laws.

Set Default Proof Using "Type*".

Lemma mk_Qp_Qp_to_Qc qp prf : (* Upstreamed *)
  mk_Qp (Qp_to_Qc qp) prf = qp.
Proof. by apply Qp_to_Qc_inj_iff. Qed.

Section if_non_zero.
  Context `{BiAffine PROP}.

  Implicit Types (P : Qp → PROP).

  Definition if_non_zero (q : Qc) P : PROP :=
    match (decide (0 < q)%Qc) with
      left prf => P (mk_Qp q prf)
    | right prf => ⌜q = 0%Qc⌝
    end.

  Lemma if_non_zero_cases q P :
    if_non_zero q P
      ⊣⊢ ⌜q = 0%Qc⌝ ∨ ∃ qp, ⌜(0 < q)%Qc⌝ ∗ ⌜q = Qp_to_Qc qp⌝ ∗ P qp.
  Proof.
    rewrite /if_non_zero.
    iSplit.
    - destruct (decide (0 < q)%Qc).
      * iIntros. iRight. iExists _. iFrame. done.
      * auto.
    - iIntros "[->|H]"; first done.
      iDestruct "H" as (qp) "(% & % & ?)".
      rewrite decide_True_pi. simplify_eq. rewrite mk_Qp_Qp_to_Qc. iFrame.
  Qed.

  Lemma if_non_zero_ge_0 q P : if_non_zero q P -∗ ⌜(0 ≤ q)%Qc⌝.
  Proof.
    rewrite /if_non_zero. destruct (decide (0 < q)%Qc).
    - iIntros. iPureIntro. apply Qclt_le_weak. done.
    - iIntros (->). done.
  Qed.

  Lemma if_non_zero_add (P : Qp → PROP) `{!Fractional P} p q :
    ⊢ P p -∗ if_non_zero q P -∗ if_non_zero (q + (Qp_to_Qc p)) P.
  Proof.
    iIntros "P P'".
    iApply if_non_zero_cases. iRight.
    iDestruct (if_non_zero_cases with "P'") as "[-> | H]".
    - iExists _. iFrame. iPureIntro.
      rewrite Qcplus_0_l.
      split; last done. apply Qp_prf.
    - iDestruct "H" as (qp) "(%gt & %eq & P')".
      iExists (p + qp)%Qp.
      rewrite (fractional p qp).
      iFrame.
      iPureIntro.
      subst.
      rewrite -Qp_to_Qc_inj_add.
      split.
      * apply Qp_prf.
      * rewrite (comm _ qp). done.
  Qed.

  Lemma if_non_zero_subtract (P : Qp → PROP) `{!Fractional P} p q :
    (Qp_to_Qc p ≤ q)%Qc →
    ⊢ if_non_zero q P -∗ if_non_zero (q - Qp_to_Qc p) P ∗ P p.
  Proof.
    iIntros (le) "P".
    iDestruct (if_non_zero_cases with "P") as "[-> | H]".
    - exfalso.
      apply Qcle_not_lt in le.
      apply (le (Qp_prf _)).
    - iDestruct "H" as (qp) "(%gt & %eq & P')".
      rewrite /if_non_zero.
      destruct (decide (0 < q - Qp_to_Qc p)%Qc).
      * rewrite -fractional.
        eassert (qp = _) as ->; last iFrame.
        apply Qp_to_Qc_inj_iff.
        rewrite Qp_to_Qc_inj_add.
        simpl.
        rewrite /Qcminus.
        rewrite -Qcplus_assoc.
        rewrite (Qcplus_comm _ (Qp_to_Qc _)).
        rewrite Qcplus_opp_r.
        rewrite Qcplus_0_r.
        done.
      * rewrite eq in n.
        subst.
        destruct (decide (qp = p)) as [eq|neq].
        + subst.
          erewrite <- Qcplus_opp_r.
          naive_solver.
        + exfalso.
          apply n.
          pose proof (Qp_prf p).
          pose proof (Qp_prf qp).
          apply (Qclt_minus_iff (Qp_to_Qc p)).
          apply Qcle_lt_or_eq in le.
          destruct le as [?|eq%Qp_to_Qc_inj_iff]; done.
  Qed.

  Lemma if_non_zero_exchange_1 (q1 q2 : Qc) p (P Q : Qp → PROP)
        `{!Fractional P, !Fractional Q}:
    (Qp_to_Qc p ≤ q2)%Qc →
    P p ∗ if_non_zero q1 P ∗ if_non_zero q2 Q ⊢
    if_non_zero (q1 + Qp_to_Qc p) P ∗ if_non_zero (q2 - Qp_to_Qc p) Q ∗ Q p.
  Proof.
    iIntros (le) "(P & ZP & ZQ)".
    iDestruct (if_non_zero_subtract with "ZQ") as "[$ $]"; first done.
    iApply (if_non_zero_add with "P [$]").
  Qed.

  Lemma mk_Qp_1 prf : mk_Qp 1 prf = 1%Qp.
  Proof. apply Qp_to_Qc_inj_iff. simpl. by rewrite Z2Qc_inj_1. Qed.

  (* Lemma mk_Qp_0 prf : mk_Qp 0 prf = 0%Qp. *)
  (* Proof. apply Qp_to_Qc_inj_iff. simpl. by rewrite Z2Qc_inj_1. Qed. *)

  Lemma if_non_zero_0 (P : Qp → PROP) :
    if_non_zero 0%Qc P = (⌜0 = 0⌝)%Qc%I.
  Proof. done. Qed.

  Lemma if_non_zero_1 (P : Qp → PROP) :
    if_non_zero 1%Qc P = P 1%Qp.
  Proof. rewrite /if_non_zero. simpl. by rewrite mk_Qp_1. Qed.

  (** A soft disjunction where instead of having only the left side or the right
  side we have a fraction of the right side and a fraction of the left side. *)
  Definition soft_disj (Q P : Qp → PROP) : PROP :=
    ∃ (q p : Qc), ⌜(q + p = 1)%Qc⌝ ∗ (if_non_zero q Q) ∗ (if_non_zero p P).

  Lemma soft_disj_exchange_l Q P `{!Fractional P, !Fractional Q} q :
    (□ ∀ q, Q q -∗ ⌜q ≤ 1⌝)%Qp -∗
    (* (□ ∀ q, P q -∗ ⌜q ≤ 1⌝)%Qp -∗ *)
    soft_disj Q P -∗ Q q -∗ soft_disj Q P ∗ P q.
  Proof.
    iIntros "#Qval".
    iDestruct 1 as (q' p') "(%eq & HQ & HP)".
    iIntros "Q".
    iAssert (⌜(Qp_to_Qc q ≤ p')%Qc⌝)%I as %le.
    { iDestruct (if_non_zero_cases with "HQ") as "[-> | H]".
      - rewrite Qcplus_0_l in eq.
        rewrite eq.
        iDestruct ("Qval" with "Q") as %le.
        iPureIntro.
        apply Qp_to_Qc_inj_le in le.
        apply le.
      - iDestruct "H" as (qp) "(%gt & %eq' & P')".
        iCombine "Q P'" as "Q".
        rewrite -fractional.
        iDestruct ("Qval" with "Q") as %le.
        iPureIntro.
        apply Qp_to_Qc_inj_le in le.
        rewrite Qp_to_Qc_inj_add in le.
        rewrite -eq' in le.
        simpl in le.
        assert (p' = 1 - q')%Qc as ->.
        { rewrite -eq.
          rewrite Qcplus_comm.
          rewrite /Qcminus.
          rewrite -Qcplus_assoc.
          rewrite Qcplus_opp_r.
          by rewrite Qcplus_0_r. }
        rewrite Qcplus_le_mono_r.
        etrans; first apply le.
        rewrite /Qcminus.
        rewrite -Qcplus_assoc.
        rewrite (Qcplus_comm _ q').
        rewrite Qcplus_opp_r.
        done. }
    iDestruct (if_non_zero_exchange_1 q' p' _ Q P with "[Q HQ HP]") as "(? & ? & hi)".
    2: { iFrame "Q". iFrame "HQ". iFrame "HP". }
    { done. }
    iFrame.
    iExists _, _. iFrame. iPureIntro.
    rewrite Qcplus_assoc.
    rewrite (Qcplus_comm _ p').
    rewrite -Qcplus_assoc.
    rewrite -Qcplus_assoc.
    rewrite (Qcplus_opp_r (Qp_to_Qc q)).
    rewrite Qcplus_0_r.
    rewrite Qcplus_comm.
    done.
  Qed.

End if_non_zero.
