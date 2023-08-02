From Equations Require Import Equations.
From iris.algebra Require Import agree.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.

From self Require Import hvec.
From self.nextgen Require Import cmra_morphism_extra nextgen_promises.
From self.algebra Require Import view.

Definition crashed_atR : cmra := prodR (agreeR viewO) (agreeR viewO).
Definition crashed_at_inG Σ Ω := genInG Σ Ω crashed_atR [].

Instance genInSelgG_empty Σ Ω :
  ∀ i : fin 0, genInSelfG Σ Ω ([]%IL !!! i).
Proof. intros i. inversion i. Qed.

Instance genInSelgG_one Σ Ω n A (DS : ivec n cmra):
  genInG Σ Ω A DS →
  ∀ i : fin 1, genInSelfG Σ Ω ([A]%IL !!! i).
Proof. intros ? i. dependent elimination i. Defined.

(* Names used:
 * - OV: The offset view, the sum of all crash views from prior generations
 * - OCV: The crash view including offsets
 * - OPV: The persist view including offsets
 * - CV: The crash view, CV = OCV - OV
 * - PV: The persist view, PV = OPV - OV
 *)

Section crashed_at.
  (* Resource for crashed at view *)
  Context `{caI : !genInDepsG Σ Ω crashed_atR [] }.
  (* Resource for views that depend on the crashed at view *)
  Context `{vI : !genInDepsG Σ Ω (authR viewUR) [crashed_atR] }.

  Definition crashed_at_trans OCV2 : crashed_atR → crashed_atR :=
    λ '(_, OCV), (OCV, to_agree OCV2).

  Instance crashed_at_trans_cmra_morphism OCV2 :
    CmraMorphism (crashed_at_trans OCV2).
  Proof. Admitted.

  Lemma crashed_at_trans_inj V1 V2 :
    crashed_at_trans V1 = crashed_at_trans V2 → V1 = V2.
  Proof.
    unfold crashed_at_trans.
    intros ?.
    specialize (equal_f H (to_agree (∅ : viewO), to_agree (∅ : viewO))).
    simpl.
    intros [= ?].
    done.
  Qed.

  Definition crashed_at_pred (OPV : view) : pred_over crashed_atR :=
    λ t, ∃ OCV2, OPV ⊑ OCV2 ∧ t = crashed_at_trans OCV2.

  Definition crashed_at_rel PV : rel_over [] crashed_atR :=
    crashed_at_pred PV.

  Definition crashed_at_offset γ OV OCV :=
    gen_own γ (to_agree OV, to_agree OCV).

  Definition crashed_at γ (CV : view) : iProp Σ :=
    ∃ (OV OCV LV : view),
      (* "%view_add" ∷ ⌜ OV `view_add` CV = OCV ⌝ ∗ *)
      "%view_eq" ∷ ⌜ OCV `view_sub` OV = CV ⌝ ∗
      "agree" ∷ gen_own γ (to_agree OV, to_agree OCV)
      (* ∗ "rely" ∷ rely γ [] (crashed_at_rel LV) (crashed_at_pred LV). *)
      ∗ "rely" ∷ rely_self γ (crashed_at_pred LV).

  Definition crashed_at_tok γ LV : iProp Σ :=
    token γ [] (crashed_at_rel LV) (crashed_at_pred LV).

  Lemma crashed_at_alloc CV :
    ⊢ |==> ∃ γ, crashed_at γ CV ∗ crashed_at_tok γ CV.
  Proof.
    iMod (own_gen_alloc (DS := [])
      (to_agree ∅, to_agree CV) [] [] with "[]") as (γ) "(HO & tok)".
    { done. }
    { iIntros (i'). inversion i'. }
    iMod (
      token_strengthen_promise (DS := [])
        _ [] [] _ (crashed_at_rel CV) _ (crashed_at_pred CV) with "[] tok")
      as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      exists (λ '(_, CV1), (CV1, to_agree CV)).
      split; first apply _.
      exists CV. done. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iExists (γ).
    iDestruct (token_to_rely with "tok") as "#R".
    iFrame.
    iExists ∅, CV, _. iFrame.
    iDestruct (rely_to_rely_self with "R") as "$".
    iPureIntro.
    apply view_sub_empty.
  Qed.

  (** Owning [crashed_at] gives [crashed_at] for some view in the next
   * generation. *)
  Lemma crashed_at_nextgen γ CV :
    crashed_at γ CV ⊢ ⚡==> ∃ CV2, crashed_at γ CV2.
  Proof.
    iNamed 1.
    iModIntro.
    iDestruct "agree" as (t) "[picked1 agree]".
    iDestruct "rely" as "[rely (%t' & %HP & picked2)]".
    (* iDestruct "rely" as "[rely (%t' & % & (? & %HP) & picked2 & ?)]". *)
    iDestruct (gen_picked_in_agree with "picked1 picked2") as %<-.
    destruct HP as (OCV2 & ? & eq).
    (* iExists _, _, _. *)
    unfold crashed_at.
    rewrite eq. simpl.
    iExists _, _, _, LV.
    iFrame.
    iPureIntro. reflexivity.
  Qed.

  Lemma crashed_at_pick_nextgen γ OV OCV OCV2 LV :
    LV ⊑ OCV2 →
    crashed_at_offset γ OV OCV -∗
    crashed_at_tok γ LV -∗
    |==> ⚡==> crashed_at_offset γ OCV OCV2 ∗
          crashed_at_tok γ LV.
  Proof.
    iIntros (le) "AG tok".
    unfold crashed_at_tok, crashed_at_offset.
    iMod (
      token_pick (DS := []) _ _ _ _ []%HV (crashed_at_trans OCV2) with "[] tok")
      as "[tok picked]".
    { exists OCV2. done. }
    { iIntros (i). inversion i. }
    iModIntro.
    iModIntro.
    iFrame "tok".
    iDestruct "AG" as (t) "[picked2 ?]".
    iDestruct (gen_picked_in_agree with "picked picked2") as %<-.
    simpl. done.
  Qed.

End crashed_at.

Definition persisted_genInG Σ Ω := genInG Σ Ω (authR viewUR) [agreeR viewO].

Section persisted.
  Context `{!genInDepsG Σ Ω crashed_atR [] }.
  Context `{i : !genInDepsG Σ Ω (authR viewUR) [crashed_atR] }.
  Context (persist_view_name : gname).
  Context (crashedγ : gname).

  Local Definition persisted_rel : rel_over [crashed_atR] (authR viewUR) :=
    λ tC tP,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        tP = fmap_auth (const OCV).

  Definition persisted_auth OPV : iProp Σ :=
    gen_own persist_view_name (● OPV) ∗
    rely_self crashedγ (crashed_at_pred OPV).

  Definition persisted PV : iProp Σ :=
    ∃ OV OCV OPV,
      "%view_eq" ∷ ⌜ OPV `view_sub` OCV = PV ⌝ ∗
      "agree" ∷ crashed_at_offset crashedγ OV OCV ∗
      "persLub" ∷ gen_own persist_view_name (◯ OPV) ∗
      "crashRely" ∷ rely_self crashedγ (crashed_at_pred OPV) ∗
      "rely" ∷ rely persist_view_name [crashedγ] persisted_rel (λ _, true).

  (* Lemma persisted_weak PV PV' : PV' ≼ PV → persisted PV -∗ persisted PV'. *)
  (* Proof. ... Qed. *)

  Lemma view_sub_something OPV OCV2 OCV :
    OPV ⊑ OCV2 →
    OPV `view_sub` OCV2 = view_to_zero (OPV `view_sub` OCV).
  Proof.
    intros gr.
    rewrite view_sub_greater; last done.
    apply view_to_zero_dom_eq.
    symmetry.
    apply view_sub_dom_eq.
  Qed.
  Lemma post_crash_persisted PV :
    persisted PV ⊢
    ⚡==> persisted (view_to_zero PV) ∗
          ∃ CV, ⌜ PV ⊑ CV ⌝ ∗ crashed_at crashedγ CV.
  Proof.
    iNamed 1.
    iModIntro.
    iDestruct "crashRely" as "(crashRely & (%t & (%OCV2 & %incl & ->) & picked1))".
    iDestruct "agree" as (?) "[picked2 agree]".
    iDestruct (gen_picked_in_agree with "picked1 picked2") as %<-.
    iClear "picked2".
    iDestruct "rely" as "[rely (%tP & %ts & (%rel & _) & pickedP & pickedC)]".
    simpl.
    unfold trans_for in ts.
    simpl in ts.
    dependent elimination ts as [hcons tC hnil].
    iSpecialize ("pickedC" $! 0%fin).
    simpl in rel.
    rewrite hvec_lookup_fmap_equation_2.
    iDestruct (gen_picked_in_agree with "picked1 pickedC") as %<-.
    iClear "pickedC".
    destruct rel as (OCV2' & eqs & ->).
    apply crashed_at_trans_inj in eqs as <-.
    iDestruct "persLub" as (?) "[picked2 persLub]".
    iDestruct (gen_picked_in_agree with "pickedP picked2") as %<-.
    iClear "picked2".
    (* Search bi_sep bi_exist. *)
    rewrite bi.sep_exist_l.
    iExists (OCV2 `view_sub` OCV).
    assert (PV ⊑ OCV2 `view_sub` OCV).
    { rewrite -view_eq. apply view_sub_mono. done. }
    iSplit.
    { iExists OCV, OCV2, OPV. iFrame. simpl.
      rewrite fmap_auth_frag. simpl.
      iSplit.
      { iPureIntro. rewrite -view_eq.
        apply view_sub_something. done. }
      iApply (gen_own_mono with "persLub").
      Search auth_frag "view".
      destruct incl as (V & ->).
      exists (◯ V). done. }
    iFrame.
    iSplit; first done.
    iExists _, _, _.
    iFrame.
    done.
  Qed.

End persisted.
