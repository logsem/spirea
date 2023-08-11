(* The generational resources used by BaseSpirea.
 *
 * The base logic uses 5 resources that change at a crash:
 * - The crashed_at resource.
 * - The persisted resource.
 * - The heap.
 * - The store view.
 * - The [NC] crashGS thing from Perennial
 *)

From Equations Require Import Equations.
From iris.algebra Require Import gmap_view agree.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises.
From self.nextgen Require Import nextgen_promises.
From self.algebra Require Import view.

From self.lang Require Import lang.

Instance genInSelfG_empty Σ Ω :
  ∀ i : fin 0, genInSelfG Σ Ω ([]%IL !!! i).
Proof. intros i. inversion i. Qed.

Instance genInSelfG_one Σ Ω n A (DS : ivec n cmra):
  genInG Σ Ω A DS →
  ∀ i : fin 1, genInSelfG Σ Ω ([A]%IL !!! i).
Proof. intros ? i. dependent elimination i. Defined.

Definition crashed_atR : cmra := prodR (agreeR viewO) (agreeR viewO).
(* Definition crashed_at_inG Σ Ω := genInDepsG Σ Ω crashed_atR []. *)
Notation crashed_at_inG Σ Ω := (genInDepsG Σ Ω crashed_atR []).

(* Names used:
 * - OV: The offset view, the sum of all crash views from prior generations
 * - OCV: The crash view including offsets
 * - OPV: The persist view including offsets
 * - CV: The crash view, CV = OCV - OV
 * - PV: The persist view, PV = OPV - OV
 *)

Section crashed_at.
  (* Resource for crashed at view *)
  Context `{caI : !crashed_at_inG Σ Ω}.

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

  Definition crashed_at_both γ OV OCV : iProp Σ :=
    gen_own (i := genInDepsG_gen caI) γ (to_agree OV, to_agree OCV).

  (* Ownership over the offest crashed at view. *)
  Definition crashed_at_offset γ OCV : iProp Σ :=
    ∃ OV, gen_own γ (to_agree OV, to_agree OCV).

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
    crashed_at_both γ OV OCV -∗
    crashed_at_tok γ LV -∗
    |==> ⚡==> crashed_at_both γ OCV OCV2 ∗ crashed_at_tok γ LV.
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
    simpl. naive_solver.
  Qed.

End crashed_at.

Definition persisted_genInG Σ Ω `{i : !crashed_at_inG Σ Ω} :=
  genInDepsG Σ Ω (authR viewUR) [crashed_atR].

Section persisted.
  Context `{!crashed_at_inG Σ Ω}.
  Context `{i : !persisted_genInG Σ Ω}.
  Context (persist_view_name : gname).
  Context (crashedγ : gname).

  Local Definition persisted_rel : rel_over [crashed_atR] (authR viewUR) :=
    λ tC tP,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        tP = fmap_auth (const OCV).

  Definition persisted_auth OPV : iProp Σ :=
    gen_own (i := genInDepsG_gen i) persist_view_name (● OPV) ∗
    rely_self crashedγ (crashed_at_pred OPV).

  Definition persisted PV : iProp Σ :=
    ∃ OCV OPV,
      "%view_eq" ∷ ⌜ OPV `view_sub` OCV = PV ⌝ ∗
      "agree" ∷ crashed_at_offset crashedγ OCV ∗
      "persLub" ∷ gen_own (i := genInDepsG_gen i) persist_view_name (◯ OPV) ∗
      "crashRely" ∷ rely_self crashedγ (crashed_at_pred OPV) ∗
      "rely" ∷ rely (g := i) persist_view_name [crashedγ] persisted_rel (λ _, true).

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
    iDestruct "agree" as (??) "[picked2 agree]".
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
    { iExists OCV2, OPV. iFrame. simpl.
      rewrite fmap_auth_frag. simpl.
      iSplit.
      { iPureIntro. rewrite -view_eq.
        apply view_sub_something. done. }
      iSplit. { iExists _. iFrame. }
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

Definition gmap_view_genInG Σ Ω `{i : !genInDepsG Σ Ω crashed_atR [] } :=
  genInDepsG Σ Ω (gmap_viewR loc (leibnizO (gmap nat message))) [crashed_atR].

Section heap.
  (* The transformation of the heap depends on the transformation of the crashed_at view. *)
  Context `{!genInDepsG Σ Ω crashed_atR [] }.
  Context {V : Type}.
  Context `{i : !genInDepsG Σ Ω (gmap_viewR loc (leibnizO (gmap nat V))) [crashed_atR] }.
  Context (crashedγ : gname).
  (* Context (heapγ : gname). *)

  Definition drop_above_hist (OCV : view) (l : loc) (hist : leibnizO (gmap nat V)) : option (leibnizO (gmap nat V)) :=
    (λ '(MaxNat t), drop_above (t) hist) <$> (OCV !! l).

  Instance drop_above_hist_map_trans OCV:
     MapTrans (drop_above_hist OCV).
  Proof.
    split; last solve_proper.
    unfold drop_above_hist.
    intros ℓ v1 ->%fmap_None v2. done.
  Qed.

  Definition drop_above_map (OCV : view) heap :=
    map_imap (drop_above_hist OCV) heap.

  Local Definition heap_rel : rel_over [crashed_atR] (gmap_viewR loc (leibnizO (gmap nat V))) :=
    λ tC tP, ∃ OCV,
      tC = crashed_at_trans OCV ∧
      tP = map_entry_lift_gmap_view (drop_above_hist OCV).

  Definition own_auth_heap heapγ heap : iProp Σ :=
    ∃ OCV,
      "own_auth" ∷  gen_own heapγ (gmap_view_auth (DfracOwn 1) heap) ∗
      "crashed" ∷ crashed_at_offset crashedγ OCV ∗
      (* We only keep the rely as we never want to strengthen the promise and
       * never want to pick anything (the promise itself completely determines
       * the transformation). *)
      "rely" ∷ rely heapγ [crashedγ] heap_rel (λ _, true).
       (* "tok" ∷ token heapγ [crashedγ] heap_rel True_pred. *)

  Lemma own_auth_heap_alloc LV heap OCV :
    crashed_at_offset crashedγ OCV -∗
    rely_self crashedγ (crashed_at_pred LV) ==∗
    ∃ heapγ, own_auth_heap heapγ heap.
  Proof.
    iIntros "crashed #rely".
    iMod (own_gen_alloc (DS := [_])
      (gmap_view_auth (DfracOwn 1) heap)
      [crashedγ] [crashed_at_pred LV] with "[]") as (γ) "[HH tok]".
    { apply gmap_view_auth_valid. }
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely". }
    iMod (
      token_strengthen_promise (DS := [_])
        _ [_] [_] _ heap_rel _ True_pred with "[] tok")
      as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    2: {
      iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely". }
    { intros ts crashedPred.
      dependent elimination ts as [hcons tC hnil].
      destruct crashedPred as ((OCV2 & ? & ->) & _).
      exists (map_entry_lift_gmap_view (drop_above_hist OCV2)).
      split; first apply _.
      simpl.
      exists OCV2. done. }
    iModIntro.
    iExists γ, OCV.
    unfold own_auth_heap.
    iFrame.
    iDestruct (token_to_rely with "tok") as "$".
  Qed.

  Lemma map_entry_lift_gmap_view_auth dq (heap : gmap loc (leibnizO (gmap nat V))) map_entry :
    (map_entry_lift_gmap_view map_entry
                      (gmap_view_auth dq heap)) =
    (gmap_view_auth dq (map_imap map_entry heap)).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    rewrite agree_map_to_agree. done.
  Qed.

  Lemma own_auth_heap_nextgen heapγ heap :
    own_auth_heap heapγ heap
    ⊢ ⚡==> ∃ OCV,
      crashed_at_offset crashedγ OCV ∗
      own_auth_heap heapγ (drop_above_map OCV heap).
  Proof.
    iNamed 1.
    iModIntro.
    iDestruct ("crashed") as (? tC) "(pickedC & ?)".
    iDestruct "rely" as "(rely & (%tH & % & (%rel & _) & pickedH & pickedC'))".
    iSpecialize ("pickedC'" $! 0%fin).
    dependent elimination ts as [hcons tC' hnil].
    rewrite hvec_lookup_fmap_equation_2.
    iDestruct (gen_picked_in_agree with "pickedC pickedC'") as %<-.
    iClear "pickedC'".
    iDestruct "own_auth" as (tH') "(pickedH' & own_auth)".
    iDestruct (gen_picked_in_agree with "pickedH pickedH'") as %<-.
    iClear "pickedH'".
    destruct rel as (OCV2 & -> & ->).
    iExists OCV2.
    iSplit.
    { iExists _. iFrame. }
    { iExists _. iFrame.
      iSplit. 2: { iExists _. iFrame. }
      rewrite map_entry_lift_gmap_view_auth.
      iFrame. }
  Qed.

End heap.

(* All the functors that we need for the base logic (and not ghost names). This
is identical to [nvmBaseFixedG] except for the [invG] part. *)
Class nvmBaseG Σ Ω  := NvmBaseG {
  (* crashed at *)
  nvmBaseG_crashed_at_in :> crashed_at_inG Σ Ω;
  crashed_at_name : gname;
  (* persisted *)
  nvmBaseG_persisted_in :> persisted_genInG (i := nvmBaseG_crashed_at_in) Σ Ω;
  persisted_name : gname;
  (* heap map *)
  nvmBaseG_gmap_view_in :> gmap_view_genInG (i := nvmBaseG_crashed_at_in) Σ Ω;
  heap_name : gname;
}.

(* The state interpretation for the base logic. *)
Definition nvm_heap_ctx `{!nvmBaseG Σ Ω} (σ : mem_config) : iProp Σ :=
  ∃ (OV OCV : view),
    (* crashed at*)
    "crashed" ∷ gen_own crashed_at_name (to_agree OV, to_agree OCV) ∗
    "crashed_at_tok" ∷ crashed_at_tok crashed_at_name (OV `view_add` σ.2) ∗
    (* The interpretation of the heap. *)
    "Hσ" ∷
      own_auth_heap (i := nvmBaseG_gmap_view_in) crashed_at_name heap_name σ.1 ∗
    (* "lubauth" ∷ own store_view_name (● (max_view σ.1)) ∗ *)
    "%Hop" ∷ ⌜ valid_heap σ.1 ⌝ ∗
    "pers" ∷ persisted_auth (i := nvmBaseG_persisted_in) crashed_at_name persisted_name (OV `view_add` σ.2)
    .
    (* ∗ *)
    (* "crash" ∷ (∃ (CV : view), *)
    (*   "%cvSubset" ∷ ⌜dom CV ⊆ dom σ.1⌝ ∗ *)
    (*   "#crashedAt" ∷ own crashed_at_view_name (to_agree CV : agreeR viewO)). *)

From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.

(* If we have the state interpretation before a crash, then after a crash we
 * will have it under the nextgen modality. *)
Lemma heap_ctx_next_generation `{!nvmBaseG Σ Ω} σ1 σ2 :
  crash_prim_step nvm_crash_lang σ1 σ2 →
  nvm_heap_ctx σ1 ⊢ |==> ⚡==> nvm_heap_ctx σ2.
Proof.
  intros [store PV CV pIncl cut].
  unfold nvm_heap_ctx.
  iNamed 1.
  iMod (crashed_at_pick_nextgen _ _ _ (OV `view_add` CV) with "crashed crashed_at_tok") as "crashed".
  { simpl. admit. (* trivial *) }
  iModIntro. iModIntro.
  iDestruct "crashed" as "(crashed & crashed_at_tok)".
  iExists OCV, _.
  iFrame "crashed". simpl.
  (* iFrame "crashed_at_tok". *)
Admitted.

