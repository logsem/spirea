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

From self Require Import extra map_extra view_slice.
From self.nextgen Require Import hvec nextgen_promises.
From self.nextgen Require Import nextgen_promises.
From self.algebra Require Import view.

From self.lang Require Import lang.

Definition crashed_atR : cmra := prodR (agreeR viewO) (agreeR viewO).
(* Definition crashed_at_inG Σ Ω := genInDepsG Σ Ω crashed_atR []. *)
Notation crashed_at_inG Σ Ω := (genInDepsG Σ Ω crashed_atR [#]).

(* Names used:
 * - OV: The offset view, the sum of all crash views from prior generations
 * - OCV: The crash view including offsets
 * - OPV: The persist view including offsets
 * - CV: The crash view, CV = OCV - OV
 * - PV: The persist view, PV = OPV - OV
 *)

Definition drop_word s := substring (1 + findex 0 " " s) (String.length s) s.

Tactic Notation "iPickedInAgree" constr(Hs) :=
  let na := eval vm_compute in (drop_word Hs) in
  iDestruct (gen_picked_in_agree with Hs) as %<-;
  iClear na.

Section crashed_at.
  (* Resource for crashed at view *)
  Context `{caI : !crashed_at_inG Σ Ω}.

  (* The transition function that gets applied to the crashed at view at a
   * crash. [OCV2] is the news offset crash view. *)
  Definition crashed_at_trans OCV2 : crashed_atR → crashed_atR :=
    λ '(_, OCV), (OCV, to_agree OCV2).

  Instance crashed_at_trans_cmra_morphism OCV2 :
    CmraMorphism (crashed_at_trans OCV2).
  Proof.
    rewrite /crashed_at_trans.
    split.
    - intros ? [??] [??] [? eq]. simpl in *. rewrite eq. done.
    - intros ? [??] [??]. simpl in *. split; done.
    - intros [??]. done.
    - intros [??] [??]. simpl. split; first done. simpl.
      rewrite agree_idemp. done.
      Search inj.
  Qed.

  #[global]
  Instance crashed_at_trans_inj : Inj (=) (=) crashed_at_trans.
  Proof.
    unfold crashed_at_trans. intros ???.
    specialize (equal_f H (to_agree (∅ : viewO), to_agree (∅ : viewO))).
    simpl. intros [= ?]. done.
  Qed.

  Definition crashed_at_pred (OPV : view) : pred_over crashed_atR :=
    λ t, ∃ OCV2, OPV ⊑ OCV2 ∧ t = crashed_at_trans OCV2.

  Definition crashed_at_rel PV : rel_over [#] crashed_atR :=
    crashed_at_pred PV.

  Definition crashed_at_both γ OV OCV : iProp Σ :=
    gen_own (i := genInDepsG_gen caI) γ (to_agree OV, to_agree OCV).

  Lemma crashed_at_both_agree γ OV1 OCV1 OV2 OCV2 :
    crashed_at_both γ OV1 OCV1 -∗
    crashed_at_both γ OV2 OCV2 -∗
    ⌜ OV1 = OV2 ⌝ ∗ ⌜ OCV1 = OCV2 ⌝.
  Proof.
    iIntros "O1 O2".
    iCombine "O1 O2" as "O".
    rewrite /gen_own own_valid /gc_tup_elem gen_cmra_validI.
    simpl.
    iDestruct "O" as "(_ & _ & %Hv & _)".
    iPureIntro.
    move: Hv. rewrite Some_valid pair_valid. simpl.
    intros [?%to_agree_op_inv ?%to_agree_op_inv].
    split; apply leibniz_equiv; done.
  Qed.

  (* Ownership over the offest crashed at view. *)
  Definition crashed_at_offset γ OCV : iProp Σ :=
    ∃ OV, gen_own γ (to_agree OV, to_agree OCV).

  Definition crashed_at γ (CV : view) : iProp Σ :=
    ∃ (OV OCV LV : view),
      (* "%view_add" ∷ ⌜ OV `view_add` CV = OCV ⌝ ∗ *)
      "%view_eq" ∷ ⌜ OCV `view_sub` OV = CV ⌝ ∗
      "agree" ∷ gen_own γ (to_agree OV, to_agree OCV)
      (* ∗ "rely" ∷ rely γ [] (crashed_at_pred LV) (crashed_at_pred LV). *)
      ∗ "rely" ∷ rely_self γ (crashed_at_pred LV).

  (** Ownership over the crashed at token with a promise that after the next
   * crash the [OCV] will be at least [LV]. *)
  Definition crashed_at_tok γ LV : iProp Σ :=
    token γ [#] (crashed_at_pred LV) (crashed_at_pred LV).

  Lemma crashed_at_tok_strengthen γ LV1 LV2 :
    LV1 ⊑ LV2 →
    crashed_at_tok γ LV1 ⊢ |==> crashed_at_tok γ LV2.
  Proof.
    iIntros (le) "tok".
    iApply (token_strengthen_promise_0_deps with "tok").
    - intros ?. unfold crashed_at_pred.
      intros (LV3 & ? & ?). eexists LV3. split; last done. etrans; done.
    - exists (λ '(_, CV1), (CV1, to_agree LV2)).
      split; first apply _.
      eexists LV2. done.
  Qed.

  Lemma crashed_at_alloc CV :
    ⊢ |==> ∃ γ, crashed_at γ CV ∗ crashed_at_tok γ CV.
  Proof.
    iMod (own_gen_alloc (DS := [#])
      (to_agree ∅, to_agree CV) [#] [##] with "[]") as (γ) "(HO & tok)".
    { done. }
    { iIntros (i'). inversion i'. }
    iMod (
      token_strengthen_promise (DS := [#])
        _ [#] [##] _ (crashed_at_pred CV) _ (crashed_at_pred CV) with "[] tok")
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
    |==> ⚡==>
      crashed_at_both γ OCV OCV2 ∗ crashed_at_tok γ LV ∗
      picked_in γ (crashed_at_trans OCV2).
  Proof.
    iIntros (le) "AG tok".
    unfold crashed_at_tok, crashed_at_offset.
    iMod (
      token_pick (DS := [#]) _ _ _ _ [##]%HV (crashed_at_trans OCV2) with "[] tok")
      as "[tok picked]".
    { exists OCV2. done. }
    { iIntros (i). inversion i. }
    iModIntro.
    iModIntro.
    iFrame "tok".
    iDestruct "AG" as (t) "[picked2 ?]".
    iPickedInAgree "picked picked2".
    simpl. naive_solver.
  Qed.

End crashed_at.

Definition persisted_genInG Σ Ω `{i : !crashed_at_inG Σ Ω} :=
  genInDepsG Σ Ω (authR viewUR) [#crashed_atR].

#[global]
Instance genInSelfG_one Σ Ω A :
  genInSelfG Σ Ω A →
  ∀ i : fin 1, genInSelfG Σ Ω ([#A] !!! i).
Proof. intros ? i. dependent elimination i. Defined.

Section rules_one_dep.
  Context `{gd : !genInSelfG Σ Ω B}.
  Context `{g : !genInDepsG Σ Ω A [#B] }.

  #[global]
  Instance rely_1_dep_into_nextgen γ γd R P :
    IntoNextgen (rely (DS := [#_]) γ [#γd] R P)
      (rely γ [#γd] R P ∗
      ∃ (t : A → A) (td : B → B),
        ⌜ R td t ∧ P t ⌝ ∗
        picked_in γ t ∗
        picked_in (g := genInSelfG_gen gd) γd td).
  Proof.
    rewrite /IntoNextgen.
    iIntros "R". iModIntro.
    iDestruct "R" as "($ & (%t & %ts & [% %] & ? & HD))".
    iSpecialize ("HD" $! 0%fin).
    dependent elimination ts as [hcons td hnil].
    iExists t, td.
    iFrame.
    iPureIntro. split; done.
  Qed.

End rules_one_dep.

Section persisted.
  Context `{!crashed_at_inG Σ Ω}.
  Context `{i : !persisted_genInG Σ Ω}.
  Context (persist_view_name : gname).
  Context (crashedγ : gname).

  Local Definition persisted_rel : rel_over [#crashed_atR] (authR viewUR) :=
    λ tC tP,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        tP = fmap_auth (const OCV).

  Definition persisted_auth OPV : iProp Σ :=
    gen_own (i := genInDepsG_gen i) persist_view_name (● OPV) ∗
    rely (g := i) persist_view_name [#crashedγ] persisted_rel (λ _, true).
    (* ∗ rely_self crashedγ (crashed_at_pred OPV). *)

  (* has been upstreamed to [iris-nextgen]. *)
  Lemma fmap_auth_auth {A : ucmra} (a : A) t :
    fmap_auth t (● a) ≡ ● (t a) ⋅ ◯ (t ε).
  Proof.
    rewrite /fmap_auth /fmap_view view.view_op_eq /=.
    rewrite right_id left_id /fmap_pair agree_map_to_agree //.
  Qed.

  #[global]
  Instance persisted_auth_into_nextgen OPV :
    IntoNextgen
      (persisted_auth OPV)
      (∃ OCV2,
        persisted_auth OCV2 ∗
        picked_in crashedγ (crashed_at_trans OCV2)).
      (* (∃ OCV2, ⌜ OPV ⊑ OCV2 ⌝ ∗ persisted_auth (OPV `view_add` CV)). *)
  Proof.
    rewrite /IntoNextgen /persisted_auth.
    iIntros "(auth & relyP)".
    iModIntro.
    iDestruct "auth" as (t) "(picked & auth)".
    iDestruct "relyP" as "(relyP & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV2 & -> & ->).
    iExists OCV2.
    rewrite fmap_auth_auth. simpl.
    iFrame.
    iDestruct "auth" as "($ & _)".
  Qed.

  Definition persisted PV : iProp Σ :=
    ∃ OCV OPV,
      "%view_eq" ∷ ⌜ OPV `view_sub` OCV = PV ⌝ ∗
      "agree" ∷ crashed_at_offset crashedγ OCV ∗
      "persLub" ∷ gen_own (i := genInDepsG_gen i) persist_view_name (◯ OPV) ∗
      "crashRely" ∷ rely_self crashedγ (crashed_at_pred OPV) ∗
      "rely" ∷ rely (g := i) persist_view_name [#crashedγ] persisted_rel (λ _, true).

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

  #[global]
  Instance persisted_into_nextgen PV :
    IntoNextgen
      (persisted PV)
      (persisted (view_to_zero PV) ∗ ∃ CV, ⌜PV ⊑ CV⌝ ∗ crashed_at crashedγ CV).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashRely" as "(crashRely & (%t & (%OCV2 & %incl & ->) & picked1))".
    iDestruct "agree" as (??) "[picked2 agree]".
    iPickedInAgree "picked1 picked2".
    iDestruct "rely" as "[rely (%tP & %ts & (%rel & _) & pickedP & pickedC)]".
    simpl.
    unfold trans_for in ts.
    simpl in rel.
    (* rewrite hvec_lookup_fmap_equation_2. *)
    iPickedInAgree "picked1 pickedC".
    destruct rel as (OCV2' & eqs & ->).
    apply crashed_at_trans_inj in eqs as <-.
    iDestruct "persLub" as (?) "[picked2 persLub]".
    iPickedInAgree "pickedP picked2".
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

Definition gmap_view_genInG Σ Ω `{i : !genInDepsG Σ Ω crashed_atR [#] } :=
  genInDepsG Σ Ω (gmap_viewR loc (leibnizO (gmap nat message))) [#crashed_atR].

(* Resources and transformation for the heap. *)

Definition heapR : cmra := gmap_viewR loc (leibnizO history).

Section heap.
  (* The transformation of the heap depends on the transformation of the
   * crashed_at view. *)
  Context `{!genInDepsG Σ Ω crashed_atR [#] }.
  (* Context {V : Type}. *)
  Context `{i : !genInDepsG Σ Ω heapR [#crashed_atR] }.
  Context (crashedγ : gname).

  (* Given a new [OCV] we can define the transformation applied to the history
   * [hist] at each key [l]. *)
  Definition drop_above_hist (OCV : view) (l : loc)
      (hist : leibnizO history) : option _ :=
    (λ '(MaxNat t),
      discard_msg_views <$> drop_above t hist) <$> (OCV !! l).

  Instance drop_above_hist_map_trans OCV: MapTrans (drop_above_hist OCV).
  Proof.
    split; last solve_proper. unfold drop_above_hist.
    intros ℓ v1 ->%fmap_None v2. done.
  Qed.

  Definition drop_above_map (OCV : view) heap :=
    map_imap (drop_above_hist OCV) heap.

  Local Definition heap_rel : rel_over [#crashed_atR] (heapR) :=
    λ tC tP, ∃ OCV,
      tC = crashed_at_trans OCV ∧
      tP = map_entry_lift_gmap_view (drop_above_hist OCV).

  Definition own_auth_heap heapγ heap : iProp Σ :=
    ∃ OCV,
      "own_auth" ∷ gen_own heapγ (gmap_view_auth (DfracOwn 1) heap) ∗
      "crashed" ∷ crashed_at_offset crashedγ OCV ∗
      (* We only keep the rely as we never want to strengthen the promise and
       * never want to pick anything (the promise itself completely determines
       * the transformation). *)
      "rely" ∷ rely heapγ [#crashedγ] heap_rel (λ _, true).
       (* "tok" ∷ token heapγ [crashedγ] heap_rel True_pred. *)

  Lemma own_auth_heap_alloc LV heap OCV :
    crashed_at_offset crashedγ OCV -∗
    rely_self crashedγ (crashed_at_pred LV) ==∗
    ∃ heapγ, own_auth_heap heapγ heap.
  Proof.
    iIntros "crashed #rely".
    iMod (own_gen_alloc (DS := [#_])
      (gmap_view_auth (DfracOwn 1) heap)
      [#crashedγ] [##crashed_at_pred LV] with "[]") as (γ) "[HH tok]".
    { apply gmap_view_auth_valid. }
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely". }
    iMod (
      token_strengthen_promise (DS := [#_])
        _ [#_] [##_] _ heap_rel _ True_pred with "[] tok")
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

  Lemma map_entry_lift_gmap_view_auth dq
      (heap : gmap loc (leibnizO history)) map_entry :
    (map_entry_lift_gmap_view map_entry (gmap_view_auth dq heap)) =
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
    iPickedInAgree "pickedC pickedC'".
    iDestruct "own_auth" as (tH') "(pickedH' & own_auth)".
    iPickedInAgree "pickedH pickedH'".
    destruct rel as (OCV2 & -> & ->).
    iExists OCV2.
    iSplit.
    { iExists _. iFrame. }
    { iExists _. iFrame.
      iSplit. 2: { iExists _. iFrame. }
      rewrite map_entry_lift_gmap_view_auth.
      iFrame. }
  Qed.

  #[global]
  Instance into_nextgen_own_auth_heap heapγ heap : IntoNextgen _ _ :=
    own_auth_heap_nextgen heapγ heap.

End heap.

(* All the functors that we need for the base logic (and not ghost names). This
is identical to [nvmBaseFixedG] except for the [invG] part. *)
Class nvmBaseG Σ Ω  := NvmBaseG {
  (* crashed at *)
  nvmBaseG_crashed_at_in :> crashed_at_inG Σ Ω;
  crashed_at_name : gname;
  (* persisted *)
  nvmBaseG_persisted_in :>
    genInDepsG Σ Ω (authR viewUR) [#crashed_atR];
    (* persisted_genInG (i := nvmBaseG_crashed_at_in) Σ Ω; *)
  persisted_name : gname;
  (* heap map *)
  nvmBaseG_gmap_view_in :>
    genInDepsG Σ Ω (gmap_viewR loc (leibnizO (gmap nat message))) [#crashed_atR];
    (* gmap_view_genInG (i := nvmBaseG_crashed_at_in) Σ Ω; *)
  heap_name : gname;
}.

Search drop_prefix.
(* [hist] might have locations that are not in [OCV]. Hence we cannot use
 * [map_zip_with] here. *)
Definition store_drop_prefix OCV (hist : store) :=
  map_imap (λ l h, Some $ drop_prefix h (OCV !!0 l)) hist.

(* The state interpretation for the base logic. *)
Definition nvm_heap_ctx `{!nvmBaseG Σ Ω} (σ : mem_config) : iProp Σ :=
  ∃ (OV OCV : view) (full_hist : store),
    (* crashed at *)
    "%full_hist_eq" ∷
      ⌜ σ.1 = store_drop_prefix OCV full_hist ⌝ ∗
      (* ⌜ σ.1 = map_zip_with drop_prefix full_hist (max_nat_car <$> OCV) ⌝ ∗ *)
    "%Hop" ∷ ⌜ valid_heap σ.1 ⌝ ∗
    "crashed" ∷ gen_own crashed_at_name (to_agree OV, to_agree OCV) ∗
    (* The lower bound on the next [OCV] is the current [OCV] plus [PV]. *)
    "crashed_at_tok" ∷ crashed_at_tok crashed_at_name (OCV `view_add` σ.2) ∗
    (* The interpretation of the heap. *)
    "Hσ" ∷ own_auth_heap crashed_at_name heap_name full_hist ∗
    (* (drop_prefix σ.1) ∗ *)
    (* "lubauth" ∷ own store_view_name (● (max_view σ.1)) ∗ *)
    "pers" ∷ persisted_auth (i := nvmBaseG_persisted_in) persisted_name crashed_at_name (OCV `view_add` σ.2)
    .
    (* ∗ *)
    (* "crash" ∷ (∃ (CV : view), *)
    (*   "%cvSubset" ∷ ⌜dom CV ⊆ dom σ.1⌝ ∗ *)
    (*   "#crashedAt" ∷ own crashed_at_view_name (to_agree CV : agreeR viewO)). *)

(* From Perennial.program_logic Require Export weakestpre. *)
(* From Perennial.program_logic Require Export crash_lang crash_weakestpre. *)

(* Lemma view_add_offsets_add V1 V2 : *)
(*   max_nat_car <$> V1 `view_add` V2 = offsets_add (max_nat_car <$> V1) V2. *)
(* Proof. *)
(*   rewrite /offsets_add /view_add. *)
(*   apply map_eq => l. *)
(*   rewrite map_lookup_zip_with. *)
(*   rewrite 2!lookup_fmap. *)
(*   rewrite lookup_merge. *)
(*   destruct (V1 !! l); simpl; *)
(*     destruct (V2 !! l); simpl; try done. *)
(* Admitted. *)

(* Lemma drop_above_map_drop_all_above OCV CV full_hist : *)
(*   (λ hist : history, discard_msg_views <$> hist) <$> *)
(*     drop_all_above (offsets_add (max_nat_car <$> OCV) CV) full_hist = *)
(*   drop_above_map (OCV `view_add` CV) full_hist. *)
(* Proof. *)
(*   unfold drop_above_map. unfold drop_all_above. unfold drop_above_hist. *)
(*   rewrite -view_add_offsets_add. *)
(*   rewrite map_fmap_zip_with. apply map_eq => l. *)
(*   rewrite map_zip_with_flip. rewrite map_lookup_imap. *)
(*   rewrite map_lookup_zip_with. rewrite lookup_fmap. *)
(*   destruct (full_hist !! l) as [h|] eqn:look1; rewrite look1 /=; last done. *)
(*   destruct ((OCV `view_add` CV) !! l) as [[t]|]; done. *)
(* Qed. *)

(* Lemma slice_of_store_drop_cv CV hists (offsets : view) : *)
(*   slice_of_store CV (store_drop_prefix offsets hists) = *)
(*     map_zip_with drop_prefix *)
(*             ((λ hist : history, discard_msg_views <$> hist) <$> *)
(*             drop_all_above (offsets `view_add` CV) hists) *)
(*             (offsets `view_add` CV). *)

Lemma view_add_lookup_zero V1 V2 ℓ :
  (V1 `view_add` V2) !!0 ℓ = (V1 !!0 ℓ) + (V2 !!0 ℓ).
Proof.
Admitted.

Lemma slice_of_store_drop_prefix CV OCV full_hist :
  dom OCV ⊆ dom CV →
  slice_of_store CV (store_drop_prefix OCV full_hist) =
  store_drop_prefix (OCV `view_add` CV)
    (drop_above_map (OCV `view_add` CV) full_hist).
Proof.
  intros sub.
  apply map_eq => ℓ.
  rewrite /store_drop_prefix.
  rewrite /slice_of_store.
  rewrite /slice_of_hist.
  rewrite 2!lookup_fmap.
  rewrite /drop_above_map.
  rewrite 2!map_lookup_imap.
  rewrite /slice_hist.
  rewrite map_zip_with_flip.
  rewrite map_lookup_zip_with.
  rewrite map_lookup_imap.
  destruct (full_hist !! ℓ) eqn:look; rewrite look; simpl; last done.
  unfold drop_above_hist.
  rewrite !view_add_lookup_zero.
  unfold view_add.
  rewrite lookup_merge.
  unfold lookup_zero.
  destruct (CV !! ℓ) as [[t]|] eqn:look2; simpl;
    destruct (OCV !! ℓ) as [[t2]|] eqn:look3; simpl; try done.
  - f_equiv.
    apply map_eq. intros i.
    rewrite !drop_prefix_lookup.
    rewrite !lookup_fmap.
    destruct (decide (i = 0)) as [->|neq]; simpl.
    * rewrite drop_above_lookup_t.
      rewrite Nat.add_comm.
      destruct (g !! (t2 + t)); done.
    * rewrite drop_above_lookup_gt; last lia.
      destruct (g !! (t + t2)); simpl;
        rewrite ?lookup_singleton_ne; done.
  - f_equiv.
    apply map_eq. intros i.
    rewrite !drop_prefix_lookup.
    rewrite !lookup_fmap.
    rewrite Nat.add_comm. simpl.
    destruct (decide (i = 0)) as [->|neq]; simpl.
    * rewrite drop_above_lookup_t.
      destruct (g !! t); done.
    * rewrite drop_above_lookup_gt; last lia.
      destruct (g !! t); simpl;
        rewrite ?lookup_singleton_ne; done.
  - apply not_elem_of_dom_2 in look2.
    apply elem_of_dom_2 in look3.
    set_solver.
Qed.

(* If we have the state interpretation before a crash, then after a crash we
 * have it under the nextgen modality. *)
Lemma heap_ctx_next_generation `{!nvmBaseG Σ Ω} σ1 σ2 :
  crash_prim_step nvm_crash_lang σ1 σ2 →
  nvm_heap_ctx σ1 ⊢ |==> ⚡==> |==> nvm_heap_ctx σ2.
Proof.
  intros [store PV CV pIncl cut].
  unfold nvm_heap_ctx. simpl.
  iNamed 1.
  iMod (crashed_at_pick_nextgen _ _ _ (OCV `view_add` CV)
    with "crashed crashed_at_tok") as "crashed".
  { f_equiv. done. }
  iModIntro. iModIntro.
  iDestruct "crashed" as "(#crashed & crashed_at_tok & pickedC)".
  iMod (crashed_at_tok_strengthen _ _ (OCV `view_add` CV) with "crashed_at_tok") as "tok".
  { f_equiv. done. }
  iModIntro.
  set (OCV2 := OCV `view_add` CV).
  iDestruct ("Hσ") as (?) "[(% & crashed') Hσ]".
  iDestruct (crashed_at_both_agree with "crashed' crashed") as "[-> ->]".
  iExists OCV, OCV2, _.
  iFrame "Hσ".
  iSplit.
  { iPureIntro. rewrite full_hist_eq.
    rewrite /OCV2.
    apply slice_of_store_drop_prefix.
    admit. }
    (* domm OCV =  *)
    (* dom offsets ⊑ dom CV *)
    (* (* rewrite view_add_offsets_add. *) *)
    (* rewrite slice_of_store_drop. *)
    (* rewrite drop_above_map_drop_all_above. done. } *)
  iSplit. { iPureIntro. apply store_inv_cut; done. }
  iFrame "crashed". simpl.
  rewrite -(assoc view_add).
  rewrite view_add_view_zero.
  iFrame "tok".
  iDestruct "pers" as "(% & pers & pickedC')".
  iDestruct (gen_picked_in_agree with "pickedC' pickedC") as %eq.
  apply crashed_at_trans_inj in eq.
  rewrite eq.
  iFrame "pers".
Qed.

