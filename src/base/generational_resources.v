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

(* Names used:
 * - OV: The offset view, the sum of all crash views from prior generations
 * - OCV: The crash view including offsets
 * - OPV: The persist view including offsets
 * - CV: The crash view, CV = OCV - OV
 * - PV: The persist view, PV = OPV - OV
 * - SV: The store view (also called "lub" view), SV = OSV - OV
 *)

Definition store_viewR : cmra := (authR viewO).
Notation store_view_inG Σ Ω := (genInDepsG Σ Ω store_viewR [#]).


Definition crashed_atR : cmra := prodR (agreeR viewO) (agreeR viewO).
(* Definition crashed_at_inG Σ Ω := genInDepsG Σ Ω crashed_atR []. *)
Notation crashed_at_inG Σ Ω := (genInDepsG Σ Ω crashed_atR [#]).

(* All the functors that we need for the base logic (and not ghost names). This
is identical to [nvmBaseFixedG] except for the [invG] part. *)
Class nvmBaseG Σ Ω  := NvmBaseG {
  (* valid view *)
  nvmBaseG_store_view_in :> store_view_inG Σ Ω;
  store_view_name : gname;
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

(* has been upstreamed to [iris-nextgen]. *)
Lemma fmap_auth_auth {A : ucmra} (a : A) t :
  fmap_auth t (● a) ≡ ● (t a) ⋅ ◯ (t ε).
Proof.
  rewrite /fmap_auth /fmap_view view.view_op_eq /=.
  rewrite right_id left_id /fmap_pair agree_map_to_agree //.
Qed.

Definition drop_word s := substring (1 + findex 0 " " s) (String.length s) s.

Tactic Notation "iPickedInAgree" constr(Hs) :=
  let na := eval vm_compute in (drop_word Hs) in
  iDestruct (gen_picked_in_agree with Hs) as %<-;
  iClear na.

Section store_view.
  (* Resource for lub view *)
  Context `{!nvmBaseG Σ Ω}.
  #[local] Notation storeI := (nvmBaseG_store_view_in).
  #[local] Existing Instance nvmBaseG_store_view_in.
  (* we don't care about the transformation of valid views since [validV] predicates
   * are not supposed to survive into next generation anyway. *)
  Definition store_view_trans : store_viewR → store_viewR :=
    fmap_auth (const ∅).

  Instance store_view_trans_cmra_morphism :
    CmraMorphism store_view_trans.
  Proof.
    rewrite /store_view_trans.
    apply @fmap_auth_gentrans, cmra_morphism_const.
    - apply _.
    - done.
    - done.
  Qed.

  Definition store_view_pred: pred_over store_viewR :=
    λ t, t = store_view_trans.

  Definition store_view_auth γ SV: iProp Σ :=
    "store_view_at" ∷ gen_own (i := genInDepsG_gen storeI) γ (● SV) ∗
    "store_view_tok" ∷ token γ [#] (store_view_pred) (store_view_pred).

  (* Expresses that the view [V] is valid. This means that it is included in the
   * lub view. *)
  Definition validV (V : view) : iProp Σ :=
    gen_own (i := genInDepsG_gen storeI) store_view_name (◯ V).

  Lemma store_view_alloc SV :
    ⊢ |==> ∃ γ, store_view_auth γ SV.
  Proof.
    iMod (own_gen_alloc (DS := [#])
      (● SV) [#] [##] with "[]") as (γ) "(HO & tok)".
    { apply auth_auth_valid, view_valid. }
    { iIntros (i'). inversion i'. }
    iMod (
      token_strengthen_promise (DS := [#])
        _ [#] [##] _ (store_view_pred) _ (store_view_pred) with "[] tok")
      as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      eexists.
      split; last done.
      apply _. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iExists (γ).
    iFrame.
  Qed.

  (** Owning [lub_at] and [store_view_tok] allows us to pick any view in
   * next generation (after a bupd). *)
  Lemma store_view_nextgen γ SV1 SV2 :
    store_view_auth γ SV1 ⊢ ⚡==> |==> store_view_auth γ SV2.
  Proof.
    iNamed 1.
    iDestruct (token_to_rely with "[$]") as "#rely".
    iModIntro.
    iDestruct "store_view_at" as "(%t & #picked1 & lub_at)".
    iDestruct "rely" as "[rely (% & % & (? & ->) & picked2 & ?)]".
    iDestruct (gen_picked_in_agree with "picked1 picked2") as %->.

    rewrite /store_view_trans fmap_auth_auth /=.
    iDestruct (gen_own_op with "lub_at") as "[lub_at _]".
    iFrame.
    iMod (own_update with "lub_at") as "$"; last done.
    apply gen_cmra_update; try done.
    apply option_update, auth_auth_grow; first apply view_valid.
    apply view_empty_least.
  Qed.
End store_view.

Section crashed_at.
  (* Resource for crashed at view *)
  Context `{!nvmBaseG Σ Ω}.
  #[local] Existing Instance nvmBaseG_crashed_at_in.
  #[local] Notation caI := nvmBaseG_crashed_at_in.

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

  Definition crashed_at_pred_strengthen OCV1 OCV2:
    OCV2 ⊑ OCV1 →
    pred_stronger (crashed_at_pred OCV1) (crashed_at_pred OCV2).
  Proof.
    intros.
    intros t (OPV & ? & ?).
    exists OPV.
    split; last done.
    by trans OCV1.
  Qed.

  Definition crashed_at_rel PV : rel_over [#] crashed_atR :=
    crashed_at_pred PV.

  Definition crashed_at_both OV OCV : iProp Σ :=
    gen_own (i := genInDepsG_gen caI) crashed_at_name (to_agree OV, to_agree OCV).

  Lemma crashed_at_both_agree OV1 OCV1 OV2 OCV2 :
    crashed_at_both OV1 OCV1 -∗
    crashed_at_both OV2 OCV2 -∗
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
  Definition crashed_at_offset OCV : iProp Σ :=
    ∃ OV, gen_own crashed_at_name (to_agree OV, to_agree OCV).

  Lemma crashed_at_offset_agree OCV OCV' :
    crashed_at_offset OCV -∗ crashed_at_offset OCV' -∗ ⌜OCV = OCV'⌝.
  Proof.
    iIntros "[% H1] [% H2]".
    iDestruct (gen_own_valid_2 with "H1 H2") as "%eq".
    rewrite pair_valid ?to_agree_op_valid_L in eq.
    destruct eq as [-> ->].
    done.
  Qed.

  Definition crashed_at (CV : view) : iProp Σ :=
    ∃ (OV OCV LV : view),
      (* "%view_add" ∷ ⌜ OV `view_add` CV = OCV ⌝ ∗ *)
      "%view_eq" ∷ ⌜ OCV `view_sub` OV = CV ⌝ ∗
      "agree" ∷ gen_own crashed_at_name (to_agree OV, to_agree OCV)
      (* ∗ "rely" ∷ rely γ [] (crashed_at_pred LV) (crashed_at_pred LV). *)
      ∗ "rely" ∷ rely_self crashed_at_name (crashed_at_pred LV).

  Lemma crashed_at_agree CV CV' :
    crashed_at CV -∗ crashed_at CV' -∗ ⌜CV = CV'⌝.
  Proof.
    iNamed 1.
    iIntros "(% & % & % & % & agree' & _)".
    simplify_eq.
    iPoseProof (gen_own_op with "[$agree $agree']") as "agree".
    iDestruct (gen_own_valid with "[$]") as "%eq".
    rewrite pair_valid ?to_agree_op_valid_L in eq.
    destruct eq as [-> ->].
    done.
  Qed.
  
  (** Ownership over the crashed at token with a promise that after the next
   * crash the [OCV] will be at least [LV]. *)
  Definition crashed_at_tok γ LV : iProp Σ :=
    token γ [#] (crashed_at_pred LV) (crashed_at_pred LV).

  Lemma crashed_at_tok_strengthen {γ} LV1 LV2 :
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

  Definition crashed_at_auth_crashed_at OV OCV LV:
    crashed_at_tok crashed_at_name LV -∗
    crashed_at_both OV OCV -∗
    crashed_at (OCV `view_sub` OV).
  Proof.
    iIntros.
    rewrite /crashed_at_both /crashed_at_tok.
    iPoseProof (token_to_rely with "[$]") as "?".
    iPoseProof (rely_to_rely_self with "[$]") as "?".
    iExists _, _, _.
    iFrame "∗#".
    done.
  Qed.

  (* Lemma crashed_at_alloc CV : *)
  (*   ⊢ |==> ∃ γ, crashed_at γ CV ∗ crashed_at_tok γ CV. *)
  (* Proof. *)
  (*   iMod (own_gen_alloc (DS := [#]) *)
  (*     (to_agree ∅, to_agree CV) [#] [##] with "[]") as (γ) "(HO & tok)". *)
  (*   { done. } *)
  (*   { iIntros (i'). inversion i'. } *)
  (*   iMod ( *)
  (*     token_strengthen_promise (DS := [#]) *)
  (*       _ [#] [##] _ (crashed_at_pred CV) _ (crashed_at_pred CV) with "[] tok") *)
  (*     as "tok". *)
  (*   { intros ???. unfold True_rel. rewrite huncurry_curry. done. } *)
  (*   { done. } *)
  (*   { intros ts. dependent elimination ts. done. } *)
  (*   { intros ts _. dependent elimination ts. *)
  (*     exists (λ '(_, CV1), (CV1, to_agree CV)). *)
  (*     split; first apply _. *)
  (*     exists CV. done. } *)
  (*   { iIntros (i'). inversion i'. } *)
  (*   iModIntro. *)
  (*   iExists (γ). *)
  (*   iDestruct (token_to_rely with "tok") as "#R". *)
  (*   iFrame. *)
  (*   iExists ∅, CV, _. iFrame. *)
  (*   iDestruct (rely_to_rely_self with "R") as "$". *)
  (*   iPureIntro. *)
  (*   apply view_sub_empty. *)
  (* Qed. *)

  (** Owning [crashed_at] gives [crashed_at] for some view in the next
   * generation. *)
  Lemma crashed_at_nextgen CV :
    crashed_at CV ⊢ ⚡==> ∃ CV2, crashed_at CV2.
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

  Lemma crashed_at_pick_nextgen OV OCV OCV2 LV :
    LV ⊑ OCV2 →
    crashed_at_both OV OCV -∗
    crashed_at_tok crashed_at_name LV -∗
    |==> ⚡==>
      crashed_at_both OCV OCV2 ∗ crashed_at_tok crashed_at_name LV ∗
      picked_in crashed_at_name (crashed_at_trans OCV2).
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
  Context `{!nvmBaseG Σ Ω}.
  #[local] Existing Instance nvmBaseG_crashed_at_in.
  #[local] Notation i := nvmBaseG_persisted_in.
  #[local] Existing Instance nvmBaseG_persisted_in.

  Local Definition persisted_rel : rel_over [#crashed_atR] (authR viewUR) :=
    λ tC tP,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        tP = fmap_auth (const OCV).

  Definition persisted_auth OPV : iProp Σ :=
    gen_own (i := genInDepsG_gen i) persisted_name (● OPV) ∗
    rely (g := i) persisted_name [#crashed_at_name] persisted_rel (λ _, true).
    (* ∗ rely_self crashedγ (crashed_at_pred OPV). *)

  #[global]
  Instance persisted_auth_into_nextgen OPV :
    IntoNextgen
      (persisted_auth OPV)
      (∃ OCV2,
        persisted_auth OCV2 ∗
        picked_in crashed_at_name (crashed_at_trans OCV2)).
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
    ∃ OCV OPV OPV',
      "%view_eq" ∷ ⌜ OPV `view_sub` OCV = PV ⌝ ∗
      "#agree" ∷ crashed_at_offset OCV ∗
      "#persLub" ∷ gen_own (i := genInDepsG_gen i) persisted_name (◯ OPV) ∗
      "%actualOPV" ∷ ⌜ OPV ⊑ OPV' ⌝ ∗
      "#crashRely" ∷ rely_self crashed_at_name (crashed_at_pred OPV') ∗
      "#rely" ∷ rely (g := i) persisted_name [#crashed_at_name] persisted_rel (λ _, true).

  Lemma persisted_auth_included OCV OPV PV' :
    crashed_at_offset OCV -∗
    persisted_auth OPV -∗
    persisted PV' -∗
    ⌜PV' ⊑ OPV `view_sub` OCV ⌝.
  Proof.
    iIntros "[% crashed_at] [auth _] persisted".
    iNamed "persisted".
    iDestruct (gen_own_valid_2 with "auth persLub") as %[_ [incl _]]%auth_both_dfrac_valid_discrete.
    iDestruct "agree" as "[% crashed_at']".
    iDestruct (gen_own_valid_2 with "crashed_at crashed_at'") as %[_ <-%to_agree_op_valid_L]%pair_valid.
    iPureIntro.
    simplify_eq.
    by apply view_sub_mono.
  Qed.

  Lemma persisted_weak PV1 PV2 : PV2 ≼ PV1 → persisted PV1 -∗ persisted PV2.
  Proof.
    intros H.
    iNamed 1.
    set OPV2 := (map_imap (λ ℓ t, Some (MaxNat (match PV1 !! ℓ with
                                                | Some (MaxNat 0) => 0
                                                | _ => (max_nat_car t + (OCV !!0 ℓ))
                                                end))) PV2).
    iExists OCV, OPV2, OPV'.
    iFrame "#".
    iSplit; first iPureIntro.
    { rewrite /view_sub map_imap_compose /=.
      apply map_eq.
      intros j.
      rewrite map_lookup_imap /=.
      rewrite -subseteq_view_incl view_included in H.
      specialize (H j).
      destruct (PV2 !! j) as [[n2] | ]; last done.
      simpl.
      do 2 f_equiv.
      destruct (PV1 !! j) as [[[ | n1]] | ].
      - apply Some_MaxNat_included in H.
        lia.
      - lia.
      - apply option_not_included_None in H.
        done. }
    assert (le: OPV2 ⊑ OPV). {
      apply view_included.
      intros j.
      rewrite -subseteq_view_incl view_included in H.
      specialize (H j).
      simplify_eq. subst OPV2.
      rewrite /view_sub map_lookup_imap /= in H.
      rewrite /view_sub !map_lookup_imap /=.
      destruct (PV2 !! j) as [ [n1] | ]; destruct (OPV !! j) as [ [n2] | ]; simpl in *; try done.
      - apply Some_MaxNat_included in H.
        apply Some_MaxNat_included.
        destruct (n2 - (OCV !!0 j)) eqn:?; lia.
      - apply option_not_included_None in H.
        done.
      - apply option_included_total.
        by left. }
    iSplit.
    { rewrite /named.
      rewrite -(gen_own_mono _ _ (◯ OPV2)); first iApply "persLub".
      apply auth_frag_mono, le. }
    iPureIntro.
    etrans; first apply le.
    done.
  Qed.

  Global Instance persisted_persistent PV : Persistent (persisted PV).
  Proof. apply _. Qed.

  (* [persisted] is anti-monotone. *)
  Global Instance persisted_anti_mono : Proper ((⊑@{view}) ==> flip (⊢)) (persisted).
  Proof. intros ???. iApply persisted_weak. done. Qed.

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
      (persisted (view_to_zero PV) ∗ ∃ CV, ⌜PV ⊑ CV⌝ ∗ crashed_at CV).
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
    { rewrite -view_eq. apply view_sub_mono. by trans OPV'. }
    iSplit.
    { iExists OCV2, OPV, OPV'. iFrame "#%". simpl.
      rewrite fmap_auth_frag. simpl.
      iSplit.
      { iPureIntro. rewrite -view_eq.
        apply view_sub_something. by trans OPV'. }
      iSplit. { iExists _. iFrame "#". }
      iApply (gen_own_mono with "persLub").
      apply auth_frag_mono.
      by trans OPV'. }
    iSplit; first done.
    iExists _, _, _.
    iFrame "#".
    done.
  Qed.
End persisted.

Definition gmap_view_genInG Σ Ω `{i : !genInDepsG Σ Ω crashed_atR [#] } :=
  genInDepsG Σ Ω (gmap_viewR loc (leibnizO (gmap nat message))) [#crashed_atR].

(* Resources and transformation for the heap. *)

Section heap.
  (* The transformation of the heap depends on the transformation of the
   * crashed_at view. *)
  Context `{!nvmBaseG Σ Ω}.
  #[local] Existing Instance nvmBaseG_gmap_view_in.
  #[local] Existing Instance nvmBaseG_crashed_at_in.
  #[local] Notation i := nvmBaseG_crashed_at_in.
  #[local] Definition heapR : cmra := gmap_viewR loc (leibnizO history).

  (* Context {V : Type}. *)
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

  Definition own_auth_heap heap : iProp Σ :=
    ∃ OCV,
      "own_auth" ∷ gen_own heap_name (gmap_view_auth (DfracOwn 1) heap) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      (* We only keep the rely as we never want to strengthen the promise and
       * never want to pick anything (the promise itself completely determines
       * the transformation). *)
      "#rely" ∷ rely heap_name [#crashed_at_name] heap_rel (λ _, true).
       (* "tok" ∷ token heapγ [crashedγ] heap_rel True_pred. *)

  (* [f(ull-)mapsto] is the mapsto predicate containing the entire history
   * in the ghost resource, while [mapsto] only assert over the current generation
   * history *)
  Definition fmapsto (ℓ: loc) (dq: dfrac) (h_full: leibnizO history): iProp Σ :=
    gen_own heap_name (gmap_view_frag ℓ dq h_full).

  Definition mapsto (ℓ: loc) (dq: dfrac) (h: leibnizO history): iProp Σ :=
    ∃ OCV (h_full: leibnizO history), "crashed_at_offset" ∷ crashed_at_offset OCV ∗
                  "%drop_prefix_eq" ∷ ⌜ h = drop_prefix h_full (OCV !!0 ℓ) ⌝ ∗
                  "fmapsto" ∷ fmapsto ℓ dq h_full.

  (* [hist] might have locations that are not in [OCV]. Hence we cannot use
   * [map_zip_with] here. *)
  (* Definition store_drop_prefix OCV (hist : store) := *)
  (*   map_imap (λ l h, Some $ drop_prefix h (OCV !!0 l)) hist. *)
  (* The [map_imap] definition is giving me a lot of trouble with
   * [heap_array] related lemmas. I'm restating it with [map_zip_with]
   * and manual padding *)

  Definition store_drop_prefix OCV (hist : store) :=
    map_zip_with
      (λ h '(MaxNat n), drop_prefix h n)
      hist
      (OCV ⊔ (view_to_zero $ max_view hist)).

  Lemma store_drop_prefix_alt ℓ OCV hist:
    (store_drop_prefix OCV hist) !! ℓ = (λ h, drop_prefix h (OCV !!0 ℓ)) <$> hist !! ℓ.
  Proof.
    rewrite map_lookup_zip_with lookup_op ?lookup_fmap /lookup_zero /=.
    destruct (hist !! ℓ) as [? | ] eqn:Heqn; last done.
    simpl.
    set v := (OCV !! ℓ).
    destruct v; last done.
    simpl.
    rewrite Nat.max_0_r //.
  Qed.

  Lemma dom_store_drop_prefix OCV hist:
    dom $ store_drop_prefix OCV hist = dom hist.
  Proof.
    rewrite dom_map_zip_with_L /view_to_zero dom_op ?dom_fmap_L /=.
    set_solver.
  Qed.

  Lemma disjoint_store_drop_prefix V store:
    dom V ## dom store →
    store_drop_prefix V store = store.
  Proof.
    intros.
    rewrite /store_drop_prefix.
    apply map_eq.
    intros ℓ.
    rewrite map_lookup_zip_with lookup_op ?lookup_fmap /=.
    set v := (V !! ℓ).
    destruct (store !! ℓ) as [ h | ] eqn:Heqn; last done.
    simpl.
    apply elem_of_dom_2 in Heqn.
    assert (v = None) as ->
                         by (apply not_elem_of_dom; set_solver).
    rewrite /= drop_prefix_zero //.
  Qed.

  Lemma store_drop_prefix_union OCV store1 store2:
    store1 ##ₘ store2 →
    store_drop_prefix OCV (store1 ∪ store2) =
    store_drop_prefix OCV store1 ∪ store_drop_prefix OCV store2.
  Proof.
    intros H.
    rewrite /store_drop_prefix.
    apply map_eq.
    intros ℓ.
    rewrite ?map_lookup_zip_with ?lookup_op ?lookup_fmap /=.
    destruct ((store1 ∪ store2) !! ℓ) eqn:Heqn; simpl.
    - rewrite map_disjoint_alt in H.
      destruct (H ℓ) as [ ? | ? ].
      + rewrite lookup_union_r;
          rewrite ?map_lookup_zip_with ?lookup_op ?lookup_fmap /=;
          simplify_map_eq; last done.
        rewrite lookup_union_r in Heqn; last done.
        simplify_map_eq.
        set v := (OCV !! ℓ).
        by destruct v.
      + rewrite lookup_union_l;
          rewrite ?map_lookup_zip_with ?lookup_op ?lookup_fmap /=;
          simplify_map_eq; last done.
        rewrite lookup_union_l in Heqn; last done.
        simplify_map_eq.
        set v := (OCV !! ℓ).
        by destruct v.
    - symmetry.
      apply lookup_union_None.
      apply lookup_union_None in Heqn as [??].
      rewrite ?map_lookup_zip_with ?lookup_op ?lookup_fmap /=.
      simplify_map_eq.
      done.
  Qed.

  Lemma insert_store_drop_prefix ℓ t v hist hist' OCV store:
    ℓ ∈ dom store →
    hist' = (drop_prefix hist (OCV !!0 ℓ)) →
    store_drop_prefix OCV (<[ℓ := <[ t + (OCV !!0 ℓ) := v ]> hist]>store) =
    <[ℓ := <[ t := v ]> hist' ]> (store_drop_prefix OCV store).
  Proof.
    intros.
    subst hist'.
    set t' := t + (OCV !!0 ℓ).
    replace t with (t' - (OCV !!0 ℓ)) by lia.
    rewrite drop_prefix_insert.
    rewrite Nat.sub_add; last lia.
    rewrite /store_drop_prefix.
    set padded_view := (e in map_zip_with _ (insert _ _ _) e).
    replace padded_view with (<[ℓ := MaxNat (OCV !!0 ℓ)]> padded_view).
    - rewrite -map_insert_zip_with.
      do 3 f_equal.
      apply view_to_zero_dom_eq.
      rewrite ?dom_fmap_L dom_insert_L.
      set_solver.
    - apply insert_id.
      rewrite lookup_op /=.
      rewrite (view_to_zero_dom_eq _ (max_view store)).
      2: { rewrite ?dom_fmap_L dom_insert_L.
           set_solver. }
      erewrite view_to_zero_lookup.
      2: { apply (lookup_lookup_total_dom (Inhabited0 := populate (MaxNat 0))).
           rewrite ?dom_fmap_L //. }
      rewrite /lookup_zero.
      set v' := (OCV !! ℓ).
      destruct v' as [[?] | ]; simpl; last done.
      rewrite -Some_op max_nat_op Nat.max_0_r //.
  Qed.

  (* [gen_heap] lemmas, probably better put into typeclass instances later *)

  Lemma fmapsto_heap_valid heap ℓ dq h_full:
    own_auth_heap heap -∗ fmapsto ℓ dq h_full -∗ ⌜ heap !! ℓ = Some h_full ⌝.
  Proof.
    iIntros "heap fmapsto".
    iNamed "heap".
    iDestruct (gen_own_valid_2 with "own_auth fmapsto") as %[_ [_ look]]%gmap_view_both_dfrac_valid_L.
    done.
  Qed.

  Lemma mapsto_heap_valid OCV heap ℓ dq h:
    crashed_at_offset OCV -∗ own_auth_heap heap -∗ mapsto ℓ dq h -∗ ⌜ store_drop_prefix OCV heap !! ℓ = Some h ⌝.
  Proof.
    iIntros "crashed_at_offset' heap mapsto".
    iNamed "mapsto".
    iDestruct (crashed_at_offset_agree with "crashed_at_offset crashed_at_offset'") as "->".
    iDestruct (fmapsto_heap_valid with "[$] [$]") as %look.
    iPureIntro.
    rewrite store_drop_prefix_alt look /=.
    by f_equiv.
  Qed.

  Lemma heap_alloc_fmapsto σ ℓ h_full :
    σ !! ℓ = None →
    own_auth_heap σ ==∗ own_auth_heap (<[ℓ:=h_full]>σ) ∗ fmapsto ℓ (DfracOwn 1) h_full.
  Proof.
    iIntros (Hσl).
    iNamed 1.
    iMod (gen_own_update with "own_auth") as "[own_auth frag]".
    { eapply (gmap_view.gmap_view_alloc _ _ (DfracOwn 1)); [ apply Hσl | done ]. }
    iFrame.
    iModIntro.
    iExists _.
    iFrame "#".
  Qed.

  Lemma heap_alloc_big_fmapsto σ σ' :
    σ' ##ₘ σ →
    own_auth_heap σ ==∗
    own_auth_heap (σ' ∪ σ) ∗ ([∗ map] ℓ ↦ h_full ∈ σ', fmapsto ℓ(DfracOwn 1) h_full).
  Proof.
    revert σ; induction σ' as [| ℓ v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (heap_alloc_fmapsto with "Hσ'σ") as "[$ $]";
    first by apply lookup_union_None.
  Qed.

  Lemma fmapsto_heap_update σ ℓ h_full1 h_full2:
    own_auth_heap σ -∗
    fmapsto ℓ (DfracOwn 1) h_full1 ==∗
    own_auth_heap (<[ℓ:=h_full2]>σ) ∗ fmapsto ℓ (DfracOwn 1) h_full2.
  Proof.
    iNamed 1.
    iIntros "fmapsto".
    iMod (gen_own_update_2 with "own_auth fmapsto") as "[$ $]".
    { apply gmap_view_update. }
    iModIntro.
    iExists _.
    iFrame "#".
  Qed.

  Lemma mapsto_heap_update OCV σ ℓ h1 h_full2:
    crashed_at_offset OCV -∗
    own_auth_heap σ -∗
    mapsto ℓ (DfracOwn 1) h1 ==∗
    own_auth_heap (<[ℓ := h_full2]>σ) ∗
    mapsto ℓ (DfracOwn 1) (drop_prefix h_full2 (OCV !!0 ℓ)).
  Proof.
    iIntros "#crashed_at_offset' auth". iNamed 1.
    iDestruct (crashed_at_offset_agree with "crashed_at_offset crashed_at_offset'") as "->".
    iMod (fmapsto_heap_update with "[$] [$]") as "[$ fmapsto]".
    iExists _, _.
    iFrame.
    done.
  Qed.

  (* Lemma own_auth_heap_alloc LV heap OCV : *)
  (*   crashed_at_offset OCV -∗ *)
  (*   rely_self crashed_at_name (crashed_at_pred LV) ==∗ *)
  (*   ∃ heapγ, own_auth_heap heapγ heap. *)
  (* Proof. *)
  (*   iIntros "crashed #rely". *)
  (*   iMod (own_gen_alloc (DS := [#_]) *)
  (*     (gmap_view_auth (DfracOwn 1) heap) *)
  (*     [#crashed_at_name] [##crashed_at_pred LV] with "[]") as (γ) "[HH tok]". *)
  (*   { apply gmap_view_auth_valid. } *)
  (*   { iIntros (i'). *)
  (*     dependent elimination i' as [0%fin]. *)
  (*     iApply "rely". } *)
  (*   iMod ( *)
  (*     token_strengthen_promise (DS := [#_]) *)
  (*       _ [#_] [##_] _ heap_rel _ True_pred with "[] tok") *)
  (*     as "tok". *)
  (*   { intros ???. unfold True_rel. rewrite huncurry_curry. done. } *)
  (*   { done. } *)
  (*   { intros ts. dependent elimination ts. done. } *)
  (*   2: { *)
  (*     iIntros (i'). *)
  (*     dependent elimination i' as [0%fin]. *)
  (*     iApply "rely". } *)
  (*   { intros ts crashedPred. *)
  (*     dependent elimination ts as [hcons tC hnil]. *)
  (*     destruct crashedPred as ((OCV2 & ? & ->) & _). *)
  (*     exists (map_entry_lift_gmap_view (drop_above_hist OCV2)). *)
  (*     split; first apply _. *)
  (*     simpl. *)
  (*     exists OCV2. done. } *)
  (*   iModIntro. *)
  (*   iExists γ, OCV. *)
  (*   unfold own_auth_heap. *)
  (*   iFrame. *)
  (*   iDestruct (token_to_rely with "tok") as "$". *)
  (* Qed. *)

  Lemma map_entry_lift_gmap_view_auth dq
      (heap : gmap loc (leibnizO history)) map_entry :
    (map_entry_lift_gmap_view map_entry (gmap_view_auth dq heap)) =
    (gmap_view_auth dq (map_imap map_entry heap)).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    rewrite agree_map_to_agree. done.
  Qed.

  Lemma own_auth_heap_nextgen heap :
    own_auth_heap heap
    ⊢ ⚡==> ∃ OCV,
      crashed_at_offset OCV ∗
      own_auth_heap (drop_above_map OCV heap).
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
    iFrame "#".
    iSplit.
    { iExists _. iFrame "#". }
    { iExists _.
      iSplit. 2: { iExists _. iFrame "#". }
      rewrite map_entry_lift_gmap_view_auth.
      iFrame. }
  Qed.

  #[global]
  Instance into_nextgen_own_auth_heap heap : IntoNextgen _ _ :=
    own_auth_heap_nextgen heap.
End heap.

Notation "l ↦fh{ dq } v" := (fmapsto l dq (v%V))
  (at level 20, format "l  ↦fh{ dq }  v") : bi_scope.
Notation "l ↦fh□ v" := (fmapsto l DfracDiscarded (v%V))
  (at level 20, format "l  ↦fh□  v") : bi_scope.
Notation "l ↦fh{# q } v" := (fmapsto l (DfracOwn q) (v%V))
  (at level 20, format "l  ↦fh{# q }  v") : bi_scope.
Notation "l ↦fh v" := (fmapsto l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦fh  v") : bi_scope.

Notation "l ↦h{ dq } v" := (mapsto l dq (v%V))
  (at level 20, format "l  ↦h{ dq }  v") : bi_scope.
Notation "l ↦h□ v" := (mapsto l DfracDiscarded (v%V))
  (at level 20, format "l  ↦h□  v") : bi_scope.
Notation "l ↦h{# q } v" := (mapsto l (DfracOwn q) (v%V))
  (at level 20, format "l  ↦h{# q }  v") : bi_scope.
Notation "l ↦h v" := (mapsto l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦h  v") : bi_scope.

(* The state interpretation for the base logic. *)
Definition nvm_heap_ctx `{!nvmBaseG Σ Ω} (σ : mem_config) : iProp Σ :=
  ∃ (OV OCV : view) (full_hist : store),
    (* store view *)
    "store_view_auth" ∷ store_view_auth store_view_name (max_view σ.1) ∗
    (* crashed at *)
    "%full_hist_eq" ∷ ⌜ σ.1 = store_drop_prefix OCV full_hist ⌝ ∗
    "%Hop" ∷ ⌜ valid_heap σ.1 ⌝ ∗
    "#crashed" ∷ gen_own crashed_at_name (to_agree OV, to_agree OCV) ∗
    (* The lower bound on the next [OCV] is the current [OCV] plus [PV]. *)
    "crashed_at_tok" ∷ crashed_at_tok crashed_at_name (OCV `view_add` σ.2) ∗
    (* The interpretation of the heap. *)
    "Hσ" ∷ own_auth_heap full_hist ∗
    (* [OCV] is "the sum of all crash views". The domain of the crash views
     * only grows and is always included in the persist view. And hence the
     * domain of the persist view also contains the domain of [OCV].
     * Furthermore, the domain of persist view is always smaller than the
     * heap itself. *)
    "%ocvDom" ∷ ⌜ dom OCV ⊆ dom σ.2 ∧ dom OCV ⊆ dom σ.1 ⌝ ∗
    "pers" ∷ persisted_auth (OCV `view_add` σ.2).

Lemma view_add_lookup_zero V1 V2 ℓ :
  (V1 `view_add` V2) !!0 ℓ = (V1 !!0 ℓ) + (V2 !!0 ℓ).
Proof.
  rewrite /view_add /lookup_zero lookup_merge.
  destruct (V1 !! ℓ); destruct (V2 !! ℓ); simpl; done.
Qed.

Lemma slice_of_store_drop_prefix CV OCV full_hist :
  dom OCV ⊆ dom CV →
  slice_of_store CV (store_drop_prefix OCV full_hist) =
  store_drop_prefix (OCV `view_add` CV)
    (drop_above_map (OCV `view_add` CV) full_hist).
Proof.
  intros sub.
  apply map_eq => ℓ.
  rewrite /slice_of_store.
  rewrite /slice_of_hist.
  rewrite 2!lookup_fmap.
  rewrite /drop_above_map.
  rewrite !store_drop_prefix_alt.
  rewrite !map_lookup_imap.
  rewrite /slice_hist.
  rewrite map_zip_with_flip.
  rewrite {1}map_lookup_zip_with.
  rewrite store_drop_prefix_alt.
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

Lemma view_add_dom V1 V2 :
  dom (V1 `view_add` V2) = dom V1 ∪ dom V2.
Proof.
  apply set_eq => ℓ.
  rewrite elem_of_union 3!elem_of_dom.
  rewrite /view_add lookup_merge.
  destruct (V1 !! ℓ); destruct (V2 !! ℓ); naive_solver.
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
  iMod (crashed_at_pick_nextgen _ _ (OCV `view_add` CV)
    with "crashed crashed_at_tok") as "crashed'".
  { f_equiv. done. }
  iModIntro.
  iPoseProof (store_view_nextgen _ _ (max_view (slice_of_store CV store)) with "[$]") as "store_view_auth".
  iModIntro.
  iMod "store_view_auth".
  iDestruct "crashed'" as "(#crashed' & crashed_at_tok & pickedC)".
  iMod (crashed_at_tok_strengthen _ (OCV `view_add` CV) with "crashed_at_tok") as "tok".
  { f_equiv. done. }
  iModIntro.
  set (OCV2 := OCV `view_add` CV).
  iDestruct ("Hσ") as (?) "[(% & crashed'') Hσ]".
  iDestruct (crashed_at_both_agree with "crashed'' crashed'") as "[-> ->]".
  iExists OCV, OCV2, _.
  iFrame "Hσ store_view_auth".
  apply view_le_dom_subseteq in pIncl.
  iSplit.
  { iPureIntro. rewrite full_hist_eq.
    rewrite /OCV2.
    apply slice_of_store_drop_prefix.
    trans (dom CV); set_solver. }
  iSplit. { iPureIntro. apply store_inv_cut; done. }
  iFrame "crashed''". simpl.
  rewrite -(assoc view_add).
  rewrite view_add_view_zero.
  iFrame "tok".
  iDestruct "pers" as "(% & pers & pickedC')".
  iDestruct (gen_picked_in_agree with "pickedC' pickedC") as %eq.
  apply crashed_at_trans_inj in eq.
  rewrite eq.
  iFrame "pers".
  iPureIntro.
  rewrite /OCV2.
  rewrite /view_add.
  rewrite view_add_dom.
  rewrite /view_to_zero.
  rewrite dom_fmap.
  split; first set_solver.
  subst.
  apply consistent_cut_subseteq_dom in cut.
  rewrite /slice_of_store /slice_of_hist !dom_fmap_L dom_map_zip_with_L.
  set_solver.
Qed.
