(* Weakest precondition rules for non-atomic locations. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self Require Export extra ipm_tactics encode_relation.
From self.high Require Export dprop.
From self Require Export view.
From self.lang Require Export lang lemmas tactics.
From self.base Require Import primitive_laws.
From self.lang Require Import syntax.
From self.high Require Import resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol.

Section wp_na_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (ϕ : ST → val → nvmDeltaG Σ → dProp Σ).

  Lemma wp_load_na ℓ (b : bool) ss s Q ϕ `{!LocationProtocol ϕ} positive E :
    last ss = Some s →
    {{{ mapsto_ex b ℓ ss ∗
        know_protocol ℓ ϕ ∗
        (<obj> (∀ v, ϕ s v _ -∗ Q v ∗ ϕ s v _)) }}}
      Load (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ v, RET v; mapsto_ex b ℓ ss ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "(pts & temp & pToQ)".
    iNamed "temp".
    iDestruct "pts" as (?tP ?tS SV absHist msg) "pts". iNamed "pts".
    iDestruct "haveSV" as %haveSV.
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV' PV] BV] incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. }
    { by apply prim_step_load_no_fork. }
    iNamed 1.
    iDestruct (own_all_preds_pred with "predicates knowPred") as
      (pred predsLook) "#predsEquiv".
    iDestruct (own_full_history_agree with "[$] [$]") as %absHistlook.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    (* clear predsLook'. *)

    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply (wp_load (extra := {| extra_state_interp := True |}) with "[$pts $val]").
    iNext. iIntros (t' v' msg') "[pts (%look & %msgVal & %gt)]".
    rewrite /store_view. simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val".

    (* We need to conclude that the only write we could read is [tS]. I.e., that
    [t' = tS]. *)
    assert (tS ≤ SV' !!0 ℓ) as tSle.
    { etrans; first done.
      destruct TV as [[??]?].
      destruct TV' as [[??]?].
      rewrite /store_view /=.
      apply view_lt_lt; last done.
      etrans; first apply haveSV.
      etrans; first apply incl; apply incl2. }
    assert (tS ≤ t') as lte.
    { etrans; first done. apply gt. }
    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    assert (is_Some (absHist !! t')) as HI.
    { apply elem_of_dom.
      erewrite <- dom_fmap_L.
      erewrite <- domEq.
      apply elem_of_dom.
      naive_solver. }
    assert (t' = tS) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      pose proof (nolater t' lt) as eq.
      rewrite eq in HI. inversion HI as [? [=]]. }
    assert (absHist !! tS = Some s) as lookS.
    { rewrite -sLast.
      apply map_slice_lookup_hi in slice.
      rewrite slice.
      done. }
    clear lte HI.

    iDestruct (auth_map_map_lookup_agree with "[$] [$]") as %eq.
    { done. } { done. }
    subst.

    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      first done.
    { rewrite lookup_fmap. rewrite lookS. done. }
    iDestruct (predicate_holds_phi with "predsEquiv predHolds") as "phi";
      first done.
    rewrite monPred_at_objectively.
    iSpecialize ("pToQ" $! (msg_to_tv msg) (msg_val msg)).
    rewrite monPred_at_wand.
    iDestruct ("pToQ" with "[//] phi") as "[Q phi]".
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iApply (predicate_holds_phi with "predsEquiv phi"). done. }
    (* Reinsert into the map. *)
    iDestruct ("predsHold" with "[predMap]") as "predsHold". { naive_solver. }

    iSplitR "ptsMap physHist allOrders ordered predsHold history predicates
             sharedLocs crashedAt allBumpers bumpMono predPostCrash
             sharedLocsHistories"; last first.
    { repeat iExists _. iFrameNamed. }
    iSplit; first done.
    iApply "Φpost".
    iSplitR "Q".
    2: {
      simplify_eq.
      rewrite /msg_to_tv.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      - etrans; first done.
        destruct TV as [[??]?]. destruct TV' as [[??]?].
        etrans; first apply haveSV.
        etrans; first apply incl.
        apply incl2.
      - admit.
      - apply view_empty_least.
    }
    iExists _, _, _, _, _.
    iFrameNamed.
    monPred_simpl.
    iDestruct (objective_at with "pers") as "$". { destruct b; apply _. }
    iPureIntro.
    etrans. eassumption.
    etrans. eassumption.
    eassumption.
  Admitted.

  Lemma wp_store_na ℓ b ss v s__last s ϕ `{!LocationProtocol ϕ} st E :
    last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_ex b ℓ ss ∗ know_protocol ℓ ϕ ∗ ϕ s v _ }}}
      #ℓ <- v @ st; E
    {{{ RET #(); mapsto_ex b ℓ (ss ++ [s]) }}}.
  Proof.
    intros last stateGt Φ.
    iStartProof (iProp _). iIntros (TV).
    iIntros "[pts phi]".
  Admitted.
  (*   iDestruct "pts" as (?tGP ?tP ?tS absHist hist) "(pts & predsHold & %incrL & %lookupP & %lookupV & %nolater & %lastVal & hist & slice & %know & per)". *)
  (*   rewrite monPred_at_wand. simpl. *)
  (*   iIntros (TV' incl) "Φpost". *)
  (*   rewrite monPred_at_later. *)
  (*   rewrite wp_eq /wp_def. *)
  (*   rewrite wpc_eq. simpl. *)
  (*   iIntros ([[SV PV] BV] incl2) "#val interp". *)
  (*   rewrite monPred_at_pure. *)
  (*   iApply program_logic.crash_weakestpre.wp_wpc. *)
  (*   iApply (wp_store with "pts"). *)
  (* Qed. *)

End wp_na_rules.
