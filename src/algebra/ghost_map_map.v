(** A "ghost map map", meaning ghost state for a map of maps.

The ghost state is insert-only. New entries can be added but existing entries
can not be modified.  *)

From iris.algebra Require Import auth gmap.
From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

From self Require Import extra.
From self.algebra Require Import ghost_map.

Class ghost_map_mapG Σ (K1 K2 V : Type) `{Countable K1, Countable K2} :=
  GhostMapMapG {
      ghost_map_outer_inG :> ghost_mapG Σ K1 (gname * gname);
      ghost_map_inner_inG :> ghost_mapG Σ K2 V;
      ghost_map_inner_frac_inG :> inG Σ dfracR;
    }.

Definition dfrac_div_2 (dq : dfrac) :=
  match dq with
  | DfracOwn q => DfracOwn (q / 2)
  | DfracDiscarded => DfracDiscarded
  | DfracBoth q => DfracBoth (q / 2)
  end.

Section definitions.
  Context `{ghost_map_mapG Σ K1 K2 V}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).

  (* Ownership over the entire map. *)
  (* FIXME: Take a [dq] argument. *)
  Definition full_map γ dq m : iProp Σ :=
    ∃ (gnames : gmap K1 (gname * gname)),
      ghost_map_auth γ dq gnames ∗
        ([∗ map] k1 ↦ γi;mi ∈ gnames;m,
           ghost_map_auth γi.1 (dfrac_div_2 dq) mi).

  (* Ownership over the entire history for a single key. *)
  Definition full_entry γ k1 dq mi : iProp Σ :=
    ∃ γp, k1 ↪[γ]□ γp ∗ own γp.2 dq ∗ ghost_map_auth γp.1 (dfrac_div_2 dq) mi.

  Definition frag_entry γ k1 k2 v : iProp Σ :=
    ∃ γi γf, k1 ↪[γ]□ (γi, γf) ∗ k2 ↪[γi]□ v.

End definitions.

Section lemmas.
  Context `{ghost_map_mapG Σ K1 K2 V}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).

  Global Instance full_entry_fractional γ ℓ enc_abs_hist :
    Fractional (λ q, full_entry γ ℓ (DfracOwn q) enc_abs_hist).
  Proof.
    intros p q.
    rewrite /full_entry.
    iSplit.
    - simpl. rewrite Qp_div_add_distr.
      iDestruct 1 as ([γi γf]) "(#ptsa & [dq dq'] & [auth auth'])".
      iSplitL "dq auth"; iExists (γi, γf); iFrame "∗#".
    - iIntros "[(%γp & #pts & dq & auth) (%γp' & #pts' & dq' & auth')]".
      iDestruct (ghost_map_elem_agree with "pts pts'") as %<-.
      iCombine "auth auth'" as "auth".
      iCombine "dq dq'" as "dq".
      rewrite -Qp_div_add_distr.
      iExists γp; iFrame "∗#".
  Qed.
  Global Instance own_full_encoded_history_as_fractional γ ℓ q enc_abs_hist :
    AsFractional
      (full_entry γ ℓ (DfracOwn q) enc_abs_hist)
      (λ q, full_entry γ ℓ (DfracOwn q) enc_abs_hist)%I q.
  Proof. split; [done | apply _]. Qed.

  Lemma full_map_full_entry γ k1 dq1 dq2 m mi :
    full_map γ dq1 m -∗
    full_entry γ k1 dq2 mi -∗
    ⌜ m !! k1 = Some mi ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as ([γi γf]) "(pts & dq & authI)".
    iDestruct (ghost_map_lookup with "auth pts") as %look.
    iDestruct (big_sepM2_lookup_l with "map") as (mi' mLook) "authI'"; first done.
    iDestruct (ghost_map_auth_agree with "authI authI'") as %->.
    done.
  Qed.

  Lemma full_map_frag_entry γ k1 k2 dq1 m v :
    full_map γ dq1 m -∗
    frag_entry γ k1 k2 v -∗
    ∃ mi, ⌜ m !! k1 = Some mi ⌝ ∗ ⌜ mi !! k2 = Some v ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as (γi γf) "(pts1 & pts2)".
    iDestruct (ghost_map_lookup with "auth pts1") as %look.
    iDestruct (big_sepM2_lookup_l with "map") as (mi mLook) "authI"; first done.
    iExists mi.
    iDestruct (ghost_map_lookup with "authI pts2") as %->.
    done.
  Qed.

  Lemma full_map_persist γ q m :
    full_map γ (DfracOwn q) m ==∗ full_map γ DfracDiscarded m.
  Proof.
    iDestruct 1 as (?) "[auth map]".
    iExists _.
    iMod (ghost_map_auth_persist with "auth") as "$".
    iApply big_sepM2_bupd.
    iApply (big_sepM2_impl with "map").
    iIntros "!>" (?????) "authI".
    iApply (ghost_map_auth_persist with "authI").
  Qed.

  Local Lemma full_entry_alloc_big m :
    ⊢ |==> ∃ gnames,
      ([∗ map] γi;mi ∈ gnames;m,
          ghost_map_auth γi.1 (dfrac_div_2 (DfracOwn 1)) mi) ∗
      ([∗ map] k1 ↦ γi;mi ∈ gnames;m,
        ghost_map_auth γi.1 (dfrac_div_2 (DfracOwn 1)) mi ∗
        own γi.2 (DfracOwn 1)) ∗
      ([∗ map] k1 ↦ γi;mi ∈ gnames;m,
        ([∗ map] k↦v ∈ mi, k ↪[γi.1]□ v)).
  Proof.
    setoid_rewrite <- big_sepM2_sep. setoid_rewrite <- big_sepM2_sep.
    induction m as [|k1 mi m ? IH] using map_ind.
    - naive_solver.
    - iMod IH as (gnames) "M".
      iDestruct (big_sepM2_dom with "M") as %domEq.
      iMod (ghost_map_alloc_persistent mi) as (γ1) "[[H1 H1'] H2]".
      iMod (own_alloc (DfracOwn 1)) as (γ2) "dq"; first done.
      iExists (<[ k1 := (γ1, γ2) ]> gnames).
      iModIntro.
      rewrite big_sepM2_insert; try done.
      2: { apply not_elem_of_dom. rewrite domEq. apply not_elem_of_dom. done. }
      iFrame.
  Qed.

  Lemma full_map_alloc m :
    ⊢ |==> ∃ γ,
      full_map γ (DfracOwn 1) m ∗
      ([∗ map] k1 ↦ mi ∈ m, full_entry γ k1 (DfracOwn 1) mi) ∗
      [∗ map] k1 ↦ mi ∈ m, [∗ map] k2 ↦ v ∈ mi, frag_entry γ k1 k2 v.
  Proof.
    rewrite /full_map /full_entry.
    iMod (full_entry_alloc_big m) as (gnames) "(M1 & M2 & F)".
    iMod (ghost_map_alloc_persistent gnames) as (γ) "[H1 #ptsMap]".
    iExists γ.
    rewrite bi.sep_exist_r.
    iExists (gnames).
    iFrame.
    iModIntro.
    iSplit.
    2: {
      rewrite /frag_entry.
      iApply big_sepM_forall. iIntros (???).
      iApply big_sepM_forall. iIntros (???).
      iDestruct (big_sepM2_lookup_r with "F") as ([??]) "H"; first done.
      iExists _, _.
      iDestruct "H" as (look) "M".
      iDestruct (big_sepM_lookup with "ptsMap") as "$"; first done.
      iDestruct (big_sepM_lookup with "M") as "$"; first done. }
    iApply big_sepM_exist_l.
    iExists gnames.
    iApply (big_sepM2_impl with "M2").
    iIntros "!>" (k [??] ???) "(A & B & C)".
    iFrame.
    iDestruct (big_sepM_lookup with "ptsMap") as "$"; first done.
    iCombine "B C" as "$".
  Qed.

  Lemma map_eq_dom m1 m2 :
    dom (gset _) m1 = dom _ m2 →
    m1 = m2 ↔ (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → x = y).
  Proof.
    intros domEq.
    rewrite map_eq_iff. split.
    - intros ? ? ? ? ? ?. apply (inj Some). congruence.
    - intros l k1.
      destruct (m1 !! k1) as [mi|] eqn:eq.
      * assert (is_Some (m2 !! k1)) as [mi' eq2].
        { apply elem_of_dom. rewrite -domEq. apply elem_of_dom. done. }
        rewrite eq2.
        f_equal.
        eapply l; try done.
      * symmetry.
        apply not_elem_of_dom.
        rewrite -domEq.
        apply not_elem_of_dom.
        done.
  Qed.

  Lemma full_entry_valid γ k1 dq mi : full_entry γ k1 dq mi -∗ ⌜ ✓ dq ⌝.
  Proof.
    iDestruct 1 as (?) "(_ & dq & _)".
    iDestruct (own_valid with "dq") as %val.
    done.
  Qed.

  (* Agreement lemmas. *)

  Lemma full_map_agree γ dq1 dq2 m1 m2 :
    full_map γ dq1 m1 -∗ full_map γ dq2 m2 -∗ ⌜ m1 = m2 ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as (gnames') "(auth' & map')".
    iDestruct (ghost_map_auth_agree with "auth auth'") as %<-.
    iDestruct (big_sepM2_dom with "map") as %domEq1.
    iDestruct (big_sepM2_dom with "map'") as %domEq2.
    rewrite map_eq_dom; last congruence.
    iIntros (k1 mi mi' m1Look m2Look).
    assert (is_Some (gnames !! k1)) as [γi gnamesLook].
    { apply elem_of_dom. rewrite domEq1. apply elem_of_dom. done. }
    iDestruct (big_sepM2_lookup with "map") as "authI"; [done|done| ].
    iDestruct (big_sepM2_lookup with "map'") as "authI'"; [done|done| ].
    iDestruct (ghost_map_auth_agree with "authI authI'") as "$".
  Qed.

  Lemma full_entry_agree γ k1 dq1 dq2 mi1 mi2 :
    full_entry γ k1 dq1 mi1 -∗ full_entry γ k1 dq2 mi2 -∗ ⌜ mi1 = mi2 ⌝.
  Proof.
    iDestruct 1 as (γi) "(pts & dq & auth)".
    iDestruct 1 as (γi') "(pts' & dq' & auth')".
    iDestruct (ghost_map_elem_agree with "pts pts'") as %<-.
    iDestruct (ghost_map_auth_agree with "auth auth'") as "$".
  Qed.

  Lemma frag_entry_agree γ k1 k2 v v' :
    frag_entry γ k1 k2 v -∗ frag_entry γ k1 k2 v' -∗ ⌜ v = v' ⌝.
  Proof.
    iDestruct 1 as (??) "[pts1 pts2]".
    iDestruct 1 as (??) "[pts1' pts2']".
    iDestruct (ghost_map_elem_agree with "pts1 pts1'") as %[= <- <-].
    iDestruct (ghost_map_elem_agree with "pts2 pts2'") as %<-.
    done.
  Qed.

  Lemma full_entry_frag_entry γ k1 dq mi k2 v :
    full_entry γ k1 dq mi -∗
    frag_entry γ k1 k2 v -∗
    ⌜ mi !! k2 = Some v ⌝.
  Proof.
    iDestruct 1 as ([γi ?]) "(pts & ? & auth)". simpl.
    iDestruct 1 as (γi' ?) "(pts' & pts2)".
    iDestruct (ghost_map_elem_agree with "pts pts'") as %[= <- <-].
    iDestruct (ghost_map_lookup with "auth pts2") as "$".
  Qed.

  (* Insert a new entry at the top level *)
  Lemma full_map_insert γ m k1 mi :
    m !! k1 = None →
    full_map γ (DfracOwn 1) m ==∗
      full_map γ (DfracOwn 1) (<[k1 := mi]> m) ∗
      full_entry γ k1 (DfracOwn 1) mi ∗
      [∗ map] k2 ↦ v ∈ mi, frag_entry γ k1 k2 v.
  Proof.
    intros ?.
    rewrite /full_map /full_entry.
    iDestruct 1 as (gnames) "[auth map]".
    iDestruct (big_sepM2_dom with "map") as %domEq.
    (* Allocate the ghost state for the entry. *)
    iMod (ghost_map_alloc_persistent mi) as (γi) "[[authI authI'] H]".
    iMod (own_alloc (DfracOwn 1)) as (γf) "dq"; first done.
    assert (gnames !! k1 = None).
    { apply not_elem_of_dom. rewrite domEq. apply not_elem_of_dom. done. }
    iMod (ghost_map_insert_persist k1 (γi, γf) with "auth") as "[auth #pts]";
      first done.
    iModIntro. iSplitL "auth authI map".
    { iExists (<[k1 := (_, _)]> gnames).
      rewrite big_sepM2_insert; [|done|done].
      iFrame. }
    iSplit.
    { iExists _. iFrame "pts". iFrame. }
    iApply (big_sepM_impl with "H").
    { iIntros "!>" (???) "pts2". iExists _, _. iFrame "pts pts2". }
  Qed.

  Lemma full_map_full_entry_insert γ m k1 k2 v mi :
    mi !! k2 = None →
    full_map γ (DfracOwn 1) m -∗
    full_entry γ k1 (DfracOwn 1) mi ==∗
      let mi' := (<[ k2 := v ]>mi) in
      full_map γ (DfracOwn 1) (<[ k1 := mi' ]> m) ∗
      full_entry γ k1 (DfracOwn 1) mi' ∗
      frag_entry γ k1 k2 v.
  Proof.
    iIntros (?) "FM FE".
    iDestruct (full_map_full_entry with "FM FE") as %mLook.
    iDestruct "FM" as (gnames) "[auth map]".
    iDestruct "FE" as ([γi γf]) "(pts & dq & authI)".
    iDestruct (ghost_map_lookup with "auth pts") as %look.
    iDestruct (big_sepM2_delete with "map") as "[authI' map]"; [done|done| ].
    iCombine "authI authI'" as "authI".
    iMod (ghost_map_insert_persist k2 v with "authI") as "[[authI authI'] ptsI]";
      first done.
    iDestruct (big_sepM2_insert_delete with "[$map $authI']") as "map".
    rewrite (insert_id gnames); last done.
    iModIntro.
    iSplitL "auth map". { iExists gnames. iFrame. }
    iSplit. { iExists _. iFrame. }
    iExists _, _. iFrame.
  Qed.

End lemmas.

Opaque full_map.
Opaque full_entry.
Opaque frag_entry.
