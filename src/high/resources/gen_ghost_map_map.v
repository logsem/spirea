From Equations Require Import Equations.
From iris.algebra Require Import gmap_view.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises.
From self.algebra Require Import view.
From self.base Require Import generational_resources.

From self.lang Require Import lang.

From self.high.resources Require Import gen_ghost_map.

Set Default Proof Using "Type*".

(* the following sections is mostly adapted from the [ghost_map_map.v] file. *)
(* major simplification: I'm removing the second ghost resource about fractions,
 * since I believe it's obsolete after nextgen update. *)
Class ghost_map_mapGpreS (K1 K2 V: Type) Σ Ω `{Countable K1, Countable K2}  `{!crashed_atGpreS Σ Ω} := {
    ghost_map_outer_GpreS :: ghost_mapGpreS K1 gname Σ Ω;
    ghost_map_inner_GpreS :: ghost_mapGpreS K2 V Σ Ω;
  }.

Definition dfrac_div_2 (dq : dfrac) :=
  match dq with
  | DfracOwn q => DfracOwn (q / 2)
  | DfracDiscarded => DfracDiscarded
  | DfracBoth q => DfracBoth (q / 2)
  end.

Section definitions.
  Notation K1 := loc.
  Notation K2 := nat.

  Context `{!nvmBaseGS Σ Ω, !ghost_map_mapGpreS K1 K2 V Σ Ω}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).
  Implicit Types (dq: dfrac) (γ: gname) (bumper: V → option V).

  (* TODO: make these two assumption into a typeclass *)
  Context `{!ghost_mapGpreS loc (V → option V) Σ Ω}. (* ghost map for bumpers *)
  Variable (γbumper: gname).
  (* reminder to myself:
   * [k1] is location, [k2] is timestamp,
   * [γm] is the ghost name for the inner map *)

  (* Ownership over the entire map. *)
  Definition full_map γ dq m : iProp Σ :=
    ∃ (gnames : gmap loc gname),
      ghost_map_auth γ loc_map_rel dq gnames ∗
        ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
           ∃ bumper, k1 ↪[γbumper, loc_map_rel]□ bumper ∗
                     ghost_map_auth γm (hist_map_rel k1 bumper) (dfrac_div_2 dq) mi).

  (* Ownership over the entire history for a single key. *)
  Definition full_entry γ k1 dq mi : iProp Σ :=
    ∃ γm bumper, k1 ↪[γ, loc_map_rel]□ γm ∗
                 k1 ↪[γbumper, loc_map_rel]□ bumper ∗
                 ghost_map_auth γm (hist_map_rel k1 bumper) (dfrac_div_2 dq) mi.

  Definition frag_entry γ k1 k2 v : iProp Σ :=
    ∃ γm bumper, k1 ↪[γ, loc_map_rel]□ γm ∗
                    k1 ↪[γbumper, loc_map_rel]□ bumper ∗
                    k2 ↪[γm, hist_map_rel k1 bumper]□ v.
End definitions.

Section lemmas.
  Notation K1 := loc.
  Notation K2 := nat.
  Notation V := positive.
  Context `{!nvmBaseGS Σ Ω, !ghost_map_mapGpreS K1 K2 V Σ Ω}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).
  Implicit Types (dq: dfrac) (γ: gname) (bumper: V → option V).

  (* TODO: make these two assumption into a typeclass *)
  Context `{!ghost_mapGpreS loc (V → option V) Σ Ω}. (* ghost map for bumpers *)
  Variable (γbumper: gname).

  Global Instance full_entry_fractional γ ℓ enc_abs_hist :
    Fractional (λ q, full_entry γbumper γ ℓ (DfracOwn q) enc_abs_hist).
  Proof.
    intros p q.
    rewrite /full_entry.
    iSplit.
    - simpl. rewrite Qp.div_add_distr.
      iDestruct 1 as (γm bumper) "(#ptsa & #? & auth)".
      (* TODO: investigate why typeclasses doesn't work here *)
      rewrite ghost_map_auth_fractional.
      iDestruct "auth" as "[auth auth']".
      iSplitL "auth"; iExists γm, bumper; iFrame "∗#".
    - iIntros "[(%γm & %bumper & #pts & #bumper & auth) (%γm' & %bumper' & #pts' & #bumper' & auth')]".
      iDestruct (ghost_map_elem_agree with "pts pts'") as %<-.
      iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
      rewrite /dfrac_div_2.
      iPoseProof (@ghost_map_auth_fractional with "[$auth $auth']") as "auth".
      rewrite Qp.div_add_distr.
      iExists γm, bumper; iFrame "∗#".
  Qed.

  Global Instance own_full_encoded_history_as_fractional γ ℓ q enc_abs_hist :
    AsFractional
      (full_entry γbumper γ ℓ (DfracOwn q) enc_abs_hist)
      (λ q, full_entry γbumper γ ℓ (DfracOwn q) enc_abs_hist)%I q.
  Proof. split; [done | apply _]. Qed.

  Lemma full_map_full_entry γ k1 dq1 dq2 m mi :
    full_map γbumper γ dq1 m -∗
    full_entry γbumper γ k1 dq2 mi -∗
    ⌜ m !! k1 = Some mi ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as (γm bumper) "(pts & #bumper & authI)".
    iDestruct (ghost_map_lookup with "auth pts") as %look.
    iDestruct (big_sepM2_lookup_l with "map") as (mi' mLook bumper') "[#bumper' authI']"; first done.
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %->.
    iDestruct (ghost_map_auth_agree with "authI authI'") as %->.
    done.
  Qed.

  Lemma full_map_frag_entry γ k1 k2 dq1 m v :
    full_map γbumper γ dq1 m -∗
    frag_entry γbumper γ k1 k2 v -∗
    ∃ mi, ⌜ m !! k1 = Some mi ⌝ ∗ ⌜ mi !! k2 = Some v ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as (γm bumper) "(#ptsγp & #bumper & #ptsv)".
    iDestruct (ghost_map_lookup with "auth ptsγp") as %look.
    iDestruct (big_sepM2_lookup_l with "map") as (mi mLook bumper') "[#bumper' authI]"; first done.
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %->.
    iExists mi.
    iDestruct (ghost_map_lookup with "authI ptsv") as %->.
    done.
  Qed.

  Lemma full_map_persist γ q m :
    full_map γbumper γ (DfracOwn q) m ==∗ full_map γbumper γ DfracDiscarded m.
  Proof.
    iDestruct 1 as (?) "[auth map]".
    iExists _.
    iMod (ghost_map_auth_persist with "auth") as "$".
    iApply big_sepM2_bupd.
    iApply (big_sepM2_impl with "map").
    iIntros "!>" (?????) "authI".
    iDestruct "authI" as (bumper) "[#bumper authI]".
    iMod (ghost_map_auth_persist with "authI") as "authI".
    iExists _.
    iFrame "∗#".
    done.
  Qed.
  
  (* since the new [ghost_map_map] depends on bumpers for nextgen behavior,
   * its allocation now requires knowledge of bumpers at the allocated entries. *)

  Local Lemma full_entry_alloc_big m :
    ([∗set] k1 ∈ dom m, ∃ bumper, k1 ↪[γbumper, loc_map_rel]□ bumper) ==∗
    ∃ gnames,
      ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
         ∃ bumper, k1 ↪[γbumper, loc_map_rel]□ bumper ∗
                   ghost_map_auth γm (hist_map_rel k1 bumper) (dfrac_div_2 (DfracOwn 1)) mi) ∗
      ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
         ∃ bumper, k1 ↪[γbumper, loc_map_rel]□ bumper ∗
                   ghost_map_auth γm (hist_map_rel k1 bumper) (dfrac_div_2 (DfracOwn 1)) mi) ∗
      ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
         ∃ bumper, k1 ↪[γbumper, loc_map_rel]□ bumper ∗
                   ([∗ map] k2 ↦ v ∈ mi, k2 ↪[γm, hist_map_rel k1 bumper]□ v)).
  Proof.
  Admitted.

  Lemma full_map_alloc OPV OCV m :
    ([∗set] k1 ∈ dom m, ∃ bumper, k1 ↪[γbumper, loc_map_rel]□ bumper) -∗
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, full_map γbumper γ (DfracOwn 1) m ∗
         ([∗ map] k1 ↦ mi ∈ m, full_entry γbumper γ k1 (DfracOwn 1) mi) ∗
         [∗ map] k1 ↦ mi ∈ m, [∗ map] k2 ↦ v ∈ mi, frag_entry γbumper γ k1 k2 v.
  Proof.
    rewrite /full_map /full_entry.
    iIntros "#bumpers #crashed_at_offset #rely_self".
    iMod (full_entry_alloc_big m with "bumpers") as (gnames) "(M1 & M2 & F)".
    iMod (ghost_map_alloc_persistent OPV OCV loc_map_rel gnames with "[#$] [#$]") as (γ) "[H1 #ptsMap]".
    iExists γ.
    rewrite bi.sep_exist_r.
    iExists (gnames).
    iFrame.
    iModIntro.
    iSplit.
    - iApply big_sepM_exist_l.
      iExists gnames.
      iApply (big_sepM2_impl with "M1").
      iIntros "!>" (k ? ???) "(%bumper & #bumper & auth)".
      iExists bumper.
      iFrame "∗#".
      iDestruct (big_sepM_lookup with "ptsMap") as "$"; first done.
    - rewrite /frag_entry.
      iApply big_sepM_forall. iIntros (???).
      iApply big_sepM_forall. iIntros (???).
      iDestruct (big_sepM2_lookup_r with "F") as (γm) "H"; first done.
      iDestruct "H" as (look) "(%bumper & bumper & M)".
      (* iDestruct (big_sepS_elem_of _ _ k with "bumpers") as (bumper) "#bumper". *)
      (* { rewrite elem_of_dom //. } *)
      iExists γm, bumper.
      iDestruct (big_sepM_lookup with "ptsMap") as "$"; first done.
      iDestruct (big_sepM_lookup with "M") as "$"; first done.
      iFrame.
  Qed.

  (* (* Agreement lemmas. *) *)

  Lemma full_map_agree γ dq1 dq2 m1 m2 :
    full_map γbumper γ dq1 m1 -∗ full_map γbumper γ dq2 m2 -∗ ⌜ m1 = m2 ⌝.
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
    iDestruct (big_sepM2_lookup with "map") as (bumper) "[bumper authI]"; [done|done| ].
    iDestruct (big_sepM2_lookup with "map'") as (bumper') "[bumper' authI']"; [done|done| ].
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %->.
    iDestruct (ghost_map_auth_agree with "authI authI'") as "$".
  Qed.

  Lemma full_entry_agree γ k1 dq1 dq2 mi1 mi2 :
    full_entry γbumper γ k1 dq1 mi1 -∗ full_entry γbumper γ k1 dq2 mi2 -∗ ⌜ mi1 = mi2 ⌝.
  Proof.
    iDestruct 1 as (γm bumper) "(pts & bumper & auth)".
    iDestruct 1 as (γm' bumper') "(pts' & bumper' & auth')".
    iDestruct (ghost_map_elem_agree with "pts pts'") as %<-.
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
    iDestruct (ghost_map_auth_agree with "auth auth'") as "$".
  Qed.

  Lemma frag_entry_agree γ k1 k2 v v' :
    frag_entry γbumper γ k1 k2 v -∗ frag_entry γbumper γ k1 k2 v' -∗ ⌜ v = v' ⌝.
  Proof.
    iDestruct 1 as (??) "(pts1 & bumper & pts2)".
    iDestruct 1 as (??) "(pts1' & bumper' & pts2')".
    iDestruct (ghost_map_elem_agree with "pts1 pts1'") as %<-.
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
    iDestruct (ghost_map_elem_agree with "pts2 pts2'") as %<-.
    done.
  Qed.

  Lemma full_entry_frag_entry γ k1 dq mi k2 v :
    full_entry γbumper γ k1 dq mi -∗
    frag_entry γbumper γ k1 k2 v -∗
    ⌜ mi !! k2 = Some v ⌝.
  Proof.
    iDestruct 1 as (γm bumper) "(pts & bumper & auth)". simpl.
    iDestruct 1 as (γm' bumper') "(pts' & bumper' & pts2)".
    iDestruct (ghost_map_elem_agree with "pts pts'") as %<-.
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
    iDestruct (ghost_map_lookup with "auth pts2") as "$".
  Qed.

  (* Insert a new entry at the top level *)
  Lemma full_map_insert γ m k1 bumper mi :
    m !! k1 = None →
    (∃ OPV, rely_self crashed_at_name (crashed_at_pred OPV)) -∗
    k1 ↪[γbumper, loc_map_rel]□ bumper -∗
    full_map γbumper γ (DfracOwn 1) m ==∗
      full_map γbumper γ (DfracOwn 1) (<[k1 := mi]> m) ∗
      full_entry γbumper γ k1 (DfracOwn 1) mi ∗
      [∗ map] k2 ↦ v ∈ mi, frag_entry γbumper γ k1 k2 v.
  Proof.
    iIntros (?) "[%OPV #rely_self] #bumper".
    rewrite /full_map /full_entry.
    iDestruct 1 as (gnames) "[auth map]".
    iDestruct (big_sepM2_dom with "map") as %domEq.
    (* extract [crashed_at_offset] from existing resource *)
    iDestruct (ghost_map_auth_crashed_at_offset with "auth") as (OCV) "#crashed_at_offset".
    (* Allocate the ghost state for the entry. *)
    iMod (ghost_map_alloc_persistent OPV OCV (hist_map_rel k1 bumper) mi with "[#$] [#$]") as (γm) "[authI pts2]".
    iEval (rewrite -Qp.half_half -dfrac_op_own ghost_map_auth_fractional) in "authI".
    replace (DfracOwn (1 / 2)) with (dfrac_div_2 (DfracOwn 1)); last done.
    iDestruct "authI" as "[authI authI']".
    assert (gnames !! k1 = None).
    { apply not_elem_of_dom. rewrite domEq. apply not_elem_of_dom. done. }
    iMod (ghost_map_insert_persist k1 γm with "auth") as "[auth #pts]";
      first done.
    iModIntro. iSplitL "auth authI map".
    { iExists (<[k1 := _]> gnames).
      rewrite big_sepM2_insert; [|done|done].
      iSplitL "auth"; first iFrame.
      iSplitR "map"; last iFrame.
      iExists bumper.
      iFrame "∗#". }
    iSplit.
    { iExists _, _. iFrame "∗#". }
    iApply (big_sepM_impl with "pts2").
    { iIntros "!>" (???) "pts2". iExists _, _. iFrame "∗#". }
  Qed.

  Lemma full_map_full_entry_insert γ m k1 k2 v mi :
    mi !! k2 = None →
    full_map γbumper γ (DfracOwn 1) m -∗
    full_entry γbumper γ k1 (DfracOwn 1) mi ==∗
      let mi' := (<[ k2 := v ]>mi) in
      full_map γbumper γ (DfracOwn 1) (<[ k1 := mi' ]> m) ∗
      full_entry γbumper γ k1 (DfracOwn 1) mi' ∗
      frag_entry γbumper γ k1 k2 v.
  Proof.
    iIntros (?) "FM FE".
    iDestruct (full_map_full_entry with "FM FE") as %mLook.
    iDestruct "FM" as (gnames) "[auth map]".
    iDestruct "FE" as (γm bumper) "(pts & #bumper & authI)".
    iDestruct (ghost_map_lookup with "auth pts") as %look.
    iDestruct (big_sepM2_delete with "map") as "[(%bumper' & bumper' & authI') map]"; [done|done| ].
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
    iCombine "authI authI'" as "authI".
    iEval (rewrite -ghost_map_auth_fractional Qp.half_half) in "authI".
    iMod (ghost_map_insert_persist k2 v with "authI") as "[authI ptsI]";
      first done.
    iEval (rewrite -Qp.half_half -dfrac_op_own ghost_map_auth_fractional) in "authI".
    replace (DfracOwn (1 / 2)) with (dfrac_div_2 (DfracOwn 1)); last done.
    iDestruct "authI" as "[authI authI']".
    iDestruct (big_sepM2_insert_delete with "[map authI']") as "map".
    { iFrame. iExists bumper. iFrame "∗#". }
    rewrite (insert_id gnames); last done.
    iModIntro.
    iSplitL "auth map". { iExists gnames. iFrame. }
    iSplit. { iExists _, _. iFrame. }
    iExists _, _. iFrame.
  Qed.

  Lemma full_entry_lookup_big γ k dq mi mi2 :
    full_entry γbumper γ k dq mi -∗
    ([∗ map] k2 ↦ v ∈ mi2, frag_entry γbumper γ k k2 v) -∗
    ⌜ mi2 ⊆ mi ⌝.
  Proof.
    rewrite /full_entry /frag_entry.
    iDestruct 1 as (γm bumper) "(#topPts & #bumper & M)".
    iIntros "H". simpl.
    iApply (ghost_map_lookup_big (dq := DfracDiscarded) with "M").
    iApply (big_sepM_impl with "H").
    iModIntro. iIntros (???).
    iIntros "(% & % & hi & bumper' & ho)".
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
    iDestruct (ghost_map_elem_agree with "topPts hi") as %->.
    naive_solver.
  Qed.
End lemmas.

Opaque full_map.
Opaque full_entry.
Opaque frag_entry.
