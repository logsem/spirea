From Equations Require Import Equations.
From iris.algebra Require Import gmap_view.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import classes ltac_tactics.
From iris_named_props Require Import named_props.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises.
From self.algebra Require Import view.
From self.base Require Import generational_resources.

From self.lang Require Import lang.

From self.high.resources Require Export gen_ghost_map.

(* the following sections is mostly adapted from the [ghost_map_map.v] file. *)
(* major simplification: I'm removing the second ghost resource about fractions,
 * since I believe it's obsolete after nextgen update. *)
Class ghost_map_mapGpreS (K1 K2: Type) (V: Type) Σ Ω `{Countable K1, Countable K2} `{!crashed_atGpreS Σ Ω} `{!ghost_mapGpreS K1 (V → option V) Σ Ω} := {
    ghost_map_map_outer_GpreS :: ghost_mapGpreS K1 gname Σ Ω;
    ghost_map_map_inner_GpreS :: ghost_mapGpreS K2 V Σ Ω;
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
  
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K1 (V → option V) Σ Ω, !ghost_map_mapGpreS K1 K2 V Σ Ω, Inhabited V}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).
  Implicit Types (dq: dfrac) (γ γm: gname) (bumper: V → option V) (v: V).

  Variable (γbumper: gname).
  (* reminder to myself:
   * [k1] is location, [k2] is timestamp,
   * [γm] is the ghost name for the inner map *)

  (* Ownership over the entire map. *)
  Definition full_map γ dq m : iProp Σ :=
    ∃ (gnames : gmap loc gname),
      ghost_map_auth γ drop_OCV dq gnames ∗
        ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
           ∃ bumper, k1 ↪[γbumper, drop_OCV]□ bumper ∗
                     ghost_map_auth γm (drop_above_bump k1 bumper) (dfrac_div_2 dq) mi).

  (* Ownership over the entire history for a single key. *)
  Definition full_entry γ k1 dq mi : iProp Σ :=
    ∃ γm bumper, k1 ↪[γ, drop_OCV]□ γm ∗
                 k1 ↪[γbumper, drop_OCV]□ bumper ∗
                 ghost_map_auth γm (drop_above_bump k1 bumper) (dfrac_div_2 dq) mi.

  Definition frag_entry γ k1 k2 v : iProp Σ :=
    ∃ γm bumper, k1 ↪[γ, drop_OCV]□ γm ∗
                    k1 ↪[γbumper, drop_OCV]□ bumper ∗
                    k2 ↪[γm, drop_above_bump k1 bumper]□ v.

  (** The last generation map assertions *)
  (* Ownership over the entire map. *)
  Definition lastgen_full_map γ dq m : iProp Σ :=
    ∃ (gnames : gmap loc gname),
      lastgen_ghost_map_auth γ dq gnames ∗
        ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
           lastgen_ghost_map_auth γm (dfrac_div_2 dq) mi).

  (* Ownership over the entire history for a single key. *)
  Definition lastgen_full_entry γ (k1: K1) dq mi : iProp Σ :=
    ∃ γm, lastgen_ghost_map_elem γ k1 DfracDiscarded γm ∗
          lastgen_ghost_map_auth γm (dfrac_div_2 dq) mi.
  
  Definition lastgen_frag_entry γ (k1: K1) (k2: K2) v : iProp Σ :=
    ∃ γm, lastgen_ghost_map_elem γ k1 DfracDiscarded γm ∗
          lastgen_ghost_map_elem γm k2 DfracDiscarded v.
End definitions.

(** We do not need all the lemmas for lastgen assertions
 ** We are mostly interested in lookup and persist lemmas. *)
Section lastgen_lemmas.
  Notation K1 := loc.
  Notation K2 := nat.  
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K1 (V → option V) Σ Ω, !ghost_map_mapGpreS K1 K2 V Σ Ω, Inhabited V}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).
  Implicit Types (dq: dfrac) (γ γm: gname) (bumper: V → option V) (v: V).
Lemma lastgen_full_map_persist {γ} q m :
    lastgen_full_map γ (DfracOwn q) m ==∗ lastgen_full_map γ DfracDiscarded m.
  Proof.
    iDestruct 1 as (?) "[auth map]".
    iExists _.
    iMod (lastgen_ghost_map_auth_persist with "auth") as "$".
    iApply big_sepM2_bupd.
    iApply (big_sepM2_impl with "map").
    iIntros "!>" (?????) "authI".
    iMod (lastgen_ghost_map_auth_persist with "authI") as "$".
    done.
  Qed.

  Lemma lastgen_full_map_frag_entry γ (k1: K1) (k2: K2) dq1 m v :
    lastgen_full_map γ dq1 m -∗
    lastgen_frag_entry γ k1 k2 v -∗
    ∃ mi, ⌜ m !! k1 = Some mi ⌝ ∗ ⌜ mi !! k2 = Some v ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as (γm) "[#ptsγp #ptsv]".
    iDestruct (lastgen_ghost_map_lookup with "auth ptsγp") as %look.
    iDestruct (big_sepM2_lookup_l with "map") as (mi mLook) "authI"; first done.
    iExists mi.
    iDestruct (lastgen_ghost_map_lookup with "authI ptsv") as %?.
    done.
  Qed.

  Lemma lastgen_full_map_full_entry γ k1 dq1 dq2 m mi :
    lastgen_full_map γ dq1 m -∗
    lastgen_full_entry γ k1 dq2 mi -∗
    ⌜ m !! k1 = Some mi ⌝.
  Proof.
    iDestruct 1 as (gnames) "(auth & map)".
    iDestruct 1 as (γm) "[pts authI]".
    iDestruct (lastgen_ghost_map_lookup with "auth pts") as %look.
    iDestruct (big_sepM2_lookup_l with "map") as (mi' mLook) "authI'"; first done.
    iDestruct (lastgen_ghost_map_auth_agree with "authI authI'") as %->.
    done.
  Qed.

  Lemma lastgen_full_entry_frag_entry γ k1 dq mi k2 v :
    lastgen_full_entry γ k1 dq mi -∗
    lastgen_frag_entry γ k1 k2 v -∗
    ⌜ mi !! k2 = Some v ⌝.
  Proof.
    iDestruct 1 as (γm) "(pts & auth)". simpl.
    iDestruct 1 as (γm') "(pts' & pts2)".
    iDestruct (lastgen_ghost_map_elem_agree with "pts pts'") as %<-.
    iDestruct (lastgen_ghost_map_lookup with "auth pts2") as "$".
  Qed.
  
  Lemma lastgen_frag_entry_agree γ k1 k2 v v' :
    lastgen_frag_entry γ k1 k2 v -∗ lastgen_frag_entry γ k1 k2 v' -∗ ⌜ v = v' ⌝.
  Proof.
    iDestruct 1 as (?) "[pts1 pts2]".
    iDestruct 1 as (?) "[pts1' pts2']".
    iDestruct (lastgen_ghost_map_elem_agree with "pts1 pts1'") as %<-.
    iDestruct (lastgen_ghost_map_elem_agree with "pts2 pts2'") as %<-.
    done.
  Qed.
End lastgen_lemmas.

Section lemmas.
  Notation K1 := loc.
  Notation K2 := nat.
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K1 (V → option V) Σ Ω, !ghost_map_mapGpreS K1 K2 V Σ Ω, Inhabited V}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).
  Implicit Types (dq: dfrac) (γ γm: gname) (bumper: V → option V) (v: V).
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
    iDestruct (ghost_map_lookup with "authI ptsv") as %?.
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
  Local Lemma full_entry_alloc_big {OCV OPV} m :
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) -∗
    ([∗set] k1 ∈ dom m, ∃ bumper, k1 ↪[γbumper, drop_OCV]□ bumper) ==∗
    ∃ gnames,
      ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
         ∃ bumper, k1 ↪[γbumper, drop_OCV]□ bumper ∗
                   ghost_map_auth γm (drop_above_bump k1 bumper) (dfrac_div_2 (DfracOwn 1)) mi) ∗
      ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
         ∃ bumper, k1 ↪[γbumper, drop_OCV]□ bumper ∗
                   ghost_map_auth γm (drop_above_bump k1 bumper) (dfrac_div_2 (DfracOwn 1)) mi) ∗
      ([∗ map] k1 ↦ γm;mi ∈ gnames;m,
         ∃ bumper, k1 ↪[γbumper, drop_OCV]□ bumper ∗
                   ([∗ map] k2 ↦ v ∈ mi, k2 ↪[γm, drop_above_bump k1 bumper]□ v)).
  Proof.
    setoid_rewrite <- big_sepM2_sep. setoid_rewrite <- big_sepM2_sep.
    induction m as [|k1 mi m ? IH] using map_ind.
    - naive_solver.
    - iIntros "#crashed_at #crashed_rely bumpers".
      assert (k1 ∉ dom m) by by apply not_elem_of_dom.
      rewrite dom_insert_L big_sepS_insert //.
      iDestruct "bumpers" as "#[[%bumper bumper] bumpers]".
      iMod (IH with "crashed_at crashed_rely bumpers") as (gnames) "M".
      iDestruct (big_sepM2_dom with "M") as %domEq.
      iMod (ghost_map_alloc_persistent OPV OCV mi with "crashed_at crashed_rely") as (γ1) "[auth discard]".
      iExists (<[ k1 := γ1 ]> gnames).
      iModIntro.
      rewrite big_sepM2_insert; try done.
      2: { apply not_elem_of_dom. rewrite domEq. apply not_elem_of_dom. done. }
      iFrame.
      
      iEval (rewrite -Qp.half_half ghost_map_auth_fractional) in "auth".
      iDestruct "auth" as "[auth1 auth2]".
      iSplitL "auth1".
      { iExists bumper. iFrame "∗#". }
      iSplitL "auth2".
      { iExists bumper. iFrame "∗#". }
      iFrame "∗#".
  Qed.
  
  Lemma full_map_alloc OPV OCV m :
    ([∗set] k1 ∈ dom m, ∃ bumper, k1 ↪[γbumper, drop_OCV]□ bumper) -∗
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, full_map γbumper γ (DfracOwn 1) m ∗
         ([∗ map] k1 ↦ mi ∈ m, full_entry γbumper γ k1 (DfracOwn 1) mi) ∗
         [∗ map] k1 ↦ mi ∈ m, [∗ map] k2 ↦ v ∈ mi, frag_entry γbumper γ k1 k2 v.
  Proof.
    rewrite /full_map /full_entry.
    iIntros "#bumpers #crashed_at_offset #rely_self".
    iMod (full_entry_alloc_big m with "[#$] [#$] bumpers") as (gnames) "(M1 & M2 & F)".
    iMod (ghost_map_alloc_persistent OPV OCV gnames with "[#$] [#$]") as (γ) "[H1 #ptsMap]".
    iExists γ.
    rewrite bi.sep_exist_r.
    iFrame.
    iModIntro.
    iSplit.
    - iApply big_sepM_exist_l.
      iExists gnames.
      iApply (big_sepM2_impl with "M1").
      iIntros "!>" (k ? ???) "(%bumper & #bumper & auth)".
      iExists bumper.
      iFrame "∗#".
      iDestruct (big_sepM_lookup with "ptsMap") as "[$ [$ _]]"; first done.
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
    rewrite map_eq_dom; last rewrite -domEq1 -domEq2 //.
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
    k1 ↪[γbumper, drop_OCV]□ bumper -∗
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
    iMod (ghost_map_alloc_persistent OPV OCV mi with "[#$] [#$]") as (γm) "[authI pts2]".
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
      iFrame "∗#". iDestruct "bumper" as "[$ [$ _]]". }
    iSplit.
    { iExists _, _. iFrame "∗#". iDestruct "bumper" as "[$ [$ _]]". }
    iApply (big_sepM_impl with "pts2").
    { iIntros "!>" (???) "pts2". iExists _, _. iFrame "∗#". iDestruct "bumper" as "[$ [$ _]]". }
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
    iDestruct (big_sepM2_insert_delete _ gnames with "[map authI']") as "map".
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
    iApply (ghost_map_lookup_big with "M").
    iApply (big_sepM_impl with "H").
    iModIntro. iIntros (???).
    iIntros "(% & % & hi & bumper' & ho)".
    iDestruct (ghost_map_elem_agree with "bumper bumper'") as %<-.
    iDestruct (ghost_map_elem_agree with "topPts hi") as %->.
    naive_solver.
  Qed.
End lemmas.

Section Nextgen.
  Notation K1 := loc.
  Notation K2 := nat.
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K1 (V → option V) Σ Ω, !ghost_map_mapGpreS K1 K2 V Σ Ω, Inhabited V}.
  Implicit Types (m : gmap K1 (gmap K2 V)).
  Implicit Types (mi : gmap K2 V).
  Implicit Types (dq: dfrac) (γ γm: gname) (bumper: V → option V) (v: V).
  Implicit Types (OCV: view) (abs_hists: gmap K1 (gmap K2 V)) (abs_hist: gmap K2 V) (ℓ: K1) (t: K2).

  Context {bumpers: gmap K1 (V → option V)} {γbumper γ: gname}.
  (* It's difficult to enforce [ℓ ∈ dom bumpers], we take the easy path. *)
  Definition per_loc_trans OCV ℓ abs_hist: option (gmap K2 V) :=
    match bumpers !! ℓ with
    | Some bump => Some (drop_bump_map ℓ bump OCV abs_hist)
    | None => None
    end.
  
  (* we combine the [drop_OCV] and [drop_above_bump] transformers. *)
  Definition abs_hist_trans OCV (abs_hists: gmap K1 (gmap K2 V)): gmap K1 (gmap K2 V) :=
    restrict (dom OCV) $ map_imap (per_loc_trans OCV) abs_hists.

  Lemma dom_abs_hist_trans OCV abs_hists:
    dom abs_hists ⊆ dom bumpers →
    dom (abs_hist_trans OCV abs_hists) = dom OCV ∩ dom abs_hists.
  Proof.
    intros.
    rewrite /abs_hist_trans restrict_dom_L.
    f_equal.
    apply dom_imap_L.
    intros ℓ. split.
    - rewrite elem_of_dom => [[abs_hist absHistsLook]].
      eexists.
      split; first done.
      rewrite /per_loc_trans.
      destruct (bumpers !! ℓ) eqn:Heq; first done.
      rewrite -not_elem_of_dom in Heq.
      apply elem_of_dom_2 in absHistsLook.
      set_solver.
    - intros (abs_hist & look & _).
      apply elem_of_dom.
      by eexists.
  Qed.
  
  Lemma restrict_abs_hist_trans (X: gset loc) OCV abs_hists:
    restrict X (abs_hist_trans OCV abs_hists) =
    abs_hist_trans OCV (restrict X abs_hists).
  Proof.
    apply map_eq.
    intros ℓ.
    rewrite /abs_hist_trans.
    destruct (decide (ℓ ∈ X)); destruct (decide (ℓ ∈ dom OCV)).
    - rewrite ?restrict_lookup_elem_of // ?map_lookup_imap /=.
      rewrite restrict_lookup_elem_of //.
    - rewrite (restrict_lookup_elem_of _ X) //.
      rewrite !(restrict_lookup_not_elem_of _ (dom OCV)) //.
    - rewrite (restrict_lookup_not_elem_of _ X) //.
      rewrite ?(restrict_lookup_elem_of _ (dom OCV)) //.
      rewrite map_lookup_imap.
      rewrite (restrict_lookup_not_elem_of _ X) //.
    - rewrite ?restrict_lookup_not_elem_of //.
  Qed.
  
  (* Since we need to have some notion of global bumpers, it's difficult to make it
   * work with the [IntoNextgen] typeclass. *)
  Lemma full_map_nextgen dq1 dq2 abs_hists:
    full_map γbumper γ dq1 abs_hists -∗
    ghost_map_auth γbumper drop_OCV dq2 bumpers -∗
    ghost_map_auth γbumper drop_OCV dq2 bumpers ∗
    ⚡==>
      lastgen_full_map γ dq1 abs_hists ∗
      ∀ OCV, crashed_at_offset OCV -∗
             full_map γbumper γ dq1 (abs_hist_trans OCV abs_hists).
  Proof.
    iIntros "(%gnames & gnames_auth & abs_hists_auth) bumpers".
    iDestruct (big_sepM2_dom with "abs_hists_auth") as %domEq.
    iAssert ⌜ map_Forall (λ ℓ _, is_Some (bumpers !! ℓ)) gnames ⌝%I as %domBumpers.
    { rewrite -big_sepM_pure.
      iPoseProof (bi.exist_intro abs_hists with "abs_hists_auth") as "map".
      rewrite -big_sepM_exist_r.
      iDestruct (big_sepM_impl_dom_subseteq_with_resource with "bumpers map []") as "(? & $ & ?)".
      { done. }
      iIntros "!>" (ℓ γm γm' ??) "allBumpers (% & %bumper & #knowBumper & _)".
      simplify_map_eq.
      iDestruct (ghost_map_lookup with "allBumpers [knowBumper]") as %bumperLook.
      { iApply "knowBumper". }
      iFrame. iPureIntro.
      by eexists. }
    iPoseProof (big_sepM2_impl_dom_subseteq_with_resource _
                  (λ ℓ gname abs_hist,
                     ⚡==> lastgen_ghost_map_auth (V := leibnizO V) gname (dfrac_div_2 dq1) abs_hist ∗
                         ∃ bump, 
                         ⌜ bumpers !! ℓ = Some bump ⌝ ∗
                         ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
                                ℓ ↪[γbumper,drop_OCV]□ bump ∗
                                ghost_map_auth (V := leibnizO V) gname (drop_above_bump ℓ bump) (dfrac_div_2 dq1) (drop_bump_map ℓ bump OCV abs_hist))%I
                  gnames abs_hists gnames abs_hists with "bumpers abs_hists_auth []")
      as "[$ abs_hists_auth]"; [ done | done | | ].
    - iIntros "!>" (ℓ gname abs_hist gname' abs_hist' ????) "allBumpers entry".
      simplify_map_eq.
      iDestruct "entry" as "(%bump & #knowBumper & fullEntry)".
      iDestruct (ghost_map_lookup with "allBumpers knowBumper") as %bumperLook.
      iFrame "allBumpers".
      iModIntro.
      iDestruct "fullEntry" as "[$ fullEntry]".
      iExists bump. iSplit; first done.
      iIntros (?) "#offset domOCV".
      iDestruct "knowBumper" as "[_ knowBumper]".
      iSpecialize ("knowBumper" with "offset domOCV").
      iSpecialize ("fullEntry" with "offset").
      iFrame.
    - iDestruct (big_sepM2_alt with "abs_hists_auth") as (_) "abs_hists_auth".
      rewrite nextgen_big_sepM.
      iModIntro.
      iDestruct "gnames_auth" as "[lastgen_gnames_auth gnames_auth]".
      iDestruct (big_sepM_sep with "abs_hists_auth") as "[lastgen_abs_hists_auth abs_hists_auth]".
      iSplitL "lastgen_gnames_auth lastgen_abs_hists_auth".
      { iExists gnames. rewrite big_sepM2_alt. by iFrame. }
      iIntros (OCV) "#offset".
      iSpecialize ("gnames_auth" with "offset").
      iExists (restrict (dom OCV) gnames).
      iFrame.
      rewrite big_sepM2_alt.
      iSplit; first iPureIntro.
      + rewrite /abs_hist_trans /per_loc_trans.
        rewrite ?restrict_dom_L.
        f_equal.
        rewrite -dom_eq_alt_L.
        intros ℓ.
        rewrite map_lookup_imap.
        destruct (gnames !! ℓ) eqn:Heq.
        * pose proof (map_Forall_lookup_1 _ _ ℓ _ domBumpers Heq) as [bumper bumperLook].
          assert (is_Some (abs_hists !! ℓ)) as [? ->].
          { rewrite -elem_of_dom -domEq elem_of_dom. by eexists. }
          simpl.
          rewrite bumperLook /=.
          split; intros; by eexists.
        * assert (abs_hists !! ℓ = None) as ->.
          { rewrite -not_elem_of_dom -domEq not_elem_of_dom //. }
          simpl.
          split; intros []; congruence.
      + iDestruct (big_sepM_impl_dom_subseteq _ _ _
                     (map_zip (restrict (dom OCV) gnames) (abs_hist_trans OCV abs_hists))
                    with "abs_hists_auth []") as "[$ _]".
        { etrans; first apply dom_map_zip_with_fst.
          rewrite dom_map_zip_with.
          rewrite restrict_dom_L domEq.
          set_solver. }
        iIntros "!>" (ℓ [γm abs_hist] [γm' abs_hist'] [? absHistLook]%map_lookup_zip_Some [gnameLook' absHistLook']%map_lookup_zip_Some).
        simpl in *.
        iIntros "(%bumper & %bumperLook & entry)".
        assert (ℓ ∈ dom OCV).
        { apply elem_of_dom_2 in gnameLook'.
          rewrite restrict_dom_L in gnameLook'.
          set_solver. }
        iDestruct ("entry" with "offset [%]") as "[knowBumper entry]"; first done.
        rewrite /abs_hist_trans restrict_lookup_elem_of // map_lookup_imap absHistLook /= in absHistLook'.
        rewrite /per_loc_trans bumperLook in absHistLook'.
        rewrite restrict_lookup_elem_of // in gnameLook'.
        simplify_map_eq.
        iExists bumper.
        iFrame.
  Qed.
  
  Lemma full_entry_nextgen ℓ dq1 dq2 abs_hist:
    full_entry γbumper γ ℓ dq1 abs_hist -∗
    ghost_map_auth γbumper drop_OCV dq2 bumpers -∗
    ghost_map_auth γbumper drop_OCV dq2 bumpers ∗
    ⚡==> ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
                 match per_loc_trans OCV ℓ abs_hist with
                 | Some abs_hist' => full_entry γbumper γ ℓ dq1 abs_hist'
                 | None => emp
                 end.
  Proof.
    iIntros "(%γm & %bump & #knowGname & #knowBumper & fullEntry) allBumpers".
    iDestruct (ghost_map_lookup with "allBumpers knowBumper") as %bumperLook.
    rewrite /per_loc_trans.
    rewrite bumperLook.
    iFrame "allBumpers".
    iModIntro.
    iIntros (?) "#offset %domOCV".
    iDestruct "knowGname" as "[_ knowGname]".
    iSpecialize ("knowGname" with "offset [//]").
    iDestruct "knowBumper" as "[_ knowBumper]".
    iSpecialize ("knowBumper" with "offset [//]").
    iDestruct "fullEntry" as "[_ fullEntry]".
    iSpecialize ("fullEntry" with "offset").
    rewrite /full_entry.
    iExists _, _. iFrame "∗#".
  Qed.

  Lemma full_entry_local_nextgen ℓ dq1 dq2 bumper abs_hist:
    full_entry γbumper γ ℓ dq1 abs_hist -∗
    ghost_map_elem γbumper drop_OCV ℓ dq2 bumper -∗
    ⚡==> lastgen_full_entry γ ℓ dq1 abs_hist ∗
    ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
           full_entry γbumper γ ℓ dq1 (drop_bump_map ℓ bumper OCV abs_hist).
  Proof.
    iIntros "(%γm & %bump & #knowGname & #knowBumper & fullEntry) knowBumper'".
    iDestruct (ghost_map_elem_agree with "knowBumper knowBumper'") as %<-.
    rewrite /per_loc_trans.
    iModIntro.
    iDestruct "knowGname" as "[$ knowGname]".
    iDestruct "fullEntry" as "[$ fullEntry]".
    iIntros (?) "#offset %domOCV".
    iSpecialize ("knowGname" with "offset [//]").
    iDestruct "knowBumper" as "[_ knowBumper]".
    iSpecialize ("knowBumper" with "offset [//]").
    iSpecialize ("fullEntry" with "offset").
    rewrite /full_entry.
    iExists _, _. iFrame "∗#".
  Qed.
  
  Lemma all_loc_full_entry_nextgen abs_hists dq1 dq2:
    dom abs_hists ⊆ dom bumpers →
    ([∗ map] ℓ ↦ abs_hist ∈ abs_hists, full_entry γbumper γ ℓ dq1 abs_hist) -∗
    ghost_map_auth γbumper drop_OCV dq2 bumpers -∗
    ghost_map_auth γbumper drop_OCV dq2 bumpers ∗
    ⚡==> ∀ OCV, crashed_at_offset OCV -∗
                 ([∗ map] ℓ ↦ abs_hist ∈ (abs_hist_trans OCV abs_hists), full_entry γbumper γ ℓ dq1 abs_hist).
  Proof.
    iIntros (incl) "all_entries allBumpers".
    iDestruct (big_sepM_impl_dom_subseteq_with_resource _ _ _ abs_hists abs_hists with "allBumpers all_entries []") as "($ & all_entries & _)".
    { done. }
    - iIntros "!>" (ℓ abs_hist abs_hist' ? ?) "allBumpers entries".
      simplify_map_eq.
      assert (is_Some (bumpers !! ℓ)) as [bumper bumperLook].
      { rewrite -elem_of_dom.
        pose proof (elem_of_subseteq (dom abs_hists) (dom bumpers)) as [HelemOf _].
        apply HelemOf; first done.
        apply elem_of_dom. by eexists. }
      iDestruct (full_entry_nextgen with "entries allBumpers") as "[$ entry]".
      iAccu.
    - simpl.
      rewrite nextgen_big_sepM.
      iModIntro.
      iIntros (?) "#offset".
      iDestruct (big_sepM_impl_dom_subseteq _ _ _ (abs_hist_trans OCV abs_hists) with "all_entries []") as "[$ _]".
      { rewrite /abs_hist_trans restrict_dom_L.
        etrans; first apply intersection_subseteq_r.
        etrans; first apply dom_imap_subseteq.
        done. }
      rewrite /abs_hist_trans.
      iIntros "!>" (ℓ abs_hist abs_hist' absHistsLook absHistsLook') "entries".
      destruct (decide (ℓ ∈ dom OCV)); last rewrite restrict_lookup_not_elem_of // in absHistsLook'.
      iSpecialize ("entries" with "offset [//]").
      rewrite /abs_hist_trans restrict_lookup_elem_of // map_lookup_imap absHistsLook /= in absHistsLook'.
      by rewrite absHistsLook'.
  Qed.

  Lemma frag_entry_nextgen ℓ t v bumper dq:
    bumpers !! ℓ = Some bumper →
    frag_entry γbumper γ ℓ t v -∗
    ghost_map_auth γbumper drop_OCV dq bumpers -∗
    ghost_map_auth γbumper drop_OCV dq bumpers ∗
    ⚡==> lastgen_frag_entry γ ℓ t v ∗
          ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
                 match drop_above_bump ℓ bumper OCV t v with
                 | Some v' => frag_entry γbumper γ ℓ t v'
                 | None => emp
                 end.
  Proof.
    iIntros (bumperLook) "(%γm & %bumper' & #knowGname & #knowBumper & entry) allBumpers".
    iDestruct (ghost_map_lookup with "allBumpers knowBumper") as %bumperLook'.
    iFrame "allBumpers".
    simplify_map_eq.
    iModIntro.
    iDestruct "knowGname" as "[l1 knowGname]".
    iDestruct "entry" as "[l2 entry]".
    iSplitL "l1 l2".
    { iExists _. iFrame "∗#". }
    iIntros (?) "#offset %domOCV".
    iSpecialize ("knowGname" with "offset [//]").
    iDestruct "knowBumper" as "[_ knowBumper]".
    iSpecialize ("knowBumper" with "offset [//]").
    iSpecialize ("entry" with "offset").
    destruct (drop_above_bump _ _ _ _); last done.
    iExists _, _. iFrame "∗#".
  Qed.

  Lemma per_loc_frag_entry_nextgen ℓ abs_hist bumper dq:
    bumpers !! ℓ = Some bumper →
    ([∗ map] t ↦ encσ ∈ abs_hist, frag_entry γbumper γ ℓ t encσ) -∗
    ghost_map_auth γbumper drop_OCV dq bumpers -∗
    ghost_map_auth γbumper drop_OCV dq bumpers ∗
    ⚡==> ([∗ map] t ↦ encσ ∈ abs_hist, lastgen_frag_entry γ ℓ t encσ) ∗
          ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
                 match per_loc_trans OCV ℓ abs_hist with
                 | Some abs_hist' => ([∗ map] t ↦ encσ ∈ abs_hist', frag_entry γbumper γ ℓ t encσ)
                 | None => emp
                 end.
  Proof.
    iIntros (bumperLook) "entries allBumpers".
    iDestruct (big_sepM_impl_dom_subseteq_with_resource _ _ _ abs_hist abs_hist with "allBumpers entries []") as "($ & entries & _)".
    { done. }
    - iIntros "!>" (t v v' ? ?) "allBumpers entry".
      simplify_map_eq.
      iDestruct (frag_entry_nextgen with "entry allBumpers") as "[$ entry]"; first done.
      iAccu.
    - simpl.
      rewrite nextgen_big_sepM.
      iModIntro.
      iDestruct (big_sepM_sep with "entries") as "[$ entries]".
      iIntros (?) "#offset %domOCV".
      rewrite /per_loc_trans bumperLook.
      iDestruct (big_sepM_impl_dom_subseteq _ _ _ (drop_bump_map ℓ bumper OCV abs_hist) with "entries []") as "[$ _]".
      { rewrite /drop_bump_map.
        etrans; first apply dom_imap_subseteq.
        done. }
      rewrite /drop_bump_map /drop_above_bump.
      iIntros "!>" (t v v' absHistLook absHistLook') "entry".
      iSpecialize ("entry" with "offset [//]").
      rewrite map_lookup_imap absHistLook /= in absHistLook'.
      destruct (decide _); last done.
      by rewrite absHistLook'.
  Qed.
  
  Lemma all_loc_frag_entry_nextgen abs_hists dq:
    dom abs_hists = dom bumpers →
    ([∗ map] ℓ ↦ abs_hist ∈ abs_hists,
       [∗ map] t ↦ encσ ∈ abs_hist, frag_entry γbumper γ ℓ t encσ) -∗
    ghost_map_auth γbumper drop_OCV dq bumpers -∗
    ghost_map_auth γbumper drop_OCV dq bumpers ∗
    ⚡==> ([∗ map] ℓ ↦ abs_hist ∈ abs_hists,
             [∗ map] t ↦ encσ ∈ abs_hist, lastgen_frag_entry γ ℓ t encσ) ∗
          ∀ OCV, crashed_at_offset OCV -∗
                 ([∗ map] ℓ ↦ abs_hist ∈ abs_hist_trans OCV abs_hists,
                    [∗ map] t ↦ encσ ∈ abs_hist, frag_entry γbumper γ ℓ t encσ).
  Proof.
    iIntros (domEq) "all_entries allBumpers".
    iDestruct (big_sepM_impl_dom_subseteq_with_resource _ _ _ abs_hists abs_hists with "allBumpers all_entries []") as "($ & all_entries & _)".
    { done. }
    - iIntros "!>" (ℓ abs_hist abs_hist' ? ?) "allBumpers entries".
      simplify_map_eq.
      assert (is_Some (bumpers !! ℓ)) as [bumper bumperLook].
      { rewrite -elem_of_dom -domEq elem_of_dom. by eexists. }
      iDestruct (per_loc_frag_entry_nextgen with "entries allBumpers") as "[$ entry]"; first done.
      iAccu.
    - simpl.
      rewrite nextgen_big_sepM.
      iModIntro.
      iDestruct (big_sepM_sep with "all_entries") as "[$ all_entries]".
      iIntros (?) "#offset".
      iDestruct (big_sepM_impl_dom_subseteq _ _ _ (abs_hist_trans OCV abs_hists) with "all_entries []") as "[$ _]".
      { rewrite /abs_hist_trans restrict_dom_L.
        etrans; first apply intersection_subseteq_r.
        etrans; first apply dom_imap_subseteq.
        done. }
      rewrite /abs_hist_trans.
      iIntros "!>" (ℓ abs_hist abs_hist' absHistsLook absHistsLook') "entries".
      destruct (decide (ℓ ∈ dom OCV)); last rewrite restrict_lookup_not_elem_of // in absHistsLook'.
      iSpecialize ("entries" with "offset [//]").
      rewrite /abs_hist_trans restrict_lookup_elem_of // map_lookup_imap absHistsLook /= in absHistsLook'.
      by rewrite absHistsLook'.
  Qed.
  
  (* This version uses per-location bumper knowledge *)
  Lemma frag_entry_local_nextgen ℓ t v:
    frag_entry γbumper γ ℓ t v -∗
    ⚡==>
      lastgen_frag_entry γ ℓ t v ∗
      ∀ OCV bumper, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
           ℓ ↪[γbumper, drop_OCV]□ bumper -∗
           match drop_above_bump ℓ bumper OCV t v with
           | Some v' => frag_entry γbumper γ ℓ t v'
           | None => emp
           end.
  Proof.
    iIntros "(%γm & %bumper' & #knowGname & #knowBumper & entry)".
    iModIntro.
    iDestruct "knowGname" as "[l1 knowGname]".
    iDestruct "entry" as "[l2 entry]".
    iSplitL "l1 l2".
    { iExists _. by iFrame. }
    iIntros (??) "#offset %domOCV knowBumper'".
    iDestruct "knowBumper" as "[_ knowBumper]".
    iSpecialize ("knowBumper" with "offset [//]").
    iDestruct (ghost_map_elem_agree with "knowBumper knowBumper'") as %->.
    iSpecialize ("knowGname" with "offset [//]").
    iSpecialize ("entry" with "offset").
    destruct (drop_above_bump _ _ _ _); last done.
    iExists _, _. iFrame "∗#".
  Qed.

  #[global] Instance frag_entry_local_into_nextgen ℓ t v:
    IntoNextgen
      (frag_entry γbumper γ ℓ t v)
      (lastgen_frag_entry γ ℓ t v ∗
       ∀ OCV bumper, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗
           ℓ ↪[γbumper, drop_OCV]□ bumper -∗
           match drop_above_bump ℓ bumper OCV t v with
           | Some v' => frag_entry γbumper γ ℓ t v'
           | None => emp
           end).
  Proof.
    rewrite /IntoNextgen.
    iApply frag_entry_local_nextgen.
  Qed.
End Nextgen.

Arguments abs_hist_trans {_ _} _ _ _.

Opaque full_map.
Opaque full_entry.
Opaque frag_entry.
