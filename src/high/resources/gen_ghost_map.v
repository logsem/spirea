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

(* we first define a version of [ghost_map] that is dependent on
 * the [crashed_at] resource. we do not fix the [t] function for now. *)
Section crashed_at_ghost_map.
  Context {V: Type} `{Countable K}.

  Implicit Type (k: K) (v: V) (OCV: view) (m: gmap K V).

  Definition ghost_mapUR: cmra := gmap_viewUR K (leibnizO V).
  Notation ghost_map_inG Σ Ω := (genInDepsG Σ Ω (ghost_mapUR) [#crashed_atR]).

  Definition ghost_map_relyT := rel_over [#crashed_atR] ghost_mapUR.

  Implicit Types (R: ghost_map_relyT).

  Context `{!nvmBaseG Σ Ω, !ghost_map_inG Σ Ω}.
  Definition ghost_map_auth γ R dq m: iProp Σ :=
    ∃ OCV,
      "own_auth" ∷ gen_own γ (gmap_view_auth (V := leibnizO V) dq m) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      "#rely" ∷ rely γ [#crashed_at_name] R True_pred.

  Definition ghost_map_elem γ R k dq v: iProp Σ :=
    ∃ OCV,
      "own_elem" ∷ gen_own γ (gmap_view_frag (V:= leibnizO V) k dq v) ∗
      "#crashed" ∷ crashed_at_offset OCV ∗
      "#rely" ∷ rely γ [#crashed_at_name] R True_pred.
End crashed_at_ghost_map.

Notation genC_ghost_map_inG K V Σ Ω := (genInDepsG Σ Ω (ghost_mapUR (K := K) (V := V)) [#crashed_atR]).
Notation "k ↪[ γ , R ] dq v" := (ghost_map_elem γ R k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ , R ] dq  v") : bi_scope.

(* current generation ghost map lemmas *)
Section cgen_ghost_map_lemmas.
  Context `{Countable K} {V: Type}.
  Context `{!nvmBaseG Σ Ω, !genC_ghost_map_inG K V Σ Ω}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).
  (* select lemmas that is being used in Spirea repo. *)

  Global Instance ghost_map_elem_timeless k γ R dq v : Timeless (k ↪[γ, R]{dq} v).
  Proof. apply _. Qed.
  Global Instance ghost_map_elem_persistent k γ R v : Persistent (k ↪[γ, R]□ v).
  Proof. apply _. Qed.
  Global Instance ghost_map_elem_fractional k R γ v :
    Fractional (λ q, k ↪[γ, R]{#q} v)%I.
  Proof.
    intros p q.
    apply bi.equiv_entails_2.
    - iNamed 1.
      iDestruct "own_elem" as "[p q]".
      iSplitL "p".
      { iExists _. iFrame "∗#". }
      iExists _.
      iFrame "∗#".
    - iIntros "[(% & own & ? & ?) (% & own' & ? & ?)]".
      iExists _.
      iFrame.
      iDestruct (gen_own_op_2 with "own own'") as "own".
      rewrite -gmap_view_frag_op dfrac_op_own.
      done.
  Qed.

  Global Instance ghost_map_elem_as_fractional k γ R q v :
    AsFractional (k ↪[γ, R]{#q} v) (λ q, k ↪[γ, R]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance ghost_map_auth_fractional γ R m : Fractional (λ q, ghost_map_auth γ R (DfracOwn q) m)%I.
  Proof.
    intros p q.
    apply bi.equiv_entails_2.
    - iNamed 1.
      iDestruct "own_auth" as "[p q]".
      iSplitL "p".
      { iExists _. iFrame "∗#". }
      iExists _.
      iFrame "∗#".
    - iIntros "[(% & own & ? & ?) (% & own' & ? & ?)]".
      iExists _.
      iFrame.
      iDestruct (gen_own_op_2 with "own own'") as "own".
      rewrite -gmap_view_auth_dfrac_op dfrac_op_own.
      done.
  Qed.

  Global Instance ghost_map_auth_as_fractional k γ R q m :
    AsFractional (ghost_map_auth γ R (DfracOwn q) m) (λ q, ghost_map_auth γ R (DfracOwn q) m)%I q.
  Proof. split; first done. apply _. Qed.

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist γ R k dq v:
    k ↪[γ, R]{dq} v ==∗ k ↪[γ, R]□ v.
  Proof.
    iNamed 1.
    iMod (gen_own_update with "own_elem") as "?".
    { apply gmap_view_frag_persist. }
    iModIntro.
    iExists OCV.
    naive_solver.
  Qed.

  Lemma ghost_map_insert {γ R m} k v :
    m !! k = None →
    ghost_map_auth γ R (DfracOwn 1) m ==∗ ghost_map_auth γ R (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ, R] v.
  Proof.
    intros Hm.
    iNamed 1.
    iMod (gen_own_update with "own_auth") as "[? ?]".
    { apply:gmap_view_alloc; [ done | done | ].
      apply dfrac_valid_own_1. }
    iModIntro.
    iFrame.
    iSplit.
    { iExists OCV. iFrame "#". }
    iExists OCV.
    iFrame "#".
  Qed.

  Lemma ghost_map_insert_persist {γ R m} k v :
    m !! k = None →
    ghost_map_auth γ R (DfracOwn 1) m ==∗ ghost_map_auth γ R (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ, R]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_lookup {γ R dp m k dq v} :
    ghost_map_auth γ R dp m -∗ k ↪[γ, R]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    iNamed 1. iNamed 1.
    iDestruct (gen_own_valid_2 with "own_auth own_elem") as
      %[?[??]]%gmap_view_both_dfrac_valid_L.
    done.
  Qed.

  Lemma ghost_map_lookup_big {γ R dp dq m} m0 :
    ghost_map_auth γ R dp m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ, R]{dq} v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  (** Make a the authorative element read-only. *)
  Lemma ghost_map_auth_persist γ dq m R:
    ghost_map_auth γ R dq m ==∗ ghost_map_auth γ R DfracDiscarded m.
  Proof.
    iNamed 1.
    iMod (gen_own_update with "own_auth") as "?".
    { apply gmap_view_auth_persist. }
    iModIntro.
    iExists OCV.
    iFrame "∗#".
  Qed.

  Lemma ghost_map_auth_valid_2 γ R dq1 dq2 m1 m2 :
    ghost_map_auth γ R dq1 m1 -∗ ghost_map_auth γ R dq2 m2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ m1 = m2⌝.
  Proof.
    iNamed 1.
    iIntros "(% & own_auth' & _)".
    iDestruct (gen_own_valid_2 with "own_auth own_auth'") as %[??]%gmap_view_auth_dfrac_op_valid_L.
    done.
  Qed.

  Lemma ghost_map_auth_agree γ R dq1 dq2 m1 m2 :
    ghost_map_auth γ R dq1 m1 -∗ ghost_map_auth γ R dq2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  Lemma ghost_map_elem_valid k γ dq v R: k ↪[γ, R]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    iNamed 1.
    iDestruct (gen_own_valid with "own_elem") as %?%gmap_view_frag_valid.
    naive_solver.
  Qed.

  Lemma ghost_map_elem_valid_2 k γ R dq1 dq2 v1 v2 :
    k ↪[γ, R]{dq1} v1 -∗ k ↪[γ, R]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    iNamed 1.
    iIntros "(% & own_elem' & _)".
    iDestruct (gen_own_valid_2 with "own_elem own_elem'") as %[? Hag]%gmap_view_frag_op_valid.
    done.
  Qed.

  Lemma ghost_map_elem_agree k γ R dq1 dq2 v1 v2 :
    k ↪[γ, R]{dq1} v1 -∗ k ↪[γ, R]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.
  (* TODO: allocation lemmas *)

  Lemma ghost_map_alloc LV R OCV m dq :
    ✓ dq →
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred LV) ==∗
    ∃ γ, ghost_map_auth γ R (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, R]{dq} v.
  Proof.
    iIntros (?) "#crashed_at_offset #rely_self".
    iMod (own_gen_alloc
                  (DS := [#crashed_atR])
                  (gmap_view_auth (V:=leibnizO V) (DfracOwn 1) ∅)
                  [#crashed_at_name]
                  [##_] with "[]") as (γ) "[auth tok]";
      first apply gmap_view_auth_valid.
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iAssumption. }
    iExists γ.
    iMod (gen_own_update with "auth") as "[auth frag]".
    { apply: (gmap_view_alloc_big (V:=leibnizO V) _ m dq).
      - apply map_disjoint_empty_r.
      - done. }
    iMod (token_strengthen_promise
            (DS := [#crashed_atR])
            _ [#_] [##_] _ R _ True_pred
           with "[] tok") as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    2: {
      iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely_self". }
    (* TODO: this subgoal requires me to prove that for any transformer picked for
     * [crashed_atR], there exists a transformer for the map that satisfy [R].
     * this can only be proven given specific [R]. I should move this lemma around. *)
    { admit. }
    iDestruct (token_to_rely with "tok") as "#rely".
    iModIntro.
    iSplitL "auth".
    { iExists OCV.
      rewrite (right_id _ (∪)).
      iFrame "∗#". }
    (* TODO: need [gen_own] and [big_op] commute lemma *)
    rewrite /ghost_map_elem.
    replace (gen_own γ ([^ op map] k ↦ v ∈ m, (gmap_view_frag (V:= leibnizO V) k dq v))) with
      ([∗map] k ↦ v ∈ m, gen_own γ (gmap_view_frag (V:= leibnizO V) k dq v))%I; last admit.
    iApply (big_sepM_impl with "frag").
    iIntros "!>" (k v ?) "frag".
    iExists OCV.
    iFrame "∗#".
  Admitted.

  Lemma ghost_map_alloc_persistent LV R OCV m :
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred LV) ==∗
    ∃ γ, ghost_map_auth γ R (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, R]□ v.
  Proof.
    iIntros "#crashed_at_offset #rely_self".
    iMod (ghost_map_alloc LV R OCV m (DfracDiscarded) with "[#$] [#$]") as (γ) "[auth map]";
      first done.
    iExists γ.
    iFrame.
    done.
  Qed.

  (* nextgen lemmas/instances *)

  (* TODO: merge this lemma with the other lemma with the same name in base spirea. *)
  Lemma map_entry_lift_gmap_view_auth dq m map_entry :
    (map_entry_lift_gmap_view map_entry (gmap_view_auth (V := leibnizO V) dq m)) =
    (gmap_view_auth dq (map_imap map_entry m)).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    rewrite agree_map_to_agree. done.
  Qed.
End cgen_ghost_map_lemmas.

(* nextgen lemmas for the location maps *)
Section loc_map_lemmas.
  Context {V: Type}.
  Implicit Type (v: V) (OCV: view) (m: gmap loc V).

  Definition drop_OCV OCV ℓ v :=
    if (decide (ℓ ∈ dom OCV)) then Some v else None.

  Definition loc_map_rel: ghost_map_relyT (K := loc) :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = map_entry_lift_gmap_view (V := leibnizO V) $ drop_OCV OCV.

  Lemma map_imap_drop_OCV_restrict OCV m:
    map_imap (drop_OCV OCV) m = restrict (dom OCV) m.
  Proof.
    apply map_eq => i.
    rewrite /drop_OCV map_lookup_imap /=.
    destruct (decide (i ∈ dom OCV)).
    - rewrite restrict_lookup_elem_of; last done.
      by destruct (m !! i).
    - rewrite restrict_lookup_not_elem_of; last done.
      by destruct (m !! i).
  Qed.

  Lemma elem_of_drop_OCV_gmap_view_frag OCV k dq v :
    k ∈ dom OCV →
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV OCV) (gmap_view_frag (V := leibnizO V) k dq v)) =
    (gmap_view_frag (V:= leibnizO V) k dq v).
  Proof.
    intros.
    unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
    unfold gmap_view_frag, view_frag.
    f_equal.
    rewrite -{1}insert_empty.
    erewrite map_imap_insert_Some;
      first rewrite map_imap_empty insert_empty //.
    rewrite agree_option_map_to_agree /drop_OCV decide_True //.
  Qed.

  Context `{!nvmBaseG Σ Ω, !genC_ghost_map_inG loc V Σ Ω}.

  Instance ghost_map_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ loc_map_rel dq m)
      (∃ OCV,
          ghost_map_auth γ loc_map_rel dq (restrict (dom OCV) m) ∗
          picked_in crashed_at_name (crashed_at_trans OCV)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct ("own_auth") as (t) "[#picked own_auth]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iExists OCV'.
    rewrite map_entry_lift_gmap_view_auth.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at]".
    iPickedInAgree "pickedC pickedC'".
    iFrame "#".
    iExists _.
    rewrite map_imap_drop_OCV_restrict.
    iFrame.
    iExists OCV.
    iApply "crashed_at".
  Qed.

  Instance ghost_map_elem_into_nextgen γ k dq v:
    IntoNextgen
      (ghost_map_elem γ loc_map_rel k dq v)
      (∃ OCV,
          (if (decide (k ∈ dom OCV)) then ghost_map_elem γ loc_map_rel k dq v else emp) ∗
          picked_in crashed_at_name (crashed_at_trans OCV)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "own_elem" as (t) "[#picked elem]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iExists OCV'.
    destruct (decide (k ∈ dom OCV')).
    - rewrite elem_of_drop_OCV_gmap_view_frag; last done.
      iDestruct "crashed" as (??) "[pickedC' #crashed_at]".
      iPickedInAgree "pickedC pickedC'".
      iFrame "#".
      iExists _.
      iFrame.
      iExists OCV.
      iApply "crashed_at".
    - iFrame "#".
  Qed.
End loc_map_lemmas.

(* the other ghost map we use are the per location history maps,
 * the transformer is roughly [(drop_above k, bumper v)] *)
Section hist_map_lemmas.
  Notation K := nat.
  (* we are fixed for one location and assumes its bumper. *)
  Context {V: Type}.
  Variable (ℓ: loc) (bumper: V → option V).
  Implicit Type (v: V) (OCV: view) (hist: gmap K V).
  (* we first define the transformer based on the whole map *)
  (* [!!0] should be fine here since in case of location is lost, we will allocate a new gname
   * in the outer map, and forget about this inner map completely. *)

  (* old definition for reference: *)
  (* Definition new_hist OCV hist := *)
  (*   omap bumper (drop_above (OCV !!0 ℓ) hist). *)

  Definition drop_bump OCV t v :=
    if decide (t ≤ OCV !!0 ℓ) then bumper v else None.

  Definition hist_map_rel: ghost_map_relyT (K := nat) :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = map_entry_lift_gmap_view (V := leibnizO V) $ drop_bump OCV.
End hist_map_lemmas.
