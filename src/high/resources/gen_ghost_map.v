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
From self.base.modalities Require Import if_rec.

From self.lang Require Import lang.

Set Default Proof Using "Type*".

(* we first define a version of [ghost_map] that is dependent on
 * the [crashed_at] resource. we do not fix the [t] function for now. *)
Section ghost_map.
  Context (K V: Type) `{!EqDecision K, !Countable K}.

  Implicit Type (k: K) (v: V) (OCV: view) (m: gmap K V).

  Definition ghost_mapR: cmra := gmap_viewUR K (leibnizO V).

  Class ghost_mapGpreS (Σ: gFunctors) (Ω: gGenCmras Σ) `{!crashed_atGpreS Σ Ω} := {
    ghost_mapGpreS_ghost_map :: genInDepsG Σ Ω ghost_mapR [#crashed_atR];
  }.
  (* I don't define a [ghost_mapGS] because there are multiple resources
   * using the same resource type. *)

  Definition ghost_map_relyT := rel_over [#crashed_atR] ghost_mapR.

  Implicit Types (R: ghost_map_relyT).

  Context `{!nvmBaseGS Σ Ω, !ghost_mapGpreS Σ Ω}.
  Definition ghost_map_auth γ R dq m: iProp Σ :=
    "own_auth" ∷ gen_own (i := genInDepsG_gen ghost_mapGpreS_ghost_map) γ (gmap_view_auth (V := leibnizO V) dq m) ∗
    "#rely" ∷ rely (g := ghost_mapGpreS_ghost_map) γ [#crashed_at_name] R True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition ghost_map_elem γ R k dq v: iProp Σ :=
    "own_elem" ∷ gen_own γ (gmap_view_frag (V:= leibnizO V) k dq v) ∗
    "#rely" ∷ rely γ [#crashed_at_name] R True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.
End ghost_map.

Arguments ghost_map_auth {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments ghost_map_elem {_ _ _ _ _ _ _ _} _ _ _ _ _.

Notation "k ↪[ γ , R ] dq v" := (ghost_map_elem γ R k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ , R ] dq  v") : bi_scope.

(* current generation ghost map lemmas *)
Section current_gen_ghost_map_lemmas.
  Context `{Countable K, V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K V Σ Ω}.
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
      iSplitL "p"; iFrame "∗#".
    - iIntros "[[p $] [q _]]".
      iDestruct (gen_own_op_2 with "p q") as "pq".
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
      iSplitL "p"; iFrame "∗#".
    - iIntros "[[p $] [q _]]".
      iDestruct (gen_own_op_2 with "p q") as "pq".
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
    iMod (gen_own_update with "own_elem") as "$".
    { apply gmap_view_frag_persist. }
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
    iFrame "∗#".
  Qed.

  Lemma ghost_map_update {γ R m k v} w :
    ghost_map_auth γ R (DfracOwn 1) m -∗ k ↪[γ, R] v ==∗ ghost_map_auth γ R (DfracOwn 1) (<[k := w]> m) ∗ k ↪[γ, R] w.
  Proof.
    iNamed 1.
    iIntros "[own_elem _]".
    iMod (gen_own_update_2 with "own_auth own_elem") as "[$ $]".
    { apply: gmap_view_update. }
    by iFrame "#".
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
    iNamed 1.
    iIntros "[own_elem _]".
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
    iFrame "∗#".
  Qed.

  Lemma ghost_map_auth_valid_2 γ R dq1 dq2 m1 m2 :
    ghost_map_auth γ R dq1 m1 -∗ ghost_map_auth γ R dq2 m2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ m1 = m2⌝.
  Proof.
    iNamed 1.
    iIntros "[own_auth' _]".
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
    iIntros "[own_elem' _]".
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

  Lemma ghost_map_alloc OPV OCV R m dq :
    ✓ dq →
    (* this precondition means that we can only allocate in the context of [wp]. *)
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
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
    rewrite (right_id _ (∪)).
    iFrame "auth #".
    iSplit; first by iExists _.
    (* TODO: need [gen_own] and [big_op] commute lemma *)
    rewrite /ghost_map_elem.
    rewrite big_opM_gen_own_1.
    (* replace (gen_own γ ([^ op map] k ↦ v ∈ m, (gmap_view_frag (V:= leibnizO V) k dq v))) with *)
    (*   ([∗map] k ↦ v ∈ m, gen_own γ (gmap_view_frag (V:= leibnizO V) k dq v))%I; last admit. *)
    iApply (big_sepM_impl with "frag").
    iIntros "!>" (k v ?) "$".
    iFrame "#".
    by iExists _.
  Admitted.
  
  Lemma ghost_map_alloc_persistent OPV OCV R m :
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, ghost_map_auth γ R (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, R]□ v.
  Proof.
    iIntros "#crashed_at_offset #rely_self".
    iMod (ghost_map_alloc OPV OCV R m (DfracDiscarded) with "[#$] [#$]") as (γ) "[auth map]";
      first done.
    iExists γ.
    iFrame.
    done.
  Qed.

  (* TODO: merge this lemma with the other lemma with the same name in base spirea. *)
  Lemma map_entry_lift_gmap_view_auth dq m map_entry :
    (map_entry_lift_gmap_view map_entry (gmap_view_auth (V := leibnizO V) dq m)) =
    (gmap_view_auth dq (map_imap map_entry m)).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    rewrite agree_map_to_agree. done.
  Qed.
  
  (* The following two lemmas make the two-level maps easier to work with. *)
  Lemma ghost_map_auth_crashed_at_offset γ R dq m:
    ghost_map_auth γ R dq m -∗ ∃ OCV, crashed_at_offset OCV.
  Proof. iNamed 1. iFrame "#". Qed.

  Lemma ghost_map_elem_crashed_at_offset γ R ℓ dq v:
    ghost_map_elem γ R ℓ dq v -∗ ∃ OCV, crashed_at_offset OCV.
  Proof. iNamed 1. iFrame "#". Qed.
End current_gen_ghost_map_lemmas.

(* nextgen lemmas for the location maps *)
Section loc_map_lemmas.
  Context {V: Type}.
  Implicit Type (v: V) (OCV: view) (m: gmap loc V).

  Definition drop_OCV OCV ℓ v :=
    if (decide (ℓ ∈ dom OCV)) then Some v else None.

  Definition loc_map_rel: ghost_map_relyT loc V :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = map_entry_lift_gmap_view (V := leibnizO V) $ drop_OCV OCV.

  #[global] Instance drop_OCV_maptrans OCV: MapTrans (V := leibnizO V) (drop_OCV OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_OCV; intros; destruct (decide _); done.
  Qed.

  Lemma loc_map_cmra_morphism OCV:
    CmraMorphism (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV OCV)).
  Proof. apply _. Qed.
  
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

  Lemma elem_of_drop_OCV_gmap_view_frag OCV ℓ dq v :
    ℓ ∈ dom OCV →
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV OCV) (gmap_view_frag (V := leibnizO V) ℓ dq v)) =
    (gmap_view_frag (V:= leibnizO V) ℓ dq v).
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

  Context `{!nvmBaseGS Σ Ω, !ghost_mapGpreS loc V Σ Ω}.

  #[global] Instance ghost_map_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ loc_map_rel dq m)
      (∀ OCV,
         crashed_at_offset OCV -∗
         ghost_map_auth γ loc_map_rel dq (restrict (dom OCV) m)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_auth" as (tH') "[#pickedH' own_auth]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite /ghost_map_auth.
    iFrame "rely".
    iSplit; last by iExists _, _.
    rewrite map_entry_lift_gmap_view_auth.
    rewrite map_imap_drop_OCV_restrict.
    iFrame.
  Qed.

  #[global] Instance ghost_map_elem_into_nextgen γ ℓ dq v:
    IntoNextgen
      (ghost_map_elem γ loc_map_rel ℓ dq v)
      (∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗ (ghost_map_elem γ loc_map_rel ℓ dq v)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct "own_elem" as (t) "[#picked elem]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iIntros (OCV'') "#crashed_at_offset %domOCV".
    iAssert ⌜ OCV'' = OCV' ⌝%I as %->.
    { iDestruct "crashed_at_offset" as (OV) "crashed_at_both".
      iDestruct "crashed" as (??) "[pickedC' #crashed_at_both']".
      iPickedInAgree "pickedC pickedC'".
      iDestruct (crashed_at_both_agree with "crashed_at_both crashed_at_both'") as %[-> ->].
      iPureIntro.
      done. }
    rewrite elem_of_drop_OCV_gmap_view_frag; last done.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at']".
    iPickedInAgree "pickedC pickedC'".
    iFrame "∗#".
    iIntros.
    iExists _, _.
    iApply "crashed_at'".
  Qed.
  
  Lemma ghost_map_elem_into_nextgen_ifrec γ ℓ dq v:
    ghost_map_elem γ loc_map_rel ℓ dq v -∗
    ⚡==> if_rec ℓ (ghost_map_elem γ loc_map_rel ℓ dq v).
  Proof.
    iIntros "H !>" (OCV ?) "? ?".
    iDestruct ("H" with "[$] [%]") as "$".
    by apply elem_of_dom.
  Qed.
End loc_map_lemmas.

(* Unlike other [ghost_map loc], [na_views] also need to clear the view to [∅]. *)
Section na_views_lemmas.
  Notation V := view.
  Implicit Type (v: V) (OCV: view) (m: gmap loc V).
  
  Context `{!nvmBaseGS Σ Ω, !ghost_mapGpreS loc V Σ Ω}.

  Definition drop_OCV_clear OCV ℓ v: option view :=
    if (decide (ℓ ∈ dom OCV)) then Some ∅ else None.

  Definition na_views_rel: ghost_map_relyT loc V :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = map_entry_lift_gmap_view (V := leibnizO V) $ drop_OCV_clear OCV.

  #[global] Instance drop_OCV_clear_maptrans OCV: MapTrans (V := leibnizO V) (drop_OCV_clear OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_OCV_clear; intros; destruct (decide _); done.
  Qed.

  Lemma na_views_map_cmra_morphism OCV:
    CmraMorphism (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV_clear OCV)).
  Proof. apply _. Qed.
  
  Lemma map_imap_drop_OCV_clear_restrict OCV m:
    map_imap (drop_OCV_clear OCV) m = const ∅ <$> restrict (dom OCV) m.
  Proof.
    apply map_eq => i.
    rewrite /drop_OCV_clear map_lookup_imap lookup_fmap /=.
    destruct (decide (i ∈ dom OCV)).
    - rewrite restrict_lookup_elem_of; last done.
      by destruct (m !! i).
    - rewrite restrict_lookup_not_elem_of; last done.
      by destruct (m !! i).
  Qed.

  Lemma elem_of_drop_OCV_clear_gmap_view_frag OCV ℓ dq v :
    ℓ ∈ dom OCV →
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV_clear OCV) (gmap_view_frag (V := leibnizO V) ℓ dq v)) =
    (gmap_view_frag (V:= leibnizO V) ℓ dq ∅).
  Proof.
    intros.
    unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
    unfold gmap_view_frag, view_frag.
    f_equal.
    rewrite -{1}insert_empty.
    erewrite map_imap_insert_Some;
      first rewrite map_imap_empty insert_empty //.
    rewrite agree_option_map_to_agree /drop_OCV_clear decide_True //.
  Qed.
  
  #[global] Instance na_views_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ na_views_rel dq m)
      (∀ OCV,
         crashed_at_offset OCV -∗
         ghost_map_auth γ na_views_rel dq (const ∅ <$> restrict (dom OCV) m)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_auth" as (tH') "[#pickedH' own_auth]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite /ghost_map_auth.
    iFrame "rely".
    iSplit; last by iExists _, _.
    rewrite map_entry_lift_gmap_view_auth.
    rewrite map_imap_drop_OCV_clear_restrict.
    iFrame.
  Qed.

  #[global] Instance na_views_elem_into_nextgen γ ℓ dq v:
    IntoNextgen
      (ghost_map_elem γ na_views_rel ℓ dq v)
      (∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗ (ghost_map_elem γ na_views_rel ℓ dq ∅)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct "own_elem" as (t) "[#picked elem]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iIntros (OCV'') "#crashed_at_offset %domOCV".
    iAssert ⌜ OCV'' = OCV' ⌝%I as %->.
    { iDestruct "crashed_at_offset" as (OV) "crashed_at_both".
      iDestruct "crashed" as (??) "[pickedC' #crashed_at_both']".
      iPickedInAgree "pickedC pickedC'".
      iDestruct (crashed_at_both_agree with "crashed_at_both crashed_at_both'") as %[-> ->].
      iPureIntro.
      done. }
    rewrite elem_of_drop_OCV_clear_gmap_view_frag; last done.
    iDestruct "crashed" as (??) "[pickedC' #crashed_at']".
    iPickedInAgree "pickedC pickedC'".
    iFrame "∗#".
    iIntros.
    iExists _, _.
    iApply "crashed_at'".
  Qed.
End na_views_lemmas.

(* the other ghost map we use are the per location history maps,
 * the transformer is roughly [(drop_above k <$> bumper v)] *)
Section per_location_map_lemmas.
  Notation K := nat.
  
  (* we are fixed for one location and assumes its bumper. *)
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K V Σ Ω, !Inhabited V}.
  Variable (ℓ: loc) (bumper: V → option V).
  Implicit Type (v: V) (OCV: view) (hist: gmap K V).
  (* we first define the transformer based on the whole map
   * [!!0] should be fine here since in case of location is lost, we will allocate a new gname
   * in the outer map, and forget about this inner map completely.
   * old definition for reference: 
   * [Definition new_hist OCV hist := omap bumper (drop_above (OCV !!0 ℓ) hist).] *)  
  (* We need this [safe_bumper] due to the technicality of [gmap_view] transformers.
   * in [ghost_map_map] we can prove that this is not necessary. *)
  Definition safe_bumper v: option V := Some (default inhabitant (bumper v)).
  Definition drop_above_bump OCV t v: option V :=
    if decide (t ≤ OCV !!0 ℓ) then safe_bumper v else None.

  Definition per_loc_map_rel: ghost_map_relyT nat V :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧
        t = map_entry_lift_gmap_view (V := leibnizO V) $ drop_above_bump OCV.

  #[global] Instance drop_above_bump_maptrans OCV: MapTrans (V := leibnizO V) (drop_above_bump OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_above_bump; intros; destruct (decide _); try done.
  Qed.

  Lemma per_loc_map_cmra_morphism OCV:
    CmraMorphism (map_entry_lift_gmap_view (V := leibnizO V) (drop_above_bump OCV)).
  Proof. apply _. Qed.
  
  Definition drop_bump_map OCV hist: gmap K V :=
    map_imap (drop_above_bump OCV) hist.
  
  #[global] Instance per_loc_map_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ per_loc_map_rel dq m)
      (∀ OCV,
         crashed_at_offset OCV -∗
         ghost_map_auth γ per_loc_map_rel dq (drop_bump_map OCV m)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_auth" as (tH') "[#pickedH' own_auth]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite /ghost_map_auth.
    iFrame "rely".
    iSplit; last by iExists _, _.
    rewrite map_entry_lift_gmap_view_auth.
    iFrame "own_auth".
  Qed.

  Lemma elem_of_drop_above_bump_gmap_view_frag OCV t dq v v' :
    drop_above_bump OCV t v = Some v' →
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_above_bump OCV) (gmap_view_frag (V := leibnizO V) t dq v)) =
    (gmap_view_frag (V:= leibnizO V) t dq v').
  Proof.
    intros H.
    unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
    unfold gmap_view_frag, view_frag.
    f_equal.
    rewrite -{1}insert_empty.
    erewrite map_imap_insert_Some;
      first rewrite map_imap_empty insert_empty //.
    move: H.
    rewrite agree_option_map_to_agree /drop_above_bump /safe_bumper.
    destruct (decide _); last done.
    destruct (bumper v); simpl.
    - intros.
      simpl.
      by simplify_eq.
    - intros.
      simpl.
      by simplify_eq.
  Qed.

  #[global] Instance per_loc_map_elem_into_nextgen γ t dq v:
    IntoNextgen
      (ghost_map_elem γ per_loc_map_rel t dq v)
      (∀ OCV,
         crashed_at_offset OCV -∗
         match drop_above_bump OCV t v with
         | Some v' => ghost_map_elem γ per_loc_map_rel t dq v'
         | None => emp
         end).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_elem" as (tH') "[#pickedH' own_elem]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    destruct (drop_above_bump OCV t v) eqn:Heq; last done.
    rewrite (elem_of_drop_above_bump_gmap_view_frag _ _ _ _ _ Heq).
    rewrite /ghost_map_elem.
    iFrame "rely".
    iSplit; last by iExists _, _.
    done.
  Qed.
End per_location_map_lemmas.

(* [crashed_in] behaves more like one-generation resources: it cannot move into next generation.
 * Thus we choose the most convenient posssible definition. *)
Section crashed_in_map.
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS loc V Σ Ω} (γ: gname).
  Implicit Type (v: V) (OCV: view) (m: gmap loc V).
  
  Definition erase (ℓ: loc) (v: V): option V :=
    None.

  #[global] Instance erase_maptrans: MapTrans (V := leibnizO V) erase.
  Proof.
    split; last solve_proper.
    intros. done.
  Qed.

  Lemma crashed_in_map_cmra_morphism:
    CmraMorphism (map_entry_lift_gmap_view (V := leibnizO V) erase).
  Proof. apply _. Qed.

  (* we could have avoided the [crashed_at] dependency altogether, but it doesn't really hurt. *)
  Definition crashed_in_rel: ghost_map_relyT loc V :=
    λ tC t, t = map_entry_lift_gmap_view (V := leibnizO V) erase.

  Lemma crashed_in_map_empty m1:
    map_imap (erase) m1 = ∅.
  Proof.
    rewrite /erase.
    apply map_eq => ℓ.
    rewrite map_lookup_imap /=.
    destruct (m1 !! ℓ); done.
  Qed.

  Definition crashed_at_auth m: iProp Σ := 
    "map_auth" ∷ ghost_map_auth γ crashed_in_rel (DfracOwn 1) m ∗
    "map_discards" ∷ [∗ map] ℓ ↦ v ∈ m, ℓ ↪[γ, crashed_in_rel]□ v.

  Lemma nextgen_bupd_crashed_in {OCV m__old} m__new:
    picked_out crashed_at_name (crashed_at_trans OCV) -∗
    crashed_at_auth m__old -∗
    ⚡==> |==> crashed_at_auth m__new ∗
               [∗ map] ℓ ↦ v ∈ m__new, ℓ ↪[γ, crashed_in_rel]□ v.
  Proof.
    iIntros "pickedC".
    iNamed 1. iNamed "map_auth".
    iModIntro.
    iDestruct "rely" as "[rely (%t & % & [-> _] & picked & _)]".
    iDestruct "own_auth" as (t') "[picked' own_auth]".
    iDestruct "crashed" as (OV OCV' tC') "[pickedC' own_crashed]".
    iPickedInAgree "picked picked'".
    iPickedInAgree "pickedC pickedC'".
    simpl.
    iAssert (∃ OCV, crashed_at_offset OCV)%I with "[own_crashed]" as "#crashed".
    { by iExists _, _. }
    rewrite map_entry_lift_gmap_view_auth crashed_in_map_empty.
    iMod (gen_own_update with "own_auth") as "[own_auth own_frag]".
    { apply: (gmap_view_alloc_big (V:=leibnizO V) _ m__new (DfracOwn 1)).
      - apply map_disjoint_empty_r.
      - done. }
    rewrite (right_id _ (∪)).
    iFrame "own_auth rely crashed".
    rewrite -big_sepM_sep.
    rewrite big_opM_gen_own_1 -big_sepM_bupd.
    iApply (big_sepM_impl with "own_frag").
    iIntros "!>" (ℓ v ?) "gen_own".
    iMod (gen_own_update with "gen_own") as "discard"; first apply gmap_view_frag_persist.
    iDestruct "discard" as "#discard".
    by iFrame "#".
  Qed.
End crashed_in_map.
