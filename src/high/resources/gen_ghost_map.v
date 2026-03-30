(** This is a replication of the Iris [ghost_map] resource, except that:
 ** - we replace normal [own] with [gen_own] so that we can reason about generational transformations.
 ** - we use [prodR gmap_viewUR gmap_viewUR] so that we can remember the last generation's map.
 ** This construction is not generic in the sense that it always depends on the [crashed_atR] from the
 ** base logic. **)
From Equations Require Import Equations.
From iris.algebra Require Import gmap_view view.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import classes ltac_tactics.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra.

From self Require Import extra map_extra.
From self.nextgen Require Import hvec nextgen_promises gmap_view_transformation.
From self.algebra Require Import view.
From self.base Require Import generational_resources.
From self.base.modalities Require Import if_rec.

From self.lang Require Import lang.

Set Default Proof Using "Type*".

(* typeclasses *)
Definition ghost_mapR (K: Type) (V: Type) `{!EqDecision K, !Countable K}: cmra := prodR (gmap_viewUR K (agreeR (leibnizO V))) (gmap_viewUR K (agreeR (leibnizO V))).
Class ghost_mapGpreS (K: Type) (V: Type) `{!EqDecision K, !Countable K} (Σ: gFunctors) (Ω: gGenCmras Σ) `{!crashed_atGpreS Σ Ω} := {
  ghost_mapGpreS_ghost_map :: genInDepsG Σ Ω (ghost_mapR K V) [#crashed_atR];
}.

(* All ghost map share a similar transformation [λ OCV, λ (_, m), (discard m, t OCV m)]
 * with [t] specific to each instance.
 * We first define the common components of all ghost maps. *)
Section transformers.
  Context (K: Type) (V: Type) `{!EqDecision K, !Countable K}.

  Implicit Type (k: K) (v: V) (OCV: view) (m: gmap K V).
  (* the instance-specific transformer. *)
  Context (map_entry_trans: view → K → V → option (leibnizO V)) `{Hmaptrans: !∀ OCV, MapTrans (V := leibnizO V) (map_entry_trans OCV)}.
  
  Definition ghost_map_trans OCV: cmra_to_trans (ghost_mapR K V) :=
    λ '(_, x), (x, (map_entry_lift_gmap_view (V := leibnizO V) (map_entry_trans OCV)) x).

  #[local] Instance map_entry_trans_cmra_morphism OCV:
    CmraMorphism (map_entry_lift_gmap_view (V := leibnizO V) (map_entry_trans OCV)).
  Proof. apply _. Qed.

  #[global] Instance ghost_map_trans_cmra_morphism OCV:
    CmraMorphism (ghost_map_trans OCV).
  Proof.
    split.
    - intros n x y [Hne_auth Hne_frag].
      destruct x,y =>/=.
      rewrite /ghost_map_trans.
      simpl in *.
      rewrite cmra_morphism_ne; last done.
      f_equiv.
      done.
    - intros n [x y].
      rewrite /ghost_map_trans /= 2!pair_validN.
      intros [Hx Hy].
      split; first done.
      apply cmra_morphism_validN; first apply _.
      done.
    - intros [? [auth frag]].
      rewrite /ghost_map_trans 2!pair_pcore /=.
      f_equiv.
      pose proof (@cmra_morphism_pcore _ _ _ _ (map_entry_trans_cmra_morphism OCV)).
      specialize H with (View auth frag).
      rewrite /= view.view_pcore_eq in H.
      inversion H.
      done.
    - intros [xlast xcurr] [ylast ycurr].
      rewrite /ghost_map_trans /= -pair_op.
      f_equiv.
      by rewrite cmra_morphism_op.
  Qed.

  Definition ghost_map_relyT := rel_over [#crashed_atR] (ghost_mapR K V).

  Definition ghost_map_rel: ghost_map_relyT :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧ t = ghost_map_trans OCV.
End transformers.


Arguments ghost_map_trans {_ _ _ _} _ _.
Arguments ghost_map_rel {_ _ _ _} _.

Section assertions.
  Context (K: Type) (V: Type) `{!EqDecision K, !Countable K}.

  Implicit Type (k: K) (v: V) (OCV: view) (m: gmap K V).
  Context `{!nvmBaseGS Σ Ω, !ghost_mapGpreS K V Σ Ω}.
  (* the instance-specific transformer. *)
  Context (γ: gname) (map_entry_trans: view → K → V → option (leibnizO V)) `{Hmaptrans: !∀ OCV, MapTrans (V := leibnizO V) (map_entry_trans OCV)}.
  
  Definition ghost_map_auth dq m: iProp Σ :=
    "own_auth" ∷ gen_own γ (ε, gmap_view_auth (V := agreeR (leibnizO V)) dq (to_agree <$> m)) ∗
    "#rely" ∷ rely (g := ghost_mapGpreS_ghost_map) γ [#crashed_at_name] (ghost_map_rel map_entry_trans) True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition ghost_map_elem k dq v: iProp Σ :=
    "own_elem" ∷ gen_own γ (ε, gmap_view_frag (V:= agreeR (leibnizO V)) k dq (to_agree v)) ∗
    "#rely" ∷ rely γ [#crashed_at_name] (ghost_map_rel map_entry_trans) True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition lastgen_ghost_map_auth dq m: iProp Σ :=
    gen_own γ (gmap_view_auth (V := agreeR (leibnizO V)) dq (to_agree <$> m), ε).

  Definition lastgen_ghost_map_elem k dq v: iProp Σ :=
    gen_own γ (gmap_view_frag (V:= agreeR (leibnizO V)) k dq (to_agree v), ε).
End assertions.

Arguments ghost_map_auth {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments lastgen_ghost_map_auth {_ _ _ _ _ _ _ _} _ _ _.
Arguments ghost_map_elem {_ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments lastgen_ghost_map_elem {_ _ _ _ _ _ _ _} _ _ _ _.

Notation "k ↪[ γ , trans ] dq v" := (ghost_map_elem γ trans k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ , trans ] dq  v") : bi_scope.

Set Default Proof Using "Type".

(* current generation ghost map lemmas *)
Section current_gen_ghost_map_lemmas.
  Context `{Countable K, V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K V Σ Ω}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).
  (* select lemmas that is being used in Spirea repo. *)

  Context {t: view → K → V → option (leibnizO V)}.

  Global Instance ghost_map_elem_timeless k γ dq v : Timeless (k ↪[γ, t]{dq} v).
  Proof. apply _. Qed.
  Global Instance ghost_map_elem_persistent k γ v : Persistent (k ↪[γ, t]□ v).
  Proof. apply _. Qed.
  
  #[global] Instance ghost_map_auth_persistent γ m :
    Persistent (ghost_map_auth γ t DfracDiscarded m).
  Proof. rewrite /ghost_map_auth /gmap_view_auth. apply _. Qed.

  Global Instance ghost_map_elem_fractional k γ v :
    Fractional (λ q, k ↪[γ, t]{#q} v)%I.
  Proof.
    intros p q.
    apply bi.equiv_entails_2.
    - iNamed 1.
      rewrite -(agree_idemp (A := leibnizO V) (to_agree v)).
      iDestruct "own_elem" as "[p q]".
      iSplitL "p"; iFrame "∗#".
    - iIntros "[[p $] [q _]]".
      iDestruct (gen_own_op_2 with "p q") as "pq".
      rewrite -?pair_op.
      rewrite -gmap_view_frag_op dfrac_op_own agree_idemp.
      done.
  Qed.

  Global Instance ghost_map_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ, t]{#q} v) (λ q, k ↪[γ, t]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance ghost_map_auth_fractional γ m : Fractional (λ q, ghost_map_auth γ t (DfracOwn q) m)%I.
  Proof.
    intros p q.
    apply bi.equiv_entails_2.
    - iNamed 1.
      iDestruct "own_auth" as "[p q]".
      iSplitL "p"; iFrame "∗#".
    - iIntros "[[p $] [q _]]".
      iDestruct (gen_own_op_2 with "p q") as "pq".
      rewrite -pair_op -gmap_view_auth_dfrac_op dfrac_op_own.
      done.
  Qed.

  Global Instance ghost_map_auth_as_fractional k γ q m :
    AsFractional (ghost_map_auth γ t (DfracOwn q) m) (λ q, ghost_map_auth γ t (DfracOwn q) m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma prod_update_r {A B: cmra} (x: A) (y z: B):
    y ~~> z → (x, y) ~~> (x, z).
  Proof. intros. by apply prod_update. Qed.
  
  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist γ k dq v:
    k ↪[γ, t]{dq} v ==∗ k ↪[γ, t]□ v.
  Proof.
    iNamed 1.
    iMod (gen_own_update with "own_elem") as "$".
    { apply prod_update_r.
      apply gmap_view_frag_persist. }
    naive_solver.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ t (DfracOwn 1) m ==∗ ghost_map_auth γ t (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ, t] v.
  Proof.
    intros Hm.
    iNamed 1.
    iMod (gen_own_update _ (ε, _) (ε, _) with "own_auth") as "[? ?]".
    { apply prod_update_r.
      apply (gmap_view_alloc (V := agreeR $ leibnizO V) _ k (DfracOwn 1) (to_agree v)); [ | done | done ].
      rewrite lookup_fmap Hm //. }
    iModIntro.
    iFrame "∗#".
    rewrite fmap_insert //.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ t (DfracOwn 1) m -∗ k ↪[γ, t] v ==∗ ghost_map_auth γ t (DfracOwn 1) (<[k := w]> m) ∗ k ↪[γ, t] w.
  Proof.
    iNamed 1.
    iIntros "[own_elem _]".
    iMod (gen_own_update_2 with "own_auth own_elem") as "[$ $]".
    { apply prod_update_r. rewrite fmap_insert. apply: gmap_view_replace. done. }
    by iFrame "#".
  Qed.

  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ t (DfracOwn 1) m ==∗ ghost_map_auth γ t (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ, t]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_lookup {γ dp m k dq v} :
    ghost_map_auth γ t dp m -∗ k ↪[γ, t]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    iNamed 1.
    iIntros "[own_elem _]".
    iDestruct (gen_own_valid_2 with "own_auth own_elem") as
      %[_ (av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total]%pair_valid.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    apply (to_agree_included_L (SI:=natSI) (A:=leibnizO V)) in Hincl.
    by rewrite Hincl.
  Qed.

  Lemma ghost_map_lookup_big {γ dp dq m} m0 :
    ghost_map_auth γ t dp m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ, t]{dq} v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  (** Make a the authorative element read-only. *)
  Lemma ghost_map_auth_persist γ dq m:
    ghost_map_auth γ t dq m -∗ |==> ghost_map_auth γ t DfracDiscarded m.
  Proof.
    iNamed 1.
    iMod (gen_own_update with "own_auth") as "?".
    { apply prod_update_r. apply gmap_view_auth_persist. }
    iModIntro.
    iFrame "∗#".
  Qed.

  Lemma ghost_map_auth_valid_2 γ dq1 dq2 m1 m2 :
    ghost_map_auth γ t dq1 m1 -∗ ghost_map_auth γ t dq2 m2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ m1 = m2⌝.
  Proof.
    iNamed 1.
    iIntros "[own_auth' _]".
    iDestruct (gen_own_valid_2 with "own_auth own_auth'") as %[_ [? ?%(map_fmap_equiv_inj _
      (to_agree_inj (A:=(leibnizO _))))]%gmap_view_auth_dfrac_op_valid]%pair_valid.
    by fold_leibniz.
  Qed.

  Lemma ghost_map_auth_agree γ dq1 dq2 m1 m2 :
    ghost_map_auth γ t dq1 m1 -∗ ghost_map_auth γ t dq2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  Lemma ghost_map_elem_valid k γ dq v: k ↪[γ, t]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    iNamed 1.
    iDestruct (gen_own_valid with "own_elem") as %[_ ?%gmap_view_frag_valid]%pair_valid.
    naive_solver.
  Qed.

  Lemma ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ, t]{dq1} v1 -∗ k ↪[γ, t]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    iNamed 1.
    iIntros "[own_elem' _]".
    iDestruct (gen_own_valid_2 with "own_elem own_elem'") as %[_ [? Hag]%gmap_view_frag_op_valid]%pair_valid.
    rewrite to_agree_op_valid_L in Hag. done.
  Qed.

  Lemma ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ, t]{dq1} v1 -∗ k ↪[γ, t]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.
  (* TODO: allocation lemmas *)
  Lemma big_op_pair_unit_l (m: gmap K V) dq:
    (ε: gmap_viewUR K (agreeR (leibnizO V)), [^ op map] k↦v ∈ (to_agree <$> m), gmap_view_frag (V := agreeR (leibnizO V)) k dq v) ≡
    [^ op map] k↦v ∈ (to_agree <$> m), ((ε: gmap_viewUR K (agreeR (leibnizO V)), gmap_view_frag (V := agreeR (leibnizO V)) k dq v): ghost_mapR K V).
  Proof.
    induction m using map_ind.
    - rewrite ?big_opM_empty //.
    - rewrite fmap_insert ?big_opM_insert ?lookup_fmap ?H0 //.
      rewrite pair_op_2.
      f_equiv.
      done.
  Qed.

  Lemma ghost_map_alloc `{∀OCV, MapTrans (V := leibnizO V) (t OCV)} OPV OCV m dq :
    ✓ dq →
    (* this precondition means that we can only allocate in the context of [wp]. *)
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, ghost_map_auth γ t (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, t]{dq} v.
  Proof.
    iIntros (?) "#crashed_at_offset #rely_self".
    iMod (own_gen_alloc
                  (DS := [#crashed_atR])
                  (ε, gmap_view_auth (V:=agreeR (leibnizO V)) (DfracOwn 1) ∅)
                  [#crashed_at_name]
                  [##_] with "[]") as (γ) "[auth tok]".
    { apply pair_valid. split; first apply ucmra_unit_valid. apply gmap_view_auth_valid. }
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iAssumption. }
    iExists γ.
    iMod (gen_own_update _ (ε, _) (ε, _) with "auth") as "[auth frag]".
    { apply prod_update_r. apply: (gmap_view_alloc_big (V:= agreeR (leibnizO V)) _ (to_agree <$> m) dq).
      - apply map_disjoint_empty_r.
      - done.
      - by apply map_Forall_fmap. }
    iMod (token_strengthen_promise
            (DS := [#crashed_atR])
            _ [#_] [##_] _ (ghost_map_rel t) _ True_pred
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
    { intros ts crashedPred.
      dependent elimination ts as [hcons tC hnil].
      destruct crashedPred as ((OCV2 & ? & ->) & _).
      exists (ghost_map_trans t OCV2).
      split; first apply _.
      simpl.
      exists OCV2. done. }
    iDestruct (token_to_rely with "tok") as "#rely".
    iModIntro.
    rewrite (right_id _ (∪)).
    iFrame "auth #".
    rewrite /ghost_map_elem.
    rewrite big_op_pair_unit_l big_opM_gen_own_1.
    rewrite big_sepM_fmap.
    iApply (big_sepM_impl with "frag").
    iIntros "!>" (k v ?) "$".
    iFrame "#".
  Qed.
  
  Lemma ghost_map_alloc_persistent `{∀ OCV, MapTrans (V := leibnizO V) (t OCV)} OPV OCV m :
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, ghost_map_auth γ t (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, t]□ v.
  Proof.
    iIntros "#crashed_at_offset #rely_self".
    iMod (ghost_map_alloc OPV OCV m (DfracDiscarded) with "[#$] [#$]") as (γ) "[auth map]";
      first done.
    iExists γ.
    iFrame.
    done.
  Qed.

  Lemma ghost_map_auth_crashed_at_offset γ dq m:
    ghost_map_auth γ t dq m -∗ ∃ OCV, crashed_at_offset OCV.
  Proof. iNamed 1. iFrame "#". Qed.
End current_gen_ghost_map_lemmas.

(* last generation ghost map lemmas *)
Section last_gen_ghost_map_lemmas.
  Context `{Countable K, V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K V Σ Ω}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).
  (* select lemmas that is being used in Spirea repo. *)

  Global Instance lastgen_ghost_map_elem_timeless k γ dq v : Timeless (lastgen_ghost_map_elem γ k dq v).
  Proof. apply _. Qed.
  Global Instance lastgen_ghost_map_elem_persistent k γ v : Persistent (lastgen_ghost_map_elem γ k DfracDiscarded v).
  Proof. rewrite /lastgen_ghost_map_elem. apply _. Qed.

  #[global] Instance lastgen_ghost_map_auth_persistent γ m :
    Persistent (lastgen_ghost_map_auth γ DfracDiscarded m).
  Proof. rewrite /lastgen_ghost_map_auth /gmap_view_auth. apply _. Qed.

  Lemma prod_update_l {A B: cmra} (x: A) (y z: B):
    y ~~> z → (y, x) ~~> (z, x).
  Proof. intros. by apply prod_update. Qed.
  
  Lemma lastgen_ghost_map_auth_persist γ dq m:
    lastgen_ghost_map_auth γ dq m -∗ |==> lastgen_ghost_map_auth γ DfracDiscarded m.
  Proof.
    iIntros "own_auth".
    iMod (gen_own_update with "own_auth") as "?".
    { apply prod_update_l. apply gmap_view_auth_persist. }
    iModIntro.
    iFrame "∗#".
  Qed.

  Lemma lastgen_ghost_map_lookup {γ dp m k dq v} :
    lastgen_ghost_map_auth γ dp m -∗ lastgen_ghost_map_elem γ k dq v -∗ ⌜m !! k = Some v⌝.
  Proof.
    iIntros "own_auth own_elem".
    iDestruct (gen_own_valid_2 with "own_auth own_elem") as
      %[(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total _]%pair_valid.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    (* FIXME: Why do we need [(SI:=natSI) (A:=leibnizO V)]
    https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/555 seems to resolve
    the problem? *)
    apply (to_agree_included_L (SI:=natSI) (A:=leibnizO V)) in Hincl.
    by rewrite Hincl.
  Qed.
  
  Lemma lastgen_ghost_map_lookup_big {γ dp dq m} m0 :
    lastgen_ghost_map_auth γ dp m -∗
    ([∗ map] k↦v ∈ m0, lastgen_ghost_map_elem γ k dq v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (lastgen_ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma lastgen_ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    lastgen_ghost_map_elem γ k dq1 v1 -∗
    lastgen_ghost_map_elem γ k dq2 v2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    iIntros "own_elem own_elem'".
    iDestruct (gen_own_valid_2 with "own_elem own_elem'") as %[[? Hag]%gmap_view_frag_op_valid _]%pair_valid.
    rewrite to_agree_op_valid_L in Hag. done.
  Qed.
  
  Lemma lastgen_ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    lastgen_ghost_map_elem γ k dq1 v1 -∗
    lastgen_ghost_map_elem γ k dq2 v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (lastgen_ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Lemma lastgen_ghost_map_auth_valid_2 γ dq1 dq2 m1 m2 :
    lastgen_ghost_map_auth γ dq1 m1 -∗ lastgen_ghost_map_auth γ dq2 m2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ m1 = m2⌝.
  Proof.
    iIntros "own_auth own_auth'".
    iDestruct (gen_own_valid_2 with "own_auth own_auth'") as %[[? ?%(map_fmap_equiv_inj _
      (to_agree_inj (A:=(leibnizO _))))]%gmap_view_auth_dfrac_op_valid _]%pair_valid.
    by fold_leibniz.
  Qed.
  
  Lemma lastgen_ghost_map_auth_agree γ dq1 dq2 m1 m2 :
    lastgen_ghost_map_auth γ dq1 m1 -∗ lastgen_ghost_map_auth γ dq2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (lastgen_ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.
End last_gen_ghost_map_lemmas.

(* [loc_map]s are ghost maps that simply drop or preserve entries based on the key and
 * *)
Section loc_map_lemmas.
  Context {V: Type}.
  Implicit Type (v: V) (OCV: view) (m: gmap loc V).

  Definition drop_OCV OCV ℓ v :=
    if (decide (ℓ ∈ dom OCV)) then Some v else None.


  #[global] Instance drop_OCV_maptrans OCV: MapTrans (V := leibnizO V) (drop_OCV OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_OCV; intros; destruct (decide _); done.
  Qed.

  Lemma loc_map_cmra_morphism OCV:
    CmraMorphism (ghost_map_trans drop_OCV OCV).
  Proof. apply ghost_map_trans_cmra_morphism. apply _. Qed.
  
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
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV OCV) (gmap_view_frag (V := agreeR (leibnizO V)) ℓ dq (to_agree v))) =
    (gmap_view_frag (V:= agreeR (leibnizO V)) ℓ dq (to_agree v)).
  Proof.
    intros.
    rewrite map_entry_lift_gmap_view_frag /drop_OCV decide_True //.
  Qed.

  Context `{!nvmBaseGS Σ Ω, !ghost_mapGpreS loc V Σ Ω}.

  Lemma prod_op_unit {A B: ucmra} (a: A) (b: B): (a, b) ≡ (ε, b) ⋅ (a, ε).
  Proof. rewrite -pair_op left_id right_id //. Qed.
  
  #[global] Instance ghost_map_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ drop_OCV dq m)
      (lastgen_ghost_map_auth γ dq m ∗
       ∀ OCV,
         crashed_at_offset OCV -∗
         ghost_map_auth γ drop_OCV dq (restrict (dom OCV) m)).
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
    iEval (simpl) in "own_auth".
    rewrite prod_op_unit gen_own_op.
    iDestruct "own_auth" as "[own_auth $]".
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
      (ghost_map_elem γ drop_OCV ℓ dq v)
      (lastgen_ghost_map_elem γ ℓ dq v ∗
       ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗ (ghost_map_elem γ drop_OCV ℓ dq v)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct "own_elem" as (t) "[#picked elem]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iEval (rewrite /= prod_op_unit gen_own_op) in "elem".
    iDestruct "elem" as "[elem $]".
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
  Qed.
  
  Lemma ghost_map_elem_into_nextgen_ifrec γ ℓ dq v:
    ghost_map_elem γ drop_OCV ℓ dq v -∗
    ⚡==> lastgen_ghost_map_elem γ ℓ dq v ∗ if_rec ℓ (ghost_map_elem γ drop_OCV ℓ dq v).
  Proof.
    iIntros "H !>".
    iDestruct "H" as "[$ H]".
    iIntros (OCV ?) "? ?".
    iDestruct ("H" with "[$] [%]") as "$".
    by apply elem_of_dom.
  Qed.
End loc_map_lemmas.

(* Unlike other [ghost_map loc], [na_views] also need to clear all surviving
 * views to [∅]. *)
Section na_views_lemmas.
  Notation V := view.
  Implicit Type (v: V) (OCV: view) (m: gmap loc V).
  
  Context `{!nvmBaseGS Σ Ω, !ghost_mapGpreS loc V Σ Ω}.

  Definition drop_OCV_clear OCV ℓ v: option view :=
    if (decide (ℓ ∈ dom OCV)) then Some ∅ else None.

  #[global] Instance drop_OCV_clear_maptrans OCV: MapTrans (V := leibnizO V) (drop_OCV_clear OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_OCV_clear; intros; destruct (decide _); done.
  Qed.

  Lemma na_views_map_cmra_morphism OCV:
    CmraMorphism (ghost_map_trans drop_OCV_clear OCV).
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
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_OCV_clear OCV) (gmap_view_frag (V := agreeR (leibnizO V)) ℓ dq (to_agree v))) =
    (gmap_view_frag (V:= agreeR (leibnizO V)) ℓ dq (to_agree ∅)).
  Proof.
    intros.
    rewrite map_entry_lift_gmap_view_frag /drop_OCV_clear decide_True //.
  Qed.
  
  #[global] Instance na_views_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ drop_OCV_clear dq m)
      (lastgen_ghost_map_auth γ dq m ∗
       ∀ OCV,
         crashed_at_offset OCV -∗
         ghost_map_auth γ drop_OCV_clear dq (const ∅ <$> restrict (dom OCV) m)).
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
    iEval (rewrite /= prod_op_unit gen_own_op) in "own_auth".
    iDestruct "own_auth" as "[own_auth $]".
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
      (ghost_map_elem γ drop_OCV_clear ℓ dq v)
      (lastgen_ghost_map_elem γ ℓ dq v ∗ ∀ OCV, crashed_at_offset OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗ (ghost_map_elem γ drop_OCV_clear ℓ dq ∅)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iDestruct "crashed" as (OCV) "crashed".
    iModIntro.
    iDestruct "own_elem" as (t) "[#picked elem]".
    iDestruct "rely" as "(rely & (%t' & %tC & (%R & _) & picked' & pickedC))".
    iPickedInAgree "picked picked'".
    destruct R as (OCV' & -> & ->).
    iEval (rewrite /= prod_op_unit gen_own_op) in "elem".
    iDestruct "elem" as "[elem $]".
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
  Qed.
End na_views_lemmas.

(* the other ghost map we use are the per location history maps,
 * the transformer is roughly [(drop_above k <$> bumper v)] *)
Section per_location_map_lemmas.
  Notation K := nat.
  
  (* we are fixed for one location and assumes its bumper. *)
  Context `{V: Type, !nvmBaseGS Σ Ω, !ghost_mapGpreS K V Σ Ω, !Inhabited V}.
  Context (ℓ: loc) (bumper: V → option V).
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

  #[global] Instance drop_above_bump_maptrans OCV: MapTrans (V := leibnizO V) (drop_above_bump OCV).
  Proof.
    split; last solve_proper.
    rewrite /drop_above_bump; intros; destruct (decide _); try done.
  Qed.

  Lemma per_loc_map_cmra_morphism OCV:
    CmraMorphism (ghost_map_trans drop_above_bump OCV).
  Proof. apply _. Qed.
  
  Definition drop_bump_map OCV hist: gmap K V :=
    map_imap (drop_above_bump OCV) hist.
  
  #[global] Instance per_loc_map_auth_into_nextgen γ dq m:
    IntoNextgen
      (ghost_map_auth γ drop_above_bump dq m)
      (lastgen_ghost_map_auth γ dq m ∗
       ∀ OCV,
         crashed_at_offset OCV -∗
         ghost_map_auth γ drop_above_bump dq (drop_bump_map OCV m)).
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
    iEval (rewrite /= prod_op_unit gen_own_op) in "own_auth".
    iDestruct "own_auth" as "[own_auth $]".
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
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_above_bump OCV) (gmap_view_frag (V := agreeR (leibnizO V)) t dq (to_agree v))) =
    (gmap_view_frag (V:= agreeR (leibnizO V)) t dq (to_agree v')).
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
      (ghost_map_elem γ drop_above_bump t dq v)
      (lastgen_ghost_map_elem γ t dq v ∗
       ∀ OCV,
         crashed_at_offset OCV -∗
         match drop_above_bump OCV t v with
         | Some v' => ghost_map_elem γ drop_above_bump t dq v'
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
    iEval (rewrite /= prod_op_unit gen_own_op) in "own_elem".
    iDestruct "own_elem" as "[own_elem $]".
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
