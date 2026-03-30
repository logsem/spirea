(** This file provides non-discrete instance of [ghost_map] so that we can store predicates.
 ** It's mostly the same as [gen_ghost_map.v], with the only difference being that [V] can be any ofe.
 ** I couldn't merge them because many typeclass resolutions will fail for the [leibnizO V] case,
 ** Maybe it can be resolved in the future. *)
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

(* types and typeclasses *)
Definition ghost_mapOR (K: Type) (V: ofe) `{!EqDecision K, !Countable K}: cmra := gmap_viewUR K (agreeR V).
Class ghost_mapOGpreS (K: Type) (V: ofe) `{!EqDecision K, !Countable K} (Σ: gFunctors) (Ω: gGenCmras Σ) `{!crashed_atGpreS Σ Ω} := {
  #[local] ghost_mapOGpreS_ghost_mapO :: genInDepsG Σ Ω (ghost_mapOR K V) [#crashed_atR];
}.

Set Default Proof Using "Type*".
Section transformers.
  Context (K: Type) (V: ofe) `{!EqDecision K, !Countable K}.

  Implicit Type (k: K) (v: V) (OCV: view) (m: gmap K V).
  (* the instance-specific transformer. *)
  Context (map_entry_trans: view → K → V → option V) `{Hmaptrans: !∀ OCV, MapTrans (map_entry_trans OCV)}.
  
  Definition ghost_mapO_trans OCV: cmra_to_trans (ghost_mapOR K V) :=
    (map_entry_lift_gmap_view (map_entry_trans OCV)).

  #[local] Instance map_entry_trans_cmra_morphism OCV:
    CmraMorphism (map_entry_lift_gmap_view (map_entry_trans OCV)).
  Proof. apply _. Qed.

  #[global] Instance ghost_mapO_trans_cmra_morphism OCV:
    CmraMorphism (ghost_mapO_trans OCV).
  Proof. apply _. Qed.

  Definition ghost_mapO_relyT := rel_over [#crashed_atR] (ghost_mapOR K V).

  Definition ghost_mapO_rel: ghost_mapO_relyT :=
    λ tC t,
      ∃ OCV,
        tC = crashed_at_trans OCV ∧ t = ghost_mapO_trans OCV.
End transformers.

Set Default Proof Using "Type".
Arguments ghost_mapO_trans {_ _ _ _} _ _.
Arguments ghost_mapO_rel {_ _ _ _} _.

Section assertions.
  Context (K: Type) (V: ofe) `{!EqDecision K, !Countable K}.

  Implicit Type (k: K) (v: V) (OCV: view) (m: gmap K V).
  Context `{!nvmBaseGS Σ Ω, !ghost_mapOGpreS K V Σ Ω}.
  (* the instance-specific transformer. *)
  Context (γ: gname) (map_entry_trans: view → K → V → option V) `{Hmaptrans: !∀ OCV, MapTrans (map_entry_trans OCV)}.
  
  Definition ghost_mapO_auth dq m: iProp Σ :=
    "own_auth" ∷ gen_own γ (gmap_view_auth (V := agreeR V) dq (to_agree <$> m)) ∗
    "#rely" ∷ rely (g := ghost_mapOGpreS_ghost_mapO) γ [#crashed_at_name] (ghost_mapO_rel map_entry_trans) True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition ghost_mapO_elem k dq v: iProp Σ :=
    "own_elem" ∷ gen_own γ (gmap_view_frag (V:= agreeR V) k dq (to_agree v)) ∗
    "#rely" ∷ rely γ [#crashed_at_name] (ghost_mapO_rel map_entry_trans) True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.
End assertions.

Arguments ghost_mapO_auth {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments ghost_mapO_elem {_ _ _ _ _ _ _ _} _ _ _ _ _.

Notation "k ↪[ γ , trans ] dq v" := (ghost_mapO_elem γ trans k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ , trans ] dq  v") : bi_scope.

(* current generation ghost map lemmas *)
Section ghost_mapO_lemmas.
  Context `{Countable K, V: ofe, !nvmBaseGS Σ Ω, !ghost_mapOGpreS K V Σ Ω}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).
  (* select lemmas that is being used in Spirea repo. *)

  Context {t: view → K → V → option V}.

  #[global] Instance ghost_mapO_elem_persistent k γ v : Persistent (k ↪[γ, t]□ v).
  Proof. apply _. Qed.
  
  #[global] Instance ghost_mapO_auth_persistent γ m :
    Persistent (ghost_mapO_auth γ t DfracDiscarded m).
  Proof. rewrite /ghost_mapO_auth /gmap_view_auth. apply _. Qed.

  Global Instance ghost_mapO_elem_fractional k γ v :
    Fractional (λ q, k ↪[γ, t]{#q} v)%I.
  Proof.
    intros p q.
    apply bi.equiv_entails_2.
    - iNamed 1.
      rewrite -(agree_idemp (A := V) (to_agree v)).
      iDestruct "own_elem" as "[p q]".
      iSplitL "p"; iFrame "∗#".
    - iIntros "[[p $] [q _]]".
      iDestruct (gen_own_op_2 with "p q") as "pq".
      rewrite -?pair_op.
      rewrite -gmap_view_frag_op dfrac_op_own agree_idemp.
      done.
  Qed.

  Global Instance ghost_mapO_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ, t]{#q} v) (λ q, k ↪[γ, t]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance ghost_mapO_auth_fractional γ m : Fractional (λ q, ghost_mapO_auth γ t (DfracOwn q) m)%I.
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

  Global Instance ghost_mapO_auth_as_fractional k γ q m :
    AsFractional (ghost_mapO_auth γ t (DfracOwn q) m) (λ q, ghost_mapO_auth γ t (DfracOwn q) m)%I q.
  Proof. split; first done. apply _. Qed.

  (** Make an element read-only. *)
  Lemma ghost_mapO_elem_persist γ k dq v:
    k ↪[γ, t]{dq} v ==∗ k ↪[γ, t]□ v.
  Proof.
    iNamed 1.
    iMod (gen_own_update with "own_elem") as "$".
    { apply gmap_view_frag_persist. }
    naive_solver.
  Qed.

  Lemma ghost_mapO_insert {γ m} k v :
    m !! k = None →
    ghost_mapO_auth γ t (DfracOwn 1) m ==∗ ghost_mapO_auth γ t (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ, t] v.
  Proof.
    intros Hm.
    iNamed 1.
    iMod (gen_own_update with "own_auth") as "[? ?]".
    { apply (gmap_view_alloc (V := agreeR V) _ k (DfracOwn 1) (to_agree v)); [ | done | done ].
      rewrite lookup_fmap Hm //. }
    iModIntro.
    iFrame "∗#".
    rewrite fmap_insert //.
  Qed.

  Lemma ghost_mapO_update {γ m k v} w :
    ghost_mapO_auth γ t (DfracOwn 1) m -∗ k ↪[γ, t] v ==∗ ghost_mapO_auth γ t (DfracOwn 1) (<[k := w]> m) ∗ k ↪[γ, t] w.
  Proof.
    iNamed 1.
    iIntros "[own_elem _]".
    iMod (gen_own_update_2 with "own_auth own_elem") as "[$ $]".
    { rewrite fmap_insert. apply: gmap_view_replace. done. }
    by iFrame "#".
  Qed.

  Lemma ghost_mapO_insert_persist {γ m} k v :
    m !! k = None →
    ghost_mapO_auth γ t (DfracOwn 1) m ==∗ ghost_mapO_auth γ t (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ, t]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_mapO_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_mapO_elem_persist. done.
  Qed.
  
  (** Make a the authorative element read-only. *)
  Lemma ghost_mapO_auth_persist γ dq m:
    ghost_mapO_auth γ t dq m -∗ |==> ghost_mapO_auth γ t DfracDiscarded m.
  Proof.
    iNamed 1.
    iMod (gen_own_update with "own_auth") as "?".
    { apply gmap_view_auth_persist. }
    iModIntro.
    iFrame "∗#".
  Qed.
  
  Lemma ghost_mapO_alloc `{∀OCV, MapTrans (t OCV)} OPV OCV m dq :
    ✓ dq →
    (* this precondition means that we can only allocate in the context of [wp]. *)
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, ghost_mapO_auth γ t (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, t]{dq} v.
  Proof.
    iIntros (?) "#crashed_at_offset #rely_self".
    iMod (own_gen_alloc
                  (DS := [#crashed_atR])
                  (gmap_view_auth (V:=agreeR V) (DfracOwn 1) ∅)
                  [#crashed_at_name]
                  [##_] with "[]") as (γ) "[auth tok]".
    { apply gmap_view_auth_valid. }
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iAssumption. }
    iExists γ.
    iMod (gen_own_update with "auth") as "[auth frag]".
    { apply: (gmap_view_alloc_big (V:= agreeR V) _ (to_agree <$> m) dq).
      - apply map_disjoint_empty_r.
      - done.
      - by apply map_Forall_fmap. }
    iMod (token_strengthen_promise
            (DS := [#crashed_atR])
            _ [#_] [##_] _ (ghost_mapO_rel t) _ True_pred
           with "[] tok") as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    2: {
      iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely_self". }
    (* TODO: this subgoal requires me to prove that for any transformer picked for
     *
 [crashed_atR], there exists a transformer for the map that satisfy [R].
     * this can only be proven given specific [R]. I should move this lemma around. *)
    { intros ts crashedPred.
      dependent elimination ts as [hcons tC hnil].
      destruct crashedPred as ((OCV2 & ? & ->) & _).
      exists (ghost_mapO_trans t OCV2).
      split; first apply _.
      simpl.
      exists OCV2. done. }
    iDestruct (token_to_rely with "tok") as "#rely".
    iModIntro.
    rewrite (right_id _ (∪)).
    iFrame "auth #".
    rewrite /ghost_mapO_elem.
    rewrite big_opM_gen_own_1.
    rewrite big_sepM_fmap.
    iApply (big_sepM_impl with "frag").
    iIntros "!>" (k v ?) "$".
    iFrame "#".
  Qed.
  
  Lemma ghost_mapO_alloc_persistent `{∀ OCV, MapTrans (t OCV)} OPV OCV m :
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, ghost_mapO_auth γ t (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ, t]□ v.
  Proof.
    iIntros "#crashed_at_offset #rely_self".
    iMod (ghost_mapO_alloc OPV OCV m (DfracDiscarded) with "[#$] [#$]") as (γ) "[auth map]";
      first done.
    iExists γ.
    iFrame.
    done.
  Qed.

  Lemma ghost_mapO_lookup γ dp m k dq v:
    ghost_mapO_auth γ t dp m -∗ ghost_mapO_elem γ t k dq v -∗ m !! k ≡ Some v.
  Proof.
    iNamed 1.
    iDestruct 1 as "[own_frag _]".
    iDestruct (gen_own_valid_2 with "own_auth own_frag") as "#val".
    rewrite /= gmap_view_both_dfrac_validI.
    iDestruct "val" as (v' ?) "(_ & %look & _ & incl)".
    apply lookup_fmap_Some in look as (v'' & <- & look).
    rewrite look.
    rewrite option_includedI prod_includedI prod_equivI /=.
    iDestruct "incl" as "[[_ incl] | [_ equiv]]".
    - rewrite to_agree_includedI.
      iRewrite "incl".
      done.
    - rewrite agree_equivI.
      iRewrite "equiv".
      done.
  Qed.

  Lemma ghost_mapO_elem_agree k γ dq1 dq2 v1 v2 :
    ghost_mapO_elem γ t k dq1 v1 -∗ ghost_mapO_elem γ t k dq2 v2 -∗ v1 ≡ v2.
  Proof.
    iIntros "[Helem1 _] [Helem2 _]".
    iDestruct (gen_own_valid_2 with  "Helem1 Helem2") as "#val".
    rewrite gmap_view_frag_op_validI to_agree_op_validI.
    iDestruct "val" as "[_ $]".
  Qed.

  Lemma ghost_mapO_auth_crashed_at_offset γ dq m:
    ghost_mapO_auth γ t dq m -∗ ∃ OCV, crashed_at_offset OCV.
  Proof. iNamed 1. iFrame "#". Qed.
End ghost_mapO_lemmas.

Opaque ghost_mapO_auth ghost_mapO_elem.
