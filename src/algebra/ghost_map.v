(** This is a fork of the ghost map included in Iris. The fork allows for the
authorative element to be persisted and it includes additional lemmas for
working with both with persisted authorative and fragmental elements. *)

(** A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap_view.
From iris.algebra Require Export dfrac.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(** The CMRA we need.
FIXME: This is intentionally discrete-only, but
should we support setoids via [Equiv]? *)
Class ghost_mapG Σ (K V : Type) `{Countable K} := GhostMapG {
  ghost_map_inG :> inG Σ (gmap_viewR K (leibnizO V));
}.
Definition ghost_mapΣ (K V : Type) `{Countable K} : gFunctors :=
  #[ GFunctor (gmap_viewR K (leibnizO V)) ].

Global Instance subG_ghost_mapΣ Σ (K V : Type) `{Countable K} :
  subG (ghost_mapΣ K V) Σ → ghost_mapG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{ghost_mapG Σ K V}.

  Definition ghost_map_auth_def (γ : gname) (dq : dfrac) (m : gmap K V) : iProp Σ :=
    own γ (gmap_view_auth (V:=leibnizO V) dq m).
  Definition ghost_map_auth_aux : seal (@ghost_map_auth_def). Proof. by eexists. Qed.
  Definition ghost_map_auth := ghost_map_auth_aux.(unseal).
  Definition ghost_map_auth_eq : @ghost_map_auth = @ghost_map_auth_def := ghost_map_auth_aux.(seal_eq).

  Definition ghost_map_elem_def (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    own γ (gmap_view_frag (V:=leibnizO V) k dq v).
  Definition ghost_map_elem_aux : seal (@ghost_map_elem_def). Proof. by eexists. Qed.
  Definition ghost_map_elem := ghost_map_elem_aux.(unseal).
  Definition ghost_map_elem_eq : @ghost_map_elem = @ghost_map_elem_def := ghost_map_elem_aux.(seal_eq).
End definitions.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "k ↪[ γ ]{ dq } v" := (ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq at level 50, format "k  ↪[ γ ]{ dq }  v") : bi_scope.
Notation "k ↪[ γ ]{# q } v" := (k ↪[γ]{DfracOwn q} v)%I
  (at level 20, γ at level 50, q at level 50, format "k  ↪[ γ ]{# q }  v") : bi_scope.
Notation "k ↪[ γ ] v" := (k ↪[γ]{#1} v)%I
  (at level 20, γ at level 50, format "k  ↪[ γ ]  v") : bi_scope.
Notation "k ↪[ γ ]□ v" := (k ↪[γ]{DfracDiscarded} v)%I
  (at level 20, γ at level 50) : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_map_auth_eq /ghost_map_auth_def
  ?ghost_map_elem_eq /ghost_map_elem_def.

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dp dq : dfrac) (q : Qp) (m : gmap K V).

  Global Instance ghost_map_auth_persistent γ m :
    Persistent (ghost_map_auth γ DfracDiscarded m).
  Proof. unseal. rewrite /gmap_view_auth. apply _. Qed.

  (** * Lemmas about the map elements *)
  Global Instance ghost_map_elem_timeless k γ dq v : Timeless (k ↪[γ]{dq} v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_elem_persistent k γ v : Persistent (k ↪[γ]□ v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_elem_fractional k γ v : Fractional (λ q, k ↪[γ]{#q} v)%I.
  Proof. unseal. intros p q. rewrite -own_op gmap_view_frag_add //. Qed.
  Global Instance ghost_map_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ]{#q} v) (λ q, k ↪[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Local Lemma ghost_map_elems_unseal γ m dq :
    ([∗ map] k ↦ v ∈ m, k ↪[γ]{dq} v) ==∗
    own γ ([^op map] k↦v ∈ m, gmap_view_frag (V:=leibnizO V) k dq v).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Lemma ghost_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Helem".
    iDestruct (own_valid with "Helem") as %?%gmap_view_frag_valid.
    done.
  Qed.
  Lemma ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%gmap_view_frag_op_valid_L.
    done.
  Qed.
  Lemma ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Lemma ghost_map_elem_combine k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_map_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Lemma ghost_map_elem_dfrac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma ghost_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_map_elem_dfrac_ne. apply: exclusive_l. Qed.

  (** Make a the authorative element read-only. *)
  Lemma ghost_map_auth_persist γ dq m :
    ghost_map_auth γ dq m ==∗ ghost_map_auth γ DfracDiscarded m.
  Proof. unseal. iApply own_update. apply gmap_view_auth_persist. Qed.

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof. unseal. iApply own_update. apply gmap_view_frag_persist. Qed.

  (** * Lemmas about [ghost_map_auth] *)
  Lemma ghost_map_alloc_strong P m dq :
    pred_infinite P →
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_auth γ (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ]{dq} v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (gmap_view_auth (V:=leibnizO V) (DfracOwn 1) ∅) P)
      as (γ) "[% Hauth]"; first done.
    { apply gmap_view_auth_valid. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    etrans; first apply: (gmap_view_alloc_big (V:=leibnizO V) _ m dq).
    - apply map_disjoint_empty_r.
    - done.
    - rewrite right_id. done.
  Qed.
  Lemma ghost_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_auth γ (DfracOwn 1) (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc_strong P ∅ (DfracOwn 1)) as (γ) "(% & Hauth & _)";
              [done | done | eauto].
  Qed.
  Lemma ghost_map_alloc m :
    ⊢ |==> ∃ γ, ghost_map_auth γ (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    iMod (ghost_map_alloc_strong (λ _, True) m (DfracOwn 1)) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - done.
    - eauto.
  Qed.
  Lemma ghost_map_alloc_persistent m :
    ⊢ |==> ∃ γ, ghost_map_auth γ (DfracOwn 1) m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ]□ v.
  Proof.
    iMod (ghost_map_alloc_strong (λ _, True) m (DfracDiscarded)) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - done.
    - eauto.
  Qed.
  Lemma ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, ghost_map_auth γ (DfracOwn 1) (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance ghost_map_auth_timeless γ dq m : Timeless (ghost_map_auth γ dq m).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_auth_fractional γ m : Fractional (λ q, ghost_map_auth γ (DfracOwn q) m)%I.
  Proof. intros p q. unseal. rewrite -own_op -gmap_view_auth_dfrac_op //. Qed.
  Global Instance ghost_map_auth_as_fractional γ q m :
    AsFractional (ghost_map_auth γ (DfracOwn q) m) (λ q, ghost_map_auth γ (DfracOwn q) m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma ghost_map_auth_valid γ dq m : ghost_map_auth γ dq m -∗ ✓ dq.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%gmap_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma ghost_map_auth_valid_2 γ dq1 dq2 m1 m2 :
    ghost_map_auth γ dq1 m1 -∗ ghost_map_auth γ dq2 m2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_view_auth_dfrac_op_valid_L.
    done.
  Qed.
  Lemma ghost_map_auth_agree γ dq1 dq2 m1 m2 :
    ghost_map_auth γ dq1 m1 -∗ ghost_map_auth γ dq2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma ghost_map_lookup {γ dp m k dq v} :
    ghost_map_auth γ dp m -∗ k ↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %[?[??]]%gmap_view_both_dfrac_valid_L.
    eauto.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ (DfracOwn 1) m ==∗ ghost_map_auth γ (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ] v.
  Proof.
    unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: gmap_view_alloc; done.
  Qed.
  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ (DfracOwn 1) m ==∗ ghost_map_auth γ (DfracOwn 1) (<[k := v]> m) ∗ k ↪[γ]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_delete {γ m k v} :
    ghost_map_auth γ (DfracOwn 1) m -∗ k ↪[γ] v ==∗
    ghost_map_auth γ (DfracOwn 1) (delete k m).
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -own_op.
    iApply own_update. apply: gmap_view_delete.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ (DfracOwn 1) m -∗ k ↪[γ] v ==∗ ghost_map_auth γ (DfracOwn 1) (<[k := w]> m) ∗ k ↪[γ] w.
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -!own_op.
    apply own_update. apply: gmap_view_update.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma ghost_map_lookup_big {γ dp dq m} m0 :
    ghost_map_auth γ dp m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ]{dq} v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma ghost_map_insert_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ (DfracOwn 1) m ==∗
    ghost_map_auth γ (DfracOwn 1) (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ] v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op. iApply own_update.
    apply: gmap_view_alloc_big; done.
  Qed.
  Lemma ghost_map_insert_persist_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ (DfracOwn 1) m ==∗
    ghost_map_auth γ (DfracOwn 1) (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
  Proof.
    iIntros (Hdisj) "Hauth".
    iMod (ghost_map_insert_big m' with "Hauth") as "[$ Helem]"; first done.
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Helem").
    iIntros "!#" (k v) "_". iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_map_delete_big {γ m} m0 :
    ghost_map_auth γ (DfracOwn 1) m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ (DfracOwn 1) (m ∖ m0).
  Proof.
    iIntros "Hauth Hfrag". iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_delete_big.
  Qed.

  Theorem ghost_map_update_big {γ m} m0 m1 :
    dom m0 = dom m1 →
    ghost_map_auth γ (DfracOwn 1) m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ (DfracOwn 1) (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k ↪[γ] v.
  Proof.
    iIntros (?) "Hauth Hfrag". iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_update_big. done.
  Qed.

End lemmas.
