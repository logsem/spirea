(* The generational resources used by HighSpirea.
 *
 * The following resources are all [ghost_map loc V], and a crash
 * will only shrink the domain of the map, but never changes the value, and thus
 * share (most of) nextgen definition.
 * - the knowledge of protocols
 * - the knowledge of preorder
 * - the knowledge of bumper
 * - the knowledge of atomic and non-atomic locations
 * The following resources were maintained by highSpirea, but it's now maintained
 * in baseSpirea already and we only need to import the definitions:
 * - the offsets for each location
 * - the full physical history including messages from previous generation
 * The following resources require their own nextgen construction:
 * - the view for every non-atomic location (since they are not shared, there is always
 *   a single view one will access)
 * - the abstract history
 *)

From Equations Require Import Equations.
From iris.algebra Require Import gmap_view agree excl gset.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.proofmode Require Import classes tactics.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra map_extra view_slice encode_relation.
From self.nextgen Require Import hvec nextgen_promises.
From self.nextgen Require Import nextgen_promises.
From self.algebra Require Import view.
From self.base Require Import generational_resources.

From self.lang Require Import lang.

From self.high.lib Require Import abstract_state.
From self.high.resources Require Export gen_ghost_map gen_ghost_map_map gen_alocs gen_predicates auth_map_map abstract_history.

Class nvmHighG `{!nvmBaseG Σ Ω} := NvmHighG {
  nvm_predicatesG :> predicates_inG Σ Ω;
  (* TODO: after merge, this will be three ghost names *)
  predicates_name : gname;
  abs_historiesG :> ghost_map_mapG loc time positive Σ Ω;
  abs_history_name : gname;
  (* resharing [phy_history] for atomic locations *)
  phy_historiesG :> auth_map_mapR_inG Σ Ω (leibnizO message);
  phy_history_name : gname;
  non_atomic_views :> genC_ghost_map_inG loc view Σ Ω;
  non_atomic_views_gname : gname;
  crashed_in_inG :> genC_ghost_map_inG loc positive Σ Ω;
  crashed_in_name : gname;
  preordersG :> genC_ghost_map_inG loc (relation2 positive) Σ Ω;
  preorders_name : gname;
  locsG :> gen_alocsR_inG Σ Ω;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  nvm_bumpersG :> genC_ghost_map_inG loc (positive → option positive) Σ Ω;
  bumpers_name : gname;
}.

(* Wrappers around ownership of resources that extracts the ghost names from
   [nvmDeltaG]. These wrapper makes it easier to switch the ghost names around
   after a crash in [post_crash_modality.v]. *)
Section ownership_wrappers.
  Context `{nvmHighG}.

  (* We have these wrappers partly to avoid having to spell out the global ghost
  names, and partly such that we can conveniently swap them out by giving the
  named type class instance [nD] *)

  Definition know_encoded_bumper (ℓ : loc)
             (encoded_bumper : positive → option positive) : iProp Σ :=
    ℓ ↪[bumpers_name, loc_map_rel]□ encoded_bumper.

  (* TODO: fix preorder *)
  (* Definition know_preorder_loc `{Countable ST} ℓ (preorder : relation2 ST) : iProp Σ := *)
  (*   own_know_preorder_loc preorders_name ℓ preorder. *)

  Definition know_full_encoded_history_loc ℓ q enc_abs_hist : iProp Σ :=
    history_full_entry_encoded bumpers_name abs_history_name ℓ q enc_abs_hist.

  Definition know_full_history_loc `{Countable ST}
             ℓ q (abs_hist : gmap time ST) : iProp Σ :=
    full_entry_unenc bumpers_name abs_history_name ℓ q abs_hist.

  Definition know_frag_encoded_history_loc ℓ t e : iProp Σ :=
    frag_entry bumpers_name abs_history_name ℓ t e.

  Definition know_frag_history_loc `{Countable ST} ℓ t (s : ST) : iProp Σ :=
    frag_entry_unenc bumpers_name abs_history_name ℓ t s.

  (* physical history is now part of base logic *)
  Definition know_phys_hist_msg ℓ t msg : iProp Σ :=
    auth_map_map_frag_singleton phy_history_name ℓ t msg.

End ownership_wrappers.

Section location_sets.
  Context `{nvmHighG}.

  Implicit Types (locs : gset loc) (ℓ : loc).

  Lemma location_sets_singleton_included γ locs ℓ :
    gen_alocs_auth γ locs -∗ gen_alocs_frag γ {[ ℓ ]} -∗ ⌜ ℓ ∈ locs ⌝.
  Proof.
    iNamed 1. iNamed 1.
    iDestruct (gen_own_valid_2 with "own_auth own_frag")
      as %[V%gset_included _]%auth_both_valid_discrete.
    rewrite elem_of_subseteq_singleton.
    done.
  Qed.

  Lemma location_sets_lookup γ locs ℓ :
    ℓ ∈ locs → gen_alocs_frag γ locs -∗ gen_alocs_frag γ {[ ℓ ]}.
  Proof.
    intros.
    iNamed 1.
    iPoseProof (gen_own_mono _ _ (◯ {[ ℓ ]}) with "own_frag") as "own_frag".
    { apply auth_frag_mono. set_solver. }
    iExists OCV.
    iFrame "∗#".
  Qed.
End location_sets.


(* Resource algebra that stores the encoded preorder for each location. *)
Definition relationO := leibnizO (positive → positive → Prop).
(* Definition preordersG Σ := ghost_mapG Σ loc (relation2 positive). *)

Section preorders.
  Context `{nvmHighG}.

  Implicit Type (preorders : gmap loc (relation2 positive)).
  Context `{Countable A}.

  Definition own_all_preorders γ preorders :=
    ghost_map_auth γ loc_map_rel (DfracOwn 1) preorders.

  Definition own_know_preorder_loc γ ℓ (preorder : relation2 A) : iProp Σ :=
    ℓ ↪[γ, loc_map_rel]□ encode_relation preorder.

  Lemma own_all_preorders_gname_alloc (preorders : gmap loc (relation2 positive)) :
    ⊢ |==> ∃ γ,
      own_all_preorders γ preorders ∗ ([∗ map] ℓ ↦ p ∈ preorders, ℓ ↪[γ, loc_map_rel]□ p).
  Proof.
  Admitted.

  Lemma orders_lookup γ ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders γ orders -∗
    own_know_preorder_loc γ ℓ order2 -∗
    ⌜order1 = encode_relation order2⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (ghost_map_lookup with "auth frag") as "%".
    iPureIntro. congruence.
  Qed.

End preorders.

Section bumpers.
  Context `{AbstractState ST}.

  Definition encode_bumper (bumper : ST → ST) :=
    λ e, encode <$> (bumper <$> decode e).

  Lemma encode_bumper_Some_decode (bumper : ST → ST) (x x' : positive) :
    encode_bumper bumper x = Some x' →
    ∃ (s : ST), decode x = Some s ∧ encode (bumper s) = x'.
  Proof.
    rewrite /encode_bumper => eq.
    destruct (decode x) as [s|].
    - exists s. inversion eq. done.
    - inversion eq.
  Qed.

  Lemma encode_bumper_encode (bumper : ST → ST) (s : ST) :
    encode_bumper bumper (encode s) = Some (encode (bumper s)).
  Proof. rewrite /encode_bumper. rewrite decode_encode. done. Qed.

  (* An encoded bumper returns some encoded value then that encoded value will
  also result in some other encoded bumper again. This represents that encoded
  bumpers take "valid" encodings to "valid" encodings. *)
  Lemma encode_bumper_bump_to_valid bumper e e' :
    encode_bumper bumper e = Some e' → is_Some (encode_bumper bumper e').
  Proof.
    intros (s' & ? & encodeEq)%encode_bumper_Some_decode.
    rewrite <- encodeEq. rewrite encode_bumper_encode. done.
  Qed.

End bumpers.

Section own_encoded_bumpers.
  Context `{nvmHighG}.

  Definition own_all_bumpers γ (encoded_bumpers: gmap loc (positive → option positive)) :=
    ghost_map_auth γ loc_map_rel (DfracOwn 1) encoded_bumpers.

  (* TODO: *)
  Lemma own_all_bumpers_alloc bumpers :
    ⊢ |==> ∃ γ, own_all_bumpers γ bumpers ∗
                ([∗ map] ℓ ↦ bumper ∈ bumpers, ℓ ↪[γ, loc_map_rel]□ bumper).
  Proof. Admitted.

End own_encoded_bumpers.

Section own_bumpers.
  Context `{nvmHighG}.
  Context `{AbstractState ST}.

  Definition own_know_bumper γ (ℓ : loc) (bumper : ST → ST) : iProp Σ :=
    let encodedBumper := encode_bumper bumper
    in ⌜∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2⌝ ∗
       ℓ ↪[γ, loc_map_rel]□ encodedBumper.

  Lemma own_all_bumpers_persist γ encoded_bumpers :
    own_all_bumpers γ encoded_bumpers ==∗
    ghost_map_auth γ loc_map_rel DfracDiscarded encoded_bumpers.
  Proof. apply ghost_map_auth_persist. Qed.

  Lemma own_all_bumpers_insert (bumpers : gmap loc _) ℓ γ (bumper : ST → ST)
        `{!Proper ((⊑@{ST}) ==> (⊑))%signature bumper} :
    bumpers !! ℓ = None →
    own_all_bumpers γ bumpers ==∗
    own_all_bumpers γ (<[ℓ := encode_bumper bumper]>bumpers) ∗ own_know_bumper γ ℓ bumper.
  Proof.
    rewrite /own_all_bumpers /own_know_bumper. iIntros (look) "A".
    iMod (ghost_map_insert_persist with "A") as "[$ $]"; done.
  Qed.

  Definition bumperO := leibnizO (positive → option positive).

  Lemma bumpers_lookup γ ℓ encoded_bumpers bumper :
    own_all_bumpers γ encoded_bumpers -∗
    own_know_bumper γ ℓ bumper -∗
    ⌜ encoded_bumpers !! ℓ = Some (encode_bumper bumper) ⌝.
  Proof.
    iIntros "A [mono F]".
    iDestruct (ghost_map_lookup with "A F") as "$".
  Qed.

End own_bumpers.
