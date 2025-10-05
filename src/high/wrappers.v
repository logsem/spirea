(** This file contains several wrapper definitions and their lemmas
 ** base logic to high logic.

 ** In spirea 1.0, wrappers were defined so that one can swap out the
 ** ghost names easily. Even though that is no longer necessary, I'm redefining
 ** them in similar shapes for minimal proof changes.

 ** A key difference between spirea 1.0 and spirea 2.0 wrappers is that I decide to use
 ** [⎡ P ⎤] whenever possible. This wasn't possible because generational ghost names were
 ** part of the [BiIndex]. *)
From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From iris.algebra Require Import gset.
From self Require Import extra encode_relation.
From self.high.lib Require Import abstract_state.

From iris.bi.lib Require Import fractional.
From self.nextgen Require Import nextgen_promises.
From self.high Require Export generational_resources.

(* For some reason [iris.algebra.view.view] always triumph the in-house definition. *)
From self.algebra Require Export view.

Set Default Proof Using "Type*".

Section BaseLifting.
  Context `{nvmBaseGS}.

  Definition offset_loc ℓ (t : nat) : iProp Σ :=
    ∃ OCV, crashed_at_offset OCV ∗ ⌜ OCV !! ℓ = Some $ MaxNat t ⌝.

  Lemma offset_loc_agree ℓ t1 t2 :
    offset_loc ℓ t1 -∗
    offset_loc ℓ t2 -∗
    ⌜ t1 = t2 ⌝.
  Proof.
    rewrite /offset_loc.
    iIntros "(% & ? & %) (% & ? & %)".
    iDestruct (crashed_at_offset_agree with "[$] [$]") as "%".
    by simplify_map_eq.
  Qed.

  Lemma offset_loc_crashed_at_agree ℓ t OCV :
    offset_loc ℓ t -∗
    crashed_at_offset (MaxNat <$> OCV) -∗
    ⌜ OCV !! ℓ = Some $ t ⌝.
  Proof.
    iIntros "(%OCV' & offset1 & %look) offset2".
    iDestruct (crashed_at_offset_agree with "offset1 offset2") as "->".
    rewrite lookup_fmap in look.
    destruct (OCV !! ℓ) eqn:Heqn; simpl in look; by simplify_eq.
  Qed.

  (* (* although the offset never decreases and thus a stronger lemma should be correct, *)
  (*  * the way [crashed_at_trans] is defined right now doesn't guarantee that. *) *)
  (* Global Instance offset_loc_into_nextgen ℓ t: *)
  (*   IntoNextgen *)
  (*   (offset_loc ℓ t) *)
  (*   (∃ t', offset_loc ℓ t'). *)
  (* Proof. *)
  (*   rewrite /IntoNextgen. *)
  (*   iIntros "offset !>". *)
  (*   iDestruct "offset" as (OCV) "[(%OV & %trans & picked & offset) %]". *)

End BaseLifting.

Section location_sets.
  Context `{nvmHighGS}.
  Implicit Types (locs : gset loc) (ℓ : loc).

  Definition is_at_loc ℓ : iProp Σ :=
    gen_alocs_frag shared_locs_name {[ ℓ ]}.
  Definition is_na_loc ℓ : iProp Σ :=
    gen_alocs_frag exclusive_locs_name {[ ℓ ]}.

  Lemma location_sets_singleton_included {γ} locs ℓ :
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

Section preorders.
  Context `{nvmHighGS}.

  Implicit Type (preorders : gmap loc (relation2 positive)).
  Context `{Countable ST}.

  Definition own_all_preorders γ preorders :=
    ghost_map_auth γ loc_map_rel (DfracOwn 1) preorders.

  Definition own_know_preorder_loc γ ℓ (preorder : relation2 ST) : iProp Σ :=
    ℓ ↪[γ, loc_map_rel]□ encode_relation preorder.

  Definition know_preorder_loc ℓ (preorder : relation2 ST) : iProp Σ :=
    own_know_preorder_loc preorders_name ℓ preorder.

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

(* Pure facts about bumpers *)
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
  Context `{nvmHighGS}.

  Definition own_all_bumpers γ (encoded_bumpers: gmap loc (positive → option positive)) :=
    ghost_map_auth γ loc_map_rel (DfracOwn 1) encoded_bumpers.

  (* TODO: *)
  Lemma own_all_bumpers_alloc bumpers :
    ⊢ |==> ∃ γ, own_all_bumpers γ bumpers ∗
                ([∗ map] ℓ ↦ bumper ∈ bumpers, ℓ ↪[γ, loc_map_rel]□ bumper).
  Proof. Admitted.

End own_encoded_bumpers.

Section own_bumpers.
  Context `{nvmHighGS} `{AbstractState ST}.

  Definition own_know_bumper γ (ℓ : loc) (bumper : ST → ST) : iProp Σ :=
    let encodedBumper := encode_bumper bumper
    in ⌜∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2⌝ ∗
       ℓ ↪[γ, loc_map_rel]□ encodedBumper.

  Definition know_bumper ℓ (bumper : ST → ST) : iProp Σ :=
    own_know_bumper bumpers_name ℓ bumper.

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

Section NAView.
  Context `{nvmHighGS}.

  Definition know_na_view ℓ q (SV : view) : iProp Σ :=
    ℓ ↪[non_atomic_views_gname, loc_map_rel]{#q} SV%I.

  Lemma know_na_view_agree ℓ p q V V' :
    know_na_view ℓ q V -∗
    know_na_view ℓ p V' -∗
    ⌜ V = V' ⌝.
  Proof.
    iApply (ghost_map_elem_agree _ _ _ _ _ V).
  Qed.

  Global Instance know_na_view_fractional ℓ V :
    Fractional (λ q, know_na_view ℓ q V).
  Proof. apply _. Qed.

  Global Instance know_na_view_as_fractional ℓ V q :
    AsFractional (know_na_view ℓ q V)
      (λ q, know_na_view ℓ q V) q.
  Proof. apply _. Qed.
End NAView.

(* so that iDestruct will prioritize fractional lemma over splitting [gen_own] *)
#[global] Opaque know_na_view.

(* TODO: replace this definition with [picked_in] of abstract history *)
Section crashed_in.
  Context `{nvmHighGS}.
  Context `{Countable ST}.

  (* [crashed_in ℓ s] means location [ℓ] crashed in (latest) abstract state [s]
   * (before applying bumper). *)
  Definition crashed_in ℓ (s : ST) : iProp Σ :=
    ∃ es, ⌜ decode es = Some s ⌝ ∗ ℓ ↪[crashed_in_name, loc_map_rel]□ es.
End crashed_in.

Section Histories.
  Context `{nvmHighGS}.

  Definition know_full_encoded_history_loc ℓ q enc_abs_hist : iProp Σ :=
    history_full_entry_encoded bumpers_name abs_history_name ℓ q enc_abs_hist.

  Definition know_frag_encoded_history_loc ℓ t e : iProp Σ :=
    frag_entry bumpers_name abs_history_name ℓ t e.

  Definition know_phys_hist_msg ℓ t msg : iProp Σ :=
    auth_map_map_frag_singleton phy_history_name ℓ t msg.

  Context `{Countable ST}.

  Definition know_full_history_loc `{Countable ST}
             ℓ q (abs_hist : gmap time ST) : iProp Σ :=
    full_entry_unenc bumpers_name abs_history_name ℓ q abs_hist.

  Definition know_frag_history_loc `{Countable ST} ℓ t (s : ST) : iProp Σ :=
    frag_entry_unenc bumpers_name abs_history_name ℓ t s.

  Lemma know_full_entry_frag_entry_unenc ℓ q abs_hist t s :
    know_full_history_loc ℓ q abs_hist -∗
    know_frag_history_loc ℓ t s -∗
    ⌜ abs_hist !! t = Some s ⌝.
  Proof.
    rewrite /know_full_history_loc.
    rewrite /know_frag_history_loc.
    iApply full_entry_frag_entry_unenc.
  Qed.

  Lemma know_full_history_loc_agree ℓ p q (abs_hist1 abs_hist2 : gmap nat ST) :
    know_full_history_loc ℓ p abs_hist1 -∗
    know_full_history_loc ℓ q abs_hist2 -∗
    ⌜ abs_hist1 = abs_hist2 ⌝.
  Proof.
    iApply full_entry_unenc_agree.
  Qed.

  Global Instance know_full_history_loc_fractional ℓ (abs_hist : gmap nat ST) :
    Fractional (λ q, know_full_history_loc ℓ q abs_hist).
  Proof. apply _. Qed.

  Global Instance know_full_history_loc_as_fractional ℓ (abs_hist : gmap nat ST) q :
    AsFractional (know_full_history_loc ℓ q abs_hist)
      (λ q, know_full_history_loc ℓ q abs_hist) q.
  Proof. apply _. Qed.
End Histories.
