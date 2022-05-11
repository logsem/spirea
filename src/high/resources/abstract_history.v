(* Ghost state to represent abstract histories. This is just a few extra
definitions and lemmas on top of [ghost_map_map]. *)

From iris.bi Require Import lib.fractional.
From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self.algebra Require Import ghost_map ghost_map_map.
From self.lang Require Import lang.
From self Require Import extra ipm_tactics.

(* For abstract history we need two types of fragmental knowledge. One that
represents ownership about the entire abstract history of a location (for
non-atomic) and one that represents only knowledge about one entry in the
abstract history. *)

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{ghost_map_mapG Σ loc time positive}.
  Context `{Countable ST}.

  Implicit Types
    (abs_hist : gmap time ST) (ℓ : loc)
    (enc_abs_hist : gmap time positive)
    (abs_hists : gmap loc (gmap time positive)).

  (* In this definition we store that decoding the stored encoded histry is
  equal to our abstract history. This is weaker than strogin the other way
  around, namely that encoding our history is equal to the stored encoded
  history. Storing this weaker fact makes the definition easier to show. This is
  important for the load lemma where, when we load some state and we want to
  return [store_lb] for the returned state. At that point we can conclude that
  decoding the encoding gives a result but not that the encoding is an encoding
  of some state. *)
  Definition frag_entry_unenc γ ℓ t (s : ST) : iProp Σ :=
    ∃ e, ⌜ decode e = Some s ⌝ ∗ frag_entry γ ℓ t e.

  Definition history_full_entry_encoded γ ℓ q enc_abs_hist : iProp Σ :=
    full_entry γ ℓ (DfracOwn q) enc_abs_hist.

  Definition full_entry_unenc γ ℓ q abs_hist : iProp Σ :=
    full_entry γ ℓ (DfracOwn q) (encode <$> abs_hist).

  Lemma full_entry_unenc_agree γ ℓ q p abs_hist1 abs_hist2 :
    full_entry_unenc γ ℓ q abs_hist1 -∗
    full_entry_unenc γ ℓ p abs_hist2 -∗
    ⌜ abs_hist1 = abs_hist2 ⌝.
  Proof.
    iIntros "[A _]". iIntros "[B _]".
    iDestruct (full_entry_agree with "A B") as %<-%(inj _). done.
  Qed.

  Lemma own_full_equiv γ ℓ q abs_hist :
    full_entry_unenc γ ℓ q abs_hist ⊣⊢
      history_full_entry_encoded γ ℓ q (encode <$> abs_hist).
  Proof. done. Qed.

  Lemma frag_history_equiv γ ℓ t s :
    frag_entry γ ℓ t (encode s) -∗
    frag_entry_unenc γ ℓ t s.
  Proof. iIntros "H". iExists _. iFrame. rewrite decode_encode. done. Qed.

  Lemma full_map_frag_singleton_agreee γ dq ℓ t (s : ST) hists :
    full_map γ dq hists -∗
    frag_entry_unenc γ ℓ t s -∗
    ⌜∃ hist enc,
      hists !! ℓ = Some hist ∧ hist !! t = Some enc ∧ decode enc = Some s⌝.
  Proof.
    iIntros "H1 (% & % & H2)".
    iDestruct (full_map_frag_entry with "H1 H2") as %(mi & EQ & hq).
    iPureIntro. eexists _, _. split_and!; done.
  Qed.

  Lemma history_full_entry_frag_lookup γ q ℓ enc_abs_hist t (s : ST) :
    history_full_entry_encoded γ ℓ q enc_abs_hist -∗
    frag_entry_unenc γ ℓ t s -∗
    ⌜∃ enc,
      enc_abs_hist !! t = Some enc ∧ decode enc = Some s⌝.
  Proof.
    rewrite /history_full_entry_encoded.
    iIntros "H1 (% & % & H2)".
    iDestruct (full_entry_frag_entry with "H1 H2") as %look.
    iPureIntro. eexists _. split_and!; done.
  Qed.

  Lemma history_full_entry_frag_lookup_big γ q ℓ enc_abs_hist hist :
    history_full_entry_encoded γ ℓ q enc_abs_hist -∗
    ([∗ map] t↦s ∈ hist, frag_entry_unenc γ ℓ t s) -∗
    ⌜ ∃ hist_enc,
      hist_enc ⊆ enc_abs_hist ∧
      dom (gset _) hist = dom _ hist_enc ∧
      map_Forall (λ k enc, ∃ s, decode enc = Some s ∧
                                hist !! k = Some s) hist_enc ⌝.
  Proof.
    iIntros "F M".
    rewrite /frag_entry_unenc.
    iDestruct (big_sepM_exist_r with "M") as (hist_enc) "M".
    iDestruct (full_entry_lookup_big _ _ _ _ hist_enc with "F [M]") as %sub.
    { iApply big_sepM_forall.
      iIntros (???).
      iDestruct (big_sepM2_lookup_r with "M") as (???) "$"; first done. }
    iExists hist_enc.
    iSplit; first done.
    iDestruct (big_sepM2_dom with "M") as %domeq.
    iSplit; first done.
    iIntros (?? look).
    iDestruct (big_sepM2_lookup_r with "M") as (???) "hih"; first done.
    iExists x1. done.
  Qed.

  Lemma own_frag_history_singleton_agreee γ ℓ t s1 s2 :
    frag_entry_unenc γ ℓ t s1 -∗
    frag_entry_unenc γ ℓ t s2 -∗
    ⌜ s1 = s2 ⌝.
  Proof.
    iDestruct 1 as (enc deq) "K".
    iDestruct 1 as (enc' deq') "K'".
    iDestruct (frag_entry_agree with "K K'") as %<-.
    iPureIntro. congruence.
  Qed.

  Lemma full_entry_frag_entry_unenc γ ℓ q abs_hist t s :
    full_entry_unenc γ ℓ q abs_hist -∗
    frag_entry_unenc γ ℓ t s -∗
    ⌜ abs_hist !! t = Some s ⌝.
  Proof.
    iIntros "A B".
    iDestruct ("B") as (e decEq) "B".
    iDestruct (full_entry_frag_entry with "A B") as %look.
    apply lookup_fmap_Some in look as (s' & encEq & look).
    assert (s = s') as <-.
    { rewrite -encEq decode_encode in decEq. by inversion decEq. }
    done.
  Qed.

End abs_history_lemmas.
