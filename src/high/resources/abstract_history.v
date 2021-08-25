(* Resource algebra to store the abstract histories. *)

From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import own ghost_map.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self.lang Require Import lang.
From self Require Import extra.

(* Resource algebras that for each location stores the encoded abstract states
associated with each message/store. *)
Definition encoded_abs_historyR := gmapUR time (agreeR positiveO).
(* Definition enc_abs_histories := gmap loc (gmap time positive). *)

Definition know_abs_historiesR :=
  authR (gmapUR loc (gmapUR time (agreeR positiveO))).

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{!ghost_mapG Σ loc (gmap time positive), inG Σ know_abs_historiesR}.
  Context `{Countable ST}.

  Implicit Types
    (abs_hist : gmap time ST) (ℓ : loc)
    (enc_abs_hist : gmap time positive)
    (abs_hists : gmap loc (gmap time positive)).

  Definition abs_hist_to_ra abs_hist : encoded_abs_historyR :=
    (to_agree ∘ encode) <$> abs_hist.

  (* If we own the full history then we own the authorative view of both the
  resource algebras. *)
  Definition own_full_history γ1 γ2 abs_hists : iProp Σ :=
    ghost_map_auth γ1 1 abs_hists ∗
    own γ2 (
      ● ((λ m : gmap _ _, to_agree <$> m) <$> abs_hists) : know_abs_historiesR
    ).

  (* Definition own_full_history abs_hists : iProp Σ := *)
  (*   own_full_history abs_history_name know_abs_history_name abs_hists. *)

  Definition own_full_encoded_history_loc γ ℓ enc_abs_hist : iProp Σ :=
    ℓ ↪[ γ ] enc_abs_hist.

  Definition own_full_history_loc γ ℓ abs_hist : iProp Σ :=
    ℓ ↪[ γ ] (encode <$> abs_hist).

  Definition own_frag_encoded_history_loc γ ℓ enc_abs_hist : iProp Σ :=
    own γ (◯ {[ ℓ := to_agree <$> enc_abs_hist ]}).

  (* In this definition we store that decoding the stored encoded histry is
  equal to our abstract history. This is weaker than strong the other way
  around, namely that encoding our history is equal to the stored encoded
  history. Storing this weaker fact makes the definition easier to show. This is
  important for the load lemma where, when we load some state and we want to
  return [know_store_lb] for the returned state. At that point we can
  conclude that decoding the encoding gives a result but not that the encoding
  is an encoding of some state. *)
  Definition own_frag_history_loc γ ℓ (abs_hist : gmap time ST) : iProp Σ :=
    ∃ enc,
      ⌜decode <$> enc = Some <$> abs_hist⌝ ∗
      (* ⌜enc = encode <$> abs_hist⌝ ∗ *)
      own_frag_encoded_history_loc γ ℓ enc.

  Lemma own_full_history_alloc h :
    ⊢ |==> ∃ γ1 γ2,
        own_full_history γ1 γ2 h ∗
        own γ2 (◯ ((λ m : gmap _ _, to_agree <$> m) <$> h) : know_abs_historiesR) ∗
        [∗ map] k↦v ∈ h, k ↪[γ1] v.
  Proof.
    iMod (ghost_map_alloc h) as (new_abs_history_name) "[A B]".
    iExists _. iFrame "A B".
    setoid_rewrite <- own_op.
    iMod (own_alloc _) as "$".
    { apply auth_both_valid_2; last reflexivity.
      intros k.
      rewrite lookup_fmap.
      destruct (h !! k); simpl; last done.
      apply Some_valid.
      intros k'.
      rewrite lookup_fmap.
      destruct (g !! k'); done. }
    done.
  Qed.

  Lemma own_full_equiv γ ℓ abs_hist :
    own_full_history_loc γ ℓ abs_hist ⊣⊢
      own_full_encoded_history_loc γ ℓ (encode <$> abs_hist).
  Proof. done. Qed.

  Lemma own_frag_equiv γ ℓ abs_hist :
    own_frag_encoded_history_loc γ ℓ (encode <$> abs_hist) ⊢
    own_frag_history_loc γ ℓ abs_hist.
  Proof.
    rewrite /own_frag_history_loc /own_frag_encoded_history_loc.
    iIntros "H".
    iExists _. iFrame. iPureIntro.
    apply map_eq. intros t.
    rewrite !lookup_fmap.
    destruct (abs_hist !! t); last done.
    simpl. by rewrite decode_encode.
  Qed.

  Lemma abs_hist_to_ra_inj hist hist' :
    abs_hist_to_ra hist' ≡ abs_hist_to_ra hist →
    hist' = hist.
  Proof.
    intros eq.
    apply: map_eq. intros t.
    pose proof (eq t) as eq'.
    rewrite !lookup_fmap in eq'.
    destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq';
      try inversion eq'; auto.
    simpl in eq'.
    apply Some_equiv_inj in eq'.
    apply to_agree_inj in eq'.
    apply encode_inj in eq'.
    rewrite eq'.
    done.
  Qed.

  Lemma abs_hist_to_ra_agree hist hist' :
    to_agree <$> hist' ≡ abs_hist_to_ra hist → hist' = encode <$> hist.
  Proof.
    intros eq.
    apply: map_eq. intros t.
    pose proof (eq t) as eq'.
    rewrite !lookup_fmap in eq'.
    rewrite lookup_fmap.
    destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq';
      try inversion eq'; auto.
    simpl in eq'. simpl.
    apply Some_equiv_inj in eq'.
    apply to_agree_inj in eq'.
    f_equiv.
    apply eq'.
  Qed.

  (** If you know the full history for a location and own the "all-knowing"
  resource, then those two will agree. *)
  Lemma own_full_history_agree γ1 γ2 ℓ hist hists :
    own_full_history γ1 γ2 hists -∗
    own_full_history_loc γ1 ℓ hist -∗
    ⌜hists !! ℓ = Some (encode <$> hist)⌝.
  Proof.
    iIntros "[A _] B".
    iApply (ghost_map_lookup with "[$] [$]").
  Qed.

  Lemma own_frag_history_agree γ1 γ2 ℓ (part_hist : gmap time ST) hists :
    own_full_history γ1 γ2 hists -∗
    own_frag_history_loc γ2 ℓ part_hist -∗
    ⌜∃ hist, hists !! ℓ = Some (hist) ∧
            (Some <$> part_hist) ⊆ (decode <$> hist)⌝.
  Proof.
    rewrite /own_full_history.
    iIntros "[O A]".
    iDestruct 1 as (enc) "[%eq K]".
    iDestruct (own_valid_2 with "A K") as %[incl _]%auth_both_valid_discrete.
    apply singleton_included_l in incl.
    destruct incl as [hist' [look incl]].
    rewrite lookup_fmap in look.
    destruct (hists !! ℓ) as [hist|]. 2: { inversion look. }
    simpl in look.
    iExists hist.
    iSplit; first done.
    rewrite <- eq.
    move: incl.
    rewrite <- look.
    rewrite Some_included_total.
    rewrite -to_agree_fmap.
    intros incl.
    iPureIntro.
    by apply map_fmap_mono.
  Qed.

  Lemma own_frag_history_agree_singleton γ1 γ2 ℓ t (s : ST) hists :
    own_full_history γ1 γ2 hists -∗
    own_frag_history_loc γ2 ℓ {[ t := s ]} -∗
    ⌜∃ hist enc,
      hists !! ℓ = Some hist ∧ hist !! t = Some enc ∧ decode enc = Some s⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_frag_history_agree with "H1 H2") as %[hist [look H1]].
    iExists hist. iPureIntro.
    rewrite map_fmap_singleton in H1.
    rewrite -> map_subseteq_spec in H1.
    specialize H1 with t (Some s).
    epose proof (H1 _) as H2.
    Unshelve. 2: { rewrite lookup_singleton. done. }
    apply lookup_fmap_Some in H2.
    destruct H2 as (enc & eq & lookHist).
    exists enc.
    repeat split; done.
  Qed.

  Lemma own_full_history_alloc_frag γ1 γ2 ℓ t encS (s : ST) hists hist :
    hists !! ℓ = Some hist →
    hist !! t = Some encS →
    decode encS = Some s →
    own_full_history γ1 γ2 hists ==∗
    own_full_history γ1 γ2 hists ∗ own_frag_history_loc γ2 ℓ {[ t := s ]}.
  Proof.
    iIntros (look lookHist decEq) "[$ H2]".
    rewrite /own_full_history /own_frag_history_loc.
    iMod (own_update with "H2") as "[$ H]".
    { apply (auth_update_dfrac_alloc _ _ {[ ℓ := {[ t := to_agree encS ]} ]}).
      apply singleton_included_l.
      eexists _.
      rewrite lookup_fmap.
      rewrite look.
      simpl.
      split; first reflexivity.
      rewrite /abs_hist_to_ra.
      apply Some_included_total.
      apply singleton_included_l.
      eexists _.
      rewrite lookup_fmap.
      rewrite lookHist.
      simpl.
      split; f_equiv. }
    iExists {[ t := encS ]}.
    rewrite /own_frag_encoded_history_loc.
    rewrite !map_fmap_singleton.
    rewrite decEq.
    iFrame.
    done.
  Qed.

  (* This lemma seems false :'( *)
  (* Lemma own_frag_history_agree ℓ part_hist hists : *)
  (*   own_full_history hists -∗ *)
  (*   know_frag_history_loc ℓ part_hist -∗ *)
  (*   ⌜∃ hist, hists !! ℓ = Some (encode <$> hist) ∧ part_hist ⊆ hist⌝. *)
  (* Proof. w w *)
  (*   iIntros "O K". *)
  (* Admitted. *)

End abs_history_lemmas.
