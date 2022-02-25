(* Resource algebra to represent abstract histories. *)

From iris.bi Require Import lib.fractional.
From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self.algebra Require Import ghost_map ghost_map_map.
From self.lang Require Import lang.
From self Require Import extra.
(* From self.high.resources Require Import auth_map_map. *)

(* For abstract history we need two types of fragmental knowledge. One that
represents ownership about the entire abstract history of a location (for
non-atomic) and one that represents only knowledge about one entry in the
abstract history. *)

(* Resource algebras that for each location stores the encoded abstract states
associated with each message/store. *)
(* Definition encoded_abs_historyR := gmapUR time (agreeR positiveO). *)

(* Definition know_abs_historiesR := auth_map_mapR positiveO. *)

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{ghost_map_mapG Σ loc time positive}.
  (* Context `{!ghost_mapG Σ loc (gmap time positive), inG Σ know_abs_historiesR}. *)
  Context `{Countable ST}.

  Implicit Types
    (abs_hist : gmap time ST) (ℓ : loc)
    (enc_abs_hist : gmap time positive)
    (abs_hists : gmap loc (gmap time positive)).

  (* Definition abs_hist_to_ra abs_hist : encoded_abs_historyR := *)
  (*   (to_agree ∘ encode) <$> abs_hist. *)

  (* If we own the full history then we own the authorative view of both the
  resource algebras. *)
  Definition history_full_map γ abs_hists : iProp Σ :=
    full_map γ (DfracOwn 1) abs_hists.

  Definition history_frag_entry γ ℓ t e : iProp Σ :=
    frag_entry γ ℓ t e.

  (* Definition history_frag_entry γ ℓ enc_abs_hist : iProp Σ := *)
  (*   full_entry γ ℓ enc_abs_hist. *)

  (* In this definition we store that decoding the stored encoded histry is
  equal to our abstract history. This is weaker than strogin the other way
  around, namely that encoding our history is equal to the stored encoded
  history. Storing this weaker fact makes the definition easier to show. This is
  important for the load lemma where, when we load some state and we want to
  return [store_lb] for the returned state. At that point we can conclude that
  decoding the encoding gives a result but not that the encoding is an encoding
  of some state. *)
  Definition history_frag_entry_unenc γ ℓ t (s : ST) : iProp Σ :=
    ∃ e, ⌜ decode e = Some s ⌝ ∗ history_frag_entry γ ℓ t e.

  Definition history_full_entry_encoded γ ℓ q enc_abs_hist : iProp Σ :=
    full_entry γ ℓ (DfracOwn q) enc_abs_hist.
    (* ℓ ↪[ γ ]{#q} enc_abs_hist ∗ *)
    (* history_frag_entry ℓ enc_abs_hist. *)

  Definition history_full_map_loc γ ℓ q abs_hist : iProp Σ :=
    history_full_entry_encoded γ ℓ q (encode <$> abs_hist).

  (* Global Instance own_full_encoded_history_fractional γ ℓ enc_abs_hist : *)
  (*   Fractional (λ q, history_full_entry_encoded γ ℓ q enc_abs_hist). *)
  (* Proof. apply _. *)
  (*   intros p q. *)
  (*   rewrite /history_full_entry_encoded. *)
  (*   iSplit. *)
  (*   - iIntros "[[$$] #?]". iFrame "#". *)
  (*   - iIntros "[[$ $] [$ _]]". *)
  (* Qed. *)
  (* Global Instance own_full_encoded_history_as_fractional γ ℓ q enc_abs_hist : *)
  (*   AsFractional *)
  (*     (history_full_entry_encoded γ ℓ q enc_abs_hist) *)
  (*     (λ q, history_full_entry_encoded γ ℓ q enc_abs_hist)%I q. *)
  (* Proof. split; [done | apply _]. Qed. *)

  Lemma history_full_map_loc_agree γ ℓ q p abs_hist1 abs_hist2 :
    history_full_map_loc γ ℓ q abs_hist1 -∗
    history_full_map_loc γ ℓ p abs_hist2 -∗
    ⌜ abs_hist1 = abs_hist2 ⌝.
  Proof.
    iIntros "[A _]". iIntros "[B _]".
    iDestruct (full_entry_agree with "A B") as %<-%(inj _). done.
  Qed.

  (* Lemma history_full_map_loc_to_frag γ ℓ q abs_hist : *)
  (*   history_full_map_loc γ ℓ q abs_hist -∗ *)
  (*   history_frag_entry_unenc γ ℓ abs_hist. *)
  (* Proof. *)
  (*   iIntros "[_ H]". iExists _. iFrame "H". *)
  (*   iPureIntro. *)
  (*   apply map_eq. intros t. *)
  (*   rewrite 3!lookup_fmap. *)
  (*   destruct (abs_hist !! t); last done. *)
  (*   simpl. rewrite decode_encode. done. *)
  (* Qed. *)

  (* Lemma history_frag_entry_unenc_lookup ℓ abs_hist t h : *)
  (*   abs_hist !! t = Some h → *)
  (*   history_frag_entry_unenc ℓ abs_hist -∗ *)
  (*   history_frag_entry_unenc ℓ {[ t := h ]}. *)
  (* Proof. *)
  (*   iIntros (look). *)
  (*   iIntros "(%m & %eq & H)". *)
  (*   setoid_rewrite map_eq_iff in eq. *)
  (*   specialize (eq t). *)
  (*   rewrite 2!lookup_fmap in eq. *)
  (*   rewrite look in eq. *)
  (*   simpl in eq. *)
  (*   rewrite -lookup_fmap in eq. *)
  (*   apply lookup_fmap_Some in eq as (e & dec & mLook). *)
  (*   iExists ({[ t := e ]}). *)
  (*   iDestruct (auth_map_map_frag_lookup_singleton with "H") as "$". *)
  (*   { rewrite lookup_singleton. done. } *)
  (*   { done. } *)
  (*   iPureIntro. *)
  (*   rewrite !map_fmap_singleton. *)
  (*   congruence. *)
  (* Qed. *)

  (* Lemma history_full_map_alloc h : *)
  (*   ⊢ |==> ∃ γ , *)
  (*     history_full_map γ h ∗ *)
  (*     (* auth_map_map_frag h ∗ *) *)
  (*     ([∗ map] k↦v ∈ h, *)
  (*       history_full_entry_encoded γ k 1 v ∗ *)
  (*       ([∗ map] k2 ↦ x ∈ v, history_frag_entry γ k k2 x)). *)
  (* Proof. *)
  (*   apply full_map_alloc. *)
  (*   (* iMod (ghost_map_alloc h) as (new_abs_history_name) "[A B]". *) *)
  (*   (* iExists _. iFrame "A B". *) *)
  (*   (* setoid_rewrite <- own_op. *) *)
  (*   (* iMod (own_alloc _) as "$". *) *)
  (*   (* { apply auth_both_valid_2; last reflexivity. *) *)
  (*   (*   intros k. *) *)
  (*   (*   rewrite lookup_fmap. *) *)
  (*   (*   case (h !! k); simpl; last done. *) *)
  (*   (*   intros ? k'. *) *)
  (*   (*   apply Some_valid. *) *)
  (*   (*   rewrite lookup_fmap. *) *)
  (*   (*   case (g !! k'); done. } *) *)
  (*   (* done. *) *)
  (* Qed. *)

  Lemma own_full_equiv γ ℓ q abs_hist :
    history_full_map_loc γ ℓ q abs_hist ⊣⊢
      history_full_entry_encoded γ ℓ q (encode <$> abs_hist).
  Proof. done. Qed.

  (* Lemma own_frag_equiv γ ℓ abs_hist : *)
  (*   history_frag_entry γ ℓ (encode <$> abs_hist) ⊢ *)
  (*   history_frag_entry_unenc γ ℓ abs_hist. *)
  (* Proof. *)
  (*   rewrite /history_frag_entry_unenc /history_frag_entry. *)
  (*   iIntros "H". *)
  (*   iExists _. iFrame. iPureIntro. *)
  (*   apply map_eq. intros t. *)
  (*   rewrite !lookup_fmap. *)
  (*   destruct (abs_hist !! t); last done. *)
  (*   simpl. by rewrite decode_encode. *)
  (* Qed. *)

  (* Lemma abs_hist_to_ra_inj hist hist' : *)
  (*   abs_hist_to_ra hist' ≡ abs_hist_to_ra hist → *)
  (*   hist' = hist. *)
  (* Proof. *)
  (*   intros eq. *)
  (*   apply: map_eq. intros t. *)
  (*   pose proof (eq t) as eq'. *)
  (*   rewrite !lookup_fmap in eq'. *)
  (*   destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq'; *)
  (*     try inversion eq'; auto. *)
  (*   simpl in eq'. *)
  (*   apply Some_equiv_inj in eq'. *)
  (*   apply to_agree_inj in eq'. *)
  (*   apply encode_inj in eq'. *)
  (*   rewrite eq'. *)
  (*   done. *)
  (* Qed. *)

  (* Lemma abs_hist_to_ra_agree hist hist' : *)
  (*   to_agree <$> hist' ≡ abs_hist_to_ra hist → hist' = encode <$> hist. *)
  (* Proof. *)
  (*   intros eq. *)
  (*   apply: map_eq. intros t. *)
  (*   pose proof (eq t) as eq'. *)
  (*   rewrite !lookup_fmap in eq'. *)
  (*   rewrite lookup_fmap. *)
  (*   destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq'; *)
  (*     try inversion eq'; auto. *)
  (*   simpl in eq'. simpl. *)
  (*   apply Some_equiv_inj in eq'. *)
  (*   apply to_agree_inj in eq'. *)
  (*   f_equiv. *)
  (*   apply eq'. *)
  (* Qed. *)

  (** If you know the full history for a location and own the "all-knowing"
  resource, then those two will agree. *)
  Lemma history_full_map_agree γ ℓ q hist hists :
    history_full_map γ hists -∗
    history_full_map_loc γ ℓ q hist -∗
    ⌜hists !! ℓ = Some (encode <$> hist)⌝.
  Proof.
    iIntros "A [B _]".
    iApply (full_map_full_entry with "A B").
  Qed.

  (* Lemma own_frag_history_agree γ ℓ (part_hist : gmap time ST) hists : *)
  (*   history_full_map γ hists -∗ *)
  (*   history_frag_entry_unenc ℓ part_hist -∗ *)
  (*   ⌜∃ hist, hists !! ℓ = Some (hist) ∧ *)
  (*           (Some <$> part_hist) ⊆ (decode <$> hist)⌝. *)
  (* Proof. *)
  (*   rewrite /history_full_map. *)
  (*   iIntros "[O A]". *)
  (*   iDestruct 1 as (enc) "[%eq K]". *)
  (*   iDestruct (own_valid_2 with "A K") as %[incl _]%auth_both_valid_discrete. *)
  (*   apply fmap_fmap_to_agree_singleton_included_l in incl. *)
  (*   destruct incl as [hist' [look incl]]. *)
  (*   iPureIntro. *)
  (*   exists hist'. *)
  (*   split. { apply leibniz_equiv. done. } *)
  (*   rewrite -eq. apply map_fmap_mono. done. *)
  (* Qed. *)

  Lemma history_full_map_frag_singleton_agreee γ ℓ t (s : ST) hists :
    history_full_map γ hists -∗
    history_frag_entry_unenc γ ℓ t s -∗
    ⌜∃ hist enc,
      hists !! ℓ = Some hist ∧ hist !! t = Some enc ∧ decode enc = Some s⌝.
  Proof.
    iIntros "H1 (% & % & H2)".
    iDestruct (full_map_frag_entry with "H1 H2") as %(mi & EQ & hq).
    iPureIntro. eexists _, _. split_and!; done.
  Qed.

  (* Lemma history_full_map_lookup γ abs_hists enc_abs_hist ℓ t s : *)
  (*   abs_hists !! ℓ = Some enc_abs_hist → *)
  (*   enc_abs_hist !! t = Some s → *)
  (*   history_full_map γ abs_hists ==∗ *)
  (*   history_full_map γ abs_hists ∗ *)
  (*   history_frag_entry γ ℓ t s. *)
  (* Proof. *)
  (*   iIntros (look1 look2). *)
  (*   iIntros "[M N]". *)
  (*   iMod (auth_map_map_lookup with "N") as "[N hip]"; try done. *)
  (*   iFrame. *)
  (*   done. *)
  (* Qed. *)

  Lemma own_frag_history_singleton_agreee γ ℓ t s1 s2 :
    history_frag_entry_unenc γ ℓ t s1 -∗
    history_frag_entry_unenc γ ℓ t s2 -∗
    ⌜ s1 = s2 ⌝.
  Proof.
    iDestruct 1 as (enc deq) "K".
    iDestruct 1 as (enc' deq') "K'".
    iDestruct (frag_entry_agree with "K K'") as %<-.
    iPureIntro. congruence.
  Qed.

  (* Lemma history_full_map_alloc_frag γ ℓ t encS (s : ST) hists hist : *)
  (*   hists !! ℓ = Some hist → *)
  (*   hist !! t = Some encS → *)
  (*   decode encS = Some s → *)
  (*   history_full_map γ hists ==∗ *)
  (*   history_full_map γ hists ∗ history_frag_entry_unenc γ ℓ {[ t := s ]}. *)
  (* Proof. *)
  (*   iIntros (look lookHist decEq) "M". *)
  (*   iMod (history_full_map_lookup with "M") as "[M hi]"; try done. *)
  (*   iFrame. iModIntro. *)
  (*   rewrite /history_frag_entry_unenc. *)
  (*   iExists {[ t := encS ]}. *)
  (*   rewrite /history_frag_entry. *)
  (*   rewrite !map_fmap_singleton. *)
  (*   rewrite decEq. *)
  (*   iFrame. *)
  (*   done. *)
  (* Qed. *)

  (* Insert a new location into an abstract history. *)
  (* Lemma history_full_map_history_insert_loc γ abs_hists ℓ enc_abs_hist : *)
  (*   abs_hists !! ℓ = None → *)
  (*   history_full_map γ abs_hists ==∗ *)
  (*   history_full_map γ (<[ℓ := enc_abs_hist]>abs_hists) ∗ *)
  (*   history_full_entry_encoded γ ℓ 1 enc_abs_hist. *)
  (*   (* history_frag_entry γ ℓ enc_abs_hist. *) *)
  (* Proof. apply full_map_insert. Qed. *)

  (* Insert a new message into an abstract history. *)
  (* Lemma own_full_encoded_history_insert γ ℓ t enc_abs_hist abs_hists encS : *)
  (*   enc_abs_hist !! t = None → *)
  (*   history_full_map γ abs_hists -∗ *)
  (*   history_full_entry_encoded γ ℓ 1 enc_abs_hist ==∗ *)
  (*   let enc_abs_hist' := <[t := encS]>enc_abs_hist *)
  (*   in history_full_map γ (<[ℓ := enc_abs_hist']>abs_hists) ∗ *)
  (*      history_full_entry_encoded γ ℓ 1 enc_abs_hist' ∗ *)
  (*      history_frag_entry γ ℓ t encS. *)
  (* Proof. apply full_map_full_entry_insert. Qed. *)

  (* Insert a new message into an abstract history. *)
  (* Lemma history_full_map_insert γ ℓ t abs_hist abs_hists (s : ST) : *)
  (*   abs_hist !! t = None → *)
  (*   history_full_map γ abs_hists -∗ *)
  (*   history_full_map_loc γ ℓ 1 abs_hist ==∗ *)
  (*   let abs_hist' := <[t := s]>abs_hist *)
  (*   in history_full_map γ (<[ℓ := encode <$> abs_hist']>abs_hists) ∗ *)
  (*      history_full_map_loc γ ℓ 1 abs_hist' ∗ *)
  (*      history_frag_entry_unenc γ ℓ t s. *)
  (* Proof. *)
  (*   iIntros (look) "??". *)
  (*   iMod (own_full_encoded_history_insert with "[$] [$]") as "(H1 & H2 & H3)". *)
  (*   { rewrite lookup_fmap. apply fmap_None. done. } *)
  (*   iModIntro. *)
  (*   rewrite /history_full_map_loc /history_frag_entry_unenc fmap_insert. *)
  (*   iFrame "H1 H2". *)
  (*   iExists _. iFrame. *)
  (*   iPureIntro. rewrite decode_encode. done. *)
  (* Qed. *)

End abs_history_lemmas.
