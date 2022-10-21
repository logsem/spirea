From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self.lang Require Import lang.
From self.high Require Export resources dprop.

Section predicates.
  Context `{!nvmG Σ, hGD : nvmDeltaG}.

  (* Note, there are three types for predicates.
     1/ The real/initial type which depends on some [ST]: *)
  Definition predicate ST := ST → val → dProp Σ.
  Canonical Structure predicateO ST := ST -d> val -d> dPropO Σ.

  (* 2/ The encoded type that doesnt depend on [ST]: *)
  Definition enc_predicate := positive → val → option (dProp Σ).
  Definition enc_predicateO := positive -d> val -d> optionO (dPropO Σ).

  (* 3/ The unwrapped type where we project out of [dProp], forgets that it is
        monotone, and end up with [thread_view → iProp Σ]: *)
  Definition unwrapped_predicate :=
    positive → val → option (thread_view * nvmDeltaG → iProp Σ).
  Canonical Structure unwrapped_predicateO :=
    positive -d> val -d> optionO (thread_view * nvmDeltaG -d> iPropO Σ).

  Definition predO :=
    positive -d> val -d> optionO (thread_view * nvmDeltaG -d> iPropO Σ).

  (* Unfold the [dProp] and forget about monotonicity. *)
  Definition encoded_pred_unwrap
    (pred : enc_predicate) : unwrapped_predicate :=
      λ s v, (λ p i, monPred_at p i) <$> (pred s v).

  Definition encoded_pred_unwrap'
    (pred : enc_predicateO) : predO :=
      λ s v, (λ p i, monPred_at p i) <$> (pred s v).

  Definition unwrapped_pred_to_ra (pred : unwrapped_predicateO) :
    (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  Definition pred_to_ra (pred : enc_predicateO) : (@predicateR Σ) :=
    unwrapped_pred_to_ra (encoded_pred_unwrap pred).

  Global Instance enoded_pred_unwrap_proper :
    ∀ n, Proper (@dist enc_predicateO _ n ==> @dist predO _ n) encoded_pred_unwrap.
  Proof.
    intros ? p1 p2 eq.
    rewrite /encoded_pred_unwrap.
    simpl.
    intros e v.
    specialize (eq e v).
    destruct (p1 e v); destruct (p2 e v); simpl;
      [ |inversion eq|inversion eq|done].
    apply Some_dist_inj in eq.
    constructor.
    intros ?.
    apply eq.
  Qed.

  Global Instance pred_to_ra_ne :
    ∀ n, Proper (@dist enc_predicateO _ n ==> dist n) pred_to_ra.
  Proof.
    intros ??? eq.
    rewrite /pred_to_ra.
    rewrite /pred_to_ra.
    rewrite /unwrapped_pred_to_ra.
    apply (@to_agree_ne (positive -d> val -d> laterO (optionO (index -d> (iPropO Σ))))).
    intros ??.
    eassert (NonExpansive Next) as ne; last apply ne; first by apply _.
    apply enoded_pred_unwrap_proper in eq.
    specialize (eq x0).
    apply eq.
  Qed.

  Definition preds_to_ra (preds : gmap loc (enc_predicate))
    : gmapUR loc (@predicateR Σ) := pred_to_ra <$> preds.

  Definition own_all_preds dq preds :=
    own predicates_name (●{dq} (preds_to_ra preds) : predicatesR).

  Definition encode_predicate `{Countable ST} (ϕ : predicateO ST)
    : enc_predicateO :=
    λ encS v, (λ s, ϕ s v) <$> decode encS.

  Definition predicate_to_unwrapped_predicate `{Countable ST} (ϕ : predicate ST)
    : unwrapped_predicate :=
    encoded_pred_unwrap (encode_predicate ϕ).

  Definition know_pred `{Countable ST} ℓ (ϕ : predicateO ST) : iProp Σ :=
    own predicates_name
        (◯ {[ ℓ := unwrapped_pred_to_ra (predicate_to_unwrapped_predicate ϕ) ]}).

  Local Instance unwrapped_pred_to_ra_contractive :
    Contractive unwrapped_pred_to_ra.
  Proof.
    rewrite /pred_to_ra.
    rewrite /unwrapped_pred_to_ra.
    intros ????.
    apply (@to_agree_ne (positive -d> val -d> laterO (optionO (index -d> (iPropO Σ))))).
    intros ??.
    destruct n; first done.
    apply (contractive_S Next).
    apply (H x0 x1).
  Qed.

  Local Instance pred_to_ra_contractive :
    Contractive (pred_to_ra).
  Proof. solve_contractive. Qed.

  Global Instance encode_predicate_ne `{Countable ST} :
    NonExpansive (encode_predicate (ST := ST)).
  Proof.
    rewrite /encode_predicate.
    intros ??????.
    simpl.
    destruct (decode x0); simpl; last done.
    f_equiv.
    apply (H0 _ _).
  Qed.

  Global Instance know_pred_contractive `{Countable ST} ℓ :
    Contractive (know_pred (ST := ST) ℓ).
  Proof.
    intros ????.
    rewrite /know_pred.
    do 3 f_equiv.
    f_contractive.
    apply enoded_pred_unwrap_proper.
    simpl in H0.
    rewrite H0.
    f_equiv.
  Qed.

  Lemma encode_predicate_extract `{Countable ST}
      (ϕ : predicate ST) e s v
      (P : dPropO Σ) i :
    decode e = Some s →
    (encode_predicate ϕ e v : optionO (dPropO Σ)) ≡ Some P -∗
    P i -∗
    ϕ s v i.
  Proof.
    rewrite /encode_predicate.
    iIntros (->) "equiv".
    simpl.
    rewrite option_equivI.
    iRewrite "equiv".
    iIntros "$".
  Qed.

  Lemma encode_predicate_extract_L `{Countable ST}
        (ϕ : ST → val → dProp Σ) e s v P i :
    decode e = Some s →
    encode_predicate ϕ e v = Some P →
    P i -∗
    ϕ s v i.
  Proof. rewrite /encode_predicate. iIntros (-> [= <-]). done. Qed.

  Lemma know_predicates_alloc preds :
    ⊢ |==> ∃ γ,
          own γ ((● (pred_to_ra <$> preds)) : predicatesR) ∗
          own γ ((◯ (pred_to_ra <$> preds)) : predicatesR).
  Proof.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_2; last reflexivity.
    intros ℓ.
    rewrite lookup_fmap.
    by case (preds !! ℓ).
  Qed.

  Lemma encoded_pred_unwrap_inj state v o1 o2 :
    ⊢@{iPropI Σ} encoded_pred_unwrap o1 state v
        ≡@{optionO (index -d> iPropO Σ)}
        encoded_pred_unwrap o2 state v -∗
      o1 state v ≡@{optionO (dPropO Σ)} o2 state v.
  Proof.
    iIntros "#eq".
    rewrite /encoded_pred_unwrap.
    destruct o1; destruct o2; simpl;
      rewrite option_equivI; try done.
    rewrite option_equivI.
    rewrite !discrete_fun_equivI.
    rewrite monPred_equivI. iIntros (i).
    iApply "eq".
  Qed.

  Lemma own_all_preds_pred `{Countable ST}
        dq ℓ (ϕ : predicate ST) (preds : gmap loc enc_predicate) :
    own_all_preds dq preds -∗
    know_pred ℓ ϕ -∗
    (∃ (o : enc_predicateO),
       ⌜preds !! ℓ = Some o⌝ ∗ (* Some encoded predicate exists. *)
       ▷ (o ≡ encode_predicate ϕ)).
  Proof.
    iIntros "O K".
    iDestruct (own_valid_2 with "O K") as "H".
    iDestruct (auth_both_dfrac_validI with "H") as "(_ & tmp & val)".
    iDestruct "tmp" as (c) "#eq".
    rewrite gmap_equivI.
    iSpecialize ("eq" $! ℓ).
    rewrite lookup_fmap.
    rewrite lookup_op.
    rewrite lookup_singleton.
    destruct (preds !! ℓ) as [o|] eqn:eq; rewrite eq; simpl.
    2: {
      case (c !! ℓ); intros; iDestruct "eq" as %eq'; inversion eq'. }
    iExists o.
    iSplit; first done.
    case (c !! ℓ).
    - intros ?.
      rewrite -Some_op.
      rewrite !option_equivI.
      rewrite wsat.agree_equiv_inclI.
      rewrite !discrete_fun_equivI. iIntros (state).
      iSpecialize ("eq" $! state).
      rewrite !discrete_fun_equivI. iIntros (v).
      iSpecialize ("eq" $! v).
      rewrite later_equivI_1.
      iNext.
      rewrite /predicate_to_unwrapped_predicate.
      iDestruct (encoded_pred_unwrap_inj with "eq") as "eq2".
      iRewrite "eq2".
      done.
    - rewrite right_id.
      simpl.
      rewrite !option_equivI.
      rewrite agree_equivI.
      rewrite !discrete_fun_equivI. iIntros (state).
      iSpecialize ("eq" $! state).
      rewrite !discrete_fun_equivI. iIntros (v).
      iSpecialize ("eq" $! v).
      rewrite later_equivI_1.
      iNext.
      rewrite /predicate_to_unwrapped_predicate.
      iDestruct (encoded_pred_unwrap_inj with "eq") as "eq2".
      done.
  Qed.

  Lemma predicates_frag_lookup γ predicates (ℓ : loc) pred :
    predicates !! ℓ = Some pred →
    own γ (◯ (pred_to_ra <$> predicates) : predicatesR) -∗
    own γ (◯ {[ ℓ := pred_to_ra pred ]}).
  Proof.
    intros look. f_equiv. simpl.
    apply auth_frag_mono.
    rewrite singleton_included_l.
    eexists _.
    rewrite lookup_fmap look.
    naive_solver.
  Qed.

  (** If [pred] is the encoding of [Φ] then [pred] holding for the encoding of
  [s] is equivalent to [ϕ] holding for [s]. *)
  Lemma pred_encode_Some `{Countable ST}
        ϕ (s : ST) (v : val) (pred : enc_predicateO) :
    (pred ≡ encode_predicate ϕ : iProp Σ) -∗
    (pred (encode s) v ≡ Some (ϕ s v) : iProp Σ).
  Proof.
    iIntros "eq".
    iEval (setoid_rewrite discrete_fun_equivI) in "eq".
    iEval (setoid_rewrite discrete_fun_equivI) in "eq".
    iSpecialize ("eq" $! (encode s) v).
    Unshelve. 2: { done. } 2: { done. }
    rewrite /encode_predicate. rewrite decode_encode /=.
    done.
  Qed.

  Lemma own_all_preds_insert `{Countable ST} preds ℓ (ϕ : ST → val → dProp Σ) :
    preds !! ℓ = None →
    own predicates_name (● preds_to_ra preds) ==∗
    own predicates_name (● preds_to_ra (<[ℓ := encode_predicate ϕ]>preds)) ∗
    know_pred ℓ ϕ.
  Proof.
    iIntros (look) "A".
    rewrite /know_pred.
    rewrite comm.
    iMod (own_update with "A") as "[H $]".
    { apply auth_update_alloc.
      apply alloc_local_update; last done.
      rewrite /preds_to_ra. rewrite lookup_fmap. rewrite look. done. }
    iModIntro.
    rewrite /preds_to_ra.
    rewrite fmap_insert.
    iFrame.
  Qed.

End predicates.

Section encoded_predicate.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ}.

  Implicit Types (s : ST) (ϕ : ST → val → dProp Σ).

  Definition encoded_predicate_holds
    (enc_pred : positive → val → optionO (dPropO Σ))
    (enc_state : positive) (v : val) i : iProp Σ :=
    (∃ P, (enc_pred enc_state v ≡ Some P) ∗ P i).

  Lemma predicate_holds_phi_decode ϕ s encS (encϕ : enc_predicateO) v i :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v i ∗-∗ ϕ s v i).
  Proof.
    iIntros (eq') "predsEquiv".
    iSplit.
    - iDestruct 1 as (P') "[eq PH]".
      iDestruct (discrete_fun_equivI with "predsEquiv") as "HI".
      iDestruct ("HI" $! encS) as "HIP". (* iClear "HI". *)
      iEval (rewrite discrete_fun_equivI) in "HIP".
      iDestruct ("HIP" $! v) as "HI". (* iClear "HIP". *)
      rewrite /encode_predicate.
      rewrite eq'.
      simpl.
      iRewrite "eq" in "HI".
      rewrite option_equivI.
      by iRewrite "HI" in "PH".
    - iIntros "phi".
      rewrite /encoded_predicate_holds.
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate. rewrite eq'.
      simpl.
      destruct (encϕ encS v); rewrite option_equivI; last done.
      iExists _. iSplit; first done.
      by iRewrite "predsEquiv".
  Qed.

  Lemma predicate_holds_phi_decode_1 ϕ s encS (encϕ : enc_predicateO) v i :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v i -∗ ϕ s v i).
  Proof.
    iIntros (?) "H1 H2".
    iApply (predicate_holds_phi_decode with "H1 H2").
    done.
  Qed.

  Lemma predicate_holds_phi_decode_2 ϕ s encS (encϕ : enc_predicateO) v i :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    ϕ s v i -∗
    encoded_predicate_holds encϕ encS v i.
  Proof.
    iIntros (?) "H1 H2".
    iApply (predicate_holds_phi_decode with "H1 H2").
    done.
  Qed.

  Lemma predicate_holds_phi ϕ s encS (encϕ : enc_predicateO) v i :
    encS = encode s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v i ∗-∗ ϕ s v i).
  Proof.
    iIntros (eqEncS) "predsEquiv".
    iApply predicate_holds_phi_decode; last done.
    rewrite eqEncS. apply decode_encode.
  Qed.

  Global Instance encoded_predicate_holds_mono encϕ encS v :
    Proper ((⊑) ==> (⊢)) (encoded_predicate_holds encϕ encS v).
  Proof.
    iIntros (???). iDestruct 1 as (P) "[eq P]".
    iExists P. iFrame.
  Qed.

End encoded_predicate.
