(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import extra.
From self.algebra Require Import ghost_map ghost_map_map.
From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop abstract_state lifted_modalities.
From self.high Require Export abstract_state.
From self.high.resources Require Export bumpers preorders auth_map_map abstract_history.

Class nvmHighDeltaG := MkNvmHighDeltaG {
  (* "Global" ghost names *)
  abs_history_name : gname;
  (* For physical history *)
  phys_history_name : gname;
  non_atomic_views_gname : gname;
  crashed_in_name : gname;
  predicates_name : gname;
  preorders_name : gname;
  offset_name : gname;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  bumpers_name : gname;
}.

(* A record of all the global ghost names that we need. *)
Class nvmDeltaG := NvmDeltaG {
  nvm_delta_base :> nvmBaseDeltaG;
  nvm_delta_high :> nvmHighDeltaG
}.

(* Resource algebra used to represent agreement on which predicates are
associated with which locations. *)

Definition predicateR {Σ} :=
  agreeR (positive -d> val -d> laterO (optionO (nvmDeltaG -d> thread_view -d> iPropO Σ))).

Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

Class predicatesG Σ := { predicates_inG :> inG Σ (@predicatesR Σ) }.

Definition predicate_F :=
  agreeRF (positive -d> val -d> ▶ (optionOF (nvmDeltaG -d> thread_view -d> ∙))).

Definition predicates_F := authRF (gmapURF loc predicate_F).

Definition predicatesΣ := #[ GFunctor predicates_F ].

Instance subG_predicatesΣ {Σ} : subG predicatesΣ Σ → predicatesG Σ.
Proof. solve_inG. Qed.

(* Resource algebra that contains all the locations that are _shared_. *)
Definition shared_locsR := authR (gsetUR loc).

Class nvmHighFixedG Σ := {
  nvm_predicatesG :> predicatesG Σ;
  abs_histories :> ghost_map_mapG Σ loc time positive;
  phys_histories :> inG Σ (auth_map_mapR (leibnizO message));
  non_atomic_views :> ghost_mapG Σ loc view;
  crashed_in_inG :> ghost_mapG Σ loc positive;
  preordersG :> ghost_mapG Σ loc (relation2 positive);
  offsetsG :> ghost_mapG Σ loc nat;
  locsG :> inG Σ shared_locsR;
  nvm_bumpersG :> bumpersG Σ;
}.

Definition nvmHighΣ :=
  #[ predicatesΣ;
     ghost_map_mapΣ loc time positive;
     GFunctor (auth_map_mapR (leibnizO message));
     ghost_mapΣ loc view;
     ghost_mapΣ loc positive;
     ghost_mapΣ loc (relation2 positive);
     ghost_mapΣ loc nat;
     GFunctor (shared_locsR);
     ghost_mapΣ loc (positive → option positive) ].

Instance subG_nvmHighΣ {Σ} : subG nvmHighΣ Σ → nvmHighFixedG Σ.
Proof. solve_inG. Qed.

Class nvmG Σ := NvmFixedG {
  nvmG_baseG :> nvmBaseFixedG Σ;
  nvmG_highG :> nvmHighFixedG Σ;
}.

(* All the functors that we need for the high-level logic (and no ghost names). *)
Class nvmGpreS Σ := NvmPreG {
  nvmPreG_base :> nvmBaseGpreS Σ;
  nvmPreG_high :> nvmHighFixedG Σ; (* We can use [nvmHighFixedG] directly as it has no ghost names. *)
}.

Definition nvmΣ := #[ nvmBaseΣ; nvmHighΣ ].

Instance subG_nvmΣ {Σ} : subG nvmΣ Σ → nvmGpreS Σ.
Proof. solve_inG. Qed.

(* Wrappers around ownership of resources that extracts the ghost names from
[nvmDeltaG]. These wrapper makes it easier to switch the ghost names around
after a crash in [post_crash_modality.v]. *)

Section location.
  Context `{nvmG Σ, nD : nvmDeltaG}.

  Definition is_na_loc ℓ := own exclusive_locs_name (◯ {[ ℓ ]}).

  Definition is_at_loc ℓ := own shared_locs_name (◯ {[ ℓ ]}).

End location.

Section ownership_wrappers.
  Context `{nvmG Σ, nD : nvmDeltaG}.

  (* We have these wrappers partly to avoid having to spell out the global ghost
  names, and partly such that we can conveniently swap them out by giving the
  named type class instance [nD] *)

  Definition know_encoded_bumper (ℓ : loc)
             (encoded_bumper : positive → option positive) : iProp Σ :=
    ℓ ↪[bumpers_name]□ encoded_bumper.

  Definition know_bumper `{AbstractState ST} ℓ (bumper : ST → ST) : iProp Σ :=
    own_know_bumper bumpers_name ℓ bumper.

  Definition know_preorder_loc `{Countable ST} ℓ (preorder : relation2 ST) : iProp Σ :=
    own_know_preorder_loc preorders_name ℓ preorder.

  Definition know_full_encoded_history_loc ℓ q enc_abs_hist : iProp Σ :=
    history_full_entry_encoded abs_history_name ℓ q enc_abs_hist.

  Definition know_full_history_loc `{Countable ST}
             ℓ q (abs_hist : gmap time ST) : iProp Σ :=
    full_entry_unenc abs_history_name ℓ q abs_hist.

  Definition know_frag_encoded_history_loc ℓ t e : iProp Σ :=
    frag_entry abs_history_name ℓ t e.

  Definition know_frag_history_loc `{Countable ST} ℓ t (s : ST) : iProp Σ :=
    frag_entry_unenc abs_history_name ℓ t s.

  (* The storeview of the most recent write to a na location. *)
  Definition know_na_view ℓ q (SV : view) : iProp Σ :=
    ℓ ↪[non_atomic_views_gname]{#q} SV.

  Definition know_phys_hist_msg ℓ t msg : iProp Σ :=
    auth_map_map_frag_singleton phys_history_name ℓ t msg.

  Definition crashed_in_mapsto `{Countable ST} ℓ (s : ST) : iProp Σ :=
    ∃ es, ⌜ decode es = Some s ⌝ ∗ ℓ ↪[crashed_in_name]□ es.

  Lemma crashed_in_mapsto_agree `{Countable ST} ℓ (s1 s2 : ST) :
    crashed_in_mapsto ℓ s1 -∗ crashed_in_mapsto ℓ s2 -∗ ⌜ s1 = s2 ⌝.
  Proof.
    iDestruct 1 as (? eq1) "pts1".
    iDestruct 1 as (? e2) "pts2".
    iDestruct (ghost_map_elem_agree with "pts1 pts2") as %->.
    iPureIntro. congruence.
  Qed.

End ownership_wrappers.

Section location_sets.
  Context `{nvmG Σ}.

  Implicit Types (locs : gset loc) (ℓ : loc).

  Lemma location_sets_singleton_included γ locs ℓ :
    own γ (● locs) -∗ own γ (◯ {[ ℓ ]}) -∗ ⌜ ℓ ∈ locs ⌝.
  Proof.
    iIntros "A B".
    iDestruct (own_valid_2 with "A B")
      as %[V%gset_included _]%auth_both_valid_discrete.
    rewrite elem_of_subseteq_singleton.
    done.
  Qed.

  Lemma location_sets_lookup γ locs ℓ :
    ℓ ∈ locs → own γ (◯ locs) -∗ own γ (◯ {[ ℓ ]}).
  Proof.
    iIntros (elm). f_equiv. simpl.
    eexists (◯ locs).
    rewrite -auth_frag_op.
    f_equiv.
    set_solver.
  Qed.

End location_sets.

Section predicates.
  Context `{!nvmG Σ, hGD : nvmDeltaG}.

  (* Note, there are three types for predicates.
     1/ The real/initial type which depends on some [ST]: *)
  Definition predicate ST := ST → val → nvmDeltaG → dProp Σ.
  (* 2/ The encoded type that doesnt depend on [ST]: *)
  Definition enc_predicate := positive → val → option (nvmDeltaG → dProp Σ).
  (* 3/ The unwrapped type where we project out of [dProp], forgets that it is
        monotone, and end up with [thread_view → iProp Σ]: *)
  Definition unwrapped_predicate :=
    positive → val → option (nvmDeltaG → thread_view → iProp Σ).

  Definition enc_predicateO :=
    positive -d> val -d> optionO (nvmDeltaG -d> dPropO Σ).

  Definition predO :=
    positive -d> val -d> optionO (nvmDeltaG -d> thread_view -d> iPropO Σ).

  (* Unfold the [dProp] and forget about monotinicity. *)
  Definition encoded_pred_unwrap
    (pred : enc_predicate) : unwrapped_predicate :=
      λ s v, (λ p nD TV, monPred_at (p nD) TV) <$> (pred s v).

  Definition encoded_pred_unwrap'
    (pred : enc_predicateO) : predO :=
      λ s v, (λ p nD TV, monPred_at (p nD) TV) <$> (pred s v).

  Definition unwrapped_pred_to_ra (pred : unwrapped_predicate) :
    (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  Definition pred_to_ra (pred : enc_predicate) : (@predicateR Σ) :=
    unwrapped_pred_to_ra (encoded_pred_unwrap pred).

  Global Instance enoded_predc_unwrap :
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
    intros ??.
    specialize (eq x).
    apply eq.
  Qed.

  Global Instance pred_to_ra_ne :
    ∀ n, Proper (@dist enc_predicateO _ n ==> dist n) pred_to_ra.
  Proof.
    intros ??? eq.
    rewrite /pred_to_ra.
    rewrite /pred_to_ra.
    rewrite /unwrapped_pred_to_ra.
    apply (@to_agree_ne (positive -d> val -d> laterO (optionO (nvmDeltaG -d> thread_view -d> (iPropO Σ))))).
    intros ??.
    eassert (NonExpansive Next) as ne; last apply ne; first by apply _.
    apply enoded_predc_unwrap in eq.
    specialize (eq x0).
    apply eq.
  Qed.

  Definition preds_to_ra (preds : gmap loc (enc_predicate))
    : gmapUR loc (@predicateR Σ) := pred_to_ra <$> preds.

  Definition own_all_preds dq preds :=
    own predicates_name (●{dq} (preds_to_ra preds) : predicatesR).

  Definition encode_predicate `{Countable ST} (ϕ : predicate ST)
    : enc_predicate :=
    λ encS v, (λ s, ϕ s v) <$> decode encS.

  Definition predicate_to_unwrapped_predicate `{Countable ST} (ϕ : predicate ST)
    : unwrapped_predicate :=
    encoded_pred_unwrap (encode_predicate ϕ).

  Definition know_pred `{Countable ST} ℓ (ϕ : predicate ST) : iProp Σ :=
    own predicates_name
        (◯ {[ ℓ := unwrapped_pred_to_ra (predicate_to_unwrapped_predicate ϕ) ]}).

  Lemma encode_predicate_extract `{Countable ST}
      (ϕ : predicate ST) e s v
      (P : nvmDeltaG -d> dPropO Σ) TV hG' :
    decode e = Some s →
    (encode_predicate ϕ e v : optionO (nvmDeltaG -d> dPropO Σ)) ≡ Some P -∗
    P hG' TV -∗
    ϕ s v hG' TV.
  Proof.
    rewrite /encode_predicate.
    iIntros (->) "equiv".
    simpl.
    rewrite option_equivI.
    iEval (setoid_rewrite discrete_fun_equivI) in "equiv".
    iSpecialize ("equiv" $! hG').
    iRewrite "equiv".
    iIntros "$".
  Qed.

  Lemma encode_predicate_extract_L `{Countable ST}
        (ϕ : ST → val → nvmDeltaG → dProp Σ) e s v P TV hG' :
    decode e = Some s →
    encode_predicate ϕ e v = Some P →
    P hG' TV -∗
    ϕ s v hG' TV.
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
        ≡@{optionO (nvmDeltaG -d> thread_view -d> iPropO Σ)}
        encoded_pred_unwrap o2 state v -∗
      o1 state v ≡@{optionO (nvmDeltaG -d> dPropO Σ)} o2 state v.
  Proof.
    iIntros "#eq".
    rewrite /encoded_pred_unwrap.
    destruct o1; destruct o2; simpl;
      rewrite option_equivI; try done.
    rewrite option_equivI.
    rewrite !discrete_fun_equivI. iIntros (nD).
    rewrite monPred_equivI. iIntros (TV).
    iSpecialize ("eq" $! nD).
    rewrite discrete_fun_equivI.
    iSpecialize ("eq" $! TV).
    done.
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
    destruct (preds !! ℓ) as [o|] eqn:eq; simpl.
    2: { simpl. case (c !! ℓ); intros; iDestruct "eq" as %eq'; inversion eq'. }
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

  Lemma own_all_preds_insert `{Countable ST} preds ℓ (ϕ : ST → val → nvmDeltaG → dProp Σ) :
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
      rewrite /preds_to_ra. rewrite lookup_fmap. erewrite look. done. }
    iModIntro.
    rewrite /preds_to_ra.
    rewrite fmap_insert.
    iFrame.
  Qed.

End predicates.

Section encoded_predicate.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ, hG : nvmDeltaG}.

  Implicit Types (s : ST) (ϕ : ST → val → nvmDeltaG → dProp Σ).

  Definition encoded_predicate_holds
    (enc_pred : positive → val → optionO (nvmDeltaG -d> dPropO Σ))
    (enc_state : positive) (v : val) TV : iProp Σ :=
    (∃ P, (enc_pred enc_state v ≡ Some P) ∗ P _ TV).

  Lemma predicate_holds_phi_decode ϕ s encS (encϕ : enc_predicateO) v TV :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v TV ∗-∗ ϕ s v _ TV).
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
      iEval (setoid_rewrite discrete_fun_equivI) in "HI".
      iSpecialize ("HI" $! hG).
      by iRewrite "HI" in "PH".
    - iIntros "phi".
      rewrite /encoded_predicate_holds.
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate. rewrite eq'.
      simpl.
      destruct (encϕ encS v); rewrite option_equivI; last done.
      iExists _. iSplit; first done.
      iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! hG).
      by iRewrite "predsEquiv".
  Qed.

  Lemma predicate_holds_phi_decode_1 ϕ s encS (encϕ : enc_predicateO) v TV :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v TV -∗ ϕ s v _ TV).
  Proof.
    iIntros (?) "H1 H2".
    iApply (predicate_holds_phi_decode with "H1 H2").
    done.
  Qed.

  Lemma predicate_holds_phi_decode_2 ϕ s encS (encϕ : enc_predicateO) v TV :
    decode encS = Some s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    ϕ s v _ TV -∗
    encoded_predicate_holds encϕ encS v TV.
  Proof.
    iIntros (?) "H1 H2".
    iApply (predicate_holds_phi_decode with "H1 H2").
    done.
  Qed.

  Lemma predicate_holds_phi ϕ s encS (encϕ : enc_predicateO) v TV :
    encS = encode s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v TV ∗-∗ ϕ s v _ TV).
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
