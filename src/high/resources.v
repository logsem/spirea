(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import extra.
From self.algebra Require Import ghost_map.
From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop abstract_state lifted_modalities.
From self.high Require Export abstract_state.
From self.high.resources Require Export bumpers preorders auth_map_map abstract_history.

Class nvmHighDeltaG := MkNvmHighDeltaG {
  (* "Global" ghost names *)
  (* For abstract history *)
  abs_history_name : gname;
  know_abs_history_name : gname;
  (* For physical history *)
  know_phys_history_name : gname;
  non_atomic_views_gname : gname;
  predicates_name : gname;
  preorders_name : gname;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  bumpers_name : gname;
}.

Class nvmDeltaG Σ := NvmDeltaG {
  nvm_delta_base :> nvmBaseDeltaG Σ;
  nvm_delta_high :> nvmHighDeltaG
}.

(* Resource algebra used to represent agreement on which predicates are
associated with which locations. *)
Definition predicateR {Σ} :=
  agreeR (positive -d> val -d> laterO (optionO (nvmDeltaG Σ -d> (dPropO Σ)))).
Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

(* Definition bumpersR := *)
(*   authR (gmapUR loc (agreeR (leibnizO (positive → option positive)))). *)

(* Resource algebra that contains all the locations that are _shared_. *)
Definition shared_locsR := authR (gsetUR loc).

Class nvmHighFixedG Σ := {
  predicates_inG :> inG Σ (@predicatesR Σ);
  ra_inG' :> inG Σ know_abs_historiesR;
  abs_histories :> ghost_mapG Σ loc (gmap time positive);
  phys_histories :> inG Σ (auth_map_mapR (leibnizO message));
  non_atomic_views :> ghost_mapG Σ loc view;
  preordersG :> ghost_mapG Σ loc (relation2 positive);
  shared_locsG :> inG Σ shared_locsR;
  exclusive_locsG :> inG Σ shared_locsR;
  nvm_bumpersG :> bumpersG Σ;
}.

Class nvmHighG Σ := NvmHighG {
  nvm_high_inG :> nvmHighFixedG Σ;
  nvm_high_deltaG :> nvmHighDeltaG;
}.

Class nvmFixedG Σ := NvmFixedG {
  nvmG_baseG :> nvmBaseFixedG Σ;
  nvmG_highG :> nvmHighFixedG Σ;
}.

(* All the functors that we need for the high-level logic (and no ghost names). *)
Class nvmGpreS Σ := NvmPreG {
  nvmPreG_base :> nvmBaseGpreS Σ;
  nvmPreG_high :> nvmHighFixedG Σ; (* We can use [nvmHighFixedG] directly as it has no ghost names. *)
}.

(* Wrappers around ownership of resources that extracts the ghost names from
[nvmDeltaG]. These wrapper makes it easier to switch the ghost names around
after a crash in [post_crash_modality.v]. *)

Section location.
  Context `{nvmFixedG Σ, nD : nvmDeltaG Σ}.

  Definition is_na_loc ℓ := own exclusive_locs_name (◯ {[ ℓ ]}).

  Definition is_at_loc ℓ := own shared_locs_name (◯ {[ ℓ ]}).

End location.

Section ownership_wrappers.
  Context `{nvmFixedG Σ, nD : nvmDeltaG Σ}.

  (* We have these wrappers partly to avoid having to spell out the global ghost
  names, and partly such that we can conveniently swap them out by giving the
  named type class instance [nD] *)

  Definition know_encoded_bumper (ℓ : loc)
             (encoded_bumper : positive → option positive) : iProp Σ :=
    ℓ ↪[bumpers_name]□ encoded_bumper.

  Definition know_bumper `{AbstractState ST} ℓ (bumper : ST → ST) : iProp Σ :=
    own_know_bumper bumpers_name ℓ bumper.

  Definition know_preorder_loc `{Countable A} ℓ (preorder : relation2 A) : iProp Σ :=
    own_know_preorder_loc preorders_name ℓ preorder.

  Definition know_full_encoded_history_loc ℓ q enc_abs_hist : iProp Σ :=
    own_full_encoded_history_loc abs_history_name ℓ q enc_abs_hist.

  Definition know_full_history_loc `{Countable ST}
             ℓ q (abs_hist : gmap time ST) : iProp Σ :=
    own_full_history_loc abs_history_name ℓ q abs_hist.

  Definition know_frag_encoded_history_loc ℓ enc_abs_hist : iProp Σ :=
    own_frag_encoded_history_loc know_abs_history_name ℓ enc_abs_hist.

  Definition know_frag_history_loc `{Countable ST}
             ℓ (abs_hist : gmap time ST) : iProp Σ :=
    own_frag_history_loc know_abs_history_name ℓ abs_hist.

  (* The storeview of the most recent write to a na location. *)
  Definition know_na_view ℓ q (SV : view) : iProp Σ :=
    ℓ ↪[non_atomic_views_gname]{#q} SV.

  Definition know_phys_hist_msg ℓ t msg : iProp Σ :=
    auth_map_map_frag_singleton know_phys_history_name ℓ t msg.

End ownership_wrappers.

Section location_sets.
  Context `{nvmFixedG Σ}.

  Lemma location_sets_singleton_included γ locs ℓ :
    own γ (● locs) -∗ own γ (◯ {[ ℓ ]}) -∗ ⌜ℓ ∈ locs⌝.
  Proof.
    iIntros "A B".
    iDestruct (own_valid_2 with "A B")
      as %[V%gset_included _]%auth_both_valid_discrete.
    rewrite elem_of_subseteq_singleton.
    done.
  Qed.

End location_sets.

Section predicates.
  Context `{!nvmFixedG Σ, hGD : nvmDeltaG Σ}.

  Definition predO := positive -d> val -d> optionO (nvmDeltaG Σ -d> dPropO Σ).

  Definition pred_to_ra
             (pred : positive → val → option (nvmDeltaG Σ → dProp Σ)) :
    (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  Definition preds_to_ra
             (preds : gmap loc
                               (positive → val → option (nvmDeltaG Σ → dProp Σ)))
    : gmapUR loc (@predicateR Σ) := pred_to_ra <$> preds.

  Definition own_all_preds dq preds :=
    own predicates_name (●{dq} (pred_to_ra <$> preds) : predicatesR).

  Definition encode_predicate `{Countable s}
             (ϕ : s → val → nvmDeltaG Σ → dProp Σ)
    : positive → val → option (nvmDeltaG Σ → dProp Σ) :=
    λ encS v, (λ s, ϕ s v) <$> decode encS.

  Definition know_pred `{Countable s}
      ℓ (ϕ : s → val → nvmDeltaG Σ → dProp Σ) : iProp Σ :=
    own predicates_name
        (◯ {[ ℓ := pred_to_ra (encode_predicate ϕ) ]}).

  Lemma encode_predicate_extract `{Countable ST}
        (ϕ : ST → val → nvmDeltaG Σ → dProp Σ) e s v P TV hG' :
    decode e = Some s →
    encode_predicate ϕ e v = Some P →
    P hG' TV -∗
    ϕ s v hG' TV.
  Proof. rewrite /encode_predicate. by iIntros (-> [= ->]). Qed.

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

  Lemma own_all_preds_pred `{Countable ST}
        dq ℓ (ϕ : ST → val → nvmDeltaG Σ → dProp Σ) (preds : gmap loc predO) :
    own_all_preds dq preds -∗
    know_pred ℓ ϕ -∗
    (∃ (o : predO),
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
    destruct (preds !! ℓ) as [o|] eqn:eq; rewrite eq /=.
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
      iRewrite "eq".
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
  Lemma pred_encode_Some `{Countable ST} ϕ (s : ST) (v : val) (pred : predO) :
    (pred ≡ encode_predicate ϕ : iProp Σ) -∗
    (pred (encode s) v ≡ Some (ϕ s v) : iProp Σ).
  Proof.
    iIntros "eq".
    iEval (setoid_rewrite discrete_fun_equivI) in "eq".
    iEval (setoid_rewrite discrete_fun_equivI) in "eq".
    iSpecialize ("eq" $! (encode s) v).
    Unshelve. 2: { done. } 2: { done. }
    (* iRewrite "eq". Why this no work? *)
    rewrite /encode_predicate. rewrite decode_encode /=.
    done.
  Qed.

  Lemma own_all_preds_insert `{Countable ST} preds ℓ (ϕ : ST → val → nvmDeltaG Σ → dProp Σ) :
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
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (s : ST) (ϕ : ST → val → nvmDeltaG Σ → dProp Σ).

  Definition encoded_predicate_holds
             (enc_pred : positive → val → optionO (nvmDeltaG Σ -d> dPropO Σ))
             (enc_state : positive) (v : val) TV : iProp Σ :=
    (∃ P, (enc_pred enc_state v ≡ Some P) ∗ P _ TV).

  Lemma predicate_holds_phi ϕ s encS (encϕ : predO) v TV :
    encS = encode s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v TV ∗-∗ ϕ s v _ TV).
  Proof.
    iIntros (eqEncS) "predsEquiv".
    iSplit.
    - iDestruct 1 as (P) "[eqP PH]".
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate.
      rewrite {2}eqEncS.
      rewrite decode_encode.
      simpl.
      iRewrite "eqP" in "predsEquiv".
      rewrite option_equivI.
      iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! hG).
      by iRewrite -"predsEquiv".
    - iIntros "phi".
      rewrite /encoded_predicate_holds.
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate. rewrite eqEncS. rewrite decode_encode.
      simpl.
      destruct (encϕ (encode s) v); rewrite option_equivI; last done.
      iExists _. iSplit; first done.
      iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! hG).
      by iRewrite "predsEquiv".
  Qed.

  Lemma predicate_holds_phi_decode ϕ s encS (encϕ : predO) v TV :
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

  Global Instance encoded_predicate_holds_mono encϕ encS v :
    Proper ((⊑) ==> (⊢)) (encoded_predicate_holds encϕ encS v).
  Proof.
    iIntros (???). iDestruct 1 as (P) "[eq P]".
    iExists P. iFrame.
  Qed.

End encoded_predicate.
