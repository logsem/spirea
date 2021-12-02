(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.base_logic.lib Require Import own ghost_map.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import extra.
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
  preordersG :> inG Σ preordersR;
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

Section ownership_wrappers.
  Context `{nvmFixedG Σ, nD : nvmDeltaG Σ}.

  Definition know_bumper `{AbstractState ST} ℓ bumper :=
    own_know_bumper bumpers_name ℓ bumper.

  Definition know_preorder_loc `{Countable A} ℓ (preorder : relation2 A) : iProp Σ :=
    own_know_preorder_loc preorders_name ℓ preorder.

  Definition know_full_encoded_history_loc ℓ enc_abs_hist : iProp Σ :=
    own_full_encoded_history_loc abs_history_name ℓ enc_abs_hist.

  Definition know_full_history_loc `{Countable ST}
             ℓ (abs_hist : gmap time ST) : iProp Σ :=
    own_full_history_loc abs_history_name ℓ abs_hist.

  Definition know_frag_encoded_history_loc ℓ enc_abs_hist : iProp Σ :=
    own_frag_encoded_history_loc know_abs_history_name ℓ enc_abs_hist.

  Definition know_frag_history_loc `{Countable ST}
             ℓ (abs_hist : gmap time ST) : iProp Σ :=
    own_frag_history_loc know_abs_history_name ℓ abs_hist.

  Definition know_na_view ℓ (SV : view) : iProp Σ :=
    ℓ ↪[non_atomic_views_gname] SV.

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

Definition increasing_list `{SqSubsetEq ST} (ss : list ST) :=
  ∀ i j s s', i < j → (ss !! i = Some s) → (ss !! j = Some s') → s ⊑ s'.

Lemma increasing_list_singleton `{SqSubsetEq ST} (s : ST) : increasing_list [s].
Proof. intros [|][|]?????; try naive_solver. simplify_eq. lia. Qed.

Lemma lookup_snoc_Some {A} (l : list A) x x2 i :
  (l ++ [x]) !! i = Some x2 →
  (l !! i = Some x2) ∨ (length l = i ∧ x = x2).
Proof.
  intros [look|[? [??]%list_lookup_singleton_Some]]%lookup_app_Some.
  - left. apply look.
  - right. auto with lia.
Qed.

Lemma increasing_list_snoc `{SqSubsetEq ST} xs xs__last (x : ST) :
  (last xs) = Some xs__last →
  xs__last ⊑ x →
  increasing_list xs → increasing_list (xs ++ [x]).
Proof.
  intros last incl incr.
  intros ?????.
  intros [?|[??]]%lookup_snoc_Some; intros [look|[??]]%lookup_snoc_Some.
  * eapply incr; done.
  * simplify_eq.
    admit.
  * apply lookup_lt_Some in look. lia.
  * lia.
Admitted.

Section points_to_shared.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ, AbstractState ST}.

  Implicit Types (e : expr) (ℓ : loc) (s : ST)
           (ss : list ST) (ϕ : ST → val → nvmDeltaG Σ → dProp Σ).

  Definition abs_hist_to_ra_old
          (abs_hist : gmap time (message * positive)) : encoded_abs_historyR :=
    (to_agree ∘ snd) <$> abs_hist.

  Lemma singleton_included_l' `{Countable K, CmraTotal A}
        (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  Definition is_exclusive_loc ℓ := own exclusive_locs_name (◯ {[ ℓ ]}).

  Definition is_shared_loc ℓ : iProp Σ := own shared_locs_name (◯ {[ ℓ ]}).

  (* _Exclusive_ points-to predicate. This predcate says that we know that the
  last events at [ℓ] corresponds to the *)
  Program Definition mapsto_ex (persisted : bool) (ℓ : loc) (ss : list ST) : dProp Σ :=
    (* MonPred (λ TV, *)
      (∃ (tP tStore : time) SV (abs_hist : gmap time ST) (msg : message),
        (* NOTE: Maybe we can actually remove [increasing_list]? It should be
        covered by the fact that the list corresponds to [abs_hist] and that one
        is sorted. *)
        "%incrList" ∷ ⌜ increasing_list ss ⌝ ∗
        "isExclusiveLoc" ∷ ⎡ is_exclusive_loc ℓ ⎤ ∗
        "#order" ∷ ⎡ know_preorder_loc ℓ (abs_state_relation) ⎤ ∗

        (* [tStore] is the last message and it agrees with the last state in ss. *)
        "%lookupV" ∷ ⌜ abs_hist !! tStore = last ss ⌝ ∗
        "%nolater" ∷ ⌜ map_no_later abs_hist tStore ⌝ ∗

        (* Ownership over the abstract history. *)
        "hist" ∷ ⎡ know_full_history_loc ℓ abs_hist ⎤ ∗

        "knowSV" ∷ ⎡ know_na_view ℓ SV ⎤ ∗
        "%slice" ∷ ⌜ map_slice abs_hist tP tStore ss ⌝ ∗
        "#physMsg" ∷ ⎡ auth_map_map_frag_singleton know_phys_history_name ℓ tStore msg ⎤ ∗
        (* "%msgViewIncluded" ∷ ⌜ msg_store_view msg ⊑ SV ⌝ ∗ *)
        "#inThreadView" ∷ monPred_in (SV, msg_persisted_after_view msg, ∅) ∗
        (* We have the [tStore] timestamp in our store view. *)
        "%haveTStore" ∷ ⌜ tStore ≤ SV !!0 ℓ ⌝ ∗
        (* "haveTStore" ∷ monPred_in ({[ ℓ := MaxNat tStore ]}, ∅, ∅) ∗ *)

        "pers" ∷ if persisted then ⎡ persisted_loc ℓ tP ⎤ else ⌜ tP = 0 ⌝)%I.

  (* NOTE: This comment is out of date. *)
  (* This definition uses an existentially quantified [s']. We do this such that
  owning [know_persist_lb ℓ s] before a crash also results in owning
  exactly the same, [know_persist_lb ℓ s], after a crash. Had the
  definition said that _exactly_ [s] was persisted at [t] then we would have a
  different state after a crash, since after a crash there is only a single
  entry in the history for [ℓ] and that entry may refer to any abstract state
  greater than [s]. Said in another way, this definition allows for weakening
  (lowering the state) which we do after a crash to get a simpler (but just as
  useful) interaction with the post crash modality. *)
  (* This definition must satisfy that is we load a location in state [s] then
  the recovery predicate holds for [s]. Hence we cannot store a lower bound on
  [s] but must ensure that exactly [s] exists in the abstract history. *)
  Program Definition know_persist_lb ℓ (sP : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ tP,
        (* "%sPInclSP'" ∷ ⌜ sP ⊑ sP' ⌝ ∗ *)
        (* We have the persisted state in our store view. *)
        "%tPLe" ∷ ⌜ tP ≤ (store_view TV) !!0 ℓ ⌝ ∗
        "persisted" ∷ persisted_loc ℓ tP ∗
        "order" ∷ know_preorder_loc ℓ abs_state_relation ∗
        "knowFragHist" ∷ know_frag_history_loc ℓ {[ tP := sP ]})%I _.
  Next Obligation. solve_proper. Qed.

  Program Definition know_flush_lb ℓ (s : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ (tF : nat),
        (* Either the location is persisted or we have something in the flush
        view. The later case is for use after a crash where we don't have
        anything in the flush view. *)
        "viewFact" ∷ (⌜tF ≠ 0⌝ ∗ ⌜tF ≤ flush_view TV !!0 ℓ⌝  ∨
                      ⌜tF = 0⌝ ∗ persisted_loc ℓ 0) ∗
        (* ("%tFLe" ∷ ⌜ tF ≤ (flush_view TV) !!0 ℓ ⌝ ∨ *)
        (*            (⌜tF = 0⌝ ∗ persisted_loc ℓ 0)) ∗ *)
        (* (⌜ tF ≤ (flush_view TV) !!0 ℓ ⌝ ∨ ⌜tF = 0⌝ ∗ ) ∗ *)
        "order" ∷ know_preorder_loc ℓ abs_state_relation ∗
        "knowFragHist" ∷ know_frag_history_loc ℓ {[ tF := s ]}
    )%I _.
  Next Obligation. solve_proper. Qed.

  Program Definition know_store_lb ℓ (s : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ (tS : nat) (* (msg : message) *),
        "%tSLe" ∷ ⌜ tS ≤ (store_view TV) !!0 ℓ ⌝ ∗
        "#order" ∷ know_preorder_loc ℓ abs_state_relation ∗
        "#knowFragHist" ∷ know_frag_history_loc ℓ {[ tS := s ]} (* ∗ *)
        (* "#knowFragPhysHist" ∷ *)
        (*   auth_map_map_frag_singleton know_phys_history_name ℓ tS msg ∗ *)
        (* "%msgViewIncluded" ∷ ⌜ msg.(msg_persist_view) ⊑ store_view TV ⌝ *)
    )%I _.
  Next Obligation. solve_proper. Qed.

  (* The location [ℓ] was recovered in the abstract state [s]. *)
  Definition recovered_at ℓ s : dProp Σ :=
    ∃ CV,
      "#knowFragHist" ∷ ⎡know_frag_history_loc ℓ {[ 0 := s ]}⎤ ∗
      "#crashed" ∷ ⎡crashed_at CV⎤ ∗
      "%inCV" ∷ ⌜ℓ ∈ dom (gset _) CV⌝.

  (* [ℓ] was recovered at the last crash. *)
  Definition recovered ℓ : dProp Σ := ∃ s, recovered_at ℓ s.

  (* [ℓ] was not recovered at the last crash. *)
  Definition lost ℓ : dProp Σ :=
    ∃ CV,
      "#crashed" ∷ ⎡crashed_at CV⎤ ∗
      "%notInCV" ∷ ⌜ℓ ∉ dom (gset _) CV⌝.

  (* Let's see if we want this.
  Definition mapsto_shared ℓ s1 s2 s3 ϕ : dProp Σ :=
    "knowPred" ∷ ⎡ know_pred ℓ ϕ ⎤ ∗
    "isSharedLoc" ∷ ⎡ own shared_locs_name (◯ {[ ℓ ]}) ⎤ ∗
    "globalPerLB" ∷ know_persist_lb ℓ s1 ∗
    "persistLB" ∷ know_flush_lb ℓ s2 ∗
    "storeLB" ∷ know_store_lb ℓ s3.
  *)

  Global Instance know_flush_lb_persistent
         ℓ (s : ST) : Persistent (know_flush_lb ℓ s).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Global Instance know_store_lb_persistent
         ℓ (s : ST) : Persistent (know_store_lb ℓ s).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  (* Lemma know_flush_lb_at_zero ℓ (s s' : ST) : *)
  (*   s ⊑ s' → *)
  (*   ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗ *)
  (*   ⎡ know_preorder_loc ℓ abs_state_relation ⎤ -∗ *)
  (*   know_flush_lb ℓ s. *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (incl ?) "?". *)
  (*   iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia. *)
  (* Qed. *)

  (*
  Lemma know_store_lb_at_zero ℓ (s s' : ST) :
    s ⊑ s' →
    ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗
    ⎡ know_preorder_loc ℓ abs_state_relation ⎤ -∗
    know_store_lb ℓ s.
  Proof.
    iStartProof (iProp _). iIntros (incl ?) "?".
    iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia.
  Qed.
  *)

  (* A few utility lemmas. *)
  Lemma recovered_at_not_lot ℓ s : recovered_at ℓ s -∗ lost ℓ -∗ False.
  Proof.
    iNamed 1. iIntros "(%CV' & crashed' & %notInCV)".
    iDestruct (crashed_at_agree with "[$] [$]") as %->.
    set_solver.
  Qed.

  Lemma mapsto_ex_store_lb ℓ b ss s :
    last ss = Some s →
    mapsto_ex b ℓ ss -∗
    know_store_lb ℓ s.
  Proof. Admitted.

  Lemma mapsto_ex_last b ℓ ss : mapsto_ex b ℓ ss -∗ ⌜∃ s, last ss = Some s⌝.
  Proof.
    rewrite /mapsto_ex.
    iNamed 1.
    apply map_slice_lookup_hi_alt in slice.
    naive_solver.
  Qed.

  Lemma mapsto_ex_store_lb_incl ℓ b ss s1 s2 :
    last ss = Some s1 →
    know_store_lb ℓ s2 -∗
    mapsto_ex b ℓ ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof. Admitted.

  Lemma mapsto_ex_flush_lb_incl ℓ b ss s1 s2 :
    last ss = Some s1 →
    know_flush_lb ℓ s2 -∗
    mapsto_ex b ℓ ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof. Admitted.

End points_to_shared.

(** Notation for the exclusive points-to predicate. *)
Notation "l ↦ ss" := (mapsto_ex false l ss) (at level 20).
Notation "l ↦ₚ ss" := (mapsto_ex true l ss) (at level 20).
(* Notation "l ↦ xs ; ys | P" := (mapsto_ex l xs ys P) (at level 20). *)

(** Notation for the shared points-to predicate. *)
(* Notation "l ↦ ( s1 , s2 , s3 )  | P" := (mapsto_shared l s1 s2 s3 P) (at level 20). *)
