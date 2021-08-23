(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.base_logic.lib Require Import own ghost_map.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import extra.
From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop lifted_modalities.

Class nvmHighDeltaG := MkNvmHighDeltaG {
  (* "Global" ghost names *)
  abs_history_name : gname;
  know_abs_history_name : gname;
  predicates_name : gname;
  preorders_name : gname;
  shared_locs_name : gname;
  (* exclusive_locs_name : gname; *) (* NOTE: Keep this in case we need it again. *)
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

(* Resource algebras that for each location stores the encoded abstract states
associated with each message/store. *)
Definition encoded_abs_historyR := gmapUR time (agreeR positiveO).
Definition enc_abs_histories := gmap loc (gmap time positive).

Definition know_abs_historiesR :=
  authR (gmapUR loc (gmapUR time (agreeR positiveO))).

(* Resourcce algebra that stores the encoded preorder for each location. *)
Definition relationO := leibnizO (positive → positive → Prop).
Definition preordersR := authR (gmapUR loc (agreeR relationO)).

Definition bumpersR :=
  authR (gmapUR loc (agreeR (leibnizO (positive → option positive)))).

(* Resource algebra that contains all the locations that are _shared_. *)
Definition shared_locsR := authR (gsetUR loc).

Class nvmHighFixedG Σ := {
  predicates_inG :> inG Σ (@predicatesR Σ);
  ra_inG' :> inG Σ know_abs_historiesR;
  abs_histories :> ghost_mapG Σ loc (gmap time positive);
  preordersG :> inG Σ preordersR;
  shared_locsG :> inG Σ shared_locsR;
  bumpersG :> inG Σ bumpersR
}.

Class nvmHighG Σ := NvmHighG {
  nvm_high_inG :> nvmHighFixedG Σ;
  nvm_high_deltaG :> nvmHighDeltaG;
}.

Class nvmFixedG Σ := NvmFixedG {
  nvmG_baseG :> nvmBaseFixedG Σ;
  nvmG_highG :> nvmHighFixedG Σ;
}.

Class AbstractState ST `{Countable ST} := {
  abs_state_relation : relation2 ST;
  abs_state_preorder :> PreOrder abs_state_relation;
}.

Instance abstract_state_sqsubseteq `{AbstractState ST} : SqSubsetEq ST :=
  abs_state_relation.

Global Instance discretizable_ghost_map_elem `{ghost_mapG Σ K V} ℓ γ v :
  own_discrete.Discretizable (ℓ ↪[γ] v).
Proof. rewrite ghost_map_elem_eq /ghost_map_elem_def. apply _. Qed.

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ}.
  Context `{Countable ST}.

  Implicit Types
    (abs_hist : gmap time ST) (ℓ : loc)
    (enc_abs_hist : gmap time positive)
    (abs_hists : gmap loc (gmap time positive)).

  Definition abs_hist_to_ra abs_hist : encoded_abs_historyR :=
    (to_agree ∘ encode) <$> abs_hist.

  Definition own_full_history_gname γ1 γ2 abs_hists : iProp Σ :=
    ghost_map_auth γ1 1 abs_hists ∗
    own γ2 (
      ● ((λ m : gmap _ _, to_agree <$> m) <$> abs_hists) : know_abs_historiesR
    ).

  Definition own_full_history abs_hists : iProp Σ :=
    own_full_history_gname abs_history_name know_abs_history_name abs_hists.

  Definition know_full_history_loc ℓ abs_hist : iProp Σ :=
    ℓ ↪[ abs_history_name ] (encode <$> abs_hist).

  Definition know_full_encoded_history_loc
             ℓ (abs_hist : gmap time positive) : iProp Σ :=
    ℓ ↪[ abs_history_name ] abs_hist.

  Definition know_frag_encoded_history_loc ℓ enc_abs_hist : iProp Σ :=
    own know_abs_history_name (◯ {[ ℓ := to_agree <$> enc_abs_hist ]}).

  (* In this definition we store that decoding the stored encoded histry is
  equal to our abstract history. This is weaker than strong the other way
  around, namely that encoding our history is equal to the stored encoded
  history. Storing this weaker fact makes the definition easier to show. This is
  important for the load lemma where, when we load some state and we want to
  return [know_store_lb] for the returned state. At that point we can
  conclude that decoding the encoding gives a result but not that the encoding
  is an encoding of some state. *)
  Definition know_frag_history_loc ℓ (abs_hist : gmap time ST) : iProp Σ :=
    ∃ enc,
      ⌜decode <$> enc = Some <$> abs_hist⌝ ∗
      (* ⌜enc = encode <$> abs_hist⌝ ∗ *)
      know_frag_encoded_history_loc ℓ enc.

  Lemma own_full_history_gname_alloc h :
    ⊢ |==> ∃ γ1 γ2,
        own_full_history_gname γ1 γ2 h ∗
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

  Lemma know_full_equiv ℓ abs_hist :
    know_full_history_loc ℓ abs_hist ⊣⊢
      know_full_encoded_history_loc ℓ (encode <$> abs_hist).
  Proof. done. Qed.

  Lemma know_frag_equiv ℓ abs_hist :
    know_frag_encoded_history_loc ℓ (encode <$> abs_hist) ⊢
    know_frag_history_loc ℓ abs_hist.
  Proof.
    rewrite /know_frag_history_loc /know_frag_encoded_history_loc.
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
  Lemma own_full_history_agree ℓ hist hists :
    own_full_history hists -∗
    know_full_history_loc ℓ hist -∗
    ⌜hists !! ℓ = Some (encode <$> hist)⌝.
  Proof.
    iIntros "[A _] B".
    iApply (ghost_map_lookup with "[$] [$]").
  Qed.

  Lemma own_frag_history_agree ℓ (part_hist : gmap time ST) hists :
    own_full_history hists -∗
    know_frag_history_loc ℓ part_hist -∗
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

  Lemma own_frag_history_agree_singleton ℓ t (s : ST) hists :
    own_full_history hists -∗
    know_frag_history_loc ℓ {[ t := s ]} -∗
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

  Lemma own_full_history_alloc ℓ t encS (s : ST) hists hist :
    hists !! ℓ = Some hist →
    hist !! t = Some encS →
    decode encS = Some s →
    own_full_history hists ==∗
    own_full_history hists ∗ know_frag_history_loc ℓ {[ t := s ]}.
  Proof.
    iIntros (look lookHist decEq) "[$ H2]".
    rewrite /own_full_history /know_frag_history_loc.
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
    rewrite /know_frag_encoded_history_loc.
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
    ⊢ |==> ∃ γ, own γ ((● (pred_to_ra <$> preds)) : predicatesR) ∗
                own γ ((◯ (pred_to_ra <$> preds)) : predicatesR).
  Proof.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_2; last reflexivity.
    intros ℓ.
    rewrite lookup_fmap.
    by case (preds !! ℓ).
  Qed.

  Lemma own_all_preds_pred `{Countable s}
        dq ℓ (ϕ : s → val → nvmDeltaG Σ → dProp Σ) (preds : gmap loc predO) :
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

End predicates.

(* (* For each location in the heap we maintain the following "meta data". *)
(* For every location we want to store: A type/set of abstract events, its full *)
(* abstract history, the invariant assertion. The abstract history maps *)
(* timestamps to elements of the abstract events. *) *)
(* Record loc_info := { *)
(*   l_state : Type; *)
(* (*   (* l_val : val; *) *) *)
(* (*   l_ϕ : l_state → val → dProp Σ; *) *)
(*   l_abstract_history : gmap nat l_state; *)
(* (*   (* * Type class instances *) *) *)
(*   l_sqsubseteq : SqSubsetEq l_state; *)
(*   l_preorder : PreOrder (⊑@{l_state}); *)
(*   (* We need countable to squash states into [positive] *) *)
(*   l_eqdecision : EqDecision l_state; *)
(*   l_countable : Countable l_state; *)
(* }. *)

(* Existing Instances l_eqdecision l_countable. *)

(* Definition encode_loc_info {Σ} (l : (@loc_info Σ)):= *)
(*   ((λ '(m, s), (m, encode s)) <$> (l_abstract_history l), *)
(*    λ v s, (l_ϕ l $ v) <$> decode s). *)

Definition lift2 {A B C} `{MBind M, MRet M, FMap M} (f : A → B → C) (am : M A) (bm : M B) :=
  a ← am;
  b ← bm;
  mret (f a b).

Definition mapply {A B} `{MBind M, FMap M} (mf : M (A → B)) (a : M A) :=
  mf ≫= (λ f, f <$> a).

(* This notation does not seem to work for some reason. *)
(* Notation "<*>" := mapply (at level 61, left associativity). *)
Notation "mf <*> a" := (mapply mf a) (at level 61, left associativity).

Section preorders.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ}.
  Context `{Countable A}.

  Implicit Type (preorders : gmap loc (relation2 positive)).

  Definition encode_relation (R : relation2 A) : relation2 positive :=
    λ (a b : positive), default False (R <$> decode a <*> decode b).

  Lemma encode_relation_iff (R : relation2 A) (a b : A) :
    R a b ↔ (encode_relation R) (encode a) (encode b).
  Proof.
    rewrite /encode_relation.
    rewrite !decode_encode.
    reflexivity.
  Qed.

  Definition map_to_agree preorders : gmapUR _ (agreeR relationO) :=
    to_agree <$> preorders.

  Definition own_all_preorders_gname γ preorders :=
    own γ (● (map_to_agree preorders)).

  Definition own_all_preorders preorders :=
    own_all_preorders_gname preorders_name preorders.

  Definition know_preorder_loc ℓ (preorder : relation2 A) : iProp Σ :=
    own preorders_name (◯ ({[ ℓ := to_agree (encode_relation preorder) ]})).

  Global Instance persistent_know_preorder_loc ℓ preorder :
    Persistent (know_preorder_loc ℓ preorder).
  Proof. apply _. Qed.

  Lemma own_all_preorders_gname_alloc (preorders : gmap loc (relation2 positive)) :
    ⊢ |==> ∃ γ, own_all_preorders_gname γ preorders ∗
                own γ (◯ ((to_agree <$> preorders) : gmapUR _ (agreeR relationO))).
  Proof.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_discrete. split; first done.
    rewrite /map_to_agree.
    apply (valid_to_agree_fmap (B := relationO) preorders).
  Qed.

  Lemma own_all_preorders_persist γ preorders :
    own_all_preorders_gname γ preorders ==∗
    own γ (●□ ((to_agree <$> preorders) : gmapUR _ (agreeR relationO))).
  Proof. iApply own_update. apply auth_update_auth_persist. Qed.

  Lemma auth_valid_to_agree_singleton_l {B}
        dq (m : gmap loc (leibnizO B)) e (ℓ : loc) :
    ✓ (●{dq} (to_agree <$> m : gmapUR _ (agreeR _)) ⋅
       ◯ {[ℓ := to_agree e]}) →
    m !! ℓ = Some e.
  Proof.
    intros [_ [incl _]]%auth_both_dfrac_valid_discrete.
    move: incl.
    rewrite singleton_included_l.
    intros [y [eq incl]].
    move: incl.
    rewrite lookup_fmap in eq.
    apply Some_equiv_eq in eq.
    destruct eq as [y' [look' eq]].
    rewrite -eq.
    rewrite <- look'.
    rewrite option_included_total.
    intros [|(? & ? & [= ?] & [= ?] & incl)]; first done.
    destruct (m !! ℓ) as [encOrder|]; last done.
    simpl in *.
    simplify_eq.
    setoid_rewrite to_agree_included in incl.
    f_equiv.
    apply leibniz_equiv.
    done.
  Qed.

  Lemma own_all_preorders_singleton_frag dq γ ℓ preorders preorder :
    own γ (●{dq} (map_to_agree preorders)) -∗
    own γ (◯ ({[ ℓ := to_agree (encode_relation preorder)]})) -∗
    ⌜preorders !! ℓ = Some (encode_relation preorder)⌝.
  Proof.
    iIntros "auth frag".
    iDestruct (own_valid_2 with "auth frag") as %V.
    iPureIntro.
    eapply auth_valid_to_agree_singleton_l.
    apply V.
  Qed.

  Lemma orders_lookup ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders orders -∗
    know_preorder_loc ℓ order2 -∗
    ⌜order1 = encode_relation order2⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (own_all_preorders_singleton_frag with "auth frag")
      as %look'.
    simplify_eq. done.
  Qed.

  Lemma orders_frag_lookup γ preorders (ℓ : loc) order :
    preorders !! ℓ = Some order →
    own γ (◯ (map_to_agree preorders)) -∗
    own γ (◯ ({[ ℓ := to_agree order ]} : gmapUR _ (agreeR relationO))).
  Proof.
    intros look. f_equiv. simpl.
    apply auth_frag_mono.
    rewrite singleton_included_l.
    eexists _.
    rewrite lookup_fmap look.
    naive_solver.
  Qed.

  (* If we know that two encoded values are related by en encoded relation, then
  we can "recover" related unencoded values taht are related by the unencoded
  relation. *)
  Lemma encode_relation_related (R : relation2 A) ea eb :
    (encode_relation R) ea eb →
    ∃ a b, decode ea = Some a ∧ decode eb = Some b ∧ R a b.
  Proof.
    rewrite /encode_relation.
    destruct (decode ea) as [|], (decode eb) as [|]; try done.
    intros ?. eexists _, _. done.
  Qed.

  Lemma encode_relation_decode_iff (R : relation2 A) ea eb (a b : A) :
    decode ea = Some a →
    decode eb = Some b →
    (encode_relation R) ea eb →
    R a b.
  Proof. rewrite /encode_relation. intros -> ->. done. Qed.

End preorders.

Section bumpers.
  Context `{!nvmFixedG Σ, hGD : nvmDeltaG Σ}.
  Context `{AbstractState ST}.

  Definition know_bumper (ℓ : loc) (bumper : ST → ST) : iProp Σ :=
    let encodedBumper e := encode <$> (bumper <$> decode e)
    in ⌜∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2⌝ ∗
       own bumpers_name ((◯ {[ ℓ := to_agree encodedBumper ]}) : bumpersR).

  Definition own_all_bumpers_gname γ encoded_bumpers :=
    own γ (● (to_agree <$> encoded_bumpers) : bumpersR).

  Definition own_all_bumpers encoded_bumpers :=
    own_all_bumpers_gname bumpers_name encoded_bumpers.

  Lemma own_all_bumpers_gname_alloc bumpers :
    ⊢ |==> ∃ γ, own_all_bumpers_gname γ bumpers ∗
                own γ (◯ ((to_agree <$> bumpers) : gmapUR _ (agreeR _))).
  Proof.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_discrete. split; first done.
    apply valid_to_agree_fmap.
  Qed.

  Lemma own_all_bumpers_persist γ encoded_bumpers :
    own_all_bumpers_gname γ encoded_bumpers ==∗
    own γ (●□ ((to_agree <$> encoded_bumpers) : gmapUR _ (agreeR _))).
  Proof. iApply own_update. apply auth_update_auth_persist. Qed.

  Lemma bumpers_frag_lookup γ (bumpers : gmap loc (positive → option positive))
        (ℓ : loc) (bumper : positive → option positive) :
    bumpers !! ℓ = Some bumper →
    own γ (◯ (to_agree <$> bumpers) : bumpersR) -∗
    own γ (◯ {[ ℓ := to_agree bumper ]}).
  Proof.
    intros look. f_equiv. simpl.
    apply auth_frag_mono.
    rewrite singleton_included_l.
    eexists _.
    rewrite lookup_fmap look.
    naive_solver.
  Qed.

End bumpers.

Definition increasing_list `{SqSubsetEq ST} (ss : list ST) :=
  ∀ i j s s', i < j → (ss !! i = Some s) → (ss !! j = Some s') → s ≠ s' ∧ s ⊑ s'.

Lemma increasing_list_singleton `{SqSubsetEq ST} (s : ST) : increasing_list [s].
Proof. intros [|][|]?????; try naive_solver. simplify_eq. lia. Qed.

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

  Definition know_inv ℓ ϕ : dProp Σ :=
    ⎡know_pred ℓ ϕ ∗ know_preorder_loc ℓ (⊑@{ST})⎤%I.

  Program Definition have_store_view ℓ t : dProp Σ :=
    MonPred (λ (TV : thread_view), ⌜t ≤ (store_view TV) !!0 ℓ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  (* Definition is_exclusive_loc ℓ := own exclusive_locs_name (◯ {[ ℓ ]}). *)

  Definition is_shared_loc ℓ := own shared_locs_name (◯ {[ ℓ ]}).

  (* _Exclusive_ points-to predicate. This predcate says that we know that the
  last events at [ℓ] corresponds to the *)
  Program Definition mapsto_ex (persisted : bool) (ℓ : loc) (ss : list ST) : dProp Σ :=
    (* MonPred (λ TV, *)
      (∃ (tP tStore : time) (abs_hist : gmap time ST),
        "%incrList" ∷ ⌜increasing_list ss⌝ ∗
        (* "isExclusiveLoc" ∷ ⎡ is_exclusive_loc ℓ ⎤ ∗ *)
        "#order" ∷ ⎡ know_preorder_loc ℓ (abs_state_relation) ⎤ ∗

        (* [tStore] is the last message and it agrees with the last state in ss. *)
        "%lookupV" ∷ ⌜abs_hist !! tStore = last ss⌝ ∗
        "%nolater" ∷ ⌜map_no_later abs_hist tStore⌝ ∗

        (* Ownership over the abstract history. *)
        "hist" ∷ ⎡ know_full_history_loc ℓ abs_hist ⎤ ∗

        "%slice" ∷ ⌜map_slice abs_hist tP tStore ss⌝ ∗

        (* We "have"/"know of" the three timestamps. *)
        "haveTStore" ∷ have_store_view ℓ tStore ∗
        "pers" ∷ if persisted then ⎡ persisted_loc ℓ tP ⎤ else ⌜tP = 0⌝)%I.

  Global Instance mapsto_ex_discretizable b ℓ ss :
    Discretizable (mapsto_ex b ℓ ss).
  Proof. destruct b; apply _. Qed.

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
      ∃ tP sP',
        "%sPInclSP'" ∷ ⌜ sP ⊑ sP' ⌝ ∗
        (* We have the persisted state in our store view. *)
        "%tPLe" ∷ ⌜ tP ≤ (store_view TV) !!0 ℓ ⌝ ∗
        "persisted" ∷ persisted_loc ℓ tP ∗
        "order" ∷ know_preorder_loc ℓ abs_state_relation ∗
        "knowFragHist" ∷ know_frag_history_loc ℓ {[ tP := sP' ]})%I _.
  Next Obligation. solve_proper. Qed.

  Program Definition know_flush_lb ℓ (s : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ (tF : nat) s',
        "%sInclS'" ∷ ⌜ s ⊑ s' ⌝ ∗
        (* Either the location is persisted or we have something in the flush
        view. The later case is for use after a crash where we don't have
        anything in the flush view. *)
        "viewFact" ∷ (⌜tF ≠ 0⌝ ∗ ⌜tF ≤ flush_view TV !!0 ℓ⌝  ∨
                      ⌜tF = 0⌝ ∗ persisted_loc ℓ 0) ∗
        (* ("%tFLe" ∷ ⌜ tF ≤ (flush_view TV) !!0 ℓ ⌝ ∨ *)
        (*            (⌜tF = 0⌝ ∗ persisted_loc ℓ 0)) ∗ *)
        (* (⌜ tF ≤ (flush_view TV) !!0 ℓ ⌝ ∨ ⌜tF = 0⌝ ∗ ) ∗ *)
        "order" ∷ know_preorder_loc ℓ abs_state_relation ∗
        "knowFragHist" ∷ know_frag_history_loc ℓ {[ tF := s' ]}
    )%I _.
  Next Obligation. solve_proper. Qed.

  Program Definition know_store_lb ℓ (s : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ (tS : nat) s',
        "%sInclS'" ∷ ⌜ s ⊑ s' ⌝ ∗
        "%tSLe" ∷ ⌜ tS ≤ (store_view TV) !!0 ℓ ⌝ ∗
        "order" ∷ know_preorder_loc ℓ abs_state_relation ∗
        "knowFragHist" ∷ know_frag_history_loc ℓ {[ tS := s' ]}
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

  (* Live expresses that once we read from [ℓ] we are sure to get a message that
  was written during this execution and not one that was recoverd. *)
  Definition live ℓ : dProp Σ :=
    ∃ (t : nat) CV,
      (* This disjunction entails that ϕ holds for the write *)
      "%storeDisj" ∷ ⌜0 ≠ t ∨ ℓ ∉ dom (gset _) CV⌝ ∗
      "%tvIn" ∷ monPred_in (∅, ∅, {[ ℓ := MaxNat t ]}) ∗
      "#crashed" ∷ ⎡crashed_at CV⎤.
      (* ∗ "#knowFragHist" ∷ ⎡know_frag_history_loc ℓ {[ t := s ]}⎤. *)

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

  Lemma know_store_lb_at_zero ℓ (s s' : ST) :
    s ⊑ s' →
    ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗
    ⎡ know_preorder_loc ℓ abs_state_relation ⎤ -∗
    know_store_lb ℓ s.
  Proof.
    iStartProof (iProp _). iIntros (incl ?) "?".
    iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia.
  Qed.

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

End points_to_shared.

(** Notation for the exclusive points-to predicate. *)
Notation "l ↦ ss" := (mapsto_ex false l ss) (at level 20).
Notation "l ↦ₚ ss" := (mapsto_ex true l ss) (at level 20).
(* Notation "l ↦ xs ; ys | P" := (mapsto_ex l xs ys P) (at level 20). *)

(** Notation for the shared points-to predicate. *)
(* Notation "l ↦ ( s1 , s2 , s3 )  | P" := (mapsto_shared l s1 s2 s3 P) (at level 20). *)
