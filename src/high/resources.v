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

(* Resource algebra used to represent agreement on which predicates are
associated with which locations. *)
Definition predicateR {Σ} := agreeR (positive -d> val -d> laterO (optionO (dPropO Σ))).
Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

(* Definition recPredicateR {Σ} := *)
(*   agreeR (positive -d> val -d> laterO (nvmG Σ -d> optionO (dPropO Σ))). *)
(* Definition recPredicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)). *)

Notation abs_history := (gmap time).

(* Resource algebras that for each location stores the encoded abstract states
associated with each message/store. *)
Definition encoded_abs_historyR := gmapUR time (agreeR positiveO).
Definition enc_abs_histories := gmap loc (gmap time positive).

Definition know_abs_historiesR := authR (gmapUR loc (gmapUR time (agreeR positiveO))).

(* Resourcce algebra that stores the encoded preorder for each location. *)
Definition relationO := leibnizO (positive → positive → Prop).
Definition preordersR := authR (gmapUR loc (agreeR relationO)).

(* Resource algebra that contains all the locations that are _shared_. *)
Definition shared_locsR := authR (gsetUR loc).

Class nvmHighG Σ := NvmHighG {
  (* "Global" ghost names *)
  abs_history_name : gname;
  know_abs_history_name : gname;
  predicates_name : gname;
  recovery_predicates_name : gname;
  preorders_name : gname;
  shared_locs_name : gname;
  exclusive_locs_name : gname;
  (* Functors *)
  ra_inG :> inG Σ (@predicatesR Σ);
  ra_inG' :> inG Σ know_abs_historiesR;
  abs_histories :> ghost_mapG Σ loc (gmap time positive);
  preordersG :> inG Σ preordersR;
  shared_locsG :> inG Σ shared_locsR
}.

Class nvmG Σ := NvmG {
  nvmG_baseG :> nvmBaseG Σ;
  nvmG_highG :> nvmHighG Σ;
}.

Class AbstractState T := {
  abs_state_eqdecision :> EqDecision T;
  abs_state_countable :> Countable T;
  abs_state_relation : relation2 T;
  abs_state_preorder :> PreOrder abs_state_relation;
}.

Instance abstract_state_sqsubseteq `{AbstractState T} : SqSubsetEq T :=
  abs_state_relation.

Global Instance discretizable_ghost_map_elem `{ghost_mapG Σ K V} ℓ γ v :
  own_discrete.Discretizable (ℓ ↪[γ] v).
Proof. rewrite ghost_map_elem_eq /ghost_map_elem_def. apply _. Qed.

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{hG : nvmG Σ}.
  Context `{Countable ST}.

  Implicit Types (abs_hist : gmap time ST) (ℓ : loc).
  Implicit Types (abs_hists : gmap loc (gmap time positive)).

  Definition abs_hist_to_ra abs_hist : encoded_abs_historyR :=
    (to_agree ∘ encode) <$> abs_hist.

  Definition own_full_history_gname γ1 γ2 abs_hists : iProp Σ :=
    ghost_map_auth γ1 1 abs_hists ∗
    own γ2
        (● ((λ m : gmap _ _, to_agree <$> m) <$> abs_hists) : know_abs_historiesR).

  Definition own_full_history abs_hists : iProp Σ :=
    own_full_history_gname abs_history_name know_abs_history_name abs_hists.

  Definition know_full_history_loc ℓ abs_hist : iProp Σ :=
    ℓ ↪[ abs_history_name ] (encode <$> abs_hist).

  Definition know_full_encoded_history_loc ℓ (abs_hist : gmap time positive) : iProp Σ :=
    ℓ ↪[ abs_history_name ] abs_hist.

  Definition know_frag_history_loc ℓ (abs_hist : abs_history ST) : iProp Σ :=
    ∃ enc,
      ⌜(decode <$> enc = Some <$> abs_hist)⌝ ∗
      own know_abs_history_name (◯ {[ ℓ := to_agree <$> enc ]}).

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
    to_agree <$> hist' ≡ abs_hist_to_ra hist →
    hist' = encode <$> hist.
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
    ⌜∃ hist, hists !! ℓ = Some (hist) ∧ (Some <$> part_hist) ⊆ (decode <$> hist)⌝.
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
      (* rewrite map_fmap_compose. *)
      (* rewrite !map_fmap_singleton. *)
      apply singleton_included_l.
      eexists _.
      rewrite lookup_fmap.
      rewrite lookHist.
      simpl.
      split; f_equiv. }
    iExists {[ t := encS ]}.
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

Section predicates.
  Context `{!nvmG Σ}.

  Definition predO := positive -d> val -d> optionO (dPropO Σ).

  Definition pred_to_ra (pred : positive → val → option (dProp Σ)) : (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  Definition preds_to_ra (preds : gmap loc (positive → val → option (dProp Σ)))
    : gmapUR loc (@predicateR Σ) := pred_to_ra <$> preds.

  Definition know_all_preds preds :=
      own predicates_name (● (pred_to_ra <$> preds) : predicatesR).

  Definition encode_predicate `{Countable s}
             (ϕ : s → val → dProp Σ) : positive → val → option (dProp Σ) :=
    λ encS v, (λ s, ϕ s v) <$> decode encS.

  Definition know_pred `{Countable s}
      (ℓ : loc) (ϕ : s → val → dProp Σ) : iProp Σ :=
    own predicates_name (◯ {[ ℓ := pred_to_ra (encode_predicate ϕ) ]} : predicatesR).

  Lemma know_predicates_alloc preds :
    ⊢ |==> ∃ γ, own γ ((● (pred_to_ra <$> preds)) : predicatesR).
  Proof.
    iMod (own_alloc _) as "$"; last done.
    apply auth_auth_valid.
    intros ℓ.
    rewrite lookup_fmap.
    by case (preds !! ℓ).
  Qed.

  Lemma know_pred_agree `{Countable s} ℓ (ϕ : s → val → dProp Σ) (preds : gmap loc predO) :
    know_all_preds preds -∗
    know_pred ℓ ϕ -∗
    (∃ (o : predO),
       ⌜preds !! ℓ = Some o⌝ ∗ (* Some encoded predicate exists. *)
       ▷ (o ≡ encode_predicate ϕ)).
  Proof.
    iIntros "O K".
    rewrite /know_all_preds /know_pred.
    iDestruct (own_valid_2 with "O K") as "H".
    iDestruct (auth_both_validI with "H") as "[tmp val]".
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
      rewrite /pred_to_ra.
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

End predicates.

(*
Section recovery_predicates.
  Context `{!nvmG Σ}.

  Definition recPredO := positive -d> val -d> optionO (nvmG Σ -d> dPropO Σ).

  Definition pred_to_ra (pred : positive → val → option (nvmG Σ → dProp Σ)) :
    (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  Definition preds_to_ra (preds : gmap loc (positive → val → option (dProp Σ)))
    : gmapUR loc (@predicateR Σ) := pred_to_ra <$> preds.

  Definition know_all_preds preds :=
      own predicates_name (● (pred_to_ra <$> preds) : predicatesR).

  Definition encode_predicate `{Countable s}
             (ϕ : s → val → dProp Σ) : positive → val → option (dProp Σ) :=
    λ encS v, (λ s, ϕ s v) <$> decode encS.

  Definition know_pred `{Countable s}
      (ℓ : loc) (ϕ : s → val → dProp Σ) : iProp Σ :=
    own predicates_name (◯ {[ ℓ := pred_to_ra (encode_predicate ϕ) ]} : predicatesR).

  Lemma know_predicates_alloc preds :
    ⊢ |==> ∃ γ, own γ ((● (pred_to_ra <$> preds)) : predicatesR).
  Proof.
    iMod (own_alloc _) as "$"; last done.
    apply auth_auth_valid.
    intros ℓ.
    rewrite lookup_fmap.
    by case (preds !! ℓ).
  Qed.

End recovery_predicates.
*)

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
  Context `{hG : nvmG Σ}.
  Context `{Countable A}.

  Definition encode_relation (R : relation2 A) : relation2 positive :=
    λ (a b : positive), default False (R <$> decode a <*> decode b).

  Lemma encode_relation_iff (R : relation2 A) (a b : A) :
    R a b ↔ (encode_relation R) (encode a) (encode b).
  Proof.
    rewrite /encode_relation.
    rewrite !decode_encode.
    reflexivity.
  Qed.

  Definition own_all_preorders_gname γ (preorders : gmap loc (relation2 positive)) :=
    own γ (● ((to_agree <$> preorders) : gmapUR _ (agreeR relationO))).

  Definition own_all_preorders (preorders : gmap loc (relation2 positive)) :=
    own_all_preorders_gname preorders_name preorders.

  Definition own_preorder_loc ℓ (preorder : relation2 A) : iProp Σ :=
    own preorders_name (◯ ({[ ℓ := to_agree (encode_relation preorder) ]})).

  Global Instance persistent_own_preorder_loc ℓ preorder :
    Persistent (own_preorder_loc ℓ preorder).
  Proof. apply _. Qed.

  Lemma own_all_preorders_gname_alloc (preorders : gmap loc (relation2 positive)) :
    ⊢ |==> ∃ γ, own_all_preorders_gname γ preorders.
  Proof.
    iMod (own_alloc _) as "$"; last done.
    apply auth_auth_valid.
    intros ℓ.
    rewrite lookup_fmap.
    by case (preorders !! ℓ).
  Qed.

  Lemma orders_lookup ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders orders -∗
    own_preorder_loc ℓ order2 -∗
    ⌜ order1 = encode_relation order2 ⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (own_valid_2 with "auth frag") as %[incl _]%auth_both_valid_discrete.
    iPureIntro.
    move: incl.
    rewrite singleton_included_l.
    intros [y [eq incl]].
    move: incl.
    rewrite lookup_fmap in eq.
    rewrite look in eq.
    apply equiv_Some_inv_r' in eq.
    destruct eq as [y' [look' eq]].
    rewrite eq.
    rewrite <- look'.
    rewrite Some_included_total.
    rewrite to_agree_included.
    intros eq'.
    rewrite eq'.
    done.
  Qed.

  (* If we know that two encoded values are related by en encoded relation, then
  we can "recover" rela unencoded values taht are related by the unencoded
  relation. *)
  Lemma encode_relation_related (R : relation2 A) ea eb :
    (encode_relation R) ea eb →
    ∃ a b, decode ea = Some a ∧ decode eb = Some b ∧ R a b.
  Proof.
    rewrite /encode_relation.
    destruct (decode ea) as [|a], (decode eb) as [|b]; try done.
    intros ?. eexists _, _. done.
  Qed.

  Lemma encode_relation_decode_iff (R : relation2 A) ea eb (a b : A) :
    decode ea = Some a →
    decode eb = Some b →
    (encode_relation R) ea eb →
    R a b.
  Proof. rewrite /encode_relation. intros -> ->. done. Qed.

End preorders.

Section points_to_shared.
  Context `{!nvmG Σ}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).

  Definition abs_hist_to_ra_old
             (abs_hist : gmap time (message * positive)) : encoded_abs_historyR :=
    (to_agree ∘ snd) <$> abs_hist.

  Lemma singleton_included_l' `{Countable K} `{CmraTotal A} (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  Definition increasing_list `{AbstractState ST} (ss : list ST) :=
    ∀ i j (s s' : ST), i ≤ j → (ss !! i = Some s) → (ss !! j = Some s') → s ⊑ s'.

  (* _Exclusive_ points-to predicate. This predcate says that we know that the
  last events at [ℓ] corresponds to the *)
  Definition mapsto_ex `{AbstractState ST}
             ℓ (ss1 ss2 : list ST)
             (ϕ : ST → val → dProp Σ) : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time) (abs_hist : abs_history ST),

      "%incrList" ∷ ⌜ increasing_list (ss1 ++ ss2) ⌝ ∗
      "#knowOrder" ∷ ⎡ own_preorder_loc ℓ ((⊑@{ST})) ⎤ ∗

      "%lookupP" ∷ ⌜abs_hist !! tPers = head ss2⌝ ∗ (* Note: This also ensures that [ss2] is non-empty :) *)
      (* [tStore] is the last message and it agrees with the last state in ss2. *)
      "%lookupV" ∷ ⌜abs_hist !! tStore = last ss2⌝ ∗
      "%nolater" ∷ ⌜(∀ t', tStore < t' → abs_hist !! t' = None)⌝ ∗

      (* Ownership over the abstract history. *)
      "hist" ∷ ⎡know_full_history_loc ℓ abs_hist⎤ ∗
      (* Knowledge of the predicate. *)
      "knowPred" ∷ ⎡know_pred ℓ ϕ⎤ ∗

      "%slice" ∷ ⌜map_slice abs_hist tGlobalPers tStore (ss1 ++ ss2)⌝ ∗

      (* We "have"/"know of" the three timestamps. *)
      "%know" ∷ monPred_in ({[ ℓ := MaxNat tStore ]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      "per" ∷ ⎡persisted ({[ ℓ := MaxNat tGlobalPers ]} : view)⎤
    ).

  Global Instance mapsto_ex_discretizable `{AbstractState ST} ℓ ss1 ss2 ϕ :
    Discretizable (mapsto_ex ℓ ss1 ss2 ϕ).
  Proof. apply _. Qed.

  (* This definition uses an existentially quantified [s']. We do this such that
  owning [know_global_per_lower_bound ℓ s] before a crash also results in owning
  exactly the same, [know_global_per_lower_bound ℓ s], after a crash. Had the
  definition said that _exactly_ [s] was persisted at [t] then we would have a
  different state after a crash, since after a crash there is only a single
  entry in the history for [ℓ] and that entry may refer to any abstract state
  greater than [s]. Said in another way, this definition allows for weakening
  (lowering the state) which we do after a crash to get a simpler (but just as
  useful) interaction with the post crash modality. *)
  Definition know_global_per_lower_bound `{AbstractState ST} (ℓ : loc) (s : ST) : dProp Σ :=
    ∃ t s', ⌜ s ⊑ s' ⌝ ∗
            ⎡ own_preorder_loc ℓ abs_state_relation ∗
              persisted {[ ℓ := MaxNat t ]} ∗
              know_frag_history_loc ℓ {[ t := s' ]} ⎤.

  Program Definition know_persist_lower_bound `{AbstractState ST} (ℓ : loc) (s : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ (t : nat) s',
        ⌜ s ⊑ s' ⌝ ∗
        ⌜t ≤ (persist_view TV) !!0 ℓ⌝ ∗
        own_preorder_loc ℓ abs_state_relation ∗
        know_frag_history_loc ℓ {[ t := s' ]}
    )%I _.
  Next Obligation. solve_proper. Qed.

  Program Definition know_store_lower_bound `{AbstractState ST} (ℓ : loc) (s : ST) : dProp Σ :=
    MonPred (λ TV,
      ∃ (t : nat) s',
        ⌜ s ⊑ s' ⌝ ∗
        ⌜t ≤ (store_view TV) !!0 ℓ⌝ ∗
        own_preorder_loc ℓ abs_state_relation ∗
        know_frag_history_loc ℓ {[ t := s' ]}
    )%I _.
  Next Obligation. solve_proper. Qed.

  Definition mapsto_shared `{AbstractState ST}
             ℓ (s1 s2 s3 : ST) (ϕ : ST → val → dProp Σ) : dProp Σ :=
    "knowPred" ∷ ⎡ know_pred ℓ ϕ ⎤ ∗
    "isSharedLoc" ∷ ⎡ own shared_locs_name (◯ {[ ℓ ]}) ⎤ ∗
    "globalPerLB" ∷ know_global_per_lower_bound ℓ s1 ∗
    "persistLB" ∷ know_persist_lower_bound ℓ s2 ∗
    "storeLB" ∷ know_store_lower_bound ℓ s3.

  Global Instance know_persist_lower_bound_persistent `{AbstractState ST}
         ℓ (s : ST) : Persistent (know_persist_lower_bound ℓ s).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Global Instance know_store_lower_bound_persistent `{AbstractState ST}
         ℓ (s : ST) : Persistent (know_store_lower_bound ℓ s).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Lemma know_persist_lower_bound_at_zero `{AbstractState ST} ℓ (s s' : ST) :
    s ⊑ s' →
    ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗
    ⎡ own_preorder_loc ℓ abs_state_relation ⎤ -∗
    know_persist_lower_bound ℓ s.
  Proof.
    iStartProof (iProp _). iIntros (incl ?) "?".
    iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia.
  Qed.

  Lemma know_store_lower_bound_at_zero `{AbstractState ST} ℓ (s s' : ST) :
    s ⊑ s' →
    ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗
    ⎡ own_preorder_loc ℓ abs_state_relation ⎤ -∗
    know_store_lower_bound ℓ s.
  Proof.
    iStartProof (iProp _). iIntros (incl ?) "?".
    iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia.
  Qed.

End points_to_shared.

(** Notation for the exclusive points-to predicate. *)
Notation "l ↦ xs ; ys | P" := (mapsto_ex l xs ys P) (at level 20).

(** Notation for the shared points-to predicate. *)
Notation "l ↦ ( s1 , s2 , s3 )  | P" := (mapsto_shared l s1 s2 s3 P) (at level 20).
