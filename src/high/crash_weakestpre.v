From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import agree auth gset.
From iris.base_logic Require Import ghost_map.
From iris_named_props Require Import named_props.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require crash_weakestpre.

From self Require Import extra.
From self.base Require Import primitive_laws class_instances.
From self.high Require Export dprop resources lifted_modalities monpred_simpl.

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

Section wpc.
  Context `{hG : !nvmG Σ}.

  (* NOTE: The definition uses [i < j] and not [i ≤ j] in order to make the
  lemma [increasing_map_singleton] provable. When we use [increating_map] the
  relation [R] will always be reflexive, and hence this does not matter. The
  _knowledge_ that [R] is reflexive may not always be available however (since
  we may not know that [R] is in fact the encoding of some preorder, and hence
  this definition works best. *)
  Definition increasing_map (ss : gmap nat positive) (R : relation2 positive) :=
    ∀ i j (s s' : positive), i < j → (ss !! i = Some s) → (ss !! j = Some s') → R s s'.

  Lemma increasing_map_singleton t s R : increasing_map {[ t := s ]} R.
  Proof. intros ????? ?%lookup_singleton_Some ?%lookup_singleton_Some. lia. Qed.

  Lemma increasing_map_empty  R : increasing_map ∅ R.
  Proof. intros ????? [=]. Qed.

  (* Convert a message to a thread_view corresponding to what is stored in the
  message. *)
  Definition msg_to_tv (m : message) : thread_view :=
    (* NOTE: We use the [msg_persisted_after_view] and _not_ the
    [msg_persist_view]. This is because the [msg_persisted_after] can be
    transfered to the recovery program after a crash and the predicate then
    still holds. *)
    (m.(msg_store_view), m.(msg_persisted_after_view), ∅).

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)
  Definition interp : iProp Σ :=
    (∃ (hists : gmap loc (gmap time (message * positive)))
       (preds : gmap loc (positive → val → option (dProp Σ)))
       (orders : gmap loc (relation2 positive))
       (shared_locs : gset loc),
      (* We keep the points-to predicates to ensure that we know that the keys
      in the abstract history correspond to the physical history. This ensures
      that at a crash we know that the value recoreved after a crash has a
      corresponding abstract value. *)
      "ptsMap" ∷ ([∗ map] ℓ ↦ hist ∈ hists, ℓ ↦h (fst <$> hist)) ∗
      (* Agreement on the preorders and the ordered/sorted property. *)
      "allOrders" ∷ own_all_preorders orders ∗
      "ordered" ∷ ([∗ map] ℓ ↦ hist; order ∈ hists; orders,
                    ⌜increasing_map (snd <$> hist) order⌝) ∗
      (* The predicates hold. *)
      "map" ∷
        ([∗ map] ℓ ↦ hist; pred ∈ hists; preds,
          (* The predicate holds for each message in the history. *)
          ([∗ map] t ↦ p ∈ hist, let '(msg, encState) := p in
            (∃ (P : dProp Σ),
              ⌜pred encState msg.(msg_val) = Some P⌝ ∗ P (msg_to_tv msg)))) ∗
      (* Ownership over the full knowledge of the abstract history of _all_
      locations. *)
      "history" ∷ own_full_history ((λ (h : (gmap _ _)), snd <$> h) <$> hists) ∗
      (* Knowledge of all the predicates. *)
      "preds" ∷ own predicates_name (● (pred_to_ra <$> preds) : predicatesR) ∗
      (* Shared locations. *)
      "sharedLocs" ∷ own shared_locs_name (● (shared_locs : gsetUR _)) ∗
      "%mapShared" ∷
        ⌜map_Forall (λ _, map_Forall
          (* For shared locations the two persist views are equal. This enforces
          that shared locations can only be written to using release load and RMW
          operations. *)
          (λ _ '(msg, _), msg.(msg_persist_view) = msg.(msg_persisted_after_view)))
          (restrict shared_locs hists)⌝).

  Program Definition wpc_def s k E e (Φ : val → dProp Σ) (Φc : dProp Σ) : dProp Σ :=
    (* monPred_objectively Φc ∗ *)
    MonPred (λ V,
      ∀ TV,
        ⌜V ⊑ TV⌝ -∗
        validV (store_view TV) -∗
        interp -∗
        WPC (ThreadState e TV) @ s; k; E {{ λ res,
          let '(ThreadVal v TV') := res return _ in
            ⌜TV ⊑ TV'⌝ ∗ (* The operational semantics always grow the thread view, encoding this in the WPC is convenient. *)
            validV (store_view TV') ∗ (Φ v TV') ∗ interp
          }}{{ Φc (∅, ∅, ∅) }}
    )%I _.
  Next Obligation. solve_proper. Qed.

  (* This sealing follows the same ritual as the [wp] in Iris. *)
  Definition wpc_aux : seal (@wpc_def). by eexists. Qed.

  Global Instance expr_wpc : Wpc expr_lang (dProp Σ) stuckness nat := wpc_aux.(unseal).

  Lemma wpc_eq : wpc = wpc_def.
  Proof. rewrite -wpc_aux.(seal_eq). done. Qed.

  Global Instance wpc_ne s k E1 e n :
    Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) (wpc s k E1 e).
  Proof.
    rewrite wpc_eq. constructor => V. solve_proper.
  Qed.

  Global Instance wpc_proper s k E1 e :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (wpc s k E1 e).
  Proof.
    rewrite wpc_eq. constructor => V. solve_proper.
  Qed.

  (** The weakest precondition is defined in terms of the crash weakest precondition. *)
  Definition wp_def : Wp expr_lang (dProp Σ) stuckness :=
    λ s E e Φ, (WPC e @ s ; 0 ; E {{ Φ }} {{ True }})%I.
  Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
  Definition wp' := wp_aux.(unseal).
  (* Global Arguments wp' {Λ Σ _}. *)
  (* Check wp'. *)
  Global Existing Instance wp'.
  Lemma wp_eq : wp = @wp_def.
  Proof. rewrite -wp_aux.(seal_eq) //. Qed.

  Lemma wpc_bind K s k E1 (e : expr) Φ Φc :
    WPC e @ s; k; E1 {{ v, WPC fill K (of_val v) @ s; k; E1 {{ Φ }} {{ Φc }} }} {{ Φc }}
                      ⊢ WPC fill K e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (V).
    iIntros "WP".
    iIntros (TV) "%incl val interp".
    iDestruct ("WP" with "[% //] val interp") as "HI".
    rewrite nvm_fill_fill.
    iApply crash_weakestpre.wpc_bind.
    { apply: ectx_lang_ctx. }
    iApply (wpc_mono with "HI").
    2: { done. }
    iIntros ([v TV']) "(%cinl & val & wpc & interp)".
    iDestruct ("wpc" $! TV' with "[//] val interp") as "HI".
    rewrite nvm_fill_fill.
    simpl. rewrite /thread_of_val.
    iApply (wpc_strong_mono' with "HI"); try auto.
    iSplit.
    2: { iModIntro. iIntros "$". eauto. }
    iIntros ([??]) "[%incl' $]".
    iPureIntro. etrans; eassumption.
  Qed.

  Lemma wp_wpc s k E1 e Φ:
    WP e @ s ; E1 {{ Φ }} ⊢ WPC e @ s ; k ; E1 {{ Φ }} {{ True }}.
  Proof.
    iStartProof (iProp _).
    rewrite wp_eq /wp_def wpc_eq /wpc_def.
    iIntros (?) "H /=". iIntros (TV ?) "??".
    setoid_rewrite (monPred_at_pure ⊥).
    rewrite /crash_weakestpre.wpc_def crash_weakestpre.wpc_eq.
    iIntros (n).
    iApply wpc0_change_k.
    iApply ("H" $! TV with "[% //] [$] [$]").
  Qed.

  (*
  Lemma wpc_wp s k E1 e Φ Φc:
    WPC e @ s ; k ; E1 {{ Φ }} {{ Φc }} ⊢ WP e @ s ; E1 {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def wpc_eq. iIntros "H" (?).
    iApply wpc0_change_k.
    iApply (wpc0_strong_mono with "H"); auto. by apply omega_le_refl.
  Qed.
  *)

  Lemma wpc_strong_mono s1 s2 k1 k2 E1 E2 e Φ Ψ Φc Ψc `{!Objective Φc, !Objective Ψc} :
    s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 →
    WPC e @ s1; k1; E1 {{ Φ }} {{ Φc }} -∗
    (∀ v, Φ v -∗ |NC={E2}=> Ψ v) ∧ <disc> (Φc -∗ |C={E2}_k2=> Ψc) -∗
    WPC e @ s2; k2; E2 {{ Ψ }} {{ Ψc }}.
  Proof.
    intros ?? HE.
    rewrite wpc_eq.
    rewrite /wpc_def.
    iStartProof (iProp _). iIntros (tv).
    monPred_simpl. simpl.
    iIntros "wpc".
    iIntros (tv' ?) "conj".
    iIntros (TV ?) "??".
    iSpecialize ("wpc" $! TV with "[%] [$] [$]"); try eassumption.
    { etrans; eassumption. }
    iApply (wpc_strong_mono with "wpc"); try eassumption.
    iSplit.
    - iIntros ([??]) "(%incl & val & phi & int)".
      monPred_simpl.
      iDestruct "conj" as "[conj _]".
      iSpecialize ("conj" $! _).
      monPred_simpl.
      iSpecialize ("conj" $! _ with "[%] phi").
      { etrans. eassumption. eassumption. }
      rewrite ncfupd_unfold_at.
      iMod "conj" as "conj".
      iModIntro.
      iFrame "∗%".
    - monPred_simpl.
      iDestruct ("conj") as "[_ conj]".
      rewrite disc_unfold_at.
      iModIntro.
      iIntros "phi".
      monPred_simpl.
      iSpecialize ("conj" $! tv' with "[% //]").
      rewrite /cfupd.
      iIntros "HC".
      monPred_simpl.
      iSpecialize ("conj" with "[phi]").
      { iApply objective_at. iApply "phi". }
      iSpecialize ("conj" $! tv' with "[% //] [HC]").
      { iApply monPred_at_embed. done. }
      rewrite fupd_level_unfold_at.
      iApply fupd_level_mono; last iApply "conj".
      iApply objective_at.
  Qed.

  Lemma wpc_strong_mono' s1 s2 k1 k2 E1 E2 e Φ Ψ Φc Ψc `{!Objective Φc, !Objective Ψc} :
    s1 ⊑ s2 → k1 ≤ k2 → E1 ⊆ E2 →
    WPC e @ s1; k1; E1 {{ Φ }} {{ Φc }} -∗
    (∀ v, Φ v ={E2}=∗ Ψ v) ∧ <disc> (Φc -∗ |k2={E2}=> Ψc) -∗
    WPC e @ s2; k2; E2 {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros (???) "? H".
    iApply (wpc_strong_mono with "[$] [-]"); auto.
    iSplit.
    - iDestruct "H" as "(H&_)". iIntros. iMod ("H" with "[$]"). auto.
    - iDestruct "H" as "(_&H)". iModIntro.
      iIntros "HΦc C". iApply "H". iAssumption.
  Qed.

  Lemma ncfupd_wpc s k E1 e Φ Φc `{!Objective Φc} :
    <disc> (cfupd k E1 Φc) ∧ (|NC={E1}=> WPC e @ s; k; E1 {{ Φ }} {{ Φc }}) ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    iIntros "H".
    simpl.
    iIntros (?) "%incl val interp".
    iApply ncfupd_wpc.
    iSplit.
    - iDestruct "H" as "[H _]".
      rewrite disc_unfold_at.
      iModIntro.
      rewrite cfupd_unfold_at.
      iDestruct "H" as ">H".
      iModIntro.
      iApply objective_at.
      iApply "H".
    - iDestruct "H" as "[_ H]".
      rewrite ncfupd_unfold_at.
      iDestruct "H" as ">H".
      iModIntro.
      iApply ("H" with "[//] val interp").
  Qed.

  Lemma wpc_atomic_crash_modality s k E1 e Φ Φc
        `{!AtomicBase StronglyAtomic e, !Objective Φc} :
    <disc> (cfupd k E1 (Φc)) ∧
    (WP e @ s; E1 {{ v, |={E1}=> (|={E1}=>Φ v) ∧ <disc> cfupd k E1 (Φc) }}) ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    iIntros "H".
    simpl.
    iIntros (?) "%incl val interp".
    iApply wpc_atomic_crash_modality.
    iSplit; [iDestruct "H" as "[H _]"|iDestruct "H" as "[_ H]"].
    - rewrite disc_unfold_at. iModIntro.
      rewrite cfupd_unfold_at.
      iMod "H".
      iModIntro.
      iApply objective_at.
      iApply "H".
    - rewrite wp_eq. rewrite /wp_def.
      rewrite wpc_eq. rewrite /wpc_def.
      simpl.
      rewrite crash_weakestpre.wp_eq /crash_weakestpre.wp_def.
      iSpecialize ("H" with "[//] val interp").
      monPred_simpl.
      iApply (wpc_mono with "H"); last done.
      simpl.
      iIntros ([??]) "(? & ? & H & interp)".
      rewrite monPred_at_fupd.
      monPred_simpl.
      iDestruct "H" as ">H".
      (* rewrite monPred_at_and. *)
      iModIntro.
      iSplit; [iDestruct "H" as "[H _]"|iDestruct "H" as "[_ H]"].
      * rewrite monPred_at_fupd.
        iMod "H".
        iModIntro. iSplit; first done. iFrame.
      * rewrite disc_unfold_at.
        iModIntro.
        rewrite cfupd_unfold_at.
        iMod "H".
        iModIntro.
        iApply objective_at.
        iApply "H".
  Qed.

  Lemma wpc_value s k E1 (Φ : val → dProp Σ) (Φc : dProp Σ)
        `{!Objective Φc} (v : val) :
    ((|NC={E1}=> Φ v) : dProp _) ∧
    (<disc> |C={E1}_k=> Φc) ⊢ WPC of_val v @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    simpl.
    iIntros "H".
    iIntros (TV') "%lec hv i".
    iApply (wpc_value _ _ _ _ _ (ThreadVal _ _)).
    iSplit.
    - iFrame. iDestruct "H" as "(H & _)".
      rewrite ncfupd_unfold_at.
      iMod "H" as "H".
      iModIntro.
      iFrame.
      done.
    - iDestruct "H" as "(_ & HO)".
      rewrite disc_unfold_at.
      iModIntro.
      rewrite cfupd_unfold_at.
      rewrite objective_at.
      iFrame.
  Qed.

  Lemma wpc_value' s k E1 Φ Φc `{!Objective Φc} v :
    Φ v ∧ <disc> Φc ⊢ WPC of_val v @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply wpc_value.
    iSplit.
    - iModIntro. iDestruct "H" as "($&_)".
    - iDestruct "H" as "(_&H)". iModIntro. iModIntro. iFrame.
  Qed.

  (** * Derived rules *)

  Lemma wpc_mono s k E1 e Φ Ψ Φc Ψc `{!Objective Φc, !Objective Ψc} :
    (∀ v, Φ v ⊢ Ψ v) → (Φc ⊢ Ψc) → WPC e @ s; k; E1 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; k; E1 {{ Ψ }} {{ Ψc }}.
  Proof.
    iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono' with "H"); auto.
    iSplit.
    - iIntros (v) "?". by iApply HΦ.
    - iIntros "!> ? !>". by iApply HΦc.
  Qed.

  Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
  Proof. intros Hpost. rewrite wp_eq. apply: wpc_mono; done. Qed.

  Lemma wpc_atomic s k E1 e Φ Φc `{!AtomicBase StronglyAtomic e, !Objective Φc} :
    <disc> (|k={E1}=> Φc) ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ <disc> |k={E1}=> Φc }} ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply (wpc_atomic_crash_modality). iApply (bi.and_mono with "H").
    {
      f_equiv.
      iIntros "H HC".
      iFrame "H". }
    iIntros "H".
    iApply (wp_mono with "H"). iIntros (?).
    iIntros "H". iModIntro.
    iApply (bi.and_mono with "H"); auto.
    { f_equiv. iIntros "H HC". eauto. }
  Qed.

  (* Note that this also reverses the postcondition and crash condition, so we
  prove the crash condition first *)
  Lemma wpc_atomic_no_mask s k E1 e Φ Φc
        `{!AtomicBase StronglyAtomic e, !Objective Φc} :
    <disc> Φc ∧ WP e @ s; E1 {{ v, <disc> (|k={E1}=> Φc) ∧ (|={E1}=> Φ v) }} ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
   Proof.
    iIntros "Hc_wp".
    iApply wpc_atomic.
    iSplit.
    - iDestruct "Hc_wp" as "(?&_)". by do 2 iModIntro.
    - iDestruct "Hc_wp" as "[_ Hwp]".
      iApply (wp_mono with "Hwp").
      iIntros (x) "HΦ".
      iSplit.
      + iDestruct "HΦ" as "[_  >HΦc]". eauto.
      + iDestruct "HΦ" as "[HΦ _]". iModIntro. iMod "HΦ". by iModIntro.
  Qed.

End wpc.

