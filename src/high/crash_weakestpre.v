From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import agree auth.
From iris.base_logic Require Import ghost_map.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require crash_weakestpre.

From self.base Require Import primitive_laws class_instances.
From self.high Require Export dprop resources lifted_modalities.

Global Instance discretizable_ghost_map_elem `{ghost_mapG Σ K V} ℓ γ v :
  own_discrete.Discretizable (ℓ ↪[γ] v).
Proof. rewrite ghost_map_elem_eq /ghost_map_elem_def. apply _. Qed.

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{hG : nvmG Σ}.
  Context `{Countable ST}.

  Implicit Types (abs_hist : gmap time ST) (ℓ : loc).

  Definition abs_hist_to_ra abs_hist : encoded_abs_historyR :=
    (to_agree ∘ encode) <$> abs_hist.

  Definition own_full_history (abs_hists : gmap loc (gmap time positive)) :=
    ghost_map_auth (abs_history_name) 1 abs_hists.

  Definition know_full_history_loc ℓ abs_hist : iProp Σ :=
    ℓ ↪[ abs_history_name ] (encode <$> abs_hist).

  Definition know_full_encoded_history_loc ℓ (abs_hist : gmap time positive) : iProp Σ :=
    ℓ ↪[ abs_history_name ] abs_hist.

  Definition know_frag_history_loc ℓ (abs_hist : abs_history ST) : iProp Σ :=
    True. (* FIXME *)
    (* own abs_history_name ((◯ {[ ℓ := ◯ (abs_hist_to_ra abs_hist) ]}) : abs_historiesR). *)

  Lemma know_full_equiv ℓ abs_hist :
    know_full_history_loc ℓ abs_hist ⊣⊢ know_full_encoded_history_loc ℓ (encode <$> abs_hist).
  Proof.
    done.
    (* apply equivI_elim_own. *)
    (* do 3 f_equiv. *)
    (* rewrite /abs_hist_to_ra. *)
    (* rewrite map_fmap_compose. *)
    (* done. *)
  Qed.

  Lemma abs_hist_to_ra_inj hist hist' :
    abs_hist_to_ra hist' ≡ abs_hist_to_ra hist →
    hist' = hist.
  Proof.
    intros eq.
    apply: map_eq. intros t.
    pose proof (eq t) as eq'.
    rewrite !lookup_fmap in eq'.
    destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq'; try inversion eq'; auto.
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
    destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq'; try inversion eq'; auto.
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
    iIntros "O K".
  Admitted.
  (*   iDestruct (own_valid_2 with "O K") as %[Incl _]%auth_both_valid_discrete. *)
  (*   iPureIntro. *)
  (*   apply singleton_included_l in Incl as [encHist' [look incl]]. *)
  (*   rewrite lookup_fmap in look. *)
  (*   destruct (hists !! ℓ) as [hist'|] eqn:histsLook. *)
  (*   2: { rewrite histsLook in look. inversion look. } *)
  (*   rewrite histsLook in look. *)
  (*   simpl in look. *)
  (*   apply Some_equiv_inj in look. *)
  (*   f_equiv. *)
  (*   apply abs_hist_to_ra_agree. *)
  (*   apply Some_included in incl as [eq|incl]. *)
  (*   - rewrite <- eq in look. *)
  (*     apply auth_auth_inj in look as [_ eq']. *)
  (*     done. *)
  (*   - rewrite <- look in incl. *)
  (*     assert (● (to_agree <$> hist') ≼ ● (to_agree <$> hist') ⋅ ◯ (ε : gmapUR _ _)) as incl'. *)
  (*     { eexists _. reflexivity. } *)
  (*     pose proof (transitivity incl incl') as incl''. *)
  (*     apply auth_auth_included in incl''. *)
  (*     done. *)
  (* Qed. *)

  Lemma own_frag_history_agree ℓ part_hist hists :
    own_full_history hists -∗
    know_frag_history_loc ℓ part_hist -∗
    ⌜∃ hist, hists !! ℓ = Some (encode <$> hist) ∧ part_hist ⊆ hist⌝.
  Proof.
    iIntros "O K".
  Admitted.

End abs_history_lemmas.

Section predicates.
  Context `{!nvmG Σ}.

  Definition predO := positive -d> val -d> optionO (dPropO Σ).

  Definition pred_to_ra (pred : positive → val → option (dProp Σ)) : (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  Definition know_all_preds preds :=
      own predicates_name (● (pred_to_ra <$> preds) : predicatesR).

  Definition know_pred `{Countable s}
      (ℓ : loc) (ϕ : s → val → dProp Σ) : iProp Σ :=
    own predicates_name (◯ {[ ℓ := pred_to_ra (λ s' v, (λ s, ϕ s v) <$> decode s') ]} : predicatesR).

  Lemma know_pred_agree `{Countable s} ℓ (ϕ : s → val → dProp Σ) (preds : gmap loc predO) :
    know_all_preds preds -∗
    know_pred ℓ ϕ -∗
    (∃ (o : predO),
       ⌜ preds !! ℓ = Some o ⌝ ∗
       ▷ (o ≡ λ s' v, (λ s, ϕ s v) <$> decode s')).
  Proof.
    iIntros "O K".
    rewrite /know_all_preds.
    rewrite /know_pred.
    iDestruct (own_valid_2 with "O K") as "H".
    iDestruct (auth_both_validI with "H") as "[H A]".
    iDestruct "H" as (c) "eq".
    rewrite gmap_equivI.
    iDestruct ("eq" $! ℓ) as "HI".
    rewrite lookup_fmap.
    rewrite lookup_op.
    rewrite lookup_singleton.
    case (c !! ℓ).
    - admit.
    - rewrite right_id.
      destruct (preds !! ℓ) as [o|] eqn:eq; rewrite eq.
      2: { simpl. iDestruct "HI" as %HI. inversion HI. }
      iExists o.
      iSplit; first done.
      simpl.
      rewrite !option_equivI.
      rewrite agree_equivI.
      rewrite !discrete_fun_equivI. iIntros (state).
      iDestruct ("HI" $! state) as "HI".
      rewrite !discrete_fun_equivI. iIntros (v).
      iDestruct ("HI" $! v) as "HI".
      rewrite later_equivI_1.
      done.
    Admitted.

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

(* Workaround for universe issues in stdpp. *)
Definition relation2 A := A -> A -> Prop.

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

  Definition own_all_preorders (preorders : gmap loc (relation2 positive)) :=
    own preorders_name (● ((to_agree <$> preorders) : gmapUR _ (agreeR relationO))).

  Definition own_preorder_loc ℓ (preorder : relation2 A) : iProp Σ :=
    own preorders_name (◯ ({[ ℓ := to_agree (encode_relation preorder) ]})).

  Global Instance persistent_own_preorder_loc ℓ preorder : Persistent (own_preorder_loc ℓ preorder).
  Proof. apply _. Qed.

  (* Global Instance discretizable_know_full_history_loc ℓ ord : *)
  (*   own_discrete.Discretizable (own_preorder_loc ℓ ord). *)
  (* Proof. *)
  (*   apply _.  *)

  Lemma orders_lookup ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders orders -∗
    own_preorder_loc ℓ order2 -∗
    ⌜ order1 = encode_relation order2 ⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (own_valid_2 with "auth frag") as %[incl _]%auth_both_valid_discrete.
    (* move: incl. *)
    (* rewrite -> singleton_included_l. *)
    (* rewrite singleton_included_l in incl. *)
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

End preorders.

Section wpc.
  Context `{!nvmG Σ}.

  (* NOTE: We can abstract this later if we need to. *)
  Definition increasing_map (ss : gmap nat positive) (R : relation2 positive) :=
    ∀ i j (s s' : positive), i ≤ j → (ss !! i = Some s) → (ss !! j = Some s') → R s s'.

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)
  Definition interp : iProp Σ :=
    (∃ (hists : gmap loc (gmap time (message * positive)))
       (preds : gmap loc (positive → val → option (dProp Σ)))
       (orders : gmap loc (relation2 positive)),
      (* We keep the points-to predicates to ensure that we know that the keys
      in the abstract history correspond to the physical history. This ensures
      that on a crash we know that the value recoreved after a crash has a
      corresponding abstract value. *)
      ([∗ map] ℓ ↦ hist ∈ hists, ℓ ↦h (fst <$> hist)) ∗
      (* Agreement on the preorders and the ordered/sorted property. *)
      own_all_preorders orders ∗
      ([∗ map] ℓ ↦ hist; order ∈ hists; orders, ⌜increasing_map (snd <$> hist) order⌝) ∗

      ([∗ map] ℓ ↦ hist; pred ∈ hists; preds,
        (* ⌜ ∃ (T : loc_info), True ⌝ ∗ *)
        (* ⌜ increasing_map (snd <$> hist) ⌝ ∗ (* FIXME *) *)
        (* The predicate hold. *)
        ([∗ map] t ↦ p ∈ hist,
           (∃ (P : dProp Σ),
             ⌜(pred) (snd p) (fst p).(msg_val) = Some P⌝ ∗ (* Should this be ≡ *)
             P (msg_to_tv (fst p))))) ∗
      (* Ownership over the full knowledge of the abstract history of _all_
      locations. *)
      own_full_history ((λ (h : (gmap _ _)), snd <$> h) <$> hists) ∗
      (* Knowledge of all the predicates. *)
      own predicates_name (● (pred_to_ra <$> preds) : predicatesR)).

  Program Definition wpc_def s k E e (Φ : val → dProp Σ) (Φc : dProp Σ) : dProp Σ :=
    (* monPred_objectively Φc ∗ *)
    MonPred (λ V,
      ∀ TV,
        ⌜V ⊑ TV⌝ -∗
        validV (store_view TV) -∗
        interp -∗
        WPC (ThreadState e TV) @ s; k; E {{ λ res,
          let '(ThreadVal v TV') := res return _ in
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
    iIntros ([v TV']) "(val & wpc & interp)".
    iDestruct ("wpc" $! TV' with "[//] val interp") as "HI".
    rewrite nvm_fill_fill.
    simpl. rewrite /thread_of_val.
    iApply (wpc_crash_mono with "[] HI").
    iModIntro.
    iIntros "$".
    (* iApply (wpc_strong_mono' with "HI"); eauto. *)
    (* iSplit. *)
    (* - admit. *)
    (* - iModIntro. iIntros "H". iModIntro. *)
    (*   iApply monPred_mono. done. *)
    (* Abort. *)
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
  Lemma ncfupd_wpc s k E1 e Φ Φc :
    <disc> (cfupd k E1 Φc) ∧ (|NC={E1}=> WPC e @ s; k; E1 {{ Φ }} {{ Φc }}) ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
  Admitted.

  Lemma wpc_atomic_crash_modality s k E1 e Φ Φc `{!Atomic StronglyAtomic e} :
    <disc> (cfupd k E1 (Φc)) ∧
    (WP e @ s; E1 {{ v, |={E1}=> (|={E1}=>Φ v) ∧ <disc> cfupd k E1 (Φc) }}) ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    iIntros "H".
  Admitted.

  Lemma wpc_value s k E1 (Φ : val → dProp Σ) (Φc : dProp Σ) `{!Objective Φc} (v : val) :
    ((|NC={E1}=> Φ v) : dProp _) ∧ (<disc> |C={E1}_k=> Φc) ⊢ WPC of_val v @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (TV).
    simpl.
    iIntros "H".
    iIntros (TV') "%lec hv i".
    iApply (wpc_value _ _ _ _ _ (ThreadVal _ _)).
    iSplit.
    - iFrame. iDestruct "H" as "(H & _)".
      iApply monPred_mono.
      * apply lec.
      * rewrite ncfupd_eq.
        iApply "H".
    - iDestruct "H" as "(_ & HO)".
      rewrite disc_unfold_at.
      simpl.
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

  Lemma wpc_mono s k E1 e Φ Ψ Φc Ψc :
    (∀ v, Φ v ⊢ Ψ v) → (Φc ⊢ Ψc) → WPC e @ s; k; E1 {{ Φ }} {{ Φc }} ⊢ WPC e @ s; k; E1 {{ Ψ }} {{ Ψc }}.
  Proof.
  Admitted.
  (*   iIntros (HΦ HΦc) "H"; iApply (wpc_strong_mono' with "H"); auto. *)
  (*   iSplit. *)
  (*   - iIntros (v) "?". by iApply HΦ. *)
  (*   - iIntros "!> ? !>". by iApply HΦc. *)
  (* Qed. *)

  Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
  Proof. intros Hpost. rewrite wp_eq. apply wpc_mono; done. Qed.

  Lemma wpc_atomic s k E1 e Φ Φc `{!Atomic StronglyAtomic e} :
    <disc> (|k={E1}=> Φc) ∧ WP e @ s; E1 {{ v, (|={E1}=> Φ v) ∧ <disc> |k={E1}=> Φc }} ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "H". iApply (wpc_atomic_crash_modality); iApply (bi.and_mono with "H").
    {
      f_equiv.
      iStartProof (iProp _). iIntros (tv).
      rewrite uPred_fupd_level_eq.
      rewrite /uPred_fupd_level_def.
      simpl.
      iIntros "H HC".
      eauto.
      admit. }
    iIntros "H".
    iApply (wp_mono with "H"). iIntros (?).
    iIntros "H". iModIntro.
    iApply (bi.and_mono with "H"); auto.
    { f_equiv. admit. (* iIntros "H HC". eauto. *) }
  Admitted.

  (* note that this also reverses the postcondition and crash condition, so we
  prove the crash condition first *)
  Lemma wpc_atomic_no_mask s k E1 e Φ Φc `{!AtomicBase StronglyAtomic e} :
    <disc> Φc ∧ WP e @ s; E1 {{ v, <disc> (|k={E1}=> Φc) ∧ (|={E1}=> Φ v) }} ⊢
    WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
  Admitted.
  (*   iIntros "Hc_wp". *)
  (*   iApply wpc_atomic. *)
  (*   iSplit. *)
  (*   - iDestruct "Hc_wp" as "(?&_)". iModIntro. *)
  (*     iApply fupd_level_mask_intro_discard; [ set_solver+ | ]. *)
  (*     eauto. *)
  (*   - iDestruct "Hc_wp" as "[_ Hwp]". *)
  (*     iApply (wp_mono with "Hwp"). *)
  (*     iIntros (x) "HΦ". *)
  (*     iSplit. *)
  (*     + iDestruct "HΦ" as "[_  >HΦc]". eauto. *)
  (*     + iDestruct "HΦ" as "[HΦ _]". iModIntro. *)
  (*       iMod "HΦ" as "HΦ". *)
  (*       iApply fupd_level_mask_intro_discard; [ set_solver+ | ]; iFrame. *)
  (* Qed. *)
End wpc.
