From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import agree auth.
From iris.base_logic Require Import ghost_map.
From Perennial.base_logic.lib Require Export ncfupd.
From Perennial.program_logic Require crash_weakestpre.

From self.base Require Import primitive_laws.
From self.high Require Export dprop resources lifted_modalities.

(** We define a few things about the resource algebra that that we use to encode
abstract histories. *)
Section abs_history_lemmas.
  Context `{hG : nvmG Σ}.
  Context `{Countable ST}.

  Implicit Types (abs_hist : abs_history ST) (ℓ : loc).

  Definition abs_hist_to_ra abs_hist : encoded_abs_historyR :=
    (to_agree ∘ encode) <$> abs_hist.

  Definition own_full_history (abs_hists : gmap loc (gmap time positive)) :=
    ghost_map_auth (abs_history_name) 1 abs_hists.
        (* ((● ((λ h, ● (to_agree <$> h)) <$> abs_hists)) : abs_historiesR). *)

  Definition know_full_history_loc ℓ abs_hist : iProp Σ :=
    ℓ ↪[ abs_history_name ] (encode <$> abs_hist).
    (* own abs_history_name ((◯ {[ ℓ := ● (abs_hist_to_ra abs_hist) ]}) : abs_historiesR). *)

  Definition know_full_encoded_history_loc ℓ (abs_hist : gmap time st) : iProp Σ :=
    ℓ ↪[ abs_history_name ] abs_hist.
    (* own abs_history_name ((◯ {[ ℓ := ● ((to_agree <$> abs_hist) : gmap _ (agreeR stO)) ]}) : abs_historiesR). *)

  Definition know_frag_history_loc ℓ abs_hist :=
    own abs_history_name ((◯ {[ ℓ := ◯ (abs_hist_to_ra abs_hist) ]}) : abs_historiesR).

  Lemma equivI_elim_own {A: cmra} `{Hin: inG Σ A} γ (a b: A):
    (a ≡ b) → own γ a ⊣⊢ own γ b.
  Proof. iIntros (Hequiv). f_equiv. eauto. Qed.

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
    destruct (hist' !! t) as [h|] eqn:leq, (hist !! t) as [h'|] eqn:leq';
      rewrite leq leq'; rewrite leq leq' in eq'; try inversion eq'; auto.
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
      rewrite ?leq leq'; rewrite ?leq ?leq' in eq'; try inversion eq'; auto.
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

End abs_history_lemmas.

Section predicates.
  Context `{!nvmG Σ}.

  Definition predO := st -d> val -d> optionO (dPropO Σ).

  Definition pred_to_ra (pred : st → val → option (dProp Σ)) : (@predicateR Σ) :=
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

Section wpc.
  Context `{!nvmG Σ}.

  (* NOTE: We can abstract this later if we need to. *)
  Definition increasing_map (ss : gmap nat positive) :=
    ∀ i j (s s' : positive), i ≤ j → (ss !! i = Some s) → (ss !! j = Some s') → (s ≤ s')%positive.

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)
  Definition interp : iProp Σ :=
    (∃ (hists : gmap loc (gmap time (message * st)))
       (preds : gmap loc (st → val → option (dProp Σ))),
      (* We keep the points-to predicates to ensure that we know that the keys
      in the abstract history correspond to the physical history. This ensures
      that on a crash we know that the value recoreved after a crash has a
      corresponding abstract value. *)
      ([∗ map] ℓ ↦ hist ∈ hists, ℓ ↦h (fst <$> hist)) ∗
      ([∗ map] ℓ ↦ hist; pred ∈ hists; preds,
        ⌜ increasing_map (snd <$> hist) ⌝ ∗
        (* The predicate hold. *)
        ([∗ map] t ↦ p ∈ hist,
           (∃ (P : dProp Σ),
             ⌜(pred) (snd p) (fst p).(msg_val) = Some P⌝ ∗
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

End wpc.
