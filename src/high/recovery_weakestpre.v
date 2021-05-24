(* Implementation of the recovery weakest precondition for NvmLang. *)
From stdpp Require Import sets.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import ghost_map.
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require Import recovery_weakestpre.
From Perennial.program_logic Require Import recovery_adequacy.

From self Require Import view.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop.
From self.high Require Import resources weakestpre crash_weakestpre post_crash_modality.

Definition restrict `{FinMap K M, ElemOf K D, !RelDecision (∈@{D})} {A} (s : D) (m : M A) :=
  filter (λ '(k, _), k ∈ s) m.

Section restrict.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.

  Lemma restrict_lookup_Some (s : D) (m : M A) (k : K) (x : A) :
    restrict s m !! k = Some x → (m !! k = Some x) ∧ k ∈ s.
  Proof. by rewrite map_filter_lookup_Some. Qed.

  Lemma restrict_superset_id (s : D) (m : M A) :
    dom _ m ⊆ s → restrict s m = m.
  Proof.
    intros Hsub.
  Admitted.

  Lemma restrict_dom_subset (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) ≡ s.
  Proof.
    intros Hsub.
    rewrite /restrict.
    eapply dom_filter.
    intros i.
    split; [|by intros [_ [_ ?]]].
    intros.
    assert (is_Some (m !! i)) as [x ?] by (apply elem_of_dom; set_solver).
    by exists x.
  Qed.

End restrict.

Section restrict_leibniz.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Context `{!LeibnizEquiv D}.

  Lemma restrict_dom_subset_L (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) = s.
  Proof. unfold_leibniz. apply restrict_dom_subset. Qed.

End restrict_leibniz.

Set Default Proof Using "Type".

Notation pbundleG := recovery_weakestpre.pbundleG.

Notation perennialG := recovery_weakestpre.perennialG.

(* This approach does not seem to work.
Definition wpr `{hG : !nvmG Σ} `{hC : !crashG Σ} (s : stuckness) (k : nat) E
           (e : expr) (rec : expr) (Φ : val → dProp Σ) (Φinv : nvmG Σ → dProp Σ) (Φc : nvmG Σ -> val -> dPropO Σ) :=
  MonPred (λ V,
    ⌜ ∀ Hc t, Objective (Hc t Φc) ⌝ ∗
    ∀ TV,
      ⌜ V ⊑ TV ⌝ -∗
      validV (store_view TV) -∗
      interp -∗
      wpr s k (* hC ({| recovery_weakestpre.pbundleT := nvm_get_names Σ _ |}) *) E
        (ThreadState e TV)
        (ThreadState rec (∅, ∅, ∅))
        (λ res,
          let '(ThreadVal v TV') := res in Φ v TV')
        (λ _, True%I)
        (λ hG res,
          let '(ThreadVal v TV') := res in Φc (hG) v TV')
  )%I. *)

Record nvm_high_names := {
  name_abs_history : gname;
  name_know_abs_history : gname;
  name_predicates : gname;
  name_preorders : gname;
}.

Definition nvm_high_get_names Σ (hG : nvmHighG Σ) : nvm_high_names :=
  {| name_abs_history := abs_history_name;
     name_know_abs_history := know_abs_history_name;
     name_predicates := predicates_name;
     name_preorders := preorders_name;
  |}.

Canonical Structure nvm_high_namesO := leibnizO nvm_high_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_high_update Σ (hG : nvmHighG Σ) (names : nvm_high_names) :=
  {| (* Ghost names *)
     abs_history_name := names.(name_abs_history);
     know_abs_history_name := names.(name_know_abs_history);
     predicates_name := names.(name_predicates);
     preorders_name := names.(name_preorders);
     (* Functors *)
     ra_inG := hG.(@ra_inG _);
     ra_inG' := hG.(@ra_inG' _);
     abs_histories := hG.(@abs_histories _);
     preordersG := hG.(@preordersG _);
  |}.

Record nvm_names := {
  name_base_names : nvm_base_names; (* Names used by the base logic. *)
  name_high_names : nvm_high_names; (* Names used by the high-level logic. *)
}.

Definition nvm_get_names Σ (hG : nvmG Σ) : nvm_names :=
  {| name_base_names := nvm_base_get_names _ nvmG_baseG;
     name_high_names := nvm_high_get_names _ nvmG_highG |}.

Canonical Structure nvm_namesO := leibnizO nvm_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_update Σ (hG : nvmG Σ) (Hinv : invG Σ) (Hcrash : crashG Σ) (names : nvm_names) :=
  {| nvmG_baseG := nvm_base_update _ hG.(@nvmG_baseG _) Hinv Hcrash names.(name_base_names);
     nvmG_highG := nvm_high_update _ hG.(@nvmG_highG _) names.(name_high_names) |}.

(* The recovery WP is parameterized by two predicates: [Φ] is the postcondition
   for normal non-crashing execution and [Φr] is the postcondition satisfied in
   case of a crash. *)
Definition wpr_pre Σ (s : stuckness) (k : nat)
    (wpr : nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ) :
  nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ :=
  λ hG E e e_rec Φ Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ σ' (HC : crash_prim_step nvm_crash_lang σ σ') n,
        ⎡ interp -∗ state_interp σ n ={E}=∗ ▷ ∀ (Hc1 : crashG Σ) q, NC q ={E}=∗
          ∃ (names : nvm_names),
            let hG := (nvm_update Σ hG _ Hc1 names) in
              state_interp σ' 0 ∗
              (monPred_at (wpr hG E e_rec e_rec (λ v, Φr hG v) Φr) (∅, ∅, ∅)) ∗
              NC q ⎤
     }})%I.

Local Instance wpr_pre_contractive {Σ} s k: Contractive (wpr_pre Σ s k).
Proof.
  rewrite /wpr_pre. intros ??? Hwp ??????.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def {Σ} (s : stuckness) k := fixpoint (wpr_pre Σ s k).
Definition wpr_aux {Σ} : seal (@wpr_def Σ). by eexists. Qed.
Definition wpr' {Σ} := (@wpr_aux Σ).(unseal).
Lemma wpr_eq {Σ} : @wpr' Σ = @wpr_def Σ.
Proof. rewrite /wpr'. rewrite wpr_aux.(seal_eq). done. Qed.

Lemma wpr_unfold `{hG : nvmG Σ} st k E e rec Φ Φc :
  wpr' st k hG E e rec Φ Φc ⊣⊢ wpr_pre Σ st k (wpr' st k) hG E e rec Φ Φc.
Proof.
  rewrite wpr_eq. rewrite /wpr_def.
  apply (fixpoint_unfold (wpr_pre Σ st k)).
Qed.

Definition wpr `{nvmG Σ} s k := wpr' s k _.

Section wpr.
  Context `{hG : nvmG Σ}.

  (* For each location in [p] pick the message in the store that it specifies. *)
  Definition slice_of_hist (p : view) (σ : gmap loc (gmap time (message * positive))) : gmap loc (gmap time (message * positive)) :=
    map_zip_with
      (λ '(MaxNat t) hist,
       match hist !! t with
         Some (msg, s) => {[ 0 := (discard_msg_views msg, s) ]}
       | None => ∅ (* The None branch here should never be taken. *)
       end)
      p σ.

  Lemma slice_of_hist_dom_subset p hists :
    dom (gset loc) (slice_of_hist p hists) ⊆ dom (gset loc) hists.
  Proof.
    rewrite /slice_of_hist.
    intros l.
    rewrite !elem_of_dom.
    intros [??].
    apply map_lookup_zip_with_Some in H.
    destruct H as (? & ? & ? & ? & ?).
    eexists _. done.
  Qed.

  (* Given the state interpretations _before_ a crash we reestablish the
  interpretations _after_ a crash. *)
  Lemma nvm_reinit (hG' : nvmG Σ) n Pg tv σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) :
    crash_step σ σ' →
    ⊢ interp -∗
      state_interp σ n -∗
      (post_crash Pg) tv ==∗
      ∃ names : nvm_names,
        let hG := nvm_update Σ hG' Hinv Hcrash names in
          interp (hG := hG) ∗
          nvm_heap_ctx (hG := _) σ' ∗
          Pg hG (∅, ∅, ∅).
  Proof.
    iIntros (step).
    iDestruct 1 as (hists preds orders) "(psts & orders & incr & ? & ? & preds)".
    iIntros "(heap & authStor & inv & pers & recov) Pg".

    (* We need to first re-create the ghost state for the base interpretation. *)
    iMod (nvm_heap_reinit _ _ _ _ Hcrash step with "heap inv pers") as (baseNames) "(map & interp' & #persImpl)".

    iDestruct (big_sepM2_dom with "incr") as %domHistsEqOrders.

    destruct step as [store p p' pIncl].

    (* Allocate new ghost state for the logical histories. *)
    rewrite /interp.
    set newHists := slice_of_hist p' hists.
    iMod (own_full_history_gname_alloc ((λ h : abs_history (message * positive), snd <$> h) <$> newHists)) as (new_abs_history_name new_know_abs_history_name) "[hists' needThis]".

    (* Some locations may be lost after a crash. For these we need to
    forget/throw away the predicate and preorder that was choosen for the
    location. *)
    set newOrders := restrict (dom (gset _) newHists) orders.
    iMod (own_all_preorders_gname_alloc newOrders) as (new_orders_name) "newOrders".

    (* iMod (own_alloc ()) *)
    (* own_full_history ((λ h : abs_history (message * positive), snd <$> h) <$> hists) *)

    iModIntro.
    iExists
      ({| name_base_names := baseNames;
          name_high_names := {| name_abs_history := new_abs_history_name;
                                name_know_abs_history := new_know_abs_history_name;
                                name_predicates := _;
                                name_preorders := new_orders_name |} |}).
    iFrame "interp'".
    rewrite /nvm_heap_ctx.
    (* iFrame. *)
    iSplitR ""; last first. { admit. }
    rewrite /interp.
    iExists _, _, _.
    rewrite /own_full_history.
    iFrame "newOrders".
    iFrame "preds".
    iFrame "hists'".
    iSplitL "".
    { admit. } (* We need the points-to predicates. *)
    iSplitL "".
    { iApply big_sepM2_intuitionistically_forall.
      - setoid_rewrite <- elem_of_dom.
        apply set_eq. (* elem_of_equiv_L *)
        rewrite restrict_dom_subset_L; first done.
        rewrite -domHistsEqOrders.
        apply slice_of_hist_dom_subset.
      - iModIntro.
        rewrite /newHists.
        iIntros (??? slice ?).
        iPureIntro.
        apply map_lookup_zip_with_Some in slice.
        destruct slice as ([t] & hist & -> & more).
        destruct (hist !! t) as [[??]|]; simpl.
        { rewrite map_fmap_singleton. simpl. apply increasing_map_singleton. }
        { rewrite fmap_empty. apply increasing_map_empty. }
    }
    admit.
  Admitted.


  Lemma nvm_reinit' (hG' : nvmG Σ) n σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) Pg :
    crash_step σ σ' →
    ⊢ ⎡interp⎤ -∗
      ⎡state_interp σ n⎤ -∗
      post_crash Pg ==∗
      ∃ names : nvm_names,
        let hG := nvm_update Σ hG' Hinv Hcrash names in
          ⎡interp (hG := hG)⎤ ∗
          ⎡nvm_heap_ctx (hG := _) σ'⎤ ∗
          Pg hG.
  Proof.
    iIntros (step) "interp baseInterp".
    iMod (nvm_heap_reinit_alt _ _ _ _ Hcrash _ step with "baseInterp []") as (hnames) "(map & baseInterp & idemp)".
  Admitted.

  (* _The_ lemma for showing a recovery weakest precondition. *)
  Lemma idempotence_wpr s k E1 e rec Φ Φr Φc `{∀ hG, Objective (Φc hG)} :
    ⊢ WPC e @ s ; k ; E1 {{ Φ }} {{ Φc hG }} -∗
      (<obj> □ ∀ (hG' : nvmG Σ),
            Φc hG' -∗ ▷ post_crash (λ hG', (WPC rec @ s ; k; E1 {{ Φr hG' }} {{ Φc hG' }}))) -∗
      wpr s k E1 e rec Φ Φr.
  Proof.
    iStartProof (iProp _).
    iLöb as "IH" forall (e Φ hG).

    iIntros (?). monPred_simpl.
    iIntros "wpc".
    iIntros (? ?).
    iIntros "#Hidemp".
    rewrite /wpr.
    rewrite wpr_unfold.
    rewrite /wpr_pre.
    iApply (wpc_strong_mono' with  "wpc"); try reflexivity.
    iSplit. { iIntros (?). monPred_simpl. setoid_rewrite monPred_at_fupd. auto. }
    rewrite disc_unfold_at. monPred_simpl.
    iIntros "!>".
    iIntros (??).
    iIntros "phiC".
    rewrite fupd_level_unfold_at.
    iModIntro.
    iIntros (?? step ?).
    iDestruct ("Hidemp" with "phiC") as "idemp'".
    iIntros "interp state".
    iModIntro (|={E1}=> _)%I.
    iNext.
    iIntros (??) "NC".

    (* Allocate the new ghost state. *)
    iMod (nvm_reinit _ _ _ _ _ _ _ _ with "interp state idemp'") as (names) "(interp & stateInterp & idemp)".
    { apply step. }

    iModIntro (|={E1}=> _)%I.
    iExists names.
    iFrame.
    monPred_simpl.
    iSpecialize ("IH" $! _ _ (nvm_update Σ hG iris_invG Hc1 names) (∅, ∅, ∅) with "[idemp] [Hidemp]").
    { done. }
    { monPred_simpl. done. }
    iApply "IH".
  Qed.

End wpr.
