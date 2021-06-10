(* In this file we define our weakest precondition on top of the weakest
precondition included in Iris. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self Require Export extra.
From self.high Require Export dprop.
From self Require Export view.
From self Require Export lang.
From self.base Require Import primitive_laws.
From self.lang Require Import syntax.
From self.high Require Import resources crash_weakestpre lifted_modalities monpred_simpl modalities.

Section wp.
  Context `{!nvmG Σ}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).

  (* We prove a few basic facts about our weakest precondition. *)
  Global Instance wp_ne s E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e).
  Proof. rewrite wp_eq. solve_proper. Qed.
  Global Instance wp_proper s E e :
    Proper (pointwise_relation val (≡) ==> (≡)) (wp s E e).
  Proof. rewrite wp_eq. solve_proper. Qed.

  (* For the WP in Iris the other direction also holds, but not for this WP *)
  Lemma wp_value_fupd' s E Φ v : (|NC={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def.
    iIntros "H".
    iApply wpc_value.
    iSplit.
    - iMod "H". iModIntro. done.
    - iModIntro. iModIntro. done.
  Qed.

  (* Lemma wp_value_fupd s E Φ e v : IntoVal e v → (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}. *)
  Lemma wp_value_fupd s E Φ e v : IntoVal e v → (|NC={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
  Proof. intros <-. apply wp_value_fupd'. Qed.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof. iIntros "H". iApply wp_value_fupd'. iModIntro. iFrame. Qed.

  (* Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, fupd E E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}. *)
  (* Proof. Admitted. *)
  (*   (* iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. by iIntros (v) ">H". Qed. *) *)

  Notation PureExecBase P nsteps e1 e2 :=
    (∀ TV, PureExec P nsteps (ThreadState e1 TV) (ThreadState e2 TV)).

  (* Upstream this to Iris. *)
  Lemma monPred_at_step_fupd i Eo Ei (P : dProp Σ) :
    (|={Eo}[Ei]▷=> P) i ⊣⊢ |={Eo}[Ei]▷=> P i.
  Proof. by rewrite monPred_at_fupd monPred_at_later monPred_at_fupd. Qed.

  Lemma monPred_at_step_fupdN E E' n (P : dProp Σ) j :
    ((|={E}[E']▷=>^n P) j ⊣⊢ (|={E}[E']▷=>^n (P j)))%I.
  Proof.
    induction n as [|n IH]; [done|]. by rewrite monPred_at_step_fupd IH.
  Qed.

  Global Instance make_monPred_at_step_fupd `{BiFUpd PROP} i E1 E2 (P : dProp Σ) 𝓟 :
    MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|={E1}[E2]▷=> P)%I (|={E1}[E2]▷=> 𝓟)%I.
  Proof. by rewrite /MakeMonPredAt monPred_at_step_fupd=> <-. Qed.

  Global Instance make_monPred_at_step_fupdN `{BiFUpd PROP} i E1 E2 n (P : dProp Σ) 𝓟 :
    MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|={E1}[E2]▷=>^n P)%I (|={E1}[E2]▷=>^n 𝓟)%I.
  Proof. rewrite /MakeMonPredAt. rewrite monPred_at_step_fupdN => h.
         Abort.
         (* rewrite h. <-. Qed. *)

  Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def wpc_eq /wpc_def => Hexec Hφ. iStartProof (iProp _).
    simpl.
    iIntros "% Hwp" (?) "A V C".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.
    iApply wp_pure_step_fupd; first apply Hφ.
    simpl.
    monPred_simpl.
    rewrite monPred_at_step_fupdN.
    simpl.
    iApply (step_fupdN_wand with "Hwp").
    iIntros "H".
    iSpecialize ("H" $! TV with "A V C").
    iApply wpc_wp.
    iFrame.
  Qed.

  (* This lemma is like the [wp_pure_step_later] in Iris except its premise uses
  [PureExecBase] instead of [PureExec]. *)
  Lemma wp_pure_step_later s E e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

End wp.

(* Definition lastR (abs_state : Type) : cmra := *)
(*   prodR fracR (agreeR (prodO (leibnizO abs_state) valO)). *)

Section wp_rules.
  Context `{AbstractState abs_state}.
  Context `{!nvmG Σ}.

  Implicit Types (ℓ : loc) (s : abs_state) (ϕ : abs_state → val → dProp Σ).

  Lemma last_cons (A : Type) (l : list A) (a b : A) :
    last l = Some a → last (b :: l) = Some a.
  Proof. intros Hl. induction l; [done|by rewrite -Hl]. Qed.
  Lemma last_app (A : Type) (l1 l2 : list A) (a : A) :
    last l2 = Some a → last (l1 ++ l2) = Some a.
  Proof.
    intros Hl. induction l1; [done|].
    by erewrite <- app_comm_cons, last_cons.
  Qed.

  (* FIXME: This has been committed upstream, delete later when dependencies are updated. *)
  Lemma make_monPred_at_embed2 {I : biIndex} {PROP : bi} name (i : I) P (𝓟 : PROP) :
    MakeMonPredAt i P 𝓟 →
    MakeMonPredAt i (named name P) (named name 𝓟).
  Proof. done. Qed.

  Hint Extern 0 (MakeMonPredAt _ (named _ _) _) => apply make_monPred_at_embed2 : typeclass_instances.

  Lemma wp_load_ex ℓ ss ss' s Q ϕ positive E :
    last ss' = Some s →
    {{{ ℓ ↦ ss; ss' | ϕ ∗ <obj> (∀ v, ϕ s v -∗ Q v ∗ ϕ s v) }}}
      Load (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ v, RET v; ℓ ↦ ss; ss' | ϕ ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "[pts pToQ]".
    iDestruct "pts" as (?tGP ?tP ?tS absHist) "pts". iNamed "pts".
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV PV] BV] incl2) "#val interp".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    (* rewrite /interp. *)
    iNamed "interp".
    iDestruct (know_pred_agree with "preds knowPred") as (pred predsLook) "#predsEquiv".
    iDestruct (own_full_history_agree with "[$] [$]") as %look.
    apply lookup_fmap_Some in look.
    destruct look as [ℓhist [histAbsHist l]].
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply (wp_load with "[$pts $val]").
    iNext. iIntros (t' v' msg) "[pts (%look & %msgVal & %gt)]".
    apply lookup_fmap_Some in look.
    destruct look as [[hip s'] [msgEq histLook]].
    simpl in msgEq. subst.
    rewrite /store_view. simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val".

    (* We need to conclude that the only write we could read is [tS]. I.e., that
    [t' = tS]. *)
    assert ({[ℓ := MaxNat tS]} ⊑ SV) as inclSingl.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      etrans.
      apply know.
      etrans.
      apply incl.
      apply incl2. }
    assert (tS ≤ t') as lte.
    { eapply (view_lt_lookup ℓ).
      - apply inclSingl.
      - rewrite /lookup_zero. rewrite lookup_singleton. done.
      - apply gt. }
    assert (is_Some (absHist !! t')) as HI.
    { eapply fmap_is_Some.
      rewrite -lookup_fmap.
      rewrite <- histAbsHist.
      rewrite lookup_fmap.
      rewrite histLook.
      eauto. }
      (* ∘rewrite fmap_comp in histAbsHist. *)
      (* apply (elem_of_dom (M:=gmap time)). rewrite -domEq. apply elem_of_dom. *)
      (* rewrite -lookup_fmap in look. *)
      (* apply lookup_fmap_Some in look. *)
      (* destruct look as [msg look']. *)
      (* exists msg. apply look'. } *)
    assert (t' = tS) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      pose proof (nolater t' lt) as eq.
      rewrite eq in HI. inversion HI as [? [=]]. }
    (* assert (v' = v) as ->. *)
    (* { apply (inj Some). *)
    (*   rewrite -lastVal -look. *)
    (*   done. } *)
    (* iAssert (⌜v' = v⌝)%I as %->. *)
    (* { rewrite -lookup_fmap in look. *)
    (*   apply lookup_fmap_Some in look. *)
    (*   destruct look as [msg [msgEq look']]. *)
    (*   iDestruct (big_sepM2_lookup with "map") as "%eq"; [done|done|]. *)
    (*   iPureIntro. simpl in eq. congruence. } *)
    assert (absHist !! tS = Some s) as lookS.
    { rewrite -sLast.
      apply map_slice_lookup_hi in slice.
      rewrite slice.
      erewrite last_app; done. }
    clear lte HI.

    iPoseProof (big_sepM2_dom with "map") as "%domEq".
    (* We need to get the predicate for [s] and [v']. *)
    (* iDestruct (big_sepM2_lookup_acc with "map") as "[HI HO]"; [done|done|]. *)
    iDestruct (big_sepM2_lookup_acc with "map") as "[predMap map]"; [done|done|].
    (* We now know exactly what the value in [ℓhist] at [tS] is. *)
    assert (s' = encode s) as sEq.
    { setoid_rewrite map_eq_iff in histAbsHist.
      move: (histAbsHist tS).
      rewrite !lookup_fmap.
      rewrite histLook.
      rewrite lookupV.
      rewrite sLast.
      simpl.
      congruence. }
    (* assert (ℓhist !! tS = Some (msg, encode s)). *)
    (* { setoid_rewrite map_eq_iff in histAbsHist. *)
    (*   pose proof (histAbsHist tS) as eq. *)
    (* } *)
    iDestruct (big_sepM_lookup_acc with "predMap") as "[predHolds predMap]"; first done.
    simpl.
    iDestruct "predHolds" as (P') "[%eq PH]".
    iDestruct (discrete_fun_equivI with "predsEquiv") as "HI".
    iDestruct ("HI" $! s') as "HIP". iClear "HI".
    iEval (rewrite discrete_fun_equivI) in "HIP".
    iDestruct ("HIP" $! (msg_val msg)) as "HI". iClear "HIP".
    rewrite /encode_predicate.
    rewrite sEq.
    rewrite decode_encode.
    simpl.
    iEval (rewrite -sEq) in "HI".
    rewrite eq.
    rewrite option_equivI.
    iRewrite "HI" in "PH".
    rewrite monPred_at_objectively.
    iSpecialize ("pToQ" $! (msg_to_tv msg) (msg_val msg)).
    rewrite monPred_at_wand.
    iSpecialize ("pToQ" $! (msg_to_tv msg)).
    iDestruct ("pToQ" with "[//] PH") as "[Q phi]".
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iExists _. rewrite -sEq. iSplit; first done.
      iRewrite "HI". done. }
    (* Reinsert into the map. *)
    iDestruct ("map" with "[$predMap]") as "map".
    (* { done. } *)

    iSplit; first done.
    iSplitR "ptsMap allOrders ordered map history preds sharedLocs crashedAt
             recPreds mapRecPredsImpl".
    2: { iExists _, _, _, _, _, _, _. iFrame "∗#". done. }
    iApply "Φpost".
    iSplitR "Q".
    2: {
      (* This _should_ hold bc. the view in the message is smaller. But, we
      don't have that fact. *)
      admit.
    }
    iExists _, _, _, _.
    iFrame "∗#%".
    iPureIntro.
    etrans. eassumption.
    etrans. eassumption.
    eassumption.
  Admitted.

  Lemma wp_store_ex ℓ ss1 ss2 v s__last s ϕ st E :
    last ss2 = Some s__last →
    s__last ⊑ s →
    {{{ ℓ ↦ ss1; ss2 | ϕ ∗ ϕ s v }}}
      #ℓ <- v @ st; E
    {{{ RET #(); ℓ ↦ ss1; ss2 ++ [s] | ϕ }}}.
  Proof.
    intros last stateGt Φ.
    iStartProof (iProp _). iIntros (TV).
    iIntros "[pts phi]".
  Admitted.
  (*   iDestruct "pts" as (?tGP ?tP ?tS absHist hist) "(pts & map & %incrL & %lookupP & %lookupV & %nolater & %lastVal & hist & slice & %know & per)". *)
  (*   rewrite monPred_at_wand. simpl. *)
  (*   iIntros (TV' incl) "Φpost". *)
  (*   rewrite monPred_at_later. *)
  (*   rewrite wp_eq /wp_def. *)
  (*   rewrite wpc_eq. simpl. *)
  (*   iIntros ([[SV PV] BV] incl2) "#val interp". *)
  (*   rewrite monPred_at_pure. *)
  (*   iApply program_logic.crash_weakestpre.wp_wpc. *)
  (*   iApply (wp_store with "pts"). *)
  (* Qed. *)

  (* A read-only points-to predicate. *)
  (* Definition mapsto_ro ℓ (s : abs_state) ϕ : dProp Σ := *)
  (*   ∃ t, monPred_in ({[ ℓ := MaxNat t ]}, ∅, ∅) ∗ *)
  (*        ⎡know_pred ℓ ϕ⎤ ∗ ⎡know_state ℓ t s⎤. *)

  (* Notation "l ↦ro s | P" := (mapsto_ro l s P) (at level 20). *)

  (* Lemma know_state_Some `{Countable ST} hists ℓ t (s : ST) : *)
  (*   own abs_history_name (● (abs_hist_to_ra_old <$> hists) : encoded_historiesR) -∗ *)
  (*   know_state ℓ t s -∗ *)
  (*   ∃ m, ⌜hists !! ℓ = Some m⌝. *)
  (* Proof. *)
  (*   iIntros "A B". *)
  (*   destruct (hists !! ℓ) as [m|] eqn:Heq. *)
  (*   { iExists m. done. } *)
  (*   iDestruct (own_valid_2 with "A B") as %[Hincl _]%auth_both_valid_discrete. *)
  (*   apply singleton_included_l' in Hincl. *)
  (*   move: Hincl => [? [isSome ?]]. *)
  (*   rewrite lookup_fmap in isSome. *)
  (*   rewrite Heq in isSome. *)
  (*   inversion isSome. *)
  (* Qed. *)

  (* Lemma wp_load ℓ s ϕ st E R : *)
  (*   {{{ (∀ s' v, ϕ s' v -∗ ϕ s' v ∗ R s' v) ∗ *)
  (*       ℓ ↦ro s | ϕ }}} *)
  (*     Load (Val $ LitV $ LitLoc ℓ) @ st; E *)
  (*   {{{ s' v, RET v; ℓ ↦ro s' | ϕ ∗ R s' v }}}. *)
  (* Proof. *)
  (*   rewrite wp_eq /wp_def. *)
  (*   iStartProof (iProp _). *)
  (*   iIntros (post ((sv & pv) & bv)) "[Htrans #Hpts]". *)
  (*   iDestruct "Hpts" as (t) "(%seen & knowPred & knowState)". *)
  (*   iIntros (? ?) "Hpost". simpl. iIntros ([[sv' pv'] bv'] ?) "#Hv Hint". *)
  (*   iDestruct "Hint" as (hists preds) "(pointsToPreds & ? & authHists & authPreds)". *)
  (*   iDestruct (own_valid_2 with "authHists knowState") as %Hv. *)
  (*   iDestruct (know_state_Some with "[$] [$]") as %[hist look]. *)
  (*   iDestruct (big_sepM_delete with "pointsToPreds") as "[ℓPts pointsToPreds]"; first done. *)
  (*   iApply (wp_load with "[$ℓPts $Hv]"). *)
  (*   iNext. *)
  (*   iIntros (t' v') "[ℓPts %FOO]". *)
  (*   iFrame "Hv". *)
  (*   iSplitL "Hpost". *)
  (*   - iApply "Hpost". *)
  (*     admit. *)
  (*   - (* Re-establish interp. *) *)
  (*     rewrite /interp. *)
  (*     iExists _, _. *)
  (*     iFrame "authHists authPreds". *)
  (*     iFrame. *)
  (*     iApply big_sepM_delete; first done. *)
  (*     iFrame. *)
  (* Abort. *)

  (*
  Lemma wp_alloc `{!SqSubsetEq abs_state, !PreOrder (⊑@{abs_state})}
        ℓ v (s : abs_state) (Φ : abs_state → val → dProp Σ) st E :
    {{{ Φ s v }}}
      ref v @ st; E
    {{{ ι, RET ℓ; mapsto_ex ι ℓ [] [] s Φ }}}
  Proof.

  Lemma wp_load ℓ ι ℓ ss ss' ϕ s E :
    {{{ mapsto_ex ι ℓ ss ss' s Φ }}}
      !ℓ @ s; E
    {{{ v, RET v; mapsto_ex ι ℓ ss ss' Φ ∗ ϕ s v }}}
  Proof.
  *)

  Lemma wp_wb_ex ℓ ss1 ss2 s ϕ st E :
    last ss2 = Some s →
    {{{ ℓ ↦ ss1; ss2 | ϕ }}}
      WB #ℓ @ st; E
    {{{ RET #(); ℓ ↦ ss1; ss2 | ϕ ∗ <fence> know_persist_lower_bound ℓ s }}}.
   Proof.
   Admitted.

  Lemma wp_fence P st E :
    {{{ <fence> P }}}
      Fence @ st; E
    {{{ RET #(); P }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    rewrite monPred_at_wand.
    iIntros "P". iIntros (tv' incl) "HΦ".
    monPred_simpl.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV PV] BV] incl2) "#val interp".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.
    iApply (wp_fence with "[//]").
    iNext. iIntros (_).
    cbn.
    iFrame "#∗".
    iSplit. { iPureIntro. repeat split; try done. apply view_le_l. }
    iApply "HΦ".
    - iPureIntro. etrans. apply incl2. repeat split; try done.
      apply view_le_l.
    - iApply monPred_mono; last iApply "P".
      eassert ((sv, pv, bv) ⊑ _) as incl3. { etrans; [apply incl|apply incl2]. }
      destruct tv' as [[??]?].
      repeat split; try apply incl3.
      f_equiv; apply incl3.
  Qed.

  (** * Shared points-to predicate *)

  Lemma msg_persisted_views_eq
        (ℓ : loc) (hists : gmap loc (abs_history (message * positive)))
        (hist : gmap time (message * positive)) (msg : message) (sharedLocs : gset loc) (t : time) (s' : positive) :
    map_Forall
      (λ _ : loc,
          map_Forall
            (λ (_ : nat) '(msg, _), msg_persist_view msg = msg_persisted_after_view msg))
      (restrict sharedLocs hists) →
    hists !! ℓ = Some hist →
    hist !! t = Some (msg, s') →
    own shared_locs_name (● (sharedLocs : gsetUR loc)) -∗
    own shared_locs_name (◯ {[ℓ]}) -∗
    ⌜msg.(msg_persist_view) = msg.(msg_persisted_after_view)⌝.
  Proof.
    iIntros (m look look') "A B".
    iDestruct (own_valid_2 with "A B") as %[V%gset_included _]%auth_both_valid_discrete.
    setoid_rewrite <- elem_of_subseteq_singleton in V.
    iPureIntro.
    assert (restrict sharedLocs hists !! ℓ = Some hist) as look2.
    - apply restrict_lookup_Some. done.
    (* { apply restrict_lookup_Some. done. }. *)
    - setoid_rewrite map_Forall_lookup in m.
    specialize (m ℓ hist look2).
    setoid_rewrite map_Forall_lookup in m.
    specialize (m t (msg, s') look').
    simpl in m.
    done.
  Qed.

  Lemma wp_load_shared ℓ s1 s2 s3 Q ϕ positive E :
    {{{ ℓ ↦ (s1, s2, s3) | ϕ ∗ <obj> (∀ s v, ⌜ s3 ⊑ s ⌝ ∗ ϕ s v -∗ Q s v ∗ ϕ s v) }}}
      LoadAcquire (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ s v, RET v; ℓ ↦ (s1, s2, s) | ϕ ∗ post_fence (Q s v) }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "[pts pToQ]".
    (* We destruct the points-to predicate. *)
    iNamed "pts".
    (* We only need the information related to the store view. *)
    iDestruct "storeLB" as (tS s3' s3Incl ?lt) "[knowOrder histS3]".
    (* iDestruct "pts" as (?tGP ?tP ?tS) "tmp". iNamed "tmp". *)
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    rewrite wp_eq /wp_def.
    rewrite wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val interp".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We open [interp]. *)
    iNamed "interp".

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (know_pred_agree with "preds knowPred")
      as (pred predsLook) "#predsEquiv".

    (* We need to get the points-to predicate for [ℓ] which is is inside
    [interp].  We want to look up the points-to predicate in [ptsMap]. To this
    end, we combine our fragment of the history with the authorative element. *)
    iDestruct (own_frag_history_agree_singleton with "history histS3") as %look.
    destruct look as (absHist & enc & histAbsHist & lookTS & decodeEnc).
    apply lookup_fmap_Some in histAbsHist.
    destruct histAbsHist as [hist [histAbsHist histsLook]].

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply wp_fupd.
    iApply (wp_load_acquire with "[$pts $val]").
    iNext. iIntros (t' v' SV' PV' _PV') "(%look & %gt & #val' & pts)".

    apply lookup_fmap_Some in look.
    destruct look as [[? s'] [msgEq histLook]].
    simpl in msgEq.
    rewrite /store_view.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val'".

    (* We immediately show that [PV'] is equal to [_PV']. *)
    iDestruct (msg_persisted_views_eq with "[$] [$]") as %pvEq; try done.
    rewrite msgEq in pvEq.
    simpl in pvEq. rewrite <- pvEq in msgEq. clear pvEq _PV'.

    assert (tS ≤ t') as lte.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      etrans; first done.
      etrans; last done.
      rewrite /store_view /=.
      f_equiv.
      etrans. apply incl. apply incl2. }

    iDestruct (big_sepM2_lookup_acc with "map") as "[predMap map]"; [done|done|].
    iDestruct (big_sepM_lookup_acc with "predMap") as "[predHolds predMap]"; first done.
    simpl.
    iDestruct "predHolds" as (P') "[%eq PH]".
    iDestruct (discrete_fun_equivI with "predsEquiv") as "HI".
    iDestruct ("HI" $! s') as "HIP". iClear "HI".
    iEval (rewrite discrete_fun_equivI) in "HIP".
    iDestruct ("HIP" $! v') as "HI". iClear "HIP".
    rewrite msgEq. simpl.
    rewrite msgEq in eq. simpl in eq.
    rewrite eq.
    (* The loaded state must be greater than [s3]. *)
    iDestruct (big_sepM2_lookup_1 with "ordered") as (order) "[%ordersLook %increasingMap]".
    { apply histsLook. }
    iDestruct (orders_lookup with "allOrders knowOrder") as %orderEq; first apply ordersLook.
    epose proof (increasingMap tS t' (encode s3) s') as hihi.
    assert (order enc s') as orderRelated.
    { destruct (le_lt_or_eq _ _ lte) as [le|tSEq].
      - eapply increasingMap.
        * apply le.
        * subst. done.
        * rewrite lookup_fmap. rewrite histLook. done.
      - (* We can conclude that [enc] is equal to [t']. *)
        assert (enc = s') as ->.
        2: { rewrite orderEq. rewrite /encode_relation. rewrite decodeEnc. simpl. done. }
        move: lookTS.
        rewrite -histAbsHist.
        rewrite lookup_fmap.
        rewrite tSEq.
        rewrite histLook.
        simpl.
        by intros [=]. }
    rewrite orderEq in orderRelated.
    epose proof (encode_relation_related _ _ _ orderRelated) as (? & s & eqX & decodeS' & s3InclS').
    assert (x = s3') as -> by congruence.
    rewrite /encode_predicate.
    rewrite decodeS'.
    simpl.
    rewrite option_equivI.
    iRewrite "HI" in "PH".
    rewrite /msg_to_tv. simpl.
    iSpecialize ("pToQ" $! (SV', PV', ∅) s v').
    monPred_simpl.
    iEval (setoid_rewrite monPred_at_sep) in "pToQ".
    iSpecialize ("pToQ" $! (SV', PV', ∅)).
    iDestruct ("pToQ" with "[//] [$PH]") as "[Q phi]".
    { iPureIntro. etrans; done. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iExists _. iSplit; first done.
      iRewrite "HI". done. }
    (* Reinsert into the map. *)
    iDestruct ("map" with "[$predMap]") as "map".

    iMod (own_full_history_alloc with "history") as "[history histS]".
    { rewrite lookup_fmap.
      erewrite histsLook.
      simpl.
      reflexivity. }
    { rewrite lookup_fmap.
      erewrite histLook.
      simpl.
      reflexivity. }
    { eassumption. }
    iModIntro.
    (* We re-establish [interp]. *)
    iSplit. { iPureIntro. repeat split; try done; apply view_le_l. }
    iSplitR "ptsMap allOrders ordered map history preds sharedLocs crashedAt
             recPreds mapRecPredsImpl".
    2: { iExists _, _, _, _, _, _, _. iFrame. iFrame "#". done. }
    iSpecialize ("Φpost" $! s v').
    monPred_simpl.
    iApply "Φpost".
    { iPureIntro.
      etrans. eassumption.
      repeat split; try done; try apply view_le_l. }
    (* The thread view we started with [TV] is smaller than the view we ended
    with. *)
    assert (TV ⊑ (SV ⊔ SV', PV, BV ⊔ PV')).
    { do 2 (etrans; first done). repeat split; auto using view_le_l. }
    iSplitR "Q".
    - iFrame "knowPred isSharedLoc globalPerLB".
      iSplitL "persistLB".
      { iApply monPred_mono; done. }
      iExists t', s.
      iFrame.
      iSplit; first done.
      (* FIXME: Intuitively the lhs. should be included in because we read [t']
      and a write includes its own timestamp. But, we don't remember this fact,
      yet. *)
      admit.
    - simpl.
      (* rewrite /post_fence. simpl. rewrite /monPred_at. *)
      rewrite /store_view /persist_view /=.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      * apply view_le_r.
      * rewrite assoc. apply view_le_r.
      * apply view_empty_least.
  Admitted.

End wp_rules.
