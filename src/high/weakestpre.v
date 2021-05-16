(* In this file we define our weakest precondition on top of the weakest
precondition included in Iris. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.

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

  Definition abs_hist_to_ra_old (abs_hist : gmap time (message * positive)) : encoded_abs_historyR :=
    (to_agree ∘ snd) <$> abs_hist.

  (* Definition loc_to_hist_ra (l : (@loc_info Σ)) `{Countable l} : encoded_abs_historyR := *)
  (*   (to_agree ∘ encode) <$> l_abstract_history l. *)

  (* Record foo := { foo_car : Type; foo_rel : relation foo_car; }. *)
  (* Definition bar := gmap nat foo. *)

  (* Definition test : Prop := ∃ (S : Set) (_ : relation S), True. *)
  (* Definition test : iProp Σ := ∃ (S : Set) (_ : relation S), True. *)

  (* Definition test (m : gmap nat nat) : iProp Σ := *)
  (*   ([∗ map] ℓ ↦ enc ∈ m, *)
  (*     ∃ (S : Type) _ : EqDecision S) (_ : Countable S) (_ : relation S), *)
  (*       ⌜encode s = enc⌝). *)

  (* Test the use of countable encoding. *)
  (* Lemma test_encoding {S : Set} `{Countable S} *)
  (*     (ϕ : S → iProp Σ) (ϕenc : positive → iProp Σ) s p : *)
  (*   ϕ = ϕenc ∘ encode → *)
  (*   encode s = p →  *)
  (*   ϕenc p -∗ ϕ s. *)
  (* Proof. *)
  (*   iIntros (eq eq') "H". rewrite eq. simpl. rewrite eq'. iApply "H". *)
  (* Qed. *)

  (* Lemma test_encoding {S : Set} `{Countable S} *)
  (*   (ϕ : S → iProp Σ) (ϕenc : positive -d> optionO (iPropO Σ)) s p (P : iProp Σ) : *)
  (*   ϕenc ≡ (λ s, ϕ <$> (decode s)) → *)
  (*   p ≡ encode s → *)
  (*   ϕenc p ≡ Some P → *)
  (*   P ⊣⊢ ϕ s. *)
  (* Proof. *)
  (*   iIntros (eq eq'). rewrite eq'. *)
  (*   pose proof (eq (encode s)) as HI. *)
  (*   rewrite HI. *)
  (*   rewrite decode_encode. *)
  (*   simpl. *)
  (*   intros HO. *)
  (*   apply Some_equiv_inj in HO. *)
  (*   rewrite HO. *)
  (*   done. *)
  (* Qed. *)

  (*
  Definition old_interp : iProp Σ :=
    (∃ (hists : gmap loc (gmap time (message * positive)))
       (preds : gmap loc (positive → val → option (dProp Σ))),
      (* We have the points-to predicates. *)
      ([∗ map] ℓ ↦ hist ∈ hists, ℓ ↦h (fst <$> hist)) ∗
      (* The predicates hold. *)
      ([∗ map] ℓ ↦ hist; pred ∈ hists; preds,
        ([∗ map] t ↦ p ∈ hist,
           (∃ (P : dProp Σ),
             ⌜(pred) (snd p) (fst p).(msg_val) = Some P⌝ ∗
             P (msg_to_tv (fst p))))) ∗
      (* Authorative ghost states. *)
      (* own abs_history_name (● (abs_hist_to_ra_old <$> hists) : encoded_historiesR) ∗ *)
      own predicates_name (● (pred_to_ra <$> preds) : predicatesR)).
  *)

  (* Definition own_abstract_history `{Countable ST} ℓ q (abs_hist : abs_history ST) : dProp Σ := *)
  (*   ⎡own abs_history_name (●{#q} {[ ℓ := (abs_hist_to_ra abs_hist)]})⎤. *)

  (* Definition know_abstract_history `{Countable ST} ℓ (abs_hist : abs_history ST) : dProp Σ := *)
  (*   ⎡own abs_history_name (◯ {[ ℓ := (abs_hist_to_ra abs_hist)]})⎤. *)

  (* Definition know_state `{Countable s} ℓ (t : time) (s' : s) : iProp Σ := *)
  (*   own (◯ {[ ℓ := {[ t := to_agree (encode s') ]} ]} : encoded_historiesR). *)

  (* A few lemmas about [interp], [know_pred], [know_state]. *)

  Lemma singleton_included_l' `{Countable K} `{CmraTotal A} (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    (* Use [setoid_rewrite] to rewrite under the binder. *)
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  Definition increasing_list `{AbstractState ST} (ss : list ST) :=
    ∀ i j (s s' : ST), i ≤ j → (ss !! i = Some s) → (ss !! j = Some s') → s ⊑ s'.

  (* _Exclusive_ points-to predicate. This predcate says that we know that the
  last events at [ℓ] corresponds to the *)
  Definition mapsto_ex `{AbstractState ST}
             ℓ (ss1 ss2 : list ST)
             (* (v : val) *)
             (ϕ : ST → val → dProp Σ) : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time) (abs_hist : abs_history ST) (* hist *),

      (* The location ℓ points to the physical history expressed using the base logic. *)
      (* ⎡ℓ ↦h{#1/2} hist⎤ ∗ (* The other half of the points-to predicate is in [interp]. *) *)

      (* The abstract history and physical history satisfy the invariant
      predicate. This pair-wise map over two lists also implies that their
      domains are equal. *)
      (* ⎡([∗ map] t ↦ msg; abs ∈ hist; abs_hist, *)
      (*     ϕ abs msg.(msg_val) (msg.(msg_store_view), msg.(msg_persist_view), ∅))⎤ ∗ *)

      ⌜ increasing_list (ss1 ++ ss2) ⌝ ∗
      ⎡ own_preorder_loc ℓ ((⊑@{ST})) ⎤ ∗

      ⌜abs_hist !! tPers = head ss2⌝ ∗ (* Note: This also ensures that [ss2] is non-empty :) *)
      (* [tStore] is the last message and it agrees with the last state in ss2 and the value. *)
      ⌜abs_hist !! tStore = last ss2⌝ ∗
      ⌜(∀ t', tStore < t' → abs_hist !! t' = None)⌝ ∗
      (* ⌜msg_val <$> (hist !! tStore) = Some v⌝ ∗ *)

      (* Ownership over the abstract history. *)
      ⎡know_full_history_loc ℓ abs_hist⎤ ∗
      (* Knowledge of the predicate. *)
      ⎡know_pred ℓ ϕ⎤ ∗

      (* ⌜max_member abs_hist tStore⌝ ∗ *)
      ⌜map_slice abs_hist tGlobalPers tStore (ss1 ++ ss2)⌝ ∗
      (* ⌜map_slice abs_hist tGlobalPers tPers ss1⌝ ∗ *)

      (* We "have"/"know" of the three timestamps. *)
      monPred_in ({[ ℓ := MaxNat tStore ]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      ⎡persisted ({[ ℓ := MaxNat tGlobalPers ]} : view)⎤
    ).

  Global Instance mapsto_ex_discretizable `{AbstractState ST} ℓ ss1 ss2 ϕ :
    Discretizable (mapsto_ex ℓ ss1 ss2 ϕ).
  Proof. apply _. Qed.

  Definition mapsto_shared `{AbstractState ST}
             ℓ (s1 s2 s3 : ST) (ϕ : ST → val → dProp Σ) : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time),
      ⎡ own_preorder_loc ℓ ((⊑@{ST})) ⎤ ∗
      ⎡ know_frag_history_loc ℓ {[ tGlobalPers := s1 ]} ⎤ ∗
      ⎡ know_frag_history_loc ℓ {[ tPers := s2 ]} ⎤ ∗
      ⎡ know_frag_history_loc ℓ {[ tStore := s3 ]} ⎤ ∗
      ⎡ know_pred ℓ ϕ ⎤ ∗
      (* We "have"/"know" of the three timestamps. *)
      monPred_in ({[ ℓ := MaxNat tStore ]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      ⎡ persisted ({[ ℓ := MaxNat tGlobalPers ]}) ⎤
    ).

  Definition know_global_per_lower_bound `{Countable ST} (ℓ : loc) (s : ST) : dProp Σ :=
    ∃ t,
      ⎡ persisted ({[ ℓ := MaxNat t ]} : view) ⎤ ∗
      ⎡ know_frag_history_loc ℓ {[ t := s ]} ⎤.

  Definition know_persist_lower_bound `{Countable ST} (ℓ : loc) (s : ST) : dProp Σ :=
    ∃ t,
      monPred_in (∅, {[ ℓ := MaxNat t ]}, ∅) ∗
      ⎡know_frag_history_loc ℓ {[ t := s ]}⎤.

  Definition know_store_lower_bound `{Countable ST} (ℓ : loc) (t : time) (s : ST) : dProp Σ :=
    monPred_in ({[ ℓ := MaxNat t ]}, ∅, ∅) ∗
    ⎡know_frag_history_loc ℓ {[ t := s ]}⎤.

  (*
  Definition mapsto_read `{!SqSubsetEq abs_state, !PreOrder (⊑@{abs_state})}
             ι γabs γlast ℓ (s1 s2 s3 : abs_state) ϕ : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time),
      (* We know that the global persist view has [tGlobalPers]. *)
      ⎡persisted {[ ℓ := MaxNat tGlobalPers ]}⎤ ∗
      (* We know that our lobal views have [tPers] and [tStore]. *)
      monPred_in ({[ ℓ := MaxNat tStore]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      ⎡inv ι (mapsto_ex_inv ℓ ϕ γabs γlast)⎤ ∗
      ⎡own γabs ({[ tGlobalPers := to_agree s1 ]} : encoded_abs_historyR abs_state)⎤ ∗
      ⎡own γabs ({[ tPers := to_agree s2 ]} : encoded_abs_historyR abs_state)⎤ ∗
      ⎡own γabs ({[ tStore := to_agree s3 ]} : encoded_abs_historyR abs_state)⎤).
  *)

  (*
  Definition mapsto_ex_inv ℓ ϕ (γabs γlast : gname) : iProp Σ :=
    (∃ (hist_misc : (gmap time (message * abs_state))) (s : abs_state) v, (* (es es' : list abs_state), *)
      (* ℓ points to the messages in [hist_misc]. *)
      ℓ ↦h (fst <$> hist_misc) ∗
      (* ghost state for all the abstract states. *)
      (* ⌜hi = (snd <$> hist_misc)⌝ ∗ *)
      own γabs ((to_agree <$> (snd <$> hist_misc)) : encoded_abs_historyR abs_state) ∗
      (* [s] and [v] is the state and value of the last write *)
      own γlast (((1/2)%Qp, to_agree (s, v)) : lastR abs_state) ∗
      (* FIXME *)
      ([∗ map] ℓ ↦ misc ∈ hist_misc,
        ϕ (snd misc) (msg_val $ fst $ misc) (msg_store_view $ fst $ misc, msg_persist_view $ fst $ misc, ∅))
    ).
  *)

  (* We prove a few basic facts about our weakest precondition. *)
  Global Instance wp_ne s E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e).
  Proof. rewrite wp_eq. solve_proper. Qed.
  Global Instance wp_proper s E e :
    Proper (pointwise_relation val (≡) ==> (≡)) (wp s E e).
  Proof. rewrite wp_eq. solve_proper. Qed.

  (* For the WP in Iris the other direction also holds, but not for this WP *)
  Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |NC={E}=> Φ v.
  Proof.
    rewrite wp_eq /wp_def. iStartProof (iProp _). iIntros (TV). iSplit.
    - rewrite ncfupd_unfold_at.
      iIntros "Hwp".
      (* iApply wpc_value_inv'. done. *)
      admit.
    - iIntros "HΦ". iApply ncfupd_wpc. iSplit.
      { rewrite disc_unfold_at. iModIntro. iModIntro. done. }
      rewrite ncfupd_eq. rewrite /ncfupd_def. simpl.
      iMod "HΦ". iApply wpc_value'. rewrite monPred_at_and. eauto.
  Admitted.

  (* Lemma wp_value_fupd s E Φ e v : IntoVal e v → (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}. *)
  Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |NC={E}=> Φ v.
  Proof. intros <-. apply wp_value_fupd'. Qed.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof. rewrite wp_value_fupd'. iIntros "H". iModIntro. iFrame. Qed.

  (* Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, fupd E E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}. *)
  (* Proof. Admitted. *)
  (*   (* iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. by iIntros (v) ">H". Qed. *) *)

  Notation PureExecBase P nsteps e1 e2 :=
    (∀ TV, PureExec P nsteps (ThreadState e1 TV) (ThreadState e2 TV)).

  Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    rewrite wp_eq=>Hexec Hφ. iStartProof (iProp _).
  Admitted.
  (*   iIntros "% Hwp" (V ->) "Hseen Hinterp". iApply (lifting.wp_pure_step_fupd _ E E')=>//. *)
  (*   clear Hexec. iInduction n as [|n] "IH"=>/=. *)
  (*   - iApply ("Hwp" with "[% //] Hseen Hinterp"). *)
  (*   - iMod "Hwp". iModIntro. iModIntro. iMod "Hwp". iModIntro. *)
  (*     iApply ("IH" with "Hwp [$] [$]"). *)
  (* Qed. *)

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

(** Notation for the exclusive points-to predicate. *)
Notation "l ↦ xs ; ys | P" := (mapsto_ex l xs ys P) (at level 20).

(** Notation for the shared points-to predicate. *)
Notation "l ↦ ( s1 , s2 , s3 ) | P" := (mapsto_shared l s1 s2 s3 P) (at level 20).

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
    iDestruct "pts" as (?tGP ?tP ?tS absHist) "(%incrL & #knowOrder & %lookupP & %lookupV & %nolater & hist & knowPred & %slice & %know & per)".
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV PV] BV] incl2) "#val interp".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iDestruct "interp" as (hists preds orders) "(ptsMap & allOrders & ordered & map & history & preds)".
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
    { pose proof (view_lt_lt _ _ ℓ inclSingl) as HIP.
      rewrite lookup_singleton in HIP.
      pose proof (transitivity HIP gt) as leq.
      simpl in leq.
      apply leq. }
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
    iSplitR "ptsMap allOrders ordered map history preds".
    2: { iExists _, _, _. iFrame. }
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

  (*** Shared points-to predicate *)

  Lemma wp_load_shared ℓ s1 s2 s3 Q ϕ positive E :
    {{{ ℓ ↦ (s1, s2, s3) | ϕ ∗ <obj> (∀ s v, ⌜ s3 ⊑ s ⌝ ∗ ϕ s v -∗ Q s v ∗ ϕ s v) }}}
      LoadAcquire (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ s v, RET v; ℓ ↦ (s1, s2, s) | ϕ ∗ Q s v }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "[pts pToQ]".
    (* We destruct the points-to predicate. *)
    iDestruct "pts" as (?tGP ?tP ?tS) "#(knowOrder & histS1 & histS2 & histS3 & knowPred & %know & per)".
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    rewrite wp_eq /wp_def.
    rewrite wpc_eq.
    iIntros ([[SV PV] BV] incl2) "#val interp".
    monPred_simpl.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We open [interp]. *)
    iDestruct "interp" as (hists preds orders) "(ptsMap & allOrders & #ordered & map & history & preds)".

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (know_pred_agree with "preds knowPred") as (pred predsLook) "#predsEquiv".

    (* We need to get the points-to predicate for [ℓ] which is is inside
    [interp].  We want to look up the points-to predicate in [ptsMap]. To this
r   end, we combine our fragment of the history with the authorative element. *)
    iDestruct (own_frag_history_agree_singleton with "history histS3") as %look.
    destruct look as (absHist & enc & histAbsHist & lookTS & decodeEnc).
    apply lookup_fmap_Some in histAbsHist.
    destruct histAbsHist as [hist [histAbsHist histsLook]].

    (* We can now get the points-to predicate and execute the load. *)
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply wp_fupd.
    iApply (wp_load_acquire with "[$pts $val]").
    iNext. iIntros (t' v' SV' PV') "(%look & %gt & #val' & pts)".

    apply lookup_fmap_Some in look.
    destruct look as [[? s'] [msgEq histLook]].
    simpl in msgEq.
    rewrite /store_view. simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val'".

    assert ({[ℓ := MaxNat tS]} ⊑ SV) as inclSingl.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      etrans.
      apply know.
      etrans.
      apply incl.
      apply incl2. }
    assert (tS ≤ t') as lte.
    { pose proof (view_lt_lt _ _ ℓ inclSingl) as HIP.
      rewrite lookup_singleton in HIP.
      pose proof (transitivity HIP gt) as leq.
      simpl in leq.
      apply leq. }
    (* assert (is_Some (absHist !! t')) as HI. *)
    (* { eapply fmap_is_Some. *)
    (*   rewrite -lookup_fmap. *)
    (*   rewrite <- histAbsHist. *)
    (*   rewrite !lookup_fmap. *)
    (*   rewrite histLook. *)
    (*   eauto. } *)
    (* assert (t' = tS) as ->. *)
    (* { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done. *)
    (*   pose proof (nolater t' lt) as eq. *)
    (*   rewrite eq in HI. inversion HI as [? [=]]. } *)
    (* assert (absHist !! tS = Some s) as lookS. *)
    (* { rewrite -sLast. *)
    (*   apply map_slice_lookup_hi in slice. *)
    (*   rewrite slice. *)
    (*   erewrite last_app; done. } *)
    (* clear lte HI. *)

    (* iPoseProof (big_sepM2_dom with "map") as "%domEq". *)
    (* We need to get the predicate for [s] and [v']. *)
    (* iDestruct (big_sepM2_lookup_acc with "map") as "[HI HO]"; [done|done|]. *)

    iDestruct (big_sepM2_lookup_acc with "map") as "[predMap map]"; [done|done|].
    iDestruct (big_sepM_lookup_acc with "predMap") as "[predHolds predMap]"; first done.
    simpl.
    iDestruct "predHolds" as (P') "[%eq PH]".
    iDestruct (discrete_fun_equivI with "predsEquiv") as "HI".
    iDestruct ("HI" $! s') as "HIP". iClear "HI".
    iEval (rewrite discrete_fun_equivI) in "HIP".
    iDestruct ("HIP" $! v') as "HI". iClear "HIP".
    (* We now know exactly what the value in [ℓhist] at [tS] is. *)
    (* assert (s' = encode s) as sEq. *)
    (* { setoid_rewrite map_eq_iff in histAbsHist. *)
    (*   move: (histAbsHist tS). *)
    (*   rewrite !lookup_fmap. *)
    (*   rewrite histLook. *)
    (*   rewrite lookupV. *)
    (*   rewrite sLast. *)
    (*   simpl. *)
    (*   congruence. } *)
    (* rewrite sEq. *)
    (* rewrite decode_encode. *)
    (* iEval (rewrite -sEq) in "HI". *)
    rewrite msgEq. simpl.
    rewrite msgEq in eq. simpl in eq.
    rewrite eq.
    (*
    iAssert (⌜∃ s, Some s = decode s'⌝)%I as %[s sEqs'].
    { destruct (decode s').
      - iPureIntro. by eexists _.
      - simpl.
        rewrite option_equivI.
        iDestruct "HI" as %[]. }
     *)
    (* The loaded state must be greater than [s3]. *)
    iDestruct (big_sepM2_lookup_1 with "ordered") as (order) "[%ordersLook %increasingMap]".
    { apply histsLook. }
    iDestruct (orders_lookup with "allOrders knowOrder") as %orderEq; first apply ordersLook.
    (* epose proof (increasingMap tS t' (encode s3) s') as hihi. *)
    epose proof (increasingMap tS t' (encode s3) s') as hihi.
    assert (order enc s') as orderRelated.
    { eapply increasingMap.
      - apply lte.
      - subst. done.
      - rewrite lookup_fmap. rewrite histLook. done. }
    rewrite orderEq in orderRelated.
    epose proof (encode_relation_related _ _ _ orderRelated) as (? & s & eqX & decodeS' & s3InclS').
    assert (x = s3) as -> by congruence.
    (* rewrite decode_encode in eqX. *)
    (* pose proof eqX as [= <-]. *)
    (* clear eqX. *)
    (* iAssert (⌜s3 ⊑ s⌝)%I as %s3InclS. *)
    (* { iPureIntro. *)
    (*   eapply encode_relation_decode_iff with (eb := s') (ea := encode s3). *)
    (*   { by rewrite decode_encode. } *)
    (*   { done. } *)
    (*   (* apply encode_relation_iff. *) *)
    (*   rewrite -orderEq. *)
    (*   epose proof (increasingMap tS t' (encode s3) s') as hihi. *)
    (*   apply hihi. *)
    (*   - assumption. *)
    (*   - admit. (* We need to derive more knowledge about [tS], probably using [subset]. *) *)
    (*   - rewrite lookup_fmap. *)
    (*     rewrite histLook. *)
    (*     simpl. *)
    (*     done. } *)
    (* rewrite -sEqs'. *)
    rewrite decodeS'.
    simpl.
    rewrite option_equivI.
    iRewrite "HI" in "PH".
    (* rewrite monPred_at_objectively. *)
    rewrite /msg_to_tv. simpl.
    iSpecialize ("pToQ" $! (SV', PV', ∅) s v').
    monPred_simpl.
    iSpecialize ("pToQ" $! (SV', PV', ∅)).
    iDestruct ("pToQ" with "[//] [$PH]") as "[Q phi]".
    { monPred_simpl. done. }
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
    iSplitR "ptsMap allOrders ordered map history preds".
    2: { iExists _, _, _. iFrame. iFrame "#". }
    iSpecialize ("Φpost" $! s v').
    monPred_simpl.
    iApply "Φpost".
    { iPureIntro.
      etrans. eassumption.
      repeat split.
      - apply view_le_l.
      - apply view_le_l.
      - done. }
    iSplitR "Q".
    - iExists tGP, tP, t'.
      iFrame "knowOrder histS1".
      iFrame "∗#%".
      iPureIntro.
      repeat split.
      * (* FIXME: Intuitively the lhs. should be included in because we read
        [t'] and a write includes its own timestamp. We don't remember this
        fact, however. *)
        admit.
      * destruct TV as [[??]?].
        destruct TV' as [[??]?].
        etrans.
        apply know.
        etrans.
        apply incl.
        etrans.
        apply incl2.
        apply view_le_l.
      * apply view_empty_least.
    - iApply monPred_mono; last iApply "Q".
      repeat split.
      * apply view_le_r.
      * apply view_le_r.
      * apply view_empty_least.
  Admitted.

End wp_rules.
