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
From self.high Require Import resources crash_weakestpre lifted_modalities.

(* For each location in the heap we maintain the following "meta data".
For every location we want to store: A type/set of abstract events, its full
abstract history, the invariant assertion. The abstract history maps
timestamps to elements of the abstract events. *)
(* Record loc_info {Σ} := { *)
(*   l_state : Type; *)
(*   (* l_val : val; *) *)
(*   l_ϕ : l_state → val → dProp Σ; *)
(*   l_abstract_history : gmap nat (message * l_state); *)

(*   (* * Type class instances *) *)
(*   (* l_sqsubseteq : SqSubsetEq l_state; *) *)
(*   (* l_preorder : PreOrder (⊑@{l_state}); *) *)
(*   (* We need countable to squash states into [positive] *) *)
(*   l_eqdecision : EqDecision l_state; *)
(*   l_countable : Countable l_state; *)
(* }. *)

(* Existing Instances l_eqdecision l_countable. *)

(* Definition encode_loc_info {Σ} (l : (@loc_info Σ)):= *)
(*   ((λ '(m, s), (m, encode s)) <$> (l_abstract_history l), *)
(*    λ v s, (l_ϕ l $ v) <$> decode s). *)

Section wp.
  Context `{!nvmG Σ}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).

  Definition abs_hist_to_ra_old (abs_hist : gmap time (message * st)) : encoded_abs_historyR :=
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
    (∃ (hists : gmap loc (gmap time (message * st)))
       (preds : gmap loc (st → val → option (dProp Σ))),
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
  Proof.
  Admitted.

  Definition know_global_per_lower_bound `{Countable ST} (ℓ : loc) (s : ST) : dProp Σ :=
    ∃ t,
      ⎡persisted ({[ ℓ := MaxNat t ]} : view)⎤ ∗
      ⎡know_frag_history_loc ℓ {[ t := s ]}⎤.

  Definition know_persist_lower_bound `{Countable ST} (ℓ : loc) (s : ST) : dProp Σ :=
    ∃ t,
      monPred_in (∅, {[ ℓ := MaxNat t ]}, ∅) ∗
      ⎡know_frag_history_loc ℓ {[ t := s ]}⎤.

  (* It appears that we don't actually need this one. *)
  (* Definition know_store_lower_bound `{Countable ST} (ℓ : loc) (t : time) (s : ST) : dProp Σ := *)
  (*   monPred_in ({[ ℓ := MaxNat t ]}, ∅, ∅) ∗ *)
  (*   ⎡know_frag_history_loc ℓ {[ t := s ]}⎤. *)

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
    - rewrite ncfupd_unfold_at. simpl.
      iIntros "Hwp" (q).
      (* iApply wpc_value_inv'. done. *)
      admit.
    - iIntros "HΦ". iApply ncfupd_wpc. iSplit.
      { rewrite disc_unfold_at. done. }
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

(* Definition lastR (abs_state : Type) : cmra := *)
(*   prodR fracR (agreeR (prodO (leibnizO abs_state) valO)). *)

Section post_fence_modalities.
  Context `{!nvmG Σ}.

  Implicit Types (P : dProp Σ).

  Program Definition post_fence P : dProp Σ :=
    MonPred (λ '(s, p, b), P (s, (p ⊔ b), ∅)) _.
  Next Obligation.
    (* FIXME: Figure out if there is a way to make [solve_proper] handle this,
    perhaps by using [pointwise_relatio]. *)
    intros P. intros [[??]?] [[??]?] [[??]?]. rewrite /store_view /persist_view. simpl.
    assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
    apply monPred_mono.
    rewrite !subseteq_prod'.
    done.
  Qed.

End post_fence_modalities.

Notation "'<fence>' P" := (post_fence P) (at level 20, right associativity) : bi_scope.

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

  Lemma wp_load_ex ℓ ss ss' s Q ϕ st E :
    last ss' = Some s →
    {{{ ℓ ↦ ss; ss' | ϕ ∗ <obj> (∀ v, ϕ s v -∗ Q v ∗ ϕ s v) }}}
      Load (Val $ LitV $ LitLoc ℓ) @ st; E
    {{{ v, RET v; ℓ ↦ ss; ss' | ϕ ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "[pts pToQ]".
    iDestruct "pts" as (?tGP ?tP ?tS absHist) "(%incrL & %lookupP & %lookupV & %nolater & hist & knowPred & %slice & %know & per)".
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV PV] BV] incl2) "#val interp".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iDestruct "interp" as (hists preds) "(ptsMap & map & history & preds)".
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
    iDestruct (big_sepM2_lookup_acc with "map") as "[(%incr & predMap) map]"; [done|done|].
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
    { done. }

    iSplitR "ptsMap map history preds".
    2: { iExists _, _. iFrame. }
    iApply "Φpost".
    iSplitR "Q".
    2: {
      (* This _should_ hold bc. the view in the message is smaller. But, we
      don't have that fact. *)
      admit.
    }
    iExists _, _, _, _.
    iFrame "∗". iFrame "%".
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
  Admitted.

End wp_rules.
