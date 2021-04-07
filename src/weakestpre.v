(* In this file we define our weakest precondition on top of the weakest
precondition included in Iris. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Export invariants.
From iris.proofmode Require Export tactics.
From iris.algebra Require Import gmap excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.

From self Require Export extra dprop view lang.
From self.lang Require Import primitive_laws syntax.


(* Resource algebra for location histories. *)
(* Definition event states : Type := val * states. *)
(* Definition abshist abs_state := gmap time abs_state. *)
(* Definition abshistR (states : Type) : ucmra := gmapUR time (agreeR (leibnizO states)). *)

Notation st := positive (only parsing).
Notation stO := positiveO (only parsing).

Definition predicateR {Σ} := agreeR (st -d> val -d> laterO (optionO (dPropO Σ))).
Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

Definition abs_history := gmap time st.
Definition abs_historyR := gmapUR nat (agreeR stO).
Definition historiesR := authR (gmapUR loc abs_historyR).

(* For each location in the heap we maintain the following "meta data".
For every location we want to store: A type/set of abstract events, its full
abstract history, the invariant assertion. The abstract history maps
timestamps to elements of the abstract events. *)
Record loc_info {Σ} := {
  l_state : Type;
  (* l_val : val; *)
  l_ϕ : l_state → val → dProp Σ;
  l_abstract_history : gmap nat (message * l_state);

  (* * Type class instances *)
  (* l_sqsubseteq : SqSubsetEq l_state; *)
  (* l_preorder : PreOrder (⊑@{l_state}); *)
  (* We need countable to squash states into [positive] *)
  l_eqdecision : EqDecision l_state;
  l_countable : Countable l_state;
}.

(* Existing Instances l_eqdecision l_countable. *)

(* Definition encode_loc_info {Σ} (l : (@loc_info Σ)):= *)
(*   ((λ '(m, s), (m, encode s)) <$> (l_abstract_history l), *)
(*    λ v s, (l_ϕ l $ v) <$> decode s). *)

Class wpnvmG Σ := WpnvmG {
  γh : gname;
  γp : gname;
  ra_inG :> inG Σ (@predicatesR Σ);
  ra'_inG :> inG Σ historiesR;
}.

Section wp.
  Context `{!nvmG Σ, !wpnvmG Σ}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).

  Definition abs_hist_to_ra (abs_hist : gmap time (message * st)) : abs_historyR :=
    (to_agree ∘ snd) <$> abs_hist.

  Definition hi (f : nat → nat) : natO -d> natO := f.

  Definition pred_to_ra (pred : st → val → option (dProp Σ)) : (@predicateR Σ) :=
    to_agree ((λ a b, Next (pred a b))).

  (* Definition loc_to_hist_ra (l : (@loc_info Σ)) `{Countable l} : abs_historyR := *)
  (*   (to_agree ∘ encode) <$> l_abstract_history l. *)

  (* Record foo := { foo_car : Type; foo_rel : relation foo_car; }. *)
  (* Definition bar := gmap nat foo. *)

  (* Definition test : Prop := ∃ (S : Set) (_ : relation S), True. *)
  (* Definition test : iProp Σ := ∃ (S : Set) (_ : relation S), True. *)
  
  (* Definition test (m : gmap nat nat) : iProp Σ := *)
  (*   ([∗ map] ℓ ↦ enc ∈ m, *)
  (*     ∃ (S : Type) _ : EqDecision S) (_ : Countable S) (_ : relation S), *)
  (*       ⌜encode s = enc⌝). *)

  Lemma foo_testa {S : Set} `{Countable S}
      (ϕ : S → iProp Σ) (ϕenc : positive → iProp Σ) s p :
    ϕ = ϕenc ∘ encode →
    encode s = p → 
    ϕenc p -∗ ϕ s.
  Proof.
    iIntros (eq eq') "H". rewrite eq. simpl. rewrite eq'. iApply "H".
  Qed.

  Lemma foo_testb {S : Set} `{Countable S}
    (ϕ : S → iProp Σ) (ϕenc : positive -d> optionO (iPropO Σ)) s p (P : iProp Σ) :
    ϕenc ≡ (λ s, ϕ <$> (decode s)) →
    p ≡ encode s →
    ϕenc p ≡ Some P →
    P ⊣⊢ ϕ s.
  Proof.
    iIntros (eq eq'). rewrite eq'.
    pose proof (eq (encode s)) as HI.
    rewrite HI.
    rewrite decode_encode.
    simpl.
    intros HO.
    apply Some_equiv_inj in HO.
    rewrite HO.
    done.
  Qed.

  (** We keep this in the weakest precondition. **)
  Definition interp : iProp Σ :=
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
      own γh (● (abs_hist_to_ra <$> hists) : historiesR) ∗
      own γp (● (pred_to_ra <$> preds) : predicatesR)).

  Definition know_pred `{Countable s}
      (ℓ : loc) (ϕ : s → val → dProp Σ) : iProp Σ :=
    own γp (◯ {[ ℓ := pred_to_ra (λ s' v, (λ s, ϕ s v) <$> decode s') ]} : predicatesR).

  Definition know_state `{Countable s} ℓ (t : time) (s' : s) : iProp Σ :=
    own γh (◯ {[ ℓ := {[ t := to_agree (encode s') ]} ]} : historiesR).

  (* A few lemmas about [interp], [know_pred], [know_state]. *)

  Lemma singleton_included_l' `{Countable K} `{CmraTotal A} (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    (* Use [setoid_rewrite] to rewrite under the binder. *)
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  Lemma know_state_Some `{Countable ST} hists ℓ t (s : ST) :
    own γh (● (abs_hist_to_ra <$> hists) : historiesR) -∗
    know_state ℓ t s -∗
    ∃ m, ⌜hists !! ℓ = Some m⌝.
  Proof.
    iIntros "A B".
    destruct (hists !! ℓ) as [m|] eqn:Heq.
    { iExists m. done. }
    iDestruct (own_valid_2 with "A B") as %[Hincl _]%auth_both_valid_discrete.
    apply singleton_included_l' in Hincl.
    move: Hincl => [? [isSome ?]].
    rewrite lookup_fmap in isSome.
    rewrite Heq in isSome.
    inversion isSome.
  Qed.

  (* _Exclusive_ points-to predicate. This predcate says that we know that the
  last events at [ℓ] corresponds to the *)
  Definition mapsto_ex `{Countable ST}
      ℓ (ss ss' : list (ST * val)) (ϕ : ST → val → dProp Σ) : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time) (abs_hist : gmap time (ST * val)) hist,
      ⎡([∗ map] t ↦ msg; abs ∈ hist; abs_hist, ⌜msg.(msg_val) = abs.2⌝)⎤ ∗
      ⎡ℓ ↦h hist⎤ ∗
      ⌜abs_hist !! tStore = last ss'⌝ ∗
      ⌜(∀ t', tStore < t' → abs_hist !! t' = None)⌝ ∗
      (* ⌜max_member abs_hist tStore ⌝ ∗ *)
      (* ⌜map_slice abs_hist tGlobalPers tStore (ss ++ ss')⌝ ∗ *)
      (* ⌜map_slice abs_hist tPers tStore ss'⌝ ∗ *)
      (* We "have"/"know" of the three timestamps. *)
      monPred_in ({[ ℓ := MaxNat tStore ]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      ⎡persisted ({[ ℓ := MaxNat tGlobalPers ]} : view)⎤).

  (*
  Definition mapsto_read `{!SqSubsetEq abs_state, !PreOrder (⊑@{abs_state})}
             ι γabs γlast ℓ (s1 s2 s3 : abs_state) ϕ : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time),
      (* We know that the global persist view has [tGlobalPers]. *)
      ⎡persisted {[ ℓ := MaxNat tGlobalPers ]}⎤ ∗
      (* We know that our lobal views have [tPers] and [tStore]. *)
      monPred_in ({[ ℓ := MaxNat tStore]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      ⎡inv ι (mapsto_ex_inv ℓ ϕ γabs γlast)⎤ ∗
      ⎡own γabs ({[ tGlobalPers := to_agree s1 ]} : abs_historyR abs_state)⎤ ∗
      ⎡own γabs ({[ tPers := to_agree s2 ]} : abs_historyR abs_state)⎤ ∗
      ⎡own γabs ({[ tStore := to_agree s3 ]} : abs_historyR abs_state)⎤).
  *)

  (*
  Definition mapsto_ex_inv ℓ ϕ (γabs γlast : gname) : iProp Σ :=
    (∃ (hist_misc : (gmap time (message * abs_state))) (s : abs_state) v, (* (es es' : list abs_state), *)
      (* ℓ points to the messages in [hist_misc]. *)
      ℓ ↦h (fst <$> hist_misc) ∗
      (* ghost state for all the abstract states. *)
      (* ⌜hi = (snd <$> hist_misc)⌝ ∗ *)
      own γabs ((to_agree <$> (snd <$> hist_misc)) : abs_historyR abs_state) ∗
      (* [s] and [v] is the state and value of the last write *)
      own γlast (((1/2)%Qp, to_agree (s, v)) : lastR abs_state) ∗
      (* FIXME *)
      ([∗ map] ℓ ↦ misc ∈ hist_misc,
        ϕ (snd misc) (msg_val $ fst $ misc) (msg_store_view $ fst $ misc, msg_persist_view $ fst $ misc, ∅))
    ).
  *)

  (* Our weakest precondition is a [dProp]. We construct it using [MonPred]
  which wraps the function along with a proof that it is monotone. *)
  Program Definition wp_def s E e Φ : dProp Σ :=
    MonPred (λ V,
      ∀ TV,
        ⌜V ⊑ TV⌝ -∗
        valid (store_view TV) -∗
        interp -∗
        WP (ThreadState e TV) @ s; E {{ λ res,
          let '(ThreadVal v TV') := res return _ in
            valid (store_view TV') ∗ (Φ v TV') ∗ interp
        }})%I _.
  Next Obligation. solve_proper. Qed.

  (* This is sealing follows the same ritual as the [wp] in Iris. *)
  Definition wp_aux : seal (@wp_def). by eexists. Qed.

  Global Instance expr_wp : Wp expr_lang (dProp Σ) stuckness := wp_aux.(unseal).

  Lemma wp_eq : wp = wp_def.
  Proof. rewrite -wp_aux.(seal_eq). done. Qed.

  (* We prove a few basic facts about our weakest precondition. *)
  Global Instance wp_ne s E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e).
  Proof. rewrite wp_eq. constructor=>V. solve_proper. Qed.
  Global Instance wp_proper s E e :
    Proper (pointwise_relation val (≡) ==> (≡)) (wp s E e).
  Proof. rewrite wp_eq. constructor=>V. solve_proper. Qed.

  (* For the WP in Iris the other direction also holds, but not for this WP *)
  Lemma wp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
  Proof.
    iStartProof (iProp _). iIntros (TV').
    rewrite wp_eq. rewrite /wp_def.
    iIntros ">HΦ %TV **".
    iApply (weakestpre.wp_value_fupd' _ _ _ (ThreadVal v TV)).
    iFrame "#∗". done.
  Qed.

  Lemma wp_value_fupd s E Φ e v : IntoVal e v → (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
  Proof. intros <-. by apply wp_value_fupd'. Qed.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof. rewrite -wp_value_fupd'. auto. Qed.

  Notation PureExecBase P nsteps e1 e2 :=
    (∀ TV, PureExec P nsteps (ThreadState e1 TV) (ThreadState e2 TV)).

  Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    rewrite wp_eq=>Hexec Hφ. iStartProof (iProp _).
    iIntros "% Hwp" (V ->) "Hseen Hinterp". iApply (lifting.wp_pure_step_fupd _ E E')=>//.
    clear Hexec. iInduction n as [|n] "IH"=>/=.
    - iApply ("Hwp" with "[% //] Hseen Hinterp").
    - iMod "Hwp". iModIntro. iModIntro. iMod "Hwp". iModIntro.
      iApply ("IH" with "Hwp [$] [$]").
  Qed.

  (* This lemma is like the [wp_pure_step_later] in Iris except its premise uses
  [PureExecBase] instead of [PureExec]. *)
  Lemma wp_pure_step_later `{!nvmG Σ} s E e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

End wp.

(* Definition abs_history (abs_state : Type) : Type := gmap time (agree (leibnizO abs_state)). *)
(* Definition abs_historyR (abs_state : Type) : cmra := gmapR time (agreeR (leibnizO abs_state)). *)

(* Definition last (abs_state : Type) : Type :=  *)
Definition lastR (abs_state : Type) : cmra :=
  prodR fracR (agreeR (prodO (leibnizO abs_state) valO)).

Section wp_rules.
  Context `{SqSubsetEq abs_state, !PreOrder (⊑@{abs_state}), Countable abs_state}.
  Context `{!nvmG Σ, !wpnvmG Σ}.

  Implicit Types (ℓ : loc) (s : abs_state) (ϕ : abs_state → val → dProp Σ).

  (* The exclusive points-to predicate. *)
  Notation "l ↦ xs ; ys | P" := (mapsto_ex l xs ys P) (at level 20).

  Lemma wp_load_ex ℓ ss ss' s v ϕ st E :
    last ss' = Some (s, v) →
    {{{ ℓ ↦ ss ; ss' | ϕ }}}
      Load (Val $ LitV $ LitLoc ℓ) @ st; E
    {{{ RET v; ℓ ↦ ss ; ss' | ϕ }}}.
  Proof.
    intros last.
    rewrite wp_eq /wp_def.
    iStartProof (iProp _).
    iIntros (post ((sv & pv) & bv)) "Hpts".
    (* We destruct the exclusive points-to predicate. *)
    iDestruct "Hpts" as (t1 t2 t3 abs hist) "(big & ℓPts & %look & %nolater & %incl & #pers)".
    rewrite last in look.
    simpl.
    iPoseProof (big_sepM2_dom with "big") as "%domEq".
    move: incl => [[incl3 incl2] incl'].
    iIntros ([[idxS idxP] idxB] [[??]?]) "Hpost". simpl.
    iIntros ([[sv' pv'] bv'] [[??]?]) "#Hv Hint".
    iApply (wp_load with "[$ℓPts $Hv]").
    iNext.
    iIntros (t' v') "[ℓPts [%hi %ho]]".
    rewrite /store_view. simpl.
    iFrame "#∗".
    assert ({[ℓ := MaxNat t3]} ⊑ sv').
    { etrans. eassumption. etrans. eassumption. eassumption. }
    (* We need to conclude that the only write we could read is the one at [t3]. *)
    assert (t3 ≤ t') as lte.
    { pose proof (view_lt_lt _ _ ℓ H7) as HIP.
      pose proof (transitivity HIP ho).
      rewrite lookup_singleton in H8.
      simpl in H8.
      apply H8. }
    assert (is_Some (abs !! t')) as HI.
    { apply elem_of_dom. rewrite -domEq. apply elem_of_dom.
      rewrite -lookup_fmap in hi.
      apply lookup_fmap_Some in hi.
      destruct hi as [msg look'].
      exists msg. apply look'. }
    assert (t' = t3) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      pose proof (nolater t' lt) as eq.
      rewrite eq in HI. inversion HI. inversion H8. }
    iAssert (⌜v' = v⌝)%I as %->.
    { rewrite -lookup_fmap in hi.
      apply lookup_fmap_Some in hi.
      destruct hi as [msg [msgEq look']].
      iDestruct (big_sepM2_lookup with "big") as "%eq"; [done|done|].
      iPureIntro. simpl in eq. congruence. }
    (* We need this fact to be apple  to apply Hpost. *)
    assert ((idxS, idxP, idxB) ⊑ (sv', pv', bv')). { done. }
    iApply "Hpost".
    iExists _, _, _, _, _.
    rewrite last.
    iFrame (look nolater) "big ℓPts pers".
    iSplit; first iSplit; try done; iPureIntro.
    - etrans. apply incl2.
      etrans. eassumption.
      eassumption.
    - apply view_empty_least.
  Qed.

  (* A read-only points-to predicate. *)
  Definition mapsto_ro ℓ (s : abs_state) ϕ : dProp Σ :=
    ∃ t, monPred_in ({[ ℓ := MaxNat t ]}, ∅, ∅) ∗
         ⎡know_pred ℓ ϕ⎤ ∗ ⎡know_state ℓ t s⎤.

  Notation "l ↦ro s | P" := (mapsto_ro l s P) (at level 20).

  Lemma wp_load ℓ s ϕ st E R :
    {{{ (∀ s' v, ϕ s' v -∗ ϕ s' v ∗ R s' v) ∗
        ℓ ↦ro s | ϕ }}}
      Load (Val $ LitV $ LitLoc ℓ) @ st; E
    {{{ s' v, RET v; ℓ ↦ro s' | ϕ ∗ R s' v }}}.
  Proof.
    rewrite wp_eq /wp_def.
    iStartProof (iProp _).
    iIntros (post ((sv & pv) & bv)) "[Htrans #Hpts]".
    iDestruct "Hpts" as (t) "(%seen & knowPred & knowState)".
    iIntros (? ?) "Hpost". simpl. iIntros ([[sv' pv'] bv'] ?) "#Hv Hint".
    iDestruct "Hint" as (hists preds) "(pointsToPreds & ? & authHists & authPreds)".
    iDestruct (own_valid_2 with "authHists knowState") as %Hv.
    iDestruct (know_state_Some with "[$] [$]") as %[hist look].
    iDestruct (big_sepM_delete with "pointsToPreds") as "[ℓPts pointsToPreds]"; first done.
    iApply (wp_load with "[$ℓPts $Hv]").
    iNext.
    iIntros (t' v') "[ℓPts %FOO]".
    iFrame "Hv".
    iSplitL "Hpost".
    - iApply "Hpost".
      admit.
    - (* Re-establish interp. *)
      rewrite /interp.
      iExists _, _.
      iFrame "authHists authPreds".
      iFrame.
      iApply big_sepM_delete; first done.
      iFrame.
  Abort.

  (*
  Lemma wp_alloc `{!SqSubsetEq abs_state, !PreOrder (⊑@{abs_state})}
        ℓ v (s : abs_state) (Φ : abs_state → val → dProp Σ) st E :
    {{{ Φ s v }}}
      ref v @ st; E
    {{{ ι, RET ℓ; mapsto_ex ι ℓ [] [] s Φ }}}
  Proof.

  Lemma wp_store ℓ ι ℓ ss ss' s ev' ϕ s E :
    {{{ mapsto_ex ι ℓ ss ss' s Φ ∗ ϕ ev' v }}}
      #ℓ <- v @ s; E
    {{{ RET #(); mapsto_ex ι ℓ ss (ss' ++ [s]) ev' Φ }}}
  Proof.

  Lemma wp_load ℓ ι ℓ ss ss' ϕ s E :
    {{{ mapsto_ex ι ℓ ss ss' s Φ }}}
      !ℓ @ s; E
    {{{ v, RET v; mapsto_ex ι ℓ ss ss' Φ ∗ ϕ s v }}}
  Proof.
  *)

End wp_rules.

Section wp_things.
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

End wp_things.
