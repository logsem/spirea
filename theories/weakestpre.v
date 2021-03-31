(* In this file we define our weakest precondition on top of the weakest
precondition included in Iris. *)

From stdpp Require Import countable numbers gmap.
From iris Require Export invariants.
From iris.proofmode Require Export tactics.
From iris.algebra Require Import gmap excl auth.
From iris.program_logic Require weakestpre.
From iris.program_logic Require Import ownp.
From iris_string_ident Require Import ltac2_string_ident.
From iris.heap_lang Require Import locations.

From self Require Export dprop view lang.
From self.lang Require Import primitive_laws syntax.

(* Resource algebra for location histories. *)
(* Definition event states : Type := val * states. *)
(* Definition abshist abs_state := gmap time abs_state. *)
(* Definition abshistR (states : Type) : ucmra := gmapUR time (agreeR (leibnizO states)). *)

Notation st := positive.
Notation stO := positiveO.

Definition predicateR {Σ} := agreeR (st -d> laterO (optionO (dPropO Σ))).
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
  l_ϕ : l_state → dProp Σ;
  l_abstract_history : gmap nat l_state;

  (* * Type class instances *)
  l_sqsubseteq : SqSubsetEq l_state;
  l_preorder : PreOrder (⊑@{l_state});
  (* We need countable to squash states into [positive] *)
  l_eqdecision : EqDecision l_state;
  l_countable : Countable l_state;
}.

Existing Instances l_eqdecision l_countable.

Definition encode_loc_info {Σ} (l : (@loc_info Σ)):=
  (encode <$> (l_abstract_history l), λ s, (l_ϕ l) <$> decode s).

Section wp.
  Context `{!nvmG Σ, !inG Σ (@predicatesR Σ), !inG Σ historiesR}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).

  Definition abs_hist_to_ra (abs_hist : abs_history) : abs_historyR :=
    to_agree <$> abs_hist.

  Definition pred_to_ra (pred : st → option (dProp Σ)) : (@predicateR Σ) :=
    to_agree (Next ∘ (pred : st -d> optionO (dPropO Σ))).

  (* Definition loc_to_hist_ra (l : (@loc_info Σ)) `{Countable l} : abs_historyR := *)
  (*   (to_agree ∘ encode) <$> l_abstract_history l. *)

  (* We keep this in the weakest precondition. *)
  Definition interp (γ : gname) : iProp Σ :=
    (∃ (ls : gmap loc ((gmap time positive) * (positive → option (dProp Σ)))),
        ⌜map_Forall (λ ℓ enc, ∃ l, enc = encode_loc_info l) ls⌝ ∗
        (own γ ((● (abs_hist_to_ra <$> (fst <$> ls))) : historiesR)) ∗
        (own γ (● ((pred_to_ra <$> (snd <$> ls))) : predicatesR))).

  (* Our weakest precondition is a [dProp]. We construct it using [MonPred]
  which wraps the function along with a proof that it is monotone. *)
  Program Definition wp_def s E e Φ : dProp Σ :=
    MonPred (λ V,
      ∀ TV,
        ⌜V ⊑ TV⌝ -∗
        valid (store_view TV) -∗
        WP (ThreadState e TV) @ s; E {{ λ res,
          let '(ThreadVal v TV') := res return _ in
            valid (store_view TV') ∗ (Φ v TV')
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
    iIntros "% Hwp" (V ->) "Hseen". iApply (lifting.wp_pure_step_fupd _ E E')=>//.
    clear Hexec. iInduction n as [|n] "IH"=>/=.
    - by iApply "Hwp".
    - iMod "Hwp". iModIntro. iModIntro. iMod "Hwp". iModIntro.
      by iApply ("IH" with "Hwp").
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

Definition abs_history (abs_state : Type) : Type := gmap time (agree (leibnizO abs_state)).
Definition abs_historyR (abs_state : Type) : cmra := gmapR time (agreeR (leibnizO abs_state)).

(* Definition last (abs_state : Type) : Type :=  *)
Definition lastR (abs_state : Type) : cmra :=
  prodR fracR (agreeR (prodO (leibnizO abs_state) valO)).

Section wp_rules.
  Context `{!SqSubsetEq abs_state, !PreOrder (⊑@{abs_state})}.
  Context `{!nvmG Σ}.
  Context `{!inG Σ (abs_historyR abs_state), !inG Σ (lastR abs_state)}.

  Implicit Types (ℓ : loc) (ϕ : abs_state → val → dProp Σ).

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

  (* Exclusive points-to predicate. This predcate says that we know that the
  last events at [ℓ] corresponds to the *)
  Definition mapsto_ex ι γabs γlast ℓ (ss ss' : list abs_state)
             (s : abs_state) v ϕ : dProp Σ :=
    (∃ (tGlobalPers tPers tStore : time),
      ⎡inv ι (mapsto_ex_inv ℓ ϕ γabs γlast)⎤ ∗
      monPred_in ({[ ℓ := MaxNat tStore ]}, {[ ℓ := MaxNat tPers ]}, ∅) ∗
      ⎡own γlast (((1/2)%Qp, to_agree (s, v)) : lastR abs_state)⎤ ∗
      ⎡own γabs ({[ tStore := to_agree s ]} : abs_historyR abs_state)⎤ ∗
      ⎡persisted ({[ ℓ := MaxNat tGlobalPers ]} : view)⎤
    ).

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

  Lemma wp_alloc `{!SqSubsetEq abs_state, !PreOrder (⊑@{abs_state})}
        ℓ v (s : abs_state) (ϕ : abs_state → val → dProp Σ) st E :
    {{{ ϕ s v }}}
      ref v @ st; E
    {{{ ι, RET #ℓ; mapsto_ex ι ℓ [] [] s Φ }}}
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

Section wp_rules.
