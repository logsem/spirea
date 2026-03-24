From iris.proofmode Require Import proofmode monpred.
From iris_named_props Require Import named_props.

From self Require Import solve_view_le.
From self.base Require Import generational_resources primitive_laws.
From self.high Require Import wrappers protocol locations.
From self.high.lib Require Import abstract_state.
From self.high.modalities Require Import fence.

From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section post_fence_sync.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}.
  Implicit Types (ℓ : loc) (P Q: dProp Σ).
  (* For every location we [flush], we will keep the follow tuple,
   * - [ℓ], the location
   * - [σ], the abstract state we flush,
   * - [σ_xchg], the "exchange" state we want to extract resources from,
   * - [seen ℓ σ_xchg], so that we have the necessary view,
   * and we also keep enough resource to make three consecutive exchanges/updates with
   * the protocol in the future and obtain final post condition [R] (when we [flush_sync]),
   * - [<obj> p_read σ v -∗ □ <obj> P], for getting some basic facts about the physical value,
   * - [P -∗ <obj> (p_pers σ_old v_old ==∗ <obj> Q ∗ p_pers σ v)] roughly, for the persistent state update,
   * - [Q -∗ <obj> (p_read σ_xchg v_xchg ==∗ R ∗ p_read σ_xchg v_xchg)] for the read only exchange. *)

  Definition exchange_3 `{AbstractState ST} ℓ (σ_xchg: ST) (prot: LocationProtocol ST) Q: dProp Σ :=
    ∀ v_xchg, <obj> (prot.(p_read) σ_xchg v_xchg ==∗ Q ∗ prot.(p_read) σ_xchg v_xchg).

  (* TODO: include the other case as well *)
  Definition exchange_2 `{AbstractState ST} ℓ (σ_xchg σ: ST) v (prot: LocationProtocol ST) Q: dProp Σ :=
    ∀ σ_old v_old,
    <obj> ((⌜ σ_old ⊑ σ ⌝ -∗ prot.(p_pers) σ_old v_old ==∗
           prot.(p_pers) σ v ∗ exchange_3 ℓ σ_xchg prot Q) ∧
           (⌜ σ ⊑ σ_old ⌝ -∗ prot.(p_pers) σ_old v_old ==∗
           prot.(p_pers) σ_old v_old ∗ exchange_3 ℓ σ_xchg prot Q)).

  Definition exchange_1 `{AbstractState ST} ℓ (σ_xchg σ: ST) (prot: LocationProtocol ST) Q: dProp Σ :=
    ∀ v,
    <obj> (prot.(p_read) σ v -∗ prot.(p_read) σ v ∗ exchange_2 ℓ σ_xchg σ v prot Q).

  Record FlushInfo := MkFlushInfo {
    fi_ℓ: loc;
    fi_ST: Type;
    fi_ST_eqdec :> EqDecision fi_ST;
    fi_ST_countable :> Countable fi_ST;
    fi_ST_is_abstract :> AbstractState fi_ST;
    fi_prot: LocationProtocol fi_ST;
    fi_prot_conds :> ProtocolConditions fi_prot;
    fi_σ: fi_ST;
    fi_σ_xchg: fi_ST;
    fi_post: dProp Σ
  }.

  #[local] Definition internal_flush_lb `{AbstractState ST} ℓ (prot: LocationProtocol ST) (s : ST) : dProp Σ :=
    ∃ (t : nat) offset,
      "#lbBase" ∷ lb_base ℓ prot offset t s ∗
      (* this assertion is only ever to be used internally, we can safely assert over
       *  about buffer views. *)
      "%haveBV" ∷ have_thread_view (∅, ∅, {[ ℓ := MaxNat (t - offset) ]}).

  (* Definition seen_state_post_fence `{AbstractState ST} ℓ (prot: LocationProtocol ST) (s : ST) : dProp Σ := *)
  (*   ∃ (t offset : nat) (msg: message), *)
  (*     "#knowFragHist" ∷ lb_base ℓ prot offset t s ∗ *)
  (*     "#knowPhysMsg" ∷ ⎡ know_phys_hist_msg ℓ t msg ⎤ ∗ *)
  (*     "#haveMsg" ∷ have_msg_post_fence msg. *)
  
  Program Definition post_fence_sync_advanced
    (P : dProp Σ) : dProp Σ :=
    MonPred (λ TV,
      ∃ (fi_list: list FlushInfo),
        ([∗ list] fi ∈ fi_list,
           ⎡ is_at_loc fi.(fi_ℓ) ⎤ ∗
           ⎡ know_protocol fi.(fi_ℓ) fi.(fi_prot) ⎤ ∗
           (* this can probably be promoted to [flush_lb], but doens't seem necessary? *)
           internal_flush_lb fi.(fi_ℓ) fi.(fi_prot) fi.(fi_σ) ∗
           seen_state_post_fence (EqDecision0 := fi.(fi_ST_eqdec)) (H0 := fi.(fi_ST_countable)) fi.(fi_ℓ) fi.(fi_σ_xchg) ∗
           exchange_1 fi.(fi_ℓ) fi.(fi_σ_xchg) fi.(fi_σ) fi.(fi_prot) fi.(fi_post))
          TV ∗
        ((persisted (buffer_view TV)) -∗
         (([∗ list] fi ∈ fi_list, fi.(fi_post)) -∗ P)
           (store_view TV, (flush_view TV ⊔ buffer_view TV), buffer_view TV))
      )%I _.
  Next Obligation.
    intros P. intros [[??]?] [[??]?] [[??]?]. simpl.
    assert (g0 ⊔ g1 ⊑ g3 ⊔ g4). { solve_proper. }
    iIntros "(%fi_list & Hfi & P)".
    iExists fi_list.
    iSplitL "Hfi".
    - iApply monPred_mono; last done.
      solve_view_le.
    - iIntros "pers".
      iPoseProof (persisted_anti_mono with "pers") as "pers";
        (* use the special reasoning to figure out the view automatically. *)
        last iSpecialize ("P" with "pers"); first done.
      iApply monPred_mono; last done.
      solve_view_le.
  Qed.
End post_fence_sync.

Notation "'<FS>' P" :=
  (post_fence_sync_advanced P) (at level 20, right associativity) : bi_scope.

Section lemmas.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}.
  Implicit Types (ℓ : loc) (P Q: dProp Σ).

  Lemma post_fenc_sync_advanced_post_fence_sync P :
    <fence_sync> P -∗ <FS> P.
  Proof.
    iModel. simpl.
    iIntros "P".
    iExists []. simpl.
    rewrite left_id.
    iFrame.
    done.
  Qed.

  Lemma post_fence_sync_advanced_mono P Q : (P ⊢ Q) → <FS> P ⊢ <FS> Q.
  Proof.
    intros Hi. iModel. simpl.
    iIntros "(%fi_list & exchanges & P)".
    iExists fi_list.
    rewrite -Hi.
    iFrame.
  Qed.

  Lemma post_fence_sync_advanced_intro P : P ⊢ <FS> P.
  Proof.
    iModel. destruct TV as [[??]?]. simpl.
    iIntros "P".
    iExists []. simpl.
    iSplitR; first done.
    iIntros "pers".
    rewrite left_id.
    iApply (monPred_mono with "P"). repeat split; auto using view_le_l.
  Qed.

  Lemma post_fence_sync_advanced_emp : (emp : dProp Σ) ⊢ <FS> emp.
  Proof. apply post_fence_sync_advanced_intro. Qed.

  Lemma post_fence_sync_and P Q : <FS> (P ∧ Q) ⊣⊢ <FS> P ∧ <FS> Q.
  Proof.
  Abort.

  Lemma post_fece_sync_advanced_sep P Q:
    post_fence_sync_advanced P ∗ post_fence_sync_advanced Q ⊢ (post_fence_sync_advanced (P ∗ Q)).
  Proof.
    iModel.
    destruct TV as [[SV PV] BV].
    iIntros "[P Q]".
    rewrite /post_fence_sync_advanced /=.
    iDestruct "P" as (P_list) "[P_exchanges Ppost]".
    iDestruct "Q" as (Q_list) "[Q_exchanges Qpost]".
    iExists (P_list ++ Q_list).
    rewrite ?monPred_at_big_sepL.
    iDestruct (big_sepL_app with "[$P_exchanges $Q_exchanges]") as "exchanges".
    iFrame "exchanges".
    rewrite big_sepL_app.
    rewrite ?monPred_at_wand.
    iIntros "#persisted" ([[SV' PV'] BV'] [[? ?] ?]) "[Pfi_post Qfi_post]".
    iSpecialize ("Ppost" with "[$]").
    iDestruct ("Ppost" with "[] Pfi_post") as "$".
    { iPureIntro. solve_view_le. }
    iSpecialize ("Qpost" with "[$]").
    iDestruct ("Qpost" with "[] Qfi_post") as "$".
    { iPureIntro. solve_view_le. }
  Qed.

  Lemma post_fence_sync_advanced_intuitionistically_2 P : □ <FS> P ⊢ <FS> □ P.
  Proof.
    iModel. simpl.
    iIntros "(%fi_list & #exchanges & #P)".
    iExists fi_list.
    iFrame "exchanges".
    iIntros "#persisted".
    iSpecialize ("P" with "persisted").
    rewrite ?monPred_at_wand.
    iIntros (TV' ?) "fi_post".
    iSpecialize ("P" with "[//] fi_post").
  Abort.
End lemmas.

Section Tests.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, AbstractState ST}.
  
  Variables (ℓ : loc) (prot: LocationProtocol ST) (σ σ_xchg: ST) (P: iProp Σ) (Q: dProp Σ).

  (* just need to make sure [P] survives until last exchange *)
  Example embed_into_exchange_3:
    ⎡ P ⎤ ⊢ exchange_1 ℓ σ σ_xchg prot Q.
  Proof.
    rewrite /exchange_1 /exchange_2 /exchange_3.
    iIntros "P" (v) "!> $".
    iIntros (σ_old v_old) "!>".
    iSplit.
    - admit.
    - iIntros (?) "$ !>".
      iIntros (v_xchg) "!> $".
      iClear "P".
  Abort.
End Tests.
