(** This file defines the lifted [nextgen] modality for [monPred] *)

From iris.proofmode Require Import proofmode.

From self.high.lib Require Import abstract_state.

From self.base Require Import generational_resources.
From self.high Require Import dprop generational_resources.
From self.nextgen Require Export nextgen_promises.

Set Default Proof Using "Type*".

(** Even with the nextgen modality, we still need some resources that is only
 ** obtainable with a centralized view of the system.
 ** NOTE: we need to know a state exist even though it might survive anyway.
 ** This is used to obtain the decode/encode relation, which in turns tell us that
 ** decoding the crash state will succeed. *)
Definition know_crash_frag_history_loc `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}: iProp Σ :=
  □ (∀ ℓ t (ST: Type) (_ : EqDecision ST) (_ : Countable ST) (_ : abstract_state.AbstractState ST)
       (bumper: ST → ST) (OV OCV: view.view) (σ: ST),
       crashed_at_both OV OCV -∗ ⌜ ℓ ∈ dom OCV ⌝ -∗ (* that we know location [ℓ] survives *)
       lastgen_know_preorder_loc ℓ (abstract_state.abs_state_relation (ST := ST)) -∗ (* and we know the preorder *)
       lastgen_know_frag_history_loc ℓ t σ -∗ (* and we know a state exists. *)
       lastgen_know_bumper ℓ bumper -∗ (* and we know the bumper *)
       (* we know a crashed timestamp exists. *)
       ∃ (σ_c: ST) v_c, crashed_in_loc ℓ σ_c ∗ know_frag_history_loc ℓ (OCV !!0 ℓ) (bumper σ_c) ∗
                        know_phys_hist_msg ℓ (OCV !!0 ℓ) (Msg v_c ∅ ∅ ∅) ∗
                        (* and any state we know are "persisted" will be ordered earlier than [σ_c] *)
                        (* TODO: the first half of this knowledge should really be part of the [crashed_at] rely *)
                        ⌜ t - (OV !!0 ℓ) ≤ (OCV !!0 ℓ) - (OV !!0 ℓ) → OV !!0 ℓ ≤ OCV !!0 ℓ ∧ σ ⊑ σ_c ⌝).

(* Definition crashed_in_impl OCV `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}: iProp Σ := *)
(*   [∗ map] ℓ ↦ t ∈ OCV, *)
(*     □ (∀ (ST: Type) (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST) (bumper: ST → ST), *)
(*          know_preorder_loc ℓ (abs_state_relation (ST := ST)) -∗ *)
(*          know_bumper ℓ bumper -∗ *)
(*          ∃ (σ: ST), crashed_in_loc ℓ σ ∗ know_frag_history_loc ℓ (max_nat_car t) (bumper σ)). *)

Program Definition nextgen `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω} (P: dProp Σ): dProp Σ :=
  MonPred (λ TV, ⚡==> know_crash_frag_history_loc -∗ P (∅, ∅, ∅))%I _.

Class IntoNextgen `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω} (P Q : dProp Σ) :=
  into_nextgen : P ⊢ nextgen Q.
#[global] Arguments IntoNextgen {_ _ _ _} _%_I _%_I.
#[global] Arguments into_nextgen {_ _ _ _} _%_I _%_I.
#[global] Hint Mode IntoNextgen + + + + + - : typeclass_instances.


Section Modality.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}.
  Implicit Types (P Q: dProp Σ).

  Lemma nextgen_mono (P Q: dProp Σ) :
    (P ⊢ Q) → nextgen P ⊢ nextgen Q.
  Proof.
    intros Hi.
    iStartProof (iProp _); iIntros (?).
    simpl.
    iApply nextgen_mono.
    iIntros "H #?".
    iApply Hi.
    by iApply "H".
  Qed.

  #[global] Instance nextgen_mono' :
    Proper ((⊢) ==> (⊢)) (nextgen).
  Proof. intros P Q. apply nextgen_mono. Qed.

  (* #[global] Instance nextgen_ne : NonExpansive nextgen. *)
  (* Proof.  solve_proper. Qed. *)

  (* #[global] Instance nextgen_proper : Proper ((≡) ==> (≡)) nextgen := ne_proper _. *)

  Lemma nextgen_intuitionistic P Q:
    IntoNextgen P Q → □ P ⊢ nextgen (□ Q).
  Proof.
    intros Hi.
    iStartProof (iProp _); iIntros (?).
    rewrite Hi.
    simpl.
    iIntros "#H !> #?".
    rewrite monPred_at_intuitionistically.
    iModIntro.
    by iApply "H".
  Qed.

  Lemma nextgen_and P Q:
    nextgen P ∧ nextgen Q ⊢ nextgen (P ∧ Q).
  Proof.
    intros.
    iStartProof (iProp _); iIntros (?). simpl.
    rewrite nextgen_and_1.
    iIntros "H !> #?".
    iSplit.
    - iDestruct "H" as "[H _]".
      by iApply "H".
    - iDestruct "H" as "[_ H]".
      by iApply "H".
  Qed.

  Lemma nextgen_emp:
    emp ⊢ nextgen emp.
  Proof.
    iStartProof (iProp _); iIntros (?). simpl.
    by iIntros "_ !> _".
  Qed.

  Lemma nextgen_sep P Q:
    nextgen P ∗ nextgen Q ⊢ nextgen (P ∗ Q).
  Proof.
    iStartProof (iProp _). iIntros (TV).
    simpl.
    rewrite nextgen_sep_2.
    iIntros "H !> #?".
    iDestruct "H" as "[P Q]".
    iSplitL "P"; first by iApply "P".
    by iApply "Q".
  Qed.

  Lemma modality_nextgen_mixin :
    modality_mixin (@nextgen _ _ _ _)
      (MIEnvTransform IntoNextgen) (MIEnvTransform IntoNextgen).
  Proof.
    split; simpl; split_and?.
    - apply nextgen_intuitionistic.
    - apply nextgen_and.
    - done.
    - apply nextgen_emp.
    - apply nextgen_mono.
    - apply nextgen_sep.
  Qed.
  Definition modality_nextgen :=
    Modality _ modality_nextgen_mixin.

  #[global] Instance from_modal_nextgen (P: dProp Σ) :
    FromModal True modality_nextgen (nextgen P) (nextgen P) P | 1.
  Proof. by rewrite /FromModal. Qed.

  #[global] Instance into_nextgen_into_nextgen (P Q: iProp Σ) :
    nextgen_promises_model.IntoNextgen P Q → IntoNextgen ⎡ P ⎤ ⎡ Q ⎤.
  Proof.
    rewrite /IntoNextgen /IntoNextgen.
    intros Hi.
    iStartProof (iProp _); iIntros (?). simpl.
    rewrite Hi.
    iIntros "H !> _".
    done.
  Qed.

  #[global] Instance post_crash_objective P : Objective (nextgen P)%I.
  Proof.
    iIntros (??) "P".
    iModIntro.
    done.
  Qed.
End Modality.

Notation "'<NG>' P" := (nextgen P)
  (at level 200, right associativity) : bi_scope.

Section IntoNextgen.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}.

  (* Arguments IntoNextgen {_} {_} {_} _%I hi%I. *)

  #[global] Instance into_nextgen_sep (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoNextgen P P' →
    IntoNextgen Q Q' →
    IntoNextgen (P ∗ Q)%I (P' ∗ Q')%I.
  Proof.
    rewrite /IntoNextgen.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply (nextgen_sep). iFrame.
  Qed.

  #[global] Instance into_nextgen_pure (P : Prop) :
    IntoNextgen (⌜ P ⌝) (⌜ P ⌝)%I.
  Proof. rewrite /IntoNextgen. iIntros "%". by iModIntro. Qed.

  Lemma into_nextgen_proper P P' Q Q':
    IntoNextgen P Q →
    (P ⊣⊢ P') →
    (Q ⊣⊢ Q') →
    IntoNextgen P' Q'.
  Proof.
    rewrite /IntoNextgen.
    iIntros (HD Hwand1 Hwand2) "HP".
    iApply nextgen_mono; last first.
    { iApply HD. iApply Hwand1. eauto. }
    intros. simpl. by rewrite Hwand2.
  Qed.

  #[global] Instance into_nextgen_big_sepM `{Countable K} :
    ∀ (A : Type) Φ (Ψ : K → A → dProp Σ) (m : gmap K A),
    (∀ (k : K) (x : A), IntoNextgen (Φ k x) (Ψ k x)) →
    IntoNextgen ([∗ map] k↦x ∈ m, Φ k x)%I ([∗ map] k↦x ∈ m, Ψ k x)%I.
  Proof.
    intros. induction m using map_ind.
    - eapply (into_nextgen_proper True%I _ True%I).
      * apply _.
      * rewrite big_sepM_empty. apply bi.True_emp.
      * intros. rewrite big_sepM_empty. apply bi.True_emp.
    - eapply (into_nextgen_proper (Φ i x ∗ [∗ map] k↦x0 ∈ m, Φ k x0) _
                                ((Ψ i x ∗ [∗ map] k↦x0 ∈ m, Ψ k x0)%I)).
      * apply _.
      * rewrite big_sepM_insert //=.
      * intros. rewrite big_sepM_insert //=.
  Qed.

  #[global] Instance into_nextgen_emp : IntoNextgen emp emp.
  Proof. rewrite /IntoNextgen. by iIntros "_ !>". Qed.

  #[global]
  Instance into_nextgen_disj P P' Q Q' :
    IntoNextgen P P' → IntoNextgen Q Q' → IntoNextgen (P ∨ Q)%I (P' ∨ Q')%I.
  Proof.
    rewrite /IntoNextgen.
    iIntros (Pi Qi) "[ H | H ]"; rewrite ?Pi ?Qi; iApply (nextgen_mono with "H"); naive_solver.
  Qed.

  #[global] Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoNextgen (Φ x) (Ψ x)) →
    IntoNextgen (∃ x, Φ x)%I ((∃ x, Ψ x)%I).
  Proof.
    rewrite /IntoNextgen.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (nextgen_mono with "HΦ"). auto.
  Qed.
End IntoNextgen.

Section nextgen_derived.
  Context `{!nvmBaseGS Σ Ω} `{AbstractState ST}.

  (* TODO: if this lemma is required, prove it in base logic. *)
  (* Lemma post_crash_persisted_loc_d ℓ t : *)
  (*   persisted_loc_d ℓ t ⊢ *)
  (*   <PC> ( *)
  (*     persisted_loc_d ℓ 0 ∗ *)
  (*     ∃ CV t', ⌜ CV !! ℓ = Some (MaxNat t') ∧ t ≤ t' ⌝ ∗ crashed_at_d CV)%I. *)
  (* Proof. *)
  (*   iIntros "P". *)
  (*   iDestruct (post_crash_persisted_d with "P") as "P". *)
  (*   iApply (post_crash_mono with "P"). *)
  (*   rewrite view_to_zero_singleton. *)
  (*   iIntros "[$ M]". *)
  (*   setoid_rewrite view_le_singleton. *)
  (*   setoid_rewrite bi.pure_exist. *)
  (*   setoid_rewrite bi.sep_exist_r. *)
  (*   done. *)
  (* Qed. *)

  (* Lemma post_crash_know_frag_history_loc ℓ t (s : ST) : *)
  (*   ⎡ know_preorder_loc ℓ (⊑@{ST}) ∗ *)
  (*     know_frag_history_loc ℓ {[ t := s ]} ∗ *)
  (*     persisted {[ ℓ := MaxNat t]} ⎤ -∗ *)
  (*   post_crash (λ nD', *)
  (*     ∃ s' t' CV, *)
  (*       ⌜ s ⊑ s' ⌝ ∗ *)
  (*       ⌜ t ≤ t' ⌝ ∗ *)
  (*       ⌜ CV !! ℓ = Some (MaxNat t') ⌝ ∗ *)
  (*       ⎡ know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)) ∗ *)
  (*         know_frag_history_loc ℓ {[ 0 := s' ]} ∗ *)
  (*         crashed_at CV ∗ *)
  (*         persisted {[ ℓ := MaxNat 0 ]} ⎤ *)
  (*   ). *)
  (* Proof. *)
  (*   iStartProof (dProp _). *)
  (*   iIntros "(order & hist & pers)". *)
  (*   iCrash. *)
  (*   iDestruct "pers" as "[pers (%CV & %t' & [%cvLook %le] & #crash)]". *)
  (*   iDestruct (or_lost_get with "[$] order") as "order"; first naive_solver. *)
  (*   iDestruct "hist" as (CV') "[crash' [hist | %cvLook']]"; *)
  (*     iDestruct (crashed_at_agree with "crash crash'") as %<-; last congruence. *)
  (*   iClear "crash'". *)
  (*   iDestruct "hist" as (? cvLook' s' impl) "fragHist". *)
  (*   simplify_eq. *)
  (*   iExists s', t', CV. *)
  (*   iFrame. *)
  (*   iFrame "#". *)
  (*   naive_solver. *)
  (* Qed. *)

End nextgen_derived.

Notation base_IntoNextgen := (nextgen_promises_model.IntoNextgen).
Notation base_nextgen := (nextgen_promises_model.nextgen).
Opaque nextgen.
