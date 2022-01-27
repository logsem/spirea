From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.Helpers Require Import ipm NamedProps.
From Perennial.program_logic Require Import recovery_weakestpre.

From self Require Import extra ipm_tactics if_non_zero.
From self.algebra Require Import ghost_map.
From self.base Require Import primitive_laws wpr_lifting.
From self.base Require post_crash_modality.
From self.high Require Import dprop resources monpred_simpl.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

(** We define the post crash modality. *)

Definition or_lost_post_crash `{nvmBaseFixedG Σ, nD : nvmBaseDeltaG Σ}
           ℓ (P : nat → iProp Σ) :=
  (∃ (CV : view),
    crashed_at CV ∗
    ((∃ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗ P t) ∨ ⌜CV !! ℓ = None⌝))%I.

Instance or_lost_post_crash_proper `{nvmBaseFixedG Σ, nD : nvmBaseDeltaG Σ} ℓ :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (or_lost_post_crash ℓ).
Proof. solve_proper. Qed.

Definition or_lost_post_crash_no_t `{nvmBaseFixedG Σ, nD : nvmBaseDeltaG Σ}
           ℓ (P : iProp Σ) :=
  or_lost_post_crash ℓ (λ _, P).

Section or_lost_post_crash.
  Context `{nvmBaseFixedG Σ, nD: nvmBaseDeltaG Σ}.

  Lemma or_lost_post_crash_lookup (CV : view) ℓ t P :
    CV !! ℓ = Some (MaxNat t) →
    crashed_at CV -∗
    or_lost_post_crash ℓ P -∗
    P t.
  Proof.
    iIntros (look) "crash".
    iIntros "(% & crash' & [l|%])";
      iDestruct (crashed_at_agree with "crash crash'") as %<-;
      last congruence.
    iDestruct "l" as (t' eq) "P".
    by simplify_eq.
  Qed.

  (* Lemma or_lost_post_crash_no_t_lookup (CV : view) ℓ t P : *)
  (*   CV !! ℓ = Some (MaxNat t) → *)
  (*   crashed_at CV -∗ *)
  (*   or_lost_post_crash_no_t ℓ P -∗ *)
  (*   P. *)
  (* Proof. apply or_lost_post_crash_lookup. Qed. *)

End or_lost_post_crash.

(* Lemma or_lost_post_crash_no_t_alt `{nvmFixedG Σ, nD : nvmDeltaG Σ} *)
(*            ℓ (P : iProp Σ) : *)
(*   (∃ (CV : view), *)
(*     crashed_at CV ∗ *)
(*     ((⌜ℓ ∈ dom (gset _) CV⌝ ∗ P) ∨ ⌜CV !! ℓ = None⌝)) -∗ *)
(*   or_lost_post_crash_no_t ℓ P. *)
(* Proof. *)
(* Admitted.   *)

Definition know_history_post_crash `{nvmFixedG Σ}
            (hG : nvmDeltaG Σ) ℓ q (hist : gmap time positive) : iProp Σ :=
  or_lost_post_crash ℓ (λ t,
    ∃ s, ⌜hist !! t = Some s⌝ ∗
         know_full_encoded_history_loc ℓ q ({[ 0 := s ]}) ∗
         know_frag_encoded_history_loc ℓ ({[ 0 := s ]}) ∗
         (* Remove this last thing if [persisted] is added to [crashed_at]. *)
         persisted_loc ℓ 0)%I.

Lemma know_history_post_crash_sep `{nvmBaseFixedG Σ, nvmBaseDeltaG Σ} ℓ P Q :
  or_lost_post_crash ℓ (λ t, P t ∗ Q t) ⊣⊢
  or_lost_post_crash ℓ (λ t, P t) ∗ or_lost_post_crash ℓ (λ t, Q t).
Proof.
  (* intros F q p. *)
  iSplit.
  -
    (* iDestruct 1 as (?) "(CV & disj)". *)
    iDestruct 1 as (?) "(#CV & [(%t & %look & P & Q)|%look])".
    * iSplitL "P"; iExists _; naive_solver.
    * iSplitL; iExists _; naive_solver.
  - iIntros "[(%CV & cr1 & [(%t1 & %look1 & P)|%look1])
              (%CV' & cr2 & [(%t2 & %look2 & Q)|%look2])]";
      iDestruct (crashed_at_agree with "cr1 cr2") as %eq;
      simplify_eq.
    * iExists _. iFrame. iLeft. iExists _. iFrame "∗#%".
    * iExists _. iFrame. iRight. done.
Qed.

Instance or_lost_post_crash_fractional `{nvmBaseFixedG Σ, nvmBaseDeltaG Σ} ℓ P :
  (∀ t, Fractional (P t)) →
  Fractional (λ q, or_lost_post_crash ℓ (λ t, P t q)).
Proof.
  intros F q p.
  rewrite -know_history_post_crash_sep.
  setoid_rewrite fractional.
  done.
Qed.

Instance know_history_post_crash_fractional `{nvmFixedG Σ} hG ℓ hist :
  Fractional (λ q, know_history_post_crash hG ℓ q hist).
Proof.
  apply or_lost_post_crash_fractional.
  iIntros (t p q).
  iSplit.
  - iDestruct 1 as (??) "([L R] & #? & #?)".
    iSplitL "L"; naive_solver.
  - iDestruct 1 as "[(% & % & L & #? & #?) (% & % & R & #? & #?)]".
    simplify_eq. iCombine "L R" as "F". naive_solver.
Qed.

Definition post_crash_history_impl `{hG : nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST) ℓ (t : nat) (s : ST),
    know_frag_history_loc (nD := nD) ℓ {[ t := s ]} -∗
    (or_lost_post_crash ℓ (λ t', ∃ s',
      ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
      know_frag_history_loc (nD := nD') ℓ {[ 0 := s' ]})).

Definition post_crash_preorder_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST) ℓ,
    know_preorder_loc (nD := nD) ℓ (abs_state_relation (ST := ST)) -∗
    (or_lost_post_crash_no_t ℓ
      (know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)))).

Definition post_crash_pred_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) ℓ (ϕ : ST → val → nvmDeltaG Σ → dProp Σ),
    know_pred (hGD := nD) ℓ ϕ -∗
    or_lost_post_crash_no_t ℓ (know_pred (hGD := nD') ℓ ϕ).

Definition post_crash_shared_loc_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ℓ, is_shared_loc (hGD := nD) ℓ -∗
    or_lost_post_crash_no_t ℓ (is_shared_loc (hGD := nD') ℓ).

Definition post_crash_exclusive_loc_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ℓ, is_exclusive_loc (hGD := nD) ℓ -∗
    or_lost_post_crash_no_t ℓ (is_exclusive_loc (hGD := nD') ℓ).

Definition post_crash_na_view_map `{nvmFixedG Σ}
           (na_views : gmap loc view) (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  (∀ ℓ q SV, know_na_view (nD := nD) ℓ q SV -∗ ⌜ na_views !! ℓ = Some SV ⌝) ∗
  [∗ map] ℓ ↦ SV ∈ na_views,
    soft_disj
      (λ q, know_na_view (nD := nD) ℓ q SV)
      (λ q, or_lost_post_crash_no_t ℓ (know_na_view (nD := nD') ℓ q ∅)).

Instance know_na_view_post_crash_fractional `{nvmFixedG Σ, nvmDeltaG Σ} ℓ :
  Fractional (λ q0 : Qp, or_lost_post_crash_no_t ℓ (know_na_view ℓ q0 ∅)).
Proof. apply or_lost_post_crash_fractional. apply _. Qed.

Definition get_bumpers_name {Σ} (hD : nvmDeltaG Σ) := bumpers_name.

Definition post_crash_bumper_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
      ℓ (bumper : ST → ST),
    know_bumper (nD := nD) ℓ bumper -∗
    or_lost_post_crash_no_t ℓ (know_bumper (nD := nD') ℓ bumper).

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_map `{nvmFixedG Σ}
           (hh : gmap loc (gmap time positive)) (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ q hist, (know_full_encoded_history_loc (nD := nD) ℓ q hist) -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (* The map used to perform the the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh,
    soft_disj
      (λ q, know_full_encoded_history_loc (nD := nD) ℓ q hist)
      (λ q, know_history_post_crash nD' ℓ q hist).

Definition post_crash_resource `{nvmFixedG Σ}
           (h : gmap loc (gmap time positive)) (na_views : gmap loc view) (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  "#post_crash_history_impl" ∷ post_crash_history_impl nD nD' ∗
  "#post_crash_preorder_impl" ∷ post_crash_preorder_impl nD nD' ∗
  "#post_crash_pred_impl" ∷ post_crash_pred_impl nD nD' ∗
  "#post_crash_shared_loc_impl" ∷ post_crash_shared_loc_impl nD nD' ∗
  "#post_crash_exclusive_loc_impl" ∷ post_crash_exclusive_loc_impl nD nD' ∗
  "#post_crash_bumper_impl" ∷ post_crash_bumper_impl nD nD' ∗
  (* "#post_crash_exclusive_loc_impl" ∷ post_crash_exclusive_loc_impl nD nD' ∗ *)
  "post_crash_na_view_map" ∷ post_crash_na_view_map na_views nD nD' ∗
  "post_crash_map" ∷ post_crash_map h nD nD'.

Program Definition post_crash `{nvmFixedG Σ, nD : nvmDeltaG Σ}
        (P : nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ _TV,
    ∀ (hhGD' : nvmHighDeltaG) hh na_views,
      base_post_crash (λ nD',
        let nD' := NvmDeltaG _ nD' hhGD'
        in (post_crash_resource hh na_views nD nD') -∗
          P nD' (∅, ∅, ∅) ∗
          (post_crash_resource hh na_views nD nD')))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Notation "'<PC>' g , P" := (post_crash (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

(** Tiny shortcut for introducing the assumption for a [post_crash]. *)
Ltac iIntrosPostCrash := iIntros (hG' hh na_views).

Section post_crash_prop.
  Context `{nvmFixedG Σ, nD: nvmDeltaG Σ}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.

  Global Instance post_crash_objective P : Objective (post_crash P).
  Proof. done. Qed.

  (* Lemma post_crash_intro Q: *)
  (*   (⊢ Q) → *)
  (*   (⊢ post_crash (λ _, Q)). *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (TV'). *)
  (*   iIntros (Hmono). *)
  (*   iIntrosPostCrash. *)
  (*   iFrame "∗". *)
  (*   iApply Hmono. *)
  (* Qed. *)

  (** ** Structural rules *)

  Lemma post_crash_mono P Q :
    (∀ hG, P hG -∗ Q hG) → post_crash P -∗ post_crash Q.
  Proof.
    iStartProof (iProp _). iIntros (Hmono TV') "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG') as "P".
    iApply (post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    (* rewrite /post_crash_impl. *)
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    iDestruct (Hmono with "P") as "H".
    done.
  Qed.

  Lemma post_crash_sep P Q :
    post_crash P ∗ post_crash Q -∗ <PC> hG, P hG ∗ Q hG.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG' hh na_views) as "HP".
    iDestruct ("HQ" $! hG' hh na_views) as "HQ".
    post_crash_modality.iCrash.
    iIntros "M".
    iDestruct ("HP" with "M") as "[$ M]".
    iDestruct ("HQ" with "M") as "[$ $]".
  Qed.

  Lemma post_crash_pure (P : Prop) : P → ⊢ <PC> _, ⌜P⌝.
  Proof.
    iIntros (HP).
    iStartProof (iProp _). iIntros (TV').
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "$".
    iApply monPred_at_pure.
    iFrame "%".
  Qed.

  Lemma post_crash_embed_nodep P :
    ⎡ P ⎤ -∗ <PC> _, ⎡ P ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "P".
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "$".
    iApply monPred_at_embed.
    iFrame.
  Qed.

  Lemma post_crash_named P name :
    named name (post_crash (λ hG, P hG)) -∗
    post_crash (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

End post_crash_prop.

Section post_crash_interact.
  Context `{nvmFixedG Σ, nD: nvmDeltaG Σ}.

  Context `{AbstractState ST}.

  (** ** The rules for the "special" assertions

  How the post crash modality interacts with the assertions in the logic. *)

  (* The predicate [P] holds for [ℓ] or [ℓ] has been lost. *)
  Definition or_lost {nD' : nvmDeltaG Σ} ℓ (P : dProp Σ) : dProp Σ :=
    ∃ CV, ⎡crashed_at CV⎤ ∗ (P ∨ ⌜CV !! ℓ = None⌝).

  Definition or_lost_with_t {nD' : nvmDeltaG Σ} ℓ (P : time → dProp Σ) : dProp Σ :=
    ∃ CV, ⎡crashed_at CV⎤ ∗ ((∃ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗ P t)
                          ∨ ⌜CV !! ℓ = None⌝).

  Lemma or_lost_sep {nD' : nvmDeltaG Σ} ℓ (P Q : dProp Σ) :
    or_lost ℓ P ∗ or_lost ℓ Q ⊣⊢ or_lost ℓ (P ∗ Q)%I.
  Proof.
    iSplit.
    - iIntros "[(%CV & crash & MP) (%CV' & crash' & MQ)]".
      iDestruct (crashed_at_agree with "crash crash'") as %<-.
      iExists CV. iFrame.
      iDestruct "MP" as "[P|%]"; iDestruct "MQ" as "[Q|%]"; try (by iRight).
      iLeft. iFrame.
    - iIntros "(%CV & #crash & [[P Q]|%])".
      * iSplitL "P"; iExists CV; iFrame "∗#".
      * iSplitL; iExists CV; iFrame "#%".
  Qed.

  Lemma or_lost_mono {nD' : nvmDeltaG Σ} ℓ (P Q : dProp Σ) :
    (P -∗ Q) -∗ or_lost ℓ P -∗ or_lost ℓ Q.
  Proof.
    rewrite /or_lost.
    iIntros "pToQ (%CV & crashed & disj)".
    iExists CV. iFrame "crashed". iDestruct "disj" as "[P | %lost]".
    - iLeft. iApply "pToQ". iApply "P".
    - iRight. iFrame (lost).
  Qed.

  Lemma or_lost_embed {nD' : nvmDeltaG Σ} ℓ P TV :
    or_lost_post_crash_no_t ℓ P -∗ or_lost ℓ ⎡ P ⎤ TV.
  Proof.
    iDestruct 1 as (CV) "[crash disj]". iExists _. iFrame "crash".
    iDestruct "disj" as "[(% & _ & ?) | hop]"; try naive_solver.
  Qed.

  Lemma or_lost_get `{nvmDeltaG Σ} CV ℓ P :
    is_Some (CV !! ℓ) → ⎡ crashed_at CV ⎤ -∗ or_lost ℓ P -∗ P.
  Proof.
    iIntros ([[t] look]) "crash (%CV' & crash' & [$ | %look'])".
    iDestruct (crashed_at_agree with "crash crash'") as %<-.
    congruence.
  Qed.

  Lemma or_lost_with_t_get `{nvmDeltaG Σ} CV ℓ t P :
    CV !! ℓ = Some (MaxNat t) → ⎡ crashed_at CV ⎤ -∗ or_lost_with_t ℓ P -∗ P t.
  Proof.
    rewrite /or_lost_with_t.
    iIntros (look) "crash (%CV' & crash' & [(%t' & %look' & P)|%look'])";
    iDestruct (crashed_at_agree with "crash crash'") as %<-.
    - simplify_eq. iFrame "P".
    - congruence.
  Qed.

  Lemma post_crash_know_full_history_loc ℓ q (abs_hist : gmap time ST) :
    ⎡ know_full_history_loc ℓ q abs_hist ⎤ -∗
    <PC> _, or_lost_with_t ℓ (λ t, ∃ (s : ST),
        ⌜abs_hist !! t = Some s⌝ ∗
        ⎡ know_full_history_loc ℓ q {[ 0 := s ]} ⎤ ∗
        ⎡ know_frag_history_loc ℓ {[ 0 := s ]} ⎤ ∗
        (* Remove this last thing if [persisted] is added to [crashed_at]. *)
        ⎡ persisted_loc ℓ 0 ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    iFrame "post_crash_preorder_impl".
    iDestruct "post_crash_map" as "[in M]".
    rewrite /know_full_history_loc own_full_equiv.
    iAssert (⌜hh !! _ = Some _⌝)%I as %HI.
    { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[H reIns]"; first done.
    iDestruct (soft_disj_exchange_l with "[] H [$]") as "[H HP]".
    { iIntros "!>" (?) "H".
      setoid_rewrite <- dfrac_valid_own.
      iApply (ghost_map_elem_valid with "H"). }
    iFrame "#∗".
    iDestruct ("reIns" with "H") as "$".
    rewrite /know_history_post_crash.
    rewrite /know_history_post_crash /or_lost_with_t.
    iDestruct "HP" as (CV) "[crashedAt [H|H]]"; iExists (CV);
      iFrame "crashedAt"; [iLeft|iRight; done].
    iDestruct "H" as (t) "[%cvLook (%estate & %look & hist & frag)]".
    apply lookup_fmap_Some in look as [st [eq ?]].
    iExists t. iFrame (cvLook). iExists st.
    iPureGoal. { assumption. }
    rewrite /know_full_history_loc own_full_equiv.
    rewrite -eq. rewrite map_fmap_singleton.
    rewrite -map_fmap_singleton.
    rewrite /know_frag_encoded_history_loc own_frag_equiv.
    iFrame.
  Qed.

  Lemma post_crash_preorder ℓ :
    ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ -∗
    post_crash (λ hG', or_lost ℓ ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST) ) ⎤)%I.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_preorder_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.

  Lemma post_crash_frag_history ℓ t (s : ST) :
    ⎡ know_frag_history_loc ℓ {[ t := s ]} ⎤ -∗
    post_crash (λ hG',
                (or_lost_with_t ℓ (λ t', ∃ s',
                  ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
                  ⎡know_frag_history_loc ℓ {[ 0 := s' ]}⎤))).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource.
    iFrameNamed.
    iDestruct ("post_crash_history_impl" with "HP") as (CV) "[crash HI]".
    iExists CV. iFrame.
  Qed.

  Lemma post_crash_know_pred `{Countable ST'} ℓ (ϕ : ST' → val → nvmDeltaG Σ → dProp Σ) :
    ⎡ know_pred ℓ ϕ ⎤ -∗ <PC> _, or_lost ℓ (⎡ know_pred ℓ ϕ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_pred_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.

  Lemma post_crash_shared_loc ℓ :
    ⎡ is_shared_loc ℓ ⎤ -∗ <PC> _, or_lost ℓ (⎡ is_shared_loc ℓ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_shared_loc_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.

  Lemma post_crash_exclusive_loc ℓ :
    ⎡ is_exclusive_loc ℓ ⎤ -∗ <PC> _, or_lost ℓ (⎡ is_exclusive_loc ℓ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_exclusive_loc_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.

  Lemma post_crash_know_na_view ℓ q SV :
    ⎡ know_na_view ℓ q SV ⎤ -∗ <PC> _, or_lost ℓ (⎡ know_na_view ℓ q ∅ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    iDestruct "post_crash_na_view_map" as "[in M]".
    iAssert (⌜ na_views !! _ = Some _ ⌝)%I as %HI. { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[H reIns]"; first done.
    iDestruct (soft_disj_exchange_l with "[] H [$]") as "[H HP]".
    { iIntros "!>" (?) "H".
      setoid_rewrite <- dfrac_valid_own.
      iApply (ghost_map_elem_valid with "H"). }
    iFrame "#∗".
    iDestruct ("reIns" with "H") as "$".
    rewrite -or_lost_embed.
    done.
  Qed.

  Lemma post_crash_know_bumper `{AbstractState ST} ℓ (bumper : ST → ST) :
    ⎡ know_bumper ℓ bumper ⎤ -∗ <PC> _, or_lost ℓ (⎡ know_bumper ℓ bumper ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_bumper_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.

  (*
  Lemma post_crash_is_exclusive_loc ℓ :
    ⎡ is_exclusive_loc ℓ ⎤ -∗ <PC> _, or_lost ℓ (⎡ is_exclusive_loc ℓ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_exclusive_loc_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.
  *)

End post_crash_interact.

Class IntoCrash {Σ} `{nvmFixedG Σ, nvmDeltaG Σ}
      (P : dProp Σ) (Q : nvmDeltaG Σ → dProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ nD', Q nD').

Arguments IntoCrash {_} {_} {_} _%I _%I.

Section IntoCrash.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  (* Arguments IntoCrash {_} {_} {_} _%I hi%I. *)

  Global Instance pure_into_crash (P : Prop) :
    IntoCrash (⌜ P ⌝) (λ _, ⌜ P ⌝)%I.
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance lifted_embed_nodep_into_crash (P : iProp Σ) :
    IntoCrash (⎡ P ⎤) (λ _, ⎡ P ⎤)%I | 1000.
  Proof. apply post_crash_embed_nodep. Qed.

  Global Instance lifted_embed_into_crash (P : iProp Σ) Q :
    base.post_crash_modality.IntoCrash P Q →
    IntoCrash (⎡ P ⎤) (λ _, ⎡ Q _ ⎤)%I.
  Proof.
    rewrite /IntoCrash.
    iStartProof (iProp _).
    iIntros (??) "?".
    iIntrosPostCrash.
    post_crash_modality.iCrash.
    iIntros "$". done.
  Qed.

  Global Instance sep_into_crash (P Q : dProp Σ) (P' Q' : _ → dProp Σ) :
    IntoCrash P P' → IntoCrash Q Q' → IntoCrash (P ∗ Q)%I (λ hD, P' hD ∗ Q' hD)%I.
  Proof.
    rewrite /IntoCrash.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply (post_crash_sep). iFrame.
  Qed.

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) →
    IntoCrash (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (post_crash_mono with "HΦ"). auto.
  Qed.

  Tactic Notation "lift_into_crash" uconstr(lem) := 
    rewrite /IntoCrash; iIntros "P"; by iApply lem.

  (* Global Instance embed_into_crash P : *)
  (*   IntoCrash (⎡ P ⎤%I) (λ _, ⎡ P ⎤%I). *)
  (* Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_embed_nodep. Qed. *)

  Global Instance into_crash_know_full_history_loc `{AbstractState ST}
         ℓ q abs_hist :
    IntoCrash
      (⎡ know_full_history_loc ℓ q abs_hist ⎤)
      (λ hG', or_lost_with_t ℓ (λ t, ∃ (s : ST),
        ⌜abs_hist !! t = Some s⌝ ∗
        ⎡ know_full_history_loc ℓ q {[ 0 := s ]} ⎤ ∗
        ⎡ know_frag_history_loc ℓ {[ 0 := s ]} ⎤ ∗
        ⎡ persisted_loc ℓ 0 ⎤ ))%I.
  Proof. lift_into_crash post_crash_know_full_history_loc. Qed.

  Global Instance into_crash_preorder `{AbstractState ST} ℓ :
    IntoCrash
    (⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤)
    (λ hG', or_lost ℓ (⎡know_preorder_loc ℓ (abs_state_relation (ST := ST))⎤))%I.
  Proof. lift_into_crash post_crash_preorder. Qed.

  Global Instance frag_history_into_crash `{AbstractState ST} ℓ t s :
    IntoCrash
      (⎡ know_frag_history_loc ℓ {[ t := s ]} ⎤)
      (λ hG', or_lost_with_t ℓ (λ t', ∃ (s' : ST),
              ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
              ⎡know_frag_history_loc ℓ {[ 0 := s' ]}⎤
                             ))%I.
  Proof. lift_into_crash post_crash_frag_history. Qed.

  Global Instance know_pred_into_crash `{AbstractState ST}
         ℓ (ϕ : ST → val → _ → dProp Σ) :
    IntoCrash
      (⎡ know_pred ℓ ϕ ⎤)%I
      (λ hG', or_lost ℓ (⎡ know_pred ℓ ϕ ⎤))%I.
  Proof. lift_into_crash post_crash_know_pred. Qed.

  Global Instance shared_loc_into_crash ℓ :
    IntoCrash
      (⎡ is_shared_loc ℓ ⎤)%I
      (λ hG', or_lost ℓ (⎡ is_shared_loc ℓ ⎤))%I.
  Proof. lift_into_crash post_crash_shared_loc. Qed.

  Global Instance exclusive_loc_into_crash ℓ :
    IntoCrash
      (⎡ is_exclusive_loc ℓ ⎤)%I
      (λ hG', or_lost ℓ (⎡ is_exclusive_loc ℓ ⎤))%I.
  Proof. lift_into_crash post_crash_exclusive_loc. Qed.

  Global Instance exclusive_know_na_view_crash ℓ q SV :
    IntoCrash
      (⎡ know_na_view ℓ q SV ⎤)%I
      (λ hG', or_lost ℓ (⎡ know_na_view ℓ q ∅ ⎤))%I.
  Proof. lift_into_crash post_crash_know_na_view. Qed.

  Global Instance know_bumper_into_crash `{AbstractState ST} ℓ (bumper : ST → ST) :
    IntoCrash
      (⎡ know_bumper ℓ bumper ⎤)%I
      (λ hG', or_lost ℓ (⎡ know_bumper ℓ bumper ⎤))%I.
  Proof. lift_into_crash post_crash_know_bumper. Qed.

  (*
  Global Instance exclusive_loc_into_crash ℓ :
    IntoCrash
      (⎡ is_exclusive_loc ℓ ⎤)
      (λ _, or_lost ℓ (⎡ is_exclusive_loc ℓ ⎤)).
  Proof.
    rewrite /IntoCrash. iIntros "P". by iApply post_crash_is_exclusive_loc.
  Qed.
  *)

End IntoCrash.

Lemma modus_ponens {Σ} (P Q : dProp Σ)  : P -∗ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A =>
      first [ iEval (rewrite (@into_crash _ _ _ A) ) in id || iClear id ] ; crash_env Γ'
  end.

Ltac crash_ctx :=
  match goal with
  | [ |- environments.envs_entails ?Γ _] =>
    let spatial := pm_eval (environments.env_spatial Γ) in
    let intuit := pm_eval (environments.env_intuitionistic Γ) in
    crash_env spatial; crash_env intuit
  end.

Ltac iCrash :=
  crash_ctx;
  iApply (modus_ponens with "[-]"); [ iNamedAccu | ];
  rewrite ?post_crash_named ?post_crash_sep; iApply post_crash_mono;
  intros; simpl;
  let H := iFresh in iIntros H; iNamed H.

Section post_crash_derived.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Context `{AbstractState ST}.

  Lemma post_crash_know_frag_history_loc ℓ t (s : ST) :
    ⎡ know_preorder_loc ℓ (⊑@{ST}) ∗
      know_frag_history_loc ℓ {[ t := s ]} ∗
      persisted {[ ℓ := MaxNat t]} ⎤ -∗
    post_crash (λ nD',
      ∃ s' t' CV,
        ⌜ s ⊑ s' ⌝ ∗
        ⌜ t ≤ t' ⌝ ∗
        ⌜ CV !! ℓ = Some (MaxNat t') ⌝ ∗
        ⎡ know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)) ∗
          know_frag_history_loc ℓ {[ 0 := s' ]} ∗
          crashed_at CV ∗
          persisted {[ ℓ := MaxNat 0 ]} ⎤
    ).
  Proof.
    iStartProof (dProp _).
    iIntros "(order & hist & pers)".
    iCrash.
    iDestruct "pers" as "[pers (%CV & %t' & [%cvLook %le] & #crash)]".
    iDestruct (or_lost_get with "[$] order") as "order"; first naive_solver.
    iDestruct "hist" as (CV') "[crash' [hist | %cvLook']]";
      iDestruct (crashed_at_agree with "crash crash'") as %<-; last congruence.
    iClear "crash'".
    iDestruct "hist" as (? cvLook' s' impl) "fragHist".
    simplify_eq.
    iExists s', t', CV.
    iFrame.
    iFrame "#".
    naive_solver.
  Qed.

  (* NOTE: This rule is wrong as it does not take the bumper into account. *)
  Lemma post_crash_know_persist_lb (ℓ : loc) (s : ST) :
    know_persist_lb ℓ s -∗
    post_crash (λ hG, ∃ s', ⌜s ⊑ s'⌝ ∗
      know_persist_lb ℓ s' ∗
      know_flush_lb ℓ s' ∗
      know_store_lb ℓ s').
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iNamed 1.
    iDestruct (post_crash_know_frag_history_loc with "[$]") as "HI".
    iApply (post_crash_mono with "HI").
    iStartProof (iProp _).
    iIntros (hG' TV').
    iDestruct 1 as
        (s'' t' CV) "(%incl' & %le & %cvLook & #ord & #hist & #crash & #pers)".
    assert (s ⊑ s'') by (etrans; done).
    iExists s''.
    iSplit; first done.
    (* We show the global persist lower bound. *)
    iSplit.
    { iExists 0. iFrame "#%". iPureIntro. lia. }
    (* We show the local persist lower bound. *)
    iSplit.
    - iExists 0. iFrame "#%". iPureIntro. naive_solver.
    - iExists 0. iFrame "#%". iPureIntro. lia. 
  Qed.

  Lemma post_crash_know_store_lb (ℓ : loc) (s : ST) :
    know_store_lb ℓ s -∗
    post_crash (λ hG, or_lost ℓ (∃ (s' : ST),
      (* know_persist_lb ℓ s' ∗ *)
      (* know_flush_lb ℓ s' ∗ *)
      know_store_lb ℓ s')).
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iNamed 1.
    iDestruct "order" as "-#order".
    iDestruct "knowFragHist" as "-#knowFragHist".
    iDestruct (post_crash_preorder with "order") as "order".
    iDestruct (post_crash_frag_history with "knowFragHist") as "knowFragHist".
    iDestruct (post_crash_sep with "[$order $knowFragHist]") as "H".
    iApply (post_crash_mono with "H").
    iStartProof (iProp _).
    iIntros (hD' TV').
    iIntros "[(%CV & crashed & disj) (%CV' & crashed' & disj2)]".
    iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
    iExists (CV). iFrame "crashed".
    iDestruct "disj" as "[order|%R]"; iDestruct "disj2" as "[L2|%R2]";
      try (iRight; done).
    iDestruct "L2" as (????? look) "hist".
    iLeft.
    iExists _, 0.
    iFrame "order".
    iSplitPure; first lia.
    rewrite /know_frag_history_loc.
    rewrite /own_frag_history_loc.
    iExists _. iSplitPure. { apply look. }
    iFrame "hist".
  Qed.

  (* NOTE: This rule should be changed once the "bump-back function" is
  introduced. *)
  Lemma post_crash_mapsto_persisted_ex `{AbstractState ST} ℓ q (ss : list ST) :
    ℓ ↦_{true}^{q} ss -∗ <PC> hG', ∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{true}^{q} [s] ∗ recovered_at ℓ s.
  Proof.
    rewrite /mapsto_na. iNamed 1.
    iDestruct "isExclusiveLoc" as "-#isExclusiveLoc".
    iDestruct "order" as "-#order".
    iCrash.
    iDestruct "pers" as "(persisted & (%CV & % & [% %] & #crash))".
    iDestruct (or_lost_get with "crash isExclusiveLoc") as "isExclusiveLoc"; first done.
    iDestruct (or_lost_get with "crash order") as "order"; first done.
    iDestruct (or_lost_get with "crash knowSV") as "knowSV"; first done.
    iDestruct (or_lost_with_t_get with "crash hist") as (s) "(% & ? & ? & _)";
      first done.
    iExists s.
    iPureGoal. { by eapply map_slice_no_later_elem_of. }
    iSplit.
    - iExists 0, 0, ∅, _, (Msg _ ∅ ∅ ∅). iFrame.
      iPureGoal. { apply increasing_list_singleton. }
      iPureGoal. { by rewrite lookup_singleton. }
      iPureGoal. { apply map_no_later_singleton. }
      iPureGoal. { simpl. by rewrite lookup_singleton. }
      iSplit. { admit. } (* FIXME: We'd need to add some post crash rule for this. *)
      iStopProof.
      iStartProof (iProp _). iIntros (?) "_ !%".
      split_and!; try done.
      destruct i as [[??]?]; repeat split; apply view_empty_least.
    - iExists _. iFrame "∗#". iPureIntro. apply elem_of_dom. naive_solver.
  Admitted.

  Lemma post_crash_mapsto_na `{AbstractState ST} ℓ p q (ss : list ST) :
    ℓ ↦_{p}^{q} ss -∗
    post_crash (λ hG', or_lost ℓ (∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{true}^{q} [s] ∗ recovered_at ℓ s)).
  Proof.
    destruct p.
    { iIntros "H".
      iDestruct (post_crash_mapsto_persisted_ex with "H") as "H".
      iCrash. iExists _. iFrame. admit. }
    rewrite /mapsto_na.
    iNamed 1.
    iDestruct "pers" as %tPeq.
    iDestruct "order" as "-#order".
    iDestruct "isExclusiveLoc" as "-#isExclusiveLoc".
    iCrash.
    iDestruct "hist" as (CV) "[#crash [left|%look]]".
    - iDestruct "left" as (t look) "(%s & %absHistLook & full & frag & pers)".
      iDestruct (or_lost_get with "crash isExclusiveLoc") as "isExclusiveLoc"; first done.
      iDestruct (or_lost_get with "crash order") as "order"; first done.
      iDestruct (or_lost_get with "crash knowSV") as "knowSV"; first done.
      iExists CV. iFrame "crash". iLeft.
      iExists s.
      iSplit.
      { iPureIntro. apply: map_slice_lookup_between; try done.
        split; first lia.
        eapply map_no_later_Some; naive_solver. }
      rewrite /recovered_at.
      iSplit.
      + iExists 0, 0, ∅, _, (Msg _ ∅ ∅ ∅). iFrame.
        iPureGoal. { apply increasing_list_singleton. }
        iPureGoal. { by rewrite lookup_singleton. }
        iPureGoal. { apply map_no_later_singleton. }
        iPureGoal. { by rewrite lookup_singleton. }
        iSplit. { admit. } (* FIXME: We'd need to add some post crash rule for this. *)
        iStopProof.
        iStartProof (iProp _). iIntros (?) "_".
        simpl. iPureIntro. split_and!; try done.
        destruct i as [[??]?]; repeat split; apply view_empty_least.
      + iExists _. iFrame "∗#". iPureIntro. rewrite elem_of_dom. naive_solver.
    - iExists CV. iFrame "crash".
      iRight. iPureIntro. done.
  Admitted.

  Global Instance mapsto_na_into_crash `{AbstractState ST} ℓ p q (ss : list ST) :
    IntoCrash
      (ℓ ↦_{p}^{q} ss)%I
      (λ hG', or_lost ℓ (∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{true}^{q} [s] ∗ recovered_at ℓ s))%I.
  Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_mapsto_na. Qed.

  Global Instance mapsto_na_persisted_into_crash `{AbstractState ST} ℓ (ss : list ST) :
    IntoCrash (ℓ ↦_{true} ss)%I (λ hG', ∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{true} [s] ∗ recovered_at ℓ s)%I.
  Proof.
    rewrite /IntoCrash. iIntros "P". by iApply post_crash_mapsto_persisted_ex.
  Qed.

  Lemma recovered_at_or_lost `{AbstractState ST} ℓ P (s : ST) :
    recovered_at ℓ s -∗ or_lost ℓ P -∗ P.
  Proof.
    iNamed 1.
    iIntros "(%CV' & crash & [$ | %look])".
    iDestruct (crashed_at_agree with "crashed crash") as %->.
    apply elem_of_dom in inCV.
    destruct inCV as [??].
    congruence.
  Qed.

End post_crash_derived.

(* Definition post_crash_flush `{nvmFixedG Σ, nvmDeltaG Σ} *)
(*         (P : nvmDeltaG Σ → dProp Σ) : dProp Σ := *)
(*     <PC> (λ (nD' : nvmDeltaG Σ), P nD'). *)
(* Definition post_crash_flush `{nvmFixedG Σ, nvmDeltaG Σ} *)
(*         (P : nvmDeltaG Σ → dProp Σ) : dProp Σ := *)
(*   (∀ TV, monPred_in TV -∗ *)
(*     <PC> (nD' : nvmDeltaG Σ), *)
(*       ∀ (CV : view), *)
(*         ⌜ flush_view TV ⊑ CV ⌝ -∗ *)
(*         ⎡ crashed_at CV ⎤ -∗ *)
(*         P nD')%I. *)
(* Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed. *)

Program Definition post_crash_flush `{nvmFixedG Σ, nvmDeltaG Σ}
        (P : nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (<PC> (nD' : nvmDeltaG Σ),
      ∀ (CV : view),
        ⌜ flush_view TV ⊑ CV ⌝ ∗
        (* ⎡ persisted (flush_view TV) ⎤ -∗ *)
        ⎡ persisted (view_to_zero (flush_view TV)) ⎤ ∗
        ⎡ crashed_at CV ⎤ -∗
        P nD') (∅, ∅, ∅))%I _.
Next Obligation. intros ???????. apply post_crash_mono. solve_proper. Qed.

(*
Program Definition post_crash_flush `{hG : !nvmFixedG Σ, nvmDeltaG Σ}
        (P : nvmFixedG Σ, nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (post_crash (λ hG', ∃ CV, ⌜flush_view TV ⊑ CV⌝ ∗ ⎡crashed_at CV⎤ -∗ P hG')) TV
  )%I _.
Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed.
*)

Notation "'<PCF>' g , P" :=
  (post_crash_flush (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

Section post_crash_persisted.
  Context `{hG: !nvmFixedG Σ, nvmDeltaG Σ}.

  Lemma post_crash_flush_post_crash P :
    post_crash P -∗
    post_crash_flush P.
  Proof.
    iStartProof (iProp _).
    iIntros (TV) "P".
    rewrite /post_crash_flush.
    rewrite /post_crash.
    simpl.
    iIntros (nD CV na_views).
    iSpecialize ("P" $! nD CV na_views).
    iApply (base.post_crash_modality.post_crash_mono with "P").
    iIntros (?) "A R".
    iDestruct ("A" with "R") as "[P $]".
    monPred_simpl.
    iIntros (???) "_".
    iApply monPred_mono; done.
  Qed.

  Lemma post_crash_flush_named `{nvmFixedG Σ, nvmDeltaG Σ} P name :
    named name (post_crash_flush (λ hG, P hG)) -∗
    post_crash_flush (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

  Lemma post_crash_flush_sep `{nvmFixedG Σ, nvmDeltaG Σ} P Q :
    post_crash_flush P ∗ post_crash_flush Q -∗ <PCF> hG, P hG ∗ Q hG.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG' hh na_views) as "HP".
    iDestruct ("HQ" $! hG' hh na_views) as "HQ".
    base.post_crash_modality.iCrash.
    iIntros "M".
    iDestruct ("HP" with "M") as "[H M]".
    iDestruct ("HQ" with "M") as "[H1 $]".
    iIntros (CV).
    iSpecialize ("H" $! CV).
    iSpecialize ("H1" $! CV).
    monPred_simpl.
    iIntros (TV'' le) "(%flushLe & #pers & #crashedAt)".
    iSpecialize ("H" $! TV'' le with "[$pers $crashedAt //]").
    iSpecialize ("H1" $! TV'' le with "[$pers $crashedAt //]").
    iFrame.
  Qed.

  Lemma post_crash_flush_mono P Q :
    (∀ hG, P hG -∗ Q hG) → post_crash_flush P -∗ post_crash_flush Q.
  Proof.
    iStartProof (iProp _). iIntros (Hmono TV') "HP".
    iIntrosPostCrash.
    simpl.
    iDestruct ("HP" $! hG' hh na_views) as "P".
    iApply (base.post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    (* rewrite /post_crash_impl. *)
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    iIntros (CV).
    iSpecialize ("P" $! CV).
    monPred_simpl.
    iIntros (TV'' le) "(%flushLe & pers & crashedAt)".
    iSpecialize ("P" $! TV'' le with "[$pers $crashedAt //]").
    iDestruct (Hmono with "P") as "H".
    done.
  Qed.

  Lemma post_crash_flush_pure (P : Prop) : P → ⊢ <PCF> _, ⌜P⌝.
    rewrite -post_crash_flush_post_crash. apply post_crash_pure.
  Qed.

  Lemma post_crash_flush_embed_nodep P :
    ⎡ P ⎤ -∗ <PCF> _, ⎡ P ⎤.
  Proof.
    rewrite -post_crash_flush_post_crash. apply post_crash_embed_nodep.
  Qed.

  Lemma post_crash_flush_know_flush_lb `{AbstractState ST}
        (ℓ : loc) (s : ST) :
    know_flush_lb ℓ s -∗
    <PCF> hG, ∃ s__pc, ⌜s ⊑ s__pc⌝ ∗ 
      recovered_at ℓ s__pc ∗ know_persist_lb ℓ s__pc ∗
      know_flush_lb ℓ s__pc ∗ know_store_lb ℓ s__pc.
  Proof.
    iStartProof (iProp _).
    iIntros (TV).
    rewrite /know_flush_lb.
    simpl.
    iNamed 1.
    iIntros (???).
    iDestruct (post_crash_modality.post_crash_nodep with "order") as "order".
    iDestruct (post_crash_modality.post_crash_nodep with "knowFragHist") as "knowFragHist".
    iDestruct "viewFact" as "[[%neq %leq] | [%eq pers]]".
    * base.post_crash_modality.iCrash.
      iNamed 1.
      rewrite /post_crash_resource.
      iFrameNamed.
      iDestruct ("post_crash_history_impl" with "knowFragHist") as "knowFragHist".
      iDestruct ("post_crash_preorder_impl" with "order") as "order'".
      iIntros (CV).
      iIntros (??) "(% & #pers & #crash)".
      simpl.
      destruct (flush_view TV !! ℓ) as [[tF']|] eqn:eq; last first.
      { exfalso.
        rewrite /lookup_zero in leq.
        rewrite eq in leq.
        simpl in leq.
        lia. }
      edestruct view_le_look as (t'' & lookCV & lt); [apply eq|eassumption |].
      iDestruct (or_lost_post_crash_lookup CV with "crash order'") as "#order";
        first apply lookCV.
      iDestruct (or_lost_post_crash_lookup CV with "crash knowFragHist")
        as "(%s'' & %imp & knowFragHist)";
        first apply lookCV.
      assert (s ⊑ s'') as sInclS''.
      { etrans; first done. apply imp.
        etrans; first done.
        rewrite /lookup_zero.
        rewrite eq.
        simpl. done. }
      iAssert (persisted_loc ℓ 0) as "persisted".
      { iApply (persisted_persisted_loc with "pers").
        rewrite /view_to_zero.
        rewrite lookup_fmap.
        rewrite eq.
        done. }
      iExists s''.
      iSplit. { done. }
      iSplit. { iExists CV. iFrame "crash knowFragHist". iPureIntro.
                apply elem_of_dom. done. }
      iSplit. { iExists 0. iFrameNamed. iPureIntro. lia. }
      iSplit.
      { iExists 0.
        iFrameNamed.
        iRight. by iFrame "#". }
      iExists 0.
      iFrameNamed.
      iPureIntro. apply lookup_zero_gt_zero.
    * base.post_crash_modality.iCrash.
      iNamed 1.
      rewrite /post_crash_resource.
      iFrameNamed.
      iDestruct ("post_crash_history_impl" with "knowFragHist") as "knowFragHist".
      iDestruct ("post_crash_preorder_impl" with "order") as "order'".
      iIntros (CV).
      iIntros (??) "(% & #pers' & #crash)".
      simpl.
      iDestruct "pers" as "[#persisted (%CV' & %t & [%lookCV _] & crash')]".
      iDestruct (crashed_at_agree with "crash crash'") as %<-.
      iClear "crash'".
      iDestruct (or_lost_post_crash_lookup CV with "crash order'") as "#order";
        first apply lookCV.
      iDestruct (or_lost_post_crash_lookup CV with "crash knowFragHist")
        as "(%s'' & %imp & knowFragHist)";
        first apply lookCV.
      assert (s ⊑ s'') as sInclS''.
      { etrans; first done. apply imp.
        etrans; first done.
        rewrite /lookup_zero.
        rewrite eq.
        lia. }
      iExists s''.
      iSplit. { done. }
      iSplit. { iExists CV. iFrame "crash knowFragHist". iPureIntro.
                apply elem_of_dom. done. }
      iSplit.
      { iExists 0. iFrameNamed. iPureIntro. lia. }
      iSplit.
      { iExists 0. iFrameNamed. iRight. by iFrame "#". }
      iExists 0. iFrameNamed. iPureIntro. lia.
  Qed.

End post_crash_persisted.

Class IntoCrashFlush {Σ} `{nvmFixedG Σ, nvmDeltaG Σ}
      (P : dProp Σ) (Q : nvmDeltaG Σ → dProp Σ) :=
  into_crash_flushed : P -∗ post_crash_flush (Σ := Σ) (λ nD', Q nD').

Arguments IntoCrashFlush {_} {_} {_} _%I _%I.

Section IntoCrashFlush.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  (* Arguments IntoCrash {_} {_} {_} _%I hi%I. *)

  Global Instance into_crash_into_crash_flushed P Q :
    IntoCrash P Q →
    IntoCrashFlush P Q.
  Proof.
    rewrite /IntoCrashFlush /IntoCrash.
    rewrite -post_crash_flush_post_crash.
    done.
  Qed.

  (* Global Instance pure_into_crash_flushed (P : Prop) : *)
  (*   IntoCrashFlush (⌜ P ⌝) (λ _, ⌜ P ⌝)%I. *)
  (* Proof. rewrite /IntoCrashFlush. iIntros "%". by iApply post_crash_flush_pure. Qed. *)

  Global Instance know_flush_into_crash `{AbstractState ST} ℓ (s : ST) :
    IntoCrashFlush (know_flush_lb ℓ s) (λ _, ∃ s__pc, ⌜ s ⊑ s__pc ⌝ ∗
      recovered_at ℓ s__pc ∗
      know_persist_lb ℓ s__pc ∗
      know_flush_lb ℓ s__pc ∗
      know_store_lb ℓ s__pc)%I.
  Proof.
    rewrite /IntoCrashFlush. iIntros "P".
    by iApply post_crash_flush_know_flush_lb.
  Qed.

  Global Instance exist_into_crash_flush {A} Φ Ψ:
    (∀ x : A, IntoCrashFlush (Φ x) (λ hG, Ψ hG x)) →
    IntoCrashFlush (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrashFlush.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (post_crash_flush_mono with "HΦ"). auto.
  Qed.

End IntoCrashFlush.

Ltac crash_flush_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash_flush _) => crash_flush_env Γ'
    | environments.Esnoc ?Γ' ?id ?A =>
      first [ iEval (rewrite (@into_crash_flushed _ _ _ A) ) in id || iClear id ] ; crash_flush_env Γ'
  end.

Ltac crash_flush_ctx :=
  match goal with
  | [ |- environments.envs_entails ?Γ _] =>
    let spatial := pm_eval (environments.env_spatial Γ) in
    let intuit := pm_eval (environments.env_intuitionistic Γ) in
    crash_flush_env spatial; crash_flush_env intuit
  end.

Ltac iCrashFlush :=
  crash_flush_ctx;
  iApply (modus_ponens with "[-]"); [ iNamedAccu | ];
  rewrite ?post_crash_flush_named ?post_crash_flush_sep; iApply post_crash_flush_mono;
  intros; simpl;
  let H := iFresh in iIntros H; iNamed H.

Section post_crash_flush_test.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Lemma foo P : ⌜ P ⌝ -∗ <PCF> _, ⌜ P ⌝.
  Proof.
    iIntros "P".
    iCrashFlush.
    done.
  Qed.

End post_crash_flush_test.
