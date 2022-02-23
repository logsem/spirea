From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.Helpers Require Import ipm NamedProps.
From Perennial.program_logic Require Import recovery_weakestpre.

From self Require Import extra ipm_tactics if_non_zero.
From self.algebra Require Import ghost_map.
From self.base Require Import primitive_laws wpr_lifting.
From self.base Require post_crash_modality.
From self.high Require Import dprop resources monpred_simpl or_lost.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

(** We define the post crash modality. *)

(* The three implications for the things stored for a protocolt. *)
Definition post_crash_pred_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) ℓ (ϕ : ST → val → nvmDeltaG Σ → dProp Σ),
    know_pred (hGD := nD) ℓ ϕ -∗
    or_lost_post_crash_no_t ℓ (▷ know_pred (hGD := nD') ℓ ϕ).

Definition post_crash_preorder_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST) ℓ,
    know_preorder_loc (nD := nD) ℓ (abs_state_relation (ST := ST)) -∗
    (or_lost_post_crash_no_t ℓ
      (know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)))).

Definition post_crash_bumper_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
      ℓ (bumper : ST → ST),
    know_bumper (nD := nD) ℓ bumper -∗
    or_lost_post_crash_no_t ℓ (know_bumper (nD := nD') ℓ bumper).

Definition post_crash_shared_loc_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ℓ, is_at_loc (nD := nD) ℓ -∗
    or_lost_post_crash_no_t ℓ (is_at_loc (nD := nD') ℓ).

Definition post_crash_exclusive_loc_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ℓ, is_na_loc (nD := nD) ℓ -∗
    or_lost_post_crash_no_t ℓ (is_na_loc (nD := nD') ℓ).

Definition map_map_phys_history_impl `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ℓ tStore msg,
    know_phys_hist_msg (nD := nD) ℓ tStore msg -∗
      or_lost_post_crash_no_t ℓ (
        ∃ v, know_phys_hist_msg (nD := nD') ℓ 0 (Msg v ∅ ∅ ∅)
      ).

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

Definition know_history_post_crash `{nvmFixedG Σ}
            (hG : nvmDeltaG Σ) ℓ q bumper (hist : gmap time positive) : iProp Σ :=
  or_lost_post_crash ℓ (λ t,
    ∃ sOld sNew,
      ⌜hist !! t = Some sOld⌝ ∗
      ⌜bumper sOld = Some sNew⌝ ∗
      know_full_encoded_history_loc ℓ q ({[ 0 := sNew ]}) ∗
      know_frag_encoded_history_loc ℓ ({[ 0 := sNew ]}))%I.

Instance know_history_post_crash_fractional `{nvmFixedG Σ} hG ℓ bumper hist :
  Fractional (λ q, know_history_post_crash hG ℓ q bumper hist).
Proof.
  apply or_lost_post_crash_fractional.
  iIntros (t p q).
  iSplit.
  - iDestruct 1 as (????) "([[L R] #?] & #?)".
    iSplitL "L"; iExists _, _; iFrame "#%∗".
  - iDestruct 1 as "[(% & % & % & % & [L #?] & #?) (% & % & % & % & [R #?] & #?)]".
    simplify_eq. iCombine "L R" as "F". iExists _, _. iFrame "∗#%".
Qed.

Definition post_crash_frag_history_impl `{hG : nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
    ℓ (t : nat) (s : ST) (bumper : ST → ST),
      know_preorder_loc (nD := nD) ℓ (abs_state_relation (ST := ST)) -∗
      know_bumper (nD := nD) ℓ bumper -∗
      know_frag_history_loc (nD := nD) ℓ {[ t := s ]} -∗
      (or_lost_post_crash ℓ (λ t', ∃ s',
        ⌜t ≤ t' → s ⊑ s'⌝ ∗
        know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)) ∗
        know_bumper (nD := nD') ℓ bumper ∗
        know_frag_history_loc (nD := nD') ℓ {[ 0 := bumper s' ]})).

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_full_history_map `{nvmFixedG Σ}
           (hh : gmap loc (gmap time positive))
           (bb : gmap loc (positive → option positive))
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ q hist,
     know_full_encoded_history_loc (nD := nD) ℓ q hist -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (∀ ℓ b,
     know_encoded_bumper (nD := nD) ℓ b -∗ ⌜bb !! ℓ = Some b⌝) ∗
  (* The map used to perform the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh, ∃ bumper,
    ⌜ bb !! ℓ = Some bumper ⌝ ∗
    soft_disj
      (λ q, know_full_encoded_history_loc (nD := nD) ℓ q hist)
      (λ q, know_history_post_crash nD' ℓ q bumper hist).

Definition post_crash_resource_persistent `{nvmFixedG Σ}
           (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  "#post_crash_frag_history_impl" ∷ post_crash_frag_history_impl nD nD' ∗
  "#post_crash_preorder_impl" ∷ post_crash_preorder_impl nD nD' ∗
  "#post_crash_pred_impl" ∷ post_crash_pred_impl nD nD' ∗
  "#post_crash_shared_loc_impl" ∷ post_crash_shared_loc_impl nD nD' ∗
  "#post_crash_exclusive_loc_impl" ∷ post_crash_exclusive_loc_impl nD nD' ∗
  "#post_crash_map_map_phys_history_impl" ∷ map_map_phys_history_impl nD nD' ∗
  "#post_crash_bumper_impl" ∷ post_crash_bumper_impl nD nD'.

Definition post_crash_resource_ephmeral `{nvmFixedG Σ}
           (hh : gmap loc (gmap time positive)) (bb : gmap loc (positive → option positive))
           (na_views : gmap loc view) (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  "post_crash_na_view_map" ∷ post_crash_na_view_map na_views nD nD' ∗
  "post_crash_full_history_map" ∷ post_crash_full_history_map hh bb nD nD'.

Definition post_crash_resource `{nvmFixedG Σ}
           (hh : gmap loc (gmap time positive)) bb
           (na_views : gmap loc view) (nD nD' : nvmDeltaG Σ) : iProp Σ :=
  post_crash_resource_persistent nD nD' ∗
  post_crash_resource_ephmeral hh bb na_views nD nD'.

Program Definition post_crash `{nvmFixedG Σ, nD : nvmDeltaG Σ}
        (P : nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ _TV,
    ∀ (hhGD' : nvmHighDeltaG) hh bb na_views,
      base_post_crash (λ nD',
        let nD' := NvmDeltaG _ nD' hhGD'
        in (post_crash_resource hh bb na_views nD nD') -∗
          ▷ P nD' (∅, ∅, ∅) ∗
          (post_crash_resource_ephmeral hh bb na_views nD nD')))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Notation "'<PC>' g , P" := (post_crash (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

(** Tiny shortcut for introducing the assumption for a [post_crash]. *)
Ltac iIntrosPostCrash := iIntros (hG' hh bb na_views).

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

  Lemma post_crash_emp : emp ⊢ post_crash (λ _, emp).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    post_crash_modality.iCrash.
    iIntros "[_ $]". done.
  Qed.

  Lemma post_crash_sep P Q :
    post_crash P ∗ post_crash Q -∗ <PC> hG, P hG ∗ Q hG.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG' hh bb na_views) as "HP".
    iDestruct ("HQ" $! hG' hh bb na_views) as "HQ".
    post_crash_modality.iCrash.
    iIntros "[#M1 M2]".
    iDestruct ("HP" with "[$M1 $M2]") as "[$ M2]".
    iDestruct ("HQ" with "[$M1 $M2]") as "[$ $]".
  Qed.

  Lemma post_crash_disj P Q :
    post_crash P ∨ post_crash Q -∗ <PC> hG, P hG ∨ Q hG.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iIntros "[HP | HQ]".
    - iIntrosPostCrash.
      iDestruct ("HP" $! hG' hh bb na_views) as "HP".
      post_crash_modality.iCrash.
      iIntros "M".
      iDestruct ("HP" with "M") as "[$ $]".
    - iIntrosPostCrash.
      iDestruct ("HQ" $! hG' hh bb na_views) as "HQ".
      post_crash_modality.iCrash.
      iIntros "M".
      iDestruct ("HQ" with "M") as "[$ $]".
  Qed.

  Lemma post_crash_pure (P : Prop) : P → ⊢ <PC> _, ⌜P⌝.
  Proof.
    iIntros (HP).
    iStartProof (iProp _). iIntros (TV').
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "[H $]".
    iApply monPred_at_pure.
    iFrame "%".
  Qed.

  Lemma post_crash_embed_nodep P :
    ⎡ P ⎤ -∗ <PC> _, ⎡ P ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "P".
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "[H $]".
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

  Lemma post_crash_know_full_history_loc ℓ q (abs_hist : gmap time ST) (bumper : ST → ST) :
    ⎡ know_bumper ℓ bumper ⎤ ∗ ⎡ know_full_history_loc ℓ q abs_hist ⎤ -∗
    <PC> _, or_lost_with_t ℓ (λ t, ∃ (s : ST),
        ⌜abs_hist !! t = Some s⌝ ∗
        ⎡ know_bumper ℓ bumper ⎤ ∗
        ⎡ know_full_history_loc ℓ q {[ 0 := bumper s ]} ⎤ ∗
        ⎡ know_frag_history_loc ℓ {[ 0 := bumper s ]} ⎤).
  Proof.
    iStartProof (iProp _).
    iIntros (TV1) "[bumper hist]".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "bumper") as "bumper".
    iDestruct (post_crash_modality.post_crash_nodep with "hist") as "hist".
    post_crash_modality.iCrash.
    iIntros "[Ha Hb]". iNamed "Ha". iNamed "Hb".
    (* iFrame "post_crash_preorder_impl". *)
    (* Get the new bumper. *)
    iDestruct ("post_crash_bumper_impl" with "bumper") as "#newBumper".
    iDestruct "post_crash_full_history_map" as "(inH & inB & M)".
    rewrite /know_full_history_loc own_full_equiv.
    iAssert (⌜hh !! _ = Some _⌝)%I as %HI. { iApply ("inH" with "hist"). }
    iAssert (⌜bb !! _ = Some _⌝)%I as %BI.
    { iApply ("inB" with "[bumper]").
      rewrite /know_bumper /own_know_bumper.
      iDestruct "bumper" as "[_ $]". }
    iDestruct (big_sepM_lookup_acc with "M") as
      "[(%bumper' & %bumpersLook & H) reIns]"; first done.
    simplify_eq.
    iDestruct (soft_disj_exchange_l with "[] H [$]") as "[H newHist]".
    { iIntros "!>" (?) "[H _]".
      setoid_rewrite <- dfrac_valid_own.
      iApply (ghost_map_elem_valid with "H"). }
    (* iFrame "#∗". *)
    iDestruct ("reIns" with "[H]") as "M".
    { iExists _. iSplitPure; done. }
    iSplitL "newHist newBumper".
    { iDestruct "newHist" as (CV) "[#crashed [H|H]]"; iExists (CV);
        iFrame "crashed"; [iLeft|iRight; done].
      iDestruct "H" as (t) "(%cvLook & #per & (% & % & %look & %bump & hist & frag))".
      iDestruct (or_lost_post_crash_lookup with "crashed newBumper") as "bumper";
        first done.
      apply lookup_fmap_Some in look as [st [eq ?]].
      apply encode_bumper_Some_decode in bump as (sn & decEq & encEq).
      simplify_eq.
      rewrite decode_encode in decEq.
      iExists t. iFrame (cvLook) "per". iExists st.
      iSplitPure; first assumption.
      iFrame "bumper".
      rewrite /history_full_map_loc /know_full_encoded_history_loc. rewrite map_fmap_singleton.
      simplify_eq. iFrame "hist".
      iExists _. iFrame "frag". iPureIntro. rewrite !map_fmap_singleton.
      rewrite decode_encode. done. }
    rewrite /post_crash_resource.
    iFrame "post_crash_na_view_map". iFrame.
  Qed.

  Lemma post_crash_preorder ℓ :
    ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ -∗
    post_crash (λ hG', or_lost ℓ ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST) ) ⎤)%I.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    iDestruct ("post_crash_preorder_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    iNext. iFrame "H".
  Qed.

  Lemma post_crash_frag_history ℓ t bumper (s : ST) :
    ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ ∗
    ⎡ know_bumper ℓ bumper ⎤ ∗
    ⎡ know_frag_history_loc ℓ {[ t := s ]} ⎤ -∗
    post_crash (λ hG',
      (or_lost_with_t ℓ (λ t', ∃ s',
        ⌜t ≤ t' → s ⊑ s'⌝ ∗
        ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ ∗
        ⎡ know_bumper ℓ bumper ⎤ ∗
        ⎡ know_frag_history_loc ℓ {[ 0 := bumper s' ]} ⎤))).
  Proof.
    iStartProof (iProp _).
    iIntros (?) "(order & bumper & hist)".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "order") as "order".
    iDestruct (post_crash_modality.post_crash_nodep with "bumper") as "bumper".
    iDestruct (post_crash_modality.post_crash_nodep with "hist") as "hist".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    iDestruct ("post_crash_frag_history_impl" with "order bumper hist") as "hist".
    iApply or_lost_with_t_at.
    iApply (or_lost_post_crash_mono with "[] hist").
    iIntros (?) "_".
    iDestruct 1 as (?) "(% & ? & ? & ?)". iExists _. iFrame. done.
  Qed.

  Lemma post_crash_know_pred `{Countable ST'} ℓ (ϕ : ST' → val → nvmDeltaG Σ → dProp Σ) :
    ⎡ know_pred ℓ ϕ ⎤ -∗ <PC> _, or_lost ℓ (⎡ know_pred ℓ ϕ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_pred_impl" with "HP") as "H".
    rewrite /or_lost /or_lost_with_t.
    iNext.
    iDestruct "H" as (CV) "H".
    iExists _. iFrame "H".
  Qed.

  Lemma post_crash_shared_loc ℓ :
    ⎡ is_at_loc ℓ ⎤ -∗ <PC> _, or_lost ℓ (⎡ is_at_loc ℓ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource.
    iDestruct ("post_crash_shared_loc_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    iFrame "H".
  Qed.

  Lemma post_crash_exclusive_loc ℓ :
    ⎡ is_na_loc ℓ ⎤ -∗ <PC> _, or_lost ℓ (⎡ is_na_loc ℓ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_exclusive_loc_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    iFrame "H".
  Qed.

  Lemma post_crash_know_phys_hist_msg ℓ t msg :
    ⎡ know_phys_hist_msg ℓ t msg ⎤ -∗ <PC> _, or_lost ℓ (∃ v,
      ⎡ know_phys_hist_msg ℓ 0 (Msg v ∅ ∅ ∅) ⎤
    ).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_map_map_phys_history_impl" with "HP") as "H".
    rewrite /or_lost.
    iApply or_lost_with_t_at.
    iApply (or_lost_post_crash_mono with "[] H").
    naive_solver.
  Qed.

  Lemma post_crash_know_na_view ℓ q SV :
    ⎡ know_na_view ℓ q SV ⎤ -∗ <PC> _, or_lost ℓ (⎡ know_na_view ℓ q ∅ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha Hb]". iNamed "Ha". iNamed "Hb".
    iDestruct "post_crash_na_view_map" as "[in M]".
    iAssert (⌜ na_views !! _ = Some _ ⌝)%I as %HI. { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[H reIns]"; first done.
    iDestruct (soft_disj_exchange_l with "[] H [$]") as "[H HP]".
    { iIntros "!>" (?) "H".
      setoid_rewrite <- dfrac_valid_own.
      iApply (ghost_map_elem_valid with "H"). }
    rewrite -or_lost_embed.
    iFrame "HP".
    iFrame "post_crash_full_history_map".
    iDestruct ("reIns" with "H") as "$".
    iFrame "in".
  Qed.

  Lemma post_crash_know_bumper `{AbstractState ST} ℓ (bumper : ST → ST) :
    ⎡ know_bumper ℓ bumper ⎤ -∗ <PC> _, or_lost ℓ (⎡ know_bumper ℓ bumper ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_bumper_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    iFrame "H".
  Qed.

  (*
  Lemma post_crash_is_na_loc ℓ :
    ⎡ is_na_loc ℓ ⎤ -∗ <PC> _, or_lost ℓ (⎡ is_na_loc ℓ ⎤).
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
    iIntros "[_ $]". done.
  Qed.

  Tactic Notation "lift_into_crash" uconstr(lem) :=
    rewrite /IntoCrash; iIntros "P"; by iApply lem.

  Global Instance emp_into_crash : IntoCrash emp (λ hD, emp)%I.
  Proof. lift_into_crash post_crash_emp. Qed.

  Global Instance sep_into_crash (P Q : dProp Σ) (P' Q' : _ → dProp Σ) :
    IntoCrash P P' → IntoCrash Q Q' → IntoCrash (P ∗ Q)%I (λ hD, P' hD ∗ Q' hD)%I.
  Proof.
    rewrite /IntoCrash.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply (post_crash_sep). iFrame.
  Qed.

  Global Instance disj_into_crash (P Q : dProp Σ) (P' Q' : _ → dProp Σ) :
    IntoCrash P P' → IntoCrash Q Q' → IntoCrash (P ∨ Q)%I (λ hD, P' hD ∨ Q' hD)%I.
  Proof.
    rewrite /IntoCrash.
    iIntros (Pi Qi) "[P|Q]".
    - iDestruct (Pi with "P") as "P".
      iApply post_crash_disj.
      iLeft.
      iFrame.
    - iDestruct (Qi with "Q") as "Q".
      iApply post_crash_disj.
      iRight.
      iFrame.
  Qed.

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) →
    IntoCrash (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (post_crash_mono with "HΦ"). auto.
  Qed.

  (* Global Instance embed_into_crash P : *)
  (*   IntoCrash (⎡ P ⎤%I) (λ _, ⎡ P ⎤%I). *)
  (* Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_embed_nodep. Qed. *)

  Global Instance into_crash_know_full_history_loc `{AbstractState ST}
         ℓ q (bumper : ST → ST) abs_hist :
    IntoCrash
      (⎡ know_bumper ℓ bumper ⎤ ∗ ⎡ know_full_history_loc ℓ q abs_hist ⎤)
      (λ hG', or_lost_with_t ℓ (λ t, ∃ (s : ST),
        ⌜abs_hist !! t = Some s⌝ ∗
        ⎡ know_bumper ℓ bumper ⎤ ∗
        ⎡ know_full_history_loc ℓ q {[ 0 := bumper s ]} ⎤ ∗
        ⎡ know_frag_history_loc ℓ {[ 0 := bumper s ]} ⎤))%I.
  Proof.
    lift_into_crash post_crash_know_full_history_loc.
  Qed.

  Global Instance into_crash_preorder `{AbstractState ST} ℓ :
    IntoCrash
    (⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤)
    (λ hG', or_lost ℓ (⎡know_preorder_loc ℓ (abs_state_relation (ST := ST))⎤))%I.
  Proof. lift_into_crash post_crash_preorder. Qed.

  Global Instance frag_history_into_crash `{AbstractState ST}
         ℓ bumper t (s : ST) : IntoCrash _ _ :=
    post_crash_frag_history ℓ bumper t s.

  Global Instance know_pred_into_crash `{AbstractState ST}
         ℓ (ϕ : ST → _ → _ → dProp Σ) :
    IntoCrash _ _ := post_crash_know_pred ℓ ϕ.

  Global Instance shared_loc_into_crash ℓ :
    IntoCrash
      (⎡ is_at_loc ℓ ⎤)%I
      (λ hG', or_lost ℓ (⎡ is_at_loc ℓ ⎤))%I.
  Proof. lift_into_crash post_crash_shared_loc. Qed.

  Global Instance exclusive_loc_into_crash ℓ :
    IntoCrash
      (⎡ is_na_loc ℓ ⎤)%I
      (λ hG', or_lost ℓ (⎡ is_na_loc ℓ ⎤))%I.
  Proof. lift_into_crash post_crash_exclusive_loc. Qed.

  Global Instance know_phys_hist_msg_into_crash ℓ t msg :
    IntoCrash
      (⎡ know_phys_hist_msg ℓ t msg ⎤)%I
      (λ hG', or_lost ℓ (∃ v, ⎡ know_phys_hist_msg ℓ 0 (Msg v ∅ ∅ ∅) ⎤))%I.
  Proof. lift_into_crash post_crash_know_phys_hist_msg. Qed.

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
      (⎡ is_na_loc ℓ ⎤)
      (λ _, or_lost ℓ (⎡ is_na_loc ℓ ⎤)).
  Proof.
    rewrite /IntoCrash. iIntros "P". by iApply post_crash_is_na_loc.
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

Program Definition post_crash_flush {Σ} `{nvmFixedG Σ, nvmDeltaG Σ}
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
    iIntros (nD hh bb na_views).
    iSpecialize ("P" $! nD hh bb na_views).
    iApply (base.post_crash_modality.post_crash_mono with "P").
    iIntros (?) "A R".
    iDestruct ("A" with "R") as "[P $]".
    iNext.
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
    iDestruct ("HP" $! hG' hh bb na_views) as "HP".
    iDestruct ("HQ" $! hG' hh bb na_views) as "HQ".
    base.post_crash_modality.iCrash.
    iIntros "[#M1 M2]".
    iDestruct ("HP" with "[$M1 $M2]") as "[H M2]".
    iDestruct ("HQ" with "[$M1 $M2]") as "[H1 $]".
    iIntros (CV).
    iSpecialize ("H" $! CV).
    iSpecialize ("H1" $! CV).
    monPred_simpl.
    iNext.
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
    iDestruct ("HP" $! hG' hh bb na_views) as "P".
    iApply (base.post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    (* rewrite /post_crash_impl. *)
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    iNext.
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

End post_crash_persisted.

Class IntoCrashFlush {Σ} `{nvmFixedG Σ, nvmDeltaG Σ}
      (P : dProp Σ) (Q : nvmDeltaG Σ → dProp Σ) :=
  into_crash_flushed : P -∗ post_crash_flush (Σ := Σ) (λ nD', Q nD').

Arguments IntoCrashFlush {_} {_} {_} _%I _%I.

Section IntoCrashFlush.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  (* This is not an instance as it would probably have a negative impact on the
  performance of type class resolution. *)
  Lemma into_crash_into_crash_flushed P Q :
    IntoCrash P Q →
    IntoCrashFlush P Q.
  Proof.
    rewrite /IntoCrashFlush /IntoCrash.
    rewrite -post_crash_flush_post_crash.
    done.
  Qed.

  Global Instance pure_into_crash_flushed (P : Prop) :
    IntoCrashFlush (⌜ P ⌝) (λ _, ⌜ P ⌝)%I.
  Proof. apply into_crash_into_crash_flushed. apply _. Qed.

  Global Instance lifted_embed_nodep_into_crash_flush (P : iProp Σ) :
    IntoCrashFlush (⎡ P ⎤) (λ _, ⎡ P ⎤)%I | 1000.
  Proof. apply into_crash_into_crash_flushed. apply _. Qed.

  Global Instance emp_into_crash_flush : IntoCrashFlush emp (λ hD, emp)%I.
  Proof. apply: into_crash_into_crash_flushed. Qed.

  Global Instance sep_into_crash_flush (P Q : dProp Σ) (P' Q' : _ → dProp Σ) :
    IntoCrashFlush P P' →
    IntoCrashFlush Q Q' →
    IntoCrashFlush (P ∗ Q)%I (λ hD, P' hD ∗ Q' hD)%I.
  Proof.
    rewrite /IntoCrashFlush.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply (post_crash_flush_sep). iFrame.
  Qed.

  Global Instance exist_into_crash_flush {A} Φ Ψ:
    (∀ x : A, IntoCrashFlush (Φ x) (λ hG, Ψ hG x)) →
    IntoCrashFlush (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrashFlush.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (post_crash_flush_mono with "HΦ"). auto.
  Qed.

  Global Instance big_sepL_into_crash_flush {A} ϕ ψ l :
    (∀ k (x : A), IntoCrashFlush (ϕ k x) (ψ k x)) →
    IntoCrashFlush ([∗ list] k↦x ∈ l, ϕ k x)%I (λ hG, [∗ list] k↦x ∈ l, ψ k x _)%I.
  Proof. revert ϕ ψ. induction l as [|x l IH]=> Φ ψ ? /=; apply _. Qed.

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

Typeclasses Opaque post_crash.
Typeclasses Opaque post_crash_flush.
