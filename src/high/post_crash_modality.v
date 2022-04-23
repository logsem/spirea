From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.Helpers Require Import ipm NamedProps.
From Perennial.program_logic Require Import recovery_weakestpre.

From self Require Import extra ipm_tactics if_non_zero map_extra.
From self.algebra Require Import ghost_map ghost_map_map.
From self.base Require Import primitive_laws wpr_lifting.
From self.base Require post_crash_modality.
From self.high Require Import dprop resources monpred_simpl or_lost if_rec.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

(** We define the post crash modality. *)

(* The three implications for the things stored for a protocolt. *)
Definition post_crash_pred_impl `{nvmG Σ} (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) ℓ (ϕ : ST → val → nvmDeltaG → dProp Σ),
    know_pred (hGD := nD) ℓ ϕ -∗
    or_lost_post_crash_no_t ℓ (▷ know_pred (hGD := nD') ℓ ϕ).

Definition post_crash_preorder_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST) ℓ,
    know_preorder_loc (nD := nD) ℓ (abs_state_relation (ST := ST)) -∗
    (or_lost_post_crash_no_t ℓ
      (know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)))).

Definition post_crash_bumper_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
      ℓ (bumper : ST → ST),
    know_bumper (nD := nD) ℓ bumper -∗
    or_lost_post_crash_no_t ℓ (know_bumper (nD := nD') ℓ bumper).

Definition post_crash_at_loc_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ, is_at_loc (nD := nD) ℓ -∗
    or_lost_post_crash_no_t ℓ (is_at_loc (nD := nD') ℓ).

Definition post_crash_na_loc_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ, is_na_loc (nD := nD) ℓ -∗
    or_lost_post_crash_no_t ℓ (is_na_loc (nD := nD') ℓ).

Definition offsets_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ t, ℓ ↪[@offset_name (@nvm_delta_high nD)]□ t -∗
    or_lost_post_crash
      ℓ
      (λ tC, ℓ ↪[@offset_name (@nvm_delta_high nD')]□ (t + tC)).

Definition map_map_phys_history_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ tStore msg,
    know_phys_hist_msg (nD := nD) ℓ tStore msg -∗
      or_lost_post_crash_no_t ℓ (
        ∃ v, know_phys_hist_msg (nD := nD') ℓ 0 (Msg v ∅ ∅ ∅)
      ).

Definition post_crash_na_view_map `{nvmG Σ}
           (na_views : gmap loc view) (nD nD' : nvmDeltaG) : iProp Σ :=
  (∀ ℓ q SV, know_na_view (nD := nD) ℓ q SV -∗ ⌜ na_views !! ℓ = Some SV ⌝) ∗
  [∗ map] ℓ ↦ SV ∈ na_views,
    soft_disj
      (λ q, know_na_view (nD := nD) ℓ q SV)
      (λ q, or_lost_post_crash_no_t ℓ (know_na_view (nD := nD') ℓ q ∅)).

Instance know_na_view_post_crash_fractional `{nvmG Σ, nvmDeltaG} ℓ :
  Fractional (λ q0 : Qp, or_lost_post_crash_no_t ℓ (know_na_view ℓ q0 ∅)).
Proof. apply or_lost_post_crash_fractional. apply _. Qed.

Definition new_hist t (bumper : positive → option positive) (hist : gmap time positive) :=
  omap bumper (drop_above t hist).

Definition know_history_post_crash `{nvmG Σ}
           (hG : nvmDeltaG) ℓ q bumper (hist : gmap time positive) : iProp Σ :=
  or_lost_post_crash ℓ (λ t,
    ∃ t' sOld sNew,
      ⌜ hist !! t' = Some sOld ⌝ ∗
      ⌜ bumper sOld = Some sNew ⌝ ∗
      (* ℓ ↪[crashed_in_name]□ sOld ∗ *)
      ℓ ↪[offset_name]□ t' ∗
      know_full_encoded_history_loc ℓ q (new_hist t' bumper hist) ∗
      know_frag_encoded_history_loc ℓ t' sNew
    )%I.

Instance know_history_post_crash_fractional `{nvmG Σ} hG ℓ bumper hist :
  Fractional (λ q, know_history_post_crash hG ℓ q bumper hist).
Proof.
Admitted. (* Trivial *)
(*   apply or_lost_post_crash_fractional. *)
(*   iIntros (t p q). *)
(*   iSplit. *)
(*   - iDestruct 1 as (?????) "(#? & #? & [L R] & #?)". *)
(*     iSplitL "L"; iExistsN; iFrame "#%∗". *)
(*   - iDestruct 1 as "[(% & % & % & % & % & #? & #off & L & #?) (% & % & % & % & % & #? & #? & R & #?)]". *)
(*     simplify_eq. *)
(*     iDestruct (ghost_map_elem_agree with "off [$]") as %<-. *)
(*     iCombine "L R" as "F". *)
(*     iExistsN. iFrame "∗#%". *)
(* Qed. *)

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_full_history_map `{nvmG Σ}
           (hh : gmap loc (gmap time positive))
           (bb : gmap loc (positive → option positive))
           (nD nD' : nvmDeltaG) : iProp Σ :=
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

Definition post_crash_frag_history_impl `{hG : nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
    ℓ (t : nat) (s : ST) (bumper : ST → ST),
      (* FIXME: It seems that we can remove the preorder *)
      know_preorder_loc (nD := nD) ℓ (abs_state_relation (ST := ST)) -∗
      know_bumper (nD := nD) ℓ bumper -∗
      know_frag_history_loc (nD := nD) ℓ t s -∗
      (or_lost_post_crash ℓ (λ t', ∃ offset,
        (* ⌜ t ≤ t' → s ⊑ s' ⌝ ∗ *)
        (* crashed_in_mapsto ℓ s' ∗ *)
        ⌜ t ≤ offset ⌝ ∗
        ℓ ↪[offset_name]□ offset ∗
        know_preorder_loc (nD := nD') ℓ (abs_state_relation (ST := ST)) ∗
        know_bumper (nD := nD') ℓ bumper ∗
        know_frag_history_loc (nD := nD') ℓ t (bumper s))).

Definition post_crash_resource_persistent `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  "#post_crash_frag_history_impl" ∷ post_crash_frag_history_impl nD nD' ∗
  "#post_crash_preorder_impl" ∷ post_crash_preorder_impl nD nD' ∗
  "#post_crash_pred_impl" ∷ post_crash_pred_impl nD nD' ∗
  "#post_crash_at_loc_impl" ∷ post_crash_at_loc_impl nD nD' ∗
  "#post_crash_na_loc_impl" ∷ post_crash_na_loc_impl nD nD' ∗
  "#post_crash_offsets_impl" ∷ offsets_impl nD nD' ∗
  "#post_crash_map_map_phys_history_impl" ∷ map_map_phys_history_impl nD nD' ∗
  "#post_crash_bumper_impl" ∷ post_crash_bumper_impl nD nD'.

Definition post_crash_resource_ephmeral `{nvmG Σ}
           (hh : gmap loc (gmap time positive))
           (bb : gmap loc (positive → option positive))
           (na_views : gmap loc view) (nD nD' : nvmDeltaG) : iProp Σ :=
  "post_crash_na_view_map" ∷ post_crash_na_view_map na_views nD nD' ∗
  "post_crash_full_history_map" ∷ post_crash_full_history_map hh bb nD nD'.

Definition post_crash_resource `{nvmG Σ}
           (hh : gmap loc (gmap time positive)) bb
           (na_views : gmap loc view) (nD nD' : nvmDeltaG) : iProp Σ :=
  post_crash_resource_persistent nD nD' ∗
  post_crash_resource_ephmeral hh bb na_views nD nD'.

Program Definition post_crash `{nvmG Σ, nD : nvmDeltaG}
        (P : nvmDeltaG → dProp Σ) : dProp Σ :=
  MonPred (λ _TV,
    ∀ (hhGD' : nvmHighDeltaG) hh bb na_views,
      base_post_crash (λ nD',
        let nD' := NvmDeltaG nD' hhGD'
        in (post_crash_resource hh bb na_views nD nD') -∗
          ▷ P nD' (∅, ∅, ∅) ∗
          (post_crash_resource_ephmeral hh bb na_views nD nD')))%I
    _.

Notation "'<PC>' g , P" := (post_crash (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

(** Tiny shortcut for introducing the assumption for a [post_crash]. *)
Ltac iIntrosPostCrash := iIntros (hG' hh bb na_views).

Section post_crash_prop.
  Context `{nvmG Σ, nD: nvmDeltaG}.

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
    iModel. iIntros "HP".
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

  Lemma post_crash_nodep (P : dProp Σ) `{!Objective P} : P -∗ <PC> _, P.
  Proof.
    iStartProof (iProp _). iIntros (TV') "P".
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "[H $]".
    iApply (objective_at with "P").
  Qed.

  Lemma post_crash_named P name :
    named name (post_crash (λ hG, P hG)) -∗
    post_crash (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

End post_crash_prop.

Section post_crash_interact.
  Context `{nvmG Σ, nD: nvmDeltaG}.

  Context `{AbstractState ST}.

  (** ** The rules for the "special" assertions

  How the post crash modality interacts with the assertions in the logic. *)

  Lemma new_hist_encode_eq t bumper (abs_hist : gmap time ST) :
    new_hist t (encode_bumper bumper) (encode <$> abs_hist) =
      encode <$> (bumper <$> drop_above t abs_hist).
  Proof.
    rewrite /new_hist. rewrite /drop_above.
  Admitted.

  Lemma post_crash_know_full_history_loc ℓ q (bumper : ST → ST)
        (abs_hist : gmap time ST) :
    ⎡ know_bumper ℓ bumper ⎤ ∗
    ⎡ know_full_history_loc ℓ q abs_hist ⎤ -∗
    <PC> _, if_rec ℓ (∃ t' (s : ST),
        ⌜ abs_hist !! t' = Some s ⌝ ∗
        ⎡ know_bumper ℓ bumper ⎤ ∗
        ⎡ ℓ ↪[offset_name]□ t' ⎤ ∗
        ⎡ know_full_history_loc ℓ q (bumper <$> (drop_above t' abs_hist)) ⎤ ∗
        ⎡ know_frag_history_loc ℓ t' (bumper s) ⎤
        (* ⎡ crashed_in_mapsto ℓ s ⎤). *)
          ).
   Proof.
    iStartProof (iProp _).
    iIntros (TV1) "[bumper hist]".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "bumper") as "bumper".
    iDestruct (base.post_crash_modality.post_crash_nodep with "hist") as "hist".
    post_crash_modality.iCrash.
    iIntros "[Ha Hb]". iNamed "Ha". iNamed "Hb".
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
    { iIntros "!>" (?) "H".
      iApply (full_entry_valid with "H"). }
    iDestruct ("reIns" with "[H]") as "M".
    { iExists _. iSplitPure; done. }
    iSplitL "newHist newBumper".
    { iNext.
      rewrite /know_history_post_crash.
      iApply or_lost_if_rec_at.
      iDestruct "newHist" as (CV) "[#crashed [H|H]]"; iExists (CV);
        iFrame "crashed"; [iLeft|iRight; done].
      iDestruct "H" as (t) "(%cvLook & #per & H)".
      iDestruct "H" as (???) "(%look & %bump & #offset & hist & frag)".
      iDestruct (or_lost_post_crash_lookup with "crashed newBumper") as "bumper";
        first done.
      apply lookup_fmap_Some in look as [st [eq ?]].
      apply encode_bumper_Some_decode in bump as (sn & decEq & encEq).
      simplify_eq.
      rewrite decode_encode in decEq.
      simplify_eq.
      iExists t. iFrame (cvLook) "per". iExists t', sn.
      iSplitPure; first assumption.
      iFrameF "bumper".
      iFrameF "offset".
      rewrite /full_entry_unenc /know_full_encoded_history_loc.
      rewrite new_hist_encode_eq.
      (* rewrite map_fmap_singleton. *)
      iFrame "hist".
      iExists _. iFrame "frag". iPureIntro. apply decode_encode. }
    rewrite /post_crash_resource.
    iFrame "post_crash_na_view_map". iFrame.
  Qed.

  Lemma post_crash_preorder ℓ :
    ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ -∗
    post_crash (λ hG', if_rec ℓ ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST) ) ⎤)%I.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    iDestruct ("post_crash_preorder_impl" with "HP") as "H".
    iNext.
    iApply or_lost_if_rec_embed. iFrame.
  Qed.

  Lemma post_crash_frag_history ℓ t bumper (s : ST) :
    ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ ∗
    ⎡ know_bumper ℓ bumper ⎤ ∗
    ⎡ know_frag_history_loc ℓ t s ⎤ -∗
    post_crash (λ hG',
      (or_lost_with_t ℓ (λ t', ∃ offset, (* ∃ s2, *)
        (* ⌜ t ≤ t' → s ⊑ s2 ⌝ ∗ *)
        (* ⎡ crashed_in_mapsto ℓ s2 ⎤ ∗ *)
        ⌜ t ≤ offset ⌝ ∗
        ⎡ ℓ ↪[offset_name]□ offset ⎤ ∗
        ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ ∗
        ⎡ know_bumper ℓ bumper ⎤ ∗
        ⎡ know_frag_history_loc ℓ t (bumper s) ⎤))).
  Proof.
    iStartProof (iProp _).
    iIntros (?) "(order & bumper & hist)".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "order") as "order".
    iDestruct (base.post_crash_modality.post_crash_nodep with "bumper") as "bumper".
    iDestruct (base.post_crash_modality.post_crash_nodep with "hist") as "hist".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    iDestruct ("post_crash_frag_history_impl" with "order bumper hist") as "hist".
    iApply or_lost_with_t_at.
    iApply (or_lost_post_crash_mono with "[] hist").
    iIntros (??) "_".
    naive_solver.
    (* iDestruct 1 as (?) "(% & ? & ? & ?)". iExists _. iFrame. done. *)
  Qed.

  Lemma post_crash_know_pred `{Countable ST'} ℓ (ϕ : ST' → val → nvmDeltaG → dProp Σ) :
    ⎡ know_pred ℓ ϕ ⎤ -∗ <PC> _, if_rec ℓ (⎡ know_pred ℓ ϕ ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_pred_impl" with "HP") as "H".
    iNext.
    iApply or_lost_if_rec_embed. iFrame.
  Qed.

  Lemma post_crash_at_loc ℓ :
    ⎡ is_at_loc ℓ ⎤ -∗ <PC> _, if_rec ℓ ⎡ is_at_loc ℓ ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource.
    iDestruct ("post_crash_at_loc_impl" with "HP") as "H".
    iApply or_lost_if_rec_embed. iFrame.
  Qed.

  Lemma post_crash_na_loc ℓ :
    ⎡ is_na_loc ℓ ⎤ -∗ <PC> _, if_rec ℓ ⎡ is_na_loc ℓ ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_na_loc_impl" with "HP") as "H".
    iApply or_lost_if_rec_embed. iFrame.
  Qed.

  (* Lemma post_crash_offset_with_t ℓ t1 : *)
  (*   ⎡ ℓ ↪[offset_name]□ t1 ⎤ -∗ *)
  (*   <PC> _, or_lost_with_t ℓ (λ t2, ⎡ ℓ ↪[offset_name]□ (t1 + t2) ⎤). *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (TV') "HP". *)
  (*   iIntrosPostCrash. *)
  (*   iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP". *)
  (*   post_crash_modality.iCrash. *)
  (*   iIntros "[Ha $]". iNamed "Ha". *)
  (*   rewrite /post_crash_resource. iFrameNamed. *)
  (*   iDestruct ("post_crash_offsets_impl" with "HP") as "H". *)
  (*   iApply or_lost_with_t_at. *)
  (*   iApply or_lost_post_crash_mono; last iApply "H". *)
  (*   iIntros (?) "? $". *)
  (* Qed. *)

  Lemma post_crash_offset ℓ tO :
    ⎡ ℓ ↪[offset_name]□ tO ⎤ -∗
    <PC> _, if_rec ℓ (∃ tC CV, ⌜ CV !! ℓ = Some (MaxNat tC) ⌝ ∗
                               ⎡ crashed_at CV ⎤ ∗
                               ⎡ ℓ ↪[offset_name]□ (tO + tC) ⎤).
  Proof.
  (* Admitted. (* Should be proveable from above. *) *)
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_offsets_impl" with "HP") as "H".
    iNext.
    rewrite -if_rec_or_lost_with_t.
    iApply or_lost_with_t_at.
    (* iApply or_lost_with_t_at. *)
    iApply or_lost_post_crash_mono; last iApply "H".
    iIntros (t CV).
    iNamed 1. iIntros "O".
    iExists _. iFrame (cvLook) "crashed O".
  Qed.

  Lemma post_crash_know_phys_hist_msg ℓ t msg :
    ⎡ know_phys_hist_msg ℓ t msg ⎤ -∗
    <PC> _, if_rec ℓ (∃ v, ⎡ know_phys_hist_msg ℓ 0 (Msg v ∅ ∅ ∅) ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_map_map_phys_history_impl" with "HP") as "H".
    iNext.
    iDestruct (or_lost_if_rec_embed with "H") as "H".
    iApply (if_rec_mono with "H").
    apply embed_exist_1.
  Qed.

  Lemma post_crash_know_na_view ℓ q SV :
    ⎡ know_na_view ℓ q SV ⎤ -∗ <PC> _, if_rec ℓ ⎡ know_na_view ℓ q ∅ ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha Hb]". iNamed "Ha". iNamed "Hb".
    iDestruct "post_crash_na_view_map" as "[in M]".
    iAssert (⌜ na_views !! _ = Some _ ⌝)%I as %HI. { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[H reIns]"; first done.
    iDestruct (soft_disj_exchange_l with "[] H [$]") as "[H HP]".
    { iIntros "!>" (?) "H".
      setoid_rewrite <- dfrac_valid_own.
      iApply (ghost_map_elem_valid with "H"). }
    rewrite -or_lost_if_rec_embed.
    iFrame "HP".
    iFrame "post_crash_full_history_map".
    iDestruct ("reIns" with "H") as "$".
    iFrame "in".
  Qed.

  Lemma post_crash_know_bumper `{AbstractState ST} ℓ (bumper : ST → ST) :
    ⎡ know_bumper ℓ bumper ⎤ -∗ <PC> _, if_rec ℓ ⎡ know_bumper ℓ bumper ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_bumper_impl" with "HP") as "H".
    iApply or_lost_if_rec_embed. iFrame.
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
    iDestruct ("post_crash_na_loc_impl" with "HP") as "H".
    rewrite -or_lost_embed.
    done.
  Qed.
  *)

End post_crash_interact.

Class IntoCrash {Σ} `{nvmG Σ, nvmDeltaG}
      (P : dProp Σ) (Q : nvmDeltaG → dProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ nD', Q nD').

Arguments IntoCrash {_} {_} {_} _%I _%I.

Section IntoCrash.
  Context `{nvmG Σ, nvmDeltaG}.

  (* Arguments IntoCrash {_} {_} {_} _%I hi%I. *)

  Global Instance pure_into_crash (P : Prop) :
    IntoCrash (⌜ P ⌝) (λ _, ⌜ P ⌝)%I.
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance lifted_embed_nodep_into_crash (P : iProp Σ) :
    IntoCrash (⎡ P ⎤) (λ _, ⎡ P ⎤)%I | 1000.
  Proof. apply: post_crash_nodep. Qed.

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
    IntoCrash _ _ := post_crash_know_full_history_loc ℓ q bumper abs_hist.

  Global Instance into_crash_preorder `{AbstractState ST} ℓ :
    IntoCrash _ _ := post_crash_preorder (ST := ST) ℓ.

  Global Instance frag_history_into_crash `{AbstractState ST}
         ℓ bumper t (s : ST) : IntoCrash _ _ :=
    post_crash_frag_history ℓ bumper t s.

  Global Instance know_pred_into_crash `{Countable ST}
         ℓ (ϕ : ST → _ → _ → dProp Σ) :
    IntoCrash _ _ := post_crash_know_pred ℓ ϕ.

  Global Instance at_loc_into_crash ℓ : IntoCrash _ _ := post_crash_at_loc ℓ.

  Global Instance na_loc_into_crash ℓ :
    IntoCrash _ _ := post_crash_na_loc ℓ.

  Global Instance offset_into_crash ℓ t :
    IntoCrash _ _ := post_crash_offset ℓ t.

  Global Instance know_phys_hist_msg_into_crash ℓ t msg :
    IntoCrash _ _ := post_crash_know_phys_hist_msg ℓ t msg.

  Global Instance exclusive_know_na_view_crash ℓ q SV :
    IntoCrash _ _ := post_crash_know_na_view ℓ q SV.

  Global Instance know_bumper_into_crash `{AbstractState ST} ℓ (bumper : ST → ST) :
    IntoCrash _ _ := post_crash_know_bumper ℓ bumper.

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
  Context `{nvmG Σ, nvmDeltaG}.

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

(* Definition post_crash_flush `{nvmG Σ, nvmDeltaG} *)
(*         (P : nvmDeltaG → dProp Σ) : dProp Σ := *)
(*     <PC> (λ (nD' : nvmDeltaG), P nD'). *)
(* Definition post_crash_flush `{nvmG Σ, nvmDeltaG} *)
(*         (P : nvmDeltaG → dProp Σ) : dProp Σ := *)
(*   (∀ TV, monPred_in TV -∗ *)
(*     <PC> (nD' : nvmDeltaG), *)
(*       ∀ (CV : view), *)
(*         ⌜ flush_view TV ⊑ CV ⌝ -∗ *)
(*         ⎡ crashed_at CV ⎤ -∗ *)
(*         P nD')%I. *)
(* Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed. *)

Program Definition post_crash_flush {Σ} `{nvmG Σ, nvmDeltaG}
        (P : nvmDeltaG → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (<PC> (nD' : nvmDeltaG),
      ∀ (CV : view),
        ⌜ flush_view TV ⊑ CV ⌝ ∗
        (* ⎡ persisted (flush_view TV) ⎤ -∗ *)
        ⎡ persisted (view_to_zero (flush_view TV)) ⎤ ∗
        ⎡ crashed_at CV ⎤ -∗
        P nD') (∅, ∅, ∅))%I _.
Next Obligation. intros ???????. apply post_crash_mono. solve_proper. Qed.

(*
Program Definition post_crash_flush `{hG : !nvmG Σ, nvmDeltaG}
        (P : nvmG Σ, nvmDeltaG → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (post_crash (λ hG', ∃ CV, ⌜flush_view TV ⊑ CV⌝ ∗ ⎡crashed_at CV⎤ -∗ P hG')) TV
  )%I _.
Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed.
*)

Notation "'<PCF>' g , P" :=
  (post_crash_flush (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

Section post_crash_persisted.
  Context `{hG: !nvmG Σ, nvmDeltaG}.

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

  Lemma post_crash_flush_named `{nvmG Σ, nvmDeltaG} P name :
    named name (post_crash_flush (λ hG, P hG)) -∗
    post_crash_flush (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

  Lemma post_crash_flush_sep `{nvmG Σ, nvmDeltaG} P Q :
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

  Lemma post_crash_flush_disj P Q :
    post_crash_flush P ∨ post_crash_flush Q -∗ <PCF> hG, P hG ∨ Q hG.
  Proof.
    iModel.
    iIntros "[HP | HP]".
    - iIntrosPostCrash.
      iDestruct ("HP" $! hG' hh bb na_views) as "HP".
      base.post_crash_modality.iCrash.
      iIntros "[#RP RE]".
      iDestruct ("HP" with "[$RP $RE]") as "[HP $]".
      iNext.
      iIntros (CV).
      iSpecialize ("HP" $! CV).
      iIntros (TV'' le) "(%flushLe & #pers & #crashedAt)".
      iSpecialize ("HP" with "[$pers $crashedAt //]").
      iLeft. iFrame "HP".
    - iIntrosPostCrash.
      iDestruct ("HP" $! hG' hh bb na_views) as "HP".
      base.post_crash_modality.iCrash.
      iIntros "[#RP RE]".
      iDestruct ("HP" with "[$RP $RE]") as "[HP $]".
      iNext.
      iIntros (CV).
      iSpecialize ("HP" $! CV).
      iIntros (TV'' le) "(%flushLe & #pers & #crashedAt)".
      iSpecialize ("HP" with "[$pers $crashedAt //]").
      iRight. iFrame "HP".
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

  Lemma post_crash_flush_nodep P `{!Objective P} :
    P -∗ <PCF> _, P.
  Proof. rewrite -post_crash_flush_post_crash. apply: post_crash_nodep. Qed.

  Lemma post_crash_have_FV_strong ℓ t :
    have_FV_strong ℓ t -∗
    <PCF> _,
      ⎡ persisted ({[ ℓ := MaxNat 0 ]}) ⎤ ∗
      ∃ CV t', ⌜CV !! ℓ = Some (MaxNat t') ∧ t ≤ t'⌝ ∗ ⎡ crashed_at CV ⎤.
  Proof.
    iModel. iIntros "le". simpl.
    iIntros (nD hh bb na_views).
    base.post_crash_modality.iCrash.
    destruct (TV) as [[??]?]. iDestruct "le" as %[[? le] ?].
    iIntros "[_ $] !>" (CV).
    monPred_simpl. simpl.
    iIntros (??) "(%le2 & pers & crashed)".
    iDestruct (persisted_persisted_loc with "[$]") as "$".
    { apply view_le_singleton in le as (t2 & look & ?).
      eapply view_to_zero_lookup. done. }
    pose proof (transitivity le le2) as le3.
    apply view_le_singleton in le3 as (? & look & ?).
    iExists _, _. iFrame "crashed". done.
  Qed.

End post_crash_persisted.

Class IntoCrashFlush {Σ} `{nvmG Σ, nvmDeltaG}
      (P : dProp Σ) (Q : nvmDeltaG → dProp Σ) :=
  into_crash_flushed : P -∗ post_crash_flush (Σ := Σ) (λ nD', Q nD').

Arguments IntoCrashFlush {_} {_} {_} _%I _%I.

Section IntoCrashFlush.
  Context `{nvmG Σ, nvmDeltaG}.

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

  Global Instance lifted_embed_into_crash_flush (P : iProp Σ) Q :
    base.post_crash_modality.IntoCrash P Q →
    IntoCrashFlush (⎡ P ⎤) (λ _, ⎡ Q _ ⎤)%I.
  Proof. intros ?. apply into_crash_into_crash_flushed. apply _. Qed.

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

  Global Instance disj_into_crash_flush (P Q : dProp Σ) (P' Q' : _ → dProp Σ) :
    IntoCrashFlush P P' → IntoCrashFlush Q Q' → IntoCrashFlush (P ∨ Q)%I (λ hD, P' hD ∨ Q' hD)%I.
  Proof.
    rewrite /IntoCrashFlush.
    iIntros (Pi Qi) "[P|Q]".
    - iDestruct (Pi with "P") as "P".
      iApply post_crash_flush_disj.
      iLeft.
      iFrame.
    - iDestruct (Qi with "Q") as "Q".
      iApply post_crash_flush_disj.
      iRight.
      iFrame.
  Qed.

  Global Instance have_FV_strong_into_crash_flush ℓ t :
    IntoCrashFlush _ _ := post_crash_have_FV_strong ℓ t.

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

  Global Instance offset_into_crash_flush ℓ t : IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (offset_into_crash ℓ t).

  Global Instance know_pred_into_crash_flush `{Countable ST}
         ℓ (ϕ : ST → _ → _ → _) :
    IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (know_pred_into_crash ℓ ϕ).

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
  Context `{nvmG Σ, nvmDeltaG}.

  Lemma foo P `{Countable ST'} ℓ (ϕ : ST' → val → nvmDeltaG → dProp Σ) t :
    ⌜ P ⌝ -∗
    ⎡ know_pred ℓ ϕ ⎤ -∗
    ⎡ persisted_loc ℓ t ⎤ -∗
    <PCF> _, ⌜ P ⌝ ∗ if_rec ℓ ⎡ know_pred ℓ ϕ ⎤.
  Proof.
    iIntros "P pred pers".
    iCrashFlush.
    iFrame.
  Qed.

End post_crash_flush_test.

Typeclasses Opaque post_crash.
Typeclasses Opaque post_crash_flush.
