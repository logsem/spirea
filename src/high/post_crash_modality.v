From iris.algebra Require Import auth.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.Helpers Require Import ipm NamedProps.
From Perennial.program_logic Require Import recovery_weakestpre.

From self Require Import extra ipm_tactics if_non_zero map_extra.
From self.algebra Require Import ghost_map ghost_map_map.
From self.base Require Import primitive_laws wpr_lifting.
From self.base Require post_crash_modality.
From self.high Require Import dprop dprop_liftings viewobjective resources
  monpred_simpl or_lost if_rec predicates.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

(** We define the post crash modality. *)

(* The three implications for the things stored for a protocolt. *)
Definition post_crash_full_pred_impl `{nvmG Σ} (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) ℓ (ϕ : ST → val → dProp Σ),
    know_full_pred (hGD := nD) ℓ ϕ -∗
    or_lost_post_crash_no_t ℓ (▷ know_full_pred (hGD := nD') ℓ ϕ).

Definition post_crash_read_pred_impl `{nvmG Σ} (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) ℓ (ϕ : ST → val → dProp Σ),
    know_read_pred (hGD := nD) ℓ ϕ -∗
    or_lost_post_crash_no_t ℓ (▷ know_read_pred (hGD := nD') ℓ ϕ).

Definition post_crash_pers_pred_impl `{nvmG Σ} (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) ℓ (ϕ : ST → val → dProp Σ),
    know_pers_pred (hGD := nD) ℓ ϕ -∗
    or_lost_post_crash_no_t ℓ (▷ know_pers_pred (hGD := nD') ℓ ϕ).

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
    own_know_bumper (get_bumpers_name nD) ℓ bumper -∗
    or_lost_post_crash_no_t ℓ (own_know_bumper (get_bumpers_name nD') ℓ bumper).

Definition post_crash_at_loc_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ, own (get_at_locs_name nD) (◯ {[ ℓ ]}) -∗
    or_lost_post_crash_no_t ℓ (own (get_at_locs_name nD') (◯ {[ ℓ ]})).

Definition post_crash_na_loc_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ, own (get_na_locs_name nD) (◯ {[ ℓ ]}) -∗
    or_lost_post_crash_no_t ℓ (own (get_na_locs_name nD') (◯ {[ ℓ ]})).

Definition offsets_impl `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ℓ t, ℓ ↪[get_offset_name nD]□ t -∗
    or_lost_post_crash ℓ (λ tC, ℓ ↪[get_offset_name nD']□ (t + tC)).

(* We don't have a post crash rule for the physical history anymore, instead one
gets the physical history knowledge from knowing the full abstract history. *)
(* Definition map_map_phys_history_impl `{nvmG Σ} *)
(*            (nD nD' : nvmDeltaG) : iProp Σ := *)
(*   □ ∀ ℓ tStore msg, *)
(*     know_phys_hist_msg (nD := nD) ℓ tStore msg -∗ *)
(*       or_lost_post_crash_no_t ℓ ( *)
(*         ∃ v, know_phys_hist_msg (nD := nD') ℓ 0 (Msg v ∅ ∅ ∅) *)
(*       ). *)

Definition post_crash_na_view_map `{nvmG Σ}
           (na_views : gmap loc view) (nD nD' : nvmDeltaG) : iProp Σ :=
  (∀ ℓ q SV,
     ℓ ↪[get_na_views_name nD]{#q} SV -∗ ⌜ na_views !! ℓ = Some SV ⌝) ∗
  [∗ map] ℓ ↦ SV ∈ na_views,
    soft_disj
      (λ q, ℓ ↪[get_na_views_name nD]{#q} SV)
      (λ q, or_lost_post_crash_no_t ℓ (ℓ ↪[get_na_views_name nD']{#q} ∅)).

Instance know_na_view_post_crash_fractional `{nvmG Σ, nD : nvmDeltaG} ℓ :
  Fractional (λ q0 : Qp, or_lost_post_crash_no_t ℓ (ℓ ↪[get_na_views_name nD]{#q0} ∅)).
Proof. apply or_lost_post_crash_fractional. apply _. Qed.

Definition new_hist t (bumper : positive → option positive) (hist : gmap time positive) :=
  omap bumper (drop_above t hist).

Definition know_history_post_crash `{nvmG Σ}
           (hG : nvmDeltaG) ℓ q bumper (hist : gmap time positive) : iProp Σ :=
  or_lost_post_crash ℓ (λ t,
    ∃ t2 sOld sNew v,
      ⌜ hist !! t2 = Some sOld ⌝ ∗
      ⌜ bumper sOld = Some sNew ⌝ ∗
      ℓ ↪[crashed_in_name]□ sOld ∗
      ℓ ↪[offset_name]□ t2 ∗
      know_full_encoded_history_loc ℓ q (new_hist t2 bumper hist) ∗
      (* We could give the following two for the whole new history. *)
      know_frag_encoded_history_loc ℓ t2 sNew ∗
      know_phys_hist_msg ℓ t2 (Msg v ∅ ∅ ∅)
    )%I.

Instance know_history_post_crash_fractional `{nvmG Σ} hG ℓ bumper hist :
  Fractional (λ q, know_history_post_crash hG ℓ q bumper hist).
Proof.
  apply or_lost_post_crash_fractional.
  iIntros (t p q).
  iSplit.
  - iDestruct 1 as (??????) "(#? & #? & [L R] & #?)".
    iSplitL "L"; iExistsN; iFrame "#%∗".
  - iDestruct 1 as "[(% & % & % & % & % & % & #? & #off & L & #?)
                     (% & % & % & % & % & % & #? & #? & R & #?)]".
    simplify_eq.
    iDestruct (ghost_map_elem_agree with "off [$]") as %<-.
    iCombine "L R" as "F".
    iExistsN. iFrame "∗#%".
Qed.

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_full_history_map `{nvmG Σ}
           (hh : gmap loc (gmap time positive))
           (bb : gmap loc (positive → option positive))
           (nD nD' : nvmDeltaG) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ q hist,
     know_full_encoded_history_loc (nD := nD) ℓ q hist -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (∀ ℓ b, know_encoded_bumper (nD := nD) ℓ b -∗ ⌜bb !! ℓ = Some b⌝) ∗
  (* The map used to perform the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh, ∃ bumper,
    ⌜ bb !! ℓ = Some bumper ⌝ ∗
    soft_disj
      (λ q, know_full_encoded_history_loc (nD := nD) ℓ q hist)
      (λ q, know_history_post_crash nD' ℓ q bumper hist).

Definition crashed_in_mapsto `{nvmG Σ, nvmDeltaG} `{Countable ST} ℓ (s : ST) : iProp Σ :=
  ∃ es, ⌜ decode es = Some s ⌝ ∗ ℓ ↪[crashed_in_name]□ es.

Lemma crashed_in_mapsto_agree `{nvmG Σ, nvmDeltaG} `{Countable ST} ℓ (s1 s2 : ST) :
  crashed_in_mapsto ℓ s1 -∗ crashed_in_mapsto ℓ s2 -∗ ⌜ s1 = s2 ⌝.
Proof.
  iDestruct 1 as (? eq1) "pts1".
  iDestruct 1 as (? e2) "pts2".
  iDestruct (ghost_map_elem_agree with "pts1 pts2") as %->.
  iPureIntro. congruence.
Qed.

Definition post_crash_frag_history_impl `{hG : nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  □ ∀ ST (_ : EqDecision ST) (_ : Countable ST) (_ : AbstractState ST)
    ℓ (t offset : nat) (s : ST) (bumper : ST → ST),
      know_preorder_loc (nD := nD) ℓ (abs_state_relation (ST := ST)) -∗
      ℓ ↪[@offset_name (@nvm_delta_high nD)]□  offset -∗
      own_know_bumper (get_bumpers_name nD) ℓ bumper -∗
      know_frag_history_loc (nD := nD) ℓ t s -∗
      (or_lost_post_crash ℓ (λ tC, ∃ s2 v,
        crashed_in_mapsto ℓ s2 ∗
        know_frag_history_loc (nD := nD') ℓ (offset + tC) (bumper s2) ∗
        know_phys_hist_msg ℓ (offset + tC) (Msg v ∅ ∅ ∅) ∗
        (⌜ t ≤ offset + tC ⌝ -∗
          ⌜ s ⊑ s2 ⌝ ∗
          know_frag_history_loc (nD := nD') ℓ t (bumper s)))).

Definition post_crash_resource_persistent `{nvmG Σ}
           (nD nD' : nvmDeltaG) : iProp Σ :=
  "#post_crash_frag_history_impl" ∷ post_crash_frag_history_impl nD nD' ∗
  "#post_crash_preorder_impl" ∷ post_crash_preorder_impl nD nD' ∗
  "#post_crash_full_pred_impl" ∷ post_crash_full_pred_impl nD nD' ∗
  "#post_crash_read_pred_impl" ∷ post_crash_read_pred_impl nD nD' ∗
  "#post_crash_pers_pred_impl" ∷ post_crash_pers_pred_impl nD nD' ∗
  "#post_crash_at_loc_impl" ∷ post_crash_at_loc_impl nD nD' ∗
  "#post_crash_na_loc_impl" ∷ post_crash_na_loc_impl nD nD' ∗
  "#post_crash_offsets_impl" ∷ offsets_impl nD nD' ∗
  (* "#post_crash_map_map_phys_history_impl" ∷ map_map_phys_history_impl nD nD' ∗ *)
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

Program Definition post_crash `{nvmG Σ}
        (P : dProp Σ) : dProp Σ :=
  MonPred (λ i,
    let nD := i.2 in
    ∀ (hhGD' : nvmHighDeltaG) hh bb na_views,
      base_post_crash (λ nD',
        let nD' := NvmDeltaG nD' hhGD'
        in (post_crash_resource hh bb na_views nD nD') -∗
          ▷ P ((∅, ∅, ∅), nD') ∗
          (post_crash_resource_ephmeral hh bb na_views nD nD')))%I
    _.
Next Obligation.
  intros ??? [TV1 gnames] [TV2 ?] [? [= <-]].
  solve_proper.
Qed.

Notation "'<PC>' P" := (post_crash P)
  (at level 200, right associativity) : bi_scope.

(** Tiny shortcut for introducing the assumption for a [post_crash]. *)
Ltac iIntrosPostCrash := iIntros (hG' hh bb na_views).

Class IntoCrash {Σ} `{nvmG Σ} (P : dProp Σ) (Q : dProp Σ) :=
  into_crash : P ⊢ post_crash (Σ := Σ) Q.

Arguments IntoCrash {_} {_} _%I _%I.

Section post_crash_prop.
  Context `{nvmG Σ, nD: nvmDeltaG}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.

  Global Instance post_crash_objective P : ViewObjective (post_crash P).
  Proof.
    intros ???.
    iIntros "PC".
    iIntrosPostCrash.
    simpl.
    iDestruct ("PC" $! hG') as "P".
    iApply (post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    done.
  Qed.

  (* Lemma post_crash_intro Q: *)
  (*   (⊢ (∀ nG, Q nG)) → *)
  (*   ⊢ post_crash (λ nG, Q nG). *)
  (* Proof. *)
  (*   intros HQ. *)
  (*   iStartProof (iProp _). iIntros (TV'). *)
  (*   iIntrosPostCrash. *)
  (*   iApply post_crash_modality.post_crash_for_all. *)
  (*   iIntros (hD). *)
  (*   iIntros "[_ $]". *)
  (*   iNext. *)
  (*   iApply HQ. *)
  (* Qed. *)

  (** ** Structural rules *)

  Lemma post_crash_mono P Q :
    (P ⊢ Q) → post_crash P ⊢ post_crash Q.
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

  Global Instance post_crash_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) post_crash.
  Proof.
    intros ?? eq.
    apply (anti_symm _).
    - apply post_crash_mono. rewrite eq. done.
    - apply post_crash_mono. rewrite eq. done.
  Qed.

  Lemma post_crash_emp : emp ⊢ post_crash emp.
  Proof.
    iModel. iIntros "HP".
    iIntrosPostCrash.
    post_crash_modality.iCrash.
    iIntros "[_ $]". done.
  Qed.

  Lemma post_crash_sep P Q :
    post_crash P ∗ post_crash Q ⊢ <PC> (P ∗ Q).
  Proof.
    iModel.
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG' hh bb na_views) as "HP".
    iDestruct ("HQ" $! hG' hh bb na_views) as "HQ".
    post_crash_modality.iCrash.
    iIntros "[#M1 M2]".
    iDestruct ("HP" with "[$M1 $M2]") as "[$ M2]".
    iDestruct ("HQ" with "[$M1 $M2]") as "[$ $]".
  Qed.

  Lemma modality_post_crash_mixin :
    modality_mixin (@post_crash Σ _)
      (MIEnvClear) (MIEnvTransform IntoCrash).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, post_crash_emp,
      post_crash_mono, post_crash_sep.
  Qed.
  Definition modality_post_crash :=
    Modality _ modality_post_crash_mixin.

  Global Instance from_modal_post_crash P :
    FromModal True (modality_post_crash) (<PC> P) (<PC> P) P.
  Proof. by rewrite /FromModal. Qed.

  (* NOTE: This might be true, but we can't prove it. *)
  Lemma post_crash_intuitionistically_2 P :
    (□ <PC> P)%I ⊢ <PC> □ P.
  Proof. Abort.

  Lemma post_crash_disj P Q :
    post_crash P ∨ post_crash Q -∗ <PC> P ∨ Q.
  Proof.
    iStartProof (iProp _). iIntros ([TV i]).
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

  Lemma post_crash_pure (P : Prop) : P → ⊢ <PC> ⌜P⌝.
  Proof.
    iIntros (HP).
    iStartProof (iProp _). iIntros ([TV' ?]).
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "[H $]".
    iApply monPred_at_pure.
    iFrame "%".
  Qed.

  Lemma post_crash_nodep (P : dProp Σ) `{!Objective P} : P ⊢ <PC> P.
  Proof.
    iStartProof (iProp _). iIntros ([TV' ?]) "P".
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "[H $]".
    iApply (objective_at with "P").
  Qed.

  Lemma post_crash_named P name :
    named name (post_crash P) ⊢
    post_crash (named name P).
  Proof. rewrite //=. Qed.

End post_crash_prop.

Section post_crash_interact.
  Context `{nvmG Σ}.

  Context `{AbstractState ST}.

  (** ** The rules for the "special" assertions
  How the post crash modality interacts with the assertions in the logic. *)

  Lemma new_hist_encode_eq t bumper (abs_hist : gmap time ST) :
    new_hist t (encode_bumper bumper) (encode <$> abs_hist) =
      encode <$> (bumper <$> drop_above t abs_hist).
  Proof.
    rewrite /new_hist. rewrite /drop_above.
    apply map_eq. intros t'.
    rewrite lookup_omap.
    rewrite map_filter_lookup.
    rewrite !lookup_fmap.
    rewrite map_filter_lookup.
    destruct (abs_hist !! t'); simpl; last done.
    destruct (decide (t' ≤ t)).
    - rewrite !option_guard_True; try done.
      simpl.
      apply encode_bumper_encode.
    - rewrite !option_guard_False; done.
  Qed.

  Lemma post_crash_know_full_history_loc ℓ q (bumper : ST → ST)
        (abs_hist : gmap time ST) :
    know_bumper ℓ bumper ∗
    know_full_history_loc_d ℓ q abs_hist ⊢
    <PC> if_rec ℓ (∃ t' (s : ST) v,
        ⌜ abs_hist !! t' = Some s ⌝ ∗
        know_bumper ℓ bumper ∗
        crashed_in_mapsto_d ℓ s ∗
        with_gnames (λ nD, ⎡ ℓ ↪[offset_name]□ t' ⎤) ∗
        know_full_history_loc_d ℓ q (bumper <$> (drop_above t' abs_hist)) ∗
        with_gnames (λ nD, ⎡ know_frag_history_loc ℓ t' (bumper s) ⎤) ∗
        with_gnames (λ nD, ⎡ know_phys_hist_msg ℓ t' (Msg v ∅ ∅ ∅) ⎤)
      ).
   Proof.
     iModel. simpl.
     iIntros "[bumper hist]".
     rewrite 2!monPred_at_embed.
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
       rewrite /own_know_bumper.
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
       iDestruct "H" as (???) "(%v & %look & %bump & #crashedIn & #offset & hist & frag & phys)".
       iDestruct (or_lost_post_crash_lookup with "crashed newBumper") as "bumper";
         first done.
       apply lookup_fmap_Some in look as [st [eq ?]].
       apply encode_bumper_Some_decode in bump as (sn & decEq & encEq).
       simplify_eq.
       rewrite decode_encode in decEq.
       simplify_eq.
       iExists t. iFrame (cvLook) "per". iExists t2, sn, v.
       iSplitPure; first assumption.
       simpl.
       iFrameF "bumper".
       iSplit. { iExists _. iFrame "crashedIn". rewrite decode_encode. done. }
       iFrameF "offset".
       rewrite /full_entry_unenc /know_full_encoded_history_loc.
       rewrite new_hist_encode_eq.
       iFrame "hist phys".
       iExists _. iFrame "frag". iPureIntro. apply decode_encode. }
     rewrite /post_crash_resource.
     iFrame "post_crash_na_view_map". iFrame.
  Qed.

  Lemma post_crash_preorder ℓ :
    know_preorder_loc_d ℓ (abs_state_relation (ST := ST)) ⊢
    post_crash (if_rec ℓ (know_preorder_loc_d ℓ (abs_state_relation (ST := ST) )))%I.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    iDestruct ("post_crash_preorder_impl" with "HP") as "H".
    iNext.
    rewrite /know_preorder_loc_d.
    iApply or_lost_if_rec_with_names_embed. iFrame.
  Qed.

  Lemma post_crash_frag_history ℓ t offset bumper (s : ST) :
    know_preorder_loc_d ℓ (abs_state_relation (ST := ST)) -∗
    offset_loc ℓ offset -∗
    know_bumper ℓ bumper -∗
    know_frag_history_loc_d ℓ t s -∗
    post_crash (
      (if_rec ℓ (∃ sC CV tC v,
        ⌜ CV !! ℓ = Some (MaxNat tC) ⌝ ∗
        crashed_at_d CV ∗
        crashed_in_mapsto_d ℓ sC ∗
        know_frag_history_loc_d ℓ (offset + tC) (bumper sC) ∗
        with_gnames (λ nD, ⎡ know_phys_hist_msg ℓ (offset + tC) (Msg v ∅ ∅ ∅) ⎤) ∗
        (⌜ t ≤ offset + tC ⌝ -∗
          ⌜ s ⊑ sC ⌝ ∗ with_gnames (λ nD, ⎡ know_frag_history_loc ℓ t (bumper s) ⎤))))).
  Proof.
    iModel.
    iIntros "order".
    iIntros ([??] [? [= <-]]) "offset".
    iIntros ([??] [? [= <-]]) "bumper".
    iIntros ([??] [? [= <-]]) "hist".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "order") as "order".
    iDestruct (base.post_crash_modality.post_crash_nodep with "offset") as "offset".
    iDestruct (base.post_crash_modality.post_crash_nodep with "bumper") as "bumper".
    iDestruct (base.post_crash_modality.post_crash_nodep with "hist") as "hist".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    iDestruct ("post_crash_frag_history_impl" $! ST with "order offset bumper hist") as "hist".
    iApply or_lost_if_rec_at.
    iApply (or_lost_post_crash_mono with "[] hist").
    iIntros (tC ?) "(? & crashed & %cvLook) impl".
    iDestruct "impl" as (s2 v) "(#crashedIn & hist & physHist & impl)".
    monPred_simpl. iExists (s2).
    monPred_simpl. iExists (CV).
    monPred_simpl. iExists (tC).
    monPred_simpl. iExists (v).
    iSplitPure. { done. }
    simpl.
    iFrame.
    iFrameF "crashedIn".
    iIntros ([??] [? [= <-]]).
    simpl. rewrite monPred_at_embed.
    iApply "impl".
  Qed.

  Lemma post_crash_know_full_pred `{Countable ST} ℓ (ϕ : ST → val → dProp Σ) :
    know_full_pred_d ℓ ϕ ⊢ <PC> if_rec ℓ (know_full_pred_d ℓ ϕ).
  Proof.
    iModel.
    iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_full_pred_impl" with "HP") as "H".
    iNext.
    iApply or_lost_if_rec_with_names_embed. iFrame.
  Qed.

  Lemma post_crash_know_read_pred `{Countable ST} ℓ (ϕ : ST → val → dProp Σ) :
    know_read_pred_d ℓ ϕ ⊢ <PC> if_rec ℓ (know_read_pred_d ℓ ϕ).
  Proof.
    iModel.
    iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_read_pred_impl" with "HP") as "H".
    iNext.
    iApply or_lost_if_rec_with_names_embed. iFrame.
  Qed.

  Lemma post_crash_know_pers_pred `{Countable ST} ℓ (ϕ : ST → val → dProp Σ) :
    know_pers_pred_d ℓ ϕ ⊢ <PC> if_rec ℓ (know_pers_pred_d ℓ ϕ).
  Proof.
    iModel.
    iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_pers_pred_impl" with "HP") as "H".
    iNext.
    iApply or_lost_if_rec_with_names_embed. iFrame.
  Qed.

  Lemma post_crash_at_loc ℓ :
    is_at_loc ℓ ⊢ <PC> if_rec ℓ (is_at_loc ℓ).
  Proof.
    iModel. iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource.
    iDestruct ("post_crash_at_loc_impl" with "HP") as "H".
    iApply or_lost_if_rec_with_names_embed. iFrame.
  Qed.

  Lemma post_crash_na_loc ℓ :
    is_na_loc ℓ ⊢ <PC> if_rec ℓ (is_na_loc ℓ).
  Proof.
    iModel. iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_na_loc_impl" with "HP") as "H".
    iApply or_lost_if_rec_with_names_embed. iFrame.
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
    offset_loc ℓ tO ⊢
    <PC> if_rec ℓ (∃ tC CV, ⌜ CV !! ℓ = Some (MaxNat tC) ⌝ ∗
                               crashed_at_d CV ∗
                               offset_loc ℓ (tO + tC)).
  Proof.
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
    iApply or_lost_post_crash_mono; last iApply "H".
    iIntros (t CV).
    iNamed 1. iIntros "O".
    iExists _.
    rewrite /crashed_at_d. rewrite /offset_loc. rewrite !lift_d_at.
    iFrame (cvLook) "crashed O".
  Qed.

  (*
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
  *)

  Lemma post_crash_know_na_view ℓ q SV :
    know_na_view ℓ q SV ⊢ <PC> if_rec ℓ (know_na_view ℓ q ∅).
  Proof.
    iModel. iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha Hb]". iNamed "Ha". iNamed "Hb".
    iDestruct "post_crash_na_view_map" as "[in M]".
    iAssert (⌜ na_views !! _ = Some _ ⌝)%I as %HI. { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[H reIns]"; first done.
    rewrite monPred_at_embed.
    iDestruct (soft_disj_exchange_l with "[] H HP") as "[H HP]".
    { iIntros "!>" (?) "H".
      setoid_rewrite <- dfrac_valid_own.
      iApply (ghost_map_elem_valid with "H"). }
    rewrite -or_lost_if_rec_with_names_embed.
    iFrame "HP".
    iFrame "post_crash_full_history_map".
    iDestruct ("reIns" with "H") as "$".
    iFrame "in".
  Qed.

  Lemma post_crash_know_bumper `{AbstractState ST} ℓ (bumper : ST → ST) :
    know_bumper ℓ bumper ⊢ <PC> if_rec ℓ (know_bumper ℓ bumper).
  Proof.
    iModel. iIntros "HP".
    iIntrosPostCrash.
    iDestruct (base.post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[Ha $]". iNamed "Ha".
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_bumper_impl" with "HP") as "H".
    rewrite -or_lost_if_rec_with_names_embed.
    iFrame.
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

Section IntoCrash.
  Context `{nvmG Σ}.

  (* Arguments IntoCrash {_} {_} {_} _%I hi%I. *)

  Global Instance sep_into_crash (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∗ Q)%I (P' ∗ Q')%I.
  Proof.
    rewrite /IntoCrash.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply (post_crash_sep). iFrame.
  Qed.

  Global Instance pure_into_crash (P : Prop) :
    IntoCrash (⌜ P ⌝) (⌜ P ⌝)%I.
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Lemma into_crash_proper P P' Q Q':
    IntoCrash P Q →
    (P ⊣⊢ P') →
    (Q ⊣⊢ Q') →
    IntoCrash P' Q'.
  Proof.
    rewrite /IntoCrash.
    iIntros (HD Hwand1 Hwand2) "HP".
    iApply post_crash_mono; last first.
    { iApply HD. iApply Hwand1. eauto. }
    intros. simpl. by rewrite Hwand2.
  Qed.

  Global Instance big_sepM_into_crash `{Countable K} :
    ∀ (A : Type) Φ (Ψ : K → A → dProp Σ) (m : gmap K A),
    (∀ (k : K) (x : A), IntoCrash (Φ k x) (Ψ k x)) →
    IntoCrash ([∗ map] k↦x ∈ m, Φ k x)%I ([∗ map] k↦x ∈ m, Ψ k x)%I.
  Proof.
    intros. induction m using map_ind.
    - eapply (into_crash_proper True%I _ True%I).
      * apply _.
      * rewrite big_sepM_empty. apply bi.True_emp.
      * intros. rewrite big_sepM_empty. apply bi.True_emp.
    - eapply (into_crash_proper (Φ i x ∗ [∗ map] k↦x0 ∈ m, Φ k x0) _
                                ((Ψ i x ∗ [∗ map] k↦x0 ∈ m, Ψ k x0)%I)).
      * apply _.
      * rewrite big_sepM_insert //=.
      * intros. rewrite big_sepM_insert //=.
  Qed.

  Global Instance lifted_embed_nodep_into_crash (P : iProp Σ) :
    IntoCrash (⎡ P ⎤) (⎡ P ⎤)%I | 1000.
  Proof. apply: post_crash_nodep. Qed.

  Global Instance lifted_embed_into_crash (P : iProp Σ) Q :
    (∀ (nD : nvmDeltaG), base.post_crash_modality.IntoCrash P Q) →
    IntoCrash (⎡ P ⎤) (with_gnames (λ nD, ⎡ Q _ ⎤))%I.
  Proof.
    rewrite /IntoCrash.
    intros hyp.
    iModel.
    iIntros "?".
    iIntrosPostCrash.
    post_crash_modality.iCrash.
    iIntros "[_ $]". done.
  Qed.

  Tactic Notation "lift_into_crash" uconstr(lem) :=
    rewrite /IntoCrash; iIntros "P"; by iApply lem.

  Global Instance emp_into_crash : IntoCrash emp emp.
  Proof. lift_into_crash post_crash_emp. Qed.

  Global Instance disj_into_crash (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoCrash P P' → IntoCrash Q Q' → IntoCrash (P ∨ Q)%I (P' ∨ Q')%I.
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

  (* Global Instance later_into_crash_flush P P' : *)
  (*   IntoCrash P P' → *)
  (*   IntoCrash (▷ P) (▷ P'). *)
  (* Proof. *)
  (*   intros (?). *)
  (*   rewrite /IntoCrash. *)
  (*   iModel. *)
  (*   iIntros "H". *)
  (* Qed. *)

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (Ψ x)) →
    IntoCrash (∃ x, Φ x)%I ((∃ x, Ψ x)%I).
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

  (* NOTE: We don't have an instance for [know_frag_history_loc] due to the
   * extra assumptions for the post crash behavior that makes such an instance
   * impractical. *)
  (* Global Instance frag_history_into_crash `{AbstractState ST} *)
  (*        ℓ bumper t offset (s : ST) : IntoCrash _ _ := *)
  (*   post_crash_frag_history ℓ bumper t offset s. *)

  Global Instance know_full_pred_into_crash `{Countable ST}
         ℓ (ϕ : ST → _ → dProp Σ) :
    IntoCrash _ _ := post_crash_know_full_pred ℓ ϕ.

  Global Instance know_read_pred_into_crash `{Countable ST}
         ℓ (ϕ : ST → _ → dProp Σ) :
    IntoCrash _ _ := post_crash_know_read_pred ℓ ϕ.

  Global Instance know_pers_pred_into_crash `{Countable ST}
         ℓ (ϕ : ST → _ → dProp Σ) :
    IntoCrash _ _ := post_crash_know_pers_pred ℓ ϕ.

  Global Instance at_loc_into_crash ℓ : IntoCrash _ _ := post_crash_at_loc ℓ.

  Global Instance na_loc_into_crash ℓ :
    IntoCrash _ _ := post_crash_na_loc ℓ.

  Global Instance offset_into_crash ℓ t :
    IntoCrash _ _ := post_crash_offset ℓ t.

  (* Global Instance know_phys_hist_msg_into_crash ℓ t msg : *)
  (*   IntoCrash _ _ := post_crash_know_phys_hist_msg ℓ t msg. *)

  Global Instance exclusive_know_na_view_crash ℓ q SV :
    IntoCrash _ _ := post_crash_know_na_view ℓ q SV.

  Global Instance know_bumper_into_crash `{AbstractState ST} ℓ (bumper : ST → ST) :
    IntoCrash _ _ := post_crash_know_bumper ℓ bumper.

  Global Instance post_crash_into_crash P : IntoCrash (<PC> P) P.
  Proof. done. Qed.

End IntoCrash.

Section post_crash_derived.
  Context `{nvmG Σ}.

  Context `{AbstractState ST}.

  Lemma post_crash_persisted_d PV :
    persisted_d PV ⊢
    <PC> (persisted_d (view_to_zero PV) ∗ ∃ CV, ⌜ PV ⊑ CV ⌝ ∗ crashed_at_d CV).
  Proof.
    iModel.
    simpl.
    rewrite monPred_at_embed.
    iIntros "P".
    iIntrosPostCrash.
    base.post_crash_modality.iCrash.
    iIntros "[_ $]".
    iNext.
    simpl.
    monPred_simpl.
    simpl.
    rewrite monPred_at_embed.
    iDestruct "P" as "[$ (%CV & ho)]".
    iExists (CV).
    monPred_simpl.
    simpl.
    monPred_simpl.
    iFrame.
  Qed.

  Global Instance into_crash_persisted_d PV :
    IntoCrash _ _ := post_crash_persisted_d PV.

  Lemma post_crash_persisted_loc_d ℓ t :
    persisted_loc_d ℓ t ⊢
    <PC> (
      persisted_loc_d ℓ 0 ∗
      ∃ CV t', ⌜ CV !! ℓ = Some (MaxNat t') ∧ t ≤ t' ⌝ ∗ crashed_at_d CV)%I.
  Proof.
    iIntros "P".
    iDestruct (post_crash_persisted_d with "P") as "P".
    iApply (post_crash_mono with "P").
    rewrite view_to_zero_singleton.
    iIntros "[$ M]".
    setoid_rewrite view_le_singleton.
    setoid_rewrite bi.pure_exist.
    setoid_rewrite bi.sep_exist_r.
    done.
  Qed.

  Global Instance into_crash_persisted_loc_d ℓ t :
    IntoCrash _ _ := post_crash_persisted_loc_d ℓ t.

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

(* Definition post_crash_flush `{nvmG Σ} *)
(*         (P : dProp Σ) : dProp Σ := *)
(*     <PC> (P nD'). *)
(* Definition post_crash_flush `{nvmG Σ, nvmDeltaG} *)
(*         (P : nvmDeltaG → dProp Σ) : dProp Σ := *)
(*   (∀ TV, monPred_in TV -∗ *)
(*     <PC> (nD' : nvmDeltaG), *)
(*       ∀ (CV : view), *)
(*         ⌜ flush_view TV ⊑ CV ⌝ -∗ *)
(*         ⎡ crashed_at CV ⎤ -∗ *)
(*         P nD')%I. *)
(* Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed. *)

Program Definition post_crash_flush {Σ} `{nvmG Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ i,
    (<PC>
      ∀ (CV : view),
        ⌜ flush_view i.1 ⊑ CV ⌝ ∗
        persisted_d (view_to_zero (flush_view i.1)) ∗
        crashed_at_d CV -∗
        P) (∅, ∅, ∅, i.2))%I _.
Next Obligation.
  intros ??? [??] [??] [? [= ->]].
  apply post_crash_mono.
  solve_proper.
Qed.

Class IntoCrashFlush {Σ} `{nvmG Σ}
      (P : dProp Σ) (Q : dProp Σ) :=
  into_crash_flushed : P ⊢ post_crash_flush (Σ := Σ) Q.

Arguments IntoCrashFlush {_} {_} _%I _%I.

(*
Program Definition post_crash_flush `{hG : !nvmG Σ, nvmDeltaG}
        (P : nvmG Σ, nvmDeltaG → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (post_crash (λ hG', ∃ CV, ⌜flush_view TV ⊑ CV⌝ ∗ ⎡crashed_at CV⎤ -∗ P hG')) TV
  )%I _.
Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed.
*)

Notation "'<PCF>' P" :=
  (post_crash_flush P)
  (at level 200, right associativity) : bi_scope.

Section post_crash_persisted.
  Context `{hG: !nvmG Σ}.

  Lemma post_crash_flush_post_crash P :
    post_crash P ⊢ post_crash_flush P.
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
    named name (post_crash_flush P) ⊢
    post_crash_flush (named name P).
  Proof. rewrite //=. Qed.

  Lemma post_crash_flush_sep `{nvmG Σ} P Q :
    post_crash_flush P ∗ post_crash_flush Q ⊢ <PCF> P ∗ Q.
  Proof.
    iModel.
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
    post_crash_flush P ∨ post_crash_flush Q -∗ <PCF> P ∨ Q.
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
      iIntros ([TV'' ?] [le [= <-]]) "(%flushLe & #pers & #crashedAt)".
      simpl.
      monPred_simpl.
      iLeft.
      iSpecialize ("HP" $! (TV'', _) with "[%] [pers crashedAt]").
      { done. }
      { monPred_simpl. simpl. rewrite !monPred_at_embed.
        iFrame "#". done. }
      iFrame "HP".
    - iIntrosPostCrash.
      iDestruct ("HP" $! hG' hh bb na_views) as "HP".
      base.post_crash_modality.iCrash.
      iIntros "[#RP RE]".
      iDestruct ("HP" with "[$RP $RE]") as "[HP $]".
      iNext.
      iIntros (CV).
      iSpecialize ("HP" $! CV).
      iIntros ([TV'' ?] [le [= <-]]) "(%flushLe & #pers & #crashedAt)".
      simpl.
      monPred_simpl.
      iSpecialize ("HP" $! (TV'', _) with "[%] [pers crashedAt]").
      { done. }
      { monPred_simpl. simpl. rewrite !monPred_at_embed.
        iFrame "#". done. }
      iRight. iFrame "HP".
  Qed.

  (* This lemma is not true for the <PCF> modality. *)
  Global Instance post_crash_flush_objective P : ViewObjective (<PCF> P).
  Proof. Abort.

  Lemma post_crash_flush_mono P Q :
    (P ⊢ Q) → post_crash_flush P ⊢ post_crash_flush Q.
  Proof.
    intros mono.
    iModel.
    iIntros "HP".
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
    iDestruct (mono with "P") as "H".
    done.
  Qed.

  Global Instance post_crash_flush_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (post_crash_flush).
  Proof.
    intros ?? eq.
    apply (anti_symm _).
    - apply post_crash_flush_mono. rewrite eq. done.
    - apply post_crash_flush_mono. rewrite eq. done.
  Qed.

  Lemma post_crash_flush_emp : emp ⊢ post_crash_flush emp.
  Proof.
    rewrite -post_crash_flush_post_crash. apply post_crash_emp.
  Qed.

  Lemma modality_post_crash_flush_mixin :
    modality_mixin (@post_crash_flush Σ _)
      (MIEnvClear) (MIEnvTransform IntoCrashFlush).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, post_crash_flush_emp,
      post_crash_flush_mono, post_crash_flush_sep.

    (* intros P Q. rewrite /IntoCrash. => ->. *)
    (* by rewrite post_crash_flush_intuitionistically_2. *)
  Qed.
  Definition modality_post_crash_flush :=
    Modality _ modality_post_crash_flush_mixin.

  Global Instance from_modal_post_crash_flush P :
    FromModal True (modality_post_crash_flush) (<PCF> P) (<PCF> P) P.
  Proof. by rewrite /FromModal. Qed.

  Lemma post_crash_flush_pure (P : Prop) : P → ⊢ <PCF> ⌜P⌝.
    rewrite -post_crash_flush_post_crash. apply post_crash_pure.
  Qed.

  Lemma post_crash_flush_nodep P `{!Objective P} :
    P ⊢ <PCF> P.
  Proof. rewrite -post_crash_flush_post_crash. apply: post_crash_nodep. Qed.

  Lemma post_crash_have_FV_strong ℓ t :
    have_FV_strong ℓ t ⊢
    <PCF>
      persisted_d {[ ℓ := MaxNat 0 ]} ∗
      ∃ CV t', ⌜CV !! ℓ = Some (MaxNat t') ∧ t ≤ t'⌝ ∗ crashed_at_d CV.
  Proof.
    iModel. iIntros "le". simpl.
    iIntros (nD hh bb na_views).
    base.post_crash_modality.iCrash.
    destruct (TV) as [[??]?].
    iDestruct "le" as %[[? le] ?].
    iIntros "[_ $] !>" (CV).
    monPred_simpl. simpl.
    iIntros ([??] [? [= <-]]) "(%le2 & pers & crashed)".
    monPred_simpl.
    simpl.
    rewrite monPred_at_embed.
    iDestruct (persisted_persisted_loc with "[$]") as "$".
    { apply view_le_singleton in le as (t2 & look & ?).
      eapply view_to_zero_lookup. done. }
    pose proof (transitivity le le2) as le3.
    apply view_le_singleton in le3 as (? & look & ?).
    iExists _, _. iFrame "crashed". done.
  Qed.

End post_crash_persisted.

Section IntoCrashFlush.
  Context `{nvmG Σ}.

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
    IntoCrashFlush (⌜ P ⌝) (⌜ P ⌝)%I.
  Proof. apply into_crash_into_crash_flushed. apply _. Qed.

  Global Instance lifted_embed_nodep_into_crash_flush (P : iProp Σ) :
    IntoCrashFlush (⎡ P ⎤) (⎡ P ⎤)%I | 1000.
  Proof. apply into_crash_into_crash_flushed. apply _. Qed.

  (* Global Instance lifted_embed_into_crash_flush (P : iProp Σ) Q : *)
  (*   base.post_crash_modality.IntoCrash P Q → *)
  (*   IntoCrashFlush (⎡ P ⎤) (⎡ Q ⎤)%I. *)
  (* Proof. intros ?. apply into_crash_into_crash_flushed. apply _. Qed. *)

  Global Instance emp_into_crash_flush : IntoCrashFlush emp emp.
  Proof. apply: into_crash_into_crash_flushed. Qed.

  Global Instance sep_into_crash_flush (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoCrashFlush P P' →
    IntoCrashFlush Q Q' →
    IntoCrashFlush (P ∗ Q)%I (P' ∗ Q')%I.
  Proof.
    rewrite /IntoCrashFlush.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply (post_crash_flush_sep).
    iFrame.
  Qed.

  Global Instance disj_into_crash_flush (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoCrashFlush P P' →
    IntoCrashFlush Q Q' →
    IntoCrashFlush (P ∨ Q)%I (P' ∨ Q')%I.
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

  Global Instance if_else_into_crash_flush (b : bool) P P' Q Q' :
    IntoCrashFlush P P' →
    IntoCrashFlush Q Q' →
    IntoCrashFlush (if b then P else Q) (if b then P' else Q').
  Proof. intros ??. destruct b; apply _. Qed.

  (* Global Instance later_into_crash_flush P P' : *)
  (*   IntoCrashFlush P P' → *)
  (*   IntoCrashFlush (▷ P) (▷ P'). *)
  (* Proof. *)
  (* Qed. *)

  Global Instance have_FV_strong_into_crash_flush ℓ t :
    IntoCrashFlush _ _ := post_crash_have_FV_strong ℓ t.

  Global Instance exist_into_crash_flush {A} Φ Ψ:
    (∀ x : A, IntoCrashFlush (Φ x) (Ψ x)) →
    IntoCrashFlush (∃ x, Φ x) (∃ x, Ψ x).
  Proof.
    rewrite /IntoCrashFlush.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (post_crash_flush_mono with "HΦ"). auto.
  Qed.

  Global Instance big_sepL_into_crash_flush {A} ϕ ψ l :
    (∀ k (x : A), IntoCrashFlush (ϕ k x) (ψ k x)) →
    IntoCrashFlush ([∗ list] k↦x ∈ l, ϕ k x)%I ([∗ list] k↦x ∈ l, ψ k x)%I.
  Proof. revert ϕ ψ. induction l as [|x l IH]=> Φ ψ ? /=; apply _. Qed.

  Global Instance offset_into_crash_flush ℓ t : IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (offset_into_crash ℓ t).

  Global Instance know_full_pred_into_crash_flush `{Countable ST}
         ℓ (ϕ : ST → _ → _) :
    IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (know_full_pred_into_crash ℓ ϕ).

  Global Instance know_read_pred_into_crash_flush `{Countable ST}
         ℓ (ϕ : ST → _ → _) :
    IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (know_read_pred_into_crash ℓ ϕ).

  Global Instance know_pers_pred_into_crash_flush `{Countable ST}
         ℓ (ϕ : ST → _ → _) :
    IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (know_pers_pred_into_crash ℓ ϕ).

  Global Instance post_crash_flush_into_crash_flush P : IntoCrashFlush (<PCF> P) P.
  Proof. done. Qed.

  Global Instance post_crash_into_crash_flush P : IntoCrashFlush (<PC> P) P.
  Proof. apply into_crash_into_crash_flushed. done. Qed.

  Global Instance lifted_persisted_d_into_crash_flush PV :
    IntoCrashFlush _ _%I :=
    into_crash_into_crash_flushed _ _ (into_crash_persisted_d PV).

  Global Instance lifted_persisted_loc_d_into_crash_flush ℓ t :
    IntoCrashFlush _ _%I :=
    into_crash_into_crash_flushed _ _ (into_crash_persisted_loc_d ℓ t).

End IntoCrashFlush.

Section post_crash_flush_test.
  Context `{nvmG Σ}.

  Lemma foo P `{Countable ST'} ℓ (ϕ : ST' → val → dProp Σ) t :
    ⌜ P ⌝ -∗
    know_full_pred_d ℓ ϕ -∗
    persisted_loc_d ℓ t -∗
    <PCF> ⌜ P ⌝ ∗ if_rec ℓ (know_full_pred_d ℓ ϕ).
  Proof.
    iIntros "P pred pers".
    iModIntro.
    iFrame.
  Qed.

End post_crash_flush_test.

Typeclasses Opaque post_crash.
Typeclasses Opaque post_crash_flush.

(* Since the post crash modality does not satisfy
   [post_crash_intuitionistically_2] the [iModIntro] tactic clears the
   intuitionistic context when introducing the post crash modality. This is quite
   unfortunate. To improve the situation we define [iCrashIntro] which improves on
   this by moving the entire intuitionistic context into the spatial context before
   introducing the post crash modality.

   The tactic works both with <PC> and with <PCF>.
 *)

From iris.bi Require Import bi.
Import bi.
From iris.proofmode Require Import tactics environments intro_patterns monpred.

Section intuit_to_spatial.
  Context {PROP : bi}.

  Implicit Types Γ Γp Γs : env PROP.
  Implicit Types Δ : envs PROP.
  Implicit Types P Q : PROP.

  (* Lemma envs_clear_spatial_sound Δ : *)
  (*   of_envs Δ ⊢ of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ. *)
  (* Proof. *)
  (*   rewrite !of_envs_eq /envs_clear_spatial /=. apply pure_elim_l=> Hwf. *)
  (*   rewrite -persistent_and_sep_assoc. apply and_intro. *)
  (*   - apply pure_intro. destruct Hwf; constructor; simpl; auto using Enil_wf. *)
  (*   - rewrite -persistent_and_sep_assoc. rewrite left_id. done. *)
  (* Qed. *)

  Lemma envs_clear_intuitionistic_sound Δ :
    of_envs Δ ⊢
    env_and_persistently (env_intuitionistic Δ) ∗ of_envs (envs_clear_intuitionistic Δ).
  Proof.
    rewrite !of_envs_eq /envs_clear_spatial /=. apply pure_elim_l=> Hwf.
    rewrite persistent_and_sep_1.
    rewrite (pure_True); first by rewrite !left_id.
    destruct Hwf. constructor; simpl; auto using Enil_wf.
  Qed.

  Lemma big_opL_and_sep (l : env PROP) : □ [∧] l -∗ [∗] l.
  Proof.
    iInduction (l) as [|??] "IH"; simpl; first done.
    iIntros "#[$ ?]". iApply "IH". done.
  Qed.

  Lemma big_opL_env_and_sep `{BiAffine PROP} (l : env PROP) :
    env_and_persistently l ⊢ [∗] l.
  Proof.
    iInduction (l) as [|??] "IH"; simpl; first done.
    iIntros "[#$ ?]". iApply "IH". done.
  Qed.

  Definition envs_intuitionistic_to_spatial {PROP} (Δ : envs PROP) : option (envs PROP) :=
    envs_app false (env_intuitionistic Δ) (envs_clear_intuitionistic Δ).

  Lemma envs_intuitionistic_to_spatial_sound `{BiAffine PROP} Δ Δ' P :
    envs_intuitionistic_to_spatial Δ = Some Δ' →
    envs_entails Δ' P →
    envs_entails Δ P.
  Proof.
    rewrite /envs_intuitionistic_to_spatial.
    intros eq.
    rewrite envs_entails_unseal.
    intros <-.
    apply envs_app_sound in eq.
    apply wand_elim_l' in eq.
    rewrite <- eq.
    rewrite envs_clear_intuitionistic_sound.
    iIntros "[? $]".
    rewrite -big_opL_env_and_sep.
    done.
  Qed.

End intuit_to_spatial.

(* Moves the intuitionistic context to the spatial context. *)
Tactic Notation "iIntuitToSpatial" :=
  eapply envs_intuitionistic_to_spatial_sound;
    [ done
    | cbv [ env_spatial ]].

Tactic Notation "iCrashIntro" := iIntuitToSpatial; iModIntro.
