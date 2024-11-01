From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From iris.bi Require Import monpred.
From self.nextgen Require Export nextgen_promises.
From self.base Require Import generational_resources primitive_laws.
From self.high Require Import dprop monpred_simpl.
From self.high.modalities Require Import nextgen.

From self.algebra Require Import view.

Program Definition nextgen_flush `{nvmBaseG} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (<NG>
      ∀ (CV : view),
        ⌜ flush_view TV ⊑ CV ⌝ ∗
        ⎡ persisted (view_to_zero (flush_view TV)) ⎤ ∗
        ⎡ crashed_at CV ⎤ -∗
        P) (∅, ∅, ∅))%I _.
Next Obligation.
  intros ???????.
  apply nextgen_mono.
  solve_proper.
Qed.

Class IntoNGFlush `{nvmBaseG}
      (P : dProp Σ) (Q : dProp Σ) :=
  into_nextgen_flushed : P ⊢ nextgen_flush (Σ := Σ) Q.

Arguments IntoNGFlush {_ _ _} _%I _%I.

Notation "'<NGF>' P" :=
  (nextgen_flush P)
  (at level 200, right associativity) : bi_scope.

Section nextgen_persisted.
  Context `{nvmBaseG}.

  Lemma nextgen_flush_nextgen P :
    nextgen P ⊢ nextgen_flush P.
  Proof.
    iStartProof (iProp _).
    iIntros (TV) "P".
    rewrite /nextgen_flush.
    rewrite /nextgen.
    simpl.
    iModIntro.
    iIntros (CV TV') "% not_lost".
    iApply monPred_mono; done.
  Qed.

  Lemma nextgen_flush_named P name :
    named name (nextgen_flush P) ⊢
    nextgen_flush (named name P).
  Proof. rewrite //=. Qed.

  Lemma nextgen_flush_sep P Q :
    nextgen_flush P ∗ nextgen_flush Q ⊢ <NGF> P ∗ Q.
  Proof.
    iModel.
    iIntros "(HP & HQ)".
    rewrite /nextgen_flush //=.
    iModIntro.
    iIntros (CV TV') "% #not_lost".
    iDestruct ("HP" $! CV with "[$]") as "HP".
    iDestruct ("HQ" $! CV with "[$]") as "HQ".
    iSplitL "HP"; iApply monPred_mono; done.
  Qed.

  Lemma nextgen_flush_disj P Q :
    nextgen_flush P ∨ nextgen_flush Q -∗ <NGF> P ∨ Q.
  Proof.
    iModel.
    rewrite /nextgen_flush //=.
    iIntros "[HP | HQ]"; iModIntro; iIntros (CV TV') "% #not_lost".
    - iDestruct ("HP" $! CV with "[$]") as "HP".
      iLeft.
      iApply monPred_mono; done.
    - iDestruct ("HQ" $! CV with "[$]") as "HQ".
      iRight.
      iApply monPred_mono; done.
  Qed.

  Lemma nextgen_flush_mono P Q :
    (P ⊢ Q) → nextgen_flush P ⊢ nextgen_flush Q.
  Proof.
    intros mono.
    iModel.
    rewrite /nextgen_flush //=.
    iApply nextgen_promises_model.nextgen_mono.
    iIntros "HP" (CV TV') "% #not_lost".
    iDestruct ("HP" $! CV with "[$]") as "HP".
    iApply mono.
    iApply monPred_mono; done.
  Qed.

  Global Instance nextgen_flush_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (nextgen_flush).
  Proof.
    intros ?? eq.
    apply (anti_symm _).
    - apply nextgen_flush_mono. rewrite eq. done.
    - apply nextgen_flush_mono. rewrite eq. done.
  Qed.

  Lemma nextgen_flush_emp : emp ⊢ nextgen_flush emp.
  Proof.
    rewrite -nextgen_flush_nextgen. by iIntros "_ !>".
  Qed.

  Lemma modality_nextgen_flush_mixin :
    modality_mixin (@nextgen_flush Σ _ _)
      (MIEnvClear) (MIEnvTransform IntoNGFlush).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, nextgen_flush_emp,
      nextgen_flush_mono, nextgen_flush_sep.

    (* intros P Q. rewrite /IntoNextgen. => ->. *)
    (* by rewrite nextgen_flush_intuitionistically_2. *)
  Qed.
  Definition modality_nextgen_flush :=
    Modality _ modality_nextgen_flush_mixin.

  Global Instance from_modal_nextgen_flush P :
    FromModal True (modality_nextgen_flush) (<NGF> P) (<NGF> P) P.
  Proof. by rewrite /FromModal. Qed.

  Lemma nextgen_flush_pure (P : Prop) : P → ⊢ <NGF> ⌜P⌝.
    rewrite -nextgen_flush_nextgen. by iIntros (?) "!>".
  Qed.

  Lemma nextgen_have_FV_strong ℓ t :
    have_FV_strong ℓ t ⊢
    <NGF>
      ⎡ persisted {[ ℓ := MaxNat 0 ]} ⎤ ∗
      ∃ CV t', ⌜CV !! ℓ = Some (MaxNat t') ∧ t ≤ t'⌝ ∗ ⎡ crashed_at CV ⎤.
  Proof.
    iModel. iIntros "le". simpl.
    iModIntro.
    iIntros (CV TV') "% (% & #? & #?)".
    destruct (TV) as [[??]?].
    iDestruct "le" as %[[? le] ?].
    iDestruct (persisted_persisted_loc with "[$]") as "$".
    { apply view_le_singleton in le as (t2 & look & ?).
      eapply view_to_zero_lookup. done. }
    iExists CV. iFrame "#".
    iPureIntro.
    apply view_le_singleton.
    etrans; done.
  Qed.
End nextgen_persisted.

Section IntoNGFlush.
  Context `{nvmBaseG}.

  (* This is not an instance as it would probably have a negative impact on the
  performance of type class resolution. *)
  (* TODO (Yixuan): verify performance *)
  Global Instance into_crash_into_crash_flushed P Q :
    IntoNextgen P Q →
    IntoNGFlush P Q.
  Proof.
    rewrite /IntoNGFlush /IntoNextgen.
    rewrite -nextgen_flush_nextgen.
    done.
  Qed.

  (* Global Instance pure_into_crash_flushed (P : Prop) : *)
  (*   IntoNGFlush (⌜ P ⌝) (⌜ P ⌝)%I. *)
  (* Proof. apply into_crash_into_crash_flushed. apply _. Qed. *)

  (* Global Instance lifted_embed_nodep_into_crash_flush (P : iProp Σ) : *)
  (*   IntoNGFlush (⎡ P ⎤) (⎡ P ⎤)%I | 1000. *)
  (* Proof. apply into_crash_into_crash_flushed. apply into_nextgen_into_nextgen. Qed. *)

  (* Global Instance lifted_embed_into_crash_flush (P : iProp Σ) Q : *)
  (*   base.nextgen_modality.IntoNextgen P Q → *)
  (*   IntoNGFlush (⎡ P ⎤) (⎡ Q ⎤)%I. *)
  (* Proof. intros ?. apply into_crash_into_crash_flushed. apply _. Qed. *)

  (* Global Instance emp_into_crash_flush : IntoNGFlush emp emp. *)
  (* Proof. apply _. apply: into_crash_into_crash_flushed. Qed. *)

  Global Instance sep_into_crash_flush (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoNGFlush P P' →
    IntoNGFlush Q Q' →
    IntoNGFlush (P ∗ Q)%I (P' ∗ Q')%I.
  Proof.
    rewrite /IntoNGFlush.
    iIntros (Pi Qi) "[P Q]".
    iDestruct (Pi with "P") as "P".
    iDestruct (Qi with "Q") as "Q".
    iApply nextgen_flush_sep.
    iFrame.
  Qed.

  Global Instance disj_into_crash_flush (P Q : dProp Σ) (P' Q' : dProp Σ) :
    IntoNGFlush P P' →
    IntoNGFlush Q Q' →
    IntoNGFlush (P ∨ Q)%I (P' ∨ Q')%I.
  Proof.
    rewrite /IntoNGFlush.
    iIntros (Pi Qi) "[P|Q]".
    - iDestruct (Pi with "P") as "P".
      iApply nextgen_flush_disj.
      iLeft.
      iFrame.
    - iDestruct (Qi with "Q") as "Q".
      iApply nextgen_flush_disj.
      iRight.
      iFrame.
  Qed.

  Global Instance if_else_into_crash_flush (b : bool) P P' Q Q' :
    IntoNGFlush P P' →
    IntoNGFlush Q Q' →
    IntoNGFlush (if b then P else Q) (if b then P' else Q').
  Proof. intros ??. destruct b; apply _. Qed.

  (* Global Instance later_into_crash_flush P P' : *)
  (*   IntoNGFlush P P' → *)
  (*   IntoNGFlush (▷ P) (▷ P'). *)
  (* Proof. *)
  (* Qed. *)

  Global Instance have_FV_strong_into_crash_flush ℓ t :
    IntoNGFlush _ _ := nextgen_have_FV_strong ℓ t.

  Global Instance exist_into_crash_flush {A} Φ Ψ:
    (∀ x : A, IntoNGFlush (Φ x) (Ψ x)) →
    IntoNGFlush (∃ x, Φ x) (∃ x, Ψ x).
  Proof.
    rewrite /IntoNGFlush.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (nextgen_flush_mono with "HΦ"). auto.
  Qed.

  Global Instance big_sepL_into_crash_flush {A} ϕ ψ l :
    (∀ k (x : A), IntoNGFlush (ϕ k x) (ψ k x)) →
    IntoNGFlush ([∗ list] k↦x ∈ l, ϕ k x)%I ([∗ list] k↦x ∈ l, ψ k x)%I.
  Proof. revert ϕ ψ. induction l as [|x l IH]=> Φ ψ ? /=; apply _. Qed.
End IntoNGFlush.


(* since I no longer import the other high level definitions, this test section is commentted. *)
(* Section nextgen_flush_test. *)
(*   From self.high Require Import predicates. *)
(*   From self.high.modalities Require Import if_rec. *)
(*   Context `{generational_resources.nvmHighG}. *)

(*   Lemma foo P `{Countable ST'} ℓ (ϕ : ST' → val → dProp Σ) t : *)
(*     ⌜ P ⌝ -∗ *)
(*     ⎡ know_pred ℓ ϕ ⎤ -∗ *)
(*     ⎡ persisted_loc ℓ t ⎤ -∗ *)
(*     <NGF> ⌜ P ⌝ ∗ if_rec ℓ (⎡ know_pred ℓ ϕ ⎤). *)
(*   Proof. *)
(*     iIntros "P pred pers". *)
(*     iModIntro. *)
(*     rewrite if_rec_lift_if_rec. *)
(*     iFrame. *)
(*   Qed. *)

(* End nextgen_flush_test. *)

Typeclasses Opaque nextgen.
Typeclasses Opaque nextgen_flush.

(* Since the post crash modality does not satisfy
   [nextgen_intuitionistically_2] the [iModIntro] tactic clears the
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
