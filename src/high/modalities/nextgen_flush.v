From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From iris.bi Require Import monpred.
From self.nextgen Require Import nextgen_promises.
From self.base Require Import generational_resources primitive_laws.
From self.high Require Import dprop generational_resources monpred_simpl.
From self.high.modalities Require Import nextgen.

From self.algebra Require Import view.

Program Definition nextgen_flush `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (<NG> ∀ (CV : view),
       ⌜ flush_view TV ⊑ CV ⌝ ∗
       ⎡ persisted (view_to_zero (flush_view TV)) ⎤ ∗
       ⎡ crashed_at CV ⎤ -∗
       P) (∅, ∅, ∅))%I _.
Next Obligation.
  intros ????????.
  apply nextgen_mono.
  do 6 f_equiv; first solve_proper.
  iApply persisted_weak.
  solve_proper.
Qed.

Class IntoNGFlush `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}
      (P : dProp Σ) (Q : dProp Σ) :=
  into_nextgen_flushed : P ⊢ nextgen_flush Q.

Arguments IntoNGFlush {_ _ _ _} _%I _%I.

Notation "'<NGF>' P" :=
  (nextgen_flush P)
  (at level 200, right associativity) : bi_scope.

Section nextgen_persisted.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}.

  Lemma nextgen_flush_nextgen P :
    nextgen P ⊢ nextgen_flush P.
  Proof.
    iStartProof (iProp _).
    iIntros (TV) "P".
    rewrite /nextgen_flush.
    rewrite /nextgen.
    simpl.
    iModIntro.
    iIntros "#?".
    iIntros (CV TV') "% not_lost".
    iApply monPred_mono; first done.
    iApply "P"; done.
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
    iIntros "#?".
    iIntros (CV TV') "% #not_lost".
    iDestruct ("HP" with "[#$]") as "HP".
    iDestruct ("HQ" with "[#$]") as "HQ".
    iDestruct ("HP" $! CV with "[$]") as "HP".
    iDestruct ("HQ" $! CV with "[$]") as "HQ".
    iSplitL "HP"; iApply monPred_mono; done.
  Qed.

  Lemma nextgen_flush_disj P Q :
    nextgen_flush P ∨ nextgen_flush Q -∗ <NGF> P ∨ Q.
  Proof.
    iModel.
    rewrite /nextgen_flush //=.
    iIntros "[HP | HQ]"; iIntros "!> #?"; iIntros (CV TV') "% #not_lost".
    - iDestruct ("HP" with "[#$]") as "HP".
      iDestruct ("HP" $! CV with "[$]") as "HP".
      iLeft.
      iApply monPred_mono; done.
    - iDestruct ("HQ" with "[#$]") as "HQ".
      iDestruct ("HQ" $! CV with "[$]") as "HQ".
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
    iIntros "HP #?" (CV TV') "% #not_lost".
    iDestruct ("HP" with "[#$]") as "HP".
    iDestruct ("HP" $! CV with "[$]") as "HP".
    iApply mono.
    iApply monPred_mono; done.
  Qed.

  #[global] Instance nextgen_flush_proper :
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

  Lemma nextgen_flush_intuitionistic P Q:
    IntoNGFlush P Q → □ P ⊢ <NGF> (□ Q).
  Proof.
    rewrite /IntoNGFlush => ->.
    iStartProof (iProp _); iIntros (?) "P".
    rewrite ?bi.intuitionistically_into_persistently.
    rewrite /nextgen_flush /=.
    iPoseProof (nextgen_intuitionistically_2 with "P") as "P".
    iModIntro.
    rewrite -bi.intuitionistically_into_persistently.
    iDestruct "P" as "#P".
    iIntros "#?".
    iIntros (CV TV' ?) "(% & #? & #?)".
    iSpecialize ("P" with "[#$]").
    iSpecialize ("P" $! CV with "[]").
    { by iFrame "#". }
    iModIntro.
    done.
  Qed.

  Lemma nextgen_flush_and P Q:
    ((<NGF> P) ∧ (<NGF> Q))%I ⊢ <NGF> (P ∧ Q).
  Proof.
    iModel.
    rewrite /nextgen_flush /=.
    rewrite nextgen_and_1.
    iIntros "HPQ"; iIntros "!> #?"; iIntros (CV TV') "% #not_lost".
    iSplit.
    - iDestruct "HPQ" as "[HP _]".
      iDestruct ("HP" with "[#$]") as "HP".
      iDestruct ("HP" $! CV with "[$]") as "$".
    - iDestruct "HPQ" as "[_ HQ]".
      iDestruct ("HQ" with "[#$]") as "HQ".
      iDestruct ("HQ" $! CV with "[$]") as "$".
  Qed.

  Lemma modality_nextgen_flush_mixin :
    modality_mixin (@nextgen_flush Σ _ _ _)
      (MIEnvTransform IntoNGFlush) (MIEnvTransform IntoNGFlush).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, nextgen_flush_emp,
      nextgen_flush_mono, nextgen_flush_sep, nextgen_flush_intuitionistic, nextgen_flush_and.
  Qed.
  Definition modality_nextgen_flush :=
    Modality _ modality_nextgen_flush_mixin.

  #[global] Instance from_modal_nextgen_flush P :
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
    iIntros "!> #?".
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
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω}.

  (* This is not an instance as it would probably have a negative impact on the
  performance of type class resolution. *)
  (* TODO (Yixuan): verify performance *)
  Lemma into_nextgen_into_nextgen_flushed P Q :
    IntoNextgen P Q →
    IntoNGFlush P Q.
  Proof.
    rewrite /IntoNGFlush /IntoNextgen.
    rewrite -nextgen_flush_nextgen.
    done.
  Qed.

  #[global] Instance into_nextgen_flush_nextgen_flush P : IntoNGFlush (<NGF> P) P.
  Proof. done. Qed.
  
  (* Global Instance pure_into_nextgen_flushed (P : Prop) : *)
  (*   IntoNGFlush (⌜ P ⌝) (⌜ P ⌝)%I. *)
  (* Proof. apply into_nextgen_into_nextgen_flushed. apply _. Qed. *)

  (* Global Instance lifted_embed_nodep_into_nextgen_flush (P : iProp Σ) : *)
  (*   IntoNGFlush (⎡ P ⎤) (⎡ P ⎤)%I | 1000. *)
  (* Proof. apply into_nextgen_into_nextgen_flushed. apply into_nextgen_into_nextgen. Qed. *)

  (* Global Instance lifted_embed_into_nextgen_flush (P : iProp Σ) Q : *)
  (*   base.nextgen_modality.IntoNextgen P Q → *)
  (*   IntoNGFlush (⎡ P ⎤) (⎡ Q ⎤)%I. *)
  (* Proof. intros ?. apply into_nextgen_into_nextgen_flushed. apply _. Qed. *)

  Global Instance emp_into_flush : IntoNGFlush emp emp.
  Proof. apply: into_nextgen_into_nextgen_flushed. Qed.

  Global Instance sep_into_nextgen_flush (P Q : dProp Σ) (P' Q' : dProp Σ) :
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

  Global Instance disj_into_nextgen_flush (P Q : dProp Σ) (P' Q' : dProp Σ) :
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

  Global Instance if_else_into_nextgen_flush (b : bool) P P' Q Q' :
    IntoNGFlush P P' →
    IntoNGFlush Q Q' →
    IntoNGFlush (if b then P else Q) (if b then P' else Q').
  Proof. intros ??. destruct b; apply _. Qed.

  (* Global Instance later_into_nextgen_flush P P' : *)
  (*   IntoNGFlush P P' → *)
  (*   IntoNGFlush (▷ P) (▷ P'). *)
  (* Proof. *)
  (* Qed. *)

  Global Instance have_FV_strong_into_nextgen_flush ℓ t :
    IntoNGFlush _ _ := nextgen_have_FV_strong ℓ t.

  Global Instance exist_into_nextgen_flush {A} Φ Ψ:
    (∀ x : A, IntoNGFlush (Φ x) (Ψ x)) →
    IntoNGFlush (∃ x, Φ x) (∃ x, Ψ x).
  Proof.
    rewrite /IntoNGFlush.
    iIntros (Hc) "H". iDestruct "H" as (?) "HΦ". iPoseProof (Hc with "[$]") as "HΦ".
    iApply (nextgen_flush_mono with "HΦ"). auto.
  Qed.

  Global Instance big_sepL_into_nextgen_flush {A} ϕ ψ l :
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
