From self.base Require Import primitive_laws.
From self.base Require post_crash_modality.
From self.high Require Import dprop weakestpre.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

Program Definition post_crash {Σ} (P : nvmG Σ → dProp Σ) `{hG : !nvmG Σ} : dProp Σ :=
  MonPred
    (λ TV, ∀ (hhG' : nvmHighG Σ), base_post_crash (λ hG', P (NvmG _ hG' hhG') (∅, ∅, ∅)))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Section post_crash_prop.
  Context `{hG: !nvmG Σ}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.
  Implicit Types v : thread_val.

  (** Tiny shortcut for introducing the assumption for a [post_crash]. *)
  Ltac iIntrosPostCrash := iIntros (hG').

  Lemma post_crash_intro Q:
    (⊢ Q) →
    (⊢ post_crash (λ _, Q)).
  Proof.
    iIntros (Hmono).
    iIntrosPostCrash.
    iFrame "∗".
    iApply Hmono.
  Qed.

  Lemma post_crash_mono P Q:
    (∀ hG, P hG -∗ Q hG) →
    post_crash P -∗ post_crash Q.
  Proof.
    iIntros (Hmono) "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG') as "P".
    by iApply Hmono.
  Qed.

  

End post_crash_prop.
