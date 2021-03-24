(* In this file we define our weakest precondition on top of the weakest
(* precondition included in Iris. *) *)

From iris.proofmode Require Export tactics.
From iris.algebra Require Import gmap excl auth.
From iris.program_logic Require weakestpre.
From iris.program_logic Require Import ownp.

From self Require Export dprop view lang.
From self.lang Require Import primitive_laws syntax.

Section wp.
  Context `{!nvmG Σ}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).
  (* (P Q : dProp Σ) (E : coPset) *)

  (* Global Instance fst_lat_mono : Proper ((⊑) ==> (⊑)) (@fst A B).
  Proof. move => [??][??][-> _]//. Qed.

  Global Instance snd_lat_mono : Proper ((⊑) ==> (⊑)) (@snd A B).
  Proof. move => [??][??][_ ->]//. Qed. *)

  Global Instance store_view_mono : Proper ((⊑) ==> (⊑)) store_view.
  Proof.
    intros [[??]?] [[??]?].
    rewrite /sqsubseteq /subseteq_thread_view /subseteq_view.
    rewrite !pair_included.
    intros [[le _] _].
    done.
  Qed.

  Global Instance persist_view_mono : Proper ((⊑) ==> (⊑)) persist_view.
  Proof.
    intros [[??]?] [[??]?].
    rewrite /sqsubseteq /subseteq_thread_view /subseteq_view.
    rewrite !pair_included.
    intros [[_ le] _].
    done.
  Qed.

  Global Instance wb_buffer_view_mono : Proper ((⊑) ==> (⊑)) wb_buffer_view.
  Proof.
    intros [[??]?] [[??]?].
    rewrite /sqsubseteq /subseteq_thread_view /subseteq_view.
    rewrite !pair_included.
    intros [_ le].
    done.
  Qed.

  (* Program Definition test' P : dProp Σ :=
    MonPred (λ V,
      ∀ TV, ⌜V ⊑ TV⌝ -∗ P)%I _.
  Next Obligation. solve_proper. Qed. *)

  (* Program Definition test P : dProp Σ :=
    MonPred (λ V,
      ∀ TV, ⌜(store_view V) ⊑ (store_view TV)⌝ -∗ P)%I _.
  Next Obligation. solve_proper. Qed. *)

  (* Our weakest precondition is a [dProp]. We construct it using [MonPred]
  which wraps the function along with a proof that it is monotone. *)
  Program Definition wp_def s E e Φ : dProp Σ :=
    MonPred (λ V,
      ∀ TV,
        (* ⌜TV ⊑ V⌝ -∗ *)
        ⌜(store_view V) ⊑ (store_view TV)⌝ -∗
        ⌜(persist_view V) ⊑ (persist_view TV)⌝ -∗
        ⌜(wb_buffer_view V) ⊑ (wb_buffer_view TV)⌝ -∗
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

  Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof.
    rewrite wp_eq. rewrite /wp_def.
    iStartProof (iProp _). simpl. iIntros (TV'). iSplit.
    - iIntros "hi". admit.
    - iIntros "HΦ **".
      iApply (weakestpre.wp_value_fupd' _ _ _ (ThreadVal v TV)).
      iFrame.
  Admitted.
      (* epose proof (weakestpre.wp_value_fupd' s E _ (ThreadVal v TV)).
      simpl in *.
      rewrite H2.
      iApply weakestpre.wp_value_fupd'. *)
      (* rewrite -(weakestpre.wp_value_fupd' _ _ (Φ v)). *)
      (* iDestruct (weakestpre.wp_value_fupd' with "HΦ") as "HI". *)
      (* rewrite -wp_value_fupd'.
      iApply (wp_value' _ _ _ (ThreadVal v _)). iFrame.
    rewrite wp_value_fupd'.
  Admitted. *)

  (* Definition prop : dProp Σ := ⎡⌜1 =2⌝⎤%I. *)

  (* Definition prop' : dProp Σ := (⎡⌜1 =2⌝⎤ -∗ True)%Ig *)

  Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. intros <-. by apply wp_value_fupd'. Qed.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof.
    iStartProof (iProp _). simpl. rewrite wp_eq /wp_def. iIntros "% HΦ %% ? ??".
    iApply (wp_value' _ _ _ (ThreadVal v _)). iFrame.
  Qed.

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
