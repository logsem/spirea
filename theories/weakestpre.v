(* In this file we define our weakest precondition on top of the weakest
(* precondition included in Iris. *) *)

From iris.proofmode Require Export tactics.
From iris.algebra Require Import gmap excl auth.
From iris.program_logic Require weakestpre.
From iris.program_logic Require Import ownp.

From self Require Import vprop view lang.
From self.lang Require Import primitive_laws syntax.

Section wp.
  Context `{!nvmG Σ}.

  Implicit Types (Φ : val → vProp Σ) (e : expr).
  (* (P Q : vProp Σ) (E : coPset) *)

  (* Our weakest precondition is a [vProp]. We construct it using [MonPred]
  which wraps the function along with a proof that it is monotone. *)
  Program Definition wp_def s E e Φ : vProp Σ :=
    MonPred (λ V,
      ∀ TV, ⌜V ⊑ TV.(tv_store_view)⌝ -∗
            valid (TV.(tv_store_view)) -∗
            WP (ThreadState e TV) @ s; E {{ λ '(ThreadVal v TV), (Φ v (TV.(tv_store_view))) }})%I%V _.
  Next Obligation. solve_proper. Qed.

  (* This is sealing follows the same ritual as the [wp] in Iris. *)
  Definition wp_aux : seal (@wp_def). by eexists. Qed.

  Global Instance expr_wp : Wp expr_lang (vProp Σ) stuckness := unseal (wp_aux).

  Lemma wp_eq : wp = wp_def.
  Proof. rewrite -wp_aux.(seal_eq). done. Qed.

  (* We prove a few basic facts about our weakest precondition. *)
  Global Instance wp_ne s E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e).
  Proof. rewrite wp_eq. split=>V. Admitted. (* solve_proper. Qed. *) (* FIXME: Why does this not work? *)
  Global Instance wp_proper s E e :
    Proper (pointwise_relation val (≡) ==> (≡)) (wp s E e).
  Proof. rewrite wp_eq. constructor=>V.
    (* solve_proper. Qed. *)
  Admitted.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value E Φ v : Φ v ⊢ WP (of_val v) @ E {{ Φ }}.
  Proof.
    iStartProof (iProp _). simpl. rewrite wp_eq /wp_def. iIntros "% HΦ %% ?".
    iApply (wp_value' _ _ _ (ThreadVal v _)). iFrame.
  Qed.

End wp.
