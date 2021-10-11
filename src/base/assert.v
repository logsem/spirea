From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.

From self.lang Require Import lang.
From self.base Require Import proofmode.

From iris.prelude Require Import options.

Section lifting.
  Context `{!nvmBaseFixedG Σ, !extraStateInterp Σ, nvmBaseDeltaG Σ}.

  Lemma wp_assert E (Φ : thread_val → iProp Σ) e TV :
    WP e `at` TV @ E {{ v, ⌜val_val v = #true⌝ ∧ ▷ Φ (ThreadVal #() (val_view v)) }} -∗
    WP (assert: e)%V `at` TV @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_lam.
    wp_smart_apply (wp_wand with "HΦ"). iIntros ([v ?]) "[% ?]".
    rewrite /thread_fill_item.
    simpl in *.
    subst.
    wp_if.
    done.
  Qed.

End lifting.
