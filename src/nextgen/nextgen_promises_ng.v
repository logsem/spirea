(* This file defines lemmas for cameras that do _not_ interact with the
 * [nextgen] modality and proves rules for these. *)

From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

From self.nextgen Require Export nextgen_promises_model.

(** Non-generational cameras. *)
Class ngInG Σ (Ω : gGenCmras Σ) A := NgInG {
  ngInG_inG :> inG Σ A;
  ngInG_evidence : ∀ i, Ogid Ω i ≠ inG_id ngInG_inG;
}.

Section non_generational_resources.
  Context `{!ngInG Σ Ω A}.
  Implicit Types (a : A).

  Lemma nextgen_ng_own γ a :
    own γ a ⊢ ⚡==> own γ a.
  Proof. iApply nextgen_own_non_gen. apply ngInG_evidence. Qed.

  #[global]
  Instance ng_own_into_nextgen γ (a : A) `{!ngInG Σ Ω A} :
    IntoNextgen _ _ := nextgen_ng_own γ a.

End non_generational_resources.

