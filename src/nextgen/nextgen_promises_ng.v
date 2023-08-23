(* This file defines lemmas for cameras that do _not_ interact with the
 * [nextgen] modality and proves rules for these. *)

From Equations Require Import Equations.
From stdpp Require Import finite.

From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From iris_named_props Require Import named_props.
From nextgen Require Export nextgen_basic cmra_morphism_extra gen_single_shot gen_nc.

From self Require Export hvec.
From self.high Require Import increasing_map.
From self.nextgen Require Export types omega generational_cmra transmap
  promise nextgen_promises_model gen_ing.

Import EqNotations. (* Get the [rew] notation. *)
Import uPred.

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
