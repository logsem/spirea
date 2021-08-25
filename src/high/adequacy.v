From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.

From Perennial.program_logic Require Import recovery_adequacy.

From self.high Require Import weakestpre.
From self.high Require Import recovery_weakestpre.
(* From Perennial.program_logic Require Export crash_lang recovery_weakestpre. *)
(* From Perennial.program_logic Require Import crash_adequacy. *)

(* Lemma high_recv_adequacy (Σ : gFunctors) s k e r σ g (φ φr : val → Prop) : *)
(*   valid_heap σ.1 → *)
(*   recv_adequate (CS := nvm_crash_lang) s e r σ g (λ v _ _, φ (val_val v)) (λ v _ _, φr (val_val v)) (λ _ _, True). *)
