From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

(** * Generational transformations *)
Class GenTrans {A : cmra} (f : A → A) := {
  gen_trans_ne :> NonExpansive f;
  gen_trans_validN n x : ✓{n} x → ✓{n} f x;
  gen_trans_monoN n : Proper (includedN n ==> includedN n) f;
}.
Global Hint Mode GenTrans - ! : typeclass_instances.
Global Arguments gen_trans_validN {_} _ {_} _ _ _.
Global Arguments gen_trans_monoN {_} _ {_}.

Global Instance gen_trans_proper {A : cmra} (t : A → A) `{!GenTrans t} :
  Proper ((≡) ==> (≡)) t := ne_proper _.

#[global]
Instance cmra_morphism_monotoneN' {M : ucmra} (f : M → M) `{!CmraMorphism f} :
  GenTrans f.
Proof.
  split.
  - apply _.
  - apply: cmra_morphism_validN.
  - intros ??. apply: cmra_morphism_monotoneN.
Qed.

