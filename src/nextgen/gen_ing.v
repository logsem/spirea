From iris.base_logic.lib Require Export own.
From self.nextgen Require Import types hvec omega generational_cmra.

Import EqNotations. (* Get the [rew] notation. *)

(* We define [genInG] which is our generational replacement for [inG]. *)

Class genInG {n} Σ (Ω : gGenCmras Σ) A (DS : ivec n cmra) := GenInG {
  genInG_id : ggid Ω;
  genInG_gcd_n : n = On Ω genInG_id;
  genInG_gti_typ : A = Oc Ω genInG_id;
  genInG_gcd_deps : DS = rew <- [λ n, ivec n _] genInG_gcd_n in
                           (Ω.(gc_map) genInG_id).(gcd_deps);
}.

Global Arguments genInG_id {_} {_} {_} {_} {_} _.

Lemma omega_genInG_cmra_eq {n} {DS : ivec n cmra} `{i : !genInG Σ Ω A DS} :
  generational_cmraR A DS =
  generational_cmraR (Oc Ω (genInG_id i)) (Ocs Ω (genInG_id i)).
Proof.
  apply (generational_cmraR_transp genInG_gcd_n genInG_gti_typ genInG_gcd_deps).
Defined.

(* The regular [inG] class can be derived from [genInG]. *)
Global Instance genInG_inG {n : nat} `{i : !genInG Σ Ω A DS} :
    inG Σ (generational_cmraR A DS) := {|
  inG_id := Ogid Ω (genInG_id (n := n) i);
  inG_prf := eq_trans omega_genInG_cmra_eq (Oeq Ω _);
|}.

(* Knowledge that [A] is a resource, with the information about its dependencies
hidden in the dependent pair. *)
Class genInSelfG (Σ : gFunctors) Ω (A : cmra) := GenInG2 {
  genInSelfG_n : nat;
  genInSelfG_DS : ivec genInSelfG_n cmra;
  genInSelfG_gen : genInG Σ Ω A (genInSelfG_DS);
}.

Arguments genInSelfG_gen {_ _ _} _.
Definition genInSelfG_id `(g : genInSelfG Σ Ω) := genInG_id (genInSelfG_gen g).

Instance genInG_genInSelfG {Σ Ω} {n A DS} (i : genInG Σ Ω A DS) : genInSelfG Σ Ω A := {|
  genInSelfG_n := n;
  genInSelfG_DS := DS;
  genInSelfG_gen := i;
|}.

(** Equality for [On] and [genInG]. *)
Lemma On_genInG {A n} {DS : ivec n cmra} `{i : !genInG Σ Ω A DS} :
  On Ω (genInG_id i) = n.
Proof. symmetry. apply (genInG_gcd_n (genInG := i)). Defined.

(* This class ties together a [genInG] instance for one camera with [genInG]
 * instances for all of its dependencies such that those instances have the
 * right ids as specified in [Ω]. *)
Class genInDepsG {n} (Σ : gFunctors) Ω (A : cmra) (DS : ivec n cmra)
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)} := GenDepsInG {
  genInDepsG_gen :> genInG Σ Ω A DS;
  genInDepsG_eqs : ∀ i,
    genInSelfG_id (gs i) = Oids Ω (genInG_id genInDepsG_gen) !!! (rew genInG_gcd_n in i);
}.

Global Arguments genInDepsG_gen {_ _ _ _ _ _} _.

Definition genInDepsG_id `(g : genInDepsG Σ Ω A DS) :=
  genInG_id (genInDepsG_gen g).

Section omega_helpers_genInG.
  Context `{Σ : gFunctors, Ω : gGenCmras Σ}.
  Context {A n} {DS : ivec n cmra} {i : genInG Σ Ω A DS}.

  (* When we have a [genInG] instance, that instance mentions some types ([A]
   * and [DS]) that are in fact equal to some of the types in [Ω]. The lemmas
   * in this section establishes these equalities. *)

  Lemma rel_over_Oc_Ocs_genInG :
    rel_over DS A = rel_over (Ocs Ω (genInG_id _)) (Oc Ω (genInG_id _)).
  Proof.
    rewrite /Ocs.
    apply (rel_over_eq genInG_gcd_n genInG_gti_typ genInG_gcd_deps).
  Defined.

  Lemma pred_over_Oc_genInG : pred_over A = pred_over (Oc Ω (genInG_id _)).
  Proof.
    apply (eq_rect _ (λ c, pred_over A = pred_over c) eq_refl _ genInG_gti_typ).
  Defined.

  Lemma trans_for_genInG :
    trans_for n DS = trans_for (On Ω _) (Ocs Ω (genInG_id _)).
  Proof.
    apply (hvec_fmap_eq genInG_gcd_n).
    apply genInG_gcd_deps.
  Defined.

  Lemma preds_for_genInG :
    preds_for n DS = preds_for (On Ω _) (Ocs Ω (genInG_id _)).
  Proof.
    apply (hvec_fmap_eq genInG_gcd_n).
    apply genInG_gcd_deps.
  Defined.

End omega_helpers_genInG.

Section rules.
  Context {n : nat} {DS : ivec n cmra} `{i : !genInG Σ Ω A DS}.

  Lemma own_gen_cmra_data_to_inG γ (a : generational_cmraR A DS) :
    own γ a = Oown (genInG_id i) γ (rew omega_genInG_cmra_eq in a).
  Proof.
    (* Note, the way a [genInG] creates an [inG] instance is carefully defined
     * to match [Oown] to make this lemma be provable only with
     * [eq_trans_rew_distr]. *)
    rewrite /Oown own.own_eq /own.own_def /own.iRes_singleton.
    unfold cmra_transport.
    rewrite eq_trans_rew_distr.
    done.
  Qed.

  Lemma own_gen_cmra_data_to_inG' γ (a : generational_cmraR _ _) :
    own γ (rew <- omega_genInG_cmra_eq in a) = Oown (genInG_id i) γ a.
  Proof. rewrite own_gen_cmra_data_to_inG. rewrite rew_opp_r. done. Qed.

End rules.
