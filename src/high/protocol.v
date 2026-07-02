From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From self.high.lib Require Import abstract_state.
From self Require Import encode_relation.

From self.high Require Import dprop generational_resources modalities monpred_simpl predicates.
From self.high.resources Require Import gen_ghost_map.
From self.high Require Export protocol_defs.
From self.high Require Import locations_defs.
From self.lang Require Import lang.

(* Type class collection the properties that a protocol should have.
 * Note: The fields are ordered by "difficulty" in the sense of how difficult
 * these conditions usually are to show. *)
Class ProtocolConditions `{AbstractState ST, nvmHighGS} (ℓ : loc) (prot : LocationProtocol ST) := {
  bumper_mono :
    Proper ((⊑@{ST}) ==> (⊑))%signature (prot.(p_bumper));
  full_nobuf ::
    ∀ s v, BufferFree (prot.(p_full) s v);
  read_nobuf ::
    ∀ s v, BufferFree (prot.(p_read) s v);
  pers_obj ::
    ∀ s v, Objective (prot.(p_pers) s v);
  full_read_split :
    forall s v, prot.(p_full) s v ⊣⊢ prot.(p_read) s v ∗ (prot.(p_read) s v -∗ prot.(p_full) s v);
  pred_full_nextgen :
    ⎡ know_protocol ℓ prot ⎤ ⊢
      ∀ σ_p v_p σ_f v_f, ⌜ σ_p ⊑ σ_f ⌝ -∗ prot.(p_pers) σ_p v_p -∗ prot.(p_full) σ_f v_f -∗
      (* first case: we crash exactly at [σ_f] *)
      (|==> <NGF> crashed_in prot ℓ σ_f -∗
            prot.(p_full) (prot.(p_bumper) σ_f) v_f ∗ prot.(p_pers) (prot.(p_bumper) σ_f) v_f) ∧
      (* second case: we crash later than [s_p] (included) but before [s] (excluded) *)
      (∀ σ_c v_c,
         (* We cannot take subjective resource from [p_full],
          * but we can take subjective resource from [p_read]. *)
         <obj> (prot.(p_read) σ_c v_c -∗ ⌜ σ_p ⊑ σ_c ⌝ -∗ ⌜ σ_c ⊑ σ_f ⌝ ==∗
                <NGF> crashed_in prot ℓ σ_c -∗
                      prot.(p_full) (prot.(p_bumper) σ_c) v_c ∗ prot.(p_pers) (prot.(p_bumper) σ_c) v_c));
  pred_read_nextgen :
    ⊢ ∀ s v, prot.(p_read) s v -∗ <NGF> prot.(p_read) (prot.(p_bumper) s) v
}.

#[global] Hint Mode ProtocolConditions + + + + + + + + - ! : typeclass_instances.

Existing Instance full_nobuf.
Existing Instance read_nobuf.
Existing Instance pers_obj.
Existing Instance bumper_mono.

(* Helpers shared by the [na]/[at] allocation proofs (and used to discharge the
   injected [crash_witness_enc] condition of [predFullNextgen]). *)
Section encoding_lemmas.
  Context `{AbstractState ST}.
  Context `{nvmHighGS}.

  Lemma know_protocol_enc_know_protocol ℓ (prot : LocationProtocol ST) :
    Proper ((⊑@{ST}) ==> (⊑)) prot.(p_bumper) →
    know_protocol_enc ℓ (encode_predicate prot.(p_full)) (encode_predicate prot.(p_read))
      (encode_predicate prot.(p_pers)) (encode_relation (⊑@{ST}))
      (encode_bumper prot.(p_bumper))
    ⊢ know_protocol ℓ prot.
  Proof. by iIntros "% ($ & $ & $ & $ & $)". Qed.

  Lemma know_protocol_know_protocol_enc ℓ (prot : LocationProtocol ST) :
    know_protocol ℓ prot ⊢
    know_protocol_enc ℓ (encode_predicate prot.(p_full)) (encode_predicate prot.(p_read))
                        (encode_predicate prot.(p_pers)) (encode_relation (⊑@{ST}))
                        (encode_bumper prot.(p_bumper)).
  Proof. iIntros "($ & $ & $ & $ & [_ $])". Qed.
End encoding_lemmas.
