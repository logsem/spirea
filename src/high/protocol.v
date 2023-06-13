From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import encode_relation.
From self.high Require Import dprop dprop_liftings resources modalities
  post_crash_modality monpred_simpl or_lost if_rec predicates.
From self.lang Require Import lang.
From self.high.modalities Require Import no_buffer.

(* A handy alias for the type of location predicates. *)
Definition loc_pred `{nvmG Σ} ST `{AbstractState ST} := ST → val → dProp Σ.

Definition loc_predO `{nvmG Σ} ST := ST -d> val -d> dPropO Σ.


(* A protocol consists of
  - A predicate [p_inv] that holds for each write and corresponding state of the
    location.
  - A function [bumper] that specifies how the state of a location changes
    after a crash. *)
Record LocationProtocol ST `{AbstractState ST, nvmG Σ} := MkProt {
  p_full : loc_pred ST;
  p_read : loc_pred ST;
  p_pers : loc_pred ST;
  p_bumper : ST → ST;
}.

Global Arguments MkProt {_} {_} {_} {_} {_} {_} _%I _%I.

Global Arguments p_full {ST} {_} {_} {_} {_} {_} _.
Global Arguments p_read {ST} {_} {_} {_} {_} {_} _.
Global Arguments p_pers {ST} {_} {_} {_} {_} {_} _.
Global Arguments p_bumper {ST} {_} {_} {_} {_} {_} _.

(* Type class collection the properties that a protocol should have.

Note: The fields are ordered by "difficulty" in the sense of how difficult these
conditions usually are to show.  *)

Class ProtocolConditions `{AbstractState ST, nvmG Σ} (prot : LocationProtocol ST) := {
  bumper_mono :
    Proper ((⊑@{ST}) ==> (⊑))%signature (prot.(p_bumper));
  full_nobuf :>
    ∀ s v, BufferFree (prot.(p_full) s v);
  read_nobuf :>
    ∀ s v, BufferFree (prot.(p_read) s v);
  pers_nobuf :>
    ∀ s v, BufferFree (prot.(p_pers) s v);
  full_read_split :
    forall s v, prot.(p_full) s v ⊣⊢ prot.(p_read) s v ∗ (prot.(p_read) s v -∗ prot.(p_full) s v);
  pred_full_post_crash :
    ⊢ ∀ s_p v_p, prot.(p_pers) s_p v_p -∗
      (* first case: we crash exactly at [s] *)
      (∀ s v, prot.(p_full) s v -∗ <PCF> prot.(p_full) (prot.(p_bumper) s) v ∗ prot.(p_pers) (prot.(p_bumper) s) v) ∧
      (* second case: we crash later than [s_p] (included) but before [s] (excluded) *)
      (∀ s v s_c v_c,
         (* we need to extract the objective facts from the full predicate *)
         ∃ P, (<obj> (prot.(p_full) s v -∗ <obj> P)) ∗
              (P -∗ prot.(p_read) s_c v_c -∗ ⌜ s_p ⊑ s_c ⌝ -∗ ⌜ s_c ⊑ s ⌝ -∗
              <PCF> prot.(p_full) (prot.(p_bumper) s_c) v_c ∗ prot.(p_pers) (prot.(p_bumper) s_c) v_c));
  pred_read_post_crash :
    ⊢ ∀ s v, prot.(p_read) s v -∗ <PCF> prot.(p_read) (prot.(p_bumper) s) v
}.

(* I'm not sure about this part *)
#[global] Hint Mode ProtocolConditions + + + + + ! ! : typeclass_instances.

Existing Instance full_nobuf.
Existing Instance read_nobuf.
Existing Instance pers_nobuf.
Existing Instance bumper_mono.

(** [know_protocol] represents the knowledge that a location is associated with a
specific protocol. It's defined simply using more "primitive" assertions. *)
Definition know_protocol `{AbstractState ST, nvmG Σ}
           ℓ (prot : LocationProtocol ST) : dProp Σ :=
  "#knowFullPred" ∷ know_full_pred_d ℓ prot.(p_full) ∗
  "#knowReadPred" ∷ know_read_pred_d ℓ prot.(p_read) ∗
  "#knowPersPred" ∷ know_pers_pred_d ℓ prot.(p_pers) ∗
  "#knowPreorder" ∷ know_preorder_loc_d ℓ (⊑@{ST}) ∗
  "#knowBumper" ∷ know_bumper ℓ prot.(p_bumper).

Lemma encode_bumper_bump_mono `{AbstractState ST}
      (bumper : ST → ST) `{!Proper ((⊑@{ST}) ==> (⊑))%signature bumper}
      (x y x' y' : positive) :
  encode_bumper bumper x = Some x' →
  encode_bumper bumper y = Some y' →
  encode_relation (⊑@{ST}) x y →
  encode_relation (⊑@{ST}) x' y'.
Proof.
  rewrite /encode_bumper. rewrite /encode_relation.
  intros (sx & -> & <-)%encode_bumper_Some_decode.
  intros (sy & -> & <-)%encode_bumper_Some_decode.
  rewrite !decode_encode /=.
  solve_proper.
Qed.

Section protocol.
  Context `{nvmG Σ, AbstractState ST}.

  Implicit Types (prot : LocationProtocol ST).

  Lemma post_crash_know_protocol ℓ prot :
    know_protocol ℓ prot -∗ <PC> if_rec ℓ (know_protocol ℓ prot).
  Proof.
    iIntros "(a & b & c & d & e)".
    iModIntro.
    iModIntro. iFrame.
  Qed.

  Global Instance know_protocol_into_crash ℓ prot :
    IntoCrash
      (know_protocol ℓ prot)
      (if_rec ℓ (know_protocol ℓ prot)).
  Proof.
    rewrite /IntoCrash. iIntros "P". by iApply post_crash_know_protocol.
  Qed.

  Lemma know_protocol_extract ℓ prot :
    know_protocol ℓ prot -∗
      know_full_pred_d ℓ prot.(p_full) ∗
      know_read_pred_d ℓ prot.(p_read) ∗
      know_pers_pred_d ℓ prot.(p_pers) ∗
      know_preorder_loc_d ℓ (⊑@{ST}) ∗
      know_bumper ℓ prot.(p_bumper).
  Proof. iNamed 1. iFrame "#". Qed.

  Lemma know_protocol_unfold ℓ prot i :
    know_protocol ℓ prot i ⊣⊢
       ("#knowFullPred" ∷ know_full_pred_d ℓ (p_full prot) i ∗
        "#knowReadPred" ∷ know_read_pred_d ℓ (p_read prot) i ∗
        "#knowPersPred" ∷ know_pers_pred_d ℓ (p_pers prot) i ∗
        "#knowPreorder" ∷ know_preorder_loc_d ℓ (⊑@{ST}) i ∗
        "#knowBumper" ∷ know_bumper ℓ (p_bumper prot) i).
  Proof. rewrite /know_protocol !monPred_at_sep //. Qed.

  Global Instance know_protocol_buffer_free ℓ prot :
    BufferFree (know_protocol ℓ prot).
  Proof. apply _. Qed.

  Lemma know_protocol_at ℓ prot TV gnames :
    (know_protocol ℓ prot) (TV, gnames) ⊣⊢
      know_full_pred ℓ prot.(p_full) ∗
      know_read_pred ℓ prot.(p_read) ∗
      know_pers_pred ℓ prot.(p_pers) ∗
      know_preorder_loc ℓ (⊑@{ST}) ∗
      own_know_bumper (get_bumpers_name gnames) ℓ prot.(p_bumper).
  Proof.
    rewrite /know_protocol. rewrite !monPred_at_sep.
    simpl. rewrite !monPred_at_embed.
    done.
  Qed.

  Global Instance know_protocol_contractive ℓ bumper :
    Contractive (λ (invs : (prodO (prodO (loc_predO ST) (loc_predO ST)) (loc_predO ST))),
                      let '(full, read, pers) := invs in
                      (know_protocol ℓ (MkProt full read pers bumper))).
  Proof.
    rewrite /know_protocol.
    rewrite /know_full_pred_d /know_read_pred_d /know_pers_pred_d.
    intros ????.
    destruct x as [[full read] pers].
    destruct y as [[full' read'] pers'].
    repeat
      done ||
      f_equiv ||
      (intros ?? ->; f_contractive; apply H2).
  Qed.

End protocol.

Opaque know_protocol.
