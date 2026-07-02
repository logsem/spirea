From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From self Require Import encode_relation.

From self.high Require Import dprop generational_resources modalities monpred_simpl predicates.
From self.high.lib Require Import abstract_state.

From self.lang Require Import lang.

(* A handy alias for the type of location predicates. *)
Definition loc_pred `{nvmHighGS} ST `{AbstractState ST} := ST → val → dProp Σ.

Definition loc_predO `{nvmHighGS} ST := ST -d> val -d> dPropO Σ.

(* A protocol consists of
  - A predicate [p_inv] that holds for each write and corresponding state of the
    location.
  - A function [bumper] that specifies how the state of a location changes
    after a crash. *)

Record LocationProtocol ST `{AbstractState ST, nvmHighGS} := MkProt {
  p_full : loc_pred ST;
  p_read : loc_pred ST;
  p_pers : loc_pred ST;
  p_bumper : ST → ST;
}.

#[global] Arguments MkProt   {ST _ _ _ _ _ _ _} _%_I _%_I _%_I _.
#[global] Arguments p_full   {ST _ _ _ _ _ _ _} _.
#[global] Arguments p_read   {ST _ _ _ _ _ _ _} _.
#[global] Arguments p_pers   {ST _ _ _ _ _ _ _} _.
#[global] Arguments p_bumper {ST _ _ _ _ _ _ _} _ _.

(** [know_protocol] represents the knowledge that a location is associated with a
specific protocol. It's defined simply using more "primitive" assertions. *)
Definition know_protocol `{AbstractState ST, nvmHighGS}
           ℓ (prot : LocationProtocol ST) : iProp Σ :=
  "#knowFullPred" ∷  know_full_pred ℓ prot.(p_full)  ∗
  "#knowReadPred" ∷  know_read_pred ℓ prot.(p_read)  ∗
  "#knowPersPred" ∷  know_pers_pred ℓ prot.(p_pers)  ∗
  "#knowPreorder" ∷  know_preorder_loc ℓ (⊑@{ST})  ∗
  "#knowBumper" ∷  know_bumper ℓ prot.(p_bumper) .

Section encoded.
  #[local] Existing Instance nvmHighGS_inG.
  Definition know_protocol_enc `{nvmHighGS} ℓ
    (encp_full encp_read encp_pers : (enc_predicateO))
    (order : extra.relation2 positive) (bump : positive → option positive) : iProp Σ :=
    know_pred_ra full_predicates_name ℓ (unwrapped_pred_to_ra (encoded_pred_unwrap encp_full)) ∗
    know_pred_ra read_predicates_name ℓ (unwrapped_pred_to_ra (encoded_pred_unwrap encp_read)) ∗
    know_pred_ra pers_predicates_name ℓ (unwrapped_pred_to_ra (encoded_pred_unwrap encp_pers)) ∗
    (ℓ ↪[preorders_name, drop_OCV]□ order) ∗
    (ℓ ↪[bumpers_name, drop_OCV]□ bump).
End encoded.

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
  Context `{nvmHighGS, AbstractState ST}.

  Implicit Types (prot : LocationProtocol ST).

  #[local] Existing Instance nvmHighGS_inG.
  #[local] Existing Instance nvmHighGpreS_bumpers.

  Lemma nextgen_know_protocol ℓ prot :
    know_protocol ℓ prot -∗
    ⚡==> base_if_rec ℓ (lastgen_know_bumper ℓ prot.(p_bumper) ∗ lastgen_know_preorder_loc ℓ (⊑@{ST}) ∗ know_protocol ℓ prot).
  Proof.
    iNamed 1.
    iPoseProof (ghost_map_elem_into_nextgen_ifrec with "knowPreorder") as "knowPreorder'".
    iPoseProof (ghost_map_elem_into_nextgen_ifrec with "[]") as "knowBumper'".
    { iDestruct "knowBumper" as "[? $]". }
    iDestruct "knowBumper" as "[% _]".
    iModIntro.
    iDestruct "knowBumper'" as "[$ knowBumper']".
    iDestruct "knowPreorder'" as "[$ knowPreorder']".
    rewrite -?if_rec_lift_if_rec.

    iModIntro. iFrame "#%".
  Qed.

  #[global] Instance know_protocol_into_nextgen ℓ prot :
    base_IntoNextgen
      ( know_protocol ℓ prot )
      (base_if_rec ℓ (lastgen_know_bumper ℓ prot.(p_bumper) ∗ lastgen_know_preorder_loc ℓ (⊑@{ST}) ∗ know_protocol ℓ prot )).
  Proof.
    rewrite /base_IntoNextgen.
    iIntros "P".
    by iApply nextgen_know_protocol.
  Qed.

  #[global] Instance know_protocol_contractive ℓ bumper :
    Contractive (λ (invs : (prodO (prodO (loc_predO ST) (loc_predO ST)) (loc_predO ST))),
                      let '(full, read, pers) := invs in
                      (know_protocol ℓ (MkProt full read pers bumper))).
  Proof.
    rewrite /know_protocol.
    intros ????.
    destruct x as [[full read] pers].
    destruct y as [[full' read'] pers'].
    simpl.
    repeat
      (done ||
       f_contractive ||
       f_equiv); apply H2.
  Qed.
End protocol.
