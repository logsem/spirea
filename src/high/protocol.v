From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From self.high.lib Require Import abstract_state.
From self Require Import encode_relation.

From self.high Require Import dprop generational_resources modalities monpred_simpl predicates wrappers.
From self.high.modalities Require Import no_buffer nextgen_flush nextgen if_rec.

From self.lang Require Import lang.

Set Default Proof Using "Type*".

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

#[global] Arguments MkProt   {ST _ _ _ _ _ _ _} _%I _%I _%I _.
#[global] Arguments p_full   {ST _ _ _ _ _ _ _} _.
#[global] Arguments p_read   {ST _ _ _ _ _ _ _} _.
#[global] Arguments p_pers   {ST _ _ _ _ _ _ _} _.
#[global] Arguments p_bumper {ST _ _ _ _ _ _ _} _ _.

(* Type class collection the properties that a protocol should have.

Note: The fields are ordered by "difficulty" in the sense of how difficult these
conditions usually are to show.  *)

Class ProtocolConditions `{AbstractState ST, nvmHighGS} (prot : LocationProtocol ST) := {
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
    ⊢ ∀ σ_p v_p σ_f v_f, ⌜ σ_p ⊑ σ_f ⌝ -∗ prot.(p_pers) σ_p v_p -∗ prot.(p_full) σ_f v_f -∗
      (* first case: we crash exactly at [σ_f] *)
      (|==> <NGF> prot.(p_full) (prot.(p_bumper) σ_f) v_f ∗ prot.(p_pers) (prot.(p_bumper) σ_f) v_f) ∧
      (* second case: we crash later than [s_p] (included) but before [s] (excluded) *)
      (∀ σ_c v_c,
         (* We cannot take subjective resource from [p_full],
          * but we can take subjective resource from [p_read]. *)
         <obj> (prot.(p_read) σ_c v_c -∗ ⌜ σ_p ⊑ σ_c ⌝ -∗ ⌜ σ_c ⊑ σ_f ⌝ ==∗
                <NGF> prot.(p_full) (prot.(p_bumper) σ_c) v_c ∗ prot.(p_pers) (prot.(p_bumper) σ_c) v_c));
  pred_read_nextgen :
    ⊢ ∀ s v, prot.(p_read) s v -∗ <NGF> prot.(p_read) (prot.(p_bumper) s) v
}.

#[global] Hint Mode ProtocolConditions + + + + + + + + ! : typeclass_instances.

Existing Instance full_nobuf.
Existing Instance read_nobuf.
Existing Instance pers_obj.
Existing Instance bumper_mono.

(** [know_protocol] represents the knowledge that a location is associated with a
specific protocol. It's defined simply using more "primitive" assertions. *)
Definition know_protocol `{AbstractState ST, nvmHighGS}
           ℓ (prot : LocationProtocol ST) : iProp Σ :=
  "#knowFullPred" ∷  know_full_pred ℓ prot.(p_full)  ∗
  "#knowReadPred" ∷  know_read_pred ℓ prot.(p_read)  ∗
  "#knowPersPred" ∷  know_pers_pred ℓ prot.(p_pers)  ∗
  "#knowPreorder" ∷  know_preorder_loc ℓ (⊑@{ST})  ∗
  "#knowBumper" ∷  know_bumper ℓ prot.(p_bumper) .

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

  (* Lemma know_protocol_extract ℓ prot : *)
  (*   know_protocol ℓ prot -∗ *)
  (*     ⎡ know_full_pred ℓ prot.(p_full) ⎤ ∗ *)
  (*     ⎡ know_read_pred ℓ prot.(p_read) ⎤ ∗ *)
  (*     ⎡ know_pers_pred ℓ prot.(p_pers) ⎤ ∗ *)
  (*     ⎡ know_preorder_loc ℓ (⊑@{ST}) ⎤ ∗ *)
  (*     ⎡ know_bumper ℓ prot.(p_bumper) ⎤. *)
  (* Proof. iNamed 1. iFrame "#". Qed. *)

  (* Lemma know_protocol_unfold ℓ prot TV : *)
  (*   know_protocol ℓ prot TV ⊣⊢ *)
  (*   ("#knowFullPred" ∷ know_full_pred ℓ (p_full prot) ∗ *)
  (*    "#knowReadPred" ∷ know_read_pred ℓ (p_read prot) ∗ *)
  (*    "#knowPersPred" ∷ know_pers_pred ℓ (p_pers prot) ∗ *)
  (*    "#knowPreorder" ∷ know_preorder_loc ℓ (⊑@{ST}) ∗ *)
  (*    "#knowBumper" ∷  know_bumper ℓ (p_bumper prot)). *)
  (* Proof. rewrite /know_protocol !monPred_at_sep !monPred_at_embed //. Qed. *)

  (* #[global] Instance know_protocol_buffer_free ℓ prot : *)
  (*   BufferFree (know_protocol ℓ prot). *)
  (* Proof. apply _. Qed. *)

  (* Lemma know_protocol_at ℓ prot TV : *)
  (*   (know_protocol ℓ prot) TV ⊣⊢ *)
  (*     know_full_pred ℓ prot.(p_full) ∗ *)
  (*     know_read_pred ℓ prot.(p_read) ∗ *)
  (*     know_pers_pred ℓ prot.(p_pers) ∗ *)
  (*     know_preorder_loc ℓ (⊑@{ST}) ∗ *)
  (*     know_bumper ℓ prot.(p_bumper). *)
  (* Proof. *)
  (*   rewrite /know_protocol. rewrite !monPred_at_sep. *)
  (*   simpl. rewrite !monPred_at_embed. *)
  (*   done. *)
  (* Qed. *)

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
