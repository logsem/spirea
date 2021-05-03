(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.base_logic.lib Require Import own ghost_map.
From iris.algebra Require Import gmap excl auth.

From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop.

Notation st := positive (only parsing).
Notation stO := positiveO (only parsing).

Definition predicateR {Σ} := agreeR (st -d> val -d> laterO (optionO (dPropO Σ))).
Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

Definition abs_history (State : Type) `{Countable State} := gmap time State.

Definition encoded_abs_historyR := gmapUR time (agreeR stO).
Definition enc_abs_histories := gmap loc (gmap time st).

Definition abs_historiesR := authR (gmapUR loc (authR encoded_abs_historyR)).

Class nvmHighG Σ := NvmHighG {
  abs_history_name : gname;
  predicates_name : gname;
  ra_inG :> inG Σ (@predicatesR Σ);
  ra'_inG :> inG Σ abs_historiesR;
  abs_histories :> ghost_mapG Σ loc (gmap time positive);
}.

Class nvmG Σ := NvmG {
  nvmG_baseG :> nvmBaseG Σ;
  nvmG_highG :> nvmHighG Σ;
}.

Class AbstractState T := {
  abs_state_eqdecision :> EqDecision T;
  abs_state_countable :> Countable T;
  abs_state_subseteq :> SqSubsetEq T;
  abs_state_preorder :> PreOrder (⊑@{T});
}.
