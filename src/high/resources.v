(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.base_logic.lib Require Import own ghost_map.
From iris.algebra Require Import gmap excl auth.

From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop.

Definition predicateR {Σ} := agreeR (positive -d> val -d> laterO (optionO (dPropO Σ))).
Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

Notation abs_history := (gmap time).

Definition encoded_abs_historyR := gmapUR time (agreeR positiveO).
Definition enc_abs_histories := gmap loc (gmap time positive).

(* Definition abs_historiesR := authR (gmapUR loc (authR encoded_abs_historyR)). *)
Definition know_abs_historiesR := authR (gmapUR loc (gmapUR time (agreeR positiveO))).

Definition relationO := leibnizO (positive → positive → Prop).
Definition preordersR := authR (gmapUR loc (agreeR relationO)).

Class nvmHighG Σ := NvmHighG {
  abs_history_name : gname;
  know_abs_history_name : gname;
  predicates_name : gname;
  preorders_name : gname;
  ra_inG :> inG Σ (@predicatesR Σ);
  ra_inG' :> inG Σ know_abs_historiesR;
  (* ra'_inG :> inG Σ abs_historiesR; *)
  abs_histories :> ghost_mapG Σ loc (gmap time positive);
  (* preordersG :> ghost_mapG Σ loc (positiveO -d> positiveO -d> PropO) *)
  preordersG :> inG Σ preordersR
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
