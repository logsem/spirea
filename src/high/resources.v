(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.base_logic.lib Require Import own ghost_map.
From iris.algebra Require Import gset gmap excl auth.

From self Require Import extra.
From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop.

(* Resource algebra used to represent agreement on which predicates are
associated with which locations. *)
Definition predicateR {Σ} := agreeR (positive -d> val -d> laterO (optionO (dPropO Σ))).
Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

Notation abs_history := (gmap time).

(* Resource algebras that for each location stores the encoded abstract states
associated with each message/store. *)
Definition encoded_abs_historyR := gmapUR time (agreeR positiveO).
Definition enc_abs_histories := gmap loc (gmap time positive).

Definition know_abs_historiesR := authR (gmapUR loc (gmapUR time (agreeR positiveO))).

(* Resourcce algebra that stores the encoded preorder for each location. *)
Definition relationO := leibnizO (positive → positive → Prop).
Definition preordersR := authR (gmapUR loc (agreeR relationO)).

(* Resource algebra that contains all the locations that are _shared_. *)
Definition shared_locsR := authR (gsetUR loc).

Class nvmHighG Σ := NvmHighG {
  (* "Global" ghost names *)
  abs_history_name : gname;
  know_abs_history_name : gname;
  predicates_name : gname;
  preorders_name : gname;
  shared_locs_name : gname;
  (* Functors *)
  ra_inG :> inG Σ (@predicatesR Σ);
  ra_inG' :> inG Σ know_abs_historiesR;
  abs_histories :> ghost_mapG Σ loc (gmap time positive);
  preordersG :> inG Σ preordersR;
  shared_locsG :> inG Σ shared_locsR
}.

Class nvmG Σ := NvmG {
  nvmG_baseG :> nvmBaseG Σ;
  nvmG_highG :> nvmHighG Σ;
}.

Class AbstractState T := {
  abs_state_eqdecision :> EqDecision T;
  abs_state_countable :> Countable T;
  abs_state_relation : relation2 T;
  abs_state_preorder :> PreOrder abs_state_relation;
}.

Instance abstract_state_sqsubseteq `{AbstractState T} : SqSubsetEq T :=
  abs_state_relation.
