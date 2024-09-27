From iris.algebra Require Import gmap auth gmap_view.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self Require Import extra.
From self.algebra Require Import ghost_map.
From self.high Require Import abstract_state.

Definition bumpersR :=
  (* authR (gmapUR loc (agreeR (leibnizO (positive → option positive)))). *)
  gmap_viewR loc (leibnizO (positive → option positive)).

Notation bumpersG Σ := (ghost_mapG Σ loc (positive → option positive)).
