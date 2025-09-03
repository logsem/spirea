(* The generational resources used by HighSpirea.
 *
 * The following resources are all [ghost_map loc V], and a crash
 * will only shrink the domain of the map, but never changes the value, and thus
 * share (most of) nextgen definition.
 * - the knowledge of protocols
 * - the knowledge of preorder
 * - the knowledge of bumper
 * - the knowledge of atomic and non-atomic locations
 * The following resources were maintained by highSpirea, but it's now maintained
 * in baseSpirea already and we only need to import the definitions:
 * - the offsets for each location
 * - the full physical history including messages from previous generation
 * The following resources require their own nextgen construction:
 * - the view for every non-atomic location (since they are not shared, there is always
 *   a single view one will access)
 * - the abstract history
 *)

From self Require Import extra.
From self.lang Require Import lang.

From self.base Require Export generational_resources.
From self.high.resources Require Export
  gen_ghost_map gen_ghost_map_map gen_alocs gen_predicates auth_map_map abstract_history.

From self.algebra Require Import view.

Class nvmHighGS Σ Ω `{!nvmBaseGS Σ Ω} := NvmHighG {
  nvm_predicatesG :> predicates_inG Σ Ω;
  full_predicates_name : gname;
  read_predicates_name : gname;
  pers_predicates_name : gname;
  abs_historiesG :> ghost_map_mapG loc time positive Σ Ω;
  abs_history_name : gname;
  (* resharing [phy_history] for atomic locations *)
  phy_historiesG :> auth_map_mapR_inG Σ Ω (leibnizO message);
  phy_history_name : gname;
  non_atomic_views :> genC_ghost_map_inG loc view Σ Ω;
  non_atomic_views_gname : gname;
  crashed_in_inG :> genC_ghost_map_inG loc positive Σ Ω;
  crashed_in_name : gname;
  preordersG :> genC_ghost_map_inG loc (relation2 positive) Σ Ω;
  preorders_name : gname;
  locsG :> gen_alocsR_inG Σ Ω;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  nvm_bumpersG :> genC_ghost_map_inG loc (positive → option positive) Σ Ω;
  bumpers_name : gname;
}.
