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
From self.nextgen Require Import gen_ing.
From self.high.resources Require Export
  gen_ghost_map gen_ghost_map_map gen_alocs gen_predicates auth_map_map.

From self.algebra Require Import view.

Class nvmHighGS Σ Ω `{!nvmBaseGS Σ Ω} := NvmHighG {
  nvm_predicatesG :: (genInDepsG Σ Ω (predicatesR (Σ := Σ)) [#crashed_atR]);
  full_predicates_name : gname;
  read_predicates_name : gname;
  pers_predicates_name : gname;
  abs_historiesG :: ghost_map_mapGpreS loc time positive Σ Ω;
  abs_history_name : gname;
  (* resharing [phy_history] for atomic locations *)
  phy_historiesG :: auth_map_mapR_inG (leibnizO message) Σ Ω;
  phy_history_name : gname;
  non_atomic_views :: ghost_mapGpreS loc view Σ Ω;
  non_atomic_views_gname : gname;
  crashed_in_inG :: ghost_mapGpreS loc positive Σ Ω;
  crashed_in_name : gname;
  preordersG :: ghost_mapGpreS loc (relation2 positive) Σ Ω;
  preorders_name : gname;
  locsG :: gen_alocsR_inG Σ Ω;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  new_locs_name : gname;
  nvm_bumpersG :: ghost_mapGpreS loc (positive → option positive) Σ Ω;
  bumpers_name : gname;
}.
