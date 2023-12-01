(* We define the resource algebras that we use in the interpretation of the
high-level logic. *)
From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import extra.
From self.algebra Require Import ghost_map ghost_map_map.
From self.lang Require Import lang.
From self.base Require Import primitive_laws.
(* From self.high Require Import abstract_state lifted_modalities. *)
From self.high Require Export abstract_state.
From self.high.resources Require Export bumpers preorders auth_map_map abstract_history.

(* All the ghost names used in the high-level logic that needs changing at a crash. *)
Class nvmHighDeltaG := MkNvmHighDeltaG {
  (* "Global" ghost names *)
  abs_history_name : gname;
  (* For physical history *)
  phys_history_name : gname;
  non_atomic_views_gname : gname;
  crashed_in_name : gname;
  full_predicates_name : gname;
  read_predicates_name : gname;
  pers_predicates_name : gname;
  preorders_name : gname;
  offset_name : gname;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  bumpers_name : gname;
  pview_lb_name : gname;
}.

(* A record of all the global ghost names that we need. *)
Class nvmDeltaG := NvmDeltaG {
  nvm_delta_base :> nvmBaseDeltaG;
  nvm_delta_high :> nvmHighDeltaG
}.

(* Resource algebra used to represent agreement on which predicates are
associated with which locations. *)

Definition predicateR {Σ} :=
  agreeR (positive -d> val -d> laterO (optionO (thread_view * nvmDeltaG -d> iPropO Σ))).

Definition predicatesR {Σ} := authR (gmapUR loc (@predicateR Σ)).

Class predicatesG Σ := { predicates_inG :> inG Σ (@predicatesR Σ) }.

Definition predicate_F :=
  agreeRF (positive -d> val -d> ▶ (optionOF (thread_view * nvmDeltaG -d> ∙))).

Definition predicates_F := authRF (gmapURF loc predicate_F).

Definition predicatesΣ := #[ GFunctor predicates_F ].

Instance subG_predicatesΣ {Σ} : subG predicatesΣ Σ → predicatesG Σ.
Proof. solve_inG. Qed.

(* Resource algebra that contains all the locations that are _shared_. *)
Definition shared_locsR := authR (gsetUR loc).

Class nvmHighFixedG Σ := {
  nvm_predicatesG :> predicatesG Σ;
  abs_histories :> ghost_map_mapG Σ loc time positive;
  phys_histories :> inG Σ (auth_map_mapR (leibnizO message));
  non_atomic_views :> ghost_mapG Σ loc view;
  crashed_in_inG :> ghost_mapG Σ loc positive;
  preordersG :> ghost_mapG Σ loc (relation2 positive);
  offsetsG :> ghost_mapG Σ loc nat;
  locsG :> inG Σ shared_locsR;
  nvm_bumpersG :> bumpersG Σ;
  pview_lbG :> inG Σ (authR viewUR);
}.

Definition nvmHighΣ :=
  #[ predicatesΣ;
     ghost_map_mapΣ loc time positive;
     GFunctor (auth_map_mapR (leibnizO message));
     ghost_mapΣ loc view;
     ghost_mapΣ loc positive;
     ghost_mapΣ loc (relation2 positive);
     ghost_mapΣ loc nat;
     GFunctor (shared_locsR);
     ghost_mapΣ loc (positive → option positive);
     GFunctor (authRF viewUR)
    ].

Instance subG_nvmHighΣ {Σ} : subG nvmHighΣ Σ → nvmHighFixedG Σ.
Proof. solve_inG. Qed.

Class nvmG Σ := NvmFixedG {
  nvmG_baseG :> nvmBaseFixedG Σ;
  nvmG_highG :> nvmHighFixedG Σ;
}.

(* All the functors that we need for the high-level logic (and no ghost names). *)
Class nvmGpreS Σ := NvmPreG {
  nvmPreG_base :> nvmBaseGpreS Σ;
  nvmPreG_high :> nvmHighFixedG Σ; (* We can use [nvmHighFixedG] directly as it has no ghost names. *)
}.

Definition nvmΣ := #[ nvmBaseΣ; nvmHighΣ ].

Instance subG_nvmΣ {Σ} : subG nvmΣ Σ → nvmGpreS Σ.
Proof. solve_inG. Qed.

(* Getters for ghost names that take the ghost name record as an explicit argument. *)
Definition get_offset_name (gnames : nvmDeltaG) := offset_name.
Definition get_bumpers_name (gnames : nvmDeltaG) := bumpers_name.
Definition get_at_locs_name (gnames : nvmDeltaG) := shared_locs_name.
Definition get_na_locs_name (gnames : nvmDeltaG) := exclusive_locs_name.
Definition get_na_views_name (gnames : nvmDeltaG) := non_atomic_views_gname.
Definition get_pview_lb_name (gnames : nvmDeltaG) := pview_lb_name.

(* Wrappers around ownership of resources that extracts the ghost names from
   [nvmDeltaG]. These wrapper makes it easier to switch the ghost names around
   after a crash in [post_crash_modality.v]. *)
Section ownership_wrappers.
  Context `{nvmG Σ, nD : nvmDeltaG}.

  (* We have these wrappers partly to avoid having to spell out the global ghost
  names, and partly such that we can conveniently swap them out by giving the
  named type class instance [nD] *)

  Definition know_encoded_bumper (ℓ : loc)
             (encoded_bumper : positive → option positive) : iProp Σ :=
    ℓ ↪[bumpers_name]□ encoded_bumper.

  Definition know_preorder_loc `{Countable ST} ℓ (preorder : relation2 ST) : iProp Σ :=
    own_know_preorder_loc preorders_name ℓ preorder.

  Definition know_full_encoded_history_loc ℓ q enc_abs_hist : iProp Σ :=
    history_full_entry_encoded abs_history_name ℓ q enc_abs_hist.

  Definition know_full_history_loc `{Countable ST}
             ℓ q (abs_hist : gmap time ST) : iProp Σ :=
    full_entry_unenc abs_history_name ℓ q abs_hist.

  Definition know_frag_encoded_history_loc ℓ t e : iProp Σ :=
    frag_entry abs_history_name ℓ t e.

  Definition know_frag_history_loc `{Countable ST} ℓ t (s : ST) : iProp Σ :=
    frag_entry_unenc abs_history_name ℓ t s.

  Definition know_phys_hist_msg ℓ t msg : iProp Σ :=
    auth_map_map_frag_singleton phys_history_name ℓ t msg.

End ownership_wrappers.

Section location_sets.
  Context `{nvmG Σ}.

  Implicit Types (locs : gset loc) (ℓ : loc).

  Lemma location_sets_singleton_included γ locs ℓ :
    own γ (● locs) -∗ own γ (◯ {[ ℓ ]}) -∗ ⌜ ℓ ∈ locs ⌝.
  Proof.
    iIntros "A B".
    iDestruct (own_valid_2 with "A B")
      as %[V%gset_included _]%auth_both_valid_discrete.
    rewrite elem_of_subseteq_singleton.
    done.
  Qed.

  Lemma location_sets_lookup γ locs ℓ :
    ℓ ∈ locs → own γ (◯ locs) -∗ own γ (◯ {[ ℓ ]}).
  Proof.
    iIntros (elm). iApply own_mono. simpl.
    eexists (◯ locs).
    rewrite -auth_frag_op.
    f_equiv.
    set_solver.
  Qed.

End location_sets.

