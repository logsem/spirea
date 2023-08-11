From iris.base_logic.lib Require Export own.

From self Require Import hvec.
From self.nextgen Require Import types generational_cmra.

(** For every entry in [Ω] we store this record of information. The equality
 * [gcd_cmra_eq] is the "canonical" equality we will use to show that the resource
 * [R Σ i] has the proper form. Using this equality is necesarry as we
 * otherwise end up with different equalities of this form that we then do not
 * know to be equal. *)
Record gen_cmra_data (Σ : gFunctors) len := {
  gcd_cmra : cmra;
  gcd_n : nat;
  gcd_deps : ivec gcd_n cmra;
  gcd_deps_ids : ivec gcd_n (fin len);
  gcd_gid : gid Σ;
  gcd_cmra_eq : generational_cmraR gcd_cmra gcd_deps = R Σ gcd_gid;
}.

Arguments gcd_cmra {_} {_}.
Arguments gcd_n {_} {_}.
Arguments gcd_deps {_} {_}.
Arguments gcd_deps_ids {_} {_}.
Arguments gcd_gid {_} {_}.
Arguments gcd_cmra_eq {_} {_}.

Definition gen_cmras_data Σ len := fin len → gen_cmra_data Σ len.

(* Each entry in [gen_cmras_data] contain a list of cameras that should be the
 * cmras of the dependencies. This duplicated information in the sense that the
 * cmras of the dependencies is also stored at their indices. We say that a
 * [gen_cmras_data] is _well-formed_ if this duplicated information is equal.
 * *)

(* [map] is well-formed at the index [id]. *)
Definition omega_wf_at {Σ len} (map : gen_cmras_data Σ len) id : Prop :=
  let gcd := map id in
  ∀ idx,
    let id2 := gcd.(gcd_deps_ids) !!! idx in
    (map id2).(gcd_cmra) = gcd.(gcd_deps) !!! idx.

(** [map] is well-formed at all indices. *)
Definition omega_wf {Σ len} (map : gen_cmras_data Σ len) : Prop :=
  ∀ id, omega_wf_at map id.

(** [gGenCmras] contains a partial map from the type of cameras into a "set"
of valid transformation function for that camera. *)
Class gGenCmras (Σ : gFunctors) := {
  gc_len : nat;
  gc_map : gen_cmras_data Σ gc_len;
  (* Storing this wf-ness criteria for the whole map may be too strong. If this
  * gives problems we can wiggle this requirement around to somewhere else. *)
  gc_map_wf : omega_wf gc_map;
  gc_map_gid : ∀ i1 i2, i1 ≠ i2 → (gc_map i1).(gcd_gid) ≠ (gc_map i2).(gcd_gid);
}.

Definition ggid {Σ} (Ω : gGenCmras Σ) := fin gc_len.

Global Arguments gc_map {_} _.

Definition gen_cmra_data_to_inG {Σ len} (gcd : gen_cmra_data Σ len) :
    inG Σ (generational_cmraR gcd.(gcd_cmra) gcd.(gcd_deps)).
Proof. econstructor. apply gcd_cmra_eq. Defined.

(* Ownership based on data in [Ω]. *)
Definition Oown {Σ} {Ω : gGenCmras Σ} (i : ggid Ω) γ a :=
  @own _ _ (gen_cmra_data_to_inG (Ω.(gc_map) i)) γ a.

#[export] Hint Mode gGenCmras +.

(*** Omega helpers *)

(* Various helpers to lookup values in [Ω]. These are defined using notation as
 * Coq is otherwise sometimes not able to figure out when things type-check. *)

(** Lookup the camera in [Ω] at the index [i] *)
Notation Oc Ω i := (Ω.(gc_map) i).(gcd_cmra).

(** Lookup the number of depenencies in [Ω] at the index [i] *)
Notation On Ω i := (Ω.(gc_map) i).(gcd_n).

Definition Ogid {Σ} (Ω : gGenCmras Σ) (i : ggid Ω) : gid Σ :=
  (Ω.(gc_map) i).(gcd_gid).

Instance Ogid_inj {Σ} (Ω : gGenCmras Σ) : Inj eq eq (Ogid Ω).
Proof.
  intros j1 j2 eq.
  destruct (decide (j1 = j2)); first done.
  exfalso. apply: gc_map_gid; done.
Qed.

(** Lookup the dependency cameras in [Ω] at the index [i] *)
Definition Ocs {Σ} (Ω : gGenCmras Σ) (i : ggid Ω) : ivec (On Ω i) cmra :=
  (Ω.(gc_map) i).(gcd_deps).

(* The remaining helpers are not defined using notation as that has not been needed. *)
Section omega_helpers.
  Context {Σ : gFunctors}.

  Implicit Types (Ω : gGenCmras Σ).

  (** Lookup the number of depenencies in [Ω] at the index [i] *)
  Definition Oids Ω i : ivec (On Ω i) (ggid Ω) :=
    (Ω.(gc_map) i).(gcd_deps_ids).

  (** Lookup the dependency cameras in [Ω] at the index [i] *)
  Definition Oeq Ω i : generational_cmraR (Oc Ω i) (Ocs Ω i) = R Σ (Ogid Ω i) :=
    (Ω.(gc_map) i).(gcd_cmra_eq).

  (** This lemma relies on [Ω] being well-formed. *)
  Definition Ocs_Oids_distr {Ω : gGenCmras Σ}
      id (idx : fin (On Ω id)) (wf : omega_wf_at Ω.(gc_map) id) :
    Ocs Ω id !!! idx = Oc Ω (Oids Ω id !!! idx) := eq_sym (wf idx).

  (* This lemma combines a use of [hvec_lookup_fmap} and [Ocs_Oids_distr] to
   * ensure that looking up in [cs] results in a useful return type. [f] will
   * usually be [pred_over] or [cmra_to_trans]. *)
  Definition lookup_fmap_Ocs `{Ω : gGenCmras Σ} {f id}
      (cs : hvec (On Ω id) (f <$> Ocs Ω id)) i (wf : omega_wf_at Ω.(gc_map) id)
      : f (Oc Ω (Oids Ω id !!! i)) :=
    eq_rect _ _ (hvec_lookup_fmap cs i) _ (Ocs_Oids_distr _ _ wf).

End omega_helpers.

