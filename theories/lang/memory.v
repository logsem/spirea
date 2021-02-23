(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.

Notation loc := Z. (* Any countable infinite type would do. *)

Notation time := nat.

Notation view := (gmap loc time).

Section memory.

  (* We assume a type of values. *)
  Context {val : Type}.

  Implicit Types (v : val) (ℓ : loc).

  Inductive mem_event : Type :=
  | MEvLoad ℓ v
  | MEvStore ℓ v
  (* acquire/release weak memory events *)
  | MEvLoadAcquire ℓ v
  | MEvStoreRelease ℓ v
  (* RMW are special *)
  | MEvRMW ℓ (vOld vNew : val) (* read-modify-write *)
  | MEvAlloc ℓ v
  (* persistent memor specific *)
  | MEvWB ℓ
  | MFence
  | MFenceSync.

  Record message : Type := Msg {
    msg_val : val;
    msg_store_view : view;
    msg_persist_view : view;
    msg_wb_buffer : view;
  }.

  Record thread_view : Type := ThreadView {
    tv_store_view : view;
    tv_persist_view : view;
    tv_wb_buffer : view;
  }.

  Definition history : Type := gmap time message.

  Definition store := gmap loc history.

  (* Small-step reduction steps on the memory. *)

  Inductive mem_step : store → thread_view → mem_event → store → thread_view → Prop :=
  (* A normal non-atomic load. *)
  | MStep_Load σ V P B t ℓ (v : val) h :
    σ !! ℓ = Some h →
    msg_val <$> (h !! t) = Some v →
    (default 0 (V !! ℓ)) ≤ t →
    mem_step σ (ThreadView V P B) (MEvLoad ℓ v) σ (ThreadView (<[ ℓ := t ]>V) P B)
  (* A normal non-atomic write. *)
  | MStep_Store σ V P B t ℓ (v : val) h V' :
    σ !! ℓ = Some h →
    (h !! t) = None → (* No event exists at t already. *)
    (default 0 (V !! ℓ)) ≤ t →
    V' = <[ ℓ := t ]>V → (* V' incorporates the new event in the threads view. *)
    mem_step σ (ThreadView V P B) (MEvLoad ℓ v)
               (<[ ℓ := <[t := (Msg v V' P B) ]>h ]>σ) (ThreadView (<[ ℓ := t ]>V') P B).

End memory.