(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.

Notation loc := Z. (* Any countable infinite type would do. *)

Notation time := nat.

Notation view := (gmap loc time).

Instance join_view : Join view := (union_with (λ (x1 x2 : nat), Some (x1 `max` x2))).

Infix "!!0" := (λ m i, default 0 (m !! i)) (at level 80).

Section memory.

  (* We assume a type of values. *)
  Context {val : Type}.

  Implicit Types (v : val) (ℓ : loc).

  Inductive mem_event : Type :=
  | MEvAlloc ℓ v
  | MEvLoad ℓ v
  | MEvStore ℓ v
  (* acquire/release weak memory events *)
  | MEvLoadAcquire ℓ v
  | MEvStoreRelease ℓ v
  (* RMW are special *)
  | MEvRMW ℓ (vOld vNew : val) (* read-modify-write *)
  (* persistent memor specific *)
  | MEvWB ℓ
  | MEvFence
  | MEvFenceSync.

  Record message : Type := Msg {
    msg_val : val;
    msg_store_view : view;
    msg_persist_view : view;
    (* msg_wb_buffer : view; (* FIXME: Do we even need this in the message or does it suffice to have it in the thread_view? *) *)
  }.

  Record thread_view : Type := ThreadView {
    tv_store_view : view;
    tv_persist_view : view;
    tv_wb_buffer : view;
  }.

  Definition history : Type := gmap time message.

  Definition store := gmap loc history.

  Definition mem_config : Type := store * view.

  (* Small-step reduction steps on the memory. *)

  Inductive mem_step : mem_config → thread_view → mem_event → mem_config → thread_view → Prop :=
  | MStepAlloc σ V P B ℓ v V' p :
    σ !! ℓ = None → (* This is a fresh location not already in the heap. *)
    V' = <[ ℓ := 0 ]>V → (* V' incorporates the new event in the threads view. *)
    mem_step (σ, p) (ThreadView V P B)
           (MEvAlloc ℓ v)
           (<[ℓ := {[ 0 := Msg v V' P ]}]>σ, p) (ThreadView V' P B)
  (* A normal non-atomic load. *)
  | MStepLoad σ V P B t ℓ (v : val) h p :
    σ !! ℓ = Some h →
    msg_val <$> (h !! t) = Some v →
    (default 0 (V !! ℓ)) ≤ t →
    mem_step (σ, p) (ThreadView V P B)
             (MEvLoad ℓ v)
             (σ, p) (ThreadView (<[ ℓ := t ]>V) P B)
  (* A normal non-atomic write. *)
  | MStepStore σ V P B t ℓ (v : val) h V' p :
    σ !! ℓ = Some h →
    (h !! t) = None → (* No event exists at t already. *)
    (V !!0 ℓ) ≤ t →
    V' = <[ℓ := t]>V → (* V' incorporates the new event in the threads view. *)
    mem_step (σ, p) (ThreadView V P B)
             (MEvStore ℓ v)
             (<[ℓ := <[t := Msg v ∅ P]>h]>σ, p) (ThreadView V' P B)
  (* An atomic acquire load. *)
  | MStepLoadAcquire σ V P B t ℓ (v : val) MV MP h V' p :
    σ !! ℓ = Some h →
    (h !! t) = Some (Msg v MV MP) →
    (V !!0 ℓ) ≤ t →
    V' = V ⊔ MV → (* FIXME: The lub here doesn't work (yet). *)
    mem_step (σ, p) (ThreadView V P B)
             (MEvLoad ℓ v)
             (σ, p) (ThreadView V' P B)
  (* An atomic release write. *)
  | MStepStoreRelease σ V P B t ℓ (v : val) h V' p :
    σ !! ℓ = Some h →
    (h !! t) = None → (* No event exists at t already. *)
    (V !!0 ℓ) ≤ t →
    V' = <[ ℓ := t ]>V → (* V' incorporates the new event in the threads view. *)
    mem_step (σ, p) (ThreadView V P B)
             (MEvStoreRelease ℓ v)
             (<[ℓ := <[t := Msg v V' P]>h]>σ, p) (ThreadView (<[ℓ := t]>V') P B)
  (* Read-modify-write instructions. *)
  (* | MStepRMW *)
  (* Write-back instruction. *)
  | MStepWB σ V P B ℓ t h p :
    σ !! ℓ = Some h →
    V !! ℓ = Some t → (* An equality here _should_ be fine, the timestamps are only lower bounds anyway? *)
    mem_step (σ, p) (ThreadView V P B)
             (MEvWB ℓ)
             (σ, p) (ThreadView V (<[ℓ := t]>P) B)
  (* Asynchronous fence. *)
  | MStepFence σ V P B p :
    mem_step (σ, p) (ThreadView V P B)
             MEvFence
             (σ, p) (ThreadView V (P ⊔ B) ∅)
  (* Synchronous fence. *)
  | MStepFenceSync σ V P B p :
    mem_step (σ, p) (ThreadView V P B)
             MEvFence
             (σ, p ⊔ P) (ThreadView V (P ⊔ B) ∅).

End memory.