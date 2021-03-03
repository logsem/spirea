(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.

(* FIXME: Can we just use [Definition] instead of [Notation] here? *)
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
  | MEvAllocN ℓ (len : nat) v
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
  (* Allocating a new location. *)
  | MStepAllocN σ V P B ℓ len v V' p :
   (∀ idx, idx < len → σ !! (ℓ + idx)%Z = None) → (* This is a fresh segment of the heap not already in use. *)
    V' = <[ ℓ := 0 ]>V → (* V' incorporates the new event in the threads view. *)
    mem_step (σ, p) (ThreadView V P B)
           (MEvAllocN ℓ len v)
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
  | MStepLoadAcquire σ V P B t ℓ (v : val) MV MP h p :
    σ !! ℓ = Some h →
    (h !! t) = Some (Msg v MV MP) →
    (V !!0 ℓ) ≤ t →
    mem_step (σ, p) (ThreadView V P B)
             (MEvLoad ℓ v)
             (σ, p) (ThreadView (V ⊔ MV) (P ⊔ MP) B) (* An acquire incorporates both the store view and the persistent view. *)
  (* An atomic release write. *)
  | MStepStoreRelease σ V P B t ℓ (v : val) h V' p :
    σ !! ℓ = Some h →
    (h !! t) = None → (* No event exists at t already. *)
    (V !!0 ℓ) ≤ t →
    V' = <[ ℓ := t ]>V → (* V' incorporates the new event in the threads view. *)
    mem_step (σ, p) (ThreadView V P B)
             (MEvStoreRelease ℓ v)
             (<[ℓ := <[t := Msg v V' P]>h]>σ, p) (ThreadView V' P B) (* A release releases both V' and P. *)
  (* Read-modify-write instructions. *)
  | MStepRMW σ ℓ h v MV MP V t V' P P' B p :
    σ !! ℓ = Some h →
    (h !! t) = Some (Msg v MV MP) → (* We read an event at time [t]. *)
    (V !!0 ℓ) ≤ t →
    (h !! (t + 1)) = None → (* The next timestamp is available, ensures that no other RMW read this event. *)
    V' = (<[ ℓ := t + 1 ]>(V ⊔ MV)) → (* V' incorporates the new event in the threads view. *)
    P' = P ⊔ MP →
    mem_step (σ, p) (ThreadView V P B)
             (MEvStoreRelease ℓ v)
             (<[ℓ := <[t := Msg v V' P']>h]>σ, p) (ThreadView V' P' B)
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