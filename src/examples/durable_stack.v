(* This in an implementation of a concurrent non-blocking stack.

The stack is implemented as a linked list. *)

From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop modalities resources crash_weakestpre weakestpre
     recovery_weakestpre lifted_modalities protocol no_buffer.

(* TODO: Add the necessary fences in this example. *)

(* A node is a pointer to a value and a pointer to the next node. *)
(* NOTE: The [mk_node] function is currently unused. *)
Definition mk_node : expr :=
  λ: "v" "next",
    let: "val" := ref_NA "v" in
    let: "toNext" := ref_NA "next" in
    ref_NA (InjR ("val", "toNext")).

Definition mk_nil : expr :=
  λ: <>, ref_NA (InjL #()).

Definition mk_stack : expr :=
  λ: <>,
    let: "toHead" := ref_NA (mk_nil #()) in
    "toHead".

(* Push takes as arguments the stack and the value to push to the stack. It
returns unit once the element has been pushed.*)
Definition push : expr :=
  λ: "toHead" "val",
    (* let: "toVal" := ref_NA "val" in *)
    let: "toNext" := ref_NA #() in
    let: "newNode" := ref_NA (InjR ("val", "toNext")) in
    (rec: "loop" <> :=
       let: "head" := ! "toHead" in
       "toNext" <- "head" ;;
       if: CAS "toHead" "head" "toNext"
       then #()
       else "loop" #()
    ) #().
    
(* Pop takes the stack and returns an option that contains the first value or
none if the stack is empty. *)
Definition pop : expr :=
  rec: "pop" "toHead" :=
    let: "head" := ! "toHead" in
    match: ! "head" with
      NONE => NONE
    | SOME "pair" =>
        let: "nextNode" := ! (Snd "pair") in
        if: CAS "toHead" "head" "nextNode"
        then SOME (! (Fst "pair"))
        else "pop" "toHead"
    end.

(* Section constant. *)
(*   Context `{nvmFixedG Σ}. *)

(*   Definition constant_inv (dv : discreteState val) (v : val) (hG : nvmDeltaG Σ) : dProp Σ := *)
(*     ⌜ dv.(get_discrete) = v ⌝. *)

(*   Program Instance : LocationProtocol constant_inv := { bumper n := n }. *)
(*   Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed. *)
(*   Next Obligation. iIntros (???) "? !> //". Qed. *)
  
(* End constant. *)

Section constant_alt.
  Context `{nvmFixedG Σ}.

  Definition constant_inv (v1 : val) (_ : unit) (v2 : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ⌜ v1 = v2 ⌝.

  Global Program Instance constant_inv_prot v : LocationProtocol (constant_inv v) := { bumper n := n }.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.
  Next Obligation. iIntros (????) "? !> //". Qed.
  
End constant_alt.
  
Section proof.
  Implicit Types (ℓ : loc).
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  (* We assume a per-element predicate. *)
  Context (ϕ : val → nvmDeltaG Σ → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a b, IntoCrashFlush (ϕ a b) (ϕ a),
            ∀ a b, IntoNoBuffer (ϕ a b) (ϕ a b)}.

  Definition node_inv (x : val) (ℓtoNext : loc) :=
    λ (_ : unit) (v : val) (hG : nvmDeltaG Σ),
      (⌜ v = (x, #ℓtoNext)%V ⌝ ∗ ϕ x hG)%I.

  Program Instance node_inv_prot x ℓ :
    LocationProtocol (node_inv x ℓ) := { bumper n := n }.
  Next Obligation.
    iIntros (?????).
    rewrite /node_inv.
    iDestruct 1 as "[A B]".
    iCrashFlush. naive_solver.
  Qed.
  Next Obligation. iIntros. iModIntro. done. Qed.

  (* Representation predicate for a node. *)
  Fixpoint is_node ℓ (xs : list val) : dProp Σ := 
    match xs with
    | [] => know_protocol ℓ (constant_inv (InjLV #()))
    | x :: xs' => ∃ ℓtoNext ℓnext,
        know_protocol ℓ (node_inv x ℓtoNext) ∗
        know_protocol ℓnext (constant_inv #ℓ) ∗
        is_node ℓnext xs'
    end.

  (* The invariant for the location that points to the first node in the
  stack. *)
  Definition stack_inv (_ : unit) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ∃ (ℓnode : loc) xs,
      ⌜ v = #ℓnode ⌝ ∗
      is_node ℓnode xs ∗
      know_store_lb ℓnode () ∗
      know_flush_lb ℓnode ().

  Program Instance stack_inv_prot : LocationProtocol (stack_inv) := { bumper n := n }.
  Next Obligation.
    iIntros (???).
    rewrite /stack_inv.
    iDestruct 1 as (??) "(A & B & stLb & flLb)".
    iCrashFlush.
    iExists ℓnode, _.
    iFrame.
  Admitted.
  (*   naive_solver. *)
  (* Qed. *)
  Next Obligation. iIntros. iModIntro. Admitted. (* done. Qed. *)

  (* The representation predicate for the entire stack. *)
  Definition is_stack (v : val) : dProp Σ :=
    ∃ (ℓtoHead : loc), ⌜ v = #ℓtoHead ⌝ ∗ know_protocol ℓtoHead stack_inv.

End proof.
