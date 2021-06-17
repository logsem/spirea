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
From self.high Require Import dprop resources crash_weakestpre weakestpre
     recovery_weakestpre lifted_modalities.

(* TODO: Add the necessary fences in this example. *)

(* A node is a pointer to a value and a pointer to the next node. *)
(* NOTE: The [mk_node] function is currently unused. *)
Definition mk_node : expr :=
  λ: "v" "next",
    let: "val" := ref "v" in
    let: "toNext" := ref "next" in
    ref (InjR ("val", "toNext")).

Definition mk_nil : expr :=
  λ: <>, ref (InjL #()).

Definition mk_stack : expr :=
  λ: <>,
    let: "toHead" := ref (mk_nil #()) in
    "toHead".

(* Push takes as arguments the stack and the value to push to the stack. It
returns unit once the element has been pushed.*)
Definition push : expr :=
  λ: "toHead" "val",
    let: "toVal" := ref "val" in
    let: "toNext" := ref #() in
    let: "newNode" := ref (InjR ("val", "toNext")) in
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
  
