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
From self.high Require Import dprop abstract_state_instances modalities
     resources crash_weakestpre weakestpre weakestpre_na weakestpre_at
     recovery_weakestpre lifted_modalities protocol no_buffer.
From self.high.modalities Require Import fence.

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
    let: "node" := ref_NA (InjL #()) in
    WB "node" ;;
    Fence ;;
    ref_AT "node".

(* Push takes as arguments the stack and the value to push to the stack. It
returns unit once the element has been pushed.*)
Definition push : expr :=
  λ: "toHead" "val",
    let: "toNext" := ref_NA #() in
    let: "newNode" := ref_NA (InjR ("val", "toNext")) in
    WB "newNode" ;;
    (rec: "loop" <> :=
       let: "head" := ! "toHead" in
       "toNext" <- "head" ;;
       WB "toNext" ;;
       Fence ;;
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

(*   Definition constant_prot (dv : discreteState val) (v : val) (hG : nvmDeltaG Σ) : dProp Σ := *)
(*     ⌜ dv.(get_discrete) = v ⌝. *)

(*   Program Instance : LocationProtocol constant_prot := { bumper n := n }. *)
(*   Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed. *)
(*   Next Obligation. iIntros (???) "? !> //". Qed. *)

(* End constant. *)

Section constant_alt.
  Context `{Σ : gFunctors}.
  Context `{nvmFixedG Σ}.

  Definition constant_prot `{nvmFixedG Σ} (v1 : val) (_ : unit) (v2 : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ⌜ v1 = v2 ⌝.

  Global Program Instance constant_inv_prot v : LocationProtocol (constant_prot v) := { bumper n := n }.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.
  Next Obligation. iIntros (????) "? !> //". Qed.

End constant_alt.

Section proof.
  Implicit Types (ℓ : loc).
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Definition mapsto_na_flushed `{AbstractState ST} ℓ q (s : ST) : dProp Σ :=
    ∃ (ss : list ST), ⌜ last ss = Some s ⌝ ∗ ℓ ↦{q} ss ∗ know_flush_lb ℓ s.

  (* We assume a per-element predicate. *)
  Context (ϕ : val → nvmDeltaG Σ → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a nD, IntoCrashFlush (ϕ a nD) (ϕ a),
            ∀ a nD, IntoNoBuffer (ϕ a nD) (ϕ a nD)}.

  (* There are four types of locations in the stack:
     * toHead - AT - The pointer to the first element in the stack.
     * toNext - NA - The pointer from a node to it's successor, this node is
       changed up to a point after which it is never changed.
     * node - NA - Points to the injection for each node. This pointer is never
       changed.
   *)

  Definition toNext_prot : loc_pred (singl loc) :=
    λ '(mk_singl ℓ) v _, ⌜ v = #ℓ ⌝%I.

  Definition nil_node_prot := constant_prot (InjLV #()).

  Definition cons_node_prot (x : val) (ℓtoNext : loc) :=
    λ (_ : unit) (v : val) (hG : nvmDeltaG Σ),
      (⌜ v = (x, #ℓtoNext)%V ⌝ ∗
       ϕ x hG)%I.

  Program Instance toNext_prot_prot :
    LocationProtocol toNext_prot := { bumper n := n }.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  Program Instance cons_node_prot_prot x ℓ :
    LocationProtocol (cons_node_prot x ℓ) := { bumper n := n }.
  Next Obligation.
    iIntros (?????).
    rewrite /cons_node_prot.
    iDestruct 1 as "[A B]".
    iCrashFlush. naive_solver.
  Qed.
  Next Obligation. iIntros. iModIntro. done. Qed.

  (* Representation predicate for a node. *)
  Fixpoint is_node ℓnode (xs : list val) : dProp Σ :=
    match xs with
    | [] =>
        ∃ q, ℓnode ↦{q} [()] ∗ know_protocol ℓnode nil_node_prot
    | x :: xs' => ∃ ℓtoNext ℓnext q1 q2,
        ℓnode ↦{q1} [()] ∗
        know_protocol ℓnode (cons_node_prot x ℓtoNext) ∗
        know_protocol ℓtoNext toNext_prot ∗
        mapsto_na_flushed ℓtoNext q2 (mk_singl ℓnext) ∗
        (* know_protocol ℓnext (constant_prot #ℓnode) ∗ *)
        is_node ℓnext xs'
    end.

  (* The invariant for the location that points to the first node in the
  stack. *)
  Definition toHead_prot (_ : unit) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ∃ (ℓnode : loc) xs,
      ⌜ v = #ℓnode ⌝ ∗
      is_node ℓnode xs ∗
      know_store_lb ℓnode () ∗
      know_flush_lb ℓnode ().

  Program Instance stack_inv_prot : LocationProtocol (toHead_prot) := { bumper n := n }.
  Next Obligation.
    iIntros (???).
    rewrite /toHead_prot.
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
    ∃ (ℓtoHead : loc), ⌜ v = #ℓtoHead ⌝ ∗ know_protocol ℓtoHead toHead_prot.

  Lemma wp_mk_stack :
    {{{ True }}}
      mk_stack #()
    {{{ v, RET v; is_stack v }}} .
  Proof.
    iIntros (Φ) "_ ϕpost".
    rewrite /mk_stack.
    wp_pures.
    wp_pures.
    wp_bind (ref_NA _)%E.
    iApply (wp_alloc_na _ () nil_node_prot with "[]"). { done. }
    iNext. iIntros (ℓnil) "[#nilProt nilPts]".
    iDestruct (mapsto_na_store_lb with "nilPts") as "#storeLb"; first done.
    wp_pures.
    wp_bind (WB _)%E.
    iApply (wp_wb_lb with "[$]"). iIntros "!>". iIntros "#flushLb".
    wp_pures.
    wp_bind Fence.
    iApply wp_fence.
    do 2 iModIntro.
    wp_pures.
    iApply (wp_alloc_at _ () toHead_prot with "[flushLb nilPts]"). {
      rewrite /toHead_prot.
      iExists _, [].
      iSplitPure; first reflexivity.
      iFrame "#".
      iExists _. iFrame. }
    iNext. iIntros (?) "(hi & ho & hip)".
    iApply "ϕpost".
    iExists _. naive_solver.
  Qed.

End proof.
