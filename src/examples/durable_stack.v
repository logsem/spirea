(* This in an implementation of a concurrent non-blocking stack.

The stack is implemented as a linked list. *)

From iris.bi Require Import lib.fractional.
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
       let: "head" := !{acq} "toHead" in
       "toNext" <- "head" ;;
       WB "toNext" ;;
       Fence ;;
       if: CAS "toHead" "head" "newNode"
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

Section constant_prot.
  Context `{Σ : gFunctors}.
  Context `{nvmFixedG Σ}.

  Definition constant_prot `{nvmFixedG Σ} (v1 : val) (_ : unit) (v2 : val)
             (hG : nvmDeltaG Σ) : dProp Σ :=
    ⌜ v1 = v2 ⌝.

  Global Program Instance constant_prot_prot v :
    LocationProtocol (constant_prot v) := { bumper n := n }.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

End constant_prot.

Definition mapsto_na_flushed `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}
           ℓ q (s : ST) : dProp Σ :=
  ∃ (ss : list ST), ⌜ last ss = Some s ⌝ ∗ ℓ ↦{q} ss ∗ know_flush_lb ℓ s.

Global Instance buffer_free_mapsto_na_flushed `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}
       ℓ q (s : ST) :
  BufferFree (mapsto_na_flushed ℓ q s).
Proof. apply _. Qed.

Lemma mapsto_na_flushed_agree `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}
      ℓ q q' (s s' : ST) :
  mapsto_na_flushed ℓ q s -∗ mapsto_na_flushed ℓ q' s' -∗ ⌜ s = s' ⌝.
Proof.
  rewrite /mapsto_na_flushed.
  iDestruct 1 as (ss last) "[pts lb]".
  iDestruct 1 as (ss' last') "[pts' lb']".
  iNamed "pts".
  iDestruct "pts'" as (?????) "(? & ? & ? & %look & %nolater' & ? & ? & ? & ? & ? & ? & ?)".
  iDestruct (ghost_map_elem_agree with "hist [$]") as %<-%(inj _).
  iPureIntro.
  apply (inj Some).
  rewrite -last -last' -lookupV -look.
  f_equiv.
  eapply map_no_later_Some_agree; try done.
  - eexists _. rewrite lookupV. done.
  - eexists _. rewrite look. done.
Qed.

Lemma mapsto_na_flushed_split `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST} ℓ p q (s : ST) :
  mapsto_na_flushed ℓ (p + q) s -∗
  mapsto_na_flushed ℓ p s ∗ mapsto_na_flushed ℓ q s.
Proof.
  iDestruct 1 as (ss last) "[[pts1 pts2] #flushLb]".
  iSplitL "pts1"; iFrame "flushLb"; iExists ss; iFrame (last) "∗".
Qed.

Global Instance mapsto_na_flushed_fractional
       `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST} ℓ (s : ST) :
  Fractional (λ q, mapsto_na_flushed ℓ q s).
Proof.
  rewrite /Fractional.
  intros p q.
  iSplit.
  - iApply mapsto_na_flushed_split.
  - iIntros "[L R]".
    iDestruct "R" as (ss last) "[[pts1 pts2] #flushLb]".
    iDestruct "L" as (? ?) "[[pts1' pts2'] _]".
    (* This direction is more annoying to show (not impossible) *)
Abort.
  
(* Global Instance mapsto_na_flushed_as_fractional `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST} per l q v : *)
(*   AsFractional (mapsto_na per l q v) (λ q, mapsto_na per l q v)%I q. *)
(* Proof. split; [done | apply _]. Qed. *)

Section definitions.
  Implicit Types (ℓ : loc).
  Context `{nvmFixedG Σ}.

  (* We assume a per-element predicate. *)
  Context (ϕ : val → nvmDeltaG Σ → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a nD, IntoCrashFlush (ϕ a nD) (ϕ a),
            ∀ a nD, BufferFree (ϕ a nD)}.

  (* There are four types of locations in the stack:
     * toHead - AT - The pointer to the first element in the stack.
     * toNext - NA - The pointer from a node to it's successor, this node is
       changed up to a point after which it is never changed.
     * node - NA - Points to the injection for each node. This pointer is never
       changed.
   *)

  Definition toNext_prot : loc_pred (singl val) :=
    λ '(mk_singl v) v' _, ⌜ v = v' ⌝%I.

  Definition nil_node_prot := constant_prot (InjLV #()).

  Definition cons_node_prot (x : val) (ℓtoNext : loc) :=
    λ (_ : unit) (v : val) (hG : nvmDeltaG Σ),
      (⌜ v = InjRV (x, #ℓtoNext)%V ⌝ ∗
       ϕ x hG)%I.

  Program Instance toNext_prot_prot :
    LocationProtocol toNext_prot := { bumper n := n }.
  Next Obligation. Admitted.
  Next Obligation. destruct s. apply _. Qed.

  Program Instance cons_node_prot_prot x ℓ :
    LocationProtocol (cons_node_prot x ℓ) := { bumper n := n }.
  Next Obligation.
    iIntros (?????).
    rewrite /cons_node_prot.
    iDestruct 1 as "[A B]".
    iCrashFlush. naive_solver.
  Qed.

  (* Representation predicate for a node. *)
  Fixpoint is_node `{nvmDeltaG Σ} ℓnode (xs : list val) : dProp Σ :=
    match xs with
    | [] =>
        ∃ q, ℓnode ↦{q} [()] ∗ know_protocol ℓnode nil_node_prot
    | x :: xs' => ∃ (ℓtoNext ℓnext : loc) q1 q2,
        ℓnode ↦{q1} [()] ∗
        know_protocol ℓnode (cons_node_prot x ℓtoNext) ∗
        know_protocol ℓtoNext toNext_prot ∗
        mapsto_na_flushed ℓtoNext q2 (mk_singl #ℓnext) ∗
        (* know_protocol ℓnext (constant_prot #ℓnode) ∗ *)
        is_node ℓnext xs'
    end.

  Global Instance into_no_buffer_is_node `{nvmDeltaG Σ} ℓnode xs :
    IntoNoBuffer (is_node ℓnode xs) (is_node ℓnode xs).
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs]; apply _.
  Qed.

  Lemma is_node_split `{nvmDeltaG Σ} ℓnode xs :
    is_node ℓnode xs -∗ is_node ℓnode xs ∗ is_node ℓnode xs.
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (q) "([pts1 pts2] & #r)".
      iSplitL "pts1"; iFrame "r"; naive_solver.
    - iDestruct 1 as (? ? ? ?) "([pts1 pts2] & #? & #? & toNextPts & node)".
      rewrite -(Qp_div_2 q2).
      iDestruct (mapsto_na_flushed_split with "toNextPts") as "[toNextPts1 toNextPts2]".
      iDestruct (IH with "node") as "[node1 node2]".
      iSplitL "pts1 toNextPts1 node1".
      + repeat iExists _. iFrame. iFrame "#".
      + repeat iExists _. iFrame. iFrame "#".
  Qed.

  (* The invariant for the location that points to the first node in the
  stack. *)
  Definition toHead_prot `{nvmDeltaG Σ} (_ : unit) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ∃ (ℓnode : loc) xs,
      "%vEqNode" ∷ ⌜ v = #ℓnode ⌝ ∗
      "isNode" ∷ is_node ℓnode xs ∗
      "#nodeFlushLb" ∷ know_flush_lb ℓnode ().

  Program Instance stack_inv_prot `{nvmDeltaG Σ} : LocationProtocol (toHead_prot) := { bumper n := n }.
  Next Obligation.
    iIntros (????).
    rewrite /toHead_prot.
    iNamed 1.
    iDestruct "nodeFlushLb" as "-#nodeFlushLb".
    iCrashFlush.
    iExists ℓnode, _.
    iFrame.
  Admitted.
  (*   naive_solver. *)
  (* Qed. *)

  (* The representation predicate for the entire stack. *)
  Definition is_stack `{nvmDeltaG Σ} (v : val) : dProp Σ :=
    ∃ (ℓtoHead : loc),
      ⌜ v = #ℓtoHead ⌝ ∗
      know_protocol ℓtoHead toHead_prot ∗
      ⎡ is_shared_loc ℓtoHead ⎤ ∗
      know_store_lb ℓtoHead ().

End definitions.

Section proof.
  Implicit Types (ℓ : loc).
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Context (ϕ : val → nvmDeltaG Σ → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a nD, IntoCrashFlush (ϕ a nD) (ϕ a),
            ∀ a nD, BufferFree (ϕ a nD)}.

  Lemma is_stack_post_crash ℓ :
    is_stack ϕ #ℓ -∗ <PC> _, or_lost ℓ (is_stack ϕ #ℓ).
  Proof.
    rewrite /is_stack.
    iDestruct 1 as (? [= <-]) "prot".
    iDestruct "prot" as "(a & b & c)".
    iDestruct (post_crash_know_store_lb with "c")  as "c".
    iCrash.
    iCombine "a b c" as "a".
    rewrite 2!or_lost_sep.
    iApply (or_lost_mono with "[] a").
    iIntros "(a & b & (%u & c))". destruct u. iExists _. iSplitPure; first done.
    iFrame.
  Qed.

  (* Lemma is_stack_post_crash_flushed ℓ : *)
  (*   is_stack ϕ #ℓ -∗ <PCF> _, or_lost ℓ (is_stack ϕ #ℓ). *)
  (* Proof. *)
  (*   rewrite /is_stack. *)
  (*   iDestruct 1 as (? [= <-]) "prot". *)
  (*   iCrashFlush. *)
  (*   iApply (or_lost_mono with "[] prot"). *)
  (*   iIntros "prot". iExists _. iSplitPure; first done. iFrame "prot". *)
  (* Qed. *)

  Lemma wp_mk_stack :
    {{{ True }}}
      mk_stack #()
    {{{ v, RET v; is_stack ϕ v }}} .
  Proof.
    iIntros (Φ) "_ ϕpost".
    rewrite /mk_stack.
    wp_pures.
    wp_apply (wp_alloc_na _ () nil_node_prot with "[//]").
    iIntros (ℓnil) "[#nilProt nilPts]".
    iDestruct (mapsto_na_store_lb with "nilPts") as "#storeLb"; first done.
    wp_pures.
    wp_apply (wp_wb_lb with "[$]").
    assert (Persistent (<fence> know_flush_lb ℓnil ())). {
      (* For some reason Coq is super slow to resolve this [Persistent] instance. *)
      (* Set Typeclasses Debug. *)
      (* Set Typeclasses Debug Verbosity 2. *)
      apply post_fence_persistent.
      apply _. }
    iIntros "#flushLb".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.
    iApply (wp_alloc_at _ () (toHead_prot ϕ) with "[flushLb nilPts]"). {
      rewrite /toHead_prot.
      iExists _, [].
      iSplitPure; first reflexivity.
      iFrame "#".
      iExists _. iFrame. }
    iNext. iIntros (?) "(hi & ho & hip)".
    iApply "ϕpost".
    iExists _. naive_solver.
  Qed.

  Lemma wpc_push stack x s E :
    {{{ is_stack ϕ stack ∗ ϕ x _ }}}
      push stack x @ s ; E
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#(%ℓstack & -> & #(stackProt & stackSh & stackLb)) phi] ϕpost".
    rewrite /push.
    wp_pures.
    wp_apply (wp_alloc_na _ (mk_singl _) toNext_prot with "[//]").
    iIntros (ℓtoNext) "[#toNextProt toNextPts]".
    wp_pures.
    wp_apply (wp_alloc_na _ () (cons_node_prot ϕ x ℓtoNext) with "[phi]").
    { rewrite /cons_node_prot. iFrame. done. }
    iIntros (ℓnode) "[#nodeProt nodePts]".
    wp_pures.
    wp_apply (wp_wb_ex with "nodePts"); first reflexivity.
    iIntros "[nodePts #nodeFlushLb]".
    wp_pure1. wp_pure1. wp_pure1.
    iAssert (∃ xs x', ⌜ last xs = Some x' ⌝ ∗ ℓtoNext ↦ xs)%I with "[toNextPts]" as "toNextPts".
    { iExists _, _. iFrame. done. }
    iLöb as "IH".
    iDestruct "toNextPts" as (xs' x' lastEq) "toNextPts".
    wp_pures.

    (* The load of the pointer to the head. *)
    wp_apply (wp_load_at _ _ (λ _ v, (∃ (ℓhead : loc) xs, ⌜v = #ℓhead⌝ ∗ is_node ϕ ℓhead xs)%I) with "[]").
    { iFrame "stackProt stackSh stackLb".
      iModIntro.
      iIntros ([] v le) "toHead".
      iNamed "toHead".
      iDestruct (is_node_split with "isNode") as "[node1 node2]".
      iSplitL "node1".
      { iExists _, _. iSplitPure; first done. iFrame "node1". }
      repeat iExists _. iFrame "#". iFrame "node2". done. }
    iIntros ([] v) "[storeLb fence]".

    wp_pures.
    wp_apply (wp_store_na _ _ _ _ _ (mk_singl v) with "[$toNextPts]").
    { done. } { done. }
    { iFrame "toNextProt". done. }
    simpl.
    iIntros "toNextPts".
    wp_pures.
    wp_apply (wp_wb_ex with "toNextPts"). { apply last_app. done. }
    iIntros "[toNextPts #toNextPtsFl]".
    wp_pures.
    wp_apply wp_fence. do 2 iModIntro.
    iDestruct "fence" as (ℓhead xs ->) "isNode".
    wp_pures.

    wp_apply (wp_cas_at (λ _, True)%I (λ _, True)%I with "[nodePts toNextPts isNode]").
    { iFrame "stackProt stackSh stackLb".
      iSplit.
      { iIntros (??). iSplitL "". { iIntros "!> $". rewrite left_id. iAccu. }
        simpl. iIntros "_". simpl. rewrite right_id.
        rewrite /toHead_prot.
        iExists _, (x :: xs).
        iSplitPure; first done.
        iFrame "nodeFlushLb".
        simpl.
        iExists _, _ , _, _.
        iFrame "nodeProt".
        iFrame "toNextProt".
        iFrame "nodePts isNode".
        iExists _. iFrame "toNextPts". iFrame "toNextPtsFl".
        iPureIntro. apply last_app. done. }
      iIntros (??).
      iSplitL ""; first iIntros "!> $ //". iAccu. }
    iIntros (b) "[(-> & H & lb)|(%s' & -> & le & _ & (nodePts & toNextPts & isNode))]".
    (* The CAS succeeded. *)
    - wp_pures. iModIntro. iApply "ϕpost". done.
    (* The CAS failed. *)
    - wp_pure _.
      iApply ("IH" with "ϕpost nodePts [toNextPts]").
      { iExists _, _. iFrame "toNextPts". iPureIntro. apply last_app. done. }
    Unshelve. { apply (). }
  Qed.

End proof.
