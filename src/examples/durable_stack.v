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
From self.high Require Import proofmode wpc_proofmode if_rec.
From self.high Require Import dprop abstract_state_instances modalities
     resources crash_weakestpre weakestpre weakestpre_na weakestpre_at
     recovery_weakestpre lifted_modalities protocol no_buffer mapsto_na_flushed.
From self.high.modalities Require Import fence.

(* TODO: Add the necessary fences in this example. *)

(* A node is a pointer to a value and a pointer to the next node. *)
(* NOTE: The [mk_node] function is currently unused. *)
(* Definition mk_node : expr := *)
(*   λ: "v" "next", *)
(*     let: "val" := ref_NA "v" in *)
(*     let: "toNext" := ref_NA "next" in *)
(*     ref_NA (InjR ("val", "toNext")). *)

(* Definition mk_nil : expr := *)
(*   λ: <>, ref_NA (InjL #()). *)

Definition mk_stack : expr :=
  λ: <>,
    let: "node" := ref_NA (InjL #()) in
    Flush "node" ;;
    Fence ;;
    ref_AT "node".

(* Push takes as arguments the stack and the value to push to the stack. It
returns unit once the element has been pushed.*)
Definition push : expr :=
  λ: "toHead" "val",
    let: "toNext" := ref_NA #() in
    let: "newNode" := ref_NA (InjR ("val", "toNext")) in
    Flush "newNode" ;;
  (rec: "loop" <> :=
      let: "head" := !_AT "toHead" in
       "toNext" <-_NA "head" ;;
       Flush "toNext" ;;
       Fence ;;
       if: CAS "toHead" "head" "newNode"
       then #()
       else "loop" #()
    ) #().

(* Pop takes the stack and returns an option that contains the first value or
none if the stack is empty. *)
Definition pop : expr :=
  rec: "pop" "toHead" :=
    let: "head" := !_AT "toHead" in
    Fence ;;
    match: !_NA "head" with
      NONE => NONE
    | SOME "pair" =>
        let: "nextNode" := !_NA (Snd "pair") in
        if: CAS "toHead" "head" "nextNode"
        then SOME (Fst "pair")
        else "pop" "toHead"
    end.

Section constant_prot.
  Context `{Σ : gFunctors}.
  Context `{nvmG Σ}.

  Program Definition constant_prot v1 : LocationProtocol unit :=
    {| pred := λ _ v2 _, ⌜ v1 = v2 ⌝%I;
       bumper v := v |}.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

End constant_prot.

Section definitions.
  Implicit Types (ℓ : loc).
  Context `{nvmG Σ}.

  (* We assume a per-element predicate. *)
  Context (ϕ : val → nvmDeltaG → dProp Σ).
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

  Program Definition toNext_prot : LocationProtocol (numbered val) :=
    {| pred := λ '(mk_numbered t v) v' _, ⌜ v = v' ⌝%I;
       bumper v := v |}.
  Next Obligation. iIntros (?[?]?) "H". iCrashFlush. done. Qed.
  Next Obligation. destruct s. simpl. apply _. Qed.

  (* Definition toNext_prot : loc_pred (singl val) := *)
  (*   λ '(mk_singl v) v' _, ⌜ v = v' ⌝%I. *)

  Definition nil_node_prot := constant_prot (InjLV #()).

  Definition cons_node_prot (x : val) (ℓtoNext : loc) :=
    constant_prot (InjRV (x, #ℓtoNext)).

    (* λ (_ : unit) (v : val) (hG : nvmDeltaG), *)
    (*   (⌜ v = InjRV (x, #ℓtoNext)%V ⌝)%I. *)
    (* ∗ ϕ x hG)%I. *)

  (* Program Instance toNext_prot_prot : *)
  (*   LocationProtocol toNext_prot := { bumper n := n }. *)
  (* Next Obligation. iIntros (?[?]?) "H". iCrashFlush. done. Qed. *)
  (* Next Obligation. destruct s. apply _. Qed. *)

  (* Program Instance cons_node_prot_prot x ℓ : *)
  (*   LocationProtocol (cons_node_prot x ℓ) := { bumper n := n }. *)
  (* Next Obligation. *)
  (*   iIntros (?????). *)
  (*   rewrite /cons_node_prot. *)
  (*   iIntros "?". *)
  (*   (* iDestruct 1 as "[A B]". *) *)
  (*   iCrashFlush. naive_solver. *)
  (* Qed. *)

  (* Representation predicate for a node. *)
  Fixpoint is_node `{nvmDeltaG} ℓnode (xs : list val) : dProp Σ :=
    match xs with
    | [] => ∃ q ss,
        ℓnode ↦_{nil_node_prot}^{q} ss ∗
        (* know_protocol ℓnode nil_node_prot ∗ *)
        flush_lb ℓnode nil_node_prot ()
    | x :: xs' => ∃ (ℓtoNext ℓnext : loc) ss q1 q2 i,
        (* ℓnode *)
        ℓnode ↦_{cons_node_prot x ℓtoNext}^{q1} ss ∗
        (* know_protocol ℓnode (cons_node_prot x ℓtoNext) ∗ *)
        flush_lb ℓnode (cons_node_prot x ℓtoNext) () ∗
        (* ℓtoNext *)
        (* know_protocol ℓtoNext toNext_prot ∗ *)
        mapsto_na_flushed ℓtoNext toNext_prot q2 (mk_numbered i #ℓnext) ∗
        (* know_protocol ℓnext (constant_prot #ℓnode) ∗ *)
        is_node ℓnext xs'
    end.

  Global Instance into_no_buffer_is_node `{nvmDeltaG} ℓnode xs :
    IntoNoBuffer (is_node ℓnode xs) (is_node ℓnode xs).
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs]; apply _.
  Qed.

  Global Instance into_crash_flushed_mapsto_na_flushed `{nvmDeltaG} ℓnode xs :
    IntoCrashFlush (is_node ℓnode xs) (λ _, is_node ℓnode xs).
  Proof.
    rewrite /IntoCrashFlush.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (??) "(nodePts & lb)".
      iCrashFlush.
      iDestruct "lb" as "[#lb (% & ? & rec)]".
      iDestruct (crashed_in_if_rec with "rec nodePts") as "nodePts".
      iDestruct "nodePts" as (???) "(? & nodePts)".
      iExists _, _. iFrame "nodePts".
      iApply persist_lb_to_flush_lb.
      iFrame "lb".
    - iDestruct 1 as (??????) "(nodePts & nodeFlushLb & toNextFlush & node)".
      iApply IH in "node".
      iCrashFlush.
      iDestruct "nodeFlushLb" as "[toNextLb (% & % & nodeRec)]".
      iDestruct "toNextFlush" as "[toNextFlush toNextRec]".
      iDestruct (crashed_in_if_rec with "nodeRec nodePts") as "nodePts".
      iDestruct "nodePts" as (???) "[? nodePts]".
      iExists _, _, _, _, _, _.
      rewrite !list_fmap_id.
      iFrame.
      iApply persist_lb_to_flush_lb.
      iFrame.
  Qed.

  Lemma is_node_split `{nvmDeltaG} ℓnode xs :
    is_node ℓnode xs -∗ is_node ℓnode xs ∗ is_node ℓnode xs.
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (q ?) "([pts1 pts2] & #r)".
      iSplitL "pts1"; iFrame "r"; naive_solver.
    - iDestruct 1 as (??????) "([pts1 pts2] & #? & toNextPts & node)".
      rewrite -(Qp_div_2 q2).
      iDestruct (mapsto_na_flushed_split with "toNextPts") as "[toNextPts1 toNextPts2]".
      iDestruct (IH with "node") as "[node1 node2]".
      iSplitL "pts1 toNextPts1 node1".
      + repeat iExists _. iFrame. iFrame "#".
      + repeat iExists _. iFrame. iFrame "#".
  Qed.

  (* The invariant for the location that points to the first node in the
  stack. *)
  Program Definition toHead_prot `{nvmDeltaG} :=
    {| pred (_ : unit) (v : val) _ :=
        (∃ (ℓnode : loc) xs,
          "%vEqNode" ∷ ⌜ v = #ℓnode ⌝ ∗
          "isNode" ∷ is_node ℓnode xs ∗
          "#phis" ∷ ([∗ list] x ∈ xs, ϕ x _))%I;
      bumper s := s;
    |}.
  Next Obligation.
    iIntros (????).
    iNamed 1.
    iCrashFlush.
    iExists ℓnode, _.
    iFrame. done.
  Qed.

  (* The representation predicate for the entire stack. *)
  Definition is_stack `{nvmDeltaG} (v : val) : dProp Σ :=
    ∃ (ℓtoHead : loc),
      ⌜ v = #ℓtoHead ⌝ ∗
      ⎡ is_at_loc ℓtoHead ⎤ ∗
      store_lb ℓtoHead toHead_prot ().

End definitions.

Section proof.
  Implicit Types (ℓ : loc).
  Context `{nvmG Σ, nvmDeltaG}.

  Context (ϕ : val → nvmDeltaG → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a nD, IntoCrashFlush (ϕ a nD) (ϕ a),
            ∀ a nD, BufferFree (ϕ a nD),
            ∀ a nD, Persistent (ϕ a nD)}.

  (* The stack is crash safe. *)
  Lemma is_stack_post_crash ℓ :
    is_stack ϕ #ℓ -∗ <PC> _, if_rec ℓ (is_stack ϕ #ℓ).
  Proof.
    iDestruct 1 as (? [= <-]) "prot".
    iDestruct "prot" as "(a & c)".
    iDestruct (post_crash_store_lb with "c")  as "c".
    iCrash.
    iModIntro.
    iDestruct "c" as ([]) "c".
    iExists _. iSplitPure; first done.
    iFrame.
    iApply persist_lb_to_store_lb. iFrame.
  Qed.

  Lemma wp_mk_stack :
    {{{ True }}}
      mk_stack #()
    {{{ v, RET v; is_stack ϕ v }}} .
  Proof.
    iIntros (Φ) "_ ϕpost".
    rewrite /mk_stack.
    wp_pures.
    wp_apply (wp_alloc_na _ () nil_node_prot with "[//]").
    iIntros (ℓnil) "nilPts".
    iDestruct (mapsto_na_store_lb with "nilPts") as "#storeLb"; first done.
    wp_pures.
    wp_apply (wp_flush_lb with "[$]").
    iIntros "[#flushLb _]".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.
    iApply (wp_alloc_at _ () (toHead_prot ϕ) with "[flushLb nilPts]"). {
      rewrite /toHead_prot.
      iExists _, [].
      iSplitPure; first reflexivity.
      simpl. iFrame "#".
      iExists _, _. iFrame. }
    iNext. iIntros (?) "(? & ?)".
    iApply "ϕpost".
    iExists _. naive_solver.
  Qed.

  Lemma wpc_push stack x s E :
    {{{ is_stack ϕ stack ∗ ϕ x _ }}}
      push stack x @ s ; E
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ)
      "[#(%ℓstack & -> & #(stackSh & stackLb)) #phi] ϕpost".
    rewrite /push.
    wp_pures.
    wp_apply (wp_alloc_na _ (mk_numbered 0 _) toNext_prot with "[]").
    { simpl. done. }
    iIntros (ℓtoNext) "toNextPts".
    wp_pures.
    wp_apply (wp_alloc_na _ () (cons_node_prot x ℓtoNext)).
    { done. } (* rewrite /cons_node_prot. iFrame. done. } *)
    iIntros (ℓnode) "nodePts".
    wp_pures.
    wp_apply (wp_flush_ex with "nodePts"); first reflexivity.
    iIntros "(nodePts & #nodeFlushLb & _)".
    wp_pure1. wp_pure1. wp_pure1.
    iAssert (∃ xs x', ⌜ last xs = Some x' ⌝ ∗ ℓtoNext ↦_{_} xs)%I with "[toNextPts]" as "toNextPts".
    { iExists _, _. iFrame. done. }
    iLöb as "IH".
    iDestruct "toNextPts" as (xs' [n' x'] lastEq) "toNextPts".
    wp_pures.

    (* The load of the pointer to the head. *)
    wp_apply (wp_load_at _ _ (λ _ v, (∃ (ℓhead : loc) xs, ⌜v = #ℓhead⌝ ∗ is_node ℓhead xs ∗ _)%I) with "[]").
    { iFrame "stackSh stackLb".
      iModIntro.
      iIntros ([] v le) "toHead".
      iNamed "toHead".
      iDestruct (is_node_split with "isNode") as "[node1 node2]".
      iSplitL "node1".
      { iExists _, _. iSplitPure; first done. iFrame "node1". rewrite left_id.
        iDestruct "phis" as "-#phis". iAccu. }
      repeat iExists _. iFrame "#". iFrame "node2". done. }
    iIntros ([] v) "[storeLb fence]".

    wp_pures.
    wp_apply (wp_store_na _ _ _ _ _ (mk_numbered (S n') v) with "[$toNextPts]").
    { done. } { apply numbered_le. lia. }
    { simpl. done. }
    simpl.
    iIntros "toNextPts".
    wp_pures.
    wp_apply (wp_flush_ex with "toNextPts"). { apply last_app. done. }
    iIntros "(toNextPts & #toNextPtsFl & _)".
    wp_pures.
    wp_apply wp_fence. do 2 iModIntro.
    iDestruct "fence" as (ℓhead xs ->) "[isNode #phis]".
    wp_pures.

    wp_apply (wp_cas_at (λ _, True)%I (λ _, True)%I with "[nodePts toNextPts isNode]").
    { iFrame "stackSh stackLb".
      iIntros (???).
      iSplitL "". { iIntros "_". iPureIntro. left. done. }
      iSplit.
      { iSplitPure. { destruct s_l. reflexivity. }
        iSplitL "". { iIntros (???) "??". done. }
        iSplitL "".
        { iIntros "!>". iNamed 1. iSplitL "isNode".
          - repeat iExists _. iFrame "∗#". done.
          - iAccu. }
        simpl. iIntros "_". simpl. rewrite right_id.
        rewrite /toHead_prot.
        iExists _, (x :: xs). (* FIXME! *)
        iSplitPure; first done.
        iFrame "phi phis".
        (* iFrame "nodeFlushLb". *)
        iExists _, _ , _, _, _.
        iFrame "isNode".
        iFrame "nodePts nodeFlushLb".
        iExists _, _. iFrame "toNextPts toNextPtsFl".
        iPureIntro. apply last_app. done. }
      iSplitL ""; first iIntros "!> $ //". iAccu. }
    iIntros (b ?) "[(-> & H & lb)|(-> & le & _ & (nodePts & toNextPts & isNode))]".
    (* The CAS succeeded. *)
    - wp_pures. iModIntro. iApply "ϕpost". done.
    (* The CAS failed. *)
    - wp_pure _.
      iApply ("IH" with "ϕpost nodePts [toNextPts]").
      { iExists _, _. iFrame "toNextPts". iPureIntro. apply last_app. done. }
  Qed.

  Lemma wpc_pop stack s E :
    {{{ is_stack ϕ stack }}}
      pop stack @ s ; E
    {{{ v, RET v;
        (⌜ v = NONEV ⌝) ∨ (∃ x, ⌜ v = InjRV x ⌝ ∗ ϕ x _) }}}.
  Proof.
    iIntros (Φ) "#(%ℓstack & -> & #(stackSh & stackLb)) ϕpost".
    rewrite /pop.
    wp_pure1.
    iLöb as "IH".
    wp_pures.
    wp_apply (wp_load_at _ _
      (λ _ v, (∃ (ℓhead : loc) xs, ⌜v = #ℓhead⌝ ∗ is_node ℓhead xs ∗ _)%I) with "[]").
    { iFrame "stackSh stackLb".
      iModIntro.
      iIntros ([] v le) "toHead".
      iNamed "toHead".
      iDestruct (is_node_split with "isNode") as "[node1 node2]".
      iSplitL "node1".
      { iExists _, _. iSplitPure; first done. iFrame "node1". rewrite left_id.
        iDestruct "phis" as "-#phis". iAccu. }
      repeat iExists _. iFrame "#". iFrame "node2". done. }
    iIntros ([] v) "[storeLb fence]".
    wp_pures.
    wp_apply wp_fence. do 2 iModIntro.
    iDestruct "fence" as (ℓhead xs ->) "[node #phis]".
    wp_pures.
    destruct xs as [|x xs]; simpl.
    - (* The queue is empty. *)
      iDestruct "node" as (??) "(headPts & #headLb)".
      iDestruct (mapsto_na_last with "headPts") as %[[]?].
      wp_apply (wp_load_na with "[$headPts]").
      { done. }
      { iModIntro. iIntros (?). rewrite /constant_prot. iIntros "#eq".
        iFrame "eq". iDestruct "eq" as "-#eq". rewrite right_id. iAccu. }
      iIntros (v) "(headPts & <-)".
      wp_pures.
      iModIntro.
      iApply "ϕpost". iLeft. done.
    - (* The queue is non-empty. *)
      iDestruct "phis" as "[phi phis]".
      iDestruct "node" as (??????) "(headPts & #headFlushLb & toNextPts & node)".
      iDestruct (mapsto_na_last with "headPts") as %[[]?].
      wp_apply (wp_load_na with "[$headPts]").
      { done. }
      { iModIntro. iIntros (?) "#eq". iFrame "eq". iDestruct "eq" as "-#eq".
        rewrite right_id. iAccu. }
      simpl.
      iIntros (v) "[headPts <-]".
      wp_pures.
      rewrite /mapsto_na_flushed. iNamed "toNextPts".
      wp_apply (wp_load_na with "[$pts]").
      { done. }
      { iModIntro. iIntros (?). rewrite /toNext_prot. iIntros "#eq".
        iFrame "eq". iDestruct "eq" as "-#eq". rewrite right_id. iAccu. }
      simpl.
      iIntros (?) "(toNextPts & <-)".
      wp_pures.

      wp_apply (wp_cas_at (λ _, True)%I (λ _, True)%I with "[node]").
      { iFrame "stackSh stackLb".
        iIntros (???).
        iSplitL "". { iIntros "_". iPureIntro. left. done. }
        iSplit.
        { iSplitPure. { destruct s_l. reflexivity. }
          iSplitL "". { iIntros (???) "??". done. }
          iSplitL "". { iIntros "!> $". naive_solver. }
          simpl. iIntros "_". simpl. rewrite right_id.
          rewrite /toHead_prot.
          iExists _, xs.
          iSplitPure; first done.
          iFrame "node phis". }
        (* iIntros (??). *)
        iSplitL ""; first iIntros "!> $ //". iAccu. }
      iIntros (b ?) "[(-> & H & lb)|(-> & ?)]".
      * (* The CAS succeeded. *)
        wp_pures.
        (* Now we just need to load the value. *)
        iModIntro. iApply "ϕpost". iRight. iExists _. iFrame "phi". done.
      * (* The CAS failed. *)
        wp_pure _.
        iApply ("IH" with "ϕpost").
  Qed.

End proof.
