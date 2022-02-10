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
From self.high Require Import proofmode wpc_proofmode or_lost.
From self.high Require Import dprop abstract_state_instances modalities
     resources crash_weakestpre weakestpre weakestpre_na weakestpre_at
     recovery_weakestpre lifted_modalities protocol no_buffer.
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
       let: "head" := !{acq} "toHead" in
       "toNext" <- "head" ;;
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
    let: "head" := !{acq} "toHead" in
    Fence ;;
    match: ! "head" with
      NONE => NONE
    | SOME "pair" =>
        let: "nextNode" := ! (Snd "pair") in
        if: CAS "toHead" "head" "nextNode"
        then SOME (Fst "pair")
        else "pop" "toHead"
    end.

Section constant_prot.
  Context `{Σ : gFunctors}.
  Context `{nvmFixedG Σ}.

  Program Definition constant_prot v1 : LocationProtocol unit :=
    {| pred := λ _ v2 _, ⌜ v1 = v2 ⌝%I;
       bumper v := v |}.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

End constant_prot.

Definition mapsto_na_flushed `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}
           ℓ (prot : LocationProtocol ST) q (s : ST) : dProp Σ :=
  ∃ (ss : list ST),
    "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗
    "pts" ∷ ℓ ↦_{prot}^{q} ss ∗
    "#flushLb" ∷ know_flush_lb ℓ prot s.

Section mapsto_na_flushed.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}.

  Global Instance buffer_free_mapsto_na_flushed ℓ prot q (s : ST) :
    BufferFree (mapsto_na_flushed ℓ prot q s).
  Proof. apply _. Qed.

  Lemma mapsto_na_flushed_agree ℓ prot q q' (s s' : ST) :
    mapsto_na_flushed ℓ prot q s -∗ mapsto_na_flushed ℓ prot q' s' -∗ ⌜ s = s' ⌝.
  Proof.
    rewrite /mapsto_na_flushed.
    iNamed 1.
    iDestruct 1 as (ss' last') "[pts' lb']".
    rewrite /mapsto_na. iNamed "pts".
    iDestruct "pts'" as (?????) "(? & ? & ? & %look & %nolater' & ? & ? & ? & ? & ? & ? & ?)".
    iDestruct (ghost_map_elem_agree with "hist [$]") as %<-%(inj _).
    iPureIntro.
    apply (inj Some).
    rewrite -lastEq -last' -lookupV -look.
    f_equiv.
    eapply map_no_later_Some_agree; try done.
    - eexists _. rewrite lookupV. done.
    - eexists _. rewrite look. done.
  Qed.

  Lemma mapsto_na_flushed_split ℓ prot p q (s : ST) :
    mapsto_na_flushed ℓ prot (p + q) s -∗
    mapsto_na_flushed ℓ prot p s ∗ mapsto_na_flushed ℓ prot q s.
  Proof.
    iDestruct 1 as (ss last) "[[pts1 pts2] #flushLb]".
    iSplitL "pts1"; iFrame "flushLb"; iExists ss; iFrame (last) "∗".
  Qed.

  Global Instance mapsto_na_flushed_fractional ℓ prot (s : ST) :
    Fractional (λ q, mapsto_na_flushed ℓ prot q s).
  Proof.
    rewrite /Fractional.
    intros p q.
    iSplit.
    - iApply mapsto_na_flushed_split.
    - iIntros "[L R]".
      iNamed "R".
      iDestruct "L" as (??) "[[pts1' pts2'] _]".
      (* This direction is more annoying to show (not impossible) *)
  Abort.

  Lemma mapsto_na_increasing_list ℓ p q (ss : list ST) :
    mapsto_na p ℓ q ss -∗ ⌜ increasing_list ss ⌝.
  Proof. rewrite /mapsto_na. iNamed 1. iFrame (incrList). Qed.

  (* Lemma foo (ss : list ST) s1 s2 : *)
  (*   increasing_list ss → last ss = Some s1 → s2 ∈ ss → s2 ⊑ s1. *)
  (* Proof. *)
  (*   Admitted. *)

  Global Instance mapsto_na_flushed_post_crash_flushed ℓ prot q (s : ST) :
    IntoCrashFlush (mapsto_na_flushed ℓ prot q s)
                   (λ _, mapsto_na_flushed ℓ prot q s ∗ recovered_at ℓ s)%I.
  Proof.
    rewrite /IntoCrashFlush.
    iNamed 1.
    (* iDestruct 1 as (? ss eq) "[pts lb]". *)
    iDestruct "flushLb" as "-#flushLb".
    (* We could leave out these two lines, but [iCrashFlush] takes a looong time
    to find the [IntoCrashFlush] instance. *)
    iDestruct (mapsto_na_increasing_list with "pts") as %incr.
    iDestruct (post_crash_mapsto_na with "pts") as "pts".
    iDestruct (post_crash_flush_post_crash with "pts") as "pts".
    iCrashFlush.
    iDestruct "flushLb" as (s' ?) "(#r & ?)".
    iDestruct (recovered_at_or_lost with "r pts") as "(%s'' & ? & pts & ?)".
    iDestruct (recovered_at_agree with "r [$]") as %<-.
    (* We can't prove that with this approach, but it is (will be) true. *)
  Admitted.
  (*   assert (s = s'). { eapply anti_symm. first apply H3. apply foo. } *)
  (*   iExists [s']. *)
  (*   iFrame. *)
  (* Qed. *)

End mapsto_na_flushed.

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

  Program Definition toNext_prot : LocationProtocol (singl val) :=
    {| pred := λ '(mk_singl v) v' _, ⌜ v = v' ⌝%I;
       bumper v := v |}.
  Next Obligation. iIntros (?[?]?) "H". iCrashFlush. done. Qed.
  Next Obligation. destruct s. simpl. apply _. Qed.
  
  (* Definition toNext_prot : loc_pred (singl val) := *)
  (*   λ '(mk_singl v) v' _, ⌜ v = v' ⌝%I. *)

  Definition nil_node_prot := constant_prot (InjLV #()).

  Definition cons_node_prot (x : val) (ℓtoNext : loc) :=
    constant_prot (InjRV (x, #ℓtoNext)).

    (* λ (_ : unit) (v : val) (hG : nvmDeltaG Σ), *)
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
  Fixpoint is_node `{nvmDeltaG Σ} ℓnode (xs : list val) : dProp Σ :=
    match xs with
    | [] => ∃ q,
        ℓnode ↦_{nil_node_prot}^{q} [()] ∗
        (* know_protocol ℓnode nil_node_prot ∗ *)
        know_flush_lb ℓnode nil_node_prot ()
    | x :: xs' => ∃ (ℓtoNext ℓnext : loc) q1 q2,
        (* ℓnode *)
        ℓnode ↦_{cons_node_prot x ℓtoNext}^{q1} [()] ∗
        (* know_protocol ℓnode (cons_node_prot x ℓtoNext) ∗ *)
        know_flush_lb ℓnode (cons_node_prot x ℓtoNext) () ∗
        (* ℓtoNext *)
        (* know_protocol ℓtoNext toNext_prot ∗ *)
        mapsto_na_flushed ℓtoNext toNext_prot q2 (mk_singl #ℓnext) ∗
        (* know_protocol ℓnext (constant_prot #ℓnode) ∗ *)
        is_node ℓnext xs'
    end.

  Global Instance into_no_buffer_is_node `{nvmDeltaG Σ} ℓnode xs :
    IntoNoBuffer (is_node ℓnode xs) (is_node ℓnode xs).
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs]; apply _.
  Qed.

  Global Instance into_crash_flushed_mapsto_na_flushed `{nvmDeltaG Σ} ℓnode xs :
    IntoCrashFlush (is_node ℓnode xs) (λ _, is_node ℓnode xs).
  Proof.
    rewrite /IntoCrashFlush.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (?) "(nodePts & lb)".
      iCrashFlush.
      iDestruct "lb" as ([] le) "(#rec & lb)".
      iDestruct (recovered_at_or_lost with "rec nodePts") as "nodePts".
      iDestruct "nodePts" as ([] elem) "(nodePts & ?)".
      iExists _. iFrame "nodePts". iFrame.
      iApply persist_lb_to_flush_lb.
      iFrame "lb".
    - iDestruct 1 as (????) "(nodePts & nodeFlushLb & toNextFlush & node)".
      iApply IH in "node".
      iCrashFlush.
      iDestruct "nodeFlushLb" as ([] ?) "(#nodeRec & toNextFlushLb)" .
      iDestruct "toNextFlush" as "[toNextFlush toNextRec]".
      iDestruct (recovered_at_or_lost with "nodeRec nodePts") as "nodePts".
      iDestruct "nodePts" as ([]?) "[nodePts _]".
      iExists _, _, _, q2.
      iFrame.
      iApply persist_lb_to_flush_lb.
      iFrame.
  Qed.

  Lemma is_node_split `{nvmDeltaG Σ} ℓnode xs :
    is_node ℓnode xs -∗ is_node ℓnode xs ∗ is_node ℓnode xs.
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (q) "([pts1 pts2] & #r)".
      iSplitL "pts1"; iFrame "r"; naive_solver.
    - iDestruct 1 as (????) "([pts1 pts2] & #? & toNextPts & node)".
      rewrite -(Qp_div_2 q2).
      iDestruct (mapsto_na_flushed_split with "toNextPts") as "[toNextPts1 toNextPts2]".
      iDestruct (IH with "node") as "[node1 node2]".
      iSplitL "pts1 toNextPts1 node1".
      + repeat iExists _. iFrame. iFrame "#".
      + repeat iExists _. iFrame. iFrame "#".
  Qed.

  (* The invariant for the location that points to the first node in the
  stack. *)
  Program Definition toHead_prot `{nvmDeltaG Σ} :=
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
  Definition is_stack `{nvmDeltaG Σ} (v : val) : dProp Σ :=
    ∃ (ℓtoHead : loc),
      ⌜ v = #ℓtoHead ⌝ ∗
      ⎡ is_at_loc ℓtoHead ⎤ ∗
      know_store_lb ℓtoHead toHead_prot ().

End definitions.

Section proof.
  Implicit Types (ℓ : loc).
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Context (ϕ : val → nvmDeltaG Σ → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a nD, IntoCrashFlush (ϕ a nD) (ϕ a),
            ∀ a nD, BufferFree (ϕ a nD),
            ∀ a nD, Persistent (ϕ a nD)}.

  Lemma is_stack_post_crash ℓ :
    is_stack ϕ #ℓ -∗ <PC> _, or_lost ℓ (is_stack ϕ #ℓ).
  Proof.
    rewrite /is_stack.
    iDestruct 1 as (? [= <-]) "prot".
    iDestruct "prot" as "(a & c)".
    iDestruct (post_crash_know_store_lb with "c")  as "c".
    iCrash.
    iCombine "a c" as "a".
    rewrite !or_lost_sep.
    iApply (or_lost_mono with "[] a").
    iIntros "(a & (%u & c))". destruct u. iExists _. iSplitPure; first done.
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
    wp_apply (wp_wb_lb with "[$]").
    iIntros "#flushLb".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.
    iApply (wp_alloc_at _ () (toHead_prot ϕ) with "[flushLb nilPts]"). {
      rewrite /toHead_prot.
      iExists _, [].
      iSplitPure; first reflexivity.
      simpl. iFrame "#".
      iExists _. iFrame. }
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
    wp_apply (wp_alloc_na _ (mk_singl _) toNext_prot with "[]").
    { simpl. done. }
    iIntros (ℓtoNext) "toNextPts".
    wp_pures.
    wp_apply (wp_alloc_na _ () (cons_node_prot x ℓtoNext)).
    { done. } (* rewrite /cons_node_prot. iFrame. done. } *)
    iIntros (ℓnode) "nodePts".
    wp_pures.
    wp_apply (wp_wb_ex with "nodePts"); first reflexivity.
    iIntros "[nodePts #nodeFlushLb]".
    wp_pure1. wp_pure1. wp_pure1.
    iAssert (∃ xs x', ⌜ last xs = Some x' ⌝ ∗ ℓtoNext ↦_{_} xs)%I with "[toNextPts]" as "toNextPts".
    { iExists _, _. iFrame. done. }
    iLöb as "IH".
    iDestruct "toNextPts" as (xs' x' lastEq) "toNextPts".
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
    wp_apply (wp_store_na _ _ _ _ _ (mk_singl v) with "[$toNextPts]").
    { done. } { done. }
    { simpl. done. }
    simpl.
    iIntros "toNextPts".
    wp_pures.
    wp_apply (wp_wb_ex with "toNextPts"). { apply last_app. done. }
    iIntros "[toNextPts #toNextPtsFl]".
    wp_pures.
    wp_apply wp_fence. do 2 iModIntro.
    iDestruct "fence" as (ℓhead xs ->) "[isNode #phis]".
    wp_pures.

    wp_apply (wp_cas_at (λ _, True)%I (λ _, True)%I with "[nodePts toNextPts isNode]").
    { iFrame "stackSh stackLb".
      iSplit.
      { iIntros (??).
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
        iExists _, _ , _, _.
        iFrame "isNode".
        iFrame "nodePts nodeFlushLb".
        iExists _. iFrame "toNextPts toNextPtsFl".
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
      iDestruct "node" as (?) "(headPts & #headLb)".
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
      iDestruct "node" as (????) "(headPts & #headFlushLb & toNextPts & node)".
      wp_apply (wp_load_na with "[$headPts]").
      { done. }
      { iModIntro. iIntros (?) "#eq". iFrame "eq". iDestruct "eq" as "-#eq". 
        rewrite right_id. iAccu. }
      simpl.
      iIntros (v) "[headPts <-]".
      wp_pures.
      iNamed "toNextPts".
      wp_apply (wp_load_na with "[$pts]").
      { done. }
      { iModIntro. iIntros (?). rewrite /toNext_prot. iIntros "#eq".
        iFrame "eq". iDestruct "eq" as "-#eq". rewrite right_id. iAccu. }
      simpl.
      iIntros (?) "(toNextPts & <-)".
      wp_pures.

      wp_apply (wp_cas_at (λ _, True)%I (λ _, True)%I with "[node]").
      { iFrame "stackSh stackLb".
        iSplit.
        { iIntros (??).
          iSplitL "".
          { iIntros "!> $". naive_solver. }
          simpl. iIntros "_". simpl. rewrite right_id.
          rewrite /toHead_prot.
          iExists _, xs.
          iSplitPure; first done.
          iFrame "node phis". }
        iIntros (??).
        iSplitL ""; first iIntros "!> $ //". iAccu. }
      iIntros (b) "[(-> & H & lb)|(%h & -> & ?)]".
      * (* The CAS succeeded. *)
        wp_pures.
        (* Now we just need to load the value. *)
        iModIntro. iApply "ϕpost". iRight. iExists _. iFrame "phi". done.
      * (* The CAS failed. *)
        wp_pure _.
        iApply ("IH" with "ϕpost").
        Unshelve. { apply (). }
  Qed.

End proof.
