(* This in an implementation of a durable variant of the fine-grained concurrent
Treiber stack.

The stack is implemented as a linked list and the pointer to the head the list
is updated with a CAS. *)
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gmap_view.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra solve_view_le encode_relation map_extra view_slice.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high.lib Require Import abstract_state abstract_state_instances increasing_map protocols.
From self.high Require Import monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high Require Import weakestpre_at weakestpre_na weakestpre_exp proofmode.

From self.examples.lib Require Import excl_list.

From self Require Export lang.
From self.high Require Export dprop.

Section LocationAxioms.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, AbstractState ST}.

  Implicit Types (ℓ: loc) (σ s: ST) (prot: LocationProtocol ST).

  Lemma mapsto_na_agree ℓ q1 q2 prot ss1 ss2:
    ℓ ↦_{prot}^{q1} ss1 -∗
    ℓ ↦_{prot}^{q2} ss2 -∗
    ⌜ ss1 = ss2 ⌝.
  Proof.
  Admitted.

  Lemma mapsto_na_flushed_agree ℓ q1 q2 prot s1 s2:
    mapsto_na_flushed ℓ prot q1 s1 -∗
    mapsto_na_flushed ℓ prot q2 s2 -∗
    ⌜ s1 = s2 ⌝.
  Proof.
    iNamed 1.
    iIntros "(% & % & pts' & _)".
    iDestruct (mapsto_na_agree with "pts pts'") as %->.
    by simplify_eq.
  Qed.
End LocationAxioms.

(* A node is a pointer to a value and a pointer to the next node. *)
Definition nil : expr := InjL #().
Definition cons v toNext : expr := InjR (v, toNext).

Definition mk_stack : expr :=
  λ: <>,
    let: "node" := ref_NA nil in
    Flush "node" ;;
    Fence ;;
    ref_AT "node".

(* Push takes as arguments the stack and the value to push to the stack. It
returns unit once the element has been pushed.*)
Definition push : expr :=
  λ: "toHead" "val",
    let: "toNext" := ref_NA #() in
    let: "newNode" := ref_NA (cons "val" "toNext") in
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
  rec: "loop" "toHead" :=
    let: "head" := !_AT "toHead" in
    Fence ;;
    match: !_NA "head" with
      NONE => NONE
    | SOME "pair" =>
        let: "nextNode" := !_NA (Snd "pair") in
        if: CAS "toHead" "head" "nextNode"
        then SOME (Fst "pair")
        else "loop" "toHead"
    end.

Definition sync : expr :=
  λ: "toHead",
    Flush "toHead" ;;
    FenceSync.

Set Default Proof Using "Type*".

Section StackHist.
  Definition history := list (leibnizO (val + unit)).

  Implicit Types (h: history).
  
  #[global] Instance history_abstract_relation: AbstractState history :=
    {
      abs_state_relation h1 h2 := h1 `prefix_of` h2
    }.
  
  Fixpoint eval h (xs: list val): option (list val) :=
    match h with
    | [] => Some xs
    | inl v :: h' => eval h' (v :: xs)
    | inr () :: h' =>
        match xs with
        | [] => None
        | _ :: xs' => eval h' xs'
        end
    end.

  Lemma eval_app h1 h2 xs1 xs2 res:
    eval h1 xs1 = Some xs2 →
    eval h2 xs2 = res →
    eval (h1 ++ h2) xs1 = res.
  Proof.
    generalize dependent xs1.
    induction h1 as [ | [ | []] ]; simpl; intros; simplify_eq.
    - done.
    - apply IHh1; done.
    - destruct xs1; first done.
      apply IHh1; done.
  Qed.

  Lemma eval_app_None h1 h2 xs:
    eval h1 xs = None →
    eval (h1 ++ h2) xs = None.
  Proof.
    generalize dependent xs.
    induction h1 as [ | [ | []] ]; simpl; intros; simplify_eq.
    - apply IHh1; done.
    - destruct xs; first done.
      apply IHh1; done.
  Qed.
  
  Lemma eval_snoc_push h v xs:
    eval h [] = Some xs →
    eval (h ++ [inl v]) [] = Some (v :: xs).
  Proof.
    intros.
    eapply eval_app; done.
  Qed.

  Lemma eval_snoc_pop h v xs:
    eval h [] = Some (v :: xs) →
    eval (h ++ [inr ()]) [] = Some xs.
  Proof.
    intros.
    eapply eval_app; done.
  Qed.

  (* this assertion doesn't specify that [last h1] is [push v], which should be obtained somewhere from context. *)
  Definition paired h1 h2 :=
    ∃ h__int, h2 = h1 ++ h__int ++ [inr ()] ∧ eval h__int [] = Some [].

  Lemma paired_unique_aux h1 h2 h2':
    paired h1 h2 →
    paired h1 h2' →
    h2 `prefix_of` h2' →
    h2 = h2'.
  Proof.
    destruct 1 as (h__int & Happ & Heval).
    destruct 1 as (h__int' & Happ' & Heval').
    destruct 1 as [h3 Heq].
    simplify_eq.
    rewrite -?app_assoc in Heq.
    apply app_inv_head in Heq.
    destruct (last h3) as [ op | ] eqn:Heq'.
    - apply last_Some in Heq' as [h3' ->].
      rewrite ?app_assoc in Heq.
      apply app_inj_tail in Heq as [Heq <-].
      simplify_map_eq.
      pose proof (eval_app _ [inr ()] _ _ None Heval ltac:(done)) as Heval''.
      pose proof (eval_app_None _ h3' _ Heval'') as Heval'''.
      rewrite -?app_assoc in Heval', Heval'''.
      congruence.
    - rewrite last_None in Heq'.
      simplify_eq.
      rewrite app_nil_r in Heq.
      rewrite Heq //.
  Qed.

  Lemma paired_unique h1 h2 h2':
    paired h1 h2 →
    paired h1 h2' →
    h2 `prefix_of` h2' ∨ h2' `prefix_of` h2 →
    h2 = h2'.
  Proof.
    intros ?? [? | ?].
    - by eapply paired_unique_aux.
    - symmetry. by eapply paired_unique_aux.
  Qed.

  Lemma eval_snoc_push_inv h x x' xs xs':
    eval (h ++ [inl x]) xs = Some (x' :: xs') →
    eval h xs = Some xs' ∧ x = x'.
  Proof.
    intros.
    destruct (eval h xs) eqn:Heqn.
    - rewrite (eval_app _ [inl x] _ _ _ Heqn ltac:(done)) /= in H.
      by simplify_eq.
    - rewrite (eval_app_None _ [inl x] _ Heqn) in H.
      congruence.
  Qed.

  
  Lemma eval_snoc_pop_inv h xs xs':
    eval (h ++ [inr ()]) xs = Some xs' →
    ∃ x, eval h xs = Some (x :: xs').
  Proof.
    intros.
    destruct (eval h xs) eqn:Heqn.
    - rewrite (eval_app _ [inr ()] _ _ _ Heqn ltac:(done)) /= in H.
      destruct l; first done.
      simplify_eq.
      by eexists.
    - rewrite (eval_app_None _ [inr ()] _ Heqn) in H.
      congruence.
  Qed.
  
  (* Lemma eval_find_push n: ∀ h stk x xs, *)
  (*   length h ≤ n → *)
  (*   eval h stk = Some (x :: xs) → *)
  (*   (* Case 1: x came from the initial stack *) *)
  (*   (∃ popped, stk = popped ++ (x :: xs)) ∨ *)
  (*   (* Case 2: x was pushed by h *) *)
  (*   (∃ h1 h2, h = h1 ++ [inl x] ++ h2 ∧  *)
  (*             eval h2 [] = Some [] ∧  *)
  (*             eval h1 stk = Some xs). *)
  (* Proof. *)
  (*   induction n; simpl; intros ???? Hlength Heval. *)
  (*   - destruct h as [ | ]; last (simpl in *; lia). *)
  (*     simpl in Heval. *)
  (*     simplify_eq. *)
  (*     left. *)
  (*     by (exists []). *)
  (*   - destruct (last h) as [ [ | ] | ] eqn:Hlast. *)
  (*     + apply last_Some in Hlast as [h' ->]. *)
  (*       pose proof Heval as Heval'. *)
  (*       apply eval_snoc_push_inv in Heval' as [Heval' <-]. *)
  (*       right. *)
  (*       exists h', []. *)
  (*       done. *)
  (*     + apply last_Some in Hlast as [h' ->]. *)
  (*       rewrite length_app /= in Hlength. *)
  (*       assert (length h' ≤ n) as Hlength' by lia. *)
        
  (*     + rewrite last_None in Hlast. *)
  (*       rewrite Hlast /= in Heval. *)
  (*       simplify_eq. *)
  (*       left. *)
  (*       by (exists []). *)
  Lemma paired_exists_aux h x xs1 xs2:
    eval h [] = Some (xs1 ++ x :: xs2) →
    ∃ h1 h2, h = h1 ++ inl x :: h2 ∧ eval h2 [] = Some xs1.
  Proof.
    generalize dependent x.
    generalize dependent xs1.
    generalize dependent xs2.
    induction h as [ | [| []] ] using rev_ind; simpl; intros.
    - destruct xs1; simpl in *; congruence.
    - pose proof H as H'.
      destruct xs1; simpl in *.
      + apply eval_snoc_push_inv in H' as [? <-].
        exists h, [].
        split; done.
      + apply eval_snoc_push_inv in H' as [Heval <-].
        apply IHh in Heval as (h1 & h2 & -> & Heval).
        exists h1, (h2 ++ [inl v]).
        simplify_list_eq.
        split; first done.
        eapply eval_app; done.
    - pose proof H as H'.
      apply eval_snoc_pop_inv in H' as [x' Heval].
      rewrite app_comm_cons in Heval.
      apply IHh in Heval as (h1 & h2 & -> & Heval).
      exists h1, (h2 ++ [inr ()]).
      simplify_list_eq.
      split; first done.
      eapply eval_app; done.
  Qed.

  Lemma paired_exists h x xs:
    eval h [] = Some (x :: xs) →
    ∃ h__pop, last h__pop = Some (inl x) ∧ paired h__pop (h ++ [inr ()]).
  Proof.
    intros.
    apply (paired_exists_aux h x [] xs) in H as (h1 & h2 & -> & Heval).
    exists (h1 ++ [inl x]).
    split; first rewrite last_snoc //.
    exists h2.
    simplify_list_eq.
    done.
  Qed.
End StackHist.

Section definitions.
  Context `{!excl_listG (leibnizO (val + unit)) Σ Ω, !nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.

  (* We assume a per-element predicate. *)
  Context (ϕ : val → dProp Σ) (γ: gname).

  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a, IntoNGFlush (ϕ a) (ϕ a),
            ∀ a, BufferFree (ϕ a)}.

  Implicit Types (ℓ : loc) (h: history).
  (* There are four types of locations in the stack:
     * toHead - AT - The pointer to the first element in the stack.
     * toNext - NA - The pointer from a node to it's successor, this node is
       changed up to a point after which it is never changed.
     * node - NA - Points to the injection for each node. This pointer is never
       changed.
   *)

  Program Definition toNext_prot : LocationProtocol (numbered val) :=
    {|
      p_full := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
      p_read := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
      p_pers := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
      p_bumper v := v |}.

  Global Instance toNext_prot_conditions : ProtocolConditions toNext_prot.
  Proof.
    split; try apply _.
    - destruct s. simpl. apply _.
    - destruct s. simpl. apply _.
    - destruct s. simpl. apply _.
    - iIntros ([?] ?). rewrite /p_full /p_read /=.
      iSplit.
      + by iIntros.
      + iIntros "[% %]".
        iPureIntro.
        naive_solver.
    - rewrite /p_full /p_read /=.
      iIntros ([?] ? [?] ? _ _ ?).
      iSplit.
      + do 2 iModIntro.
        done.
      + iIntros ([?] ?) "!> % _ _".
        do 2 iModIntro.
        done.
    - rewrite /p_read /=.
      iIntros ([?] ?) "%".
      by iModIntro.
  Qed.

  Definition node_prot := discrete_prot.

  Definition cons_node v ℓtoNext := mk_discrete (InjRV (v, #ℓtoNext)).
  Definition nil_node := mk_discrete (InjLV #()).
  
  (* Definition nil_node_prot := constant_prot (InjLV #()). *)

  (* Definition cons_node_prot (x : val) (ℓtoNext : loc) := *)
  (*   constant_prot (InjRV (x, #ℓtoNext)). *)

  (* Representation predicate for a node. *)
  Fixpoint is_node ℓnode (xs : list val) : dProp Σ :=
    match xs with
    | [] => ∃ q,
        ℓnode ↦_{node_prot}^{q} [nil_node] ∗
        flush_lb ℓnode node_prot nil_node
    | x :: xs' => ∃ (ℓtoNext ℓnext : loc) q1 q2 i,
        (* ℓnode *)
        ℓnode ↦_{node_prot}^{q1} [cons_node x ℓtoNext] ∗
        flush_lb ℓnode (node_prot) (cons_node x ℓtoNext) ∗
        (* ℓtoNext *)
        mapsto_na_flushed ℓtoNext toNext_prot q2 (mk_numbered i #ℓnext) ∗
        is_node ℓnext xs'
  end.

  Global Instance into_no_buffer_is_node ℓnode xs :
    IntoNoBuffer (is_node ℓnode xs) (is_node ℓnode xs).
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs]; apply _.
  Qed.
  
  Global Instance is_node_into_ng_flushed ℓnode xs :
    IntoNGFlush (is_node ℓnode xs) (is_node ℓnode xs).
  Proof.
    rewrite /IntoNGFlush.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (?) "(nodePts & lb)".
      iModIntro.
      iDestruct "lb" as "[#lb (% & ? & rec)]".
      iDestruct (crashed_in_if_rec with "rec nodePts") as "nodePts".
      iDestruct "nodePts" as (?? [-> ->]%prefix_app_singleton) "(? & nodePts)".
      iExists _.
      simpl.
      iFrame "nodePts".
      iApply persist_lb_to_flush_lb.
      iFrame "lb".
    - iDestruct 1 as (?????) "(nodePts & nodeFlushLb & toNextFlush & node)".
      iApply IH in "node".
      iModIntro.
      iDestruct "nodeFlushLb" as "[toNextLb (% & % & nodeRec)]".
      iDestruct "toNextFlush" as "[toNextFlush toNextRec]".
      iDestruct (crashed_in_if_rec with "nodeRec nodePts") as "nodePts".
      iDestruct "nodePts" as (?? [-> ->]%prefix_app_singleton) "[? nodePts]".
      iExists _, _, _, _, _.
      fold is_node.
      rewrite !list_fmap_id.
      iFrame.
      iApply persist_lb_to_flush_lb.
      iFrame.
  Qed.

  Lemma is_node_split ℓnode xs :
    is_node ℓnode xs -∗ is_node ℓnode xs ∗ is_node ℓnode xs.
  Proof.
    generalize dependent ℓnode.
    induction xs as [|x xs IH]; iIntros (ℓnode).
    - iDestruct 1 as (q) "([pts1 pts2] & #r)".
      iSplitL "pts1"; iFrame "r"; naive_solver.
    - iDestruct 1 as (?????) "([pts1 pts2] & #? & toNextPts & node)".
      rewrite -(Qp.div_2 q2).
      iDestruct (mapsto_na_flushed_split with "toNextPts") as "[toNextPts1 toNextPts2]".
      iDestruct (IH with "node") as "[node1 node2]".
      iSplitL "pts1 toNextPts1 node1".
      + repeat iExists _. iFrame. iFrame "#".
      + repeat iExists _. iFrame. iFrame "#".
  Qed.

  (* TODO: need lemma about [mapsto_na] agreement. *)
  Lemma is_node_agree ℓnode xs1 xs2:
    is_node ℓnode xs1 -∗ is_node ℓnode xs2 -∗ ⌜ xs1 = xs2 ⌝.
  Proof.
    generalize dependent ℓnode.
    generalize dependent xs2.
    induction xs1 as [ | x1 xs1' ]; intros; destruct xs2 as [ | x2 xs2' ]; simpl.
    - naive_solver.
    - iDestruct 1 as (?) "[mapsto1 _]".
      iDestruct 1 as (?????) "[mapsto2 _]".
      iDestruct (mapsto_na_agree with "mapsto1 mapsto2") as %contra.
      inversion contra.
    - iDestruct 1 as (?????) "[mapsto1 _]".
      iDestruct 1 as (?) "[mapsto2 _]".
      iDestruct (mapsto_na_agree with "mapsto1 mapsto2") as %contra.
      inversion contra.
    - iDestruct 1 as (?????) "(mapsto1 & _ & toNext1 & node1)".
      iDestruct 1 as (?????) "(mapsto2 & _ & toNext2 & node2)".
      iDestruct (mapsto_na_agree with "mapsto1 mapsto2") as %?.
      simplify_eq.
      iDestruct (mapsto_na_flushed_agree with "toNext1 toNext2") as %?.
      simplify_eq.
      iDestruct (IHxs1' with "node1 node2") as %->.
      done.
  Qed.
  
  Definition ownϕ (h: history): dProp Σ :=
    match last h with
    | Some (inl v) => ϕ v ∨ ∃ h__pop, ⌜ paired h h__pop ⌝ ∗ ⎡ list_elem_with_rely γ h__pop ⎤
    | _ => emp%I
    end.

  Definition duplicable_inv h (v: val): dProp Σ :=
    ∃ (ℓnode : loc) xs,
      "%vEqNode" ∷ ⌜ v = #ℓnode ⌝ ∗
      "%eval" ∷ ⌜ eval h [] = Some xs ⌝ ∗
      "isNode" ∷ is_node ℓnode xs.

  Definition seen_states ℓ (h: history): dProp Σ :=
    ∀ h', ⌜ h' ≠ h ⌝ -∗ ⌜ h' `prefix_of` h ⌝ -∗ seen_state ℓ h'.
  
  Definition toHead_prots ℓ :=
    {| p_full (h : history) (v : val) := (⎡ list_auth γ h ⎤ ∗ duplicable_inv h v ∗ ownϕ h ∗ seen_states ℓ h)%I;
       p_read (h : history) (v : val) := (duplicable_inv h v ∗ ownϕ h)%I;
       p_pers (h : history) (v : val) := (⎡ list_token γ (length h) ⎤)%I;
       p_bumper s := s;
    |}.

  p_full ⊢ <NG> p_full.

  seen_states ℓ h ⊢ <NG> seen_states ℓ h                  

  #[global] Instance toHead_prot_conditions ℓ : ProtocolConditions (toHead_prots ℓ).
  Proof.
  Admitted.

  (* The representation predicate for the entire stack. *)
  Definition is_stack (ℓtoHead : loc) : dProp Σ :=
    ∃ h, ℓtoHead ↦_AT^{toHead_prots ℓtoHead} [h].

  Definition is_synced (ℓtoHead : loc) : dProp Σ :=
    ∃ h, persist_lb ℓtoHead (toHead_prots ℓtoHead) h.
  
  Definition booked_int (ℓtoHead: loc) v (h__push h__pop: history): dProp Σ :=
    "%Hpush" ∷ ⌜ last h__push = Some (inl v) ⌝ ∗
    "%Hpaired" ∷ ⌜ paired h__push h__pop ⌝ ∗
    "#seen_push" ∷ seen_state ℓtoHead h__push ∗
    "token_pop" ∷ ⎡ list_elem γ h__pop ⎤.

  (* we need to attach a few more ingredients once we are out of [CAS] proof *)
  Definition booked (ℓtoHead: loc) v: dProp Σ :=
    ∃ h__push h__pop,
      "%Hpush" ∷ ⌜ last h__push = Some (inl v) ⌝ ∗
      "%Hpaired" ∷ ⌜ paired h__push h__pop ⌝ ∗
      "#seen_push" ∷ <fence> seen_state ℓtoHead h__push ∗
      "#store_lb" ∷ store_lb ℓtoHead (toHead_prots ℓtoHead) h__pop ∗
      "token_pop" ∷ ⎡ list_elem γ h__pop ⎤.
End definitions.

Section proof.
  Implicit Types (ℓ : loc).
  Context `{!excl_listG (leibnizO (val + unit)) Σ Ω, !nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.

  Context (ϕ : val → dProp Σ).
  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a, IntoNGFlush (ϕ a) (ϕ a),
            ∀ a, BufferFree (ϕ a)}.
  
  Lemma wp_mk_stack :
    {{{ True }}}
      mk_stack #()
    {{{ ℓ γ, RET #ℓ; is_stack ϕ γ ℓ }}} .
  Proof.
    iIntros (Φ) "_ ϕpost".
    rewrite /mk_stack.
    wp_pures.
    wp_apply (wp_alloc_na _ nil_node node_prot with "[//]").
    iIntros (ℓnil) "nilPts".
    iDestruct (mapsto_na_store_lb with "nilPts") as "#storeLb".
    wp_pures.
    wp_apply (wp_flush_lb with "[$]").
    iIntros "[#flushLb _]".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.
    (* TODO: make this separate lemma/instance *)
    (* allocate ghost resource *)
    rewrite wp_wpc. iApply fupd_wpc.
    iMod (excl_list_alloc) as (γ) "[list_auth list_token]". iModIntro.
    rewrite -wp_wpc.
    iApply (wp_alloc_at_strong (toHead_prots ϕ γ) _ [] with "[flushLb nilPts $list_auth $list_token]").
    { iIntros (ℓ).
      rewrite /= /duplicable_inv /=.
      iFrame.
      iSplit.
      { iExists ℓnil, [].
        repeat (iSplit; first done).
        rewrite /is_node /=.
        iExists _. iFrame.
        done. }
      rewrite /ownϕ /= left_id.
      iIntros (h' ? [? ?]).
      destruct h'; done. }
    iNext. iIntros (?) "?".
    iApply "ϕpost".
    iExists _. iFrame.
  Qed.

  Context (γ: gname).

  (* The stack is crash safe. *)
  Lemma is_stack_post_crash ℓ :
    is_stack ϕ γ ℓ -∗ <NG> if_rec ℓ (is_stack ϕ γ ℓ).
  Proof.
    iIntros "[% pts]".
    rewrite /is_stack.
    iModIntro.
    iModIntro.
    iDestruct "pts" as (h') "[c pts]".
    iExists h'.
    iFrame.
  Qed.

  Lemma is_stack_synced_post_crash ℓ :
    is_stack ϕ γ ℓ -∗ is_synced ϕ γ ℓ -∗ <NG> (is_stack ϕ γ ℓ).
  Proof.
    iIntros "[% pts] [% S]".
    iModIntro.
    iDestruct "S" as "[per (% & % & crashed)]".
    iDestruct (crashed_in_if_rec with "crashed pts") as (h') "[crashed pts]".
    iExists h'. iFrame "pts".
  Qed.

  Lemma wp_push stack x s E :
    {{{ is_stack ϕ γ stack ∗ ϕ x }}}
      push #stack x @ s ; E
    {{{ RET #(); True }}}.
  Proof.
    rewrite /is_stack.
    iIntros (Φ) "[[% #stackPts] ϕ] ϕpost".
    rewrite /push.
    wp_pures.
    wp_apply (wp_alloc_na _ (mk_numbered 0 _) toNext_prot with "[]").
    { simpl. done. }
    iIntros (ℓtoNext) "toNextPts".
    wp_pures.
    wp_apply (wp_alloc_na _ (cons_node x ℓtoNext) node_prot).
    { done. } (* rewrite /cons_node_prot. iFrame. done. } *)
    iIntros (ℓnode) "nodePts".
    wp_pures.
    wp_apply (wp_flush_na with "nodePts").
    iIntros "(nodePts & #nodeFlushLb & _)".
    wp_pure1. wp_pure1. wp_pure1.
    iAssert (∃ xs x', ⌜ last xs = Some x' ⌝ ∗ ℓtoNext ↦_{_} xs)%I with "[toNextPts]" as "toNextPts".
    { iExists _, _. iFrame. done. }
    iLöb as "IH".
    iDestruct "toNextPts" as (xs' [n' x'] lastEq) "toNextPts".
    wp_pures.

    (* The load of the pointer to the head. *)
    wp_apply (wp_load_at_simple _ _ (λ _ v, (∃ (ℓhead : loc), ⌜v = #ℓhead⌝)%I)
      with "[$stackPts]").
    { iModIntro.
      iIntros (? v le) "[inv $]".
      iNamed "inv".
      iSplit; first by iExists _.
      repeat iExists _. iFrame "#". iFrame. done. }
    iIntros (hL v) "[storeLb fence]".

    wp_pures.
    wp_apply (wp_store_na _ _ _ _ _ (mk_numbered (S n') v) with "[$toNextPts]").
    { done. } { apply numbered_le. lia. }
    { simpl. done. }
    simpl.
    iIntros "toNextPts".
    wp_pures.
    wp_apply (wp_flush_na with "toNextPts").
    iIntros "(toNextPts & #toNextPtsFl & _)".
    wp_pures.
    wp_apply wp_fence. do 2 iModIntro.
    iDestruct "fence" as (ℓhead) "->".
    wp_pures.

    wp_apply (wp_cas_at
                (λ _ _, True)%I (* Q1 - success *)
                (λ _, True)%I   (* Q2 - failure *)
                (ℓnode ↦_{node_prot} [cons_node x ℓtoNext] ∗ ℓtoNext ↦_{toNext_prot} (xs' ++ [mk_numbered (S n') #ℓhead]) ∗ ϕ x)%I          (* Q3 - failure no flush *)
                (λ _, True%I)   (* P *)
                (λ h, ⎡ list_auth γ h ⎤ ∗ ∃ xs, ⌜ eval h [] = Some xs ⌝ ∗ is_node ℓhead xs ∗ seen_states stack h)%I (* R *)
                [] h _ (toHead_prots ϕ γ stack)
               with "[$stackPts nodePts toNextPts ϕ]").
    { iIntros.
      iSplitR. { iIntros "_". iPureIntro. left. done. }
      iSplit.
      - iIntros.
        iExists (σ_l ++ [inl x]).
        iSplitR.
        { iIntros "!> _".
          iPureIntro.
          by apply prefix_app_r. }
        iSplitR.
        { iIntros (???) "[[list_auth1 _] _] [[[list_auth2 _] _] | [ _ (% & % & % & [[list_auth2 _] _ ]) ] ]";
            iDestruct (gen_own_valid_2 with "list_auth1 list_auth2") as %[]%gmap_view_auth_op_valid. }
        iSplitR.
        { iIntros "!> predP".
          iSplitR; first by iModIntro.
          naive_solver. }
        iSplitR.
        { iModIntro.
          iIntros "[($ & inv & $ & $) _]".
          iNamed "inv".
          simplify_eq.
          iDestruct (is_node_split with "isNode") as "[node1 node2]".
          iSplitR "node2"; last (by (iExists _; iSplit)).
          iExists _, _. iSplitPure; first done. iSplitPure; first done. iFrame. }
        iIntros "seen [list_auth (%xs & %Heval & isNode & seens)]".
        iMod (list_auth_grow with "list_auth") as "[list_auth _]".
        iModIntro.
        iSplitL; last (iSplit; [by iModIntro | done]).
        rewrite /toHead_prots /duplicable_inv /=.
        iFrame.
        iSplitR "ϕ seen seens".
        { iExists ℓnode, (x :: xs).
          iSplit; first done.
          erewrite eval_snoc_push; last eassumption.
          iSplitPure; first done.
          iExists _, _ , _, _, _.
          iFrame "isNode".
          iFrame "nodePts".
          iFrame "nodeFlushLb".
          iExists _. iFrame "toNextPts toNextPtsFl".
          iPureIntro. rewrite last_app. done. }
        rewrite /ownϕ last_snoc.
        iSplitL "ϕ"; first by iLeft.
        iIntros (h' ? Hprefix).
        destruct (decide (σ_l = h')); simplify_list_eq; first done.
        iApply "seens"; first done.
        iPureIntro.
        destruct Hprefix as [h'' ?].
        destruct (last h'') eqn:Heqn.
        + apply last_Some in Heqn as [h''' ->].
          simplify_list_eq.
          by eexists.
        + apply last_None in Heqn as ->.
          simplify_list_eq.
      - iSplitL ""; last iFrame.
        iModIntro.
        naive_solver. }
    iIntros (b ? ?) "[[-> _] | (-> & _ & _ & _ & nodePts & toNextPts & ϕ)]".
    (* The CAS succeeded. *)
    - wp_pures. iModIntro. iApply "ϕpost". done.
    (* The CAS failed. *)
    - wp_pure _.
      iApply ("IH" with "ϕ ϕpost nodePts [toNextPts]").
      { iExists _, _. iFrame "toNextPts". iPureIntro. rewrite last_app. done. }
  Qed.

  Lemma wp_pop stack s E :
    {{{ is_stack ϕ γ stack }}}
      pop #stack @ s ; E
    {{{ v, RET v;
        (⌜ v = NONEV ⌝) ∨ (∃ x, ⌜ v = InjRV x ⌝ ∗ booked ϕ γ stack x) }}}.
  Proof.
    iIntros (Φ) "[% #stackPts] ϕpost".
    rewrite /pop.
    wp_pure1.
    iLöb as "IH".
    wp_pures.
    wp_apply (wp_load_at_simple _ _
      (λ _ v, (∃ (ℓhead : loc) xs, ⌜v = #ℓhead⌝ ∗ is_node ℓhead xs)%I) with "[$stackPts]").
    {
      simpl.
      iModIntro.
      iIntros (? v le) "[inv $]".
      iNamed "inv".
      iDestruct (is_node_split with "isNode") as "[node1 node2]".
      iSplitL "node1".
      { iExists _, _. iSplitPure; first done. iFrame "node1". }
      repeat iExists _. iFrame "#". iFrame. done. }
    iIntros (? v) "[storeLb fence]".
    wp_pures.
    wp_apply wp_fence. do 2 iModIntro.
    iDestruct "fence" as (ℓhead xs ->) "node".
    wp_pures.
    iDestruct (is_node_split with "node") as "[node node']".
    destruct xs as [ | x xs ]; iEval (simpl) in "node".
    - (* The queue is empty. *)
      iDestruct "node" as (?) "(headPts & #headLb)".
      iDestruct (mapsto_na_last with "headPts") as %[? eq].
      simpl in eq. simplify_eq.
      wp_apply (wp_load_na with "[$headPts]").
      { done. }
      { iModIntro. iIntros (?). rewrite /constant_prot. iIntros "#eq".
        iFrame "eq". iDestruct "eq" as "-#eq". rewrite right_id. iAccu. }
      simpl.
      iIntros (v) "(headPts & ->)".
      wp_pures.
      iModIntro.
      iApply "ϕpost". iLeft. done.
    - (* The queue is non-empty. *)
      iDestruct "node" as (?????) "(headPts & #headFlushLb & toNextPts & node)".
      (* iDestruct (mapsto_na_last with "headPts") as %[[]?]. *)
      wp_apply (wp_load_na with "[$headPts]").
      { done. }
      { iModIntro. iIntros (?) "#eq". iFrame "eq". iDestruct "eq" as "-#eq".
        rewrite right_id. iAccu. }
      iSimpl.
      iIntros (v) "[headPts ->]".
      wp_pures.
      rewrite /mapsto_na_flushed. iNamed "toNextPts".
      wp_apply (wp_load_na with "[$pts]").
      { done. }
      { iModIntro. iIntros (?). rewrite /toNext_prot. iIntros "#eq".
        iFrame "eq". iDestruct "eq" as "-#eq". rewrite right_id. iAccu. }
      iSimpl.
      iIntros (?) "(toNextPts & <-)".
      wp_pures.
      wp_apply (wp_cas_at
                  (λ _ (h__pop: history), ∃ h__push, booked_int γ stack x h__push h__pop)%I (* Q1 - success *)
                  (λ _, True)%I                 (* Q2 - failure *)
                  (True)%I                      (* Q3 - failure no flush *)
                  (λ _, True%I)                 (* P *)
                  (λ h, ⎡ list_auth γ h ⎤ ∗ ∃ xs, ⌜ eval h [] = Some xs ⌝ ∗ is_node ℓhead xs ∗ seen_states stack h)%I (* R *)
                  [] _ _ (toHead_prots ϕ γ stack)
                 with "[$stackPts headPts toNextPts node node']").
    { iIntros.
      iSplitR. { iIntros "_". iPureIntro. left. done. }
      iSplit.
      - iIntros.
        iExists (σ_l ++ [inr ()]).
        iSplitR.
        { iIntros "!> _".
          iPureIntro.
          by apply prefix_app_r. }
        iSplitR.
        { iIntros (???) "[[list_auth1 _] _] [[[list_auth2 _] _] | [ _ (% & % & % & [[list_auth2 _] _ ]) ] ]";
            iDestruct (gen_own_valid_2 with "list_auth1 list_auth2") as %[]%gmap_view_auth_op_valid. }
        iSplitR.
        { iIntros "!> predP".
          iSplitR; first by iModIntro.
          naive_solver. }
        iSplitR.
        { iModIntro.
          iIntros "[($ & inv & $ & $) _]".
          iNamed "inv".
          simplify_eq.
          iDestruct (is_node_split with "isNode") as "[node1 node2]".
          iSplitR "node2"; last (by (iExists _; iSplit)).
          iExists _, _. iSplitPure; first done. iSplitPure; first done. iFrame. }
        iIntros "#seen [list_auth (%xs' & %Heval & isNode & #seens)]".
        iMod (list_auth_grow with "list_auth") as "[$ list_elem]".
        iModIntro.
        (* make sure two knowledge of linked list agree with each other. *)
        iDestruct (is_node_agree with "node' isNode") as "<-".
        iDestruct "node'" as (?????) "(headPts' & _ & toNextPts' & node')".
        fold is_node.
        iDestruct (mapsto_na_agree with "headPts headPts'") as %eq1.
        inversion eq1.
        subst ℓtoNext0.
        clear eq1.
        iAssert ⌜ ℓnext = ℓnext0 ⌝%I with "[toNextPts toNextPts']" as "<-".
        { iDestruct "toNextPts'" as (?) "(% & toNextPts' & _)".
          iDestruct (mapsto_na_agree with "toNextPts toNextPts'") as %eq.
          by simplify_map_eq. }
        iClear "node' isNode headPts headPts' toNextPts toNextPts'".
        assert (eval (σ_l ++ [inr ()]) [] = Some xs) as Heval'.
        { by eapply eval_snoc_pop. }
        (* [booked] *)
        iSplitR "list_elem".
        2: {
          iSplit; first by iModIntro.
          rewrite /booked.
          destruct (paired_exists _ _ _ Heval) as (h__push & Hlast & Hpair).
          iExists h__push.
          iSplitPure; first done.
          iSplitPure; first done.
          (* [view_incl] *)
          iSplitR; last done.
          destruct (decide (σ_l = h__push)); simplify_list_eq; first done.
          iApply "seens"; first done.
          iPureIntro.
          destruct Hpair as (? & ? & ?).
          simplify_list_eq.
          by eexists. }
        iSplitL.
        2: {
          rewrite /ownϕ last_snoc left_id.
          iIntros (h' ? Hprefix).
          destruct (decide (σ_l = h')); simplify_list_eq; first done.
          iApply "seens"; first done.
          iPureIntro.
          destruct Hprefix as [h'' ?].
          destruct (last h'') eqn:Heqn.
          + apply last_Some in Heqn as [h''' ->].
            simplify_list_eq.
            by eexists.
          + apply last_None in Heqn as ->.
            simplify_list_eq. }
        iExists ℓnext, xs.
        iSplit; first done.
        erewrite eval_snoc_pop; last eassumption.
        iSplitPure; done.
      - iSplitL ""; last done.
        iModIntro.
        naive_solver. }
      iIntros (b ? h__pop) "[ (-> & fence & #stackPts') | [-> _] ]".
      * (* The CAS succeeded. *)
        wp_pures.
        (* Now we just need to load the value. *)
        iModIntro. iApply "ϕpost". iRight. iExists _.
        iSplit; first done.
        iDestruct "fence" as (???) "[#seen >tok]".
        iExists h__push, h__pop.
        iFrame "∗#".
        iSplit; first done.
        iSplit; first done.
        iApply mapsto_at_store_lb.
        done.
      * (* The CAS failed. *)
        wp_pure _.
        iApply ("IH" with "ϕpost").
  Qed.

    Lemma wp_flush stack v s E:
    {{{ is_stack ϕ γ stack ∗ booked ϕ γ stack v }}}
      sync #stack @ s; E
    {{{ RET #(); ϕ v }}}.
  Proof.
    iIntros (Φ) "[[% #toHeadPts] booked] ϕpost".
    rewrite /sync.
    wp_pures.
    iNamed "booked".
    wp_apply (wp_flush_xchg stack (toHead_prots ϕ γ stack) h__push h__pop _ _ (ϕ v) with "[token_pop]").
    - iSplit.
      { by iNamed "toHeadPts". }
      iSplit; first done.
      iSplit; first done.
      iIntros (?) "!> $".
      iIntros (h__old ?) "!>".
      rewrite /=.
      iSplit.
      + iIntros (?) "token".
        iDestruct (list_token_strengthen (length h__pop) with "token") as ">[$ rely]".
        { by apply prefix_length. }
        iModIntro.
        rewrite /exchange_3 /=.
        iIntros (?) "!> [$ ownϕ]".
        rewrite /ownϕ Hpush.
        iDestruct ("ownϕ") as "[ϕ | (%h__pop' & %paired' & [list_elem _])]".
        2:{
          iDestruct (list_elem_prefix with "[$] [$]") as %Hprefix.
          eapply paired_unique in Hprefix as <-; try done.
          iDestruct (list_elem_excl with "[$] [$]") as %[]. }
        iAssert ⎡ list_elem_with_rely γ h__pop ⎤%I with "[token_pop rely]" as "list_elem".
        { iDestruct "token_pop" as "[$ $]".
          iExists (length h__pop).
          iSplitPure; first lia.
          done. }
        iModIntro.
        iFrame.
        iRight.
        iExists h__pop.
        by iFrame.
      + iIntros (?) "token".
        iDestruct (token_to_rely with "token") as "#rely".
        iModIntro.
        iFrame.
        rewrite /exchange_3 /=.
        iIntros (?) "!> [$ ownϕ]".
        rewrite /ownϕ Hpush.
        iDestruct ("ownϕ") as "[ϕ | (%h__pop' & %paired' & [list_elem _])]".
        2:{
          iDestruct (list_elem_prefix with "[$] [$]") as %Hprefix.
          eapply paired_unique in Hprefix as <-; try done.
          iDestruct (list_elem_excl with "[$] [$]") as %[]. }
        iAssert ⎡ list_elem_with_rely γ h__pop ⎤%I with "[token_pop rely]" as "list_elem".
        { iDestruct "token_pop" as "[$ $]".
          iExists (length h__old).
          iDestruct (rely_to_rely_self with "rely") as "$".
          iPureIntro.
          by apply prefix_length. }
        iModIntro.
        iFrame.
        iRight.
        iExists h__pop.
        by iFrame.
    - iIntros "R".
      wp_pures.
      wp_bind FenceSync.
      iApply (wp_fence_sync' with "R").
      iIntros "!> [_ R]".
      wp_pures.
      iApply "ϕpost".
      done.
  Qed.
  
  Lemma wpc_sync (stack : loc) s E :
    {{{ is_stack ϕ γ stack }}}
      sync #stack @ s ; E
    {{{ RET #(); is_synced ϕ γ stack }}}.
  Proof.
    iIntros (Φ) "[% #stackPts] ϕpost".
    rewrite /sync.
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "stackPts").
    iIntros "(_ & PF & PFS)".
    wp_pures.
    iApply (wp_fence_sync s E Φ).
    iNext. iModIntro.
    iApply "ϕpost".
    rewrite /is_synced.
    iExists _.
    iFrame "PFS".
  Qed.
End proof.
