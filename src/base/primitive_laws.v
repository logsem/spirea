From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map. (* gen_inv_heap. *)

From Perennial.program_logic Require Import ectx_lifting.
From Perennial.program_logic Require Export ectx_language weakestpre lifting.

From iris.algebra Require Import auth gmap numbers.
From iris.prelude Require Import options.

From self Require Import extra.
From self.algebra Require Import view.
From self.lang Require Import notation.
From self.base Require Import tactics.

Class nvmG Σ := NvmG {
  nvmG_invG : invG Σ;                        (* For invariants. *)
  nvmG_crashG : crashG Σ;                    (* Stuff for Perennial. *)
  nvmG_gen_heapG :> gen_heapG loc history Σ; (* For the heap. *)
  view_inG :> inG Σ (authR viewUR);          (* For views. *)
  recovered_inG :> inG Σ (agreeR viewO);      (* For recovered knowledge. *)
  store_view_name : gname;                   (* For validity of store views. *)
  persist_view_name : gname;                 (* For knowledge about the persisted view. *)
  recovered_view_name : gname;               (* For knowledge about the view recovered after the last crash. *)
}.

(** Get the largest time of any message in a given history. *)
Definition max_msg (h : history) : time :=
  max_list (elements (dom (gset time) h)).

(**** Lemmas about [max_msg]. *)

Lemma lookup_max_msg (hist : history) :
  is_Some (hist !! 0) → is_Some (hist !! max_msg hist).
Proof.
  intros H.
  apply elem_of_dom.
  rewrite /max_msg.
  apply elem_of_elements.
  apply max_list_elem_of.
  apply elem_of_dom in H.
  apply elem_of_elements in H.
  eapply elem_of_not_nil.
  done.
Qed.

Lemma max_msg_insert t msg hist : max_msg (<[t:=msg]> hist) = t `max` max_msg hist.
Proof.
  rewrite /max_msg. rewrite dom_insert.
  destruct (decide (t ∈ (dom (gset time) hist))) as [Hin|Hin].
  - replace ({[t]} ∪ dom (gset time) hist) with (dom (gset time) hist) by set_solver.
    symmetry. apply max_r.
    apply max_list_elem_of_le.
    apply elem_of_elements.
    done.
  - rewrite elements_union_singleton; last done.
    simpl. done.
Qed.

(* Lemma max_msg_lookup_included. *)
Lemma max_msg_le_insert hist t msg :
  max_msg hist ≤ max_msg (<[t:=msg]> hist).
Proof. rewrite max_msg_insert. lia. Qed.

Lemma lookup_max_msg_succ (hist : history) :
  hist !! (max_msg hist + 1) = None.
Proof.
  rewrite /max_msg.
  apply not_elem_of_dom.
  rewrite -elem_of_elements.
  apply max_list_not_elem_of_gt.
  lia.
Qed.

(** Convert a [store] to a [view] by taking the largest time for of any message
for each location. We call this the "lub view" b.c., in an actual execution this
view will be the l.u.b. of all the threads views. *)
Definition lub_view (heap : store) : view := MaxNat <$> (max_msg <$> heap).

Definition hist_inv lub hist `{!nvmG Σ} : iProp Σ :=
  ( (* Every history has an initial message. *)
    ⌜is_Some (hist !! 0)⌝ ∗ (* FIXME: Move this into the points-to predicate. *)
    (* Every view in every message is included in the lub view. *)
    ([∗ map] t ↦ msg ∈ hist, ⌜msg.(msg_store_view) ⊑ lub⌝))%I.

Definition store_inv `{hG : !nvmG Σ} store : iProp Σ :=
  ([∗ map] ℓ ↦ hist ∈ store, hist_inv (lub_view store) hist).

Definition nvm_heap_ctx `{hG : !nvmG Σ} σ : iProp Σ :=
  gen_heap_interp σ.1 ∗ (* The interpretation of the heap. This is standard, except the heap store historie and not plain values. *)
  own store_view_name (● (lub_view σ.1)) ∗
  store_inv σ.1 ∗
  own persist_view_name (● σ.2) ∗
  (∃ (rv : view), own recovered_view_name (to_agree rv : agreeR viewO)).

Global Program Instance nvmG_irisG `{!nvmG Σ} : irisG nvm_lang Σ := {
  iris_invG := nvmG_invG;
  iris_crashG := nvmG_crashG;
  num_laters_per_step := λ n, n; (* This is they choice GooseLang takes. *)
  state_interp σ _nt := nvm_heap_ctx σ;
  global_state_interp _g _ns _κs := True%I;
  fork_post _ := True%I;
}.
Next Obligation. intros. eauto. Qed.

(* NOTE: Uncomment as needed. *)
(* Notation "l ↦h{ dq } v" := (mapsto (L:=loc) (V:=val) l dq (Some v%V))
  (at level 20, format "l  ↦h{ dq }  v") : bi_scope.
Notation "l ↦h□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded (Some v%V))
  (at level 20, format "l  ↦h□  v") : bi_scope.
Notation "l ↦h{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) (Some v%V))
  (at level 20, format "l  ↦h{# q }  v") : bi_scope. *)
Notation "l ↦h v" := (mapsto (L:=loc) (V:=history) l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦h  v") : bi_scope.

Section view_ra_rules.
  (** Rules for view RA. ***)
  Context `{inG Σ (authR viewUR)}.

  Lemma view_valid (V : view) : ✓ V.
  Proof. intros ?. case (_ !! _); done. Qed.

  Lemma auth_auth_view_grow_op γ V V' : ⊢ own γ (● V) ==∗ own γ (● (V ⋅ V')) ∗ own γ (◯ V').
  Proof.
    iIntros "H".
    iMod (own_update with "H") as "[Ho Hf]".
    { apply auth_update_alloc.
      apply (op_local_update_discrete _ _ V').
      intros. apply view_valid. }
    rewrite comm.
    rewrite right_id.
    by iFrame.
  Qed.

  Lemma auth_auth_view_grow_incl γ V V' : V ⊑ V' → own γ (● V) ==∗ own γ (● V').
  Proof.
    iIntros ([x ->]) "H".
    by iMod (auth_auth_view_grow_op with "H") as "[$ _]".
  Qed.
End view_ra_rules.

(* Expresses that the view [V] is valid. This means that it is included in the
lub view. *)
Definition valid {Σ} `{hG : nvmG Σ} (V : view) : iProp Σ := own store_view_name (◯ V).

(* Expresses that the view [P] is persisted. This means that it is included in
the global persisted view. *)
Definition persisted {Σ} `{hG : nvmG Σ} (V : view) : iProp Σ := own persist_view_name (◯ V).

(* Expresses that the view [rv] was recovered after the last crash. *)
Definition recovered {Σ} `{hG : nvmG Σ} (rv : view) : iProp Σ :=
  ∃ fullRv, ⌜map_Forall (λ ℓ t, fullRv !! ℓ = Some t) rv⌝ ∗ own recovered_view_name (to_agree fullRv).

Section lifting.

  Context `{!nvmG Σ}.

  Implicit Types Q : iProp Σ.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types efs : list expr.
  (* Implicit Types σ : state. *)
  Implicit Types v : val.
  Implicit Types ℓ : loc.
  Implicit Types V W : view.
  Implicit Types hist : history.


  Global Instance valid_persistent V : Persistent (valid V).
  Proof. apply _. Qed.

  Global Instance recovered_persistent rv : Persistent (valid rv).
  Proof. apply _. Qed.

  Global Instance persisted_persistent V : Persistent (persisted V).
  Proof. apply _. Qed.

  Lemma auth_frag_leq V W γ : ⊢ own γ (◯ V) -∗ own γ (● W) -∗ ⌜V ⊑ W⌝.
  Proof.
    iIntros "H1 H2".
    rewrite /valid.
    iDestruct (own_valid_2 with "H2 H1") as %[Hincl _]%auth_both_valid_discrete.
    done.
  Qed.

  (**** Lemmas about [lub_view] *)

  (* If a location has history [hist] then looking up a message from the
  lub_view will result in some message. *)
  Lemma history_lookup_lub heap ℓ hist :
    heap !! ℓ = Some hist → is_Some (hist !! 0) → is_Some (hist !! ((lub_view heap) !!0 ℓ)).
  Proof.
    intros Ha Hb.
    rewrite /lub_view. rewrite !lookup_fmap. rewrite Ha.
    simpl. apply lookup_max_msg. done.
  Qed.

  Lemma history_lookup_lub_succ heap ℓ hist :
    heap !! ℓ = Some hist →
    hist !! ((lub_view heap !!0 ℓ) + 1) = None.
  Proof.
    intros look.
    rewrite /lub_view. rewrite !lookup_fmap. rewrite look.
    simpl. apply lookup_max_msg_succ.
  Qed.

  Lemma lub_view_incl_insert V heap ℓ t msg hist :
    heap !! ℓ = Some hist →
    V ≼ lub_view heap →
    <[ℓ := MaxNat t]>V ≼ lub_view (<[ℓ := (<[t := msg]> hist)]> heap).
  Proof.
    intros look incl.
    rewrite lookup_included. intros ℓ'.
    rewrite !lookup_fmap.
    destruct (decide (ℓ = ℓ')).
    * subst. rewrite !lookup_insert. simpl.
      apply Some_included_2.
      apply max_nat_included. simpl.
      rewrite max_msg_insert.
      lia.
    * rewrite !lookup_insert_ne; [|done|done].
      move: incl. rewrite lookup_included.
      intros H. pose proof (H ℓ') as H.
      etrans; first apply H.
      rewrite !lookup_fmap. done.
  Qed.

  Lemma lub_view_insert V (ℓ : loc) (t : time) (msg : message) (hist : history) (heap : store) :
    (V !!0 ℓ) < t →
    heap !! ℓ = Some hist →
    lub_view (<[ℓ := (<[t := msg]> hist)]> heap) = <[ℓ := MaxNat t]>(lub_view heap).
  Proof. Admitted.

  (* If a new message is inserted into the heap the lub_view can only grow. *)
  Lemma lub_view_insert_incl (ℓ : loc) (t : time) (msg : message) hist (heap : store) :
    heap !! ℓ = Some hist →
    lub_view heap ⊑ lub_view (<[ℓ := (<[t := msg]> hist)]> heap).
  Proof.
    rewrite subseteq_view_incl.
    rewrite lookup_included.
    intros look ℓ'.
    rewrite !lookup_fmap.
    destruct (decide (ℓ = ℓ')).
    * subst. rewrite lookup_insert. rewrite look. simpl.
      apply Some_included_2.
      apply max_nat_included. simpl.
      apply max_msg_le_insert.
    * rewrite lookup_insert_ne; done.
  Qed.

  (***** Lemmas about ownership over [lub_view]. *)

  Lemma auth_lub_view_insert V ℓ t (heap : store) (hist : history) msg :
    heap !! ℓ = Some hist →
    (V !!0 ℓ) < t →
    own store_view_name (● lub_view heap) ==∗
    own store_view_name (● lub_view (<[ℓ := <[t := msg]> hist]> heap)) ∗
    own store_view_name (◯ {[ ℓ := MaxNat t ]}).
  Proof.
    iIntros (look lt) "Olub".
    pose proof (lub_view_insert_incl ℓ t msg hist heap look) as incl.
    iMod (auth_auth_view_grow_incl _ _ _ incl with "Olub") as "Olub".
    iMod (own_update with "Olub") as "[$ $]".
    { apply: auth_update_dfrac_alloc.
      erewrite lub_view_insert; [|apply lt|done].
      apply singleton_included_insert.
      reflexivity. }
    done.
  Qed.

  Lemma hist_inv_grow (heap : store) (W W' : view) :
    W ⊑ W' →
    ([∗ map] h ∈ heap, hist_inv W h) -∗
    ([∗ map] h ∈ heap, hist_inv W' h).
  Proof.
    iIntros (incl) "#M".
    iApply big_sepM_intuitionistically_forall.
    iModIntro.
    iIntros (ℓ h look).
    iDestruct (big_sepM_lookup with "M") as "[% #M']"; first done.
    iSplitL; first done.
    iApply big_sepM_intuitionistically_forall. iModIntro.
    iIntros (t msg look').
    iDestruct (big_sepM_lookup with "M'") as %incl'; first done.
    iPureIntro. by trans W.
  Qed.

  Lemma hist_inv_insert_msg (heap : store) v p ℓ t hist :
    heap !! ℓ = Some hist →
    hist !! t = None →
    ([∗ map] h ∈ heap, hist_inv (lub_view heap) h) -∗
    ([∗ map] h ∈ <[ℓ:=<[t:={| msg_val := v;
                              msg_store_view := ∅;
                              msg_persist_view := p |}]> hist]> heap,
         hist_inv
           (lub_view
              (<[ℓ:=<[t:={| msg_val := v;
                            msg_store_view := ∅;
                            msg_persist_view := p |}]> hist]> heap)) h).
  Proof.
    iIntros (look histLook) "#M".
    iApply big_sepM_insert_override_2; simpl; first done.
    - iApply (hist_inv_grow with "M").
      by apply lub_view_insert_incl.
    - iIntros "[% map]". iSplit.
      * iPureIntro. apply lookup_insert_is_Some'. by right.
      * iApply big_sepM_insert; first apply histLook.
        iSplit.
        + simpl. iPureIntro. rewrite subseteq_view_incl.
          apply (ucmra_unit_least (lub_view _)).
        + done.
  Qed.

  Lemma hist_inv_insert_msg' (heap : store) v p ℓ t hist V :
    heap !! ℓ = Some hist →
    hist !! t = None →
    V ≼ (lub_view
              (<[ℓ:=<[t:= Msg v V p]> hist]> heap)) →
    ([∗ map] h ∈ heap, hist_inv (lub_view heap) h) -∗
    ([∗ map] h ∈ <[ℓ:=<[t := Msg v V p]> hist]> heap,
         hist_inv (lub_view (<[ℓ:=<[t:=Msg v V p]> hist]> heap)) h).
  Proof.
    iIntros (look histLook Vincl) "#M".
    iApply big_sepM_insert_override_2; simpl; first done.
    - iApply (hist_inv_grow with "M").
      by apply lub_view_insert_incl.
    - iIntros "[% map]". iSplit.
      * iPureIntro. apply lookup_insert_is_Some'. by right.
      * iApply big_sepM_insert; first apply histLook.
        iSplit.
        + simpl. iPureIntro. rewrite subseteq_view_incl. done.
          (* apply (ucmra_unit_least (lub_view _)). *)
        + done.
  Qed.

  Lemma store_view_alloc_big (σ σ' : (gmap loc history)) :
    σ' ##ₘ σ →
    own store_view_name (● (lub_view (σ))) ==∗
    own store_view_name (● (lub_view (σ' ∪ σ))).
  Proof.
  Admitted.

  Lemma message_included_in_lub_view ℓ (hist : history) heap t v MV MP :
    heap !! ℓ = Some hist →
    hist !! t = Some {| msg_val := v; msg_store_view := MV; msg_persist_view := MP |} →
    ([∗ map] h ∈ heap, hist_inv (lub_view heap) h) -∗
    ⌜MV ⊑ lub_view heap⌝.
  Proof.
    iIntros (heapLook histLook) "M".
    iDestruct (big_sepM_lookup with "M") as "[_ M]"; first done.
    iDestruct (big_sepM_lookup with "M") as "%"; first done.
    done.
  Qed.

  Lemma hist_inv_alloc ℓ P v0 n heap :
    heap_array ℓ P (replicate (Z.to_nat n) v0) ##ₘ heap →
    ([∗ map] hist ∈ heap, hist_inv (lub_view heap) hist) -∗
    ([∗ map] hist ∈ (heap_array ℓ P (replicate (Z.to_nat n) v0) ∪ heap),
      hist_inv (lub_view (heap_array ℓ P (replicate (Z.to_nat n) v0) ∪ heap)) hist).
  Proof.
    iIntros (disj) "H".
    rewrite big_sepM_union; last apply disj.
    iSplitR "H".
    - iApply big_sepM_intuitionistically_forall.
      iIntros (ℓ' hist) "!> %".
      admit.
    - iApply (big_sepM_impl with "H").
    (* - iApply (big_sepM_wand with "H"). *)
      (* iApply big_sepM_intuitionistically_forall. *)
      iIntros (ℓ' hist) "!> % [% H]".
      iSplit; first done.
      iApply (big_sepM_impl with "H").
      iIntros (t msg) "!> % %".
  Admitted.

  (* Create a message from a [value] and a [thread_view]. *)
  Definition mk_message (v : val) (T : thread_view) := Msg v (store_view T) (persist_view T).

  (** Rules for memory operations. **)

  Lemma heap_array_to_seq_mapsto l (P : view) (v : val) (n : nat) :
    ([∗ map] l' ↦ ov ∈ heap_array l P (replicate n v), gen_heap.mapsto l' (DfracOwn 1) ov) -∗
    [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦h initial_history P v.
  Proof.
    iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
    { done. }
    rewrite big_opM_union; last first.
    { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
      intros (j&w&?&Hjl&_)%heap_array_lookup.
      rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
    rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite <-loc_add_assoc.
    rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
  Qed.

  Lemma wp_allocN v T (hist : history) n s E :
    (0 < n)%Z →
    {{{ True }}}
      (ThreadState (AllocN #n v) T) @ s; E
    {{{ ℓ, RET (ThreadVal #ℓ T);
          [∗ list] i ∈ seq 0 (Z.to_nat n), (ℓ +ₗ (i : nat)) ↦h initial_history (persist_view T) v }}}.
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns κ κs k) "(Hσ & Hauth & Hop & Hpers) Ht !>". iSplit.
    - (* We must show that [ref v] is can take tome step. *)
       rewrite /head_reducible.
       destruct T as [[sv pv] bv].
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step.
       * constructor. done.
       * apply alloc_fresh. lia.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      simpl in *.
      inv_impure_thread_step.
      iSplitR=>//.
      assert (heap_array ℓ P (replicate (Z.to_nat n) v) ##ₘ g) as Hdisj.
      { apply heap_array_map_disjoint.
        rewrite replicate_length Z2Nat.id; auto with lia. }
      iFrame "Hpers".
      (* We now update the [gen_heap] ghost state to include the allocated location. *)
      iMod (gen_heap_alloc_big with "Hσ") as "(Hσ & Hl & Hm)"; first apply Hdisj.
      iFrame "Hσ".
      rewrite /state_init_heap.
      iMod (store_view_alloc_big with "Hauth") as "$".
      { apply Hdisj. }
      iModIntro.
      iDestruct (hist_inv_alloc with "Hop") as "Hop"; first apply Hdisj.
      iFrame.
      iApply "HΦ". iApply heap_array_to_seq_mapsto. iFrame.
  Qed.

  (* Non-atomic load. *)
  Lemma wp_load (V p B : view) ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (! #ℓ) (V, p, B)) @ s; E
    {{{ t v, RET (ThreadVal v (V, p, B));
        ℓ ↦h hist ∗ ⌜msg_val <$> (hist !! t) = Some v ∧ (V !!0 ℓ) ≤ t⌝ }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([heap ?] [] ns κ κs k) "(Hheap & lubauth & #Hincl & persist) Ht /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      iAssert (⌜is_Some (hist !! 0)⌝%I) as %HisS.
      { iDestruct (big_sepM_lookup with "Hincl") as "[% _]"; first apply Hlook. done. }
      pose proof (history_lookup_lub _ _ _ Hlook HisS) as [msg Hmsgeq].
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 [] efs Hstep) "!>".
      inv_impure_thread_step.
      iSplitR=>//.
      iFrame "Hheap lubauth persist Hincl Ht".
      iApply "HΦ". iFrame. done.
  Qed.

  Lemma wp_load_acquire V p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (!{acq} #ℓ) (V, p, B)) @ s; E
    {{{ t v V' P', RET (ThreadVal v (V ⊔ V', p ⊔ P', B));
        ⌜(hist !! t) = Some (Msg v V' P') ∧ (V !!0 ℓ) ≤ t⌝ ∗
        valid (V ⊔ V') }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([heap ?] [] ns κ κs k) "(Hheap & lubauth & #Hincl & persist) Ht /= !>".
    (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
    iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      iAssert (⌜is_Some (hist !! 0)⌝%I) as %HisS.
      { iDestruct (big_sepM_lookup with "Hincl") as "[% _]"; first apply Hlook. done. }
      pose proof (history_lookup_lub _ _ _ Hlook HisS) as [[msgv msgV msgP] Hmsgeq].
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      iDestruct (message_included_in_lub_view with "Hincl") as "%"; try done.
      iMod (own_update with "lubauth") as "[lubauth valid']".
      { apply (auth_update_dfrac_alloc _ _ (V ⋅ MV)).
        rewrite -subseteq_view_incl.
        apply view_le_lub; done. }
      iFrame "Hheap lubauth persist Hincl Ht". iModIntro.
      iApply ("HΦ" $! t v MV MP). iSplit; first done.
      done.
  Qed.

  Lemma wp_store V v p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (#ℓ <- v) (V, p, B)) @ s; E
    {{{ t, RET ThreadVal #() (<[ℓ := MaxNat t]>V, p, B);
          ⌜msg_val <$> (hist !! t) = None⌝ ∗
          ⌜(V !!0 ℓ) < t⌝ ∗
          valid (<[ℓ := MaxNat t]>V) ∗
          ℓ ↦h (<[t := Msg v ∅ p]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([heap ?] [] ns κ κs k) "(Hheap & lubauth & #Hincl & persist) Ht /= !>".
    (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
    iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the store can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      iAssert (⌜is_Some (hist !! 0)⌝%I) as %HisS.
      { iDestruct (big_sepM_lookup with "Hincl") as "[% _]"; first apply Hlook. done. }
      (* pose proof (history_lookup_lub _ _ _ Hlook HisS) as [[msgv msgV msgP] Hmsgeq]. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ ℓ Vincl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      (* The persist view didn't change. *)
      iFrame "persist".
      (* We update the heap with the new history at ℓ. *)
      iMod (gen_heap_update with "Hheap ℓPts") as "[Hheap ℓPts]".
      iFrame "Hheap".
      (* We must now update the authorative element for the lub_view. *)
      iMod (auth_lub_view_insert with "lubauth") as "[lubauth viewT]"; [done|done|].
      iFrame "lubauth Ht".
      (* We now update the big op. *)
      iSplitR. { iApply hist_inv_insert_msg; done. }
      iApply "HΦ".
      iModIntro.
      iFrame "%∗".
      iSplit. { rewrite H10. done. }
      iCombine "Hval viewT" as "v".
      rewrite -view_insert_op; last lia.
      iFrame "v".
  Qed.

  Lemma wp_store_release V v p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (#ℓ <-{rel} v) (V, p, B)) @ s; E
    {{{ t, RET ThreadVal #() (<[ℓ := MaxNat t]>V, p, B);
          ⌜msg_val <$> (hist !! t) = None⌝ ∗
          ⌜(V !!0 ℓ) < t⌝ ∗
          valid (<[ℓ := MaxNat t]>V) ∗
          ℓ ↦h (<[t := Msg v (<[ℓ := MaxNat t]>V) p]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([heap ?] [] ns κ κs k) "(Hheap & lubauth & #Hincl & persist) Ht /= !>".
    (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
    iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the store can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      iAssert (⌜is_Some (hist !! 0)⌝%I) as %HisS.
      { iDestruct (big_sepM_lookup with "Hincl") as "[% _]"; first apply Hlook. done. }
      (* pose proof (history_lookup_lub _ _ _ Hlook HisS) as [[msgv msgV msgP] Hmsgeq]. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ ℓ Vincl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      (* The persist view didn't change. *)
      iFrame "persist".
      (* We update the heap with the new history at ℓ. *)
      iMod (gen_heap_update with "Hheap ℓPts") as "[Hheap ℓPts]".
      iFrame "Hheap".
      (* We must now update the authorative element for the lub_view. *)
      iMod (auth_lub_view_insert with "lubauth") as "[lubauth viewT]"; [done|done|].
      iFrame "lubauth Ht".
      (* We now update the big op. *)
      iSplitR.
      { iApply hist_inv_insert_msg'; try done. apply lub_view_incl_insert; done. }
      iApply "HΦ".
      iModIntro.
      iFrame "%∗".
      iSplit. { rewrite H10. done. }
      iCombine "Hval viewT" as "v".
      rewrite -view_insert_op; last lia.
      iFrame "v".
  Qed.

  (* Lemma wp_cmpxch  *)

  (* Lemma wp_faa  *)

  Lemma wp_wb V P B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist }}}
      (ThreadState (WB #ℓ) (V, P, B)) @ s; E
    {{{ RET ThreadVal #() (V, P, <[ℓ := MaxNat (V !!0 ℓ)]>B); ℓ ↦h hist }}}.
  Proof.
    iIntros (Φ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] κ κs ? k) "(Hheap & Hauth & Hop & Hpers) Ht /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      inv_impure_thread_step. iSplitR=>//.
      iModIntro. iFrame. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_fence V P B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist }}}
      (ThreadState Fence (V, P, B)) @ s; E
    {{{ RET ThreadVal #() (V, P ⊔ B, ∅); ℓ ↦h hist }}}.
  Proof.
    iIntros (Φ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] κ κs ? k) "(Hheap & Hauth & Hop & Hpers) Ht /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      inv_impure_thread_step. iSplitR=>//.
      iModIntro. iFrame. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_fence_fence V P B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V ∗ persisted P }}}
      (ThreadState FenceSync (V, P, B)) @ s; E
    {{{ RET ThreadVal #() (V, P ⊔ B, ∅);
          persisted (P ⊔ B) }}}.
  Proof.
    iIntros (Φ) "(pts & valV & perP) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] κ κs ? k) "(Hheap & Hauth & Hop & Hpers & recov) Ht /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      inv_impure_thread_step. iSplitR=>//.
      iMod (auth_auth_view_grow_op with "Hpers") as "[$ perB]".
      iCombine "perP perB" as "perPB".
      iModIntro. iFrame.
      iApply "HΦ". iFrame.
  Qed.

End lifting.
