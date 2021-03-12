From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.algebra Require Import auth gmap numbers.
From iris.prelude Require Import options.

From self.algebra Require Import view.
From self.lang Require Import notation.

Class nvmG Σ := NvmG {
  nvmG_invG : invG Σ;
  nvmG_gen_heapG :> gen_heapG loc history Σ;
  view_inG :> inG Σ (authR viewUR);
  (* heapG_inv_heapG :> inv_heapG loc (option val) Σ; *)
  nvmG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
  store_view_name : gname;
  persist_view_name : gname;
}.

Definition max_msg (h : history) : time :=
  max_list (elements (dom (gset time) h)).

Lemma max_list_elem_of ns : ns ≠ [] → max_list ns ∈ ns.
Proof.
  intros H. induction ns; first done.
  simpl.
  edestruct (Nat.max_spec a) as [[Hle ->]|[HO ->]].
  - destruct ns; first simpl in *; first lia.
    apply elem_of_list_further.
    apply IHns.
    done.
  - apply elem_of_list_here.
Qed.

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

Lemma lookup_max_msg_succ (hist : history) :
  hist !! (max_msg hist + 1) = None.
Proof.
Admitted.

Definition lub_view (heap : store) : view := MaxNat <$> (max_msg <$> heap).

Definition hist_inv heap hist `{!nvmG Σ} : iProp Σ :=
  ( (* Every history has an initial message. *)
    ⌜is_Some (hist !! 0)⌝ ∗ (* FIXME: Move this into the points-to predicate. *)
    (* Every view in every message is included in the lub view. *)
    ([∗ map] t ↦ msg ∈ hist, ⌜msg.(msg_store_view) ⊑ lub_view heap⌝))%I.

Global Instance nvmG_irisG `{!nvmG Σ} : irisG nvm_lang Σ := {
  iris_invG := nvmG_invG;
  state_interp σ κs _ := (
    (* The interpetation of the heap. This is standard, except the heap store
    historie and not plain values. *)
    gen_heap_interp (fst σ) ∗
    own store_view_name (● (lub_view (fst σ))) ∗
    ([∗ map] ℓ ↦ hist ∈ (fst σ), hist_inv (fst σ) hist) ∗
    own persist_view_name (● (snd σ))
    (* proph_map_interp κs σ.(used_proph_id) *)
  )%I;
  fork_post _ := True%I;
}.

(* NOTE: Uncomment as needed. *)
(* Notation "l ↦h{ dq } v" := (mapsto (L:=loc) (V:=val) l dq (Some v%V))
  (at level 20, format "l  ↦h{ dq }  v") : bi_scope.
Notation "l ↦h□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded (Some v%V))
  (at level 20, format "l  ↦h□  v") : bi_scope.
Notation "l ↦h{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) (Some v%V))
  (at level 20, format "l  ↦h{# q }  v") : bi_scope. *)
Notation "l ↦h v" := (mapsto (L:=loc) (V:=history) l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦h  v") : bi_scope.

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

  Definition valid (V : view) : iProp Σ := own store_view_name (◯ V).

  Global Instance valid_persistent V : Persistent (valid V).
  Proof. apply _. Qed.

  Definition persisted (V : view) : iProp Σ := own persist_view_name (◯ V).

  Global Instance persisted_persistent V : Persistent (persisted V).
  Proof. apply _. Qed.

  Lemma auth_frag_leq V W γ : ⊢ own γ (◯ V) -∗ own γ (● W) -∗ ⌜V ⊑ W⌝.
  Proof.
    iIntros "H1 H2".
    rewrite /valid.
    iDestruct (own_valid_2 with "H2 H1") as %[Hincl _]%auth_both_valid_discrete.
    done.
  Qed.

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

  Lemma lub_view_insert V (ℓ : loc) (t : time) (msg : message) (hist : history) (heap : store) :
    (V !!0 ℓ) < t →
    lub_view (<[ℓ := (<[t := msg]> hist)]> heap) = <[ℓ := MaxNat t]>(lub_view heap).
  Proof. Admitted.

  Lemma auth_lub_view_insert V ℓ t (heap : store) (hist : history) msg :
    (V !!0 ℓ) < t →
    own store_view_name (● lub_view heap) ==∗
    own store_view_name (● lub_view (<[ℓ := <[t := msg]> hist]> heap)) ∗
    own store_view_name (◯ {[ ℓ := MaxNat t ]}).
  Proof.
  Admitted.

  Lemma store_view_alloc_big (σ σ' : (gmap loc history)) :
    σ' ##ₘ σ →
    own store_view_name (● (lub_view (σ))) ==∗
    own store_view_name (● (lub_view (σ' ∪ σ))).
  Proof.
  Admitted.

  Lemma message_included_in_lub_view ℓ (hist : history) heap t v MV MP :
    heap !! ℓ = Some hist →
    hist !! t = Some {| msg_val := v; msg_store_view := MV; msg_persist_view := MP |} →
    ([∗ map] h ∈ heap, hist_inv heap h) -∗
    ⌜MV ⊑ lub_view heap⌝.
  Proof.
    iIntros (heapLook histLook) "M".
    iDestruct (big_sepM_lookup with "M") as "[_ M]"; first done.
    iDestruct (big_sepM_lookup with "M") as "%"; first done.
    done.
  Qed.

  Lemma hist_inv_alloc ℓ P v0 n heap :
    heap_array ℓ P (replicate (Z.to_nat n) v0) ##ₘ heap →
    ([∗ map] hist ∈ heap, hist_inv heap hist) -∗
    ([∗ map] hist ∈ (heap_array ℓ P (replicate (Z.to_nat n) v0) ∪ heap),
      hist_inv (heap_array ℓ P (replicate (Z.to_nat n) v0) ∪ heap) hist).
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
  Definition mk_message (v : val) (T : thread_view) := Msg v T.(tv_store_view) T.(tv_persist_view).

  (* This tactics performs inversion in [thread_step], and its constituents
  [head_step] and [mem_step]. *)
  Ltac inv_thread_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : mem_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
      and should thus better be avoided. *)
      inversion H; subst; clear H
    | H : nvm_lang.head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
      and should thus better be avoided. *)
      inversion H; subst; clear H
    | H : thread_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
      and should thus better be avoided. *)
      inversion H; subst; clear H
    end.

  (*** Rules for memory operations. ***)

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
          [∗ list] i ∈ seq 0 (Z.to_nat n), (ℓ +ₗ (i : nat)) ↦h initial_history T.(tv_persist_view) v }}}.
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([??] κ κs k) "(Hσ & Hauth & Hop & Hpers) !>"; iSplit.
    - (* We must show that [ref v] is can take tome step. *)
       rewrite /head_reducible.
       destruct T.
       iExists [], _, _, _. simpl. iPureIntro.
       eapply impure_step.
       * constructor. done.
       * apply alloc_fresh. lia.
    - iNext. iIntros (e2 σ2 efs Hstep).
      simpl in *. inv_thread_step. iSplitR=>//.
      assert (heap_array ℓ P (replicate (Z.to_nat n) v0) ##ₘ g) as Hdisj.
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
      iFrame "Hop".
      iApply "HΦ". iApply heap_array_to_seq_mapsto. iFrame.
  Qed.

  (* Non-atomic load. *)
  Lemma wp_load V p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (! #ℓ) (ThreadView V p B)) @ s; E
    {{{ t v, RET (ThreadVal v (ThreadView V p B));
          ⌜msg_val <$> (hist !! t) = Some v ∧ (V !!0 ℓ) ≤ t⌝ }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([heap ?] κ κs k) "(Hheap & lubauth & #Hincl & persist) /= !>".
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
      iExists [], _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 efs Hstep) "!>".
      simpl in *. inv_thread_step. iSplitR=>//.
      (* assert (h = hist) as ->. { rewrite Hlook in H9. congruence. } *)
      iFrame "Hheap lubauth persist Hincl".
      by iApply "HΦ".
  Qed.

  Lemma wp_load_acquire V p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (!{acq} #ℓ) (ThreadView V p B)) @ s; E
    {{{ t v V' P', RET (ThreadVal v (ThreadView (V ⊔ V') (p ⊔ P') B));
        ⌜(hist !! t) = Some (Msg v V' P') ∧ (V !!0 ℓ) ≤ t⌝ ∗
        valid (V ⊔ V') }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([heap ?] κ κs k) "(Hheap & lubauth & #Hincl & persist) /= !>".
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
      iExists [], _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 efs Hstep).
      simpl in *. inv_thread_step. iSplitR=>//.
      iDestruct (message_included_in_lub_view with "Hincl") as "%"; try done.
      iMod (own_update with "lubauth") as "[lubauth valid']".
      { apply (auth_update_dfrac_alloc _ _ (V ⋅ MV)).
        rewrite -subseteq_view_incl.
        apply view_le_lub; done. }
      iFrame "Hheap lubauth persist Hincl". iModIntro.
      iApply ("HΦ" $! t v MV MP). iSplit; first done.
      done.
  Qed.

  Lemma wp_store V v p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (#ℓ <- v) (ThreadView V p B)) @ s; E
    {{{ t, RET ThreadVal #() (ThreadView (<[ℓ := MaxNat t]>V) p B);
          ⌜msg_val <$> (hist !! t) = None⌝ ∗
          ⌜(V !!0 ℓ) ≤ t⌝ ∗
          valid (<[ℓ := MaxNat t]>V) ∗
          ℓ ↦h (<[t := Msg v ∅ p]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([heap ?] κ κs k) "(Hheap & lubauth & #Hincl & persist) /= !>".
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
      iExists [], _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ ℓ Vincl). lia.
        + done.
    - iNext. iIntros (e2 σ2 efs Hstep).
      simpl in *. inv_thread_step. iSplitR=>//.
      (* The persist view didn't change. *)
      iFrame "persist".
      (* We update the heap with the new history at ℓ. *)
      iMod (gen_heap_update with "Hheap ℓPts") as "[Hheap ℓPts]".
      iFrame "Hheap".
      (* We must now update the authorative element for the lub_view. *)
      iMod (auth_lub_view_insert with "lubauth") as "[lubauth viewT]"; first done.
      iFrame "lubauth".
      iModIntro.
      iApply ("HΦ" $! t v MV MP). iSplit; first done.
      done.
  Abort.

  Lemma wp_store_release V v p B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V }}}
      (ThreadState (#ℓ <-{rel} v) (ThreadView V p B)) @ s; E
    {{{ t, RET ThreadVal #() (ThreadView (<[ℓ := MaxNat t]>V) p B);
          ⌜msg_val <$> (hist !! t) = None⌝ ∗
          ⌜(V !!0 ℓ) ≤ t⌝ ∗
          valid (<[ℓ := MaxNat t]>V) ∗
          ℓ ↦h (<[t := Msg v (<[ℓ := MaxNat t]>V) p]>hist) }}}.
  Proof.
  Abort.

  (* Lemma wp_cmpxch  *)

  (* Lemma wp_faa  *)

  Lemma wp_wb V P B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist }}}
      (ThreadState (WB #ℓ) (ThreadView V P B)) @ s; E
    {{{ RET ThreadVal #() (ThreadView V P (<[ℓ := MaxNat (V !!0 ℓ)]>B)); ℓ ↦h hist }}}.
  Proof.
    iIntros (ϕ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([??] κ κs k) "(Hheap & Hauth & Hop & Hpers) /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 efs Hstep).
      inv_thread_step. iSplitR=>//.
      iModIntro. iFrame. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_fence V P B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist }}}
      (ThreadState Fence (ThreadView V P B)) @ s; E
    {{{ RET ThreadVal #() (ThreadView V (P ⊔ B) ∅); ℓ ↦h hist }}}.
  Proof.
    iIntros (ϕ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([??] κ κs k) "(Hheap & Hauth & Hop & Hpers) /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 efs Hstep).
      inv_thread_step. iSplitR=>//.
      iModIntro. iFrame. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_fence_fence V P B ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ valid V ∗ persisted P }}}
      (ThreadState FenceSync (ThreadView V P B)) @ s; E
    {{{ RET ThreadVal #() (ThreadView V (P ⊔ B) ∅);
          persisted (P ⊔ B) }}}.
  Proof.
    iIntros (ϕ) "(pts & valV & perP) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([??] κ κs k) "(Hheap & Hauth & Hop & Hpers) /= !>".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hheap pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 efs Hstep).
      inv_thread_step. iSplitR=>//.
      iMod (own_update with "Hpers") as "[Hpers perB]".
      { apply auth_update_alloc.
        apply (op_local_update_discrete _ _ B).
        intros. apply view_valid. }
      iCombine "perP perB" as "perPB".
      rewrite right_id.
      replace (B ⋅ g0) with (g0 ⋅ B) by apply: comm.
      iModIntro. iFrame.
      iApply "HΦ". iFrame.
  Qed.

End lifting.