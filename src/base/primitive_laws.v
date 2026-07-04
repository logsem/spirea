From iris.proofmode Require Import ltac_tactics.
From iris.bi.lib Require Import fractional.
(* From iris.base_logic.lib Require Export gen_heap. (* proph_map. *) *)

(* From PerennialNG.program_logic Require Import ectx_lifting. *)
(* From PerennialNG.program_logic Require Export ectx_language weakestpre lifting. *)
From self.program_logic Require Export ectx_lifting crash_weakestpre.
From self.base Require Import generational_resources class_instances.
From self.nextgen Require Import nextgen_promises.

From iris.algebra Require Import auth gmap numbers.
From iris_named_props Require Import named_props.
From iris.prelude Require Import options.

From self.nextgen Require Import omega.
From self Require Import extra ipm_tactics.
From self Require Import view_slice cred_frag.
From self.algebra Require Import view.
From self.lang Require Export notation tactics.

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

Lemma max_msg_insert t msg hist :
  max_msg (<[t:=msg]> hist) = t `max` max_msg hist.
Proof.
  rewrite /max_msg. rewrite dom_insert.
  destruct (decide (t ∈ (dom hist))) as [Hin|Hin].
  - replace ({[t]} ∪ dom hist) with (dom hist) by set_solver.
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

(* prefer perennial definitions around invariants *)
Notation invGS := PerennialNG.base_logic.lib.wsat.invGS.invGS.
Notation inv := PerennialNG.base_logic.lib.invariants.inv.

Definition borrowN := nroot .@ "borrow".
Definition crash_borrow_ginv_number : nat := 6%nat.
Definition crash_borrow_ginv `{!invGS Σ} `{Ω : gGenCmras Σ} `{creditGS Σ}
  := (inv borrowN (cred_frag crash_borrow_ginv_number)).

Class PerennialG Σ := {
  P_invGS :> invGS Σ;
  P_creditG :> creditGS Σ;
}.

Class extraStateInterp Σ := {
  extra_state_interp : iProp Σ;
}.

Global Program Instance Perennial_irisGS
       `{!PerennialG Σ, extraStateInterp Σ, Ω : gGenCmras Σ, !nvmBaseGS Σ Ω} :
  crash_weakestpre.irisGS nvm_lang Σ Ω := {
  iris_invGS := P_invGS;
  global_state_interp g ns mj D _ :=
      (validV ∅ ∗ ∃ ns' mj' D', ⌜ ns = ns' ∧ mj = mj' ∧ D = D' ⌝)%I;
    (* (@crash_borrow_ginv _ P_invGS _ _ ∗ *)
    (*  cred_interp ns ∗ *)
    (*  ⌜(/ 2 < mj ≤ 1) ⌝%Qp ∗ *)
    (*  pinv_tok mj D)%I; *)
  fork_post _ := True%I;
  num_laters_per_step := (λ n, 3 ^ (n + 1))%nat; (* This is the choice GooseLang takes. *)
  step_count_next := (λ n, 10 * (n + 1))%nat;
  }.
Next Obligation.
  intros.
  iIntros "[$ ?]".
  by iExistsN.
  (* intros (**). iIntros "($ & ? & $)". *)
  (* by iMod (cred_interp_incr with "[$]") as "($ & _)". *)
Qed.
Next Obligation. intros => //=. lia. Qed.


Global Program Instance nvmBaseG_irisGS
  `{!nvmBaseGS Σ Ω, !extraStateInterp Σ, !PerennialG Σ} :
  irisGS nvm_lang Σ Ω := {
    perennial_irisGS := Perennial_irisGS;
    state_interp σ _ := (nvm_heap_ctx σ ∗ extra_state_interp)%I;
  }.


(** * Lemmas about [max_view] *)
Section max_view.
  Context `{!nvmBaseGS Σ Ω}.
  Implicit Types hist : history.
  Implicit Types ℓ : loc.

  Lemma valid_heap_lookup heap ℓ hist :
    valid_heap heap → heap !! ℓ = Some hist → is_Some (hist !! 0).
  Proof.
    intros val ?. eapply map_Forall_lookup_1 in val; last done. apply val.
  Qed.

  Lemma valid_heap_msg_lookup heap ℓ hist t v SV FV PV :
    valid_heap heap →
    heap !! ℓ = Some hist →
    hist !! t = Some (Msg v SV FV PV) →
    SV ⊑ max_view heap.
  Proof.
    intros val heapLook histLook.
    apply val in heapLook. apply heapLook in histLook. done.
  Qed.

  (* If a location has history [hist] then looking up a message from the
  max_view will result in some message. *)
  Lemma history_lookup_lub heap ℓ hist :
    heap !! ℓ = Some hist →
    is_Some (hist !! 0) →
    is_Some (hist !! ((max_view heap) !!0 ℓ)).
  Proof.
    intros Ha Hb.
    rewrite /max_view. rewrite /lookup_zero !lookup_fmap. rewrite Ha.
    simpl. apply lookup_max_msg. done.
  Qed.

  Lemma history_lookup_lub_valid heap ℓ hist :
    heap !! ℓ = Some hist →
    valid_heap heap →
    is_Some (hist !! ((max_view heap) !!0 ℓ)).
  Proof.
    intros Ha Hb.
    apply history_lookup_lub; first done.
    eapply valid_heap_lookup; done.
  Qed.

  Lemma history_lookup_lub_succ heap ℓ hist :
    heap !! ℓ = Some hist →
    hist !! ((max_view heap !!0 ℓ) + 1) = None.
  Proof.
    intros look.
    rewrite /max_view. rewrite /lookup_zero !lookup_fmap. rewrite look.
    simpl. apply lookup_max_msg_succ.
  Qed.

  Lemma max_view_incl_insert V heap ℓ t msg hist :
    heap !! ℓ = Some hist →
    V ≼ max_view heap →
    <[ℓ := MaxNat t]>V ≼ max_view (<[ℓ := (<[t := msg]> hist)]> heap).
  Proof.
    intros look incl.
    rewrite lookup_included. intros ℓ'.
    rewrite !lookup_fmap.
    destruct (decide (ℓ = ℓ')).
    * subst. rewrite !lookup_insert_eq. simpl.
      apply Some_included_2.
      right. apply max_nat_included. simpl.
      rewrite max_msg_insert.
      lia.
    * rewrite !lookup_insert_ne; [|done|done].
      move: incl. rewrite lookup_included.
      intros le. pose proof (le ℓ') as le.
      etrans; first apply le.
      rewrite !lookup_fmap. done.
  Qed.

  Lemma max_view_union σ σ' :
    σ ##ₘ σ' → max_view σ ⊔ max_view σ' = max_view (σ ∪ σ').
  Proof.
    intros disj.
    rewrite /max_view.
    apply map_eq. intros ℓ.
    rewrite view_join.
    rewrite lookup_op.
    rewrite !lookup_fmap.
    destruct (σ !! ℓ) eqn:look; simpl.
    - erewrite lookup_union_Some_l; last apply look.
      erewrite map_disjoint_Some_r; done.
    - rewrite left_id.
      destruct (σ' !! ℓ) eqn:look'; simpl.
      * erewrite lookup_union_Some_r; done.
      * assert ((σ ∪ σ') !! ℓ = None) as ->. { by apply lookup_union_None. }
        done.
  Qed.

  Lemma max_view_included_union_l σ σ' : σ ##ₘ σ' → max_view σ ⊑ max_view (σ ∪ σ').
  Proof. intros disj. rewrite -max_view_union; last done. apply view_le_l. Qed.

  Lemma max_view_included_union_r σ σ' : σ ##ₘ σ' → max_view σ ⊑ max_view (σ' ∪ σ).
  Proof. intros disj. rewrite -max_view_union; last done. apply view_le_r. Qed.

  (* If a new message is inserted into the heap the max_view can only grow. *)
  Lemma max_view_insert_incl (ℓ : loc) (t : time) (msg : message) hist (heap : store) :
    heap !! ℓ = Some hist →
    max_view heap ⊑ max_view (<[ℓ := (<[t := msg]> hist)]> heap).
  Proof.
    rewrite subseteq_view_incl.
    rewrite lookup_included.
    intros look ℓ'.
    rewrite !lookup_fmap.
    destruct (decide (ℓ = ℓ')).
    * subst. rewrite lookup_insert_eq. rewrite look. simpl.
      apply Some_included_2.
      right. apply max_nat_included. simpl.
      apply max_msg_le_insert.
    * rewrite lookup_insert_ne; done.
  Qed.

  (***** Lemmas about ownership over [max_view]. *)

  Lemma max_view_lookup_insert_eq ℓ t msg hist (heap : store) :
    ∃ t', max_view (<[ℓ := <[t := msg]> hist]> heap) !! ℓ = Some (MaxNat t') ∧ t ≤ t'.
  Proof.
    rewrite /max_view.
    rewrite fmap_insert.
    rewrite lookup_fmap.
    rewrite lookup_insert_eq.
    eexists _.
    simpl.
    split; first reflexivity.
    rewrite /max_msg.
    rewrite dom_insert.
    apply max_list_elem_of_le.
    apply elem_of_elements.
    set_solver.
  Qed.

  Lemma auth_both_max_view_insert ℓ t (heap : store) V (hist : history) msg :
    heap !! ℓ = Some hist →
    store_view_auth (max_view heap) -∗
    validV V ==∗
    store_view_auth (max_view (<[ℓ := <[t := msg]> hist]> heap)) ∗
    validV (<[ℓ := MaxNat t]> V).
  Proof.
    iIntros (look) "Olub Flub".
    iNamed "Olub".
    pose proof (max_view_insert_incl ℓ t msg hist heap look) as incl.
    iDestruct (gen_own_valid_2 with "store_view_at Flub") as %[? ?]%auth_both_valid_discrete.
    iMod (gen_own_update with "store_view_at") as "store_view_at".
    { apply auth_auth_grow; last apply incl.
      apply view_valid. }
    iMod (gen_own_update with "store_view_at") as "[$ $]".
    { apply: auth_update_dfrac_alloc.
      apply max_view_incl_insert; done. }
    done.
  Qed.
End max_view.

Section lifting.
  Context `{!nvmBaseGS Σ Ω, extra : !extraStateInterp Σ, !PerennialG Σ}.

  Notation storeI := store_viewGpreS_store_view.
  Notation persistedI := persistedGpreS_persisted.

  Implicit Types Q : iProp Σ.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types efs : list expr.
  (* Implicit Types σ : state. *)
  Implicit Types v : val.
  Implicit Types ℓ : loc.
  Implicit Types V W : view.
  Implicit Types hist : history.

  Global Instance valid_persistent V : Persistent (validV V).
  Proof. apply _. Qed.

  Lemma gen_own_auth_frag_leq V W γ :
    gen_own (i := genInDepsG_gen storeI) γ (◯ V) -∗ gen_own (i := genInDepsG_gen storeI) γ (● W) -∗ ⌜V ⊑ W⌝.
  Proof.
    iIntros "H1 H2".
    rewrite /validV.
    iDestruct (gen_own_valid_2 with "H2 H1") as %[Hincl _]%auth_both_valid_discrete.
    done.
  Qed.

  Lemma hist_inv_grow (heap : store) (W W' : view) :
    W ⊑ W' →
    valid_heap_lub W heap →
    valid_heap_lub W' heap.
  Proof.
    intros incl M.
    intros ℓ h look.
    pose proof (map_Forall_lookup_1 _ _ _ _ M look) as [? M'].
    split; first done.
    intros t msg look'.
    pose proof (map_Forall_lookup_1 _ _ _ _ M' look') as incl'.
    by trans W.
  Qed.

  (* Insert a new message into [hist_inv]. *)
  Lemma hist_inv_insert_msg (heap : store) v p ℓ t hist V PV :
    heap !! ℓ = Some hist →
    hist !! t = None →
    V ≼ max_view (<[ℓ:=<[t:= Msg v V PV p]> hist]> heap) →
    valid_heap heap →
    valid_heap (<[ℓ:=<[t := Msg v V PV p]> hist]> heap).
  Proof.
    intros look histLook Vincl M.
    apply map_Forall_insert_2.
    - rewrite /hist_inv.
      pose proof (map_Forall_lookup_1 _ _ _ _ M look) as [? ?].
      split.
      * apply lookup_insert_is_Some'. by right.
      *
        apply map_Forall_insert_2.
        + done.
        + eapply map_Forall_impl; first done.
          simpl.
          intros ???.
          etrans; first done.
          by apply max_view_insert_incl.
    - eapply hist_inv_grow; last apply M.
      by apply max_view_insert_incl.
  Qed.

  Lemma view_valid (V : view) : ✓ V.
  Proof. intros ?. case (_ !! _); done. Qed.

  Lemma auth_auth_view_grow_op γ V V' :
    gen_own (i := genInDepsG_gen persistedI) γ (● V) ==∗
    gen_own (i := genInDepsG_gen persistedI) γ (● (V ⋅ V')) ∗ gen_own (i := genInDepsG_gen persistedI) γ (◯ V').
  Proof.
    iIntros "H".
    iMod (gen_own_update with "H") as "[Ho Hf]".
    { apply auth_update_alloc.
      apply (op_local_update_discrete _ _ V').
      intros. apply view_valid. }
    rewrite comm.
    rewrite right_id.
    by iFrame.
  Qed.

  Lemma store_auth_auth_view_grow_incl γ V V' :
    V ⊑ V' →
    gen_own (i := genInDepsG_gen storeI) γ (● V) ==∗
    gen_own (i := genInDepsG_gen storeI) γ (● V').
  Proof.
    iIntros (incl) "H".
    iMod (gen_own_update with "H") as "$"; last done.
    apply auth_auth_grow. - apply view_valid. - done.
  Qed.

  (* TODO: I cannot get the same lemma to work for two different ghost resource when their dependency
   * different *)

  Lemma persisted_auth_auth_view_grow_incl γ V V' :
    V ⊑ V' →
    gen_own (i := genInDepsG_gen persistedI) γ (● V) ==∗
    gen_own (i := genInDepsG_gen persistedI) γ (● V').
  Proof.
    iIntros (incl) "H".
    iMod (gen_own_update with "H") as "$"; last done.
    apply auth_auth_grow. - apply view_valid. - done.
  Qed.

  Lemma store_view_alloc_big (σ σ' : (gmap loc history)) :
    σ' ##ₘ σ →
    gen_own (i := genInDepsG_gen storeI) store_view_name (● (max_view (σ))) ==∗
    gen_own (i := genInDepsG_gen storeI) store_view_name (● (max_view (σ' ∪ σ))).
  Proof.
    iIntros (disj) "H".
    iMod (store_auth_auth_view_grow_incl with "H") as "$"; last done.
    rewrite map_union_comm; last done.
    apply max_view_included_union_l. done.
  Qed.

  Lemma message_included_in_max_view ℓ (hist : history) heap t v MV MP MPP :
    heap !! ℓ = Some hist →
    hist !! t = Some (Msg v MV MP MPP) →
    valid_heap heap →
    MV ⊑ max_view heap.
  Proof.
    intros heapLook histLook M.
    pose proof (map_Forall_lookup_1 _ _ _ _ M heapLook) as [? M'].
    pose proof (map_Forall_lookup_1 _ _ _ _ M' histLook) as ?.
    done.
  Qed.

  Lemma hist_inv_alloc ℓ a SV PV v0 n heap :
    SV ⊑ max_view heap →
    heap_array ℓ a SV PV (replicate (Z.to_nat n) v0) ##ₘ heap →
    valid_heap heap →
    valid_heap (heap_array ℓ a SV PV (replicate (Z.to_nat n) v0) ∪ heap).
  Proof.
    rewrite /valid_heap /valid_heap_lub.
    intros incl disj val.
    apply map_Forall_union; first done. split.
    - intros ? ? (j & w & ? & Hjl & eq & mo)%heap_array_lookup.
      rewrite eq.
      split. { rewrite lookup_singleton_eq. naive_solver. }
      apply map_Forall_singleton. simpl.
      destruct a.
      * apply view_empty_least.
      * etrans; last apply max_view_included_union_r; done.
    - eapply map_Forall_impl; first apply val.
      intros ℓ' hist [??].
      split; first done.
      eapply map_Forall_impl; first done.
      simpl. intros ???.
      etrans; first done.
      apply max_view_included_union_r.
      done.
  Qed.

  (* some of the implicit arguments are giving me trouble. *)
  Ltac whack_global :=
    iPoseProof (global_state_interp_le (Λ := nvm_lang) _ _ ()) as "impl";
    last iMod ("impl" with "[$]") as "$";
    first (rewrite /step_count_next; simpl; lia).
  
  Lemma wp_fork s E (e : expr) TV (Φ : thread_val → iProp Σ) :
    ▷ WP (ThreadState e TV) @ s; ⊤ {{ _, True }} -∗
    ▷ Φ (ThreadVal (LitV LitUnit) TV) -∗
    WP ThreadState (Fork e) TV @ s; E {{ Φ }}.
  Proof.
    iIntros "He HΦ".
    iApply (wp_lift_atomic_head_step (Φ := Φ)); first done.
    iIntros (σ1 [] mj D ns κ κs n) "Hσ Hg !>".
    iPureGoal.
    { rewrite /base_reducible.
      destruct TV as [[SV FV] BV].
      eexists [], _, _, _, _. simpl.
      constructor. constructor. }
    iNext. iIntros (v2 σ2 g2 efs Hstep).
    whack_global.
    inv_head_step. inv_thread_step. by iFrame.
  Qed.

  (* Create a message from a [value] and a [thread_view]. *)
  Definition mk_message (v : val) (T : thread_view) := Msg v (store_view T) (flush_view T).

  (** Rules for memory operations. **)

  Lemma heap_array_to_seq_mapsto ℓ a (SV PV : view) (v : val) (n : nat) :
    ([∗ map] ℓ' ↦ ov ∈ heap_array ℓ a SV PV (replicate n v), ℓ' ↦fh ov) -∗
    [∗ list] i ∈ seq 0 n, (ℓ +ₗ (i : nat)) ↦fh initial_history a SV PV v.
  Proof.
    iIntros "Hvs". iInduction n as [|n] "IH" forall (ℓ); simpl.
    { done. }
    rewrite big_opM_union; last first.
    { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
      intros (j&w&?&Hjl&_)%heap_array_lookup.
      rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
    rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite <-Loc.add_assoc.
    rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
  Qed.

  Lemma wp_allocN v a SV FV BV n s E :
    (0 < n)%Z →
    {{{ validV SV }}}
      AllocN a #n v `at` (SV, FV, BV) @ s; E
    {{{ ℓ CV, RET (#ℓ `at` (SV, FV, BV));
      crashed_at CV ∗
      ([∗ list] i ∈ seq 0 (Z.to_nat n),
        (ℓ +ₗ (i : nat)) ↦fh initial_history a SV FV v) ∗
      ⌜ ∀ (i : Z), (0 ≤ i < n)%Z → SV !!0 (ℓ +ₗ i) = 0 ⌝ ∗
      (* The allocated locations are not in the last view we crashed at. *)
      ([∗ list] i ∈ seq 0 (Z.to_nat n), (⌜ℓ +ₗ (i : nat) ∉ dom CV⌝))
    }}}.
  Proof.
    iIntros (Hn Φ) "Hval HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([σ PV] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "Hg !>".
    simpl in *. subst σ.
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    (* The time at the view is smaller than the time in the lub view (which is *)
    (* the time of the most recent message *)
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iSplit.
    - (* We must show that [ref v] is can take some step. *)
       rewrite /base_reducible.
       (* destruct TV as [[sv pv] bv]. *)
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step.
       * constructor. lia.
       * apply alloc_fresh. lia.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *.
      inv_impure_thread_step.
      iSplitR=>//.
      assert ((heap_array ℓ a SV FV (replicate (Z.to_nat n) v)) ##ₘ store_drop_prefix OCV full_hist) as Hdisj.
      { apply heap_array_map_disjoint.
        rewrite length_replicate. assumption. }
      rewrite map_disjoint_dom in Hdisj.
      rewrite dom_store_drop_prefix -map_disjoint_dom in Hdisj.
      (* We now update the [gen_heap] ghost state to include the allocated location. *)
      iMod (heap_alloc_big_fmapsto with "Hσ") as "[Hσ Hl]"; first apply Hdisj.
      rewrite /state_init_heap.
      simpl.
      iMod (store_view_alloc_big with "store_view_at") as "$".
      { apply heap_array_map_disjoint.
        rewrite length_replicate. assumption. }
      iModIntro.
      rewrite -!assoc.
      simpl.
      (* get [rely_self] for [crashed] *)
      iDestruct (crashed_at_auth_crashed_at with "[$] [$]") as "#rely".
      iDestruct ("HΦ" with "[Hl]") as "$".
      + iFrame "#".
        iDestruct (heap_array_to_seq_mapsto with "Hl") as "$".
        rewrite -> dom_store_drop_prefix in *.
        apply view_le_dom_subseteq in Vincl.
        iSplit.
        { iPureIntro. intros i le.
          apply lookup_zero_None_zero.
          (* For future me: [H13] is the hypothesis about everything
           * in the newly allocated range are absent from [full_hist] *)
          specialize (H13 i ltac:(lia) ltac:(lia)).
          rewrite <- ?not_elem_of_dom in *.
          set_solver. }
        rewrite big_sepL_forall.
        iIntros (? i [hi ho]%lookup_seq) "!%".
        eapply not_elem_of_weaken; last done.
        rewrite view_sub_dom_eq.
        specialize (H13 i ltac:(lia) ltac:(lia)).
        rewrite <- ?not_elem_of_dom in *.
        rewrite dom_store_drop_prefix in H13.
        set_solver.
      + iFrame "extra".
        iExists _, _, _.
        iFrame "∗#%".
        rewrite ?store_drop_prefix_union; last done.
        rewrite (disjoint_store_drop_prefix _ (heap_array _ _ _ _ _)).
        2: { pose proof (dom_store_drop_prefix OCV full_hist).
             rewrite map_disjoint_dom in Hdisj.
             set_solver. }
        iSplit; first done.
        iSplit.
        { iPureIntro.
          apply hist_inv_alloc; try done.
          rewrite -> map_disjoint_dom in *.
          rewrite dom_store_drop_prefix.
          done. }
        iPureIntro.
        set_solver.
  Qed.

  Lemma wp_alloc s a E v SV FV BV :
    {{{ validV SV }}}
      Alloc a (Val v) `at` (SV, FV, BV) @ s; E
    {{{ ℓ CV, RET LitV (LitLoc ℓ) `at` (SV, FV, BV);
        crashed_at CV ∗ ⌜ℓ ∉ dom CV⌝ ∗ ⌜ SV !!0 ℓ = 0 ⌝ ∗
        ℓ ↦fh initial_history a SV FV v }}}.
  Proof.
    iIntros (Φ) "#Hval HΦ".
    iApply wp_allocN; [lia|auto|]; first iFrame.
    iNext.
    iIntros (ℓ CV) "/= (? & ? & % & ?)". rewrite !right_id. rewrite Loc.add_0.
    iApply "HΦ"; iFrame.
    iPureIntro. rewrite -(Loc.add_0 ℓ). auto with lia.
  Qed.

  (* Non-atomic load. *)
  Lemma wp_load (SV FV BV : view) ℓ q (hist : history) s E :
    {{{ ℓ ↦h{q} hist ∗ validV SV }}}
      !_NA #ℓ `at` (SV, FV, BV) @ s; E
    {{{ t msg, RET msg.(msg_val) `at` (SV, FV, BV);
        ℓ ↦h{q} hist ∗ ⌜hist !! t = Some msg ∧ SV !!0 ℓ ≤ t⌝ }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    iDestruct (mapsto_heap_valid with "crashed_at_offset Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook) as [msg Hmsgeq]; first done.
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iNamed "store_view_auth".
      iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      iSplitR=>//.
      iFrame.
      (* iFrame "Hheap lubauth persist Hincl Ht". *)
      rewrite -lookup_fmap in H10.
      apply lookup_fmap_Some in H10.
      destruct H10 as [x [<- ?]].
      iDestruct ("HΦ" with "[$ℓPts //]") as "$".
      iModIntro.
      iExists OV.
      simpl.
      iFrame "#∗".
      done.
  Qed.

  Lemma wp_load_alt (OCV SV FV BV: view) ℓ q (h : history) s E :
    {{{ crashed_at_offset OCV ∗ ℓ ↦fh{q} h ∗ validV SV }}}
      !_NA #ℓ `at` (SV, FV, BV) @ s; E
    {{{ t msg, RET msg.(msg_val) `at` (SV, FV, BV);
        ℓ ↦fh{q} h ∗ ⌜h !! t = Some msg ∧ Nat.add (SV !!0 ℓ) (OCV !!0 ℓ) ≤ t⌝ }}}.
  Proof.
    set hist := (drop_prefix h (OCV !!0 ℓ)).
    iIntros (Φ) "(#offsets & ℓPts & Hval) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* The time at the view is smaller than the time in the lub view (which is
    the time of the most recent message *)
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert ⌜ OCV0 = OCV ⌝%I as %->.
    { iAssert (crashed_at_offset OCV0)%I as "#crashed_at_offset"; first by iExists _.
      iDestruct (crashed_at_offset_agree with "offsets crashed_at_offset") as %->.
      done. }
    
    iDestruct (fmapsto_heap_valid with "Hσ ℓPts") as %Hlook'.
    assert (store_drop_prefix OCV full_hist !! ℓ = Some hist) as Hlook.
    { rewrite store_drop_prefix_alt Hlook' /= //. }

    iSplit.
    - (* We must show that the load can take some step. To do this we must use
      the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgSV msgP] Hmsgeq]; first done.
      (* The time at the view is smaller than the time in the lub view (which is
      the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      iFrame.
      (* [H10 : msg_val <$> hist !! t = Some v] *)
      rewrite -lookup_fmap in H10.
      apply lookup_fmap_Some in H10.
      destruct H10 as [x [<- ?]].
      iDestruct ("HΦ" $! (t + (OCV !!0 ℓ)) with "[$ℓPts]") as "$".
      { iPureIntro.
        split; last lia.
        rewrite -drop_prefix_lookup //. }
      iExists OV.
      simpl.
      iFrame "∗#".
      done.
  Qed.
  
  Lemma wp_load_acquire SV PV BV ℓ q (hist : history) s E :
    {{{ ℓ ↦h{q} hist ∗ validV SV }}}
      !_AT #ℓ `at` (SV, PV, BV) @ s; E
    {{{ t v SV2 PV2 _P, RET v `at` (SV ⊔ SV2, PV, BV ⊔ PV2);
        ⌜ hist !! t = Some (Msg v SV2 PV2 _P) ⌝ ∗
        ⌜ SV !!0 ℓ ≤ t ⌝ ∗
        validV (SV ⊔ SV2) ∗
        ℓ ↦h{q} hist }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* The time at the view is smaller than the time in the lub view (which is
    the time of the most recent message *)
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    iDestruct (mapsto_heap_valid with "crashed_at_offset Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
      the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgSV msgP] Hmsgeq]; first done.
      (* The time at the view is smaller than the time in the lub view (which is
      the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      iMod (gen_own_update with "store_view_at") as "[store_view_at valid']".
      { apply (auth_update_dfrac_alloc _ _ (SV ⋅ MV)).
        rewrite -subseteq_view_incl.
        apply view_lub_le; first done.
        eapply message_included_in_max_view; done. }
      iFrame. iModIntro.
      iDestruct ("HΦ" $! t v MV MP _ with "[$ℓPts $valid' //]") as "$".
      iExists OV.
      simpl.
      iFrame "#∗".
      done.
  Qed.

  Lemma wp_load_acquire_alt OCV SV PV BV ℓ q (h : history) s E :
    {{{ crashed_at_offset OCV ∗ ℓ ↦fh{q} h ∗ validV SV }}}
      !_AT #ℓ `at` (SV, PV, BV) @ s; E
    {{{ t v SV2 PV2 _P, RET v `at` (SV ⊔ SV2, PV, BV ⊔ PV2);
        ⌜ h !! t = Some (Msg v SV2 PV2 _P) ⌝ ∗
        ⌜ Nat.add (SV !!0 ℓ) (OCV !!0 ℓ) ≤ t ⌝ ∗
        validV (SV ⊔ SV2) ∗
        ℓ ↦fh{q} h }}}.
  Proof.
    set hist := (drop_prefix h (OCV !!0 ℓ)).
    iIntros (Φ) "(#offsets & ℓPts & Hval) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* The time at the view is smaller than the time in the lub view (which is
    the time of the most recent message *)
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert ⌜ OCV0 = OCV ⌝%I as %->.
    { iAssert (crashed_at_offset OCV0)%I as "#crashed_at_offset"; first by iExists _.
      iDestruct (crashed_at_offset_agree with "offsets crashed_at_offset") as %->.
      done. }
    
    iDestruct (fmapsto_heap_valid with "Hσ ℓPts") as %Hlook'.
    assert (store_drop_prefix OCV full_hist !! ℓ = Some hist) as Hlook.
    { rewrite store_drop_prefix_alt Hlook' /= //. }

    iSplit.
    - (* We must show that the load can take some step. To do this we must use
      the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgSV msgP] Hmsgeq]; first done.
      (* The time at the view is smaller than the time in the lub view (which is
      the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor; last by apply view_lt_lt.
        + done.
        + rewrite Hmsgeq. done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      iMod (gen_own_update with "store_view_at") as "[store_view_at valid']".
      { apply (auth_update_dfrac_alloc _ _ (SV ⋅ MV)).
        rewrite -subseteq_view_incl.
        apply view_lub_le; first done.
        eapply message_included_in_max_view; done. }
      iFrame. iModIntro.
      iDestruct ("HΦ" $! (t + (OCV !!0 ℓ)) v MV MP _ with "[$ℓPts $valid']") as "$".
      { iPureIntro.
        split; last lia.
        rewrite -drop_prefix_lookup //. }
      iExists OV.
      simpl.
      iFrame "∗#".
      done.
  Qed.

  Lemma wp_store v SV PV BV ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ validV SV }}}
      (#ℓ <-_NA v) `at` (SV, PV, BV) @ s; E
    {{{ t, RET #() `at` (<[ℓ := MaxNat t]>SV, PV, BV);
          ⌜hist !! t = None⌝ ∗
          ⌜(SV !!0 ℓ) < t⌝ ∗
          validV (<[ℓ := MaxNat t]>SV) ∗
          ℓ ↦h (<[t := Msg v ∅ ∅ PV]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    iDestruct (mapsto_heap_valid with "crashed_at_offset Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iNamed "store_view_auth".
      iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ Vincl ℓ _ eq_refl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      iSplitR=>//.
      assert (ℓ ∈ dom full_hist) as elemOf.
      { apply elem_of_dom_2 in Hlook.
        by rewrite dom_store_drop_prefix in Hlook. }
      pose proof elemOf.
      apply elem_of_dom in elemOf as [h Hlook'].
      assert (hist = drop_prefix h (OCV !!0 ℓ)) as drop_eq.
      { rewrite store_drop_prefix_alt Hlook' /= in Hlook.
           by simplify_eq. }
      iMod (mapsto_heap_update with "[$] Hσ ℓPts") as "[Hσ ℓPts]".
      iEval (rewrite <- drop_prefix_insert) in "ℓPts".
      iEval (rewrite <- drop_eq) in "ℓPts".
      iMod (auth_both_max_view_insert with "[$] [$]")
        as "[store_view_auth Hval]"; [done|].
      rewrite -?(insert_store_drop_prefix _ _ _ h); try assumption.
      iDestruct ("HΦ" with "[$ℓPts $Hval //]") as "$".
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#".
      iSplit; first done.
      iSplit.
      { iPureIntro.
        simpl.
        erewrite insert_store_drop_prefix; try eassumption.
        apply hist_inv_insert_msg; try done.
        apply view_empty_least. }
      iPureIntro.
      simpl.
      erewrite insert_store_drop_prefix; try eassumption.
      rewrite dom_insert_L.
      set_solver.
  Qed.

  Lemma wp_store_alt v OCV SV PV BV ℓ (h : history) s E :
    {{{ crashed_at_offset OCV ∗ ℓ ↦fh h ∗ validV SV }}}
      (#ℓ <-_NA v) `at` (SV, PV, BV) @ s; E
    {{{ t, RET #() `at` (<[ℓ := MaxNat (t - (OCV !!0 ℓ))]>SV, PV, BV);
          ⌜h !! t = None⌝ ∗
          ⌜Nat.add (OCV !!0 ℓ) (SV !!0 ℓ) < t⌝ ∗
          validV (<[ℓ := MaxNat (t - (OCV !!0 ℓ))]>SV) ∗
          ℓ ↦fh (<[t := Msg v ∅ ∅ PV]>h) }}}.
  Proof.
    set hist := (drop_prefix h (OCV !!0 ℓ)).
    iIntros (Φ) "(#offsets & ℓPts & Hval) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert ⌜ OCV0 = OCV ⌝%I as %->.
    { iAssert (crashed_at_offset OCV0)%I as "#crashed_at_offset"; first by iExists _.
      iDestruct (crashed_at_offset_agree with "offsets crashed_at_offset") as %->.
      done. }
    
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iDestruct (fmapsto_heap_valid with "Hσ ℓPts") as %Hlook'.
    assert (store_drop_prefix OCV full_hist !! ℓ = Some hist) as Hlook.
    { rewrite store_drop_prefix_alt Hlook' /= //. }

    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ Vincl ℓ _ eq_refl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      iSplitR=>//.
      assert (ℓ ∈ dom full_hist) as elemOf.
      { apply elem_of_dom_2 in Hlook.
        by rewrite dom_store_drop_prefix in Hlook. }
      (* pose proof elemOf. *)
      (* apply elem_of_dom in elemOf as [h Hlook']. *)
      iMod (fmapsto_heap_update with "Hσ ℓPts") as "[Hσ ℓPts]".
      (* iEval (rewrite <- drop_prefix_insert) in "ℓPts". *)
      (* iEval (rewrite <- drop_eq) in "ℓPts". *)
      iMod (auth_both_max_view_insert with "[$] [$]")
        as "[store_view_at Hval]"; [done|].
      (* rewrite -?(insert_store_drop_prefix _ _ _ h); try (subst hist; done). *)
      iSpecialize ("HΦ" $! (t + (OCV !!0 ℓ))).
      replace (t + (OCV !!0 ℓ) - (OCV !!0 ℓ)) with t by lia.
      (* rewrite -?(insert_store_drop_prefix _ _ _ h); try by subst hist. *)
      iDestruct ("HΦ" with "[$ℓPts $Hval]") as "$".
      { iSplit; iPureIntro; last lia.
        subst hist.
        (*   H10 : drop_prefix h (OCV !!0 ℓ) !! t = None *)
        rewrite drop_prefix_lookup // in H10. }
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#".
      subst hist. simpl.
      iSplit.
      { iPureIntro.
        simpl.
        by erewrite insert_store_drop_prefix. }
      iSplit.
      { iPureIntro.
          simpl.
          (* erewrite insert_store_drop_prefix; try eassumption. *)
          apply hist_inv_insert_msg; try done.
          apply view_empty_least. }
      iPureIntro.
      simpl.
      rewrite dom_insert_L.
      set_solver.
  Qed.
  
  Lemma wp_store_release SV v FV BV ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ validV SV }}}
      #ℓ <-_AT v `at` (SV, FV, BV) @ s; E
    {{{ t, RET #() `at` (<[ℓ := MaxNat t]>SV, FV, BV);
          ⌜ hist !! t = None ⌝ ∗
          ⌜ SV !!0 ℓ < t ⌝ ∗
          validV (<[ℓ := MaxNat t]>SV) ∗
          ℓ ↦h (<[t := Msg v (<[ℓ := MaxNat t]>SV) FV FV]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iDestruct (mapsto_heap_valid with "crashed_at_offset Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ Vincl ℓ _ eq_refl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      iSplitR=>//.
      assert (ℓ ∈ dom full_hist) as elemOf.
      { apply elem_of_dom_2 in Hlook.
        by rewrite dom_store_drop_prefix in Hlook. }
      pose proof elemOf.
      apply elem_of_dom in elemOf as [h Hlook'].
      assert (hist = drop_prefix h (OCV !!0 ℓ)) as drop_eq.
      { rewrite store_drop_prefix_alt Hlook' /= in Hlook.
           by simplify_eq. }
      iMod (mapsto_heap_update with "[$] Hσ ℓPts") as "[Hσ ℓPts]".
      iEval (rewrite <- drop_prefix_insert) in "ℓPts".
      iEval (rewrite <- drop_eq) in "ℓPts".
      iMod (auth_both_max_view_insert with "[$] [$]")
        as "[store_view_at Hval]"; [done|].
      rewrite -?(insert_store_drop_prefix _ _ _ h); try assumption.
      iDestruct ("HΦ" with "[$ℓPts $Hval //]") as "$".
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#".
      iSplit; first done.
      iSplit.
      { iPureIntro.
        simpl.
        erewrite insert_store_drop_prefix; try eassumption.
        apply hist_inv_insert_msg; try done.
        apply max_view_incl_insert; done. }
      iPureIntro.
      simpl.
      erewrite insert_store_drop_prefix; try eassumption.
      rewrite dom_insert_L.
      set_solver.
  Qed.
  Lemma wp_store_release_alt OCV SV v FV BV ℓ (h : history) s E :
    {{{ crashed_at_offset OCV ∗ ℓ ↦fh h ∗ validV SV }}}
      #ℓ <-_AT v `at` (SV, FV, BV) @ s; E
    {{{ t, RET #() `at` (<[ℓ := MaxNat (t - (OCV !!0 ℓ))]>SV, FV, BV);
          ⌜ h !! t = None ⌝ ∗
          ⌜ Nat.add (SV !!0 ℓ) (OCV !!0 ℓ) < t ⌝ ∗
          validV (<[ℓ := MaxNat (t - (OCV !!0 ℓ))]>SV) ∗
          ℓ ↦fh (<[t := Msg v (<[ℓ := MaxNat (t - (OCV !!0 ℓ))]>SV) FV FV]>h) }}}.
  Proof.
    set hist := (drop_prefix h (OCV !!0 ℓ)).
    iIntros (Φ) "(#offsets & ℓPts & Hval) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert ⌜ OCV0 = OCV ⌝%I as %->.
    { iAssert (crashed_at_offset OCV0)%I as "#crashed_at_offset"; first by iExists _.
      iDestruct (crashed_at_offset_agree with "offsets crashed_at_offset") as %->.
      done. }
    
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iDestruct (fmapsto_heap_valid with "Hσ ℓPts") as %Hlook'.
    assert (store_drop_prefix OCV full_hist !! ℓ = Some hist) as Hlook.
    { rewrite store_drop_prefix_alt Hlook' /= //. }

    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /base_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ Vincl ℓ _ eq_refl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      iSplitR=>//.
      assert (ℓ ∈ dom full_hist) as elemOf.
      { apply elem_of_dom_2 in Hlook.
        by rewrite dom_store_drop_prefix in Hlook. }
      (* pose proof elemOf. *)
      (* apply elem_of_dom in elemOf as [h Hlook']. *)
      iMod (fmapsto_heap_update with "Hσ ℓPts") as "[Hσ ℓPts]".
      (* iEval (rewrite <- drop_prefix_insert) in "ℓPts". *)
      (* iEval (rewrite <- drop_eq) in "ℓPts". *)
      iMod (auth_both_max_view_insert with "[$] [$]")
        as "[store_view_at Hval]"; [done|].
      (* rewrite -?(insert_store_drop_prefix _ _ _ h); try (subst hist; done). *)
      iSpecialize ("HΦ" $! (t + (OCV !!0 ℓ))).
      replace (t + (OCV !!0 ℓ) - (OCV !!0 ℓ)) with t by lia.
      iDestruct ("HΦ" with "[$ℓPts $Hval]") as "$".
      { iSplit; iPureIntro; last lia.
        subst hist.
        (*   H10 : drop_prefix h (OCV !!0 ℓ) !! t = None *)
        rewrite drop_prefix_lookup // in H10. }
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#".
      subst hist. simpl.
      iSplit.
      { iPureIntro.
        simpl.
        by erewrite insert_store_drop_prefix. }
      iSplit.
      { iPureIntro.
          simpl.
          (* erewrite insert_store_drop_prefix; try eassumption. *)
          apply hist_inv_insert_msg; try done.
          by apply max_view_incl_insert. }
      iPureIntro.
      simpl.
      rewrite dom_insert_L.
      set_solver.
  Qed.
  
  Lemma wp_cmpxchg ℓ hist (v_i v_t : val) SV FV BV s E :
    ▷ ⌜ (∀ (t : nat) (msg : message),
      SV !!0 ℓ ≤ t → hist !! t = Some msg → vals_compare_safe v_i (msg_val msg)) ⌝ -∗
    {{{ ℓ ↦h hist ∗ validV SV }}}
      CmpXchg #ℓ v_i v_t `at` (SV, FV, BV) @ s; E
    {{{ t v SVm FVm _PVm SV3 b, RET (v, #b) `at` (SV3, FV, BV ⊔ FVm);
      ⌜ SV !!0 ℓ ≤ t ⌝ ∗
      validV SV3 ∗
      ⌜ hist !! t = Some (Msg v SVm FVm _PVm) ⌝ ∗
      ⌜ hist !! (t + 1)%nat = None ⌝ ∗
      ( (* Success *)
        ⌜ b = true ⌝ ∗
        ⌜ v = v_i ⌝ ∗
        ⌜ SV3 = <[ ℓ := MaxNat (t + 1) ]>(SV ⊔ SVm) ⌝ ∗
        ℓ ↦h <[ (t + 1) := Msg v_t SV3 (FV ⊔ FVm) (FV ⊔ FVm) ]>hist
        ∨
        (* Failure *)
        ⌜ b = false ⌝ ∗ ⌜ SV3 = SV ⊔ SVm ⌝ ∗ ℓ ↦h hist)
    }}}.
  Proof.
    iIntros "#safe".
    iIntros "!>" (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra] ?".
    iMod "safe" as "%safe".
    iModIntro.
    iNamed "interp".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iDestruct (mapsto_heap_valid with "crashed_at_offset Hσ ℓPts") as %Hlook.
    iSplit.
    - rewrite /base_reducible.
      (* We need to show that there is _some_ message that the CmpXchg could
       * read. It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgSV msgP] Hmsgeq]; first done.
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      destruct (decide (msgv = v_i)) as [->|neq].
      { iExists [], _, _, _, _. iPureIntro. simpl.
        eapply impure_step.
        * apply CmpXchgSuccS.
        * eapply (MStepRMW _ _ _ _ _ _ _ (max_view (store_drop_prefix OCV full_hist) !!0 ℓ)); try done.
          f_equiv. done. }
      { iExists [], _, _, _, _. iPureIntro. simpl.
        eapply impure_step.
        * apply CmpXchgFailS. apply neq.
        * eapply MStepRMWFail; try done. f_equiv. done. }
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      * iSplitR=>//.
        assert (ℓ ∈ dom full_hist) as elemOf.
        { apply elem_of_dom_2 in Hlook.
          by rewrite dom_store_drop_prefix in Hlook. }
        pose proof elemOf.
        apply elem_of_dom in elemOf as [h Hlook'].
        assert (hist = drop_prefix h (OCV !!0 ℓ)) as drop_eq.
        { rewrite store_drop_prefix_alt Hlook' /= in Hlook.
          by simplify_eq. }
        iMod (mapsto_heap_update with "[$] Hσ ℓPts") as "[Hσ ℓPts]".
        iEval (rewrite <- drop_prefix_insert) in "ℓPts".
        iEval (rewrite <- drop_eq) in "ℓPts".
        assert (MV ⊑ max_view (store_drop_prefix OCV full_hist)) as incl2 by
          by eapply valid_heap_msg_lookup.
        iMod (gen_own_update with "store_view_at") as "[store_view_at mvView]".
        { apply auth_frac.auth_frac_update_core_id; last apply incl2. apply _. }
        iPoseProof (gen_own_op_2 with "Hval mvView") as "Hval".
        rewrite -auth_frag_op.
        iMod (auth_both_max_view_insert with "[$] [$]")
          as "[store_view_at Hval]"; [done|].
        rewrite -?(insert_store_drop_prefix _ _ _ h); try assumption.
        iDestruct ("HΦ" with "[ℓPts $Hval]") as "$".
        { iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iLeft.
          by iFrame. }
        iModIntro.
        iFrame "extra".
        iExists _, _, _.
        iFrame "∗#".
        iSplit; first done.
        iSplit.
        { iPureIntro.
          simpl.
          erewrite insert_store_drop_prefix; try eassumption.
          apply hist_inv_insert_msg; try done.
          apply max_view_incl_insert; first done.
          apply view_lub_le; done. }
        iPureIntro.
        simpl.
        erewrite insert_store_drop_prefix; try eassumption.
        rewrite dom_insert_L.
        set_solver.
      * iSplitR=>//.
        iMod (gen_own_update with "store_view_at") as "[store_view_at valid']".
        { apply (auth_update_dfrac_alloc _ _ (SV ⋅ MV)).
          rewrite -subseteq_view_incl.
          apply view_lub_le; first done.
          eapply message_included_in_max_view; done. }
        iFrame. iModIntro.
        iDestruct ("HΦ" with "[ℓPts $valid']") as "$".
        { iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          iRight.
          by iFrame. }
        iExists OV.
        simpl.
        iFrame "#∗".
        done.
  Qed.

  Lemma wp_cmpxchg_alt ℓ h (v_i v_t : val) SV FV BV OCV s E :
    ▷ ⌜ ∀ (t : nat) (msg : message),
      Nat.add (OCV !!0 ℓ) (SV !!0 ℓ) ≤ t → h !! t = Some msg → vals_compare_safe v_i (msg_val msg) ⌝ -∗
    {{{ ℓ ↦fh h ∗ validV SV ∗ crashed_at_offset OCV }}}
      CmpXchg #ℓ v_i v_t `at` (SV, FV, BV) @ s; E
    {{{ t v SVm FVm _PVm SV3 b, RET (v, #b) `at` (SV3, FV, BV ⊔ FVm);
      ⌜ Nat.add (OCV !!0 ℓ) (SV !!0 ℓ) ≤ t ⌝ ∗
      validV SV3 ∗
      ⌜ h !! t = Some (Msg v SVm FVm _PVm) ⌝ ∗
      ⌜ h !! (t + 1)%nat = None ⌝ ∗
      ( (* Success *)
        ⌜ b = true ⌝ ∗
        ⌜ v = v_i ⌝ ∗
        ⌜ SV3 = <[ ℓ := MaxNat (t - (OCV !!0 ℓ) + 1) ]>(SV ⊔ SVm) ⌝ ∗
        ℓ ↦fh <[ (t + 1) := Msg v_t SV3 (FV ⊔ FVm) (FV ⊔ FVm) ]>h
        ∨
        (* Failure *)
        ⌜ b = false ⌝ ∗ ⌜ SV3 = SV ⊔ SVm ⌝ ∗ ℓ ↦fh h)
    }}}.
  Proof.
    set hist := (drop_prefix h (OCV !!0 ℓ)).
    iIntros "#safe".
    iIntros "!>" (Φ) "(ℓPts & Hval & #offset) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra] ?".
    iMod "safe" as "%safe".
    iModIntro.
    iNamed "interp".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV0)%I as "crashed_at_offset"; first by iExists _.
    iDestruct (crashed_at_offset_agree with "offset crashed_at_offset") as %<-.
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iDestruct (fmapsto_heap_valid with "Hσ ℓPts") as %Hlook'.
    iSplit.
    - rewrite /base_reducible.
      (* We need to show that there is _some_ message that the CmpXchg could
       * read. It could certainly read the most recent message. *)
      assert (store_drop_prefix OCV full_hist !! ℓ = Some hist) as Hlook.
      { rewrite store_drop_prefix_alt Hlook' /= //. }
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgSV msgP] Hmsgeq]; first done.
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      destruct (decide (msgv = v_i)) as [->|neq].
      { iExists [], _, _, _, _. iPureIntro. simpl.
        eapply impure_step.
        * apply CmpXchgSuccS.
        * eapply (MStepRMW _ _ _ _ _ _ _ (max_view (store_drop_prefix OCV full_hist) !!0 ℓ)); try done.
          + f_equiv. done.
          + intros ??? lookSome.
            rewrite drop_prefix_lookup_Some in lookSome.
            apply (safe (t' + (OCV !!0 ℓ))); last done.
            lia. }
      { iExists [], _, _, _, _. iPureIntro. simpl.
        eapply impure_step.
        * apply CmpXchgFailS. apply neq.
        * eapply MStepRMWFail; try done.
          + f_equiv. done.
          + intros ??? lookSome.
            rewrite drop_prefix_lookup_Some in lookSome.
            apply (safe (t' + (OCV !!0 ℓ))); last done.
            lia. }
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      * assert (h0 = hist) as ->.
        (* H8: store_drop_prefix OCV full_hist !! ℓ = Some h0 *)
        { rewrite store_drop_prefix_alt Hlook' /= in H8. simplify_eq. done. }
        iSplitR=>//.
        assert (ℓ ∈ dom full_hist) as elemOf.
        { by apply elem_of_dom_2 in Hlook'. }
        (* assert (hist = drop_prefix h (OCV !!0 ℓ)) as drop_eq. *)
        (* { rewrite store_drop_prefix_alt Hlook' /= in Hlook. *)
        (*   by simplify_eq. } *)
        iMod (fmapsto_heap_update with "Hσ ℓPts") as "[Hσ ℓPts]".
        (* iEval (rewrite <- drop_prefix_insert) in "ℓPts". *)
        (* iEval (rewrite <- drop_eq) in "ℓPts". *)
        assert (MV ⊑ max_view (store_drop_prefix OCV full_hist)) as incl2 by
          by eapply valid_heap_msg_lookup.
        iMod (gen_own_update with "store_view_at") as "[store_view_at mvView]".
        { apply auth_frac.auth_frac_update_core_id; last apply incl2. apply _. }
        iPoseProof (gen_own_op_2 with "Hval mvView") as "Hval".
        rewrite -auth_frag_op.
        iMod (auth_both_max_view_insert with "[$] [$]")
          as "[store_view_at Hval]"; [done|].
        (* rewrite -?(insert_store_drop_prefix _ _ _ h); try assumption. *)
        iDestruct ("HΦ" $! (t + (OCV !!0 ℓ)) with "[ℓPts $Hval]") as "$".
        { replace (t + (OCV !!0 ℓ) + 1) with (t + 1 + (OCV !!0 ℓ)) by lia.
          iSplit; first (iPureIntro; lia).
          iSplit; first rewrite -drop_prefix_lookup_Some //.
          iSplit; first rewrite -drop_prefix_lookup //.
          iLeft.
          iSplit; first done.
          iSplit; first done.
          iSplit.
          { iPureIntro.
            f_equiv; last done.
            f_equiv. lia. }
          done. }
        iModIntro.
        iFrame "extra".
        iExists _, _, _.
        iFrame "∗#".
        iSplit.
        { iPureIntro.
          simpl.
          erewrite <- insert_store_drop_prefix; done. }
        iSplit.
        { iPureIntro.
          simpl.
          (* erewrite insert_store_drop_prefix; try eassumption. *)
          apply hist_inv_insert_msg; try done.
          apply max_view_incl_insert; first done.
          apply view_lub_le; done. }
        iPureIntro.
        simpl.
        rewrite dom_insert_L.
        set_solver.
      * assert (h0 = hist) as ->.
        (* H11: store_drop_prefix OCV full_hist !! ℓ = Some h0 *)
        { rewrite store_drop_prefix_alt Hlook' /= in H11. simplify_eq. done. }
        iSplitR=>//.
        iMod (gen_own_update with "store_view_at") as "[store_view_at valid']".
        { apply (auth_update_dfrac_alloc _ _ (SV ⋅ MV)).
          rewrite -subseteq_view_incl.
          apply view_lub_le; first done.
          eapply message_included_in_max_view; done. }
        iFrame. iModIntro.
        iDestruct ("HΦ" with "[ℓPts $valid']") as "$".
        { replace (t + (OCV !!0 ℓ) + 1) with (t + 1 + (OCV !!0 ℓ)) by lia.
          iSplit; first (iPureIntro; lia).
          iSplit; first rewrite -drop_prefix_lookup_Some //.
          iSplit; first rewrite -drop_prefix_lookup //.
          iRight.
          by iFrame. }
        iExists OV.
        simpl.
        iFrame "#∗".
        done.
  Qed.
  
  (* Lemma valid_heap *)

  (* Lemma wp_faa  *)
  Lemma wp_faa_alt ℓ h (n : Z) SV FV BV OCV s E :
    ▷ ⌜ ∀ (t : nat) (msg : message),
      Nat.add (OCV !!0 ℓ) (SV !!0 ℓ) ≤ t → h !! t = Some msg → ∃ (n: Z), msg.(msg_val) = #n ⌝ -∗
    {{{ ℓ ↦fh h ∗ validV SV ∗ crashed_at_offset OCV }}}
      FAA #ℓ #n `at` (SV, FV, BV) @ s; E
    {{{ t (n__old: Z) SVm FVm _PVm SV3, RET #n__old `at` (SV3, FV, BV ⊔ FVm);
      ⌜ Nat.add (OCV !!0 ℓ) (SV !!0 ℓ) ≤ t ⌝ ∗
      validV SV3 ∗
      ⌜ h !! t = Some (Msg #n__old SVm FVm _PVm) ⌝ ∗
      ⌜ h !! (t + 1)%nat = None ⌝ ∗
      ⌜ SV3 = <[ ℓ := MaxNat (t - (OCV !!0 ℓ) + 1) ]>(SV ⊔ SVm) ⌝ ∗
      ℓ ↦fh <[ (t + 1) := Msg #(n__old + n) SV3 (FV ⊔ FVm) (FV ⊔ FVm) ]>h
    }}}.
  Proof.
    set hist := (drop_prefix h (OCV !!0 ℓ)).
    iIntros "#safe".
    iIntros "!>" (Φ) "(ℓPts & Hval & #offset) HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra] ?".
    iMod "safe" as "%safe".
    iModIntro.
    iNamed "interp".
    simpl in *.
    subst g.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iAssert (crashed_at_offset OCV0)%I as "crashed_at_offset"; first by iExists _.
    iDestruct (crashed_at_offset_agree with "offset crashed_at_offset") as %<-.
    iNamed "store_view_auth".
    iDestruct (gen_own_auth_frag_leq with "Hval store_view_at") as %Vincl.
    iDestruct (fmapsto_heap_valid with "Hσ ℓPts") as %Hlook'.
    iSplit.
    - rewrite /base_reducible.
      (* We need to show that there is _some_ message that the CmpXchg could
       * read. It could certainly read the most recent message. *)
      assert (store_drop_prefix OCV full_hist !! ℓ = Some hist) as Hlook.
      { rewrite store_drop_prefix_alt Hlook' /= //. }
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgSV msgP] Hmsgeq]; first done.
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      pose proof Hmsgeq as Hmsgeq'.
      rewrite drop_prefix_lookup_Some in Hmsgeq'.
      apply safe in Hmsgeq' as [? Heq].
      2: { rewrite comm. apply Nat.add_le_mono_r. f_equiv. done. }
      simpl in Heq. subst msgv.  
      iExists [], _, _, _, _. iPureIntro. simpl.
        eapply impure_step.
        + apply FaaS.
        + eapply (MStepRMW _ _ _ _ _ _ _ (max_view (store_drop_prefix OCV full_hist) !!0 ℓ)); try done.
          * f_equiv. done.
          * intros ??? lookSome.
            rewrite drop_prefix_lookup_Some in lookSome.
            by constructor.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step.
      assert (h0 = hist) as ->.
      (* H8: store_drop_prefix OCV full_hist !! ℓ = Some h0 *)
      { rewrite store_drop_prefix_alt Hlook' /= in H8. simplify_eq. done. }
      iSplitR=>//.
      assert (ℓ ∈ dom full_hist) as elemOf.
      { by apply elem_of_dom_2 in Hlook'. }
      (* assert (hist = drop_prefix h (OCV !!0 ℓ)) as drop_eq. *)
      (* { rewrite store_drop_prefix_alt Hlook' /= in Hlook. *)
      (*   by simplify_eq. } *)
      iMod (fmapsto_heap_update with "Hσ ℓPts") as "[Hσ ℓPts]".
      (* iEval (rewrite <- drop_prefix_insert) in "ℓPts". *)
      (* iEval (rewrite <- drop_eq) in "ℓPts". *)
      assert (MV ⊑ max_view (store_drop_prefix OCV full_hist)) as incl2 by
                                                                    by eapply valid_heap_msg_lookup.
      iMod (gen_own_update with "store_view_at") as "[store_view_at mvView]".
      { apply auth_frac.auth_frac_update_core_id; last apply incl2. apply _. }
      iPoseProof (gen_own_op_2 with "Hval mvView") as "Hval".
      rewrite -auth_frag_op.
      iMod (auth_both_max_view_insert with "[$] [$]")
        as "[store_view_at Hval]"; [done|].
      (* rewrite -?(insert_store_drop_prefix _ _ _ h); try assumption. *)
      iDestruct ("HΦ" $! (t + (OCV !!0 ℓ)) with "[ℓPts $Hval]") as "$".
      { replace (t + (OCV !!0 ℓ) + 1) with (t + 1 + (OCV !!0 ℓ)) by lia.
        iSplit; first (iPureIntro; lia).
        iSplit; first rewrite -drop_prefix_lookup_Some //.
        iSplit; first rewrite -drop_prefix_lookup //.
        iSplit.
        { iPureIntro.
          f_equiv; last done.
          f_equiv. lia. }
        done. }
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#".
      iSplit.
      { iPureIntro.
        simpl.
        erewrite <- insert_store_drop_prefix; done. }
      iSplit.
      { iPureIntro.
        simpl.
        (* erewrite insert_store_drop_prefix; try eassumption. *)
        apply hist_inv_insert_msg; try done.
        apply max_view_incl_insert; first done.
        apply view_lub_le; done. }
      iPureIntro.
      simpl.
      rewrite dom_insert_L.
      set_solver.
  Qed.
  
  Lemma wp_flush SV FV BV ℓ (hist : history) s E :
    {{{ ℓ ↦h hist }}}
      (Flush #ℓ) `at` (SV, FV, BV) @ s; E
                                          {{{ RET #() `at` (SV, FV, {[ℓ := MaxNat (SV !!0 ℓ)]} ⊔ BV); ℓ ↦h hist }}}.
  Proof.
    iIntros (Φ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? /= !>".
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (mapsto_heap_valid with "[$] Hσ pts") as %Hlook.
    iSplit.
    - rewrite /base_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      inv_impure_thread_step. iSplitR=>//.
      iDestruct ("HΦ" with "pts") as "$".
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#%". done.
  Qed.

  Lemma wp_flush_alt SV FV BV ℓ (hist : history) s E :
    {{{ ℓ ↦fh hist }}}
      (Flush #ℓ) `at` (SV, FV, BV) @ s; E
    {{{ RET #() `at` (SV, FV, {[ℓ := MaxNat (SV !!0 ℓ)]} ⊔ BV); ℓ ↦fh hist }}}.
  Proof.
    iIntros (Φ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? /= !>".
    iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (fmapsto_heap_valid with "[$] [$]") as %Hlook.
    iSplit.
    - rewrite /base_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      inv_impure_thread_step. iSplitR=>//.
      iDestruct ("HΦ" with "pts") as "$".
      iModIntro.
      iFrame "extra".
      iExists _, _, _.
      iFrame "∗#%". done.
  Qed.


  Lemma wp_fence SV FV BV s E :
    {{{ True }}}
      Fence `at` (SV, FV, BV) @ s; E
    {{{ RET #() `at` (SV, FV ⊔ BV, BV); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k). iNamed 1. iIntros "Ht /= !>".
    iSplit.
    - rewrite /base_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      inv_impure_thread_step. iSplitR=>//.
      iDestruct ("HΦ" with "[//]") as "$".
      done.
  Qed.

  Lemma wp_fence_sync SV FV BV s E :
    {{{ True }}}
      FenceSync `at` (SV, FV, BV) @ s; E
    {{{ RET #() `at` (SV, FV ⊔ BV, BV); persisted BV }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    (* iIntros ([??] [] ns mj D κ κs k). iNamed 1. iIntros "Ht /= !>". *)
    iIntros ([? PV] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    simpl in *.
    subst g.
    iIntros "? /= !>".
    iSplit.
    - rewrite /base_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      inv_impure_thread_step. iSplitR=>//.
      (* we first update the crash token *)
      iMod (token_strengthen_promise_0_deps _ _ (crashed_at_pred (OCV `view_add` (PV ⊔ BV))) with "crashed_at_tok")
        as "crashed_at_tok".
      { apply crashed_at_pred_strengthen.
        f_equiv.
        apply view_le_l. }
      { eexists.
        split; last by eexists.
        apply crashed_at_trans_cmra_morphism. }
      iPoseProof (token_to_rely with "crashed_at_tok") as "#rely_self".
      iPoseProof (rely_to_rely_self with "rely_self") as "#rely_self'".
      iAssert (crashed_at_offset OCV)%I as "#crashed_at_offset"; first by iExists _.
      iDestruct "pers" as "[pers_own #pers_rely]".
      (* we need to update crash promise here *)
      iMod (auth_auth_view_grow_op with "pers_own") as "[pers_own pers_lb]".
      iDestruct ("HΦ" with "[pers_lb]") as "$".
      { rewrite /persisted.
        iExists OCV, (map_imap (λ ℓ t, Some (MaxNat (max_nat_car t + (OCV !!0 ℓ)))) BV), (OCV `view_add` (PV ⊔ BV)).
        iFrame "∗#".
        rewrite /view_sub /view_add map_imap_compose /=.
        iSplit; iPureIntro.
        + apply map_eq => i.
          rewrite map_lookup_imap /=.
          destruct (BV !! i) as [[?] | ]; last done.
          simpl.
          rewrite Nat.add_sub //.
        + rewrite view_included => i.
          rewrite map_lookup_imap lookup_merge /lookup_zero lookup_op /=.
          set pv := (PV !! i).
          set bv := (BV !! i).
          destruct pv as [[?] | ] eqn:?;
            destruct bv as [[?] | ] eqn:?;
            destruct (OCV !! i) as [[?] | ] eqn:?;
            rewrite /from_option /numbers.max_nat_car /=;
            try (apply option_included; by left);
            apply Some_MaxNat_included;
            lia.
      }
      iFrame "extra".
      iMod (persisted_auth_auth_view_grow_incl with "pers_own"); last first.
      + iModIntro.
        iExists _, _, _.
        iFrame "∗#%".
        iSplit; first done.
        simpl.
        rewrite dom_op.
        iPureIntro. set_solver.
      + simpl.
        rewrite view_included => i.
        rewrite /lookup_zero ?lookup_op 2!lookup_merge lookup_op map_lookup_imap /=.
        set pv := (PV !! i).
        set bv := (BV !! i).
        destruct pv as [[?] | ] eqn:?;
          destruct bv as [[?] | ] eqn:?;
          destruct (OCV !! i) as [[?] | ] eqn:?;
          rewrite /from_option /numbers.max_nat_car /=;
          try (apply option_included; by left);
          apply Some_MaxNat_included;
          rewrite /numbers.max_nat_car /=;
          lia.
  Qed.

  Lemma thread_of_val_fold (v : val) TV :
    ThreadState v TV = thread_of_val (ThreadVal v TV).
  Proof. done. Qed.
  
  (* this lemma came from [wpc_proofmode.v] *)
  Lemma wpc_fork s E1 e TV (Φ: thread_val → iProp Σ) Φc :
    ▷ WPC (e `at` TV) @ s; ⊤ {{ _, True }} {{ True }} -∗
                         (Φc ∧ ▷ Φ (LitV LitUnit `at` TV)%TV) -∗
                         WPC (Fork e `at` TV) @ s; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros "He HΦ".
    iApply (wpc_lift_head_step s E1 Φ Φc (Fork e `at` TV)). { done. }
    iSplit; last first.
    {  iDestruct "HΦ" as "[HΦc _]". eauto. }
    iIntros (σ1 [] ns mj D κ κs n) "interp global".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first by set_solver+.
    iModIntro. iNext.
    iPureGoal.
    { econstructor. repeat eexists _. constructor. constructor. }
    iIntros (v2 σ2 g2 efs Hstep).
    iMod "Hclose".
    iMod (global_state_interp_le with "global") as "$".
    { apply crash_weakestpre.step_count_next_incr. }
    inv_thread_step.
    iModIntro. rewrite right_id.
    iFrame.
    rewrite thread_of_val_fold.
    iApply wpc_value'. by rewrite comm.
  Qed.
End lifting.

Section extra_state_interp.
  Context `{!nvmBaseGS Σ Ω, extra : !extraStateInterp Σ, !PerennialG Σ}.
  (* Context `{!nvmBaseFixedG Σ, nvmBaseDeltaG, extra : extraStateInterp Σ, Ω : gGenCmras Σ}. *)

  Lemma wp_extra_state_interp_fupd (e : expr) `{!AtomicBase StronglyAtomic e}
        TV s E (Φ : thread_val → iProp Σ) :
    to_val e = None →
    (* [e] does not fork threads. *)
    (∀ σ1 g1 κ e2 σ2 g2 efs, prim_step (e `at` TV) σ1 g1 κ e2 σ2 g2 efs → efs = []) →
    (let
      ex : extraStateInterp Σ := {| extra_state_interp := True |}
    in
      (@extra_state_interp _ extra) -∗
      WP (e `at` TV) @ s; E {{ v, Φ v ∗ |={E}=>(@extra_state_interp _ extra) }}) -∗
    WP e `at` TV @ s; E {{ Φ }}.
  Proof.
    iIntros (eq nofork) "H".

    rewrite !wp_eq /wp_def.
    rewrite !wpc_eq /wpc_def.
    setoid_rewrite wpc0_unfold. rewrite /wpc_pre.
    iIntros (?).
    iSplit; last first.
    { iIntros.
      iApply step_fupd_extra.step_fupd2N_inner_later; auto. iFrame "#". }

    rewrite /= /thread_to_val. rewrite eq /=.
    iIntros (???????) "[interp extra]". iIntros.
    iSpecialize ("H" with "extra").
    iDestruct ("H" $! mj) as "[H _]".
    iSpecialize ("H" $! _ g1 _ _ κ [] 0 with "[$interp //] [] [$]").
    { by iExistsN. }
    iMod "H".
    iModIntro.
    iApply (step_fupd_extra.step_fupd2N_wand with "H").
    iNext.
    iIntros "[$ A]".
    iIntros (???? step).

    iMod ("A" $! _ _ _ _ step) as "(A & Q & C & AB)".

    epose proof (atomic (a := StronglyAtomic) _ _ _ _ _ _ _ step) as [val toValE2].
    apply thread_of_to_val in toValE2.
    simpl.
    subst.

    iEval (rewrite right_id) in "A".
    iMod (wpc0_value_inv_option _ _ _ _ _ _ _ _ [] _ with "C Q")
      as "([Φ extra] & global)".
    simpl.
    iFrame.
    iMod "extra".
    iModIntro.
    simpl in *.

    apply nofork in step. subst.

    rewrite /= right_id.
    rewrite wpc0_unfold /wpc_pre.
    iDestruct "A" as "[$ ?]".
    iFrame.
    iSplit. { iIntros. iFrame. done. }
    iIntros.
    iApply step_fupd_extra.step_fupd2N_inner_later; first done; first done.
    iModIntro.
    iFrame.
    by iExistsN.
  Qed.

  Lemma wp_extra_state_interp (e : expr) `{!AtomicBase StronglyAtomic e}
        TV s E (Φ : thread_val → iProp Σ) :
    to_val e = None →
    (∀ σ1 g1 κ e2 σ2 g2 efs, prim_step (e `at` TV) σ1 g1 κ e2 σ2 g2 efs → efs = []) →
    (let
      ex : extraStateInterp Σ := {| extra_state_interp := True |}
    in
      (@extra_state_interp _ extra) -∗
      WP (e `at` TV) @ s; E {{ v, Φ v ∗ (@extra_state_interp _ extra) }}) -∗
    WP e `at` TV @ s; E {{ Φ }}.
  Proof.
    iIntros (eq nofork) "H".
    iApply wp_extra_state_interp_fupd; [done|done|].
    iIntros "I". iSpecialize ("H" with "I").
    iApply (wp_mono with "H").
    iIntros (?) "[$ $]". done.
  Qed.

  Lemma wp_extra_state_interp_inv (e : expr) `{!AtomicBase StronglyAtomic e}
        TV s E (Φ : thread_val → iProp Σ) :
    to_val e = None →
    (∀ σ1 g1 κ e2 σ2 g2 efs, prim_step (e `at` TV) σ1 g1 κ e2 σ2 g2 efs → efs = []) →
    WP e `at` TV @ s; E {{ Φ }} -∗
    (let
      ex : extraStateInterp Σ := {| extra_state_interp := True |}
    in
      (@extra_state_interp _ extra) -∗
      WP (e `at` TV) @ s; E {{ v, Φ v ∗ (@extra_state_interp _ extra) }}).
  Proof.
    iIntros (eq nofork) "H".

    rewrite !wp_eq /wp_def.
    rewrite !wpc_eq /wpc_def.
    setoid_rewrite wpc0_unfold. rewrite /wpc_pre.
    iIntros "extra" (?).
    iSplit; last first.
    { iIntros.
      iApply step_fupd_extra.step_fupd2N_inner_later; auto. iFrame "#". }

    rewrite /= /thread_to_val. rewrite eq /=.
    iIntros (???????) "[interp _]". iIntros.
    iDestruct ("H" $! mj) as "[H _]".
    iSpecialize ("H" with "[$interp $extra] [] [$]"). 
    { by iExistsN. }
    iMod "H".
    iModIntro.
    iApply (step_fupd_extra.step_fupd2N_wand with "H").
    iNext.
    iIntros "[$ A]".
    iIntros (???? step).

    iMod ("A" $! _ _ _ _ step) as "([interp extra] & Q & C & AB)".

    epose proof (atomic (a := StronglyAtomic) _ _ _ _ _ _ _ step) as [val toValE2].
    apply thread_of_to_val in toValE2.
    simpl.
    subst.

    (* iEval (rewrite right_id) in "A". *)
    iMod (wpc0_value_inv_option _ _ _ _ _ _ _ _ [] _ with "C Q")
      as "(Φ & global)".
    simpl.
    iFrame.
    iModIntro.
    simpl in *.

    apply nofork in step. subst.

    rewrite /= right_id.
    rewrite wpc0_unfold /wpc_pre.
    iFrame.
    iSplit. { iIntros. iFrame. done. }
    iIntros.
    iApply step_fupd_extra.step_fupd2N_inner_later; first done; first done.
    iModIntro.
    iFrame.
    by iExistsN.
    (* TODO: what? *)
    Unshelve.
    - refine 0.
    - refine ().
  Qed.
End extra_state_interp.
