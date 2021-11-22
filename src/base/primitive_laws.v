From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap. (* proph_map. *)

From Perennial.program_logic Require Import ectx_lifting.
From Perennial.program_logic Require Export ectx_language weakestpre lifting.

From iris.algebra Require Import auth gmap numbers.
From iris_named_props Require Import named_props.
From iris.prelude Require Import options.

From self Require Import extra ipm_tactics.
From self Require Import cred_frag.
From self.algebra Require Import view.
From self.lang Require Export notation tactics.

Definition view_preG Σ := inG Σ (authR viewUR).

(* The functors that are unchanged after a crash. *)
Class nvmBaseFixedG Σ := {
  nvmBaseG_invGS : invGS Σ;                            (* For invariants. *)
  nvmBaseG_gen_heapGS :> gen_heapGpreS loc history Σ;  (* For the heap. *)
  view_inG :> inG Σ (authR viewUR);                    (* For views. *)
  crashed_at_inG :> inG Σ (agreeR viewO);              (* For crashed at knowledge. *)
  nvm_base_creditG :> creditGS Σ;
}.

(** Names for the heap that needs to change after a crash. *)
Record nvm_heap_names := {
  name_gen_heap : gname;
  name_gen_meta : gname;
}.

(** A record of all the ghost names useb by [nvmBaseG] that needs to change
after a crash. *)
Class nvm_base_names := {
  heap_names_name : nvm_heap_names;  (* Names used by [gen_heap]. *)
  store_view_name : gname;           (* Name used by the store view. *)
  persist_view_name : gname;         (* Name used by the persist view. *)
  crashed_at_view_name : gname;      (* Name used by the crashed at view. *)
}.

(* Things that change upon a crash. We would have like to _only_ have ghost
names in this record, but due to how Perennial works we need to keep the entire
[crashGS] in it. *)
Class nvmBaseDeltaG Σ := MkNvmBaseDeltaG {
  nvm_base_crashGS :> crashGS Σ;
  nvm_base_names' :> nvm_base_names;
}.

(* All the functors that we need for the base logic (and not ghost names). *)
Class nvmBaseGpreS Σ := NvmBasePreG {
  nvmBase_preG_iris :> invGpreS Σ;
  nvmBase_preG_gen_heapGS :> gen_heapGpreS loc history Σ;
  nvmBase_preG_crash :> crashGpreS Σ;
  nvmBase_preG_view_inG : view_preG Σ;
  nvmBase_preG_crashed_at :> inG Σ (agreeR viewO);
  nvmBase_preG_credit :> credit_preG Σ;
}.

Definition nvm_base_delta_update_names {Σ}
           (hGD : nvmBaseDeltaG Σ) (names : nvm_base_names) :=
  {| nvm_base_crashGS := nvm_base_crashGS;
     nvm_base_names' := names |}.

(* When we have an [nvmBaseG] instance we can stich together a [gen_heapGS]
instance. We need this instance b.c. we store functors and the ghost names in
separate records (for the post crash modality) and this means that we need this
to construct the [gen_heapGS] record that mixes these things together. *)
Instance nvm_baseG_to_heapG `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ} :
    gen_heapGS loc _ Σ := {|
  gen_heap_inG := _;
  gen_heap_name := name_gen_heap (heap_names_name);
  gen_meta_name := name_gen_meta (heap_names_name);
|}.

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

(* The state interpretation for the base logic. *)
Definition nvm_heap_ctx `{hG : !nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ} σ : iProp Σ :=
  "Hσ" ∷ gen_heap_interp σ.1 ∗ (* The interpretation of the heap. This is standard,
  except the heap store historie and not plain values. *)
  "lubauth" ∷ own store_view_name (● (max_view σ.1)) ∗
  "%Hop" ∷ ⌜valid_heap σ.1⌝ ∗
  "Hpers" ∷ own persist_view_name (● σ.2) ∗
  "crash" ∷ (∃ (CV : view),
    "%cvSubset" ∷ ⌜dom (gset _) CV ⊆ dom _ σ.1⌝ ∗
    "#crashedAt" ∷ own crashed_at_view_name (to_agree CV : agreeR viewO)).

Definition borrowN := nroot .@ "borrow".
Definition crash_borrow_ginv_number : nat := 6%nat.
Definition crash_borrow_ginv `{!invGS Σ} `{creditGS Σ}
  := (inv borrowN (cred_frag crash_borrow_ginv_number)).

Class extraStateInterp Σ := {
  extra_state_interp : iProp Σ;
}.

Global Program Instance nvmBaseG_irisGS `{!nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ, extraStateInterp Σ} :
  irisGS nvm_lang Σ := {
  iris_invGS := nvmBaseG_invGS;
  iris_crashGS := nvm_base_crashGS;
  state_interp σ _nt := (nvm_heap_ctx σ ∗ extra_state_interp)%I;
  global_state_interp g ns mj D _ :=
    (@crash_borrow_ginv _ nvmBaseG_invGS _ ∗
     cred_interp ns ∗
     ⌜(/ 2 < mj ≤ 1) ⌝%Qp ∗
     pinv_tok mj D)%I;
  fork_post _ := True%I;
  num_laters_per_step := (λ n, 3 ^ (n + 1))%nat; (* This is the choice GooseLang takes. *)
  step_count_next := (λ n, 10 * (n + 1))%nat;
}.

Next Obligation.
  intros (**). iIntros "($ & ? & $)".
  by iMod (cred_interp_incr with "[$]") as "($ & _)".
Qed.
Next Obligation. intros => //=. lia. Qed.

(* NOTE: Uncomment as needed. *)
Notation "l ↦h{ dq } v" := (mapsto (L:=loc) (V:=history) l dq (v%V))
  (at level 20, format "l  ↦h{ dq }  v") : bi_scope.
Notation "l ↦h□ v" := (mapsto (L:=loc) (V:=history) l DfracDiscarded (v%V))
  (at level 20, format "l  ↦h□  v") : bi_scope.
Notation "l ↦h{# q } v" := (mapsto (L:=loc) (V:=history) l (DfracOwn q) (v%V))
  (at level 20, format "l  ↦h{# q }  v") : bi_scope.
Notation "l ↦h v" := (mapsto (L:=loc) (V:=history) l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦h  v") : bi_scope.

Section view_ra_rules.
  (** Rules for view RA. ***)
  Context `{inG Σ (authR viewUR)}.

  Lemma view_valid (V : view) : ✓ V.
  Proof. intros ?. case (_ !! _); done. Qed.

  Lemma auth_auth_view_grow_op γ V V' :
    ⊢ own γ (● V) ==∗ own γ (● (V ⋅ V')) ∗ own γ (◯ V').
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
    iIntros (incl) "H".
    iMod (own_update with "H") as "$"; last done.
    apply auth_auth_grow. - apply view_valid. - done.
  Qed.
End view_ra_rules.

(* Expresses that the view [V] is valid. This means that it is included in the
lub view. *)
Definition validV `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ} (V : view) : iProp Σ :=
  own store_view_name (◯ V).

(* Expresses that the view [V] is persisted. This means that it is included in
the global persisted view. *)
Definition persisted `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ} (V : view) : iProp Σ :=
  own persist_view_name (◯ V).

Definition persisted_loc `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ}
           ℓ t : iProp Σ :=
  persisted {[ ℓ := MaxNat t ]}.

(* Expresses that the view [rv] was recovered after the last crash. *)
Definition crashed_at {Σ} `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ}
           (CV : view) : iProp Σ :=
  own crashed_at_view_name (to_agree CV).

Section crashed_at.
  Context `{nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ}.

  Lemma crashed_at_agree CV CV' :
    crashed_at CV -∗ crashed_at CV' -∗ ⌜CV = CV'⌝.
  Proof.
    iIntros "A B".
    by iDestruct (own_valid_2 with "A B") as %HV%to_agree_op_inv_L.
  Qed.

End crashed_at.

(** * Lemmas about [max_view] *)
Section max_view.
  Context `{!nvmBaseFixedG Σ, hGD : nvmBaseDeltaG Σ}.
  Implicit Types hist : history.
  Implicit Types ℓ : loc.

  Lemma valid_heap_lookup heap ℓ hist :
    valid_heap heap → heap !! ℓ = Some hist → is_Some (hist !! 0).
  Proof.
    intros val ?. eapply map_Forall_lookup_1 in val; last done. apply val.
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
    * subst. rewrite !lookup_insert. simpl.
      apply Some_included_2.
      apply max_nat_included. simpl.
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

  Lemma max_view_included_union σ σ' : σ ##ₘ σ' → max_view σ ⊑ max_view (σ ∪ σ').
  Proof.
    intros disj.
    rewrite -max_view_union; last done.
    apply view_le_l.
  Qed.

  (* Lemma max_view_insert V (ℓ : loc) (t : time) (msg : message) (hist : history) (heap : store) : *)
  (*   (V !!0 ℓ) < t → *)
  (*   heap !! ℓ = Some hist → *)
  (*   max_view (<[ℓ := (<[t := msg]> hist)]> heap) = <[ℓ := MaxNat t]>(max_view heap). *)
  (* Proof. Abort. *)

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
    * subst. rewrite lookup_insert. rewrite look. simpl.
      apply Some_included_2.
      apply max_nat_included. simpl.
      apply max_msg_le_insert.
    * rewrite lookup_insert_ne; done.
  Qed.

  (***** Lemmas about ownership over [max_view]. *)

  Lemma max_view_lookup_insert ℓ t msg hist (heap : store) :
    ∃ t', max_view (<[ℓ := <[t := msg]> hist]> heap) !! ℓ = Some (MaxNat t') ∧ t ≤ t'.
  Proof.
    rewrite /max_view.
    rewrite fmap_insert.
    rewrite lookup_fmap.
    rewrite lookup_insert.
    eexists _.
    simpl.
    split; first reflexivity.
    rewrite /max_msg.
    rewrite dom_insert.
    apply max_list_elem_of_le.
    apply elem_of_elements.
    set_solver.
  Qed.

  Lemma auth_max_view_insert ℓ t (heap : store) (hist : history) msg :
    heap !! ℓ = Some hist →
    (* (V !!0 ℓ) < t → *)
    own store_view_name (● max_view heap) ==∗
    own store_view_name (● max_view (<[ℓ := <[t := msg]> hist]> heap)) ∗
    own store_view_name (◯ {[ ℓ := MaxNat t ]}).
  Proof.
    iIntros (look) "Olub".
    pose proof (max_view_insert_incl ℓ t msg hist heap look) as incl.
    iMod (auth_auth_view_grow_incl _ _ _ incl with "Olub") as "Olub".
    iMod (own_update with "Olub") as "[$ $]".
    { apply: auth_update_dfrac_alloc.
      apply singleton_included_l.
      epose proof (max_view_lookup_insert _ _ _ _ _) as (y & look' & le).
      exists (MaxNat y).
      erewrite look'.
      split; first done.
      apply Some_included_2.
      apply max_nat_included. simpl.
      apply le. }
    done.
  Qed.

End max_view.

Section persisted.
  Context `{!nvmBaseFixedG Σ, nvmBaseDeltaG Σ}.

  Global Instance persisted_persistent PV : Persistent (persisted PV).
  Proof. apply _. Qed.

  Lemma persisted_auth_included dq PV PV' :
    own persist_view_name (●{dq} PV) -∗ persisted PV' -∗ ⌜PV' ⊑ PV⌝.
  Proof.
    iIntros "A B".
    by iDestruct (own_valid_2 with "A B")
      as %[_ [incl _]]%auth_both_dfrac_valid_discrete.
  Qed.

  Lemma persisted_weak PV PV' : PV' ≼ PV → persisted PV -∗ persisted PV'.
  Proof. rewrite /persisted. iIntros ([x ->]) "[$ _]". Qed.

  (* [persisted] is anti-monotone. *)
  Global Instance persisted_anti_mono : Proper ((⊑@{view}) ==> flip (⊢)) (persisted).
  Proof. intros ??. apply persisted_weak. Qed.

  Lemma persisted_persisted_loc PV ℓ t :
    PV !! ℓ = Some (MaxNat t) → persisted PV -∗ persisted_loc ℓ t.
  Proof.
    intros look.
    rewrite /persisted_loc /persisted.
    f_equiv.
    apply auth_frag_mono.
    apply singleton_included_l.
    eexists (MaxNat t).
    rewrite look.
    auto.
  Qed.

End persisted.

Section lifting.
  Context `{!nvmBaseFixedG Σ, nvmBaseDeltaG Σ, extra : !extraStateInterp Σ}.

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

  Lemma auth_frag_leq V W γ : ⊢ own γ (◯ V) -∗ own γ (● W) -∗ ⌜V ⊑ W⌝.
  Proof.
    iIntros "H1 H2".
    rewrite /validV.
    iDestruct (own_valid_2 with "H2 H1") as %[Hincl _]%auth_both_valid_discrete.
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

  Lemma store_view_alloc_big (σ σ' : (gmap loc history)) :
    σ' ##ₘ σ →
    own store_view_name (● (max_view (σ))) ==∗
    own store_view_name (● (max_view (σ' ∪ σ))).
  Proof.
    iIntros (disj) "H".
    iMod (auth_auth_view_grow_incl with "H") as "$"; last done.
    rewrite map_union_comm; last done.
    apply max_view_included_union. done.
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

  Lemma hist_inv_alloc ℓ P v0 n heap :
    heap_array ℓ P (replicate (Z.to_nat n) v0) ##ₘ heap →
    valid_heap heap →
    valid_heap (heap_array ℓ P (replicate (Z.to_nat n) v0) ∪ heap).
  Proof.
    rewrite /valid_heap /valid_heap_lub.
    intros disj val.
    apply map_Forall_union; first done. split.
    - intros ? ? (j & w & ? & Hjl & eq & mo)%heap_array_lookup.
      rewrite eq.
      split. { rewrite lookup_singleton. naive_solver. }
      apply map_Forall_singleton. simpl. apply view_empty_least.
    - eapply map_Forall_impl; first apply val.
      intros ℓ' hist [??].
      split; first done.
      eapply map_Forall_impl; first done.
      simpl. intros ???.
      rewrite -max_view_union; last done.
      etrans; first done.
      apply view_le_r.
  Qed.

  Ltac whack_global :=
    iMod (global_state_interp_le (Λ := nvm_lang) _ _ () _ _ _ with "[$]") as "$";
      first (simpl; lia).

  Lemma wp_fork s E (e : expr) TV (Φ : thread_val → iProp Σ) :
    ▷ WP (ThreadState e TV) @ s; ⊤ {{ _, True }} -∗
    ▷ Φ (ThreadVal (LitV LitUnit) TV) -∗
    WP ThreadState (Fork e) TV @ s; E {{ Φ }}.
  Proof.
    iIntros "He HΦ".
    iApply (wp_lift_atomic_head_step (Φ := Φ)); first done.
    iIntros (σ1 [] mj D ns κ κs n) "Hσ Hg !>".
    iPureGoal.
    { rewrite /head_reducible.
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

  Lemma wp_allocN v T n s E :
    (0 < n)%Z →
    {{{ True }}}
      (ThreadState (AllocN #n v) T) @ s; E
    {{{ ℓ CV, RET (ThreadVal #ℓ T);
      crashed_at CV ∗
      ([∗ list] i ∈ seq 0 (Z.to_nat n),
        (ℓ +ₗ (i : nat)) ↦h initial_history (flush_view T) v) ∗
      ([∗ list] i ∈ seq 0 (Z.to_nat n), (⌜ℓ +ₗ (i : nat) ∉ dom (gset _) CV⌝))
    }}}.
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>". iNamed "crash".
    iSplit.
    - (* We must show that [ref v] is can take some step. *)
       rewrite /head_reducible.
       destruct T as [[sv pv] bv].
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step.
       * constructor. done.
       * apply alloc_fresh. lia.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
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
      iMod (store_view_alloc_big with "lubauth") as "$".
      { apply Hdisj. }
      iModIntro.
      iPureGoal. { apply hist_inv_alloc; done. }
      (* rewrite left_id. *)
      iFrame.
      iDestruct ("HΦ" with "[Hl Hm]") as "$".
      { iFrame "crashedAt".
        iDestruct (heap_array_to_seq_mapsto with "Hl") as "$".
        iApply big_sepL_forall. iIntros (?? [hi ho]%lookup_seq) "!%".
        eapply not_elem_of_weaken; last done.
        apply not_elem_of_dom.
        apply H11; lia. }
      iExists CV.
      iFrame "crashedAt".
      iPureIntro. set_solver.
  Qed.

  Lemma wp_alloc s E v TV :
    {{{ True }}}
      ThreadState (Alloc (Val v)) TV @ s; E
    {{{ ℓ CV, RET (ThreadVal (LitV (LitLoc ℓ)) TV);
        crashed_at CV ∗ ⌜ℓ ∉ dom (gset _) CV⌝ ∗
        ℓ ↦h initial_history (flush_view TV) v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_allocN; [lia|auto|].
    iNext.
    iIntros (ℓ CV) "/= (? & hi & ho)". rewrite !right_id. rewrite loc_add_0.
    iApply "HΦ"; iFrame.
  Qed.

  (* Non-atomic load. *)
  Lemma wp_load (SV FV BV : view) ℓ q (hist : history) s E :
    {{{ ℓ ↦h{q} hist ∗ validV SV }}}
      (ThreadState (! #ℓ) (SV, FV, BV)) @ s; E
    {{{ t v msg, RET (ThreadVal v (SV, FV, BV));
        ℓ ↦h{q} hist ∗ ⌜hist !! t = Some msg ∧ msg.(msg_val) = v ∧ (SV !!0 ℓ) ≤ t⌝ }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>". iNamed "crash".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook) as [msg Hmsgeq]; first done.
      (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
      iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
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
      rewrite -lookup_fmap in H11.
      apply lookup_fmap_Some in H11.
      destruct H11 as [x [??]].
      iDestruct ("HΦ" with "[$ℓPts]") as "$"; first naive_solver.
      iModIntro.
      naive_solver.
  Qed.

  Lemma wp_load_acquire SV PV BV ℓ q (hist : history) s E :
    {{{ ℓ ↦h{q} hist ∗ validV SV }}}
      (ThreadState (!{acq} #ℓ) (SV, PV, BV)) @ s; E
    {{{ t v V' P' _P, RET (ThreadVal v (SV ⊔ V', PV, BV ⊔ P'));
        ⌜ (hist !! t) = Some (Msg v V' P' _P) ⌝ ∗
        ⌜ (SV !!0 ℓ) ≤ t ⌝ ∗
        validV (SV ⊔ V') ∗
        ℓ ↦h{q} hist }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>". iNamed "crash".
    (* The time at the view is smaller than the time in the lub view (which is
    the time of the most recent message *)
    iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the load can take some step. To do this we must use
      the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_valid _ _ _ Hlook)
        as [[msgv msgV msgP] Hmsgeq]; first done.
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
      iMod (own_update with "lubauth") as "[lubauth valid']".
      { apply (auth_update_dfrac_alloc _ _ (SV ⋅ MV)).
        rewrite -subseteq_view_incl.
        apply view_lub_le; first done.
        eapply message_included_in_max_view; done. }
      iFrame. iModIntro.
      iDestruct ("HΦ" $! t v MV MP _ with "[$ℓPts $valid' //]") as "$".
      naive_solver.
  Qed.

  Lemma wp_store v SV PV BV ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ validV SV }}}
      (ThreadState (#ℓ <- v) (SV, PV, BV)) @ s; E
    {{{ t, RET ThreadVal #() (<[ℓ := MaxNat t]>SV, PV, BV);
          ⌜hist !! t = None⌝ ∗
          ⌜(SV !!0 ℓ) < t⌝ ∗
          validV (<[ℓ := MaxNat t]>SV) ∗
          ℓ ↦h (<[t := Msg v ∅ ∅ PV]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>". iNamed "crash".
    (* The time at the view is smaller than the time in the lub view (which is
    the time of the most recent message *)
    iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the store can take some step. To do this we must use
         the points-to predicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
      iExists [], _, _, _, _. simpl. iPureIntro.
      eapply impure_step.
      * constructor.
      * econstructor.
        + done.
        + apply lookNone.
        + pose proof (view_lt_lt _ _ Vincl ℓ ℓ eq_refl). lia.
        + done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      (* The persist view didn't change. *)
      iFrame "Hpers". simpl.
      (* We update the heap with the new history at ℓ. *)
      iMod (gen_heap_update with "Hσ ℓPts") as "[Hσ ℓPts]".
      iFrame "Hσ".
      (* We must now update the authorative element for the max_view. *)
      iMod (auth_max_view_insert with "lubauth") as "[lubauth viewT]"; [done|].
      iFrame "lubauth".
      (* We now update the big op. *)
      iModIntro.
      iPureGoal.
      { apply hist_inv_insert_msg; try done. apply view_empty_least. }
      iCombine "Hval viewT" as "v".
      iDestruct ("HΦ" with "[$ℓPts v]") as "$".
      { rewrite -view_insert_op; last lia. rewrite H11. naive_solver. }
      iFrame. iExists _. iFrame "#". iPureIntro. set_solver.
  Qed.

  Lemma wp_store_release SV v FV BV ℓ (hist : history) s E :
    {{{ ℓ ↦h hist ∗ validV SV }}}
      (ThreadState (#ℓ <-{rel} v) (SV, FV, BV)) @ s; E
    {{{ t, RET ThreadVal #() (<[ℓ := MaxNat t]>SV, FV, BV);
          ⌜msg_val <$> (hist !! t) = None⌝ ∗
          ⌜(SV !!0 ℓ) < t⌝ ∗
          validV (<[ℓ := MaxNat t]>SV) ∗
          ℓ ↦h (<[t := Msg v (<[ℓ := MaxNat t]>SV) FV FV]>hist) }}}.
  Proof.
    iIntros (Φ) "[ℓPts Hval] HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? !>". iNamed "crash".
    (* The time at the view is smaller than the time in the lub view (which is the time of the most recent message *)
    iDestruct (auth_frag_leq with "Hval lubauth") as %Vincl.
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hσ ℓPts") as %Hlook.
    iSplit.
    - (* We must show that the store can take some step. To do this we must use
         the points-tostep_fupdN_freshredicate and fact that the view is valid. *)
      rewrite /head_reducible.
      (* We need to show that there is _some_ message that the load could read.
      It could certainly read the most recent message. *)
      pose proof (history_lookup_lub_succ _ _ _ Hlook) as lookNone.
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
      simpl in *. inv_impure_thread_step. iSplitR=>//.
      (* The persist view didn't change. *)
      iFrame "Hpers".
      (* We update the heap with the new history at ℓ. *)
      iMod (gen_heap_update with "Hσ ℓPts") as "[Hσ ℓPts]".
      iFrame "Hσ".
      (* We must now update the authorative element for the max_view. *)
      iMod (auth_max_view_insert with "lubauth") as "[lubauth viewT]"; [done|].
      iFrame "lubauth".
      (* We now update the big op. *)
      iPureGoal.
      { apply hist_inv_insert_msg; try done. apply max_view_incl_insert; done. }
      iCombine "Hval viewT" as "v".
      iDestruct ("HΦ" with "[$ℓPts v]") as "$".
      { rewrite -view_insert_op; last lia. rewrite H11. naive_solver. }
      iFrame. iExists _. iFrame "#". iPureIntro. set_solver.
  Qed.

  (* Lemma wp_cmpxch  *)

  (* Lemma wp_faa  *)

  Lemma wp_wb SV FV BV ℓ (hist : history) s E :
    {{{ ℓ ↦h hist }}}
      (ThreadState (WB #ℓ) (SV, FV, BV)) @ s; E
    {{{ RET ThreadVal #() (SV, FV, {[ℓ := MaxNat (SV !!0 ℓ)]} ⊔ BV); ℓ ↦h hist }}}.
  Proof.
    iIntros (Φ) "pts HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? /= !>". iNamed "crash".
    (* From the points-to predicate we know that [hist] is in the heap at ℓ. *)
    iDestruct (gen_heap_valid with "Hσ pts") as %Hlook.
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global.
      Unshelve. 2: { done. }
      inv_impure_thread_step. iSplitR=>//.
      iDestruct ("HΦ" with "pts") as "$".
      iModIntro. iFrame "∗%". naive_solver.
  Qed.

  Lemma wp_fence SV FV BV s E :
    {{{ True }}}
      (ThreadState Fence (SV, FV, BV)) @ s; E
    {{{ RET ThreadVal #() (SV, FV ⊔ BV, BV); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    iIntros ([??] [] ns mj D κ κs k). iNamed 1. iIntros "Ht /= !>".
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global. Unshelve. 2: { done. }
      inv_impure_thread_step. iSplitR=>//.
      iModIntro. iFrame "∗%". iApply "HΦ". done.
  Qed.

  Lemma wp_fence_sync SV FV BV s E :
    {{{ True }}}
      (ThreadState FenceSync (SV, FV, BV)) @ s; E
    {{{ RET ThreadVal #() (SV, FV ⊔ BV, BV); persisted BV }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (Φ := Φ)); first done.
    (* iIntros ([??] [] ns mj D κ κs k). iNamed 1. iIntros "Ht /= !>". *)
    iIntros ([??] [] ns mj D κ κs k) "[interp extra]". iNamed "interp".
    iIntros "? /= !>". iNamed "crash".
    iSplit.
    - rewrite /head_reducible.
       iExists [], _, _, _, _. simpl. iPureIntro.
       eapply impure_step; by econstructor; done.
    - iNext. iIntros (e2 σ2 [] efs Hstep).
      whack_global. Unshelve. 2: { done. }
      inv_impure_thread_step. iSplitR=>//.
      iMod (auth_auth_view_grow_op with "Hpers") as "[$ perB]".
      iModIntro. iFrame "∗%". iDestruct ("HΦ" with "perB") as "$". naive_solver.
  Qed.

End lifting.

From self.base Require Import class_instances.

Section extra_state_interp.

  Context `{!nvmBaseFixedG Σ, nvmBaseDeltaG Σ, extra : extraStateInterp Σ}.

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
      iApply step_fupd_extra.step_fupd2N_inner_later; auto. iNext. iFrame. }

    rewrite /= /thread_to_val. rewrite eq /=.
    iIntros (????????) "[interp extra]". iIntros.
    iSpecialize ("H" with "extra").
    iDestruct ("H" $! mj) as "[H _]".
    iSpecialize ("H" $! _ _ g1 _ _ κ [] 0 with "[$interp //] [$] [$]").

    iMod "H".
    iModIntro.
    iApply (step_fupd_extra.step_fupd2N_wand with "H").
    iNext.
    iIntros "[$ A]".
    iIntros (???? step).

    iMod ("A" $! _ _ _ _ step) as "(A & Q & C & D & AB)".

    epose proof (atomic (a := StronglyAtomic) _ _ _ _ _ _ _ step) as [val toValE2].
    apply thread_of_to_val in toValE2.
    simpl.
    subst.

    iEval (rewrite right_id) in "A".
    iMod (wpc0_value_inv_option _ _ _ _ _ _ _ _ _ _ [] _ with "C Q AB")
      as "([Φ extra] & B & V)".
    Unshelve. 2: { apply (). }
    simpl.
    iFrame.
    iMod "extra".
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

End extra_state_interp.
