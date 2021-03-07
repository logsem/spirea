From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.heap_lang Require Export class_instances.
From iris.heap_lang Require Import tactics notation.
From iris.algebra Require Import auth gmap numbers.
From iris.prelude Require Import options.

From self.lang Require Import notation.

(* Resource algebra for views. *)
Definition viewUR := gmapUR loc max_natUR.

Definition view_to_ra (v : view) : viewUR := MaxNat <$> v.

Class nvmG Σ := NvmG {
  nvmG_invG : invG Σ;
  nvmG_gen_heapG :> gen_heapG loc (@history val) Σ;
  view_inG :> inG Σ (authR viewUR);
  (* heapG_inv_heapG :> inv_heapG loc (option val) Σ; *)
  nvmG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
  store_view_name : gname;
}.

Global Instance nvmG_irisG `{!nvmG Σ} : irisG nvm_lang Σ := {
  iris_invG := nvmG_invG;
  state_interp σ κs _ := (
    gen_heap_interp (fst σ) ∗
    ∃ W, own store_view_name (● (view_to_ra W))
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
Notation "l ↦h v" := (mapsto (L:=loc) (V:=(@history val)) l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦h  v") : bi_scope.

Section lifting.

  Context `{!nvmG Σ}.

  Definition valid (V : view) : iProp Σ := True%I.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ Ψ : val → iProp Σ.
  Implicit Types efs : list expr.
  (* Implicit Types σ : state. *)
  Implicit Types v : val.
  Implicit Types ℓ : loc.

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

  Lemma heap_array_to_seq_mapsto l (P : view) v (n : nat) :
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

  Lemma wp_allocN_at_view_lang v T (hist : (@history val)) n s E :
    (0 < n)%Z →
    {{{ True }}}
      (ThreadState (AllocN #n v) T) @ s; E
    {{{ ℓ, RET (mkVal #ℓ T); [∗ list] i ∈ seq 0 (Z.to_nat n), (ℓ +ₗ (i : nat)) ↦h initial_history T.(tv_persist_view) v }}}.
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros ([??] κ κs k) "[Hσ Hσse] !>"; iSplit.
    - (* We must show that [ref v] is can take tome step. *)
       rewrite /head_reducible.
       destruct T.
       iExists [], _, _, _. simpl. iPureIntro.
       eapply impure_step.
       * constructor. done.
       * apply alloc_fresh. lia.
    - iNext. iIntros (e2 σ2 efs Hstep).
      simpl in *. inv_thread_step. iSplitR=>//.
      (* We now update the [gen_heap] ghost state to include the allocated location. *)
      iMod (gen_heap_alloc_big _ (heap_array ℓ _ (replicate (Z.to_nat n) v0)) with "Hσ")
        as "(Hσ & Hl & Hm)".
      { apply heap_array_map_disjoint.
        rewrite replicate_length Z2Nat.id; auto with lia. }
      iModIntro.
      iFrame "Hσse Hσ". iApply "HΦ".
      iApply heap_array_to_seq_mapsto.
      iFrame.
  Qed.

End lifting.