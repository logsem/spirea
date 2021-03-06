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

  Lemma wp_alloc_at_view_lang v T (hist : (@history val)) s E :
    {{{ True }}}
      (ThreadState (ref v) T) @ s; E
    {{{ ℓ, RET (mkVal #ℓ T); ℓ ↦h {[ 0 := mk_message v T ]} }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_lift_atomic_head_step_no_fork (_)); first done.
    iIntros (σ1 κ κs k) "[Hσst Hσse] !>"; iSplit.
    - (* We must show that [ref v] is can take tome step. *)
       rewrite /head_reducible.
       iExists [], _, _, _. simpl. iPureIntro.
       eapply impure_step.
       * constructor. done.
       * destruct σ1, T.
         apply MStepAllocN. constructor.
       (* iExists _, _, _, _. *)
       auto with lia head_step.
  Qed.


End lifting.