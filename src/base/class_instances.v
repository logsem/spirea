(* This file add instances for the [Atomic] and the [PureExec] type classes.
These are used in the proof mode. *)

From Perennial.program_logic Require Export language.
From iris.prelude Require Import options.

From self.lang Require Export lang notation.
From self.base Require Import tactics.

(* [IntoVal] and [AsVal] for nvm_lang. *)
Global Instance into_val_ts v TV : IntoVal (ThreadState (Val v) TV) (ThreadVal v TV).
Proof. done. Qed.
Global Instance as_val_val_ts v TV : AsVal (ThreadState (Val v) TV).
Proof. by eexists (ThreadVal _ _). Qed.

(* [IntoVal] and [AsVal] for expr_lang. *)
Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by exists v. Qed.

(** * Instances of the [Atomic] class *)

Global Notation AtomicBase s e := (∀ TV, Atomic s (ThreadState e TV)).

Section atomic.
  Local Ltac solve_atomic :=
    intros tv;
    apply strongly_atomic_atomic;
    apply: ectx_language_atomic; [
      inversion 1; inv_head_step; rewrite /thread_to_val; naive_solver
    | apply: ectxi_language_sub_redexes_are_values; intros [] [] [=]; naive_solver
    ].

  Global Instance rec_atomic s f x e : AtomicBase s (Rec f x e).
  Proof. solve_atomic. Qed.
  Global Instance pair_atomic s v1 v2 : AtomicBase s (Pair (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance injl_atomic s v : AtomicBase s (InjL (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance injr_atomic s v : AtomicBase s (InjR (Val v)).
  Proof. solve_atomic. Qed.
  (** The instance below is a more general version of [Skip] *)
  Global Instance beta_atomic s f x v1 v2 : AtomicBase s (App (RecV f x (Val v1)) (Val v2)).
  Proof. destruct f, x; solve_atomic. Qed.
  Global Instance unop_atomic s op v : AtomicBase s (UnOp op (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance binop_atomic s op v1 v2 : AtomicBase s (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance if_true_atomic s v1 e2 :
    AtomicBase s (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. solve_atomic. Qed.
  Global Instance if_false_atomic s e1 v2 :
    AtomicBase s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance fst_atomic s v : AtomicBase s (Fst (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance snd_atomic s v : AtomicBase s (Snd (Val v)).
  Proof. solve_atomic. Qed.

  Global Instance fork_atomic s e : AtomicBase s (Fork e).
  Proof. solve_atomic. Qed.

  Global Instance alloc_atomic s v w : AtomicBase s (AllocN (Val v) (Val w)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic s v : AtomicBase s (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic s v1 v2 : AtomicBase s (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance cmpxchg_atomic s v0 v1 v2 : AtomicBase s (CmpXchg (Val v0) (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance faa_atomic s v1 v2 : AtomicBase s (FAA (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.

  (* Note: Uncomment if we need prophecy variables.

  Global Instance new_proph_atomic s : Atomic s NewProph.
  Proof. solve_atomic. Qed.
  Global Instance resolve_atomic s e v1 v2 :
    Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
  Proof.
    rename e into e1. intros H σ1 e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
    simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
    - subst. inversion_clear step. by eapply (H σ1 (Val _) _ σ2 efs), head_prim_step.
    - rewrite fill_app. rewrite fill_app in Hfill.
      assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
      { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
        apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step. }
      destruct K; (inversion Hfill; clear Hfill; subst; try
        match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
      refine (_ (H σ1 (fill (Ks ++ [_]) e2') _ σ2 efs _)).
      + destruct s; intro Hs; simpl in *.
        * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
        * apply irreducible_resolve. by rewrite fill_app in Hs.
      + econstructor; try done. simpl. by rewrite fill_app.
  Qed.
  *)
End atomic.

(** * Instances of the [PureExec] class

Note that these instances are for nvm_lang thread states in the "normal" WP. In
the proofmode these are then lifted to apply to expressions in our custom WP.
*)

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Global Notation PureExecBase P nsteps e1 e2 :=
  (∀ TV, PureExec P nsteps (ThreadState e1 TV) (ThreadState e2 TV)).

Section pure_exec.
  Local Ltac solve_exec_safe :=
    intros ? []; eexists _, _, _, _; simpl; apply pure_step with (efs := []); econstructor; eauto.
    (* intros; eexists _, _, _, _; apply pure_step with (efs := []); econstructor; eauto. *)
  Local Ltac solve_exec_puredet :=
    simpl; intros; inv_thread_step; repeat split_and; eauto using fmap_nil_inv.
    (* simpl; intros; inv_thread_step; eauto using fmap_nil_inv. *)
  Local Ltac solve_pure_exec :=
    subst; intros ??; apply nsteps_once, (pure_head_step_pure_step (ThreadState _ _));
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExecBase True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_pairc (v1 v2 : val) :
    PureExecBase True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed. (* solve_pure_exec. Qed. *)
  Global Instance pure_injlc (v : val) :
    PureExecBase True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExecBase True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExecBase True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExecBase (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExecBase (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Higher-priority instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExecBase (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros TV Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert TV Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExecBase True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExecBase True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExecBase True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExecBase True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExecBase True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExecBase True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.
End pure_exec.
