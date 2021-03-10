From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.prelude Require Import options.

From self.lang Require Export syntax.
From self.lang Require Export memory.

(* nvm_lang.  A language with release/acquire weak memory and persistent
non-volatile memory. The language is adapted from HeapLang. *)

(* Scope delimiters like the ones that HeapLang has. *)
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module nvm_lang.

  (** Evaluation contexts *)
  Inductive ectx_item :=
    (* Functions and application. *)
    | AppLCtx (v2 : val)
    | AppRCtx (e1 : expr)
    (* Base types and their operations *)
    | UnOpCtx (op : un_op)
    | BinOpLCtx (op : bin_op) (v2 : val)
    | BinOpRCtx (op : bin_op) (e1 : expr)
    | IfCtx (e1 e2 : expr)
    (* Products *)
    | PairLCtx (v2 : val)
    | PairRCtx (e1 : expr)
    | FstCtx
    | SndCtx
    (* Sums *)
    | InjLCtx
    | InjRCtx
    | CaseCtx (e1 : expr) (e2 : expr)
    (* Memory operations. *)
    | AllocNLCtx (v2 : val)
    | AllocNRCtx (e1 : expr)
    | LoadCtx
    | LoadAcquireCtx
    | StoreLCtx (v2 : val)
    | StoreRCtx (e1 : expr)
    | StoreReleaseLCtx (v2 : val)
    | StoreReleaseRCtx (e1 : expr)
    (* RMW memory operations. *)
    | CmpXchgLCtx (v1 : val) (v2 : val)
    | CmpXchgMCtx (e0 : expr) (v2 : val)
    | CmpXchgRCtx (e0 : expr) (e1 : expr)
    | FaaLCtx (v2 : val)
    | FaaRCtx (e1 : expr).

  (* [fill_item] inserts an expression into an evaluation context item. *)
  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx v2 => App e (of_val v2)
    | AppRCtx e1 => App e1 e
    | UnOpCtx op => UnOp op e
    | BinOpLCtx op v2 => BinOp op e (Val v2)
    | BinOpRCtx op e1 => BinOp op e1 e
    | IfCtx e1 e2 => If e e1 e2
    | PairLCtx v2 => Pair e (Val v2)
    | PairRCtx e1 => Pair e1 e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | AllocNLCtx v2 => AllocN e (Val v2)
    | AllocNRCtx e1 => AllocN e1 e
    | LoadCtx => Load e
    | LoadAcquireCtx => LoadAcquire e
    | StoreLCtx v2 => Store e (Val v2)
    | StoreRCtx e1 => Store e1 e
    | StoreReleaseLCtx v2 => StoreRelease e (Val v2)
    | StoreReleaseRCtx e1 => StoreRelease e1 e
    | CmpXchgLCtx v1 v2 => CmpXchg e (Val v1) (Val v2)
    | CmpXchgMCtx e0 v2 => CmpXchg e0 e (Val v2)
    | CmpXchgRCtx e0 e1 => CmpXchg e0 e1 e
    | FaaLCtx v2 => FAA e (Val v2)
    | FaaRCtx e1 => FAA e1 e
    end.

  (** Substitution, replaces occurrences of [x] in [e] with [v]. *)
  Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
    match e with
    | Val _ => e
    | Var y => if decide (x = y) then Val v else Var y
    | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
    | App e1 e2 => App (subst x v e1) (subst x v e2)
    | UnOp op e => UnOp op (subst x v e)
    | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
    | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
    | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
    | Fst e => Fst (subst x v e)
    | Snd e => Snd (subst x v e)
    | InjL e => InjL (subst x v e)
    | InjR e => InjR (subst x v e)
    | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
    | Fork e => Fork (subst x v e)
    | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
    | Load e => Load (subst x v e)
    | LoadAcquire e => LoadAcquire (subst x v e)
    | Store e1 e2 => Store (subst x v e1) (subst x v e2)
    | StoreRelease e1 e2 => StoreRelease (subst x v e1) (subst x v e2)
    | WB e => WB (subst x v e)
    | Fence => Fence
    | FenceSync => FenceSync
    | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
    | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
    | NewProph => NewProph
    | Resolve ex e1 e2 => Resolve (subst x v ex) (subst x v e1) (subst x v e2)
    end.

  Definition subst' (mx : binder) (v : val) : expr → expr :=
    match mx with BNamed x => subst x v | BAnon => id end.

  (* Steps. *)

  Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

  Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option literal :=
    match op with
    | PlusOp => Some $ LitInt (n1 + n2)
    | MinusOp => Some $ LitInt (n1 - n2)
    | MultOp => Some $ LitInt (n1 * n2)
    | QuotOp => Some $ LitInt (n1 `quot` n2)
    | RemOp => Some $ LitInt (n1 `rem` n2)
    | AndOp => Some $ LitInt (Z.land n1 n2)
    | OrOp => Some $ LitInt (Z.lor n1 n2)
    | XorOp => Some $ LitInt (Z.lxor n1 n2)
    | ShiftLOp => Some $ LitInt (n1 ≪ n2)
    | ShiftROp => Some $ LitInt (n1 ≫ n2)
    | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
    | LtOp => Some $ LitBool (bool_decide (n1 < n2))
    | EqOp => Some $ LitBool (bool_decide (n1 = n2))
    | OffsetOp => None (* Pointer arithmetic *)
    end%Z.

  Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option literal :=
    match op with
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
    | AndOp => Some (LitBool (b1 && b2))
    | OrOp => Some (LitBool (b1 || b2))
    | XorOp => Some (LitBool (xorb b1 b2))
    | ShiftLOp | ShiftROp => None (* Shifts *)
    | LeOp | LtOp => None (* InEquality *)
    | EqOp => Some (LitBool (bool_decide (b1 = b2)))
    | OffsetOp => None (* Pointer arithmetic *)
    end.

  Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : literal) : option literal :=
    match op, v2 with
    | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
    | _, _ => None
    end.

  Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
    if decide (op = EqOp) then
      if decide (vals_compare_safe v1 v2) then
        Some $ LitV $ LitBool $ bool_decide (v1 = v2)
      else
        None
    else
      match v1, v2 with
      | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
      | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
      | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
      | _, _ => None
      end.

  Inductive head_step : expr → option mem_event → list observation → expr → list expr → Prop :=
  (* Pure. *)
   RecS f x e :
     head_step (Rec f x e) None [] (Val $ RecV f x e) []
  | PairS v1 v2 :
     head_step (Pair (Val v1) (Val v2)) None [] (Val $ PairV v1 v2) []
  | InjLS v :
     head_step (InjL $ Val v) None [] (Val $ InjLV v) []
  | InjRS v :
     head_step (InjR $ Val v) None [] (Val $ InjRV v) []
  | BetaS f x e1 v2 e' :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) None [] e' []
  | UnOpS op v v' :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) None [] (Val v') []
  | BinOpS op v1 v2 v' :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) None [] (Val v') []
  | IfTrueS e1 e2 :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) None [] e1 []
  | IfFalseS e1 e2 :
     head_step (If (Val $ LitV $ LitBool false) e1 e2) None [] e2 []
  | FstS v1 v2 :
     head_step (Fst (Val $ PairV v1 v2)) None [] (Val v1) []
  | SndS v1 v2 :
     head_step (Snd (Val $ PairV v1 v2)) None [] (Val v2) []
  | CaseLS v e1 e2 :
     head_step (Case (Val $ InjLV v) e1 e2) None [] (App e1 (Val v)) []
  | CaseRS v e1 e2 :
     head_step (Case (Val $ InjRV v) e1 e2) None [] (App e2 (Val v)) []
  (* Concurrency. *)
  | ForkS e :
     head_step (Fork e) None [] (Val $ LitV LitUnit) [e]
  (* Memory. *)
  | AllocNS (n : Z) v ℓ :
     (0 < n)%Z →
     (* (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (ℓ + i) = None) → *)
     head_step (AllocN (Val $ LitV $ LitInt n) (Val v))
               (Some $ MEvAllocN ℓ (Z.to_nat n) v)
               []
               (Val $ LitV $ LitLoc ℓ)
               []
  | LoadS ℓ v :
     head_step (Load (Val $ LitV $ LitLoc ℓ))
               (Some $ MEvLoad ℓ v)
               []
               (of_val v)
               []
  | StoreS ℓ v :
     head_step (Store (Val $ LitV $ LitLoc ℓ) (Val v))
               (Some $ MEvStore ℓ v)
               []
               (Val $ LitV LitUnit)
               []
  | WBS ℓ :
     head_step (WB (Val $ LitV $ LitLoc ℓ))
               (Some $ MEvWB ℓ)
               []
               (Val $ LitV LitUnit)
               []
  | FenceS : head_step Fence
               (Some $ MEvFence)
               []
               (Val $ LitV LitUnit)
               []
  | FenceSyncS : head_step Fence
               (Some $ MEvFenceSync)
               []
               (Val $ LitV LitUnit)
               []
  | CmpXchgSuccS ℓ v1 v2 vl :
    (* FIXME: We probably need to check that _all_ the possible things we
    could've read here are safe to compare with. Let's see when that becomes a
    problem :). Note: Do this in the memory transition probably. Also, figure
    out why that neccessary. *)
     vals_compare_safe vl v1 →
     (vl = v1) →
     head_step (CmpXchg (Val $ LitV $ LitLoc ℓ) (Val v1) (Val v2))
               (Some $ MEvRMW ℓ vl v2)
               []
               (Val $ PairV vl (LitV $ LitBool true))
               []
  | CmpXchgFailS ℓ v1 v2 vl :
     vals_compare_safe vl v1 →
     (vl ≠ v1) →
     head_step (CmpXchg (Val $ LitV $ LitLoc ℓ) (Val v1) (Val v2))
               (Some $ MEvLoadAcquire ℓ vl) (* FIXME: This is not enough per the above comment, probably need separate event. *)
               []
               (Val $ PairV vl (LitV $ LitBool false))
               []
  | FaaS ℓ (i1 i2 : Z) :
     head_step (FAA (Val $ LitV $ LitLoc ℓ) (Val $ LitV $ LitInt i2))
               (Some $ MEvRMW ℓ (LitV $ LitInt i1) (LitV $ LitInt $ i1 + i2)%Z)
               []
               (Val $ LitV $ LitInt i1)
               []
  (* Propechy. *)
  (* | NewProphS σ p :
     p ∉ σ.(used_proph_id) →
     head_step NewProph σ
               []
               (Val $ LitV $ LitProphecy p) (state_upd_used_proph_id ({[ p ]} ∪.) σ)
               [] *)
  (* | ResolveS p v e σ w σ' κs ts :
     head_step e σ κs (Val v) σ' ts →
     head_step (Resolve e (Val $ LitV $ LitProphecy p) (Val w)) σ
               (κs ++ [(p, (v, w))]) (Val v) σ' ts *).

  (** Basic properties about the language *)
  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

  (* If an expression [e] can take a step then it is not a value. *)
  Lemma val_head_stuck e mev κ e' efs : head_step e mev κ e' efs → to_val e = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e ev κ e2 efs :
    head_step (fill_item Ki e) ev κ e2 efs → is_Some (to_val e).
  Proof. revert κ e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    revert Ki2. induction Ki1; intros Ki2; induction Ki2; try naive_solver eauto with f_equal.
  Qed.

  (* We synchronize the memory model with the stepping relation for expressions
  and arrive at a semantics in the form that Iris requires. *)

  (* In [EctxLanguage] each thread is represented by an "expression". However,
  for our langauge the state of each thread consists of more than just an
  expression. The definition below is will serve as the "expressions" in our
  language definition, even though it really isnt' an expression. This requires
  us to define a few things that feels a bit weird (substition, conversion to
  val, etc.). *)
  Record thread_state : Type :=
    ThreadState { ts_expr : expr; ts_view : thread_view }.
  Record thread_val : Type :=
    ThreadVal { val_val : val; val_view : thread_view }.
  (* Definition ectx_item := nvm_lang.ectx_item. *)
  Definition thread_fill_item (Ki : ectx_item) (e : thread_state) : thread_state :=
    ThreadState (fill_item Ki e.(ts_expr)) e.(ts_view).
  Definition thread_of_val (v : thread_val) : thread_state :=
    ThreadState (of_val v.(val_val)) v.(val_view).
  Definition thread_to_val (e : thread_state) : option thread_val :=
    (λ v, ThreadVal v e.(ts_view)) <$> to_val e.(ts_expr).

  Definition thread_subst x es (e : thread_state) : thread_state :=
    ThreadState (subst x es e.(ts_expr)) (ts_view e).

  Inductive thread_step :
    thread_state → mem_config → list observation →
    thread_state → mem_config → list thread_state → Prop :=
  | pure_step e V σ e' efs :
      head_step e None [] e' (ts_expr <$> efs) →
      (* Forall (eq V) (ts_view <$> efs) → *) (* FIXME: Is this really needed? *)
      thread_step (ThreadState e V) σ [] (ThreadState e' V) σ efs
  | impure_step e V σ evt e' V' σ' :
      head_step e (Some evt) [] e' [] →
      mem_step σ V evt σ' V' →
      thread_step (ThreadState e V) σ [] (ThreadState e' V') σ' [].
  Arguments thread_step _%E _ _ _%E _ _%E.

  (* Lemma head_step_view_sqsubseteq e V σ κs e' V' σ' ef P B P' B'
    (step : head_step (ThreadState e (ThreadView V P B)) σ κs (ThreadState e' (ThreadView V' P' B')) σ' ef) :
    V ⊑ V'.
  Proof.
    inversion step; first done. subst.
    match goal with H : mem_step _ _ _ _ _ |- _ => destruct H; try solve_lat end.
    intros ℓ'. case (decide (ℓ = ℓ')) => [ <- | ? ] ;
      [ rewrite lookup_insert | by rewrite lookup_insert_ne ].
    by subst.
  Qed. *)

  (** Some properties of the language. **)

  Lemma thread_to_of_val v : thread_to_val (thread_of_val v) = Some v.
  Proof. by destruct v. Qed.

  Lemma thread_of_to_val e v : thread_to_val e = Some v → thread_of_val v = e.
  Proof. by destruct e as [[] ?]=>// [= <-] //. Qed.

  Instance thread_of_val_inj : Inj (=) (=) thread_of_val.
  Proof. by intros [][][=-> ->]. Qed.

  Instance thread_fill_item_inj Ki : Inj (=) (=) (thread_fill_item Ki).
  Proof. by intros [][][= ->%fill_item_inj ->]. Qed.

  Lemma thread_fill_item_val Ki e :
    is_Some (thread_to_val (thread_fill_item Ki e)) → is_Some (thread_to_val e).
  Proof. move/fmap_is_Some/fill_item_val => H. exact/fmap_is_Some. Qed.

  Lemma thread_val_stuck σ1 e1 κs σ2 e2 ef :
    thread_step e1 σ1 κs e2 σ2 ef → thread_to_val e1 = None.
  Proof.
    inversion 1 as [????? Hstep|??????? Hstep]; inversion Hstep; done.
  Qed.

  Lemma thread_head_ctx_step_val Ki e σ κs e2 σ2 ef :
    thread_step (thread_fill_item Ki e) σ κs e2 σ2 ef → is_Some (thread_to_val e).
  Proof.
    inversion 1; subst; apply fmap_is_Some; exact: nvm_lang.head_ctx_step_val.
  Qed.

  Lemma thread_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    thread_to_val e1 = None → thread_to_val e2 = None → thread_fill_item Ki1 e1 = thread_fill_item Ki2 e2
    → Ki1 = Ki2.
  Proof.
    move => /fmap_None H1 /fmap_None H2 [] H3 ?.
    exact: fill_item_no_val_inj _ _ H3.
  Qed.

  Lemma nvm_lang_mixin :
    EctxiLanguageMixin thread_of_val thread_to_val thread_fill_item thread_step.
  Proof.
    split; eauto using thread_to_of_val, thread_of_to_val, thread_val_stuck, thread_fill_item_val,
      thread_fill_item_no_val_inj, thread_head_ctx_step_val with typeclass_instances.
  Qed.

End nvm_lang.

Canonical Structure nvm_ectxi_lang := EctxiLanguage nvm_lang.nvm_lang_mixin.
Canonical Structure nvm_ectx_lang := EctxLanguageOfEctxi nvm_ectxi_lang.
Canonical Structure nvm_lang := LanguageOfEctx nvm_ectx_lang.

Export nvm_lang.
