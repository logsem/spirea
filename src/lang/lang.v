(* We define the syntax and operational semantics of NvmLang. A language with
 release/acquire weak memory and non-volatile memory.

 The language is adapted from HeapLang and is identical to it in all aspects
 except for those related to the memory model. *)

From stdpp Require Import binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.

From self.lang Require Export memory.

From Perennial.program_logic Require Export language ectx_language ectxi_language.
From Perennial.program_logic Require Export crash_lang.

From self.lang Require Export syntax.

Module nvm_lang.

  (** Evaluation context items. *)
  Inductive ectx_item :=
    (* Functions and application. *)
    | AppLCtx (v2 : val)
    | AppRCtx (e1 : expr)
    (* Base types and their operations *)
    | UnOpCtx (op : un_op)
    | BinOpLCtx (op : bin_op) (v2 : val)
    | BinOpRCtx (op : bin_op) (e1 : expr)
    | IfCtx (e1 e2 : expr)
    (* Products. *)
    | PairLCtx (v2 : val)
    | PairRCtx (e1 : expr)
    | FstCtx
    | SndCtx
    (* Sums. *)
    | InjLCtx
    | InjRCtx
    | CaseCtx (e1 : expr) (e2 : expr)
    (* Memory operations. *)
    | AllocNLCtx (a : memory_access) (v2 : val)
    | AllocNRCtx (a : memory_access) (e1 : expr)
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
    | AllocNLCtx a v2 => AllocN a e (Val v2)
    | AllocNRCtx a e1 => AllocN a e1 e
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
    | AllocN a e1 e2 => AllocN a (subst x v e1) (subst x v e2)
    | Load e => Load (subst x v e)
    | LoadAcquire e => LoadAcquire (subst x v e)
    | Store e1 e2 => Store (subst x v e1) (subst x v e2)
    | StoreRelease e1 e2 => StoreRelease (subst x v e1) (subst x v e2)
    | Flush e => Flush (subst x v e)
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

  (* We define a labeled per-thread reduction. This will be synchronized later
  with the memory model to derive a unlabeled reductions (which is what Iris
  expects). *)
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
  | AllocNS a (n : Z) v ℓ :
     (0 < n)%Z →
     (* (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (ℓ + i) = None) → *)
     head_step (AllocN a (Val $ LitV $ LitInt n) (Val v))
               (Some $ MEvAllocN a ℓ (Z.to_nat n) v)
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
  | LoadAcquireS ℓ v :
     head_step (LoadAcquire (Val $ LitV $ LitLoc ℓ))
               (Some $ MEvLoadAcquire ℓ v)
               []
               (of_val v)
               []
  | StoreReleaseS ℓ v :
     head_step (StoreRelease (Val $ LitV $ LitLoc ℓ) (Val v))
               (Some $ MEvStoreRelease ℓ v)
               []
               (Val $ LitV LitUnit)
               []
  | FlushS ℓ :
     head_step (Flush (Val $ LitV $ LitLoc ℓ))
               (Some $ MEvFlush ℓ)
               []
               (Val $ LitV LitUnit)
               []
  | FenceS : head_step Fence
               (Some $ MEvFence)
               []
               (Val $ LitV LitUnit)
               []
  | FenceSyncS : head_step FenceSync
               (Some $ MEvFenceSync)
               []
               (Val $ LitV LitUnit)
               []
  | CmpXchgSuccS ℓ v1 v2 vl :
     head_step (CmpXchg (Val $ LitV $ LitLoc ℓ) (Val v1) (Val v2))
               (Some $ MEvRMW ℓ v1 v2)
               []
               (Val $ PairV vl (LitV $ LitBool true))
               []
  | CmpXchgFailS ℓ v1 v2 vl :
     vl ≠ v1 →
     head_step (CmpXchg (Val $ LitV $ LitLoc ℓ) (Val v1) (Val v2))
               (Some $ MEvLoadEx ℓ vl)
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

  Lemma fill_item_val_inv Ki v1 v2 :
    is_Some (to_val (fill_item Ki (of_val v1))) →
    is_Some (to_val (fill_item Ki (of_val v2))).
  Proof. intros. induction Ki; simplify_option_eq; eauto. Qed.

  (* Even though what we have so far does not qualify as a "language" that we
  can instantiate Iris with, we will instantiate Iris with a pseudo/pro forma
  instance.  This is because the WPC notation in Perennial is constructed using
  a type class called [Wpc] which requires the expression argument to be the
  expression for some language.  We call it `expr_lang` since it expressions are
  actually expressions (in comparison to `nvm_lang` where expressions are thread
  states). Note: in the past is was also the case that [WP] in Iris itself
  depended on the expressions having a language instance, but this is no longer
  the case. *)
  Lemma expr_ectxi_lang_mixin :
    EctxiLanguageMixin (state := unit) (observation := Empty_set) (global_state := unit)
      of_val to_val fill_item
      (fun _ _ _ _ _ _ _ _ => False).
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
            fill_item_val, fill_item_val_inv, fill_item_no_val_inj,
            head_ctx_step_val =>//.
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
  (* The second argument to [ThreadState] and [ThreadVal] is a pair, but if they
  appear somewhere where our expression/value scope is in effect then the pair
  notation of the language will be used. We add this annotation to ensure that
  for the second arguments Coq's core pair notation is always used. *)
  Arguments ThreadState _ _%core.
  Arguments ThreadVal _ _%core.

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
    thread_state → mem_config → unit → list observation →
    thread_state → mem_config → unit → list thread_state → Prop :=
  | pure_step e TV σ e' efs :
      head_step e None [] e' efs →
      thread_step (ThreadState e TV) σ () []
                  (ThreadState e' TV) σ () ((λ e, ThreadState e TV) <$> efs)
  | impure_step e TV σ evt e' V' σ' :
      head_step e (Some evt) [] e' [] →
      mem_step σ TV evt σ' V' →
      thread_step (ThreadState e TV) σ () [] (ThreadState e' V') σ' () [].
  Arguments thread_step _%E _ _ _%E _ _%E.

  (* The thread view is monotonically increasing with steps. *)
  Lemma thread_step_view_sqsubseteq e TV σ g κs e' TV' σ' g' ef :
    thread_step (ThreadState e TV) σ g κs (ThreadState e' TV') σ' g' ef →
    TV ⊑ TV'.
  Proof.
    inversion 1; first done.
    match goal with H : mem_step _ _ _ _ _ |- _ => destruct H end;
      repeat split; auto using view_le_l, view_le_r, view_insert_le'
                         with lia subst.
  Qed.

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

  Lemma thread_val_stuck e1 σ1 g1 κs e2 σ2 g2 ef :
    thread_step e1 σ1 g1 κs e2 σ2 g2 ef → thread_to_val e1 = None.
  Proof.
    inversion 1 as [????? Hstep|??????? Hstep]; inversion Hstep; done.
  Qed.

  Lemma thread_head_ctx_step_val Ki e σ g1 κs e2 σ2 g2 ef :
    thread_step (thread_fill_item Ki e) σ g1 κs e2 σ2 g2 ef → is_Some (thread_to_val e).
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

  Lemma thread_fill_item_val_inv Ki (v1 v2 : thread_val) :
    is_Some (thread_to_val (thread_fill_item Ki (thread_of_val v1))) →
    is_Some (thread_to_val (thread_fill_item Ki (thread_of_val v2))).
  Proof. intros. induction Ki; simplify_option_eq; eauto. Qed.

  Lemma nvm_lang_mixin :
    EctxiLanguageMixin thread_of_val thread_to_val thread_fill_item thread_step.
  Proof.
    split;
      apply _ ||
      eauto using thread_to_of_val, thread_of_to_val, thread_val_stuck,
        thread_fill_item_val, thread_fill_item_val_inv,
        thread_fill_item_no_val_inj, thread_head_ctx_step_val.
  Qed.
End nvm_lang.

Canonical Structure expr_ectxi_lang := EctxiLanguage nvm_lang.expr_ectxi_lang_mixin.
Canonical Structure expr_ectx_lang := EctxLanguageOfEctxi expr_ectxi_lang.
Canonical Structure expr_lang := LanguageOfEctx expr_ectx_lang.

Canonical Structure nvm_ectxi_lang := EctxiLanguage nvm_lang.nvm_lang_mixin.
Canonical Structure nvm_ectx_lang := EctxLanguageOfEctxi nvm_ectxi_lang.
Canonical Structure nvm_lang := LanguageOfEctx nvm_ectx_lang.

Canonical Structure nvm_crash_lang : crash_semantics nvm_lang :=
  {| crash_prim_step := crash_step |}.

Export nvm_lang.

Declare Scope thread_expr_scope.
Declare Scope thread_val_scope.

Bind Scope thread_expr_scope with thread_state.
Bind Scope thread_val_scope with thread_val.

(* Scope delimiters like the ones that HeapLang has. *)
Delimit Scope thread_expr_scope with TE.
Delimit Scope thread_val_scope with TV.

(* Convenient way of writing an expression and a thread view. *)
Notation "e '`at`' TV" := (ThreadState e%E TV) (at level 180) : thread_expr_scope.
Notation "v '`at`' TV" := (ThreadVal v%V TV) (at level 180) : thread_val_scope.

Notation "e '`at`' TV" := (ThreadState e%E TV) (at level 180) : expr_scope.
Notation "v '`at`' TV" := (ThreadVal v%V TV) (at level 180) : val_scope.

(* There is a correspondance between [fill] in nvm_lang and expr_lang. *)
Lemma nvm_fill_fill (K : list (ectx_item)) (e1 : expr) TV :
  ThreadState (fill K e1) TV =
    fill (K : list (ectxi_language.ectx_item nvm_ectxi_lang)) (ThreadState e1 TV).
Proof.
  induction K using rev_ind.
  - done.
  - rewrite !fill_app. rewrite -IHK. done.
Qed.

Lemma pure_step_thread_view e1 e2 TV1 TV2 :
  language.pure_step (ThreadState e1 TV1) (ThreadState e2 TV2) → TV1 ⊑ TV2.
Proof.
  destruct 1 as [safe det].
  rewrite /reducible_no_obs in safe.
  edestruct (safe (∅, ∅) ()) as ([e' TV'] & ? & ? & ? & step).
  simpl in *.
  pose proof (det _ _ _ _ _ _ _ step) as (? & ? & ? & ? & ?).
  simplify_eq.
  destruct step as [K [? TV1'] [? TV2'] eq1 eq2 step].
  simpl in *.
  apply thread_step_view_sqsubseteq in step.
  rewrite -!nvm_fill_fill in eq1, eq2.
  by simplify_eq.
Qed.

Lemma nsteps_pure_step_thread_view n e1 TV1 e2 TV2 :
  relations.nsteps language.pure_step n (e1 `at` TV1)%E (e2 `at` TV2)%E → TV1 ⊑ TV2.
Proof.
  revert e1 TV1 e2 TV2.
  induction n as [|n IH].
  - inversion 1. done.
  - intros e1 TV1 e2 TV2. inversion 1 as [|? ? [??] ? step ?].
    apply pure_step_thread_view in step.
    etrans; first apply step.
    eapply IH.
    done.
Qed.

(* This lemma seems true, but we haven't needed it yet. If (e `at` TV) can
take a pure step to (e' at TV) then for any TV (e `at` TV') can take a pure
step to (e' at TV'). *)
Lemma pure_step_thread_view_independent e1 e2 TV :
  language.pure_step (e1 `at` TV)%E (e2 `at` TV)%E →
  ∀ TV', language.pure_step (e1 `at` TV')%E (e2 `at` TV')%E.
Proof.
  intros [safe det] TV'.
  rewrite /reducible_no_obs in safe.
  edestruct (safe (∅, ∅) ()) as ([e' ?TV] & ? & ? & ? & step).
  simpl in *.
  pose proof (det _ _ _ _ _ _ _ step) as (? & ? & ? & ? & ?).
  simplify_eq.
  destruct step as [K [? TV1'] [? TV2'] eq1 eq2 step].
  simpl in *.
  inversion step.
Abort.
