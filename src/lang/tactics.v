From stdpp Require Import fin_maps.
From self.lang Require Import lang.
From iris Require Import options.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K], and a list of pairs of values [vs] (prophecy identifier and
     resolution value) that is only non-empty if a [ResolveLCtx] item (maybe
     having several levels) is in the process of being constructed. Note that
     a fully-constructed item is inserted into [K] by calling [add_item], and
     that is only the case when a non-[ResolveLCtx] item is built. When [vs]
     is non-empty, [add_item] also wraps the item under several [ResolveLCtx]
     constructors: one for each pair in [vs]. *)
  let rec go K vs e :=
    match e with
    | _                               => lazymatch vs with [] => tac K e | _ => fail end
    | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) vs K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) vs K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) vs K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) vs K e0
    | Pair ?e (Val ?v)                => add_item (PairLCtx v) vs K e
    | Pair ?e1 ?e2                    => add_item (PairRCtx e1) vs K e2
    | Fst ?e                          => add_item FstCtx vs K e
    | Snd ?e                          => add_item SndCtx vs K e
    | InjL ?e                         => add_item InjLCtx vs K e
    | InjR ?e                         => add_item InjRCtx vs K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0
    | AllocN ?a ?e (Val ?v)           => add_item (AllocNLCtx a v) vs K e
    | AllocN ?a ?e1 ?e2               => add_item (AllocNRCtx a e1) vs K e2
    | Load ?e                         => add_item LoadCtx vs K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) vs K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) vs K e2
    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLCtx v1 v2) vs K e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMCtx e0 v2) vs K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgRCtx e0 e1) vs K e2
    | FAA ?e (Val ?v)                 => add_item (FaaLCtx v) vs K e
    | FAA ?e1 ?e2                     => add_item (FaaRCtx e1) vs K e2
    (* Uncomment this if we need prophecy variables. *)
    (* | Resolve ?ex (Val ?v1) (Val ?v2) => go K ((v1,v2) :: vs) ex
    | Resolve ?ex ?e1 (Val ?v2)       => add_item (ResolveMCtx ex v2) vs K e1
    | Resolve ?ex ?e1 ?e2             => add_item (ResolveRCtx ex e1) vs K e2 *)
    end
  with add_item Ki vs K e :=
    lazymatch vs with
    | []               => go (Ki :: K) (@nil (val * val)) e
    (* | (?v1,?v2) :: ?vs => add_item (ResolveLCtx Ki v1 v2) vs K e *)
    end
  in
  go (@nil ectx_item) (@nil (val * val)) e.

  (* See [inv_impure_thread_step] below which is much faster than this
  tactic. *)
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
    | H : thread_step ?e _ _ _ _ _ _ _ |- _ =>
        try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
        and should thus better be avoided. *)
        inversion H; subst; clear H
    end.

  Ltac inv_head_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : nvm_lang.head_step ?e _ _ _ _ |- _ =>
        try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
        and should thus better be avoided. *)
        inversion H; subst; clear H
    end.

  Ltac inv_mem_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : mem_step _ _ _ _ _ |- _ =>
        inversion H; subst; clear H
    end.

  (* This tactic find an assumption in the context of the form [thread_step ...]
  and performs inversion on it. It assumes that the expression is _impure_,
  i.e., that all the steps the expression can take interact with the memory. *)
  Ltac inv_impure_thread_step :=
    match goal with
    | H : thread_step ?e _ _ _ _ _ _ _ |- _ =>
      inversion H;
      [ (* The first goal corresponds to a pure step which we can rule out. *)
        match goal with H : head_step _ _ _ _ _ |- _ => inversion H end
        (* We do inversion in the [head_step] first. We know what the expression
        is so this will determine the memory event which the inversion in the
        memory step can use to find a unique constructor. *)
      | inv_head_step; inv_mem_step
      ]
    end.
