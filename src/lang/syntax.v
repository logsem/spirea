From stdpp Require Export binders strings.
From stdpp Require Import countable.
From iris.algebra Require Import ofe.
From iris.heap_lang Require Import locations.

Module syntax.

  Implicit Type ℓ : loc.

  Definition proph_id := positive.

  Inductive memory_access := NA | AT.

  (* Literals of the language. *)
  Inductive literal : Set :=
    | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitPoison
    | LitLoc ℓ | LitProphecy (p: proph_id).

  Inductive un_op : Set := NegOp | MinusUnOp.

  Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

  Inductive expr :=
    (* Embed values inside expressions. *)
    | Val (v : val)
    (* Functions and application. *)
    | Var (x : string)
    | Rec (f x : binder) (e : expr)
    | App (e1 e2 : expr)
    (* Base types and their operations *)
    | UnOp (op : un_op) (e : expr)
    | BinOp (op : bin_op) (e1 e2 : expr)
    | If (e0 e1 e2 : expr)
    (* Products *)
    | Pair (e1 e2 : expr)
    | Fst (e : expr)
    | Snd (e : expr)
    (* Sums *)
    | InjL (e : expr)
    | InjR (e : expr)
    | Case (e0 : expr) (e1 : expr) (e2 : expr)
    (* Concurrency *)
    | Fork (e : expr)
    (* Memory operations. *)
    | AllocN (a : memory_access) (e1 e2 : expr)
    | Load (e : expr)
    | LoadAcquire (e : expr)
    | Store (e1 e2 : expr)
    | StoreRelease (e1 e2 : expr)
    | WB (e1 : expr)
    | Fence
    | FenceSync
    (* RMW memory operations. *)
    | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
    | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
    (* Prophecy *)
    | NewProph
    | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *)
    with val :=
    | LitV (l : literal)
    | RecV (f x : binder) (e : expr)
    | PairV (v1 v2 : val)
    | InjLV (v : val)
    | InjRV (v : val).

  Declare Scope expr_scope.
  Declare Scope val_scope.

  Bind Scope expr_scope with expr.
  Bind Scope val_scope with val.

  Delimit Scope expr_scope with E.
  Delimit Scope val_scope with V.

  Definition observation : Set := proph_id * (val * val).

  (* Convert values to expressions. *)
  Notation of_val := Val (only parsing).

  (* Convert expressions to values. *)
  Definition to_val (e : expr) : option val :=
    match e with
    | Val v => Some v
    | _ => None
    end.

  (** Equality and other typeclass stuff *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. done. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. destruct e=>//=. by intros [= <-]. Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. intros. congruence. Qed.

  Definition lit_is_unboxed (l: literal) : Prop :=
    match l with
    | LitProphecy _ | LitPoison => False
    | LitInt _ | LitBool _  | LitLoc _ | LitUnit => True
    end.
  Definition val_is_unboxed (v : val) : Prop :=
    match v with
    | LitV l => lit_is_unboxed l
    | InjLV (LitV l) => lit_is_unboxed l
    | InjRV (LitV l) => lit_is_unboxed l
    | _ => False
    end.

  Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
  Proof. destruct l; simpl; exact (decide _). Defined.
  Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
  Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

  Definition vals_compare_safe (vl v1 : val) : Prop :=
    val_is_unboxed vl ∨ val_is_unboxed v1.
  Global Arguments vals_compare_safe !_ !_ /.

  (* Expressions have decidable equality. *)
  Global Instance base_lit_eq_dec : EqDecision literal.
  Proof. solve_decision. Defined.
  Global Instance un_op_eq_dec : EqDecision un_op.
  Proof. solve_decision. Defined.
  Global Instance bin_op_eq_dec : EqDecision bin_op.
  Proof. solve_decision. Defined.
  Global Instance memory_access_eq_dec : EqDecision memory_access.
  Proof. solve_decision. Defined.
  Global Instance expr_eq_dec : EqDecision expr.
  Proof.
    refine (
    fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
      match e1, e2 with
      | Val v, Val v' => cast_if (decide (v = v'))
      | Var x, Var x' => cast_if (decide (x = x'))
      | Rec f x e, Rec f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
      | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
      | BinOp o e1 e2, BinOp o' e1' e2' =>
          cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
      | If e0 e1 e2, If e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Pair e1 e2, Pair e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | Fst e, Fst e' => cast_if (decide (e = e'))
      | Snd e, Snd e' => cast_if (decide (e = e'))
      | InjL e, InjL e' => cast_if (decide (e = e'))
      | InjR e, InjR e' => cast_if (decide (e = e'))
      | Case e0 e1 e2, Case e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Fork e, Fork e' => cast_if (decide (e = e'))
      | AllocN a e1 e2, AllocN a' e1' e2' =>
          cast_if_and3 (decide (a = a')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Load e, Load e' => cast_if (decide (e = e'))
      | LoadAcquire e, LoadAcquire e' => cast_if (decide (e = e'))
      | Store e1 e2, Store e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | StoreRelease e1 e2, StoreRelease e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | WB e, WB e' => cast_if (decide (e = e'))
      | Fence, Fence => left _
      | FenceSync, FenceSync => left _
      | CmpXchg e0 e1 e2, CmpXchg e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | FAA e1 e2, FAA e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | NewProph, NewProph => left _
      | Resolve e0 e1 e2, Resolve e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | _, _ => right _
      end
    with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
      match v1, v2 with
      | LitV l, LitV l' => cast_if (decide (l = l'))
      | RecV f x e, RecV f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
      | PairV e1 e2, PairV e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | InjLV e, InjLV e' => cast_if (decide (e = e'))
      | InjRV e, InjRV e' => cast_if (decide (e = e'))
      | _, _ => right _
      end
    for go); try (clear go gov; abstract intuition congruence).
  Defined.
  Global Instance val_eq_dec : EqDecision val.
  Proof. solve_decision. Defined.

  (* Expressions are countable. *)
  Global Instance base_lit_countable : Countable literal.
  Proof.
  refine (inj_countable' (λ l, match l with
    | LitInt n => (inl (inl n), None)
    | LitBool b => (inl (inr b), None)
    | LitUnit => (inr (inl false), None)
    | LitPoison => (inr (inl true), None)
    | LitLoc l => (inr (inr l), None)
    | LitProphecy p => (inr (inl false), Some p)
    end) (λ l, match l with
    | (inl (inl n), None) => LitInt n
    | (inl (inr b), None) => LitBool b
    | (inr (inl false), None) => LitUnit
    | (inr (inl true), None) => LitPoison
    | (inr (inr l), None) => LitLoc l
    | (_, Some p) => LitProphecy p
    end) _); by intros [].
  Qed.
  Global Instance un_op_finite : Countable un_op.
  Proof.
  refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
    (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
  Qed.
  Global Instance bin_op_countable : Countable bin_op.
  Proof.
  refine (inj_countable' (λ op, match op with
    | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
    | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
    | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
    end) (λ n, match n with
    | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
    | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
    | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
    end) _); by intros [].
  Qed.
  Global Instance memory_access_countable : Countable memory_access.
  Proof.
    refine
      (inj_countable' (λ a, match a with NA => 0 | AT => 1 end)
                      (λ n, match n with 0 => NA | _ => AT end) _).
    intros []; done.
  Qed.
  Global Instance expr_countable : Countable expr.
  Proof.
  set (enc :=
    fix go e :=
      match e with
      | Val v => GenNode 0 [gov v]
      | Var x => GenLeaf (inl (inl x))
      | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
      | App e1 e2 => GenNode 2 [go e1; go e2]
      | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
      | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
      | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
      | Pair e1 e2 => GenNode 6 [go e1; go e2]
      | Fst e => GenNode 7 [go e]
      | Snd e => GenNode 8 [go e]
      | InjL e => GenNode 9 [go e]
      | InjR e => GenNode 10 [go e]
      | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
      | Fork e => GenNode 12 [go e]
      | AllocN NA e1 e2 => GenNode 13 [go e1; go e2]
      | AllocN AT e1 e2 => GenNode 26 [go e1; go e2]
      | Load e => GenNode 15 [go e]
      | LoadAcquire e => GenNode 16 [go e]
      | Store e1 e2 => GenNode 17 [go e1; go e2]
      | StoreRelease e1 e2 => GenNode 18 [go e1; go e2]
      | WB e => GenNode 19 [go e]
      | Fence => GenNode 20 []
      | FenceSync => GenNode 21 []
      | CmpXchg e0 e1 e2 => GenNode 22 [go e0; go e1; go e2]
      | FAA e1 e2 => GenNode 23 [go e1; go e2]
      | NewProph => GenNode 24 []
      | Resolve e0 e1 e2 => GenNode 25 [go e0; go e1; go e2]
      end
    with gov v :=
      match v with
      | LitV l => GenLeaf (inr (inl l))
      | RecV f x e =>
          GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
      | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
      | InjLV v => GenNode 2 [gov v]
      | InjRV v => GenNode 3 [gov v]
      end
    for go).
  set (dec :=
    fix go e :=
      match e with
      | GenNode 0 [v] => Val (gov v)
      | GenLeaf (inl (inl x)) => Var x
      | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
      | GenNode 2 [e1; e2] => App (go e1) (go e2)
      | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
      | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
      | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
      | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
      | GenNode 7 [e] => Fst (go e)
      | GenNode 8 [e] => Snd (go e)
      | GenNode 9 [e] => InjL (go e)
      | GenNode 10 [e] => InjR (go e)
      | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
      | GenNode 12 [e] => Fork (go e)
      | GenNode 13 [e1; e2] => AllocN NA (go e1) (go e2)
      | GenNode 26 [e1; e2] => AllocN AT (go e1) (go e2)
      | GenNode 15 [e] => Load (go e)
      | GenNode 16 [e] => LoadAcquire (go e)
      | GenNode 17 [e1; e2] => Store (go e1) (go e2)
      | GenNode 18 [e1; e2] => StoreRelease (go e1) (go e2)
      | GenNode 19 [e] => WB (go e)
      | GenNode 20 [] => Fence
      | GenNode 21 [] => FenceSync
      | GenNode 22 [e0; e1; e2] => CmpXchg (go e0) (go e1) (go e2)
      | GenNode 23 [e1; e2] => FAA (go e1) (go e2)
      | GenNode 24 [] => NewProph
      | GenNode 25 [e0; e1; e2] => Resolve (go e0) (go e1) (go e2)
      | _ => Val $ LitV LitUnit (* dummy *)
      end
    with gov v :=
      match v with
      | GenLeaf (inr (inl l)) => LitV l
      | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
      | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
      | GenNode 2 [v] => InjLV (gov v)
      | GenNode 3 [v] => InjRV (gov v)
      | _ => LitV LitUnit (* dummy *)
      end
    for go).
  refine (inj_countable' enc dec _).
  refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
  - destruct e as [v| | | | | | | | | | | | | | [|] | | | | | | | | | | |]; simpl; f_equal;
      [exact (gov v)| try done..].
  - destruct v; by f_equal.
  Qed.
  Global Instance val_countable : Countable val.
  Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.

End syntax.

Export syntax.
