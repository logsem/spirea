From Equations Require Import Equations.

From stdpp Require Import tactics.
From stdpp Require Import options.
From stdpp Require Import vector.
Local Set Universe Polymorphism.

(* To prevent problems with Equations. *)
Set Transparent Obligations.
Local Unset Mangle Names. (* work around https://github.com/mattam82/Coq-Equations/issues/407 *)

(* Not using [list] in order to avoid universe inconsistencies. [ilist] stands
for indenpendet list in the sense that it is independent from anything in stdpp
that might cause universe problems. *)
Inductive ilist (A : Type) :=
| inil : ilist A
| icons : A → ilist A → ilist A.

Derive NoConfusion for ilist.

Arguments inil {A}.
Arguments icons {A} a l.

Declare Scope ilist_scope.
Bind Scope ilist_scope with ilist.
Delimit Scope ilist_scope with L2.

Global Notation "[ ] " := inil : ilist_scope.
Global Notation "[ x ] " := (icons x inil) : ilist_scope.
Global Notation "[ x ; .. ; y ] " := (icons x .. (icons y inil) ..) : ilist_scope.

Section ilist.

  Equations ilen {A} (l : ilist A) : nat :=
  | inil => 0
  | icons _ t => S (ilen t).
  Global Transparent ilen.

  Equations ilist_to_vec {A} (l : ilist A) : vec A (ilen l) :=
  | inil => [#]
  | icons t ts => t ::: ilist_to_vec ts.

  Fixpoint ilist_fmap {A B} (f : A → B) (l : ilist A) :=
    match l with inil => inil | icons x l => icons (f x) (ilist_fmap f l) end.

  (* Definition ihead (As : ilist Type) := *)
  (*   match As with inil => unit%type *)
  (*   | icons x _ => x end. *)

  (* Definition ttail (As : ilist Type) := *)
  (*   match As with inil => inil | icons _ xs => xs end. *)

  Equations ilist_lookup {A} (As : ilist A) (i : fin (ilen As)) : A :=
  | icons x _, 0%fin => x
  | icons _ xs, FS i => ilist_lookup xs i.

  (* Lookup in a [ilist Type] with [unit] as a fallback. *)
  Fixpoint ilist_type_lookup (As : ilist Type) (i : nat) : Type :=
    match As with
    | inil => unit
    | icons t ts =>
        match i with
        | 0 => t
        | S i' => ilist_type_lookup ts i'
        end
    end.

  Equations ilist_lookup_fin (As : ilist Type) (i : fin (ilen As)) : Type :=
    | icons t ts, 0%fin := t;
    | icons t ts, FS i' := ilist_lookup_fin ts i'.

End ilist.

#[global] Infix "👀" := ilist_lookup (at level 20).

(* We call it [hvec] just to distinguish is from the stdpp's [hlist]. *)
Inductive hvec : ilist Type → Type :=
  | hnil : hvec inil
  | hcons {A As} : A → hvec As → hvec (icons A As).

Derive Signature NoConfusion NoConfusionHom for hvec.
Derive Subterm for hvec.

Fixpoint tapp (As Bs : ilist Type) : ilist Type :=
  match As with inil => Bs | icons A As => icons A (tapp As Bs) end.
Fixpoint happ {As Bs} (xs : hvec As) (ys : hvec Bs) : hvec (tapp As Bs) :=
  match xs with hnil => ys | hcons x xs => hcons x (happ xs ys) end.

Definition hhead {A As} (xs : hvec (icons A As)) : A :=
  match xs with hnil => () | hcons x _ => x end.
Definition htail {A As} (xs : hvec (icons A As)) : hvec As :=
  match xs with hnil => () | hcons _ xs => xs end.

Fixpoint hheads {As Bs} : hvec (tapp As Bs) → hvec As :=
  match As with
  | inil => λ _, hnil
  | icons _ _ => λ xs, hcons (hhead xs) (hheads (htail xs))
  end.
Fixpoint htails {As Bs} : hvec (tapp As Bs) → hvec Bs :=
  match As with
  | inil => id
  | icons _ _ => λ xs, htails (htail xs)
  end.

Fixpoint himpl (As : ilist Type) (B : Type) : Type :=
  match As with inil => B | icons A As => A → himpl As B end.

(** A telescope inspired notation for [himpl]. *)
Notation "As -h> B" :=
  (himpl As B) (at level 99, B at level 200, right associativity).

Definition hinit {B} (y : B) : himpl inil B := y.
Definition hlam {A As B} (f : A → himpl As B) : himpl (icons A As) B := f.
Global Arguments hlam _ _ _ _ _ / : assert.

Definition huncurry {As B} (f : himpl As B) (xs : hvec As) : B :=
  (fix go {As} xs :=
    match xs in hvec As return himpl As B → B with
    | hnil => λ f, f
    | hcons x xs => λ f, go xs (f x)
    end) _ xs f.
Coercion huncurry : himpl >-> Funclass.

Fixpoint hcurry {As B} : (hvec As → B) → himpl As B :=
  match As with
  | inil => λ f, f hnil
  | icons x xs => λ f, hlam (λ x, hcurry (f ∘ hcons x))
  end.

Lemma huncurry_curry {As B} (f : hvec As → B) xs :
  huncurry (hcurry f) xs = f xs.
Proof. by induction xs as [|A As x xs IH]; simpl; rewrite ?IH. Qed.

Fixpoint hcompose {As B C} (f : B → C) {struct As} : himpl As B → himpl As C :=
  match As with
  | inil => f
  | icons A As => λ g, hlam (λ x, hcompose f (g x))
  end.

Compute (icons nat (icons bool (icons Z inil))) 👀 1%fin.

(* Infix "👀" := ilist_type_lookup (at level 20). *)
(* Fixpoint hvec_lookup (As : ilist Type) (l : hvec As) : *)
(*     ∀ (i : nat), ilist_type_lookup As i := *)
(*   match l in hvec As return ∀ i : nat, As 👀 i with *)
(*   | hnil => λ i, tt *)
(*   | @hcons A As' x xs => λ i : nat, *)
(*       match i return ((icons A As') 👀 i) with *)
(*       | 0 => x *)
(*       | S i' => hvec_lookup As' xs i' *)
(*       end *)
(*   end. *)

Equations ilist_lookup_vec {As} (l : hvec As) (i : fin (ilen As)) : As 👀 i :=
| hcons x _, 0%fin := x
| hcons _ xs, FS i' := ilist_lookup_vec xs i'.
