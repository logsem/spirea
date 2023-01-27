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
  Global Transparent ilist_lookup.

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

  Fixpoint iapp {A} (As Bs : ilist A) : ilist A :=
    match As with inil => Bs | icons A As => icons A (iapp As Bs) end.

  Fixpoint iimpl (As : ilist A) (B : Type) : Type :=
    match As with inil => B | icons A As => F A → iimpl As B end.

End ilist.

(** A telescope inspired notation for [iimpl]. *)
Notation "As -h> B" :=
  (iimpl As B) (at level 99, B at level 200, right associativity).

#[global] Infix "👀" := ilist_lookup (at level 20).

(* We call it [hvec] just to distinguish is from the stdpp's [hlist]. We
parameterize [hvec] by a type [A] and a family [F] over the type. The key
benefit of this is that we then know that the elements in the elements in [hvec]
all have the shape [F x] for some [x : A].

For instance, [A] might be [Type] [F] might be [λ x, x * x]. We would then know
that all elements in the list are pair. Furthermore, Coq is able to compute this
fact in some circumstantes. In particular [hvec_lookup] we can a priori know the
shape of the returned type without knowing the specific index and Coq can
compute with this fact.  *)
Inductive hvec {A : Type} (F : A → Type) : ilist A → Type :=
  | hnil : hvec F inil
  | hcons {x As} : F x → hvec F As → hvec F (icons x As).

Arguments hnil {A F}.
Arguments hcons {A F} {_ _} a l.

Definition hvec_ty := @hvec Type (λ T, T).

Derive Signature NoConfusion NoConfusionHom for hvec.
Derive Subterm for hvec.

Section hvec.
  Context {A : Type} {F : A → Type}.

  Fixpoint happ {As Bs} (xs : hvec F As) (ys : hvec F Bs) : hvec F (iapp As Bs) :=
    match xs with hnil => ys | hcons x xs => hcons x (happ xs ys) end.

  Definition hhead {A As} (xs : hvec F (icons A As)) : F A :=
    match xs with hnil => () | hcons x _ => x end.
  Definition htail {A As} (xs : hvec F (icons A As)) : hvec F As :=
    match xs with hnil => () | hcons _ xs => xs end.

  Fixpoint hheads {As Bs} : hvec F (iapp As Bs) → hvec F As :=
    match As with
    | inil => λ _, hnil
    | icons _ _ => λ xs, hcons (hhead xs) (hheads (htail xs))
    end.
  Fixpoint htails {As Bs} : hvec F (iapp As Bs) → hvec F Bs :=
    match As with
    | inil => id
    | icons _ _ => λ xs, htails (htail xs)
    end.

  Definition hinit {B} (y : B) : himpl inil B := y.
  Definition hlam {x As B} (f : F x → himpl As B) : himpl (icons x As) B := f.
  Global Arguments hlam _ _ _ _ _ / : assert.

  Definition huncurry {As B} (f : himpl As B) (xs : hvec F As) : B :=
    (fix go {As} xs :=
      match xs in hvec _ As return himpl As B → B with
      | hnil => λ f, f
      | hcons x xs => λ f, go xs (f x)
      end) _ xs f.
  Coercion huncurry : himpl >-> Funclass.

  Fixpoint hcurry {As B} : (hvec F As → B) → himpl As B :=
    match As with
    | inil => λ f, f hnil
    | icons x xs => λ f, hlam (λ x, hcurry (f ∘ hcons x))
    end.

  Lemma huncurry_curry {As B} (f : hvec F As → B) xs :
    huncurry (hcurry f) xs = f xs.
  Proof. by induction xs as [|? As x xs IH]; simpl; rewrite ?IH. Qed.

  Fixpoint hcompose {As B C} (f : B → C) {struct As} : himpl As B → himpl As C :=
    match As with
    | inil => f
    | icons A As => λ g, hlam (λ x, hcompose f (g x))
    end.

  Compute (icons nat (icons bool (icons Z inil))) 👀 1%fin.

  (* Infix "👀" := ilist_type_lookup (at level 20). *)
  (* Fixpoint hvec_lookup (As : ilist Type) (l : hvec F As) : *)
  (*     ∀ (i : nat), ilist_type_lookup As i := *)
  (*   match l in hvec F As return ∀ i : nat, As 👀 i with *)
  (*   | hnil => λ i, tt *)
  (*   | @hcons A As' x xs => λ i : nat, *)
  (*       match i return ((icons A As') 👀 i) with *)
  (*       | 0 => x *)
  (*       | S i' => hvec_lookup As' xs i' *)
  (*       end *)
  (*   end. *)

  Equations hvec_lookup {As} (l : hvec F As) (i : fin (ilen As)) : F (As 👀 i) :=
    hvec_lookup (hcons xx _) 0%fin := xx ;
    hvec_lookup (hcons _ xs) (FS i') := hvec_lookup xs i'.

End hvec.

#[global] Infix "👀" := hvec_lookup (at level 20).
