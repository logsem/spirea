From Equations Require Import Equations.

From stdpp Require Import tactics.
From stdpp Require Import options.
From stdpp Require Import vector.
Local Set Universe Polymorphism.

(* To prevent problems with Equations. *)
Set Transparent Obligations.
Local Unset Mangle Names. (* work around https://github.com/mattam82/Coq-Equations/issues/407 *)

(* Not using [list] in order to avoid universe inconsistencies. [ivec] stands
for indenpendet list in the sense that it is independent from anything in stdpp
that might cause universe problems. *)
Inductive ivec (A : Type) : nat → Type :=
| inil : ivec A 0
| icons {n : nat} : A → ivec A n → ivec A (S n).

(* Derive NoConfusion for ivec. *)
Derive Signature NoConfusion NoConfusionHom for ivec.
Derive Subterm for ivec.

Arguments inil {A}.
Arguments icons {A} {n} a l.

Declare Scope ivec_scope.
Bind Scope ivec_scope with ivec.
Delimit Scope ivec_scope with IL.

Global Infix "::" := icons (at level 60, right associativity) : ivec_scope.
Global Notation "[ ] " := inil : ivec_scope.
Global Notation "[ x ] " := (icons x inil) : ivec_scope.
Global Notation "[ x ; .. ; y ] " := (icons x .. (icons y inil) ..) : ivec_scope.

Section ivec.

  Equations ilen {A n} (l : ivec A n) : nat :=
  | inil => 0
  | icons _ t => S (ilen t).
  Global Transparent ilen.

  Equations ivec_to_vec {A n} (l : ivec A n) : vec A (ilen l) :=
  | inil => [#]
  | icons t ts => t ::: ivec_to_vec ts.

  Fixpoint ivec_fmap {A B n} (f : A → B) (l : ivec A n) :=
    match l with inil => inil | icons x l => icons (f x) (ivec_fmap f l) end.

  Equations ivec_lookup {A n} : Lookup nat A (ivec A n) :=
  | _, inil => None
  | 0, icons x _ => Some x
  | S i, icons _ xs => ivec_lookup i xs.
  Global Transparent ivec_lookup.

  #[global] Existing Instance ivec_lookup.

  Equations ivec_lookup_total {A n} (As : ivec A n) (i : fin n) : A :=
  | icons x _, 0%fin => x
  | icons _ xs, FS i => ivec_lookup_total xs i.
  Global Transparent ivec_lookup_total.

  (* Lookup in a [ivec Type] with [unit] as a fallback. *)
  Fixpoint ivec_type_lookup {n} (As : ivec Type n) (i : nat) : Type :=
    match As with
    | inil => unit
    | icons t ts =>
        match i with
        | 0 => t
        | S i' => ivec_type_lookup ts i'
        end
    end.

  Fixpoint iapp {A n m} (As : ivec A n) (Bs : ivec A m) : ivec A (n + m) :=
    match As with
    | inil => Bs
    | icons A As => icons A (iapp As Bs)
    end.

  Fixpoint iimpl {A n} (F : A → Type) (As : ivec A n) (B : Type) : Type :=
    match As with
    | inil => B
    | icons A As => F A → iimpl F As B
    end.

End ivec.

#[global] Infix "++" := iapp (at level 60, right associativity) : ivec_scope.

(** A telescope inspired notation for [iimpl]. *)
Notation "As -h> B" :=
  (iimpl (λ A, A) As B) (at level 99, B at level 200, right associativity).

#[global] Infix "👀" := ivec_lookup_total (at level 20).

(* We call it [hvec] just to distinguish is from the stdpp's [hlist]. We
parameterize [hvec] by a type [A] and a family [F] over the type. The key
benefit of this is that we then know that the elements in the elements in [hvec]
all have the shape [F x] for some [x : A].

For instance, [A] might be [Type] [F] might be [λ x, x * x]. We would then know
that all elements in the list are pair. Furthermore, Coq is able to compute this
fact in some circumstantes. In particular [hvec_lookup] we can a priori know the
shape of the returned type without knowing the specific index and Coq can
compute with this fact.  *)
Inductive hvec {A : Type} (F : A → Type) : forall (n : nat), ivec A n → Type :=
  | hnil : hvec F 0 []
  | hcons {n x} {As : ivec A n} : F x → hvec F n As → hvec F (S n) (x :: As).

Arguments hnil {A F}.
Arguments hcons {_ _ _ _ _} a l.

Definition hvec_ty := @hvec Type (λ T, T).

Derive Signature NoConfusion NoConfusionHom for hvec.
Derive Subterm for hvec.

Section hvec.
  Context {A : Type} {F : A → Type}.

  Fixpoint happ {n m} {As : ivec A n} {Bs : ivec A m}
      (xs : hvec F n As) (ys : hvec F m Bs) : hvec F (n + m) (iapp As Bs) :=
    match xs with hnil => ys | hcons x xs => hcons x (happ xs ys) end.

  Definition hhead {n a As} (xs : hvec F (S n) (a :: As)) : F a :=
    match xs with hnil => () | hcons x _ => x end.
  Definition htail {n a As} (xs : hvec F (S n) (a :: As)) : hvec F n As :=
    match xs with hnil => () | hcons _ xs => xs end.

  Fixpoint hheads {n m As} {Bs : ivec A m} :
      hvec F (n + m) (As ++ Bs) → hvec F n As :=
    match As with
    | inil => λ _, hnil
    | icons _ _ => λ xs, hcons (hhead xs) (hheads (htail xs))
    end.
  Fixpoint htails {n m} {As : ivec A n} {Bs : ivec A m} : hvec F (n + m) (iapp As Bs) → hvec F m Bs :=
    match As with
    | inil => id
    | icons _ _ => λ xs, htails (htail xs)
    end.

  Definition hinit {B} (y : B) : iimpl F inil B := y.
  Definition hlam {n x} {As : ivec A n} {B}
    (f : F x → iimpl F As B) : iimpl F (icons x As) B := f.
  Global Arguments hlam _ _ _ _ _ _ / : assert.

  (* Equations huncurry {As B} (f : iimpl F As B) (xs : hvec F As) : B := *)
  (* | f, hnil => f *)
  (* | f, hcons x xs => huncurry (f x) xs. *)

  Equations huncurry {n} {As B} (f : iimpl F As B) (xs : hvec F n As) : B :=
  | f, hnil => f
  | f, hcons xx xs => huncurry (f xx) xs.
  Global Transparent huncurry.

  (* Definition huncurry {n} {As B} (f : iimpl F As B) (xs : hvec F n As) : B := *)
  (*   (fix go {As} xs := *)
  (*     match xs in hvec _ _ As return iimpl F As B → B with *)
  (*     | hnil => λ f, f *)
  (*     | hcons x xs => λ f, go xs (f x) *)
  (*     end) _ xs f. *)
  Coercion huncurry : iimpl >-> Funclass.

  Fixpoint hcurry {n} {As B} : (hvec F n As → B) → iimpl F As B :=
    match As with
    | inil => λ f, f hnil
    | icons x xs => λ f, hlam (λ x, hcurry (f ∘ hcons x))
    end.

  Lemma huncurry_curry {n As B} (f : hvec F n As → B) xs :
    huncurry (hcurry f) xs = f xs.
  Proof. by induction xs as [|n ? As x xs IH]; simpl; rewrite ?IH. Qed.

  Fixpoint hcompose {n} {As : ivec A n} {B C} (f : B → C) {struct As} :
      iimpl F As B → iimpl F As C :=
    match As with
    | inil => f
    | icons A As => λ g, hlam (λ x, hcompose f (g x))
    end.

  Compute (icons nat (icons bool (icons Z inil))) 👀 1%fin.

  (* Infix "👀" := ivec_type_lookup (at level 20). *)
  (* Fixpoint hvec_lookup (As : ivec Type) (l : hvec F As) : *)
  (*     ∀ (i : nat), ivec_type_lookup As i := *)
  (*   match l in hvec F As return ∀ i : nat, As 👀 i with *)
  (*   | hnil => λ i, tt *)
  (*   | @hcons A As' x xs => λ i : nat, *)
  (*       match i return ((icons A As') 👀 i) with *)
  (*       | 0 => x *)
  (*       | S i' => hvec_lookup As' xs i' *)
  (*       end *)
  (*   end. *)

  Equations hvec_lookup {n As} (l : hvec F n As) (i : fin n) : F (As 👀 i) :=
    hvec_lookup (hcons xx _) 0%fin := xx ;
    hvec_lookup (hcons _ xs) (FS i') := hvec_lookup xs i'.

End hvec.

#[global] Infix "👀" := hvec_lookup (at level 20).
