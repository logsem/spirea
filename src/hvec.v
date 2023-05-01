From Equations Require Import Equations.

From stdpp Require Import tactics fin.

Local Set Universe Polymorphism.

(* To prevent problems with Equations. *)
Set Transparent Obligations.
Local Unset Mangle Names. (* work around https://github.com/mattam82/Coq-Equations/issues/407 *)

(* Not using [list] in order to avoid universe inconsistencies. [ivec] stands
   for independent list in the sense that it is independent from anything in
   stdpp that might cause universe problems. *)
Inductive ivec' (A : Type) : nat → Type :=
| inil : ivec' A 0
| icons {n : nat} : A → ivec' A n → ivec' A (S n).

Definition ivec n A := ivec' A n.

(* Derive NoConfusion for ivec. *)
Derive Signature NoConfusion NoConfusionHom for ivec'.
Derive Subterm for ivec'.

Arguments inil {A}.
Arguments icons {A} {n} a l.

Declare Scope ivec_scope.
Bind Scope ivec_scope with ivec'.
Bind Scope ivec_scope with ivec.
Delimit Scope ivec_scope with IL.

Global Infix "::" := icons (at level 60, right associativity) : ivec_scope.
Global Notation "[ ] " := inil : ivec_scope.
Global Notation "[ x ] " := (icons x inil) : ivec_scope.
Global Notation "[ x ; .. ; y ] " := (icons x .. (icons y inil) ..) : ivec_scope.

Section ivec.

  Equations ilen {A n} (l : ivec n A) : nat :=
  | inil => 0
  | icons _ t => S (ilen t).
  Global Transparent ilen.

  (* Equations ivec_to_vec {A n} (l : ivec n A) : vec A (ilen l) := *)
  (* | inil => [#] *)
  (* | icons t ts => t ::: ivec_to_vec ts. *)

  Fixpoint ivec_map {A B n} (f : A → B) (l : ivec n A) :=
    match l with
    | inil => inil
    | icons x l => icons (f x) (ivec_map f l)
    end.

  (* NOTE: We don't add this instance as its use sometimes causes universe
  issues that plain [ivec_map] does not suffer from. *)
  (* Global Instance ivec_fmap n : FMap (ivec n) := λ A B f, ivec_map f. *)

  Equations ivec_lookup {A n} : Lookup nat A (ivec n A) :=
  | _, inil => None
  | 0, icons x _ => Some x
  | S i, icons _ xs => ivec_lookup i xs.
  Global Transparent ivec_lookup.

  #[global] Existing Instance ivec_lookup.

  Equations ivec_lookup_total {A n} : LookupTotal (fin n) A (ivec n A) :=
  | 0%fin, icons x _ => x
  | FS i, icons _ xs => ivec_lookup_total i xs.
  Global Transparent ivec_lookup_total.

  #[global] Existing Instance ivec_lookup_total.

  (* (* Lookup in a [ivec Type] with [unit] as a fallback. *) *)
  (* Fixpoint ivec_type_lookup {n} (As : ivec n Type) (i : nat) : Type := *)
  (*   match As with *)
  (*   | inil => unit *)
  (*   | icons t ts => *)
  (*       match i with *)
  (*       | 0 => t *)
  (*       | S i' => ivec_type_lookup ts i' *)
  (*       end *)
  (*   end. *)

  Fixpoint iapp {A n m} (As : ivec n A) (Bs : ivec m A) : ivec (n + m) A :=
    match As with
    | inil => Bs
    | icons A As => icons A (iapp As Bs)
    end.

  Fixpoint iimpl {A n} (F : A → Type) (As : ivec n A) (B : Type) : Type :=
    match As with
    | inil => B
    | icons A As => F A → iimpl F As B
    end.

  Fixpoint ivec_to_list {A n} (As : ivec n A) : list A :=
    match As with
    | inil => nil
    | icons A As => cons A (ivec_to_list As)
    end.

  Global Instance ivec_to_list_inj {A n} : Inj (=) (=) (@ivec_to_list A n).
  Proof.
    intros l1 l2.
    induction l1 as [ | ? ? ? IH].
    - dependent elimination l2. done.
    - dependent elimination l2. simpl.
      inversion 1 as [[eq1 eq2]].
      apply IH in eq2 as ->.
      done.
  Qed.

  Lemma ivec_lookup_fmap {A B n} (F : A → B) (As : ivec n A) i :
    F (As !!! i) = (ivec_map F As) !!! i.
  Proof.
    induction As as [|??? IH]. { inversion i. }
    dependent elimination i. { reflexivity. }
    apply IH.
  Defined.

End ivec.

#[global] Infix "<$>" := ivec_map (at level 61, left associativity) : ivec_scope.
#[global] Infix "++" := iapp (at level 60, right associativity) : ivec_scope.

(** A telescope inspired notation for [iimpl]. *)
Notation "As -h> B" :=
  (iimpl (λ A, A) As B) (at level 99, B at level 200, right associativity).

(* We call it [hvec] just to distinguish is from the stdpp's [hlist]. We
 * parameterize [hvec] by a type [A], a length, and a list of [A]. *)
Inductive hvec : forall (n : nat), ivec' Type n → Type :=
  | hnil : hvec 0 []%IL
  | hcons {n x} {As : ivec' Type n} : x → hvec n As → hvec (S n) (x :: As)%IL.

Arguments hcons {_ _ _} a l.

Derive Signature NoConfusion NoConfusionHom for hvec.
Derive Subterm for hvec.

Declare Scope hvec_scope.
Bind Scope hvec_scope with hvec.
Delimit Scope hvec_scope with HV.

Global Infix "::" := hcons (at level 60, right associativity) : hvec_scope.
Global Notation "[ ] " := hnil : hvec_scope.
Global Notation "[ x ] " := (hcons x hnil) : hvec_scope.
Global Notation "[ x ; .. ; y ] " := (hcons x .. (hcons y hnil) ..) : hvec_scope.

Section hvec.
  Fixpoint happ {n m} {As : ivec n Type} {Bs : ivec m Type}
      (xs : hvec n As) (ys : hvec m Bs) : hvec (n + m) (iapp As Bs) :=
    match xs with hnil => ys | hcons x xs => hcons x (happ xs ys) end.

  Definition hhead {n a As} (xs : hvec (S n) (a :: As)) : a :=
    match xs with hnil => () | hcons x _ => x end.
  Definition htail {n a As} (xs : hvec (S n) (a :: As)) : hvec n As :=
    match xs with hnil => () | hcons _ xs => xs end.

  Fixpoint hheads {n m As} {Bs : ivec m Type} :
      hvec (n + m) (As ++ Bs) → hvec n As :=
    match As with
    | inil => λ _, hnil
    | icons _ _ => λ xs, hcons (hhead xs) (hheads (htail xs))
    end.
  Fixpoint htails {n m} {As : ivec n Type} {Bs : ivec m Type} : hvec (n + m) (iapp As Bs) → hvec m Bs :=
    match As with
    | inil => id
    | icons _ _ => λ xs, htails (htail xs)
    end.

  Definition hinit {B} (y : B) : iimpl id inil B := y.
  Definition hlam {n x} {As : ivec n Type} {B}
    (f : x → iimpl id As B) : iimpl id (icons x As) B := f.
  Global Arguments hlam _ _ _ _ _ _ / : assert.

  Equations huncurry {n} {As B} (f : iimpl id As B) (xs : hvec n As) : B :=
  | f, hnil => f
  | f, hcons xx xs => huncurry (f xx) xs.
  Global Transparent huncurry.

  Coercion huncurry : iimpl >-> Funclass.

  Fixpoint hcurry {n} {As B} : (hvec n As → B) → iimpl id As B :=
    match As with
    | inil => λ f, f []%HV
    | icons x xs => λ f, hlam (λ x, hcurry (f ∘ hcons x))
    end.

  Lemma huncurry_curry {n As B} (f : hvec n As → B) xs :
    huncurry (hcurry f) xs = f xs.
  Proof. by induction xs as [|n ? As x xs IH]; simpl; rewrite ?IH. Qed.

  Fixpoint hcompose {n} {As : ivec n Type} {B C} (f : B → C) {struct As} :
      iimpl id As B → iimpl id As C :=
    match As with
    | inil => f
    | icons A As => λ g, hlam (λ x, hcompose f (g x))
    end.

  (* Compute (icons nat (icons bool (icons (fin 0) inil))) !!! 1%fin. *)

  Equations hvec_lookup {n As} (l : hvec n As) (i : fin n) : As !!! i :=
    hvec_lookup (xx :: _) 0%fin := xx ;
    hvec_lookup (_ :: xs) (FS i') := hvec_lookup xs i'.
  Global Transparent hvec_lookup.

  (** Turns a function over [fin n] into an [hvec] of length [n]. *)
  Equations fun_to_hvec {n A} F (As : ivec n A)
    (f : ∀ (i : fin n), F (As !!! i)) : hvec n (F <$> As) :=
  | _, inil, _ => []
  | _, icons A' As', f =>
      hcons (f 0%fin : F A') (fun_to_hvec F As' (λ i, f (FS i))).
  Global Transparent fun_to_hvec.

  Lemma fun_ex_to_ex_hvec {n} (As : ivec n Type) (P : ∀ i (x : (As !!! i)), Prop) :
    (∀ (i : fin n), ∃ (x : (As !!! i)), P i x) →
    (∃ (xs : hvec n As), (∀ i, P i (hvec_lookup xs i))).
  Proof.
    intros ?.
    induction n.
    - dependent elimination As.
      exists []%HV.
      intros i.
      dependent elimination i.
    - dependent elimination As as [icons a As'].
      edestruct IHn as (xs & allP).
      { intros i. destruct (H (FS i)). exists x. apply H0. }
      destruct (H 0%fin) as (x & xP).
      exists (x :: xs)%HV.
      intros i.
      dependent elimination i as [0%fin | FS ii].
      * apply xP.
      * apply allP.
  Qed.

  (* Equations hvec_map {G n As} (f : ∀ x, F x → G x) (l : hvec F n As) : hvec G n As := *)
  (* | f, hnil => hnil *)
  (* | f, hcons xx xs => hcons (f _ xx) (hvec_map f xs). *)

  Equations hvec_lookup_fmap {n A F} {As : ivec n A}
    (l : hvec n (F <$> As)) (i : fin n) : F (As !!! i) :=
    @hvec_lookup_fmap _ _ _ (_ :: _) (xx :: _) 0%fin := xx ;
    @hvec_lookup_fmap _ _ _ (_ :: _) (_ :: xs) (FS i') := hvec_lookup_fmap xs i'.

  Lemma hvec_lookup_fmap_eq {n A F As} (l : hvec n (F <$> As)) i :
    hvec_lookup l i =
      eq_rect _ id (hvec_lookup_fmap (A := A) l i) _ (ivec_lookup_fmap _ _ _).
  Proof.
    induction As as [|??? IH]. { inversion i. }
    dependent elimination l.
    dependent elimination i.
    { simpl. done. }
    apply IH.
  Qed.

  Equations hvec_lookup_to_vec_involution A F n (As : ivec n A) f i :
    (hvec_lookup_fmap (fun_to_hvec F As f)) i = f i :=
  hvec_lookup_to_vec_involution _ _ _ (_ :: _) f 0%fin => eq_refl ;
  hvec_lookup_to_vec_involution _ _ n1 (_ :: As') f (FS i) =>
    hvec_lookup_to_vec_involution _ _  n1 As' (λ i, f (FS i)) i.

  Lemma fun_ex_to_ex_hvec_fmap {n A F} (As : ivec n A) (P : ∀ i (x : F (As !!! i)), Prop) :
    (∀ (i : fin n), ∃ (x : F (As !!! i)), P i x) →
    (∃ (xs : hvec n (F <$> As)), (∀ i, P i (hvec_lookup_fmap xs i))).
  Proof.
    (* NOTE: This proof is copy pasted from the non-fmap version. This was
     * easier than reusing the other lemma. *)
    intros ?.
    induction n.
    - dependent elimination As.
      exists []%HV.
      intros i.
      dependent elimination i.
    - dependent elimination As as [icons a As'].
      edestruct IHn as (xs & allP).
      { intros i. destruct (H (FS i)). exists x. apply H0. }
      destruct (H 0%fin) as (x & xP).
      exists (x :: xs)%HV.
      intros i.
      dependent elimination i as [0%fin | FS ii].
      * apply xP.
      * apply allP.
  Qed.

  (* Alternative proof of the above using tactics and [dependent elimination]
  * instead of dependent pattern matching. *)
  (* Lemma hvec_lookup_to_vec_involution' {n} {As : ivec n A} l i : *)
  (*   (hvec_lookup (fun_to_hvec As l)) i = l i. *)
  (* Proof. *)
  (*   induction As. *)
  (*   { dependent elimination i. } *)
  (*   dependent elimination i. *)
  (*   - simp fun_to_hvec hvec_lookup. done. *)
  (*   - specialize (IHAs (λ i, l (FS i)) t). *)
  (*     apply IHAs. *)
  (* Qed. *)

End hvec.

#[global] Infix "👀" := hvec_lookup (at level 20).
