From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.program_logic Require Import staged_invariant post_expr crash_weakestpre.
From Perennial.base_logic.lib Require Import saved_prop.
From Perennial.Helpers Require Import Qextra.

(* Notation: copied from iris bi/weakestpre.v *)
Class Wpc (Λ : language) (PROP A : Type) :=
  wpc : A → coPset → expr Λ → (val Λ → PROP) → PROP → PROP.
Arguments wpc {_ _ _ _} _ _ _%E _%I _%I.
Instance: Params (@wpc) 9 := {}.

(* Instance wpc' `{!irisGS Λ Σ, !generationGS Λ Σ} : Wpc Λ (iProp Σ) stuckness := wpc_aux.(unseal). *)
Instance wpc' `{!irisGS Λ Σ, !generationGS Λ Σ} : Wpc Λ (iProp Σ) stuckness :=
  crash_weakestpre.wpc.

(** Notations for partial crash weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WPC' e @ s ; E1 {{ Φ } } {{ Φc } }" := (wpc s E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e @ E1 {{ Φ } } {{ Φc } }" := (wpc NotStuck E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Notation "'WPC' e {{ Φ } } {{ Φc } }" := (wpc NotStuck ⊤ e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.

(** Notations with binder.  *)
Notation "'WPC' e @ s ; E1 {{ v , Q } } {{ R } }" := (wpc s E1 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[hv' 'WPC'  e  '/' @  '[' s ;  E1  ']' '/' {{  '[' v ,  '/' Q  ']' } }  '/' {{  '[' R  ']' } } ']'") : bi_scope.
Notation "'WPC' e @ E1 {{ v , Q } } {{ R } }" := (wpc NotStuck E1 e%E (λ v, Q) R)
  (at level 20, e, Q, R at level 200,
   format "'[hv' 'WPC'  e  '/' @  '[' E1  ']' '/' {{  '[' v ,  '/' Q  ']' } }  '/' {{  '[' R  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc,
      P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  E1  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc,
      P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ E1 {{ Φ }} {{ Φc }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' E1  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.

(*
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  x  ..  y ,   RET  pat ;  Q  } } } ']'") : bi_scope.
*)

Notation "'{{{' P } } } e @ s ; E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' s ;  E1  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (□ ∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ E1 {{ Φ }} {{ Φc }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' E1  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } }  '/' {{{  '[' Qc  ']' } } } ']'") : bi_scope.
(*
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  E  ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' ? {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
*)

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ s ; E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E1 {{{ x .. y , 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPC e @ E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
(*
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }}) : stdpp_scope.
*)
Notation "'{{{' P } } } e @ s ; E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ s; E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
Notation "'{{{' P } } } e @ E1 {{{ 'RET' pat ; Q } } } {{{ Qc } } }" :=
  (∀ Φ Φc, P -∗ (Qc -∗ Φc) ∧ ▷ (Q -∗ Φ pat%V) -∗ WPC e @ E1 {{ Φ }} {{ Φc }}) : stdpp_scope.
