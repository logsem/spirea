From Equations Require Import Equations.
From stdpp Require Import finite.

From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From iris_named_props Require Import named_props.

From self Require Import hvec extra basic_nextgen_modality cmra_morphism_extra
  gen_single_shot gen_pv.
From self Require Import generation_update_next.
From self.nextgen Require Import types omega generational_cmra transmap promise.

Import uPred.

Equations forall_fin_2 (P : fin 2 → Type) : P 0%fin * P 1%fin → ∀ (i : fin 2), P i :=
| P, p, 0%fin => fst p
| P, p, 1%fin => snd p.

(* This is a hacky way to find all the [genInSelfG] instances when there are
exactly two dependencies. It would be nicer with a solution that could iterate
over all the dependencies during type class resolution (maybe inspired by
[TCForall] for lists). *)
Global Instance genInG_forall_2 {Σ n m} {Ω} {A B} {DS1 : ivec n cmra} {DS2 : ivec m cmra}
  (g1 : genInG Σ Ω A DS1) (g2 : genInG Σ Ω B DS2) :
  ∀ (i : fin 2), genInSelfG Σ Ω ([A; B]%IL !!! i).
Proof.
  intros i.
  dependent elimination i as [Fin.F1|FS i].
  dependent elimination i as [Fin.F1|FS i].
  dependent elimination i.
Defined.

(* Two lemmas to check that the weird definition above does what it is supposed to. *)
Lemma genInG_forall_2_lookup_1 {Σ n m} {A B} {DS1 : ivec n cmra} {DS2 : ivec m cmra}
  `{g1 : !genInG Σ Ω A DS1} `{g2 : !genInG Σ Ω B DS2} :
  genInG_forall_2 g1 g2 0%fin =
    (genInG_genInSelfG g1).
Proof. done. Qed.

Lemma genInG_forall_2_lookup_2 {Σ n m} {A B} {DS1 : ivec n cmra} {DS2 : ivec m cmra}
  `{g1 : !genInG Σ Ω A DS1} `{g2 : !genInG Σ Ω B DS2} :
  genInG_forall_2 g1 g2 1%fin =
    (genInG_genInSelfG g2).
Proof. done. Qed.

Section test.
  Context `{max_i : !genInG Σ Ω max_natR [] }.
  Context `{unit_i : !genInG Σ Ω unitR [] }.
  Context `{i : !genInDepsG Σ Ω max_natR [max_natR; unitR] }.

  Lemma test :
    ⊢ ⚡==> ⌜ (2 + 2 = 4)%nat ⌝.
  Proof using i. iModIntro. done. Qed.

End test.

Definition myΣ : gFunctors := #[
  GFunctor (generational_cmraR max_natR []);
  GFunctor (generational_cmraR unitR []);
  GFunctor (generational_cmraR max_natR [max_natR; unitR])
].

Set Printing Coercions.
Print myΣ.

Ltac dep_inv_fin idx :=
  let H := fresh in
  let T := type of idx in
  match eval hnf in T with
  | fin ?n =>
    match eval hnf in n with
    | 0 => inversion idx
    | 1 => dependent elimination idx as [Fin.F1]
    | S ?n => dependent elimination idx as [Fin.F1 | FS H];
              last rename H into idx
    end
  end.

(* Destruct a finite number as much a possible. *)
Ltac destruct_fin i1 := repeat (dep_inv_fin i1).

Ltac solve_gid_uniq :=
  intros i1 i2 neq;
  destruct_fin i1;
  destruct_fin i2; done.

Ltac solve_omega_wf :=
  intros idx dIdx look;
  destruct_fin idx;
  destruct_fin dIdx;
  done.

Program Definition myΩ : gGenCmras myΣ := {|
  gc_len := 3;
  gc_map := λ (i : fin 3), _;
|}.
Next Obligation.
  intros idx.
  dependent elimination idx as [Fin.F1 | FS idx].
  { apply {|
      gcd_cmra := max_natR;
      gcd_n := 0;
      gcd_deps := inil;
      gcd_deps_ids := inil;
      gcd_gid := (0%fin : gid myΣ);
      gcd_cmra_eq := eq_refl;
    |}. }
  dependent elimination idx as [Fin.F1 | FS idx].
  { apply {|
      gcd_cmra := unitR;
      gcd_n := 0;
      gcd_deps := inil;
      gcd_deps_ids := inil;
      gcd_gid := (1%fin : gid myΣ);
      gcd_cmra_eq := eq_refl;
    |}. }
  apply {|
      gcd_cmra := max_natR;
      gcd_n := 2;
      gcd_deps := [max_natR; unitR];
      gcd_deps_ids := [0%fin; 1%fin];
      gcd_gid := (2%fin : gid myΣ);
      gcd_cmra_eq := eq_refl;
    |}.
Defined.
Next Obligation. solve_omega_wf. Qed.
Next Obligation. solve_gid_uniq. Qed.

Instance subG_raΣ_1 : genInG myΣ myΩ max_natR [].
Proof. eapply (GenInG 0 myΣ myΩ max_natR [] 0%fin eq_refl); done. Defined.

Instance subG_raΣ_2 : genInG myΣ myΩ unitR [].
Proof. eapply (GenInG 0 myΣ myΩ unitR [] 1%fin eq_refl); done. Defined.

Instance subG_raΣ_3 : genInG myΣ myΩ max_natR [max_natR; unitR].
Proof. eapply (GenInG _ myΣ myΩ _ _ 2%fin eq_refl); done. Defined.

(* NOTE: If we don't supply [gs] manually here then Coq infers [subG_raΣ_3] for
 * the second instance which is horrible. *)
Instance subG_raΣ_3_deps : genInDepsG (gs := genInG_forall_2 subG_raΣ_1 subG_raΣ_2) myΣ myΩ max_natR [max_natR; unitR].
Proof.
  (* set (gs := genInG_forall_2 subG_raΣ_1 subG_raΣ_2). *)
  eapply (GenDepsInG _ myΣ myΩ max_natR _).
  intros i. destruct_fin i.
  - done.
  - done.
Qed.

(* Instance subG_raΣ {Σ} : subG myΣ Σ → inG Σ (generational_cmraR max_natR []). *)
(* Proof. solve_inG. Qed. *)

(* Instance subG_raΣ_max {Σ} : subG myΣ Σ → inG Σ (generational_cmraR unitR []). *)
(* Proof. solve_inG. Qed. *)

(* Instance subG_raΣ_3 {Σ} : *)
(*   subG myΣ Σ → inG Σ (generational_cmraR unitR [max_natR; unitR]). *)
(* Proof. solve_inG. Qed. *)

From iris.base_logic Require Export bi.

Lemma closed_proof :
  2 + 2 = 4.
Proof.
  specialize (@test myΣ myΩ _ _ subG_raΣ_3_deps).
  intros H.
  apply nextgen_plain_soundness in H; last apply _.
  apply (pure_soundness (M := iResUR myΣ)).
  apply H.
Qed.
