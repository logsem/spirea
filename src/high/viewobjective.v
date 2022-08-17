From iris.bi Require Export monpred.
From iris.proofmode Require Import monpred tactics.
From iris.base_logic.lib Require Import iprop.

From self.high Require Import dprop dprop_liftings.

Program Definition monPred_view_objectively_def {Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ i, ∀ TV, P (TV, i.2))%I _.
Next Obligation.
  intros.
  intros [? gnames].
  introsIndex ? ?.
  naive_solver.
Qed.
Definition monPred_view_objectively_aux : seal (@monPred_view_objectively_def).
Proof. by eexists. Qed.
Definition monPred_view_objectively :=
  monPred_view_objectively_aux.(unseal).
Definition monPred_view_objectively_eq : @monPred_view_objectively = _ :=
  monPred_view_objectively_aux.(seal_eq).

Global Arguments monPred_view_objectively {_} _%I.

Notation "'<vobj>' P" := (monPred_view_objectively P) (at level 20, right associativity) : bi_scope.

(* Expresses that a proposition holds independently of the thread view but may
   still depend on the ghost names. *)
Class ViewObjective {Σ} (P : dProp Σ) :=
  view_objective_at TV1 TV2 gnames : P (TV1, gnames) -∗ P (TV2, gnames).
Global Arguments ViewObjective {_} _%I.
Global Arguments view_objective_at {_} _%I {_}.
Global Hint Mode ViewObjective + ! : typeclass_instances.
Global Instance: Params (@Objective) 1 := {}.

Section view_objective_instances.
  Context {Σ : gFunctors}.

  Implicit Types (P : dProp Σ).
  Implicit Types (Pi : iProp Σ).

  Lemma monPred_objectively_unfold :
    monPred_view_objectively = λ P, lift_d (λ nD, ∀ TV, P (TV, nD))%I.
  Proof.
    rewrite monPred_view_objectively_eq.
    rewrite /monPred_view_objectively_def.
    simpl.
  Admitted.

  Lemma view_objective_objective P : Objective P → ViewObjective P.
  Proof.
    rewrite /Objective.
    rewrite /ViewObjective.
    naive_solver.
  Qed.

  Global Instance embed_objective (P : iProp Σ) : ViewObjective (⎡ P ⎤ : dProp Σ)%I.
  Proof.
    rewrite /ViewObjective.
    setoid_rewrite monPred_at_embed.
    naive_solver.
  Qed.

  Global Instance with_gnames_view_objective (P : nvmDeltaG → dProp Σ) :
    (∀ gnames, ViewObjective (P gnames)) → ViewObjective (with_gnames P).
  Proof.
    rewrite /ViewObjective.
    intros Ho.
    iIntros.
    iApply Ho.
    iFrame.
  Qed.

  Lemma monPred_at_view_objectively i P : (<vobj> P) i ⊣⊢ ∀ TV, P (TV, i.2).
  Proof. by rewrite monPred_view_objectively_eq. Qed.

  Lemma view_objective_view_objectively P `{!ViewObjective P} : P ⊢ <vobj> P.
  Proof.
    iModel.
    rewrite monPred_at_view_objectively.
    simpl.
    iIntros "H" (?).
    iApply view_objective_at.
    done.
  Qed.

  Global Instance embed_view_objective Pi : ViewObjective ⎡ Pi ⎤.
  Proof. apply view_objective_objective. apply _. Qed.
  Global Instance pure_view_objective φ : ViewObjective (⌜ φ ⌝ : dProp Σ)%I.
  Proof. apply view_objective_objective. apply _. Qed.
  Global Instance emp_view_objective : ViewObjective (emp : dProp Σ)%I.
  Proof. apply view_objective_objective. apply _. Qed.
  Global Instance objectively_view_objective P : ViewObjective (<vobj> P).
  Proof. rewrite monPred_view_objectively_eq. done. Qed.

  Global Instance and_view_objective P Q `{!ViewObjective P, !ViewObjective Q} : ViewObjective (P ∧ Q).
  Proof.
    iIntros (i j ?).
    rewrite 2!monPred_at_and. rewrite 2!(view_objective_at _ i j).
    done.
  Qed.
  Global Instance or_view_objective P Q `{!ViewObjective P, !ViewObjective Q} : ViewObjective (P ∨ Q).
  Proof.
    intros i j ?. rewrite 2!monPred_at_or. rewrite 2!(view_objective_at _ i j). done.
  Qed.
  (* Global Instance impl_view_objective P Q `{!ViewObjective P, !ViewObjective Q} : ViewObjective (P → Q). *)
  (* Proof. *)
  (*   intros i j. unseal. rewrite (bi.forall_elim i) bi.pure_impl_forall. *)
  (*   rewrite bi.forall_elim //. apply bi.forall_intro=> k. *)
  (*   rewrite bi.pure_impl_forall. apply bi.forall_intro=>_. *)
  (*   rewrite (objective_at Q i). by rewrite (objective_at P k). *)
  (* Qed. *)
  Global Instance forall_view_view_objective (A : Type) (Φ : A → dProp Σ) :
    (∀ x : A, ViewObjective (Φ x)) → ViewObjective (∀ x : A, Φ x).
  Proof.
    iIntros (????).
    rewrite 2!monPred_at_forall.
    iIntros "?" (?).
    iApply view_objective_at.
    iAssumption.
  Qed.
  (* Global Instance exists_view_objective {A} Φ {H : ∀ x : A, ViewObjective (Φ x)} : *)
  (*   @ViewObjective I PROP (∃ x, Φ x)%I. *)
  (* Proof. intros i j. unseal. do 2 f_equiv. by apply objective_at. Qed. *)

  (* Global Instance sep_view_objective P Q `{!ViewObjective P, !ViewObjective Q} : ViewObjective (P ∗ Q). *)
  (* Proof. intros i j. unseal. by rewrite !(objective_at _ i j). Qed. *)
  Global Instance sep_view_objective P Q :
    ViewObjective P → ViewObjective Q → ViewObjective (P ∗ Q).
  Proof.
    intros ? ? i j ?.
    rewrite 2!monPred_at_sep. rewrite 2!(view_objective_at _ i j).
    done.
  Qed.

  Global Instance wand_view_objective P Q `{!ViewObjective P, !ViewObjective Q} : ViewObjective (P -∗ Q).
  Proof.
    iIntros (i j ?) "w".
    introsIndex ? ?.
    rewrite (view_objective_at _ p i).
    iIntros "P".
    iSpecialize ("w" with "P").
    rewrite (view_objective_at Q i p).
    done.
  Qed.
  (* Global Instance persistently_view_objective P `{!ViewObjective P} : ViewObjective (<pers> P). *)
  (* Proof. intros i j. unseal. by rewrite objective_at. Qed. *)

  (* Global Instance affinely_view_objective P `{!ViewObjective P} : ViewObjective (<affine> P). *)
  (* Proof. rewrite /bi_affinely. apply _. Qed. *)
  (* Global Instance intuitionistically_view_objective P `{!ViewObjective P} : ViewObjective (□ P). *)
  (* Proof. rewrite /bi_intuitionistically. apply _. Qed. *)
  (* Global Instance absorbingly_view_objective P `{!ViewObjective P} : ViewObjective (<absorb> P). *)
  (* Proof. rewrite /bi_absorbingly. apply _. Qed. *)
  (* Global Instance persistently_if_view_objective P p `{!ViewObjective P} : ViewObjective (<pers>?p P). *)
  (* Proof. rewrite /bi_persistently_if. destruct p; apply _. Qed. *)
  (* Global Instance affinely_if_view_objective P p `{!ViewObjective P} : ViewObjective (<affine>?p P). *)
  (* Proof. rewrite /bi_affinely_if. destruct p; apply _. Qed. *)
  (* Global Instance absorbingly_if_view_objective P p `{!ViewObjective P} : ViewObjective (<absorb>?p P). *)
  (* Proof. rewrite /bi_absorbingly_if. destruct p; apply _. Qed. *)
  (* Global Instance intuitionistically_if_view_objective P p `{!ViewObjective P} : ViewObjective (□?p P). *)
  (* Proof. rewrite /bi_intuitionistically_if. destruct p; apply _. Qed. *)

End view_objective_instances.
