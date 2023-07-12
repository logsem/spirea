From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import csum excl auth dfrac.
From iris.algebra Require Import csum excl auth dfrac.

(** A good core is one that returns the largest local unit. *)
Definition pcore_good (A : cmra) :=
  ∀ (a : A),
    match pcore a with
    | None =>
        (* [a] has no core and no local units. *)
        ∀ a', ✓ (a ⋅ a') → a ⋅ a' ≢ a
    | Some pa =>
        (* [a] has a core and it is the greatest local units. *)
        ∀ a', ✓ (a ⋅ a') → (a ⋅ a' ≡ a) → a' ≡ pa ∨ a' ≼ pa
    end.

    (* (* [a] has no core and no local units. *) *)
    (* (pcore a = None ∧ (∀ a', ✓ (a ⋅ a') → a ⋅ a' ≢ a)) ∨ *)
    (* (* [a] has a core and it is the greatest local units. *) *)
    (* (∃ pa, pcore a = Some pa ∧ *)
    (*   (∀ a', ✓ (a ⋅ a') → (a ⋅ a' ≡ a) → a' ≡ pa ∨ a' ≼ pa)). *)

(** When the core is total we can simplify the requirement. *)
Definition core_good (A : cmra) :=
  ∀ (a : A), (∀ a', ✓ (a ⋅ a') → a ⋅ a' ≡ a → a' ≼ core a).

Lemma pcore_good_to_core_good {A : cmra} `{CmraTotal A} :
  pcore_good A ↔ core_good A.
Proof.
  split.
  - intros Hi a a' eq.
    specialize (Hi a).
    destruct (pcore a) as [|pa] eqn:eq'.
    2: { rewrite cmra_pcore_core in eq'. inversion eq'. }
    admit.
  - admit.
Admitted.

Lemma qp_add_neq q p : (q + p ≠ q)%Qp.
Proof.
  intros Heq. eapply (Qp.not_add_le_l q p). rewrite Heq //.
Qed.

Lemma dfrac_pcore_good : pcore_good dfrac.
Proof.
  intros [?| |?]; simpl.
  - intros [?| |?] ?; try done.
    rewrite dfrac_op_own.
    intros [= ?%qp_add_neq ]. done.
  - intros [?| |?]; try done. intros ?. left. done.
  - intros [?| |?] ?; try naive_solver.
    + inversion 1. apply qp_add_neq in H2. done.
    + inversion 1. apply qp_add_neq in H2. done.
Qed.

Lemma excl_pcore_good {A} : pcore_good (exclR A).
Proof.
  intros [?|].
  - intros [?|] ?; inversion 1.
  - intros [?|]; inversion 1.
Qed.

Lemma option_pcore_good {A} : pcore_good A → pcore_good (option A).
Proof.
  intros Hi.
  apply pcore_good_to_core_good.
  unfold core_good.
  intros [a|] [a'|] Hval eq; try naive_solver.
  - inversion eq as [? ? eqA|]. specialize (Hi a).
    destruct (pcore a) as [pa|] eqn:eq'.
    2: { specialize (Hi a' Hval). done. }
    unfold core. simpl.
    rewrite eq'.
    specialize (Hi _ Hval eqA) as [->|incl]; first done.
    apply Some_included_2.
    apply incl.
  - replace None with (ε : option A) by done.
    apply ucmra_unit_least.
  - inversion eq.
Qed.

Lemma agree_pcore_good {A} : pcore_good (agreeR A).
Proof.
  intros a. simpl.
  intros a' val eq1.
  right. apply agree_included. rewrite -{1}eq1 comm. done.
Qed.

Lemma prod_pcore_good {A B} :
  pcore_good A → pcore_good B → pcore_good (prodR A B).
Proof.
  unfold pcore_good.
  intros Ha Hb [a b].
  specialize (Ha a). specialize (Hb b).

  unfold pcore, cmra_pcore. simpl. unfold prod_pcore_instance. simpl.
  destruct (pcore a) as [pa|].
  2: { simpl. intros [a2 b2] [??] [??]. simpl in *. eapply Ha; done. }
  simpl.
  destruct (pcore b) as [pb|].
  2: { simpl. intros [a2 b2] [??] [??]. simpl in *. eapply Hb; done. }
  simpl.
  intros [a2 b2] [??] [??]. simpl in *.
  edestruct Ha as [?|?].
Admitted.

Lemma prod_core_good {A B} `{CmraTotal A, CmraTotal B} :
  core_good A → core_good B → core_good (prodR A B).
Proof. rewrite -!pcore_good_to_core_good. apply prod_pcore_good. Qed.

Lemma view_valid {A : ofe} {B : ucmra} a (f : B) (rel : view_rel A B) :
  ✓ (View a f : view rel) → ✓ a ∧ ✓ f.
Proof.
  rewrite view.view_valid_eq. simpl.
  destruct a as [[??]|]; simpl.
  - intros [Hfv H].
    split.
    + split; first done. simpl.
      intros ?.
      specialize (H n) as (? & ? & ?).
      rewrite H.
      done.
    + apply cmra_valid_validN.
      intros ?.
      specialize (H n) as [? H].
      eapply view_rel_validN.
      apply H.
  - intros ?. split; first done.
    apply cmra_valid_validN.
    intros ?.
    specialize (H n) as [? H].
    eapply view_rel_validN.
    apply H.
Qed.

Lemma view_pcore_good A (B : ucmra) rel : pcore_good B → pcore_good (@viewR A B rel).
Proof.
  intros Hg%pcore_good_to_core_good.
  apply pcore_good_to_core_good.
  intros [a1 f1] [a2 f2] [??]%view_valid.
  inversion 1 as [eq ?]. simpl in *.
  rewrite view.view_core_eq. simpl.
  destruct (Hg f1 f2) as [fp2 ->]; [done|done| ].
  specialize (option_pcore_good (prod_pcore_good dfrac_pcore_good (agree_pcore_good (A := A)))) as Hg2.
  apply pcore_good_to_core_good in Hg2.
  destruct (Hg2 a1 a2) as [ap2 ->]; [done|done| ].
  exists (View ap2 fp2).
  done.
Qed.

(** A good cmra is one where every element has either no local unit or one
 * greatest local unit. *)
Definition good_cmra (A : cmra) : Prop :=
  ∀ (a : A) (au1 au2 : A),
    a ⋅ au1 ≡ a → a ⋅ au2 ≡ a → (* [au1] and [au2] are two local units *)
    (au1 ≡ au2 ∨ au1 ≼ au2 ∨ au2 ≼ au1).

Class SaneCmra (A : cmra) := {
  has_largest_core :
    ∀ (a : A),
      (* [a] has one largest local unit *)
      {pa : A |
        ✓ (a ⋅ pa) ∧ pa ⋅ a ≡ a ∧
        ∀ pa', ✓ (a ⋅ pa') → pa' ⋅ a ≡ a → pa ≡ pa' ∨ pa' ≼ pa
      } +
      (* [a] has no local unit *)
      {∀ a', ✓ (a ⋅ a') → a ⋅ a' ≢ a}
}.

Definition ucore `{!SaneCmra A} (a : A) : option A :=
  match has_largest_core a with
  | inleft (exist _ pa _) => Some pa
  | inright _ => None
  end.

Section ucore.
  Context `{!SaneCmra A}.

  Lemma ucore_unit (x : A) cx :
    ucore x = Some cx → cx ⋅ x ≡ x.
  Proof.
    unfold ucore.
    destruct (has_largest_core x) as [(pa & ? & ? & ?)|]; last done.
    intros [= <-]. done.
  Qed.

  Lemma ucore_idemp (x cx : A) :
    ucore x = Some cx → ucore cx ≡ Some cx.
  Proof.
    unfold ucore.
    destruct (has_largest_core x) as [(pa & ? & ? & ?)|]; last done.
    intros [= <-].
    destruct (has_largest_core pa) as [(ppa & ? & ? & ?)|]; simpl.
    - f_equiv.
      assert (ppa ⋅ x ≡ x) as eq.
      { rewrite -{1}H0. rewrite assoc. rewrite H3. done. }
      (* rewrite -H3 in H0. *)
      destruct (H1 ppa); [ |done| | ].
      { rewrite comm. rewrite eq. rewrite -H0. rewrite comm. done. }
      + done.
      + admit.
    - 
  Admitted.

End ucore.
