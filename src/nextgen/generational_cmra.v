From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import classes tactics.

From self Require Import hvec extra cmra_morphism_extra gen_single_shot gen_pv.
From self.nextgen Require Import types.

Import EqNotations. (* Get the [rew] notation. *)

Local Infix "*R*" := prodR (at level 50, left associativity).
Local Infix "*UR*" := prodUR (at level 50, left associativity).

Section dependency_relation_cmra.
  Context {n : nat}.

  Canonical Structure pred_overO (A : cmra) :=
    leibnizO (pred_over A).
  Canonical Structure rel_overO (DS : ivec n cmra) (A : cmra) :=
    leibnizO (rel_over DS A).

End dependency_relation_cmra.

Definition mono_list (A : ofe) : Type := auth (max_prefix_listUR A).

Record generational_cmra {n} (A : cmra) (DS : ivec n cmra) : Type := MkGen {
  (* Agreement on transformation into generation *)
  gc_in : optionR (agreeR (leibnizO (A → A)));
  (* Facilitates choice of transformation out of generation *)
  gc_single_shot : GTSR (A → A);
  (* Ownership over A *)
  gc_elem : option A;
  (* Gname of dependencies - we don't need to store their [gid] as that is static. *)
  gc_deps : option (agree (leibnizO (list gname)));
  (* List of promised relations. *)
  gc_promises_rel : gen_pv (mono_list (rel_overO DS A));
  (* List of promised predicates. *)
  gc_promises_pred : gen_pv (mono_list (pred_overO A));
}.

Arguments MkGen {_ _ _} _.
Arguments gc_in {_ _ _}.
Arguments gc_single_shot {_ _ _}.
Arguments gc_elem {_ _ _}.
Arguments gc_deps {_ _ _}.
Arguments gc_promises_rel {_ _ _}.
Arguments gc_promises_pred {_ _ _}.

Local Instance gen_cmra_dist {n} {A : cmra} (DS : ivec n cmra) : Dist (generational_cmra A DS) :=
  λ n a b,
    gc_in a ≡{n}≡ gc_in b ∧
    gc_single_shot a ≡{n}≡ gc_single_shot b ∧
    gc_elem a ≡{n}≡ gc_elem b ∧
    gc_deps a ≡{n}≡ gc_deps b ∧
    gc_promises_rel a ≡{n}≡ gc_promises_rel b ∧
    gc_promises_pred a ≡{n}≡ gc_promises_pred b.

Section cmra.
  Context {n : nat} (A : cmra) (DS : ivec n cmra).

  #[global]
  Instance gen_cmra_equiv : Equiv (generational_cmra A DS) :=
    λ a b,
      gc_in a ≡ gc_in b ∧
      gc_single_shot a ≡ gc_single_shot b ∧
      gc_elem a ≡ gc_elem b ∧
      gc_deps a ≡ gc_deps b ∧
      gc_promises_rel a ≡ gc_promises_rel b ∧
      gc_promises_pred a ≡ gc_promises_pred b.

  #[global]
  Instance mk_gen_proper :
    Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) MkGen.
  Proof. repeat intros ?. done. Qed.

  Definition generational_cmra_ofe_mixin : OfeMixin (generational_cmra A DS).
  Proof.
    split.
    - intros [??????] [??????].
      unfold equiv, gen_cmra_equiv, dist, gen_cmra_dist. simpl.
      rewrite 6!equiv_dist.
      naive_solver.
    - intros ?. split.
      + done.
      + intros [??????] [??????] (? & ? & ? & ? & ? & ?). done.
      + intros [??????] [??????] [??????]
          (? & ? & ? & ? & ? & ?) (? & ? & ? & ? & ? & ?).
        split_and!; etrans; done.
    - intros ?? [??????] [??????] (? & ? & ? & ? & ? & ?) ?. simpl in *.
      split_and!; eapply dist_lt; done.
  Qed.
  Canonical Structure generational_cmraO := Ofe (generational_cmra A DS) generational_cmra_ofe_mixin.

  Local Instance gen_cmra_valid_instance : Valid (generational_cmra A DS) := λ ma,
    ✓ (gc_in ma) ∧
    ✓ (gc_single_shot ma) ∧
    ✓ (gc_elem ma) ∧
    ✓ (gc_deps ma) ∧
    ✓ (gc_promises_rel ma) ∧
    ✓ (gc_promises_pred ma).

  Local Instance gen_cmra_validN_instance : ValidN (generational_cmra A DS) := λ n ma,
    ✓{n} (gc_in ma) ∧
    ✓{n} (gc_single_shot ma) ∧
    ✓{n} (gc_elem ma) ∧
    ✓{n} (gc_deps ma) ∧
    ✓{n} (gc_promises_rel ma) ∧
    ✓{n} (gc_promises_pred ma).

  Local Instance gen_cmra_pcore_instance : PCore (generational_cmra A DS) := λ ma,
    Some (MkGen
      (core (gc_in ma))
      (core (gc_single_shot ma))
      (core (gc_elem ma))
      (core (gc_deps ma))
      (core (gc_promises_rel ma))
      (core (gc_promises_pred ma))).
  Local Arguments gen_cmra_pcore_instance !_ /.
  Local Instance gen_cmra_op_instance : Op (generational_cmra A DS) :=
    λ a b, MkGen
      (gc_in a ⋅ gc_in b)
      (gc_single_shot a ⋅ gc_single_shot b)
      (gc_elem a ⋅ gc_elem b)
      (gc_deps a ⋅ gc_deps b)
      (gc_promises_rel a ⋅ gc_promises_rel b)
      (gc_promises_pred a ⋅ gc_promises_pred b).

  Lemma gen_cmra_op_eq a a' b b' c c' d d' e e' f f' :
   MkGen a b c d e f ⋅ MkGen a' b' c' d' e' f' =
     MkGen (a ⋅ a') (b ⋅ b') (c ⋅ c') (d ⋅ d') (e ⋅ e') (f ⋅ f').
  Proof. done. Qed.

  Lemma gen_cmra_incl_mono a a' b b' c c' d d' e e' f f' :
    (a ≼ a' ∧ b ≼ b' ∧ c ≼ c' ∧ d ≼ d' ∧ e ≼ e' ∧ f ≼ f') ↔
    MkGen a b c d e f ≼ MkGen a' b' c' d' e' f'.
  Proof.
    split.
    - intros ([a3 ?] & [b3 ?] & [c3 ?] & [d3 ?] & [e3 ?] & [f3 ?]).
      exists (MkGen a3 b3 c3 d3 e3 f3).
      rewrite gen_cmra_op_eq.
      split_and!; simpl; assumption.
    - intros [[??????] ?].
      destruct H as (? & ? & ? & ? & ? & ?). simpl in *.
      split_and!; eexists _; eassumption.
  Qed.

  Lemma generational_cmra_cmra_mixin : CmraMixin (generational_cmra A DS).
  Proof.
    apply cmra_total_mixin.
    - done.
    - intros [??????] ? [??????] [??????].
      rewrite 2!gen_cmra_op_eq /dist /gen_cmra_dist. simpl.
      intros (-> & -> & -> & -> & -> & ->). done.
    - intros ? [??????] [??????].
      unfold core, pcore, gen_cmra_pcore_instance.
      unfold dist, gen_cmra_dist. simpl.
      intros (-> & -> & -> & -> & -> & ->).
      done.
    - intros ? [??????] [??????]. simpl.
      unfold validN, gen_cmra_validN_instance. simpl.
      unfold dist, gen_cmra_dist. simpl.
      intros eq.
      destruct eq as (-> & -> & -> & -> & -> & ->).
      done.
    - intros [??????]. simpl.
      unfold valid, gen_cmra_valid_instance, validN, gen_cmra_validN_instance.
      simpl. rewrite 6!cmra_valid_validN.
      naive_solver.
    - intros ? [??????].
      unfold validN, gen_cmra_validN_instance. simpl.
      intros H; split_and!; apply cmra_validN_S, H.
    - intros [??????] [??????] [??????].
      rewrite 4!gen_cmra_op_eq.
      rewrite 6!assoc. done.
    - intros [??????] [??????]. rewrite 2!gen_cmra_op_eq.
      split_and!; simpl; apply: comm.
    - intros [??????]. rewrite gen_cmra_op_eq. simpl.
      split_and!; simpl; apply cmra_core_l.
    - intros [??????].
      unfold core, pcore, gen_cmra_pcore_instance. simpl.
      split_and!; simpl; apply cmra_core_idemp.
    - intros [??????] [??????].
      unfold core, pcore, gen_cmra_pcore_instance. simpl.
      rewrite -2!gen_cmra_incl_mono.
      intros inc. split_and!; try apply: cmra_core_mono; apply inc.
    - intros ? [??????] [??????]. simpl.
      intros (? & ? & ? & ? & ? & ?). simpl in *.
      split_and!; simpl; eapply cmra_validN_op_l; eassumption.
    - eauto.
      intros n' [a1 a2 a3 a4 a5 a6] [b1 b2 b3 b4 b5 b6] [c1 c2 c3 c4 c5 c6].
      intros (? & ? & ? & ? & ? & ?). simpl in *.
      intros (? & ? & ? & ? & ? & ?). simpl in *.
      Search "cmra" "ext".
      edestruct (cmra_extend n' a1 b1 c1) as (z1 & y1 & ? & ? & ?); [done|done| ].
      edestruct (cmra_extend n' a2 b2 c2) as (z2 & y2 & ? & ? & ?); [done|done| ].
      edestruct (cmra_extend n' a3 b3 c3) as (z3 & y3 & ? & ? & ?); [done|done| ].
      edestruct (cmra_extend n' a4 b4 c4) as (z4 & y4 & ? & ? & ?); [done|done| ].
      edestruct (cmra_extend n' a5 b5 c5) as (z5 & y5 & ? & ? & ?); [done|done| ].
      edestruct (cmra_extend n' a6 b6 c6) as (z6 & y6 & ? & ? & ?); [done|done| ].
      eexists (MkGen _ _ _ _ _ _).
      eexists (MkGen _ _ _ _ _ _).
      rewrite gen_cmra_op_eq.
      split. { split_and!; simpl; eassumption. }
      split. { split_and!; simpl; eassumption. }
      split_and!; simpl; try eassumption.
  Qed.
  Canonical Structure generational_cmraR :=
    Cmra (generational_cmra A DS) generational_cmra_cmra_mixin.

  (* Global Instance generational_cmra_cmra_discrete : CmraDiscrete A → CmraDiscrete (generational_cmraR A DS). *)
  (* Proof. split; [apply _|]. by intros [a|]; [apply (cmra_discrete_valid a)|]. Qed. *)

  Local Instance generational_cmra_unit_instance : Unit (generational_cmra A DS) :=
    MkGen ε ε ε ε ε ε.
    (* MkGen ε. *)
  Lemma generational_cmra_ucmra_mixin : UcmraMixin (generational_cmraR).
  Proof.
    split; [done| |done]. intros [b].
    unfold ε, generational_cmra_unit_instance. simpl.
    simpl.
    rewrite gen_cmra_op_eq.
    rewrite !left_id.
    rewrite (left_id (A := prodUR _ _) _ _ gc_single_shot0).
    done.
  Qed.
  Canonical Structure generational_cmraUR := Ucmra (generational_cmra A DS) generational_cmra_ucmra_mixin.

  #[global]
  Instance gen_cmra_coreid a b c d e f :
    CoreId a → CoreId b → CoreId c → CoreId d → CoreId e → CoreId f →
    CoreId (MkGen (A := A) (DS := DS) a b c d e f).
  Proof. constructor. simpl. rewrite 6!core_id_core. done. Qed.

  Lemma gen_cmra_update a a' b b' c c' d d' e e' f f' :
    a ~~> a' → b ~~> b' → c ~~> c' → d ~~> d' → e ~~> e' → f ~~> f' →
    MkGen a b c d e f ~~> MkGen a' b' c' d' e' f'.
  Proof.
    intros Hf1 Hf2 Hf3 Hf4 Hf5 Hf6.
    intros n' mf.
    specialize (Hf1 n' (gc_in <$> mf)).
    specialize (Hf2 n' (gc_single_shot <$> mf)).
    specialize (Hf3 n' (gc_elem <$> mf)).
    specialize (Hf4 n' (gc_deps <$> mf)).
    specialize (Hf5 n' (gc_promises_rel <$> mf)).
    specialize (Hf6 n' (gc_promises_pred <$> mf)).
    intros (? & ? & ? & ? & ? & ?); simpl in *.
    destruct mf as [[??????]|]; simpl in *; split_and!; naive_solver.
  Qed.

End cmra.

Local Infix "*M*" := prod_map (at level 50, left associativity).

Lemma gen_cmra_unit_least {n} (A : cmra) (DS : ivec n cmra) (a : generational_cmra A DS) :
  ε ≼ a.
Proof. apply: ucmra_unit_least. Qed.

(* (* The generational transformation function for the encoding of each ownership *)
(* over a generational camera. *) *)
(* Definition underlying_trans {n} {A : cmra} {DS : ivec n cmra} *)
(*     (t : A → A) : underlyingR A DS → underlyingR A DS := *)
(*   (const (Some (to_agree t)) : _ → optionR (agreeR (leibnizO (A → A)))) *M* *)
(*   (GTS_floor : (GTSR (A → A)) → (GTSR (A → A))) *M* *)
(*   (fmap t : optionR A → optionR A) *M* *)
(*   id *M* *)
(*   gen_pv_trans *M* *)
(*   gen_pv_trans. *)

(* The generational transformation function for the encoding of each ownership
 * over a generational camera. *)
Definition gen_cmra_trans {n} {A : cmra} {DS : ivec n cmra} (t : A → A) :
    generational_cmra A DS → generational_cmra A DS :=
  λ a, MkGen
    (Some (to_agree t))
    (GTS_floor (gc_single_shot a))
    (fmap t (gc_elem a))
    (gc_deps a)
    (gen_pv_trans (gc_promises_rel a))
    (gen_pv_trans (gc_promises_pred a)).

Section contstructors.
  Context {n : nat}.
  Implicit Types (A : cmra) (DS : ivec n cmra).

  (* Constructors for each of the elements in the pair. *)

  Definition gc_tup_pick_in {A} (DS : ivec n cmra) pick_in : generational_cmraR A DS :=
   MkGen (Some (to_agree (pick_in))) ε ε ε ε ε.

  Definition gc_tup_pick_out {A} (DS : ivec n cmra) pick_out : generational_cmraR A DS :=
   MkGen ε pick_out ε ε ε ε.

  Definition gc_tup_elem {A} (DS : ivec n cmra) a : generational_cmraR A DS :=
   MkGen ε ε (Some a) ε ε ε.

  Definition gc_tup_deps A (DS : ivec n cmra) deps : generational_cmraR A DS :=
   MkGen ε ε ε (Some (to_agree deps)) ε ε.

  Definition gc_tup_promise_list {A} {DS : ivec n cmra} l : generational_cmraR A DS :=
   MkGen ε ε ε ε l ε.

  Definition gc_tup_rel_pred {A} {DS : ivec n cmra} l1 l2 : generational_cmraR A DS :=
   MkGen ε ε ε ε l1 l2.
End contstructors.

Section upred.
  Context {M : ucmra}.
  Context {n : nat} (A : cmra) (DS : ivec n cmra).

  (* Force implicit argument M *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).

  Lemma gen_cmra_validI a b c d e f :
    ✓ (MkGen (A := A) (DS := DS) a b c d e f)
    ⊣⊢@{uPred M} ✓ a ∧ ✓ b ∧ ✓ c ∧ ✓ d ∧ ✓ e ∧ ✓ f.
  Proof.
    uPred.unseal. done.
  Qed.

End upred.

Section lemmas.
  Context {n : nat} (A : cmra) (DS : ivec n cmra).

  Lemma prod_valid_1st {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ (MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ⋅ MkGen a2 b2 c2 d2 e2 f2) ⊢@{iProp Σ} ✓ (a1 ⋅ a2).
  Proof. rewrite gen_cmra_op_eq gen_cmra_validI. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_2nd {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ (MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ⋅ MkGen a2 b2 c2 d2 e2 f2) ⊢@{iProp Σ} ✓ (b1 ⋅ b2).
  Proof. rewrite gen_cmra_op_eq gen_cmra_validI. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_3rd {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ (MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ⋅ MkGen a2 b2 c2 d2 e2 f2) ⊢@{iProp Σ} ✓ (c1 ⋅ c2).
  Proof. rewrite gen_cmra_op_eq gen_cmra_validI. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_4th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ (MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ⋅ MkGen a2 b2 c2 d2 e2 f2) ⊢@{iProp Σ} ✓ (d1 ⋅ d2).
  Proof. rewrite gen_cmra_op_eq gen_cmra_validI. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_5th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ (MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ⋅ MkGen a2 b2 c2 d2 e2 f2) ⊢@{iProp Σ} ✓ (e1 ⋅ e2).
  Proof. rewrite gen_cmra_op_eq gen_cmra_validI. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_6th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ (MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ⋅ MkGen a2 b2 c2 d2 e2 f2) ⊢@{iProp Σ} ✓ (f1 ⋅ f2).
  Proof. rewrite gen_cmra_op_eq gen_cmra_validI. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_6_equiv a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    MkGen (A := A) (DS := DS) a1 b1 c1 d1 e1 f1 ≡ MkGen a2 b2 c2 d2 e2 f2
    ↔ (a1 ≡ a2) ∧ (b1 ≡ b2) ∧ (c1 ≡ c2) ∧ (d1 ≡ d2) ∧ (e1 ≡ e2) ∧ (f1 ≡ f2).
  Proof. done. Qed.

  (* Lemma prod_6_equivI {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 : *)
  (*   (a1, b1, c1, d1, e1, f1) ≡ (a2, b2, c2, d2, e2, f2) *)
  (*   ⊣⊢@{iProp Σ} (a1 ≡ a2) ∧ (b1 ≡ b2) ∧ (c1 ≡ c2) ∧ (d1 ≡ d2) ∧ (e1 ≡ e2) ∧ (f1 ≡ f2). *)
  (* Proof. rewrite !prod_equivI. simpl. rewrite -4!assoc. done. Qed. *)

  (* Lemma pair_op_6 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 : *)
  (*   (a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2) = *)
  (*   (a1 ⋅ a2, b1 ⋅ b2, c1 ⋅ c2, d1 ⋅ d2, e1 ⋅ e2, f1 ⋅ f2). *)
  (* Proof. done. Qed. *)

  Lemma own_gen_cmra_split {Σ} `{!inG Σ (generational_cmraR A DS)}
      γ a b c d e f :
    own γ (MkGen a b c d e f) ⊣⊢
      own γ (MkGen a ε ε ε ε ε) ∗
      own γ (MkGen ε b ε ε ε ε) ∗
      own γ (MkGen ε ε c ε ε ε) ∗
      own γ (MkGen ε ε ε d ε ε) ∗
      own γ (MkGen ε ε ε ε e ε) ∗
      own γ (MkGen ε ε ε ε ε f).
   Proof.
     rewrite -5!own_op.
     f_equiv.
     rewrite gen_cmra_op_eq. simpl.
     (* NOTE: Doing the split before rewriting is, for some reason, slightly faster
      * than doing the rewrite without the split. *)
     repeat split; simpl;
       rewrite ?ucmra_unit_right_id; rewrite ?ucmra_unit_left_id; reflexivity.
  Qed.

  (* The lemma above somehow causes [Qed]s to be very slow, this variant seems
   * slightly better. *)
  Lemma own_gen_cmra_split_alt {Σ}
      `{!inG Σ (generational_cmraR A DS)} γ a b c d e f :
      own γ (MkGen a b c d e f) ⊣⊢
        own γ (MkGen a ε ε ε ε ε) ∗
        own γ (MkGen ε b ε ε ε ε) ∗
        own γ (MkGen ε ε c ε ε ε) ∗
        own γ (MkGen ε ε ε d ε ε) ∗
        own γ (MkGen ε ε ε ε e ε) ∗
        own γ (MkGen ε ε ε ε ε f).
  Proof.
    rewrite -5!own_op.
    rewrite 1!gen_cmra_op_eq. simpl.
    f_equiv.
    repeat split; simpl;
      rewrite ?ucmra_unit_right_id; rewrite ?ucmra_unit_left_id; reflexivity.
  Qed.

  Global Instance gen_generation_gen_trans (f : A → A)
    `{!Proper (equiv ==> equiv) f} :
    CmraMorphism f → CmraMorphism (gen_cmra_trans (DS := DS) f).
  Proof. Admitted. (* apply _. Qed. *)

  (* Global Instance gen_generation_proper (f : A → A) : *)
  (*   Proper ((≡) ==> (≡)) f → *)
  (*   Proper ((≡) ==> (≡)) (underlying_trans (DS := DS) f). *)
  (* Proof. *)
  (*   intros ? [[??]?] [[??]?] [[??]?]. simpl in *. *)
  (*   rewrite /underlying_trans. *)
  (*   simpl in *. *)
  (*   solve_proper. *)
  (* Qed. *)

  Global Instance gen_generation_proper (f : A → A) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡)) (gen_cmra_trans (DS := DS) f).
  Proof.
  Admitted.
  (*   intros ? [[[??]?]] [[[??]?]] [[[??]?]]. simpl in *. *)
  (*   rewrite /gen_cmra_trans. *)
  (*   simpl. *)
  (*   a *)
  (*   solve_proper. *)
  (* Qed. *)

  Global Instance gen_generation_ne (f : A → A) :
    NonExpansive f →
    NonExpansive (gen_cmra_trans (DS := DS) f).
  Proof. Admitted. (* solve_proper. Qed. *)

  Lemma gen_cmra_trans_apply (t : A → A) a b c d e f :
    (gen_cmra_trans t) (MkGen a b c d e f) =
      MkGen (DS := DS)
        (Some (to_agree t)) (GTS_floor b) (t <$> c) d
        (gen_pv_trans e) (gen_pv_trans f).
  Proof. done. Qed.

End lemmas.

Lemma generational_cmraR_transp {A1 A2 n1 n2} {DS1 : ivec n1 cmra} {DS2 : ivec n2 cmra}
    (eq_n : n1 = n2) :
  A1 = A2 →
  DS1 = rew <- eq_n in DS2 →
  generational_cmraR A1 DS1 = generational_cmraR A2 DS2.
Proof. revert eq_n. intros -> -> ->. done. Defined.

Lemma generational_cmraR_transp_refl {A n} {DS : ivec n cmra} :
  generational_cmraR_transp (A1 := A) (n1 := n) (DS1 := DS)
    eq_refl eq_refl eq_refl = eq_refl.
Proof. done. Qed.

Section generational_resources.
  Context {n} {A} {DS : ivec n cmra} `{i : !inG Σ (generational_cmraR A DS)}.
  Implicit Types (R : rel_over DS A) (P : (A → A) → Prop).

  Definition gen_pick_out γ r : iProp Σ :=
    own γ (gc_tup_pick_out DS r).

  (* The generational version of [own] that should be used instead of [own]. *)
  Definition gen_own (γ : gname) (a : A) : iProp Σ :=
    own γ (gc_tup_elem DS a).

  Definition know_deps γ (γs : ivec n gname) : iProp Σ :=
    own γ (gc_tup_deps A DS (ivec_to_list γs)).

  (* Definition gen_promise_list γ l := *)
  (*   own γ (gc_tup_promise_list l). *)

  Definition gen_promise_rel_pred_list γ rels preds :=
    own γ (gc_tup_rel_pred rels preds).

  Definition gen_token_used γ : iProp Σ :=
    gen_pick_out γ GTS_tok_perm.

  Definition gen_token γ : iProp Σ :=
    gen_pick_out γ (GTS_tok_both).

  Definition own_frozen_auth_promise_list γ rels preds : iProp Σ :=
    gen_promise_rel_pred_list γ
      (gP (●ML rels) ⋅ gV (●ML□ rels)) (gP (●ML preds) ⋅ gV (●ML□ preds)).

  Definition own_unit γ : iProp Σ :=
    own γ ε.

End generational_resources.
