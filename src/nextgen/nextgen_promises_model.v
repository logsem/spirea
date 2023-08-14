(* A high-level [nextgen] modality that supports picking transformations per
 * ghost location that satisfies a dynamically picked promise that can depend
 * on other ghost locations.
 *
 * This file contains the basic definition of the modality and general rules.
 *)

From Equations Require Import Equations.
From stdpp Require Import finite.

From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From iris_named_props Require Import named_props.
From nextgen Require Export nextgen_basic cmra_morphism_extra gen_single_shot gen_nc.

From self Require Export hvec.
From self.high Require Import increasing_map.
From self.nextgen Require Export types omega generational_cmra transmap promise.

Import EqNotations. (* Get the [rew] notation. *)
Import uPred.

(* NOTE: Some terminology used in this module.
 *
 * If [A] is a camera a _transformation_ for [A] is a function of type [A → A].
 *
 * A _predicate_ is a unary-predicate over a transformation for [A] with type
 * [(A → A) → Prop].
 *
 * A _relation_ is an n-ary predicate over transformation for a list of cameras
 * [DS] and a camera [A]. I.e., with the type [(DS_0 → DS_0) → ... (DS_n →
 * DS_n) → (A → A) → Prop].
 *
 * Note that we use "predicate" to mean "unary-predicate" and "relation" to
 * mean "n-aray" predicate where n > 1.
 *)

Definition map_unfold {Σ} {i : gid Σ} : R Σ i -n> Rpre Σ i :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Definition map_fold {Σ} {i : gid Σ} : Rpre Σ i -n> R Σ i :=
  rFunctor_map _ (iProp_unfold, iProp_fold).

Lemma map_unfold_inG_unfold {Σ A} {i : inG Σ A} :
  map_unfold ≡ own.inG_unfold (i := i).
Proof. done. Qed.

Lemma map_fold_unfold {Σ} {i : gid Σ} (a : R Σ i) :
  map_fold (map_unfold a) ≡ a.
Proof.
  rewrite /map_fold /map_unfold -rFunctor_map_compose -{2}[a]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_fold_unfold.
Qed.

Lemma map_unfold_op {Σ} {i : gid Σ} (a b : R Σ i)  :
  map_unfold a ⋅ map_unfold b ≡ map_unfold (a ⋅ b).
Proof. rewrite cmra_morphism_op. done. Qed.

Lemma map_unfold_validN {Σ} {i : gid Σ} n (x : R Σ i) :
  ✓{n} (map_unfold x) ↔ ✓{n} x.
Proof.
  split; [|apply (cmra_morphism_validN _)].
  move=> /(cmra_morphism_validN map_fold). by rewrite map_fold_unfold.
Qed.

Lemma map_unfold_validI {Σ} {i : gid Σ} (a : R Σ i) :
  ✓ map_unfold a ⊢@{iPropI Σ} ✓ a.
Proof. apply valid_entails=> n. apply map_unfold_validN. Qed.

(** Transport an endo map on a camera along an equality in the camera. *)
Definition cmra_map_transport {A B : cmra}
    (Heq : A = B) (f : A → A) : (B → B) :=
  eq_rect A (λ T, T → T) f _ Heq.

Section cmra_map_transport.
  Context {A B : cmra} (eq : A = B).

  #[global]
  Instance cmra_map_transport_ne' f :
    NonExpansive f →
    NonExpansive (cmra_map_transport (A := A) (B := B) eq f).
  Proof. solve_proper. Qed.

  Lemma cmra_map_transport_cmra_transport
      (f : A → A) a :
    (cmra_map_transport eq f) (cmra_transport eq a) =
    (cmra_transport eq (f a)).
  Proof. destruct eq. simpl. reflexivity. Defined.

  Global Instance cmra_map_transport_proper (f : A → A) :
    (Proper ((≡) ==> (≡)) f) →
    (Proper ((≡) ==> (≡)) (cmra_map_transport eq f)).
  Proof. naive_solver. Qed.

  Lemma cmra_map_transport_op f `{!CmraMorphism f} x y :
    cmra_map_transport eq f (x ⋅ y) ≡
      cmra_map_transport eq f x ⋅ cmra_map_transport eq f y.
  Proof. destruct eq. simpl. apply: cmra_morphism_op. Qed.

  (* Lemma cmra_map_transport_core x : T (core x) = core (T x). *)
  (* Proof. by destruct H. Qed. *)

  Lemma cmra_map_transport_validN n f `{!CmraMorphism f} a :
    ✓{n} a → ✓{n} cmra_map_transport eq f a.
  Proof. destruct eq. apply: cmra_morphism_validN. Qed.

  Lemma cmra_map_transport_pcore f `{!CmraMorphism f} x :
    cmra_map_transport eq f <$> pcore x ≡ pcore (cmra_map_transport eq f x).
  Proof. destruct eq. simpl. apply: cmra_morphism_pcore. Qed.

End cmra_map_transport.

Section build_trans.
  Context `{Σ : gFunctors, Ω : gGenCmras Σ}.
(*
How to represent the dependencies?

We need
- To be able to store both a collection of ..
  - .. the types of the dependencies [A : Type, ..]
  - .. transformation functions matching the types of the dependencis [t : A → A, ..]
  - .. predicates over the transformation functions.
- We need to be able to map over the types.
- To be able to do an ∧ or a ∗ over the transformation functions.
*)
  Lemma finite_decidable_sig `{Finite A} (P : A → Prop) `{∀ i, Decision (P i)} :
    {i : A | P i} + {∀ i, ¬ P i}.
  Proof. destruct (decide (∃ i, P i)) as [?%choice | ?]; naive_solver. Qed.

  Definition Omega_lookup_inverse (j : gid Σ) :
    {i : ggid Ω | Ogid Ω i = j} + {∀ i, Ogid Ω i ≠ j}.
  Proof. apply (finite_decidable_sig (λ i, Ogid Ω i = j)). Qed.

  Lemma Omega_lookup_inverse_eq i j (eq : Ogid Ω i = j) :
    Omega_lookup_inverse j = inleft (exist _ i eq).
  Proof.
    destruct (Omega_lookup_inverse j) as [(?& eq')|oo].
    - f_equiv.
      simplify_eq.
      assert (x = i) as ->.
      { apply Ogid_inj. done. }
      assert (eq' = eq_refl) as ->.
      { rewrite (proof_irrel eq' eq_refl). done. }
      done.
    - exfalso. apply (oo i). done.
  Qed.

  Definition build_trans_at (m : iResUR Σ) (i : ggid Ω)
      (tts : gmap gname (Oc Ω i → Oc Ω i)) : gmapUR gname (Rpre Σ (Ogid Ω i)) :=
    let gccd := Ω.(gc_map) i in
    map_imap (λ γ (a : Rpre Σ gccd.(gcd_gid)),
      (* If the map of transmap contains a transformation then we apply the
       * transformation otherwise we leave the element unchanged. In all
       * cases we apply something of the form [cmra_map_transport]. *)
      let inner_trans : gccd.(gcd_cmra) → gccd.(gcd_cmra) :=
        default (λ a, a) (tts !! γ) in
      let trans :=
        cmra_map_transport gccd.(gcd_cmra_eq) (gen_cmra_trans inner_trans)
      in Some $ map_unfold $ trans $ map_fold a
    ) (m gccd.(gcd_gid)).

  (** This is a key definition for [TransMap]. It builds a global generational
   * transformation based on the transformations in [transmap]. *)
  Definition build_trans transmap : (iResUR Σ → iResUR Σ) :=
    λ (m : iResUR Σ), λ (j : gid Σ),
      match Omega_lookup_inverse j with
      | inleft (exist _ i eq) =>
        rew [λ a, gmapUR gname (Rpre Σ a)] eq in build_trans_at m i (transmap i)
      | inright _ => m j
      end.

  (* (** This is a key definition for [TransMap]. It builds a global generational *)
  (*  * transformation based on the transformations in [transmap]. *) *)
  (* Definition build_trans transmap : (iResUR Σ → iResUR Σ) := *)
  (*   λ (m : iResUR Σ), λ (i : gid Σ), build_trans_at m i (transmap i). *)

  Lemma core_Some_pcore {A : cmra} (a : A) : core (Some a) = pcore a.
  Proof. done. Qed.

  #[global]
  Lemma build_trans_generation transmap :
    transmap_valid transmap → CmraMorphism (build_trans transmap).
  Proof.
    intros val.
    rewrite /build_trans.
    split.
    - rewrite /Proper.
      intros ??? eq i γ.
      destruct (Omega_lookup_inverse i) as [[j []]|]; last apply eq.
      specialize (eq (Ω.(gc_map) j).(gcd_gid) γ).
      unfold build_trans_at.
      simpl.
      rewrite 2!map_lookup_imap.
      destruct (y (Ω.(gc_map) j).(gcd_gid) !! γ) as [b|] eqn:look1;
        rewrite look1; rewrite look1 in eq; simpl.
      2: { apply dist_None in eq. rewrite eq. done. }
      apply dist_Some_inv_r' in eq as (a & look2 & eq).
      apply symmetry in eq.
      rewrite look2.
      destruct (transmap j !! γ) eqn:look; simpl.
      2: { solve_proper. }
      apply val in look as [gt ?].
      solve_proper.
    - intros ? a Hval.
      intros i γ.
      destruct (Omega_lookup_inverse i) as [[j []]|]; last apply Hval.
      simpl.
      rewrite !map_lookup_imap.
      specialize (Hval (Ω.(gc_map) j).(gcd_gid) γ).
      destruct (a (Ω.(gc_map) j).(gcd_gid) !! γ) eqn:eq; rewrite eq /=; last done.
      rewrite eq in Hval.
      apply Some_validN.
      apply: cmra_morphism_validN.
      destruct (transmap j !! γ) as [pick|] eqn:eq2.
      * simpl.
        specialize (val j γ pick eq2) as GT.
        apply: cmra_map_transport_validN.
        apply: cmra_morphism_validN.
        apply Hval.
      * simpl.
        apply: cmra_map_transport_validN.
        apply: cmra_morphism_validN.
        apply Hval.
    - move=> m /=.
      rewrite cmra_pcore_core.
      simpl.
      f_equiv.
      intros i γ.
      rewrite lookup_core.
      destruct (Omega_lookup_inverse i) as [[j eq']|].
      2: { rewrite lookup_core. reflexivity. }
      destruct eq'. simpl.
      rewrite 2!map_lookup_imap.
      rewrite lookup_core.
      destruct (m (Ω.(gc_map) j).(gcd_gid) !! γ) as [a|] eqn:look;
        rewrite look; simpl; last done.
      simpl.
      rewrite 2!core_Some_pcore.
      rewrite -cmra_morphism_pcore.
      destruct (transmap j !! γ) as [pick|] eqn:pickLook; simpl.
      * specialize (val j γ pick pickLook) as ?.
        rewrite -cmra_map_transport_pcore.
        rewrite -cmra_morphism_pcore.
        destruct (pcore a); done.
      * rewrite -cmra_map_transport_pcore.
        rewrite -cmra_morphism_pcore.
        destruct (pcore a); done.
    - intros m1 m2.
      intros i γ.
      rewrite !discrete_fun_lookup_op.
      destruct (Omega_lookup_inverse i) as [[j eq']|]; last reflexivity.
      destruct eq'. simpl.
      unfold build_trans_at.
      rewrite !discrete_fun_lookup_op.
      rewrite !map_lookup_imap.
      rewrite 2!lookup_op.
      rewrite !map_lookup_imap.
      destruct (m1 (Ω.(gc_map) j).(gcd_gid) !! γ) eqn:eq1;
        destruct (m2 (Ω.(gc_map) j).(gcd_gid) !! γ) eqn:eq2;
        rewrite eq1 eq2; simpl; try done.
      rewrite -Some_op.
      f_equiv.
      rewrite map_unfold_op.
      f_equiv.
      destruct (transmap j !! γ) as [pick|] eqn:pickLook.
      * specialize (val j γ pick pickLook) as ?.
        rewrite -cmra_map_transport_op.
        f_equiv.
        rewrite -cmra_morphism_op.
        done.
      * simpl.
        rewrite -cmra_map_transport_op.
        f_equiv.
        rewrite -cmra_morphism_op.
        done.
  Qed.

  Lemma build_trans_at_singleton_neq id1 id2 mm pick :
    id1 ≠ (Ogid Ω id2) →
    build_trans_at (discrete_fun_singleton id1 mm) id2 pick ≡ ε.
  Proof.
    intros neq.
    unfold build_trans_at.
    rewrite discrete_fun_lookup_singleton_ne; last done.
    rewrite map_imap_empty.
    done.
  Qed.

  Lemma build_trans_singleton_alt picks id γ
      (a : generational_cmraR (Oc Ω id) (Ocs Ω id)) eqIn (V : transmap_valid picks) pps :
    Oeq Ω id = eqIn →
    picks id = pps →
    build_trans picks (discrete_fun_singleton (Ogid Ω id) {[
      γ := map_unfold (cmra_transport eqIn a)
      ]}) ≡
      discrete_fun_singleton (Ogid Ω id) {[
        γ := map_unfold (cmra_transport eqIn (gen_cmra_trans
        (default (λ a, a) (picks id !! γ)) a))
      ]}.
  Proof.
    rewrite /build_trans. simpl.
    intros eqLook picksLook j2.
    rewrite /own.iRes_singleton.
    destruct (decide (Ogid Ω id = j2)) as [eq|neq].
    - intros γ2.
      rewrite (Omega_lookup_inverse_eq id _ eq).
      rewrite picksLook /=.
      unfold build_trans_at.
      rewrite <- eq.
      rewrite 2!discrete_fun_lookup_singleton.
      destruct eq. simpl.
      rewrite map_lookup_imap.
      destruct (decide (γ = γ2)) as [<- | neqγ].
      2: { rewrite !lookup_singleton_ne; done. }
      rewrite 2!lookup_singleton.
      simpl.
      f_equiv.
      f_equiv.
      rewrite -eqLook.
      unfold Oeq.
      rewrite -cmra_map_transport_cmra_transport.
      assert (∃ bingo, pps !! γ = bingo ∧ (bingo = None ∨ (∃ t, bingo = Some t ∧ CmraMorphism t)))
          as (mt & ppsLook & disj).
      { exists (pps !! γ).
        split; first done.
        destruct (pps !! γ) eqn:ppsLook. 2: { left. done. }
        right. eexists _. split; try done.
        eapply V. rewrite picksLook. done. }
      rewrite ppsLook. simpl.
      destruct disj as [-> | (t & -> & GT)].
      + simpl. rewrite map_fold_unfold. done.
      + simpl. rewrite map_fold_unfold. done.
    - simpl.
      rewrite discrete_fun_lookup_singleton_ne; last done.
      rewrite discrete_fun_lookup_singleton_ne; last done.
      destruct (Omega_lookup_inverse j2) as [[? eq]|]; last done.
      destruct eq. simpl.
      apply build_trans_at_singleton_neq.
      done.
  Qed.

End build_trans.

Section transmap.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (transmap : TransMap Ω).
  Implicit Types (ps : list (promise_info Ω)).

  (* We need to:
    - Be able to turn a list of promises and a map of picks into a
      global transformation.
    - Say that a set of picks respects a list of promises.
    - Merge two lists of promises.
   *)

  (** The vector [trans] contains at every index the transition for the
   * corresponding dependency in [p] from [transmap] *)
  Definition trans_at_deps transmap (i : ggid Ω) (γs : ivec (On Ω i) gname)
      (ts : hvec (On Ω i) (cmra_to_trans <$$> Ocs Ω i)) :=
    ∀ idx,
      let id := Oids Ω i !!! idx in
      let t : Oc Ω id → Oc Ω id := lookup_fmap_Ocs ts idx (Ω.(gc_map_wf) i) in
      transmap id !! (γs !!! idx) = Some t.

  (** The transformations in [transmap] satisfy the relation in [p]. *)
  Definition transmap_satisfy_rel transmap p :=
    ∃ ts t,
      transmap p.(pi_id) !! p.(pi_γ) = Some t ∧
      trans_at_deps transmap p.(pi_id) p.(pi_deps_γs) ts ∧
      huncurry p.(pi_rel) ts t.

  (** The [transmap] respect the promises in [ps]: There is a pick for every
   * promise and all the relations in the promises are satisfied by the
   * transformations in transmap. *)
  Definition transmap_resp_promises transmap prs :=
    Forall (transmap_satisfy_rel transmap) prs.

  Definition Oc_trans_transport {id1 id2} (eq : id1 = id2)
    (o : Oc Ω id1 → _) : Oc Ω id2 → Oc Ω id2 :=
      eq_rect _ (λ id, Oc Ω id → Oc Ω id) o _ eq.

  Lemma promises_has_deps_resp_promises pi idx promises transmap :
    promises_has_deps pi promises (Ω.(gc_map_wf) pi.(pi_id)) →
    transmap_resp_promises transmap promises →
    ∃ t, (pi_deps_pred pi idx (Ω.(gc_map_wf) pi.(pi_id))) t ∧
         transmap (pi_deps_id pi idx) !! (pi.(pi_deps_γs) !!! idx) = Some t.
  Proof.
    intros hasDeps resp.
    rewrite /transmap_resp_promises Forall_forall in resp.
    specialize (hasDeps idx) as (p2 & Helem & eq1 & eq2 & strong).
    destruct (resp _ Helem) as (ts & (t & tmLook & ? & relHolds)).
    specialize (p2.(pi_rel_to_pred) ts t relHolds) as predHolds.
    exists (Oc_trans_transport (eq_sym eq2) t).
    split.
    * apply strong in predHolds.
      clear -predHolds. destruct eq2. simpl. done.
    * rewrite eq1. clear -tmLook. destruct eq2. apply tmLook.
  Qed.

  (* What would a more general version of this lemma look like? *)
  Lemma rew_cmra_to_pred (x : cmra) f y (eq : x = y) t :
    (eq_rect x pred_over f y eq) t = f (eq_rect_r cmra_to_trans t eq).
  Proof. destruct eq. done. Qed.

  (** If a [transmap] respects a list [promises] and growing the list with [p]
   * is well formed, then we can conjur up a list of transitions from
   * [transmap] that match the dependencies in [p] and that satisfy their
   * predicates. *)
  Lemma transmap_satisfy_wf_cons p promises transmap :
    promises_wf (Ω.(gc_map_wf)) (p :: promises) →
    transmap_resp_promises transmap promises →
    ∃ ts,
      trans_at_deps transmap p.(pi_id) p.(pi_deps_γs) ts ∧
      preds_hold p.(pi_deps_preds) ts.
  Proof.
    intros WF resp.
    destruct WF as [[uniq hasDeps] WF'].
    edestruct (fun_ex_to_ex_hvec_fmap (F := cmra_to_trans) (Ocs Ω (pi_id p))
      (λ i t,
        let t' := eq_rect _ _ t _ (Ocs_Oids_distr p.(pi_id) _ (Ω.(gc_map_wf) _)) in
        let pred := hvec_lookup_fmap p.(pi_deps_preds) i in
        pred t ∧
        transmap (Oids Ω p.(pi_id) !!! i) !! (p.(pi_deps_γs) !!! i) = Some t'))
      as (ts & ?).
    { intros idx.
      specialize (promises_has_deps_resp_promises _ idx _ transmap hasDeps resp).
      intros (t & ? & ?).
      exists (eq_rect_r _ t (Ocs_Oids_distr _ _ (Ω.(gc_map_wf) _))).
      simpl.
      split.
      * rewrite /lookup_fmap_Ocs in H.
        simpl in H.
        clear -H.
        rewrite <- rew_cmra_to_pred.
        apply H.
      * rewrite H0.
        rewrite rew_opp_r.
        done. }
    exists ts.
    split.
    - intros di. apply H.
    - apply preds_hold_alt. intros di.
      apply (H di).
  Qed.

  Lemma transmap_resp_promises_insert owf p promises transmap t :
    promises_wf owf (p :: promises) →
    transmap_resp_promises transmap promises →
    transmap_resp_promises
      (transmap_insert transmap (pi_id p) (pi_γ p) t) promises.
  Proof.
    intros [[uniq hasDeps] WF].
    rewrite /transmap_resp_promises !Forall_forall.
    intros impl p2 elem.
    destruct (impl _ elem) as (t' & ts & rest).
    exists t', ts.
    rewrite /trans_at_deps.
    (* NOTE: This proof might be a bit of a mess. *)
    setoid_rewrite transmap_insert_lookup_ne.
    + apply rest.
    + eapply promises_lookup_at_None; done.
    + apply elem_of_list_lookup_1 in elem as (? & look).
      specialize (
        promises_well_formed_lookup owf promises _ p2 WF look) as hasDeps2.
      specialize (hasDeps2 idx) as (p3 & look3 & eq & eq2 & ?).
      simpl in *.
      rewrite eq2.
      rewrite eq.
      simpl.
      eapply promises_lookup_at_None; done.
  Qed.

  Lemma transmap_resp_promises_weak owf transmap prsL prsR :
    promises_wf owf prsR →
    promise_list_stronger prsL prsR →
    transmap_resp_promises transmap prsL →
    transmap_resp_promises transmap prsR.
  Proof.
    intros wf strong.
    rewrite /transmap_resp_promises.
    rewrite !Forall_forall.
    intros resp [id γ pia2] elm.
    destruct (strong id γ pia2) as (pia1 & look2 & stronger).
    { apply (promises_elem_of owf _ (MkPi id γ pia2)); done. }
    destruct (resp (MkPi id γ pia1)) as (? & ? & ? & ? & ?).
    { apply promises_lookup_at_Some. done. }
    eexists _, _.
    split; first done.
    split.
    { rewrite /trans_at_deps. simpl.
      destruct stronger as [<- ho].
      apply H0. }
    simpl.
    apply stronger.
    done.
  Qed.

  Lemma transmap_resp_promises_lookup_at transmap promises id γ pia :
    transmap_resp_promises transmap promises →
    promises_lookup_at promises id γ = Some pia →
    transmap_satisfy_rel transmap (MkPi id γ pia).
  Proof.
    rewrite /transmap_resp_promises Forall_forall.
    intros resp ?%promises_lookup_at_Some.
    apply resp. done.
  Qed.

  Definition transmap_overlap_resp_promises transmap ps :=
    ∀ i p, ps !! i = Some p →
      transmap_satisfy_rel transmap p ∨ (transmap p.(pi_id) !! p.(pi_γ) = None).

  Lemma trans_at_deps_subseteq transmap1 transmap2 id γs ts :
    transmap1 ⊆ transmap2 →
    trans_at_deps transmap1 id γs ts →
    trans_at_deps transmap2 id γs ts.
  Proof.
    intros sub ta.
    intros idx. simpl.
    specialize (sub (Oids Ω id !!! idx)).
    rewrite map_subseteq_spec in sub.
    specialize (ta idx).
    apply sub.
    apply ta.
  Qed.

  Lemma trans_at_deps_union_l picks1 picks2 i t1 c1 :
    trans_at_deps picks1 i t1 c1 →
    trans_at_deps (picks1 ∪ picks2) i t1 c1.
  Proof.
    apply trans_at_deps_subseteq.
    apply transmap_union_subseteq_l.
  Qed.

  Lemma trans_at_deps_union_r picks1 picks2 i γs ts :
    (∀ i, map_agree_overlap (picks1 i) (picks2 i)) →
    trans_at_deps picks2 i γs ts →
    trans_at_deps (picks1 ∪ picks2) i γs ts.
  Proof.
    intros over.
    apply trans_at_deps_subseteq.
    apply transmap_union_subseteq_r.
    done.
  Qed.

  Lemma trans_at_deps_insert i γs id γ t ts picks :
    picks id !! γ = None →
    trans_at_deps picks i γs ts →
    trans_at_deps (transmap_singleton id γ t ∪ picks) i γs ts.
  Proof.
    intros look.
    apply trans_at_deps_subseteq.
    apply transmap_union_subseteq_r.
    intros ???? look2 ?.
    apply gen_f_singleton_lookup_Some in look2 as (-> & <- & ?).
    congruence.
  Qed.


  Lemma transmap_overlap_resp_promises_cons transmap p promises :
    transmap_overlap_resp_promises transmap (p :: promises) →
    transmap_overlap_resp_promises transmap promises.
  Proof. intros HL. intros i ? look. apply (HL (S i) _ look). Qed.

  (* Grow a transformation map to satisfy a list of promises. This works by
  * traversing the promises and using [promise_info] to extract a
  * transformation. *)
  Lemma transmap_and_promises_to_full_map transmap promises :
    transmap_valid transmap →
    transmap_overlap_resp_promises transmap promises →
    promises_wf (Ω.(gc_map_wf)) promises →
    ∃ (full_map : TransMap Ω),
      transmap_valid full_map ∧
      transmap_resp_promises full_map promises ∧
      transmap ⊆ full_map.
  Proof.
    intros val.
    induction promises as [|p promises' IH].
    - intros _ _. exists transmap.
      split_and!; try done.
      apply Forall_nil_2.
    - intros HR [WF WF'].
      specialize (promise_wf_neq_deps _ _ _ WF) as depsDiff.
      destruct IH as (map & resp & val' & sub).
      {  eapply transmap_overlap_resp_promises_cons. done. } { done. }
      (* We either need to use the transformation in [picks] or extract one
       * from [p]. *)
      destruct (transmap p.(pi_id) !! p.(pi_γ)) eqn:look.
      + destruct (HR 0 p) as [sat | ?]; [done | | congruence].
        destruct sat as (ts & t & transIn & hold & pRelHolds).
        exists map. (* We don't insert as map already has transformation. *)
        split; first done.
        split; last done.
        apply Forall_cons.
        split; try done.
        eexists _, _. split_and!; last done.
        -- specialize (sub p.(pi_id)).
           rewrite map_subseteq_spec in sub.
           apply sub.
           done.
        -- eapply trans_at_deps_subseteq; done.
      + edestruct transmap_satisfy_wf_cons as (ts & transIn & hold);
          [done|done|].
        eassert (∃ t, _ ∧ _) as (t & gt & pRelHolds).
        { apply p.(pi_witness). apply hold. }
        exists (transmap_insert map p.(pi_id) p.(pi_γ) t).
        split_and!.
        * apply transmap_valid_insert; done.
        * apply Forall_cons.
          split.
          -- rewrite /transmap_satisfy_rel.
            exists ts, t.
            split. { by rewrite transmap_insert_lookup. }
            split; last done.
            intros ??.
            simpl.
            rewrite transmap_insert_lookup_ne; first apply transIn.
            apply depsDiff.
          -- apply (transmap_resp_promises_insert Ω.(gc_map_wf)); done.
        * apply transmap_insert_subseteq_r; done.
  Qed.

  Lemma promises_to_maps (promises : list _) :
    promises_wf Ω.(gc_map_wf) promises →
    ∃ (transmap : TransMap _), transmap_resp_promises transmap promises.
  Proof.
    intros WF.
    edestruct (transmap_and_promises_to_full_map (λ i : ggid Ω, ∅))
      as (m & ? & resp & a).
    { done. }
    2: { done. }
    - intros ???. right. done.
    - exists m. apply resp.
  Qed.

End transmap.

(* Arguments promise_info Σ : clear implicits. *)
(* Arguments promise_self_info Σ : clear implicits. *)

Lemma deps_agree {Σ A n} {DS : ivec n cmra} `{!inG Σ (generational_cmraR A DS)} γ (γs1 γs2 : ivec n gname) :
  own γ (gc_tup_deps A DS (vec_to_list γs1)) -∗
  own γ (gc_tup_deps A DS (vec_to_list γs2)) -∗
  ⌜ γs1 = γs2 ⌝.
Proof.
  iIntros "A B".
  iDestruct (own_valid_2 with "A B") as "hv".
  iDestruct (prod_valid_4th with "hv") as "%val".
  iPureIntro.
  rewrite Some_valid in val.
  rewrite to_agree_op_valid_L in val.
  (* Search vec_to_list. *)
  apply vec_to_list_inj2.
  apply val.
Qed.

Lemma own_eq `{inG Σ A} γ (a b : A) : a = b → own γ a ⊢ own γ b.
Proof. intros ->. done. Qed.

Section own_picks.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (picks : TransMap Ω).

  (* NOTE: If a transformation has been picked for one ghost name, then all the
   * dependencies must also have been picked. This is ensured by this
   * definition through [trans_at_deps]. *)
  Definition own_pick picks i γ t : iProp Σ :=
    ∃ (ts : hvec (On Ω i) (cmra_to_trans <$$> Ocs Ω i))
        (γs : ivec (On Ω i) gname) Ps R Rs,
      ⌜ trans_at_deps picks i γs ts ⌝ ∧
      ⌜ huncurry R ts t ⌝ ∧
      ⌜ rel_prefix_list_for rel_weaker Rs R ⌝ ∧
      Oown i γ (
        MkGen ε (GTS_tok_gen_shot t) ε (Some (to_agree (vec_to_list γs)))
        (gC (●ML□ Rs)) (gC (●ML□ Ps))
      ).

  (* The resource contains the agreement resources for all the picks in
   * [picks]. We need to know that a picked transformation satisfies the most
   * recent/strongest promise. We thus need the authorative part of the
   * promises. *)
  Definition own_picks picks : iProp Σ :=
    ∀ (i : ggid Ω) γ t, ⌜ picks i !! γ = Some t ⌝ -∗ own_pick picks i γ t.

  #[global]
  Instance own_picks_persistent picks : Persistent (own_picks picks).
  Proof. apply _. Qed.

  Lemma tokens_for_picks_agree_overlap picks1 picks2 :
    own_picks picks1 -∗
    own_picks picks2 -∗
    ⌜ ∀ i, map_agree_overlap (picks1 i) (picks2 i) ⌝.
  Proof.
    iIntros "m1 m2". iIntros (i).
    iIntros (γ a1 a2 look1 look2).
    iDestruct ("m1" $! i γ _ look1) as (????????) "O1".
    iDestruct ("m2" $! i γ _ look2) as (????????) "O2".
    simplify_eq.
    iDestruct (own_valid_2 with "O1 O2") as "#Hv".
    rewrite prod_valid_2nd.
    rewrite GTS_tok_gen_shot_agree.
    iApply "Hv".
  Qed.

  Lemma cmra_transport_validI {A B : cmra} (eq : A =@{cmra} B) (a : A) :
    ✓ cmra_transport eq a ⊣⊢@{iPropI Σ} ✓ a.
  Proof. destruct eq. done. Qed.

  (* NOTE: The other direction does not work. *)
  Lemma own_picks_sep picks1 picks2 :
    own_picks picks1 ∗ own_picks picks2 ⊢ own_picks (picks1 ∪ picks2).
  Proof.
    iIntros "[O1 O2]".
    iDestruct (tokens_for_picks_agree_overlap with "O1 O2") as %disj.
    iIntros (??? [look|look]%transmap_lookup_union_Some ).
    * iDestruct ("O1" $! _ _ _ look) as (????????) "H".
      repeat iExists _. iFrame "∗%".
      iPureIntro. apply trans_at_deps_union_l. done.
    * iDestruct ("O2" $! _ _ _ look) as (????????) "H".
      repeat iExists _. iFrame "∗%".
      iPureIntro. apply trans_at_deps_union_r; done.
  Qed.

  Lemma own_picks_sep' picks1 picks2 :
    own_picks picks1 -∗
    own_picks picks2 -∗
    own_picks (picks1 ∪ picks2) ∗ ⌜ picks2 ⊆ picks1 ∪ picks2 ⌝.
  Proof.
    iIntros "O1 O2".
    iDestruct (tokens_for_picks_agree_overlap with "O1 O2") as %disj.
    rewrite -own_picks_sep. iFrame.
    iPureIntro. apply transmap_union_subseteq_r. done.
  Qed.

End own_picks.

Section next_gen_definition.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (picks : TransMap Ω).

  (* Every generational ghost location consists of a camera and a list of
   * cameras for the dependencies. *)

  (* This could be generalized to abitrary camera morphisms and upstreamed *)
  Instance cmra_transport_coreid i (a : R Σ i) :
    CoreId a → CoreId (map_unfold (Σ := Σ) a).
  Proof.
    intros ?. rewrite /map_unfold.
    rewrite /CoreId.
    rewrite -cmra_morphism_pcore.
    rewrite core_id.
    done.
  Qed.

  Definition own_promise_info_resource (pi : promise_info Ω)
      (Rs : list (rel_over (Ocs Ω pi.(pi_id)) _))
      (Ps : list (pred_over (Oc Ω pi.(pi_id)))) : iProp Σ :=
    Oown pi.(pi_id) pi.(pi_γ) (MkGen
      ε ε ε (Some (to_agree (vec_to_list pi.(pi_deps_γs))))
      (gNC (◯ML Rs)) (gNC (◯ML Ps))
    ).

  Definition own_promise_info (pi : promise_info Ω) : iProp Σ :=
    ∃ Rs (Ps : list (pred_over (Oc Ω pi.(pi_id)))),
      ⌜ pred_prefix_list_for' Rs Ps pi.(pi_rel) pi.(pi_pred) ⌝ ∗
      own_promise_info_resource pi Rs Ps.

  #[global]
  Instance own_promise_info_persistent pi : Persistent (own_promise_info pi).
  Proof. apply _. Qed.

  Definition own_promises (ps : list (promise_info Ω)) : iProp Σ :=
    [∗ list] p ∈ ps, own_promise_info p.

  #[global]
  Instance own_promises_persistent ps : Persistent (own_promises ps).
  Proof. apply _. Qed.

  Definition nextgen_def P : iProp Σ :=
    ∃ (picks : TransMap Ω) (prs : list (promise_info Ω)),
      "%picksValid" ∷ ⌜ transmap_valid picks ⌝ ∗
      "%prsWf" ∷ ⌜ promises_wf Ω.(gc_map_wf) prs ⌝ ∗
      (* We own resources for everything in [picks] and [promises]. *)
      "#ownPicks" ∷ own_picks picks ∗
      "#ownPrs" ∷ own_promises prs ∗
      "contP" ∷ ∀ full_picks (val : transmap_valid full_picks),
        ⌜ transmap_resp_promises full_picks prs ⌝ -∗
        ⌜ picks ⊆ full_picks ⌝ -∗
        let _ := build_trans_generation full_picks val in
        ⚡={build_trans full_picks}=> P.
  Local Definition nextgen_aux : seal (@nextgen_def). Proof. by eexists. Qed.
  Definition nextgen := nextgen_aux.(unseal).

  Lemma nextgen_unseal : nextgen = nextgen_def.
  Proof. rewrite -nextgen_aux.(seal_eq) //. Qed.

End next_gen_definition.

Notation "⚡==> P" := (nextgen P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.

Section own_promises_properties.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (prs : list (promise_info Ω)).

  Lemma prefix_of_eq_length {A} (l1 l2 : list A) :
    length l2 ≤ length l1 → l1 `prefix_of` l2 → l2 = l1.
  Proof.
    intros len [[|a l] eq].
    - rewrite -app_nil_end in eq. done.
    - assert (length l2 = length (l1 ++ a :: l)) by (rewrite eq; done).
      rewrite app_length /= in H. lia.
  Qed.

  Lemma prefix_of_disj {A} (l1 l2 : list A) :
    length l1 ≤ length l2 →
    l1 `prefix_of` l2 ∨ l2 `prefix_of` l1 →
    l1 `prefix_of` l2.
  Proof.
    intros len [pref|pref]; first done.
    assert (l1 = l2) as ->; last done.
    apply prefix_of_eq_length; done.
  Qed.

  Lemma prefix_of_conj_disj {A B} (ls1 ls2 : list A) (ls3 ls4 : list B):
    length ls1 = length ls3 →
    length ls2 = length ls4 →
    (ls1 `prefix_of` ls2 ∨ ls2 `prefix_of` ls1) →
    (ls3 `prefix_of` ls4 ∨ ls4 `prefix_of` ls3) →
    (ls1 `prefix_of` ls2 ∧ ls3 `prefix_of` ls4) ∨
    (ls2 `prefix_of` ls1 ∧ ls4 `prefix_of` ls3).
  Proof.
    intros len1 len2 [pre1|pre1] disj.
    - left. split; first done.
      apply prefix_of_disj; last done.
      apply prefix_length in pre1.
      lia.
    - right. split; first done.
      apply prefix_of_disj; last naive_solver.
      apply prefix_length in pre1.
      lia.
  Qed.

  Lemma pred_prefix_list_for_stronger id Rs Rs0 Ps Ps0
      (p1 p2 : promise_info_at Ω id) :
    pred_prefix_list_for' Rs Ps (pi_rel p1) (pi_pred p1) →
    pred_prefix_list_for' Rs0 Ps0 (pi_rel p2) (pi_pred p2) →
    pi_deps_γs p1 = pi_deps_γs p2 →
    Rs `prefix_of` Rs0 ∨ Rs0 `prefix_of` Rs →
    Ps `prefix_of` Ps0 ∨ Ps0 `prefix_of` Ps →
    promise_stronger p1 p2 ∨ promise_stronger p2 p1.
  Proof.
    intros (len1 & relPref1 & predPref1 & impl1).
    intros (len2 & relPref2 & predPref2 & impl2).
    intros depsEq rPref pPred.
    destruct (prefix_of_conj_disj Rs Rs0 Ps Ps0) as [[pref1 pref2]|[??]]; try done.
    - rewrite /promise_stronger.
      right.
      split; first done.
      split.
      * apply rel_weaker_stronger.
        apply: pred_prefix_list_for_prefix_of; done.
      * apply pred_weaker_stronger.
        apply: pred_prefix_list_for_prefix_of; try done.
    - left.
      split; first done.
      split.
      * apply rel_weaker_stronger.
        apply: pred_prefix_list_for_prefix_of; done.
      * apply pred_weaker_stronger.
        apply: pred_prefix_list_for_prefix_of; try done.
  Qed.

  (* If two promise lists has an overlap then one of the overlapping promises
   * is strictly stronger than the other. *)
  Lemma own_promises_overlap prsL prsR :
    own_promises prsL -∗
    own_promises prsR -∗
    ⌜ promises_overlap_pred prsL prsR ⌝.
  Proof.
    iIntros "O1 O2".
    iIntros (id γ p1 p2 look1 look2).
    apply promises_lookup_at_Some in look1 as elem1.
    apply promises_lookup_at_Some in look2 as elem2.
    unfold own_promises.
    rewrite big_sepL_elem_of; last done.
    rewrite big_sepL_elem_of; last done.
    iDestruct "O1" as (???) "O1".
    iDestruct "O2" as (???) "O2".
    simpl in *.
    iDestruct (own_valid_2 with "O1 O2") as "#Hv".
    rewrite gen_cmra_op_eq.
    rewrite gen_cmra_validI.
    iDestruct "Hv" as "(_ & _ & _ & %Hv1 & %Hv2 & %Hv3)".
    iPureIntro.
    rewrite -Some_op Some_valid to_agree_op_valid_L in Hv1.
    apply vec_to_list_inj2 in Hv1.
    rewrite gen_nc_op gen_nc_valid auth_frag_op_valid in Hv2.
    rewrite gen_nc_op gen_nc_valid auth_frag_op_valid in Hv3.
    apply to_max_prefix_list_op_valid_L in Hv2.
    apply to_max_prefix_list_op_valid_L in Hv3.
    eapply pred_prefix_list_for_stronger; done.
  Qed.

  Lemma own_picks_promises_satisfy picks prs :
    own_picks picks -∗
    own_promises prs -∗
    ⌜ transmap_overlap_resp_promises picks prs ⌝.
  Proof.
    iIntros "picks prs".
    iIntros (i pi look).
    destruct (picks (pi_id pi) !! pi_γ pi) as [t|] eqn:look2; last naive_solver.
    iLeft.
    iDestruct ("picks" $! _ _ _ look2) as (??????? prefList) "picks".
    apply elem_of_list_lookup_2 in look.
    unfold own_promises.
    rewrite big_sepL_elem_of; last done.
    iDestruct "prs" as (?? (?&?&?&?)) "prs".
    unfold own_promise_info_resource.
    iExists ts, t.
    iSplit; first done.
    unfold Oown.
    iDestruct (own_gen_cmra_split_alt with "prs") as "(_ & _ & _ & deps1 & RS1 & PS1)".
    iDestruct (own_gen_cmra_split_alt with "picks") as "(_ & _ & _ & deps2 & RS2 & PS2)".
    iDestruct (deps_agree with "deps1 deps2") as %<-.
    iSplit; first done.
    iDestruct (own_valid_2 with "RS1 RS2") as "V".
    iDestruct (prod_valid_5th with "V") as %V1.
    iDestruct (own_valid_2 with "PS1 PS2") as "V2".
    iDestruct (prod_valid_6th with "V2") as %V2.
    iPureIntro.
    unfold gNC, gC in V1, V2.
    apply gen_nc_op_valid in V1, V2.
    rewrite comm in V1.
    rewrite comm in V2.
    apply mono_list_both_dfrac_valid_L in V1 as [_ pref1].
    apply mono_list_both_dfrac_valid_L in V2 as [_ pref2].
    eapply pred_prefix_list_for_prefix_of in prefList; try done; last apply _.
    apply prefList.
    done.
  Qed.

End own_promises_properties.

(* In the following section we prove structural rules of the nextgen modality.
 * and add the modality instances for the proof mode. *)

Class IntoNextgen `{Ω : gGenCmras Σ} (P : iProp Σ) (Q : iProp Σ) :=
  into_nextgen : P ⊢ ⚡==> Q.
Global Arguments IntoNextgen  {_ _} _%I _%I.
Global Arguments into_nextgen {_ _} _%I _%I.
Global Hint Mode IntoNextgen + + + - : typeclass_instances.

Section nextgen_structural_properties.
  Context {Σ : gFunctors} {Ω : gGenCmras Σ}.
  Implicit Types (P : iProp Σ) (Q : iProp Σ).

  Lemma own_picks_empty :
    ⊢@{iProp Σ} own_picks (λ i, ∅).
  Proof. iIntros (????). done. Qed.

  Lemma own_promises_empty :
    ⊢@{iProp Σ} own_promises [].
  Proof. iApply big_sepL_nil. done. Qed.

  (* Helper lemma to show things under the nextgen modality when you do not
   * care about the picks and promises. *)
  Lemma nextgen_empty P :
    (∀ full_picks (val : transmap_valid full_picks),
    let _ := build_trans_generation full_picks val in
    ⚡={build_trans full_picks}=> P)
    ⊢ ⚡==> P.
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    iIntros "HP".
    iExists (λ i, ∅), [].
    iSplit; first done.
    iSplit; first done.
    iSplit; first iApply own_picks_empty.
    iSplit; first iApply own_promises_empty.
    iIntros (????).
    iApply "HP".
  Qed.

  Lemma nextgen_emp_2 : emp ⊢@{iProp Σ} ⚡==> emp.
  Proof.
    iIntros "E".
    iApply nextgen_empty.
    iIntros (full_picks ?).
    iModIntro.
    iFrame "E".
  Qed.

  Lemma big_sepL_forall_elem_of {A} (l : list A) Φ :
    (∀ x, Persistent (Φ x)) →
    ([∗ list] x ∈ l, Φ x) ⊣⊢@{iProp Σ} (∀ x, ⌜x ∈ l⌝ → Φ x).
  Proof.
    intros ?. rewrite big_sepL_forall. iSplit.
    - iIntros "H" (? [? elem]%elem_of_list_lookup_1). iApply "H". done.
    - iIntros "H" (?? ?%elem_of_list_lookup_2). iApply "H". done.
  Qed.

  Lemma own_promises_merge prsL prsR :
    promises_wf Ω.(gc_map_wf) prsL →
    promises_wf Ω.(gc_map_wf) prsR →
    own_promises prsL -∗
    own_promises prsR -∗
    ∃ prsM,
      ⌜ promises_wf Ω.(gc_map_wf) prsM ⌝ ∗
      ⌜ promises_is_valid_merge prsM prsL prsR ⌝ ∗
      own_promises prsM.
  Proof.
    iIntros (wfL wfR) "prL prR".
    iDestruct (own_promises_overlap with "prL prR") as %lap.
    destruct (merge_promises Ω.(gc_map_wf) prsL prsR) as (prsM & ? & ? & ? & ?);
      [done|done|done|].
    iExists prsM.
    iSplit; first done.
    iSplit; first done.
    unfold own_promises.
    rewrite 3!big_sepL_forall_elem_of.
    iIntros (pi elm).
    edestruct (H0) as [elm2|elm2]; first apply elm.
    - iDestruct ("prL" $! _ elm2) as (??) "?".
      iExists _, _. iFrame.
    - iDestruct ("prR" $! _ elm2) as (??) "?".
      iExists _, _. iFrame.
  Qed.

  Lemma nextgen_sep_2 P Q :
    (⚡==> P) ∗ (⚡==> Q) ⊢ ⚡==> (P ∗ Q) .
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    iIntros "[P Q]".
    iNamed "P".
    iDestruct "Q" as (? prs2)
      "(%picksValid2 & %wf2 & ownPicks2 & ownPrs2 & HQ)".
    iDestruct (own_promises_merge prs prs2 with "ownPrs ownPrs2")
        as "(%prs3 & %wf3 & (% & % & %) & prs3)";
      [done|done| ].
    iExists _, prs3.
    iDestruct (own_picks_sep' with "ownPicks ownPicks2") as "[$ %sub]".
    iFrame "prs3".
    iSplit. { iPureIntro. apply transmap_valid_union; done. }
    iSplit; first done.
    iIntros (fp vv a b).
    iSpecialize ("contP" $! fp vv with "[%] [%]").
    { eapply transmap_resp_promises_weak; done. }
    { etrans; last done. apply transmap_union_subseteq_l. }
    iSpecialize ("HQ" $! fp vv with "[%] [%]").
    { eapply transmap_resp_promises_weak; done. }
    { etrans; done. }
    iModIntro.
    iFrame.
  Qed.

  Lemma and_extract_l `{!Persistent P} Q R :
    (P ∗ Q) ∧ R ⊢ P ∗ (Q ∧ R).
  Proof.
    rewrite 1!sep_and. rewrite -and_assoc. rewrite -persistent_and_sep_1. done.
  Qed.

  Lemma and_extract_r `{!Persistent P} Q R :
    Q ∧ (P ∗ R) ⊢ P ∗ (Q ∧ R).
  Proof. rewrite comm. rewrite (comm _ Q). apply and_extract_l. Qed.

  Lemma nextgen_and_1 P Q :
    (⚡==> P) ∧ (⚡==> Q) ⊢ ⚡==> (P ∧ Q).
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    iIntros "PQ".
    rewrite and_exist_r. iDestruct "PQ" as (picks1) "PQ".
    rewrite and_exist_r. iDestruct "PQ" as (prs1) "PQ".
    rewrite and_exist_l. iDestruct "PQ" as (picks2) "PQ".
    rewrite and_exist_l. iDestruct "PQ" as (prs2) "PQ".
    rewrite 4!and_extract_l.
    iDestruct "PQ" as "(%picksValid1 & %prsWf1 & #ownPicks1 & #ownPrs1 & PQ)".
    rewrite 4!and_extract_r.
    iDestruct "PQ" as "(%picksValid2 & %prsWf2 & #ownPicks2 & #ownPrs2 & contPQ)".
    iDestruct (own_promises_merge prs1 prs2 with "ownPrs1 ownPrs2")
        as "(%prs3 & %wf3 & (% & % & %) & prs3)";
      [done|done| ].
    iExists _, prs3.
    iDestruct (own_picks_sep' with "ownPicks1 ownPicks2") as "[$ %sub]".
    iFrame "prs3".
    iSplit. { iPureIntro. apply transmap_valid_union; done. }
    iSplit; first done.
    iIntros (fp vv a b).
    rewrite -bnextgen_and.
    iSplit.
    - iDestruct "contPQ" as "[contP _]".
      iSpecialize ("contP" $! fp vv with "[%] [%]").
      { eapply transmap_resp_promises_weak; done. }
      { etrans; last done. apply transmap_union_subseteq_l. }
      iApply "contP".
    - iDestruct "contPQ" as "[_ contQ]".
      iSpecialize ("contQ" $! fp vv with "[%] [%]").
      { eapply transmap_resp_promises_weak; done. }
      { etrans; done. }
      iApply "contQ".
  Qed.

  Lemma nextgen_intuitionistically_1 P :
    (⚡==> (<pers> P)) ⊢ <pers> (⚡==> P).
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    iIntros "#P". iNamed "P".
    iExists picks, prs.
    iFrame "%#".
    iIntros (?? resp sub).
    iSpecialize ("contP" $! _ _ resp sub).
    iApply bnextgen_intuitionistically_1.
    iModIntro. iApply "contP".
  Qed.

  Lemma nextgen_intuitionistically_2 P :
    <pers> (⚡==> P) ⊢ ⚡==> (<pers> P).
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    iIntros "#P". iNamed "P".
    iExists picks, prs.
    iFrame "%#".
    iIntros (?? resp sub).
    iSpecialize ("contP" $! _ _ resp sub).
    iApply bnextgen_intuitionistically_2.
    iModIntro. iApply "contP".
  Qed.

  Lemma nextgen_mono P Q :
    (P ⊢ Q) → (⚡==> P) ⊢ ⚡==> Q.
  Proof.
    intros Hi.
    rewrite nextgen_unseal /nextgen_def.
    iIntros "P". iNamed "P".
    iExists picks, prs.
    iFrame "%#".
    iIntros (?? resp sub).
    iSpecialize ("contP" $! _ _ resp sub).
    iApply bnextgen_mono'.
    - apply Hi.
    - iApply "contP".
  Qed.

  Lemma nextgen_intuitionistically P :
    (⚡==> (<pers> P)) ⊣⊢ <pers> (⚡==> P).
  Proof.
    iSplit.
    - iApply nextgen_intuitionistically_1.
    - iApply nextgen_intuitionistically_2.
  Qed.

  #[global]
  Instance nextgen_ne : NonExpansive nextgen.
  Proof. rewrite nextgen_unseal. solve_proper. Qed.

  Global Instance nextgen_mono' :
    Proper ((⊢) ==> (⊢)) nextgen.
  Proof. intros P Q. apply nextgen_mono. Qed.

  Global Instance nextgen_proper :
    Proper ((≡) ==> (≡)) nextgen := ne_proper _.

  Lemma modality_bnextgen_mixin :
    modality_mixin (@nextgen _ _)
      (MIEnvTransform IntoNextgen) (MIEnvTransform IntoNextgen).
  Proof.
    split; simpl; split_and?.
    - intros ?? Hi.
      rewrite Hi.
      rewrite 2!intuitionistically_into_persistently.
      apply nextgen_intuitionistically_2.
    - intros. rewrite nextgen_and_1. done.
    - done.
    - apply nextgen_emp_2.
    - apply nextgen_mono.
    - apply nextgen_sep_2.
  Qed.
  Definition modality_bnextgen :=
    Modality _ modality_bnextgen_mixin.

  Global Instance from_modal_bnextgen P :
    FromModal True modality_bnextgen (⚡==> P) (⚡==> P) P | 1.
  Proof. by rewrite /FromModal. Qed.

  (* Some [IntoNextgen] instances *)

  #[global]
  Instance into_nextgen_nextgen P :
    IntoNextgen (⚡==> P) P.
  Proof. done. Qed.

  Global Instance into_nextgen_exist {A} (Ψ Ψ' : A → _) :
    (∀ x : A, IntoNextgen (Ψ x) (Ψ' x)) →
    IntoNextgen (∃ x : A, Ψ x) (∃ x : A, Ψ' x).
  Proof.
    intros ?. unfold IntoNextgen. iIntros "(% & ?)".
    iModIntro. iExists x. done.
  Qed.

  Lemma nextgen_forall {A} Ψ :
    (⚡==> (∀ a : A, Ψ a)) ⊣⊢ (∀ a : A, ⚡==> Ψ a).
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    setoid_rewrite bnextgen_forall.
    iSplit.
    - iNamed 1. iIntros (a).
      iExists picks, prs. iFrame "%#".
      iIntros (????).
      iSpecialize ("contP" $! full_picks val H H0 a).
      done.
    - iIntros "H".
  Abort.

  Lemma nextgen_intro_plain P `{!Plain P} :
    P ⊢ ⚡==> P.
  Proof.
    iIntros "HP".
    iApply nextgen_empty.
    iIntros (??).
    iModIntro.
    done.
  Qed.

  #[global]
  Instance plain_into_nextgen P `{!Plain P} : IntoNextgen _ _ :=
    nextgen_intro_plain P.

End nextgen_structural_properties.
