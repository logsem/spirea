From Equations Require Import Equations.
From iris.base_logic.lib Require Export own.

From self Require Import hvec gen_trans.
From self.nextgen Require Import types generational_cmra omega.

Import EqNotations. (* Get the [rew] notation. *)

(** The transformations [ts] satisfies the predicates [ps]. *)
Equations preds_hold {n} {DS : ivec n cmra}
    (ps : preds_for n DS) (ts : trans_for n DS) : Prop :=
  @preds_hold _ (icons _ DS') (hcons p ps') (hcons t ts') := p t ∧ preds_hold ps' ts';
  @preds_hold _ (inil) hnil hnil := True.
Global Transparent preds_hold.

Lemma preds_hold_alt {n DS} (ps : preds_for n DS) (ts : trans_for n DS) :
  preds_hold ps ts ↔ ∀ (i : fin n), (hvec_lookup_fmap ps i) (hvec_lookup_fmap ts i).
Proof.
  split.
  - intros holds i.
    induction i as [?|?? IH] eqn:eq.
    * dependent elimination DS.
      dependent elimination ts.
      dependent elimination ps.
      destruct holds as [pred ?].
      apply pred.
    * dependent elimination DS.
      dependent elimination ts.
      dependent elimination ps.
      rewrite preds_hold_equation_2 in holds.
      destruct holds as [? holds].
      apply (IH  _ _ _ holds t).
      done.
  - intros i.
    induction DS as [|??? IH].
    * dependent elimination ts.
      dependent elimination ps.
      done.
    * dependent elimination ts.
      dependent elimination ps.
      rewrite preds_hold_equation_2.
      split. { apply (i 0%fin). }
      apply IH.
      intros i'.
      apply (i (FS i')).
Qed.

(** Inside the model of the [nextgen] modality we need to store a list of all
 * known promises. To this end, [promise_info] is a record of all the
 * information that is associated with a promise. Note that we use
 * [promise_self_info] for the dependencies, this cuts off what would
 * otherwise be an inductive record - simplifying things at the cost of some
 * power.
 *
 * NOTE: We can not store cameras directly in [promise_info] as that leads to
 * universe issues (in particular, any Iris existential quantification over
 * something involing a [cmra] fails. We hence store all cameras in [Ω] and
 * look up into it). *)
Record promise_info_at {Σ} (Ω : gGenCmras Σ) id := MkPia {
  (* We have the generational cmra data for this index, this contains all
   * static info about the promise dependency for this index. *)
  pi_deps_γs : ivec (On Ω id) gname;
  (* Dynamic information that changes per promise *)
  pi_deps_preds : preds_for (On Ω id) (Ocs Ω id);
  (* The predicate that relates our transformation to those of the dependencies. *)
  (* NOTE: Maybe store the rel in curried form? *)
  pi_rel : rel_over (Ocs Ω id) (Oc Ω id);
  (* A predicate that holds for the promise's own transformation whenever
   * [pi_rel] holds. A "canonical" choice could be: [λ t, ∃ ts, pi_rel ts t]. *)
  pi_pred : pred_over (Oc Ω id);
  pi_rel_to_pred : ∀ (ts : trans_for (On Ω id) (Ocs Ω id)) t,
    huncurry pi_rel ts t → pi_pred t;
  pi_witness : ∀ (ts : trans_for (On Ω id) (Ocs Ω id)),
    preds_hold pi_deps_preds ts → (* If we can procure such a [ts] .. *)
    ∃ t, GenTrans t ∧ huncurry pi_rel ts t; (* .. we can get such a [t]. *)
}.

Record promise_info {Σ} (Ω : gGenCmras Σ) := MkPi {
  (* We need to know the specific ghost location that this promise is about *)
  pi_id : ggid Ω; (* The index of the RA in the global RA *)
  pi_γ : gname; (* Ghost name for the promise *)
  (* With this coercion the inner [promise_info_at] record behaves as if it was
   * included in [promise_info] directly. *)
  pi_at :> promise_info_at Ω pi_id;
}.

(* Check that we can existentially quantify over [promise_info] without
 * universe inconsistencies. *)
#[local] Definition promise_info_universe_test {Σ} {Ω : gGenCmras Σ} : iProp Σ :=
  ∃ (ps : promise_info Ω), True.

Arguments MkPi {_ _}.

Arguments pi_id {_ _}.
Arguments pi_γ {_ _}.
Arguments pi_at {_ _}.

Arguments pi_deps_γs {_ _ _}.
Arguments pi_deps_preds {_ _ _}.
Arguments pi_rel {_ _ _}.
Arguments pi_pred {_ _ _}.
Arguments pi_rel_to_pred {_ _ _}.
Arguments pi_witness {_ _ _}.

Definition pi_deps_id `{Ω : gGenCmras Σ} pi idx := Oids Ω pi.(pi_id) !!! idx.

Definition pi_deps_pred `{Ω : gGenCmras Σ} pi idx wf :=
  let id := pi_deps_id pi idx in
  lookup_fmap_Ocs pi.(pi_deps_preds) idx wf.

Section promise_info.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (prs : list (promise_info Ω)).
  Implicit Types (promises : list (promise_info Ω)).
  Implicit Types (pi : promise_info Ω).
  Implicit Types (γ : gname).

  Definition promises_different p1 p2 :=
    path_different p1.(pi_id) p1.(pi_γ) p2.(pi_id) p2.(pi_γ).

  (* Lemmas for [promises_different]. *)
  Lemma promises_different_not_eq pi1 pi2 :
    ¬ (pi1.(pi_id) = pi2.(pi_id) ∧ pi1.(pi_γ) = pi2.(pi_γ)) →
    promises_different pi1 pi2.
  Proof.
    intros n.
    destruct pi1, pi2.
    rewrite /promises_different /path_different. simpl.
    destruct (decide (pi_id0 = pi_id1));
      destruct (decide (pi_γ0 = pi_γ1)); naive_solver.
  Qed.

  Lemma promises_different_sym p1 p2 :
    promises_different p1 p2 → promises_different p2 p1.
  Proof. rewrite /promises_different /path_different. intros [?|?]; auto using not_eq_sym. Qed.

  Equations promises_lookup_at promises iid (γ : gname) : option (promise_info_at _ iid) :=
  | [], iid, γ => None
  | p :: ps', iid, γ with decide (p.(pi_id) = iid), decide (p.(pi_γ) = γ) => {
    | left eq_refl, left eq_refl => Some p.(pi_at);
    | left eq_refl, right _ => promises_lookup_at ps' p.(pi_id) γ
    | right _, _ => promises_lookup_at ps' iid γ
  }.

  Lemma promises_lookup_at_cons_Some_inv prs pi id γ pia :
    promises_lookup_at (pi :: prs) id γ = Some pia →
    (∃ (eq : pi.(pi_id) = id), pi.(pi_γ) = γ ∧ (rew eq in pi.(pi_at) = pia)) ∨
    ((pi.(pi_id) ≠ id ∨ pi.(pi_γ) ≠ γ) ∧ promises_lookup_at prs id γ = Some pia).
  Proof.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1 /=.
    destruct (decide (pi.(pi_id) = id)) as [eq|?]; last naive_solver.
    destruct (decide (pi.(pi_γ) = γ)) as [eq2|?]; last naive_solver.
    destruct eq. destruct eq2.
    rewrite promises_lookup_at_clause_2_clause_1_equation_1.
    intros ?. left. exists eq_refl. naive_solver.
  Qed.

  Lemma promises_lookup_at_cons_neq prs pi id2 γ2 :
    (pi.(pi_id) ≠ id2 ∨ pi.(pi_γ) ≠ γ2) →
    promises_lookup_at (pi :: prs) id2 γ2 =
      promises_lookup_at prs id2 γ2.
  Proof.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1 /=.
    intros [neq|neq];
      destruct (decide (pi.(pi_id) = id2)) as [<-|?]; try done.
    destruct (decide (pi.(pi_γ) = γ2)) as [?|?]; done.
  Qed.

  Lemma promises_lookup_at_cons_None prs id γ pi :
    promises_lookup_at (pi :: prs) id γ = None ↔
    promises_lookup_at prs id γ = None ∧ (pi.(pi_id) ≠ id ∨ pi.(pi_γ) ≠ γ).
  Proof.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1.
    destruct pi as [id' γ' ?].
    destruct (decide (id' = id)) as [->|neq1] eqn:eqI;
      destruct (decide (γ' = γ)) as [->|neq2] eqn:eqG;
      rewrite eqI eqG; naive_solver.
  Qed.

   Lemma promises_lookup_at_None prs id γ :
    promises_lookup_at prs id γ = None ↔
    (∀ pi2, pi2 ∈ prs → path_different id γ pi2.(pi_id) pi2.(pi_γ)).
  Proof.
    induction prs as [|?? IH].
    { split; first inversion 2. naive_solver. }
    rewrite promises_lookup_at_cons_None.
    split.
    * simpl.
      intros [eq diff] ? [<-|?]%elem_of_cons.
      - rewrite /promises_different /path_different. naive_solver.
      - apply IH; done.
    * intros A.
      split.
      - apply IH. intros pi ?. apply A. apply elem_of_list_further. done.
      - destruct (A a) as [?|?]; first apply elem_of_list_here; naive_solver.
  Qed.

  Definition res_trans_transport {id1 id2}
      (eq : id1 = id2) (t : R Σ id1 → R Σ id1) : (R Σ id2 → R Σ id2) :=
    eq_rect _ (λ id, _) t _ eq.

  Definition res_pred_transport {id1 id2} (eq : id1 = id2)
      (t : (R Σ id1 → R Σ id1) → Prop) : ((R Σ id2 → R Σ id2) → Prop) :=
    eq_rect _ (λ id, _) t _ eq.

  Definition gcd_transport {id1 id2}
      (eq : id1 = id2) (gcd : gen_cmra_data Σ id1) : gen_cmra_data Σ id2 :=
    eq_rect _ (λ id, _) gcd _ eq.

  (* Definition promise_satisfy_dep (pi : promise_info Ω) idx γ *)
  (*     (piaSat : promise_info_at _ (Oids Ω pi.(pi_id) !!! idx)) wf := *)
  (*   let pred : pred_over (Oc Ω _) := lookup_fmap_Ocs pi.(pi_deps_preds) idx wf in *)
  (*   pred_stronger piaSat.(pi_pred) pred. *)

  (* Definition promises_has_deps pi promises wf := *)
  (*   ∀ idx, ∃ piaSat, *)
  (*     let dep_id := Oids Ω pi.(pi_id) !!! idx in *)
  (*     promises_lookup_at promises dep_id (pi.(pi_deps_γs) !!! idx) = Some piaSat ∧ *)
  (*     promise_satisfy_dep pi idx (pi.(pi_deps_γs) !!! idx) piaSat wf. *)

  Definition promise_satisfy_dep_raw
      (id : ggid Ω) (dep_γ : gname) (pred : pred_over (Oc Ω id)) piSat :=
    dep_γ = piSat.(pi_γ) ∧
    ∃ (eq : id = piSat.(pi_id)),
      (* The predicate in [piSat] is stronger than what is stated in [pi]. *)
      pred_stronger piSat.(pi_pred) (rew [λ id, pred_over (Oc Ω id)] eq in pred).

  Definition promises_has_deps_raw {n}
      (ids : fin n → ggid Ω) (deps_γs : ivec n gname)
      (preds : ∀ idx, pred_over (Oc Ω (ids idx))) promises :=
    ∀ (idx : fin n), ∃ piSat, piSat ∈ promises ∧
      promise_satisfy_dep_raw (ids idx) (deps_γs !!! idx) (preds idx) piSat.

  (** For every dependency in [pi] the list [prs] has a sufficient promise. *)
  Definition promises_has_deps pi prs wf :=
    promises_has_deps_raw
      (λ idx, Oids Ω pi.(pi_id) !!! idx) pi.(pi_deps_γs)
      (λ idx, lookup_fmap_Ocs pi.(pi_deps_preds) idx wf)
      prs.

  (** The promise [piSat] satisfies the dependency at [idx] of [pi]. Note that
   * the predicate in [pi] may not be the same as the one in [piSat]. When we
   * combine lists of promises some promises might be replaced by stronger
   * ones. Hence we only require that the predicate in [piSat] is stronger than
   * the one in [pi]. *)
  Definition promise_satisfy_dep (pi piSat : promise_info Ω) idx wf :=
    promise_satisfy_dep_raw
      (Oids Ω pi.(pi_id) !!! idx) (pi.(pi_deps_γs) !!! idx)
      (lookup_fmap_Ocs pi.(pi_deps_preds) idx wf) piSat.

  Lemma promise_satisfy_dep_rel_stronger pi idx wf id γ pSat1 pSat2 :
    promise_satisfy_dep pi (MkPi id γ pSat1) idx wf →
    pred_stronger pSat2.(pi_pred) pSat1.(pi_pred) →
    promise_satisfy_dep pi (MkPi id γ pSat2) idx wf.
  Proof.
    intros (? & eq & ?) ?.
    split; first done.
    exists eq.
    etrans; done.
  Qed.

  (** The promise [p] is well-formed wrt. the list [promises] of promises that
   * preceeded it. *)
  Definition promise_wf pi prs wf : Prop :=
    promises_lookup_at prs pi.(pi_id) pi.(pi_γ) = None ∧
    promises_has_deps pi prs wf.

  (* This definition has nice computational behavior when applied to a [cons]. *)
  Fixpoint promises_wf (owf : omega_wf (gc_map Ω)) promises : Prop :=
    match promises with
    | nil => True
    | cons p promises' =>
        promise_wf p promises' (owf p.(pi_id)) ∧ promises_wf owf promises'
    end.

  Lemma promises_wf_unique owf prs :
    promises_wf owf prs →
    ∀ pi1 pi2, pi1 ∈ prs → pi2 ∈ prs → pi1 = pi2 ∨ promises_different pi1 pi2.
  Proof.
    induction prs as [| ?? IH].
    { intros ???. inversion 1. }
    intros [wf ?] pi1 pi2. inversion 1; inversion 1; subst; try naive_solver.
    - right. eapply promises_lookup_at_None; first apply wf. done.
    - right. apply promises_different_sym.
      eapply promises_lookup_at_None; first apply wf. done.
  Qed.

  (* NOTE: Not used, but should be implied by [promises_wf] *)
  Definition promises_unique promises : Prop :=
    ∀ (i j : nat) pi1 pi2, i ≠ j →
      pi1.(pi_id) ≠ pi2.(pi_id) ∨ pi1.(pi_γ) ≠ pi2.(pi_γ).

  Lemma promises_has_deps_weaken_cons p prs wf :
    promises_has_deps p prs wf →
    promises_has_deps p (p :: prs) wf.
  Proof.
    intros hasDeps idx.
    destruct (hasDeps idx) as (p2 & ? & ?).
    eauto using elem_of_list_further.
  Qed.

  Lemma promises_has_deps_weaken_app p prs1 prs2 wf :
    promises_has_deps p prs2 wf →
    promises_has_deps p (prs1 ++ prs2) wf.
  Proof.
    intros hasDeps idx.
    destruct (hasDeps idx) as (p2 & ? & ?).
    setoid_rewrite elem_of_app.
    naive_solver.
  Qed.

  (* A well formed promise is not equal to any of its dependencies. *)
  Lemma promise_wf_neq_deps p promises wf :
    promise_wf p promises wf →
    ∀ (idx : fin (On Ω p.(pi_id))),
      p.(pi_id) ≠ (pi_deps_id p idx) ∨ p.(pi_γ) ≠ p.(pi_deps_γs) !!! idx.
  Proof.
    intros [look hasDeps] idx.
    destruct (hasDeps idx) as (p2 & elem & idEq & γEq & jhhi).
    rewrite /pi_deps_id idEq γEq.
    eapply promises_lookup_at_None; first apply look. done.
  Qed.

  Lemma promises_wf_lookup_at prs pi :
    promises_wf gc_map_wf prs →
    promises_lookup_at prs (pi_id pi) (pi_γ pi) = Some pi.(pi_at) →
    ∃ i, prs !! i = Some pi ∧
         promises_has_deps pi (drop (S i) prs) (gc_map_wf pi.(pi_id)).
  Proof.
    induction prs as [|pi2 prs IH]; first done.
    intros [wfPi wf].
    intros [(? & ? & ?)|(? & look)]%promises_lookup_at_cons_Some_inv.
    { exists 0. simpl.
      destruct pi2. destruct pi. simpl in *.
      simplify_eq.
      split; first done.
      destruct wfPi as [??].
      done. }
    apply (IH wf) in look as (i & ?).
    exists (S i). done.
  Qed.

  Lemma promises_well_formed_lookup owf promises (idx : nat) pi :
    promises_wf owf promises →
    promises !! idx = Some pi →
    promises_has_deps pi promises (owf (pi_id pi)). (* We forget the different part for now. *)
  Proof.
    intros WF look.
    revert dependent idx.
    induction promises as [ |?? IH]; first intros ? [=].
    destruct WF as [[? hasDeps] WF'].
    intros [ | idx].
    * simpl. intros [= ->].
      apply promises_has_deps_weaken_cons.
      done.
    * intros look.
      intros d.
      destruct (IH WF' idx look d) as (? & ? & ?).
      eauto using elem_of_list_further.
  Qed.

  Lemma promises_well_formed_lookup_index owf prs pi1 i :
    promises_wf owf prs →
    prs !! (length prs - S i) = Some pi1 →
    ∀ (idx : fin (On Ω pi1.(pi_id))),
      ∃ j pi2 wf,
        j < i ∧ prs !! (length prs - S j) = Some pi2 ∧
        promise_satisfy_dep pi1 pi2 idx wf.
  Proof.
    intros wf look idx.
    generalize dependent i.
    induction prs as [|pi prs' IH]; first done.
    simpl. intros i.
    destruct wf as [[? deps] wfr].
    intros look.
    eassert _. { eapply lookup_lt_Some. done. }
    destruct (decide (length prs' ≤ i)).
    * assert (length prs' - i = 0) as eq by lia.
      rewrite eq in look. injection look as [= ->].
      specialize (deps idx) as (piSat & elm & sat).
      apply elem_of_list_lookup_1 in elm as (j' & look).
      exists (length prs' - (S j')), piSat, (owf (pi1.(pi_id))).
      pose proof look as look'.
      apply lookup_lt_Some in look.
      split_and!; last done.
      - lia.
      - replace (length prs' - (length prs' - S j')) with (S j') by lia.
        done.
    * apply not_le in n.
      assert (1 ≤ length prs' - i) as le by lia.
      apply Nat.le_exists_sub in le as (i' & ? & _).
      rewrite (comm (Nat.add)) in H0.
      simpl in H0.
      rewrite H0 in look.
      simpl in look.
      destruct (IH wfr (length prs' - S i')) as (j & ? & ? & ? & ? & ?).
      { replace (length prs' - S (length prs' - S i')) with i' by lia.
        done. }
      eexists j, _, _.
      split_and!; try done; try lia.
      replace (length prs' - j) with (S (length prs' - S j)) by lia.
      done.
  Qed.

  (* For soundness we need to be able to build a map of gts that agree with
   * picks and that satisfy all promises.

     We need to be able to extend picks along a list of promises.

     We must also be able to combine to lists of promises.
  *)

  Equations promises_info_update pi id (γ : gname) (pia : promise_info_at _ id) : promise_info Ω :=
  | pi, id, γ, pia with decide (pi.(pi_id) = id), decide (pi.(pi_γ) = γ) => {
    | left eq_refl, left eq_refl => MkPi pi.(pi_id) pi.(pi_γ) pia;
    | _, _ => pi
    }.

  Lemma promise_info_update_id pi id γ pia :
    pi_id (promises_info_update pi id γ pia) = pi.(pi_id).
  Proof.
    rewrite promises_info_update_equation_1
      promises_info_update_clause_1_equation_1.
    destruct (decide (pi_id pi = id)) as [eq|]; last done.
    destruct (decide (pi_γ pi = γ)) as [[]|];
      destruct eq; done.
  Qed.

  Lemma promise_info_update_γ pi id γ pia :
    pi_γ (promises_info_update pi id γ pia) = pi.(pi_γ).
  Proof.
    rewrite promises_info_update_equation_1
      promises_info_update_clause_1_equation_1.
    destruct (decide (pi_id pi = id)) as [eq|]; last done.
    destruct (decide (pi_γ pi = γ)) as [[]|];
      destruct eq; done.
  Qed.

  Definition promises_list_update id γ (pia : promise_info_at _ id)
      (prs : list (promise_info Ω)) :=
    (λ pi, promises_info_update pi id γ pia) <$> prs.

  Lemma promises_lookup_at_cons prs id γ pia :
    promises_lookup_at ((MkPi id γ pia) :: prs) id γ = Some pia.
  Proof.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1 /=.
    destruct (decide (id = id)) as [eq|?]; last done.
    destruct (decide (γ = γ)) as [eq2|?]; last done.
    assert (eq = eq_refl) as ->.
    { rewrite (proof_irrel eq eq_refl). done. }
    assert (eq2 = eq_refl) as ->.
    { rewrite (proof_irrel eq2 eq_refl). done. }
    rewrite promises_lookup_at_clause_2_clause_1_equation_1.
    done.
  Qed.

  Lemma promises_lookup_at_cons_pr prs pi :
    promises_lookup_at (pi :: prs) (pi_id pi) (pi_γ pi) = Some pi.(pi_at).
  Proof. destruct pi. apply promises_lookup_at_cons. Qed.

  Lemma promises_lookup_at_Some promises id γ pia :
    promises_lookup_at promises id γ = Some pia →
    MkPi id γ pia ∈ promises.
  Proof.
    induction promises as [|[id' γ' ?] ? IH]; first by inversion 1.
    destruct (decide (id' = id)) as [->|neq].
    - destruct (decide (γ' = γ)) as [->|neq].
      * rewrite promises_lookup_at_cons.
        simpl.
        intros [= <-].
        apply elem_of_list_here.
      * rewrite promises_lookup_at_cons_neq; last naive_solver.
        intros ?.
        apply elem_of_list_further.
        apply IH. done.
    - rewrite promises_lookup_at_cons_neq; last naive_solver.
      intros ?.
      apply elem_of_list_further.
      apply IH. done.
  Qed.

  Lemma promises_lookup_at_Some_lookup prs id γ pia :
    promises_lookup_at prs id γ = Some pia →
    ∃ i, prs !! i = Some (MkPi id γ pia).
  Proof.
    intros ?%promises_lookup_at_Some. apply elem_of_list_lookup_1. done.
  Qed.

  Lemma promises_info_update_self pi pia :
    promises_info_update pi (pi_id pi) (pi_γ pi) pia =
      MkPi (pi_id pi) (pi_γ pi) pia.
  Proof.
    rewrite promises_info_update_equation_1.
    rewrite promises_info_update_clause_1_equation_1.
    destruct (decide (pi_id pi = pi_id pi)) as [eq1|]; last done.
    destruct (decide (pi_γ pi = pi_γ pi)) as [eq2|]; last done.
    destruct eq2.
    assert (eq1 = eq_refl) as ->.
    { rewrite (proof_irrel eq1 eq_refl). done. }
    rewrite promises_info_update_clause_1_clause_1_equation_1.
    done.
  Qed.

  Lemma promises_info_update_ne pi id γ pia :
    path_different pi.(pi_id) pi.(pi_γ) id γ →
    promises_info_update pi id γ pia = pi.
  Proof.
    unfold path_different.
    intros neq.
    rewrite promises_info_update_equation_1.
    rewrite promises_info_update_clause_1_equation_1.
    destruct (decide (pi_id pi = id)) as [<-|]; last done.
    destruct (decide (pi_γ pi = γ)) as [eq2|]; naive_solver.
  Qed.

  Lemma promises_lookup_update prs id γ pia pia' :
    promises_lookup_at prs id γ = Some pia →
    promises_lookup_at (promises_list_update id γ pia' prs) id γ = Some pia'.
  Proof.
    induction prs as [|pi prs' IH]; first done.
    intros [(<- & <- & eq)|[neq look]]%promises_lookup_at_cons_Some_inv.
    - simpl in *.
      rewrite promises_info_update_self.
      apply promises_lookup_at_cons.
    - simpl.
      rewrite promises_info_update_ne; last done.
      rewrite promises_lookup_at_cons_neq; last done.
      apply IH.
      done.
  Qed.

  Lemma promises_list_update_elem_of pi id γ pia prs :
    pi ∈ promises_list_update id γ pia prs →
    pi ∈ prs ∨ (pi = MkPi id γ pia ∧ ∃ pia', MkPi id γ pia' ∈ prs).
  Proof.
    unfold promises_list_update.
    intros (pi' & -> & elm)%elem_of_list_fmap_2.
    rewrite promises_info_update_equation_1.
    rewrite promises_info_update_clause_1_equation_1.
    destruct (decide (pi'.(pi_id) = id)) as [<-|]; last naive_solver.
    destruct (decide (pi'.(pi_γ) = γ)) as [<-|]; last naive_solver.
    right.
    split; first naive_solver.
    exists (pi'.(pi_at)).
    destruct pi'.
    apply elm.
  Qed.

  Lemma promises_list_update_elem_of_path id γ pia pi prs :
    pi ∈ promises_list_update id γ pia prs →
    ∃ pia', (MkPi pi.(pi_id) pi.(pi_γ) pia') ∈ prs.
  Proof.
    intros [elm | [-> [pia' elm]]]%promises_list_update_elem_of.
    - exists pi. destruct pi. done.
    - exists pia'. done.
  Qed.

  Lemma promises_list_update_lookup_none prs id γ pia :
    promises_lookup_at prs id γ = None →
    promises_list_update id γ pia prs = prs.
  Proof.
    induction prs as [|pi prs IH]; first done.
    intros [look diff]%promises_lookup_at_cons_None.
    simpl.
    rewrite promises_info_update_ne; last done.
    by rewrite IH.
  Qed.

  Lemma promises_list_update_cons_eq wf pi prs pia :
    promises_wf wf (pi :: prs) →
    promises_list_update (pi_id pi) (pi_γ pi) pia (pi :: prs) =
      MkPi (pi_id pi) (pi_γ pi) pia :: prs.
  Proof.
    intros [pwf ?]. simpl.
    rewrite promises_info_update_self.
    rewrite promises_list_update_lookup_none; first done.
    apply pwf.
  Qed.

  Lemma promises_list_update_cons_ne id γ pia pi prs :
    id ≠ pi_id pi ∨ γ ≠ pi_γ pi →
    promises_list_update id γ pia (pi :: prs) =
      pi :: (promises_list_update id γ pia prs).
  Proof.
    intros ne. simpl. rewrite promises_info_update_ne; first reflexivity.
    unfold path_different.
    naive_solver.
  Qed.

  Lemma promises_wf_elem_of_head owf id γ pia1 pia2 promises :
    promises_wf owf ({| pi_id := id; pi_γ := γ; pi_at := pia2 |} :: promises) →
    {| pi_id := id; pi_γ := γ; pi_at := pia1 |}
      ∈ {| pi_id := id; pi_γ := γ; pi_at := pia2 |} :: promises →
    pia1 = pia2.
  Proof.
    intros [(diff & ?) ?].
    intros [eq|?]%elem_of_cons.
    - inversion eq. apply inj_right_pair. done.
    - eapply promises_lookup_at_None in diff; last done.
      destruct diff as [neq|neq]; simpl in neq; congruence.
  Qed.

  Lemma promises_elem_of owf promises pi :
    promises_wf owf promises →
    pi ∈ promises →
    promises_lookup_at promises pi.(pi_id) pi.(pi_γ) = Some pi.(pi_at).
  Proof.
    destruct pi as [id γ pia].
    intros wf.
    induction promises as [|[id' γ' ?] ? IH]; first by inversion 1.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1.
    simpl.
    destruct (decide (id' = id)) as [->|neq].
    - destruct (decide (γ' = γ)) as [->|neq].
      * simpl.
        intros ?%(promises_wf_elem_of_head owf); [congruence | assumption].
      * rewrite promises_lookup_at_clause_2_clause_1_equation_2.
        simpl.
        intros [?|?]%elem_of_cons; first congruence.
        apply IH; [apply wf | done].
    - rewrite promises_lookup_at_clause_2_clause_1_equation_3.
      intros [?|?]%elem_of_cons; first congruence.
      apply IH; [apply wf | done].
  Qed.

  Lemma promises_lookup_at_update id1 γ1 id2 γ2 pia prs :
    path_different id1 γ1 id2 γ2 →
    promises_lookup_at (promises_list_update id1 γ1 pia prs) id2 γ2 =
      promises_lookup_at prs id2 γ2.
  Proof.
    intros diff.
    induction prs as [|pi prs IH]; first done.
    simpl.
    destruct (path_equal_or_different id2 pi.(pi_id) γ2 pi.(pi_γ))
      as [(-> & ->) | neq].
    - simpl.
      rewrite promises_lookup_at_cons_pr.
      rewrite promises_info_update_ne.
      2: { apply path_different_sym. done. }
      apply promises_lookup_at_cons_pr.
    - rewrite promises_lookup_at_cons_neq.
      2: {
        apply path_different_sym.
        rewrite promise_info_update_id promise_info_update_γ.
        done. }
      rewrite promises_lookup_at_cons_neq.
      { apply IH. }
      apply path_different_sym. done.
  Qed.

  Lemma promises_list_update_elem_of_2 wf pi id γ pia prs :
    promises_wf wf prs →
    pi ∈ prs →
    (pi ∈ promises_list_update id γ pia prs ∧
      path_different id γ pi.(pi_id) pi.(pi_γ)) ∨
    (MkPi id γ pia ∈ promises_list_update id γ pia prs ∧
      id = pi.(pi_id) ∧ γ = pi.(pi_γ)).
  Proof.
    intros ? elm.
    destruct (path_equal_or_different id pi.(pi_id) γ pi.(pi_γ))
      as [(-> & ->) | neq].
    - right. split_and!; try done.
      apply promises_lookup_at_Some.
      eapply promises_elem_of in elm; last done.
      eapply promises_lookup_update.
      done.
    - left. split; last done.
      destruct pi.
      apply promises_lookup_at_Some.
      rewrite promises_lookup_at_update; last done.
      eapply promises_elem_of in elm; last done.
      done.
  Qed.

  Lemma promise_lookup_lookup owf prs pi i :
    promises_wf owf prs →
    prs !! i = Some pi →
    promises_lookup_at prs pi.(pi_id) pi.(pi_γ) = Some pi.(pi_at).
  Proof.
    intros wf look.
    eapply promises_elem_of; first done.
    destruct pi.
    eapply elem_of_list_lookup_2.
    apply look.
  Qed.

  Lemma promise_lookup_at_eq owf id γ prs pia pia' :
    promises_wf owf prs →
    promises_lookup_at prs id γ = Some pia →
    promises_lookup_at prs id γ = Some pia' →
    pia = pia'.
  Proof.
    intros wf.
    intros look%promises_lookup_at_Some.
    intros ?%promises_lookup_at_Some.
    eapply promises_wf_unique in look; [ |done|done].
    destruct look as [[=]|HD].
    - apply inj_right_pair. done.
    - unfold promises_different, path_different in HD. naive_solver.
  Qed.

  (** [pia1] is a better promise than [pia2]. *)
  Definition promise_stronger {id} (pia1 pia2 : promise_info_at _ id) : Prop :=
    pia1.(pi_deps_γs) = pia2.(pi_deps_γs) ∧
    rel_stronger pia1.(pi_rel) pia2.(pi_rel) ∧
    pred_stronger pia1.(pi_pred) pia2.(pi_pred).

  Lemma promise_stronger_refl {id} (pia : promise_info_at _ id) :
    promise_stronger pia pia.
  Proof. split_and!; first done; intros ?; naive_solver. Qed.

  (** This definition is supposed to encapsulate what ownership over the
   * resources for [prs1] and [prsR] entails. *)
  Definition promises_overlap_pred prs1 prsR : Prop :=
    ∀ id γ p1 p2,
      promises_lookup_at prs1 id γ = Some p1 →
      promises_lookup_at prsR id γ = Some p2 →
      promise_stronger p1 p2 ∨ promise_stronger p2 p1.

  Lemma promises_overlap_pred_sym prsL prsR :
    promises_overlap_pred prsL prsR ↔ promises_overlap_pred prsR prsL.
  Proof.
    unfold promises_overlap_pred.
    split; intros Ha; intros; rewrite comm; naive_solver.
  Qed.

  (* NOTE: We can not merge promises with a definition as we need to rely
   * on evidence that is in [Prop]. *)
  (* Fixpoint merge_promises prs1 prsR := .. *)

  (** For every promise in [prsR] there is a stronger promise in [prs1]. *)
  Definition promise_list_stronger prs1 prsR : Prop :=
    ∀ id γ pia2,
      promises_lookup_at prsR id γ = Some pia2 →
      ∃ pia1,
        promises_lookup_at prs1 id γ = Some pia1 ∧
        promise_stronger pia1 pia2.

  (** For every promise in [prsR] there is a stronger promise in [prs1]. *)
  Definition promise_list_restrict_stronger prs1 prsR (restrict : list (ggid Ω * gname)) : Prop :=
    ∀ id γ pia2,
      (id, γ) ∈ restrict →
      promises_lookup_at prsR id γ = Some pia2 →
      ∃ pia1,
        promises_lookup_at prs1 id γ = Some pia1 ∧
        promise_stronger pia1 pia2.

  (** For every promise in [prsR] and [prsM] the one in [prsM] is stronger. *)
  Definition promise_list_overlap_stronger prsM prsR : Prop :=
    ∀ id γ pia2 pia1,
      promises_lookup_at prsM id γ = Some pia1 →
      promises_lookup_at prsR id γ = Some pia2 →
        promise_stronger pia1 pia2.

  Definition promise_list_promise_stronger id γ pia prs :=
    ∀ pia1,
      promises_lookup_at prs id γ = Some pia1 → promise_stronger pia pia1.

  Lemma elem_of_elem_of_cons {A} x y (xs : list A) :
    x ∈ xs →
    y ∈ (x :: xs) ↔ y ∈ xs.
  Proof. intros elm. rewrite elem_of_cons. naive_solver. Qed.

  Lemma elem_of_cons_ne {A} x y (l : list A) :
    x ≠ y → x ∈ cons y l → x ∈ l.
  Proof. intros neq. inversion 1; try congruence. Qed.

  Lemma promise_list_restrict_stronger_cons id γ prs3 pia3 prs1 restrict :
    promise_list_overlap_stronger prs3 prs1 →
    promises_lookup_at prs3 id γ = Some pia3 →
    promise_list_restrict_stronger prs3 prs1 restrict →
    promise_list_restrict_stronger prs3 prs1 ((id, γ) :: restrict).
  Proof.
    intros lap look3 res id2 γ2 ?.
    destruct (decide ((id2, γ2) = (id, γ))) as [[= -> ->]|neq].
    - intros _ look2. exists pia3. split; first done.
      eapply lap; done.
    - intros elm. apply res.
      eapply elem_of_cons_ne; done.
  Qed.

  Definition promises_is_valid_restricted_merge prsM prs1 prsR restrict :=
    (* [prsM] has no junk, everything in it is "good". *)
    (∀ pi, pi ∈ prsM → (pi ∈ prs1 ∨ pi ∈ prsR)) ∧
    promise_list_overlap_stronger prsM prs1 ∧
    promise_list_overlap_stronger prsM prsR ∧
    (* [prsM] has enough promises, everything required by [restrict] is there. *)
    promise_list_restrict_stronger prsM prs1 restrict ∧
    promise_list_restrict_stronger prsM prsR restrict.

  Lemma promises_is_valid_restricted_merge_sym prsM prsL prsR restrict :
    promises_is_valid_restricted_merge prsM prsL prsR restrict ↔
      promises_is_valid_restricted_merge prsM prsR prsL restrict.
  Proof.
    unfold promises_is_valid_restricted_merge.
    naive_solver.
  Qed.

  Lemma promise_list_valid_restricted_merge_cons pi prsM prsL prsR restrict :
    pi ∈ prsL ∨ pi ∈ prsR →
    (∀ pia1,
      promises_lookup_at prsL pi.(pi_id) pi.(pi_γ) = Some pia1 →
      promise_stronger pi pia1) →
    (∀ pia2,
      promises_lookup_at prsR pi.(pi_id) pi.(pi_γ) = Some pia2 →
      promise_stronger pi pia2) →
    promises_is_valid_restricted_merge prsM prsL prsR restrict →
    promises_is_valid_restricted_merge (pi :: prsM) prsL prsR restrict.
  Proof.
    intros elm strL strR (elm2 & lsL & lsR & rsL & rsR). split_and!.
    - intros ?. inversion 1; naive_solver.
    - intros ???? look.
      apply promises_lookup_at_cons_Some_inv in look as [(eqId & eqγ & eq)|(? & look)].
      * destruct eqId, eqγ. rewrite -eq. apply strL.
      * apply lsL. done.
    - intros ???? look.
      apply promises_lookup_at_cons_Some_inv in look as [(eqId & eqγ & eq)|(? & look)].
      * destruct eqId, eqγ. rewrite -eq. apply strR.
      * apply lsR. done.
    - intros ???? look.
      destruct (path_equal_or_different id pi.(pi_id) γ pi.(pi_γ))
        as [(-> & ->) | neq].
      * exists pi.
        split; last apply strL; last done.
        apply promises_lookup_at_cons_pr.
      * apply rsL in look as (pia1 & ?); last done.
        exists pia1.
        destruct pi.
        simpl in neq.
        rewrite promises_lookup_at_cons_neq; first done.
        simpl.
        unfold path_different in neq.
        naive_solver.
    - intros ???? look.
      destruct (path_equal_or_different id pi.(pi_id) γ pi.(pi_γ))
        as [(-> & ->) | neq].
      * exists pi.
        split; last apply strR; last done.
        apply promises_lookup_at_cons_pr.
      * apply rsR in look as (pia1 & ?); last done.
        exists pia1.
        destruct pi.
        simpl in neq.
        rewrite promises_lookup_at_cons_neq; first done.
        simpl.
        unfold path_different in neq.
        naive_solver.
  Qed.

  Lemma promise_stronger_pred_stronger id (pia1 pia2 : promise_info_at Ω id) :
    promise_stronger pia1 pia2 → pred_stronger pia1.(pi_pred) pia2.(pi_pred).
  Proof. unfold promise_stronger. naive_solver. Qed.

  Lemma promises_is_valid_restricted_merge_stronger
      owf prsM prsR prsL restrict id γ pia1 pia2 :
    ((MkPi id γ pia1) ∈ prsL ∨ (MkPi id γ pia1) ∈ prsR) →
    promises_wf owf prsL →
    promises_wf owf prsR →
    promises_lookup_at prsM id γ = Some pia2 →
    promises_is_valid_restricted_merge prsM prsL prsR restrict →
    promise_stronger pia2 (MkPi id γ pia1).
  Proof.
    intros [elm|elm] ? ? look (? & str1 & str2 & ? & ?).
    - eapply str1; first done.
      eapply (promises_elem_of _ _ (MkPi id γ pia1)); try done.
    - eapply str2; first done.
      eapply (promises_elem_of _ _ (MkPi id γ pia1)); try done.
  Qed.

  (* Get the strongest promise from [prsL] and [prsR]. *)
  Lemma overlap_lookup_left owf prsL prsR id γ pia :
    promises_lookup_at prsL id γ = Some pia →
    promises_overlap_pred prsL prsR →
    promises_wf owf prsL →
    promises_wf owf prsR →
    ∃ pia',
      ((MkPi id γ pia') ∈ prsL ∨ (MkPi id γ pia') ∈ prsR) ∧
      promise_stronger pia' pia ∧
      (∀ pia2,
        promises_lookup_at prsR id γ = Some pia2 →
        promise_stronger pia' pia2).
  Proof.
    intros look1 lap wf1 wf2.
    destruct (promises_lookup_at prsR id γ) as [pia2|] eqn:look2.
    - edestruct lap as [?|?]; [apply look1 | apply look2 | | ].
      + exists pia.
        split_and!.
        * left. apply promises_lookup_at_Some. done.
        * apply promise_stronger_refl.
        * intros pia' [= ->]. done.
      + exists pia2.
        split_and!.
        * right. apply promises_lookup_at_Some. done.
        * done.
        * intros ? [= ->]. apply promise_stronger_refl.
    - exists pia.
      split_and!.
      + left. apply promises_lookup_at_Some. done.
      + apply promise_stronger_refl.
      + naive_solver.
  Qed.

  Lemma promises_well_formed_in_either owf prsL prsR pi wf :
    owf pi.(pi_id) = wf →
    promises_wf owf prsL →
    promises_wf owf prsR →
    (pi ∈ prsL ∨ pi ∈ prsR) →
    ∀ (idx : fin (On Ω pi.(pi_id))),
      ∃ piSat,
        (piSat ∈ prsL ∨ piSat ∈ prsR) ∧
        (* promise_satisfy_dep pi piSat idx wf. *)
        promise_satisfy_dep pi piSat idx wf.
  Proof.
    intros eq wf1 wf2 [[idx look]%elem_of_list_lookup_1 |
                    [idx look]%elem_of_list_lookup_1].
    - intros i.
      eapply promises_well_formed_lookup in wf1; last done.
      destruct (wf1 i) as (piSat & rest).
      exists piSat. naive_solver.
    - intros i.
      eapply promises_well_formed_lookup in wf2; last done.
      destruct (wf2 i) as (piSat & rest).
      exists piSat. naive_solver.
  Qed.

  (* This test serves to demonstrate how destructuring [gc_map Ω id] with some
   * thing of the form [owf id] present in the proof fails. The [generalize
   * dependent] here is necessary for the [destruct] to succeed. A similar
   * destruct is used in the prof of [merge_promises_insert_promise_idx]. *)
  Lemma test_destruct_omega_wf_at (owf : omega_wf (gc_map Ω)) pi piSat idx :
    promise_satisfy_dep pi piSat idx (owf pi.(pi_id)).
  Proof.
    destruct pi. simpl in *.
    unfold promise_satisfy_dep.
    destruct pi_at0. simpl in *.
    unfold Ocs in *.
    unfold lookup_fmap_Ocs in *.
    unfold Ocs_Oids_distr in *.
    unfold lookup_fmap_Ocs in *.
    unfold Ocs_Oids_distr in *.
    unfold Ocs in *.
    unfold Oids in *.
    (* without this generalization the destruct below fails *)
    generalize dependent (owf pi_id0). intros wf.
    unfold omega_wf_at in *.
    destruct (gc_map Ω pi_id0).
  Abort.

  (* Grow [prs3] by inserting the promise id+γ and all of its dependencies from
   * [prsL] and [prsR]. *)
  Lemma merge_promises_insert_promise_idx owf prsL prsR prs3 i pi restrict :
    promises_is_valid_restricted_merge prs3 prsL prsR restrict →
    prsL !! (length prsL - S i) = Some pi →
    promises_overlap_pred prsL prsR →
    promises_wf owf prsL →
    promises_wf owf prsR →
    promises_wf owf prs3 →
    ∃ prs3' pia3,
      promises_lookup_at prs3' (pi.(pi_id)) pi.(pi_γ) = Some pia3 ∧
      promises_wf owf prs3' ∧
      (∀ pi, pi ∈ prs3 → pi ∈ prs3') ∧
      promises_is_valid_restricted_merge prs3' prsL prsR restrict.
  Proof.
    generalize dependent pi.
    generalize dependent prs3.
    induction i as [i IH] using lt_wf_ind.
    intros prs3 [id γ pia] vm look lap wf1 wf2 wf3.
    (* We consider wether the promise is already in the list *)
    destruct (promises_lookup_at prs3 id γ) eqn:notIn.
    { (* The promise is already in the list so inserting it is easy peasy -
       * even a naive solver could do it. *)
      naive_solver. }

    (* We find the promise that we have to insert - the strongest we can find. *)
    edestruct overlap_lookup_left as (piaIns & inEither & stronger & ?).
    { eapply promise_lookup_lookup; last apply look. done. }
    { done. } { done. } { done. }

    (* To add the promise we must first add all of its dependencies. We state
     * that we can do this as a sub-assertion as we need to do a second
     * induction to prove it. *)
    assert (∃ prs3',
      promises_wf owf prs3' ∧
      (∀ pi, pi ∈ prs3 → pi ∈ prs3') ∧
      promises_has_deps (MkPi id γ piaIns) prs3' (owf id) ∧
      promises_is_valid_restricted_merge prs3' prsL prsR restrict)
        as res.
    { simpl.
      specialize (
        promises_well_formed_in_either owf prsL prsR (MkPi id γ piaIns) (owf id) eq_refl wf1 wf2 inEither
      ) as satisfyingPromiseInEither.
      generalize dependent (owf id). intros wf satisfyingPromiseInEither.
      (* We specialize this lemmas such that the following destructs also
       * breaks down this statemens. *)
      specialize (promises_well_formed_lookup_index owf prsL (MkPi id γ pia) i wf1 look) as lem.
      destruct piaIns. simpl in *.
      unfold promise_satisfy_dep in *.
      destruct pia. simpl in *.
      clear look. (* look prevents the destruct below *)
      unfold Ocs in *.
      unfold lookup_fmap_Ocs in *.
      unfold Ocs_Oids_distr in *.
      unfold lookup_fmap_Ocs in *.
      unfold Ocs_Oids_distr in *.
      unfold Ocs in *.
      unfold Oids in *.
      unfold omega_wf_at in *.
      simpl in *.
      destruct stronger as [depsEq impl]. simpl in depsEq. destruct depsEq.
      rewrite /promises_has_deps.
      rewrite /promise_satisfy_dep.
      unfold lookup_fmap_Ocs in *.
      unfold Ocs_Oids_distr in *.
      unfold Ocs in *.
      unfold Oids in *.
      simpl in *.
      clear inEither H.
      simpl in *.
      (* destruct wfEq. *)
      (* clear wfEq. *)
      (* After all the unfolding we can finally carry out this destruct. *)
      destruct (gc_map Ω id).
      simpl in *.
      clear -prs3 notIn vm wf1 wf2 wf3 IH lap lem satisfyingPromiseInEither.
      induction (gcd_n).
      { (* There are no dependencies. *)
        exists prs3.
        split_and!; try done.
        intros idx. inversion idx. }
      (* There is some number of dependencies and all the lists related to the
       * dependencies must be of the [cons] form. *)
      dependent elimination gcd_deps as [icons d_c deps'].
      dependent elimination gcd_deps_ids as [icons d_id deps_ids'].
      dependent elimination pi_deps_γs0 as [icons d_γ deps_γs'].
      dependent elimination pi_deps_preds0 as [hcons piaIns_pred deps_preds'].
      dependent elimination pi_deps_preds1 as [hcons pia_pred prec_deps_preds'].
      (* piaIns_pred should be stronger than pia_pred *)
      (* Insert all but the first dependency using the inner induction hypothesis. *)
      specialize (IHn deps' deps_ids' prec_deps_preds' deps_γs' deps_preds' (λ idx, wf (FS idx))) as (prs3' & ? & sub & hasDeps & vm2).
      { intros idx.
        specialize (satisfyingPromiseInEither (FS idx)) as (piSat & ?).
        exists piSat. done. }
        (* exists piSat, (λ i, wf (FS i)). *)
        (* done. } *)
      { intros idx.
        specialize (lem (FS idx)) as (j & pi2 & wf0 & ? & ? & ? & (? & rest)).
        exists j, pi2, (λ i, wf0 (FS i)).
        rewrite hvec_lookup_fmap_equation_3 in rest.
        unfold promise_satisfy_dep_raw.
        split_and!; naive_solver. }
      specialize (lem 0%fin) as
        (j & piD & ? & le & look2 & lookDeps & idEq & _).
      (* [piD] is the dependency found in [prsL]. *)
      (* Insert the dependency into [prs3] by using the induction hypothesis. *)
      specialize (IH j le _ piD.(pi_at) vm2 look2 lap wf1 wf2 H)
        as (prs3'' & piaD & ? & ? & sub2 & ?).
      specialize (satisfyingPromiseInEither 0%fin) as (piSat & inEither & ? & (idEq' & stronger')).
      (* [piaD] is the promise that we insert to satisfy the first dependency. *)
      (* What is the relationship between [piaD] and the dependency
       * information stored in [piaIns]? *)
        (* piaIns is from prsL or prsR, one of these have a promise that satisfy *)
      exists prs3''.
      split; first done.
      split. { intros ??. apply sub2. apply sub. done. }
      split; last done.
      (* We need to show that [prs3''] satisfies all the dependency
       * predicates of [piaIns]. *)
      intros idx.
      dependent elimination idx as [FS idx|F0]; last first.
      * specialize (hasDeps idx) as (piSat2 & elm & deps & (eq & predStronger)).
        exists piSat2.
        split. { apply sub2. done. }
        split; first done.
        exists eq.
        rewrite hvec_lookup_fmap_equation_3.
        clear -predStronger.
        apply predStronger.
      * exists (MkPi piD.(pi_id) piD.(pi_γ) piaD).
        split. { apply promises_lookup_at_Some. done. }
        split; first done.
        exists idEq.
        simpl.
        rewrite hvec_lookup_fmap_equation_2.
        rewrite hvec_lookup_fmap_equation_2 in stronger'.
        destruct piD, piSat. simpl in *. subst.
        assert (pred_stronger (pi_pred piaD) (pi_pred pi_at1)).
        { apply promise_stronger_pred_stronger.
          eapply (promises_is_valid_restricted_merge_stronger); done. }
        eapply pred_stronger_trans; first apply H3.
        simpl in *.
        (* specialize (wf 0%fin). *)
        (* destruct (wf 0%fin) as (bingo & bongo & bango). *)
        (* destruct (wfAt4 0%fin) as (bingo2 & bongo2 & bango2). *)
        clear -stronger'.
        apply stronger'. }
    (* end of assert *)
    simpl in res.
    destruct res as (prs3' & ? & sub2 & ? & ?).
    (* Check if the promise we want to insert is now in [prs3']. In reality
     * this will never happend as [prs3'] is only extended with the
     * dependencies of [pi], but it is easier just to consider the case that it
     * might than to carry through the fact that it is not. *)
    destruct (promises_lookup_at prs3' (id) γ) eqn:notIn2.
    { (* The promise is already in the list so inserting it is easy peasy -
       * even a naive solver could do it. *)
      naive_solver. }
    eexists (cons (MkPi id γ piaIns) prs3'), piaIns.
    split_and!.
    + apply promises_lookup_at_cons.
    + done.
    + intros ??. apply elem_of_list_further. apply sub2. done.
    + apply promise_list_valid_restricted_merge_cons; try done.
      intros pia2 look2. simpl in look2.
      apply (promise_lookup_lookup owf) in look; last done.
      simpl in look.
      simplify_eq.
      apply stronger.
  Qed.

  Lemma lookup_Some_length {A} (l : list A) i v :
    l !! i = Some v → ∃ j, i = length l - S j.
  Proof.
    intros le% lookup_lt_Some.
    apply Nat.le_exists_sub in le as (i' & ? & _).
    exists i'. lia.
  Qed.

  (* Grow [prsM] by inserting the promise id+γ and all of its dependencies from
   * [prsL] and [prsR]. *)
  Lemma merge_promises_insert_promise owf prsL prsR prsM id γ restrict :
    promises_is_valid_restricted_merge prsM prsL prsR restrict →
    promises_lookup_at prsM id γ = None →
    (is_Some (promises_lookup_at prsL id γ) ∨
      is_Some (promises_lookup_at prsR id γ)) →
    promises_overlap_pred prsL prsR →
    promises_wf owf prsL →
    promises_wf owf prsR →
    promises_wf owf prsM →
    ∃ prsM' pia3,
      promises_wf owf prsM' ∧
      promises_lookup_at prsM' id γ = Some pia3 ∧
      promises_is_valid_restricted_merge prsM' prsL prsR restrict.
  Proof.
    intros val _ [[? sm]|[? sm]] lap wf1 wf2 wfM.
    - apply promises_lookup_at_Some_lookup in sm as [i look].
      pose proof look as look2.
      apply lookup_Some_length in look2 as (i' & ->).
      edestruct merge_promises_insert_promise_idx as (prsM' & pia3 & ?); try done.
      exists prsM', pia3.
      naive_solver.
    - apply promises_lookup_at_Some_lookup in sm as [i look].
      apply promises_overlap_pred_sym in lap.
      apply promises_is_valid_restricted_merge_sym in val.
      pose proof look as look2.
      apply lookup_Some_length in look2 as (i' & ->).
      edestruct merge_promises_insert_promise_idx as (prsM' & pia3 & ?);
        try apply look; try done.
      exists prsM', pia3.
      rewrite promises_is_valid_restricted_merge_sym.
      naive_solver.
  Qed.

  Lemma merge_promises_restriced owf prsL prsR (restrict : list (ggid Ω * gname)) :
    promises_overlap_pred prsL prsR →
    promises_wf owf prsL →
    promises_wf owf prsR →
    ∃ prsM,
      promises_wf owf prsM ∧
      promises_is_valid_restricted_merge prsM prsL prsR restrict.
  Proof.
    rewrite /promises_is_valid_restricted_merge.
    intros lap wf1 wf2.
    induction restrict as [|[id γ] restrict' IH].
    { exists []. rewrite /promise_list_restrict_stronger.
      split_and!; try done; setoid_rewrite elem_of_nil; done. }
    destruct IH as (prsM & wf3 & from & lap1 & lap2 & stronger1 & stronger2).
    (* We're good if id+γ is already in [restrict']. *)
    destruct (decide ((id, γ) ∈ restrict')) as [elm|notElm].
    { exists prsM. rewrite /promise_list_restrict_stronger.
      setoid_rewrite (elem_of_elem_of_cons _ _ _ elm).
      done. }
    (* If the promise is already in [prsM] it should satisfy the conditions
     * already for the expanded [restrict]. *)
    destruct (promises_lookup_at prsM id γ) as [pia3|] eqn:look.
    { exists prsM. split_and!; try done.
      - eapply promise_list_restrict_stronger_cons; try done.
      - eapply promise_list_restrict_stronger_cons; done. }
    destruct (promises_lookup_at prsL id γ) as [pia1|] eqn:look1;
      destruct (promises_lookup_at prsR id γ) as [pia2|] eqn:look2.
    - edestruct (merge_promises_insert_promise) as (prs3' & temp);
        try done; first naive_solver.
      destruct temp as (pia3 & look3 & ? & ? & ? & ? & ? & ?).
      exists prs3'.
      split_and!; try done.
       * eapply promise_list_restrict_stronger_cons; done.
       * eapply promise_list_restrict_stronger_cons; done.
    - edestruct (merge_promises_insert_promise) as (prs3' & temp);
        try done; first naive_solver.
      destruct temp as (pia3 & look3 & ? & ? & ? & ? & ? & ?).
      exists prs3'.
      split_and!; try done.
       * eapply promise_list_restrict_stronger_cons; done.
       * eapply promise_list_restrict_stronger_cons; done.
    - edestruct (merge_promises_insert_promise) as (prs3' & temp);
        try done; first naive_solver.
      destruct temp as (pia3 & look3 & ? & ? & ? & ? & ? & ?).
      exists prs3'.
      split_and!; try done.
       * eapply promise_list_restrict_stronger_cons; done.
       * eapply promise_list_restrict_stronger_cons; done.
    - (* None of the promise lists have the promise in question. *)
      exists prsM.
      split_and!; try done.
      * intros ???. inversion 1; subst.
        + congruence.
        + apply stronger1. done.
      * intros ???. inversion 1; subst.
        + congruence.
        + apply stronger2. done.
  Qed.

  Definition promises_is_valid_merge prsM prsL prsR :=
    (∀ pi, pi ∈ prsM → pi ∈ prsL ∨ pi ∈ prsR) ∧
    promise_list_stronger prsM prsL ∧
    promise_list_stronger prsM prsR.

  Definition promise_get_path (pi : promise_info Ω) := (pi.(pi_id), pi.(pi_γ)).

  Definition restrict_merge prsL prsR :=
    (promise_get_path <$> prsL) ++ (promise_get_path <$> prsR).

  Lemma restrict_merge_lookup_Some prsL prsR id γ :
    is_Some (promises_lookup_at prsL id γ) →
    (id, γ) ∈ restrict_merge prsL prsR.
  Proof.
    intros (? & look%promises_lookup_at_Some).
    apply elem_of_app.
    left.
    apply elem_of_list_fmap.
    eexists _. split; last done. done.
  Qed.

  (* How to merge promises, intuitively?
   * 1. From the first list add the suffix of promises not in the other.
   * 2. From the second list add the suffix of promises not in the other.
   * 3. The last element in both lists is now also present in the other.
   *    - If they are for the same id+γ then add the strongest.
   *    - If one of them is stronger than the one in the other list then add that one.
   *    - If they are both weaker???
   *)
  Lemma merge_promises owf prsL prsR :
    promises_overlap_pred prsL prsR →
    promises_wf owf prsL →
    promises_wf owf prsR →
    ∃ prs3,
      promises_wf owf prs3 ∧ promises_is_valid_merge prs3 prsL prsR.
  Proof.
    intros lap wf1 wf2.
    destruct (merge_promises_restriced owf prsL prsR (restrict_merge prsL prsR) lap wf1 wf2)
      as (prs3 & ? & (? & ? & ? & str1 & str2)).
    exists prs3.
    split; first done.
    split_and!.
    - done.
    - intros ??? look. apply str1; last done.
      apply restrict_merge_lookup_Some.
      done.
    - intros ??? look. apply str2; last done.
      assert ((id, γ) ∈ restrict_merge prsR prsL) as elm.
      { apply restrict_merge_lookup_Some; try done. }
      move: elm.
      rewrite !elem_of_app.
      naive_solver.
  Qed.

End promise_info.

