(* This file defines the generational assertions that interact with the
 * [nextgen] modality and proves rules for these. *)

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
From self.nextgen Require Export types omega generational_cmra transmap
  promise nextgen_promises_model gen_ing.

Import EqNotations. (* Get the [rew] notation. *)
Import uPred.

(* Ownership over generational ghost state. *)

Section generational_resources.
  Context {n} {A} {DS : ivec n cmra} `{i : !genInG Σ Ω A DS}.
  Implicit Types (R : rel_over DS A) (P : (A → A) → Prop).

  Definition gen_pick_out γ r : iProp Σ :=
    own γ (gc_tup_pick_out DS r).

  (* The generational version of [own] that should be used instead of [own]. *)
  Definition gen_own (γ : gname) (a : A) : iProp Σ :=
    own γ (gc_tup_elem DS a).

  Definition know_deps γ (γs : ivec n gname) : iProp Σ :=
    own γ (gc_tup_deps A DS (vec_to_list γs)).

  Definition gen_promise_rel_pred_list γ rels preds :=
    own γ (gc_tup_rel_pred rels preds).

  Definition gen_token_used γ : iProp Σ :=
    gen_pick_out γ GTS_tok_perm.

  Definition gen_token γ : iProp Σ :=
    gen_pick_out γ (GTS_tok_both).

  Definition own_frozen_auth_promise_list γ rels preds : iProp Σ :=
    gen_promise_rel_pred_list γ
      (gN (●ML rels)) (gN (●ML preds)) ∗
    gen_promise_rel_pred_list γ
      (gC (●ML□ rels)) (gC (●ML□ preds)).

  Definition own_unit γ : iProp Σ :=
    own γ (ε : generational_cmraR A DS).

  Definition own_auth_promise_list γ rels preds : iProp Σ :=
    gen_promise_rel_pred_list γ (gNC (●ML rels)) (gNC (●ML preds)).

  Definition own_frag_promise_list γ rels preds : iProp Σ :=
    gen_promise_rel_pred_list γ (gNC (◯ML rels)) (gNC (◯ML preds)).

  Definition promise_info_for pia γs R P : Prop :=
    pia.(pi_deps_γs) = rew [λ n, ivec n _] genInG_gcd_n in γs ∧
    pia.(pi_pred) = rew genInG_gti_typ in P ∧
    pia.(pi_rel) = rew [id] rel_over_Oc_Ocs_genInG in R.

End generational_resources.

(* Store ε for every dependency in order to know that the γ is in fact
 * allocated. *)
Definition own_resource_for_deps {n : nat} {DS : ivec n cmra}
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    (γs : ivec n gname) : iProp Σ :=
  ∀ (i : fin n), own_unit (i := genInSelfG_gen (gs i)) (γs !!! i).

(** Resources shared between [token], [used_token], and [rely]. *)
Definition know_promise {n : nat} {DS : ivec n cmra} `{g : !genInG Σ Ω A DS}
  γ γs R P pia promises : iProp Σ :=
  "%pia_for" ∷ ⌜ promise_info_for pia γs R P ⌝ ∗
  (* "%pred_prefix" ∷ ⌜ pred_prefix_list_for' rels preds R P ⌝ ∗ *)
  "%pia_in" ∷ ⌜ promises_lookup_at promises _ γ = Some pia ⌝ ∗
  "%prs_wf" ∷ ⌜ promises_wf Ω.(gc_map_wf) promises ⌝ ∗
  "#prs" ∷ own_promises promises.

Section generational_resources.
  Context {n : nat} {DS : ivec n cmra} `{g : !genInG Σ Ω A DS}.

  Definition picked_out γ t : iProp Σ :=
    ∃ (picks : TransMap Ω),
      "%picksValid" ∷ ⌜ transmap_valid picks ⌝ ∗
      "#shotT" ∷ gen_pick_out γ (GTS_tok_gen_shot t) ∗
      "%picksLook" ∷
        ⌜ picks (genInG_id g) !! γ = Some (rew [cmra_to_trans] genInG_gti_typ in t) ⌝ ∗
      "picks" ∷ own_picks picks.

  Definition picked_in γ (t : A → A) : iProp Σ :=
    own γ (gc_tup_pick_in DS t).

End generational_resources.

Section generational_resources_with_deps.
  Context {n : nat} {DS : ivec n cmra}
    (* `{g : !genInG Σ Ω A DS}. *)
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    `{g : !genInDepsG Σ Ω A DS}.

  (** Ownership over the token and the promises for [γ]. *)
  Definition token (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (rels : list (rel_over DS A)) preds promises pia,
      "#tokenPromise" ∷ know_promise γ γs R P pia promises ∗
      "token" ∷ gen_pick_out γ GTS_tok_both ∗
      "%pred_prefix" ∷ ⌜ pred_prefix_list_for' rels preds R P ⌝ ∗
      "auth_preds" ∷ own_auth_promise_list γ rels preds ∗
      (* We could extract this resource from [know_promise], but keeping it
       * here might be easier *)
      "#ownDeps" ∷ own_resource_for_deps γs.

  Definition used_token (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (rels : list (rel_over DS A)) preds promises pia,
      "tokenPromise" ∷ know_promise γ γs R P pia promises ∗
      "%pred_prefix" ∷ ⌜ pred_prefix_list_for' rels preds R P ⌝ ∗
      "frocenAuthPreds" ∷ own_frozen_auth_promise_list γ rels preds ∗
      "usedToken" ∷ gen_pick_out γ GTS_tok_perm ∗
      "#ownDeps" ∷ own_resource_for_deps γs.

  (** Knowledge that γ is accociated with the predicates R and P. *)
  Definition rely (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ promises pia,
      "#relyPromise" ∷ know_promise γ γs R P pia promises ∗
      "#ownDeps" ∷ own_resource_for_deps γs.

End generational_resources_with_deps.

Definition rely_self `{g : !genInSelfG Σ Ω A} γ (P : pred_over A) : iProp Σ :=
  ∃ γs R promises pia,
    "#relyPromise" ∷ know_promise (g := genInSelfG_gen g) γ γs R P pia promises.

Equations True_preds_for {n} (ts : ivec n cmra) : preds_for n ts :=
| vnil => hnil;
| vcons t ts' => hcons True_pred (True_preds_for ts').

Lemma True_preds_for_lookup_fmap {n} (ts : ivec n cmra) i :
  hvec_lookup_fmap (True_preds_for ts) i = True_pred.
Proof.
  induction i as [|?? IH]; dependent elimination ts.
  - done.
  - apply IH.
Qed.

Lemma ivec_lookup_rew_rew {A : Set} {n m} (eq : n = m) l i :
  (rew [λ n : nat, ivec n A] eq in l !!! rew [fin] eq in i) = l !!! i.
Proof. destruct eq. done. Qed.

Lemma True_pred_rew_lookup_fmap_rew {n1 n2}
    (DS : ivec n1 cmra) (DS2 : ivec n2 cmra) i eq1 eq2 :
  hvec_lookup_fmap
    (rew [id] (hvec_fmap_eq eq1 DS DS2 eq2) in True_preds_for DS) i = True_pred.
Proof.
  destruct eq1. unfold eq_rect_r in eq2. simpl in *.
  destruct eq2. simpl.
  rewrite True_preds_for_lookup_fmap. done.
Qed.

Definition True_preds_for_id `{Ω : gGenCmras Σ}
    id : preds_for (On Ω id) (Ocs Ω id) :=
  True_preds_for (Ocs Ω id).

Lemma eq_inj {A} P (x y : A) (T1 : P x) T2 (eq : x = y) :
  rew [P] eq in T1 = rew [P] eq in T2 → T1 = T2.
Proof. destruct eq. done. Qed.

Lemma eq_rect_app_swap {A B} (f : B → Prop) (eq : B = A) (a : A) :
  (rew [λ a, a → Prop] eq in f) a ↔ f (rew <- [id] eq in a).
Proof. destruct eq. done. Qed.

Lemma rel_stronger_rew {n1 n2 A B} {DS1 : ivec n1 cmra} {DS2 : ivec n2 cmra}
    (eq1 : n1 = n2) (eq2 : A = B) eq3 (R1 R2 : rel_over DS1 A) :
  rel_stronger
    (rew [id] (rel_over_eq (DS2 := DS2) eq1 eq2 eq3) in R1)
    (rew [id] (rel_over_eq eq1 eq2 eq3)in R2) → rel_stronger R1 R2.
Proof.
  destruct eq1. destruct eq2.
  unfold eq_rect_r in eq3. simpl in eq3. destruct eq3. done.
Qed.

Lemma discrete_fun_singleton_included `{EqDecision A, finite.Finite A}
    {B : A → ucmra} {x : A} (a b : B x) :
  a ≼ b →
  (discrete_fun_singleton x a) ≼ discrete_fun_singleton x b.
Proof.
  intros incl.
  apply discrete_fun_included_spec => id.
  simpl.
  destruct (decide (id = x)) as [->|idNeq].
  2: { by rewrite !discrete_fun_lookup_singleton_ne. }
  rewrite !discrete_fun_lookup_singleton.
  done.
Qed.

Lemma discrete_fun_singleton_map_included {Σ} {i : gid Σ} {A : cmra} eq (γ : gname)
  (a b : A) :
  a ≼ b →
  ((discrete_fun_singleton i {[γ := map_unfold (cmra_transport eq a)]} : iResUR Σ)
    ≼ discrete_fun_singleton i {[γ := map_unfold (cmra_transport eq b)]}).
Proof.
  intros incl.
  apply discrete_fun_singleton_included.
  apply singleton_mono.
  apply: cmra_morphism_monotone.
  destruct eq.
  apply incl.
Qed.

Lemma iRes_singleton_included `{i : inG Σ A} (a b : A) γ :
  a ≼ b →
  (own.iRes_singleton γ a) ≼ (own.iRes_singleton γ b).
Proof. apply discrete_fun_singleton_map_included. Qed.

Lemma list_rely_self {n : nat} {DS : ivec n cmra}
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    (γs : ivec n gname) (deps_preds : preds_for n DS) :
  (∀ idx, rely_self (γs !!! idx) (hvec_lookup_fmap deps_preds idx)) -∗
  ∃ prs,
    (* a list of well formed promises *)
    ⌜ promises_wf Ω.(gc_map_wf) prs ⌝ ∗
    (* contains every promise in [γs] with the pred in [deps_preds] *)
    ⌜ promises_has_deps_raw
      (λ idx, genInG_id (@genInSelfG_gen _ _ _ (gs idx))) γs
      (λ idx, rew (genInG_gti_typ (genInG := genInSelfG_gen (gs idx)))
              in hvec_lookup_fmap deps_preds idx) prs ⌝ ∗
    own_promises prs.
Proof.
  induction n as [|n' IH].
  { iIntros "_". iExists [].
    rewrite -own_promises_empty.
    iPureIntro. split_and!; try done.
    intros i.
    inversion i. }
  iIntros "#relys".
  dependent elimination γs as [vcons γ0 γs'].
  dependent elimination DS.
  simpl in deps_preds.
  dependent elimination deps_preds as [hcons p0 preds'].
  iDestruct (IH _ (λ n, gs (FS n)) γs' preds' with "[]") as (prs wf2 prop) "OP".
  { iIntros (j).
    iSpecialize ("relys" $! (FS j)).
    iApply "relys". }
  iDestruct ("relys" $! 0%fin) as "HHH".
  rewrite hvec_lookup_fmap_equation_2.
  iDestruct "HHH" as (??) "H".
  iNamed "H". iNamed "relyPromise".
  iDestruct (own_promises_merge with "OP prs") as (prsM wfM val) "H";
    [done|done| ].
  iExists prsM.
  iFrame "H".
  iPureIntro.
  split; first done.
  intros n2.
  dependent elimination n2 as [0%fin | FS n3]; last first.
  { (* This one is from the IH *)
    destruct (prop n3) as (pia' & elm & sat).
    destruct val as (? & str & ?).
    apply (promises_elem_of _ _ _ wf2) in elm.
    destruct (str _ _ _ elm) as (pia2 & look2 & str2).
    eexists (MkPi _ _ pia2).
    split. { eapply promises_lookup_at_Some. done. }
    unfold promise_satisfy_dep_raw.
    destruct sat as (γEq & eq & predStr).
    split; first apply γEq.
    exists eq.
    etrans; last apply predStr.
    apply str2. }
  destruct val as (? & str & str2).
  destruct (str2 _ _ _ pia_in) as (pia2 & look2 & ?).
  eexists (MkPi _ _ pia2).
  split. { eapply promises_lookup_at_Some. done. }
  split; first done.
  exists eq_refl.
  etrans; first apply H0.
  destruct pia_for as (? & -> & ?).
  done.
Qed.

Lemma transmap_lookup_rew `{Ω : gGenCmras Σ} D (G : genInSelfG Σ Ω D)
  dId (γ : gname) x
  (idEq : genInG_id (genInSelfG_gen G) = dId)
  (cmraEq : Oc Ω dId = D)
  (trans : ∀ i : fin gc_len, gmap gname (Oc Ω i → Oc Ω i)) :
  trans (genInG_id (genInSelfG_gen G)) !! γ =
               Some (rew [cmra_to_trans] genInG_gti_typ in x) →
  trans dId !! γ = Some (rew [cmra_to_trans] eq_sym cmraEq in x).
Proof.
  intros ?.
  destruct idEq.
  rewrite H.
  destruct G. destruct genInSelfG_gen. simpl in *.
  destruct cmraEq.
  simpl.
  (* provable with UIP *)
Admitted.

Lemma list_picked_out {n : nat} {DS : ivec n cmra}
  `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    `{g : !genInDepsG Σ Ω A DS}
    (γs : ivec n gname) (ts : trans_for n DS) :
  (∀ idx, picked_out (g := genInSelfG_gen (gs idx))
            (γs !!! idx) (hvec_lookup_fmap ts idx)) -∗
  ∃ trans,
    ⌜ transmap_valid trans ⌝ ∗
    ⌜ trans_at_deps trans (genInDepsG_id g)
      (rew [λ n, ivec n _] genInG_gcd_n in γs)
      (rew [λ a, a] trans_for_genInG in ts) ⌝ ∗
    own_picks trans.
Proof.
  destruct g. destruct genInDepsG_gen. simpl in *.
  unfold genInDepsG_id in *.
  unfold genInG_inG in *.
  (* Set Printing All. *)
  unfold Oids in *. unfold Oeq in *. unfold Ogid in *. simpl. unfold Ocs in *.
  unfold trans_for_genInG in *. simpl in *.
  unfold Ocs in *.
  unfold trans_at_deps.
  unfold Oids in *.
  unfold lookup_fmap_Ocs.
  unfold Ocs_Oids_distr.
  unfold Ocs in *.
  unfold Oids in *.
  generalize dependent (gc_map_wf genInG_id). intros ?.
  unfold omega_wf_at in *.
  destruct (gc_map Ω genInG_id). simpl in *.
  destruct genInG_gcd_n.
  destruct genInG_gti_typ.
  unfold eq_rect_r in *. simpl in *.
  destruct genInG_gcd_deps.
  clear gcd_cmra_eq.
  induction n as [|n' IH].
  { iIntros "_". iExists (λ _, ∅).
    rewrite -own_picks_empty.
    iPureIntro. split_and!; try done.
    intros i.
    simpl in i.
    exfalso.
    inversion i. }
  iIntros "#outs".
  dependent elimination γs as [vcons γ0 γs']. simpl in *.
  dependent elimination DS as [vcons D DS'].
  dependent elimination gcd_deps_ids as [vcons dId deps_ids'].
  unfold trans_for in ts.
  dependent elimination ts. (* as [vcons t ts']. *)
  specialize (IH DS' (λ n, gs (FS n)) deps_ids' (λ n, genInDepsG_eqs (FS n))).
  specialize (IH γs' h (λ n, o (FS n))).
  iAssert (
    (∀ idx : fin n0, picked_out (γs' !!! idx) (hvec_lookup_fmap h idx))%I
  ) as "outs'".
  { iIntros (i). iSpecialize ("outs" $! (FS i)). iApply "outs". }
  iPoseProof (IH with "outs'") as (trans val transLook) "OP".
  iSpecialize ("outs" $! 0%fin).
  rewrite hvec_lookup_fmap_equation_2.
  iDestruct ("outs") as (trans2 val2) "(? & %transLook2 & OP2)".
  iDestruct (tokens_for_picks_agree_overlap with "OP OP2") as "%lap".
  iExists (trans2 ∪ trans).
  iSplit. { iPureIntro. apply transmap_valid_union; done. }
  iSplit.
  { iPureIntro.
    intros idx.
    dependent elimination idx.
    - specialize (genInDepsG_eqs 0%fin).
      apply transmap_lookup_union_Some_l.
      rewrite hvec_lookup_fmap_equation_2.
      eapply transmap_lookup_rew; done.
    - specialize (transLook t).
      apply lookup_union_r_overlap.
      { symmetry. apply (lap (deps_ids' !!! t)). }
      apply transLook. }
  iApply own_picks_sep. iFrame "OP2 OP".
Qed.

Lemma rew_lookup_total {A : Set} n m (γs : ivec n A) i (eq : m = n) :
  rew <- [λ n1 : nat, ivec n1 A] eq in γs !!! i =
  γs !!! rew [fin] eq in i.
Proof. destruct eq. done. Qed.

Lemma pred_over_rew_id_cmra {Σ} {Ω : gGenCmras Σ} (id2 : fin gc_len) id1
  (eq1 : Oc Ω id2 = Oc Ω id1)
  (t : Oc Ω id1 → Oc Ω id1)
  (eq2 : id2 = id1)
  (p : pred_over (Oc Ω id2)) :
  (rew [pred_over] eq1 in p) t →
  (rew [λ id : fin gc_len, pred_over (Oc Ω id)] eq2 in p) t.
Proof.
  destruct eq2. simpl.
  (* This holds with UIP. *)
Admitted.

Lemma promises_has_deps_rew {n : nat} {DS : ivec n cmra}
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    `{g : !genInDepsG Σ Ω A DS}
    (γs : ivec n gname) (deps_preds : preds_for n DS) prs :
  promises_has_deps_raw
    (λ idx : fin n, genInG_id (genInSelfG_gen (gs idx)))
    γs
    (λ idx : fin n,
      rew [pred_over] genInG_gti_typ in hvec_lookup_fmap deps_preds idx)
    prs →
  promises_has_deps_raw
    (λ idx : fin (On Ω (genInDepsG_id g)),
       Oids Ω (genInDepsG_id g) !!! idx)
    (rew [λ n0 : nat, ivec n0 gname] genInG_gcd_n in γs)
    (λ idx : fin (On Ω (genInDepsG_id g)),
       lookup_fmap_Ocs (rew [id] preds_for_genInG in deps_preds) idx
         (gc_map_wf (genInDepsG_id g)))
    prs.
Proof.
  intros hasDeps i.
  destruct (hasDeps (rew <- genInG_gcd_n in i)) as (pi & elm & γEq & eq' & str).
  exists pi.
  split; first done.
  specialize (genInDepsG_eqs (rew <- genInG_gcd_n in i)) as idEqs.
  rewrite rew_opp_r in idEqs.
  split.
  { rewrite -γEq -rew_lookup_total /eq_rect_r eq_sym_involutive //. }
  exists (eq_trans (eq_sym idEqs) eq').
  intros t holds.
  specialize (str t holds).
  rewrite -rew_compose.
  clear -str.
  unfold lookup_fmap_Ocs.
  unfold Ocs_Oids_distr.
  unfold preds_for_genInG.
  destruct eq'. simpl in *.
  destruct g.
  destruct genInDepsG_gen. simpl in *.
  unfold Oids in *.
  unfold Ocs in *.
  unfold preds_for_genInG. simpl.
  unfold Ocs in *.
  unfold Ocs_Oids_distr.
  unfold Oids in *.
  unfold Ocs in *.
  unfold genInDepsG_id in *.
  simpl in *.
  generalize (gc_map_wf genInG_id i).
  clear -str.
  destruct (gc_map Ω genInG_id). simpl in *.
  destruct genInG_gcd_n.
  unfold eq_rect_r in *. simpl in *.
  destruct genInG_gcd_deps. simpl.
  unfold genInSelfG_id in *.
  generalize dependent (genInSelfG_gen (gs i)).
  intros g. destruct g. simpl.
  intros t str eq2 eq3.
  revert str.
  set (p := @hvec_lookup_fmap n cmra pred_over DS deps_preds i).
  generalize p.
  clear p.
  intros p.
  destruct eq3. simpl.
  apply pred_over_rew_id_cmra.
Qed.

Lemma list_rely_self' {n : nat} {DS : ivec n cmra}
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    `{g : !genInDepsG Σ Ω A DS}
    (γs : ivec n gname) (deps_preds : preds_for n DS) :
  (∀ idx, rely_self (γs !!! idx) (hvec_lookup_fmap deps_preds idx)) -∗
  ∃ prs,
    (* a list of well formed promises *)
    ⌜ promises_wf Ω.(gc_map_wf) prs ⌝ ∗
    (* contains every promise in [γs] with the pred in [deps_preds] *)
    ⌜ promises_has_deps_raw
        (λ idx : fin (On Ω (genInDepsG_id g)),
          Oids Ω (genInDepsG_id g) !!! idx)
        (rew [λ n, ivec n gname] genInG_gcd_n in γs)
        (λ idx : fin (On Ω (genInDepsG_id g)),
          lookup_fmap_Ocs (rew [id] preds_for_genInG in deps_preds) idx
            (gc_map_wf (genInDepsG_id g)))
        prs ⌝ ∗
    own_promises prs.
Proof.
  iIntros "O".
  iDestruct (list_rely_self with "O") as (prs wf hasDeps) "OP".
  iExists (prs).
  iFrame (wf) "OP".
  iPureIntro.
  apply promises_has_deps_rew. done.
Qed.

Lemma rew_rel_over_True {n1 n2 A B} {DS1 : ivec n1 cmra} {DS2 : ivec n2 cmra}
    (eq1 : n1 = n2) (eq2 : A = B) eq3 (ts : trans_for n2 DS2) :
  (rew [id] (rel_over_eq eq1 eq2 eq3) in (True_rel (DS := DS1))) ts (λ a, a).
Proof.
  destruct eq1. destruct eq2.
  unfold eq_rect_r in eq3. simpl in eq3. destruct eq3.
  simpl. rewrite huncurry_curry. done.
Qed.

Lemma rew_True_pred {A B : cmra} (t : cmra_to_trans A) (eq : B = A) :
  (rew [pred_over] eq in True_pred) t.
Proof. destruct eq. done. Qed.

Lemma pred_prefix_list_for'_True_rew {n} {A B : cmra} {DS : ivec n cmra} {DS2 : ivec n cmra} (eq : A = B) eq2 :
  pred_prefix_list_for' (@True_rel _ DS2 _ :: nil) (True_pred :: nil)
    (rew [id] rel_over_eq eq_refl eq eq2 in (@True_rel _ DS _))
    (rew [id]
         rew [λ c : cmra, pred_over A = pred_over c] eq in eq_refl in
     (λ _ : A → A, True)).
Proof.
  destruct eq. unfold eq_rect_r in eq2. simpl in eq2. destruct eq2. simpl.
  apply pred_prefix_list_for'_True.
Qed.

(* NOTE: this lemm could be generalized. *)
Lemma pred_stronger_eq `{Ω : gGenCmras Σ} n1 n2 (eq : n1 = n2) P1 P2 :
  (pred_stronger P1 P2) →
  pred_stronger
    (rew [λ id : fin gc_len, pred_over (Oc Ω id)] eq in P1)
    (rew [λ id : fin gc_len, pred_over (Oc Ω id)] eq in P2).
Proof. destruct eq. done. Qed.

Lemma pred_stronger_rew_sym `{Ω : gGenCmras Σ} {A B} (eq : A = B) P1 P2 :
  pred_stronger (rew [λ c, pred_over c] eq in P1) P2 ↔
  pred_stronger P1 (rew <- [λ c, pred_over c] eq in P2).
Proof. destruct eq. done. Qed.

Lemma promise_has_deps_mono `{Ω : gGenCmras Σ} {n} (ids : fin n → ggid Ω) deps_γs
    (preds1 : ∀ idx, pred_over (Oc Ω (ids idx))) preds2 promises :
  (∀ i, pred_stronger (preds1 i) (preds2 i)) →
  promises_has_deps_raw ids deps_γs preds1 promises →
  promises_has_deps_raw ids deps_γs preds2 promises.
Proof.
  intros I deps idx.
  destruct (deps idx) as (piSat & ? & ? & eq & ?).
  exists piSat.
  unfold promise_satisfy_dep_raw.
  split_and!; try done.
  eexists eq.
  etrans; first done.
  apply pred_stronger_eq.
  apply I.
Qed.

Lemma promises_has_deps_raw_stronger `{Ω : gGenCmras Σ} {n} owf prs1 prs2 γs
    (ids : fin n → ggid Ω) (preds : ∀ idx, pred_over (Oc Ω (ids idx))) :
  promises_wf owf prs2 →
  promise_list_stronger prs1 prs2 →
  promises_has_deps_raw ids γs preds prs2 →
  promises_has_deps_raw ids γs preds prs1.
Proof.
  intros wf str deps.
  intros idx.
  specialize (deps idx) as (piSat2 & elm & sat).
  edestruct (str) as (piaSat1 & ? & ?).
  { eapply promises_elem_of; done. }
  eexists (MkPi _ _ piaSat1).
  split. { apply promises_lookup_at_Some. done. }
  destruct sat as (? & ? & ?).
  split; first done.
  simpl.
  exists x.
  etrans; first apply H0. done.
Qed.

Section nextgen_assertion_rules.
  (* Rules about the nextgen modality. *)
  Context {n : nat} {DS : ivec n cmra} `{g : !genInG Σ Ω A DS}.

  Lemma build_trans_singleton
        (γ : gname) picks a pps (V : transmap_valid picks) :
    picks (genInG_id g) = pps →
    build_trans picks (own.iRes_singleton γ (a : generational_cmraR A DS)) ≡
      own.iRes_singleton γ (
        gen_cmra_trans (cmra_map_transport (eq_sym genInG_gti_typ) (default (λ a, a) (pps !! γ))) a
      ).
  Proof.
    (* rewrite /build_trans. simpl. *)
    intros picksLook j2.
    (* rewrite /own.iRes_singleton. *)

    (* NOTE: It would be nice to prove this lemma using
     * [build_trans_singleton_alt] *)
    (* rewrite /own.inG_unfold. *)
    (* fold (@map_unfold Σ (inG_id genInG_inG)). *)
    (* rewrite (build_trans_singleton_alt picks). *)

    rewrite /build_trans. simpl.
    rewrite /own.iRes_singleton.
    destruct (decide (Ogid Ω (genInG_id g) = j2)) as [eq|neq].
    - intros γ2.
      rewrite (Omega_lookup_inverse_eq _ _ eq).
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
      (* rewrite -eqLook. *)
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
      rewrite /own.inG_unfold.
      rewrite cmra_map_transport_cmra_transport.
      destruct g. simpl in *. clear -disj.
      unfold genInG_inG. unfold Oeq. unfold Ogid. simpl. unfold Ocs in *.
      unfold omega_genInG_cmra_eq. simpl.
      destruct (gc_map Ω genInG_id). simpl in *.
      destruct genInG_gcd_n. simpl.
      destruct genInG_gti_typ. unfold eq_rect_r in *. simpl in *.
      destruct genInG_gcd_deps.
      rewrite generational_cmraR_transp_refl.
      rewrite eq_trans_refl_l.
      destruct disj as [-> | (t & -> & GT)].
      + simpl. rewrite map_fold_unfold.
        rewrite cmra_map_transport_cmra_transport.
        done.
      + simpl. rewrite map_fold_unfold.
        rewrite cmra_map_transport_cmra_transport.
        done.
    - simpl.
      rewrite discrete_fun_lookup_singleton_ne; last done.
      rewrite discrete_fun_lookup_singleton_ne; last done.
      destruct (Omega_lookup_inverse j2) as [[? eq]|]; last done.
      destruct eq. simpl.
      apply build_trans_at_singleton_neq.
      done.
  Qed.

  Lemma own_build_trans_next_gen γ (m : generational_cmraR A DS) picks
      `{!CmraMorphism (build_trans picks)} :
    transmap_valid picks →
    own γ m ⊢ ⚡={build_trans picks}=> own γ (
      gen_cmra_trans (
        rew <- [cmra_to_trans] genInG_gti_typ in (default (λ a, a) (picks _ !! γ))
      ) m).
  Proof.
    iIntros (?) "H".
    iEval (rewrite own.own_eq) in "H".
    rewrite /own.own_def.
    iModIntro.
    iEval (rewrite own.own_eq).
    rewrite /own.own_def.
    simpl.
    rewrite build_trans_singleton; [ |done|done].
    simpl.
    rewrite /gen_cmra_trans. simpl.
    done.
  Qed.

  Lemma own_next_gen γ (m : generational_cmraR A DS) :
    own γ m ⊢ ⚡==> ∃ t, own γ (gen_cmra_trans t m).
  Proof.
    iIntros "O".
    iApply nextgen_empty.
    iIntros (full_picks ?).
    iDestruct (own_build_trans_next_gen with "O") as "O"; first done.
    iModIntro. iExists _. iApply "O".
  Qed.

  Lemma Oown_build_trans_next_gen i γ (m : generational_cmraR _ _) picks
      `{!CmraMorphism (build_trans picks)} :
    transmap_valid picks →
    Oown i γ m ⊢ ⚡={build_trans picks}=> Oown i γ (
      gen_cmra_trans (
        (default (λ a, a) (picks _ !! γ))
      ) m).
  Proof.
    iIntros (?) "H".
    unfold Oown.
    iEval (rewrite own.own_eq) in "H".
    rewrite /own.own_def.
    iModIntro.
    iEval (rewrite own.own_eq).
    rewrite /own.own_def.
    simpl.
    rewrite build_trans_singleton_alt; try done.
  Qed.

  Lemma own_promise_info_nextgen picks pi `{!CmraMorphism (build_trans picks)} :
    transmap_valid picks →
    own_promise_info pi ⊢ ⚡={build_trans picks}=> own_promise_info pi.
  Proof.
    iIntros (val). iDestruct 1 as (???) "O".
    iDestruct (Oown_build_trans_next_gen with "O") as "O"; first done.
    iModIntro.
    iExists _, _. iSplit; first done.
    rewrite gen_cmra_trans_apply. simpl.
    iStopProof.
    unfold own_promise_info_resource.
    unfold Oown.
    f_equiv. simpl.
    simpl.
    apply gen_cmra_incl_mono; split_and!; try done; apply ucmra_unit_least.
  Qed.

  (* NOTE: This doesn't really work as an instance since TC search can't find
   * the [val] we need. This could prop. be fixed by keeping this fact in a TC. *)
  Global Instance into_bnextgen_own_promise_info picks
      `{!CmraMorphism (build_trans picks)} (val : transmap_valid picks) :
    ∀ pi, IntoBnextgen (build_trans picks) (own_promise_info pi) (own_promise_info pi).
  Proof.
    intros pi.
    rewrite /IntoBnextgen.
    iApply (own_promise_info_nextgen).
    done.
  Qed.

  Lemma own_promises_nextgen picks ps `{!CmraMorphism (build_trans picks)} :
    transmap_valid picks →
    own_promises ps ⊢ ⚡={build_trans picks}=> own_promises ps.
  Proof.
    iIntros (val) "#prs".
    rewrite /own_promises.
    rewrite big_sepL_forall_elem_of.
    specialize (into_bnextgen_own_promise_info _ val) as H.
    iModIntro.
    done.
  Qed.

  Lemma own_build_trans_next_gen_picked_in γ (m : generational_cmraR A DS) picks
      `{!CmraMorphism (build_trans picks)} :
    transmap_valid picks →
    own γ m ⊢ ⚡={build_trans picks}=>
      picked_in γ (rew <- [cmra_to_trans] genInG_gti_typ in (default (λ a, a) (picks _ !! γ)))
    .
  Proof.
    iIntros (?) "R".
    iDestruct (own_build_trans_next_gen with "R") as "R"; first done.
    iModIntro.
    iDestruct (own_gen_cmra_split with "R") as "($ & _)".
  Qed.

  Lemma know_deps_nextgen γ γs :
    know_deps γ γs ⊢ ⚡==> know_deps γ γs.
  Proof.
    rewrite /know_deps.
    iIntros "H".
    iDestruct (own_next_gen with "H") as "H".
    iModIntro.
    iDestruct "H" as (t) "H".
    rewrite gen_cmra_trans_apply. simpl.
    iDestruct (own_gen_cmra_split_alt with "H") as "(_ & _ & _ & $ & _)".
  Qed.

  Lemma nextgen_plain_soundness P `{!Plain P} :
    (⊢ ⚡==> P) → ⊢ P.
  Proof.
    rewrite nextgen_unseal /nextgen_def.
    intros HP.
    iDestruct HP as (picks prs) "H".
    iNamed "H". clear HP.
    iDestruct (own_picks_promises_satisfy with "ownPicks ownPrs") as %resp.
    destruct (transmap_and_promises_to_full_map picks prs)
      as (full_picks & val & resp' & sub); try done.
    iSpecialize ("contP" $! full_picks val resp' sub).
    set (T := build_trans_generation full_picks val).
    rewrite -{2}(bnextgen_plain (build_trans full_picks) P).
    done.
  Qed.

  Lemma know_promise_extract_frag γ γs R P pia promises :
    know_promise γ γs R P pia promises ⊢
    ∃ rels' (preds' : list (pred_over A)),
      ⌜ pred_prefix_list_for' rels' preds' R P ⌝ ∗
      know_deps γ γs ∗
      gen_promise_rel_pred_list γ (gNC (◯ML rels')) (gNC (◯ML preds')).
  Proof.
    iNamed 1.
    unfold own_promises.
    apply promises_lookup_at_Some in pia_in as elem.
    rewrite big_sepL_forall_elem_of.
    iSpecialize ("prs" $! _ elem).
    iDestruct "prs" as (???) "-#prs". simpl in *.
    (* rewrite /gen_promise_rel_pred_list own.own_eq /own.own_def. *)
    (* rewrite /own.iRes_singleton. simpl. *)
    iExists (rew <- rel_over_Oc_Ocs_genInG in Rs).
    iExists (rew <- pred_over_Oc_genInG in Ps).
    unfold gen_promise_rel_pred_list.
    unfold own_promise_info_resource.
    simpl.
    unfold know_deps.
    rewrite -own_op.
    rewrite 1!own_gen_cmra_data_to_inG.
    unfold omega_genInG_cmra_eq.
    unfold rel_over_Oc_Ocs_genInG.
    unfold gc_tup_rel_pred.
    unfold Oown.
    destruct pia_for as (-> & predEq & relEq).
    unfold rel_over_Oc_Ocs_genInG in *.
    unfold pred_over_Oc_genInG.
    destruct pia.
    destruct g.
    unfold promise_info_for in *.
    simpl in *.
    clear -H predEq relEq.
    unfold Ocs in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps.
    rewrite generational_cmraR_transp_refl.
    simpl.
    simpl in relEq.
    rewrite -predEq -relEq.
    iSplit; done.
  Qed.

End nextgen_assertion_rules.

Section rules_with_deps.
  Context {n : nat} {DS : ivec n cmra}
    `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
    `{g : !genInDepsG Σ Ω A DS}.

  Program Definition make_pia (γs : ivec n gname) deps_preds
      (R_2 : rel_over DS A) (P_2 : pred_over A)
      (R_to_P : ∀ ts t, huncurry R_2 ts t → P_2 t)
      (witness : ∀ (ts : trans_for n DS),
        preds_hold deps_preds ts →
        ∃ (e : A → A), CmraMorphism e ∧ huncurry R_2 ts e)
      : promise_info_at Ω _ := {|
    pi_deps_γs := (rew [λ n, ivec n _] genInG_gcd_n in γs);
    pi_deps_preds := rew [id] preds_for_genInG in deps_preds;
    pi_rel := rew [id] rel_over_Oc_Ocs_genInG in R_2;
    pi_pred := rew genInG_gti_typ in P_2;
  |}.
  Next Obligation.
    rewrite /rel_over_Oc_Ocs_genInG.
    intros ??????? holds.
    rewrite /pred_over_Oc_genInG.
    destruct genInDepsG_gen; simpl in *.
    unfold Ocs in *.
    destruct (Ω.(gc_map) genInG_id). simpl in *.
    destruct (genInG_gcd_n).
    destruct (genInG_gti_typ).
    unfold eq_rect_r in *. simpl in *.
    destruct (genInG_gcd_deps).
    simpl in *.
    eapply R_to_P.
  Qed.
  Next Obligation.
    rewrite /rel_over_Oc_Ocs_genInG.
    intros ???????.
    destruct genInDepsG_gen. simpl in *.
    unfold preds_for_genInG in *. simpl in *.
    unfold Ocs in *.
    destruct (Ω.(gc_map) genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps.
    simpl in *.
    apply witness.
  Qed.

  Program Definition make_true_pia (γs : ivec n gname) : promise_info_at Ω _ :=
    make_pia γs (True_preds_for DS) True_rel True_pred _ _.
  Next Obligation. intros. done. Qed.
  Next Obligation.
    intros. exists (λ a, a). rewrite huncurry_curry. split; first apply _. done.
  Qed.

  Lemma auth_promise_list_frag γ rs ps :
    own_auth_promise_list γ rs ps
    ⊢ own_auth_promise_list γ rs ps ∗ own_frag_promise_list γ rs ps.
  Proof.
    rewrite -own_op.
    unfold own_auth_promise_list.
    unfold own_frag_promise_list.
    unfold gNC.
    unfold mk_gen_nc.
    unfold gen_promise_rel_pred_list.
    unfold gc_tup_rel_pred.
    rewrite {1 2}(mono_list_auth_lb_op _ rs).
    rewrite {1 2}(mono_list_auth_lb_op _ ps).
    done.
  Qed.

  Lemma auth_promise_list_snoc γ rs ps r p :
    own_auth_promise_list γ rs ps
    ⊢ |==> own_auth_promise_list γ (rs ++ (cons r nil)) (ps ++ (cons p nil)).
  Proof.
    rewrite /own_auth_promise_list.
    rewrite /gen_promise_rel_pred_list.
    apply own_update.
    apply gen_cmra_update; try reflexivity.
    - apply gen_nc_update.
      apply mono_list_update.
      apply prefix_app_r.
      done.
    - apply gen_nc_update.
      apply mono_list_update.
      apply prefix_app_r.
      done.
  Qed.

  Lemma Oids_genInG {n2 : nat} {A2 : cmra} {DS2 : ivec n2 cmra}
      id (g2 : genInG Σ Ω A2 DS2) i (wf : omega_wf_at Ω.(gc_map) id) :
    Oids Ω id !!! i = genInG_id g2.
  Proof.
    rewrite /omega_wf_at in wf.
    rewrite /Oids.
    destruct (gc_map Ω id) eqn:eq.
    - specialize (wf i). simpl in *.
  Abort.

  Definition promises_different_gname (prs : list (promise_info Ω)) :=
    λ γ, ∀ pi, pi ∈ prs → pi.(pi_γ) ≠ γ.

  Lemma promises_different_gname_infinite prs :
    pred_infinite (promises_different_gname prs).
  Proof.
    intros γs.
    specialize (infinite_is_fresh ((pi_γ <$> prs) ++ γs)) as [no1 no2]%not_elem_of_app .
    eexists _.
    split; last done.
    intros pi elm eq.
    apply (elem_of_list_fmap_1 pi_γ) in elm.
    simplify_eq. congruence.
  Qed.

  (* Translates between the omega based resource in [own_promise_info] and
   * [genInG] based ones. *)
  Lemma own_promise_info_own' γ pia :
    own_promise_info (MkPi (genInDepsG_id g) γ pia) ⊣⊢
    (∃ Rs Ps,
      ⌜ pred_prefix_list_for' Rs Ps
          (rew <- [id] rel_over_Oc_Ocs_genInG in pia.(pi_rel))
          (rew <- genInG_gti_typ in pia.(pi_pred)) ⌝ ∗
      know_deps γ (rew <- [λ n, ivec n _] genInG_gcd_n in pia.(pi_deps_γs)) ∗
      own_frag_promise_list γ Rs Ps).
  Proof.
    destruct pia. simpl in *.
    unfold own_frag_promise_list.
    unfold own_promise_info.
    unfold own_promise_info_resource.
    unfold know_deps.
    unfold gen_promise_rel_pred_list.
    unfold genInDepsG_id in *.
    simpl in *.
    destruct genInDepsG_gen. simpl in *.
    unfold rel_over_Oc_Ocs_genInG in *.
    unfold pred_over_Oc_genInG in *.
    unfold gen_promise_rel_pred_list.
    setoid_rewrite own_gen_cmra_data_to_inG.
    unfold genInG_inG.
    simpl.
    unfold omega_genInG_cmra_eq.
    unfold generational_cmraR_transp.
    unfold Ocs in *.
    unfold Oeq.
    unfold Ogid.
    simpl in *.
    unfold Oown.
    setoid_rewrite <- own_op.
    simpl in *.
    destruct (Ω.(gc_map) genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_ind_r in *.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps. simpl.
    repeat f_equiv; done.
  Qed.

  (* Translates between the omega based resource in [own_promise_info] and
   * [genInG] based ones. *)
  Lemma own_promise_info_own γ γs R P pia :
    promise_info_for pia γs R P →
    own_promise_info (MkPi (genInDepsG_id g) γ pia) ⊣⊢
    (∃ Rs Ps,
      ⌜ pred_prefix_list_for' Rs Ps R P ⌝ ∗
      know_deps γ γs ∗
      own_frag_promise_list γ Rs Ps).
  Proof.
    unfold genInDepsG_id in *. simpl.
    rewrite own_promise_info_own'.
    intros (eq1 & eq2 & eq3).
    rewrite eq1 eq2 eq3.
    rewrite 3!rew_opp_l.
    done.
  Qed.

  Lemma promise_info_for_pi_rel pia γs P R ts t :
    promise_info_for pia γs R P →
    pi_rel pia ts t →
    R (rew <- [id] trans_for_genInG in ts)
      (rew <- [cmra_to_trans] genInG_gti_typ in t)
    ∧ P (rew <- [cmra_to_trans] genInG_gti_typ in t).
  Proof.
    intros (? & pred_eq & rel_eq) relHolds.
    pose proof (pi_rel_to_pred pia _ _ relHolds) as predHolds.
    rewrite rel_eq in relHolds.
    rewrite pred_eq in predHolds.
    rewrite /rel_over_Oc_Ocs_genInG in relHolds.
    rewrite /trans_for_genInG.
    destruct g as [genInG idsEq]. destruct genInG.
    simpl in *.
    clear -relHolds predHolds.
    unfold Ocs in *. simpl in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n. simpl in *.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps. simpl in *.
    split.
    + apply relHolds.
    + apply predHolds.
  Qed.

  (* Lemma rely_self_resource_for_deps γs deps_preds : *)
  (*   (∀ i, rely_self (γs !!! i) (hvec_lookup_fmap deps_preds i)) -∗ *)
  (*   own_resource_for_deps γs. *)
  (* Proof. *)
  (*   iIntros "O" (i). *)
  (*   iSpecialize ("O" $! i). *)
  (*   iNamed "O". *)
  (*   iStopProof. *)
  (*   f_equiv. *)
  (* Qed. *)

  Global Instance gen_own_proper γ : Proper ((≡) ==> (≡)) (gen_own γ).
  Proof. unfold gen_own, gc_tup_elem. solve_proper. Qed.

  Lemma gen_own_op γ a1 a2 : gen_own γ (a1 ⋅ a2) ⊣⊢ gen_own γ a1 ∗ gen_own γ a2.
  Proof. unfold gen_own, gc_tup_elem. rewrite -own_op. done. Qed.

  Lemma gen_own_mono γ a1 a2 : a2 ≼ a1 → gen_own γ a1 ⊢ gen_own γ a2.
  Proof. move=> [c ->]. rewrite gen_own_op sep_elim_l. done. Qed.

  Lemma rely_to_rely_self γ γs R P :
    rely γ γs R P ⊢ rely_self γ P.
  Proof. iNamed 1. iExists _, _, _, _. iFrame "relyPromise". Qed.

  Lemma own_gen_alloc (a : A) γs (deps_preds : preds_for n DS) :
    ✓ a →
    (* For every dependency we own a [rely_self]. *)
    (∀ i, rely_self (γs !!! i) (hvec_lookup_fmap deps_preds i)) -∗
    |==> ∃ γ, gen_own γ a ∗ token γ γs True_rel (λ _, True%type).
  Proof.
    iIntros (Hv) "#relys".
    rewrite /gen_own /token.
    iDestruct (list_rely_self' with "relys") as (prs wf allDeps) "ownPrs".
    (* We need to know that the new ghost name makes the new promise different
     * from all existing promises. We "overapproximate" this by requiring the
     * new gname to be different from the gname for any existing promise. *)
    iMod (own_alloc_strong
      (gc_tup_deps A DS (vec_to_list γs) ⋅
       gc_tup_elem DS a ⋅
       gc_tup_pick_out DS GTS_tok_both ⋅
       gc_tup_rel_pred
         (gNC (●ML (True_rel :: [])))
         (gNC (●ML (True_pred :: []))) ⋅
       gc_tup_rel_pred
         (gNC (◯ML (True_rel :: []))) (gNC (◯ML (True_pred :: [])))
       ) (promises_different_gname prs)) as (γ pHolds) "[[[[OD OA] A'] B1] B2]".
    { apply promises_different_gname_infinite. }
    { split_and!; simpl; try done.
      - rewrite ucmra_unit_left_id.
        rewrite gen_nc_op.
        apply gen_nc_valid.
        apply mono_list_both_valid.
        exists []. done.
      - rewrite ucmra_unit_left_id.
        rewrite gen_nc_op.
        apply gen_nc_valid.
        apply mono_list_both_valid.
        exists []. done. }
    iExists γ.
    iModIntro. iFrame "OA".
    set (pia := make_true_pia γs).
    iExists ((_) :: nil), ((_) :: nil), ((MkPi _ γ pia) :: prs), pia.
    iFrame "B1".
    iFrame "A'".
    rewrite /know_promise.
    iSplit. 2: {
      iSplit.
      - iPureIntro. apply pred_prefix_list_for'_True.
      - unfold own_resource_for_deps.
        iIntros (idx).
        iDestruct ("relys" $! idx) as (γs2 ???) "D".
        iDestruct (know_promise_extract_frag with "D") as (???) "(-#DD & _)".
        unfold own_unit. unfold know_deps.
        iClear "relys ownPrs D OD B2".
        iStopProof.
        f_equiv. simpl.
        exists (gc_tup_deps (DS !!! idx) genInSelfG_DS (vec_to_list γs2)).
        done. }
    iSplit; first done.
    iSplit. { iPureIntro. apply promises_lookup_at_cons. }
    iSplit.
    { (* Show that the promises are well-formed. *)
      iPureIntro. split; last done.
      simpl.
      split.
      - simpl.
        apply promises_lookup_at_None.
        intros pi2 elem.
        right. simpl. apply PositiveOrder.neq_sym.
        apply pHolds. done.
      - unfold promises_has_deps. simpl.
        eapply promise_has_deps_mono; last apply allDeps.
        unfold lookup_fmap_Ocs.
        intros ???.
        rewrite True_pred_rew_lookup_fmap_rew.
        apply rew_True_pred. }
    unfold own_promises.
    rewrite big_sepL_cons.
    iFrame "ownPrs".
    iApply own_promise_info_own; first done.
    iExists (True_rel :: nil).
    iExists (True_pred :: nil).
    iFrame.
    iPureIntro. apply pred_prefix_list_for'_True.
  Qed.

  Lemma gen_token_split γ :
    gen_pick_out γ GTS_tok_both ⊣⊢
      gen_pick_out γ GTS_tok_perm ∗
      gen_pick_out γ GTS_tok_gen.
  Proof. rewrite -own_op. done. Qed.

  Lemma gen_picked_in_agree γ (f f' : A → A) :
    picked_in γ f -∗ picked_in γ f' -∗ ⌜ f = f' ⌝.
  Proof.
    iIntros "A B".
    iDestruct (own_valid_2 with "A B") as "val".
    iDestruct (prod_valid_1st with "val") as %val.
    iPureIntro.
    rewrite Some_valid in val.
    apply (to_agree_op_inv_L (A := leibnizO (A → A))) in val.
    done.
  Qed.

  (* Show that [promise_has_deps] is preserved by [promises_list_update] as
   * long as  the updated promise has a stronger predicate. *)
  Lemma promises_has_deps_promises_list_update pi prs id γ pia_old pia :
    promises_wf gc_map_wf prs →
    pred_stronger pia.(pi_pred) pia_old.(pi_pred) →
    promises_lookup_at prs id γ = Some pia_old →
    promises_has_deps pi prs (gc_map_wf (pi_id pi)) →
    promises_has_deps pi (promises_list_update id γ pia prs)
      (gc_map_wf (pi_id pi)).
  Proof.
    intros ? rStr look hsd idx.
    destruct (hsd idx) as (piSat & elm & ?).
    pose proof elm as elm2.
    destruct piSat.
    eapply promises_list_update_elem_of_2 in elm as [(? & ?) | (elm & eq1 & eq2)].
    - eexists. split; done.
    - eexists. split; first done.
      simpl in *. simplify_eq.
      eapply promises_elem_of in elm2; last done. simpl in elm2.
      simplify_eq.
      eapply promise_satisfy_dep_rel_stronger; done.
    - done.
  Qed.

  (* If both [pi1] and [pi2] are in [prs] and if [pi2] is a dependency of [pi1]
   * then [pi2] is later in the list. *)
  Lemma promises_deps_later pi1 pi2 prs idx :
    promises_wf gc_map_wf prs →
    pi2 ∈ prs →
    promises_lookup_at prs (pi_id pi1) (pi_γ pi1) = Some pi1.(pi_at) →
    pi_deps_γs pi1 !!! idx = pi_γ pi2 →
    Oids Ω (pi_id pi1) !!! idx = pi_id pi2 →
    ∃ i j, i < j ∧ prs !! i = Some pi1 ∧ prs !! j = Some pi2.
  Proof.
    intros wf ? look ??.
    apply promises_wf_lookup_at in look as (i & look & deps); last done.
    destruct (deps idx) as (piSat & elm & ? & ? & ?).
    simplify_eq.
    apply elem_of_list_lookup_1 in elm as (o & elm).
    rewrite lookup_drop in elm.
    edestruct (promises_wf_unique _ _ wf pi2 piSat) as [<-|diff]; try done.
    { eapply elem_of_list_lookup_2.
      apply elm. }
    2: { destruct diff as [neq|neq]; congruence. }
    exists i, (S i + o).
    split_and!; (lia || done).
  Qed.

  Lemma promises_has_deps_cons id γ pia1 pia2 prs :
    promises_wf gc_map_wf prs →
    promises_lookup_at prs id γ = Some pia2 →
    pia2.(pi_deps_γs) = pia1.(pi_deps_γs) →
    promises_has_deps (MkPi id γ pia1) prs (gc_map_wf id) →
    promises_has_deps (MkPi id γ pia1) (tail prs) (gc_map_wf id).
  Proof.
    (* This holds since the dependencies of [pi2] are after [pi2] in the list,
     * and hence they can not be present in the head as [pi2] is either the
     * head or even further back in the list. *)
    intros wf look ? deps.
    intros idx.
    destruct (deps idx) as (piSat & ? & ? & ? & ?).
    edestruct (promises_deps_later (MkPi id γ pia2)) as (i & j & ? & ? & ?); try done.
    { simpl in *. congruence. }
    exists piSat.
    split.
    { assert (1 ≤ j) as le by lia.
      apply Nat.le_exists_sub in le as (j' & eq & _).
      rewrite (comm (Nat.add)) in eq.
      simplify_eq.
      eapply elem_of_list_lookup_2.
      rewrite lookup_tail.
      done. }
    split; first done.
    eexists _. done.
  Qed.

  (* Updating a promise to a stronger promise while preserving well-formedness. *)
  Lemma promises_wf_promises_list_update id γ pia_old pia prs :
    promises_has_deps (MkPi id γ pia) prs (gc_map_wf id) →
    pi_deps_γs pia_old = pi_deps_γs pia →
    pred_stronger pia.(pi_pred) pia_old.(pi_pred) →
    promises_wf gc_map_wf prs →
    promises_lookup_at prs id γ = Some pia_old →
    promises_wf gc_map_wf (promises_list_update id γ pia prs).
  Proof.
    intros hasDeps ? rStr wf look.
    induction prs as [|pi prs' IH]; first done.
    eapply (promises_has_deps_cons _ _ pia) in hasDeps; try done.
    destruct wf as [wfPi wf].
    apply promises_lookup_at_cons_Some_inv in look.
    destruct look as [(<- & <- & eq3) | (neq & look)]; last first.
    * (* In this case the updated promise is in the tail of the list *)
      rewrite promises_list_update_cons_ne; last naive_solver.
      simpl.
      split; last first.
      { apply IH; done. }
      destruct wfPi as [look2 wf1].
      split.
      { rewrite promises_lookup_at_None in look2.
        apply promises_lookup_at_None.
        intros ? [pia' elm]%promises_list_update_elem_of_path.
        apply (look2 _ elm). }
      eapply promises_has_deps_promises_list_update; try done.
    * (* In this case the updated promise is the head of the list *)
      simpl in eq3.
      simplify_eq.
      rewrite (promises_list_update_cons_eq gc_map_wf); last done.
      simpl.
      split; last done.
      split; first apply wfPi.
      done.
  Qed.

  Lemma own_auth_promise_list_frag γ Rs1 Rs2 Ps1 Ps2 :
    own_auth_promise_list γ Rs1 Ps1 -∗
    own_frag_promise_list γ Rs2 Ps2 -∗
    ⌜ Rs2 `prefix_of` Rs1 ∧ Ps2 `prefix_of` Ps1 ⌝.
  Proof.
    iIntros "O1 O2".
    iDestruct (own_valid_2 with "O1 O2") as "O".
    unfold gc_tup_rel_pred.
    rewrite gen_cmra_op_eq.
    rewrite gen_cmra_validI.
    iDestruct "O" as "(_ & _ & _ & _ & %V1 & %V2)".
    apply pair_valid in V1, V2. simpl in *.
    destruct V1 as [V1 _].
    destruct V2 as [V2 _].
    apply mono_list_both_valid_L in V1.
    apply mono_list_both_valid_L in V2.
    done.
  Qed.

  Lemma pred_prefix_list_for'_prefix_of
      (Rs1 Rs2 : list (rel_over DS A)) Ps1 Ps2 R1 R2 P1 P2 :
    pred_prefix_list_for' Rs1 Ps1 R1 P1 →
    pred_prefix_list_for' Rs2 Ps2 R2 P2 →
    Ps1 `prefix_of` Ps2 →
    pred_stronger P2 P1.
  Proof.
    intros (? & ? & ? & ?) (? & ? & ? & ?) pref.
    apply pred_weaker_stronger.
    apply: pred_prefix_list_for_prefix_of; done.
  Qed.

  Lemma big_helper_lemma (i : fin n) γs iid
    (* wf *)
    (genInG_gti_typ : DS !!! i = Oc Ω iid)
    (ts : hvec (On Ω (genInDepsG_id g))
      (cmra_to_trans <$$> Ocs Ω (genInDepsG_id g)))
    (full_picks : ∀ i : fin gc_len, gmap gname (Oc Ω i → Oc Ω i))
    (transAt : full_picks
                (Oids Ω (genInDepsG_id g) !!! rew [fin] genInG_gcd_n in i)
              !! (rew [λ n : nat, ivec n gname] genInG_gcd_n in γs
                  !!! rew [fin] genInG_gcd_n in i) =
              Some
                (lookup_fmap_Ocs ts (rew [fin] genInG_gcd_n in i)
                   (gc_map_wf (genInDepsG_id g))))
    (idEq : iid =
         Oids Ω (genInDepsG_id g) !!! rew [fin] genInG_gcd_n in i) :
      (rew <- [cmra_to_trans] genInG_gti_typ in
        default (λ a : Oc Ω (iid), a)
          (full_picks (iid) !! (γs !!! i))) =
      (hvec_lookup_fmap (rew <- [id] trans_for_genInG in ts) i).
  Proof.
    unfold genInDepsG_id in *.
    unfold lookup_fmap_Ocs in *.
    unfold Ocs_Oids_distr in *.
    unfold Ocs in *.
    destruct (eq_sym idEq). clear idEq.
    rewrite (ivec_lookup_rew_rew (A := gname) _ γs) in transAt.
    rewrite transAt.
    simpl in *.
    clear.
    unfold trans_for_genInG.
    destruct g. destruct genInDepsG_gen. simpl in *.
    generalize dependent (gc_map_wf genInG_id (rew [fin] genInG_gcd_n in i)).
    intros wfa.
    unfold Oids in *.
    unfold Ocs in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n. simpl in *.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps. simpl in *.
    clear.
    generalize dependent (eq_sym wfa).
    generalize dependent (eq_sym genInG_gti_typ).
    set (ll := hvec_lookup_fmap ts i).
    generalize dependent ll.
    clear -genInG_gti_typ.
    set (C := Oc Ω (gcd_deps_ids !!! i)). rewrite -/C. generalize dependent C.
    destruct genInG_gti_typ.
    intros ????.
    destruct e.
    simpl.
    (* Provable with UIP *)
  Admitted.

  Lemma own_resource_for_deps_pick_in
      (γs : ivec n gname)
      (ts : hvec (On Ω (genInDepsG_id g))
        (cmra_to_trans <$$> Ocs Ω (genInDepsG_id g)))
      (full_picks : ∀ i : fin gc_len, gmap gname (Oc Ω i → Oc Ω i))
    (hv : transmap_valid full_picks)
    (_ : CmraMorphism (build_trans full_picks)) :
    trans_at_deps full_picks
      (genInDepsG_id g)
      (rew [λ n : nat, ivec n gname] genInG_gcd_n in γs) ts →
    own_resource_for_deps γs -∗
    ⚡={build_trans full_picks}=>
      (∀ i : fin n,
        picked_in (g := genInSelfG_gen (gs i)) (γs !!! i)
          (hvec_lookup_fmap (rew <- [id] trans_for_genInG in ts) i)).
  Proof.
    unfold own_resource_for_deps.
    iIntros (transAt) "OR".
    rewrite bnextgen_forall.
    iIntros (i).
    specialize (transAt (rew genInG_gcd_n in i)). simpl in *.
    iSpecialize ("OR" $! i).
    iDestruct (own_build_trans_next_gen_picked_in with "OR") as "OR"; first done.
    iModIntro.
    pose proof (genInDepsG_eqs i).
    erewrite big_helper_lemma; done.
  Qed.

  Lemma own_resource_for_deps_nextgen γs full_picks
      (hv : transmap_valid full_picks) `{!CmraMorphism (build_trans full_picks)} :
    own_resource_for_deps γs ⊢
    ⚡={build_trans full_picks}=> own_resource_for_deps γs.
  Proof.
    iIntros "O".
    rewrite bnextgen_forall.
    iIntros (idx).
    iSpecialize ("O" $! idx).
    iDestruct (own_build_trans_next_gen with "O") as "O"; first done.
    iModIntro.
    iApply own_mono; last done.
    simpl.
    eexists (gen_cmra_trans
      (rew <- [cmra_to_trans] genInG_gti_typ in
       default (λ a : Oc Ω (genInG_id (genInSelfG_gen (gs idx))), a)
         (full_picks (genInG_id (genInSelfG_gen (gs idx))) !! (γs !!! idx))) ε).
         done.
  Qed.

  Lemma used_token_nextgen γ γs (R : rel_over DS A) P :
    used_token γ γs R P ⊢ ⚡==> token γ γs R P.
  Proof.
    iNamed 1. iNamed "tokenPromise".
    iApply nextgen_empty.
    iIntros (full_picks ?).
    iDestruct (own_resource_for_deps_nextgen with "ownDeps") as "ownDeps'";
      first done.
    iDestruct (own_promises_nextgen with "prs") as "prs'"; first done.
    iDestruct (own_build_trans_next_gen with "usedToken") as "-#usedToken";
      first done.
    iDestruct "frocenAuthPreds" as "[auth1 auth2]".
    iCombine "auth1 auth2" as "auth".
    iDestruct (own_build_trans_next_gen with "auth") as "-#auth"; first done.
    iModIntro.
    iExists rels, preds, promises, pia.
    iSplit. { iFrame "prs'". done. }
    iDestruct (own_gen_cmra_split_alt with "usedToken")
      as "(_ & $ & _ & _ & _ & _)".
    iDestruct (own_gen_cmra_split_alt with "auth")
      as "(_ & _ & _ & _ & A & B)".
    iFrame "ownDeps'".
    unfold gen_cmra_trans. simpl.
    iCombine "A B" as "$".
    done.
  Qed.

  #[global]
  Instance into_nextgen_used_token γ γs R P : IntoNextgen _ _ :=
    used_token_nextgen γ γs R P.

  Lemma own_promises_auth_promise_list prs γ rels preds (R : rel_over DS A) P pia :
    pred_prefix_list_for' rels preds R P →
    promises_lookup_at prs (genInDepsG_id g) γ = Some pia →
    own_promises prs -∗
    own_auth_promise_list γ rels preds -∗
    ⌜ pred_stronger (rew [pred_over] genInG_gti_typ in P) pia.(pi_pred) ⌝.
  Proof.
    iIntros (??) "prs O2".
    iDestruct (big_sepL_elem_of with "prs") as "H".
    { apply promises_lookup_at_Some. done. }
    iDestruct (own_promise_info_own' with "H") as (???) "(OD & OF)".
    iDestruct (own_auth_promise_list_frag with "O2 [$]") as "[% %]".
    iPureIntro.
    (* unfold pred_stronger. intros ?. *)
    eapply pred_prefix_list_for'_prefix_of in H; try done.
    apply pred_weaker_stronger.
    apply pred_stronger_rew_sym.
    done.
  Qed.

  Lemma know_deps_agree γ γs1 γs2 :
    know_deps γ γs1 -∗
    know_deps γ γs2 -∗
    ⌜ γs1 = γs2 ⌝.
  Proof. apply deps_agree. Qed.

  Lemma own_promises_know_deps prs γ γs pia :
    promises_lookup_at prs (genInDepsG_id g) γ = Some pia →
    own_promises prs -∗
    know_deps γ γs -∗
    ⌜ γs = rew <- [λ n, ivec n _] genInG_gcd_n in pia.(pi_deps_γs) ⌝.
  Proof.
    iIntros (?) "prs OD".
    iDestruct (big_sepL_elem_of with "prs") as "H".
    { apply promises_lookup_at_Some. done. }
    iDestruct (own_promise_info_own' with "H") as (???) "(OD' & ?)".
    iDestruct (know_deps_agree with "OD OD'") as "$".
  Qed.

  Lemma own_promises_list_update owf γ rels preds R_2 P_2 prs γs
      deps_preds relToPred evidence :
    promises_wf owf prs →
    pred_prefix_list_for' (rels ++ (cons R_2 nil)) (preds ++ (cons P_2 nil)) R_2 P_2 →
    know_deps γ γs -∗
    own_frag_promise_list γ (rels ++ (cons R_2 nil)) (preds ++ (cons P_2 nil)) -∗
    own_promises prs -∗
    own_promises (
      promises_list_update (genInDepsG_id g) γ
      (make_pia γs deps_preds R_2 P_2 relToPred evidence) prs).
  Proof.
    iIntros (wf ?) "OD OF OP".
    unfold own_promises.
    rewrite 2!big_sepL_forall_elem_of.
    iIntros (? [?|(-> & pia_old' & elm)]%promises_list_update_elem_of).
    { iApply "OP". done. }
    iSpecialize ("OP" $! _ elm).
    rewrite own_promise_info_own'.
    rewrite own_promise_info_own'.
    iDestruct "OP" as (???) "[HO HP]".
    simpl.
    iExists _, _.
    rewrite 3!rew_opp_l.
    iFrame "OF".
    iFrame "OD".
    done.
  Qed.

  (** Strengthen a promise. *)
  Lemma token_strengthen_promise
      γ γs (deps_preds : preds_for n DS)
      (R_1 R_2 : rel_over DS A) (P_1 P_2 : (A → A) → Prop) :
    (* The new relation is stronger. *)
    (∀ (ts : trans_for n DS) (t : A → A),
       huncurry R_2 ts t → huncurry R_1 ts t) →
    (* The new predicate is stronger. *)
    (∀ t, P_2 t → P_1 t) →
    (* The new relation implies the new predicate. *)
    (∀ ts t, huncurry R_2 ts t → P_2 t) →
    (* Evidence that the promise is realizeable. *)
    (∀ (ts : trans_for n DS),
      preds_hold deps_preds ts →
      ∃ (t : A → A), CmraMorphism t ∧ huncurry R_2 ts t) →
    (* For every dependency we own a [rely_self]. *)
    (∀ (i : fin n), rely_self (γs !!! i) (hvec_lookup_fmap deps_preds i)) -∗
    token γ γs R_1 P_1 ==∗
    token γ γs R_2 P_2.
  Proof.
    iIntros (relStronger predStronger relToPred evidence) "relys".
    iDestruct (list_rely_self' with "relys") as (depPrs wf allDeps) "ownPrs".
    iNamed 1.
    iNamed "tokenPromise".
    iDestruct (own_promises_merge with "prs ownPrs") as (prsMerged ? val) "O";
      [done|done| ].
    (* For each dependency we have a rely and that rely will have a list of
     * promises. We need to merge all of these promises and then create an
     * updated promise for the token.*)
    rewrite /token.
    set (pia2 := make_pia γs deps_preds R_2 P_2 relToPred evidence).
    iDestruct (big_sepL_elem_of with "prs") as "H".
    { eapply promises_lookup_at_Some. done. }
    iDestruct (own_promise_info_own with "H") as (???) "(deps & _)"; first done.
    iExists (rels ++ (R_2 :: nil)).
    iExists (preds ++ (P_2 :: nil)).
    iExists (promises_list_update _ γ pia2 prsMerged).
    iExists pia2.
    iFrame "token".
    destruct val as (_ & str & ?).
    specialize (str _ _ _ pia_in) as (pia3 & ? & ?).
    iDestruct (own_promises_auth_promise_list with "O auth_preds") as %str2;
      try done.
    iDestruct (own_promises_know_deps with "O deps") as %depsEq; first done.
    iMod (auth_promise_list_snoc γ with "auth_preds") as "a".
    iDestruct (auth_promise_list_frag with "a") as "[$ #frag_preds]".
    iModIntro.
    unfold know_promise.
    iSplit. 2: {
      iFrame "ownDeps".
      iPureIntro. eapply pred_prefix_list_for'_grow; done. }
    iSplit; first done.
    iSplit.
    { iPureIntro. eapply promises_lookup_update. done. }
    iSplit.
    { iPureIntro.
      eapply promises_wf_promises_list_update; last done; try done.
      * unfold promises_has_deps. simpl.
        eapply (promises_has_deps_raw_stronger _ _ depPrs); done.
      * simpl. rewrite depsEq rew_opp_r //.
      * simpl.
        etrans; last apply str2.
        clear -predStronger.
        destruct genInG_gti_typ.
        simpl.
        intros t.
        apply predStronger. }
    iApply own_promises_list_update; try done.
    eapply pred_prefix_list_for'_grow; done.
  Qed.

  Lemma gen_pick_out_pick γ t :
    gen_pick_out γ GTS_tok_gen ==∗ gen_pick_out γ (GTS_tok_gen_shot t).
  Proof.
    iApply own_update.
    apply gen_cmra_update; try reflexivity.
    apply prod_update; first done; simpl.
    apply option_update.
    apply cmra_update_exclusive. done.
  Qed.

  Lemma own_auth_promise_list_freeze γ Rs Ps :
    own_auth_promise_list γ Rs Ps ==∗
    own_frozen_auth_promise_list γ Rs Ps.
  Proof.
    unfold own_auth_promise_list.
    unfold own_frozen_auth_promise_list.
    unfold gen_promise_rel_pred_list.
    rewrite -own_op.
    iApply own_update.
    apply gen_cmra_update; try reflexivity.
    - apply prod_update; simpl; first done; simpl.
      rewrite left_id.
      apply option_update.
      apply mono_list_auth_persist.
    - apply prod_update; simpl; first done; simpl.
      rewrite left_id.
      apply option_update.
      apply mono_list_auth_persist.
  Qed.

  Lemma gentrans_rew {B : cmra} t (eq : A = B) :
    CmraMorphism t →
    CmraMorphism (rew [cmra_to_trans] eq in t).
  Proof. destruct eq. done. Qed.

  Lemma GTS_tok_gen_rew_contradiction c :
    ✓ (GTS_tok_gen_shot c
       ⋅ gc_single_shot (rew [cmra_car] omega_genInG_cmra_eq in
          gc_tup_pick_out DS GTS_tok_gen)) → False.
  Proof.
    unfold omega_genInG_cmra_eq. simpl.
    destruct g. destruct genInDepsG_gen. simpl in *.
    unfold Ocs in *. unfold Oids in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps. simpl in *.
    intros [? V].
    apply V.
  Qed.

  Lemma own_picks_gen_pick_out trans γ :
    own_picks trans -∗
    gen_pick_out γ GTS_tok_gen -∗
    ⌜ trans (genInDepsG_id g) !! γ = None ⌝.
  Proof.
    iIntros "O1 O2".
    destruct (trans (genInDepsG_id g) !! γ) eqn:look;
      last naive_solver.
    iDestruct ("O1" $! _ _ _ look) as (????????) "O1".
    unfold gen_pick_out.
    rewrite own_gen_cmra_data_to_inG.
    iDestruct (own_valid_2 with "O1 O2") as "#Hv".
    iCombine "O1 O2" as "O".
    rewrite gen_cmra_validI. simpl.
    iDestruct "Hv" as "(_ & %Hv & _)".
    apply GTS_tok_gen_rew_contradiction in Hv.
    done.
  Qed.

  Lemma own_picks_insert γ (t : A → A) trans (* γs ts Rs R Ps *) :
    trans (genInDepsG_id g) !! γ = None →
    own_pick
      (transmap_singleton (genInDepsG_id g) γ
         (rew [cmra_to_trans] genInG_gti_typ in t) ∪ trans)
      (genInDepsG_id g) γ (rew [cmra_to_trans] genInG_gti_typ in t) -∗
    own_picks trans -∗
    own_picks
      (transmap_singleton (genInDepsG_id g) γ (rew [cmra_to_trans] genInG_gti_typ in t) ∪ trans).
  Proof.
    iIntros (no) "OP O".
    iIntros (??? [look|look]%transmap_lookup_union_Some).
    2: {
      iDestruct ("O" $! _ _ _ look) as (????????) "H".
      repeat iExists _. iFrame "∗%".
      iPureIntro. apply trans_at_deps_union_r; last done.
      intros ??????.
      apply gen_f_singleton_lookup_Some in H2 as (-> & -> & ?).
      congruence. }
    apply gen_f_singleton_lookup_Some in look as (-> & <- & <-).
    iApply "OP".
  Qed.

  Lemma rel_holds_rew (R : rel_over DS A) ts t :
    R ts t →
    (rew [λ a : Type, a] rel_over_Oc_Ocs_genInG in R)
       (rew [λ a : Type, a] trans_for_genInG in ts)
       (rew [cmra_to_trans] genInG_gti_typ in t).
  Proof.
    unfold rel_over_Oc_Ocs_genInG.
    unfold trans_for_genInG.
    destruct g. destruct genInDepsG_gen. simpl in *.
    unfold Ocs in *. unfold Oids in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps. simpl in *.
    done.
  Qed.

  Lemma rel_prefix_list_for_rew (R : rel_over DS A)
      (rels : list (rel_over DS A)) :
    rel_prefix_list_for rel_weaker rels R →
    rel_prefix_list_for rel_weaker
      (rew rel_over_eq genInG_gcd_n genInG_gti_typ genInG_gcd_deps in rels)
      (rew [λ a : Type, a]
           rel_over_eq genInG_gcd_n genInG_gti_typ genInG_gcd_deps in R).
  Proof.
    destruct g. destruct genInDepsG_gen. simpl in *.
    unfold Ocs in *. unfold Oids in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps. simpl in *.
    done.
  Qed.

  (* Picks the transformation for the resource at [γ]. This is only possible if
   * transformations has been picked for all the dependencies. *)
  Lemma token_pick γ γs (R : rel_over DS A) P (ts : trans_for n DS) t
      `{!CmraMorphism t} :
    huncurry R ts t →
    (∀ i, picked_out (g := genInSelfG_gen (gs i))
            (γs !!! i) (hvec_lookup_fmap ts i)) -∗
    token γ γs R P ==∗ used_token γ γs R P ∗ picked_out γ t.
  Proof.
    iIntros (rHolds) "picks".
    iNamed 1.
    unfold used_token. unfold picked_out.
    iDestruct (gen_token_split with "token") as "[tokenPerm tokenGen]".
    iDestruct (list_picked_out with "picks") as (trans val) "[%TA picks]".
    iDestruct (own_picks_gen_pick_out with "picks tokenGen") as %Hv.
    iFrame "tokenPerm".
    iMod (gen_pick_out_pick with "tokenGen") as "#tokShot".
    iFrame "tokShot".
    iMod (own_auth_promise_list_freeze with "auth_preds") as "[auth_preds #fr]".
    iModIntro.
    iSplitL "auth_preds".
    { repeat iExists _. iFrame "auth_preds fr". iFrame "#". done. }
    set (id := genInDepsG_id g).
    iExists (
      transmap_singleton id γ (rew [cmra_to_trans] genInG_gti_typ in t) ∪ trans
    ).
    iSplit.
    { iPureIntro. apply transmap_valid_union; last done.
      apply transmap_valid_singleton.
      apply gentrans_rew. done. }
    iSplit.
    { iPureIntro.
      apply transmap_lookup_union_Some_l.
      apply transmap_singleton_lookup. }
    iApply (own_picks_insert with "[] picks"); first done.
    iExists (rew [λ a, a] trans_for_genInG in ts).
    iExists (rew [λ n, ivec n _] genInG_gcd_n in γs).
    iExists (rew pred_over_Oc_genInG in preds).
    iExists (rew [λ a, a] rel_over_Oc_Ocs_genInG in R).
    iExists (rew rel_over_Oc_Ocs_genInG in rels).
    iSplit.
    { iPureIntro. apply trans_at_deps_insert; done. }
    iSplit.
    { iPureIntro. apply rel_holds_rew. done. }
    iSplit.
    { iPureIntro.
      destruct pred_prefix as (_ & pref & _).
      apply rel_prefix_list_for_rew.
      done. }
    unfold gen_pick_out.
    iDestruct (know_promise_extract_frag with "tokenPromise")
      as (???) "(deps & ?)".
    unfold know_deps.
    unfold gen_promise_rel_pred_list.
    rewrite !own_gen_cmra_data_to_inG.
    unfold Oown.
    iCombine "deps fr tokShot " as "O".
    iApply (own_mono with "O").
    clear.
    unfold genInDepsG_id in *.
    unfold omega_genInG_cmra_eq.
    destruct g. destruct genInDepsG_gen. simpl in*. clear.
    unfold Ocs in *.
    unfold rel_over_Oc_Ocs_genInG in *.
    simpl in *.
    unfold pred_over_Oc_genInG. simpl in *.
    destruct (gc_map Ω genInG_id). simpl in *.
    destruct genInG_gcd_n.
    destruct genInG_gti_typ.
    unfold eq_rect_r in *. simpl in *.
    destruct genInG_gcd_deps.
    done.
  Qed.

  Lemma token_to_rely γ γs (R : rel_over DS A) P :
    token γ γs R P ⊢ rely γ γs R P.
  Proof. iNamed 1. repeat iExists _. iFrame "#". Qed.

  Lemma token_rely_combine_pred γ γs R1 P1 R2 P2 :
    token γ γs R1 P1 -∗ rely γ γs R2 P2 -∗ ⌜ rel_stronger R1 R2 ⌝.
  Proof.
    iNamed 1. iNamed "tokenPromise".
    iDestruct 1 as (??) "(relyPromise & _)".
    (* iNamed 1. *)
    iDestruct (know_promise_extract_frag with "relyPromise")
      as (?? pref) "[_ fragPreds]".
    iDestruct (own_valid_2 with "auth_preds fragPreds") as "val".
    iDestruct (prod_valid_5th with "val") as "%val".
    iPureIntro.
    move: val.
    rewrite gen_nc_op. rewrite gen_nc_valid.
    intros prefix%mono_list_both_valid_L.
    destruct pred_prefix as (? & ? & ? & ?).
    destruct pref as (? & ? & ? & ?).
    apply rel_weaker_stronger.
    apply: pred_prefix_list_for_prefix_of; done.
  Qed.

  Lemma know_promise_combine γ γs1 R1 P1 pia1 promises1
      γs2 R2 P2 pia2 promises2 :
    know_promise γ γs1 R1 P1 pia1 promises1 -∗
    know_promise γ γs2 R2 P2 pia2 promises2 -∗
    ⌜ γs1 = γs2 ∧
      ((rel_stronger R1 R2 ∧ pred_stronger P1 P2) ∨
       (rel_stronger R2 R1 ∧ pred_stronger P2 P1)) ⌝.
  Proof.
    iNamed 1.
    destruct pia_for as (γs_eq & pred_eq & rel_eq).
    iDestruct 1 as (inf ??) "#prs2".
    destruct inf as (depsEq2 & pred_eq2 & rel_eq2).
    iDestruct (own_promises_overlap with "prs prs2") as %lap.
    iPureIntro.
    eassert (_ ∨ _) as [str|str]. { eapply lap; done. }
    - destruct str as (depsEq & rStr & pStr).
      split. {
        rewrite depsEq depsEq2 in γs_eq. clear -γs_eq.
        rewrite /eq_rect_r in γs_eq.
        apply (eq_inj (λ y : nat, ivec y gname)) in γs_eq.
        done. }
      left.
      rewrite rel_eq rel_eq2 in rStr.
      split.
      { clear -rStr.
        rewrite /rel_over_Oc_Ocs_genInG in rStr.
        destruct genInDepsG_gen. simpl in *.
        unfold Ocs in *.
        eapply rel_stronger_rew.
        apply rStr. }
      rewrite pred_eq pred_eq2 in pStr.
      clear -pStr.
      rewrite /pred_over_Oc_genInG in pStr.
      destruct genInDepsG_gen. simpl in *.
      destruct genInG_gti_typ.
      apply pStr.
    - destruct str as (depsEq & rStr & pStr).
      split. {
        rewrite -depsEq depsEq2 in γs_eq. clear -γs_eq.
        rewrite /eq_rect_r in γs_eq.
        apply (eq_inj (λ y : nat, ivec y gname)) in γs_eq.
        done. }
      right.
      rewrite rel_eq rel_eq2 in rStr.
      split.
      { clear -rStr.
        rewrite /rel_over_Oc_Ocs_genInG in rStr.
        destruct genInDepsG_gen. simpl in *.
        unfold Ocs in *.
        eapply rel_stronger_rew.
        apply rStr. }
      rewrite pred_eq pred_eq2 in pStr.
      rewrite /pred_over_Oc_genInG in pStr.
      clear -pStr.
      destruct genInDepsG_gen. simpl in *.
      destruct genInG_gti_typ.
      apply pStr.
  Qed.

  Lemma rely_combine γ γs1 γs2 R1 P1 R2 P2 :
    rely γ γs1 R1 P1 -∗
    rely γ γs2 R2 P2 -∗
    ⌜ γs1 = γs2 ⌝ ∗
    ⌜ (rel_stronger R1 R2 ∧ pred_stronger P1 P2) ∨
      (rel_stronger R2 R1 ∧ pred_stronger P2 P1) ⌝.
  Proof.
    iNamed 1.
    iDestruct 1 as (??) "(relyPromise2 & _)".
    iDestruct (know_promise_combine with "relyPromise relyPromise2") as "$".
  Qed.

  Lemma transmap_overlap_resp_promises_empty prs :
    transmap_overlap_resp_promises (λ i : fin gc_len, ∅) prs.
  Proof. intros ???. right. done. Qed.

  Lemma gen_own_nextgen γ a :
    gen_own γ a ⊢ ⚡==> ∃ t, picked_in γ t ∗ gen_own γ (t a).
  Proof.
    iIntros "O".
    iDestruct (own_next_gen with "O") as "O".
    iModIntro.
    iDestruct "O" as (t) "O".
    iExists t.
    iDestruct (own_gen_cmra_split_alt with "O") as "($ & _ & $ & _ & _)".
  Qed.

  #[global]
  Instance into_nextgen_gen_own γ a : IntoNextgen _ _ := gen_own_nextgen γ a.

  Lemma rely_nextgen γ γs (R : rel_over DS A) (P : pred_over A) :
    rely γ γs R P ⊢
    ⚡==>
      rely γ γs R P ∗
      ∃ (t : A → A) (ts : trans_for n DS),
        ⌜ huncurry R ts t ∧ (* The transformations satisfy the promise *)
          P t ⌝ ∗ (* For convenience we also give this directly *)
        picked_in γ t ∗
        (* The transformations for the dependencies are the "right" ones *)
        (∀ i, picked_in (g := genInSelfG_gen (gs i)) (γs !!! i) (hvec_lookup_fmap ts i)).
  Proof.
    rewrite /rely.
    (* iIntros "DR". *)
    iNamed 1.
    iDestruct (know_promise_extract_frag with "relyPromise") as (?? pref1) "[? fragPreds]".
    iNamed "relyPromise".
    rewrite nextgen_unseal /nextgen_def.
    iExists (λ i, ∅), promises.
    iSplit; first done.
    iSplit; first done.
    iSplit; first iApply own_picks_empty.
    iFrame "prs".
    iIntros (full_picks val resp _).
    iDestruct (own_build_trans_next_gen with "fragPreds") as "-#frag_preds'"; first done.
    iDestruct (own_promises_nextgen with "prs") as "prs'"; first done.
    edestruct (transmap_resp_promises_lookup_at)
      as (ts & t & look & ? & relHolds); [done|done| ].
    simpl in *.
    iDestruct (own_resource_for_deps_pick_in with "ownDeps") as "depsPickedIn";
      first done.
    { destruct pia_for as (eq & _). rewrite eq in H. apply H. }
    iDestruct (own_resource_for_deps_nextgen with "ownDeps") as "ownDeps'";
      first done.
    iModIntro.
    rewrite look.
    iDestruct (own_gen_cmra_split with "frag_preds'")
      as "(picked_in & frag_preds' & _ & _ & A & B)".
    iSplit.
    - iExists promises, pia.
      iFrame "ownDeps'".
      do 3 (iSplit; first done).
      iFrame "prs'".
    - iExists (rew <- [cmra_to_trans] genInG_gti_typ in t).
      iExists (rew <- [id] trans_for_genInG in ts).
      simpl.
      iFrame "picked_in".
      iFrame "depsPickedIn".
      iPureIntro.
      eapply promise_info_for_pi_rel; done.
  Qed.

  #[global]
  Instance into_nextgen_rely γ γs R P : IntoNextgen _ _ :=
    rely_nextgen γ γs R P.

  Lemma picked_out_nextgen γ t `{!CmraMorphism t} :
    picked_out γ t ⊢ ⚡==> picked_in γ t.
  Proof.
    iNamed 1.
    rewrite nextgen_unseal /nextgen_def.
    iExists picks, [].
    iSplit; first done.
    iSplit; first done.
    iFrame "picks".
    iSplit. { iApply own_promises_empty. }
    iIntros (??? sub).
    iDestruct (own_build_trans_next_gen with "shotT") as "O"; first done.
    iModIntro.
    specialize (sub (genInDepsG_id g)).
    rewrite map_subseteq_spec in sub.
    eassert _ as eq. { apply sub. apply picksLook. }
    rewrite eq.
    simpl.
    rewrite rew_opp_l.
    done.
  Qed.

  #[global]
  Instance into_nextgen_picked_out γ t `{!CmraMorphism t} : IntoNextgen _ _ :=
    picked_out_nextgen γ t.

  Lemma rely_self_nextgen γ P :
    rely_self γ P ⊢
    ⚡==> rely_self γ P ∗ ∃ t, ⌜ P t ⌝ ∗ picked_in γ t.
  Proof.
    iNamed 1.
    iDestruct (know_promise_extract_frag with "relyPromise") as (?? pref1) "[? fragPreds]".
    iNamed "relyPromise".
    rewrite nextgen_unseal /nextgen_def.
    iExists (λ i, ∅), promises.
    iSplit; first done.
    iSplit; first done.
    iSplit; first iApply own_picks_empty.
    iFrame "prs".
    iIntros (full_picks val resp _).
    iDestruct (own_build_trans_next_gen with "fragPreds") as "-#frag_preds'"; first done.
    iDestruct (own_promises_nextgen with "prs") as "prs'"; first done.
    edestruct (transmap_resp_promises_lookup_at)
      as (ts & t & look & ? & relHolds); [done|done| ].
    simpl in *.
    iModIntro.
    iDestruct (own_gen_cmra_split with "frag_preds'")
      as "(picked_in & frag_preds' & _ & _ & A & B)".
    iSplit.
    { iExists _, _, _, _. iFrame "prs'". done. }
    iExists (rew <- [cmra_to_trans] genInG_gti_typ in t).
    rewrite look.
    iFrame "picked_in".
    iPureIntro.
    edestruct promise_info_for_pi_rel as [_ HP];  done.
  Qed.

  #[global]
  Instance into_nextgen_rely_self γ P : IntoNextgen _ _ :=
    rely_self_nextgen γ P.

End rules_with_deps.

Instance genInSelfG_empty Σ Ω :
  ∀ i : fin 0, genInSelfG Σ Ω ([#] !!! i).
Proof. intros i. inversion i. Qed.

Instance genInSelfG_one Σ Ω n A (DS : ivec n cmra):
  genInG Σ Ω A DS →
  ∀ i : fin 1, genInSelfG Σ Ω ([#A] !!! i).
Proof. intros ? i. dependent elimination i. Defined.

Section rules_zero_deps.

  Context
  (* {n : nat} {DS : ivec n cmra} *)
    (* `{gs : ∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)} *)
    `{g : !genInDepsG Σ Ω A [#] }.

  (* Various lemmas from above specialized to the case where a generational
   * camera has no dependencies. In this cas there is no difference between the
   * relation and the predicate, and there are no information about
   * dependencies, hence lemmas can be simplified quite a bit. *)

  Lemma token_strengthen_promise_0_deps γ
      (P_1 P_2 : (A → A) → Prop) :
    (* The new predicate is stronger. *)
    (∀ t, P_2 t → P_1 t) →
    (* Evidence that the promise is realizeable. *)
    (∃ (t : A → A), CmraMorphism t ∧ P_2 t) →
    token γ [#] P_1 P_1 ==∗
    token γ [#] P_2 P_2.
  Proof.
    intros. iIntros "T".
    iApply (token_strengthen_promise (DS := [#]) _ _ [##] with "[] T"); try done.
    - intros ts. dependent elimination ts as [hnil]. done.
    - intros ts. dependent elimination ts as [hnil]. done.
    - intros ts. dependent elimination ts as [hnil]. done.
    - iIntros (i). inversion i.
  Qed.

End rules_zero_deps.

Section test.
  Context `{Ω : gGenCmras Σ}.

  Lemma test :
    ⊢ ⚡==> ⌜ (2 + 2 = 4)%nat ⌝.
  Proof. iModIntro. done. Qed.

End test.

