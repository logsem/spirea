(** A generational ghost-map without dependencies.

   This is a stripped-down sibling of [self.high.resources.gen_ghost_map]: the
   standard Iris [ghost_map] resource re-expressed with [gen_own] so that it
   lives in the nextgen world.  Unlike [gen_ghost_map], the transformation here
   does *not* depend on [crashed_atR] / the offset view — it is driven purely by
   a [nat] threshold — so the underlying cmra is a bare [gmap_viewUR],
   and the assertions carry no [rely]/[crashed] side-conditions.

   The ghost-map operations reuse the lemma names and proofs of
   [gen_ghost_map] wherever they overlap.  On top of them we expose a
   persistency token whose promised transformation [gmap_trans p] keeps exactly
   the keys [≤ p] of the authoritative map.

 * This file is ported with help from claude code. *)
From Equations Require Import Equations.
From iris.algebra Require Import gmap_view agree.
From iris.bi.lib Require Import fractional.
From iris_named_props Require Import named_props.
From self.nextgen Require Import hvec nextgen_promises gmap_view_transformation.
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type*".

Definition gen_maps_drop_word s :=
  String.substring (1 + String.findex 0 " " s) (String.length s) s.

Tactic Notation "iPickedInAgree" constr(Hs) :=
  let na := eval vm_compute in (gen_maps_drop_word Hs) in
  iDestruct (gen_picked_in_agree with Hs) as %<-;
  iClear na.

Class gen_mapG (V: Type) (Σ: gFunctors) (Ω: gGenCmras Σ) := {
  gen_mapG_inG :: genInDepsG Σ Ω (gmap_viewUR nat (agreeR (leibnizO V))) [#];
}.

Section gen_map.
  Context {V: Type}.
  Context `{!gen_mapG V Σ Ω}.

  Implicit Types (m: gmap nat V) (k p n: nat) (v: V) (dq: dfrac) (q: Qp).

  Notation gmapR := (gmap_viewR nat (agreeR (leibnizO V))).

  Definition ghost_map_auth γ dq m: iProp Σ :=
    gen_own γ (gmap_view_auth (V := agreeR (leibnizO V)) dq (to_agree <$> m)).

  Definition ghost_map_elem γ k dq v: iProp Σ :=
    gen_own γ (gmap_view_frag (V := agreeR (leibnizO V)) k dq (to_agree v)).

  (** ** Instances (mirroring [gen_ghost_map]). *)

  #[global] Instance ghost_map_elem_timeless γ k dq v : Timeless (ghost_map_elem γ k dq v).
  Proof. apply _. Qed.
  #[global] Instance ghost_map_elem_persistent γ k v : Persistent (ghost_map_elem γ k DfracDiscarded v).
  Proof. apply _. Qed.
  #[global] Instance ghost_map_auth_persistent γ m :
    Persistent (ghost_map_auth γ DfracDiscarded m).
  Proof. rewrite /ghost_map_auth /gmap_view_auth. apply _. Qed.

  #[global] Instance ghost_map_elem_fractional γ k v :
    Fractional (λ q, ghost_map_elem γ k (DfracOwn q) v)%I.
  Proof.
    intros p q.
    rewrite /ghost_map_elem -gen_own_op.
    by rewrite -gmap_view_frag_op dfrac_op_own agree_idemp.
  Qed.

  #[global] Instance ghost_map_elem_as_fractional γ k q v :
    AsFractional (ghost_map_elem γ k (DfracOwn q) v) (λ q, ghost_map_elem γ k (DfracOwn q) v)%I q.
  Proof. split; first done. apply _. Qed.

  #[global] Instance ghost_map_auth_fractional γ m :
    Fractional (λ q, ghost_map_auth γ (DfracOwn q) m)%I.
  Proof.
    intros p q.
    rewrite /ghost_map_auth -gen_own_op.
    by rewrite -gmap_view_auth_dfrac_op dfrac_op_own.
  Qed.

  #[global] Instance ghost_map_auth_as_fractional γ q m :
    AsFractional (ghost_map_auth γ (DfracOwn q) m) (λ q, ghost_map_auth γ (DfracOwn q) m)%I q.
  Proof. split; first done. apply _. Qed.

  (** ** Ghost-map lemmas (mirroring [gen_ghost_map]). *)

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist γ k dq v:
    ghost_map_elem γ k dq v ==∗ ghost_map_elem γ k DfracDiscarded v.
  Proof.
    iIntros "own_elem".
    iMod (gen_own_update with "own_elem") as "$"; last done.
    apply gmap_view_frag_persist.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ (DfracOwn 1) m ==∗
    ghost_map_auth γ (DfracOwn 1) (<[k := v]> m) ∗ ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    intros Hm.
    iIntros "own_auth".
    iMod (gen_own_update with "own_auth") as "[$ $]"; last done.
    rewrite fmap_insert.
    apply: (gmap_view_alloc (V := agreeR $ leibnizO V) _ k (DfracOwn 1) (to_agree v)); [ | done | done ].
    rewrite lookup_fmap Hm //.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ (DfracOwn 1) m -∗ ghost_map_elem γ k (DfracOwn 1) v ==∗
    ghost_map_auth γ (DfracOwn 1) (<[k := w]> m) ∗ ghost_map_elem γ k (DfracOwn 1) w.
  Proof.
    iIntros "own_auth own_elem".
    iMod (gen_own_update_2 with "own_auth own_elem") as "[$ $]"; last done.
    rewrite fmap_insert. apply: gmap_view_replace. done.
  Qed.

  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ (DfracOwn 1) m ==∗
    ghost_map_auth γ (DfracOwn 1) (<[k := v]> m) ∗ ghost_map_elem γ k DfracDiscarded v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_lookup {γ dp m k dq v} :
    ghost_map_auth γ dp m -∗ ghost_map_elem γ k dq v -∗ ⌜m !! k = Some v⌝.
  Proof.
    iIntros "own_auth own_elem".
    iDestruct (gen_own_valid_2 with "own_auth own_elem") as
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    apply (to_agree_included_L (SI:=natSI) (A:=leibnizO V)) in Hincl.
    by rewrite Hincl.
  Qed.

  Lemma ghost_map_lookup_big {γ dp dq m} m0 :
    ghost_map_auth γ dp m -∗
    ([∗ map] k↦v ∈ m0, ghost_map_elem γ k dq v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  (** Make the authoritative element read-only. *)
  Lemma ghost_map_auth_persist γ dq m:
    ghost_map_auth γ dq m -∗ |==> ghost_map_auth γ DfracDiscarded m.
  Proof.
    iIntros "own_auth".
    iMod (gen_own_update with "own_auth") as "$"; last done.
    apply gmap_view_auth_persist.
  Qed.

  Lemma ghost_map_auth_valid_2 γ dq1 dq2 m1 m2 :
    ghost_map_auth γ dq1 m1 -∗ ghost_map_auth γ dq2 m2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ m1 = m2⌝.
  Proof.
    iIntros "own_auth own_auth'".
    iDestruct (gen_own_valid_2 with "own_auth own_auth'") as %[? ?%(map_fmap_equiv_inj _
      (to_agree_inj (A:=(leibnizO _))))]%gmap_view_auth_dfrac_op_valid.
    by fold_leibniz.
  Qed.

  Lemma ghost_map_auth_agree γ dq1 dq2 m1 m2 :
    ghost_map_auth γ dq1 m1 -∗ ghost_map_auth γ dq2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  Lemma ghost_map_elem_valid γ k dq v: ghost_map_elem γ k dq v -∗ ⌜✓ dq⌝.
  Proof.
    iIntros "own_elem".
    iDestruct (gen_own_valid with "own_elem") as %?%gmap_view_frag_valid.
    naive_solver.
  Qed.

  Lemma ghost_map_elem_valid_2 γ k dq1 dq2 v1 v2 :
    ghost_map_elem γ k dq1 v1 -∗ ghost_map_elem γ k dq2 v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    iIntros "own_elem own_elem'".
    iDestruct (gen_own_valid_2 with "own_elem own_elem'") as %[? Hag]%gmap_view_frag_op_valid.
    rewrite to_agree_op_valid_L in Hag. done.
  Qed.

  Lemma ghost_map_elem_agree γ k dq1 dq2 v1 v2 :
    ghost_map_elem γ k dq1 v1 -∗ ghost_map_elem γ k dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  (** ** Persistency token and its promised transformation.

     This machinery is specific to this library — [gen_ghost_map] uses the
     [crashed_at]-based [ghost_map_rel] instead. *)

  (* Keep the entries whose key is [< p].  We spell the comparison with the
     explicit [Nat.lt] (rather than the [<] notation, which may resolve to a
     different order in importing files) so that the produced [filter …]
     predicate — and hence its [Decision] instance — matches verbatim at use
     sites. *)
  Definition drop_lt p (n: nat) (v: leibnizO V): option V :=
    if decide (Nat.lt n p) then Some v else None.

  #[export] Instance drop_lt_maptrans p: MapTrans (drop_lt p).
  Proof.
    split; last solve_proper.
    rewrite /drop_lt => ? ? ? ?.
    destruct (decide _); done.
  Qed.

  Definition gmap_trans p: gmapR → gmapR :=
    map_entry_lift_gmap_view (V := leibnizO V) (drop_lt p).

  Definition gmap_prom p: pred_over gmapR :=
    λ t, ∃ p', p ≤ p' ∧ t = gmap_trans p'.

  Definition gmap_token γ p := token γ [#] (gmap_prom p) (gmap_prom p).

  Definition gmap_rely γ p := rely_self γ (gmap_prom p).

  Lemma gmap_alloc_empty:
    ⊢ |==> ∃ γ, ghost_map_auth γ (DfracOwn 1) ∅ ∗ gmap_token γ 0.
  Proof.
    iMod (own_gen_alloc (DS := [#]) (gmap_view_auth (DfracOwn 1) ∅) [#] [##] with "[]")
      as (γ) "(HO & tok)".
    { by apply gmap_view_auth_valid. }
    { iIntros (i'). inversion i'. }
    iMod (token_strengthen_promise (DS := [#])
            _ [#] [##] _ (gmap_prom 0) _ (gmap_prom 0) with "[] tok") as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      exists (gmap_trans 0).
      split; first apply _.
      exists 0.
      naive_solver. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iExists γ.
    rewrite /ghost_map_auth /gmap_token fmap_empty.
    iFrame.
  Qed.

  Lemma gmap_token_strengthen {γ p} p':
    p ≤ p' →
    gmap_token γ p ==∗ gmap_token γ p' ∗ gmap_rely γ p'.
  Proof.
    iIntros (?) "token".
    iMod (token_strengthen_promise_0_deps _ _ (gmap_prom p') with "token") as "token".
    { intros ? (p'' & ? & ->). exists p''. split; [lia|done]. }
    { exists (gmap_trans p'). split; first apply _. by exists p'. }
    iDestruct (token_to_rely with "token") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "#rely_self".
    iModIntro. iFrame "token rely_self".
  Qed.

  Lemma map_imap_drop_lt p m:
    map_imap (drop_lt p) m = filter (λ '(k, _), Nat.lt k p) m.
  Proof.
    apply map_eq. intros k.
    rewrite map_lookup_imap map_lookup_filter.
    destruct (m !! k) as [v|] eqn:E; rewrite E /=; last done.
    rewrite /drop_lt.
    destruct (decide (Nat.lt k p)) as [Hlt|Hlt];
      [ rewrite option_guard_True // | rewrite option_guard_False // ].
  Qed.

  (* A single fragment together with a rely survives a crash. *)
  Lemma gmap_elem_rely_nextgen γ k v p:
    Nat.lt k p →
    ghost_map_elem γ k (DfracOwn 1) v -∗ gmap_rely γ p -∗
    ⚡==> (ghost_map_elem γ k (DfracOwn 1) v ∗ gmap_rely γ p).
  Proof.
    iIntros (?) "elem #rely".
    rewrite /gmap_rely.
    iDestruct (rely_self_nextgen with "rely") as "rely'".
    iDestruct (gen_own_nextgen with "elem") as "elem".
    iModIntro.
    iDestruct "rely'" as "[$ (%t & %Ht & picked2)]".
    iDestruct "elem" as (t') "[picked1 elem]".
    iPickedInAgree "picked1 picked2".
    destruct Ht as (p' & ? & ->).
    rewrite /ghost_map_elem.
    iApply (gen_own_proper with "elem").
    rewrite /gmap_trans /map_entry_lift_gmap_view /gMapTrans_frag_lift
      /map_trans_frag_lift /fmap_view /fmap_pair /gmap_view_frag /view_frag /=.
    f_equiv.
    rewrite -{2}insert_empty map_imap_insert map_imap_empty.
    rewrite agree_option_map_to_agree /drop_lt decide_True //.
    lia.
  Qed.

  (* Under a crash, the authoritative map, a bundle of owned fragments and the
     token all get restricted to the entries with key [≤ p']; entries with a
     larger key are dropped. *)
  Lemma ghost_map_auth_elems_token_nextgen {γ p } p' m (m__w: gmap nat V):
    p ≤ p' →
    ghost_map_auth γ (DfracOwn 1) m -∗
    ([∗ map] k↦v ∈ m__w, ghost_map_elem γ k (DfracOwn 1) v) -∗
    gmap_token γ p -∗
    |==> ⚡==> (ghost_map_auth γ (DfracOwn 1) (filter (λ '(k, _), Nat.lt k p') m) ∗
               ([∗ map] k↦v ∈ filter (λ '(k, _), Nat.lt k p') m__w, ghost_map_elem γ k (DfracOwn 1) v) ∗
               gmap_token γ p').
  Proof.
    iIntros (Hle) "auth elems tok".
    iMod (gmap_token_strengthen p' with "tok") as "[tok _]"; first done.
    iMod (token_pick (DS := [#]) _ _ _ _ [##]%HV (gmap_trans p') with "[] tok")
      as "[tok #picked]".
    { exists p'. split; [lia|done]. }
    { iIntros (i). inversion i. }
    iModIntro.
    iDestruct (big_sepM_impl with "elems []") as "elems".
    { iIntros "!>" (k v ?) "e".
      iDestruct (gen_own_nextgen with "e") as "e". iAccu. }
    iDestruct (nextgen_big_sepM with "elems") as "elems".
    iModIntro.
    iDestruct "auth" as (t) "[#picked' auth]".
    iPickedInAgree "picked picked'".
    iSplitL "auth".
    { rewrite /ghost_map_auth.
      iApply (gen_own_proper with "auth").
      rewrite /gmap_trans map_entry_lift_gmap_view_auth map_imap_drop_lt //. }
    iFrame "tok".
    rewrite big_sepM_filter.
    iApply (big_sepM_impl with "elems").
    iIntros "!>" (k v Hk) "e %Hle'".
    iDestruct "e" as (t') "[#picked'' e]".
    iPickedInAgree "picked picked''".
    rewrite /ghost_map_elem.
    iApply (gen_own_proper with "e").
    rewrite /gmap_trans /map_entry_lift_gmap_view /gMapTrans_frag_lift
      /map_trans_frag_lift /fmap_view /fmap_pair /gmap_view_frag /view_frag /=.
    f_equiv.
    rewrite -{2}insert_empty map_imap_insert map_imap_empty.
    rewrite agree_option_map_to_agree /drop_lt decide_True //.
  Qed.
End gen_map.
