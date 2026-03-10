From Equations Require Import Equations.
From iris.algebra Require Import mono_list gmap_view.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.
From self.nextgen Require Import hvec nextgen_promises.
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type*".

(* TODO: upstream this tactic. *)
Definition drop_word s := substring (1 + findex 0 " " s) (String.length s) s.

Tactic Notation "iPickedInAgree" constr(Hs) :=
  let na := eval vm_compute in (drop_word Hs) in
  iDestruct (gen_picked_in_agree with Hs) as %<-;
  iClear na.

(** The exclusive ghost resource: [excl_list V].
 ** [list_auth γ l]: is the authoritative assertion, allowing growing the list,
 ** [list_elem γ l]: is the indivdual list element. *)
Class excl_listG (V: ofe) (Σ: gFunctors) (Ω: gGenCmras Σ) := {
  excl_listG_ghost_map_inG :: genInDepsG Σ Ω (gmap_viewUR nat (leibnizO V)) [#];
}.

Section excl_list.
  Context {V: ofe}.
  Context `{!excl_listG V Σ Ω}.

  Implicit Types (n p: nat) (l: list V) (v: leibnizO V).
  
  Definition drop_above p n (v: leibnizO V): option V :=
    if decide (n ≤ p) then Some v else None.

  Notation excl_listR := (gmap_viewR nat (leibnizO V)).
  
  #[export] Instance drop_above_maptrans p: MapTrans (drop_above p).
  Proof.
    split; last solve_proper.
    rewrite /drop_above => ? ? ? ?.
    destruct (decide _); done.
  Qed.
  
  Definition excl_list_trans p: excl_listR → excl_listR :=
    (map_entry_lift_gmap_view (V := leibnizO V) (drop_above p)).
  
  Definition to_excl_list l: gmap nat V :=
    map_seq 0 l.

  Definition to_excl_list_snoc l v:
    to_excl_list (l ++ [v]) = <[ length l := v ]> (to_excl_list l).
  Proof.
    rewrite /to_excl_list map_seq_snoc //.
  Qed.
  
  Definition excl_list_pred n: pred_over excl_listR :=
    λ t, ∃ n', n ≤ n' ∧ t = excl_list_trans n'.
  
  Definition list_auth γ l: iProp Σ :=
    "auth" ∷ gen_own γ (gmap_view_auth (V := leibnizO V) (DfracOwn 1) (to_excl_list l)) ∗
    "discards" ∷ ([∗ list] k ↦ v ∈ l, gen_own γ (gmap_view_frag (V:= leibnizO V) k DfracDiscarded v)).

  Definition dfrac_excl := DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2 / 2).

  Definition dfrac_excl_excl:
    ¬ ✓ (dfrac_excl ⋅ dfrac_excl).
  Proof.
    rewrite /dfrac_excl.
    rewrite {1}comm assoc comm -assoc dfrac_op_own dfrac_valid_own.
    rewrite Qp.half_half assoc Qp.div_2.
    apply Qp.not_add_le_r.
  Qed.
  
  Definition list_elem γ l: iProp Σ :=
    "excl" ∷ (∃ v, ⌜ last l = Some v ⌝ ∗ gen_own γ (gmap_view_frag (V := leibnizO V) (length l - 1) (dfrac_excl) v)) ∗
    "discards" ∷ ([∗ list] k ↦ v ∈ l, gen_own γ (gmap_view_frag (V:= leibnizO V) k DfracDiscarded v)).

  Definition list_token γ (n: nat) :=
    token γ [#] (excl_list_pred n) (excl_list_pred n).
  
  Definition list_elem_with_rely γ l: iProp Σ :=
    list_elem γ l ∗ ∃ n, ⌜ n ≥ length l ⌝ ∗ rely_self γ (excl_list_pred n).

  Lemma excl_list_alloc:
    ⊢ |==> ∃ γ, list_auth γ [] ∗ list_token γ 0.
  Proof.
    iMod (own_gen_alloc (DS := [#]) (gmap_view_auth (DfracOwn 1) ∅) [#] [##] with "[]") as (γ) "(HO & tok)".
    { by apply gmap_view_auth_valid. }
    { iIntros (i'). inversion i'. }
    iMod (token_strengthen_promise (DS := [#])
            _ [#] [##] _ (excl_list_pred 0) _ (excl_list_pred 0) with "[] tok")
      as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      exists (excl_list_trans 0).
      split; first apply _.
      exists 0.
      naive_solver. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iDestruct (token_to_rely with "tok") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "?".
    iExists _.
    iFrame "∗#".
    rewrite big_sepL_nil //.
  Qed.

  #[export] Instance list_elem_into_nextgen {γ} l:
    IntoNextgen
      (list_elem_with_rely γ l)
      (list_elem_with_rely γ l).
  Proof.
    rewrite /IntoNextgen /list_elem.
    iIntros "[list_elem #rely]".
    iNamed "list_elem".
    (* add nextgen modality to [∗list] *)
    iDestruct (big_sepL_impl with "discards []") as "discards".
    { iIntros "!>" (k v ?) "own".
      iDestruct (gen_own_nextgen with "own") as "own".
      iAccu. }
    simpl.
    iDestruct (nextgen_big_sepL with "discards") as "discards".
    iModIntro.
    iDestruct ("excl") as (v ? t) "[#picked1 excl]".
    iDestruct ("rely") as (n ?) "(rely & %t' & %Ht & picked2)".
    iPickedInAgree "picked1 picked2".
    destruct Ht as (n' & ? & ->).
    iSplitL "excl discards"; first iSplitL "excl".
    { iExists v.
      iSplit; first done.
      iApply (gen_own_proper with "excl").
      rewrite /excl_list_trans.
      unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
      unfold gmap_view_frag, view_frag.
      f_equiv.
      rewrite -{2}insert_empty.
      erewrite map_imap_insert_Some;
        first rewrite map_imap_empty insert_empty //.
      rewrite agree_option_map_to_agree /drop_above decide_True //.
      lia. }
    - iApply (big_sepL_impl with "discards").
      iIntros "!>" (k v' ?) "(%t & picked2 & discard)".
      assert (k < length l).
      { apply lookup_lt_is_Some_1. by eexists. }
      iPickedInAgree "picked1 picked2".
      iApply (gen_own_proper with "discard").
      rewrite /excl_list_trans.
      unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
      unfold gmap_view_frag, view_frag.
      f_equiv.
      rewrite -{2}insert_empty.
      erewrite map_imap_insert_Some;
        first rewrite map_imap_empty insert_empty //.
      rewrite agree_option_map_to_agree /drop_above decide_True //.
      lia.
    - iExists n.
      naive_solver.
  Qed.

  Lemma list_auth_grow {γ l} v:
    list_auth γ l ==∗ list_auth γ (l ++ [v]) ∗ list_elem γ (l ++ [v]).
  Proof.
    iNamed 1.
    iMod (gen_own_update with "auth") as "[$ frag]".
    { rewrite to_excl_list_snoc. apply: (gmap_view_alloc _ _ (DfracOwn 1) v); last done.
      rewrite lookup_map_seq_None. by right. }

    iDestruct "frag" as "[frag_half [frag_qtr discard]]".
    iDestruct (gen_own_op with "[$frag_half $frag_qtr]") as "frag_excl".
    rewrite -gmap_view_frag_op.
    iMod (gen_own_update with "discard") as "discard".
    { apply gmap_view_frag_persist. }
    iDestruct (big_sepL_snoc with "[$discards $discard]") as "#discards'".
    iFrame "discards'".
    iModIntro.
    iExists v.
    iSplit; first rewrite last_snoc //.
    rewrite app_length /= PeanoNat.Nat.add_sub.
    done.
  Qed.

  Lemma list_elem_excl {γ} l:
    list_elem γ l -∗ list_elem γ l -∗ False.
  Proof.
    iIntros "[(% & % & excl1) _] [(% & % & excl2) _]".
    iDestruct (gen_own_valid_2 with "[$] [$]") as %[Hval _]%gmap_view_frag_op_valid.
    apply dfrac_excl_excl in Hval as [].
  Qed.

  Lemma lookup_prefix l1 l2:
    (∀ k, k < length l1 → l1 !! k = l2 !! k) → l1 `prefix_of` l2.
  Proof.
    induction l1 using rev_ind; intros look; first by eexists.
    rewrite app_length /= in look.
    assert (l1 `prefix_of` l2) as [l2' ->].
    { apply IHl1.
      intros.
      specialize (look k ltac:(lia)).
      rewrite lookup_app_l // in look. }
    assert (head l2' = Some x) as [l2'' ->]%head_Some.
    { rewrite head_lookup.
      specialize (look (length l1) ltac:(lia)).
      rewrite ?lookup_app_r ?Nat.sub_diag /= // in look. }
    exists l2''.
    rewrite -app_assoc //.
  Qed.
    
  Lemma list_elem_prefix {γ} l1 l2:
    list_elem γ l1 -∗ list_elem γ l2 -∗ ⌜ l1 `prefix_of` l2 ∨ l2 `prefix_of` l1 ⌝.
  Proof.
    iIntros "[_ discards1] [_ discards2]".
    destruct (decide (length l1 ≤ length l2)).
    - iLeft.
      iApply bi.pure_mono; first apply lookup_prefix.
      iIntros (k lt).
      destruct (lookup_lt_is_Some_2 l1 k ltac:(lia)).
      destruct (lookup_lt_is_Some_2 l2 k ltac:(lia)).
      iDestruct (big_sepL_lookup _ _ k with "discards1") as "discard1"; first done.
      iDestruct (big_sepL_lookup _ _ k with "discards2") as "discard2"; first done.
      iDestruct (gen_own_valid_2 with "discard1 discard2") as %[_ ?]%gmap_view_frag_op_valid_L.
      by simplify_map_eq.
    - iRight.
      iApply bi.pure_mono; first apply lookup_prefix.
      iIntros (k lt).
      destruct (lookup_lt_is_Some_2 l1 k ltac:(lia)).
      destruct (lookup_lt_is_Some_2 l2 k ltac:(lia)).
      iDestruct (big_sepL_lookup _ _ k with "discards1") as "discard1"; first done.
      iDestruct (big_sepL_lookup _ _ k with "discards2") as "discard2"; first done.
      iDestruct (gen_own_valid_2 with "discard1 discard2") as %[_ ?]%gmap_view_frag_op_valid_L.
      by simplify_map_eq.
  Qed.

  Lemma list_token_strengthen {γ p} p':
    p ≤ p' →
    list_token γ p ==∗ list_token γ p' ∗ rely_self γ (excl_list_pred p').
  Proof.
    iIntros (?) "token".
    iMod (token_strengthen_promise_0_deps _ _ (excl_list_pred p') with "token") as "token".
    { rewrite /excl_list_pred.
      intros ? (p'' & ? & ->).
      eexists.
      split; last done.
      lia. }
    { exists (excl_list_trans p').
      split; first apply _.
      by eexists. }
    iDestruct (token_to_rely with "token") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "$".
    done.
  Qed.
End excl_list.
