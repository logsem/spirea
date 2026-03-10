From Equations Require Import Equations.
From iris.algebra Require Import gmap_view.
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

(* The exclusive ghost resource: [gset_disj nat]. *)
Definition excl_opsR : cmra := gmap_viewR nat unitO.
Class excl_opsG (Σ: gFunctors) (Ω: gGenCmras Σ) := {
  excl_ops_inG :: genInDepsG Σ Ω excl_opsR [#];
}.
Section Ghosts.
  Context `{!excl_opsG Σ Ω}.

  Definition drop_op (p: nat) n (_: unit): option _ :=
    if decide (n < p) then Some () else None.

  #[global] Instance drop_op_maptrans p: MapTrans (drop_op p).
  Proof.
    split; last solve_proper.
    intros. done.
  Qed.
  
  Definition excl_ops_trans (p: nat): excl_opsR → excl_opsR :=
    map_entry_lift_gmap_view (drop_op p).

  Definition excl_ops_pred (p: nat): pred_over excl_opsR :=
    λ t, ∃ p', p ≤ p' ∧ t = excl_ops_trans p'.
  
  Definition ops_auth γ (n: nat): iProp Σ :=
    gen_own γ (gmap_view_auth (DfracOwn 1) (map_seq 0 (repeat () n))).

  Definition ops_frag γ (n: nat): iProp Σ :=
    "frag" ∷ gen_own γ (gmap_view_frag n (DfracOwn 1) ()) ∗
    "#frag_rely_self" ∷ ∃ p', ⌜ n < p' ⌝ ∗ rely_self γ (excl_ops_pred p').

  Definition ops_token γ (p: nat) :=
    token γ [#] (excl_ops_pred p) (excl_ops_pred p).
  
  Lemma excl_ops_alloc:
    ⊢ |==> ∃ γ, ops_auth γ 0 ∗ ops_token γ 0.
  Proof.
    iMod (own_gen_alloc (DS := [#]) (gmap_view_auth (DfracOwn 1) ∅) [#] [##] with "[]") as (γ) "(HO & tok)".
    { by apply gmap_view_auth_valid. }
    { iIntros (i'). inversion i'. }
    iMod (token_strengthen_promise (DS := [#])
            _ [#] [##] _ (excl_ops_pred 0) _ (excl_ops_pred 0) with "[] tok")
      as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      exists (excl_ops_trans 0).
      split; first apply _.
      eexists.
      done. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iDestruct (token_to_rely with "tok") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "?".
    iExists _.
    iFrame "∗#".
  Qed.
  
  #[global] Instance ops_frag_into_nextgen {γ} n:
    IntoNextgen
      (ops_frag γ n)
      (ops_frag γ n).
  Proof.
    rewrite /IntoNextgen /ops_frag.
    iNamed 1.
    iModIntro.
    iDestruct "frag" as (t) "[picked_in frag]".
    iDestruct "frag_rely_self" as (p Hlt) "[rely_self (%t' & (%p' & %Hle & %H) & picked_in')]".
    iPickedInAgree "picked_in picked_in'".
    subst t.
    iSplitL "frag".
    { iApply (gen_own_proper with "frag").
      rewrite /excl_ops_trans.
      unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
      unfold gmap_view_frag, view_frag.
      f_equiv.
      rewrite -{2}insert_empty.
      erewrite map_imap_insert_Some;
        first rewrite map_imap_empty insert_empty //.
      rewrite agree_option_map_to_agree /drop_op decide_True //.
      lia. }
    iExists p.
    by iFrame "#".
  Qed.

  Lemma map_seq_grow (n: nat):
    (map_seq 0 (repeat () (S n)): gmap nat unit) = <[ n := () ]> (map_seq 0 (repeat () n)).
  Proof.
    simpl repeat.
    rewrite repeat_cons map_seq_snoc.
    f_equiv.
    rewrite repeat_length //.
  Qed.
  
  Lemma ops_auth_grow {γ n}:
    ops_auth γ n ==∗ ops_auth γ (S n) ∗ gen_own γ (gmap_view_frag n (DfracOwn 1) ()).
  Proof.
    iIntros "ops_auth".
    iMod (gen_own_update with "ops_auth") as "[$ $]"; last done.
    rewrite map_seq_grow.
    apply gmap_view_alloc; last done.
    rewrite lookup_map_seq_0 lookup_ge_None repeat_length //.
  Qed.
    
  Lemma ops_auth_ops_frag_false {γ} n:
    ops_auth γ n -∗
    ops_frag γ n -∗
    False.
  Proof.
    iIntros "auth". iNamed 1.
    iDestruct (gen_own_valid_2 with "auth frag") as %[_ contra]%gmap_view_both_valid_L.
    rewrite lookup_map_seq_0 in contra.
    apply lookup_lt_Some in contra.
    rewrite repeat_length in contra.
    lia.
  Qed.

  Lemma ops_token_strengthen {γ p} p':
    p ≤ p' →
    ops_token γ p ==∗ ops_token γ p' ∗ rely_self γ (excl_ops_pred p').
  Proof.
    iIntros (?) "token".
    iMod (token_strengthen_promise_0_deps _ _ (excl_ops_pred p') with "token") as "token".
    { rewrite /excl_ops_pred.
      intros ? (p'' & ? & ->).
      eexists.
      split; last done.
      lia. }
    { exists (excl_ops_trans p').
      split; first apply _.
      by eexists. }
    iDestruct (token_to_rely with "token") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "$".
    done.
  Qed.

  Lemma map_entry_lift_gmap_view_auth dq (m: gmap nat unit) map_entry :
    (map_entry_lift_gmap_view map_entry (gmap_view_auth dq m)) =
    (gmap_view_auth dq (map_imap map_entry m)).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    rewrite agree_map_to_agree. done.
  Qed.
End Ghosts.
Opaque ops_frag.
