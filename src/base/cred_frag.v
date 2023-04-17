From iris.proofmode Require Import tactics.
From iris.algebra Require Import lib.frac_auth auth numbers gmap excl.
From iris.base_logic.lib Require Import own.
From Perennial.base_logic.lib Require Import frac_coPset.

Record cr_names := {
  credit_name : gname;
  coPset_name : gname;
}.

Class credit_preG (Σ: gFunctors) := {
  credit_preG_inG :> inG Σ (authR natUR);
  frac_coPset_preG_inG :> inG Σ (frac_coPsetR);
}.

Class creditGS (Σ: gFunctors) := {
  credit_inG :> inG Σ (authR natUR);
  frac_coPset_inG :> inG Σ (frac_coPsetR);
  credit_cr_names : cr_names;
}.

Definition creditGS_update (Σ: gFunctors) (hC: creditGS Σ) (names: cr_names) :=
  {| credit_inG := credit_inG; frac_coPset_inG := frac_coPset_inG; credit_cr_names := names |}.

Definition creditGS_update_pre (Σ: gFunctors) (hT: credit_preG Σ) (names: cr_names) :=
  {| credit_inG := credit_preG_inG; frac_coPset_inG := frac_coPset_preG_inG; credit_cr_names := names |}.

Definition creditΣ : gFunctors :=
  #[GFunctor (authR natUR);
      GFunctor frac_coPsetR].

Global Instance subG_creditG {Σ} : subG creditΣ Σ → credit_preG Σ.
Proof. solve_inG. Qed.

Section creditGS_defs.
Context `{creditGS Σ}.

Definition cred_frag (n : nat) : iProp Σ := (own (credit_name (credit_cr_names)) (◯ n)).

Definition cred_auth (ns : nat) : iProp Σ :=
  (own (credit_name (credit_cr_names)) (● ns)).

Definition pinv_tok_inf q E := ownfCP_inf (coPset_name (credit_cr_names)) q E.
Definition pinv_tok q E := ownfCP (coPset_name (credit_cr_names)) q E.

Lemma cred_auth_frag_incr (ns n: nat) :
  cred_auth ns ∗ cred_frag n ==∗
  cred_auth (S ns) ∗ cred_frag (S n).
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as "Hγf".
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply auth_update, (nat_local_update _ _ (S ns) (S n)); lia. }
  iFrame. eauto.
Qed.

Lemma cred_auth_frag_incr_k (ns n k: nat) :
  cred_auth ns ∗ cred_frag n ==∗
  cred_auth (ns + k) ∗ cred_frag (n + k).
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as "Hγf".
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply auth_update, (nat_local_update _ _ (ns + k) (n + k)); lia. }
  iFrame. eauto.
Qed.

Lemma cred_auth_frag_decr (ns n: nat) :
  cred_auth ns ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ cred_auth ns' ∗ cred_frag n.
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as "Hγf".
  iDestruct (own_valid_2 with "Hγ Hγf") as % Hval.
  apply auth_both_valid_discrete in Hval as (Hincl%nat_included&_).
  destruct ns as [| ns']; first lia.
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply auth_update, (nat_local_update _ _ ns' n); lia. }
  iExists _. iFrame. iModIntro. eauto.
Qed.

Lemma cred_auth_frag_invert (ns n: nat) :
  cred_auth ns ∗ cred_frag n -∗ ∃ ns', ⌜ (ns = n + ns')%nat ⌝.
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct (own_valid_2 with "Hγ Hγf") as % Hval.
  apply auth_both_valid_discrete in Hval as (Hincl%nat_included&_).
  iExists (ns - n)%nat. iFrame. iPureIntro; lia.
Qed.

Definition cred_interp ns : iProp Σ :=
  cred_auth ns ∗ cred_frag 0.

Lemma cred_frag_split ns1 ns2 :
  cred_frag (ns1 + ns2) -∗ cred_frag ns1 ∗ cred_frag ns2.
Proof.
  iIntros "H".
  rewrite /cred_frag auth_frag_op.
  iDestruct "H" as "(H1&H2)".
  iFrame.
Qed.

Lemma cred_frag_join ns1 ns2 :
  cred_frag ns1 ∗ cred_frag ns2 -∗ cred_frag (ns1 + ns2).
Proof.
  iIntros "(H1&H2)".
  iCombine "H1 H2" as "H".
  iFrame.
Qed.

Lemma cred_interp_incr ns :
  cred_interp ns ==∗ cred_interp (S ns) ∗ cred_frag 1.
Proof.
  iIntros "H".
  iMod (cred_auth_frag_incr with "H") as "(?&H)".
  iEval (replace 1%nat with (1 + 0)%nat by lia) in "H".
  iDestruct (cred_frag_split with "H") as "($&$)".
  eauto.
Qed.

Lemma cred_interp_incr_k ns k :
  cred_interp ns ==∗ cred_interp (ns + k) ∗ cred_frag k.
Proof.
  iIntros "H".
  iMod (cred_auth_frag_incr_k _ _ k with "H") as "(?&H)".
  iDestruct (cred_frag_split with "H") as "($&$)".
  eauto.
Qed.

Lemma cred_interp_decr ns n :
  cred_interp ns ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ cred_interp ns' ∗ cred_frag n.
Proof.
  iIntros "((H&?)&Hfrag)".
  iMod (cred_auth_frag_decr with "[$H $Hfrag]") as (ns' Heq) "(?&H)". subst.
  iExists ns'. iModIntro. iSplit; eauto.
  iFrame.
Qed.

Lemma cred_interp_invert ns k :
  cred_interp ns ∗ cred_frag k -∗ ∃ ns', ⌜ ns = (k + ns')%nat ⌝.
Proof.
  iIntros "((H&?)&Hfrag)".
  iDestruct (cred_auth_frag_invert with "[$H $Hfrag]") as %[ns' Heq]; eauto.
Qed.

End creditGS_defs.

Lemma credit_name_init `{hC: credit_preG Σ} k :
  ⊢ |==> ∃ name : cr_names, let _ := creditGS_update_pre _ _ name in
                           cred_interp k ∗ cred_frag k ∗ pinv_tok 1 ∅.
Proof.
  iMod (own_alloc (● k ⋅ ◯ k)) as (γ) "[H1 H2]".
  { apply auth_both_valid_discrete; split; eauto. econstructor. }
  iMod (ownfCP_init_empty γ) as "Hemp".
  iModIntro. iExists {| credit_name := γ; coPset_name := γ |}.
  rewrite -{2}(Nat.add_0_l k).
  iDestruct (cred_frag_split with "[H2]") as "($&$)".
  { rewrite /cred_frag//=. }
  iFrame.
Qed.
