From self.lang Require Import notation tactics.

(* These lemmas can probably be simplified with extra lemmas and/or automation. *)

Lemma prim_step_ref_no_fork (a : memory_access) (v : val) SV PV BV
  (σ1 : state nvm_lang) (g1 : global_state nvm_lang) (κ : list (language.observation nvm_lang)) 
  (e2 : language.expr nvm_lang) (σ2 : state nvm_lang) (g2 : global_state nvm_lang) 
  (efs : list (language.expr nvm_lang)) :
  prim_step (Alloc a v `at` (SV, PV, BV)) σ1 g1 κ e2 σ2 g2 efs → efs = [].
Proof.
    intros [Ki [??] [??] ? ? step].
    subst.
    simpl in *.
    induction Ki using rev_ind.
    { simpl in *. subst. inv_impure_thread_step; try done.
      rewrite list_fmap_singleton.
      subst.
      congruence. }
    move: H.
    rewrite fill_app.
    simpl.
    destruct x; try done.
    - simpl.
      rewrite /thread_fill_item.
      simpl.
      inversion 1.
      simpl in *.
      rewrite <- nvm_fill_fill in *.
      simpl in *.
      destruct Ki using rev_ind; try done.
      { simpl in *. subst. inv_impure_thread_step; try done. }
      simpl in *.
      rewrite fill_app in H2.
      simpl in *.
      destruct x; try done.
    - simpl.
      rewrite /thread_fill_item.
      simpl.
      inversion 1.
      simpl in *.
      rewrite <- nvm_fill_fill in *.
      simpl in *.
      destruct Ki using rev_ind; try done.
      { simpl in *. subst. inv_impure_thread_step; try done. }
      simpl in *.
      rewrite fill_app in H3.
      simpl in *.
      destruct x; try done.
Qed.

Lemma prim_step_load_acq_no_fork ℓ SV PV BV
  (σ1 : state nvm_lang) (g1 : global_state nvm_lang) (κ : list (language.observation nvm_lang)) 
  (e2 : language.expr nvm_lang) (σ2 : state nvm_lang) (g2 : global_state nvm_lang) 
  (efs : list (language.expr nvm_lang)) :
  prim_step (!{acq} #ℓ `at` (SV, PV, BV)) σ1 g1 κ e2 σ2 g2 efs → efs = [].
Proof.
    intros [Ki [??] [??] ? ? step].
    subst.
    simpl in *.
    induction Ki using rev_ind.
    { simpl in *. subst. inv_impure_thread_step; try done.
      rewrite list_fmap_singleton.
      subst.
      congruence. }
    move: H.
    rewrite fill_app.
    simpl.
    destruct x; try done.
    simpl.
    rewrite /thread_fill_item.
    simpl.
    inversion 1.
    simpl in *.
    rewrite -nvm_fill_fill in H2.
    simpl in *.
    destruct Ki using rev_ind; try done.
    { simpl in *. subst. inv_impure_thread_step; try done. }
    simpl in *.
    rewrite fill_app in H1.
    simpl in *.
    destruct x; try done.
Qed.

(* Try and simplify this with lemmas/automation. *)
Lemma prim_step_load_no_fork ℓ SV PV BV
  (σ1 : state nvm_lang) (g1 : global_state nvm_lang) (κ : list (language.observation nvm_lang)) 
  (e2 : language.expr nvm_lang) (σ2 : state nvm_lang) (g2 : global_state nvm_lang) 
  (efs : list (language.expr nvm_lang)) :
  prim_step (! #ℓ `at` (SV, PV, BV)) σ1 g1 κ e2 σ2 g2 efs → efs = [].
Proof.
    intros [Ki [??] [??] ? ? step].
    subst.
    simpl in *.
    induction Ki using rev_ind.
    { simpl in *. subst. inv_impure_thread_step; try done.
      rewrite list_fmap_singleton.
      subst.
      congruence. }
    move: H.
    rewrite fill_app.
    simpl.
    destruct x; try done.
    simpl.
    rewrite /thread_fill_item.
    simpl.
    inversion 1.
    simpl in *.
    rewrite -nvm_fill_fill in H2.
    simpl in *.
    destruct Ki using rev_ind; try done.
    { simpl in *. subst. inv_impure_thread_step; try done. }
    simpl in *.
    rewrite fill_app in H1.
    simpl in *.
    destruct x; try done.
Qed.

Lemma prim_step_store_rel_no_fork ℓ (v : val) SV PV BV
  (σ1 : state nvm_lang) (g1 : global_state nvm_lang) (κ : list (language.observation nvm_lang))
  (e2 : language.expr nvm_lang) (σ2 : state nvm_lang) (g2 : global_state nvm_lang)
  (efs : list (language.expr nvm_lang)) :
  prim_step (#ℓ <-{rel} v `at` (SV, PV, BV)) σ1 g1 κ e2 σ2 g2 efs → efs = [].
Proof.
  intros [Ki [??] [??] ? ? step].
  subst.
  simpl in *.
  induction Ki using rev_ind.
  { simpl in *. subst. inv_impure_thread_step; try done.
    rewrite list_fmap_singleton.
    subst.
    congruence. }
  move: H.
  rewrite fill_app.
  simpl.
  destruct x; try done.
  - simpl.
    rewrite /thread_fill_item.
    simpl.
    inversion 1.
    simpl in *.
    rewrite -nvm_fill_fill in H3.
    simpl in *.
    destruct Ki using rev_ind; try done.
    { simpl in *. subst. inv_impure_thread_step; try done. }
    simpl in *.
    rewrite fill_app in H1.
    simpl in *.
    destruct x; try done.
  - simpl.
    rewrite /thread_fill_item.
    simpl.
    inversion 1.
    simpl in *.
    rewrite -nvm_fill_fill in H3.
    simpl in *.
    destruct Ki using rev_ind; try done.
    { simpl in *. subst. inv_impure_thread_step; try done. }
    simpl in *.
    rewrite fill_app in H2.
    simpl in *.
    destruct x; try done.
Qed.


Lemma prim_step_store_no_fork ℓ (v : val) SV PV BV
  (σ1 : state nvm_lang) (g1 : global_state nvm_lang) (κ : list (language.observation nvm_lang))
  (e2 : language.expr nvm_lang) (σ2 : state nvm_lang) (g2 : global_state nvm_lang)
  (efs : list (language.expr nvm_lang)) :
  prim_step (#ℓ <- v `at` (SV, PV, BV)) σ1 g1 κ e2 σ2 g2 efs → efs = [].
Proof.
  intros [Ki [??] [??] ? ? step].
  subst.
  simpl in *.
  induction Ki using rev_ind.
  { simpl in *. subst. inv_impure_thread_step; try done.
    rewrite list_fmap_singleton.
    subst.
    congruence. }
  move: H.
  rewrite fill_app.
  simpl.
  destruct x; try done.
  - simpl.
    rewrite /thread_fill_item.
    simpl.
    inversion 1.
    simpl in *.
    rewrite -nvm_fill_fill in H3.
    simpl in *.
    destruct Ki using rev_ind; try done.
    { simpl in *. subst. inv_impure_thread_step; try done. }
    simpl in *.
    rewrite fill_app in H1.
    simpl in *.
    destruct x; try done.
  - simpl.
    rewrite /thread_fill_item.
    simpl.
    inversion 1.
    simpl in *.
    rewrite -nvm_fill_fill in H3.
    simpl in *.
    destruct Ki using rev_ind; try done.
    { simpl in *. subst. inv_impure_thread_step; try done. }
    simpl in *.
    rewrite fill_app in H2.
    simpl in *.
    destruct x; try done.
Qed.
