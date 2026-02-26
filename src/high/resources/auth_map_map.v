From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From self.lang Require Import lang.
From self Require Import extra.

From self.nextgen Require Import hvec nextgen_promises.
From self.base Require Import generational_resources.

Set Default Proof Using "Type*".

Definition auth_map_mapR (A: ofe) :=
  authR (gmapUR (loc * time) (agreeR A)).

Section auth_map_map.
  Context {A : ofe}.
  Notation auth_map_mapR_inG Σ Ω := (genInDepsG Σ Ω (auth_map_mapR A) [#crashed_atR]).
  Context `{!nvmBaseGS Σ Ω, inG: !auth_map_mapR_inG Σ Ω}.

  Variable (R: rel_over [#crashed_atR] (auth_map_mapR A)).
  Implicit Types (m : gmap loc (gmap time A)).

  Definition agree_uncurry_map m: gmap (loc * time) (agreeR A) := to_agree <$> (gmap_uncurry m).
  
  Definition auth_map_map_auth γ m: iProp Σ :=
    "own_auth" ∷ gen_own γ (● agree_uncurry_map m) ∗
    "#rely" ∷ rely (g := inG) γ [#crashed_at_name] R True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition auth_map_map_frag_singleton γ ℓ t a: iProp Σ :=
    "own_frag" ∷ gen_own γ (◯ {[ (ℓ, t) := to_agree a ]}) ∗
    "#rely" ∷ rely (g := inG) γ [#crashed_at_name] R True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  (* TODO: allocation lemma *)
  (* Lemma auth_map_map_alloc m : *)
  (*   ⊢ |==> ∃ γ, auth_map_map_auth γ m ∗ auth_map_map_frag γ m. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma auth_map_map_lookup `{!LeibnizEquiv A} γ m ℓ t h a :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ m ∗ auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (mLook hLook) "(N & #$ & #$)".
    rewrite /auth_map_map_auth /auth_map_map_frag_singleton. setoid_rewrite <- own_op.
    iApply (gen_own_update with "N").
    apply: auth_update_dfrac_alloc.
    eapply singleton_included_look.
    { rewrite /agree_uncurry_map lookup_fmap lookup_gmap_uncurry mLook /= hLook. reflexivity. }
    done.
  Qed.

  Lemma insert_gmap_uncurry_None k1 k2 v m:
    m !! k1 = None ->
    gmap_uncurry (<[k1:={[k2 := v]}]> m) = <[ (k1, k2) := v ]> (gmap_uncurry m).
  Proof.
    intros look.
    apply map_eq.
    intros [ℓ t].
    destruct (decide (ℓ = k1)) as [ <- | ]; destruct (decide (t = k2)) as [ <- |  ];
      rewrite lookup_gmap_uncurry ?lookup_insert /=.
    - rewrite lookup_singleton //.
    - rewrite ?lookup_insert_ne; try congruence.
      rewrite lookup_gmap_uncurry look //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_gmap_uncurry //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_gmap_uncurry //.
  Qed.

  Lemma insert_gmap_uncurry_Some k1 k2 v m h:
    m !! k1 = Some h ->
    gmap_uncurry (<[k1:=<[k2 := v]> h]> m) = <[ (k1, k2) := v ]> (gmap_uncurry m).
  Proof.
    intros look.
    apply map_eq.
    intros [ℓ t].
    destruct (decide (ℓ = k1)) as [ <- | ]; destruct (decide (t = k2)) as [ <- |  ];
      rewrite lookup_gmap_uncurry ?lookup_insert /=.
    - rewrite lookup_insert //.
    - rewrite ?lookup_insert_ne; try congruence.
      rewrite lookup_gmap_uncurry look //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_gmap_uncurry //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_gmap_uncurry //.
  Qed.

  Lemma auth_map_map_insert_top `{!LeibnizEquiv A} γ m ℓ t a :
    m !! ℓ = None →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ (<[ℓ:= {[ t := a ]} ]> m) ∗
    auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (look).
    iIntros "(auth & #$ & #$)".
    rewrite -gen_own_op.
    iApply (gen_own_update with "auth").
    apply auth_update_alloc.
    rewrite /agree_uncurry_map.
    rewrite insert_gmap_uncurry_None; last done.
    rewrite fmap_insert.
    apply alloc_local_update.
    - rewrite lookup_fmap lookup_gmap_uncurry look. done.
    - done.
  Qed.

  (* NOTE: The requirement on leibniz equiv may not be strictly necessary, but
  it is convenient right now. *)
  Lemma auth_map_map_insert `{!LeibnizEquiv A} γ m ℓ t h a :
    m !! ℓ = Some h →
    h !! t = None →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ (<[ℓ:=<[t:=a]> h]> m) ∗
    auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (look1 look2) "(auth & #$ & #$)".
    rewrite -gen_own_op.
    iApply (gen_own_update with "auth").
    apply auth_update_alloc.
    rewrite /agree_uncurry_map.
    rewrite insert_gmap_uncurry_Some; last done.
    rewrite fmap_insert.
    apply alloc_local_update.
    - rewrite lookup_fmap lookup_gmap_uncurry look1 /= look2. done.
    - done.
  Qed.

  Lemma auth_map_map_auth_frag `{!OfeDiscrete A} `{!LeibnizEquiv A} γ m ℓ t a :
    auth_map_map_auth γ m -∗
    auth_map_map_frag_singleton γ ℓ t a -∗
    ⌜ ∃ h, m !! ℓ = Some h ∧ h !! t = Some a ⌝.
  Proof.
    iIntros "[O _] [F _]".
    iDestruct (gen_own_valid with "O") as %val.
    rewrite auth_auth_valid in val.
    iDestruct (gen_own_valid_2 with "O F") as %V.
    iPureIntro.
    apply auth_both_dfrac_valid_discrete in V as (_ & incl & _).
    apply singleton_included_l in incl as (a' & look & sub%Some_included_total).
    rewrite /agree_uncurry_map lookup_fmap lookup_gmap_uncurry in look.
    rewrite ?Some_included_total in sub.
    destruct (m !! ℓ) as [h | ]; simpl in look.
    - exists h.
      split; first done.
      simpl in *.
      apply fmap_Some_equiv in look as [v [look' equiv]].
      rewrite equiv to_agree_included in sub.
      apply leibniz_equiv in sub.
      congruence.
    - simpl in look.
      symmetry in look.
      apply None_equiv_eq in look.
      congruence.
  Qed.

  (* Lemma auth_map_map_frag_lookup `{!LeibnizEquiv A} γ m ℓ h : *)
  (*   m !! ℓ = Some h → *)
  (*   auth_map_map_frag γ m -∗ *)
  (*   auth_map_map_frag γ {[ ℓ := h ]}. *)
  (* Proof. *)
  (*   iIntros (mLook). *)
  (*   rewrite /auth_map_map_frag. *)
  (*   rewrite /auth_map_map_frag_singleton. *)
  (*   rewrite /auth_map_map_frag. *)
  (*   iIntros "(F & $ & $)". *)
  (*   iApply (gen_own_mono with "F"). *)
  (*   simpl. *)
  (*   apply auth_frag_mono. *)
  (*   rewrite /fmap_fmap_to_agree. *)
  (*   rewrite map_fmap_singleton. *)
  (*   apply singleton_included_l. *)
  (*   eexists _. *)
  (*   split. { rewrite lookup_fmap. rewrite mLook. simpl. reflexivity. } *)
  (*   done. *)
  (* Qed. *)

  (* Lemma auth_map_map_frag_lookup_singleton `{!LeibnizEquiv A} γ m ℓ h t a : *)
  (*   m !! ℓ = Some h → *)
  (*   h !! t = Some a → *)
  (*   auth_map_map_frag γ m -∗ *)
  (*   auth_map_map_frag_singleton γ ℓ t a. *)
  (* Proof. *)
  (*   iIntros (mLook hLook) "(F & #$ & #$)". *)
  (*   rewrite /auth_map_map_frag. *)
  (*   rewrite /auth_map_map_frag_singleton. *)
  (*   rewrite /auth_map_map_frag. *)
  (*   iApply (gen_own_mono with "F"). *)
  (*   simpl. *)
  (*   apply auth_frag_mono. *)
  (*   rewrite /fmap_fmap_to_agree. *)
  (*   rewrite map_fmap_singleton. *)
  (*   apply singleton_included_l. *)
  (*   eexists _. *)
  (*   split. { rewrite lookup_fmap. rewrite mLook. simpl. reflexivity. } *)
  (*   apply Some_included_total. *)
  (*   apply to_agree_fmap. *)
  (*   apply map_singleton_subseteq_l. *)
  (*   done. *)
  (* Qed. *)

  Lemma auth_map_map_lookup_agree `{!OfeDiscrete A} `{!LeibnizEquiv A} γ m ℓ h t a a' :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_auth γ m -∗
    auth_map_map_frag_singleton γ ℓ t a' -∗
    ⌜ a = a' ⌝.
  Proof.
    iIntros (mLook hLook) "[O _] [F _]".
    iDestruct (gen_own_valid_2 with "O F") as %[(? & look & incl)%singleton_included_l _]%auth_both_valid_discrete.
    rewrite /agree_uncurry_map lookup_fmap lookup_gmap_uncurry in look.
    rewrite ?Some_included_total in incl.
    rewrite mLook /= hLook in look.
    apply fmap_Some_equiv in look as [v [look' equiv]].
    rewrite equiv to_agree_included in incl.
    apply leibniz_equiv in incl.
    iPureIntro. congruence.
  Qed.
End auth_map_map.
Notation auth_map_mapR_inG A Σ Ω := (genInDepsG Σ Ω (auth_map_mapR A) [#crashed_atR]).

Section history.
  Implicit Types (histories: gmap loc (gmap time message)).
  Context `{!nvmBaseGS Σ Ω, inG: !auth_map_mapR_inG (leibnizO message) Σ Ω}.
  
  Definition drop_above_map_uncurry (OCV: view.view):
    (auth_map_mapR (leibnizO message) → auth_map_mapR (leibnizO message)) :=
    fmap_auth (map_imap (λ '(ℓ, t) a, if decide (ℓ ∈ dom OCV ∧ t ≤ OCV !!0 ℓ) then Some $ agree_map discard_msg_views a else None)).

  Definition histories_rel: rel_over [#crashed_atR] (auth_map_mapR (leibnizO message)) :=
    λ tC tH, ∃ OCV,
      tC = crashed_at_trans OCV ∧
      tH = drop_above_map_uncurry OCV.

  #[global] Instance own_all_phys_histories_nextgen γ histories:
    IntoNextgen
      (auth_map_map_auth histories_rel γ histories)
      (∀ OCV, crashed_at_offset OCV -∗
              auth_map_map_auth histories_rel γ (drop_above_map OCV histories)).
  Proof.
    rewrite /IntoNextgen.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [% _] & pickedH & pickedC')]".
    iDestruct "own_auth" as (tH') "[#pickedH' own_auth]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite /auth_map_map_auth.
    iFrame "rely".
    iSplit; last by iExists _, _.
    iApply (gen_own_mono with "own_auth").
    rewrite /drop_above_map_uncurry fmap_auth_auth.
    rewrite auth_auth_included.
    rewrite map_equiv_iff.
    intros [ℓ t].
    rewrite /agree_uncurry_map /drop_above_map map_lookup_imap ?lookup_fmap ?lookup_gmap_uncurry /= map_lookup_imap /=.
    destruct (histories !! ℓ) as [h | ] eqn:Heq1; rewrite ?Heq1 /=; last done.
    rewrite /drop_above_hist.
    destruct (OCV !! ℓ) as [[tC] | ] eqn:Heqn2; rewrite ?Heqn2 /=.
    - rewrite lookup_fmap.
      destruct (decide (t ≤ tC)).
      + rewrite map_extra.drop_above_lookup_le; last done.
        destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
        rewrite decide_True ?agree_map_to_agree //.
        split; first by eapply elem_of_dom_2.
        rewrite /lookup_zero Heqn2 /= //.
      + rewrite map_extra.drop_above_lookup_gt; last lia.
        destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
        rewrite decide_False //.
        rewrite /lookup_zero Heqn2 /=.
        lia.
    - destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
      rewrite decide_False //.
      rewrite -not_elem_of_dom in Heqn2.
      set_solver.
  Qed.
End history.
