From Equations Require Import Equations.
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

  Notation map_uncurry := (map_uncurry (M1 := gmap loc) (M2 := gmap time) (M12 := gmap (loc * time))).
  
  Definition agree_uncurry_map m: gmap (loc * time) (agreeR A) := to_agree <$> (map_uncurry m).
  
  Definition auth_map_map_auth γ m: iProp Σ :=
    "own_auth" ∷ gen_own γ (● agree_uncurry_map m) ∗
    "own_frag" ∷ gen_own γ (◯ agree_uncurry_map m) ∗
    "#rely" ∷ rely (g := inG) γ [#crashed_at_name] R True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

  Definition auth_map_map_frag_singleton γ ℓ t a: iProp Σ :=
    "own_frag" ∷ gen_own γ (◯ {[ (ℓ, t) := to_agree a ]}) ∗
    "#rely" ∷ rely (g := inG) γ [#crashed_at_name] R True_pred ∗
    "#crashed" ∷ ∃ OCV, crashed_at_offset OCV.

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
    { rewrite /agree_uncurry_map lookup_fmap lookup_map_uncurry mLook /= hLook. reflexivity. }
    done.
  Qed.

  Lemma insert_map_uncurry_None k1 k2 v m:
    m !! k1 = None ->
    map_uncurry (<[k1:={[k2 := v]}]> m) = <[ (k1, k2) := v ]> (map_uncurry m).
  Proof.
    intros look.
    apply map_eq.
    intros [ℓ t].
    destruct (decide (ℓ = k1)) as [ <- | ]; destruct (decide (t = k2)) as [ <- |  ];
      rewrite lookup_map_uncurry ?lookup_insert_eq /=.
    - rewrite lookup_singleton_eq //.
    - rewrite ?lookup_insert_ne; try congruence.
      rewrite lookup_map_uncurry look //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_map_uncurry //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_map_uncurry //.
  Qed.

  Lemma insert_map_uncurry_Some k1 k2 v m h:
    m !! k1 = Some h ->
    map_uncurry (<[k1:=<[k2 := v]> h]> m) = <[ (k1, k2) := v ]> (map_uncurry m).
  Proof.
    intros look.
    apply map_eq.
    intros [ℓ t].
    destruct (decide (ℓ = k1)) as [ <- | ]; destruct (decide (t = k2)) as [ <- |  ];
      rewrite lookup_map_uncurry ?lookup_insert_eq /=.
    - rewrite lookup_insert_eq //.
    - rewrite ?lookup_insert_ne; try congruence.
      rewrite lookup_map_uncurry look //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_map_uncurry //.
    - rewrite ?lookup_insert_ne /=; try congruence.
      rewrite lookup_map_uncurry //.
  Qed.

  Lemma auth_map_map_insert_top `{!LeibnizEquiv A} γ m ℓ t a :
    m !! ℓ = None →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ (<[ℓ:= {[ t := a ]} ]> m) ∗
    auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (look).
    iIntros "(auth & #frag & #$ & #$)".
    rewrite /agree_uncurry_map insert_map_uncurry_None // fmap_insert.
    iMod (gen_own_update with "auth") as "[$ frag']".
    { apply auth_update_alloc.
      apply alloc_local_update.
      - rewrite lookup_fmap lookup_map_uncurry look. done.
      - done. }
    rewrite insert_empty insert_singleton_op ?auth_frag_op ?gen_own_op.
    - iDestruct "frag'" as "#$". by iFrame "#".
    - rewrite lookup_fmap lookup_map_uncurry look //.
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
    iIntros (look1 look2) "(auth & #frag & #$ & #$)".
    rewrite /agree_uncurry_map insert_map_uncurry_Some // fmap_insert.
    iMod (gen_own_update with "auth") as "[$ frag']".
    { apply auth_update_alloc.
      apply alloc_local_update.
      - rewrite lookup_fmap lookup_map_uncurry look1 /= look2. done.
      - done. }
    rewrite insert_empty insert_singleton_op ?auth_frag_op ?gen_own_op.
    - iDestruct "frag'" as "#$". by iFrame "#".
    - rewrite lookup_fmap lookup_map_uncurry look1 /= look2 //.
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
    rewrite /agree_uncurry_map lookup_fmap lookup_map_uncurry in look.
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

  Lemma auth_map_map_auth_lookup_frag `{!LeibnizEquiv A} γ m ℓ h t a :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_auth γ m -∗
    auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    intros mLook hLook.
    iNamed 1.
    iFrame "rely crashed".
    iApply (gen_own_mono with "own_frag").
    apply auth_frag_mono.
    apply (singleton_included_look _ _ _ (to_agree a)); last done.
    rewrite /agree_uncurry_map lookup_fmap lookup_map_uncurry mLook /= hLook //.
  Qed.

  Lemma auth_map_map_lookup_agree `{!OfeDiscrete A} `{!LeibnizEquiv A} γ m ℓ h t a a' :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_auth γ m -∗
    auth_map_map_frag_singleton γ ℓ t a' -∗
    ⌜ a = a' ⌝.
  Proof.
    iIntros (mLook hLook) "[O _] [F _]".
    iDestruct (gen_own_valid_2 with "O F") as %[(? & look & incl)%singleton_included_l _]%auth_both_valid_discrete.
    rewrite /agree_uncurry_map lookup_fmap lookup_map_uncurry in look.
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

  #[global] Instance drop_above_map_uncurry_cmra_morphism OCV:
    CmraMorphism (drop_above_map_uncurry OCV).
  Proof.
    rewrite /drop_above_map_uncurry.
    apply @fmap_auth_gentrans.
    constructor.
    - apply gmap_view_transformation.gmap_map_imap_ne. intros [] ?. solve_proper.
    - intros n m Hm [ℓ t].
      rewrite map_lookup_imap.
      destruct (m !! (ℓ, t)) eqn:Heq; rewrite Heq /= //.
      destruct (decide _); last done.
      apply Some_validN, cmra_morphism_validN; first apply _.
      specialize (Hm (ℓ, t)).
      rewrite Heq // in Hm.
    - intros m.
      rewrite !cmra_pcore_core /=.
      f_equiv.
      intros [ℓ t].
      rewrite map_lookup_imap /= ?lookup_core map_lookup_imap.
      destruct (m !! (ℓ, t)) eqn:Heq; rewrite Heq /= //.
      destruct (decide _); done.
    - intros m1 m2 [ℓ t].
      rewrite lookup_op ?map_lookup_imap lookup_op.
      destruct (m1 !! (ℓ, t)) eqn:Heq1;
        destruct (m2 !! (ℓ, t)) eqn:Heq2;
        rewrite Heq1 Heq2 /= //;
          destruct (decide _); try done.
      rewrite -Some_op cmra_morphism_op //.
  Qed.

  Definition histories_rel: rel_over [#crashed_atR] (auth_map_mapR (leibnizO message)) :=
    λ tC tH, ∃ OCV,
      tC = crashed_at_trans OCV ∧
      tH = drop_above_map_uncurry OCV.
  
  Lemma auth_map_map_alloc OCV OPV :
    crashed_at_offset OCV -∗
    rely_self crashed_at_name (crashed_at_pred OPV) ==∗
    ∃ γ, auth_map_map_auth histories_rel γ ∅.
  Proof.
    iIntros "#crashed_at_offset #rely_self".
    iMod (own_gen_alloc
                  (DS := [#crashed_atR])
                  (● agree_uncurry_map ∅ ⋅ ◯ agree_uncurry_map ∅)
                  [#crashed_at_name]
                  [##_] with "[]") as (γ) "[[$ $] tok]".
    { by apply auth_both_valid. }
    { iIntros (i').
      dependent elimination i' as [0%fin].
      iAssumption. }
    iMod (token_strengthen_promise
            (DS := [#crashed_atR])
            _ [#_] [##_] _ histories_rel _ True_pred
           with "[] tok") as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    2: {
      iIntros (i').
      dependent elimination i' as [0%fin].
      iApply "rely_self". }
    (* TODO: this subgoal requires me to prove that for any transformer picked for
     * [crashed_atR], there exists a transformer for the map that satisfy [R].
     * this can only be proven given specific [R]. I should move this lemma around. *)
    { intros ts crashedPred.
      dependent elimination ts as [hcons tC hnil].
      destruct crashedPred as ((OCV2 & ? & ->) & _).
      exists (drop_above_map_uncurry OCV2).
      split; first apply _.
      simpl.
      exists OCV2. done. }
    iDestruct (token_to_rely with "tok") as "#rely".
    iModIntro.
    iFrame "#".
  Qed.
  
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
    iDestruct "own_frag" as (?) "[#pickedH'' own_frag]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    iPickedInAgree "pickedH pickedH''".
    destruct H as (OCV'' & -> & ->).
    iIntros (?) "offset".
    simpl.
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iNamed "offset".
      iDestruct (crashed_at_both_agree with "offset crashed") as %[-> ->].
      done. }
    rewrite /auth_map_map_auth.
    iFrame "rely".
    iFrame.
    iDestruct (gen_own_op_2 with "own_auth own_frag") as "own_auth".
    rewrite -gen_own_op.
    iApply (gen_own_mono with "own_auth").
    rewrite /drop_above_map_uncurry fmap_auth_auth fmap_auth_frag map_imap_empty /=.
    rewrite auth_both_included.
    split.
    - rewrite map_equiv_iff.
      intros [ℓ t].
      rewrite /agree_uncurry_map /drop_above_map map_lookup_imap ?lookup_fmap ?lookup_map_uncurry /= map_lookup_imap /=.
      destruct (histories !! ℓ) as [h | ] eqn:Heq1; rewrite ?Heq1 /=; last done.
      rewrite /drop_above_hist.
      destruct (OCV !! ℓ) as [[tC] | ] eqn:Heqn2; rewrite ?Heqn2 /=.
      + rewrite lookup_fmap.
        destruct (decide (t ≤ tC)).
        * rewrite map_extra.drop_above_lookup_le; last done.
          destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
          rewrite decide_True ?agree_map_to_agree //.
          split; first by eapply elem_of_dom_2.
          rewrite /lookup_zero Heqn2 /= //.
        * rewrite map_extra.drop_above_lookup_gt; last lia.
          destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
          rewrite decide_False //.
          rewrite /lookup_zero Heqn2 /=.
          lia.
      + destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
        rewrite decide_False //.
        rewrite -not_elem_of_dom in Heqn2.
        set_solver.
    - rewrite lookup_included.
      intros [ℓ t].
      rewrite /agree_uncurry_map /drop_above_map map_lookup_imap ?lookup_fmap ?lookup_map_uncurry /= map_lookup_imap /=.
      destruct (histories !! ℓ) as [h | ] eqn:Heq1; rewrite ?Heq1 /=; last done.
      rewrite /drop_above_hist.
      destruct (OCV !! ℓ) as [[tC] | ] eqn:Heqn2; rewrite ?Heqn2 /=.
      + rewrite lookup_fmap.
        destruct (decide (t ≤ tC)).
        * rewrite map_extra.drop_above_lookup_le; last done.
          destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
          rewrite decide_True ?agree_map_to_agree //.
          split; first by eapply elem_of_dom_2.
          rewrite /lookup_zero Heqn2 /= //.
        * rewrite map_extra.drop_above_lookup_gt; last lia.
          destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
          rewrite decide_False //.
          rewrite /lookup_zero Heqn2 /=.
          lia.
      + destruct (h !! t) eqn:Heqn3; rewrite ?Heqn3 /=; last done.
        rewrite decide_False //.
        rewrite -not_elem_of_dom in Heqn2.
        set_solver.
  Qed.

  #[global] Instance auth_map_map_frag_singleton_nextgen γ ℓ t msg:
    IntoNextgen
      (auth_map_map_frag_singleton histories_rel γ ℓ t msg)
      (∀ OCV, ⌜ ℓ ∈ dom OCV ∧ t ≤ OCV !!0 ℓ ⌝ -∗
              crashed_at_offset OCV -∗
              auth_map_map_frag_singleton histories_rel γ ℓ t (discard_msg_views msg)).
  Proof.
    rewrite /IntoNextgen /auth_map_map_frag_singleton.
    iNamed 1.
    iModIntro.
    iDestruct "crashed" as (OV OCV' tC) "[pickedC crashed]".
    iDestruct "rely" as "[rely (%tH & %tC' & [%Hrel _] & pickedH & pickedC')]".
    iDestruct "own_frag" as (tH') "[#pickedH' own_frag]".
    iPickedInAgree "pickedC pickedC'".
    iPickedInAgree "pickedH pickedH'".
    destruct Hrel as (OCV'' & -> & ->).
    iIntros (OCV) "%Hsurv offset".
    iAssert ⌜ OCV = OCV'' ⌝%I as %<-.
    { iDestruct "offset" as (?) "offsetBoth".
      iDestruct (crashed_at_both_agree with "offsetBoth crashed") as %[-> ->].
      done. }
    rewrite /drop_above_map_uncurry fmap_auth_frag -insert_empty map_imap_insert map_imap_empty /=.
    rewrite decide_True // insert_empty agree_map_to_agree.
    iFrame "∗#".
  Qed.
End history.
