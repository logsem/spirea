From Equations Require Import Equations.
From stdpp Require Import pmap list.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.algebra Require Import gmap gmap_view view.

From nextgen Require Import utils nextgen_basic gen_trans cmra_morphism_extra.

(** [MapTrans] defines a valid map transformation to be applied on a
    gmap resource algebra *)
Class MapTrans {L : Type} {V : ofe} (map_entry : L → V → option V) :=
{
  (* The following condition states that only locations can determine
  resource discard, so that all points-to's of a location get
  discarded reguardless of fraction or value *)
  map_trans_frag_discard_all: forall (l : L) (v1 : V),
    map_entry l v1 = None -> forall (v2 : V), map_entry l v2 = None;
    
  map_trans_frag_ne : forall k, NonExpansive (map_entry k);
}.

Existing Instance map_trans_frag_ne.

Record ghost_mapGS (L V : Type) (Σ : gFunctors) (EqDecision0 : EqDecision L) (H : Countable L) : Set := GhostMapGS
  { ghost_map_inG : inG Σ (gmap_viewR L (agreeR (leibnizO V)));  ghost_name : gname }.

Fixpoint option_list_collapse_list {A : Type} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l' => a :: option_list_collapse_list l'
  | None :: l' => option_list_collapse_list l'
  end.
Definition option_list_collapse {A : Type} (l : list (option A)) : option (list A) :=
  let l' := option_list_collapse_list l in
  if bool_decide (l' = []) then None else Some l'.

Lemma option_list_collapse_id {A : Type} l : l ≠ [] -> option_list_collapse ((λ (x : A), Some x) <$> l) = Some l.
Proof.
  intros Hnil. induction l;auto;simpl. done.
  destruct l => /= //.
  assert (a0 :: l ≠ []) as Hni%IHl =>//.
  rewrite /option_list_collapse /= in Hni.
  inversion Hni. rewrite /option_list_collapse H0 /= // H0 //.
Qed.

Lemma option_list_collapse_cons_Some {A : Type} (l : list (option A)) (a : A) :
  option_list_collapse (Some a :: l) = Some (a :: option_list_collapse_list l).
Proof.
  rewrite /option_list_collapse /= //.
Qed.

Lemma option_list_collapse_cons_None {A : Type} (l : list (option A)) :
  option_list_collapse (None :: l) = option_list_collapse l.
Proof.
  rewrite /option_list_collapse /= //.
Qed.

Lemma option_list_collapse_some_eq {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> l' = option_list_collapse_list l.
Proof.
  unfold option_list_collapse. case_match;try done. intros Hl; inversion Hl. auto.
Qed.

Lemma option_list_collapse_some_nil {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> bool_decide (l' = []) = false.
Proof.
  unfold option_list_collapse. case_match;try done.
  intros Hl. inversion Hl. auto.
Qed.

Lemma option_list_collapse_some_exists {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> exists (a : A), a ∈ l' /\ (Some a) ∈ l.
Proof.
  unfold option_list_collapse. case_match;try done.
  intros Hl. inversion Hl.
  induction l;try done.
  simpl in *. case_match;simpl in *;simplify_eq.
  - exists a0. split;constructor.
  - apply IHl in H;auto.
    destruct H as [a [Hin1 Hin2]].
    exists a. split;auto. constructor;auto.
Qed.

Lemma option_list_collapse_list_length {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> length l' = length (option_list_collapse_list l).
Proof.
  revert l'; induction l;simpl =>/=l' Hl.
  - apply option_list_collapse_some_eq in Hl as -> =>//.
  - apply option_list_collapse_some_eq in Hl as ->.
    simpl. destruct a=>//.
Qed.

Lemma option_list_collapse_length {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> 0 < length l' <= length l.
Proof.
  intros Hl. split.
  { unfold option_list_collapse in Hl. case_match; try done.
    inversion Hl. apply bool_decide_eq_false in H.
    destruct (option_list_collapse_list l);try done. simpl. lia. }
  apply option_list_collapse_some_eq in Hl;subst.
  induction l.
  - simpl. lia.
  - simpl. destruct a => /=.
    + apply le_n_S =>//.
    + constructor =>//.
Qed.

Inductive collapse_rel {A : Type} : list (option A) -> list A -> Prop :=
| collapse_nil : collapse_rel [] []
| collapse_None l l' : collapse_rel l l' -> collapse_rel (None :: l) l'
| collapse_Some l l' a : collapse_rel l l' -> collapse_rel (Some a :: l) (a :: l').

Lemma collapse_rel_iff {A : Type} (l : list (option A)) (l' : list A) :
  collapse_rel l l' ->
  (forall x, Some x ∈ l <-> x ∈ l').
Proof.
  intros Hl. induction Hl.
  - intros x;split;intros Hcontr;inversion Hcontr.
  - intros x. split.
    + intros [Heq | Hin]%elem_of_cons;[inversion Heq|].
      apply IHHl. auto.
    + intros Hin. constructor. apply IHHl. auto.
  - intros x; split; intros [Heq|Hin]%elem_of_cons;simplify_eq;constructor.
    + apply IHHl;auto.
    + apply IHHl;auto.
Qed.

Lemma collapse_rel_witness {A : Type} (l : list (option A)) (l' : list A) :
  collapse_rel l l' ->
  (forall x, x ∈ l -> (exists x', x = Some x' /\ x' ∈ l') \/ x = None).
Proof.
  intros Hl. pose proof (collapse_rel_iff _ _ Hl).
  intros x Ha.
  destruct x;[apply H in Ha|].
  + left. intros. 
    simplify_eq. eauto.
  + by right.
Qed.

Lemma option_list_collapse_spec {A : Type} (l : list (option A)) (l' : list A) :
  option_list_collapse l = Some l' -> collapse_rel l l'.
Proof.
  intros Hl. apply option_list_collapse_some_eq in Hl as ->.
  induction l.
  - simpl. constructor.
  - simpl. destruct a; constructor;auto.
Qed.

Lemma option_list_collapse_list_construct {A : Type} (l : list (option A)) (l' : list A) :
  collapse_rel l l' ->
  option_list_collapse_list l = l'.
Proof.
  intros Hl.
  induction Hl;auto.
  simpl. f_equiv. auto.
Qed.

Lemma option_list_collapse_spec_construct {A : Type} (l : list (option A)) (l' : list A) :
  bool_decide (l' = []) = false ->
  collapse_rel l l' ->
  option_list_collapse l = Some l'.
Proof.
  intros Hnil Hl.
  apply option_list_collapse_list_construct in Hl as Heq.
  rewrite /option_list_collapse Heq Hnil //.
Qed.

Lemma option_list_collapse_none_spec {A : Type} (l : list (option A)) :
  option_list_collapse l = None -> (forall x, x ∈ l -> x = None).
Proof.
  induction l =>Hnone x Hin.
  - inversion Hin.
  - apply elem_of_cons in Hin as [Heq|Hin].
    + subst. destruct a;auto.
      rewrite /option_list_collapse /= in Hnone.
      done.
    + destruct a;auto.
      rewrite /option_list_collapse /= in Hnone.
      done.
Qed.

Lemma option_list_collapse_none_construct {A : Type} (l : list (option A)) :
   (forall x, x ∈ l -> x = None) ->
  option_list_collapse l = None.
Proof.
  induction l;simpl;auto.
  intros Hcond.
  rewrite /option_list_collapse /=.
  rewrite (Hcond a);[|constructor].
  case_match;auto.
  assert (option_list_collapse l = None) as Hnone.
  { apply IHl. intros. apply Hcond. constructor. auto. }
  rewrite /option_list_collapse H in Hnone. auto.
Qed.

Lemma option_list_collapse_list_app {A : Type} (l l2 : list (option A)) :
  option_list_collapse_list (l ++ l2) = option_list_collapse_list l ++ option_list_collapse_list l2.
Proof.
  revert l2;induction l =>l2 /= //.
  destruct a;auto.
  simpl. f_equiv. apply IHl.
Qed.

Lemma option_list_collapse_some_some_app {A : Type} (l1 l2 : list (option A)) (l1' l2' : list A) :
  option_list_collapse l1 = Some l1' ->
  option_list_collapse l2 = Some l2' ->
  option_list_collapse (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  intros Hl1 Hl2.
  apply option_list_collapse_spec in Hl1 as Hspec.
  induction Hspec;auto.
  rewrite option_list_collapse_cons_Some in Hl1. simplify_eq.
  simpl. rewrite /option_list_collapse /=. f_equiv. f_equiv.
  apply option_list_collapse_some_eq in Hl2;subst.
  apply option_list_collapse_list_app.
Qed.

Lemma option_list_collapse_none_l_app {A : Type} (l1 l2 : list (option A)) res :
  option_list_collapse l1 = None ->
  option_list_collapse l2 = res ->
  option_list_collapse (l1 ++ l2) = res.
Proof.
  revert l2 res. induction l1;intros l2 res Hl1 Hres;auto.
  simpl. rewrite /option_list_collapse /=. destruct a => // /=.
  rewrite option_list_collapse_cons_None in Hl1. apply IHl1 in Hres =>//.
Qed.

Lemma option_list_collapse_none_r_app {A : Type} (l1 l2 : list (option A)) res :
  option_list_collapse l1 = res ->
  option_list_collapse l2 = None ->
  option_list_collapse (l1 ++ l2) = res.
Proof.
  revert l2 res. induction l1;intros l2 res Hl1 Hres;auto.
  - simpl. rewrite /option_list_collapse /= in Hl1. subst. auto.
  - simpl. destruct a.
    + rewrite option_list_collapse_cons_Some in Hl1; simplify_eq.
      eapply IHl1 in Hres;eauto.
      rewrite /option_list_collapse /=. f_equiv. f_equiv.
      rewrite /option_list_collapse in Hres.
      case_match;case_match;simplify_eq;try done.
      apply bool_decide_eq_true in H as ->.
      apply bool_decide_eq_true in H0 as ->. auto.
    + rewrite option_list_collapse_cons_None.
      rewrite option_list_collapse_cons_None in Hl1.
      apply IHl1;auto.
Qed.

Definition agree_option_list_map {A B} (f : A → option B) (x : agree A) : option (list B) :=
  option_list_collapse (f <$> x.(agree_car)).
Program Definition lift_option_map {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false)
  : option (agree A) :=
  match x with
  | Some agree_car' => Some {| agree_car := agree_car' ; agree_not_nil := _ |}
  | None => None
  end.
Next Obligation.
  intros. destruct x;simplify_eq. auto.
Qed.

Lemma agree_option_eq_some_1 {A} (x : option (list A)) (y : agree A) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  x = Some (agree_car y) → lift_option_map x Hne = Some y.
Proof.
  intros Hx. destruct x;[|done]. simplify_eq. simpl.
  f_equal. destruct y as [b ?]; simpl. f_equal. apply proof_irrel.
Qed.
Lemma agree_option_eq_some_2 {A} (x : option (list A)) (y : agree A) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  lift_option_map x Hne = Some y -> x = Some (agree_car y).
Proof.
  intros Hx. destruct x;[|done]. simpl in *. simplify_eq. simpl. auto.
Qed.
Lemma agree_option_eq_some {A} (x : option (list A)) (y : agree A) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  x = Some (agree_car y) <-> lift_option_map x Hne = Some y.
Proof. split. apply agree_option_eq_some_1. apply agree_option_eq_some_2. Qed.

Lemma agree_option_eq_none_1 {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  x = None → lift_option_map x Hne = None.
Proof.
  intros Hx. destruct x;[|done]. simplify_eq.
Qed.
Lemma agree_option_eq_none_2 {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  lift_option_map x Hne = None -> x = None.
Proof.
  intros Hx. destruct x;[|done]. simplify_eq.
Qed.
Lemma agree_option_eq_none {A} (x : option (list A)) (Hne : forall x', x = Some x' -> bool_decide (x' = []) = false) :
  lift_option_map x Hne = None <-> x = None.
Proof. split. apply agree_option_eq_none_2. apply agree_option_eq_none_1. Qed.


Program Definition agree_option_map {A B} (f : A → option B) (x : agree A) : option (agree B) :=
  lift_option_map (option_list_collapse (f <$> x.(agree_car))) _.
Next Obligation.
  intros A B f [[|??] ?] ? Hsome%option_list_collapse_some_nil =>//.
Qed.

Lemma option_map_list_collapse_None {A: Type} (l : list A) :
  bool_decide (l = []) = false ->
  option_list_collapse ((λ x : A, Some x) <$> l) = None -> False.
Proof.
  induction l;simpl;[done|].
  intros _ Hnone. rewrite option_list_collapse_cons_Some in Hnone. done.
Qed.

Lemma agree_option_map_id {A} (x : agree A) : bool_decide (agree_car x = []) = false -> agree_option_map (λ x, Some x) x = Some x.
Proof.
  intros Hnil.
  apply agree_option_eq_some. apply option_list_collapse_id.
  apply bool_decide_eq_false in Hnil. auto.
Qed.

Lemma collapse_rel_compose {A B C : Type} (f : A -> option B) (g : B -> option C) l1 l2 l3:
  collapse_rel (f <$> l1) l2 ->
  collapse_rel (g <$> l2) l3 ->
  collapse_rel ((λ x : A, f x ≫= g) <$> l1) l3.
Proof.
  revert l2 l3.
  induction l1 => l2 l3 Hl1 Hl2.
  - inversion Hl1;subst.
    simpl. inversion Hl2;subst;auto.
  - simpl in *. inversion Hl1;subst;simplify_eq.
    + simpl.
      constructor. eapply IHl1;eauto.
    + simpl in *.
      destruct (g a0).
      * inversion Hl2;subst. constructor.
        eapply IHl1;eauto.
      * constructor. eapply IHl1;eauto. inversion Hl2;auto.
Qed.

Lemma collapse_rel_idemp {A B : Type} (f : A -> option B) (g : B -> option B) l1 l2 :
  (forall a b, f a = Some b -> g b = Some b) ->
  collapse_rel (f <$> l1) l2 ->
  collapse_rel (g <$> l2) l2.
Proof.
  revert l2.
  induction l1 => l2 Hcond Hl1.
  - inversion Hl1;subst. auto.
  - rewrite fmap_cons in Hl1.
    inversion Hl1;subst;simplify_eq.
    + apply IHl1 in H2;auto.
    + symmetry in H. apply Hcond in H.
      rewrite fmap_cons H.
      constructor. apply IHl1;auto.
Qed.  

Lemma agree_option_map_compose {A B C} (f : A → option B) (g : B → option C) (x : agree A) :
  agree_option_map (λ x, f x ≫= g) x = agree_option_map f x ≫= agree_option_map g.
Proof.
  destruct (agree_option_map f x) eqn:Hf; simpl.
  - apply agree_option_eq_some in Hf.
    destruct (agree_option_map g a) eqn:Hg; simpl.
    + apply agree_option_eq_some in Hg.
      apply agree_option_eq_some.
      pose proof (option_list_collapse_spec _ _ Hf) as Hspec1.
      pose proof (option_list_collapse_spec _ _ Hg) as Hspec2.
      apply option_list_collapse_spec_construct.
      { destruct a0. auto. }
      eapply collapse_rel_compose;eauto.
    + apply agree_option_eq_none in Hg as Hnone.
      apply option_list_collapse_length in Hf as Hlen. destruct Hlen as [Hlt Hle].
      apply agree_option_eq_none.
      apply option_list_collapse_none_construct.
      apply option_list_collapse_spec in Hf.
      intros x' Hin. apply list_elem_of_fmap in Hin as [y [Heq Hin]].
      destruct (f y) eqn:Hy;simpl in *;subst;auto.
      eapply option_list_collapse_none_spec;eauto. apply list_elem_of_fmap.
      eexists;split;eauto.
      eapply collapse_rel_iff;eauto. rewrite -Hy.
      apply list_elem_of_fmap. eexists;split;eauto.
  - apply agree_option_eq_none.
    apply agree_option_eq_none in Hf.
    apply option_list_collapse_none_construct.
    intros x' [y [Heq Hin]]%list_elem_of_fmap.
    destruct (f y) eqn:Hy;simpl in *;auto.
    subst.
    eapply option_list_collapse_none_spec with (x:=f y) in Hf;eauto;simplify_eq.
    apply list_elem_of_fmap;eauto.
Qed.

Lemma agree_option_map_to_agree {A B} (f : A → option B) (x : A) :
  agree_option_map f (to_agree x) = (f x) ≫= (λ x, Some (to_agree x)).
Proof.
  destruct (f x) eqn:Hf.
  - simpl. apply agree_option_eq_some.
    rewrite /= Hf //.
  - simpl. apply agree_option_eq_none.
    rewrite /= Hf //.
Qed.

Section agree_option_map.
  Context {A B : ofe} (f : A → option B) {Hf: NonExpansive f}.

  Local Instance agree_option_map_ne : NonExpansive (agree_option_map f).
  Proof using Type*.
    intros n x y [H H'].
    destruct (agree_option_map f x) eqn:Hx, (agree_option_map f y) eqn:Hy;auto.
    - f_equiv. apply agree_option_eq_some in Hx.
      apply agree_option_eq_some in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec2.
      apply option_list_collapse_length in Hx as Hlen.
      apply option_list_collapse_length in Hy as Hlen'.
      rewrite length_fmap in Hlen; rewrite length_fmap in Hlen'.
      split=> b /=; setoid_rewrite list_elem_of_lookup.
      + rewrite -!list_elem_of_lookup. intros Hi.
        apply collapse_rel_iff with (x:=b) in Hspec1 as Hiff.
        apply Hiff in Hi.
        apply list_elem_of_fmap in Hi as [c [Heq Hc]];simplify_eq.
        apply H in Hc as [c' [Hin Hc']].
        apply Hf in Hc'. rewrite -Heq in Hc'.
        apply list_elem_of_fmap_2 with (f:=f) in Hin.
        destruct (f c') eqn:Hfc;inversion Hc'; subst.
        apply collapse_rel_iff with (x:=o) in Hspec2 as Hiff2.
        apply Hiff2 in Hin. exists o. rewrite -list_elem_of_lookup. split;auto.
      + rewrite -!list_elem_of_lookup. intros Hi.
        apply collapse_rel_iff with (x:=b) in Hspec2 as Hiff.
        apply Hiff in Hi.
        apply list_elem_of_fmap in Hi as [c [Heq Hc]];simplify_eq.
        apply H' in Hc as [c' [Hin Hc']].
        apply Hf in Hc'. rewrite -Heq in Hc'.
        apply list_elem_of_fmap_2 with (f:=f) in Hin.
        destruct (f c') eqn:Hfc;inversion Hc'; subst.
        apply collapse_rel_iff with (x:=o) in Hspec1 as Hiff1.
        apply Hiff1 in Hin. exists o. rewrite -list_elem_of_lookup. split;auto.
    - apply agree_option_eq_some in Hx.
      apply agree_option_eq_none in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hy) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff in Hb. apply list_elem_of_fmap in Hb as [b' [Heq Hb']].
      apply H in Hb' as Hin. destruct Hin as [c [Hin Hne]].
      apply Hf in Hne. apply list_elem_of_fmap_2 with (f:=f) in Hin.
      apply Hspec2 in Hin as Heq'. rewrite -Heq Heq' in Hne. inversion Hne.
    - apply agree_option_eq_none in Hx.
      apply agree_option_eq_some in Hy.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hx) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff in Hb. apply list_elem_of_fmap in Hb as [b' [Heq Hb']].
      apply H' in Hb' as Hin. destruct Hin as [c [Hin Hne]].
      apply Hf in Hne. apply list_elem_of_fmap_2 with (f:=f) in Hin.
      apply Hspec2 in Hin as Heq'. rewrite -Heq Heq' in Hne. inversion Hne.
  Qed.
  Local Instance agree_option_map_proper : Proper ((≡) ==> (≡)) (agree_option_map f) := ne_proper _.

  Lemma agree_option_map_ext (g : A → option B) x :
    (∀ a, f a ≡ g a) → agree_option_map f x ≡ agree_option_map g x.
  Proof using Hf.
    intros Hfg.
    destruct (agree_option_map f x) eqn:Hx, (agree_option_map g x) eqn:Hy;auto.
    - f_equiv. apply agree_option_eq_some in Hx.
      apply agree_option_eq_some in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
      pose proof (collapse_rel_iff _ _ Hspec2) as Hiff2.
      intros n.
      split=> b /=; setoid_rewrite list_elem_of_lookup.
      + rewrite -list_elem_of_lookup.
        intros Hb.
        apply Hiff1 in Hb as Hin.
        apply list_elem_of_fmap in Hin as [c [Heq Hc]].
        apply list_elem_of_fmap_2 with (f:=g) in Hc as Hc'.
        pose proof (Hfg c) as Hequiv. rewrite -Heq in Hequiv.
        destruct (g c) eqn:Hsome;[|inversion Hequiv].
        apply Hiff2 in Hc'. exists o. rewrite -list_elem_of_lookup. split;eauto.
        inversion Hequiv;subst;auto.
      + rewrite -list_elem_of_lookup.
        intros Hb.
        apply Hiff2 in Hb as Hin.
        apply list_elem_of_fmap in Hin as [c [Heq Hc]].
        apply list_elem_of_fmap_2 with (f:=f) in Hc as Hc'.
        pose proof (Hfg c) as Hequiv. rewrite -Heq in Hequiv.
        destruct (f c) eqn:Hsome;[|inversion Hequiv].
        apply Hiff1 in Hc'. exists o. rewrite -list_elem_of_lookup. split;eauto.
        inversion Hequiv;subst;auto.
    - apply agree_option_eq_some in Hx.
      apply agree_option_eq_none in Hy.
      pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hy) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff1 in Hb.
      apply list_elem_of_fmap in Hb as [y [Heq Hin]].
      apply list_elem_of_fmap_2 with (f:=g) in Hin.
      apply Hspec2 in Hin. specialize (Hfg y).
      rewrite -Heq Hin in Hfg. inversion Hfg.
    - apply agree_option_eq_some in Hy.
      apply agree_option_eq_none in Hx.
      pose proof (option_list_collapse_spec _ _ Hy) as Hspec1.
      pose proof (option_list_collapse_none_spec _ Hx) as Hspec2.
      pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
      pose proof (elem_of_agree a) as [b Hb].
      apply Hiff1 in Hb.
      apply list_elem_of_fmap in Hb as [y [Heq Hin]].
      apply list_elem_of_fmap_2 with (f:=f) in Hin.
      apply Hspec2 in Hin. specialize (Hfg y).
      rewrite -Heq Hin in Hfg. inversion Hfg.
  Qed.

  Lemma agree_option_map_validN x n :
    ✓{n} x -> ✓{n} agree_option_map f x.
  Proof.
    intros Hv.
    destruct (agree_option_map f x) eqn:Hx;cycle 1.
    { rewrite /validN /cmra_validN /= //. }
    rename a into x'.
    apply agree_option_eq_some in Hx.
    pose proof (option_list_collapse_spec _ _ Hx) as Hspec1.
    rewrite agree_validN_def in Hv.
    apply agree_validN_def.
    intros a b Ha Hb.
    pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
    apply Hiff1 in Ha as Ha'.
    apply Hiff1 in Hb as Hb'.
    apply list_elem_of_fmap in Ha' as [a' [Heq1 Ha']].
    apply list_elem_of_fmap in Hb' as [b' [Heq2 Hb']].
    eapply Hv in Ha';eauto. apply Hf in Ha'. rewrite -Heq1 -Heq2 in Ha'.
    inversion Ha';auto.
  Qed.

  Lemma agree_option_map_valid_includedN x y n:
    ✓{n} y -> x ≼{n} y -> agree_option_map f x ≼{n} agree_option_map f y.
  Proof. intros. rewrite (agree_valid_includedN _ x y) //. Qed.
  
  Lemma agree_option_map_op v1 v2 :
    agree_option_map f (v1 ⋅ v2) = agree_option_map f v1 ⋅ agree_option_map f v2.
  Proof.
    destruct (agree_option_map f v1) eqn:Hv1.
    - apply agree_option_eq_some in Hv1.
      destruct (agree_option_map f v2) eqn:Hv2. 
      + apply agree_option_eq_some in Hv2.
        destruct a,a0;simpl in *. rewrite -Some_op.
        destruct (agree_option_map f (v1 ⋅ v2)) eqn:Hv;cycle 1.
        { exfalso. apply agree_option_eq_none in Hv.
          rewrite fmap_app in Hv.
          by erewrite option_list_collapse_some_some_app in Hv;eauto. }
        apply agree_option_eq_some in Hv.
        rewrite fmap_app in Hv.
        erewrite option_list_collapse_some_some_app in Hv;eauto.
        simplify_eq. destruct a;simpl in *. cbv. rewrite -/app.
        f_equal. apply agree_eq. simpl. auto.
      + apply agree_option_eq_none in Hv2.
        destruct a;simpl in *. rewrite op_None_right_id.
        destruct (agree_option_map f (v1 ⋅ v2)) eqn:Hv;cycle 1.
        { exfalso. apply agree_option_eq_none in Hv.
          rewrite fmap_app in Hv.
          by erewrite option_list_collapse_none_r_app in Hv;eauto. }
        apply agree_option_eq_some in Hv.
        rewrite fmap_app in Hv.
        erewrite option_list_collapse_none_r_app in Hv;eauto.
        simplify_eq. destruct a;simpl in *. f_equal. apply agree_eq.
        simpl. auto.
    - apply agree_option_eq_none in Hv1.
      destruct (agree_option_map f (v1 ⋅ v2)) eqn:Hv;cycle 1.
      { apply agree_option_eq_none in Hv.
        rewrite fmap_app in Hv.
        erewrite option_list_collapse_none_l_app in Hv;eauto.
        symmetry. rewrite op_None_left_id. apply agree_option_eq_none.
        auto. }
      apply agree_option_eq_some in Hv.
      rewrite fmap_app in Hv.
      erewrite option_list_collapse_none_l_app in Hv;eauto.
      symmetry. rewrite op_None_left_id. apply agree_option_eq_some.
      auto.
  Qed.

End agree_option_map.

Definition map_trans_auth_lift {L : Type} {V : ofe} `{EqDecision L, Countable L} (f : L -> V -> option V) :
  L -> agreeR V -> option (agreeR V) :=
  λ l v, agree_option_map (f l) v.

Definition gMapTrans_auth_lift {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  map_entry : gmapO K (agreeR V) → gmapO K (agreeR V) :=
  map_imap (map_trans_auth_lift map_entry).

Definition map_trans_frag_lift {L : Type} {V : ofe} `{EqDecision L, Countable L} (f : L -> V -> option V) :
  L -> prodR dfracR (agreeR V) -> option (prodR dfracR (agreeR V)) :=
  λ l dv, let '(d,v) := dv in agree_option_map (f l) v ≫= λ v', Some (d,v').

Definition gMapTrans_frag_lift {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  map_entry : (gmap_view.gmap_view_fragUR K (agreeR V)) → (gmap_view.gmap_view_fragUR K (agreeR V)) :=
  λ frag_view, map_imap (map_trans_frag_lift map_entry) frag_view.

Definition map_entry_lift_gmap_view {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
  (map_entry: K → V → option V) : gmap_viewR K (agreeR V) -> gmap_viewR K (agreeR V) :=
  fmap_view (gMapTrans_auth_lift map_entry) (gMapTrans_frag_lift map_entry).

Global Instance gmap_map_imap_ne {K : Type} {A B : ofe} `{Countable K}
  (f : K -> A -> option B) :
  (∀ k, NonExpansive (f k)) -> NonExpansive (map_imap f).
Proof.
  intros Hf n m1 m2 Hne. intros k.
  rewrite !map_lookup_imap. pose proof (Hne k) as Hlook. rewrite Hlook. auto.
Qed.

Lemma to_agree_dist {V : ofe} n (w' : agree V) (w : V) :
  w' ≡{n}≡ to_agree w <-> forall a, a ∈ agree_car w' -> a ≡{n}≡ w.
Proof.
  split.
  - intros Hne. inversion Hne as [Hin1 Hin2].
    intros a Hin. apply Hin1 in Hin as [b [Hb Heq]].
    unfold to_agree in Hb. simpl in *.
    apply list_elem_of_singleton in Hb;subst.
    auto.
  - intros Hcond. split.
    + intros.
      apply Hcond in H. exists w. split;auto.
      rewrite /to_agree /=. constructor.
    + rewrite /to_agree /=. intros v H%list_elem_of_singleton;subst.
      pose proof (elem_of_agree w') as [a Ha].
      exists a. split;auto.
Qed.

Lemma dist_to_agree_validN {A : ofe} (n : nat) (x : agree A) (a : A) : x ≡{n}≡ to_agree a -> ✓{n} x.
Proof.
  intros.
  apply agree_validN_def. intros.
  rewrite to_agree_dist in H. apply H in H0.
  apply H in H1. rewrite H0. auto.
Qed.

Definition map_entry_lift_gmap_view_no_auth {K : Type} {V : ofe} {eqK : EqDecision K} {countK : Countable K}
    map_entry : gmap_viewR K (agreeR V) -> gmap_viewR K (agreeR V) :=
    λ (x : gmap_viewR K (agreeR V)), View None (gMapTrans_frag_lift map_entry (view_frag_proj x)).

Section map_entry.
  Context {K : Type} {V : ofe}.
  Context `{Countable K, !LeibnizEquiv V, !OfeDiscrete V}.
  Implicit Types (map_entry : K → V → option V).
  
  Lemma map_trans_auth_frag_rel
    map_entry `{!MapTrans map_entry} (n : nat)
    (m1 : gmap K V) (view_frag_proj : gmap_view.gmap_view_fragUR K (agreeR V)) :
    gmap_view.gmap_view_rel_raw K (agree V) n (to_agree <$> m1) view_frag_proj ->
    gmap_view.gmap_view_rel_raw K (agree V) n (to_agree <$> map_imap map_entry m1) (map_imap (map_trans_frag_lift map_entry) view_frag_proj).
  Proof.
    intros Hv2. intros i [d' a'] Hlook1. simpl.
    rewrite map_lookup_imap in Hlook1.
    destruct (view_frag_proj !! i) eqn:Hlook2;rewrite Hlook2 /= in Hlook1;[|done].
    destruct c as [q w'];simpl in *.
    destruct (agree_option_map (map_entry i) w') eqn:Hsome;simpl in *;simplify_eq.
    destruct (Hv2 i (d',w') Hlook2) as (? & d & (w & <- & Hw)%lookup_fmap_Some & [Hd Hval] & Hincl);simpl in *.
    apply Some_pair_includedN_r in Hincl as Hag.
    rewrite Some_includedN_total in Hag.
    pose proof (cmra_validN_includedN _ w' _ Hval ltac:(done)) as Hval'.
    apply agree_option_map_validN with (f:=map_entry i) in Hval'; [|apply _].
    rewrite Hsome in Hval'. rewrite Some_validN in Hval'.
    apply agree_option_eq_some in Hsome.
    apply option_list_collapse_spec in Hsome as Hspec.
    pose proof (collapse_rel_iff _ _ Hspec) as Hiff.
    assert (map_entry i w = map_imap map_entry m1 !! i) as Heq.
    { rewrite map_lookup_imap. rewrite Hw. done. }
    pose proof (elem_of_agree w') as [e Hin].
    assert (e = w) as ->.
    { (* TODO: is there a better proof? *)
      destruct w' as [w' ?]. simpl in *.
      rewrite /to_agree agree_includedN /op /agree_op_instance /= in Hag.
      destruct Hag as [_ Hag]. simpl in Hag.
      odestruct (Hag e _) as (e' & ->%list_elem_of_singleton & Hequiv); first set_solver.
      apply leibniz_equiv.
      apply discrete_iff in Hequiv; auto.
      apply _. }
    apply list_elem_of_fmap_2 with (f:=map_entry i) in Hin.
    destruct (map_imap map_entry m1 !! i) eqn:Hres.
    - rewrite Heq in Hin.
      apply Hiff in Hin.
      apply to_agree_uninjN in Hval' as Hb; destruct Hb as [b Hb].
      symmetry in Hb. rewrite to_agree_dist in Hb.
      apply Hb in Hin. exists (to_agree o), d'. repeat split.
      + rewrite lookup_fmap Hres /= //.
      + eapply cmra_validN_Some_includedN; first done.
        apply Some_pair_includedN_l in Hincl as Hdincl'.
        done.
      + apply: Some_includedN_refl. f_equiv.
        apply to_agree_dist. intros. rewrite Hin. auto.
    - apply option_list_collapse_some_exists in Hsome as Ha.
      destruct Ha as [a [Hina HH]].
      apply list_elem_of_fmap in HH as [y [Heq' Hy]].
      rewrite Heq in Hin.
      apply list_elem_of_fmap in Hin as [y' [Heq'' Hnone]].
      pose proof (cmra_validN_includedN _ w' _ Hval ltac:(done)) as Hval''.
      rewrite agree_validN_def in Hval''.
      eapply Hval'' in Hnone; [|apply Hy].
      assert (y = y') as ->.
      { apply leibniz_equiv. apply discrete_iff in Hnone;auto.  apply _. }
      rewrite -Heq' in Heq''. done.
  Qed.
  
  Lemma map_trans_auth_frag_rel'
    map_entry `{!MapTrans map_entry} (n : nat)
    (view_auth_proj : gmap K (agree V)) (view_frag_proj : gmap_view.gmap_view_fragUR K (agreeR V)) :
    gmap_view.gmap_view_rel_raw K (agree V) n view_auth_proj view_frag_proj ->
    gmap_view.gmap_view_rel_raw K (agree V) n (map_imap (map_trans_auth_lift map_entry) view_auth_proj) (map_imap (map_trans_frag_lift map_entry) view_frag_proj).
  Proof.
    intros Hv2. intros i [d' a'] Hlook1. simpl.
    rewrite map_lookup_imap in Hlook1.
    destruct (view_frag_proj !! i) eqn:Hlook2;rewrite Hlook2 /= in Hlook1;[|done].
    destruct c as [q w'];simpl in *.
    destruct (agree_option_map (map_entry i) w') eqn:Hsome'; simpl in *; simplify_eq.
    destruct (Hv2 i (d',w') Hlook2) as (w & d & Hw & [Hd Hval] & Hincl);simpl in *.
    apply Some_pair_includedN_r in Hincl as Hag.
    rewrite Some_includedN_total in Hag.
    pose proof (cmra_validN_includedN _ w' _ Hval ltac:(done)) as Hval'.
    opose proof (agree_option_map_valid_includedN (map_entry i) w' w n _ _) as Hincl'; [ done | done | ].
    rewrite Hsome' in Hincl'.
    pose proof Hincl' as Hsome.
    apply Some_includedN_is_Some in Hsome as [a Hsome].
    rewrite Hsome in Hincl'.
    exists a, d'.
    rewrite map_lookup_imap Hw /= /map_trans_auth_lift Hsome.
    apply agree_option_map_validN with (f:=map_entry i) in Hval'; [|apply _].
    apply agree_option_map_validN with (f:=map_entry i) in Hval; [|apply _].
    rewrite Hsome in Hval. rewrite Hsome' in Hval'.
    repeat split; try done.
    - eapply cmra_validN_Some_includedN; first done.
      apply Some_pair_includedN_l in Hincl as Hdincl'.
      done.
    - apply: Some_includedN_refl. f_equiv.
      apply Some_includedN_total in Hincl'.
      rewrite Some_validN in Hval'.
      apply agree_valid_includedN; done.
  Qed.

  Lemma agree_option_map_discard_all map_entry `{!MapTrans map_entry}
    (i : K) (v1 v2 a : agree V):
    agree_option_map (map_entry i) v1 = Some a ->
    agree_option_map (map_entry i) v2 = None -> False.
  Proof.
    intros Hag1 Hag2.
    apply agree_option_eq_some in Hag1.
    apply agree_option_eq_none in Hag2.
    pose proof (elem_of_agree v2) as [v Hv].
    pose proof (map_trans_frag_discard_all i v) as Hn.
    pose proof (option_list_collapse_none_spec _ Hag2) as Hspec2.
    apply list_elem_of_fmap_2 with (f:=map_entry i) in Hv.
    apply Hspec2 in Hv. pose proof (Hn Hv).
    pose proof (option_list_collapse_spec _ _ Hag1) as Hspec1.
    pose proof (collapse_rel_iff _ _ Hspec1) as Hiff1.
    pose proof (elem_of_agree a) as [a0 Ha0].
    apply Hiff1 in Ha0.
    apply list_elem_of_fmap in Ha0 as [? [Hcontr ?]].
    rewrite H0 in Hcontr. done.
  Qed.
  
  Global Instance gMapTrans_frag_lift_CmraMorphism
    map_entry `{!MapTrans map_entry} : CmraMorphism (gMapTrans_frag_lift map_entry).
  Proof.
    split.
    - intros n x y Hne.
      apply gmap_map_imap_ne =>//.
      destruct x,y =>/=.
      intros k m [d1 v1] [d2 v2] Hne2. simpl. inversion Hne2 as [Hne1 Hne2'];simpl in *; simplify_eq.
      apply option_mbind_ne.
      + intros a1 a2 Ha. constructor. split;auto.
      + apply: agree_option_map_ne =>//.
    - intros n x Hx i.
      specialize (Hx i).
      rewrite /gMapTrans_frag_lift map_lookup_imap.
      destruct (x !! i) eqn:Hsome;[|rewrite Hsome //].
      rewrite Hsome in Hx. rewrite Hsome /=.
      rewrite Some_validN in Hx. inversion Hx as [Hx1 Hx2].
      destruct c as [q v]; simpl in *.
      destruct (agree_option_map (map_entry i) v) eqn:Hv =>// /=.
      apply Some_validN. split => // /=. rewrite -Some_validN -Hv.
      apply: agree_option_map_validN =>//.
    - intros view_frag_proj. rewrite /gMapTrans_frag_lift /=.
      rewrite !cmra_pcore_core. f_equiv.
      intros i.
      rewrite map_lookup_imap.
      destruct (core view_frag_proj !! i) eqn:Hlook;rewrite Hlook => /=.
      * destruct c as [d v];simpl in *.
        rewrite lookup_core in Hlook. rewrite lookup_core.
        unfold map_trans_frag_lift.
        destruct (view_frag_proj !! i) eqn:Hi; rewrite Hi in Hlook;[|inversion Hlook].
        destruct c as [d' v'].
        rewrite map_lookup_imap Hi /=.
        assert (v = v') as ->.
        { destruct d,d'; inversion Hlook;auto. }
        destruct (agree_option_map (map_entry i) v') eqn:Hv1 => /= //.
        destruct d,d';auto;inversion Hlook.
      * rewrite lookup_core in Hlook.
        destruct (view_frag_proj !! i) eqn:Hi;rewrite Hi in Hlook.
        { destruct c as [d v];simpl in *. destruct d;inversion Hlook.
          rewrite lookup_core map_lookup_imap Hi /=.
          destruct (agree_option_map (map_entry i) v) =>//. }
        { rewrite lookup_core map_lookup_imap Hi /= //. }
    - intros view_frag_proj view_frag_proj0.
      intros i.
      rewrite !lookup_op !map_lookup_imap. rewrite lookup_op.
      destruct (view_frag_proj !! i) eqn:Hlook1,(view_frag_proj0 !! i) eqn:Hlook2;rewrite Hlook1 Hlook2; simpl in *=>//.
      * destruct c as [d1 v1],c0 as [d2 v2];simpl in *.
        rewrite agree_option_map_op.
        destruct (agree_option_map (map_entry i) v1) eqn:Hag1, (agree_option_map (map_entry i) v2) eqn:Hag2;simpl in *;auto.
        ** exfalso. apply: agree_option_map_discard_all;eauto.
        ** exfalso. apply: agree_option_map_discard_all;eauto.
      * rewrite op_None_right_id. auto.
      * rewrite op_None_left_id. auto.
  Qed.

  
  #[global] Instance gMapTrans_auth_lift_CmraMorphism
    map_entry `{!MapTrans map_entry} : CmraMorphism (gMapTrans_auth_lift map_entry).
  Proof.
    split.
    - intros n x y Hne.
      apply gmap_map_imap_ne =>//.
      destruct x,y =>/=.
      intros k m v1 v2 Hne2. simpl. inversion Hne2 as [Hne1 Hne2'];simpl in *; simplify_eq.
      apply: agree_option_map_ne =>//.
    - intros n x Hx i.
      specialize (Hx i).
      rewrite /gMapTrans_auth_lift /map_trans_auth_lift map_lookup_imap.
      destruct (x !! i) eqn:Hsome;[|rewrite Hsome //].
      rewrite Hsome in Hx. rewrite Hsome /=.
      rewrite Some_validN in Hx.
      destruct (agree_option_map (map_entry i) c) eqn:Hv =>// /=.
      apply Some_validN. rewrite -Some_validN -Hv.
      apply: agree_option_map_validN => //.
    - intros view_frag_proj. rewrite /gMapTrans_auth_lift /=.
      rewrite !cmra_pcore_core. f_equiv.
      intros i.
      rewrite map_lookup_imap.
      destruct (core view_frag_proj !! i) eqn:Hlook;rewrite Hlook => /=.
      * rewrite lookup_core in Hlook. rewrite lookup_core.
        unfold map_trans_frag_lift.
        destruct (view_frag_proj !! i) as [c' | ] eqn:Hi; rewrite Hi in Hlook;[|inversion Hlook].
        rewrite map_lookup_imap Hi /=.
        assert (c = c') as <-.
        { inversion Hlook;auto. }
        rewrite /map_trans_auth_lift.
        destruct (agree_option_map (map_entry i) c) eqn:Hv1 => /= //.
      * rewrite lookup_core in Hlook.
        destruct (view_frag_proj !! i) eqn:Hi;rewrite Hi in Hlook; inversion Hlook.
        rewrite lookup_core map_lookup_imap Hi /= //.
    - intros view_auth_proj view_auth_proj0.
      intros i.
      rewrite !lookup_op !map_lookup_imap. rewrite lookup_op.
      rewrite /map_trans_auth_lift.
      destruct (view_auth_proj !! i) eqn:Hlook1,(view_auth_proj0 !! i) eqn:Hlook2;rewrite Hlook1 Hlook2; simpl in *=>//.
      * rewrite agree_option_map_op //.
      * rewrite op_None_right_id. auto.
      * rewrite op_None_left_id. auto.
  Qed.
  
  (* Lemma test `{!MapTrans map_entry}  x : core ((map_entry_lift_gmap_view map_entry) x) = core x. *)
  (* Proof. *)
  (*   rewrite view.view_core_eq. f_equiv. *)
  (*   - unfold core. simpl. destruct view_auth_proj =>// /=. *)
  (*     destruct p. *)
  (*     rewrite /pcore /cmra_pcore /= /prod_pcore_instance /=. *)
  (*     rewrite /pcore /cmra_pcore /= /dfrac_pcore_instance. *)
  (*     destruct d;simpl =>//. *)

  (*     simpl.  *)
  (*     destruct p as [d a];destruct d;simpl. *)

  (*     unfold pcore. simpl. *)


      
  (*   f_equiv. apply map_eq. *)
  (*   apply agree_eq. cmra_car_eq. *)

  Global Instance gMapTrans_lift_CmraMorphism map_entry `{!MapTrans map_entry} :
    CmraMorphism (map_entry_lift_gmap_view map_entry).
  Proof.
    apply fmap_view_cmra_morphism; [apply _|apply _|].
    intros. apply: map_trans_auth_frag_rel'. auto.
  Qed.

  (* Lemma option_bind_pair_twice_eq {A B C D : Type} (f : A -> option B) (g : B -> option C) (d : D) (a : A) : *)
  (*   f a ≫= (λ (a : A), Some (d,a)) ≫= (λ (db : (D * B)), let '(d, b) := db in g b ≫= (λ (c : C), Some (d,c))) = *)
  (*     f a ≫= (λ a, Some (d,a)) ≫= (λ '(d,b), g b ≫= (λ c, Some (d,c))). *)
  (*   f a ≫= (λ b, g b ≫= (λ c, Some (d,c))). *)
    
    
  Global Instance gMapTrans_lift_Indep map_entry1 map_entry2
    `{!MapTrans map_entry1} `{!MapTrans map_entry2}
    `{Hind: ∀ k, OIndep (≡) (map_entry1 k) (map_entry2 k)} :
    Indep (≡) (map_entry_lift_gmap_view map_entry1) (map_entry_lift_gmap_view map_entry2).
  Proof.
    intros m. destruct m,view_auth_proj.
    - split;simpl.
      + f_equiv. split;simpl;auto.
        destruct p;simpl. intros n.
        rewrite -!agree_map_compose.
        apply agree_map_ext; simpl; first apply _.
        intros m. intros i. simpl.
        rewrite /gMapTrans_auth_lift /=.
        rewrite map_imap_compose.
        rewrite /= !map_lookup_imap.
        destruct (m !! i) eqn:Hm;rewrite Hm;auto;simpl.
        rewrite /map_trans_auth_lift. rewrite -?agree_option_map_compose.
        apply agree_option_map_ext.
        { intros ??? ->. auto. }
        intros ?. rewrite Hind. auto.
      + rewrite /gMapTrans_frag_lift /=.
        rewrite !map_imap_compose.
        intros i.
        rewrite !map_lookup_imap.
        destruct (view_frag_proj !! i) eqn:Hlook;rewrite Hlook/=//.
        destruct c;simpl.
        rewrite /map_trans_frag_lift /=.
        rewrite !option_fmap_bind. rewrite /compose /=.
        rewrite -!option_bind_assoc.
        rewrite -!agree_option_map_compose.
        apply option_bind_proper.
        { intros ??->. auto. }
        apply agree_option_map_ext.
        { intros ??? ->. auto. }
        intros ?. rewrite Hind. auto.
    - split;simpl;auto.
      rewrite /gMapTrans_frag_lift /=.
      rewrite map_imap_compose.
      intros i.
      rewrite !map_lookup_imap.
      destruct (view_frag_proj !! i) eqn:Hlook;rewrite Hlook/=//.
      destruct c;simpl.
      rewrite /map_trans_frag_lift /=.
      rewrite !option_fmap_bind. rewrite /compose /=.
      rewrite -!option_bind_assoc.
      rewrite -!agree_option_map_compose.
      apply option_bind_proper.
      { intros ??->. auto. }
      apply agree_option_map_ext.
      { intros ??? ->. auto. }
      intros ?. rewrite Hind. auto.
  Qed.
        
  Lemma map_entry_lift_gmap_view_auth dq m map_entry :
    map_entry_lift_gmap_view map_entry (gmap_view_auth dq (to_agree <$> m)) =
    gmap_view_auth dq (to_agree <$> map_imap map_entry m).
  Proof.
    rewrite /map_entry_lift_gmap_view /fmap_view /fmap_pair /=.
    rewrite agree_map_to_agree.
    rewrite /gmap_view_auth /view_auth.
    f_equiv; last done.
    f_equiv.
    f_equiv.
    f_equiv.
    rewrite /gMapTrans_auth_lift ?map_fmap_imap.
    apply: map_imap_ext.
    intros i.
    rewrite lookup_fmap.
    destruct (m !! i); simpl; simplify_eq; last done.
    rewrite /map_trans_auth_lift agree_option_map_to_agree /=.
    f_equiv.
    done.
  Qed.

  Lemma map_entry_lift_gmap_view_frag k dq v map_entry :
    map_entry_lift_gmap_view map_entry (gmap_view_frag k dq (to_agree v)) =
    from_option (λ v', gmap_view_frag k dq (to_agree v')) (◯V ∅) (map_entry k v).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    unfold from_option. rewrite /gMapTrans_frag_lift.
    rewrite -insert_empty. destruct (map_entry k v) eqn:Hsome.
    - erewrite map_imap_insert_Some;auto.
      simpl. rewrite agree_option_map_to_agree Hsome /= //.
    - rewrite map_imap_insert_None;auto.
      simpl. rewrite agree_option_map_to_agree Hsome /= //.
  Qed.

  Lemma map_entry_lift_gmap_view_compose map_entry1 map_entry2 `{!MapTrans map_entry1} `{!MapTrans map_entry2} :
    ∀ x, ((map_entry_lift_gmap_view map_entry1) ∘ (map_entry_lift_gmap_view map_entry2)) x ≡
          map_entry_lift_gmap_view (λ k v, (map_entry2 k) v ≫= (map_entry1 k)) x.
  Proof.
    intros x.
    destruct x.
    split;simpl.
    - destruct view_auth_proj;simpl;auto.
      destruct p;simpl. f_equiv.
      split;simpl;auto.
      rewrite -!agree_map_compose.
      apply agree_map_ext.
      { apply _. }
      intros m. simpl.
      rewrite /gMapTrans_auth_lift map_imap_compose.
      apply: utils.map_imap_ext => i.
      rewrite /map_trans_auth_lift /=.
      destruct (m !! i) eqn:Heq; rewrite Heq /=; auto.
      rewrite -!agree_option_map_compose //.
    - rewrite /gMapTrans_frag_lift.
      rewrite map_imap_compose. intros k.
      rewrite !map_lookup_imap.
      destruct (view_frag_proj !! k) eqn:Hk;rewrite Hk;auto.
      simpl. destruct c. rewrite /map_trans_frag_lift /=.
      rewrite !option_fmap_bind. rewrite /compose /=.
      rewrite -!option_bind_assoc.
      rewrite -!agree_option_map_compose.
      auto.
  Qed.

  Lemma map_entry_lift_gmap_equiv map_entry1 map_entry2 `{!MapTrans map_entry1} `{!MapTrans map_entry2} :
    (∀ l v, map_entry1 l v ≡ map_entry2 l v) ->
    ∀ x, map_entry_lift_gmap_view map_entry1 x ≡ map_entry_lift_gmap_view map_entry2 x.
  Proof.
    intros Heq.
    intros x.
    destruct x.
    split;simpl.
    - destruct view_auth_proj;simpl;auto.
      destruct p;simpl. f_equiv.
      split;simpl;auto.
      apply agree_map_ext;[apply _|].
      intros a0. intros i.
      rewrite !map_lookup_imap.
      destruct (a0 !! i) eqn:Ha;rewrite Ha;simpl;auto.
      apply agree_option_map_ext;[apply _|].
      auto.
    - rewrite /gMapTrans_frag_lift.
      intros i. rewrite !map_lookup_imap.
      destruct (view_frag_proj !! i) eqn:Ha;rewrite Ha;simpl;auto.
      destruct c;simpl.
      f_equiv.
      { intros ??->. auto. }
      apply agree_option_map_ext;[apply _|].
      auto.
  Qed.
  
  (* Lemma map_entry_lift_gmap_contractive map_entry `{!MapTrans map_entry} : *)
  (*   ∀ x, map_entry_lift_gmap_view map_entry x ≼ x. *)
  (* Proof. *)
  (*   intros x. exists (map_entry_lift_gmap_view_no_auth (map_entry_flip map_entry) x). *)
  (*   destruct x;split. *)
  (*   - simpl. rewrite /op /cmra_op /= /option_op_instance union_with_None_r. *)
  (*     destruct view_auth_proj;auto. destruct p;simpl. *)

  (*     simpl. auto. *)
  
End map_entry.
