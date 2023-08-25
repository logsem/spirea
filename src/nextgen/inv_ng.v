(* Wrappers around Perennials' invariant/fupd resources that survive crashes. *)

From iris.algebra Require Import gmap auth agree gset coPset list vector excl.
From iris.base_logic Require Import lib.later_credits.
From Perennial.algebra Require Import mlist.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic.lib Require Import wsat.

Search "invGS".
(* From Perennial.program_logic Require Export weakestpre. *)
(* From Perennial.program_logic Require Export crash_lang. *)

From self.nextgen Require Import nextgen_promises_ng.

Export invGS.

(* Below are the resources used in Perennial for fupd, but where [inG] has been
 * replaced with [inG]. *)

Class ngFmlistG (A : Type) {Heq: EqDecision A} Σ Ω :=
  { ngFmlist_inG :> ngInG Σ Ω (fmlistUR A) }.

#[global]
Instance ngFmlistG_unwrap A {Heq : EqDecision A} Σ Ω :
    ngFmlistG A Σ Ω → fmlistG A Σ := {
  fmlist_inG := _
}.

(** The ghost state for later credits *)
Class ngLcGpreS (Σ : gFunctors) Ω := NgLcGpreS {
  ngLcGpreS_inG : ngInG Σ Ω (authR natUR)
}.

#[global]
(** The ghost state for later credits *)
Instance ngLcGpreS_unwrap (Σ : gFunctors) Ω (l : ngLcGpreS Σ Ω) : lcGpreS Σ := {
  lcGpreS_inG := @ngInG_inG _ _ _ ngLcGpreS_inG;
}.

Class ngLcGS (Σ : gFunctors) Ω := NgLcGS {
  ngLcGS_inG :> ngInG Σ Ω (authR natUR);
  ngLcGS_name : gname;
}.

#[global]
Instance ngLcGS_unwrap Σ Ω : ngLcGS Σ Ω → lcGS Σ := {
  lcGS_inG := _;
  lcGS_name := ngLcGS_name;
}.

(* Global Hint Mode ngLcGS - : typeclass_instances. *)
(* Local Existing Instances lcGS_inG lcGpreS_inG. *)

Definition invR Σ :=
  authR (gmapUR positive
    (prodR (agreeR (prodO (listO (laterO (iPropO Σ))) bi_schemaO))
      (optionR (prodR fracR (agreeR (listO (laterO (iPropO Σ)))))))).

Class ngInvGpreS (Σ : gFunctors) Ω : Set := WsatPreG {
  ngInv_inPreG :> ngInG Σ Ω (invR Σ);
  ngEnabled_inPreG :> ngInG Σ Ω coPset_disjR;
  ngDisabled_inPreG :> ngInG Σ Ω (gset_disjR positive);
  ngMlist_inPreG :> ngFmlistG (invariant_level_names) Σ Ω;
  ngInv_lcPreG :> ngLcGpreS Σ Ω;
}.

#[global]
Program Instance ngInvGpreS_unwrap Σ Ω : ngInvGpreS Σ Ω → invGpreS Σ := {
  inv_inPreG := _;
  enabled_inPreG := _;
  disabled_inPreG := _;
  mlist_inPreG := _;
  inv_lcPreG := _;
}.

Class ngInvGS (Σ : gFunctors) Ω : Set := WsatG {
  ngInv_inG :> ngInvGpreS Σ Ω;
  ngInvGS_lc :> ngLcGS Σ Ω;
  ngInv_list_name : gname;
  ngEnabled_name : gname;
  ngDisabled_name : gname;
}.

#[global]
Instance ngInvGS_unwrap {Σ Ω} : ngInvGS Σ Ω → invGS Σ := {
  inv_inG := _;
  invGS_lc := _;
  inv_list_name := ngInv_list_name;
  enabled_name := ngEnabled_name;
  disabled_name := ngDisabled_name;
}.

(* #[global] *)
Definition ngInvG_combine {Σ Ω} (p : ngInvGpreS Σ Ω) (i : invGS Σ) : ngInvGS Σ Ω := {|
  ngInv_inG := p;
  ngInvGS_lc := NgLcGS _ _ (@ngLcGpreS_inG _ _ ngInv_lcPreG) lcGS_name;
  ngInv_list_name := inv_list_name;
  ngEnabled_name := enabled_name;
  ngDisabled_name := disabled_name;
|}.

Lemma ngInv_combine_unwrap {Σ Ω} (p : ngInvGpreS Σ Ω) (i : invGS Σ) :
  i = ngInvGS_unwrap (ngInvG_combine p i).
Proof.
  unfold ngInvG_combine, ngInvGS_unwrap.
  destruct i. f_equiv; try done.
Admitted.

Section ngInv_lemmas.
  Context `{!ngInvGS Σ Ω}.

  Lemma nextgen_lc k : £ k ⊢ ⚡==> £ k.
  Proof.
    iIntros "O".
    rewrite later_credits.lc_unseal /later_credits.lc_def.
    iModIntro.
    done.
  Qed.

  #[global]
  Instance into_nextgen_lc k : IntoNextgen _ _ := nextgen_lc k.

End ngInv_lemmas.
