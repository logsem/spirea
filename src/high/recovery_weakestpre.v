(* Implementation of the recovery weakest precondition for NvmLang. *)
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require Import recovery_weakestpre.
From Perennial.program_logic Require Import recovery_adequacy.

From self Require Import view.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop.
From self.high Require Import resources weakestpre crash_weakestpre.

Set Default Proof Using "Type".

Notation pbundleG := recovery_weakestpre.pbundleG.

Notation perennialG := recovery_weakestpre.perennialG.

(* This approach does not seem to work.
Definition wpr `{hG : !nvmG Σ} `{hC : !crashG Σ} (s : stuckness) (k : nat) E
           (e : expr) (rec : expr) (Φ : val → dProp Σ) (Φinv : nvmG Σ → dProp Σ) (Φc : nvmG Σ -> val -> dPropO Σ) :=
  MonPred (λ V,
    ⌜ ∀ Hc t, Objective (Hc t Φc) ⌝ ∗
    ∀ TV,
      ⌜ V ⊑ TV ⌝ -∗
      validV (store_view TV) -∗
      interp -∗
      wpr s k (* hC ({| recovery_weakestpre.pbundleT := nvm_get_names Σ _ |}) *) E
        (ThreadState e TV)
        (ThreadState rec (∅, ∅, ∅))
        (λ res,
          let '(ThreadVal v TV') := res in Φ v TV')
        (λ _, True%I)
        (λ hG res,
          let '(ThreadVal v TV') := res in Φc (hG) v TV')
  )%I. *)

Record nvm_high_names := {
  name_abs_history : gname;
  name_predicates : gname;
}.

Definition nvm_high_get_names Σ (hG : nvmHighG Σ) : nvm_high_names :=
  {| name_abs_history := abs_history_name;
     name_predicates := predicates_name |}.

Canonical Structure nvm_high_namesO := leibnizO nvm_high_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_high_update Σ (hG : nvmHighG Σ) (names : nvm_high_names) :=
  {| abs_history_name := names.(name_abs_history);
     predicates_name := names.(name_predicates);
     ra_inG := hG.(@ra_inG _);
     ra'_inG := hG.(@ra'_inG _); |}.

Record nvm_names := {
  name_base_names : nvm_base_names; (* Names used by the base logic. *)
  name_high_names : nvm_high_names; (* Names used by the high-level logic. *)
}.

Definition nvm_get_names Σ (hG : nvmG Σ) : nvm_names :=
  {| name_base_names := nvm_base_get_names _ nvmG_baseG;
     name_high_names := nvm_high_get_names _ nvmG_highG |}.

Canonical Structure nvm_namesO := leibnizO nvm_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_update Σ (hG : nvmG Σ) (Hinv : invG Σ) (Hcrash : crashG Σ) (names : nvm_names) :=
  {| nvmG_baseG := nvm_base_update _ hG.(@nvmG_baseG _) Hinv Hcrash names.(name_base_names);
     nvmG_highG := nvm_high_update _ hG.(@nvmG_highG _) names.(name_high_names) |}.

(* The recovery WP is parameterized by two predicates: [Φ] is the postcondition
   for normal non-crashing execution and [Φr] is the postcondition satisfied in
   case of a crash. *)
Definition wpr_pre Σ (s : stuckness) (k : nat)
    (wpr : crashG Σ -d> nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ) :
  crashG Σ -d> nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ :=
  λ Hc hG E e rec Φ Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step nvm_crash_lang σ σ') n,
        ⎡ interp -∗ state_interp σ n ={E}=∗ ▷ ∀ (Hc1 : crashG Σ) q, NC q ={E}=∗
          ∃ (names : nvm_names),
            let hG := (nvm_update _ hG _ Hc names) in
              state_interp σ 0 ∗
              (monPred_at (wpr Hc1 hG E rec rec (λ v, Φr hG v) Φr) (∅, ∅, ∅)) ∗
              NC q ⎤
          }})%I.

Local Instance wpr_pre_contractive {Σ} s k: Contractive (wpr_pre Σ s k).
Proof.
  rewrite /wpr_pre. intros ??? Hwp ???????.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def {Σ} (s : stuckness) k := fixpoint (wpr_pre Σ s k).

Definition wpr_aux {Σ} : seal (@wpr_def Σ). by eexists. Qed.

Definition wpr `{nvmG Σ} s k := wpr_aux.(unseal) s k _ _.
