(* Implementation of the recovery weakest precondition for NvmLang. *)
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require recovery_weakestpre.

From self Require Import view.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop weakestpre crash_weakestpre.

Set Default Proof Using "Type".

Notation pbundleG := recovery_weakestpre.pbundleG.

Notation perennialG := recovery_weakestpre.perennialG.

(* A recovery WP is parameterized by three predicates: [Φ] is the postcondition
   for normal non-crashing execution. [Φr] is the postcondition satisfied in
   case of a crash. Finally, [Φinv] is a condition that holds at each restart
   point. *)
Check expr_wpc.

(* This approach does not seem to work. *)
(*
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
  )%I.
*)

Definition wpr_pre `{nvmG Σ} `{hC : !crashG Σ} (s : stuckness) (k : nat)
    (wpr : crashG Σ -d> nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ) :
  crashG Σ -d> nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (crashG Σ -d> nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ :=
  λ Hc0 t0 E e rec Φ Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step _ σ σ') n,
        ⎡ interp -∗ state_interp σ n ={E}=∗ ▷ ∀ Hc1 q, NC q ={E}=∗
          ∃ names,
            let hG := (nvm_update _ _ _ Hc1 (@recovery_weakestpre.pbundleT _ _ names)) in
            state_interp σ 0 ∗
            wpr Hc1 hG E rec rec (λ v, Φr hG v) Φinv Φr
            NC q ⎤
          }})%I.
        True
     }})%I.
        (* ⎡interp -∗ global_state_interp g ns κs ={E}=∗  ▷ ∀ Hc1 q, NC q ={E}=∗ ∃ t1 *)
        (*     (Hsame_inv: @iris_invG _ _ (recovery_weakestpre.perennial_irisG Hc1 t1) = *)
        (*                 @iris_invG _ _ (recovery_weakestpre.perennial_irisG Hc0 t0)), *)
        (*   □ (∀ g ns κs, @global_state_interp _ _ (recovery_weakestpre.perennial_irisG Hc1 t1) g ns κs ∗-∗ *)
        (*                 @global_state_interp _ _ (recovery_weakestpre.perennial_irisG Hc0 t0) g ns κs) ∗ *)
        (*   state_interp σ' 0 ∗ *)
        (*   global_state_interp g (S ns) κs ∗ *)
        (*   (monPred_at (wpr Hc1 t1 E rec rec (λ v, Φr Hc1 t1 v) Φr) ⊥) ∗ NC q⎤}})%I. *)

Local Instance wpr_pre_contractive `{!nvmG Σ} s k: Contractive (wpr_pre s k).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp H2crash t E1 e1 rec Φ Φinv Φc.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{!perennialG Λ CS T Σ} (s : stuckness) k :
  crashG Σ → pbundleG T Σ → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) →
  (crashG Σ → pbundleG T Σ → iProp Σ) →
  (crashG Σ → pbundleG T Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre s k).
Definition wpr_aux `{!perennialG Λ CS T Σ} : seal (@wpr_def Λ CS T Σ _). by eexists. Qed.
Definition wpr `{!perennialG Λ CS T Σ} := wpr_aux.(unseal).
Definition wpr_eq `{!perennialG Λ CS T Σ} : wpr = @wpr_def Λ CS T Σ _ := wpr_aux.(seal_eq).
