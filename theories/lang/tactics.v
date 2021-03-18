From stdpp Require Import fin_maps.
From self.lang Require Import lang.
From iris Require Import options.

(* This tactics performs inversion in [thread_step], and its constituents
[head_step] and [mem_step]. *)
Ltac inv_thread_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : mem_step ?e _ _ _ _ |- _ =>
    try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
    and should thus better be avoided. *)
    inversion H; subst; clear H
  | H : nvm_lang.head_step ?e _ _ _ _ |- _ =>
    try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
    and should thus better be avoided. *)
    inversion H; subst; clear H
  | H : thread_step ?e _ _ _ _ _ |- _ =>
    try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
    and should thus better be avoided. *)
    inversion H; subst; clear H
  end.
