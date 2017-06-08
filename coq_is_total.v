(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import utils decidable_t nat_minimizer.
Require Import recalg ra_rel ra_ca ra_sem_eq ra_ca_props.

Set Implicit Arguments.

Section Coq_is_total.
  
  Variables (k : nat) (f : recalg k) (Hf : forall v, exists x, [|f|] v x).

  Let coq_f v : { n : nat & { x | [f;v] -[n>> x } }.
  Proof.
    apply nat_reify_t.
    apply ra_ca_decidable_t.
    destruct (Hf v) as (x & Hx).
    apply ra_ca_correct in Hx.
    destruct Hx as (n & ?).
    exists n; exists; exists x; trivial.
  Qed.
  
  Let cf v := proj1_sig (projT2 (coq_f v)).
  
  Let Hcf v : [|f|] v (cf v).
  Proof.
    apply ra_ca_correct.
    exists (projT1 (coq_f v)).
    apply (proj2_sig (projT2 (coq_f v))).
  Qed.
  
  Theorem Coq_is_total : { cf | forall v, [|f|] v (cf v) }.
  Proof.
    exists cf; auto.
  Qed.

End Coq_is_total.

Check Coq_is_total.
Print Assumptions Coq_is_total.
