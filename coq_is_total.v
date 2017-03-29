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
  
  Theorem Coq_is_total : { cf | forall v, [|f|] v (cf v) }.
  Proof.
    exists (fun v => proj1_sig (projT2 (coq_f v))).
    intros v; apply ra_ca_correct.
    exists (projT1 (coq_f v)).
    apply (proj2_sig (projT2 (coq_f v))).
  Qed.

End Coq_is_total.

Check Coq_is_total.
Print Assumptions Coq_is_total.

Section Russell.

  Variable (X : Type) (s : X -> (X -> Prop)) (Hs : forall P, exists x, forall y, s x y <-> P y).
  
  Let Q x := ~ s x x.
  
  Theorem Russell_Paradox : False.
  Proof.
    destruct (Hs Q) as (q & Hq).
    generalize (Hq q); unfold Q; tauto.
  Qed.

End Russell.

Require Import Omega.
 
Section Russell_nat.

  (* no surjection nat -> (nat -> nat) upto extensional equality *)

  Variable (s : nat -> (nat -> nat)) (Hs : forall f, exists n, forall x, s n x = f x).
  
  Let f n := 1 + s n n.
  
  Theorem Russell_nat : False.
  Proof.
    destruct (Hs f) as (n & Hn).
    generalize (Hn n); unfold f; omega.
  Qed.
  
End Russell_nat.

Require Import ChoiceFacts.

Section Russell_nat_choice.

  Hypothesis FC : FunctionalChoice.
  
  (* R describes a surjective map nat -> (nat -> nat) *)

  Variable (R : nat -> (nat -> nat) -> Prop)
           (HR1 : forall n, exists f, R n f) 
           (HR2 : forall n f g, R n f -> R n g -> forall x, f x = g x)
           (HR3 : forall f, exists g n, R n g /\ forall x, f x = g x).
           
  Theorem Russell_Choice : False.
  Proof.
    destruct (FC R) as (s & Hs); auto.
    apply Russell_nat with s.
    intros f.
    destruct (HR3 f) as (g & n & H1 & H2).
    exists n; intros x; rewrite H2; revert x.
    apply HR2 with n; auto.
  Qed.
  
End Russell_nat_choice.
 
Section enums.

  (* It is possible to build this surjective map
     from nat to forall k, recalg k 
     
     These are assumed here but it is not too difficult
     to implement them 
   *)

  Variable ra_dec : nat -> forall k, recalg k.
  Variable ra_enc : forall k, recalg k -> nat.
  Hypothesis ra_dec_enc : forall k (f : recalg k), f = ra_dec (ra_enc f) k.
  Hypothesis ra_enc_dec : forall k n, n = ra_enc (ra_dec n k).

  Section contradiction_1.

    Hypothesis Church_thesis : forall f : nat -> nat, { e | forall v : vec nat 1, [|e|] v (f (vec_head v)) }.
    
    Let diag f := ra_enc (proj1_sig (Church_thesis f)).
    
    (* diag provides an injective map : (nat -> nat) -> nat 
       injectivity upto extensional equality
     *)
    
    Fact diag_inj f g : diag f = diag g -> forall x, f x = g x.
    Proof.
      unfold diag.
      destruct (Church_thesis f) as (ef & Hef).
      destruct (Church_thesis g) as (eg & Heg).
      simpl.
      intros H.
      apply f_equal with (f := fun n => @ra_dec n 1) in H.
      do 2 rewrite <- ra_dec_enc in H; subst eg.
      intros x.
      generalize (Hef (x##vec_nil)) (Heg (x##vec_nil)).
      simpl.
      apply ra_rel_fun.
    Qed.
    
    (* Can we derive a contradiction from such an injection *)

  End contradiction_1.
    
End enums.