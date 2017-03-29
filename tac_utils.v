(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Eqdep_dec.

Ltac injc H := injection H; clear H;
               repeat match goal with 
                 |- _ = _ -> _ => 
               intro; subst end.

Ltac eqgoal := 
  match goal with 
    |- ?a -> ?b => replace a with b; auto 
  end.
  
Ltac inst H :=
  let K := fresh in
  match goal with 
    | [ G : ?x -> _ |- _ ] => 
    match G with 
      H => assert (x) as K; [ clear H | specialize (H K); clear K ]
    end 
  end.

Fact eq_gen { X } (P : X -> Type) x : (forall y, y = x -> P y) -> P x.
Proof. intros H; apply H, eq_refl. Qed.
  
Ltac gen_eq t := apply eq_gen with (x := t).

Fact eq_nat_pirr (n m : nat) (H1 H2 : n = m) : H1 = H2.
Proof. apply UIP_dec, eq_nat_dec. Qed.

(* Remove identities of the form H : n = n :> nat and eliminates H 
   by replacing it with eq_refl *)

Ltac natid :=
    repeat
    match goal with 
     |  [ H: ?x = ?x :> nat |- _ ]  => let G := fresh 
                                in generalize (@eq_nat_pirr _ _ H eq_refl); 
                                   intros G; subst H 
    end;
    simpl eq_rect in * |- *.

