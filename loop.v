(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** 
    
    The goal of this file is to show that one cannot assume
    that Coq has strong normalisation or even normalisation
    if axioms are added, even if only at the level of Prop.
    
    Perhaps it is possible to show normalisation meta-theoretically
    for some given set of axioms, or even, provided that those axioms
    are 1-consistent (have a model), but I am not sure.
    
    For the proofs of strong normalization or normalization that I have 
    heard of (such as Mellies and Werner's), these proofs work for 
    subsets of Coq which do not include axioms even if only in Prop. 
    
**)

Require Import Wf.

Definition forget (n : nat) := 0.
Fixpoint nat_loop (n : nat) := forget (nat_loop n).

Fixpoint loop X Y x (H : Acc (@eq X) x) : Y := 
  loop _ Y _ (match H with Acc_intro _ H => H x eq_refl end).


Definition undefined : False -> forall X, X.
Proof.
  intros H X.
  apply (loop _ _ tt).
  destruct H.
Defined.

Extraction "loop.ml" nat_loop loop undefined.

(** 

---> The extraction results in the following 

(** val forget : nat -> nat **)

let forget _ =
  O

(** val nat_loop : nat -> nat **)

let rec nat_loop n =
  forget (nat_loop n)

---> Obviously nat_loop is only normalizing
     but not strongly normalizing

---> Propositional guards that ensure the
     termination of function are erased at
     extraction and a function like loop
     is extracted into a non-terminating 
     term 

(** val loop : 'a1 -> 'a2 **)

let rec loop x =
  loop x

(** val undefined : 'a1 -> 'a2 **)

let undefined x =
  loop x

---> Hence is the set of Prop-level axioms
     chosen is inconsistent (can derive False)
     then, we can built a non-terminating 
     term within Coq

*)