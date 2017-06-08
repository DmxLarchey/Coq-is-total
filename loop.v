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
    
    The proofs of strong normalization or normalization that I have 
    heard of work for subsets of Coq which do not include axioms 
    
**)

Axioms F : False.

Section loop.

  Variable X Y : Type.

  Fixpoint loop (x : X) (Hx : Acc (fun _ _ => True) x) { struct Hx } : Y.
  Proof.
    refine (loop x _).
    destruct Hx as [ Hx ].
    apply Hx; trivial.
  Defined.
  
  Definition undefined : X -> Y.
  Proof.
    intros x; apply (loop x); destruct F.
  Defined.
  
End loop.

Extraction "loop.ml" loop undefined.

(** The extraction results in the following obviously
    non terminating functions 

(** val loop : 'a1 -> 'a2 **)

let rec loop x =
  loop x

(** val undefined : 'a1 -> 'a2 **)

let undefined x =
  loop x

*)