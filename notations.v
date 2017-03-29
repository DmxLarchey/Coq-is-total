(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Notation rel := (fun A B => A -> B -> Prop).
Notation inv := ((fun X Y (R : X -> Y -> Prop) x y => R y x) _ _).

Notation "R 'inc1' S" := (forall x, R x -> S x) (at level 72).
Notation "R 'inc2' S" := (forall x y, R x y -> S x y) (at level 72). 

Notation " R 'o'    S" := (fun x z => exists y, R x y /\ S y z) (at level 65).

Notation " R 'cap2' S " := (fun x y => R x y /\ S x y) (at level 65).
Notation " R 'cup2' S " := (fun x y => R x y \/ S x y) (at level 65). 

Definition total { X Y } (R : X -> Y -> Prop) : Prop := forall v, exists x, R v x.
Definition functional { X Y } (R : X -> Y -> Prop) : Prop := forall v x y, R v x -> R v y -> x = y.

