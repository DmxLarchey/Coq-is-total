(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.
Require Import utils.

Set Implicit Arguments.

Section recursor.

  Variables (F : nat -> Prop) (Ffun : forall n m, F n -> F m -> n = m) (HF : ex F -> sig F)
            (G : nat -> nat -> nat -> Prop) (Gfun : forall x y n m, G x y n -> G x y m -> n = m)
            (HG : forall x y, ex (G x y) -> sig (G x y)).
  
  Fixpoint recursor n x := 
    match n with
      | 0   => F x
      | S n => exists y, recursor n y /\ G n y x
      end.

  Fact recursor_fun n x y : recursor n x -> recursor n y -> x = y.
  Proof.
    revert x y; induction n as [ | n IHn ]; simpl; auto.
    intros x y (a & H1 & H2) (b & H3 & H4).
    specialize (IHn _ _ H1 H3); subst b.
    revert H2 H4; apply Gfun.
  Qed.

  Definition recursor_coq n : ex (recursor n) -> sig (recursor n).
  Proof.
    induction n as [ | n IHn ]; simpl.
    apply HF.
    intros Hn.
    destruct IHn as (xn & Hxn).
    destruct Hn as (_ & y & ? & _); exists y; auto.
    destruct (@HG n xn) as (xSn & HxSn).
    destruct Hn as (x & y & H1 & H2).
    exists x; revert H2; eqgoal; do 2 f_equal.
    revert Hxn H1; apply recursor_fun.
    exists xSn, xn; auto.
  Defined.

End recursor.

