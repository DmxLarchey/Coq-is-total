(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import decidable_t.

Set Implicit Arguments.

Section nat_reify.

  (** This is UNBOUNDED minimization when a certificate of termination
     is provided 
     
     But in this simpler case, we do not show that the minimum
     is computed 
     
  *)

  Variable P : nat -> Prop.
  Hypothesis HP : forall n, { P n } + { ~ P n }.
  
  Let R x y := x = S y /\ ~ P y.
  
  Let P_Acc_R x : P x -> Acc R x.
  Proof.
    constructor; intros ? (_ & []); auto.
  Qed.
  
  Let Acc_R_dec x : Acc R (S x) -> Acc R x.
  Proof.
    constructor; intros ? (? & _); subst; auto.
  Qed.
  
  Let Acc_R_zero x : Acc R x -> Acc R 0.
  Proof.
    induction x; auto.
  Qed.
  
  Let Acc_P : forall x (Hx : Acc R x), { m | P m }.
  Proof.
    refine (fix loop x Hx { struct Hx } := _).
    destruct (@HP x) as [ H | H ].
    exists x; trivial.
    destruct (loop (S x)) as (m & H2).
    destruct Hx as [ Hx ].
    apply Hx; split; trivial.
    exists m; trivial.
  Qed.

  Theorem nat_reify : (exists x, P x) -> { x | P x }.
  Proof.
    intros H; apply (@Acc_P 0).
    destruct H as (x & Hx).
    apply (@Acc_R_zero x), P_Acc_R, Hx.
  Qed.
  
  (* Same as nat_reif but we show that the computed value
     is the minimum *)
     
  Let Acc_P_min : forall x (Hx : Acc R x), { m | P m /\ forall y, P y -> y < x \/ m <= y }.
  Proof.
    refine (fix loop x Hx { struct Hx } := _).
    destruct (HP x) as [ H | H ].
    exists x; split; trivial.
    intros y _; destruct (le_lt_dec x y); auto.
    destruct (loop (S x)) as (m & H1 & H2).
    destruct Hx as [ Hx ].
    apply Hx; red; auto.
    clear loop.  (* we do not want the automatic tactics to use that one *)
    exists m; split; auto.
    intros y Hy; destruct (H2 _ Hy).
    destruct (eq_nat_dec x y) as [ | ].
    subst; contradict Hy; auto.
    abstract omega.
    abstract omega.
  Qed.
  
  Theorem nat_minimizer : (exists x, P x) -> { x | P x /\ forall y, P y -> x <= y }.
  Proof.
    intros H.
    destruct (@Acc_P_min 0) as (m & H1 & H2).

    destruct H as (x & Hx).
    apply (@Acc_R_zero x), P_Acc_R, Hx.
    
    exists m; split; auto.
    intros y Hy; specialize (H2 _ Hy); abstract omega.
  Qed.
  
End nat_reify.

Section nat_reify_t.

  (* The same but with nat -> Type predicates instead of nat -> Prop *)

  Variable P : nat -> Type.
  Hypothesis HP : forall n, decidable_t (P n).
  
  Let R x y := x = S y /\ ~ inhabited (P y).
  
  Let P_Acc_R x : P x -> Acc R x.
  Proof.
    intros H.
    constructor. 
    intros ? (_ & []).
    exists; auto.
  Qed.
  
  Let Acc_R_dec x : Acc R (S x) -> Acc R x.
  Proof.
    constructor; intros ? (? & _); subst; auto.
  Qed.
  
  Let Acc_R_zero x : Acc R x -> Acc R 0.
  Proof.
    induction x; auto.
  Qed.
 
  Let Acc_P : forall x (Hx : Acc R x), sigT P.
  Proof.
    refine (fix loop x Hx { struct Hx } := _).
    destruct (@HP x) as [ H | H ].
    exists x; trivial.
    destruct (loop (S x)) as (m & H2).
    destruct Hx as [ Hx ].
    apply Hx; split; trivial.
    intros []; tauto.
    exists m; trivial.
  Qed.
  
  Theorem nat_reify_t : (exists x, inhabited (P x)) -> { x : nat & P x }.
  Proof.
    intros H; apply (@Acc_P 0).
    destruct H as (x & [ Hx ]).
    apply (@Acc_R_zero x), P_Acc_R, Hx.
  Qed.
  
End nat_reify_t.
