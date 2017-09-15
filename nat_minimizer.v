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
  
  Let Acc_exists_eq x : Acc R x <-> exists i, x <= i /\ P i.
  Proof.
    split.
    
    induction 1 as [ x Hx IHx ].
    destruct (HP x).
    exists x; auto.
    destruct IHx with (S x) as (i & ? & ?); 
      [ | exists i ]; split; auto; omega.
    
    intros (i & H1 & H2).
    apply P_Acc_R in H2.
    revert H2.
    replace i with ((i-x)+x) by omega.
    generalize (i-x); clear i H1. 
    intros i; induction i; auto.
  Qed.
  
  (* @Acc_inv x Hx F is a proof of Acc R (S x) which is
     *structurally simpler* than Hx, the given proof of Acc R x 
   *) 
  
  Let Acc_inv x (Hx : Acc R x) (F : ~ P x) : Acc R (S x).
  Proof.
    refine (match Hx with 
      | Acc_intro _ H => H _ _  (* H : forall y, R y x -> Acc R y *)
    end).
    split; trivial.
  Qed.
  
  Let Acc_inv' x (Hx : Acc R x) (F : ~ P x) : Acc R (S x) :=
    let F' := conj eq_refl F     (* F'  : R (S x) x   *)
    in match Hx with 
      | Acc_intro _ H => H _ F'  (* H : forall y, R y x -> Acc R y *)
    end.
  
  (* Hence the following fixpoint type-checks 
     with Hx as structurally decreasing argument 
   *)
  
  Fixpoint Acc_P x (Hx : Acc R x) : { m | P m } :=
    match HP x with
      | left  T => exist _ x T
      | right F => @Acc_P (S x) (@Acc_inv x Hx F)
    end.
  
  Print Acc_P.
  
  Let Acc_P' := fix Acc_P' x (Hx : Acc R x) : { m | P m } :=
    match HP x with
      | left  T => exist _ x T
      | right F => 
        let Hx' := match Hx with 
              Acc_intro _ H => H (S x) (conj eq_refl F) 
        end in Acc_P' (S x) Hx'
    end.
    
  Print Acc_P'.

  Let Acc_P'' : forall x (Hx : Acc R x), { m | P m }.
  Proof.
    refine (fix loop x Hx { struct Hx } := _).
    destruct (@HP x) as [ H | H ].
    exists x; trivial.
    destruct (loop (S x)) as (m & H2).
    destruct Hx as [ Hx ].
    apply Hx; split; trivial.
    exists m; trivial.
  Qed.
  
  Print Acc_P''.

  Theorem nat_reify : (exists x, P x) -> { x | P x }.
  Proof.
    intros H. 
    apply Acc_P with 0.
    destruct H as (x & Hx).
    apply Acc_R_zero with x, P_Acc_R, Hx.
  Qed.

  (* Same as nat_reif but we show that the computed value
     is the minimum *)
     
  Let Acc_P_min : forall x (Hx : Acc R x), { m | P m /\ forall y, P y -> y < x \/ m <= y }.
  Proof.
    refine (fix Acc_P_min x Hx { struct Hx } := 
      match HP x with 
        | left T  => exist _ x _
        | right F => match Acc_P_min (S x) _ with exist _ m H => exist _ m _ end
      end).
      
    split; trivial.
    intros y _; destruct (le_lt_dec x y); auto.
    
    destruct Hx as [ Hx ].
    apply Hx; red; auto.
    
    clear Acc_P_min.  (* we do not want the automatic tactics to use that one *)
    destruct H as [ H1 H2 ].
    split; trivial.
    intros y Hy.
    destruct (eq_nat_dec x y) as [ | ].
    subst; contradict F; trivial.
    specialize (H2 _ Hy); omega.
  Qed.
  
  Print Acc_P_min.
  
  Theorem nat_minimizer : (exists x, P x) -> { x | P x /\ forall y, P y -> x <= y }.
  Proof.
    intros H.
    destruct Acc_P_min with 0 as (m & H1 & H2).

    destruct H as (x & Hx).
    apply Acc_R_zero with x, P_Acc_R, Hx.
    
    exists m; split; auto.
    intros ? Hy; specialize (H2 _ Hy); omega.
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
  
  Let Acc_inv x : Acc R x -> (P x -> False) -> Acc R (S x).
  Proof.
    intros [ Hx ] F; apply Hx; split.
    * reflexivity.
    * intros [ t ]; exact (F t).
  Defined.
  
  Print Acc_inv.
 
  Let Acc_P := fix Acc_P x (Hx : Acc R x) : sigT P :=
    match HP x with
      | inl T => existT _ x T
      | inr F => @Acc_P (S x) (@Acc_inv x Hx F)
    end.
  
  Theorem nat_reify_t : (exists x, inhabited (P x)) -> { x : nat & P x }.
  Proof.
    intros H; apply Acc_P with 0.
    destruct H as (x & [ Hx ]).
    apply Acc_R_zero with x, P_Acc_R, Hx.
  Qed.
  
End nat_reify_t.

Section functional_countable_decidable_choice.

  Variable (X : Type) (R : X -> nat -> Prop) (HR : forall x n, { R x n } + { ~ R x n }).
  
  Theorem FunctionalCountableDecidableChoice : (forall x, exists n, R x n) -> { f | forall x, R x (f x) }.
  Proof.
    intros H.
    set (f x := @nat_reify (R x) (HR x) (H x)).
    exists (fun x => proj1_sig (f x)).
    intros x.
    apply (proj2_sig (f x)).
  Qed.
  
End functional_countable_decidable_choice.

Check FunctionalCountableDecidableChoice.

  
