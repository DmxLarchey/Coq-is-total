(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Relations Wellfounded.

Require Import utils nat_minimizer .

Set Implicit Arguments.

Section weighted_reif.

  Variable (X : Type) (P : X -> Prop).
  
  (* We suppose that P x can be read as there exists a weight n s.t. Q n x holds
     and that Q n is finite at a given weight n *)
  
  Variable (Q : nat -> X -> Prop).
  Hypothesis HP : forall x, P x <-> exists n, Q n x.
  Hypothesis HQ : forall n, finite_t (Q n).
  
  Let K n := exists x, Q n x.
  
  Let K_dec n : { K n } + { ~ K n }.
  Proof.
    destruct (HQ n) as ( [ | x l ] & Hl ).
    right; intros (x & Hx); apply (Hl x), Hx.
    left; exists x; apply Hl; left; trivial.
  Qed.
  
  Theorem weighted_reif : (exists x, P x) -> { x | P x }.
  Proof.
    intros H.
    destruct (nat_reify K K_dec) as (n & Kn).
    destruct H as (x & Hx).
    apply HP in Hx.
    destruct Hx as (n & Hn).
    exists n, x; auto.
    destruct (HQ n) as ([ | y l ] & Hl).
    exfalso.
    destruct Kn as (x & Hx).
    apply (Hl x), Hx.
    exists y; apply HP.
    exists n; apply Hl; left; auto.
  Qed.
  
End weighted_reif.

Section proof.

  Variable (stm : Type) (stm_eq_dec : forall x y : stm, { x = y } + { x <> y }) 
      (stm_w : stm -> nat) 
      (stm_fin : forall n, finite_t (fun s => stm_w s = n)).
  
  (* Rule instances are of the form H1,...,Hn / C where H1,..,Hn is a list of (premise) statements and 
     C is (conclusion) statement *)
  
  Variable (inst : list stm -> stm -> Prop) (inst_dec : forall l c, { inst l c } + { ~ inst l c }).
  
  (* a proof tree is a tree of stm such that each node is an instance of some rule *)
  
  Definition proof_tree := tree_fall (fun c l => inst (map (@tree_root _) l) c).
  
  Fact proof_tree_fix c ll : proof_tree (in_tree c ll) <-> inst (map (@tree_root _) ll) c
                                                        /\ forall t, In t ll -> proof_tree t.
  Proof. apply tree_fall_fix. Qed.
  
  (* Once you can recognise valid instances, you can recognize valid proof trees 
     But this has nothing to do with decidability of provability: recognizing a proof
     is not the same thing as finding a proof
   *)
  
  Fact proof_tree_dec t : { proof_tree t } + { ~ proof_tree t }.
  Proof. apply tree_fall_dec; intros; apply inst_dec. Qed.

  (** This shows that under very reasonable assumptions, we can
      reify the provability predicate: the assumptions are
      
     1/ the equality of statement (eg formulas) can be decided
     2/ there is a weight on statements such for any given 
        weight value, only a finite number of statements have 
        that weight
     3/ discriminating between valid and invalid rule instances is decidable
     
     1&3) are really non issues for any proof system designed for
        proofs search because being able to recognise the trees which
        are valid proofs from those which are not is a must prerequisite
        
     2)  is also a very weak requirement. For instance, if you can encode
        statements with numbers, then 2) holds, the weight being
        simply the number encoding a statement
   *) 

  Definition proof_reif c : (exists p, tree_root p = c /\ proof_tree p) -> { p | tree_root p = c /\ proof_tree p }.
  Proof.
    apply weighted_reif with (Q := fun n p => proof_tree p /\ tree_root p = c /\ tree_weight stm_w p = n).
    intros t; split.
    exists (tree_weight stm_w t); tauto.
    intros (? & ? & ?); tauto.
    intros n.
    apply finite_t_dec.
    apply proof_tree_dec.
    apply finite_t_dec.
    intro; apply stm_eq_dec.
    apply finite_t_weighted_tree, stm_fin.
  Qed.
  
End proof.

Check proof_reif.
Print Assumptions proof_reif.

 
  
  