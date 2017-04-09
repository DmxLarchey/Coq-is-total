(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Relations Wellfounded.

Require Import utils nat_minimizer finite.

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

Section normal_form.

  Variables (X : Type) (R : X -> X -> Prop).
  
  Hypothesis finitary : forall x, finite_t (R x).
  
  Definition normal x := forall y, ~ R x y.
  
  Local Fact normal_dec x : { normal x } + { ~ normal x }.
  Proof.
    destruct (finitary x) as ([ | y l ] & Hl).
    left; intro; rewrite <- Hl; simpl; tauto.
    right; intros H; apply (H y), Hl; left; auto.
  Qed.
  
  Local Fixpoint Rn n x y := 
    match n with
      | 0   => x = y
      | S n => exists i, R x i /\ Rn n i y
    end.
    
  Local Fact Rn_plus a b x y : Rn (a+b) x y <-> exists i, Rn a x i /\ Rn b i y.
  Proof.
    revert x y; induction a as [ | a IHa ]; intros x y; simpl.
    split.
    exists x; simpl; auto.
    intros (? & [] & ?); auto.
    split.
    intros (i & H1 & H2).
    apply IHa in H2.
    destruct H2 as (j & H2 & H3).
    exists j; split; auto.
    exists i; auto.
    intros (i & (j & H1 & H2) & H3).
    exists j; split; auto; apply IHa.
    exists i; auto.
  Qed.
    
  Local Fact Rn_crt x y : clos_refl_trans _ R x y <-> exists n, Rn n x y.
  Proof.
    split.
    induction 1 as [ x y | | x y z _ (n1 & Hn1) _ (n2 & Hn2) ].
    exists 1, y; simpl; auto.
    exists 0; simpl; auto.
    exists (n1+n2); apply Rn_plus. 
    exists y; split; auto.
    intros (n & Hn); revert x y Hn.
    induction n as [ | n IHn ]; simpl; intros x y Hn.
    subst; constructor 2.
    destruct Hn as (i & ? & ?).
    constructor 3 with i; auto.
    constructor 1; auto.
  Qed.
    
  Fact Rn_finitary n x : finite_t (Rn n x).
  Proof.
    revert x.
    induction n as [ | n IHn ]; intros x.
    exists (x::nil); simpl; tauto.
    apply finite_t_map with (1 := finitary _) (2 := fun x _ => IHn x).
  Qed.
  
  Variable (x : X).
  
  Definition normal_form y := normal y /\ clos_refl_trans _ R x y.
  
  Let Q n y := normal y /\ Rn n x y.
  
  Let Q_dec n : finite_t (Q n).
  Proof.
    apply finite_t_dec.
    apply normal_dec.
    apply Rn_finitary.
  Qed.
  
  (** This result shows that the predicate "y is a normal form of x"
     can be refied, ie one can compute a normal form of x out of
     a proof of its existence ...
     
     Hence if x is normalizable then a normal form of x can be
     computed.
     
     The only requirement is that the relation is (informativelly)
     finitary, that is the set of one step reductions forms a finite list 
     
     This development DOES NOT require than the relation is strongly
     normalizable ... hence the algorithm is obviously not depth
     first search. In fact, it is exhaustive search for depth 0,
     then depth 1, then depth 2, etc until a suitable depth is
     reached. 
     
     It is obviously not the best algorithm to actually compute a
     normal form. This depends on the particular system in consideration.

     This development applies to lambda calculus for instance where 
     the set of reducts can be computed from the set of redexes 
     
  **)
  
  Hypothesis Hx : exists y, normal_form y. 
  
  Definition normal_form_reif : { y | normal_form y }.
  Proof.
    destruct weighted_reif with (P := fun y => exists n, Q n y) (Q := Q)
      as (y & Hy); auto.
    simpl; tauto.
    destruct Hx as (y & ? & Hy).
    apply Rn_crt in Hy.
    destruct Hy as (n & ?).
    exists y, n; split; auto.
    exists y.
    destruct Hy as (n & ? & ?); split; auto.
    apply Rn_crt; exists n; auto.
  Qed.
  
End normal_form.

Check normal_form_reif.
Print Assumptions normal_form_reif.


 
  
  