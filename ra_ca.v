(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import utils recalg.

Set Implicit Arguments.

Reserved Notation "  '[' f ';' v ']' '-[' n '>>' x " (at level 70).

(** The intuitive meaning of [f;v] -[n>> x is
   
      There is a computation of f(v) which costs n and results in x
    
    We define it in such a way that 
      1/ the cost is never 0, 
      2/ the cost of compound computation is greater than
         the sum of the costs of its sub-computations
      3/ the cost and the result are unique (if they exist) 
      
 **)
   
Inductive ra_ca : forall k, recalg k -> vec nat k -> nat -> nat -> Prop := 
    | in_ra_ca_cst  : forall n v,             [ra_cst n;        v] -[ 1           >> n
    | in_ra_ca_zero : forall v,               [ra_zero;         v] -[ 1           >> 0
    | in_ra_ca_succ : forall v,               [ra_succ;         v] -[ 1           >> S (vec_head v)
    | in_ra_ca_proj : forall k v j,           [@ra_proj k j;    v] -[ 1           >> vec_pos v j 
    
    | in_ra_ca_comp : forall k i f (gj : vec (recalg i) k) v q w p x,
                                   (forall j, [vec_pos gj j;    v] -[ vec_pos q j >> vec_pos w j)
                               ->             [f;               w] -[ p           >> x
                               ->             [ra_comp f gj;    v] -[1+p+vec_sum q>> x

    | in_ra_ca_rec_0 : forall k f (g : recalg (S (S k))) v n x,    
                                              [f;               v] -[ n           >> x 
                               ->             [ra_rec f g;   0##v] -[ S n         >> x

    | in_ra_ca_rec_S : forall k f (g : recalg (S (S k))) v n p x q y,          
                                              [ra_rec f g;   n##v] -[ p           >> x
                               ->             [g;         n##x##v] -[ q           >> y
                               ->             [ra_rec f g; S n##v] -[ 1+p+q       >> y
                               
    | in_ra_ca_min : forall k (f : recalg (S k)) v x p w q , 
                           (forall j : pos x, [f;    pos2nat j##v] -[ vec_pos q j >> S (vec_pos w j)) 
                               ->             [f;            x##v] -[ p           >> 0
                               ->             [ra_min f;        v] -[1+p+vec_sum q>> x
where " [ f ; v ] -[ n >> x " := (@ra_ca _ f v n x).

Section inversion_lemmas.

  (** The inversion tactic won't work for the dependent predicate ra_ca so
      we build the inversion lemma by hand.

      Notice the presence of type-castings (eq_rect ...) which disappear
      when we instanciate that lemma on the individual cases 
      (the lemmas ra_ca_*_inv below)

      The statement of the lemma is complicated but the proof is trivial !!
  *)

  Lemma ra_ca_inv k (f : recalg k) v n x : 
    [f;v] -[n>> x -> (n = 1 /\ exists (H : k = 0), eq_rect _ _ f _ H = ra_cst x)
                  \/ (n = 1 /\ x = 0 /\ exists (H : k = 1), eq_rect _ _ f _ H = ra_zero)
                  \/ (n = 1 /\ exists (H : k = 1), x = S (vec_head (eq_rect _ _ v _ H)) /\ eq_rect _ _ f _ H = ra_succ)
                  \/ (n = 1 /\ exists p, x = vec_pos v p /\ f = ra_proj p)
                  \/ (exists i (h : recalg i) gj w q m, n = 1+q+vec_sum m /\ [h;w] -[q>> x 
                              /\ (forall p, [vec_pos gj p;v] -[vec_pos m p>> vec_pos w p)
                              /\ f = ra_comp h gj) 
                  \/ (exists k' (H : k = S k') (h : recalg k') g m, 
                                 n = S m 
                              /\ vec_head (eq_rect _ _ v _ H) = 0
                              /\ [h;vec_tail (eq_rect _ _ v _ H)] -[m>> x 
                              /\ eq_rect _ _ f _ H = ra_rec h g) 
                  \/ (exists k' (H : k = S k') m y (h : recalg k') g p q, 
                                 vec_head (eq_rect _ _ v _ H) = S m
                              /\ n = 1+p+q
                              /\ [ra_rec h g; m##vec_tail (eq_rect _ _ v _ H)] -[p>> y                             
                              /\ [g; m##y##vec_tail (eq_rect _ _ v _ H)] -[q>> x  
                              /\ eq_rect _ _ f _ H = ra_rec h g) 
                  \/ (exists (g : recalg (S k)) (m w : vec _ x) q,
                                 n = 1+q+vec_sum m
                              /\ (forall p, [g; pos2nat p##v] -[vec_pos m p>> S (vec_pos w p))  
                              /\ [g; x##v] -[q>> 0
                              /\ f = ra_min g)  
                 .
  Proof.
    induction 1.
    do 0 right; left; split; auto; exists eq_refl; auto.
    do 1 right; left; do 2 (split; auto); exists eq_refl; auto.
    do 2 right; left; split; auto; exists eq_refl; split; simpl; auto.
    do 3 right; left; split; auto; exists j; auto.
    do 4 right; left; exists k, f, gj, w, p, q; auto.
    do 5 right; left; exists k, eq_refl, f, g, n; auto.
    do 6 right; left; exists k, eq_refl, n, x, f, g, p, q; auto.
    do 7 right; exists f, q, w, p; auto.
  Qed.

  (* The next proofs by hand are long but not complicated ... we simply have to
     discard all the unnecessary cases generated by the general
     inversion lemma using the discriminate tactic *)

  (* Automation is our friend here *)

  (* This is to destruct the inversion lemma *)
     
  Local Ltac myinv := 
    let H := fresh in
    intros H;
    apply ra_ca_inv in H;   
    destruct H as   [ (? & ? & ?) 
                  | [ (? & ? & ? & ?)
                  | [ (? & ? & ? & ?)
                  | [ (? & ? & ? & ?)
                  | [ (? & ? & ? & ? & ? & ? & ? & ? & ? & ?) 
                  | [ (? & ? & ? & ? & ? & ? & ? & ? & ?)
                  | [ (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?) 
                    | (? & ? & ? & ? & ? & ? & ? & ?) 
                    ] ] ] ] ] ] ].

  Local Ltac natSimpl :=
    repeat match goal with [ H : S _ = S _ |- _ ] => let G := fresh in injection H; intro G; subst; natid end.
    
  Local Ltac mydiscr :=     
     repeat match goal with 
            | H : _ = _ :> nat      |- _  => discriminate H; fail
            | H : _ = _ :> recalg _ |- _  => discriminate H; fail
            end.  

  Local Ltac myauto := myinv; subst; natid; natSimpl; mydiscr; auto.
  
  Lemma ra_ca_cst_inv i v n x : [ra_cst i;v] -[n>> x -> n = 1 /\ x = i.
  Proof. inversion_clear 1; auto. Qed.

  Lemma ra_ca_zero_inv v n x : [ra_zero;v] -[n>> x -> n = 1 /\ x = 0.
  Proof. inversion_clear 1; auto. Qed.

  Lemma ra_ca_succ_inv v n x : [ra_succ;v] -[n>> x -> n = 1 /\ x = S (vec_head v).
  Proof. myauto. Qed.
  
  Local Ltac ra_inj := 
    match goal with 
       | H : ra_proj _   = ra_proj _   |- _ => apply ra_proj_inj in H
       | H : ra_comp _ _ = ra_comp _ _ |- _ => apply ra_comp_inj in H; destruct H as (? & ? & ?) 
       | H : ra_rec _ _  = ra_rec _ _  |- _ => apply ra_rec_inj in H; destruct H
       | H : ra_min _    = ra_min _    |- _ => apply ra_min_inj in H
    end; subst; simpl in * |- *.

  Lemma ra_ca_proj_inv k (p : pos k) v n x : [ra_proj p;v] -[n>> x -> n = 1 /\ x = vec_pos v p.
  Proof.
    myauto; ra_inj; auto.
  Qed.
  
  (* These 4 proofs should be a bit improved because they use automatically
     generated variables and might be a bit unstable when changing Coq version *)

  Lemma ra_ca_comp_inv k i f (gj : vec (recalg i) k) v n x : 
     [ra_comp f gj;v] -[n>> x -> exists p w q,
                                   n = 1+p+vec_sum q 
                                /\ (forall j, [vec_pos gj j;v] -[vec_pos q j>> vec_pos w j)
                                /\ [f;w] -[p>> x.
  Proof.
    myauto; ra_inj. 
    exists x4, x3, x5; auto.
  Qed.
  
  Lemma ra_ca_rec_0_inv k f g v n x : 
    [@ra_rec k f g; 0##v] -[n>> x -> exists m, n = S m /\ [f;v] -[m>> x.
  Proof.
    myauto; ra_inj.
    exists x4; auto.
  Qed.

  Lemma ra_ca_rec_S_inv k f g v i n x : 
     [@ra_rec k f g; S i##v] -[n>> x -> exists y p q, 
                                          n = 1+q+p
                                       /\ [ra_rec f g; i##v] -[q>> y
                                       /\ [g; i##y##v] -[p>> x.
  Proof.
    myauto; ra_inj; natSimpl.
    exists x3, x7, x6; auto.
  Qed.

  Lemma ra_ca_min_inv k f v n x : 
     [@ra_min k f;v] -[n>> x -> exists p w q,
                                 n = 1+p+vec_sum q
                              /\ [f;x##v] -[p>> 0
                              /\ forall j, [f;pos2nat j##v] -[vec_pos q j>> S (@vec_pos _ x w j). 
  Proof.
    myauto; ra_inj.
    exists x3, x2, x1; auto.
  Qed.

End inversion_lemmas.

