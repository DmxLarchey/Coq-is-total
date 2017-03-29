(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

Require Import utils decidable_t.
Require Import recalg ra_ca.

Set Implicit Arguments.

(* Computation always have a cost greater than 1 *)

Theorem ra_ca_cost k (f : recalg k) v q x : [f;v] -[q>> x -> 0 < q.
Proof.
  induction 1; omega.
Qed.

Section functionality.

  (* This one is not very complicated but it requires inversion lemmas 
     which can be difficult to obtain if you do not know how to proceed
     with dependent types  
  *)
  
  Theorem ra_ca_fun k (f : recalg k) v n m x y : 
           [f;v] -[n>> x 
        -> [f;v] -[m>> y 
        -> n = m /\ x = y.
  Proof.
    intros H.
    revert H m y.
    induction 1 as [ n v | v | v 
                   | k v p 
                   | k i f gj v n w q x H1 IH1 H2 IH2 
                   | k f g v n x H1 IH2 
                   | k f g v n p x q y H1 IH1 H2 IH2
                   | k f v p n w q H1 IH1 H2 IH2 ]; intros n2 x2 H3.
    apply ra_ca_cst_inv  in H3; destruct H3; split; auto.
    apply ra_ca_zero_inv in H3; destruct H3; split; auto.
    apply ra_ca_succ_inv in H3; destruct H3; split; auto.
    apply ra_ca_proj_inv in H3; destruct H3; split; auto.
    
    apply ra_ca_comp_inv in H3.
    destruct H3 as (q' & w' & n' & H5 & H3 & H4).
    assert (forall p, vec_pos n p = vec_pos n' p /\ vec_pos w p = vec_pos w' p) as E.
      intros p; apply IH1, H3.
    assert (n = n' /\ w = w') as E'.
      split; apply vec_pos_ext; intro; apply E.
    destruct E'; subst n' w'.  
    destruct (IH2 _ _ H4); subst; auto.
    
    apply ra_ca_rec_0_inv in H3.
    destruct H3 as (m & ? & H3).
    apply IH2 in H3; destruct H3; subst; auto.
    apply ra_ca_rec_S_inv in H3.
    destruct H3 as (y' & q' & p' & H3 & H5 & H4).
    apply IH1 in H5; destruct H5; subst.
    apply IH2 in H4; destruct H4; subst; auto.

    apply ra_ca_min_inv in H3.
    destruct H3 as (q' & w' & n' & H3 & H5 & H4).
    destruct (lt_eq_lt_dec p x2) as [ [ C | E ] | C ].

    specialize (H4 (nat2pos C)).
    rewrite pos2nat_nat2pos in H4.
    apply IH2, proj2 in H4; discriminate H4.

    subst x2.
    apply IH2, proj1 in H5; subst q'.
    assert (forall p, vec_pos q p = vec_pos n' p /\ S (vec_pos w p) = S(vec_pos w' p)) as E.
      intros i; apply IH1, H4.
    assert (q = n' /\ w = w') as E'.
      split; apply vec_pos_ext; intro i.
      apply E.
      generalize (proj2 (E i)); omega.
    destruct E'; subst; auto.

    rewrite <- (pos2nat_nat2pos C) in H5.
    apply IH1, proj2 in H5.
    discriminate H5.
  Qed.
  
End functionality.

Section decidability.

  (* These next two forms of *ra_ca_min* are better suited for the decidability proof,
     they generate lesser subcases *)

  Local Lemma in_ra_ca_min' k (f : recalg (S k)) v x (q w : vec nat (x+1)) :
       (forall p, [f;pos2nat p##v] -[vec_pos q p>> vec_pos w p)
    -> (forall p, 0 < vec_pos w (pos_lft _ p))
    -> 0 = vec_pos w (pos_rt _ pos0)
    -> [ra_min f;v] -[1+vec_sum q>> x.
  Proof.
    intros H1 H2 H3.
    rewrite (vec_app_lft_rt _ _ q), vec_sum_app.
    rewrite (plus_comm (vec_sum _)), plus_assoc.
    apply in_ra_ca_min with (vec_set_pos (fun p => vec_pos (vec_lft w) p - 1)).
    intros j.
    generalize (H1 (pos_lft _ j)).
    rewrite pos2nat_pos_lft; eqgoal; f_equal.
    unfold vec_lft; rewrite vec_pos_set; auto.
    rewrite vec_pos_set.
    generalize (H2 j); unfold vec_lft; rewrite vec_pos_set; omega.
    rewrite H3.
    generalize (H1 (pos_rt _ pos0)).
    eqgoal; f_equal.
    rewrite pos2nat_pos_rt; f_equal; auto.
    simpl; auto.
  Qed.

  Local Lemma ra_ca_min_inv' k (f : recalg (S k)) v n x :
       [ra_min f;v] -[n>> x
    -> exists q w : vec nat (x+1),
         n = 1+vec_sum q
      /\ 0 = vec_pos w (pos_rt _ pos0)
      /\ (forall p, 0 < vec_pos w (pos_lft _ p))
      /\ (forall p, [f;pos2nat p##v] -[vec_pos q p>> vec_pos w p).
  Proof.
    intros H.
    apply ra_ca_min_inv in H.
    destruct H as (p & w & q & H1 & H2 & H3).
    exists (vec_app q (p##vec_nil)), 
           (vec_app (vec_set_pos (fun p => S (vec_pos w p))) (0##vec_nil)).
    split.
    rewrite vec_sum_app; simpl; omega.
    split.
    rewrite vec_pos_app_rt; auto.
    split.
    intros i; rewrite vec_pos_app_lft, vec_pos_set; omega.
    intros i.
    destruct (pos_split i) as [ (j & ?) | (j & ?) ]; subst i.
    repeat rewrite vec_pos_app_lft.
    rewrite vec_pos_set, pos2nat_pos_lft; auto.
    repeat rewrite vec_pos_app_rt.
    rewrite pos2nat_pos_rt.
    pos_inv j; simpl.
    revert H2; eqgoal; do 2 f_equal; auto.
    pos_inv j.
  Qed.

  (* Since ra_ca is functional, sequences of computations with the same total cost
     must have the same length *)

  Local Lemma ra_ca_id_prefix k (f : recalg (S k)) (v : vec nat k) x qx wx y qy wy :
       (forall p : pos x, [f;pos2nat p##v] -[vec_pos qx p>> vec_pos wx p)
    -> (forall p : pos y, [f;pos2nat p##v] -[vec_pos qy p>> vec_pos wy p)
    -> vec_sum qx = vec_sum qy
    -> x < y -> False.
  Proof.
    intros H3 H4 H5 H.

    assert ({ p | y = x + S p }) as E.
      exists (y-x-1); omega.
    destruct E as (p & ?); subst y.
  
    assert (qx = vec_lft qy) as E2.
      apply vec_pos_ext.
      intros i.
      unfold vec_lft; rewrite vec_pos_set.
      generalize (H4 (pos_lft _ i)).
      rewrite pos2nat_pos_lft; intros H6.
      apply (ra_ca_fun (H3 i) H6).
    rewrite (vec_app_lft_rt _ _ qy), vec_sum_app in H5.
    generalize (vec_pos_sum (vec_rt qy) pos0).
    specialize (H4 (pos_rt _ pos0)).
    apply ra_ca_cost in H4.
    rewrite <- E2 in H5.
    simpl in H5.
    omega.
  Qed.

  Local Lemma ra_ca_prefix_eq k (f : recalg (S k)) (v : vec nat k) x qx wx y qy wy :
       (forall p : pos x, [f;pos2nat p##v] -[vec_pos qx p>> vec_pos wx p)
    -> (forall p : pos y, [f;pos2nat p##v] -[vec_pos qy p>> vec_pos wy p)
    -> vec_sum qx = vec_sum qy
    -> x = y.
  Proof.
    intros H3 H4 H5.
    destruct (lt_eq_lt_dec x y) as [ [ H | ] | H ]; auto; exfalso.
    apply ra_ca_id_prefix with (1 := H3) (2 := H4); auto.
    apply ra_ca_id_prefix with (1 := H4) (2 := H3); auto.
  Qed.
 
  Theorem ra_ca_decidable_t k (f : recalg k) v n : decidable_t { x | [f;v] -[n>> x }.
  Proof.
    revert v n; induction f as [ i | | | | k i f g Hf Hg | k f g Hf Hg | k f ]; intros v n.
 
    (* case of ra_cst *) 
    destruct (eq_nat_dec n 1) as [ H | H ]; subst.
    left; exists i; constructor.
    right; intros (x & Hx); apply ra_ca_cst_inv in Hx; omega.

    (* case of ra_zero *)
    destruct (eq_nat_dec n 1) as [ H | H ]; subst.
    left; exists 0; constructor.
    right; intros (x & Hx); apply ra_ca_zero_inv in Hx; omega.

    (* case of ra_succ *)
    destruct (eq_nat_dec n 1) as [ H | H ]; subst.
    left; exists (1+vec_head v); constructor.
    right; intros (x & Hx); apply ra_ca_succ_inv in Hx; omega.

    (* case of ra_proj *)
    destruct (eq_nat_dec n 1) as [ H | H ]; subst.
    left; exists (vec_pos v p); constructor.
    right; intros (x & Hx); apply ra_ca_proj_inv in Hx; omega.

    (* case of ra_comp *) 

    destruct n as [ | n ].
    right; intros (x & Hx); apply ra_ca_cost in Hx; omega.

    (* first we try to compute [vec_pos g *;v] in less than n steps total *) 

    generalize (@vec_sum_decide_t _ (vec_set_pos (fun p n => { x | [vec_pos g p;v] -[n>> x} : Type))). 
    intros Hg'; inst Hg'.
    intros; rewrite vec_pos_set; auto.
    apply (@decidable_t_bounded' (S n)) in Hg'.
    destruct Hg' as [ (m & Hm & q & Hq & Hg') | Hg' ].

    assert (Hq' : forall p, { x | [vec_pos g p;v] -[vec_pos q p>> x }).
      intros p; specialize (Hg' p); rewrite vec_pos_set in Hg'; auto.
    clear Hg'.
    apply vec_reif_t in Hq'.
    destruct Hq' as (w & Hw).

    (* then we try to compute [f;_] in the remaining number of steps *)

    destruct (Hf w (n-m)) as [ (x & Hx) | C ].

    (* we can compute [ f o g ; v ] *) 

    left; exists x.
    cutrewrite (n = (n-m)+vec_sum q); try omega.
    apply in_ra_ca_comp with (1 := Hw); auto.

    (* [f;_] cannot be computed *)

    right; intros (x & Hx).
    apply ra_ca_comp_inv in Hx.
    destruct Hx as (p & w' & q' & H1 & H2 & H3).
    assert ( q = q' /\ w = w' ) as E.
      split; apply vec_pos_ext; intros u;
      apply (ra_ca_fun (Hw u) (H2 u)).
    destruct E; subst q' w'.
    apply C; exists x; revert H3; eqgoal; f_equal; omega.

    (* [vec_pos g *;v] cannot be computed in less than n steps total *)

    right; intros (x & Hx).
    apply ra_ca_comp_inv in Hx.
    destruct Hx as (p & w & q & H1 & H2 & H3).
    apply Hg'.
    exists (vec_sum q).
    exists. omega.
    exists q; split; auto.
    intros j; rewrite vec_pos_set; exists (vec_pos w j); auto.

    (* case of ra_rec *)
   
    rewrite (vec_head_tail v); generalize (vec_head v) (vec_tail v).
    clear v; intros u v.
    revert n; induction u as [ | u IHu ]; intros n.

    (* case of rec 0 *)

    destruct n as [ | n ].
    right; intros (x & Hx); apply ra_ca_cost in Hx; omega.
    destruct (Hf v n) as [ (x & Hx) | C ].
    left; exists x; constructor; auto.
    right; intros (x & Hx); apply C; exists x.
    apply ra_ca_rec_0_inv in Hx.
    destruct Hx as (m & Hm & Hx).
    revert Hx; eqgoal; f_equal; omega.

    (* case of rec S *)

    destruct n as [ | n ].
    right; intros (x & Hx); apply ra_ca_cost in Hx; omega.
    apply (decidable_t_bounded' (S n)) in IHu.
    destruct IHu as [ (p & H1 & y & Hy) | C ].

    destruct (Hg (u##y##v) (n-p)) as [ (x & Hx) | C ].
    left; exists x.
    cutrewrite (n = p+(n-p)); try omega.
    apply in_ra_ca_rec_S with y; auto.

    right; intros (x & Hx).
    apply ra_ca_rec_S_inv in Hx.
    destruct Hx as (y' & q' & p' & H2 & H3 & H4).
    destruct (ra_ca_fun Hy H3); subst p' y'.
    apply C; exists x; revert H4; eqgoal; f_equal; omega.

    right; intros (x & Hx).
    apply ra_ca_rec_S_inv in Hx.
    destruct Hx as (y & q & p & H2 & H3 & H4).
    apply C.
    exists p.
    exists.
    omega.
    exists y; auto.

    (* case of ra_min *)

    specialize (fun i => IHf (i##v)).
    destruct n as [ | n ].
    right; intros (x & Hx); apply ra_ca_cost in Hx; omega.
    apply (vec_sum_unbounded_decide_t) with (m := n) in IHf.
    2: intros ? (? & H); apply ra_ca_cost in H; omega.
    destruct IHf as [ (x' & q & H1 & H2) | C ].
  
    (* no sequence of computation as a total cost of n *)
    Focus 2.
    right.
    intros (x & Hx).
    apply ra_ca_min_inv' in Hx.
    destruct Hx as (q & w & H2 & H3 & H4 & H5).
    apply C.
    exists (x+1), q; split.
    omega.
    intros p; exists (vec_pos w p); auto.

    (* the sequence q has a total cost of n *)  
    apply vec_reif_t in H2.
    destruct H2 as (w & Hw).
  
    assert ( (x' = 0) + { x | (x' = x + 1)%nat } )%type as E.
      destruct x' as [ | x' ]; [ left | right ]; auto; exists x'; omega.
    destruct E as [ ? | (x & ?) ]; subst x'.
  
    (* q is of length 0 *)
    rewrite (vec_0_nil q) in H1; simpl in H1.
    right.
    intros (x & Hx).
    apply ra_ca_min_inv' in Hx.
    destruct Hx as (q' & w' & H2 & H3 & H4 & H5).
    specialize (H5 (pos_rt _ pos0)).
    apply ra_ca_cost in H5.
    generalize (vec_pos_sum q' (pos_rt _ pos0)).
    omega.
 
    (* q is of length x+1 *)
    destruct (eq_nat_dec (vec_pos w (pos_rt _ pos0)) 0) as [ H2 | H2 ].
    destruct (vec_strict_pos (vec_lft w)) as [ H3 | (p & Hp) ].
 
    (* the sequence is strictly positive and ends with 0 *)
    left; exists x.
    cutrewrite (S n = 1+vec_sum q); try omega.
    apply in_ra_ca_min' with w; auto.
    intros p; generalize (H3 p); unfold vec_lft; rewrite vec_pos_set; auto.

    (* the sequence contains a zero before it ends *)
    right; intros (x' & Hx').
    apply ra_ca_min_inv' in Hx'.
    destruct Hx' as (q' & w' & H3 & H4 & H5 & H6).
    generalize (@ra_ca_prefix_eq k f v _ q w _ q' w' Hw H6); intros H7.
    assert (x = x') as E. omega.
    subst x'; clear H7.
    specialize (Hw (pos_lft _ p)).
    rewrite pos2nat_pos_lft in Hw.
    specialize (H6 (pos_lft _ p)).
    rewrite pos2nat_pos_lft in H6.
    generalize (proj2 (ra_ca_fun Hw H6)).
    generalize (H5 p).
    unfold vec_lft in Hp; rewrite vec_pos_set in Hp; omega.

    (* the sequence does not end with a zero *)

    right; intros (x' & Hx').
    apply ra_ca_min_inv' in Hx'.
    destruct Hx' as (q' & w' & H3 & H4 & H5 & H6).
    generalize (@ra_ca_prefix_eq k f v _ q w _ q' w' Hw H6); intros H7.
    assert (x = x') as E. omega.
    subst x'; clear H7.
    specialize (Hw (pos_rt _ pos0)).
    rewrite pos2nat_pos_rt in Hw.
    specialize (H6 (pos_rt _ pos0)).
    rewrite pos2nat_pos_rt in H6.
    generalize (proj2 (ra_ca_fun Hw H6)).
    omega.
  Qed.

End decidability.

Definition ra_ca_eval k (f : recalg k) v n : option nat := 
  match ra_ca_decidable_t f v n with
    | inl T  => Some (proj1_sig T)
    | inr _ => None 
  end.
  
Fact ra_ca_eval_prop k f v n x : [f;v] -[n>> x <-> @ra_ca_eval k f v n = Some x.
Proof.
  unfold ra_ca_eval.
  destruct (ra_ca_decidable_t f v n) as [ (y & Hy) | C ]; simpl.
  split.
  intros Hx; generalize (ra_ca_fun Hx Hy); intros (? & ?); subst; auto.
  injection 1; intros; subst; auto.
  split.
  intro; exfalso; apply C; exists x; auto.
  discriminate 1.
Qed.

(*
Extraction Language Haskell.
Extraction "ra_compute" ra_ca_eval.
*)