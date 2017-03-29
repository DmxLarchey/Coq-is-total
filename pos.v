(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import notations tac_utils list_utils.

Set Implicit Arguments.

Inductive pos : nat -> Set :=
  | pos_fst : forall n, pos (S n)
  | pos_nxt : forall n, pos n -> pos (S n).

Arguments pos_nxt : clear implicits.

Definition pos_iso n m : n = m -> pos n -> pos m.
Proof. intros []; auto. Defined.

Section pos_inv.

  Let pos_inv_t n := 
    match n as x return pos x -> Set with 
      | 0   => fun _ => False 
      | S n => fun i => (( i = pos_fst n ) + { p | i = pos_nxt _ p })%type
    end.

  Let pos_inv : forall n p, @pos_inv_t n p.
  Proof.
    intros _ [ | n p ]; simpl; [ left | right ]; auto; exists p; auto.
  Defined.

  Definition pos_O_inv : pos 0 -> False.
  Proof. apply pos_inv. Defined.

  Definition pos_S_inv n (p : pos (S n)) : ( p = pos_fst n ) + { q | p = pos_nxt _ q }.
  Proof. apply (pos_inv p). Defined.

  Definition pos_nxt_inj n (p q : pos n) (H : pos_nxt _ p = pos_nxt _ q) : p = q :=
    match H in _ = a return 
       match a as a' in pos m return 
           match m with 
             | 0 => Prop 
             | S n' => pos n' -> Prop 
           end with
         | pos_fst _   => fun _  => True 
         | pos_nxt _ y => fun x' => x' = y 
       end p with 
     | eq_refl => eq_refl
   end.

End pos_inv.

Section pos_invert.

  (* Position inversion, "singleton elimination" free version 
     One problem remains tu fully use it ... it is not
     correctly traversed by type checking algorithm
     of fixpoints (structural recursion)
     
     pos_S_inv work better in that respect 
  *)

  Let pos_invert_t n : (pos n -> Type) -> Type :=
    match n with
        0   => fun P => True
      | S n => fun P => (P (pos_fst n) * forall p, P (pos_nxt _ p))%type
    end.

  Let pos_invert n : forall (P : pos n -> Type), pos_invert_t P -> forall p, P p.
  Proof.
    intros P HP; induction p; simpl in HP; apply HP.
  Defined.
  
  Theorem pos_O_invert X : pos 0 -> X.
  Proof.
    apply pos_invert; simpl; trivial.
  Defined.

  Theorem pos_S_invert n P : P (pos_fst n) -> (forall p, P (pos_nxt _ p)) -> forall p, P p.
  Proof.
    intros; apply pos_invert; split; auto.
  Defined.
  
End pos_invert.

Arguments pos_S_invert [n] P _ _ p /.

Ltac pos_O_inv p := exfalso; apply (pos_O_inv p).

Ltac pos_S_inv p := 
  let H := fresh in
  let q := fresh
  in  rename p into q; destruct (pos_S_inv q) as [ H | (p & H) ]; subst q.
 
(* 
Ltac pos_O_inv p := apply (@pos_O_invert _ p).
Ltac pos_S_inv x := induction x as [ | x ] using pos_S_invert.
*)

Ltac pos_inv p :=   
  match goal with
    | [ H: pos 0     |- _ ] => match H with p => pos_O_inv p end
    | [ H: pos (S _) |- _ ] => match H with p => pos_S_inv p end
  end; simpl.

Tactic Notation "invert" "pos" hyp(H) := pos_inv H.

Definition pos_O_any X : pos 0 -> X.
Proof. intro p; invert pos p. Qed.

Fixpoint pos_list n : list (pos n) :=
  match n with
    | 0   => nil
    | S n => pos_fst _::map (pos_nxt _) (pos_list n) 
  end.

Fact pos_list_prop n p : In p (pos_list n).
Proof.
  induction p as [ | n p Hp ].
  left; auto.
  simpl; right.
  apply in_map_iff.
  exists p; auto.
Qed.
 
Fact pos_reification X n (R : pos n -> X -> Prop) : (forall p, exists x, R p x) -> exists f, forall p, R p (f p).
Proof.
  revert R; induction n as [ | n IHn ]; intros R HR.
  exists (pos_O_any X); intros p; invert pos p.
  set (R' q x := R (pos_nxt _ q) x).
  destruct (IHn R') as (f & Hf).
  intros p; apply HR.
  unfold R' in Hf.
  destruct (HR (pos_fst _)) as (x & Hx).
  exists (fun p => match pos_S_inv p with inl _ => x | inr (exist _ q _) => f q end).
  intros p; invert pos p; auto.
Qed.

Fact pos_reif_t X n (R : pos n -> X -> Prop) : (forall p, { x | R p x }) -> { f | forall p, R p (f p) }.
Proof.
  intros H.
  exists (fun p => (proj1_sig (H p))).
  intros; apply (proj2_sig (H p)).
Qed.

Section pos_eq_dec.

  Definition pos_eq_dec n (x y : pos n) : { x = y } + { x <> y }.
  Proof.
    revert n x y.
    induction x as [ x | n x IH ]; intros y; invert pos y.
    left; trivial.
    right; discriminate.
    right; discriminate.
    destruct (IH y) as [ | C ].
    left; subst; trivial.
    right; contradict C; revert C; apply pos_nxt_inj.
  Defined.

End pos_eq_dec.

Section pos_map.

  Definition pos_map m n := pos m -> pos n.
 
  Definition pm_ext_eq m n (r1 r2 : pos_map m n) := forall p, r1 p = r2 p.  

  Definition pm_lift m n (r : pos_map m n) : pos_map (S m) (S n).
  Proof.
    intros p.
    invert pos p.
    apply pos_fst.
    apply pos_nxt, (r p).
  Defined.
  
  Fact pm_lift_fst m n (r : pos_map m n) : pm_lift r (pos_fst _) = pos_fst _.
  Proof. auto. Qed.  
  
  Fact pm_lift_nxt m n (r : pos_map m n) p : pm_lift r (pos_nxt _ p) = pos_nxt _ (r p).
  Proof. auto. Qed.

  Arguments pm_lift [ m n ] r p.

  Fact pm_lift_ext m n r1 r2 : @pm_ext_eq m n r1 r2 -> pm_ext_eq (pm_lift r1) (pm_lift r2). 
  Proof.
    intros H12 p; unfold pm_lift.
    invert pos p; simpl; auto.
    f_equal; apply H12.
  Qed.

  Definition pm_comp l m n : pos_map l m -> pos_map m n -> pos_map l n.
  Proof.
    intros H1 H2 p.
    exact (H2 (H1 p)).
  Defined. 
 
  Fact pm_comp_lift l m n r s : pm_ext_eq (pm_lift (@pm_comp l m n r s)) (pm_comp (pm_lift r) (pm_lift s)).
  Proof.
    intros p.
    unfold pm_comp, pm_lift; simpl.
    invert pos p; simpl; auto.
  Qed.

  Definition pm_id n : pos_map n n := fun p => p.

End pos_map.

Arguments pm_lift [ m n ] _ _.
Arguments pm_comp [ l m n ] _ _ _.
Arguments pm_id : clear implicits.

Section pos_nat.

  Fixpoint pos_nat n (p : pos n) : { i | i < n }.
  Proof.
    refine (match p with 
              | pos_fst _   => _
              | pos_nxt _ q => _ 
            end).
    exists 0; apply lt_O_Sn.
    exists (S (proj1_sig (pos_nat _ q))). 
    apply lt_n_S.
    apply (proj2_sig (pos_nat _ q)).
  Defined.

  Definition pos2nat n p := proj1_sig (@pos_nat n p).
  
  Fact pos2nat_prop n p : @pos2nat n p < n.
  Proof. apply (proj2_sig (pos_nat p)). Qed.

  Fixpoint nat2pos n : forall x, x < n -> pos n.
  Proof.
     refine (match n as n' return forall x, x < n' -> pos n' with 
              | O   => fun x H => _
              | S i => fun x H => _
            end).
    exfalso; revert H; apply lt_n_O.
    destruct x as [ | x ].
    apply pos_fst.
    apply pos_nxt. 
    apply (nat2pos i x); revert H; apply lt_S_n.
  Defined.

  Definition nat_pos n : { i | i < n } -> pos n.
  Proof. intros (? & H); revert H; apply nat2pos. Defined.

  Arguments pos2nat n !p /.

  Fact pos2nat_inj n (p q : pos n) : pos2nat p = pos2nat q -> p = q.
  Proof.
    revert q.
    induction p as [ n p | n p IHp ]; intros q; invert pos q; simpl; auto; try discriminate 1.
    intros H; f_equal; apply IHp; injection H; trivial.
  Qed.

  Fact pos2nat_nat2pos n i (H : i < n) : pos2nat (nat2pos H) = i.
  Proof.
    revert i H;
    induction n as [ | n IHn ]; intros [ | i ] H; simpl; auto; try omega.
    f_equal.
    apply IHn.
  Qed.
  
  Fact nat2pos_pos2nat n p (H : pos2nat p < n) : nat2pos H = p.
  Proof.
    apply pos2nat_inj; rewrite pos2nat_nat2pos; auto.
  Qed.
  
  Fact pos2nat_fst n : pos2nat (pos_fst n) = 0.
  Proof. auto. Qed.
  
  Fact pos2nat_nxt n p : pos2nat (pos_nxt n p) = S (pos2nat p).
  Proof. auto. Qed. 
  
  Fixpoint pos_sub n (p : pos n) { struct p } : forall m, n < m -> pos m.
  Proof.
    destruct p as [ | n p ]; intros [ | m ] Hm.
    exfalso; clear pos_sub; abstract omega.
    apply pos_fst.
    exfalso; clear pos_sub; abstract omega.
    apply pos_nxt.
    apply (pos_sub n p), lt_S_n, Hm.
  Defined.
  
  Fact pos_sub2nat n p m Hm : pos2nat (@pos_sub n p m Hm) = pos2nat p.
  Proof.
    revert m Hm; induction p as [ n | n p IH ]; intros [ | m ] Hm; try omega. 
    simpl; auto.
    simpl pos_sub; repeat rewrite pos2nat_nxt; f_equal; auto.
  Qed.
  
End pos_nat.

Fact pos_list_an a n : map (fun p => pos2nat p+a) (pos_list n) = list_an a n.
Proof.
  revert a; induction n as [ | n IHn ]; intros a; simpl; auto.
  f_equal.
  rewrite <- IHn, map_map.
  apply map_ext.
  intros p. simpl.
  unfold pos2nat; omega.
Qed.

Fact pos_list_n n : map (@pos2nat _) (pos_list n) = list_n n.
Proof.
  unfold list_n.
  rewrite <- pos_list_an.
  apply map_ext.
  intro; omega.
Qed.
 
Section pos_rev.

  Definition pos_rev n : pos n -> pos n.
  Proof.
    intros p.
    destruct (pos_nat p) as (i & Hi).
    apply nat_pos.
    exists (n-S i); abstract omega.
  Defined.

  Fact pos2nat_pos_rev n (p : pos n)  : pos2nat (pos_rev p) = n - S (pos2nat p).
  Proof.
    unfold pos_rev, pos2nat at 2; destruct (pos_nat p); simpl.
    rewrite pos2nat_nat2pos; auto.
  Qed.

  Fact pos_rev_rev n (p : pos n) : pos_rev (pos_rev p) = p.
  Proof.
    apply pos2nat_inj.
    do 2 rewrite pos2nat_pos_rev.
    generalize (pos2nat_prop p); omega.
  Qed.

  Fact pos_list_rev n : rev (pos_list n) = map (@pos_rev _) (pos_list n).
  Proof.
    apply map_inj with (f := @pos2nat n).
    apply pos2nat_inj.
    rewrite map_map, map_rev.
    rewrite pos_list_n.
    rewrite <- list_n_rev.
    rewrite <- pos_list_n, map_map.
    apply map_ext.
    intros. 
    rewrite pos2nat_pos_rev.
    trivial.
  Qed.

  Fact pos_list_map_rev X n (f : pos n -> X) : map f (rev (pos_list n)) = map (fun p => f (pos_rev p)) (pos_list n).
  Proof.
    rewrite pos_list_rev, map_map; auto.
  Qed.

End pos_rev.

Section pos_split.

  Fixpoint pos_lft n m (p : pos n) : pos (n+m) :=
    match p in pos x return pos (x+m) with
      | pos_fst _   => pos_fst _
      | pos_nxt _ p => pos_nxt _ (pos_lft _ p)   
    end.

  Fact pos_lft_inj n m (p q : pos n) : @pos_lft n m p = pos_lft m q -> p = q.
  Proof.
    revert q; induction p; intros q; invert pos q; simpl; auto; try discriminate 1.
    intros H; apply pos_nxt_inj, IHp in H; subst; auto.
  Qed.
  
  Fact pos2nat_pos_lft n m (p : pos n) : pos2nat (@pos_lft n m p) = pos2nat p.
  Proof.
    induction p; simpl; auto.
    do 2 rewrite pos2nat_nxt; f_equal; auto.
  Qed.

  Fixpoint pos_rt n : forall m, pos m -> pos (n+m) :=
    match n return forall m, pos m -> pos (n+m) with
      | O   => fun _ p => p
      | S n => fun m p => pos_nxt _ (pos_rt n p)
    end.

  Fact pos_rt_inj n m (p q : pos m) : @pos_rt n m p = pos_rt _ q -> p = q.
  Proof.
    revert m p q; induction n; intros m p q; simpl; auto; intros H.
    apply pos_nxt_inj, IHn in H; auto.
  Qed.
  
  Fact pos2nat_pos_rt n m (p : pos m) : pos2nat (@pos_rt n m p) = n+pos2nat p.
  Proof.
    revert m p; induction n; intros ? ?; simpl; auto.
    rewrite pos2nat_nxt; f_equal; auto.
  Qed.

  Fact pos_lft_rt_neq n m p q : @pos_lft n m p <> @pos_rt n m q.
  Proof.
    revert m q; induction p; induction m; intros q; invert pos q; simpl; try discriminate;
    intros H; apply pos_nxt_inj, IHp in H; auto.
  Qed.

  Fixpoint pos_split n : forall m (p : pos (n+m)), { q | p = @pos_lft n m q } + { q | p = @pos_rt n m q }.
  Proof.
    refine (match n as x return forall m (p : pos (x+m)), { q | p = @pos_lft x m q } + { q | p = @pos_rt x m q } with
              | 0    => fun m p => _
              | S n' => fun m p => _
            end).
    right; exists p; auto.
    simpl in p; invert pos p.
    left; exists (pos_fst _); auto.
    destruct (pos_split n' m p) as [ (q & H) | (q & H) ]; subst.
    left; exists (pos_nxt _ q); auto.
    right; exists q; auto.
  Defined.

  Arguments pos_split [ n m ] _.
  
  Fact pos_split_lft n m p : pos_split (@pos_lft n m p) = inl (exist _ p eq_refl).
  Proof.
    induction p as [ n | n p IHp ]; simpl; auto.
    rewrite IHp; auto.
  Qed.
  
  Fact pos_split_rt n m p : pos_split (@pos_rt n m p) = inr (exist _ p eq_refl).
  Proof.
    revert m p; 
    induction n as [ | n IHn ]; intros m p; simpl; auto.
    rewrite IHn; auto.
  Qed.

(*  Fact pos_split_nxt_lft n m p : pos_split (pos_nxt (n + m) (pos_lft m p)) = pos_nxt _ p. *)

  Variable X : Type.

  Definition pf_cons k x (s : pos k -> X) p := 
    match pos_S_inv p with 
      | inl _           => x
      | inr (exist _ q _) => s q
    end.

  Definition pf_head k (s : pos (S k) -> X) := s (pos_fst _).
  Definition pf_tail k (s : pos (S k) -> X) p := s (pos_nxt _ p).

  Fact pf_tail_cons_eq k x s p : pf_tail (@pf_cons k x s) p = s p.
  Proof. auto. Qed.

  Fact pf_cons_nxt_eq k x s p : @pf_cons k x s (pos_nxt _ p) = s p.
  Proof. auto. Qed.

  Fact pf_cons_fst_eq k x s : @pf_cons k x s (pos_fst _) = x.
  Proof. auto. Qed.
  
  Definition pf_merge n f m g (q : pos (n+m)) : X :=
    match pos_split q with
      | inl (exist _ p _) => f p
      | inr (exist _ p _) => g p
    end.

  Fact pf_merge_lft_eq n f m g p : @pf_merge n f m g (pos_lft _ p) = f p.
  Proof. unfold pf_merge; rewrite pos_split_lft; auto. Qed.
  
  Fact pf_merge_rt_eq n f m g p : @pf_merge n f m g (pos_rt _ p) = g p.
  Proof. unfold pf_merge; rewrite pos_split_rt; auto. Qed.

  Fact pf_merge_pos_fst n f m g : @pf_merge (S n) f m g (pos_fst (n+m)) = f (pos_fst _).
  Proof. auto. Qed.

  Fact pf_merge_pos_nxt n f m g p : @pf_merge (S n) f m g (pos_nxt (n+m) p) = pf_merge (fun p => f (pos_nxt _ p)) g p.
  Proof.
    unfold pf_merge.
    destruct (pos_split p) as [ (q & H) | (q & H) ]; subst.
    destruct (@pos_split (S n) m (pos_nxt (n+m) (pos_lft m q))) as [ (r & Hr) | (r & Hr) ].
    invert pos r; simpl in Hr; try discriminate Hr; auto.
    apply pos_nxt_inj, pos_lft_inj in Hr; subst; auto.
    simpl in Hr; apply pos_nxt_inj in Hr.
    exfalso; revert Hr; apply pos_lft_rt_neq.
    destruct (@pos_split (S n) m (pos_nxt (n+m) (pos_rt n q))) as [ (r & Hr) | (r & Hr) ].
    invert pos r; simpl in Hr; try discriminate Hr.
    apply pos_nxt_inj in Hr.
    exfalso; symmetry in Hr; revert Hr; apply pos_lft_rt_neq.
    simpl in Hr.
    apply pos_nxt_inj, pos_rt_inj in Hr; subst; auto.
  Qed.

End pos_split.

Section pos_sum.

  Fixpoint pos_sum n : (pos n -> nat) -> nat :=
    match n with
      | 0   => fun _ => 0
      | S n => fun f => f (pos_fst _) + pos_sum (fun p => f (pos_nxt _ p))
    end.

  Fact pos_sum_ext n f g : (forall p, f p = g p) -> @pos_sum n f = pos_sum g.
  Proof.
    revert f g; induction n; intros; simpl; f_equal; auto.
  Qed.

  Fact pos_sum_plus n f g : @pos_sum n (fun x => f x + g x) = pos_sum f + pos_sum g.
  Proof.
    revert f g.
    induction n; simpl; intros f g; auto.
    rewrite IHn; omega.
  Qed.

  Fact pos_sum_zero n : @pos_sum n (fun _ => 0) = 0.
  Proof.
    induction n; simpl; auto.
  Qed.

  Fact pos_sum_all_zero n f : (forall x, f x = 0) -> @pos_sum n f = 0.
  Proof.
    intros H.
    rewrite <- (pos_sum_zero n).
    apply pos_sum_ext; auto.
  Qed.

  Fact pos_sum_one n f q : (forall p, f p = 0 \/ p = q) -> @pos_sum n f = f q.
  Proof.
    revert f q; induction n as [ | n IHn ]; intros f q.
    pos_inv q.
    simpl; intros H.
    pos_inv q.
    rewrite pos_sum_all_zero.
    omega.
    intros q.
    destruct (H (pos_nxt _ q)) as [ E | C ]; auto.
    discriminate C.
    destruct (H (pos_fst _)) as [ E | C ].
    rewrite E; simpl.
    apply IHn with (q := q).
    intros p.
    destruct (H (pos_nxt _ p)) as [ | C ].
    left; auto.
    right; revert C; apply pos_nxt_inj.
    discriminate C.
  Qed. 

End pos_sum.

Arguments pos_split [ n m ] _.

Definition pos_swap i (p : pos (S (S i))) : pos (S (S i)) :=
  match p with
    | pos_fst _             => pos_nxt _ (pos_fst _)
    | pos_nxt _ (pos_fst _) => pos_fst _
    | _                     => p
  end.

Ltac pf_auto := repeat rewrite pf_cons_nxt_eq; repeat rewrite pf_cons_fst_eq; auto.

Ltac pos_auto p := intros p; repeat (invert pos p; pf_auto).

Notation pos0 := (pos_fst _).
Notation pos1 := (pos_nxt _ pos0).
Notation pos2 := (pos_nxt _ pos1).

Notation " << >> " := (pos_O_any _).

Notation "<< x , .. , y >>" := (pf_cons x .. (pf_cons y (pos_O_any _)) .. ).


