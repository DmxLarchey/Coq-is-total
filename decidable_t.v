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

Notation decidable_t := (fun P : Type => (P + (P -> False)))%type.

Fact prod_decidable_t P Q : 
       decidable_t P 
    -> decidable_t Q 
    -> (P * Q) + ((P -> False) + (Q -> False)).
Proof.
  intros [] [? | ? ]; tauto.
Qed.

Fact pos_decidable_t n (P : pos n -> Type) :
    (forall p, decidable_t (P p)) -> (forall p, P p) + { p : _ & P p -> False }.
Proof.
  revert P; induction n as [ | n IHn ].
  intros P _; left; intro p; pos_inv p.
  intros P HP.
  destruct (HP (pos_fst _)) as [ H1 | H1 ].
  destruct (IHn (fun p => P (pos_nxt _ p))) as [ H2 | H2 ].
  intro; simpl; auto.
  left; intro p; pos_inv p; auto.
  destruct H2 as (p & H2); right; exists (pos_nxt _ p); auto.
  right; exists (pos_fst _); auto.
Qed.
  
Theorem decidable_t_bounded n (P : forall i, i < n -> Type) :
     (forall i Hi, decidable_t (P i Hi)) 
  -> decidable_t { i : _  & { Hi : i < n & P i Hi } }.
Proof.
  intros HP.
  apply nat_choose in HP.
  destruct HP as [ HP | HP ]; [ left | right ]; auto.
  intros (i & Hi & H); apply (HP _ Hi); auto.
Qed.

Theorem decidable_t_bounded' n (P : nat -> Type) :
     (forall i, decidable_t (P i)) 
  -> decidable_t { i : _  & ((i < n) * P i)%type }.
Proof.
  intro. 
  destruct decidable_t_bounded with (P := fun i (_ : i < n) => P i)
    as [ (i & H1 & H2) | C ]; simpl; auto.
  left; exists i; split; auto.
  right; intros (i & H1 & H2); apply C; exists i, H1; auto.
Qed.

Section vec_decide.

  Variable (n : nat) (P : vec (nat -> Type) n).

  Hypothesis HP : forall p n , decidable_t (vec_pos P p n).

  Theorem vec_sum_decide_t m : decidable_t { v : _ & ( (vec_sum v = m)%nat 
                                                   * forall p, vec_pos P p (vec_pos v p)
                                                   )%type }.
  Proof.
    destruct (@nat_partition_choice m n (fun i x Hi => vec_get P i Hi x)
                                        (fun i x Hi => vec_get P i Hi x -> False))
      as [ (f & H1 & H2) | C ].

    intros i x Hi; simpl.
    generalize (pos2nat_nat2pos Hi); intros E.
    rewrite (vec_get_pos_eq) with (p := nat2pos Hi); auto.

    left; exists (vec_set f); split.
    rewrite <- vec_set_sum; auto.
    intros p.
    do 2 rewrite <- vec_get_pos with (H := pos2nat_prop _).
    rewrite vec_get_set; auto.

    right; intros (v & H1 & H2).
    destruct (C (vec_get v)) as (q & H3 & H4).
    rewrite vec_set_sum, vec_set_get; auto.
    apply H4.
    generalize (H2 (nat2pos H3)).
    rewrite vec_get_pos_eq with (p := nat2pos H3).
    eqgoal; f_equal.
    rewrite vec_get_pos_eq with (p := nat2pos H3); auto.
    rewrite pos2nat_nat2pos; auto.
    rewrite pos2nat_nat2pos; auto.
  Qed.

End vec_decide.

Definition nat_split_choice n (P Q : nat -> Type) :
       (forall i, decidable_t (P i)) 
    -> (forall j, decidable_t (Q j))
    -> { a : nat & { b : nat & ((n = a + b)%nat * P a * Q b)%type } }
     + (forall a b, P a -> Q b -> n <> a + b).
Proof.
  intros HP HQ.
  destruct vec_sum_decide_t with (P := P##Q##vec_nil) (m := n)
    as [ (v & H1 & H2) | H ].
  intros p x; repeat (pos_inv p; simpl; auto).
  left; exists (vec_pos v pos0), (vec_pos v pos1); repeat split.
  rewrite <- H1.
  rewrite (vec_head_tail v); simpl; f_equal.
  rewrite (vec_head_tail (vec_tail v)); simpl.
  rewrite (vec_0_nil _); simpl; omega.
  apply (H2 pos0).
  apply (H2 pos1).
  right; intros a b Ha Hb Hn.
  apply H; exists (a##b##vec_nil); split.
  simpl; omega.
  intro p; repeat (pos_inv p; simpl; auto).
Qed.

Section vec_unbounded_decide.

  Variables (P : nat -> nat -> Type)
            (HP1 : forall n m, decidable_t (P n m))
            (HP2 : forall n, P n 0 -> False).

  Definition vec_sum_unbounded_decide_t m :
     decidable_t { n : _ & { q : vec nat n & ( (vec_sum q = m)%nat
                                             * forall p, P (pos2nat p) (vec_pos q p)
                                             )%type } }.
  Proof.
    destruct (@nat_unbounded_partition_choice m _ _ HP1 HP2) as 
      [ (n & f & H1 & H2) | C ].

    left; exists n, (vec_set f); split.
    rewrite <- vec_set_sum; auto.
    intros p.
    rewrite <- vec_get_pos with (H := pos2nat_prop _), vec_get_set; auto.

    right; intros (n & q & H1 & H2).
    destruct (C _ (vec_get q)) as (u & H3 & H4).
    rewrite vec_set_sum, vec_set_get; auto.
    apply H4.
    rewrite vec_get_pos_eq with (p := nat2pos H3).
    rewrite <- (pos2nat_nat2pos H3) at 1; auto.
    rewrite pos2nat_nat2pos; auto.
  Qed.

End vec_unbounded_decide.
