(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

Set Implicit Arguments.

Section nat_rev_ind.

  (** A reverse recursion principle *)

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof. induction 1; auto. Qed.

End nat_rev_ind.

Section nat_rev_ind'.

  (** A reverse recursion principle *)

  Variables (P : nat -> Prop) (k : nat)
            (HP : forall n, n < k -> P (S n) -> P n).

  Theorem nat_rev_ind' x y : x <= y <= k -> P y -> P x.
  Proof.
    intros H1 H2. 
    set (Q n := n <= k /\ P n).
    assert (forall x y, x <= y -> Q y -> Q x) as H.
      apply nat_rev_ind.
      intros n (H3 & H4); split.
      omega.
      revert H4; apply HP, H3.
    apply (H x y).
    omega.
    split; auto; omega.
  Qed.

End nat_rev_ind'.

Section minimizer_bool.

  Variable (T F : nat -> Prop)
           (HFun  : forall n, T n -> F n -> False)
           (HComp : forall n, T n \/ F n -> { T n } + { F n }).

  Definition minimizer n := T n /\ forall i, i < n -> F i.

  Fact minimizer_fun n m : minimizer n -> minimizer m -> n = m.
  Proof.
    intros (H1 & H2) (H3 & H4).
    destruct (lt_eq_lt_dec n m) as [ [ H | ] | H ]; auto.
    * apply H4 in H; destruct (@HFun n); auto.
    * apply H2 in H; destruct (@HFun m); auto.
  Qed. 

  Inductive bar n : Prop :=
    | in_bar_0 : T n -> bar n
    | in_bar_1 : F n -> bar (S n) -> bar n.

  Let bar_ex n : bar n -> T n \/ F n.
  Proof. induction 1; auto. Qed.

  Let loop : forall n, bar n -> { k | T k /\ forall i, n <= i < k -> F i }.
  Proof.
    refine (fix loop n Hn { struct Hn } := match HComp (bar_ex Hn) with
        | left  H => exist _ n _
        | right H => match loop (S n) _ with
          | exist _ k Hk => exist _ k _
        end
      end).
    * split; trivial. 
      intros; omega.
    * destruct Hn; trivial. 
      destruct (@HFun n); trivial.
    * destruct Hk as (H1 & H2); split; trivial.
      intros i Hi; destruct (eq_nat_dec i n).
      - subst; trivial.
      - apply H2; omega.
  Qed.

  Hypothesis Hmin : ex minimizer.

  Let bar_0 : bar 0.
  Proof.
    destruct Hmin as (k & H1 & H2).
    apply in_bar_0 in H1.
    revert H1.
    apply nat_rev_ind' with (k := k).
    intros i H3.
    apply in_bar_1, H2; trivial.
    omega.
  Qed.

  Definition minimizer_bool_coq : sig minimizer.
  Proof.
    destruct (loop bar_0) as (k & H1 & H2).
    exists k; split; auto.
    intros; apply H2; omega.
  Defined.

End minimizer_bool.

Section minimizer.

  Variable (R : nat -> nat -> Prop)
           (Rfun : forall n u v, R n u -> R n v -> u = v)
           (HR : forall n, ex (R n) -> sig (R n)).

  Let T n := R n 0.
  Let F n := exists u, R n (S u).
 
  Definition minimizer_coq : ex (@minimizer T F) -> sig (@minimizer T F).
  Proof.
    apply minimizer_bool_coq.
    intros n H1 (u & H2).
    generalize (Rfun H1 H2); discriminate.
    intros n Hn.
    refine (match @HR n _ with
      | exist _ u Hu => match u as m return R _ m -> _ with
        | 0   => fun H => left H
        | S v => fun H => right (ex_intro _ v H)
        end Hu
      end).
    destruct Hn as [ Hn | (u & Hu) ].
    - exists 0; auto.
    - exists (S u); auto.
  Defined.

End minimizer.

Check minimizer_coq.
Print Assumptions minimizer_coq.

Extraction "minimizer.ml" minimizer_bool_coq minimizer_coq.

     