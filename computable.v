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

(** A relation is computable if has is a reifier *)

Definition computable X (R : X -> Prop) := ex R -> sig R.

Section vec_computable.

  (** Any computable relation can be lifted on vectors *)
   
  Variable (X Y : Type) (R : X -> Y -> Prop) (HR : forall (p : { x | ex (R x) }), { y | R (proj1_sig p) y }).
     
  Definition vec_computable : forall k v, computable (fun w => forall p : pos k, R (vec_pos v p) (vec_pos w p)).
  Proof.
    refine (fix loop k v { struct v } := match v with 
      | vec_nil           => fun _ => exist _ vec_nil _
      | @vec_cons _ k x v => fun H => _
     end).
     intro p; pos_inv p.
     assert (ex (R x)) as Hx.
       destruct H as (w & Hw).
       exists (vec_pos w pos0); apply (Hw pos0).
     refine (match @HR (exist _ x Hx), @loop k v _ with
           | exist _ y Hy, exist _ w Hw => exist _ (y##w) _
         end).
     * destruct H as (w & Hw).
       exists (vec_tail w).
       intros p; rewrite vec_pos_tail; apply (Hw (pos_nxt _ p)).
     * simpl in Hy. intros p; pos_inv p; simpl; auto.
  Defined.

End vec_computable.

Section rec_computable.

  Variables (V : Type)
            (F : V -> nat -> Prop) 
            (Ffun : forall v n m, F v n -> F v m -> n = m)
            (HF : forall p : { v | ex (F v) }, { n | F (proj1_sig p) n })
         (*   (HF : forall v, computable (F v)) *)
            (G : V -> nat -> nat -> nat -> Prop) 
            (Gfun : forall v x y n m, G v x y n -> G v x y m -> n = m)
            (HG : forall x y (p : { v | ex (G v x y) }), { n | G (proj1_sig p) x y n})
         (* (HG : forall v x y, computable (G v x y)) *).
  
  Fixpoint μ_rec v n := 
    match n with
      | 0   => F v
      | S n => fun x => exists y, μ_rec v n y /\ G v n y x
      end.

  Fact μ_rec_fun v : functional (μ_rec v). 
  Proof.
    intros n; induction n as [ | n IHn ]; simpl; auto.
    apply Ffun.
    intros x y (a & H1 & H2) (b & H3 & H4).
    specialize (IHn _ _ H1 H3); subst b.
    revert H2 H4; apply Gfun.
  Qed.

  Fixpoint rec_computable v n (Hn : ex (μ_rec v n)) : sig (μ_rec v n).
  Proof.
    destruct n as [ | n ].
    destruct (HF (exist _ v Hn)) as (n & H).
    exists n; auto.
    refine (match rec_computable v n _ with
        | exist _ xn Hxn => _
      end).
    destruct Hn as (_ & y & ? & _); exists y; auto.
    assert (ex (G v n xn)) as H.
      destruct Hn as (y & xn' & H1 & H2).
      exists y; revert H2; eqgoal; f_equal.
      revert Hxn H1; apply μ_rec_fun.
    refine(match @HG n xn (exist _ v H) with 
          | exist _ xSn HxSn => exist _ xSn _
        end).
    destruct Hn as (x & y & H1 & H2).
    simpl in HxSn.
    exists xn; auto.
  Defined.

End rec_computable.

Section min_computable.

  Variable 
           (R : nat -> nat -> Prop)
           (Rfun : forall n u v, R n u -> R n v -> u = v)
           (HR : forall (p : { n | ex (R n)}), { m | R (proj1_sig p) m }).

  Definition μ_min n := R n 0 /\ forall i, i < n -> exists u, R i (S u).

  Fact μ_min_fun n m : μ_min n -> μ_min m -> n = m.
  Proof.
    intros (H1 & H2) (H3 & H4).
    destruct (lt_eq_lt_dec n m) as [ [ H | ] | H ]; auto; 
      [ apply H4 in H | apply H2 in H ]; destruct H as (u & Hu);
      [ generalize (Rfun H1 Hu) | generalize (Rfun H3 Hu) ]; discriminate.
  Qed. 

  Inductive bar n : Prop :=
    | in_bar_0 : R n 0 -> bar n
    | in_bar_1 : (exists u, R n (S u)) -> bar (S n) -> bar n.

  Let bar_ex n : bar n -> ex (R n).
  Proof.
    induction 1 as [ n Hn | n (k & Hk) _ _ ].
    exists 0; auto.
    exists (S k); trivial.
  Qed.

  Let loop : forall n, bar n -> { k | R k 0 /\ forall i, n <= i < k -> exists u, R i (S u) }.
  Proof.
    refine (fix loop n Hn { struct Hn } := match HR (exist _ n (bar_ex Hn)) with
        | exist _ u Hu => match u as m return R _ m -> _ with
            | 0   => fun H => exist _ n _
            | S v => fun H => match loop (S n) _ with
                | exist _ k Hk => exist _ k _
              end
          end Hu
      end).
    * split; auto; intros; omega.
    * destruct Hn as [ Hn | ]; trivial; exfalso; generalize (Rfun H Hn); discriminate.
    * destruct Hk as (H1 & H2); split; trivial; intros i Hi.
      destruct (eq_nat_dec i n).
      - subst; exists v; trivial.
      - apply H2; omega.
  Qed.
  
  Definition min_computable : computable μ_min.
  Proof.
    intros Hmin.
    destruct (@loop 0) as (k & H1 & H2).
    destruct Hmin as (k & H1 & H2).
    apply in_bar_0 in H1.
    clear HR.
    revert H1.
    apply nat_rev_ind' with (k := k).
    intros i H3.
    apply in_bar_1, H2; trivial.
    omega.
    exists k; split; auto.
    intros; apply H2; omega.
  Defined.

End min_computable.



