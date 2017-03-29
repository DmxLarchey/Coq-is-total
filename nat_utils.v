(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Eqdep_dec.

Require Import notations tac_utils list_utils.

Set Implicit Arguments.

Section le_pirr.

  (* a dependent induction principle for le *)
  
  Scheme le_indd := Induction for le Sort Prop.

  Theorem le_pirr : forall n m (H1 H2 : n <= m), H1 = H2.
  Proof.
    simpl; intros n ? H1.
    induction H1 as [ | m H1 IH ] using le_indd; intro H2.

    change (le_n n) with (eq_rect _ (fun n0 => n <= n0) (le_n n) _ eq_refl).
    generalize (eq_refl n).
    pattern n at 2 4 6 10, H2. 
    case H2; [intro E | intros m l E].
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
    contradiction (le_Sn_n m); subst; auto.
    
    change (le_S n m H1) with (eq_rect _ (fun n0 => n <= n0) (le_S n m H1) _ eq_refl).
    generalize (eq_refl (S m)).
    pattern (S m) at 1 3 4 6, H2.
    case H2; [intro E | intros p H3 E].
    contradiction (le_Sn_n m); subst; auto.
    injection E; intro; subst.
    rewrite (IH H3).
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
  Qed.

End le_pirr.

(* Bounded choice in Type *)

Definition nat_choose n (P Q : forall i, i < n -> Type) :
      (forall i Hi, P i Hi + Q i Hi)
   -> { i : _ & { Hi : _ & P i Hi } } + forall i Hi, Q i Hi.
Proof.
  revert P Q; induction n as [ | n IHn ]; intros P Q H.
  right; intros; omega.
  destruct (H 0 (lt_O_Sn _)) as [ p | q ].
  left; exists 0, (lt_O_Sn _); auto.
  destruct (IHn (fun i Hi => P _ (lt_n_S _ _ Hi))
                (fun i Hi => Q _ (lt_n_S _ _ Hi))) 
      as [ (i & Hi & p) | C ].
  intros; apply H.
  left; exists (S i), (lt_n_S _ _ Hi); auto.
  right.
  intros [ | i ] Hi.
  revert q; eqgoal; f_equal; apply le_pirr.
  generalize (C _ (lt_S_n _ _ Hi)); eqgoal; f_equal; apply le_pirr.
Qed.

(* given n : nat and P Q : nat -> nat -> Type which can be decided pointwise,
   and f0,...,f(n-1), 
   either P 0 f(0), .... P (n-1) f(n-1) all hold
   or there is i <n st Q i f(i) holds
*)

Definition finite_choice n P Q (f : forall i, i < n -> nat) :
       (forall i x (Hi : i < n), P i x Hi + Q i x Hi)
    -> (forall i Hi, P i (f i Hi) Hi)
     + {i :_ & { Hi : i < n  & Q i (f i Hi) Hi } }.
Proof.
  intros H.
  destruct (@nat_choose n (fun i Hi => Q i (f i Hi) Hi) (fun i Hi => P i (f i Hi) Hi))
      as [ (i & Hi & x) | C ].
  intros i Hi; destruct (H i (f i Hi) Hi); auto.
  right; exists i, Hi; trivial.
  left; auto.
Qed.

Section nat_partition_choose.

  Definition ftail X n (f : forall i, i < S n -> X) : forall i, i < n -> X.
  Proof.
    intros i Hi; apply (f (S i)), lt_n_S, Hi.
  Defined.

  Definition fhead X n (f : forall i, i < S n -> X) : X := f 0 (lt_0_Sn _).

  Definition flift X (x : X) n (f : forall i, i < n -> X) : forall i, i < S n -> X.
  Proof.
    intros [ | i ] Hi.
    exact x.
    apply (f i), lt_S_n, Hi.
  Defined.

  Fixpoint finite_sum n : (forall i, i < n -> nat) -> nat :=
    match n return (forall i, i < n -> nat) -> nat with 
      | 0   => fun _ => 0
      | S n => fun f => fhead f + finite_sum (ftail f)
    end.

  Fact finite_sum_ext n f g : (forall i Hi, f i Hi = g i Hi) -> @finite_sum n f = finite_sum g.
  Proof.
    revert f g; induction n as [ | n IHn ]; intros f g H; simpl; auto.
    unfold fhead, ftail; f_equal; auto.
  Qed.

  Fact finite_sum_tail_lift n x f : finite_sum (ftail (@flift _ x n f)) = finite_sum f.
  Proof.
    apply finite_sum_ext.
    intros; cbv; f_equal; apply le_pirr.
  Qed.

  Fact finite_sum_lb n f : (forall i Hi, 0 < f i Hi) -> n <= @finite_sum n f.
  Proof.
    revert f; induction n as [ | n IHn ]; intros f Hf.
    omega.
    simpl.
    generalize (Hf 0 (lt_O_Sn _)).
    specialize (IHn (ftail f)).
    inst IHn.
    intros; apply Hf.
    unfold fhead; omega.
  Qed.

  Definition frepr m n (l : list (forall i, i < n -> nat)) :=
      (forall f, (@finite_sum n f = m -> { g : _ &  (In_t g l * forall i Hi, f i Hi = g i Hi) })
              * (In_t f l -> finite_sum f = m))%type.

  Definition fs_list (m n : nat) : { l : _ & @frepr m n l }.
  Proof.
    revert m; induction n as [ | n IHn ].
 
    intros [ | m ].

    exists ((fun _ _ => 0)::nil); intros f; split.
    intros _; exists (fun _ _ => 0); split.
    left; auto.
    intros; omega.
    intros [ [] | [] ]; auto.

    exists nil; intros f; split.
    discriminate 1.
    intros [].

    intros m.
    set (li i := projT1 (IHn i)).
    assert (Hli : forall i, frepr i (li i)).
      intros i; apply (projT2 (IHn i)).
    generalize li Hli; clear IHn li Hli; intros li Hli.
    set (lj i := map (@flift _ i _) (li (m-i))).
    exists (flat_map lj (list_n (S m))).
    intros f.
    split.

    intros Hf.
    simpl in Hf.
    destruct (Hli (m-fhead f) (ftail f)) as [ (g & H1 & H2) _ ].
    omega.
    exists (flift (fhead f) g); split.
    apply flat_map_In_t with (fhead f).
    apply list_n_In_t; omega.
    apply map_In_t; auto.
    intros [ | i ] Hi; simpl.
    unfold fhead; f_equal; apply le_pirr.
    rewrite <- H2; unfold ftail; f_equal; apply le_pirr.

    intros H.
    apply In_t_flat_map in H.
    destruct H as (x & H1 & H2).
    apply In_t_list_n in H1.
    unfold lj in H2.
    apply In_t_map in H2.
    destruct H2 as (g & H2 & H3).
    apply Hli in H3.
    subst f; simpl.
    unfold fhead; simpl.
    rewrite finite_sum_tail_lift; omega.
  Qed.

  Definition fsum_list m n := projT1 (fs_list m n).

  Fact fsum_list_prop1 : forall m n f, In_t f (fsum_list m n) -> finite_sum f = m.
  Proof.
    intros m n f; apply (projT2 (fs_list m n) f).
  Qed. 
  
  Fact fsum_list_prop2 : forall m n f, finite_sum f = m 
                            -> { g : _ &  (In_t g (fsum_list m n)
                                       * forall i Hi, f i Hi = g i Hi)%type }.
  Proof.
    intros m n f; apply (projT2 (fs_list m n) f).
  Qed.

  Hint Resolve fsum_list_prop1 fsum_list_prop2. 
  
  (* given m n : nat and P Q : nat -> nat -> Type which can be decided pointwise,
     either there is f0+...+f(n-1)=m and P 0 f(0), .... P (n-1) f(n-1)
     or for any f0+...+f(n-1)=m, one of Q i f(i) holds for i < n
   *)

  Definition nat_partition_choice m n P Q :
      (forall i x (Hi : i < n), P i x Hi + Q i x Hi)
   -> { f : forall i, i < n -> nat &  
          ((finite_sum f = m) *
          forall i Hi, P i (f i Hi) Hi)%type }
    + forall f : forall i, i < n -> nat, finite_sum f = m 
        -> {i :_ & { Hi : i < n & Q i (f i Hi) Hi } }.
  Proof.
    intros H.
    set (l := fsum_list m n).
    destruct (list_choose l (fun f _ => forall i Hi, P i (f i Hi) Hi)
                         (fun f _ => {i :_ & { Hi : i < n & Q i (f i Hi) Hi } }))
      as [ (f & H1 & H2) | C ].
    intros f Hf; simpl.
    apply finite_choice; auto.
    left; exists f; split; auto.
    right; intros f Hf.
    apply fsum_list_prop2 in Hf.
    destruct Hf as (g & H1 & H2).
    destruct (C _ H1) as (i & Hi & H3).
    exists i, Hi; revert H3; eqgoal; do 2 f_equal.
  Qed.

  (* given m : nat and P Q : nat -> nat -> Type which can be decided pointwise,
     and such that P x 0 is always empty
     either there is n and f0+...+f(n-1)=m and P 0 f(0), .... P (n-1) f(n-1)
     or for any n and f0+...+f(n-1)=m, one of Q i f(i) holds for i < n
   *)
     
  Definition nat_unbounded_partition_choice m P Q :
      (forall i x, P i x + Q i x)
   -> (forall i, P i 0 -> False)
   -> { n : nat & { f : forall i, i < n -> nat &  
          ((finite_sum f = m) *
          forall i Hi, P i (f i Hi))%type } }
    + forall n (f : forall i, i < n -> nat), finite_sum f = m 
        -> {i :_ & { Hi : i < n & Q i (f i Hi) } }.
  Proof.
    intros H1 H2.
    assert (forall n f, (forall i Hi, P i (f i Hi)) -> n <= @finite_sum n f ) as HP.
      intros n f Hf.
      apply finite_sum_lb.
      intros i Hi; specialize (Hf i Hi).
      destruct (f i Hi).
      apply H2 in Hf; omega.
      omega.
    destruct (@nat_choose (S m) (fun n _ => { f : forall i, i < n -> nat &  
                                         ((finite_sum f = m) *
                                         forall i Hi, P i (f i Hi))%type })
                             (fun n _ => forall f : forall i, i < n -> nat, finite_sum f = m 
        -> {i :_ & { Hi : i < n & Q i (f i Hi) } })
     ) as [ (i & Hi & f & H3 & H4 ) | C ].
    intros i Hi; simpl.
    apply nat_partition_choice with (P := fun i x _ => P i x) (Q := fun i x _ => Q i x). 
    intros; apply H1.

    left; exists i, f; auto.

    right; intros n f Hf. 
    destruct (@finite_choice _ (fun i x _ => P i x) (fun i x _ => Q i x) f) as [ H | ]; auto; simpl.
    intros; auto.
    apply C; auto.
    rewrite <- Hf; apply le_n_S, HP; auto.
  Qed.

End nat_partition_choose.
