(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List.

Require Import notations tac_utils.

Set Implicit Arguments.

Definition lsum := fold_right plus 0.
  
Fact lsum_le x l : In x l -> x <= lsum l.
Proof.
  induction l as [ | y l IHl ]; simpl.
  intros [].
  intros [ ? | H ]; subst. 
  omega.
  specialize (IHl H); omega.
Qed.
  
Definition lmax := fold_right max 0.

Fact map_inj X Y (f : X -> Y) : (forall a b, f a = f b -> a = b) -> forall l m, map f l = map f m -> l = m.
Proof.
  intros Hf.
  induction l as [ | a l IHl ]; intros [ | b m ]; auto; try discriminate 1; simpl.
  intros H; injection H; clear H; intros H1 H2.
  apply Hf in H2; subst.
  apply IHl in H1; subst.
  auto.
Qed.

Fact map_id X l : map (fun x : X => x) l = l.
Proof.
  induction l; simpl; f_equal; auto.
Qed.

Fact rev_inj X (l m : list X) : rev l = rev m -> l = m.
Proof.
  intros H; rewrite <- (rev_involutive l), H, rev_involutive; trivial.
Qed.

Section list_an.

  Fixpoint list_an a n := 
    match n with 
      | 0   => nil
      | S n => a::list_an (S a) n
    end.
    
  Fact list_an_spec a n x : In x (list_an a n) <-> a <= x < a+n.
  Proof.
    revert a.
    induction n as [ | n IH ]; intros a; simpl.
    split; (tauto || omega).
    rewrite IH; omega.
  Qed.
    
  Fact list_an_comp a n m : list_an a n ++ list_an (a+n) m = list_an a (n+m).
  Proof.
    revert a; induction n as [ | n IHn ]; intros a; simpl; auto.
    cutrewrite (a+S n = S a + n); try omega.
    f_equal; auto.
  Qed.

  Let list_an_prop a n b : a+n <= b -> map (fun x => b - S x) (list_an a n) = rev (list_an (b - (a+n)) n).
  Proof.
    revert a b; induction n; intros a b H; auto.
    simpl (list_an a (S n)); simpl map.
    rewrite IHn; try omega.
    apply rev_inj.
    rewrite rev_involutive.
    simpl rev.
    rewrite rev_involutive.
    cutrewrite (a+S n = S (a+n)); try omega.
    cutrewrite (S n = n+1); try omega.
    rewrite <- list_an_comp; simpl.
    f_equal; f_equal; omega.
  Qed.

  Definition list_n n := list_an 0 n.
  
  Fact list_n_spec n x : In x (list_n n) <-> x < n.
  Proof.
    unfold list_n; rewrite list_an_spec; omega.
  Qed. 
  
  Let list_n_rev_r n : map (fun x => n - x) (list_n (S n)) = rev (list_n (S n)).
  Proof.
    unfold list_n.
    generalize (list_an_prop 0 (S n) (le_refl _)); intros H.
    simpl plus in H.
    cutrewrite (S n - S n = 0) in H; try omega.
    rewrite <- H.
    apply map_ext.
    intros; omega.
  Qed.

  Fact list_n_rev n : map (fun x => n - S x) (list_n n) = rev (list_n n).
  Proof.
    destruct n.
    simpl; auto.
    rewrite <- list_n_rev_r.
    apply map_ext; intro; omega.
  Qed.

End list_an.

Section In_t.

  (* An informative version of In *)

  Fixpoint In_t X (x : X) (l : list X) : Set :=
    match l with
      | nil  => False
      | y::l => ((y = x) + In_t x l)%type
    end.

  Fact In_t_app X x (l m : list X) : In_t x (l++m) -> In_t x l + In_t x m.
  Proof.
    induction l.
    simpl; right; auto.
    intros [ H | H ].
    subst; left; left; auto.
    destruct (IHl H); [ left; right | right ]; auto.
  Qed.

  Fact app_In_t X x (l m : list X) : In_t x l + In_t x m -> In_t x (l++m).
  Proof.
    intros [ H | H ].
    induction l; destruct H; subst; simpl; auto.
    induction l; simpl; auto; right; auto.
  Qed.

  Fact In_t_map X Y (f : X -> Y) y l : In_t y (map f l) -> { x : X & ((y = f x) * In_t x l)%type }.
  Proof.
    induction l as [ | z l IHl ].
    intros [].
    intros [ ? | H ]; subst.
    exists z; simpl; auto.
    destruct (IHl H) as (x & ? & ?); exists x; simpl; auto.
  Qed.

  Fact map_In_t X Y (f : X -> Y) x l : In_t x l -> In_t (f x) (map f l).
  Proof.
    intros H.
    induction l; destruct H; [ left | right ]; subst; auto.
  Qed.

  Fact In_t_flat_map X Y (f : X -> list Y) y l : In_t y (flat_map f l) -> { x : _ & (In_t x l * In_t y (f x))%type }.
  Proof.
    induction l as [ | x l IHl ]; simpl.
    intros [].
    intros H.
    apply In_t_app in H.
    destruct H as [ H | H ].
    exists x; split; auto. 
    destruct (IHl H) as (c & H1 & H2).
    exists c; split; auto.
  Qed.

  Fact flat_map_In_t X Y (f : X -> list Y) x l y : In_t x l -> In_t y (f x) -> In_t y (flat_map f l).
  Proof.
    revert y; induction l as [ | a l IHl ]; intros y.
    intros [].
    intros [ H | H ] H1; subst;
    simpl; apply app_In_t; [ left | right ]; auto.
  Qed. 
 
  Fact In_t_In X x l : @In_t X x l -> In x l.
  Proof.
    induction l; intros []; [ left | right ]; auto.
  Qed.

  Definition list_choose X (l : list X) (P Q : forall x, In_t x l -> Type) :
      (forall i Hi, P i Hi + Q i Hi)
   -> { i : _ & { Hi : _ & P i Hi } } + forall i Hi, Q i Hi.
  Proof.
    revert P Q; induction l as [ | x l IHl ]; intros P Q H.
    right; intros _ [].
    destruct (H _ (inl eq_refl)) as [ p | q ].
    left; exists x, (inl eq_refl); auto.
    destruct (IHl (fun i Hi => P _ (inr Hi))
                  (fun i Hi => Q _ (inr Hi))) 
      as [ (i & Hi & p) | C ].
    intros; apply H.
    left; exists i, (inr Hi); auto.
    right.
    intros i [ Hi | Hi ]; subst; auto.
  Qed.
  
  Fact In_t_list_an a n i : In_t i (list_an a n) -> a <= i < a+n.
  Proof.
    revert a i; induction n as [ | n IHn ]; simpl; intros a i.
    intros []; split; omega.
    intros [ [] | H ].
    omega.
    apply IHn in H; omega.
  Qed.
  
  Fact list_an_In_t a n i : a <= i < a+n -> In_t i (list_an a n).
  Proof.
    revert a i; induction n as [ | n IHn ]; intros a i Hai.
    omega.
    simpl.
    destruct (eq_nat_dec a i).
    left; auto.
    right; apply IHn; omega.
  Qed.

  Fact In_t_list_n i n : In_t i (list_n n) -> i < n.
  Proof.
    intros H; apply In_t_list_an in H; omega.
  Qed.
  
  Fact list_n_In_t i n : i < n -> In_t i (list_n n).
  Proof.
    intro; apply list_an_In_t; omega.
  Qed.

End In_t.

Section list_In_map.

  Variable X Y : Type.

  Fixpoint list_In_map ll : (forall x : X, In x ll -> Y) -> list Y.
  Proof.
    refine (
      match ll with
        | nil   => fun _ => nil
        | x::mm => fun H => H x _ :: list_In_map mm _
      end).
    left; reflexivity.
    intros z ?; apply (H z); right; assumption.
  Defined.
    
  Fact list_In_map_length ll Hll : length (list_In_map ll Hll) = length ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

  Fact list_In_map_ext ll g h : (forall x (H : In x ll), g x H = h x H) -> list_In_map ll g = list_In_map ll h.
  Proof.
    induction ll; simpl; intros; f_equal; auto.
  Qed.
  
  Fact list_In_map_eq_map f ll : list_In_map ll (fun x _ => f x) = map f ll.
  Proof.
    induction ll; simpl; f_equal; assumption.
  Qed.

  Fact In_list_In_map l f x (Hx : In x l) : In (f x Hx) (list_In_map l f). 
  Proof.
    revert f x Hx; induction l; simpl; intros f x Hx.
    destruct Hx.
    destruct Hx as [ ? | Hx ].
    subst; left; auto.
    right. 
    apply IHl with (f := fun x Hx => f x (or_intror Hx)).
  Qed.

  Fact list_In_map_In l f y : In y (list_In_map l f) -> exists x Hx, y = f x Hx.
  Proof.
    revert f y; induction l as [ | x l IH ]; intros f y.
    intros [].
    intros [ ? | H ]; subst.
    exists x, (or_introl eq_refl); auto.
    destruct IH with (f := fun x Hx => f x (or_intror Hx))
                     (1 := H)
     as (u & Hu & ?).
    exists u, (or_intror Hu); auto.
  Qed.

  Hypothesis Yeq_dec : forall x y : Y, { x = y } + { x <> y }.

  Fact list_In_map_In_dec l f y : In y (list_In_map l f) -> {x : _ & { Hx | y = f x Hx } }.
  Proof.
    revert f y; induction l as [ | x l IH ]; intros f y.
    intros [].
    destruct (Yeq_dec y (f x (or_introl eq_refl))) as [ E | C ].
    exists x, (or_introl eq_refl); auto.
    intros H.
    assert (In y (list_In_map l (fun x Hx => f x (or_intror Hx)))) as Hy.
      destruct H; auto.
      contradict C; auto.
    destruct IH with (f := fun x Hx => f x (or_intror Hx))
                     (1 := Hy)
      as (u & Hu & ?); subst.
    exists u, (or_intror Hu); auto.
  Qed.
  
End list_In_map.

Fact map_list_In_map X Y Z (ll : list X) Hll (f : Y -> Z) : map f (@list_In_map X Y ll Hll) = list_In_map ll (fun x Hx => f (Hll x Hx)).  
Proof.
  induction ll; simpl; f_equal; auto.
Qed.

Fixpoint map_In X Y (f : X -> Y) l x { struct l } : In x l -> In (f x) (map f l).
Proof.
  destruct l as [ | y l ].
  intros [].
  intros [ [] | H ].
  left; reflexivity.
  right; apply map_In, H.
Defined.

Fact list_In_map_map X Y Z (ll : list X) (f : X -> Y) Hll : @list_In_map Y Z (map f ll) Hll = list_In_map ll (fun x Hx => Hll _ (map_In f ll x Hx)).
Proof.
  induction ll as [ | ? ? IH ]; simpl; f_equal.
  apply IH.
Qed.

Definition list_choose_rec X (P Q : X -> Prop) ll : 
    (forall x, In x ll -> {P x} + {Q x}) -> { z | In z ll /\ P z } + { forall z, In z ll -> Q z }.
Proof.
  induction ll as [ | x ll IHll ]; intros H.
  right; intros ? [].
  destruct (H _ (or_introl eq_refl)) as [ H1 | H1 ].
  left; exists x; split; auto; left; auto.
  destruct IHll as [ (z & H2 & H3) | C ].
  intros ? ?; apply H; right; auto.
  left; exists z; split; auto; right; auto.
  right; intros z [ ? | ? ]; subst; auto.
Qed.

Definition Forall_dec X (P : X -> Prop) ll : 
   (forall x, In x ll -> { P x } + { ~ P x }) -> { Forall P ll } + { ~ Forall P ll }.
Proof.
  intros HP.
  destruct (list_choose_rec (fun x => ~ P x) P ll) as [ (z & H1 & H2) | C ].
  intros x Hx; generalize (HP _ Hx); tauto.
  right; rewrite Forall_forall; contradict H2; auto.
  left; rewrite Forall_forall; auto.
Qed.

Fact Forall_cons_inv X (P : X -> Prop) x ll : Forall P (x::ll) <-> P x /\ Forall P ll.
Proof.
  split.
  inversion_clear 1; auto.
  constructor; tauto.
Qed.

Fact Forall2_cons_inv X Y R x l y m : @Forall2 X Y R (x::l) (y::m) <-> R x y /\ Forall2 R l m.
Proof.
  split.
  inversion_clear 1; auto.
  intros []; constructor; auto.
Qed.

Definition list_prod X Y Z (p : X -> Y -> Z) lX lY := flat_map (fun x => map (p x) lY) lX.

Fact list_prod_spec X Y Z p l m z : In z (@list_prod X Y Z p l m) <-> exists x y, z = p x y /\ In x l /\ In y m.
Proof.
  unfold list_prod.
  rewrite in_flat_map.
  split.
  intros (x & Hx & Hz).
  rewrite in_map_iff in Hz.
  destruct Hz as (y & ? & ?).
  exists x,y; auto.
  intros (x & y & ? & ? & ?); subst.
  exists x; split; auto. 
  apply in_map_iff; exists y; auto.
Qed.

