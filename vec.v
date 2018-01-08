(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega Max List.

Require Import notations tac_utils list_utils nat_utils pos.

Set Implicit Arguments.

Section vector.

  Variable X : Type.

  Inductive vec : nat -> Type :=
    | vec_nil  : vec 0
    | vec_cons : forall n, X -> vec n -> vec (S n).

  Let vec_split_type n := 
    match n with
      | 0   => Prop
      | S n => (X * vec n)%type
    end.

  Definition vec_split n (v : vec n) : vec_split_type n :=
    match v in vec k return vec_split_type k with
      | vec_nil  => False
      | @vec_cons n x v => (x,v)
    end.
    
  Definition vec_head n (v : vec (S n)) := match v with @vec_cons _ x _ => x end.
  Definition vec_tail n (v : vec (S n)) := match v with @vec_cons _ _ w => w end.
    
(*

  Definition vec_head n (v : vec (S n)) := fst (vec_split v).
  Definition vec_tail n (v : vec (S n)) := snd (vec_split v).
  
*)

  Let vec_head_tail_type n : vec n -> Prop := 
    match n with
      | 0   => fun v => v = vec_nil
      | S n => fun v => v = vec_cons (vec_head v) (vec_tail v)
    end.

  Let vec_head_tail_prop n v :  @vec_head_tail_type n v.
  Proof. induction v; simpl; auto. Qed.

  Fact vec_0_nil (v : vec 0) : v = vec_nil.
  Proof. apply (vec_head_tail_prop v). Qed.

  Fact vec_head_tail n (v : vec (S n)) : v = vec_cons (vec_head v) (vec_tail v).
  Proof. apply (vec_head_tail_prop v). Qed.

  Fact vec_n0_cons n (v : vec (S n)) : exists x w, v = vec_cons x w.
  Proof.
    exists (vec_head v), (vec_tail v).
    apply vec_head_tail.
  Qed.

  Fixpoint vec_get n (v : vec n) k {struct v} : k < n -> X.
  refine(  
    match v in vec q return k < q -> X with
    | vec_nil          => fun H => _
    | @vec_cons n' x w  => match k as q return q < S n' -> X with 
                 | 0    => fun _ => x
  	         | S k' => fun H => vec_get _ w k' _
  	    end
    end).
    apply lt_n_0 in H; destruct H.
    apply lt_S_n; assumption.
  Defined.

  Arguments vec_get [ n ] _ _ _.

  Fact vec_get_eq n v x y (Hx : x < n) (Hy : y < n) : x = y -> vec_get v x Hx = vec_get v y Hy.
  Proof. 
    intro; subst y.  
    revert x Hx Hy.
    induction v; intros a H H'.
    contradict H; omega.
    unfold vec_get; fold vec_get.
    destruct a; trivial.
  Qed.

  Fact vec_get_ext n v w : (forall i Hi, @vec_get n v i Hi = vec_get w i Hi) -> v = w. 
  Proof.
    revert w; induction v as [ | n x v IHv ]; intros w H.
    rewrite (vec_0_nil w); auto.
    revert H; rewrite (vec_head_tail w); intros H; f_equal.
    apply (H _ (lt_0_Sn _)).
    apply IHv.
    intros i Hi; generalize (H _ (lt_n_S _ _ Hi)); simpl.
    eqgoal; f_equal; apply vec_get_eq; auto.
  Qed.

  Fact vec_get_cons n x v : forall i (H : S i < S n) (H' : i < n),  vec_get (vec_cons x v) _ H = vec_get v _ H'.
  Proof.
    destruct v as [ | n x' w ]; intros i H.
    contradict H; omega.
    simpl; induction i; intros; trivial.
    apply vec_get_eq; auto.
  Qed.
  
  Fact vec_get_cons' k (x : X) v i Hi : @vec_get (S k) (vec_cons x v) (S i) Hi = vec_get v i (lt_S_n _ _ Hi).
  Proof.
    apply vec_get_cons.
  Qed.
  
  Fact vec_get_0 k v H : @vec_get (S k) v 0 H = vec_head v.
  Proof.
    rewrite (vec_head_tail v); reflexivity.
  Qed.

  Fixpoint vec_end n x (v : vec n) : vec (S n) := 
    match v with 
      | vec_nil => vec_cons x vec_nil
      | @vec_cons n' y w => vec_cons y (vec_end x w)
    end.
  
  Fact vec_get_end_0 n x v : forall i (H : i < S n) (H' : i < n), vec_get (@vec_end n x v) _ H = vec_get v _ H'.
  Proof.
    induction v; intros i H H'; try omega.
    simpl vec_end.
    destruct i; simpl; auto.
  Qed.
  
  Fact vec_get_end_1 n x v : forall (H : n < S n), vec_get (@vec_end n x v) _ H = x.
  Proof.
    induction v; intros H; auto.
    simpl vec_end.
    rewrite vec_get_cons with (H' := lt_S_n _ _ H).
    apply IHv.
  Qed.

  Fixpoint vec_app n (v : vec n) m (w : vec m) : vec (n+m) :=
    match v in vec k return vec (k+m) with
      | vec_nil        => w
      | @vec_cons n x v => vec_cons x (vec_app v w)
    end.

  Fact vec_get_app_l n v m w i (H1 : i < n+m) (H2 : i < n) :
     vec_get (@vec_app n v m w) i H1 = vec_get v _ H2.
  Proof.
    revert i H1 H2.
    induction v as [ | n x v IHv ]; simpl; intros [ | i ] H1 H2;
      try omega; auto.
  Qed.

  Let vec_get_app_r_lt n m i : i < n+m -> n <= i -> i-n < m.
  Proof. abstract omega. Qed.

  Let vec_get_app_rec n v m w i (H1 : i < m) :
      vec_get (@vec_app n v m w) _ (plus_lt_compat_l _ _ _ H1)
    = vec_get w _ H1.
  Proof.
    induction v as [ | n x v IHv ]; simpl.
    apply vec_get_eq; auto.
    rewrite <- IHv.
    apply vec_get_eq; auto.
  Qed.

  Fact vec_get_app_r n v m w i (H1 : i < n+m) (H2 : n <= i) :
    vec_get (@vec_app n v m w) i H1 = vec_get w _ (vec_get_app_r_lt _ H1 H2).
  Proof.
    assert (i-n < m) as H3. abstract omega.
    generalize (vec_get_app_rec v w H3).
    eqgoal; f_equal; apply vec_get_eq; auto.
    omega.
  Qed.

  Fixpoint vec_change n (v : vec n) i (x : X) {struct v}: vec n :=
    match v in vec k, i return vec k with
      | vec_nil        , _   => vec_nil
      | @vec_cons _ _ w , 0   => vec_cons x w
      | @vec_cons _ y w , S i => vec_cons y (vec_change w i x)	
  end.	

  Fact vec_get_change_eq n a v : forall i (H : i < n), vec_get (vec_change v i a) _ H = a.
  Proof.
    induction v; intros i H.
    exfalso; apply lt_n_0 in H; auto.
    destruct i; simpl; trivial.
  Qed.

  Fact vec_get_change_neq: forall n x v i j (D: i <> j) (H : j < n), vec_get (vec_change v i x) _ H = vec_get v _ H.
  Proof.   
    induction v as [ | n y v IHv ]; intros i j D H.
    exfalso; apply lt_n_0 in H; auto.
    destruct i; destruct j; trivial.
    contradict D; trivial.
    simpl; apply IHv.
    contradict D; subst; auto.
  Qed.

  Definition vec_set n : forall (f : forall x, x < n -> X), vec n.
  Proof.
    induction n as [ | n IHn ]; intros f.
    exact vec_nil.
    apply vec_cons with (1 := f _ (lt_O_Sn _)).
    apply IHn.
    intros x Hx.
    apply (f (S x)).
    apply lt_n_S; assumption.
  Defined.

  Fact vec_get_set n f x Hx : vec_get (@vec_set n f) x Hx = f x Hx.
  Proof.
    revert f x Hx; induction n as [ | n IHn ]; intros f x Hx; simpl.
    omega.
    destruct x as [ | x ].
    f_equal; apply le_pirr.
    rewrite IHn; f_equal; apply le_pirr.
  Qed.   

  Fact vec_set_get n v : vec_set (@vec_get n v) = v.
  Proof.
    apply vec_get_ext.
    intros; rewrite vec_get_set; auto.
  Qed.

  Fixpoint vec_rev_init (f : nat -> X) n {struct n}: vec n :=
    match n return vec n with
    | 0   => vec_nil
    | S m => vec_cons (f n) (vec_rev_init f _)
    end.

  Definition vec_init f n := vec_rev_init (fun m => f (n-m)) n.

  Fact vec_get_rev_init f n : forall i (H : i < n), vec_get (vec_rev_init f n) _ H = f (n-i).
  Proof.
    induction n; intros i H.
    contradict H; omega.
    destruct i; simpl; trivial.
  Qed.

  Fact vec_get_init f n i (H : i < n) : vec_get (vec_init f n) i H = f i.
  Proof.
    unfold vec_init; intros; rewrite vec_get_rev_init.
    f_equal; omega.
  Qed.

  Definition vec_repeat x := vec_init (fun _ => x).

  Proposition vec_repeat_prop x : forall n i (Hi : i < n), vec_get (vec_repeat x n) _ Hi = x.
  Proof. apply vec_get_init. Qed.

  Section vec_fall.

    Variable P : X -> Prop.
  
    Definition vec_fall n (v : vec n) := forall x H, P (vec_get v x H).

    Theorem vec_fall_nil : vec_fall vec_nil.
    Proof. intros ? ?; exfalso; omega. Qed. 

    Theorem vec_fall_cons n x (l : vec n) : vec_fall (vec_cons x l) <->  (P x /\ vec_fall l).
    Proof.
      split.
      
      intros H1; split. 
      generalize (H1 _ (lt_O_Sn _)); auto.
      intros i Hi.
      generalize (lt_n_S _ _ Hi); intros Hx'.
      generalize (H1 _ Hx').
      simpl.
      match goal with |- P ?x -> P ?y => cutrewrite (x=y); auto end.
      apply vec_get_eq; auto. 
      intros [ H1 H2 ] [ | y ] Hy; simpl; auto.
    Qed.

  End vec_fall.
  
End vector.

Hint Resolve vec_get_eq.

Arguments vec_get [ X n ] _ _ _.

Section vector_max.

  Fixpoint vec_max n l : nat :=
    match l with
      | vec_nil _      => 0
      | vec_cons  a l => max a (vec_max _ l)
    end.

  Fact vec_get_max n l : forall i (H : i < n), vec_get l i H <= vec_max l.
  Proof.
   induction l; intros i H.
   contradict H; omega.
   induction i; simpl.
   apply le_max_l.
   apply le_trans with (2 := le_max_r _ _).
   apply IHl.
  Qed.

  Fact vec_max_eq_n0 n (l : vec _ n) : 0 < n -> { i : nat & { H : i < n | vec_get l i H = vec_max l }}.
  Proof.
    induction l; intros Hn.
    contradict Hn; omega.
    induction n.
    exists 0. exists (le_refl _).
    rewrite (vec_0_nil l); simpl; rewrite max_l; omega.
    clear IHn. destruct IHl as [ i [ Hi IH ] ]; [ omega | idtac ].
    destruct (max_dec x (vec_max l)) as [ H | H ].
    exists 0. exists Hn. simpl. omega.
    exists (S i). exists (lt_n_S _ _ Hi).
    unfold vec_max; fold vec_max.
    rewrite vec_get_cons with (H' := Hi), IH. auto.
  Qed.

  Fact vec_max_eq_0 (l : vec _ 0) : vec_max l = 0.
  Proof. rewrite (vec_0_nil _); reflexivity. Qed.

  Fact vec_max_lub n : forall (l : vec _ n) m, (forall x Hx, vec_get l x Hx <= m) -> vec_max l <= m.
  Proof.
    induction n; intros l m H.
    rewrite vec_max_eq_0. omega.
    assert (0 < S n) as Hn. 
      omega.
    destruct (vec_max_eq_n0 l Hn) as [ i [ Hi H' ] ].
    rewrite <- H'. apply H.
  Qed.

End vector_max.

Section vector_sum.

  Fixpoint vec_sum n l : nat :=
    match l with
      | vec_nil _     => 0
      | vec_cons a l => a + vec_sum _ l
    end.

  Fact vec_set_sum n (f : forall i, i < n -> nat) : finite_sum f = vec_sum (vec_set f).
  Proof.
    revert f; induction n; simpl; auto.
  Qed.

End vector_sum.

(* notations *)

Arguments vec_nil [ X ].

Infix "##" := vec_cons (at level 60, right associativity).

Section vec_pos.

  Variable (X : Type).
  
  (* If I use pos_S_invert instead of pos_S_inv then vec_pos cannot
     be used in the definition of the recalg_rect fixpoint *)

  Fixpoint vec_pos n (v : vec X n) : pos n -> X.
  Proof.
    refine (match v with
             | vec_nil => fun p => _
             | @vec_cons _ n x v => fun p => _
            end); invert pos p.
    exact x.
    exact (vec_pos _ v p).
  Defined.

  Fact vec_pos0 n (v : vec X (S n)) : vec_pos v pos0 = vec_head v.
  Proof. 
    rewrite (vec_head_tail v).
    reflexivity.
  Qed.
  
  Fact vec_get_pos n v p H : vec_get v (pos2nat p) H = @vec_pos n v p.
  Proof.
    revert p H; induction v as [ | n x v Hv ]; intros p H; invert pos p; auto.
    apply Hv.
  Qed.
  
  Fact vec_get_pos_eq n v i Hi p : i = pos2nat p -> vec_get v i Hi = @vec_pos n v p.
  Proof.
    intros; subst; apply vec_get_pos.
  Qed.

  Fact vec_pos_tail n (v : vec X (S n)) p : vec_pos (vec_tail v) p = vec_pos v (pos_nxt _ p).
  Proof.
    rewrite vec_head_tail at 2; simpl; auto.
  Qed.
  
  Fact vec_pos1 n (v : vec X (S (S n))) : vec_pos v pos1 = vec_head (vec_tail v).
  Proof.
    rewrite <- vec_pos0, vec_pos_tail; auto.
  Qed.

  Fact vec_pos_ext n (v w : vec X n) : (forall p, vec_pos v p = vec_pos w p) -> v = w.
  Proof.
    revert v w; induction n as [ | n IHn ]; intros v w H.
    rewrite (vec_0_nil v), (vec_0_nil w); auto.
    revert H; rewrite (vec_head_tail v), (vec_head_tail w); f_equal.
    intros H; f_equal.
    apply (H pos0).
    apply IHn.
    intros p; apply (H (pos_nxt _ p)).
  Qed.

  Fixpoint vec_set_pos n : (pos n -> X) -> vec X n :=
    match n return (pos n -> X) -> vec X n with 
      | 0   => fun _ => @vec_nil _
      | S n => fun g => vec_cons (g pos0) (vec_set_pos (fun p => g (pos_nxt _ p)))
    end.

  Fact vec_pos_set n (g : pos n -> X) p : vec_pos (vec_set_pos g) p = g p. 
  Proof.
    revert g p; induction n as [ | n IHn ]; intros g p; pos_inv p; auto.
    apply IHn.
  Qed.
  
  Fact vec_pos_app_lft n m (v : vec X n) (w : vec X m) p : vec_pos (vec_app v w) (pos_lft _ p) = vec_pos v p.
  Proof.
    revert p; induction v; simpl; intros p; pos_inv p; simpl; auto.
  Qed.
  
  Fact vec_pos_app_rt n m (v : vec X n) (w : vec X m) p : vec_pos (vec_app v w) (pos_rt _ p) = vec_pos w p.
  Proof.
    induction v; simpl; auto.
  Qed.
  
  Definition vec_lft { n m } (v : vec X (n+m)) : vec X n := vec_set_pos (fun p => vec_pos v (pos_lft _ p)).
  Definition vec_rt { n m } (v : vec X (n+m)) : vec X m := vec_set_pos (fun p => vec_pos v (pos_rt _ p)).

  Fact vec_app_lft_rt n m (v : vec X (n+m)) : v = vec_app (vec_lft v) (vec_rt v).
  Proof.
    apply vec_pos_ext.
    intros p.
    unfold vec_lft, vec_rt.
    destruct (pos_split p) as [ (q & ?) | (q & ?) ]; subst p.
    rewrite vec_pos_app_lft, vec_pos_set; auto.
    rewrite vec_pos_app_rt, vec_pos_set; auto.
  Qed.
  
End vec_pos.

Fact vec_pos_sum n v p : vec_pos v p <= @vec_sum n v.
Proof.
  revert p; induction v; intros p; pos_inv p; simpl.
  omega.
  apply le_trans with (1 := IHv _); omega.
Qed.

Fact vec_sum_app n m v w : vec_sum (vec_app v w) = @vec_sum n v + @vec_sum m w.
Proof.
  induction v; simpl; auto.
  rewrite IHv; omega.
Qed.

Fact vec_sum_length n v : (forall p, 0 < vec_pos v p) -> n <= @vec_sum n v.
Proof.
  induction v; simpl; auto.
  intros H.
  generalize (H pos0) (fun p => H (pos_nxt _ p)); simpl; intros H1 H2.
  apply IHv in H2; omega.
Qed.

Fact vec_sum_min n v k : k <= n -> (forall i Hi, i < k -> 0 < vec_get v i Hi) -> k <= @vec_sum n v.
Proof.
  revert k.
  induction v; intros [ | k ] Hk H; simpl; auto.
  omega.
  apply le_S_n, IHv in Hk.
  generalize (H 0 (lt_0_Sn _)); simpl; omega.
  intros i H1 H2.
  specialize (H _ (lt_n_S _ _ H1) (lt_n_S _ _ H2)); simpl in H.
  revert H; eqgoal.
Qed.

Definition option_lift X Y (f : X -> Y) x :=
  match x with None => None | Some x => Some (f x) end.

Fact nth_error_map X Y (f : X -> Y) l i : nth_error (map f l) i = option_lift f (nth_error l i).
Proof.
  revert l; induction i; intros []; simpl; auto.
Qed.

Definition tail_error X (l : list X) :=
  match l with
    | nil  => None
    | _::l => Some l
  end.
  
Definition vec_list X n (v : vec X n) := map (vec_pos v) (pos_list n).

(* Fact vec_list_map X Y (f : X -> Y) n  : *)

Section vec_list.

  Variable X : Type.
  
  Fact vec_list_0 (v : vec X 0) : vec_list v = nil.
  Proof.
    rewrite (vec_0_nil v); auto.
  Qed.
  
  Fact vec_list_S n x (v : vec X n) : vec_list (x##v) = x::vec_list v.
  Proof.
    unfold vec_list; simpl; f_equal.
    rewrite map_map; simpl; auto.
  Qed.
 
  Fact vec_list_tail n (v : vec X (S n)) : tail_error (vec_list v) = Some (vec_list (vec_tail v)).
  Proof.
    rewrite (vec_head_tail v) at 1.
    simpl; rewrite map_map; simpl; auto.
  Qed.
  
  Fact vec_list_get n (v : vec X _) i (H : i < n) : nth_error (vec_list v) i = Some (vec_get v i H).
  Proof.
    revert v i H; induction n as [ | n IHn ]; intros v i H.
    omega.
    rewrite (vec_head_tail _).
    destruct i as [ | i ].
    unfold vec_list; simpl; auto.
    unfold vec_list; simpl.
    rewrite map_map; simpl.
    rewrite <- IHn; auto.
  Qed.
  
  Fact vec_list_split n (v : vec X n) k (Hk : k < n) : exists l r, vec_list v = l++vec_get v k Hk::r /\ k = length l.
  Proof.
    revert v k Hk; induction n as [ | n IHn ]; intros v k Hk.
    omega.
    rewrite (vec_head_tail v).
    destruct k as [ | k ].
    
    exists nil, (vec_list (vec_tail v)).
    rewrite vec_list_S; auto.
    
    destruct (IHn (vec_tail v) k (lt_S_n _ _ Hk)) as (l & r & H).
    exists (vec_head v::l), r.
    rewrite vec_list_S; simpl; split; f_equal; tauto.
  Qed.
  
End vec_list.

Section vector_map.

  Variables A B: Type.

  Section def.
 
    Variable f : A -> B.
    
    Fixpoint vec_map n (l : vec A n) {struct l} : vec B n :=
      match l in vec _ n return vec _ n with
        | vec_nil      => @vec_nil B
        | vec_cons a q => vec_cons (f a) (vec_map q)
      end.

  End def.

  Arguments vec_map f [ n ] _.

  Fact vec_get_map f n l : forall i (H : i < n), vec_get (vec_map f l) _ H = f (vec_get l _ H).
  Proof.
    induction l; intros i H.
    contradict H; omega.
    destruct i; simpl; trivial.
  Qed.

  Fact vec_map_get_ext f g n l : (forall i (H : i < n), f (vec_get l _ H) = g (vec_get l _ H)) -> vec_map f l = vec_map g l.
  Proof.
    induction l; intros H.
    trivial.
    simpl. f_equal.
    assert (0 < S n) as H'. 
      omega.
    apply (H _ H').
    apply IHl.
    intros i H'.
    assert (S i < S n) as H''. 
      omega.
    generalize (H _ H''); simpl.
    match goal with 
      |- ?a = ?b -> _ = _ => transitivity a; [ idtac | transitivity b ]
    end; auto; f_equal; auto.
  Qed.
  
  Fact vec_pos_map f n v (p : pos n) : vec_pos (vec_map f v) p = f (vec_pos v p).
  Proof.
    revert p; induction v; intros p; pos_inv p; simpl; auto.
  Qed.

End vector_map.

Arguments vec_get_map [ A B ] f [ n ] _ _ _.

Fact vec_map_map A B C (f : A -> B) (g : B -> C) n (v : vec A n) :
    vec_map g (vec_map f v) = vec_map (fun x => g (f x)) v.
Proof.
  induction v; simpl; f_equal; auto.
Qed.

Section vector_instanciate.

  Variable A B : Type.

  Definition vec_inst n (l : vec (A->B) n) (a : A) := vec_map (fun f => f a) l.
  
  Fact vec_get_inst n l : forall a i (H : i < n), vec_get (vec_inst l a) i H = vec_get l i H a.
  Proof. intros; apply vec_get_map. Qed.

End vector_instanciate.

Section vec_swap.

  Variable (X : Type) (n : nat).
  
  Definition vec_swap (v : vec X (S (S n))) := vec_set_pos (fun p => vec_pos v (pos_swap p)).
   
  Fact vec_pos0_swap v : vec_pos (vec_swap v) pos0 = vec_pos v pos1.
  Proof.
    unfold vec_swap; rewrite vec_pos_set; auto.
  Qed.
    
  Fact vec_pos1_swap v : vec_pos (vec_swap v) pos1 = vec_pos v pos0.
  Proof.
    unfold vec_swap; rewrite vec_pos_set; auto.
  Qed.
  
  Fact vec_pos_swap v p : vec_pos (vec_swap v) (pos_nxt _ (pos_nxt _ p)) = vec_pos v (pos_nxt _ (pos_nxt _ p)).
  Proof.
    unfold vec_swap; rewrite vec_pos_set; auto.
  Qed.
  
  Fact vec_head_swap v : vec_head (vec_swap v) = vec_head (vec_tail v).
  Proof.
    rewrite <- vec_pos0; unfold vec_swap; rewrite vec_pos_set; simpl.
    rewrite <- vec_pos_tail, vec_pos0; auto.
  Qed.
  
  Fact vec_tail_swap v : vec_tail (vec_swap v) = vec_head v ## vec_tail (vec_tail v).
  Proof.
    apply vec_pos_ext; intros p.
    rewrite vec_pos_tail.
    pos_inv p.
    rewrite vec_pos0; auto.
    rewrite vec_pos_set.
    simpl; do 2 rewrite vec_pos_tail; auto.
  Qed.
  
End vec_swap.

Section vec_reif.

  Variable (n : nat) (X : Type) (R : pos n -> X -> Prop).
  
  Definition vec_reif : (forall p, exists x, R p x) -> exists v, forall p, R p (vec_pos v p).
  Proof.
    intros H.
    apply pos_reification in H.
    destruct H as (f & Hf).
    exists (vec_set_pos f).
    intro; rewrite vec_pos_set; auto.
  Qed.
  
End vec_reif.

Fixpoint vec_reif_t X n : forall R : pos n -> X -> Prop, (forall p, {x | R p x}) -> {v | forall p, R p (vec_pos v p) }.
Proof.
  refine (match n with 
    | 0   => fun R _  => exist _ vec_nil _
    | S n => fun R HR => match HR pos0 with
      | exist _ x Hx => match vec_reif_t X n (fun p x => R (pos_nxt _ p) x) _ with
        | exist _ v Hv => exist _ (x##v) _
      end
    end
  end).
  intros p; pos_inv p.
  intros; apply HR.
  intros p; pos_inv p; auto.
Defined.

Section pos_choice.

  Fact pos_simple_choice U k (P Q : pos k -> U -> Prop) : 
        (forall p, { u | P p u } + { forall u, Q p u })
     -> { u | forall p, P p (vec_pos u p) }
      + { p | forall u, Q p u }.
  Proof.
    revert P Q.
    induction k as [ | k IHk ]; intros P Q HPQ.
    left; exists vec_nil; intro p; pos_inv p.
    destruct (HPQ pos0) as [ (u & Hu) | H0 ].
    destruct (IHk (fun p => P (pos_nxt _ p)) (fun p => Q (pos_nxt _ p)))
      as [ (f & Hf) | (p & Hp) ].
    intros; apply HPQ.
    left; exists (u##f).
    intros p; pos_inv p; simpl; auto.
    right; exists (pos_nxt _ p); auto.
    right; exists pos0; auto.
  Qed.  

  Fact pos_double_choice U V k (P Q : pos k -> U -> V -> Prop) : 
        (forall p, { u : _ & { v | P p u v } } + { forall u v, Q p u v })
     -> { u : _ & { v | forall p, P p (vec_pos u p) (vec_pos v p) } }
      + { p | forall u v, Q p u v }.
  Proof.
    revert P Q.
    induction k as [ | k IHk ]; intros P Q HPQ.
    left; exists vec_nil, vec_nil; intro p; pos_inv p.
    destruct (HPQ pos0) as [ (u & v & Huv) | H0 ].
    destruct (IHk (fun p => P (pos_nxt _ p)) (fun p => Q (pos_nxt _ p)))
      as [ (f & g & Hfg) | (p & Hp) ].
    intros; apply HPQ.
    left; exists (u##f), (v##g).
    intros p; pos_inv p; simpl; auto.
    right; exists (pos_nxt _ p); auto.
    right; exists pos0; auto.
  Qed.
  
  Definition pos_reif2_t U V k (P : pos k -> U -> V -> Prop) :
       (forall p, { u : _ & { v | P p u v } }) -> { f : _ & { g | forall p, P p (vec_pos f p) (vec_pos g p) } }.
  Proof.
    intros HP.
    destruct (pos_double_choice P (fun _ _ _ => False)) as [ | (p & Hp) ]; auto.
    destruct (HP p) as (u & v & _); tauto.
  Qed.

End pos_choice.

Section vec_sub.

  Definition vec_sub X n (v : vec X n) i : i < n -> { w : vec X i | forall j H1 H2, vec_get w j H1 = vec_get v j H2 }.
  Proof.
    intros Hi.
    assert (forall p : pos i, pos2nat p < n) as H.
      intro p; apply lt_trans with (2 := Hi), (pos2nat_prop p).
    exists (vec_set_pos (fun p => vec_get v (pos2nat p) (H p))).
    intros j H1 H2.
    rewrite vec_get_pos_eq with (p := nat2pos H1), 
            vec_pos_set.
    apply vec_get_eq; rewrite pos2nat_nat2pos; auto.
    rewrite pos2nat_nat2pos; auto.
  Qed.

  Definition vec_positive_sub n (v : vec nat n) : { i : _ & { H : i < n & { w : vec nat i | vec_get v _ H = 0 
                                                                    /\ forall j H1 H2, vec_get v j H1 = S (vec_get w j H2) } } }
                                                + { forall i Hi, 0 < vec_get v i Hi }.
  Proof.
    induction v as [ | n [ | x ] v IHv ].
    right; intros; omega.
    left; exists 0, (lt_0_Sn _), vec_nil; simpl; split; auto; intros; omega.
    destruct IHv as [ (i & Hi & w & H1 & H2) | IHv ].
    left; exists (S i), (lt_n_S _ _ Hi), (x##w); split; simpl.
    revert H1; eqgoal; auto.
    intros [ | ] ?; auto.
    right. intros [|] ?; simpl; auto; omega.
  Qed.

End vec_sub.

Section vec_strict_pos.

  Definition vec_strict_pos n (v : vec nat n) : (forall p, 0 < vec_pos v p) + { p | 0 = vec_pos v p }.
  Proof.
    induction v as [ n | n [ | x ] v IHv ].
    left; intros p; pos_inv p.
    right; exists pos0; auto.
    destruct IHv as [ IHv | (p & Hp) ].
    left; intros p; pos_inv p; simpl; auto; omega.
    right; exists (pos_nxt _ p); auto.
  Qed.

End vec_strict_pos.

    
   
