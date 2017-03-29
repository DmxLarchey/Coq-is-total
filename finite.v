(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List.

Require Import list_utils.

Set Implicit Arguments.

Definition finite_t X (P : X -> Prop) := { l | forall x, In x l <-> P x }.

Section finite_t.

  Fact finite_t_pair X Y (P : X -> Prop) (Q : Y -> Prop) :
    finite_t P -> finite_t Q -> finite_t (fun c => P (fst c) /\ Q (snd c)).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (list_prod (@pair _ _) l m).
    intro c; rewrite list_prod_spec, <- Hl, <- Hm.
    split.
    intros (x & y & ? & ? & ?); subst; simpl; auto.
    destruct c as (x,y); exists x, y; simpl; auto.
  Qed. 

  Fact finite_t_Forall X Y (R : X -> Y -> Prop) l : 
    (forall x, In x l -> finite_t (R x)) -> finite_t (Forall2 R l).
  Proof.
    intros Hl; induction l as [ | x l IHl ].
    exists (nil::nil).
    intros x; split.
    intros [ ? | [] ]; subst; constructor.
    inversion_clear 1; left; auto.
    destruct (Hl _ (or_introl eq_refl)) as (l1 & Hl1).
    destruct IHl as (mm1 & Hmm1).
    intros; apply Hl; right; auto.
    exists (list_prod (@cons _) l1 mm1); intros c.
    rewrite list_prod_spec.
    split.
    intros (y & m & ? & ? & ?); subst; constructor.
    apply Hl1; auto.
    apply Hmm1; auto.
    intros H.
    destruct c as [ | y m ].
    inversion H.
    rewrite Forall2_cons_inv in H.
    destruct H as (H1 & H2).
    exists y, m; split; auto; split.
    apply Hl1; auto.
    apply Hmm1; auto.
  Qed.
  
  (* Filtering out a finite set with a decidable functions gives a finite set 
     A VERY handy result *) 
  
  Fact finite_t_dec X (P Q : X -> Prop) : (forall x, { P x } + { ~ P x }) -> finite_t Q -> finite_t (fun x => P x /\ Q x).
  Proof.
    intros HP (l & Hl).
    exists (filter (fun x => if HP x then true else false) l).
    intros x.
    rewrite filter_In, <- Hl.
    destruct (HP x); split; try tauto.
    intros (_ & C); discriminate C.
  Qed.
  
  (* Mapping a finite set by a finitetary relation gives a finite set *)
  
  Fact finite_t_map X Y (P : X -> Prop) (Q : X -> Y -> Prop) : 
      finite_t P
   -> (forall x, P x -> finite_t (Q x)) 
   -> finite_t (fun y => exists x, P x /\ Q x y).
  Proof.
    intros (l & Hll) H.
    assert (forall x, In x l -> finite_t (Q x)) as H1.
      intros x Hx; rewrite Hll in Hx; auto.
    assert (finite_t (fun y => exists x, In x l /\ Q x y)) as H2.
      clear P Hll H.
      induction l as [ | x l IHl ].
      exists nil.
      intros x; split.
      intros [].
      intros (? & [] & _).
      destruct (H1 _ (or_introl eq_refl)) as (l1 & Hl1).
      destruct IHl as (l2 & Hl2).
      intros; apply H1; right; auto.
      exists (l1++l2).
      intros y; split.
      intros Hy; apply in_app_or in Hy.
      destruct Hy as [ Hy | Hy ].
      exists x; split; simpl; auto; apply Hl1; auto.
      apply Hl2 in Hy. 
      destruct Hy as (v & ? & ?); exists v; split; auto.
      right; auto.
      intros (u & [ ? | ? ] & H2); subst; apply in_or_app.
      left; apply Hl1; auto.
      right; apply Hl2; exists u; auto.
    destruct H2 as (m & Hm).
    exists m; intro; rewrite Hm.
    split; intros (u & ? & ?); exists u; split; auto; apply Hll; auto.
  Qed.
  
  Fact finite_t_plus n : finite_t (fun c => fst c + snd c = n).
  Proof.
    exists (map (fun x => (x,n-x)) (list_n (S n))).
    intros c; rewrite in_map_iff; split.
    intros (a & ? & H); subst; simpl.
    apply list_n_spec in H; omega.
    destruct c as (x,y); exists x.
    rewrite list_n_spec; simpl in H.
    split; [ f_equal | ]; omega.
  Qed.
  
  Fact finite_t_plus_lt n : finite_t (fun c => 0 < fst c /\ 0 < snd c /\ fst c + snd c = n).
  Proof.
    do 2 (apply finite_t_dec; [ intro; apply lt_dec | ]).
    apply finite_t_plus.
  Qed.
  
  (* There are only finitely many bounded lists of nat (bound on elements + bound on length *)

  Definition finite_t_list_bounded n m : finite_t (fun l => Forall (ge n) l /\ length l < m).
  Proof.
    induction m as [ | m (l & Hl) ].
    exists nil; simpl; intros; split; omega.
    exists (nil::list_prod (@cons _) (list_n (S n)) l).
    intros [ | a k ].
    simpl; split; auto; split; auto; omega.
    split.
    intros [ H | H ].
    discriminate H.
    apply list_prod_spec in H.
    destruct H as (x & y & E & H1 & H2).
    injection E; clear E; intros; subst x y.
    apply list_n_spec in H1.
    apply Hl in H2.
    split; simpl; try omega; constructor; try tauto; omega.
    intros (H1 & H2).
    apply Forall_cons_inv in H1.
    simpl in H2.
    right; apply list_prod_spec.
    exists a, k; split; auto.
    split.
    apply list_n_spec; omega.
    apply Hl; split; try tauto; omega.
  Qed.
  
  (* By filtering, lists of bounded length with a given total sum are in finite number *)
    
  Definition finite_t_part_lsum n m : finite_t (fun l => lsum l = n /\ length l < m).
  Proof.
    generalize (finite_t_list_bounded n m).
    intros H.
    apply finite_t_dec with (P := fun l => lsum l = n) in H.
    2: intro; apply eq_nat_dec.
    destruct H as (l & Hl); exists l.
    intros x; rewrite Hl.
    split; try tauto.
    intros (H1 & H2); repeat split; auto.
    rewrite Forall_forall.
    intros y Hy.
    generalize (lsum_le y x Hy); omega.
  Qed.
  
  (* By filterging again, lists of strictly positive numbers of a given total sum 
     are in finite number as well *)

  Definition finite_t_partition n : finite_t (fun l => Forall (lt 0) l /\ lsum l = n).
  Proof.
    generalize (finite_t_part_lsum n (S n)); intros H.
    apply finite_t_dec with (P := Forall (lt 0)) in H.
    2: intro; apply Forall_dec; intros; apply lt_dec.
    destruct H as (l & Hl); exists l; intros x; rewrite Hl.
    split; try tauto.
    intros (H1 & H2); repeat split; auto.
    clear Hl l; apply le_n_S.
    revert H1 n H2.
    induction 1 as [ | x l Hx Hl IH ]; intros n ?; simpl.
    omega.
    simpl in H2.
    specialize (IH (n - x)).
    apply le_trans with (S (n-x)).
    apply le_n_S, IH; omega.
    omega.
  Qed.
  
  Fact finite_t_part n : finite_t (fun ln => match ln with 
                                               | nil   => False 
                                               | x::ln => Forall (lt 0) ln 
                                                       /\ x + lsum ln = n
                                             end).
  Proof.
    set (P c := fst c + snd c = n).
    set (Q c l := match l with 
                    | nil  => False
                    | x::l => x = fst c /\ Forall (lt 0) l /\ lsum l = snd c
                  end).
    destruct (@finite_t_map _ _ P Q (finite_t_plus n)) as (l & Hl).
    unfold P, Q; intros (a,b); simpl; intros Hab.
    destruct (finite_t_partition b) as (m & Hm).
    exists (map (cons a) m).
    intros l; rewrite in_map_iff.
    split.
    intros (x & ? & Hx); subst; split; auto; apply Hm; auto.
    destruct l as [ | x l ].
    intros [].
    intros (? & H1 & H2); subst; exists l; split; auto.
    apply Hm; auto.
    
    exists l; intros x.
    rewrite Hl; unfold P, Q.
    split; destruct x as [ | u m ].
    intros (? & ? & []).
    intros ( (a,b) & ? & ? & ? & ?); simpl in *; split; auto; omega.
    intros [].
    intros (? & ?); exists (u,lsum m); simpl; auto.
  Qed.
  
End finite_t.