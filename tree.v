(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List.

Require Import notations acc_utils list_utils finite.

Set Implicit Arguments.

Section trees.

  Variable (X : Type).

  (* we do not want the too weak Coq generated induction principles *)

  Unset Elimination Schemes.

  Inductive tree : Type := in_tree : X -> list tree -> tree.

  Set Elimination Schemes.

  Definition tree_root t := match t with in_tree x _ => x end.
  Definition tree_sons t := match t with in_tree _ l => l end.

  Fact tree_root_sons_eq t : t = in_tree (tree_root t) (tree_sons t).
  Proof. destruct t; auto. Qed.
  
  (* the immediate subtree relation *)
  
  Definition imsub_tree s t := match t with in_tree _ ll => In s ll end.
  
  Infix "<ist" := imsub_tree (at level 70).
  
  Fact imsub_tree_fix s t :  s <ist t <-> exists x ll, In s ll /\ t = in_tree x ll.
  Proof.
    split.
    destruct t as [ x ll ]; exists x, ll; auto.
    intros (x & ll & H1 & ?); subst; auto.
  Qed.
  
  (* The immediate subtree relation is well founded *)
  
  Fixpoint imsub_tree_wf t : Acc imsub_tree t.
  Proof.
    refine (
      match t with
        | in_tree x ll => Acc_intro _ _
      end); simpl; clear x t.
    induction ll as [ | x ll IH ].
    intros _ [].
    intros ? [ [] | ].
    apply imsub_tree_wf.
    apply IH; auto.
  Qed.

  (* let us define our own induction principles *)

  Section tree_rect.

    Variable P : tree -> Type.
    Hypothesis f : forall a ll, (forall x, In x ll -> P x) -> P (in_tree a ll).

    Let f' : forall t, (forall x, x <ist t -> P x) -> P t.
    Proof.
      intros []; apply f.
    Defined.

    Definition tree_rect t : P t.
    Proof.
      apply Fix with (1 := imsub_tree_wf), f'.
    Defined.

    Section tree_rect_fix.
    
      Variable E : forall t, P t -> P t -> Prop.

      Hypothesis f_ext : forall a ll f1 f2, (forall x Hx, E (f1 x Hx) (f2 x Hx)) -> E (f a ll f1) (f a ll f2).

      (* Coq recursive type-checking does not allow such a definition 
         but it is possible to prove this identity
      *)

      Fact tree_rect_fix a ll : E (tree_rect (in_tree a ll)) (f a ll (fun t _ => tree_rect t)).
      Proof.
        unfold tree_rect, Fix.
        rewrite <- Fix_F_eq; unfold f'.
        apply f_ext; intros; apply Fix_F_ext.
        intros [] ? ?; apply f_ext.
      Qed.
      
    End tree_rect_fix.
    
    Section tree_rect_fix_eq.

      Hypothesis f_ext : forall a ll f1 f2, (forall x Hx, f1 x Hx = f2 x Hx) -> f a ll f1 = f a ll f2.
      
      Fact tree_rect_fix_eq a ll : tree_rect (in_tree a ll) = f a ll (fun t _ => tree_rect t).
      Proof.
        apply tree_rect_fix with (E := fun _ => @eq _); simpl; auto.
      Qed.
      
    End tree_rect_fix_eq.

  End tree_rect.
  
  Definition tree_rec (P : tree -> Set)  := tree_rect P.
  Definition tree_ind (P : tree -> Prop) := tree_rect P.

  Section tree_recursion.

    (* the particular case when the output type does not depend on the tree *)

    Variables (Y : Type) (f : X -> list tree -> list Y -> Y).    
  
    Definition tree_recursion : tree -> Y.
    Proof.
      apply tree_rect.
      intros x ll IH.
      apply (f x ll (list_In_map _ IH)).
    Defined.
    
    (* In that case, extensionnality is for free *)

    Fact tree_recursion_fix x ll : tree_recursion (in_tree x ll) = f x ll (map tree_recursion ll).
    Proof.
      unfold tree_recursion at 1.
      rewrite tree_rect_fix with (E := fun _ => eq).
      f_equal; apply list_In_map_eq_map.
      clear x ll; intros x ll g h H; simpl.
      f_equal; apply list_In_map_ext, H.
    Qed.
  
  End tree_recursion.

  (* finite quantification over the nodes of trees *)

  Section tree_fall_exst.

    Variable P : X -> list tree -> Prop.

    Definition tree_fall (t : tree) : Prop.
    Proof.
      induction t as [ a ll IH ].
      exact (P a ll /\ forall x Hx, IH x Hx).
    Defined.

   (* this is how we would like tree_fall to be recursively defined but this would
       not be well-formed in Coq
    *)

    Fact tree_fall_fix x ll : tree_fall (in_tree x ll) <-> P x ll /\ forall t, In t ll -> tree_fall t. 
    Proof.
      unfold tree_fall at 1.
      rewrite tree_rect_fix 
        with (E := fun _ A B => A <-> B);
        firstorder.
    Qed.
 
    Section tree_fall_rect.
  
      Variable (Q : tree -> Type).
  
      Hypothesis HQ : forall x ll, tree_fall (in_tree x ll) -> (forall t, In t ll -> Q t) -> Q (in_tree x ll).
  
      Theorem tree_fall_rect t : tree_fall t -> Q t.
      Proof.
        induction t as [ x ll IH ]; intros H.
        apply HQ; auto.
        rewrite tree_fall_fix in H; destruct H; auto.
      Qed.

    End tree_fall_rect.
    
    Definition tree_fall_rec (Q : tree -> Set) := @tree_fall_rect Q.
    Definition tree_fall_ind (Q : tree -> Prop) := @tree_fall_rect Q.

    Definition tree_exst (t : tree) : Prop.
    Proof.
      induction t as [ a ll IH ].
      exact (P a ll \/ exists x Hx, IH x Hx).
    Defined.

    Let disj_eq_prop (A B B' : Prop) : (B <-> B') -> (A \/ B <-> A \/ B').
    Proof. tauto. Qed.

    Fact tree_exst_fix x ll : tree_exst (in_tree x ll) <-> P x ll \/ exists t, In t ll /\ tree_exst t. 
    Proof.
      unfold tree_exst at 1.
      rewrite tree_rect_fix 
        with (E := fun _ A B => A <-> B).
      apply disj_eq_prop.
      split; intros (y & ? & ?); exists y; split; auto.
      intros; apply disj_eq_prop.
      split; intros (y & Hy & ?); exists y, Hy; apply H; auto.
    Qed.

  End tree_fall_exst.

  Fact tree_fall_inc (P Q : _ -> _ -> Prop) : P inc2 Q -> tree_fall P inc1 tree_fall Q.
  Proof.
    intros H t; induction t as [ x ll IH ].
    repeat rewrite tree_fall_fix.
    intros []; split; auto.
  Qed.

  Fact tree_exst_inc (P Q : _ -> _ -> Prop) : P inc2 Q -> tree_exst P inc1 tree_exst Q.
  Proof.
    intros H t; induction t as [ x ll IH ].
    repeat rewrite tree_exst_fix.
    intros [| (t & ? & ?)]; [ left | right ]; auto; exists t; auto.
  Qed. 
  
  Section tree_fall_exst_dec.

    Variable (P Q : X -> list tree -> Prop).

    Hypothesis PQ_incomp : forall x ll, P x ll -> Q x ll -> False.
    
    Fact tree_fall_exst_incomp t : tree_fall P t -> tree_exst Q t -> False.
    Proof.
      induction t as [ x ll IH ].
      rewrite tree_fall_fix, tree_exst_fix.
      intros [ H1 H2 ] [ H3 | (t & H3 & H4) ].
      
      apply PQ_incomp with (1 := H1); auto.
      apply IH with (1 := H3); auto.
    Qed.      

    Hypothesis PQ_dec : forall x ll, { P x ll } + { Q x ll }.    
    
    Fact tree_fall_exst_dec t : { tree_fall P t } + { tree_exst Q t }.
    Proof.
      induction t as [ x ll IH ].
      destruct (list_choose_rec (tree_exst Q) (tree_fall P) ll) as [ (t & H1 & H2) | H1 ].
      intros z Hz; specialize (IH _ Hz); tauto.
      
      right.
      apply tree_exst_fix.
      right; exists t; auto.
      
      destruct (PQ_dec x ll) as [ | H2 ].
      
      left; apply tree_fall_fix; auto.
      
      right.
      apply tree_exst_fix.
      left; auto.
    Qed.
    
  End tree_fall_exst_dec.

  Section tree_fall_dec.
  
    Variable (P : X -> list tree -> Prop).

    Hypothesis PQ_dec : forall x ll, { P x ll } + { ~ P x ll }.
    
    Fact tree_fall_dec t : { tree_fall P t } + { ~ tree_fall P t }.
    Proof.
      destruct (tree_fall_exst_dec _ _ PQ_dec t) as [ | C ].
      tauto.
      right; intros H.
      apply tree_fall_exst_incomp with (2 := H) (3 := C).
      intros; tauto.
    Qed.
    
    Fact tree_exst_dec t : { tree_exst P t } + { ~ tree_exst P t }.
    Proof.
      destruct (tree_fall_exst_dec (fun x ll => ~ P x ll) P) with (t := t) as [ C | ].
      intros x ll; specialize (PQ_dec x ll); tauto.
      right; intros H.
      apply tree_fall_exst_incomp with (2 := C) (3 := H).
      intros; tauto.
      left; auto.
    Qed.

  End tree_fall_dec.

End trees.

Section tree_map.

  Variables (X Y : Type) (f : X -> Y).
  
  Definition tree_map : tree X -> tree Y.
  Proof.
    induction 1 as [ x ts IH ] using tree_recursion.
    apply (in_tree (f x)), IH.
  Defined.

  Fact tree_map_fix x ts : tree_map (in_tree x ts) = in_tree (f x) (map tree_map ts).
  Proof.
    apply tree_recursion_fix.
  Qed.

End tree_map.

Section weighted_tree.

  Variable (X : Type) (w : X -> nat).
  
  (* We assume that there are only finitely many terms 
     for a given weight *)
  
  Hypothesis Hf : forall n, finite_t (fun x => w x = n).
  
  (* We define a weight for trees which is strictly positive *)

  Definition tree_weight : tree X -> nat.
  Proof.
    induction 1 as [ c _ ll ] using tree_recursion.
    exact (1+w c+lsum ll).
  Defined.
  
  Fact tree_weight_fix c ll : tree_weight (in_tree c ll) = 1 + w c + lsum (map tree_weight ll).
  Proof. apply tree_recursion_fix. Qed.
  
  Fact tree_weight_gt_O t : 0 < tree_weight t.
  Proof. destruct t; rewrite tree_weight_fix; omega. Qed.
  
  (* Hence there are only finitely many trees of a given weight *)
  
  Fact finite_t_weighted_tree n : finite_t (fun t => tree_weight t = n).
  Proof.
    induction n as [ [ | n ] IHn ] using (well_founded_induction_type lt_wf).
    
    exists nil.
    intros x; split.
    intros [].
    generalize (tree_weight_gt_O x); omega.
    
    set (Q ln := match ln with 
                   | nil  => fun _ => False 
                   | n::l => fun t => w (tree_root t) = n
                                   /\ map tree_weight (tree_sons t) = l end).
                                   
    destruct finite_t_map with (Q := Q) (1 := finite_t_part n) as (ll & Hll); 
      unfold Q in * |- *; clear Q.
    
    intros [ | x ln ].
    intros [].
    simpl; intros (H1 & H3).
    
    generalize (Hf x); intros Hx.
    destruct (@finite_t_Forall _ _ (fun i t => tree_weight t = i) ln) as (lt & Hlt).
    intros u Hu; apply IHn. 
    apply lsum_le in Hu; omega.
    destruct Hx as (lx & Hlx).
    exists (list_prod (@in_tree _) lx lt).
    intros t.    
    rewrite list_prod_spec; split.
    
    intros (c & ll & ? & H4 & H5); subst t; simpl.
    rewrite <- Hlx; split; auto.
    apply Hlt in H5.
    symmetry.
    clear H1 H3 Hlx lt Hlt c H4.
    induction H5; simpl; f_equal; auto.
    
    intros (? & ?); subst.
    destruct t as (c & l); exists c, l; split; auto.
    split.
    apply Hlx; auto.
    apply Hlt; simpl.
    clear H1 lx Hlx lt Hlt IHn.
    induction l; simpl; constructor; auto.
    
    exists ll.
    intros (c,l); rewrite Hll; simpl; split.
    intros ([ | x ln] & H1 & H2).
    destruct H2.
    rewrite tree_weight_fix.
    simpl in H2, H1.
    destruct H2 as (H3 & H4).
    destruct H1 as (H1 & H2).
    apply f_equal with (f := lsum) in H4.
    omega.
    
    rewrite tree_weight_fix.
    intros H.
    exists (w c::map tree_weight l); split.
    split.
    rewrite Forall_forall.
    intros t Ht.
    rewrite in_map_iff in Ht.
    destruct Ht as (x & ? & Hx); subst.
    apply tree_weight_gt_O.
    omega.
    simpl; split; auto.
  Qed.
  
End weighted_tree.

