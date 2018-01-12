(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.

Require Import utils recalg computable.

Set Implicit Arguments.

Section relational_semantics.

  (* Recursive functions can be interpreted in Coq as (functional) relations *)

  Notation natfun := (fun k => vec nat k -> nat -> Prop).

  Section defs.

    Definition s_cst c : natfun 0 := fun _ x => x=c.
    Definition s_zero  : natfun 1 := fun _ x => x=0.
    Definition s_succ  : natfun 1 := fun v x => x=S (vec_head v).
    Definition s_proj k (p : pos k) : natfun k := fun v x => vec_pos v p = x.

    Variable k i : nat.
    
    Implicit Types (f : natfun k) (g : natfun (S k)) (h : natfun (S (S k))) (gj : vec (natfun i) k).

    Definition s_comp f gj : natfun i := fun v x => exists gl, f gl x /\ forall p, vec_pos gj p v (vec_pos gl p).
      
    (** the recursor s_rec_r f h n v x 
                 <-> exists x0,...,xn,  f      v  x0,
                                        h (0##x0##v) x1,
                                        h (1##x1##v) x2,
                                        ...
                                        h (.##..##v) xn, 
                                    and xn = x 
    **)
   
    Definition s_rec f h v := μ_rec f (fun v x y => h (x##y##v)) (vec_tail v) (vec_head v).

    Definition s_min g v := μ_min (fun n => g (n##v)).

  End defs.
  
  (** we define the semantics of a recursive algorithm of arity k 
      which is a relation vec nat k -> nat -> Prop, obviously functional (see below)
      We interpret the constants ra_* with the corresponding s_* operator on relations
   **) 

  Definition ra_rel : forall k, recalg k -> natfun k.
  Proof.
    apply recalg_rect with (P := fun k _ => natfun k).
    exact s_cst.
    exact s_zero.
    exact s_succ.
    exact s_proj.
    intros ? ? ? ? hf hgj; exact (s_comp hf (vec_set_pos hgj)).
    intros ? ? ? hf hg; exact (s_rec hf hg).
    intros ? ? hf; exact (s_min hf).
  Defined.
  
  Notation "[| f |]" := (@ra_rel _ f) (at level 0).
 
  Fact ra_rel_fix_cst i :         [| ra_cst i     |]      = s_cst i.                   Proof. reflexivity. Qed.
  Fact ra_rel_fix_zero :          [| ra_zero      |]      = s_zero.                    Proof. reflexivity. Qed.
  Fact ra_rel_fix_succ :          [| ra_succ      |]      = s_succ.                    Proof. reflexivity. Qed.
  Fact ra_rel_fix_proj k p :      [| @ra_proj k p |]      = s_proj p.                  Proof. reflexivity. Qed.
  Fact ra_rel_fix_rec k f g :     [| @ra_rec k f g |]     = s_rec [|f|] [|g|].         Proof. reflexivity. Qed.
  Fact ra_rel_fix_min k f :       [| @ra_min k f |]       = s_min [|f|].               Proof. reflexivity. Qed.
  Fact ra_rel_fix_comp k i f gj : [| @ra_comp k i f gj |] = s_comp [|f|] (vec_map (fun x => [|x|]) gj).
  Proof.
    simpl ra_rel; f_equal.
    apply vec_pos_ext; intros p.
    rewrite vec_pos_set, vec_pos_map; trivial.
  Qed.
 
  Section functional.

    Lemma s_cst_fun c : functional (s_cst c).
    Proof. intros v x y Hx Hy; rewrite Hy; trivial. Qed.

    Lemma s_zero_fun : functional s_zero.
    Proof. intros v x y Hx Hy; rewrite Hy; trivial. Qed.

    Lemma s_succ_fun : functional s_succ.
    Proof. intros v x y Hx Hy; rewrite Hy; trivial. Qed.
    
    Lemma s_proj_fun k p : functional (@s_proj k p).
    Proof.
      intros v x y Hx Hy.
      red in Hx, Hy. 
      rewrite <- Hx.
      trivial.
    Qed.

    Variable k i : nat.
    Implicit Types (f : natfun k) (gj : vec (natfun i) k) (g : natfun (S k)) (h : natfun (S (S k))).

    Lemma s_comp_fun f gj : functional f -> (forall p, functional (vec_pos gj p)) -> functional (s_comp f gj).   
    Proof.
      intros f_fun gj_fun v x y [ gx [ Hx1 Hx2 ] ] [ gy [ Hy1 Hy2 ] ].
      cutrewrite (gx = gy) in Hx1.
      apply (@f_fun gy); trivial.
      apply vec_pos_ext.
      intros p; apply (gj_fun p v); auto.
    Qed.

    Lemma s_rec_fun f h : functional f -> functional h -> functional (s_rec f h).
    Proof.
      intros Hf Hh ? ? ?. 
      apply μ_rec_fun; auto.
      intros ? ? ? ? ?; apply Hh.
    Qed.

    Lemma s_min_fun g : functional g -> functional (s_min g).
    Proof.
      intros Hg ? ? ?; apply μ_min_fun.
      intros ? ? ?; apply Hg.
    Qed.

  End functional.
  
  Hint Resolve s_cst_fun s_zero_fun s_succ_fun s_proj_fun s_rec_fun s_min_fun.

  (* [| f |] is a functional/deterministic relation *)

  Theorem ra_rel_fun k (f : recalg k) v x y : [|f|] v x -> [|f|] v y -> x = y.
  Proof.
    revert v x y; change (functional [|f|]).
    induction f; try (simpl; auto; fail).
    rewrite ra_rel_fix_comp.
    apply s_comp_fun; auto. 
    intro; rewrite vec_pos_map; auto.
  Qed.

End relational_semantics.

Notation "[| f |]" := (@ra_rel _ f) (at level 0).

Section recalg_coq.

  (** This code compute the μ-recursive algorithm f into
      Coq code that mimics the algorithm f 

      It needs a termination certificate in the form 
      of a proof that the predicate [|f|] v is inhabited

      Notice: refine is used to allow better extraction
        to OCaml code

      This gives a VERY short proof of the totality of Coq !!!
   *)

  Fixpoint recalg_computable k (ra : recalg k) : forall v, computable ([|ra|] v).
  Proof.
    destruct ra as [ n | | | k p | k i f gj | k f g | k f ]; intros v Hv.

    exists n; reflexivity.
    exists 0; reflexivity.
    exists (S (vec_head v)); reflexivity.
    exists (vec_pos v p); reflexivity.
    
    refine (match @vec_computable _ _ (fun f y => [|f|] v y) _ _ gj _ with
      exist _ w Hw => match recalg_computable _ f w _ with
        exist _ x Hx => exist _ x _
      end 
    end).
    
    intros (w & Hw); apply recalg_computable; trivial.
    apply vec_reif with (R := fun p => [|vec_pos gj p|] v).
      intros p.
      destruct Hv as (q & w & _ & Hw).
      specialize (Hw p); rewrite vec_pos_set in Hw.
      exists (vec_pos w p); trivial.
    destruct Hv as (q & w' & Hw1 & Hw2).
      exists q; cutrewrite (w = w'); auto.
      apply vec_pos_ext.
      intros p; generalize (Hw p) (Hw2 p).
      rewrite vec_pos_set; apply ra_rel_fun.
    exists w; split; auto.
      intros; rewrite vec_pos_set; apply Hw.

    revert Hv; simpl; apply rec_computable.
    intros ? ?; apply ra_rel_fun.
    intros (w & Hw); simpl.
    apply recalg_computable; trivial.
    intros ? ? ? ?; apply ra_rel_fun.
    intros ? ? (w & Hw); apply recalg_computable; simpl; auto.

    revert Hv; simpl; apply min_computable; auto.
    intros ? ? ?; apply ra_rel_fun.
    intros (w & Hw); apply recalg_computable; trivial.
  Defined.

End recalg_coq.

Section Coq_is_total.
  
  Variables (k : nat) (f : recalg k) (Hf : forall v, exists x, [|f|] v x).

  Theorem Coq_is_total : { cf | forall v, [|f|] v (cf v) }.
  Proof.
    exists (fun v => proj1_sig (recalg_computable _ _ (Hf v))).
    intros v; apply (proj2_sig (recalg_computable _ _ (Hf v))).
  Defined.

End Coq_is_total.

Check recalg_computable.
Print Assumptions recalg_computable.

Check Coq_is_total.
Print Assumptions Coq_is_total.

Extraction "ra_coq.ml" recalg_computable Coq_is_total.


    
     
 


