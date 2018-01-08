(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Eqdep_dec.

Require Import utils.

Set Implicit Arguments.

Reserved Notation " '[|' f '|]' " (at level 0).

Section Recursive_algorithms.

  Unset Elimination Schemes.

  Inductive recalg : nat -> Set :=
    | ra_cst  : nat -> recalg 0
    | ra_zero : recalg 1
    | ra_succ : recalg 1
    | ra_proj : forall k, pos k -> recalg k
    | ra_comp : forall k i, recalg k -> vec (recalg i) k -> recalg i
    | ra_rec  : forall k, recalg k -> recalg (S (S k)) -> recalg (S k)
    | ra_min  : forall k, recalg (S k) -> recalg k
    .

  Set Elimination Schemes.

  Section recalg_rect.

    Variable P : forall k, recalg k -> Type.

    Hypothesis Pcst  : forall n, P (ra_cst n).
    Hypothesis Pzero : P ra_zero.
    Hypothesis Psucc : P ra_succ.
    Hypothesis Pproj : forall k p, P (@ra_proj k p).
    Hypothesis Pcomp : forall k i f gj, P f -> (forall p, @P i (@vec_pos _ k gj p)) 
                                     -> P (ra_comp f gj).
    Hypothesis Prec  : forall k f g, @P k f -> P g -> P (ra_rec f g).
    Hypothesis Pmin  : forall k f, @P (S k) f -> P (ra_min f).

    Fixpoint recalg_rect k f { struct f } : @P k f :=
      match f with
        | ra_cst n     => Pcst n
        | ra_zero      => Pzero
        | ra_succ      => Psucc
        | ra_proj p    => Pproj p 
        | ra_comp f gj => Pcomp _ [|f|] (fun p => [|vec_pos gj p|])
        | ra_rec f g   => Prec [|f|] [|g|]
        | ra_min f     => Pmin [|f|]
      end
    where "[| f |]" := (@recalg_rect _ f).

  End recalg_rect.

  Definition recalg_rec (P : forall k, recalg k -> Set) := recalg_rect P.
  Definition recalg_ind (P : forall k, recalg k -> Prop) := recalg_rect P.

  Section recalg_rec_type.

    Variables (X : Type) (P : nat -> Type).
    Hypothesis Pcst  : P 0.
    Hypothesis Pzero : P 1.
    Hypothesis Psucc : P 1.
    Hypothesis Pproj : forall k (p : pos k), P k.
    Hypothesis Pcomp : forall k i, P k -> vec (P i) k -> P i. 
    Hypothesis Prec  : forall k, P k -> P (S (S k)) -> P (S k).
    Hypothesis Pmin  : forall k, P (S k) -> P k.

    Fixpoint recalg_rec_type k (f : recalg k) { struct f } : P k :=
      match f in recalg i return P i with
        | ra_cst n     => Pcst
        | ra_zero      => Pzero
        | ra_succ      => Psucc
        | ra_proj p    => Pproj p 
        | ra_comp f gj => Pcomp [|f|] (vec_map (@recalg_rec_type _) gj)
        | ra_rec f g   => Prec [|f|] [|g|]
        | ra_min f     => Pmin [|f|]
      end
    where "[| f |]" := (@recalg_rec_type _ f).

  End recalg_rec_type.
  
  Section recalg_inj.
 
    (* Injectivity is not a given for dependently typed constructors but it holds
       when the dependent parameter is from a set (ie a Type with decidable equality *)
  
    Let nat_dep_inj (P : nat -> Type) n x y : existT P n x = existT P n y -> x = y.
    Proof. apply inj_pair2_eq_dec, eq_nat_dec. Qed.
    
    Local Ltac inj := let H := fresh in intros H; injection H; clear H; auto.
    
    Local Ltac diauto := 
      repeat match goal with 
        H: existT _ _ _ = existT _ _ _ |- _ => apply nat_dep_inj in H 
      end; auto.
      
    Fact ra_cst_inj n m : ra_cst n = ra_cst m -> n = m.
    Proof. inj. Qed.

    Fact ra_proj_inj k (p q : pos k) : ra_proj p = ra_proj q -> p = q.
    Proof. inj. Qed.
    
    (* This one is more subtle and requires type casts *)

    Fact ra_comp_inj k k' i f f' gj gj' : 
         @ra_comp k i f gj = @ra_comp k' i f' gj'
      -> exists H : k = k', eq_rect _ _ f _ H = f'
                         /\ eq_rect _ _ gj _ H = gj'.
    Proof.
      inj; intros ? ? H; exists H; subst; simpl; diauto.
    Qed.
 
    Fact ra_rec_inj k f g f' g' : @ra_rec k f g = ra_rec f' g' -> f = f' /\ g = g'.
    Proof.
      inj; intros; diauto.
    Qed.

    Fact ra_min_inj k f f' : @ra_min k f = ra_min f' -> f = f'.
    Proof.
      inj; intros; diauto.
    Qed.

  End recalg_inj.

End Recursive_algorithms.
