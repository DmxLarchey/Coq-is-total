(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Wellfounded.

Set Implicit Arguments.

(* Dependent recursion principle for Acc, same as Acc_inv_dep but for sort Type
   instead of sort Prop *)

Scheme Acc_drect := Induction for Acc Sort Type.

Section Acc_eq.

  (* Proof that Fix_F is extensionnal *)

  Variable (X : Type) (R : X -> X -> Prop).

  (* This is a weaker notion than @eq (Acc R x) but sufficient
     to establish extensinality properties *)

  Inductive Acc_eq : forall x, Acc R x -> Acc R x -> Prop := 
    | in_Acc_eq : forall x H1 H2, (forall y Hy, Acc_eq (H1 y Hy) (H2 y Hy)) -> Acc_eq (Acc_intro x H1) (Acc_intro _ H2).

  (* unless dependent functional extensionality is assumed, it is
     not possible to show that there is a unique accessibility proof
     BUT it is easy to show that they are unique upto Acc_eq ... *)

  Fact Acc_eq_total x (H1 H2 : Acc R x) : Acc_eq H1 H2.
  Proof.
    revert x H1 H2.
    induction H1 as [ x H1 IH ] using Acc_inv_dep; intros [ H2 ].
    constructor; intros; apply IH.
  Qed.

  Variable P : X -> Type.
  Variable F : forall x, (forall y, R y x -> P y) -> P x.

  Variable (E : forall x, P x -> P x -> Prop).

  Hypothesis
    F_ext :
      forall x (f g:forall y, R y x -> P y),
        (forall y (p:R y x), E (f y p) (g y p)) -> E (F f) (F g).

  (* This one generalizes Fix_F_inv from Wf in that it does not assume wellfoundedness *)

  Lemma Fix_F_ext : forall x (r s : Acc R x), E (Fix_F _ F r) (Fix_F _ F s).
  Proof.
    intros ? r s; generalize (Acc_eq_total r s).
    induction 1 as [ ? ? ? ? IH ]; apply F_ext, IH.
  Qed.

  (* This one generalizes Fix_F_eq for arbitrary relations *) 

  Theorem Fix_F_equiv x (r : Acc R x) : E (Fix_F _ F r) 
                                          (F (fun y Hy => Fix_F _ F (Acc_inv r _ Hy))).
  Proof.
    rewrite Fix_F_eq; apply Fix_F_ext.
  Qed.

  Hypothesis Rwf : well_founded R.

  (* This one generalizes Fix_eq for arbitrary relations *)

  Theorem Fix_equiv x : E (Fix Rwf P F x) (F (fun y _ => Fix Rwf P F y)).
  Proof.
    unfold Fix.
    destruct (Rwf x); simpl.
    apply F_ext. 
    intros; apply Fix_F_ext.
  Qed.

End Acc_eq.
