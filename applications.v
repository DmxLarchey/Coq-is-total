(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Relations Wellfounded.

Require Import utils nat_minimizer finite decidable_t.
Require Import recalg ra_rel ra_ca ra_sem_eq ra_ca_props.

Set Implicit Arguments.

Section weighted_reif.

  Variable (X : Type) (P : X -> Prop).
  
  (* We suppose that P x can be read as there exists a weight n s.t. Q n x holds
     and that Q n is finite at a given weight n *)
  
  Variable (Q : nat -> X -> Prop).
  Hypothesis HP : forall x, P x <-> exists n, Q n x.
  Hypothesis HQ : forall n, finite_t (Q n).
  
  Let K n := exists x, Q n x.
  
  Let K_dec n : { K n } + { ~ K n }.
  Proof.
    destruct (HQ n) as ( [ | x l ] & Hl ).
    right; intros (x & Hx); apply (Hl x), Hx.
    left; exists x; apply Hl; left; trivial.
  Qed.
  
  Theorem weighted_reif : (exists x, P x) -> { x | P x }.
  Proof.
    intros H.
    destruct (nat_reify K K_dec) as (n & Kn).
    destruct H as (x & Hx).
    apply HP in Hx.
    destruct Hx as (n & Hn).
    exists n, x; auto.
    destruct (HQ n) as ([ | y l ] & Hl).
    exfalso.
    destruct Kn as (x & Hx).
    apply (Hl x), Hx.
    exists y; apply HP.
    exists n; apply Hl; left; auto.
  Qed.
  
End weighted_reif.

Section proof.

  Variable (stm : Type) (stm_eq_dec : forall x y : stm, { x = y } + { x <> y }) 
      (stm_w : stm -> nat) 
      (stm_fin : forall n, finite_t (fun s => stm_w s = n)).
  
  (* Rule instances are of the form H1,...,Hn / C where H1,..,Hn is a list of (premise) statements and 
     C is (conclusion) statement *)
  
  Variable (inst : list stm -> stm -> Prop) (inst_dec : forall l c, { inst l c } + { ~ inst l c }).
  
  (* a proof tree is a tree of stm such that each node is an instance of some rule *)
  
  Definition proof_tree := tree_fall (fun c l => inst (map (@tree_root _) l) c).
  
  Fact proof_tree_fix c ll : proof_tree (in_tree c ll) <-> inst (map (@tree_root _) ll) c
                                                        /\ forall t, In t ll -> proof_tree t.
  Proof. apply tree_fall_fix. Qed.
  
  (* Once you can recognise valid instances, you can recognize valid proof trees 
     But this has nothing to do with decidability of provability: recognizing a proof
     is not the same thing as finding a proof
   *)
  
  Fact proof_tree_dec t : { proof_tree t } + { ~ proof_tree t }.
  Proof. apply tree_fall_dec; intros; apply inst_dec. Qed.

  (** This shows that under very reasonable assumptions, we can
      reify the provability predicate: the assumptions are
      
     1/ the equality of statement (eg formulas) can be decided
     2/ there is a weight on statements such for any given 
        weight value, only a finite number of statements have 
        that weight
     3/ discriminating between valid and invalid rule instances is decidable
     
     1&3) are really non issues for any proof system designed for
        proofs search because being able to recognise the trees which
        are valid proofs from those which are not is a must prerequisite
        
     2)  is also a very weak requirement. For instance, if you can encode
        statements with numbers, then 2) holds, the weight being
        simply the number encoding a statement
   *) 

  Definition proof_reif c : (exists p, tree_root p = c /\ proof_tree p) -> { p | tree_root p = c /\ proof_tree p }.
  Proof.
    apply weighted_reif with (Q := fun n p => proof_tree p /\ tree_root p = c /\ tree_weight stm_w p = n).
    intros t; split.
    exists (tree_weight stm_w t); tauto.
    intros (? & ? & ?); tauto.
    intros n.
    apply finite_t_dec.
    apply proof_tree_dec.
    apply finite_t_dec.
    intro; apply stm_eq_dec.
    apply finite_t_weighted_tree, stm_fin.
  Qed.
  
End proof.

Check proof_reif.
Print Assumptions proof_reif.

Section normal_form.

  Variables (X : Type) (R : X -> X -> Prop).
  
  Hypothesis finitary : forall x, finite_t (R x).
  
  Definition normal x := forall y, ~ R x y.
  
  Local Fact normal_dec x : { normal x } + { ~ normal x }.
  Proof.
    destruct (finitary x) as ([ | y l ] & Hl).
    left; intro; rewrite <- Hl; simpl; tauto.
    right; intros H; apply (H y), Hl; left; auto.
  Qed.
  
  Local Fixpoint Rn n x y := 
    match n with
      | 0   => x = y
      | S n => exists i, R x i /\ Rn n i y
    end.
    
  Local Fact Rn_plus a b x y : Rn (a+b) x y <-> exists i, Rn a x i /\ Rn b i y.
  Proof.
    revert x y; induction a as [ | a IHa ]; intros x y; simpl.
    split.
    exists x; simpl; auto.
    intros (? & [] & ?); auto.
    split.
    intros (i & H1 & H2).
    apply IHa in H2.
    destruct H2 as (j & H2 & H3).
    exists j; split; auto.
    exists i; auto.
    intros (i & (j & H1 & H2) & H3).
    exists j; split; auto; apply IHa.
    exists i; auto.
  Qed.
    
  Local Fact Rn_crt x y : clos_refl_trans _ R x y <-> exists n, Rn n x y.
  Proof.
    split.
    induction 1 as [ x y | | x y z _ (n1 & Hn1) _ (n2 & Hn2) ].
    exists 1, y; simpl; auto.
    exists 0; simpl; auto.
    exists (n1+n2); apply Rn_plus. 
    exists y; split; auto.
    intros (n & Hn); revert x y Hn.
    induction n as [ | n IHn ]; simpl; intros x y Hn.
    subst; constructor 2.
    destruct Hn as (i & ? & ?).
    constructor 3 with i; auto.
    constructor 1; auto.
  Qed.
    
  Fact Rn_finitary n x : finite_t (Rn n x).
  Proof.
    revert x.
    induction n as [ | n IHn ]; intros x.
    exists (x::nil); simpl; tauto.
    apply finite_t_map with (1 := finitary _) (2 := fun x _ => IHn x).
  Qed.
  
  Variable (x : X).
  
  Definition normal_form y := normal y /\ clos_refl_trans _ R x y.
  
  Let Q n y := normal y /\ Rn n x y.
  
  Let Q_dec n : finite_t (Q n).
  Proof.
    apply finite_t_dec.
    apply normal_dec.
    apply Rn_finitary.
  Qed.
  
  (** This result shows that the predicate "y is a normal form of x"
     can be refied, ie one can compute a normal form of x out of
     a proof of its existence ...
     
     Hence if x is normalizable then a normal form of x can be
     computed.
     
     The only requirement is that the relation is (informativelly)
     finitary, that is the set of one step reductions forms a finite list 
     
     This development DOES NOT require than the relation is strongly
     normalizable ... hence the algorithm is obviously not depth
     first search. In fact, it is exhaustive search for depth 0,
     then depth 1, then depth 2, etc until a suitable depth is
     reached. 
     
     It is obviously not the best algorithm to actually compute a
     normal form. This depends on the particular system in consideration.

     This development applies to lambda calculus for instance where 
     the set of reducts can be computed from the set of redexes 
     
  **)
  
  Hypothesis Hx : exists y, normal_form y. 
  
  Definition normal_form_reif : { y | normal_form y }.
  Proof.
    destruct weighted_reif with (P := fun y => exists n, Q n y) (Q := Q)
      as (y & Hy); auto.
    simpl; tauto.
    destruct Hx as (y & ? & Hy).
    apply Rn_crt in Hy.
    destruct Hy as (n & ?).
    exists y, n; split; auto.
    exists y.
    destruct Hy as (n & ? & ?); split; auto.
    apply Rn_crt; exists n; auto.
  Qed.
  
End normal_form.

Check normal_form_reif.
Print Assumptions normal_form_reif.

Section div2.

  (* A small library for a surjection nat -> nat*nat *)

  Fixpoint pow2 x := match x with 0 => 1 | S x => 2 * pow2 x end.

  Fact pow2_ge_1 x : 1 <= pow2 x.
  Proof. induction x; simpl; omega. Qed.

  Fact pow2_plus a b : pow2 (a+b) = pow2 a * pow2 b.
  Proof.
    induction a.
    simpl; omega.
    simpl plus.
    unfold pow2; fold pow2.
    rewrite <- mult_assoc.
    f_equal; auto.
  Qed.

  Fact mult_simpl a b c : 1 <= a -> a*b = a*c -> b = c.
  Proof.
    intros H1 H2.
    destruct a.
    omega.
    apply le_antisym; apply mult_S_le_reg_l with a; omega.
  Qed.

  Fact pow2_simpl a b c : pow2 a*b = pow2 a*c -> b = c.
  Proof.
    apply mult_simpl, pow2_ge_1.
  Qed.

  Let mp a b := (pow2 a)*(1+2*b).

  Fact decomp_ge_1 a b : 1 <= mp a b.
  Proof.
    change 1 with (1*1).
    apply mult_le_compat.
    apply pow2_ge_1.
    omega.
  Qed.

  Fact pow2_odd a b c : pow2 a*b = 1+2*c -> a = 0 /\ b = 1+2*c.
  Proof.
    destruct a as [ | a ].
    simpl; omega.
    unfold pow2; fold pow2.
    rewrite <- mult_assoc.
    omega.
  Qed.

  Fact decomp_le a b u v : mp a b = mp u v -> a <= u.
  Proof.
    unfold mp.
    intros H.
    destruct (le_lt_dec a u) as [ | C ]; auto.
    replace a with (u+(a-u)) in H by omega.
    rewrite pow2_plus, <- mult_assoc in H. 
    apply pow2_simpl in H.
    apply pow2_odd in H.
    omega.
  Qed.
 
  Fact decomp_inj a b u v : mp a b = mp u v -> a = u /\ b = v.
  Proof.
    intros H.
    assert (a = u) as E.
      apply le_antisym.
      revert H; apply decomp_le.
      symmetry in H; revert H; apply decomp_le.
    split; auto; subst u.
    unfold mp in H.
    apply pow2_simpl in H.
    omega.
  Qed.

  Definition div2 n : { p | n = 2 * p } + { p | n = 1 + 2 * p }.
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type lt_wf).
    destruct n as [ | [ | n ] ].
    left; exists 0; auto.
    right; exists 0; auto.
    destruct (IHn n) as [ (p & Hp) | (p & Hp) ].
    omega.
    left; exists (S p); omega.
    right; exists (S p); omega.
  Qed.

  Definition div_pow2 n : { c | match c with (a,b) => S n = mp a b end }.
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type lt_wf).
    destruct n as [ | n ].
    exists (0,0); auto. 
    destruct (div2 n) as [ (p & Hp) | (p & Hp) ].
    destruct (IHn p) as ((a,b) & H).
    omega.
    exists (S a, b).
    replace (S (S n)) with (2*S p) by omega.
    rewrite H; unfold mp; rewrite mult_assoc; auto.
    unfold mp; exists (0,S p); simpl; omega.
  Qed.

End div2.

Section pairing.

  Definition pair_nat (c : nat * nat) : nat := match c with (a,b) => (pow2 a)*(1+2*b)-1 end.
  Definition nat_pair n := proj1_sig (div_pow2 n).
  
  Fact nat_pair_nat c : nat_pair (pair_nat c) = c.
  Proof.
    unfold nat_pair.
    destruct (div_pow2 (pair_nat c)) as ((a,b) & H); simpl.
    destruct c as (u,v); unfold pair_nat in H.
    replace (S (pow2 u*(1+2*v)-1)) with (pow2 u*(1+2*v)) in H.
    apply decomp_inj in H.
    destruct H; subst; auto.
    generalize (decomp_ge_1 u v); omega.
  Qed.
  
End pairing.

Section vec_enum.
  
  Opaque pair_nat.
  
  Fixpoint vec_enc k : vec nat k -> nat :=
    match k with
      | 0   => fun _ => 0
      | S k => fun v => pair_nat (vec_head v,vec_enc (vec_tail v))
    end.
    
  Fixpoint vec_dec k : nat -> vec nat k :=
    match k with 
      | 0   => fun _ => vec_nil
      | S k => fun n => let (a,b) := nat_pair n in a##vec_dec k b 
    end.
    
  Fact vec_dec_enc k x : vec_dec k (vec_enc x) = x.
  Proof.
    revert x; induction k as [ | k IHk ]; intros x.
    rewrite vec_0_nil; auto.
    rewrite (vec_head_tail x).
    generalize (vec_head x) (vec_tail x); clear x; intros a v.
    simpl; rewrite nat_pair_nat, IHk; auto.
  Qed.
  
End vec_enum.

Section ex_bool_reify.

  Variable (k : nat) (f : vec nat k -> nat -> bool).
  Hypothesis (Hf : exists v, exists n, f v n = true).
  
  Let Q n := let (a,b) := nat_pair n in f (vec_dec k a) b = true.

  Let HQ n : { Q n } + { ~ Q n }.
  Proof.
    unfold Q.
    generalize (nat_pair n).
    intros (a, b).
    destruct (f (vec_dec k a) b); auto.
  Qed.
  
  Theorem ex_bool_reify : { v : vec nat k & { n | f v n = true } }.
  Proof.
    destruct (nat_reify _ HQ) as (n & Hn).
    destruct Hf as (v & n & H).
    exists (pair_nat (vec_enc v,n)).
    red; rewrite nat_pair_nat, vec_dec_enc; trivial.
    red in Hn.
    destruct (nat_pair n) as (a,b).
    exists (vec_dec k a), b; trivial.
  Qed.
  
End ex_bool_reify.
  
Section cre_reify.

  (* Reification of Coq-recursively enumerable predicates *)

  Variables (k : nat) (P : vec nat k -> nat -> Prop).
  
  (* We reify the predicate (n => exists e, P n e)
     where P is decidable, is this what reviewer 2
     calls recursively enumerable predicate (in Coq)
   *)
  
  Hypothesis (Pdec : forall v e, { P v e } + { ~ P v e }). 
  Hypothesis (HP : exists v e, P v e).
  
  Theorem cre_reify : { v : vec nat k | exists e, P v e }.
  Proof.
    destruct ex_bool_reify with (f := fun v n => if Pdec v n then true else false) 
      as (v & n & H).
    destruct HP as (v & n & H).
    exists v, n.
    destruct (Pdec v n); tauto.
    exists v, n.
    destruct (Pdec v n); auto; discriminate.
  Qed.
  
End cre_reify.

Section re_min.
 
  Variables (k : nat) (f : recalg k).
  
  Lemma ra_ca_dec v n x : { [f;v] -[n>> x } + { ~ [f;v] -[n>> x }.
  Proof.
    destruct ra_ca_decidable_t with (f := f) (v := v) (n := n)
      as [ (r & Hr) | C ].
    destruct (eq_nat_dec r x) as [ E | C ].
    subst; left; auto.
    right; contradict C; apply (ra_ca_fun Hr C).
    right; intros H; apply C; exists x; trivial.
  Qed.
  
  Lemma ra_as_ex_bool : { c : vec nat k -> nat -> nat -> bool | forall v x, [|f|] v x <-> exists n, c v x n = true }.
  Proof.
    exists (fun v x n => if ra_ca_dec v n x then true else false).
    intros v x; rewrite ra_ca_correct.
    split; intros (n & Hn); exists n;
      destruct (ra_ca_dec v n x); auto; discriminate.
  Qed.
  
  Theorem re_reify : (exists v, [|f|] v 0) -> { v | [|f|] v 0 }.
  Proof.
    intros H.
    destruct cre_reify with (P := fun v x => [f;v] -[x>> 0)
      as (v & Hv); trivial.
    intros; apply ra_ca_dec.
    destruct H as (v & Hv); exists v; apply ra_rel_inc_ca; trivial.
    exists v; apply ra_bs_inc_rel, ra_ca_inc_bs; trivial.
  Qed.

End re_min.
 
Check cre_reify.
Check re_reify.
Print Assumptions re_reify.

(* Recursively enumerable types are stable under finite/enumerable unions and finite intersection *)

Require Import Bool.


Definition dec {X : Type} (P : X -> Prop) := { f : X -> bool | forall x, P x <-> f x = true }.
Definition re {X : Type} (P : X -> Prop) := { f : X -> nat -> bool | forall x, P x <-> exists n, f x n = true }.

Fact dec_decidable X P : @dec X P -> forall x, { P x } + { ~ P x }.
Proof.
  intros (f & Hf) x.
  specialize (Hf x).
  destruct (f x).
  left; apply Hf; auto.
  right; rewrite Hf; discriminate.
Qed.

Fact dec_re X (P : X -> Prop) : dec P -> re P.
Proof.
  intros (f & Hf).
  exists (fun v _ => f v).
  intros x; rewrite Hf.
  split.
  exists 0; auto.
  intros (_ & ?); auto.
Qed.

(* Of course, this is a more general definition than with "real" recursive functions *)

Lemma re_ra k (f : recalg k) : re (fun v => [|f|] v 0).
Proof.
  destruct (ra_as_ex_bool f) as (c & Hc).
  exists (fun v => c v 0).
  intro; apply Hc.
Qed.

Fact re_empty X : re (fun _ : X => False).
Proof.
  exists (fun _ _ => false); intros x; split.
  intros [].
  intros (_ & ?); discriminate.
Qed.

Fact re_cup X (P Q : X -> Prop) : re P -> re Q -> re (fun x => P x \/ Q x).
Proof.
  intros (p & Hp) (q & Hq).
  exists (fun x n => orb (p x n) (q x n)).
  intros x; split.
  intros [ H | H ]; [ apply Hp in H | apply Hq in H ];
    destruct H as (n & Hn); exists n; apply orb_true_iff; tauto.
  intros (n & Hn); apply orb_true_iff in Hn.
  destruct Hn as [ Hn | Hn ]; [ left; apply Hp | right; apply Hq ];
    exists n; auto.
Qed.

Fact re_icup X (P : nat -> X -> Prop) : (forall n, re (P n)) -> re (fun x => exists n, P n x).
Proof.
  intros HP.
  exists (fun x c => let (a,b) := nat_pair c in proj1_sig (HP a) x b).
  intros x; split.
  intros (a & Ha).
  apply (proj2_sig (HP a)) in Ha.
  destruct Ha as (b & Hn).
  exists (pair_nat (a,b)); rewrite nat_pair_nat; auto.
  intros (n & Hn); revert Hn; generalize (nat_pair n); clear n; intros (a,b).
  intro; exists a; apply (proj2_sig (HP a)); exists b; auto.
Qed.

Fact re_full X : re (fun _ : X => True).
Proof.
  exists (fun _ _ => true); intros x; split.
  exists 0; auto.
  auto.
Qed.

Fact re_cap X (P Q : X -> Prop) : re P -> re Q -> re (fun x => P x /\ Q x).
Proof.
  intros (p & Hp) (q & Hq).
  exists (fun x c => let (a,b) := nat_pair c in andb (p x a) (q x b)).
  intros x; split.
  
  intros (HP & HQ).
  rewrite Hp in HP; rewrite Hq in HQ.
  destruct HP as (a & Ha).
  destruct HQ as (b & Hb).
  exists (pair_nat (a,b)).
  rewrite nat_pair_nat.
  apply andb_true_iff; tauto.
  
  intros (n & Hn).
  destruct (nat_pair n) as (a,b).
  apply andb_true_iff in Hn.
  rewrite Hp, Hq; split.
  exists a; tauto.
  exists b; tauto.
Qed.

(* re is probably not stable under infinite intersections 
   give an example ... *)

Fact re_dec X (P : X -> Prop) : re P -> re (fun x => ~ P x) -> (forall x, P x \/ ~ P x) -> dec P.
Proof.
  intros (f & Hf) (g & Hg) HP.
  set (h x n := let (c,m) := nat_pair n in c = 0 /\ f x m = true \/ c <> 0 /\ g x m = true). 
  assert (forall x, exists n, h x n) as Hh.
    intros x.
    destruct (HP x) as [ H | H ].
    apply Hf in H.
    destruct H as (a & Ha).
    exists (pair_nat (0,a)); unfold h.
    rewrite nat_pair_nat; auto.
    apply Hg in H.
    destruct H as (b & Hb).
    exists (pair_nat (1,b)); unfold h.
    rewrite nat_pair_nat; auto.
  assert (forall x n, { h x n } + { ~ h x n }) as hdec.
    intros x n; unfold h.
    generalize (nat_pair n); clear n; intros (c,n).
    generalize (eq_nat_dec c 0) (bool_dec (f x n) true) (bool_dec (g x n) true); tauto.
  set (c x := nat_reify (h x) (hdec x) (Hh x)).
  generalize c; clear c Hh hdec; unfold h; intros c.
  exists (fun x => let n := proj1_sig (c x) in let (a,b) := nat_pair n in if eq_nat_dec a 0 then true else false).
  intros x; split.
  
  intros Hx.
  destruct (c x) as (n & Hn); simpl.
  destruct (nat_pair n) as (a,m); simpl.
  destruct Hn as [ [ ? ? ] | [ _ Hn ] ].
  destruct (eq_nat_dec a 0); auto.
  exfalso; revert Hx; apply Hg; exists m; auto.
  
  destruct (c x) as (n & Hn); simpl.
  destruct (nat_pair n) as (a & b).
  destruct (eq_nat_dec a 0) as [ Ha | Ha ].
  intros _; apply Hf; exists b; tauto.
  discriminate.
Qed.


  
  
  