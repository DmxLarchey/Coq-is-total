Section hilbert_cid.

  Definition hilbert := forall X, inhabited X -> X.
  Definition cid := forall X (P : X -> Prop), (exists x, P x) -> { x | P x }.
  
  Fact hilbert_cid : hilbert -> cid.
  Proof.
    intros H X P HP.
    apply H.
    destruct HP as (x & Hx).
    exists.
    exists x; auto.
  Qed.
  
  Fact cid_hilbert : cid -> hilbert.
  Proof.
    intros H X HX.
    set (P (_ : X) := True).
    assert (exists x, P x) as H1.
      destruct HX as [ x ].
      exists x; red; auto.
    apply H in H1.
    destruct H1 as (x & _); exact x.
  Qed.
  
  Fact hilbert_or_plus : hilbert -> forall A B : Prop, A \/ B -> { A } + { B }.
  Proof.
    intros H A B H1.
    apply H.
    destruct H1; exists; [ left | right ]; auto.
  Qed.

End hilbert_cid.
