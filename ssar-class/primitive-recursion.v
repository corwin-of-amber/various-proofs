
Section PrimRecChurch.

  Variable A : Set.
  Variable a : A.
  Variable h : nat -> A -> A.

  Fixpoint f n := match n with
                    0 => a
                  | S k => h k (f k)
                  end.

  Definition h' nfn :=
    pair (S (fst nfn)) (h (fst nfn) (snd nfn)).  
  
  Fixpoint f' n := match n with
                     0 => pair 0 a
                   | S k => h' (f' k)
                   end.

  Lemma seq : forall n, n = fst (f' n).
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite <- IHn. reflexivity.
  Qed.
      
  Theorem defin : forall n, f n = snd (f' n).
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite <- seq, <- IHn.
      reflexivity.
  Qed.

End PrimRecChurch.