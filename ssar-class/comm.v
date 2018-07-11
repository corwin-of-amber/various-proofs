  Lemma plus_one : forall x, x + 1 = S x.
  Proof.
    intros. induction x.
    - simpl. reflexivity.
    - simpl. f_equal. assumption.
  Qed.

  Lemma plus_one' : forall x y, x + S y = S x + y.
  Proof.
    intros; simpl. induction x.
    - simpl. reflexivity.
    - simpl. f_equal. assumption.
  Qed.


  Lemma plus_comm : forall x y, x + y = y + x.
  Proof.
    intros. induction x.
    - induction y.
      + simpl; reflexivity.
      + simpl. rewrite <- IHy. simpl. reflexivity.
    - simpl. rewrite IHx. rewrite plus_one'. simpl. reflexivity.
  Qed.

  Lemma plus_assoc : forall x y z, x + (y + z) = x + y + z.
  Proof.
    intros. induction x.
    - simpl. reflexivity.
    - simpl. f_equal. assumption.
  Qed.
    
  Lemma mult_plus_one' : forall x y, x + x * y = x * S y.
  Proof.
    induction x.
    - simpl. reflexivity.
    - simpl. intro. rewrite <- IHx. f_equal.
      rewrite plus_assoc. rewrite plus_comm with (x:=x).
      rewrite plus_assoc. reflexivity.
  Qed.
  
  Lemma mult_comm : forall x y, x * y = y * x.
  Proof.
    induction x.
    - simpl. induction y.
      + simpl; reflexivity.
      + simpl; assumption.
    - simpl. intro. rewrite IHx. apply mult_plus_one'. 
  Qed.

    