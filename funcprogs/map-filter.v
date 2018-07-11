Require Import List.
Require Import PeanoNat.
Import PeanoNat.Nat.

Open Scope list_scope.

Print filter.
Print map.


Ltac dismiss := eexists; reflexivity.  (* used to finish a goal {y | y = ...} in the obvious way *)



Section MapFilter.

  Variables A B : Set.
  
  Lemma mapfilt (f: A -> B) (p : A -> bool) l : {ll | ll = map f (filter p l)}.
  Proof.
    generalize l.
    fix H0 1.
    case l0 as [|x xs]; simpl.
    - eexists; reflexivity.
    - edestruct H0 as [r R].
      case (p x); simpl.
      + rewrite <- R.
        eexists; reflexivity.
      + rewrite <- R.
        eexists; reflexivity.   
  Defined.

End MapFilter.


Extraction mapfilt.


Print length.


Section FilterLength.

  Variable A : Set.

  Lemma count (p : A -> bool) l : {y | y = length (filter p l)}.
  Proof.
    generalize l.
    fix H0 1.
    case l0 as [|x xs]; simpl.
    - dismiss.
    - edestruct H0 as [r R].
      case (p x); simpl.
      + rewrite <- R.
        dismiss.
      + rewrite <- R.
        dismiss.
  Defined.

  Lemma lt_S_S : forall n m, S n < S m <-> n < m.
  Proof.
    split.
    apply Lt.lt_S_n. apply Lt.lt_n_S.
  Qed.
  
  Lemma reflect_rewrite P p Q q : (P <-> Q) -> Bool.reflect P p -> Bool.reflect Q q -> p = q.
  Proof.
    intros. case H0; case H1; try reflexivity.
    - intros; absurd Q; try assumption; apply H; assumption.
    - intros; absurd P; try assumption; apply H; assumption.
  Qed.

  Lemma ltb_S_S : forall n m, (S n <? S m) = (n <? m).
  Proof.
    intros.
    eapply reflect_rewrite.
    eapply lt_S_S.
    apply ltb_spec0.
    apply ltb_spec0.
  Qed.

 
  Lemma less_than (p : A -> bool) n l :
    {y | y = (length (filter p l) <? n)}.
  Proof.
    generalize l n.
    fix H0 1.
    case l0 as [|x xs]; simpl.
    - dismiss.
    - 
      case (p x); simpl.
      + intro; case n0.
        * compute. dismiss.
        * intros; rewrite ltb_S_S.
          ecase H0 as [r R].
          rewrite <- R. dismiss.
      + intros; ecase H0 as [r R].
        rewrite <- R. dismiss.
  Defined.
        
End FilterLength.


Extraction count.
Extraction less_than.

