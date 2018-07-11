Set Implicit Arguments.
Require Import Lists.List.
Import ListNotations.



Section ListDel.

  Variable E : Set.

  Hypothesis Eeq_dec : forall x y : E, {x = y} + {x <> y}.

  Hypothesis in_cons : forall (e a : E) l, In e (a :: l) -> a = e \/ In e l.
  
  Definition list_delete : forall (l : list E) (e : E), exists l',
        forall e', In e' l' <-> In e' l /\ e' <> e.
  Proof.
    induction l.
    - intros. eexists. intros. simpl.
      firstorder.
      + eapply in_nil. eassumption.
      + firstorder.
    - intro e.
      edestruct IHl with (e:=e) as [l']. 
      intros. 
      destruct (Eeq_dec a e).
      + eexists. intros. simpl.
        firstorder.
        * right. apply H. eassumption.
        * firstorder.
        * subst. firstorder.
        * apply H. firstorder.
      + eexists. intros. simpl.
        firstorder.
        * apply in_cons. apply H0.
        * destruct (in_cons H0); try congruence.
          apply H. assumption.