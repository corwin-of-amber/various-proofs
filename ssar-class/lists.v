Set Implicit Arguments.
Require Import Lists.List.
Import ListNotations.

Check list.


Print rev.


Fixpoint is_sorted A (l : list A) (R : A -> A -> Prop) :=
  match l with
    [] => True
  | x :: xs => match xs with
                [] => True
              | y :: ys => R x y /\ is_sorted xs R
              end
  end.


Theorem warm_up : is_sorted [3;5;9] le.
Proof.
  firstorder.
  (* alternatively: (...)
  simpl.
  split. repeat constructor. (* constructor. constructor. constructor. *)
  repeat constructor.
   (* constructor. constructor. constructor. constructor.
      constructor. constructor. *) *)
Qed.


Lemma is_sorted' : forall A (l : list A) R a b, is_sorted (l ++ [a]) R -> R a b -> is_sorted (l ++ [a; b]) R.
Proof.
  intros.
  induction l.
  - simpl. firstorder.
  - simpl.
    destruct l.
    (* `simpl in *` simplifies the goal and all the premises.
       it is not needed here, but will help you see why `firstorder`
       works. *)
    + simpl in *. firstorder.
      (* alternatively:
      split.
      * apply H.
      * apply IHl. constructor. *)
    + simpl in *. firstorder.
      (* alternatively:
      split.
      * apply H.
      * apply IHl. apply H. *)
Qed.
    
Theorem rev_sorted : forall l, is_sorted l lt -> is_sorted (rev l) gt.
Proof.
  induction l.
  - intro; simpl. trivial.
  - simpl. induction l.
    + simpl. trivial.
    + simpl. simpl in IHl. firstorder. rewrite <- app_assoc. apply is_sorted'.
      * assumption.
      * assumption.
Qed.

