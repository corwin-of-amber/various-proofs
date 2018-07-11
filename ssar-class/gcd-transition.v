Set Implicit Arguments.
Require Import Arith.



  Definition divides a b := exists k, a * k = b.
  Notation "( a | b )" := (divides a b).

  Lemma divides_refl : forall n, (n | n).
  Proof.
    exists 1. firstorder.
  Qed.

  Section Gcd.

    Definition state : Set := nat * nat.    (*  (a, b)  *)
  
    Inductive step : state -> state -> Prop :=
      step_a : forall a b, a > b -> step (a, b) (a - b, b)
    | step_b : forall a b, a < b -> step (a, b) (a, b - a).


    Lemma div_inv a b a' b' : step (a, b) (a', b') ->
                              forall z, (z | a) /\ (z | b) <-> (z | a') /\ (z | b').

    
    Definition is_gcd (a b z : nat) :=
      (z | a) /\ (z | b) /\ forall z', (z' | a) -> (z' | b) -> (z' | z).  


    Lemma gcd_inv a b a' b' : step (a, b) (a', b') ->
                              forall z, is_gcd a b z <-> is_gcd a' b' z.






  End Gcd.
