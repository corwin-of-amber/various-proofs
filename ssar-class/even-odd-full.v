Require Import Nat.

Section EO.

  Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
  with odd : nat -> Prop :=
       | odd_S : forall n, even n -> odd (S n).

  Fixpoint is_even n :=
    match n with
      0 => True
    | S 0 => False
    | S (S k) => is_even k
    end.

  Compute is_even 8.
  
  Lemma better_together: forall n, even n \/ odd n.
  Proof.
    induction n.
    + left. constructor.
    + induction IHn.
      - right. constructor. assumption.
      - left. constructor. assumption.
  Qed.

  Lemma zero : ~ odd 0.
  Proof.
    assert (forall n, odd n -> 0 <> n).
    + intros n H.
      induction H.
      discriminate.
    + intro Hz; eapply H.
      - apply Hz.
      - reflexivity.
  Qed.

End EO.
