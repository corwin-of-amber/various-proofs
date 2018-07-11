Require Import List.
Require Import Coq.ZArith.ZArith.

Open Scope list_scope.


Inductive lodd {A} : list A -> Type :=
  | lodd_O : lodd nil  (* sorry *)
  | lodd_S : forall x xs, leven xs -> lodd (x :: xs)
with leven {A} : list A -> Type :=
     | leven_O : leven nil
     | leven_S : forall x xs, lodd xs -> leven (x :: xs).
                                         
Scheme lodd_leven := Minimality for lodd Sort Set
  with leven_lodd := Minimality for leven Sort Set.


Lemma lt_S_cases : forall n m, n < S m -> n = m \/ n < m.
Proof.
  inversion 1.
  - left; reflexivity.
  - right; assumption.
Qed.

Lemma lt_S_cases_type : forall n m, n < S m -> {n = m} + {n < m}.
Admitted.
  
Theorem strong_induction':
forall P : nat -> Prop,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n k : nat, k < n -> P k.
Proof.
  induction n.
  - intros. inversion H0.
  - intros. apply lt_S_cases in H0. destruct H0.
    + rewrite H0; apply H; apply IHn.
    + apply IHn; assumption.
Qed.

      
Theorem strong_induction:
forall P : nat -> Prop,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros. eapply strong_induction'.
  apply H.
  apply Nat.lt_succ_diag_r.
Qed.


Theorem strong_induction_type':
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n k : nat, k < n -> P k.
Proof.
  intros ? H.
  induction n.
  - intros. absurd (k < 0). apply Nat.nlt_0_r. assumption.
  - intros. apply lt_S_cases_type in H0. destruct H0.
    + rewrite e; apply H; apply IHn.
    + apply IHn; assumption.
Qed.

Theorem strong_induction_type:
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros. eapply strong_induction_type'.
  apply X.
  apply Nat.lt_succ_diag_r.
Qed.

Inductive substructure {A} : list A -> list A -> Type :=
| sHead : forall a l, substructure l (a :: l)
| sTail : forall a l1 l2, substructure l1 l2 -> substructure l1 (a :: l2).

Check substructure_ind.

Lemma substructure_cons_cases {A} :
  forall l1 l2 (a: A), substructure l1 (a :: l2) -> (l1 = l2) + (substructure l1 l2).
Proof.
  inversion 1.
  - left; reflexivity.
  - right; assumption.
Qed.

  
  
Theorem substructure_ind'' {A} (P : list A -> Prop) :
  (forall l1, (forall l2, substructure l2 l1 -> P l2) -> P l1)
  -> forall l1 l2, substructure l2 l1 -> P l2.
Proof.
  induction l1.
  - intros. inversion X.
  - intros. apply substructure_cons_cases in X. destruct X.
    + rewrite e. apply H; assumption.
    + apply IHl1; assumption.
Qed.

Theorem substructure_ind' {A} (P : list A -> Prop) :
  (forall l1, (forall l2, substructure l2 l1 -> P l2) -> P l1) -> forall l, P l.
Proof.
  intros.
  apply H.
  intros.
  eapply substructure_ind''.
  apply H.
  eassumption.
Qed.

Theorem substructure_rec'' {A} (P : list A -> Type) :
  (forall l1, (forall l2, substructure l2 l1 -> P l2) -> P l1)
  -> forall l1 l2, substructure l2 l1 -> P l2.
Proof.
  induction l1.
  - intros. inversion X0.
  - intros. apply substructure_cons_cases in X0. destruct X0.
    + rewrite e. apply X; assumption.
    + apply IHl1; assumption.
Qed.

Theorem substructure_rec' {A} (P : list A -> Type) :
  (forall l1, (forall l2, substructure l2 l1 -> P l2) -> P l1) -> forall l, P l.
Proof.
  intros.
  apply X.
  intros.
  eapply substructure_rec''.
  apply X.
  eassumption.
Qed.

