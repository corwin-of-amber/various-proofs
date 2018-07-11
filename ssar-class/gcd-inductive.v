Require Import Arith.Arith.
Import Nat.

(* ----------------------------------------------------------------- *)
(* Let's start by proving some basic facts about natural numbers.    *)

(* this one is going to come in handy *)
Theorem f_equal : forall A B (f : A -> B) x y, x = y -> f x = f y.
Proof.
  intros. rewrite H. reflexivity.  (* First one's free. *)
Qed.                               (* Try to understand it though! *)

Eval simpl in fun x => 1 + x.
Eval simpl in fun x => x + 1.  (* notice that "+" is not defined symmetrically *)

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
  - simpl. f_equal. assumption.  (* firstorder also works *)
Qed.

(* Definition of divisibility + some syntactic sugar *)
Definition divides a b := exists k, a * k = b.
Notation "( a | b )" := (divides a b).

(* commutativity lemmas. we're about to need them. *)
Check Nat.add_comm.
Check Nat.mul_comm.
  
Lemma divides_refl : forall n, (n | n).
Proof.
  intros; exists 1. rewrite Nat.mul_comm. simpl. rewrite Nat.add_comm.
  simpl. reflexivity.
Qed.


(* ----------------------------------------------------------------- *)
(* Armed with these lemmas, let's try to define the Greatest Common  *)
(* Denominator and Euclid's algorithm.                               *)

Section Gcd.

  Definition is_gcd (a b z : nat) :=
    (z | a) /\ (z | b) /\ forall z', (z' | a) -> (z' | b) -> (z' | z).  

  (* First some basic properties of gcd *)
  Theorem is_gcd_refl : forall z, is_gcd z z z.
  Proof.
    intros; firstorder.
    - apply divides_refl.
    - apply divides_refl.
    (* alternatively:
    intros; split; [|split].
    - apply divides_refl.
    - apply divides_refl.
    - trivial. *)
  Qed.

  Theorem is_gcd_comm : forall a b z, is_gcd a b z -> is_gcd b a z.
  Proof.
    firstorder.
    (* alternatively: *
    intros. induction H. induction H0. split; [|split].
    - assumption.
    - assumption.
    - intros; apply H1.
      + assumption.
      + assumption. *)
  Qed.

  (* -- this is a simplified version of Euclid -- *)
  Inductive gcd : nat -> nat -> nat -> Prop :=
    base : (forall z, gcd z z z)
  | step_a : forall a b z, gcd a b z -> gcd (a + b) b z
  | step_b : forall a b z, gcd a b z -> gcd a (a + b) z.

  (* distributivity lemmas. you will need them! *)
  Check Nat.mul_add_distr_l.
  Check Nat.mul_sub_distr_l.

  Search add mul.       (* this is how you could find them yourself *)
  Search sub mul.       (* if I hadn't told you *)

  Lemma gcd_step_aux : forall a b z, is_gcd a b z -> is_gcd (a + b) b z.
  Proof.
    intros.
    induction H. firstorder.
    + exists (x0 + x). rewrite Nat.mul_add_distr_l. rewrite H0. rewrite H. reflexivity.
    + apply H1.
      * exists (x2 - x1). rewrite Nat.mul_sub_distr_l.
        rewrite H3. rewrite H2. apply Nat.add_sub.
      * exists x1; assumption.  (* or: eexists; eassumption *)
  Qed.
  
  Theorem gcd_pcorrect : forall a b z, gcd a b z -> is_gcd a b z.
  Proof.
    intros. induction H.
    - apply is_gcd_refl.
    - apply gcd_step_aux. assumption.
    - apply is_gcd_comm. rewrite Nat.add_comm. apply gcd_step_aux.
      apply is_gcd_comm. assumption.
  Qed.

  (* -- This is a more accurate description of Euclid's algorithm *)
  Inductive euclid : nat -> nat -> nat -> Prop :=
    base' : (forall z, euclid z z z)
  | step_a' : forall a b z, a > b -> euclid (a - b) b z -> euclid a b z
  | step_b' : forall a b z, a < b -> euclid a (b - a) z -> euclid a b z.  


  Theorem euclid_gcd : forall a b z, euclid a b z -> gcd a b z.
  Proof.
    intros.
    induction H.
    - constructor.
    - rewrite <- sub_add with (m:=a) (n:=b).
      constructor. assumption. firstorder.
    - rewrite <- sub_add with (m:=b) (n:=a). rewrite Nat.add_comm.
      constructor. assumption. firstorder.
  Qed.

  Require Import Init.Wf.

  Inductive R : (nat*nat) -> (nat*nat) -> Prop :=
    by_max : forall a0 b0 a1 b1, max a0 b0 < max a1 b1 -> R (a0, b0) (a1, b1).

  Theorem Rwf' : forall m a b, max a b < m -> Acc R (a, b).
  Proof.
    induction m.
    - firstorder using nlt_0_r. 
    - intros. constructor. induction y.
      inversion_clear 1 as [? ? ? ? HH]. apply IHm.
      eapply lt_le_trans. apply HH. firstorder.
  Qed.    

  Theorem Rwf : well_founded R.
  Proof.
    intro. induction a. eapply Rwf'.
    constructor.
  Qed.
  
  Theorem noether_max P : (forall a b, (forall a' b', max a' b' < max a b -> P a' b') -> P a b) ->
                              forall a b, P a b.
  Proof.
    intro. eapply well_founded_induction_type_2.
    - apply Rwf.
    - intros.  apply X. intros; apply X0. constructor.  assumption.
  Qed.

  Theorem case_split_3way P : forall a b,
      (a < b -> P a b) -> (a = b -> P a b) -> (a > b -> P a b) -> P a b.
  Proof.
    intros. destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt]; firstorder.
  Qed.


  Check lt_eq_lt_dec.

  Print max.

  Lemma max_decreases : forall a b, 0 < a < b -> max a (b - a) < max a b.
  Proof.
    intros. apply max_lub_lt. apply max_lt_iff. firstorder.
    apply max_lt_iff. right.
    apply sub_lt. firstorder. firstorder.
  Qed.

  Theorem euclid_terminates : forall a b, a > 0 -> b > 0 -> exists z, euclid a b z.
  Proof.
    intros a b. apply noether_max with (a:=a) (b:=b).
    clear a b.
    intros a b IH apos bpos.
    apply case_split_3way with (a:=a) (b:=b); intro H.
    - induction IH with (a':=a) (b':=b-a).     (* a < b *)
      * exists x. apply step_b'. assumption. assumption.
      * apply max_decreases. firstorder.
      * assumption.
      * Search "=" "<".
        (* psst, try this as well:
        firstorder using neq_0_lt, neq_sym, sub_gt. *)
        apply neq_0_lt.
        apply neq_sym.
        apply sub_gt. assumption.
    - exists a. rewrite H. constructor.             (* a = b *)
    - induction IH with (a':=a-b) (b':=b).     (* a > b *)
      * exists x. apply step_a'. assumption. assumption.
      * Check max_comm.
        rewrite max_comm. rewrite max_comm with (n:=a).
        apply max_decreases. firstorder.
      * apply neq_0_lt.
        apply neq_sym.
        apply sub_gt. assumption.
      * assumption.
  Qed.

End Gcd.
