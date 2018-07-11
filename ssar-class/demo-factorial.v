Set Implicit Arguments.
Require Import Arith.

  (* factorial *)

  Definition state : Set := nat * nat.     (* (n, a) *)

  Inductive init n0 : state -> Prop :=
    start : init n0 (n0, 1).
  
  Inductive step : state -> state -> Prop :=
    step0 : forall n a, n > 0 -> step (n, a) (n - 1, a * n).

  (*
   * Specification -- program returns `fact n0`
   *  (where n0 is the input, i.e. initial value of n)
   *)
  Definition spec n0 s :=
    match s with
      (0, a) => a = fact n0
    | _ => True
    end.

  Print fact.  (* `fact` is defined in the Arith library *)
  

  (* General Definition *)
  Section ReflexiveTransitiveClosureDef.

    Variable D : Set.
    Variable R : D -> D -> Prop.

    Inductive tc : D -> D -> Prop :=
      tc_refl : forall s, tc s s
    | tc_step : forall s u t, R s u -> tc u t -> tc s t.

  End ReflexiveTransitiveClosureDef.

  Check tc.
  Print Implicit tc.

  
  Theorem spec_holds n0 s0 s : init n0 s0 -> tc step s0 s -> spec n0 s.
  Proof.
    intros.
    induction H0.
    - admit.
    - apply IHtc.
Abort.
  






  
  Definition inv n0 s :=
    match s with
      (n, a) => a * fact n = fact n0
    end.

  Lemma inv_inv n0 s0 s : init n0 s0 -> tc step s0 s -> inv n0 s.
  Proof.
    intros. induction H0.
    - admit.
    - apply IHtc.
  Abort.



    




    
  Lemma inv_inv' n0 s0 s : inv n0 s0 -> tc step s0 s -> inv n0 s.
  Proof.
    intros Inv Reach. induction Reach.
    - assumption.
    - apply IHReach.
      destruct H.
      destruct n.
      + inversion H.
      + simpl. unfold inv in Inv.
        rewrite Nat.sub_0_r.
        rewrite <- Nat.mul_assoc.
        assumption.
  Qed.


  Lemma inv_inv n0 s0 s : init n0 s0 -> tc step s0 s -> inv n0 s.
  Proof.
    intro Init.
    apply inv_inv'.
    unfold inv. destruct Init.
    firstorder.
  Qed.

  Theorem spec_holds n0 s0 s : init n0 s0 -> tc step s0 s -> spec n0 s.
  Proof.
    intros.
    enough (inv n0 s).
    - destruct s.
      unfold spec.
      destruct n.
      destruct H1.
      + firstorder.
      + constructor.
    - eapply inv_inv.
      eassumption.
      assumption.
  Qed.