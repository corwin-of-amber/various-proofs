Set Implicit Arguments.
Require Import List.
Import ListNotations.

Require Import Omega.  (* also makes firstorder more powerful! *)



  Definition state : Set := nat * list nat.

  Inductive step : state -> state -> Prop :=
    step1_hi : forall n x xs, n > 100 -> step (1, n :: x :: xs) (x, (n - 10) :: xs)
  | step1_lo : forall n xs, n <= 100 -> step (1, n :: xs) (1, (n + 11) :: 4 :: xs)
  | step4 : forall n xs, step (4, n :: xs) (1, n :: 5 :: xs)
  | step5 : forall n x xs, step (5, n :: x :: xs) (x, n :: xs)
  .

  Definition inv1 s :=
    match s with
      (i, n :: xs) => i = 1 \/ i = 4 \/ In 4 xs \/ n >= 91
    | _ => False
    end.

  Lemma inv1_inv s1 s2 : inv1 s1 -> step s1 s2 -> inv1 s2.
  Proof.
    induction 2; firstorder.
  Qed.

  Definition inv2 (s : state) :=
    match s with
      (i, n :: xs) => forall a, In a xs -> In a [0; 4; 5]
    | _ => False
    end.

  Lemma inv2_inv s1 s2 : inv2 s1 -> step s1 s2 -> inv2 s2.
  Proof.
    induction 2; firstorder.
  Qed.
      
  Fixpoint cnt4 l :=
    match l with
      [] => 0
    | 4 :: xs => 1 + cnt4 xs
    | _ :: xs => cnt4 xs
    end.

  (* Definition cnt4 l := count_occ Nat.eq_dec l 4. *)
  
  Definition inv3 (s : state) :=
    match s with
      (i, n :: xs) => (i = 1 \/ i = 4) /\ n <= (cnt4 xs) * 10 + 101 \/
                     (i = 0 \/ i = 5) /\ n <= (cnt4 xs) * 10 + 91
    | _ => False
    end.

  Lemma inv3_inv s1 s2 : inv2 s1 -> inv3 s1 -> step s1 s2 -> inv3 s2.
  Proof.
    induction 3.
    (* intros Inv2 Inv3 Step. *)
    (* induction Step. *)
    - destruct H with (a:=x).
      + firstorder.
      + subst. right. simpl in H0. omega.
      + destruct H2.
        * subst. left.
          { destruct H0.
            - simpl in H0. omega.
            - simpl in H0. omega.
          }
        * destruct H2; try contradiction.
          subst. right. simpl in H0. omega.
    - left. simpl. omega.
    - left. simpl in H0. simpl. omega.
    - destruct H with (a:=x).
      + firstorder.
      + subst. right. simpl in H0. omega.
      + destruct H1.
        * subst.  left. simpl in H0. omega.
        * destruct H1; try contradiction.
          subst. right. simpl in H0. omega.
  Qed.


  Section ReflexiveTransitiveClosureDef.

    Variable D : Set.
    Variable R : D -> D -> Prop.

    Inductive tc : D -> D -> Prop :=
      tc_refl : forall s, tc s s
    | tc_step : forall s u t, R s u -> tc u t -> tc s t.

  End ReflexiveTransitiveClosureDef.

  Lemma inv123_tc s1 s2 : inv1 s1 -> inv2 s1 -> inv3 s1 -> tc step s1 s2 ->
                          inv1 s2 /\ inv2 s2 /\ inv3 s2.
  Proof.
    induction 4.
    - firstorder.
    - apply IHtc; firstorder using inv1_inv, inv2_inv, inv3_inv.
  Qed.

  Theorem mccarthy91 n n' : n <= 101 -> tc step (1, [n; 0]) (0, [n']) -> n' = 91.
  Proof.
    intros.
    assert (inv1 (0, [n']) /\ inv2 (0, [n']) /\ inv3 (0, [n'])).
    - apply inv123_tc with (s1:=(1, [n; 0])).
      + firstorder.
      + firstorder.
      + firstorder.
      + assumption.
    - firstorder.
  Qed.

  
  