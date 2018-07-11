Require Import Arith.
Import Nat.


Load hoare.


(*
euclid(a, b):
  while a != b do
    if a > b then
      a := a - b
    else
      b := b - a
 *)

Definition gt01 n m := if gt_dec n m then 1 else 0.
Definition ne01 n m := if eq_dec n m then 0 else 1.

Notation "[ e1 `-` e2 ]" := (expr_op e1 sub e2).
Notation "[ e1 `>` e2 ]" := (expr_op e1 gt01 e2).
Notation "[ e1 `!=` e2 ]" := (expr_op e1 ne01 e2).


Definition euclid_cmd :=
  while [expr_var a `!=` expr_var b]
        (if_then_else [expr_var a `>` expr_var b]
                      (assign a [expr_var a `-` expr_var b])
                      (assign b [expr_var b `-` expr_var a])).


(* Definition of divisibility + some syntactic sugar *)
Definition divides a b := exists k, a * k = b.
Notation "( a | b )" := (divides a b).


Module MainProof.

  Definition c := if_then_else [expr_var a `>` expr_var b]
                               (assign a [expr_var a `-` expr_var b])
                               (assign b [expr_var b `-` expr_var a]).

  Definition linv a0 b0 :=
    fun s => forall z, (z | a0) /\ (z | b0) <-> (z | s a) /\ (z | s b).

  (* Control the behavior of `simpl` to allow more unfoldings. *)
  Arguments subst P v e /.
  Arguments set s v / z.
  Arguments var_eq_dec !v1 !v2.
  Arguments gt01 n m / : simpl nomatch.
  Arguments ne01 n m / : simpl nomatch.

  Require Import Omega.
  
  Lemma gt0_le x y : gt01 x y = 0 <-> x <= y.
  Proof.
    unfold gt01.
    destruct (gt_dec x y); firstorder.
  Qed.

  Lemma gt1_gt x y : gt01 x y <> 0 <-> x > y.
  Proof.
    unfold gt01.
    destruct (gt_dec x y); firstorder.
  Qed.

  Lemma div_sub a b z : (z | a) -> (z | b) -> (z | a - b).
  Proof.
    firstorder. exists (x1 - x0).
    rewrite Nat.mul_sub_distr_l.
    firstorder.
  Qed.

  Lemma sub_div1 a b z : a >= b -> (z | a) -> (z | a - b) -> (z | b).
  Proof.
    firstorder. exists (x1 - x0).
    rewrite Nat.mul_sub_distr_l.
    firstorder.
  Qed.

  Lemma sub_div2 a b z : a >= b -> (z | b) -> (z | a - b) -> (z | a).
  Proof.
    firstorder. exists (x0 + x1).
    rewrite Nat.mul_add_distr_l.
    firstorder.
  Qed.


  Lemma warm_up a0 b0 : hoare (fun s => s a = a0 /\ s b = b0)
                              (assign a [expr_var a `-` expr_var b])
                              (fun s => s a = a0 - b0).
  Proof.
    eapply hoare_weaken_l.
    2: constructor.
    intros s [H1 H2].
    simpl. firstorder.
  Qed.

  Lemma aux1 a0 b0 a b: (forall z, (z | a0) /\ (z | b0) <-> (z | a) /\ (z | b)) ->
                        a > b ->
                        forall z, (z | a0) /\ (z | b0) <-> (z | a - b) /\ (z | b).
  Admitted.

  Lemma aux2 a0 b0 a b: (forall z, (z | a0) /\ (z | b0) <-> (z | a) /\ (z | b)) ->
                        a < b ->
                        forall z, (z | a0) /\ (z | b0) <-> (z | a) /\ (z | b - a).
  Admitted.
                                                     
  Lemma euclid_inv a0 b0 : hoare (fun s => linv a0 b0 s /\ s a <> s b)
                                 c
                                 (linv a0 b0).
  Proof.
    constructor.
    - eapply hoare_weaken_l.        (* "then" branch -- a > b *)
      2: constructor.
      unfold linv; simpl.
      intros; apply aux1.
      + firstorder.
      + firstorder. apply gt1_gt. assumption.
      (*
      firstorder.
      + apply div_sub.
        * apply H. firstorder.
        * apply H. firstorder.
      + apply H. split.
        * { eapply sub_div2 with (b:=s b).
            - apply gt1_gt in H0. omega.
            - firstorder.
            - firstorder.
          }
        * eexists; eassumption.
      + apply H. split. (* identical to previous branch *)
        * { eapply sub_div2 with (b:=s b).
            - apply gt1_gt in H0. omega.
            - firstorder.
            - firstorder.
          }
        * eexists; eassumption.
      *)
    - eapply hoare_weaken_l.        (* "else" branch -- a < b *)
      2: constructor.
      unfold linv; simpl.
      intros; apply aux2.
      + firstorder.
      + firstorder.
        apply le_neq.
        firstorder using gt0_le.
      (*
      intros s [[H0 H1] H2].  (* can be a bit more economical by *)
      split.                  (* postponing use of firstorder    *)
      + split.
        * apply H0. assumption.
        * apply div_sub; firstorder.
      + intro; apply H0. split.
        * firstorder.
        * { eapply sub_div2.
            - apply gt0_le. eassumption.
            - firstorder.
            - firstorder.
          }
      *)
  Qed.

  Theorem euclid_post a0 b0 : hoare (fun s => s a = a0 /\ s b = b0)
                                    euclid_cmd
                                    (fun s => forall z, (z | a0) /\ (z | b0) <-> (z | s a)).
  Proof.
    eapply hoare_weaken.
    Focus 2.
    {
      apply hoare_while with (P:=linv a0 b0).
      eapply hoare_weaken_l.
      2: apply euclid_inv.
      unfold linv; simpl. firstorder.
      unfold ne01 in H0.
      destruct (eq_dec (s a) (s b)).
      - firstorder.
      - firstorder.
    }
    Unfocus.
    - unfold linv. intros s [A B]. subst; firstorder.
    - unfold linv; simpl. intros s [H1 H2].
      unfold ne01 in H2; destruct (eq_dec (s a) (s b)).
      + split; intro; apply H1.
        firstorder.
        split. assumption. rewrite <- e; assumption.
      + firstorder.
  Qed.
  
End MainProof.
