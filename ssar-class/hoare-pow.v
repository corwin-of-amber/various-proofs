Require Import Arith.
Import Nat.


Load hoare.

(*
power(x, n):
  a := 1;
  while n > 0 do    { x0 ^ n0 = a * x ^ n }
    y := n mod 2;
    n := n div 2;

    if y then a := a * x else skip;
    if n then x := x * x else skip
 *)

Definition gt01 n m := if gt_dec n m then 1 else 0.

Notation "[ e1 `*` e2 ]" := (expr_op e1 mul e2).
Notation "[ e1 `/` e2 ]" := (expr_op e1 div e2).
Notation "[ e1 `%` e2 ]" := (expr_op e1 modulo e2).
Notation "[ e1 `>` e2 ]" := (expr_op e1 gt01 e2).

Definition power_cmd :=
  seq (assign a (expr_num 1))
      (while [expr_var n `>` expr_num 0]
             (seq (assign y [expr_var n `%` expr_num 2])
                  (seq (assign n [expr_var n `/` expr_num 2])
                       (seq (if_then_else (expr_var y)
                                          (assign a [expr_var a `*` expr_var x])
                                          skip)
                            (if_then_else (expr_var n)
                                          (assign x [expr_var x `*` expr_var x])
                                          skip)
                       )
                  )
             )
      ).



Module MainProof.

  Definition c :=
    (seq (assign y [expr_var n `%` expr_num 2])
         (seq (assign n [expr_var n `/` expr_num 2])
              (seq (if_then_else (expr_var y)
                                 (assign a [expr_var a `*` expr_var x])
                                 skip)
                   (if_then_else (expr_var n)
                                 (assign x [expr_var x `*` expr_var x])
                                 skip)
              )
         )
    ).

  Definition linv x0 n0 := fun s => x0 ^ n0 = s a * (s x ^ s n).

  (* Control the behavior of `simpl` to allow more unfoldings. *)
  Arguments subst P v e /.
  Arguments set s v / z.
  Arguments var_eq_dec !v1 !v2.
  Arguments div !x !y.
  Arguments modulo !x !y.
  Arguments gt01 n m / : simpl nomatch.

  Lemma div_mod_n n k : k > 0 -> n = (n / k) * k + (n mod k).
  Admitted.

  Definition c1 := 
    (seq (assign y [expr_var n `%` expr_num 2])
         (assign n [expr_var n `/` expr_num 2])).

  
  
  Definition c2 :=
    (seq (if_then_else (expr_var y)
                       (assign a [expr_var a `*` expr_var x])
                       skip)
         (if_then_else (expr_var n)
                       (assign x [expr_var x `*` expr_var x])
                       skip)
    ).

  Lemma linv_advance x0 n0 : hoare (fun s => linv x0 n0 s /\ s n > 0)
                                   c1
                                   (fun s => x0 ^ n0 = s a * (s x * s x) ^ s n * s x ^ s y
                                          /\ s y <= 1).
  Proof.
    econstructor.
    2: constructor.
    eapply hoare_weaken_l.
    2: constructor.
    unfold linv; simpl.
    intros s [H1 H2].
    split.
    - rewrite H1.
      rewrite div_mod with (x:=s n) (y:=2) at 1; [|firstorder].
      rewrite pow_add_r.
      rewrite pow_mul_r. simpl. rewrite mul_assoc. firstorder.
    - apply lt_n_Sm_le. apply mod_upper_bound. firstorder.
  Qed.    

  Inductive hoare_two : assertion -> cmd -> cmd -> assertion -> Prop :=
    hoare_two_seq : forall c1 c2 P M Q,
      hoare P c1 M -> hoare M c2 Q -> hoare_two P c1 c2 Q
  | hoare_two_weaken : forall (P' P : assertion) c1 c2 (Q Q' : assertion),
      (forall s, P' s -> P s) ->
      hoare_two P c1 c2 Q ->
      (forall s, Q s -> Q' s) ->
      hoare_two P' c1 c2 Q'.

  Lemma hss' P c1 c2 Q c12 : c12 = seq c1 c2 ->
                             hoare P c12 Q -> hoare_two P c1 c2 Q.
  Proof.
    intros.
    induction H0; inversion H.
    - eapply hoare_two_seq. subst. eassumption. subst. eassumption.
    - eapply hoare_two_weaken. eassumption. subst; firstorder. eassumption.
  Qed.

  Lemma hss P c1 c2 Q : hoare P (seq c1 c2) Q -> hoare_two P c1 c2 Q.
  Proof.
    apply hss'. reflexivity.
  Qed.

  Lemma hoare_middle_ground' P c1 c2 Q : hoare_two P c1 c2 Q ->
                                         exists M, hoare P c1 M /\ hoare M c2 Q.
  Proof.
    induction 1.
    - exists M; firstorder.
    - destruct IHhoare_two as [M].
      exists M. firstorder.
      + eapply hoare_weaken_l; eassumption.
      + eapply hoare_weaken_r; eassumption.
  Qed.

  Lemma hoare_middle_ground P c1 c2 Q : hoare P (seq c1 c2) Q ->
                                        exists M, hoare P c1 M /\ hoare M c2 Q.
  Proof.
    intro; apply hoare_middle_ground'. apply hss. assumption.
  Qed.
  
  Lemma hoare_seq_assoc P Q c1 c2 c3 :
    hoare P (seq c1 (seq c2 c3)) Q <-> hoare P (seq (seq c1 c2) c3) Q.
  Proof.
    split.
    - intro H. apply hoare_middle_ground in H.
      destruct H as [M1 [H1 H23]].
      apply hoare_middle_ground in H23.
      destruct H23 as [M2 [H2 H3]].
      econstructor.
      + econstructor; eassumption.
      + assumption.
    - intro H. apply hoare_middle_ground in H.
      destruct H as [M2 [H12 H3]].
      apply hoare_middle_ground in H12.
      destruct H12 as [M1 [H1 H2]].
      econstructor.
      + eassumption.
      + econstructor; eassumption.
  Qed.
    (* -- this went terribly bad --
    split.
    intro H. apply hss in H. inversion H.
    - apply hss in H1. subst. induction H1.
      + econstructor.
        econstructor.
        eassumption. eassumption. eassumption.
      + eapply hoare_weaken_r.
        2: apply IHhoare_seq_seq.
        * firstorder.
        * eapply hoare_seq_weaken.
          2: eassumption.
       *)   


  Require Omega.
  
  Lemma linv_inv x0 n0 : hoare (fun s => linv x0 n0 s /\ s n > 0)
                               c
                               (linv x0 n0).
  Proof.
    apply hoare_seq_assoc.
    econstructor.
    - apply linv_advance.
    - econstructor.
      Focus 2.
      {
        econstructor.
        - eapply hoare_weaken_l.
          2: constructor.
          unfold linv; simpl.
          intros. destruct H.
          exact H.
        - eapply hoare_weaken_l.
          2: constructor.
          unfold linv; simpl.
          intros s [H1 H2].
          rewrite H1, H2. reflexivity.
      }
      Unfocus.
      econstructor.
      + eapply hoare_weaken_l. 2: constructor.
        simpl.
        intros s [[H1 H2] H3].
        assert (s y = 1) by firstorder.
        rewrite H1, H, pow_1_r.
        rewrite <- mul_assoc.
        rewrite mul_comm with (n:=_ ^ s n).
        rewrite mul_assoc.
        reflexivity.
      + eapply hoare_weaken_l. 2: constructor.
        simpl.
        intros s [[H1 H2] H3].
        rewrite H1, H3. firstorder.
  Qed.
      
        
End MainProof.
