
Axiom c : nat -> nat.
Fixpoint triv n := match n with O => 1 | S n' => 2 * n' end.

Print triv.

Ltac xform t :=
  let tac := xform in
  lazymatch (eval hnf in t) with
  | (fun n:nat => ?a) => let ret := constr:(fun n:nat => let a' := a in ltac:(tac a')) in
                   let ret' := (eval cbv zeta in ret) in exact ret'
  | (match ?n with O => ?a | S n' => ?b end) =>
    let ret := constr:(match n with
                       | O => let ret'O := a in ltac:(tac ret'O)
                       | S n' => let ret'S := b in ltac:(tac ret'S)
                       end) in
    let ret' := (eval cbv zeta in ret) in
    exact ret'
  (*| (fix f (n : nat) := _) => let ret := constr:(fix f n := a) in exact ret*)
  | _ =>
    lazymatch (type of t) with
    | nat => exact (S t)
    | _ => exact t
    end
  end.

Print triv.

Definition xx := ltac:(xform triv).
Print xx.

Definition triv' n : {y | y = triv n}.
  generalize n; fix H 1. destruct n0.
  - simpl; eexists; reflexivity.
  - simpl. rewrite <- plus_n_O. eexists; reflexivity.
Defined.

Print triv'.



Require Import Wf.

Definition R x y := y = S x.
Lemma wf_R : well_founded R.
  red.
  induction a.
  - econstructor.
    unfold R. intros. inversion H.
  - econstructor.
    intros.
    unfold R in H.
    injection H.
    intro; subst.
    assumption.
Defined.

Definition fact : nat -> nat.
  refine (@Fix nat R wf_R (fun _ => nat) (fun n fact' => match n as k return (k = n -> nat) with
                                               | O => fun _ => 1
                                               | S n' => fun e => n * fact' n' _
                                               end eq_refl)).
  - unfold R.
    symmetry; assumption.
Defined.

Compute (fact 3).

Print cons.

Ltac xform' t :=
  let tac := xform' in
  lazymatch (eval cbv delta beta in t) with
  | (fun n:nat => ?a) =>
    let ret := constr:(fun n:nat => let ret' := a in ltac:(tac ret')) in
    let ret' := (eval cbv zeta in ret) in
    exact ret'
  | (match ?n with O => ?a | S n' => ?b end) =>
    let ret := constr:(match n with
                       | O => let ret'O := a in ltac:(tac ret'O)
                       | S n' => let ret'S := b in ltac:(tac ret'S)
                       end) in
    let ret' := (eval cbv zeta in ret) in
    exact ret'
  | (match ?e with eq_refl => ?a end) =>
    let ret := tac a in
    exact ret
  | exist _ ?v _ => exact v
  | ?a => let ret := constr:(proj1_sig a) in let ret' := (eval cbv beta in ret) in exact ret
  end.

Definition xx' := ltac:(xform' triv').
Print xx'.
Print exist.