Require Import List.

Check nil.

Require Coq.Reals.Reals.

Import Coq.Reals.Rdefinitions.
Import Coq.Reals.Raxioms.

Open Scope list_scope.
Open Scope R_scope.

Check nil.

Check Coq.Reals.Rdefinitions.R.


Ltac dismiss := eexists; reflexivity.  (* used to finish a goal {y | y = ...} in the obvious way *)


Definition uncurry2 {A B C} (f : A -> B -> C) ab := f (fst ab) (snd ab).
    
Lemma uncurrying2 {A B C} (f : A -> B -> C) a b : f a b = uncurry2 f (a, b).
Admitted.

(* this is useless in its current form.
 * The idea is that a program of the form {y | y = f a} can be
 * composed by a program computing {y | y = a} followed by an application
 * of f; the program {y | y = a} can then be further refined.
 * But this one does not work because the fourth argument (a) is
 * not eliminated during extraction.
 *
Lemma seq {A B} (f : A -> B) a : {y | y = a} -> {y | y = f a}.
Admitted. *)



Notation Real := Coq.Reals.Rdefinitions.R.

Section Average.

  Fixpoint sum (l : list Real) : Real :=
    match l with
    | nil => 0
    | x::xs => x + sum xs
    end.

  Definition avg l := sum l / INR (length l).


  Lemma INR_S n : INR (S n) = 1 + INR n.
  Proof.
    simpl.
    destruct n.
    - simpl. rewrite RIneq.Rplus_0_r. reflexivity.
    - rewrite Rplus_comm. reflexivity.
  Qed.

    
  Arguments INR n : simpl nomatch.

  Lemma avg' l : {y | y = avg l}.
  Proof.
    unfold avg.
    (*rewrite (uncurrying2 Rdiv).
    apply seq.*)
    case l as [|x xs]; simpl.
    - dismiss.
    - rewrite INR_S. generalize x 1 xs.  (* "1" is called 'r' from now on *)
      fix aux 3.
      destruct xs0 as [|x' xs']; simpl.
      + rewrite !RIneq.Rplus_0_r. dismiss.
      + rewrite INR_S. rewrite <- !Rplus_assoc. apply aux.
  Defined.

  Compute (fun l => proj1_sig (avg' l)).
  
  Check exist.
  Search exist.
  Definition sigval {A} {P : A -> Prop} (x: {x | P x}) :=
    match x with exist _ v _ => v end.

  Lemma sigval_P {A} {P : A -> Prop} (x: {x | P x}) : P (sigval x).
    destruct x.
    simpl.
    assumption.
  Qed.

  Lemma avg'avg l : avg l = sigval (avg' l).
    destruct (avg' l).  (* Would be nice to use sigval_P? *)
    simpl.
    symmetry; assumption.
  Qed.

  Fixpoint avg'0 l :=
    match l with
    | nil => 0 / 0
    | x :: xs => aux x 1 xs
    end
  with aux x j xs :=
    match xs with
    | nil => x / j
    | x' :: xs' => aux (x + x') (j + 1) xs'
    end.

  
  Lemma avg'0avg l : avg l = avg'0 l.
    rewrite avg'avg.
    case l as [|x xs].
    - simpl. reflexivity.
    - simpl.
      unfold eq_rec_r, eq_rec, eq_rect.
      lazymatch goal with
      | [ |- context [?f x 1 xs] ] => set (fixterm := f)
      end.
      lazymatch goal with
      | [ |- ?a = _ ] => 
      replace a  with (
        match
          eq_sym (INR_S (length xs)) in (_ = y)
          return Real
        with
        | eq_refl => sigval (fixterm x 1 xs)
        end)
      end.
      Focus 2.
      clearbody fixterm.
      set (eq_sym _).
      set (fixterm x 1 xs).
      clearbody s e.
      Fail destruct e.  (* why does that not work?? *)
      
      Lemma buh : forall A (a b : A) (e : a = b) (f : A -> A) (s : {y | y = f a}),
          match e with
          | eq_refl => sigval s
          end =
          sigval
            match e in (_ = y) return {y0 | y0 = f y} with
            | eq_refl => s
            end.
        destruct e.
        reflexivity.
      Qed.

      apply buh.  (* but this does *)
      rewrite buh.
      refle
      rewrite (@buh Real _ _ e (fun y => (x + sum xs) / y) s).
      
      Print INR.
      Require Import Program.
      dependent destruction e.
      setoid_rewrite <- x.
      clearbody e. destruct xs.
      Focus 2. simpl.
      simpl in e.
      rewrite Rplus_comm in e.
      Print eq_rect.
      generalize x xs.
      generalize 1.
      induction xs.
      + simpl.
        give_up.
      + simpl.
*)
End Average.

Check seq.
Extraction avg'.

Definition a := fun x:nat => ltac:(exact x).

Require Import Utf8.

Ltac ret_and_left f :=
  let tac := ret_and_left in
  let T := type of f in
  lazymatch eval hnf in T with
  | ?a /\ ?b => exact (proj1 f) | ?T' → _
=> let ret := constr:(fun x' : T' => let fx := f x' in ltac:(tac fx)) in let ret' := (eval cbv zeta in ret) in
exact ret'
  end.

Goal match 5%nat with O => 0 | S _ => 1 end = 1.
  match goal with
  | [  |- context [match _ with O => _ | S _ => ?a end] ] => pose a
  end.

Goal ∀ A B : Prop, (A → A → A ∧ B) → True.
intros A B H.
pose ltac:(ret_and_left H).
Print a.
Print avg'.
Extraction avg'0.
Print avg'0.


Section Stddev.

  Definition sqr x := x * x.

  Definition variance l := avg (map (fun x => sqr (x - avg l)) l).

  Print avg'.
  
  Arguments INR n : simpl nomatch.

  Lemma variance' l : {y | y = variance l}.
  Proof.
    unfold variance.
    generalize (avg l); intro avgl. (* generalize;intro  =  let insertion *)

    (* Now I am basically replicating avg' *)
    case l as [|x xs]; unfold avg; simpl.
    - dismiss.
    - rewrite INR_S. generalize (sqr (x - avgl)) 1 xs.
      fix H0 3.
      intros. case xs0 as [|x' xs']; simpl.
      + rewrite !RIneq.Rplus_0_r. dismiss.
      + rewrite INR_S. rewrite <- !Rplus_assoc. apply H0.
  Qed.

End Stddev.


Extraction variance'.