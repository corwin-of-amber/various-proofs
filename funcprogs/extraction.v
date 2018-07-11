(* This is currently a scratchpad, some imports are needed for it to actually compile *)


Section Sum.
(*
  Lemma proj1_sig_fix : forall A, proj1_sig (fix f) = 

                          (a b : A) (e : a = b) (f : A -> A) (s : {y | y = f a}),
   *)

  
  (* This is where it becomes dicey *)
  Lemma sum''0: {r | forall l: list nat, proj1_sig (sum'' l) = r l}.

    (*eexists.*)
    unfold sum''.

    Lemma buh : forall A B (l: list A) (f : list A -> B)
                  (s0 : {y | y = f nil}) (s1 : forall x xs, {y | y = f (x :: xs)}),
          proj1_sig
            match l return {y0 | y0 = f l} with
            | nil => s0
            | x :: xs => s1 x xs
            end
          = 
          match l with
          | nil => proj1_sig s0
          | x :: xs => proj1_sig (s1 x xs)
          end.
          
        destruct l; reflexivity.
    Qed.

    (*
    lazymatch goal with
      | [ |- context [match _ with nil => _ | x :: xs => ?a x xs end] ] => pose (a x xs)
    end.*)

    eexists; intros.
    rewrite buh.
    simpl.

    Lemma beh : forall x xs (s0 : forall x0, {y | y = x0 + sum nil})
        (* (s1 : forall x0 x xs, {y | y = x0 + sum (x :: xs)}) *),
      proj1_sig
        ((fix H0 (x0 : nat) (xs0 : list nat) {struct xs0} :
            {y : nat | y = x0 + sum xs0} :=
            match xs0 as l0 return {y : nat | y = x0 + sum l0} with
            | nil =>
              s0 x0
              (*exist (fun y : nat => x0 + 0 = y) x0
                    (eq_ind x0 (fun n : nat => n = x0) eq_refl 
                            (x0 + 0) (plus_n_O x0))*)
            | x' :: xs' =>
              (*s1 x0 x' xs'*)
              eq_rec_r (fun n : nat => {y : nat | y = n}) 
                       (H0 (x0 + x') xs') (Nat.add_assoc x0 x' (sum xs'))
            end) x xs) =
      ((fix H0 (x0 : nat) (xs0 : list nat) {struct xs0} : nat :=
          match xs0 with
          | nil => proj1_sig (s0 x0)(*x0*)
          | x' :: xs' => H0 (x0 + x') xs'
          end) x xs).
      intros. generalize x.
      induction xs.
      - reflexivity.
      - intro. rewrite <- IHxs.
        unfold eq_rec_r, eq_rec, eq_rect.


      Lemma boh : forall {A} {a b : A} (e : a = b) (f : A -> A) (s : {y | y = f a}),
          proj1_sig
            match e in (_ = y) return {y0 | y0 = f y} with
            | eq_refl => s
            end
          =
          match e with
          | eq_refl => proj1_sig s
          end.
        destruct e.
        reflexivity.
      Qed.

      Lemma boh' : forall {A B} {a b : A} (e : a = b) (x : B), match e with eq_refl => x end = x.
        destruct e; reflexivity.
      Qed.
        
      (* destruct (eq_sym (Nat.add_assoc x0 a (sum xs))). *)
      rewrite (boh _ (fun y => y)), boh'.
      reflexivity.
    Qed.

    (* eexists. *)
    
    
    (* Tried this and it does not work *)
    (*
    setoid_rewrite (beh _ _ (fun x0 => exist (fun y : nat => y = x0 + 0) x0
                                       (eq_ind x0 (fun n : nat => x0 = n) eq_refl 
                                               (x0 + 0) (plus_n_O x0)))).
     *)

    (* this would work (credit Clement) *)
    lazymatch goal with
    | [  |- _ = ?r _ ] =>
      evar (fNil: nat);
        evar (fCons: nat -> list nat -> nat);
        unify r (fun l: list nat => match l with | nil => fNil | h :: t => fCons h t end)
    end.
    
    destruct l.
    - reflexivity.
    -
        rewrite (beh _ _ (fun x0 => exist (fun y : nat => y = x0 + 0) x0
                                       (eq_ind x0 (fun n : nat => x0 = n) eq_refl 
                                               (x0 + 0) (plus_n_O x0)))).
      simpl.
      reflexivity.
  Defined.


  Compute (proj1_sig sum''0).
  
  Print sum''0.

    lazymatch goal with
    | [ |- context [proj1_sig (?a x xs)] ] => pose (?a x xs)
    end.
    
    Lemma beh : forall A f g, proj1_sig (fix f (x:A) (xs:list A) {struct xs} := g f x xs) = (fix f x xs := proj1_sig g (fun x xs => proj1_sig (f x xs)) x xs).
      
    case l as [|x xs].
    - eexists. simpl. reflexivity.
    - eexists. simpl.
      generalize x. induction xs.

      + simpl. reflexivity.
      + 

      eapply proj1_sig.
    apply sum''.
    Unshelve.
    Qed.


End Sum.


Section Average.

   
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
      
      Lemma buh : forall {A} {a b : A} (e : a = b) (f : A -> A) (s : {y | y = f a}),
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

      Fail rewrite <- buh. (* second-order unification issue *)

      rewrite <- (buh e (fun y => (x + sum xs) / y)).
      reflexivity.
      
  Admitted.
      (*
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


Definition a := fun x:nat => ltac:(exact x).

Require Import Utf8.

Ltac ret_and_left f :=
  let tac := ret_and_left in
  let T := type of f in
  lazymatch eval hnf in T with
  | ?a /\ ?b => exact (proj1 f)
  | ?T' → _
=> let ret := constr:(fun x' : T' => let fx := f x' in ltac:(tac fx)) in let ret' := (eval cbv zeta in ret) in
exact ret'
  end.

Print avg'.

Ltac ret_sig_v t :=
  let tac := ret_sig_v in
  lazymatch t with
  | (match _ with O => ?a | S _ => _ end) => exact (match _ with O => a | S _ => a end)
  | _ =>
    lazymatch (eval cbv delta in t) with
    | (fun x : ?T' => ?a) => let ret' := tac a in let ret := constr:(fun x : T' => a) in exact ret
    | ?T' → _
      => let ret := constr:(fun x' : T' => let fx := t x' in fx) in
        let ret' := (eval cbv zeta in ret) in
        exact ret'
    | exist _ ?v _ => exact v
    | ?a => exact a
    end
  end.

Definition arti n : {y | y = (n + 10)%nat}.
  destruct n.
  - rewrite plus_O_n. dismiss.
  - rewrite plus_Snm_nSm. dismiss.
Defined.


Print arti.

Definition xx := (ltac:(ret_sig_v arti)).
Print xx.

Goal match 5%nat with O => 0 | S _ => 1 end = 1.
  match goal with
  | [  |- context [match _ with O => _ | S _ => ?a end] ] => pose a
  end.
Admitted.

Goal ∀ A B : Prop, (A → A → A ∧ B) → True.
intros A B H.
pose ltac:(ret_and_left H).
Admitted.
