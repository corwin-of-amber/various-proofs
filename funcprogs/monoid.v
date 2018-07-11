
Require Import List.
Require Import Bool.

Open Scope list_scope.

(* See http://learnyouahaskell.com/functors-applicative-functors-and-monoids#monoids *)


Section AnyAll.

  Variable A : Set.
  Variable p : A -> bool.

  Fixpoint foldl {A B} a0 f (l : list A) : B :=
    match l with
    | nil => a0
    | x::xs => foldl (f a0 x) f xs
    end.
  
  Definition any := foldl false (fun b x => b || p x).

  Lemma any' l : {y | y = any l}.
    unfold any.
    generalize false l; fix aux 2.
    destruct l0 as [|x xs].
    - simpl. eexists; reflexivity.
    - simpl. case b.
      + Search (true || _). rewrite orb_true_l.
        replace (foldl _ _ _) with true.
        * eexists; reflexivity.
        * induction xs. simpl. reflexivity.
          simpl. apply IHxs.
      + edestruct aux as [r R].
        rewrite <- R.
        eexists; reflexivity.
  Defined.

  (* 'all' is actually boring; just negb any (negb..) *)
End AnyAll.

Extraction any'.

Section Compare.

  Inductive Ordering := LT | EQ | GT.

  Definition mappend a b :=
    match a with
    | LT => LT
    | EQ => b
    | GT => GT
    end.

  Variable A : Set.
  Variable cmp : A -> A -> Ordering.

  Fixpoint zip {A B} (l1 : list A) (l2 : list B) :=
    match (l1, l2) with
    | (x1::xs1, x2::xs2) => (x1,x2) :: zip xs1 xs2
    | _ => nil
    end.

  Definition uncurry2 {A B C} (f : A -> B -> C) xy := f (fst xy) (snd xy).
  
  Definition lex_cmp l1 l2 := foldl EQ mappend (map (uncurry2 cmp) (zip l1 l2)).
  

  Lemma lex_cmp' l1 l2 : {y | y = lex_cmp l1 l2}.
    unfold lex_cmp.
    generalize EQ l1 l2; fix aux 2.
    destruct l0; intro.
    - simpl. eexists; reflexivity.
    - destruct l3.
      + simpl. eexists; reflexivity.
      + simpl. unfold uncurry2; simpl.
        case o.
        * replace (foldl _ _ _) with LT.
          eexists; reflexivity.
          generalize (zip l0 l3). induction l.
          unfold mappend; simpl; reflexivity.
          apply IHl.
        * unfold mappend at 1; simpl.
          apply aux.
        * replace (foldl _ _ _) with GT.
          eexists; reflexivity.
          generalize (zip l0 l3). induction l.
          unfold mappend; simpl; reflexivity.
          apply IHl.
  Defined.

End Compare.


Extraction lex_cmp'.