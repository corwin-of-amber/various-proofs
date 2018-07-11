
Require Import Bool.


Section Dup.

  Variable A : Type.
  
  Hypothesis A_eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Open Scope list_scope.
  Open Scope bool_scope.

  Definition A_eqb x y := if A_eq_dec x y then true else false.
  
  Fixpoint elem a l :=
    match l with
    | nil => false
    | x :: xs => A_eqb x a || elem a xs
    end.
  
  Fixpoint nodup l :=
    match l with
    | nil => true
    | x::xs => negb (elem x xs) && nodup xs
    end.

  Definition set := A -> bool.

  Definition set_mem a (s:set) := (s a = true).
  Definition set_memb a (s:set) := s a.
  
  Notation "a '\in' S" := (set_mem a S) (at level 70).
  Notation "a '\inb' S" := (set_memb a S) (at level 70).
  
  Definition empty_set : set := fun _ => false.

  Definition singleton_set (a : A) : set := A_eqb a.

  Definition union s0 s1 : set := fun x => s0 x || s1 x.
  Definition intersection s0 s1 : set := fun x => s0 x && s1 x.

  (* obviously not correct *)
  Axiom set_eq_dec : forall (s0 s1:set), {s0 = s1} + {s0 <> s1}.
  Definition set_eqb s0 s1 := if set_eq_dec s0 s1 then true else false.

  Require Import FunctionalExtensionality.
  
  Definition disjoint s0 s1 := set_eqb (intersection s0 s1) empty_set.

  Lemma disjoint_comm s0 s1 : disjoint s0 s1 = disjoint s1 s0.
  Admitted.
  
  Lemma disjoint_over_union_r s0 s1 s2 :
    disjoint s0 (union s1 s2) = true <->
    andb (disjoint s0 s1) (disjoint s0 s2) = true.
  Admitted.
  
  Lemma disjoint_over_union_l s0 s1 s2 :
    disjoint (union s0 s1) s2 = true <->
    andb (disjoint s0 s2) (disjoint s1 s2) = true.
  Admitted.
  
  Lemma eq_singleton x y : x = y <-> x \in singleton_set y.
    unfold set_mem, singleton_set, A_eqb.
    split.
    - intro; subst. case (A_eq_dec y y); tauto.
    - case (A_eq_dec y x). symmetry; tauto.
      intros ? H1; inversion H1.
  Qed.

  Fixpoint elems (l:list A) : set.
    destruct l as [|x xs].
    - apply empty_set.
    - apply union.
      apply (singleton_set x).
      apply (elems xs).
  Defined.
  Print elems.

  Lemma in_singleton_disjoint x s : x \in s <-> disjoint (singleton_set x) s = false.
  Admitted.

  Lemma elem_in_elems a l : elem a l = true <-> a \in (elems l).
  Admitted.

  Lemma bool_ext b0 b1 : (b0 = true <-> b1 = true) -> b0 = b1.
  Admitted.

  Lemma bool_ext_neg b0 b1 : (b0 = true <-> b1 = false) -> b0 = negb b1.
  Admitted.

  Lemma neg_swap b0 b1 : b0 = negb b1 -> negb b0 = b1.
  Admitted.
  
  (* should be obvious? *)
(*  Lemma disj_elems s  : disjoint s (elems l) = true <->
  *)                       
  
  Definition nodup' l : {y | y = nodup l}.
    destruct l as [|x xs].
    - simpl. eexists; reflexivity.
    - simpl.
      rewrite (bool_ext _ _ (elem_in_elems _ _)).
      rewrite (bool_ext_neg _ _ (in_singleton_disjoint _ _)).
      rewrite negb_involutive.
      generalize (singleton_set x) xs;  fix nodup'' 2.
      destruct xs0 as [|x' xs'].
      + simpl. eexists; reflexivity.
      + simpl. rewrite (bool_ext _ _ (disjoint_over_union_r _ _ _)).
        rewrite <- andb_assoc.
        rewrite (bool_ext _ _ (elem_in_elems _ _)).
        rewrite (bool_ext_neg _ _ (in_singleton_disjoint _ _)).
        rewrite negb_involutive.
        rewrite (andb_assoc (disjoint s (elems xs'))).
        rewrite <- (bool_ext _ _ (disjoint_over_union_l _ _ _)).
        edestruct nodup'' as [r R].
        rewrite <- R.
        rewrite disjoint_comm.
        rewrite <- (neg_swap _ _ (bool_ext_neg _ _ (in_singleton_disjoint _ _))).
        fold (set_memb x' s).
        eexists; reflexivity.
  Defined.

End Dup.

Extraction nodup'.