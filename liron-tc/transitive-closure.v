Set Implicit Arguments.


Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, R s u -> tc u t -> tc s t.

  Theorem tc_transitive : forall s u t, tc s u -> tc u t -> tc s t.
  Proof.
    intros.
    induction H.
    + assumption.
    + eapply tc_step. apply H. apply IHtc. assumption.
  Qed.

  Corollary tc_step' : forall s u t, tc s u -> R u t -> tc s t.
  Proof.
    intros; eapply tc_transitive.
    - apply H.
    - econstructor.
      + apply H0.
      + constructor.
  Qed.
    
End ReflexiveTransitiveClosureDef.


(* Notice: from this point on, tc is parameterized by D and R. *)
(* D is implicit. *)
Print Implicit tc.



Section TcProperties.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Lemma tc_frame_rule R' (u : D)
        (mod : forall v v', tc R u v -> (R v v' <-> R' v v')):
    forall v, tc R u v <-> tc R' u v.
  Proof.
    split.
    - induction 1.
      + constructor.
      + econstructor.
        apply mod.
        * constructor.
        * eassumption.
        * apply IHtc. intros; apply mod. econstructor; eassumption.
    - induction 1.
      + constructor.
      + econstructor.
        apply mod.
        * constructor.
        * eassumption.
        * apply IHtc. intros; apply mod. econstructor; try eassumption.
          apply mod. constructor. eassumption.
  Qed.

End TcProperties.



Section Reverse.

  Variable D : Set.

  Section Simple.
    
    Variable R : D -> D -> Prop.

    Definition inv s t := R t s.
  
    Let R' := inv.

    Theorem rev_all_fwd : forall s t, tc R s t -> tc R' t s.
    Proof.
      intros. induction H.
      - constructor.
      - eapply tc_step'.
        eassumption. assumption.
    Qed.

  End Simple.

  Section AnotherSimple.
    
    Variable R : D -> D -> Prop.

    Let R' := inv R.
  
    Theorem rev_all_bwd : forall s t, tc R' s t -> tc R t s.
    Proof.
      intros.
      apply rev_all_fwd.
      apply H.
    Qed.

    Theorem rev_all : forall s t, tc R s t <-> tc R' t s.
    Proof.
      split.
      - apply rev_all_fwd.
      - apply rev_all_bwd.
    Qed.
        
  End AnotherSimple.

  Section SlightlyLessSimple.

    Variable s : D.
    Variable R : D -> D -> Prop.
    
    Inductive subinv (p : D -> Prop) : D -> D -> Prop :=
      inv_true :   forall u v, p v -> R u v -> subinv p v u
    | id_false :   forall u v, ~p v -> R u v -> subinv p u v.

    Definition rev_source := subinv (tc R s).

    Let R' := rev_source.
    
    Theorem rev_some0 : forall u t, tc R s u -> tc R u t -> tc R' t u.
    Proof.
      intros.
      induction H0.
      - constructor.
      - eapply tc_step'.
        + apply IHtc. eapply tc_step'.
          eassumption. assumption.
        + apply inv_true.
          eapply tc_step'.
          eassumption. assumption.
          assumption.
    Qed.

    Theorem rev_some : forall t, tc R s t -> tc R' t s.
    Proof.
      intros; apply rev_some0.
      - constructor.
      - assumption.
    Qed.

  End SlightlyLessSimple.

End Reverse.


Section ReverseWithPointers.

  Notation "(~ f )" := (fun x y => f x = y).

  Section SomewhatPainful.

    Variable V : Set.

    Axiom Veq_dec : forall u v : V, {u = v} + {u <> v}.
    
    Variable null : V.
    
    Record RevState : Set :=
      revState { i : V; j : V; n : V -> V }.

    Definition TR s1 s2 :=
      i s1 <> null /\
      i s2 = n s1 (i s1) /\ j s2 = i s1 /\
      forall u, n s2 u = if Veq_dec u (i s1) then j s1 else n s1 u.

    Definition ax s := n s null = null /\ forall u, tc (fun x y => n s x = y) u null.

    (* OUCH! This is not a true statement.
       Lemma ax_inv s1 s2 : ax s1 -> TR s1 s2 -> ax s2.
     *)

    Lemma no_escape_rev f : forall u v : V, tc (fun x y => f y = x) u v ->
                                       f v = v -> u = v.
    Proof.
      induction 1.
      - reflexivity.
      - subst. intro; subst. rewrite IHtc; assumption.
    Qed.

    Lemma no_escape s : forall u v, tc (~n s) v u ->
                               n s v = v -> u = v.
    Proof.
      intros. eapply no_escape_rev; try eassumption.
      apply rev_all. apply H.
    Qed.

    Lemma acyclic1 s u : ax s -> n s u = u -> u = null.
    Proof.
      intros; symmetry; eapply no_escape.
      apply H. assumption.
    Qed.

    Lemma acyclic s : ax s -> forall u v, tc (~n s) u v ->
                                    tc (~n s) v u ->
                                    u = v.
      (* Redacted -- see cyclicity.v *)
    Admitted.
    
    Lemma liron's_subgoal s1 s2 s3 : ax s1 -> TR s1 s2 -> 
              (forall u v, tc (~n s1) (i s1) u ->
                      tc (~n s1) u v ->
                      tc (~n s1) (n s1 v) (i s3) ->
                      tc (~n s3) v u) ->
              (forall u v, tc (~n s2) (i s2) u ->
                      tc (~n s2) u v ->
                      tc (~n s2) (n s2 v) (i s3) ->
                      tc (~n s3) v u).
    Proof.
      intros ax_s1 H.
      
      (* Auxiliary lemmas *)
      enough (lem0 : forall u, tc (~n s1) (i s2) u ->
                          n s2 u = n s1 u).
     
      enough (lem : forall u v, tc (~n s1) (i s2) u ->
                           tc (~n s2) u v ->
                           tc (~n s1) u v).
      
      intros IH u v H1 H2 H3.
      
      apply IH.
      - econstructor. symmetry; apply H.
        apply lem.
        * constructor.
        * assumption.
      - apply lem.
        * apply lem.
          constructor. assumption.
        * assumption.
      - apply lem.
        * eapply tc_transitive.
          apply lem. constructor. eassumption.
          eapply tc_transitive.
          apply lem. apply lem. constructor. assumption.
          apply H2.
          econstructor. reflexivity. constructor.
        * rewrite <- lem0. assumption.
          apply lem. constructor.
          eapply tc_transitive; eassumption.


      (* -----   Proofs of auxiliary lemmas   ----- *)
          
      - (* lemma lem *)
      intros; simpl.
      eapply tc_frame_rule. Focus 2.
      apply H1.
      intros; simpl.
      rewrite lem0.
      + tauto.
      + eapply tc_transitive; eassumption.

      - (* lemma lem0 *)
      intros; simpl. destruct H as [A0 [A1 [A2 A3]]]. rewrite A3.
      (* - Now I want to claim that u cannot be = i s1 *)
      destruct (Veq_dec u (i s1)); try tauto.
      contradiction A0.
      eapply acyclic1. eassumption.
      rewrite <- A1.
      eapply acyclic; subst. eassumption.
      * eassumption.
      * econstructor. symmetry; apply A1. constructor.
    Qed.
    
        
    Theorem trace_property s1 s2 :
      (forall s', tc TR s1 s' -> ax s') ->
      tc TR s1 s2 ->
      forall u v, tc (~n s1) (i s1) u ->
             tc (~n s1) u v ->
             tc (~n s1) (n s1 v) (i s2) ->
             tc (~n s2) v u.
    Proof.
      induction 2 as [|s1 s1' s2].
      - admit.  (* transitivity + acyclicity -- should be trivial *)
      - inversion 1 as [|i1 u'].
        + intros; eapply tc_step'.
          * apply IHtc.
            (* - *) intros; apply H. econstructor; eassumption || constructor.
            (* - *) apply tc_refl.
            (* - *) admit.  (* OOPS?! *)
            (* - *) admit.  (* OOPS?! *)
          * admit.
        + intros; apply IHtc.
          * intros; apply H. econstructor; eassumption || constructor.
          * (* should follow from H4, H5, and "frame rule" *) admit.
          * admit.
          * admit.
    Admitted.


    Lemma admit0: forall s (u v : V),
        tc (~n s) (i s) u ->
        tc (~n s) u v ->
        tc (~n s) (n s v) (i s) ->
        tc (~n s) v u.
    Proof.
      intros.
      eapply tc_transitive; try eassumption.
      econstructor; eassumption || reflexivity.
    Qed.
    
    Lemma admit1: forall s1 s1' u v,
        ax s1 -> ax s1' -> TR s1 s1' ->
        tc (~n s1) (i s1) u ->
        tc (~n s1) (i s1) v ->
        tc (~n s1') (i s1') v.
    Admitted.
    
    Lemma admit2: forall s1 s1' s2 u v,
        ax s1 -> ax s1' -> TR s1 s1' -> tc TR s1' s2 ->
        tc (fun x y : V => n s1 x = y) (i s1) u ->
        tc (fun x y : V => n s1 x = y) (i s1) v ->
        tc (fun x y : V => n s1 x = y) (n s1 v) (i s2) ->
        tc (fun x y : V => n s1' x = y) (n s1' v) (i s2).
    Admitted.

    Lemma admit3: forall s1 s1' s2,
        ax s1 -> ax s1' -> TR s1 s1' -> tc TR s1' s2 ->
        n s2 (i s1') = i s1.
    Admitted.
    
  End SomewhatPainful.
 
End ReverseWithPointers.
