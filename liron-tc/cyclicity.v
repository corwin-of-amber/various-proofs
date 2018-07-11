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

  (*
  Theorem tc_ind' : forall (P : D -> D -> Prop),
      (forall s, P s s) -> (forall s u t, P s u -> R u t -> P s t) ->
      forall s t, tc s t -> P s t.
  Proof.
    intros.
    induction H1.
    - apply H.
    - admit.
  Admitted. *)
    
End ReflexiveTransitiveClosureDef.

  
(* Notice: from this point on, tc is parameterized by D and R. *)
(* D is implicit. *)
Print Implicit tc.



Section TcProperties.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Definition wo w x y := x <> w /\ R x y.

  Hypothesis eq_dec : forall x y : D, {x = y} + {x <> y}.
  
  Theorem tc_simple_paths u v w : tc R u v -> 
                                  tc (wo w) u v \/ tc (wo v) u w.

  Proof.
    intros UV.
    induction UV.
    - left. constructor.
    - destruct (eq_dec s w).
      + right. subst. constructor.
      + destruct (eq_dec s t).
        * subst. left. constructor.
        * { destruct IHUV.
            - left. econstructor. firstorder. eassumption. assumption.
            - right. econstructor. firstorder. eassumption. assumption.
          }
  Qed.

  Lemma tc_frame_rule1 (A : Set) R' (u : D)
        (mod : forall v v', tc R u v -> (R v v' <-> R' v v')):
    forall v, tc R u v -> tc R' u v.
  Proof.
    (*split.*)
    - induction 1.
      + constructor.
      + econstructor.
        apply mod.
        * constructor.
        * eassumption.
        * apply IHtc. intros; apply mod. econstructor; eassumption.
  Qed.

  (* TODO seems like the following can be proved by two applications of
   * tc_frame_rule1 ? But that didn't work because it's not completely
   * symmetric :(  Check how to make it work anyway.  *)
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

End Reverse.


Section AcyclicDetetrimistic.

  Section SomewhatPainful.

    Variable V : Set.

    Axiom Veq_dec : forall u v : V, {u = v} + {u <> v}.
    
    Variable null : V.
    
    Record RevState : Set :=
      revState { i : V; j : V; n : V -> V }.

    Definition ax s := n s null = null /\ forall u, tc (fun x y => n s x = y) u null.


    Require Import Init.Wf.

    Section Tc'.

      Variable D : Set.
      Variable R : D -> D -> Prop.

      Inductive tc' (s : D) : D -> Prop :=
        tc'_refl : tc' s s
      | tc'_step : forall u t, tc' s u -> R u t -> tc' s t.

      Lemma tc'_tc : forall u v, tc' u v -> tc R u v.
      Proof.
        intros. induction H.
        - constructor.
        - eapply tc_step'; eassumption.
      Qed.

      Lemma tc'_transitive : forall u v w, tc' u v -> tc' v w -> tc' u w.
      Proof.
        intros.
        induction H0.
        - assumption.
        - econstructor. apply IHtc'. assumption. 
      Qed.
    
      Lemma tc_tc' : forall u v, tc R u v -> tc' u v.
      Proof.
        intros.
        induction H.
        - constructor.
        - eapply tc'_transitive.
          + eapply tc'_step.
            * constructor.
            * eassumption.
          + assumption.
      Qed.

      Theorem tc_ind' : forall (P : D -> D -> Prop),
          (forall s, P s s) -> (forall s u t, tc R s u -> P s u -> R u t -> P s t) ->
          forall s t, tc R s t -> P s t.
      Proof.
        intros.
        apply tc_tc' in H1.
        induction H1.
        - apply H.
        - eapply H0; try eassumption.  apply tc'_tc; assumption.
      Qed.

      Theorem tc_push : forall (P : D -> Prop),
          (forall u v, P u -> R u v -> P v) ->
          forall u v, P u -> tc R u v -> P v.
      Proof.
        intros.
        induction H1; firstorder.
      Qed.

    End Tc'.


    Axiom sorry: forall {A}, A.

    Definition destruction' R (u v : V) (H : tc' R u v) : u = v \/ exists u', tc' R u u' /\ R u' v.
      destruct H; firstorder.
    Defined.

    Definition destruction R (u v : V) (H : tc R u v) :
      u = v \/ exists u', R u u' /\ tc R u' v.
      destruct H; firstorder.
    Defined.
    
    Notation "(~ f )" := (fun x y => f x = y).
    
    Definition decay f (u v : V) (H : tc (~f) u v) : u = v \/ tc (~f) (f u) v.
      destruct H.
      - left; reflexivity.
      - right; rewrite H; assumption.
    Qed.
      
    Require Coq.Program.Tactics.
    Require Coq.Logic.JMeq.
    
    Program Fixpoint tc_cycle_fix f (u v : V)
             (HC : tc (fun x y => f x = y) (f u) u)
             (H : tc' (fun x y => f x = y) u v) { struct H }
           : tc (fun x y => f x = y) v u    :=
      match H with
        tc'_refl _ _ => tc_refl _ _
      | @tc'_step _ _ _ u' v' H1 H2 =>
        let IH := tc_cycle_fix f HC H1 in
        match destruction IH with
          or_introl eq => _
        | or_intror H3 => _
        end
        (*
        match IH with
          tc_refl _ vz => @eq_ind _ _ (fun z => tc (~f) z u) HC v' H2
        | @tc_step _ _ _ u'' u H2 H3 => sorry
        end*)
      end.

      (*
      match destruction' H with
        or_introl eq => @eq_ind _ u (fun y => tc _ y u) (tc_refl _ _) v eq
      | or_intror (ex_intro _ u' (conj H1 H2)) =>
        let IH := tc_cycle_fix f HC H1 in
        (match decay f IH with
           or_introl eq => sorry
         | or_intror H3 => sorry
         end)
      end.*)
      
    
    Lemma tc_cycle f : forall u v : V, tc (fun x y => f x = y) (f u) u ->
                                  tc (fun x y => f x = y) u v ->
                                  tc (fun x y => f x = y) v u.
    Proof.
      intros.
      (* apply tc_tc' in H0. *)
      induction H0 using tc_ind'.
      - constructor.
      - pose (IHtc H) as HH.
        destruct HH.
        + subst. assumption.
        + subst. assumption.
      (* I believe this one is well-founded, but Coq does not seem to
         figure it out. *
      fix IHuv 3.
      intros u v fuu uv.
      destruct uv.
      - constructor.
      - apply IHuv.
        + assumption.
        + apply tc'_tc in uv.
          destruct uv.
          * econstructor. constructor. assumption.
          * econstructor. apply tc_tc'. eapply tc_step.
            eassumption. eassumption. assumption. *)
    Qed.

    Lemma null_end s : ax s ->
                       forall u, tc (fun x y => n s x = y) null u -> u = null.
    Proof.
      intros [Ax1 Ax2] u nullu.
      induction nullu using tc_ind'.
      - reflexivity.
      - firstorder. subst. firstorder.
    Qed.
      
    Lemma acyclic s : ax s -> forall u v, tc (fun x y => n s x = y) u v ->
                                    tc (fun x y => n s x = y) v u ->
                                    u = v.
    Proof.
      intros Ax u v uv vu.
      destruct uv.
      - reflexivity.
      - enough (s0 = null).
        + subst. symmetry. eapply null_end; try eassumption.
          econstructor; [reflexivity | assumption].
        + eapply null_end; try eassumption.
          eapply tc_cycle.
          * subst. eapply tc_transitive; eassumption.
          * firstorder.
    Qed.

    
    (* OUCH! This is not a true statement.
       Lemma ax_inv s1 s2 : ax s1 -> TR s1 s2 -> ax s2.
     *)
    
    Lemma no_escape' f : forall u v : V, tc (fun x y => f x = y) v u ->
                                    f v = v -> u = v /\ f u = u.
    Proof.
      intros u v Htc.
      induction Htc.
      - firstorder.
      - rewrite H. intro X; rewrite <- X. apply IHHtc.
        subst. f_equal. assumption.
    Qed.

    Lemma no_escape f : forall u v : V, tc (fun x y => f x = y) v u ->
                                   f v = v -> u = v.
    Proof.
      firstorder using no_escape'.
    Qed.

    Lemma no_escape_rev f : forall u v : V, tc (fun x y => f y = x) u v ->
                                       f v = v -> u = v.
    Proof.
      induction 1.
      - reflexivity.
      - subst. intro; subst. rewrite IHtc; assumption.
    Qed.
      
    Lemma acyclic1 s u : ax s -> n s u = u -> u = null.
    Proof.
      intros; symmetry; eapply no_escape.
      apply H. assumption.
    Qed.

    Lemma no_escape'2 f : forall u v w : V, tc (fun x y => f y = x) u v ->
                                       f v = w -> f w = v ->
                                       (u = v \/ u = w) /\ (f u = v \/ f u = w).
    Proof.
      intros u v w. induction 1.
      - firstorder.
      - intros. split.
        + rewrite <- H. apply IHtc; assumption.
        + (* stuff with equalities. Nelson-Oppen would have nailed this *)
          destruct IHtc as [[A0|A0] [A1|A1]]; try (reflexivity || assumption).
          * subst. left; assumption.
          * subst. left; assumption.
          * subst. repeat rewrite A1. right; reflexivity.
          * subst. repeat rewrite A1. right; reflexivity.
    Qed.

    Lemma no_escape2_rev f : forall u v w : V, tc (fun x y => f y = x) u v ->
                                          f v = w -> f w = v ->
                                          (u = v \/ u = w).
    Proof.
      intros u v w. induction 1.
      - firstorder.
      - firstorder.
        subst. right; reflexivity.
        subst. left; assumption.
    Qed.

    Lemma no_escape2 s : forall u v w, tc (fun x y => n s x = y) v u ->
                                  n s v = w -> n s w = v ->
                                  (u = v \/ u = w).
    Proof.
      intros. eapply no_escape2_rev; try eassumption.
      apply rev_all_bwd. apply H.
    Qed.
    
    Lemma acyclic2 s u : ax s -> n s (n s u) = u -> u = null.
    Proof.
      intros [A0 A1] H.
      ecase no_escape2. (* with (s:=s) (v:=u) (u:=null). *)
     
      - apply A1.
      - reflexivity.
      - eassumption.
      - firstorder.
      - intro. rewrite <- H. rewrite <- H0. assumption.
    Qed.

    Lemma no_escape_gen s : forall u v w, tc (fun x y => n s y = x) u v ->
                                     tc (fun x y => n s x = y) v w ->
                                     tc (fun x y => n s x = y) w v ->
                                     tc (fun x y => n s x = y) w u.
    Proof.
      induction 1.
      - firstorder.
      - intros.
        eapply tc_step'. apply IHtc; assumption.
        assumption.
    Qed.

    Lemma no_escape_n s : forall u v w, tc (fun x y => n s y = x) u v ->
                                   tc (fun x y => n s x = y) v w ->
                                   tc (fun x y => n s x = y) w v ->
                                   v <> w ->
                                   tc (fun x y => n s x = y) u w.
    Proof.
      induction 1 as [|u' u v].
      - firstorder.
      - intros.
        destruct IHtc; try assumption.
        destruct H2.
        contradiction.
        replace u' with u.
        eapply tc_transitive; eassumption.
        rewrite <- H, H2. reflexivity.
        replace u' with u. assumption.
        rewrite <- H, H4. reflexivity.
    Qed.
    
    Lemma acyclicn s : ax s -> forall u, tc (fun x y => n s x = y) (n s u) u ->
                                   u = null.
    Proof.
      intros.
      destruct (Veq_dec u null). assumption.
      
      eapply no_escape.
      eapply no_escape_n.
      eapply rev_all_bwd.
      
      apply H.
      eassumption.
      econstructor. reflexivity. constructor.
      firstorder using acyclic1.
      apply H.
    Qed.
    
      
    Lemma acyclic s : ax s -> forall u v, tc (fun x y => n s x = y) u v ->
                                    tc (fun x y => n s x = y) v u ->
                                    u = v.
    Proof.
      intros.
      destruct (Veq_dec u v). assumption.

      assert (u = null).

      eapply no_escape.
      eapply no_escape_n.
      eapply rev_all_bwd.
      apply H.
      eassumption.
      assumption.
      firstorder. firstorder.

      subst. symmetry. eapply no_escape. apply H0.
      apply H.
    Qed.      
    
  End SomewhatPainful.
 
End ReverseWithPointers.
