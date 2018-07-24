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



Require Import Init.Wf.


Section ReflexiveTransitiveClosureMirror.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc' (s : D) :  D -> Prop :=
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

End ReflexiveTransitiveClosureMirror.



Require Coq.Program.Tactics.
Require Coq.Logic.JMeq.
    
 
Section CyclicRules.

  Variable D : Set.

  Definition destruction R (u v : D) (H : tc R u v) :
    u = v \/ exists u', R u u' /\ tc R u' v.
    destruct H; firstorder.
  Defined.

  Definition destruction' R (u v : D) (H : tc' R u v) :
    u = v \/ exists u', tc' R u u' /\ R u' v.
    destruct H; firstorder.
  Defined.

End CyclicRules.



Section SomeProofsWithCycles.


  Notation "(~ f )" := (fun x y => f x = y).
  
  Axiom sorry : forall {a}, a.


  Section Gen.
    
    Variable D : Set.

    Program Fixpoint no_escape' f (u v : D) (H: f u = u) (uv : tc' (~f) u v) : u = v :=
      match uv with
        tc'_refl _ _ => eq_refl u
      | @tc'_step _ _ _ _ _ H1 H2 =>
        let IH := no_escape' f H H1 in 
        _ IH
      end.
    
    Lemma no_escape f (u v : D) (H : f u = u) (uv : tc (~f) u v) : u = v.
      eapply no_escape'; try eassumption.
      apply tc_tc'. assumption.
    Qed.
    
    Program Fixpoint tc_cycle f (u v : D)
            (HC : tc (~f) (f u) u)
            (H : tc' (~f) u v) { struct H }
      : tc (~f) v u    :=
      match H with
        tc'_refl _ _ => tc_refl (~f) u
      | @tc'_step _ _ _ u' v0 H1 H2 =>
        let IH := tc_cycle f HC H1 in
        match destruction IH (* see below *) with
          or_introl eq => _
        | or_intror H3 => _
        end
      end.
  
    (* --- I thought we could avoid 'destruction', but the following
           fails to unify.
      match IH with
        tc_refl _ vz => @eq_ind _ _ (fun z => tc (~f) z u) HC v' H2
      | @tc_step _ _ _ u'' u H2 H3 => sorry
      end
     *)

    Lemma tc_cycle_fix f (u v : D)
          (HC : tc (~f) (f u) u)
          (H : tc' (~f) u v)
      : tc (~f) v u.
    Proof.
      revert v H.
      fix IH 2.
      destruct 1.
      - constructor.
      - destruct (destruction (IH u0 H))  (** see below **).
        + subst. assumption.
        + firstorder. subst. assumption.
    Qed.

    (* --- similarly, this does not fly:
      - destruct (IH u0 H).
        + subst. assumption.
        + subst. assumption.
     *)

    Lemma tc_frame_rule R R' (u : D)
          (mod : forall v v', tc R u v -> (R v v' <-> R' v v')):
      forall v, tc' R u v <-> tc' R' u v.
    Proof.
      split.
      - revert v. fix f 2.
        intros v uv. destruct uv.
        + constructor.
        + econstructor.
          * apply f. eassumption.
          * apply mod. apply tc'_tc. assumption.
            assumption.
      - revert v. fix f 2.
        intros v uv. destruct uv.
        + constructor.
        + econstructor.
          * apply f. eassumption.
          * apply mod. apply tc'_tc. apply f. assumption.
            assumption.
    Qed.

  End Gen.
      
  Section ReverseWithPointers.

    Variable V : Set.

    Axiom Veq_dec : forall u v : V, {u = v} + {u <> v}.
    
    Variable null : V.
    
    Record RevState : Set :=
      revState { i : V; j : V; n : V -> V }.

    Definition TR s1 s2 :=
      i s1 <> null /\
      i s2 = n s1 (i s1) /\ j s2 = i s1 /\
      forall u, n s2 u = if Veq_dec u (i s1) then j s1 else n s1 u.

    Definition ax s := n s null = null /\ forall u,
          tc (fun x y => n s x = y) u null.

    (* that's just for convenience *)
    Lemma Veq_eq u : exists H, Veq_dec u u = left H.
    Proof.    
      destruct (Veq_dec u u).
      - eexists. reflexivity.
      - contradiction n0. reflexivity.
    Qed.

    Lemma no_escape_null s v : ax s -> tc (~n s) null v -> v = null.
    Proof.
      intros. symmetry. eapply no_escape; try eassumption.
      firstorder.
    Qed.

    Lemma cycle_null s u : ax s -> tc (~n s) (n s u) u -> u = null.
    Proof.
      intros. eapply no_escape_null; try eassumption.
      apply tc_cycle_fix.
      - assumption.
      - apply tc_tc'. firstorder.
    Qed.
        
    (* not actually needed for the proof of `reverse` but nice to have *)
    Lemma acyclic s u v : ax s -> tc (~n s) u v -> tc (~n s) v u -> u = v.
    Proof.  (* no induction needed! *)
      intros ax0 uv vu.
      destruct uv as [|u0].
      - reflexivity.
      - enough (u0 = null).
        + rewrite H0 in *.
          symmetry; eapply no_escape_null; try eassumption.
          econstructor; eassumption.
        + eapply cycle_null; try eassumption.
          subst.
          eapply tc_transitive; try eassumption.
    Qed.

    
    Lemma frame_property_tcTR_n s0 s u : ax s0 -> tc' TR s0 s ->
                                         n s u = n s0 u \/
                                         tc (~n s0) (n s0 u) (i s).
    Proof.      
      assert (sq0 : forall s s0, ax s0 -> i s <> null ->
                            ~tc (~n s0) (n s0 (i s)) (i s)).
      {
        clear s0 s.
        intros s0 s ax0 i_not_null ?.
        contradiction i_not_null.
        eapply cycle_null; try eassumption.
      }

      assert (sq1 : forall s s' u, TR s s' -> n s' u = n s u \/ u = i s).
      {
        clear s0 s u.
        intros s s' u ss'. destruct ss' as [A0 [A1 [A2 A3]]].
        rewrite A3.
        destruct (Veq_dec u (i s)); firstorder.
      }

      assert (sq2 : forall s0 s s' u, n s (i s) = n s0 (i s) ->
                                 tc (~n s0) (n s0 u) (i s) ->
                                 TR s s' ->
                                 tc (~n s0) (n s0 u) (i s')).
      {
        intros.
        eapply tc_step'; try eassumption.
        rewrite <- H. symmetry. apply H1.
      }
      
      assert (sq3 : forall s0 s s' u, n s (i s) = n s0 (i s) ->
                                 u = i s ->
                                 TR s s' ->
                                 tc (~n s0) (n s0 u) (i s')).
      {
        clear s0 s u.
        intros s0 s s' u n_eq ui ss'.
        subst.
        destruct ss' as [A0 [A1 [A2 A3]]].
        rewrite <- n_eq, <- A1. constructor.
      }

      revert s u.
      fix f 4.
      intros s u ax0; destruct 1 as [|s s'].
      - left. reflexivity.
      - (* firstorder hangs *)
        assert (sq0' : n s (i s) = n s0 (i s)).
        { destruct (f s (i s) ax0 H); firstorder. }
        destruct (f s u ax0 H).
        + destruct (sq1 s s' u H0).
          * left. rewrite H2. assumption.
          * right. subst. eapply sq3; try eassumption. reflexivity.
        + destruct (sq1 s s' u H0).
          * right. eapply sq2; try eassumption.  (* now sq0' *)
          * right. subst. firstorder.
    Qed.
    
    Lemma backbone_property s0 s : ax s0 -> tc TR s0 s -> tc (~n s0) (i s0) (i s).
    Proof.
      intro ax0.
      (* Chlipala's method *)
      assert (forall s1, tc TR s0 s1 -> tc TR s1 s ->
                    tc (~n s0) (i s1) (i s)).
      {
        revert s. fix f 4.
        intros s s1 s0s1 s1s.
        destruct s1s as [|s1 s2 s].
        - constructor.
        - apply tc_step with (u:=i s2).
          + destruct H as [A1 [A2 [A3 A4]]]. rewrite A2.
            symmetry; edestruct frame_property_tcTR_n.
            * eassumption.
            * apply tc_tc'. eassumption.
            *  eassumption.
            * contradiction A1. eapply cycle_null; eassumption.
          + apply f; try assumption.
            eapply tc_step'; eassumption.
      }
      intro; apply H.
      - constructor.
      - assumption.
    Qed.

    Lemma frame_property_tcTR_n_i0 s0 s u : ax s0 -> tc' TR s0 s ->
                                            n s u = n s0 u \/
                                            tc (~n s0) (i s0) u.
    Proof.
      revert s u. fix f 4.
      intros s u ax0 s0s.
      destruct s0s as [|s s'].
      - left. reflexivity.
      - destruct H as [A0 [A1 [A2 A3]]]. rewrite A3.
        destruct (Veq_dec u (i s)).
        + right. subst. apply backbone_property; try assumption.
          apply tc'_tc. assumption.
        + apply f; assumption.
    Qed.

    
    Lemma frame_property_TR_tcn s0 s1 u : ax s0 -> TR s0 s1 ->
                            tc' (~n s0) (i s1) u <-> tc' (~n s1) (i s1) u.
    Proof.
      intros ax0 s0s1.
      eapply tc_frame_rule.
      intros v v' i1v. destruct s0s1 as [A1 [A2 [A3 A4]]].
      rewrite A4.
      destruct (Veq_dec v (i s0)).
      - contradiction A1.
        eapply cycle_null; try apply ax0. congruence.
      - tauto.
    Qed.
        
    (* CAN WE MAKE THIS A ONE LINER PLEASE *)
    Lemma negative_feedback s0 s1 : ax s0 -> TR s0 s1 ->
                                    ~tc (~n s1) (i s1) (i s0).
    Proof.
      intros ax0 s0s1 i1i0.
      assert (tc (~n s0) (i s1) (i s0)).
      {
        apply tc'_tc. apply frame_property_TR_tcn; try assumption.
        apply tc_tc'; assumption.
      }
      
      destruct s0s1 as [A0 [A1 A2]].
      contradiction A0.
      eapply cycle_null; try eassumption.
      congruence.
    Qed.
      

    (* Urm also not necessarily true?! *
    Lemma weak_preservation s0 s1 s2 : ax s0 -> TR s0 s1 -> ax s1 -> TR s1 s2 ->
                                       ax s2.
    Proof.
      intros ax0 s0s1 ax1 s1s2.
      split.
      - destruct s1s2 as [B1 [B2 [B3 B4]]].
        rewrite B4. destruct ax1. destruct (Veq_dec null (i s1)); congruence.
      - destruct ax1 as [C1 C2].
        intro u. specialize (C2 u). revert u C2. fix f 2.
        intros u unull1. destruct (destruction unull1) as [|[u' [uu' u'null1]]].
        + subst; constructor.
        + econstructor; try reflexivity.
          destruct s1s2 as [B1 [B2 [B3 B4]]]. rewrite B4.
          destruct (Veq_dec u (i s1)).
          * (* (i s1) is not reachable from (j s1) via (n s1) *)
            assert ( ~tc (~n s1) (j s1) (i s1) ).
            {
            } *)


    Definition ax_all s0 := forall s, tc TR s0 s -> ax s.
    
    (* From whiteboard proof *)
    Lemma left_branch0 s0 s1 s u v : ax_all s0 -> TR s0 s1 -> tc TR s1 s ->
                                     i s0 = u ->
                                     (* tc' (~n s0) u v *)
                                     n s0 u = v ->
                                     v <> null -> i s = null ->
                                     (* tc (~n s) v u *)
                                     n s v = u.
    Proof.
      revert u v.
      intros u v ax0 s0s1 s1s u_eq_i uv v_not_null i_null.
      destruct s1s as [|s1 s2 s s1s2].
      - contradiction v_not_null. destruct s0s1 as [A1 [A2 [A3 A4]]].
        congruence.
      - edestruct frame_property_tcTR_n_i0 with (s0:=s2) (s:=s).
        + apply ax0; repeat ( econstructor; try eassumption ).
        + apply tc_tc'. assumption.
        + rewrite H.
          subst.
          destruct s0s1 as [A1 [A2 [A3 A4]]].
          destruct s1s2 as [B1 [B2 [B3 B4]]].
          rewrite B4. rewrite A2. edestruct Veq_eq. rewrite H0.
          assumption.
        + contradiction negative_feedback with (s0:=s1) (s1:=s2).
          * apply ax0; repeat ( econstructor; try eassumption ).
          * destruct s0s1 as [A1 [A2 A3]]. congruence.
    Qed.

    Lemma sad s u v : ax s -> n s u = null -> tc (~n s) u v
                      -> v = u \/ v = null.
    Proof.
      destruct 3.
      - left; reflexivity.
      - right; eapply no_escape_null; try eassumption.
        congruence.
    Qed.
    
    Lemma left_branch s0 s v : ax_all s0 -> tc TR s0 s ->
                               tc (~n s0) (i s0) v ->
                               v <> null -> i s = null ->
                               tc (~n s) v (i s0).
    Proof.
      revert s0 s v. fix f 5.
      intros s0 s v ax0 s0s i0v v_not_null i_null.
      destruct s0s as [|s0 s1 s s0s1 s1s].
      - specialize (ax0 s) as axs. destruct axs; try constructor.
        rewrite i_null. apply H0.
      - (* -- REPAIR -- *)
        destruct (s1s) as [|s1 s2 s s1s2 s2s].
        {
          (* WHAT THE HELL *)
          clear f.
          edestruct sad; try eassumption.
          - apply ax0. constructor.
          - destruct s0s1 as [A1 [A2 [A3 A4]]]. congruence.
          - subst; constructor.
          - contradiction v_not_null.
        }
        
        inversion i0v. (* as [|i0 i1 v i0i1 i1v]. *)
        + constructor.
        + apply tc'_tc.
          econstructor.
          apply tc_tc'. apply f with (s0:=s1); try eassumption.
          * intros s' s1s'. apply ax0. econstructor; eassumption.
          * { apply tc'_tc. apply frame_property_TR_tcn with (s0:=s0).
              - apply ax0; constructor.
              - assumption.
              - destruct s0s1 as [A1 [A2 [A3 A4]]]. apply tc_tc'. congruence.
            }
          * { eapply left_branch0; try eassumption.
              - reflexivity.
              - symmetry; apply s0s1.
              - (* REPAIR was needed for this goal *) apply s1s2.
            }
    Qed.

    (* This is a very slight generalization of frame_property_TR_tcn *)
    Lemma frame_property_TR_tcn_ex s0 s1 u v : ax s0 -> TR s0 s1 ->
                                               tc (~n s0) (i s1) u ->
                                               tc' (~n s0) u v <-> tc' (~n s1) u v.
    Proof.
      intros ax0 s0s1 i1u.
      eapply tc_frame_rule.
      clear v.
      intros v v' uv.
      destruct s0s1 as [A1 [A2 [A3 A4]]].
      rewrite A4.
      destruct (Veq_dec v (i s0)).
      - contradiction A1. eapply cycle_null; try eassumption.
        eapply tc_transitive.
        + rewrite <- A2; eassumption.
        + subst; assumption.
      - tauto.
    Qed.

    Lemma right_branch s0 s1 s u v : ax_all s0 -> TR s0 s1 -> tc TR s1 s ->
                                     (forall u v, tc (~n s1) (i s1) u ->
                                             tc (~n s1) u v ->
                                             v <> null -> i s = null ->
                                             tc (~n s) v u) ->
                                     tc (~n s0) (n s0 (i s0)) u ->
                                     tc (~n s0) u v ->
                                     v <> null -> i s = null ->
                                     tc (~n s) v u.
    Proof.
      intros ax0 s0s1 s1s IH i0u uv v_not_null i_null.
      apply IH.
      - apply tc'_tc.
        eapply frame_property_TR_tcn with (s0:=s0).
        + apply ax0; constructor.
        + assumption.
        + destruct s0s1 as [? [? [? ?]]]. apply tc_tc'. congruence.
      - apply tc'_tc.
        eapply frame_property_TR_tcn_ex with (s0:=s0).
        + apply ax0; constructor.
        + assumption.
        + destruct s0s1 as [? [? [? ?]]]. congruence.
        + apply tc_tc'; assumption.
      - assumption.
      - assumption.
    Qed.


    Lemma whiteboard_proof s0 s u v : ax_all s0 -> tc TR s0 s ->
                                      tc (~n s0) (i s0) u ->
                                      tc (~n s0) u v ->
                                      v <> null -> i s = null ->
                                      tc (~n s) v u.
    Proof.
      revert s0 s u v. fix f 6.
      intros s0 s u v ax0 s0s i0u uv v_not_null i_null.
      destruct s0s as [|s0 s1 s s0s1 s1s].
      - specialize (ax0 s (tc_refl TR s)).
        contradiction v_not_null.
        eapply no_escape_null; try eassumption.
        eapply tc_transitive; try eassumption. congruence.
      - inversion i0u.
        + (* left branch *)
          eapply left_branch; try eassumption.
          * econstructor; eassumption.
          * congruence.
        + (* right branch *)
          eapply right_branch; try eassumption.
          * intros u1 v1 i1u1 u1v1 ? ?.
            { eapply f with (s0:=s1); try assumption.
              intros s' s1s'. apply ax0. econstructor; eassumption.
            }
          * congruence.
    Qed.
    
  (*
    Theorem middle_out s0 s1 s2 s : tc TR s0 s1 -> TR s1 s2 -> tc TR s2 s ->
                                    n s0 (i s1) = i s2 /\
                                    (i s2 <> null -> n s (i s2) = i s1).
     *)
    
  End ReverseWithPointers.
    
End SomeProofsWithCycles.
