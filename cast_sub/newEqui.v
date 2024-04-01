
(* Inductive Tyeqi (R: typ -> typ -> Prop) : typ -> typ -> Prop :=
| Tyeqi_refl: forall t, Tyeqi R t t
| Tyeqi_mu_l: forall t, Tyeqi R (t_mu t) (unfold_mu t)
| Tyeqi_mu_r: forall t, Tyeqi R (unfold_mu t) (t_mu t)
| Tyeqi_trans: forall t1 t2 t3, 
    Tyeqi R t1 t2 -> Tyeqi R t2 t3 -> Tyeqi R t1 t3
| Tyeqi_arrow: forall t1 t2 t1' t2',
    R t1 t1' -> 
    R t2 t2' -> 
    Tyeqi R (t_arrow t1 t2) (t_arrow t1' t2')
.

#[export]
Hint Constructors Tyeqi : core.

CoInductive Tyeq : typ -> typ -> Prop :=
| ty_introw: forall (R: typ -> typ -> Prop),
    (forall t, R t t) ->
    (forall t1 t2, R t1 t2 -> R t2 t1) ->
    (forall t1 t2 t3, R t1 t2 -> R t2 t3 -> R t1 t3) ->
    (forall t1 t2, R t1 t2 -> Tyeq t1 t2) ->
    forall t1 t2,
      Tyeqi R t1 t2 ->
      Tyeq t1 t2. *)

      Lemma Tyeqi_symm: forall (R: typ -> typ -> Prop) t1 t2, 
      (forall t1' t2', R t1' t2' -> R t2' t1') ->
      Tyeqi R t1 t2 -> Tyeqi R t2 t1.
    Proof with auto.
      intros.
      induction H0...
      - apply Tyeqi_trans with (t2:=t2)...
      (* - apply Tyeqi_arrow.  *)
    Qed.
    
    
    
    Lemma Tyeq_symm': forall t1 t2, Tyeq t1 t2 -> Tyeq t2 t1.
    Proof with auto.
      intros.
      inversion H;subst.
      apply ty_introw with (R:=R)...
      apply Tyeqi_symm...
    Qed.
    
    
    
    Inductive WHNF_eqWi (R: mode -> typ -> typ -> Prop): typ -> typ -> Prop :=
    | wh_done: forall t1 t2, Tyeq t1 t2 -> WHNF_eqWi R t1 t2
    | wh_arrow: forall m t1 t2 t1' t2',
        R m t1 t1' -> (* coinductive WHNF_eqP *)
        R m t2 t2' ->
        WHNF_eqWi R (t_arrow t1 t2) (t_arrow t1' t2')
    | wh_trans: forall t1 t2 t3, 
        WHNF_eqWi R t1 t2 -> 
        WHNF_eqWi R t2 t3 -> 
        (* R m t1 t2 ->
        R m t2 t3 -> *)
        (* This is different?
          unlike "Subtyping, Declaratively", here we are proving soundness
          to a fully coindutive relation, which does not restrict the
          trans constructor to be inductive, so we also need the
          help of WHNF_eqP (which is inlined in the definition of WHNF_eqW)
          for the transitivity case
        *)
        WHNF_eqWi R t1 t3
    (* | wh_symm: forall t1 t2, 
        R t1 t2 -> 
        WHNF_eqWi R t2 t1 *)
    .
    
    #[export]
    Hint Constructors WHNF_eqWi : core.
    
    CoInductive WHNF_eqW : typ -> typ -> Prop :=
    | wh_introw: forall (R: mode -> typ -> typ -> Prop),
        (forall m t1 t2, R (flip m) t1 t2 -> R m t2 t1) ->
        (forall m t1 t2, R m t1 t2 -> 
          (exists A,
              (forall t1 t2, In (t1, t2) 
                (match m with m_pos => A | m_neg => reverse_A A end)
                (* A *)
                  -> WHNF_eqW t1 t2) /\
              eqe A t1 t2)) ->
        forall t1 t2,
          WHNF_eqWi R t1 t2 ->
          WHNF_eqW t1 t2.
    
    Lemma WHNF_eqWi_symm: forall (R: mode -> typ -> typ -> Prop) t1 t2, 
      (forall m t1' t2', R (flip m) t1' t2' -> R m t2' t1') ->
      WHNF_eqWi R t1 t2 -> WHNF_eqWi R t2 t1.
    Proof with auto.
      intros.
      induction H0.
      - apply wh_done. apply Tyeq_symm'...
      - apply wh_arrow with (m:=flip m); apply H; destruct m; auto.
      - apply wh_trans with (t2:=t2)...
       (* (m:=flip m); apply H; destruct m; auto. *)
    Qed.
    
    
    Lemma WHNF_eqW_symm: forall t1 t2, WHNF_eqW t1 t2 -> WHNF_eqW t2 t1.
    Proof.
      cofix IH.
      intros.
      inversion H;subst.
      apply wh_introw with (R:=R).
      +
        apply H0.
      + intros.
        destruct (H1 _ _ _ H3) as [A' [? ?]].
        exists A'. split. exact H4. exact H5.
      +
        apply WHNF_eqWi_symm with (R:=R);try assumption.
    Qed.
    
    #[export]
    Hint Constructors eqe : core.
    
    Inductive eq_env: list (typ * typ) -> list (typ * typ) -> Prop :=
    | eq_env_nil: eq_env nil nil
    | eq_env_cons_same: forall t1 t2 E1 E2,
        eq_env E1 E2 ->
        eq_env ((t1,t2)::E1) ((t1,t2)::E2)
    | eq_env_cons_rev: forall t1 t2 E1 E2,
        eq_env E1 E2 ->
        eq_env ((t1,t2)::E1) ((t2,t1)::E2)
    .
    
    Lemma eq_env_eqe_in: forall E1 E2 t1 t2,
      eq_env E1 E2 ->
      In (t1,t2) E1 ->
      In (t1,t2) E2 \/ In (t2,t1) E2.
    Proof with auto.
      intros. 
      induction H.
      - inversion H0.
      - inversion H0;subst...
        + inv H1. left. left...
        + forwards [?|?]: IHeq_env H1.
          { left. right... }
          { right. right... }
      - inversion H0;subst...
        + inv H1. right. left...
        + forwards [?|?]: IHeq_env H1.
          { left. right... }
          { right. right... }
    Qed.
    
    
    
    Lemma eq_env_refl: forall E, eq_env E E.
    Proof with auto.
      intros.
      induction E...
      constructor...
      destruct a. constructor...
    Qed.
    
    Lemma reverse_A_sem: forall t1 t2 E, 
      In (t1, t2) E -> In (t2, t1) (reverse_A E).
    Proof.
      intros.
      induction E...
      - inversion H.
      - destruct H.
        + inversion H;subst. simpl. left. reflexivity.
        + right. apply IHE. auto.
    Qed.
    
    Lemma eqe_symm: forall E t1 t2, eqe E t1 t2 -> eqe (reverse_A E) t2 t1.
    Proof with auto.
      intros.
      inductions H...
      - apply reverse_A_sem in H. auto.
      - apply e_trans with (t2:=t2)...
    Qed.
    
    Lemma reverse_A_reverse: forall E, reverse_A (reverse_A E) = E.
    Proof with auto.
      intros.
      induction E...
      simpl. destruct a. f_equal...
    Qed.
    
    
    
    
    Theorem soundW: forall t1 t2 A,
      (forall t1 t2, In (t1, t2) A -> WHNF_eqW t1 t2) ->
      (* (forall t1 t2, In (t1, t2) (reverse_A A) -> WHNF_eqW t1 t2) -> *)
      eqe A t1 t2 ->
      WHNF_eqW t1 t2.
    Proof.
      (* cofix soundW. *)
      introv HA 
      Heq.
      pose proof (wh_introw (fun m => match m with 
          | m_pos => eqe A
          | m_neg => eqe (reverse_A A) end) 
      ) as rule.
      inversion Heq;subst.
      +
        apply HA. exact H.
      (* +
        apply WHNF_eqW_symm. apply HA. exact H. *)
      +
        apply rule.
        { intros. destruct m; simpl in H. 
          apply eqe_symm in H. rewrite reverse_A_reverse in H. assumption.
          apply eqe_symm in H. assumption.
        }
        { intros. destruct m; simpl in H.
          + exists A. split. exact HA. apply H.
          + exists (reverse_A A).
            rewrite reverse_A_reverse. split. exact HA. apply H. }
        apply wh_done.
        apply ty_introw with (R:=eqe A)...
        apply Tyeq_refl.
      +
        (* trans *)
        apply rule.
        { intros. destruct m; simpl in H1. 
          apply eqe_symm in H1. rewrite reverse_A_reverse in H1. assumption.
          apply eqe_symm in H1. assumption.
        }
        { intros. destruct m; simpl in H.
          + exists A. split. exact HA. assumption.
          + exists (reverse_A A). rewrite reverse_A_reverse.  split. exact HA. assumption. }
        apply wh_trans with (t2:=t3) (m:=m_pos);assumption.
      
      +
        apply rule.
      
        { intros. destruct m; simpl in H. 
        apply eqe_symm in H. rewrite reverse_A_reverse in H. assumption.
        apply eqe_symm in H. assumption.
      }
      { intros. destruct m; simpl in H.
        + exists A. split. exact HA. assumption.
        + exists (reverse_A A). rewrite reverse_A_reverse.  split. exact HA. assumption. }
        apply wh_done.
        apply Tyeq_mu_l.
      + 
        apply rule.
        { intros. destruct m; simpl in H. 
        apply eqe_symm in H. rewrite reverse_A_reverse in H. assumption.
        apply eqe_symm in H. assumption.
      }
      { intros. destruct m; simpl in H.
        + exists A. split. exact HA. assumption.
        + exists (reverse_A A). rewrite reverse_A_reverse.  split. exact HA. assumption. }
      
        apply wh_done.
        apply Tyeq_mu_r.
      +
        cofix proof.
    
        (* 
        A failed attempt
        
        apply (wh_introw (fun t1 t2 => (exists A,
                (forall t1 t2, In (t1, t2) A -> WHNF_eqW t1 t2) /\
                eqe A t1 t2))). { auto. }
        { apply wh_arrow.
          + exists ((t_arrow t0 t3, t_arrow t1' t2') :: A).
            split;auto. intros.
            inversion H1;subst. inversion H2;subst.
            apply proof. apply HA. apply H2.
            Fail Guarded.
        }  *)
    
        apply (wh_introw ( 
         (
          fun m => match m with m_pos =>
          eqe ((t_arrow t0 t3, t_arrow t1' t2') :: A)
          | m_neg => eqe ((t_arrow t1' t2', t_arrow t0 t3) :: (reverse_A A)) end
          ))).
        (* { intros. apply eqe_symm. apply H1. }  *)
    
        { intros. destruct m; simpl in H1. 
          apply eqe_symm in H1. simpl in H1. rewrite reverse_A_reverse in H1. assumption.
          apply eqe_symm in H1. simpl in H1. assumption.
        }
        { intros. destruct m; simpl in H1.
           (* apply wh_introp with (A:= ((t_arrow t0 t3, t_arrow t1' t2') :: A)). *)
          + exists ( ((t_arrow t0 t3, t_arrow t1' t2') :: A)). split.
            2:{ exact H1. }
            intros. inversion H2;subst.
            { inversion H3;subst. apply proof. }
            { apply HA. apply H3. }
          + exists ( ((t_arrow t1' t2', t_arrow t0 t3) :: (reverse_A A))). split.
            2:{ exact H1. }
            intros. inversion H2;subst.
            { inversion H3;subst. apply proof. }
            { apply HA. rewrite reverse_A_reverse  in H3. apply H3. } 
        }
        apply wh_arrow with (m:=m_pos);try assumption.
    Qed.
    
    Lemma interp_W_aux_transform: forall A1 m,
    (forall t1 t2 : typ, In (t1, t2) match m with
                                          | m_pos => A1
                                          | m_neg => reverse_A A1
                                          end -> WHNF_eqW t1 t2) ->
    forall t1 t2, In (t1, t2) A1 -> WHNF_eqW t1 t2.
    Proof with auto.
      intros.
      destruct m; simpl in H0.
      - apply H. apply H0.
      - apply WHNF_eqW_symm. apply H.
        apply reverse_A_sem. apply H0.
    Qed.
    