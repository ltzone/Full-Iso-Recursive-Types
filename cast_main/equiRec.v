Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.


Require Export erasure.

Notation unfold_mu t := 
    (open_typ_wrt_typ t (t_mu t)).


Definition cctx_sem (cl : list (typ * typ)) (Rel: typ -> typ -> Prop) : Type :=
  Forall (fun l => match l with ( A, B) => Rel A B end) cl.


Definition reverse_E (E: cctx) :=
  map (fun v => match v with (A, B) =>  (B, A) end) E.



Lemma uniq_reverse_E: forall E, uniq E ->
  uniq (reverse_E E).
Proof with auto.
  apply uniq_map_2. 
Qed.

#[export]
Hint Immediate uniq_reverse_E : core.
  

Definition reverse_A (E: list (typ*typ)) :=
  List.map (fun v => match v with (A, B) =>  (B, A) end) E.




Inductive eqe : list (typ * typ) -> typ -> typ -> Prop :=
| e_assump1: forall E t1 t2,
    In (t1,t2) E ->
    eqe E t1 t2
| e_refl: forall E t, eqe E t t
| e_trans: forall E t1 t2 t3,
    eqe E t1 t2 -> eqe E t2 t3 -> eqe E t1 t3
(* | e_symm: forall E t1 t2, eqe E t1 t2 -> eqe E t2 t1 *)
| e_fld: forall E t, 
    eqe E (t_mu t) 
          (unfold_mu t)
| e_unfld: forall E t, 
    eqe E  
      (unfold_mu t) 
      (t_mu t) 
| e_arrfix: forall E t1 t2 t1' t2',
    eqe ((t_arrow t1 t2, t_arrow t1' t2'):: E) t1 t1' -> 
    eqe ((t_arrow t1 t2, t_arrow t1' t2'):: E) t2 t2' ->
    eqe E (t_arrow t1 t2) (t_arrow t1' t2')
.



Lemma Tyeq_symm: forall t1 t2, Tyeq t1 t2 -> Tyeq t2 t1.
Proof.
  cofix IH.
  intros.
  inversion H;subst.
  + apply Tyeq_arrow.
    apply IH. exact H0.
    apply IH. exact H1.
  + apply Tyeq_mu_r.
  + apply Tyeq_mu_l.
  + apply Tyeq_refl.
  + apply Tyeq_trans with (t2:=t3).
    - apply IH. exact H1.
    - apply IH. exact H0.
Qed.


Definition flip (m: mode) :=
  match m with
  | m_pos => m_neg
  | m_neg => m_pos
  end.

Inductive WHNF_eqWi (R: mode -> typ -> typ -> Prop): typ -> typ -> Prop :=
| wh_done: forall t1 t2, Tyeq t1 t2 -> WHNF_eqWi R t1 t2
| wh_arrow: forall m t1 t2 t1' t2',
    R m t1 t1' -> (* coinductive WHNF_eqP *)
    R m t2 t2' ->
    WHNF_eqWi R (t_arrow t1 t2) (t_arrow t1' t2')
| wh_trans: forall m t1 t2 t3, 
    (* WHNF_eqWi R t1 t2 -> 
    WHNF_eqWi R t2 t3 ->  *)
    R m t1 t2 ->
    R m t2 t3 ->
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
  - apply wh_done. apply Tyeq_symm...
  - apply wh_arrow with (m:=flip m); apply H; destruct m; auto.
  - apply wh_trans with (t2:=t2) (m:=flip m); apply H; destruct m; auto.
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

CoFixpoint interp_W: forall t1 t2,
  (WHNF_eqW t1 t2 -> Tyeq t1 t2).
Proof.
  intros.
  inversion H;subst.
  inversion H2;subst.
  - apply H3.
  - forwards (A1&He1&He2): H1 H3.
    lets He1': interp_W_aux_transform He1.
    forwards Hwhnf1: soundW He1' He2.
    forwards (A2&He3&He4): H1 H4.
    lets He3': interp_W_aux_transform He3.
    forwards Hwhnf2: soundW He3' He4.
    apply Tyeq_arrow.
    + apply interp_W. 
      (* apply WHNF_eqW_symm.  *)
      exact Hwhnf1.
    + apply interp_W. exact Hwhnf2.

  - forwards (A1&He1&He2): H1 H3.
    lets He1': interp_W_aux_transform He1.
    forwards Hwhnf1: soundW He1' He2.
    forwards (A2&He3&He4): H1 H4.
    lets He3': interp_W_aux_transform He3.
    forwards Hwhnf2: soundW He3' He4.
    apply Tyeq_trans with (t2:=t3).
    + apply interp_W. exact Hwhnf1.
    + apply interp_W. exact Hwhnf2.
(* 
  - forwards (A1&He1&He2): H0 H2.
    forwards Hwhnf1: soundW He1 He2.
    forwards (A2&He3&He4): H0 H3.
    forwards Hwhnf2: soundW He3 He4.
    apply Tyeq_trans with (t2:=t3).
    + apply interp_W. exact Hwhnf1.
    + apply interp_W. exact Hwhnf2. *)
  (* - 
    forwards (A1&He1&He2): H0 H2.
    forwards Hwhnf1: soundW He1 He2.
    apply Tyeq_symm. apply interp_W.
    Guarded. assumption. *)
Qed.




Lemma done_aux: forall R t1 t2, Tyeq t1 t2 -> WHNF_eqWi R t1 t2.
Proof.
  intros.
  apply wh_done. exact H.
Qed.

Theorem soundness: forall A t1 t2,
  (forall t1 t2, In (t1, t2) A -> Tyeq t1 t2) ->
  eqe A t1 t2 ->
  Tyeq t1 t2.
Proof.
  intros.
  apply interp_W.
  apply soundW with (A:=A). 2:{ exact H0. }
  intros.
  forwards: H H1.
  apply wh_introw with (R:=fun m x y => False).
  2:{ intros. destruct H3. }
  2:{ apply done_aux. apply H2. }
  intros. destruct H3.
Qed.


Definition to_assump (E: cctx) :=
  List.map (fun cx_v => match cx_v with (_, v) => v end) E.

Lemma revA_dist: forall G1 G2,
  reverse_A (G1 ++ G2) = (reverse_A G1) ++ (reverse_A G2).
Proof.
  apply List.map_app.
Qed.

Lemma eqe_weakening: forall G G1 G2 A B,
  eqe (G1 ++ G2) A B ->
  eqe (G1 ++ G ++ G2) A B.
Proof with auto.
  intros. generalize dependent G. dependent induction H; intros...
  - apply e_assump1. apply in_app_or in H. destruct H.
    -- apply in_or_app...
    -- apply in_or_app; right; apply in_or_app...
  (* - apply e_assump2. apply in_app_or in H. destruct H.
    -- apply in_or_app...
    -- apply in_or_app; right; apply in_or_app... *)
  - apply e_trans with t2...
  - apply e_arrfix.
    --
      repeat rewrite revA_dist.
      rewrite_alist (((t_arrow t1 t2, t_arrow t1' t2') :: G1) ++ G ++ G2). 
      apply IHeqe1...
    -- rewrite_alist (((t_arrow t1 t2, t_arrow t1' t2') :: G1) ++ G ++ G2). apply IHeqe2...
Qed.

Lemma in_remove_cx: forall cx A B E,
  In (cx, (A, B)) E -> In (A, B) (to_assump E).
Proof with auto.
  intros. induction E... simpl in *. destruct H.
  - subst...
  - right...
Qed.


Lemma revE_to_revA: forall E,
  to_assump (reverse_E E) = reverse_A (to_assump E).
Proof with auto.
  intros. induction E...
  - destruct a. simpl. f_equal...
Qed.



Theorem soundness_eqe: forall D E A B c, 
  TypCast D E A B c ->
  eqe (to_assump E) A B.
Proof with auto.
  intros.
  induction H...
  - apply e_arrfix.
   -- rewrite_alist (nil ++ [(t_arrow A1 B1, t_arrow A2 B2)] ++ (to_assump E)). apply eqe_weakening...
   -- rewrite_alist (nil ++ [(t_arrow A1 B1, t_arrow A2 B2)] ++ to_assump E). apply eqe_weakening...
  - apply e_trans with B...
  - apply e_assump1. apply in_remove_cx with cx...
  - pick_fresh cx. specialize_x_and_L cx L. simpl in *. apply e_arrfix... 
    (* rewrite <- revE_to_revA...  *)
Qed.


Theorem exist_cctx_to_E: forall E,
  exists cs, E = to_assump cs.
Proof.
  intros. induction E.
  - exists (@nil (atom * (typ * typ))). reflexivity.
  - destruct IHE as [cs' IHE]. pick_fresh i. exists ((i, a) :: cs'). simpl. f_equal. assumption.
Qed.


(* 



mu x. mu y. y -> x == mu x. x -> x


dual : fix cx. fold -> cx 
 = fix cx. unfold -> cx


*)

(* forall x, A, B in E -> Tyeq A B *)
(* forall x, A, B in E -> eqe A B *)
(* need completeness to prove symmetry *)
(* need symmetry to prove completeness *)




Lemma rev_cast_open_aux: forall c n cx, 
  cx `notin` castfv_castop c ->
  rev_cast (open_castop_wrt_castop_rec n (c_var_f cx) c) = open_castop_wrt_castop_rec n  (c_var_f cx) (rev_cast c).
Proof with auto.
  inductions c;simpl;intros;
    unfold open_castop_wrt_castop in * ;simpl;try reflexivity.
  - destruct (lt_eq_lt_dec n n0);simpl...
    destruct s...
  - rewrite IHc1...
    rewrite IHc2...
  - rewrite IHc1...
    rewrite IHc2...
  - f_equal. rewrite IHc...  
Qed.


Lemma rev_cast_open: forall c cx, 
  cx `notin` castfv_castop c ->
  rev_cast (open_castop_wrt_castop c (c_var_f cx)) = open_castop_wrt_castop (rev_cast c) (c_var_f cx).
Proof with auto.
    unfold open_castop_wrt_castop in * ;simpl. intros. apply rev_cast_open_aux with (n:=0)...
Qed.
  


Lemma In_revE: forall cx A B E, In (cx, (A, B)) E -> In (cx, (B, A)) (reverse_E E).
Proof with auto.
  intros. induction E...
  - destruct a as [cx' [A' B']]. inversion H.
    -- inv H0. left. reflexivity.
    -- simpl. right. apply IHE...
Qed.

Lemma TypCast_symm2: forall D E A B c,
  TypCast D E A B c ->
  TypCast D (reverse_E E) B A (rev_cast c).
Proof with auto.
  intros.
  induction H...
  - constructor...
  - constructor...
  - constructor...
  - simpl. apply TCast_seq with (B:=B)...
  - apply TCast_var... 
    apply In_revE...
  - pick_fresh cx. simpl.
    apply TCast_fix with (L:=L \u {{ cx }} \u castfv_castop c1 \u castfv_castop c2).
    + intros. simpl in H0. rewrite <- rev_cast_open...
    + intros. simpl in H2. rewrite <- rev_cast_open...
Qed.


Lemma in_add_cx: forall A B E,
  In (A, B) (to_assump E) -> exists cx, In (cx, (A, B)) E.
Proof with auto.
  intros. induction E.
  - inversion H.
  - destruct a as [cx' [A' B']]. inversion H.
    -- exists cx'. inversion H0; subst. constructor...
    -- destruct (IHE H0). exists x. simpl. right...
Qed.




Inductive eqe_wf :  tctx -> list (typ * typ) -> typ -> typ -> Prop :=
| ew_assump1: forall D E t1 t2,
    WFTyE D -> WFT D t1 -> WFT D t2 -> 
    In (t1,t2) E ->
    eqe_wf D E t1 t2
| ew_refl: forall D E t, WFTyE D -> WFT D t -> eqe_wf D E t t
| ew_trans: forall D E t1 t2 t3,
    WFT D t2 ->
    eqe_wf D E t1 t2 -> eqe_wf D E t2 t3 -> eqe_wf D E t1 t3
(* | e_symm: forall E t1 t2, eqe E t1 t2 -> eqe E t2 t1 *)
| ew_fld: forall D E t, 
    WFTyE D -> WFT D (t_mu t) ->
    eqe_wf D E (t_mu t) 
          (unfold_mu t)
| ew_unfld: forall D E t,
    WFTyE D -> WFT D (t_mu t) -> 
    eqe_wf D E  
      (unfold_mu t) 
      (t_mu t) 
| ew_arrfix: forall D E t1 t2 t1' t2',
    eqe_wf D ((t_arrow t1 t2, t_arrow t1' t2'):: E) t1 t1' -> 
    eqe_wf D ((t_arrow t1 t2, t_arrow t1' t2'):: E) t2 t2' ->
    eqe_wf D E (t_arrow t1 t2) (t_arrow t1' t2')
.

#[global]
Hint Constructors eqe_wf : core.

Lemma eqe_wf_complete: forall D E t1 t2,
  WFTyE D -> WFT D t1 -> WFT D t2 ->
  eqe E t1 t2 ->
  eqe_wf D E t1 t2.
Proof with auto.
  introv Hwfe Hwf1 Hwf2 Heq.
  inductions Heq...
  - admit.
  - inv Hwf1. inv Hwf2...
Admitted.


Lemma WFT_eqe: forall E t1 t2 D,
  eqe E t1 t2 -> (forall t1 t2, In (t1, t2) E -> WFT D t1 /\ WFT D t2) -> ((WFT D t1 -> WFT D t2) /\ (WFT D t2 -> WFT D t1)).
Proof with auto.
  intros. induction H...
  - apply H0 in H. destruct H...
  - destruct IHeqe1... destruct IHeqe2...
  - admit.
  - admit.
  - destruct IHeqe1...
    { intros. inv H2... inv H3.
  (* - split.
    --constructor. apply  *)
Admitted.


Lemma WFTmE_strengthening: forall D E F x U,
  WFTmE D (F ++ x ~ U ++ E ) ->
  WFTmE D (F ++ E).
Proof with auto.
  intros.
  induction F...
  - inversion H...
  - inversion H;subst.
    constructor...
Qed.

Ltac solve_uniqE := eapply uniq_remove_mid; eauto.



Lemma TypCast_strengthening: forall D cx A B T1 T2 E1 E2 c,
  TypCast D (E1 ++ [(cx, (A ,B))] ++ E2) T1 T2 c ->
  cx \notin castfv_castop c ->
  TypCast D (E1 ++ E2) T1 T2 c.
Proof with auto.
  intros.
  inductions H...
  - (* id *)
    constructor... solve_uniqE.
  - 
    (* arrow *)
    simpl in H1.
    apply TCast_arrow...
    + apply IHTypCast1 with (cx0:=cx) (A0:=A) (B0:=B)...
    + apply IHTypCast2 with (cx0:=cx) (A0:=A) (B0:=B)...
  - (* unfold *)
    constructor... solve_uniqE.
  - (* fold *)
    constructor... solve_uniqE.
  -
    (* seq *)
    simpl in H1.
    apply TCast_seq with (B:=B0)...
    + apply IHTypCast1 with (cx0:=cx) (A1:=A) (B1:=B)...
    + apply IHTypCast2 with (cx0:=cx) (A0:=A) (B1:=B)...
  -
    (* var *)
    apply in_app_or in H2. destruct H2.
    { apply TCast_var... solve_uniqE. apply in_or_app. left... }
    inversion H2;subst.
    + inv H4. simpl in H3. fsetdec.
    + apply TCast_var... solve_uniqE. apply in_or_app. right...
  -
    (* fix *)
    simpl in H3.
    apply TCast_fix with (L:=L \u {{cx}}); intros.
    --
      rewrite_alist (([(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E2).
      apply H0 with (cx1:=cx) (A0:=A) (B0:=B)...
      rewrite castfv_castop_open_castop_wrt_castop_upper.
      simpl.
      fsetdec.
    -- 
      rewrite_alist (([(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E2).
      apply H2 with (cx1:=cx) (A0:=A) (B0:=B)...
      rewrite castfv_castop_open_castop_wrt_castop_upper.
      simpl.
      fsetdec.
Qed.



Lemma TypCast_narrowing': forall D T1 T2 E1 E2 E c,
  TypCast D (E1 ++ E2) T1 T2 c ->
  uniq (E1 ++ E ++ E2) ->
  TypCast D (E1 ++ E ++ E2) T1 T2 c.
Proof with auto.
  intros.
  generalize dependent E. inductions H; intros...
  (* -
    (* arrow *)
    apply TCast_arrow...
    repeat rewrite revE_dist. apply IHTypCast1.
    + rewrite revE_dist...
    + repeat rewrite <- revE_dist. apply uniq_map_2... *)
  -
    (* seq *)
    apply TCast_seq with (B:=B)...
  -
    (* var *)
    apply in_app_or in H2. destruct H2.
    { apply TCast_var... apply in_or_app. left... }
    { apply TCast_var... apply in_or_app. right.
      apply in_or_app. right... }
  -
    (* fix *)
    apply TCast_fix with (L:=L \u dom (E1 ++ E ++ E2)); intros.
    --
      rewrite_alist (([(cx, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E ++ E2).
      apply H0... rewrite !app_assoc.
      constructor...
    --
      rewrite_alist (([(cx, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E ++ E2).
      apply H2... rewrite !app_assoc. constructor...
Qed.

Lemma TypCast_narrowing: forall D T1 T2 E1 E2 cx A B c,
  cx `notin` union (dom E1) (dom E2) ->
  lc_typ A /\ lc_typ B ->
  TypCast D (E1 ++ E2) T1 T2 c ->
  TypCast D (E1 ++ cx ~ (A, B) ++ E2) T1 T2 c.
Proof with auto.
  intros. apply TypCast_narrowing' with (E:=cx ~ (A, B))...
  apply uniq_insert_mid...
  apply TypCast_regular in H1.
  destruct_hypos...
Qed.


Lemma typcast_var_det: forall cx A B C D (E: cctx),
  uniq E ->
  In (cx, (A, B)) E ->
  In (cx, (C, D)) E ->
  A = C /\ B = D.
Proof with auto.
  intros. assert ((A, B) = (C, D)). {
    apply binds_unique with (x := cx) (E := E)...
  } inversion H2...
Qed.


Lemma typcast_var_det_aux: forall (E1 E2: cctx) cx a b A B,
  uniq (E1 ++ cx ~ (a, b) ++ E2) ->
  In (cx, (A, B)) (E1 ++ cx ~ (a, b) ++ E2) ->
  A = a /\ B = b.
Proof with auto.
  intros. assert (In (cx, (a, b)) (E1 ++ cx ~ (a, b) ++ E2)). {
    apply in_or_app. right. constructor...
  } eapply typcast_var_det; eauto.
Qed.

Lemma subst_castop : forall D E1 E2 a b c d cx c1 c2,
  TypCast D (E1 ++ [(cx, (a, b))] ++ E2) c d c1 ->
  TypCast D (E1 ++ E2) a b c2 ->
  TypCast D (E1 ++ E2) c d (castsubst_castop c2 cx c1).
Proof with auto.
  intros.
  inductions H; subst; simpl...
  - constructor... solve_uniqE.
  - apply TCast_arrow.
    apply IHTypCast1 with (a0:=a) (b0:=b)...
    apply IHTypCast2 with (a0:=a) (b0:=b)...
  - constructor... solve_uniqE.
  - constructor... solve_uniqE.
  - eapply TCast_seq with (B:=B). 
    apply IHTypCast1 with (a0:=a) (b0:=b)...
    apply IHTypCast2  with (a0:=a) (b0:=b)...
  - destruct (cx0 == cx).
    -- 
    
    subst. assert (A = a /\ B = b). {
      eapply typcast_var_det_aux. apply H1. auto.
    } destruct_hypos. subst...
    -- eapply TCast_var... solve_uniqE.
       apply in_app_or in H2.
       destruct H2.
       { apply in_or_app. left... }
       { inversion H2;subst.
        + inv H4. exfalso. apply n...
        + apply in_or_app. right... }
  - eapply TCast_fix with (L:=L \u {{ cx }} \u (dom (E1 ++ E2))); 
    intros.
    --
      rewrite castsubst_castop_open_castop_wrt_castop_var... 
      2:{ apply TypCast_regular in H3. destruct_hypos... }
      rewrite_alist (([(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E2).
      apply H0 with (a0:=a) (b0:=b)...
      rewrite_alist (nil ++ [(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ (E1 ++ E2)).
      apply TypCast_narrowing...
      specialize_x_and_L cx0 L. apply TypCast_regular in H, H1. destruct_hypos...

    --
      rewrite castsubst_castop_open_castop_wrt_castop_var... 
      2:{ apply TypCast_regular in H3. destruct_hypos... }
      rewrite_alist (([(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E2).
      apply H2 with (a0:=a) (b0:=b)...
      rewrite_alist (nil ++ [(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ (E1 ++ E2)).
      apply TypCast_narrowing...
      specialize_x_and_L cx0 L. apply TypCast_regular in H, H1. destruct_hypos...
Qed.




Theorem completeness_eqe: forall D A B G,
  WFTyE D ->
  WFT D A ->
  WFT D B ->
  eqe G A B ->
  forall cs, G = to_assump cs -> uniq cs ->
    exists c, TypCast D cs A B c.
  (* exists cs c, G = to_assump cs /\ TypCast D cs A B c. *)
Proof with auto.
  intros. gen cs.
  induction H2;intros...
  - 
    subst. apply in_add_cx in H2. destruct H2.
    exists (c_var_f x). constructor...
  -
    exists c_id. constructor...
  -
    assert (WFT D t2). { eapply WFT_eqe;eauto. admit. }
    destruct (IHeqe1) with (cs:=cs) as [c1 IHeqe1'], 
      (IHeqe2) with (cs:=cs) as [c2 IHeqe2']...
    exists (c_seq c1 c2). eapply TCast_seq with (B:=t2)...
  -
    exists (c_unfold (t_mu t))...
  -
    exists (c_fold (t_mu t))...
  -
    pick_fresh cx.
    inv H0. inv H1.
    forwards [c1 IHe1]: 
      IHeqe1 ((cx, (t_arrow t1 t2, t_arrow t1' t2')) :: cs)...
    forwards [c2 IHe2]: 
      IHeqe2 ((cx, (t_arrow t1 t2, t_arrow t1' t2')) :: cs)...
    exists (c_fixc (c_arrow 
          (close_castop_wrt_castop cx c1)
          (close_castop_wrt_castop cx c2))).
    apply TCast_fix with (L:= {{cx}} \u dom cs).
    + intros. rewrite <- castsubst_castop_spec.
      eapply subst_castop with (E1:=nil) (a:=t_arrow t1 t2) (b:=t_arrow t1' t2').
      2:{ apply TCast_var... rewrite app_nil_l... left... }
      rewrite_alist ((cx ~ (t_arrow t1 t2, t_arrow t1' t2')) ++ (cx0 ~ (t_arrow t1 t2, t_arrow t1' t2')) ++ cs).
      apply TypCast_narrowing...
    + intros. rewrite <- castsubst_castop_spec.
      eapply subst_castop with (E1:=nil) (a:=t_arrow t1 t2) (b:=t_arrow t1' t2').
      2:{ apply TCast_var... rewrite app_nil_l... left... }
      rewrite_alist ((cx ~ (t_arrow t1 t2, t_arrow t1' t2')) ++ (cx0 ~ (t_arrow t1 t2, t_arrow t1' t2')) ++ cs).
      apply TypCast_narrowing...
Admitted.



