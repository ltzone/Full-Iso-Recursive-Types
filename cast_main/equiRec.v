Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.


Require Export erasure.



Inductive eqe : tctx -> actx -> typ -> typ -> Prop :=
 | e_assump : forall (D:tctx) (H:actx) (A B:typ),
      In ( A ,  B )  H  ->
     WFT D A ->
     WFT D B ->
     eqe D H A B
 | e_refl : forall (D:tctx) (H:actx) (A:typ),
     WFT D A ->
     eqe D H A A
 | e_trans : forall (D:tctx) (H:actx) (A C B:typ),
     eqe D H A B ->
     eqe D H B C ->
     eqe D H A C
 | e_fld : forall (D:tctx) (H:actx) (A:typ),
     WFT D (t_mu A) ->
     eqe D H (t_mu A)  (open_typ_wrt_typ  A (t_mu A) ) 
 | e_unfld : forall (D:tctx) (H:actx) (A:typ),
     WFT D (t_mu A) ->
     eqe D H  (open_typ_wrt_typ  A (t_mu A) )  (t_mu A)
 | e_arrfix : forall (D:tctx) (H:actx) (A1 A2 B1 B2:typ),
     eqe D  (cons ( (t_arrow A1 A2) ,  (t_arrow B1 B2) )  H )  A1 B1 ->
     eqe D  (cons ( (t_arrow A1 A2) ,  (t_arrow B1 B2) )  H )  A2 B2 ->
     eqe D H (t_arrow A1 A2) (t_arrow B1 B2).



#[export]
Hint Constructors eqe : core.

Notation unfold_mu t := 
    (open_typ_wrt_typ t (t_mu t)).


Definition cctx_sem (cl : actx) (Rel: typ -> typ -> Prop) : Type :=
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
  

Definition reverse_A (E: actx) :=
  List.map (fun v => match v with (A, B) =>  (B, A) end) E.



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

Lemma eqe_symm: forall D E t1 t2, eqe D E t1 t2 -> eqe D (reverse_A E) t2 t1.
Proof with auto.
  intros.
  inductions H...
  - apply reverse_A_sem in H0. auto.
  - apply e_trans with (B:=B)...
Qed.

Lemma reverse_A_reverse: forall E, reverse_A (reverse_A E) = E.
Proof with auto.
  intros.
  induction E...
  simpl. destruct a. f_equal...
Qed.



Definition to_assump (E: cctx) :=
  List.map (fun cx_v => match cx_v with (_, v) => v end) E.

Lemma revA_dist: forall G1 G2,
  reverse_A (G1 ++ G2) = (reverse_A G1) ++ (reverse_A G2).
Proof.
  apply List.map_app.
Qed.

Lemma eqe_weakening: forall D G G1 G2 A B,
  eqe D (G1 ++ G2) A B ->
  eqe D (G1 ++ G ++ G2) A B.
Proof with auto.
  intros. generalize dependent G. dependent induction H; intros...
  - apply e_assump... apply in_app_or in H0. destruct H0.
    -- apply in_or_app...
    -- apply in_or_app; right; apply in_or_app...
  - apply e_trans with B...
  - apply e_arrfix.
    --
      repeat rewrite revA_dist.
      rewrite_alist (((t_arrow A1 A2, t_arrow B1 B2) :: G1) ++ G ++ G2). 
      apply IHeqe1...
    -- rewrite_alist (((t_arrow A1 A2, t_arrow B1 B2) :: G1) ++ G ++ G2). apply IHeqe2...
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
  eqe D (to_assump E) A B.
Proof with auto.
  intros.
  induction H...
  - apply e_arrfix.
   -- rewrite_alist (nil ++ [(t_arrow A1 B1, t_arrow A2 B2)] ++ (to_assump E)). apply eqe_weakening...
   -- rewrite_alist (nil ++ [(t_arrow A1 B1, t_arrow A2 B2)] ++ to_assump E). apply eqe_weakening...
  - apply e_trans with B...
  - apply e_assump... apply in_remove_cx with cx...
  - pick_fresh cx. specialize_x_and_L cx L. simpl in *. apply e_arrfix... 
Qed.


Theorem exist_cctx_to_E: forall E,
  exists cs, E = to_assump cs.
Proof.
  intros. induction E.
  - exists (@nil (atom * (typ * typ))). reflexivity.
  - destruct IHE as [cs' IHE]. pick_fresh i. exists ((i, a) :: cs'). simpl. f_equal. assumption.
Qed.


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




Lemma WFTmE_strengthening: forall E F x U,
  WFTmE (F ++ x ~ U ++ E ) ->
  WFTmE (F ++ E).
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
      rewrite_alist (([(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E2).
      apply H0 with (a0:=a) (b0:=b)...
      rewrite_alist (nil ++ [(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ (E1 ++ E2)).
      apply TypCast_narrowing...
      specialize_x_and_L cx0 L. apply TypCast_regular in H, H1. destruct_hypos...

    --
      rewrite castsubst_castop_open_castop_wrt_castop_var... 
      rewrite_alist (([(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ E1) ++ E2).
      apply H2 with (a0:=a) (b0:=b)...
      rewrite_alist (nil ++ [(cx0, (t_arrow A1 B1, t_arrow A2 B2))] ++ (E1 ++ E2)).
      apply TypCast_narrowing...
      specialize_x_and_L cx0 L. apply TypCast_regular in H, H1. destruct_hypos...
Qed.

Lemma eqe_regular: forall D E A B, eqe D E A B -> WFT D A /\ WFT D B.
Proof with auto.
  intros. induction H...
  - destruct_hypos...
  - split... inv H0.
    pick_fresh X. specialize_x_and_L X L.
    rewrite typsubst_typ_intro with (X1:=X)...
    rewrite_alist (nil ++ D).
    apply WFT_typsubst...
  - split... inv H0.
    pick_fresh X. specialize_x_and_L X L.
    rewrite typsubst_typ_intro with (X1:=X)...
    rewrite_alist (nil ++ D).
    apply WFT_typsubst...
  - destruct_hypos...
Qed.
  

Theorem completeness_eqe: forall D A B G,
  eqe D G A B ->
  forall cs, G = to_assump cs -> uniq cs ->
    exists c, TypCast D cs A B c.
  (* exists cs c, G = to_assump cs /\ TypCast D cs A B c. *)
Proof with auto.
  intros. gen cs.
  induction H;intros...
  - 
    subst. apply in_add_cx in H0. destruct H0.
    exists (c_var_f x). constructor...
  -
    exists c_id. constructor...
  -
    destruct (IHeqe1) with (cs:=cs) as [c1 IHeqe1'], 
      (IHeqe2) with (cs:=cs) as [c2 IHeqe2']...
    exists (c_seq c1 c2). eapply TCast_seq with (B:=B)...
  -
    exists (c_unfold (t_mu A))...
  -
    exists (c_fold (t_mu A))...
  - 
    subst.
    pick_fresh cx.
    forwards [c1 IHe1]: 
      IHeqe1 ((cx, (t_arrow A1 A2, t_arrow B1 B2)) :: cs)...
    forwards [c2 IHe2]: 
      IHeqe2 ((cx, (t_arrow A1 A2, t_arrow B1 B2)) :: cs)...
    exists (c_fixc (c_arrow 
          (close_castop_wrt_castop cx c1)
          (close_castop_wrt_castop cx c2))).
    apply TCast_fix with (L:= {{cx}} \u dom cs).
    + intros. rewrite <- castsubst_castop_spec.
      eapply subst_castop with (E1:=nil) (a:=t_arrow A1 A2) (b:=t_arrow B1 B2).
      2:{ forwards (?&?): eqe_regular H0.
          forwards (?&?): eqe_regular H1...
          apply TCast_var...
          rewrite app_nil_l... left... }
      rewrite_alist ((cx ~ (t_arrow A1 A2, t_arrow B1 B2)) ++ (cx0 ~ (t_arrow A1 A2, t_arrow B1 B2)) ++ cs).
      apply TypCast_narrowing...
    + intros. rewrite <- castsubst_castop_spec.
      eapply subst_castop with (E1:=nil) (a:=t_arrow A1 A2) (b:=t_arrow B1 B2).
      2:{ forwards (?&?): eqe_regular H0.
          forwards (?&?): eqe_regular H1...
          apply TCast_var...
          rewrite app_nil_l... left... }
      rewrite_alist ((cx ~ (t_arrow A1 A2, t_arrow B1 B2)) ++ (cx0 ~ (t_arrow A1 A2, t_arrow B1 B2)) ++ cs).
      apply TypCast_narrowing...
Qed.
