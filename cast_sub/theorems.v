Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.
Require Import Relation_Operators.
Require Import Operators_Properties.

Require Export equiAux.

(* Type safety of Full Iso-Recursive Types *)

Theorem progress: forall e t, Typing  nil e t -> 
  (value e) \/ exists e', Reduction e e'.
Proof.
  apply progress.
Qed.

Theorem preservation: forall e T,
  Typing  nil e T -> forall e', 
  Reduction e e' -> Typing  nil e' T.
Proof.
  apply preservation.
Qed.


(*************************************************************************************************************************)
(* Soundness and Completeness of TypCast *)



Theorem TypCast_soundness: forall D A B c, 
  TypCast D nil A B c ->
  eqe2 D nil A B.
Proof with auto.
  intros.
  forwards: soundness_eqe H...
  forwards: eqe_sound H0...
Qed.

Theorem TypCast_completeness: forall D A B, 
  eqe2 D nil A B ->
  exists c, TypCast D nil A B c.
Proof with auto.
  intros.
  forwards: eqe_complete H...
  eapply completeness_eqe with (G:=nil)...
Qed.




(*************************************************************************************************************************)
(* Typing Equivalence to the equi-recursive type system *)

Axiom subtyping_decomposition: forall A B D (Hwfa: WFT D A) (Hwfb: WFT D B),
  ACSubtyping nil A B -> 
  exists C1 C2, eqe2 D nil A C1 /\ 
    AmberSubtyping nil C1 C2 /\ 
    eqe2 D nil C2 B.

Lemma AmberSubtyping_ACSubtyping: forall A B D,
  AmberSubtyping D A B -> 
  ACSubtyping D A B.
Proof with auto.
  intros.
  induction H...
  - apply ACSub_rec with (L:=L)...
Qed.

Theorem typing_i2e_alt: forall G e t, Typing G e t -> EquiTyping G (erase e) t.
Proof with auto.
  intros.
  dependent induction H; simpls...
  - 
    apply ETyping_abs with (L:=L)...
    intros. specialize_x_and_L x L. rewrite erase_open_ee in H0...
  -
    apply ETyping_app with (A1:=A1)...
  -
    apply ETyping_sub with (A:=A)...
    { apply ACSub_eq.
      apply TypCast_soundness in H0...
    }
  -
    apply ETyping_sub with (A:=A)...
    { apply AmberSubtyping_ACSubtyping in H0... }
Qed.


Theorem typing_i2e: forall G e t, Typing G e t -> 
  EquiTypingC G (erase e) t e.
Proof with auto.
  intros.
  dependent induction H; simpls...
  - 
    apply ECTyping_abs with (L:=L)...
    intros. specialize_x_and_L x L. rewrite erase_open_ee in H0...
  -
    apply ECTyping_app with (A1:=A1)...
  -
    apply ECTyping_eq with (A:=A)...
  -
    (* apply ECTyping_sub. *)
Admitted.


Theorem typing_i2e_elab: forall G e t, Typing G e t -> 
  exists e', EquiTypingC G (erase e) t e'.
Proof with eauto.
  intros.
  dependent induction H; simpls...
  -
    pick_fresh x. specialize_x_and_L x L.
    destruct H0 as [e' ?].
    exists (e_abs A1 (close_exp_wrt_exp x e')).
    apply ECTyping_abs with (L:=L)...
    intros. specialize_x_and_L x L. 
    rewrite erase_open_ee in H0...
    rewrite <- subst_exp_spec.
    admit.
  -
    destruct IHTyping1 as [e1' ?].
    destruct IHTyping2 as [e2' ?].
    exists (e_app e1' e2').
    apply ECTyping_app with (A1:=A1)...
  -
    destruct IHTyping as [e' ?].
    exists (e_cast c (e_cast c_id e')).
    eapply ECTyping_sub.
    { apply ACSub_eq.
      apply TypCast_soundness in H0...
    }
  -
    apply ETyping_sub with (A:=A)...
    { apply AmberSubtyping_ACSubtyping in H0... }
Qed.



Theorem erase_typing: forall G e t e', 
  EquiTypingC G e t e' -> erase e' = e.
Proof with auto.
  intros.
  induction H...
  - simpl. f_equal.
    pick_fresh x. specialize_x_and_L x L.
    rewrite erase_open_ee in H0.
    simpl in H0. apply open_exp_wrt_exp_inj in H0...
    rewrite erase_fv. fsetdec.
  - simpl. f_equal...
Qed.



Theorem typing_e2i_alt: forall G e t, EquiTyping G e t -> 
  exists e', Typing G e' t /\ erase e' = e.
Proof with auto.
  intros.
  dependent induction H; simpls...
  -
    exists (e_lit i). split...
  -
    exists (e_var_f x). split...
  -
    pick_fresh x. specialize_x_and_L x L.
    destruct H0 as [e' [Hty He]].
    exists (e_abs A1 (close_exp_wrt_exp x e')). split...
    +
      apply Typing_abs with (L:=L \u dom G \u {{x}})...
      intros. rewrite <- subst_exp_spec.
      rewrite_alist (nil ++ (x0 ~ A1 ++ G)).
      apply typing_through_subst_ee with (U:=A1). 
      2:{ get_WFT... inv H1. apply Typing_var... constructor... }
      rewrite_alist (x ~ A1 ++ x0 ~ A1 ++ G). apply Typing_weakening...
      { get_WFT. inv H1. constructor... constructor... }
    +
      simpl. rewrite erase_close_ee.
      rewrite He. rewrite close_exp_wrt_exp_open_exp_wrt_exp...
  -
    destruct IHEquiTyping1 as [e1' [Hty1 He1]].
    destruct IHEquiTyping2 as [e2' [Hty2 He2]].
    exists (e_app e1' e2'). split;simpl;try congruence.
    apply Typing_app with (A1:=A1)...
  -
    destruct IHEquiTyping as [e' [Hty He]].
    forwards*: TypCast_completeness H0.
Qed.


Lemma EquiTypingC_sem: forall G e  t e',
  EquiTypingC G e  t e' ->
  Typing G e' t /\ EquiTyping G e t.
Proof with auto.
  introv Typ.
  dependent induction Typ;intros...
  - split...
    + apply Typing_abs with (L:=L).
      intros. apply H0...
    + apply ETyping_abs with (L:=L).
      intros. apply H0...
  - split...
    + destruct_hypos. apply Typing_app with (A1:=A1)...
    + destruct_hypos. apply ETyping_app with (A1:=A1)...
  - split...
    + destruct_hypos. apply Typing_cast with (A:=A)...
    + destruct_hypos. apply ETyping_eq with (A:=A)...
      eapply TypCast_soundness;eauto.
Qed.



Lemma ECTyping_weakening: forall G1 G G2 e t e',
  EquiTypingC (G1 ++ G2) e  t e' ->
  WFTmE (G1 ++ G ++ G2) ->
  EquiTypingC (G1 ++ G ++ G2) e t e'.
Proof with auto.
  introv Hty Hwf.
  gen G .
  inductions Hty;intros...
  - apply ECTyping_abs with (L:=L \u dom (G1 ++ G ++ G2))...
    intros. rewrite_alist ((x ~ A1 ++ G1) ++ G ++ G2).
    apply H0...
    rewrite_alist (x ~ A1 ++ G1 ++ G ++ G2).
    constructor... 
    { specialize_x_and_L x L. forwards (?&?): EquiTypingC_sem H.
      get_WFT. inv H2... }
  - apply ECTyping_app with (A1:=A1)...
  - apply ECTyping_eq with (A:=A)...
Qed.


Lemma ECTyping_subst: forall G1 G2 e1 t e1' e2  A e2' x,
  EquiTypingC (G1 ++ x ~ A ++ G2) e1 t e1' ->
  EquiTypingC G2 e2 A e2' ->
  (* EquiTypingC D G2 e2 m2 A e2' -> *)
  EquiTypingC (G1 ++ G2) (subst_exp e2 x e1) t (subst_exp e2' x e1').
Proof with eauto using WFTmE_strengthening.
  introv Hty1 Hty2.
  gen e2 e2'.
  inductions Hty1;intros;simpl...
  - destruct (x0 == x)...
    + subst. rewrite_alist (nil ++ G1 ++ G2). 
      apply ECTyping_weakening;rewrite app_nil_l...
      analyze_binds_uniq H0... { applys~ WFTmE_uniq... }
      (* inv Hty2... *)
  - apply ECTyping_abs with (L:=L \u dom (G1 ++ G2) \u {{x}})...
    intros. rewrite_alist ((x0 ~ A1 ++ G1) ++ G2).
    rewrite !subst_exp_open_exp_wrt_exp_var...
    apply H0 with (A0:=A)...
Qed.



Lemma EquiTypingC_complete: forall G e t,
  EquiTyping G e t ->
  exists e', EquiTypingC G e  t e'.
Proof with auto.
  introv Typ.
  dependent induction Typ;intros...
  - exists (e_lit i)...
  - exists (e_var_f x)...
  - 
    pick_fresh x. specialize_x_and_L x L.
    destruct H0 as [e' Hty'].
    exists (e_abs A1 (close_exp_wrt_exp x e')).
    apply ECTyping_abs with (L:=L \u {{x}}
      \u termfv_exp e \u termfv_exp e' \u dom G)...
    intros.
    rewrite subst_exp_intro with (x1:=x) (e1:=e)...
    rewrite <- subst_exp_spec.
    rewrite_alist (nil ++ x0 ~ A1 ++ G).
    apply ECTyping_subst with (A:=A1)...
    + rewrite_alist (x ~ A1 ++ x0 ~ A1 ++ G).
      apply ECTyping_weakening...
      get_WFT. inv H1.
      constructor...
      constructor...
    + constructor... get_WFT. inv H1.
      constructor...
  - 
    destruct IHTyp1 as [e1' Hty1].
    destruct IHTyp2 as [e2' Hty2].
    exists (e_app e1' e2').
    apply ECTyping_app with (A1:=A1)...
  -
    apply TypCast_completeness in H.
    destruct H as [c' ?].
    destruct IHTyp as [e' ?].
    exists (e_cast c' e').
    apply ECTyping_eq with (A:=A)...
Qed.

Theorem equi_alt_equiv: forall G e t,
  EquiTyping G e t <-> exists e', EquiTypingC G e t e'.
Proof with auto.
  intros. split.
  - apply EquiTypingC_complete.
  - intros [e' Hty]. apply EquiTypingC_sem in Hty...
    destruct Hty...
Qed.





Lemma ETyping_regular: forall G e t,
  EquiTyping G e t -> WFTmE G /\ WFT nil t /\ lc_exp e.
Proof with auto.
  introv Htyp.
  inductions Htyp...
  - repeat split... applys~ binds_tm_regular x G...
  - pick_fresh x. forwards (?&?&?): H0 x...
    inv H1. repeat split...
    apply lc_e_abs_exists with (x1:=x)...
  - destruct_hypos. inv H3...
  - destruct_hypos. repeat split...
    forwards (?&?): eqe2_regular H...
Qed.


(*************************************************************************************************************************)
(* Semantic Equivalence to the equi-recursive type system *)


(* From Iso to Equi, actually we do not even need the Iso terms to be well typed *)
Theorem reduction_i2e: forall e1 e2,
  Reduction e1 e2 ->
  (erase e1) ==>* (erase e2).
Proof with auto.
  apply soundness_erase.
Qed.




(*************************************************************************************************************************)
(* To prove reduction_e2i, we define a new Equi Typing relation, that annotate equi-typing judgements with the related full iso terms *)



Definition terminate (e:exp) : Prop :=
  exists v, value v /\ e ==>* v.

Lemma terminate_app_inv1: forall A e1 e2,
  Typing nil (e_app e1 e2) A ->
  terminate (e_app e1 e2) -> terminate e1.
Proof with auto.
  introv Htyp. intros.
  destruct H as [v [Hval Hred]].
  apply clos_rt_rt1n in Hred.
  dependent induction Hred.
  { inv Hval. }
  inv H.
  + exists (e_abs A0 e). split... apply rt_refl.
  + assert (terminate e1').
    { applys* IHHred.
      applys preservation. apply Htyp.
      constructor... }
    destruct H0 as [v' [Hval' Hred']].
    exists v'. split...
    apply rt_trans with (y:=e1')...
    apply rt_step...
  + exists e1. split... apply rt_refl.
  + exists (e_cast (c_arrow c1 c2) e0).
    split... apply rt_refl.
Qed.



Lemma terminate_app_inv2: forall A e1 e2,
  Typing nil (e_app e1 e2) A ->
  terminate (e_app e1 e2) -> terminate e2.
Proof with auto.
  introv Htyp. intros.
  destruct H as [v [Hval Hred]].
  apply clos_rt_rt1n in Hred.
  dependent induction Hred.
  { inv Hval. }
  inv H.
  + exists e2. split... apply rt_refl.
  + applys* IHHred e1'.
    { applys preservation. apply Htyp.
      constructor... }
  + assert (terminate e2').
    { applys* IHHred.
      applys preservation. apply Htyp.
      constructor... }
    destruct H0 as [v' [Hval' Hred']].
    exists v'. split...
    apply rt_trans with (y:=e2')...
    apply rt_step...
  + exists e2. split... apply rt_refl.
Qed.





Lemma Red_ctx_cast: forall c e e', lc_castop c ->
  e ==>* e' -> e_cast c e ==>* e_cast c e'.
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0.
  induction H0...
  - apply rt_refl.
  - applys rt_trans IHclos_refl_trans_1n.
    apply rt_step. constructor...
Qed.

Lemma Red_ctx_appl: forall e1 e1' e2, lc_exp e2 ->
  e1 ==>* e1' -> e_app e1 e2 ==>* e_app e1' e2.
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0.
  induction H0...
  - apply rt_refl.
  - applys rt_trans IHclos_refl_trans_1n.
    apply rt_step. constructor...
Qed.

Lemma Red_ctx_appr: forall e1 e2 e2', value e1 ->
  e2 ==>* e2' -> e_app e1 e2 ==>* e_app e1 e2'.
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0.
  induction H0...
  - apply rt_refl.
  - applys rt_trans IHclos_refl_trans_1n.
    apply rt_step. constructor...
Qed.



Lemma ECTyping_value: forall e t e',
  EquiTypingC  nil e t e' -> value e ->
  exists v', e' ==>* v' /\ value v' /\
   EquiTypingC nil e t v'. (* <---- This is important! *)
Proof with auto.
  introv Hty Hval.
  inductions Hty...
  - eexists. repeat split.
    + apply rt_refl.
    + constructor...
    + constructor...
  - inv Hval.
  - inv Hval. eexists;repeat split;[apply rt_refl| |].
    + constructor...
      pick_fresh x. specialize_x_and_L x L.
      forwards (?&?): EquiTypingC_sem H.
      get_lc... apply lc_e_abs_exists with (x1:=x)...
    + apply ECTyping_abs with (L:=L)...
  - inv Hval...
  - gen e e'. inductions H;intros.
    (* + inv H. *)
    + forwards (v' & ? & ? & ?): IHHty Hval...
      exists v'. split...
      applys rt_trans (e_cast c_id v').
      2:{ apply rt_step. constructor... }
      applys Red_ctx_cast...
    +
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      exists (e_cast (c_arrow c1 c2) v')...
      repeat split...
      * applys Red_ctx_cast...
      * applys ECTyping_eq Hty1...
    + 
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      forwards (?&?): EquiTypingC_sem Hty1.
      forwards (v''&?): canonical_form_mu H3... subst v'.
      inv H2. exists v''. repeat split...
      * applys rt_trans (e_cast (c_unfold (t_mu A)) (e_cast (c_fold (t_mu A)) v'')).
        { applys Red_ctx_cast... }
        apply rt_step. constructor...
      * inv Hty1. inv H13...
    +
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      exists (e_cast (c_fold (t_mu A)) v')...
      repeat split...
      * applys Red_ctx_cast...
      * apply ECTyping_eq with (A:=unfold_mu A)...
    + 
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      forwards (v1 & ? & ? & ?): IHTypCast1 Hty1...
      { intros. exists v'... repeat split... apply rt_refl. }
      assert (Hty': EquiTypingC nil  e B (e_cast c1 v')).
      { applys ECTyping_eq A... }
      forwards (v2 & ? & ? & ?): IHTypCast2 Hty'...
      { intros. exists v1... }
      exists v2. split...
      applys rt_trans (e_cast c2 (e_cast c1 v'))...
      applys rt_trans (e_cast (c_seq c1 c2) v')...
      2:{ apply rt_step. constructor... }
      applys Red_ctx_cast...
    +
      inv H2.
    +
      assert (Heqec: 
        TypCast nil nil (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2))).
      { apply TCast_fix with (L:=L)... }
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      exists (e_cast (c_arrow 
                (open_castop_wrt_castop c1 (c_fixc (c_arrow c1 c2)))
                (open_castop_wrt_castop c2 (c_fixc (c_arrow c1 c2)))) v')...
      repeat split...
      * applys rt_trans (e_cast (c_fixc (c_arrow c1 c2)) v').
        { applys Red_ctx_cast... }
        apply rt_step. constructor...
      * constructor...
        { apply lc_body_castop_wrt_castop...
          get_lc. inv H7. intro cx.
          specialize (H18 cx). inv H18. }
        { apply lc_body_castop_wrt_castop...
          get_lc. inv H7. intro cx.
          specialize (H18 cx). inv H18. }
      * apply ECTyping_eq with (A:=t_arrow A1 B1)...
        pick_fresh cx. specialize_x_and_L cx L.
        rewrite castsubst_castop_intro with (cx1:=cx) (c1:=c1)...
        rewrite castsubst_castop_intro with (cx1:=cx) (c1:=c2)...
        replace (   (c_arrow
        (castsubst_castop (c_fixc (c_arrow c1 c2)) cx
           (open_castop_wrt_castop c1 (c_var_f cx)))
        (castsubst_castop (c_fixc (c_arrow c1 c2)) cx
           (open_castop_wrt_castop c2 (c_var_f cx))))) with 
        (castsubst_castop (c_fixc (c_arrow c1 c2)) cx 
            (c_arrow (open_castop_wrt_castop c1 (c_var_f cx))
            (open_castop_wrt_castop c2 (c_var_f cx))))...
        rewrite_alist (@nil (atom * (typ * typ)) ++ nil).
        applys subst_castop... 2:{ apply Heqec. }
        constructor...
Qed.




Lemma value_lc_exp: forall v, value v -> lc_exp v.
Proof with auto.
  introv Hval. inductions Hval...
Qed.


Lemma reduction_app: forall A e1 e1' e2 e2' A1 A2,
EquiTypingC nil (e_abs A e1) (t_arrow A1 A2) e1' ->
EquiTypingC nil e2 A1 e2' ->
value e1' -> value e2 ->
exists e', (e_app e1' e2') ==>* e' /\ EquiTypingC nil (open_exp_wrt_exp e1 e2) A2 e'.
Proof with auto.
  introv Hty1 Hty2 Hval1 Hval2.
  gen e2 e2'. inductions Hty1;intros.
  - 
    clear H0.
    forwards (v2' & Hred2 & Hval2' & Hty2'): ECTyping_value Hty2...
    forwards (Hty2e' & Hty2i'): EquiTypingC_sem Hty2'.
    forwards (Hty2e & Hty2i): EquiTypingC_sem Hty2.
    exists (open_exp_wrt_exp e' v2'). split.
    {
      applys rt_trans (e_app (e_abs A1 e') v2'). 
      { applys Red_ctx_appr... }
      constructor. constructor... { apply value_lc_exp... }
    }
    { pick_fresh X. specialize_x_and_L X L.
      rewrite subst_exp_intro  with (x1:=X) (e1:=e1)...
      rewrite subst_exp_intro  with (x1:=X) (e1:=e')...
      rewrite_alist (@nil (atom * typ) ++ nil ).
      apply ECTyping_subst with (A:=A1)...
    }
  -
    (* assert (exists B1 B2, A0 = t_arrow B1 B2) by admit.
    destruct H0 as [B1 [B2 ?]]. subst. *)
    forwards (v2' & Hred2 & Hval2' & Hty2'): ECTyping_value Hty2...
    forwards (Hty2e' & Hty2i'): EquiTypingC_sem Hty2'.
    forwards (Hty2e & Hty2i): EquiTypingC_sem Hty2.
    inv H; try solve [inv Hval1]. inv Hval1.
    lets: IHHty1 Hval2...
    assert (EquiTypingC nil e2 A3 (e_cast (rev_cast c1) v2')). 
    { eapply ECTyping_eq. apply Hty2'. apply TypCast_symm2 in H5... }
    forwards (v'' & Hred' & Hty'): H0 H1...
    exists (e_cast c2 v'').
    split.
    +
      applys rt_trans (e_app (e_cast (c_arrow c1 c2) e') v2').
      { applys Red_ctx_appr... }
      applys rt_trans (e_cast c2 (e_app e' (e_cast (rev_cast c1) v2'))).
      { constructor. constructor... }
      applys Red_ctx_cast...
    +
      eapply ECTyping_eq;eassumption.
Qed.

Inductive equi_expr: exp -> Prop :=
| ee_lit : forall i, equi_expr (e_lit i)
| ee_var_f : forall x, equi_expr (e_var_f x)
| ee_abs : forall A e, 
    forall x, (equi_expr (open_exp_wrt_exp e (e_var_f x))) -> 
      equi_expr (e_abs A e)
| ee_app : forall e1 e2, equi_expr e1 -> equi_expr e2 -> equi_expr (e_app e1 e2)
.

Lemma ECTyping_equi_expr_lc: forall G e t e',
  EquiTypingC G e t e' -> equi_expr e.
Proof with auto.
  introv Hty.
  inductions Hty...
  - constructor...
  - constructor...
  - pick_fresh x. specialize_x_and_L x L. 
    apply ee_abs with (x:=x)...
  - constructor...
Qed.

Theorem reduction_e2i: forall e1 e1' e2 t,
  EquiTypingC nil e1 t e1' ->
  Reduction e1 e2 ->
  exists e2', e1' ==>* e2' /\ EquiTypingC nil e2 t e2'.
Proof with auto.
  introv Hty Hred.
  gen e1' t. induction Hred;intros; try solve [inductions Hty]...
  -
    inductions Hty.
    + clear IHHty1. clear IHHty2.
      forwards (v1' & Hred1 & Hval1' & Hty1'): ECTyping_value Hty1...
      forwards (Hty1e' & Hty1i'): EquiTypingC_sem Hty1'.
      forwards (v'' & Hred' & Hty'): reduction_app Hty1' Hty2...
      exists v''. split...
      { applys rt_trans Hred'. applys Red_ctx_appl... }
    + forwards* (e2' & Hred' & Hty'): IHHty.
      exists (e_cast c e2'). split.
      { applys Red_ctx_cast... }
      { eapply ECTyping_eq;eassumption. }
  -
    inductions Hty.
    + forwards* (e1'' & Hred' & Hty'): IHHred.
      exists (e_app e1'' e2'). split.
      { applys Red_ctx_appl... }
      { eapply ECTyping_app. apply Hty'. apply Hty2. }
    + forwards* (e'' & Hred' & Hty'): IHHty. { apply IHHred. }
      exists (e_cast c e''). split.
      { applys Red_ctx_cast... }
      { eapply ECTyping_eq;eassumption. }
  -
    inductions Hty.
    + 
      forwards (v1' & Hred1 & Hval1' & Hty1'): ECTyping_value Hty1...
      forwards* (e2'' & Hred' & Hty'): IHHred.
      exists (e_app v1' e2''). split.
      { applys rt_trans (e_app v1' e2'0). applys Red_ctx_appl...
        applys Red_ctx_appr... } { eapply ECTyping_app;eassumption. }
    + forwards* (e'' & Hred' & Hty'): IHHty. { apply IHHred. }
      exists (e_cast c e''). split.
      { applys Red_ctx_cast... } { eapply ECTyping_eq;eassumption. }
  -
    forwards Hequi: ECTyping_equi_expr_lc Hty.
    inverts Hequi as He1 He2.
    inv He1.
  -
    forwards Hequi: ECTyping_equi_expr_lc Hty.
    inv Hequi.
  -
    forwards Hequi: ECTyping_equi_expr_lc Hty.
    inv Hequi.
  -
    forwards Hequi: ECTyping_equi_expr_lc Hty.
    inv Hequi.
  -
    forwards Hequi: ECTyping_equi_expr_lc Hty.
    inv Hequi.
  -
    forwards Hequi: ECTyping_equi_expr_lc Hty.
    inv Hequi.
Qed.


(*************************************************************************************************************************)
(* Semantic Equivalence to the equi-recursive type system *)


Theorem erase_reduction: forall e t e' v,
  EquiTypingC nil e t e' ->
  e ==>* v -> value v ->
  exists v', e' ==>* v' /\ EquiTypingC nil v t v' 
  (* /\ value v' *)
  .
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0. gen e'.
  induction H0;intros.
  -
    exists e'. repeat split...
    apply rt_refl...
  -
    forwards: reduction_e2i H2 H.
    destruct H3 as [e1 [Hred1 Hty1]].
    forwards [v' [Hred2 Hty2]]: IHclos_refl_trans_1n Hty1...
    exists v'. repeat split...
    eapply rt_trans;eassumption.  
Qed.

(* i.e. ~ terminate *)
Definition diverge (e:exp) : Prop :=
  ~ (exists v, value v /\ e ==>* v).

Theorem reductions_i2e: forall e v,
  (* value v -> *)
  e ==>* v ->
  erase e ==>* erase v.
Proof with auto.
  introv Hred. 
  induction Hred.
  - apply reduction_i2e in H...
  - apply rt_refl.
  - apply rt_trans with (y:=erase y)...
Qed.


Theorem erase_diverge: forall e t e',
  EquiTypingC nil e t e' ->
  diverge e -> diverge e'.
Proof with auto.
  (* cofix IH. *)
  intros. intros Hc.
  apply H0. destruct Hc as [v [Hval Hred]].
  exists (erase v). split...
  apply erase_typing in H. subst.
  apply reductions_i2e in Hred...
Qed.

Theorem behavior_equiv_ter: forall e t e',
  EquiTypingC nil e t e' ->
  (terminate e <-> terminate e').
Proof with auto.
  intros.
  split;intros.
  + destruct H0 as [v [? ?]].
    forwards (v' & ? &?) : erase_reduction H H1...
    forwards (v'' & ? & ? & ?): ECTyping_value H3 H0...      
    exists v''. split...
    { apply rt_trans with (y:=v')... }
  + destruct H0 as [v [? ?]].
    forwards: erase_typing H.
    forwards: reductions_i2e H1...
    forwards: erase_value H0...
    exists (erase v). subst. split...
Qed.

Theorem behavior_equiv: forall e t e',
  EquiTypingC nil e t e' ->
  (terminate e <-> terminate e') /\
  (diverge e <-> diverge e').
Proof with auto.
  intros.
  split.
  - apply behavior_equiv_ter in H...
  - 
    forwards: behavior_equiv_ter H.
    split;intros Hd;intros Hc;apply Hd;apply H0...
Qed.