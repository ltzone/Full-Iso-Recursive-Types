Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.


Require Export preservation.


Inductive wfe2: tctx -> list (typ * typ) -> Prop :=
| wfe2_nil: forall D, wfe2 D nil
| wfe2_cons: forall D E t1 t2,
    wfe2 D E -> 
    eqe2 D E t1 t2 -> 
    wfe2 D ((t1,t2)::E).


Lemma ty_dec: forall (t1 t2:typ), {t1 = t2} + {t1 <> t2}.
Proof with auto.
  decide equality.
  apply eq_nat_dec.
Qed.

Lemma ty_pair_dec: forall (t1 t2:typ*typ), {t1 = t2} + {t1 <> t2}.
Proof with auto.
  decide equality.
  - apply ty_dec.
  - apply ty_dec.
Qed.


Inductive eqe2_trans: tctx -> list (typ * typ) -> typ -> typ -> list (typ * typ)  -> Prop :=
| e2t_assump1: forall D E t1 t2,
    In (t1,t2) E ->
    WFT D t1 ->
    WFT D t2 ->
    eqe2_trans D E t1 t2 [(t1,t2)]
| e2t_refl: forall D E t, WFT D t -> eqe2_trans D E t t nil
| e2t_trans: forall D E t1 t2 t3 E1 E2,
    eqe2_trans D E t1 t2 E1 ->
    eqe2_trans D E t2 t3 E2 ->
    eqe2_trans D E t1 t3 (E1 ++ E2)
| e2t_symm: forall D E t1 t2 E',
    eqe2_trans D E t1 t2 E' -> eqe2_trans D E t2 t1 (reverse_A E')
| e2t_fld: forall D E t (Hwf: WFT D (t_mu t)),
    eqe2_trans D E (t_mu t) 
          (unfold_mu t) nil
| e2t_arrfix: forall D E t1 t2 t1' t2' E1 E2
    (Hnotin: ~ In (t_arrow t1 t2, t_arrow t1' t2') E),
    eqe2_trans D ((t_arrow t1 t2, t_arrow t1' t2'):: E) t1 t1' E1 -> 
    eqe2_trans D ((t_arrow t1 t2, t_arrow t1' t2'):: E) t2 t2' E2 ->
    eqe2_trans D E (t_arrow t1 t2) (t_arrow t1' t2') 
     (List.remove ty_pair_dec (t_arrow t1' t2', t_arrow t1 t2)
      (List.remove ty_pair_dec (t_arrow t1 t2, t_arrow t1' t2') (E1 ++ E2)))
.

#[export]
Hint Constructors eqe2_trans: core.

Lemma eqe_env_cong: forall D E1 E2 t1 t2, 
  eqe D E1 t1 t2 -> 
  (forall t1' t2', In (t1',t2') E1 -> In (t1',t2') E2) ->
  eqe D E2 t1 t2.
Proof with auto.
  intros. gen E2.
  inductions H;intros...
  - apply e_trans with (B:=B)...
  - apply e_arrfix...
    + apply IHeqe1...
      intros.
      { destruct H3. inv H3. left... right. apply H2... }
    + apply IHeqe2...
      intros.
      { destruct H3. inv H3. left... right. apply H2... }
Qed.


Lemma eqe2_env_cong: forall D E1 E2 t1 t2, 
  eqe2 D E1 t1 t2 -> 
  (forall t1' t2', In (t1',t2') E1 -> In (t1',t2') E2) ->
  eqe2 D E2 t1 t2.
Proof with auto.
  intros. gen E2.
  inductions H;intros...
  - apply e2_trans with (B:=B)...
  - apply e2_arrfix...
    + apply IHeqe2_1...
      intros.
      { destruct H3. inv H3. left... right. apply H2... }
    + apply IHeqe2_2...
      intros.
      { destruct H3. inv H3. left... right. apply H2... }
Qed.


Inductive eqe' : tctx -> list (typ * typ) -> typ -> typ -> Prop :=
| e'_assump1: forall D E t1 t2,
    In (t1,t2) E ->
    WFT D t1 ->
    WFT D t2 ->
    eqe' D E t1 t2
| e'_refl: forall D E t, WFT D t -> eqe' D E t t
| e'_trans: forall D E t1 t2 t3,
    eqe' D E t1 t2 -> eqe' D E t2 t3 -> eqe' D E t1 t3
(* | e_symm: forall E t1 t2, eqe E t1 t2 -> eqe E t2 t1 *)
| e'_fld: forall D E t (Hwf: WFT D (t_mu t)), 
    eqe' D E (t_mu t) 
          (unfold_mu t)
| e'_unfld: forall D E t (Hwf: WFT D (t_mu t)), 
    eqe' D E  
      (unfold_mu t) 
      (t_mu t) 
| e'_arrfix: forall D E t1 t2 t1' t2',
    eqe' D ((t_arrow t1' t2', t_arrow t1 t2):: (t_arrow t1 t2, t_arrow t1' t2'):: E) t1 t1' -> 
    eqe' D ((t_arrow t1' t2', t_arrow t1 t2):: (t_arrow t1 t2, t_arrow t1' t2'):: E) t2 t2' ->
    eqe' D E (t_arrow t1 t2) (t_arrow t1' t2')
.

#[export]
Hint Constructors eqe' : core.


Lemma eqe'_weakening: forall D G G1 G2 A B,
  eqe' D (G1 ++ G2) A B ->
  eqe' D (G1 ++ G ++ G2) A B.
Proof with auto.
  intros.
  inductions H;intros...
  - apply e'_assump1...
    apply in_app_or in H. apply in_or_app.
    destruct H... right.
    apply in_or_app...
  - apply e'_trans with (t2:=t2)...
  - apply e'_arrfix.
    + rewrite_alist ((((t_arrow t1' t2', t_arrow t1 t2) :: (t_arrow t1 t2, t_arrow t1' t2') :: G1) ++ G ++ G2)).
      apply IHeqe'1...
    + rewrite_alist ((((t_arrow t1' t2', t_arrow t1 t2) :: (t_arrow t1 t2, t_arrow t1' t2') :: G1) ++ G ++ G2)).
      apply IHeqe'2...
Qed.


Lemma eqe'_symm: forall D E t1 t2, eqe' D E t1 t2 -> eqe' D (reverse_A E) t2 t1.
Proof with auto.
  intros.
  inductions H...
  - apply e'_assump1...
    apply reverse_A_sem...
  - apply e'_trans with (t2:=t2)...
Qed.



Lemma eqe'_env_cong: forall D E1 E2 t1 t2, 
  eqe' D E1 t1 t2 -> 
  (forall t1' t2', In (t1',t2') E1 -> In (t1',t2') E2) ->
  eqe' D E2 t1 t2.
Proof with auto.
  intros. gen E2.
  inductions H;intros...
  - apply e'_trans with (t2:=t2)...
  - apply e'_arrfix...
    + apply IHeqe'1...
      intros.
      { destruct H2. inv H2. left...
        destruct H2. inv H2. right. left...
        right. right. apply H1... }
    + apply IHeqe'2...
      intros.
      { destruct H2. inv H2. left...
        destruct H2. inv H2. right. left...
        right. right. apply H1... }
Qed.


Lemma eqe2_trans_complete: forall D E E' t1 t2, 
  eqe2_trans D E t1 t2 E' -> 
  eqe' D E' t1 t2.
Proof with auto.
  intros.
  inductions H...
  - apply e'_assump1... constructor...
  - apply e'_trans with (t2:=t2).
    + rewrite_alist (E1 ++ E2 ++ nil).
      apply eqe'_weakening... rewrite app_nil_r...
    +
      rewrite_alist (nil ++ E1 ++ E2).
      apply eqe'_weakening...
  -
    apply eqe'_symm...
  -
    apply e'_arrfix...
    +
      apply eqe'_env_cong with (E1:=E1 ++ E2).
      2:{ intros.
          destruct (ty_pair_dec (t1'0, t2'0) (t_arrow t1' t2', t_arrow t1 t2)).
          { left... } right.
          destruct (ty_pair_dec (t1'0, t2'0) (t_arrow t1 t2, t_arrow t1' t2')).
          { left... } right. 
          apply in_in_remove...
          apply in_in_remove...
      }
      rewrite_alist (E1 ++ E2 ++ nil).
      apply eqe'_weakening... rewrite app_nil_r...
    + 
    apply eqe'_env_cong with (E1:=E1 ++ E2).
      2:{ intros.
        destruct (ty_pair_dec (t1'0, t2'0) (t_arrow t1' t2', t_arrow t1 t2)).
        { left... } right.
        destruct (ty_pair_dec (t1'0, t2'0) (t_arrow t1 t2, t_arrow t1' t2')).
        { left... } right. 
        apply in_in_remove...
        apply in_in_remove...
      }
      rewrite_alist (nil ++ E1 ++ E2).
      apply eqe'_weakening...
Qed.


Lemma eqe2_trans_sublist: forall D E E' t1 t2,
  eqe2_trans D E t1 t2 E' ->
  (forall t1' t2', In (t1',t2') E' -> In (t1',t2') (E ++ reverse_A E )).
Proof with auto.
  intros. gen t1' t2'.
  inductions H...
  6:{
    intros.
    apply in_remove in H1.
    destruct H1. apply in_or_app.
    apply in_remove in H1.
    destruct H1.
    apply in_app_or in H1. destruct H1. 
    + forwards: IHeqe2_trans1 H1. apply in_app_or in H4.
      destruct H4.
      * destruct H4... congruence.
      * destruct H4... congruence.
    + forwards: IHeqe2_trans2 H1. apply in_app_or in H4.
      destruct H4.
      * destruct H4... congruence.
      * destruct H4... congruence.
  }
  - intros. inv H2. 2:{ inv H3. } inv H3.
    apply in_or_app. left...
  - intros. inv H0.
  - intros. 
    apply in_app_or in H1.
    destruct H1...
  - intros. 
    apply reverse_A_sem in H0.
    rewrite reverse_A_reverse in H0.
    apply IHeqe2_trans in H0.
    apply reverse_A_sem in H0.
    rewrite revA_dist in H0. 
    rewrite reverse_A_reverse in H0.
    apply in_app_or in H0. apply in_or_app.
    destruct H0...
  - intros. inv H0.
Qed.

Lemma eqe2_regular: forall D E t1 t2, 
  eqe2 D E t1 t2 -> 
  WFT D t1 /\ WFT D t2.
Proof with auto.
  intros.
  inductions H...
  - destruct_hypos...
  - destruct_hypos...
  - split... inv H0.
    pick_fresh X. specialize_x_and_L X L.
    rewrite typsubst_typ_intro with (X1:=X)...
    rewrite_alist (nil ++ D).
    apply WFT_typsubst...
  - destruct_hypos...
Qed.

Lemma eqe2_eqe2_trans: forall D E t1 t2, 
  eqe2 D E t1 t2 -> exists E', eqe2_trans D E t1 t2 E'.
Proof with auto.
  intros.
  inductions H;try solve [exists E;auto].
  - exists [(A,B)]...
  - exists (@nil (typ*typ))...
  - destruct IHeqe2_1 as [E1], IHeqe2_2 as [E2].
    exists (E1 ++ E2)...
    apply e2t_trans with (t2:=B)...
  - destruct IHeqe2 as [E'].
    exists (reverse_A E')...
  - exists (@nil (typ*typ))...
  - 
    destruct (In_dec ty_pair_dec (t_arrow A1 A2, t_arrow B1 B2) H).
    +
      exists [(t_arrow A1 A2, t_arrow B1 B2)].
      apply e2t_assump1...
      { forwards (?&?): eqe2_regular H1.
        forwards (?&?): eqe2_regular H0... }
      { forwards (?&?): eqe2_regular H1.
        forwards (?&?): eqe2_regular H0... }
    + destruct IHeqe2_1 as [E1], IHeqe2_2 as [E2].
      exists (List.remove ty_pair_dec (t_arrow B1 B2, t_arrow A1 A2)
      (List.remove ty_pair_dec (t_arrow A1 A2, t_arrow B1 B2) (E1 ++ E2)))...
Qed.


Inductive wfe: tctx -> list (typ * typ) -> Prop :=
| wfe_nil: forall D, wfe D nil
| wfe_cons: forall D E t1 t2,
    wfe D E -> 
    eqe D E t1 t2 -> 
    wfe D ((t1,t2)::E).

#[export]
Hint Constructors wfe wfe2: core.




Lemma eqe_drop: forall D E1 E2 E3 t1 t2,
  eqe D (E2 ++ E1 ++ E3) t1 t2 ->
  (forall t1' t2', In (t1',t2') E1 -> eqe D (E2 ++ E3) t1' t2') ->
  eqe D (E2 ++ E3) t1 t2.
Proof with auto.
  intros.
  inductions H...
  -
    apply in_app_or in H0. destruct H0.
    * apply e_assump... apply in_or_app...
    * apply in_app_or in H. destruct H...
      apply e_assump... apply in_or_app...
  -
    apply e_trans with (B:=B)...
    + apply IHeqe1 with (E4:=E1)...
    + apply IHeqe2 with (E4:=E1)...
  -
    apply e_arrfix.
    + 
      rewrite_alist (([(t_arrow A1 A2, t_arrow B1 B2)] ++ E2) ++ E3).
      apply IHeqe1 with (E4:=E1)...
      intros. 
      rewrite_alist ( nil ++ ([(t_arrow A1 A2, t_arrow B1 B2)]) ++ (E2 ++ E3)).
      apply eqe_weakening...
    + 
      rewrite_alist (([(t_arrow A1 A2, t_arrow B1 B2)] ++ E2) ++ E3).
      apply IHeqe2 with (E4:=E1)...
      intros. 
      rewrite_alist ( nil ++ ([(t_arrow A1 A2, t_arrow B1 B2)]) ++ (E2 ++ E3)).
      apply eqe_weakening...
Qed.

Lemma wfe_sem: forall t1 t2 D E, In (t1,t2) E -> wfe D E -> eqe D nil t1 t2.
Proof with auto.
  intros.
  gen t1 t2. 
  inductions H0;intros.
  - inv H.
  - destruct H1.
    + inv H1. apply eqe_drop with (E1:=E) (E2:=nil) (E3:=nil).
      { rewrite app_nil_l... rewrite app_nil_r... } { apply IHwfe... }
    + auto.
Qed.



Inductive dual_env: list (typ * typ) -> list (typ * typ) -> Prop :=
| dual_nil: dual_env nil nil
| dual_cons: forall t1 t2 E1 E2,
    dual_env E1 E2 -> dual_env ((t2,t1)::E1) ((t1,t2)::E2)
| dual_cons2: forall t1 t2 E1 E2,
    dual_env E1 E2 -> dual_env ((t1,t2)::E1) ((t1,t2)::E2).




Lemma eqe_symm_strong: forall D E t1 t2, 
  wfe D E ->
  eqe D E t1 t2 -> 
  forall E', dual_env E E' -> eqe D E' t2 t1.
Proof with auto.
  intros. gen E'.
  inductions H0;intros...
  -
    forwards : wfe_sem H0 H1 H.
    rewrite_alist (nil ++ E' ++ nil).
    apply eqe_weakening...
    simpl. apply eqe_symm in H5...
  -
    apply e_trans with (B:=B)...
  -
    assert (wfe D ((t_arrow A1 A2, t_arrow B1 B2) :: H0)).
    { constructor... }
    specialize (IHeqe1 H2).
    specialize (IHeqe2 H2).
    apply e_arrfix.
    + apply IHeqe1...
      constructor...
    + apply IHeqe2...
      constructor...
Qed.



Lemma dual_env_refl: forall E, dual_env E E.
Proof with auto.
  intros.
  inductions E.
  constructor...
  destruct a. constructor...
Qed.

Lemma eqe_symm_strong': forall D E t1 t2, 
  wfe D E ->
  eqe D E t1 t2 -> 
  eqe D E t2 t1.
Proof with auto.
  intros. apply eqe_symm_strong with (E:=E)...
  apply dual_env_refl.
Qed.
  

Fixpoint double_A (E: list (typ * typ)) : list (typ * typ) :=
  match E with
  | nil => nil
  | (t1,t2)::E' => (t2,t1)::(t1,t2)::(double_A E')
  end.

Lemma double_A_incl: forall E t1 t2,
  In (t1,t2) E -> In (t1,t2) (double_A E).
Proof with auto.
  intros.
  inductions E... 
  destruct a. simpl.
  destruct H...
Qed.

Lemma wfe_double: forall D E, wfe D E -> wfe D (double_A E).
Proof with auto.
  intros.
  inductions H...
  simpl. constructor;[constructor|]...
  - 
    apply eqe_env_cong with (E1:=E)...
    { intros. apply double_A_incl... }
  -
    apply eqe_env_cong with (E1:=E).
    { apply eqe_symm_strong'... }
    { intros. right. apply double_A_incl... }
Qed.

Lemma in_double_A: forall E t1 t2,
  In (t1,t2) (double_A E) -> In (t1,t2) E \/ In (t2,t1) E.
Proof with auto.
  intros.
  inductions E...
  destruct a. simpl in H.
  destruct H as [? |[? |?]].
  - inv H. right. left...
  - inv H. left. left...
  - apply IHE in H. destruct H. left. right... right. right...
Qed.


Inductive wfe': list (typ * typ) -> Prop :=
| wfe'_nil:  wfe' nil
| wfe'_cons: forall E t1 t2,
    wfe' E -> 
    (* eqe' D E t1 t2 ->  *)
    wfe' ((t2,t1)::(t1,t2)::E).

#[export]
Hint Constructors wfe': core.

Lemma wfe'_reverse: forall E, wfe' E ->
  forall t1' t2', In (t1',t2') E -> In (t1',t2') (reverse_A E).
Proof with auto.
  intros.
  inductions H...
  destruct H0 as [? |[? |?]].
  - inv H0. right. left...
  - inv H0. left...
  - right. right. apply IHwfe'...
Qed.



Lemma wfe'_reverse': forall E, wfe' E ->
  forall t1' t2', In (t1',t2') (reverse_A E) -> In (t1',t2') E.
Proof with auto.
  intros.
  inductions H...
  destruct H0 as [? |[? |?]].
  - inv H0. right. left...
  - inv H0. left...
  - right. right. apply IHwfe'...
Qed.



Lemma wfe'_eqe: forall D E t1 t2, 
  wfe' E ->
  eqe' D E t1 t2 ->
  eqe D E t1 t2.
Proof with auto.
  intros.
  inductions H0;intros...
  - eapply e_trans with (B:=t2);eauto.
  - 
    assert (wfe' ((t_arrow t1' t2', t_arrow t1 t2)::(t_arrow t1 t2, t_arrow t1' t2')::E)).
    { constructor... }
    forwards: IHeqe'1 H0.
    forwards: IHeqe'2 H0.
    apply e_arrfix.
    + rewrite_alist (nil ++ ([(t_arrow t1 t2, t_arrow t1' t2')] ++ E)).
      apply eqe_drop with (E1:= [(t_arrow t1' t2', t_arrow t1 t2)]).
      { rewrite app_nil_l... }
      { intros. inv H3. 2:{ inv H4. } inv H4.
        apply e_arrfix.
        * apply eqe_symm in H1.
          applys eqe_env_cong H1.
          intros. simpl in H5. simpl.
          destruct H5... destruct H5...
          right. right. apply wfe'_reverse'...
        * apply eqe_symm in H2.
          applys eqe_env_cong H2.
          intros. simpl in H5. simpl.
          destruct H5... destruct H5...
          right. right. apply wfe'_reverse'...
      }
    + rewrite_alist (nil ++ ([(t_arrow t1 t2, t_arrow t1' t2')] ++ E)).
      apply eqe_drop with (E1:= [(t_arrow t1' t2', t_arrow t1 t2)]).
      { rewrite app_nil_l... }
      { intros. inv H3. 2:{ inv H4. } inv H4.
        apply e_arrfix.
        * apply eqe_symm in H1.
          applys eqe_env_cong H1.
          intros. simpl in H5. simpl.
          destruct H5... destruct H5...
          right. right. apply wfe'_reverse'...
        * apply eqe_symm in H2.
          applys eqe_env_cong H2.
          intros. simpl in H5. simpl.
          destruct H5... destruct H5...
          right. right. apply wfe'_reverse'...
      }
Qed.




Theorem eqe_complete: forall D  t1 t2, 
  eqe2 D nil t1 t2 -> 
  eqe D nil t1 t2.
Proof with auto.
  intros.
  forwards (E'&?):eqe2_eqe2_trans H.
  forwards: eqe2_trans_complete H0.
  lets: eqe2_trans_sublist H0.
  destruct E'. 2:{ destruct p. forwards: H2 t t0... exfalso... }
  apply wfe'_eqe in H1...
Qed.



Theorem eqe_sound: forall D E t1 t2, 
  eqe D E t1 t2 -> 
  eqe2 D E t1 t2.
Proof with auto.
  intros.
  inductions H...
  - apply e2_trans with (B:=B)...
Qed.
