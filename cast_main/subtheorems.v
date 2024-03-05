Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.
Require Import Relation_Operators.
Require Import Operators_Properties.

Require Export preservation.


(*************************************************************************************************************************)
(* Subterms *)

Lemma TDSubTerm_trans: forall A B C,
  SynSub A B -> SynSub B C -> SynSub A C.
Proof with auto.
  introv Hs1 Hs2. gen A.
  inductions Hs2;intros...
Qed.

Lemma BUSubTerm_regular: forall A B,
  BtmUpSub A B -> lc_typ A /\ lc_typ B.
Proof with auto.
  intros.
  inductions H...
  - pick_fresh X. specialize_x_and_L X L. destruct_hypos. 
    split.
    + apply lc_body_typ_wrt_typ...
      admit.
      eapply lc_t_mu_exists;eassumption.
    + eapply lc_t_mu_exists;eassumption.
  - destruct_hypos...
  - destruct_hypos...
(* Qed. *)
Admitted.

Lemma BUSubTerm_subst_refl: forall X A B C, 
  lc_typ C -> BtmUpSub A B ->
  BtmUpSub (typsubst_typ C X A) (typsubst_typ C X B).
Proof with auto.
  introv Hlc Hsub. gen C.
  inductions Hsub;intros...
  - constructor... apply typsubst_typ_lc_typ...
  - simpl.
    rewrite typsubst_typ_open_typ_wrt_typ...
    apply BSub_unfold with (L:=L \u {{ X}})...
    intros.
    specialize_x_and_L X0 L.
    rewrite typsubst_typ_open_typ_wrt_typ_var...
    rewrite typsubst_typ_open_typ_wrt_typ_var...
  - simpl. apply BSub_arrowL...
    apply typsubst_typ_lc_typ...
  - simpl. apply BSub_arrowR...
    apply typsubst_typ_lc_typ...
Qed.




Lemma BUSubTerm_subst_inv: forall A B C X, 
  lc_typ B -> lc_typ C -> X `notin` typefv_typ C \u typefv_typ A ->
  BtmUpSub A (typsubst_typ C X B) ->
  BtmUpSub A C \/ exists A', A = typsubst_typ C X A' /\ BtmUpSub A' B.
(* Proof with auto.
  introv Hlc Hfv Hsub. inductions Hsub.
  - right. exists *)

Proof with auto.
  introv Hlc HlcC Hfv Hsub. gen A C X.
  inductions Hlc;intros.
  - simpl in Hsub. destruct (X == X0)...
    inv Hsub. right.
    exists (t_var_f X).
    simpl... destruct (X == X0)... { exfalso... }
  - simpl in Hsub. inv Hsub.
    right. exists t_int...
  - simpl in Hsub. inv Hsub.
    right. exists t_top...
  - simpl in Hsub. inv Hsub.
    + right. exists (t_arrow A B)...
    + forwards [|(A' &?&?)]: IHHlc1 H3...
      subst. right. exists A'...
    + forwards [|(A' &?&?)]: IHHlc2 H3...
      subst. right. exists A'...
  - 
    simpl in Hsub. inverts keep Hsub.
    + right. exists (t_mu A)...
    + 
      assert (X`notin` typefv_typ A1).
      {  forwards: typefv_typ_open_typ_wrt_typ_lower A1 
            (t_mu (typsubst_typ C X A)). fsetdec. }
      pick_fresh X'.
      forwards H3': H3 X'...
      rewrite typsubst_typ_open_typ_wrt_typ_var in H3'...
      forwards [|(A'&?&?)]: H0 H3'...
      { rewrite typefv_typ_open_typ_wrt_typ_upper... }
      { left. forwards (?&?): BUSubTerm_regular H2.
        rewrite typsubst_typ_intro with (X1:=X')...
        assert (typsubst_typ (t_mu (typsubst_typ C X A)) X' C = C)...
        { apply typsubst_typ_fresh_eq... }
        rewrite <- H6 at 2.
        apply BUSubTerm_subst_refl...
        apply BUSubTerm_regular in Hsub. destruct_hypos... }

      { subst. right. 
        exists (open_typ_wrt_typ (close_typ_wrt_typ X' A') (t_mu A)). split.
        + rewrite typsubst_typ_open_typ_wrt_typ...
          f_equal. rewrite typsubst_typ_close_typ_wrt_typ...
          rewrite <- H2. rewrite close_typ_wrt_typ_open_typ_wrt_typ...
        +
          (* forwards: BUSubTerm_subst_refl X C H4. admit.
          rewrite <- H2 in H5. *)
          apply BSub_unfold with (L:=L \u {{X}} \u {{X'}})...
          intros. rewrite <- typsubst_typ_spec.
          rewrite typsubst_typ_intro with (X1:=X') (A1:=A)...
          apply BUSubTerm_subst_refl...
      }
Qed.


(*************************************************************************************************************************)
(* Alternative Tyeq formulation *)


Fixpoint isContra (m:mode) (t:typ) :=
  match m with
  | m_pos =>
      (* is Contra *)
      match t with
      | t_arrow t1 t2 => isContra m_neg t1 && isContra m_neg t2
      | t_mu t' => isContra m_pos t'
      | t_var_f _ => false
      | t_var_b _ => false
      | _ => true
      end
  | m_neg =>
      (* is Rec *)
      match t with
      | t_arrow t1 t2 => isContra m_neg t1 && isContra m_neg t2
      | t_mu t' => isContra m_pos t'
      | t_var_f _ => true
      | t_var_b _ => true
      | _ => true
      end
  end.



Fixpoint lmc (t: typ) :=
  match t with
  | t_mu A => 1 + lmc A
  | _ => 1
  end.



Inductive algS : list (atom * (typ * typ)) -> typ -> typ -> castop -> Prop :=
| as_var : forall E X, algS E X X c_id
| as_int : forall E, algS E t_int t_int c_id
| as_top : forall E, algS E t_top t_top c_id
| as_unfold: forall E A B c,
    algS E (unfold_mu A) B c ->
    algS E (t_mu A) B (c_seq (c_unfold (t_mu A)) c)
| as_fold :  forall E A B c,
    algS E B (unfold_mu A) c ->
    algS E B (t_mu A) (c_seq c (c_fold (t_mu A)))
| as_assump: forall E A B cx,
    binds cx (A, B) E ->
    algS E A B (c_var_f cx)
| as_arr: forall L E A1 A2 B1 B2 c1 c2,
    (forall cx', ~ binds cx' ((t_arrow A1 A2), (t_arrow B1 B2)) E) ->
    (forall cx , cx \notin  L  -> 
        algS ((cx, ((t_arrow A2 B2),  (t_arrow A1 B1))) :: reverse_E E) A2 A1  (open_castop_wrt_castop c1 (c_var_f cx))) ->
    (forall cx , cx \notin  L  -> 
        algS ((cx, ((t_arrow A1 B1),  (t_arrow A2 B2))) :: E) B1 B2  (open_castop_wrt_castop c2 (c_var_f cx))) -> 
    algS E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2))
.

#[global]
Hint Constructors algS : core.



Lemma algS_decidable: forall E A B,
  {c:castop | algS E A B c } + (forall c, ~ algS E A B c).
Proof with auto.
  intros.
Admitted.
  

Lemma algS_refl: forall E A,
  algS E A A c_id.
Admitted.


(* Still need a down ward decreasing measure to prove *)
Lemma algS_trans: forall E A B C c1 c2,
  algS E A B c1 -> algS E B C c2 ->
  exists c', algS E A C c'.
Proof with auto.
  intros. gen C c2.
  inductions H;intros.
  - exists c2...
  - exists c2...
  - exists c2...
  - forwards (c'&?): IHalgS H0...
    exists (c_seq (c_unfold (t_mu A)) c')...
  - inductions H0.
    + exists (c_seq c (c_fold (t_mu A)))...
    + forwards (c'&?): IHalgS H0... exists c'...
    + 
      forwards (c'&?): IHalgS0 H...
      exists (c_seq c' (c_fold (t_mu A0)))...
    +
      admit. (* no mu in env *)
  -
    inductions H0.
    + exists (c_var_f cx)...
    + admit.
    + admit.
    + admit.
    + forwards (c'&?): IHalgS H.
      exists (c_seq c' (c_fold (t_mu A0)))...
    +
       (* if cx A <: B in E and cx <: B = C in E then cx <: A <: C in E *)
       (* problematic *)
       admit.
    +
      admit.

Admitted.



Lemma eqe_algS: forall E A B c, 
  eqec E A B c ->
  algS E A B c.
Proof.
  intros. inductions H...
  - admit.
  - apply algS_refl.
  - 
  
(* Qed. *)
Admitted.




CoInductive Tyeq' : typ -> typ -> Prop :=
| Tyeq_var' : forall X, Tyeq' (t_var_f X) (t_var_f X)
| Tyeq_int' : Tyeq' t_int t_int
| Tyeq_top' : Tyeq' t_top t_top
| Tyeq_arr' : forall A1 A2 B1 B2,
    Tyeq' A1 B1 -> Tyeq' A2 B2 -> Tyeq' (t_arrow A1 A2) (t_arrow B1 B2)
| Tyeq_mul' : forall A B,
    (* isContra m_pos A = true -> *)
    Tyeq' (unfold_mu A) B -> Tyeq' (t_mu A) B
| Tyeq_mur' : forall A B,
    (* isContra m_pos B = true -> lmc A = 0 -> *)
    Tyeq' A (unfold_mu B) -> Tyeq' A (t_mu B).

#[global]
Hint Constructors Tyeq' Tyeq: core.


Lemma Tyeq'_trans: forall A B C,
  Tyeq' A B -> Tyeq' B C -> Tyeq' A C.
Admitted.

Lemma Tyeq'_refl: forall A, Tyeq' A A.
Admitted.

Lemma Tyeq'_symm: forall A B, Tyeq' A B -> Tyeq' B A.
Admitted.

Theorem Tyeq'_Tyeq: forall A B, Tyeq' A B -> Tyeq A B.
Proof with auto.
  cofix IH.
  intros. inv H.
  - apply Tyeq_refl.
  - apply Tyeq_refl.
  - apply Tyeq_refl.
  - apply Tyeq_arrow; apply IH; assumption.
  - eapply Tyeq_trans. { apply Tyeq_mu_l. } apply IH. assumption.
  - eapply Tyeq_trans. 2:{ apply Tyeq_mu_r. } apply IH. assumption.
Qed.



Inductive WHNF_eqWi' (R: typ -> typ -> Prop): typ -> typ -> Prop :=
| wh'_done: forall t1 t2, Tyeq' t1 t2 -> WHNF_eqWi' R t1 t2
| wh'_arrow: forall t1 t2 t1' t2',
    R t1 t1' -> (* coinductive WHNF_eqP *)
    R t2 t2' ->
    WHNF_eqWi' R (t_arrow t1 t2) (t_arrow t1' t2')
| wh'_trans: forall t1 t2 t3, 
    WHNF_eqWi' R t1 t2 -> 
    WHNF_eqWi' R t2 t3 -> 
    (* R t1 t2 ->
    R t2 t3 -> *)
    WHNF_eqWi' R t1 t3
.

#[export]
Hint Constructors WHNF_eqWi' : core.

CoInductive WHNF_eqW' : typ -> typ -> Prop :=
| wh_introw: forall (R: typ -> typ -> Prop),
    (forall t1 t2, R t1 t2 -> R t2 t1) ->
    (forall t1 t2 t3, R t1 t2 -> R t2 t3 -> R t1 t3) ->
    (forall t1 t2, R t1 t2 -> 
      ( WHNF_eqW' t1 t2)) ->
    forall t1 t2,
      WHNF_eqWi' R t1 t2 ->
      WHNF_eqW' t1 t2.


Lemma WHNF_eqW'_trans: forall A B C,
  WHNF_eqW' A B -> WHNF_eqW' B C -> WHNF_eqW' A C.
Proof with auto.
  
Admitted.




Lemma Tyeq_Tyeq'_aux: forall A B, Tyeq A B -> WHNF_eqW' A B.
Proof.
  cofix IH.
  pose proof (wh_introw Tyeq Tyeq_symm Tyeq_trans IH) as rule.
  intros. inv H.
  - apply rule. apply wh'_arrow;auto.
  - apply rule.
    apply wh'_done. apply Tyeq_mul'. apply Tyeq'_refl.
  - apply rule.
    apply wh'_done. apply Tyeq_mur'. apply Tyeq'_refl.
  - apply rule.
    apply wh'_done. apply Tyeq'_refl.
  -
    apply wh_introw with (R:=WHNF_eqW').
    (* 4:{ 
    eapply wh'_trans with (t2:=t2); auto. *)
(* Qed. *)
Admitted.

Lemma WHNF_eqW'_Tyeq': forall A B, WHNF_eqW' A B -> Tyeq' A B.
Proof with auto.
  cofix IH.
  intros. inv H.
  (* induction H3. *)
  inv H3.
  - auto.
  -
    forwards He1: H2 H4.
    (* forwards: Tyeq_Tyeq'_aux He1. *)
    forwards He2: H2 H5.
    (* forwards: Tyeq_Tyeq'_aux He2. *)
    apply Tyeq_arr'.
    + apply IH... 
    + apply IH...
  (* - 
    apply Tyeq'_trans with (B:=t2). Guarded.
    + apply IHWHNF_eqWi'1...
      apply (wh_introw R H0 H1 H2). apply H3_. Guarded.
    + apply IHWHNF_eqWi'2...
      apply (wh_introw R H0 H1 H2). apply H3_0.
Qed.
    

      apply wh'_done.

    forwards He: H1 H4 H5.
    forwards He': H2 He.
    forwards: Tyeq_Tyeq'_aux He'.
    apply IH... Guarded.
  
  
  inv H.
  - apply Tyeq_arr'; apply IH; assumption.
  - apply Tyeq_mul'. apply Tyeq'_refl.
  - apply Tyeq_mur'. apply Tyeq'_refl.
  - apply Tyeq'_refl.
  - apply Tyeq'_trans with (B:=t2); apply IH; assumption.
Qed. *)
Admitted.





Lemma sub_eq_commutes: forall A B C D AE,
  AmberSubtyping AE A B -> Tyeq' B C -> AmberSubtyping AE C D ->
  exists A' D', Tyeq' A A' /\ AmberSubtyping AE A' D'  /\ Tyeq' D' D.
Proof with auto.
  intros.
  (* eapply sub_eq_commutes_aux with (B:=B) (C:=C) (B':=B) (C':=C)...
  apply SSub_refl. admit. apply SSub_refl. admit. *)
  inv H0.
  - inv H; inv H1.
    + exists (t_var_f X0), t_top. repeat split...
      apply ASub_top... admit.
    + admit. (* break well formedness *)
  - inv H; inv H1.
    + exists t_int, t_int. repeat split...
    + exists t_int, t_top. repeat split...
  - inv H; inv H1.
    + exists A, t_top. repeat split...
      apply Tyeq'_refl...
   - inv H; inv H1.
    + exists (t_arrow A0 A3), t_top. repeat split...
      { apply Tyeq'_refl... }
      { apply ASub_top... admit. }
    + 
      (* by IH *)
      admit.
  - inv H.
    + forwards: unfolding_lemma H.
      (* assert (H4a: Tyeq' (unfold_mu A0) C).
      { applys Tyeq'_trans H0.
        applys Tyeq'_symm.
        eapply Tyeq_mul'...
        apply Tyeq'_refl. } *)
      assert (exists A'' D'', Tyeq' (unfold_mu A1) A'' /\ AmberSubtyping AE A'' D'' /\ Tyeq' D'' D).
      { admit. }
      (* apply an IH on H2 *)
      destruct H4 as [A'' [D'' [? [? ?]]]].
      exists A'' D''. repeat split...
      (* { applys Tyeq_mul'... admit. preserve contract } *)
    + exists C D. repeat split...
      { apply Tyeq'_refl. }
  - inv H1.
    + exists A, t_top. repeat split...
      { apply Tyeq'_refl... }
      { apply ASub_top... admit. }
    + forwards: unfolding_lemma H1.
      (* assert (H5a: Tyeq' B (unfold_mu B0)).
      { applys Tyeq'_trans H0.
        eapply Tyeq_mul'...
        apply Tyeq'_refl. } *)
      assert (exists A'' D'', Tyeq' A A'' /\ AmberSubtyping AE A'' D'' /\ Tyeq' D'' (unfold_mu B1)).
      { admit. }
      (* apply and IH on H2 *)
      destruct H4 as [A'' [D'' [? [? ?]]]].
      exists A'' D''. repeat split...
      (* {  apply Tyeq'_symm. applys Tyeq_mul'... admit. (* preserve contract *) 
        apply Tyeq'_symm... } *)
    + exists A B. repeat split...
      { apply Tyeq'_refl. }
Admitted.



(* Lemma sub_eq_commutes_aux: forall B C,
forall B' C', SynSub B' B -> SynSub C' C ->
forall A D AE, 
AmberSubtyping AE A B -> Tyeq' B' C' -> AmberSubtyping AE C D ->
exists A' D', Tyeq' A A' /\ AmberSubtyping AE A' D'  /\ Tyeq' D' D.
Proof with auto.
  introv Hss1 Hss2 Hsub1 Heq Hsub2.
  gen C' A D AE.
Admitted. *)


(* 


Inductive unfolded_typ : typ -> Prop :=
| ut_top: unfolded_typ t_top
| ut_int: unfolded_typ t_int
| ut_var: forall X, unfolded_typ (t_var_f X)
| ut_arrow: forall A B, unfolded_typ (t_arrow A B)
.

Inductive ufd_or_mu: typ -> Prop :=
| um_ufd: forall A, unfolded_typ A -> ufd_or_mu A
| um_mu: forall A1 A2,
    ufd_or_mu (unfold_mu (t_arrow A1 A2)) -> ufd_or_mu (t_mu (t_arrow A1 A2)).

 *)
(* 

Lemma typ_is_ufd_or_mu: forall A, 
  lc_typ A ->  isContra m_pos A = true -> ufd_or_mu A.
Proof with auto.
  intros. inductions H;intros...
  - constructor... constructor...
  - constructor... constructor...
  - constructor... constructor...
  - constructor... constructor...
  - pply mu. *)



  Lemma BU_TD_SubTerm: forall A B,
  SynSub A B -> BtmUpSub A B.
Proof with auto.
  intros.
  induction H...
  +
    pick_fresh X.
    rewrite typsubst_typ_intro with (X1:=X) in IHSynSub...
    apply BUSubTerm_subst_inv in IHSynSub... 2:{ admit. } 2:{ admit. }
    destruct IHSynSub...
    destruct H0 as [A' [? ?]]. subst.
    rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (A1:=A') (X1:=X)...
    rewrite <- typsubst_typ_intro... 2:{ 
        rewrite typefv_typ_close_typ_wrt_typ... }
    apply BSub_unfold with (L:={{X}})...
    intros. rewrite <- typsubst_typ_spec.
    forwards: BUSubTerm_subst_refl X (t_var_f X0) H1...
    rewrite <- typsubst_typ_intro in H2...
Admitted.




Lemma AmberWFT_lc: forall AE A,
  AmberWFT AE A ->
  lc_typ A.
Proof with auto.
  intros.
  inductions H...
Qed.

#[global]
Hint Resolve AmberWFT_lc : core.

Lemma AmberSub_i2e: forall AE A B,
  AmberSubtyping AE A B ->
  ACSubtyping AE A B.
Proof with auto.
  intros.
  inductions H...
  - apply ACSub_top. applys* AmberWFT_lc.
  - forwards (AE1&AE2&?): in_split H0.
    subst. applys* ACSub_assump...
  - apply ACSub_rec with (L:=L)...
  (* - apply ACSub_refl. applys* AmberWFT_lc. *)
Qed.



Lemma ASub_refl: forall D A, AmberWF D -> AmberWFT D A -> AmberSubtyping D A A.
Admitted.



