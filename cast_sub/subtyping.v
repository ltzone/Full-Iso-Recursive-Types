(* The following formalizations adapt our Coq development to 
   the Coq development of "Revisiting Iso-recursive Subtyping"
*)
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import subtyping.AmberLocal.
(* Require Import subtyping.Decidability. *)
Require Export rules_inf.
Require Export LibTactics.
Require Import Lia.


(* Relating our types to TOPLAS types *)

Fixpoint trans_ty (A : typ) : Rules.typ :=
  match A with
  | t_top => typ_top
  | t_int => typ_nat
  | t_arrow A1 A2 =>
      typ_arrow (trans_ty A1) (trans_ty A2)
  | t_var_f X => typ_fvar X
  | t_var_b n => typ_bvar n
  | t_mu A => typ_mu (trans_ty A)
  end.

Fixpoint back_ty (A : Rules.typ) : typ :=
  match A with
  | typ_top => t_top
  | typ_nat => t_int
  | typ_arrow A1 A2 =>
      t_arrow (back_ty A1) (back_ty A2)
  | typ_fvar X => t_var_f X
  | typ_bvar n => t_var_b n
  | typ_mu A => t_mu (back_ty A)
  end.

Lemma AmberdomA_IsodomA: forall AE,
  domA AE [=] AmberBase.domA AE.
Proof.
  intros.
  induction AE; simpl; eauto.
  - reflexivity.
  - destruct a. fsetdec.
Qed.
  

Lemma AmberWF_Isowfe: forall AE,
  AmberWF AE <-> wfe_amber AE.
Proof with auto.
  intros. split;intro.
  + induction H; simpl; eauto.
  + induction H; simpl; eauto.
Qed.


#[export]
Hint Extern 1 (AmberWF ?AE) =>
  match goal with
  | H: wfe_amber AE |- _ => apply AmberWF_Isowfe in H
  end : core.

#[export]
Hint Extern 1 (wfe_amber ?AE) =>
  match goal with
  | H: AmberWF AE |- _ => apply AmberWF_Isowfe in H
  end : core.

Lemma trans_ty_open_typ_wrt_typ: forall A X, degree_typ_wrt_typ 1 A ->
  trans_ty (open_typ_wrt_typ A (t_var_f X)) = open_tt (trans_ty A) X.
Proof with auto.
  intros. unfold open_typ_wrt_typ.
  unfold open_tt.
  revert H.
  generalize 0. intros.
  inductions H;intros...
  - 
    simpl. destruct (lt_eq_lt_dec n2 n) as [[?|?]|?].
    + simpl. destruct (n == n2);try lia...
    + subst. simpl. destruct (n == n);try lia...
    + simpl. destruct (n == n2);try lia...
  - simpl. rewrite IHdegree_typ_wrt_typ1... 
    rewrite IHdegree_typ_wrt_typ2...
  - simpl. f_equal.
    rewrite IHdegree_typ_wrt_typ...
Qed.

Lemma trans_back_ty: forall A,
  trans_ty (back_ty A) = A.
Proof with auto.
  inductions A;simpl...
  - rewrite IHA...
  - rewrite IHA1;rewrite IHA2...
Qed.

Lemma back_trans_ty: forall A,
  back_ty (trans_ty A) = A.
Proof with auto.
  inductions A;simpl...
  - rewrite IHA1;rewrite IHA2...
  - rewrite IHA...
Qed.



Lemma back_ty_open_tt: forall A (X:atom),
  WFC A 1 ->
  back_ty (open_tt A X) = open_typ_wrt_typ (back_ty A) (t_var_f X).
Proof with auto.
  intros. 
  unfold open_typ_wrt_typ.
  unfold open_tt.
  revert H.
  generalize 0. intros.
  inductions H;intros...
  - 
    simpl. destruct (lt_eq_lt_dec b n) as [[?|?]|?].
    + simpl. destruct (n == b);try lia...
    + subst. simpl. destruct (n == n);try lia...
    + simpl. destruct (n == b);try lia...
  - simpl. rewrite IHWFC1... 
    rewrite IHWFC2...
  - simpl. f_equal.
    rewrite IHWFC...
Qed.


(* Lemma back_ty_open_tt: forall A (X:atom),
  degree_typ_wrt_typ 1 (back_ty A) ->
  back_ty (open_tt A X) = open_typ_wrt_typ (back_ty A) (t_var_f X).
Proof with auto.
  intros. 
  forwards: trans_ty_open_typ_wrt_typ X H.
  rewrite trans_back_ty in H0.
  rewrite <- H0.
  rewrite back_trans_ty...
Qed. *)

Lemma AmberWFT_lc: forall AE A,
  AmberWFT AE A -> lc_typ A.
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - pick_fresh X.
    specialize_x_and_L X L.
    pick_fresh Y'.
    specialize_x_and_L Y' (L \u {{X}}).
    apply lc_t_mu_exists with (X1:=X)...
Qed.


Lemma AmberWFT_Isowft: forall AE A,
  AmberWFT AE A -> wf_amber AE (trans_ty A).
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - apply wfa_rec with (L:=L).
    intros. specialize (H _ H1). specialize (H0 _ H1).
    specialize (H _ H2). specialize (H0 _ H2).
    rewrite <- trans_ty_open_typ_wrt_typ...
    { apply AmberWFT_lc in H. apply degree_typ_wrt_typ_of_lc_typ  in H.
      apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H... }
Qed.

Lemma type_rename_env_aux: forall E A n,
  WFC (rename_env E A) n -> WFC A n.
Proof with auto.
  intros.
  inductions A...
  - rewrite rename_bvar in H...
  - rewrite rename_mu in H...
    constructor. apply IHA.
    inversion H...
  - rewrite rename_arrow in H.
    inversion H;subst...
Qed.

Lemma type_rename_env: forall E A,
  type (rename_env E A) -> type A.
Proof with auto.
  intros.
  apply close_type_wfc in H.
  apply type_rename_env_aux in H.
  inductions E...
  - simpl in H. apply type_wfc_close...
Qed.




Lemma Isowft_AmberWFT: forall AE A,
  wf_amber AE A -> AmberWFT AE (back_ty A).
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - pick_fresh Y0. 
    apply AWFT_rec with (L:=L \u fv_tt A \u AmberBase.domA E). { apply Y0. }
    intros. rewrite <- back_ty_open_tt. { apply H0... }
    { 
      (* apply type_open_tt_WFC with (X:=X)... *)
      specialize (H X Y).
      apply wf_amber_to_WF in H...
      simpl in H. rewrite <- subst_tt_fresh in H.
      2:{ apply notin_fv_domA... apply notin_fv_tt_open_aux... }
      apply soundness_wfa in H.
      apply wfs_type in H.
      apply type_rename_env in H.
      apply type_open_tt_WFC in H...
    }
Qed.

#[export]
Hint Extern 1 (AmberWFT ?AE (back_ty ?A)) =>
  match goal with
  | H: wf_amber AE A |- _ => apply Isowft_AmberWFT in H
  end : core.

#[export]
Hint Extern 1 (wf_amber ?AE (trans_ty ?A)) =>
  match goal with
  | H: AmberWFT AE A |- _ => apply AmberWFT_Isowft in H
  end : core.



Lemma AmberSubtyping_to_IsoSubtyping: forall G A B,
  AmberSubtyping G A B -> AmberBase.sub_amber G (trans_ty A) (trans_ty B).
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - 
Admitted.


Theorem unfolding_lemma: forall A B,
  AmberSubtyping nil (t_mu A) (t_mu B) ->
  AmberSubtyping nil (open_typ_wrt_typ A (t_mu A)) (open_typ_wrt_typ B (t_mu B)).
Proof.
Admitted.
