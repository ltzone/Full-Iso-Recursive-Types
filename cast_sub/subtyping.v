(* The following formalizations adapt our Coq development to 
   the Coq development of "Revisiting Iso-recursive Subtyping"
*)
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import subtyping.AmberLocal.
Require Import subtyping.AmberSoundness.
Require Import subtyping.AmberCompleteness.
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

#[export]
Hint Extern 1 (lc_typ ?A) =>
  match goal with
  | H: AmberWFT _ A |- _ => apply AmberWFT_lc in H
  end : core.


Lemma AmberSubtyping_lc_typ: forall G A B,
  AmberSubtyping G A B -> lc_typ A /\ lc_typ B.
Proof with auto.
  intros. inductions H...
  - destruct_hypos...
  - pick_fresh X. pick_fresh Y.
    specialize_x_and_L Y L.
    specialize_x_and_L X (L \u {{Y}}).
    destruct_hypos.
    split;eapply lc_t_mu_exists;eassumption.
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


Lemma wf_open_tt_WFC: forall G A (X:atom),
  X `notin` fv_tt A ->
  wf_amber G (open_tt A X) ->
  WFC A 1.
Proof with auto.
  intros.
  apply wf_amber_to_WF in H0...
  (* simpl in H. rewrite <- subst_tt_fresh in H.
  2:{ apply notin_fv_domA... apply notin_fv_tt_open_aux... } *)
  apply soundness_wfa in H0.
  apply wfs_type in H0.
  apply type_rename_env in H0.
  apply type_open_tt_WFC in H...
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
      apply wf_open_tt_WFC in H...
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

(* Lemma sam_reflexive: forall G A,
  AmberBase.wfe_amber G ->
  AmberBase.wf_amber G A ->
  AmberBase.sub_amber G A A.
Proof with auto.
  intros.
  inductions H0...
  - apply sam_fvar.
Admitted. *)

Lemma AmberSubtyping_to_IsoSubtyping: forall G A B,
  AmberSubtyping G A B -> AmberBase.sub_amber G (trans_ty A) (trans_ty B).
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - apply sam_rec with (L:=L \u typefv_typ A)...
    intros. specialize_x_and_L Y L.
    specialize_x_and_L X (L \u {{Y}}).
    rewrite trans_ty_open_typ_wrt_typ in H0.
    2:{ apply AmberSubtyping_lc_typ in H. destruct_hypos. 
        apply degree_typ_wrt_typ_of_lc_typ  in H.
        apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H... }
    rewrite trans_ty_open_typ_wrt_typ in H0.
    2:{ apply AmberSubtyping_lc_typ in H. destruct_hypos. 
        apply degree_typ_wrt_typ_of_lc_typ  in H3.
        apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H3... }
    auto.
  - apply sam_refl...
    apply AmberWFT_Isowft in H0...
Qed.

Lemma IsoSubtyping_to_AmberSubtyping: forall G A B,
  AmberBase.sub_amber G A B -> AmberSubtyping G (back_ty A) (back_ty B).
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - apply ASub_rec with (L:=L \u fv_tt A \u fv_tt B)...
    intros.
    forwards H1': (H X Y)...
    forwards H2': (H0 X Y)...
    rewrite back_ty_open_tt in H2'.
    2:{ apply sam_regular in H1'. destruct_hypos.
        apply wf_open_tt_WFC in H4... }
    rewrite back_ty_open_tt in H2'.
    2:{ apply sam_regular in H1'. destruct_hypos.
        apply wf_open_tt_WFC in H5... }
    auto.
  - apply ASub_self...
    apply Isowft_AmberWFT in H0...
Qed.

Lemma open_tt_back_ty_distr: forall A B,
  WFC A 1 ->
  back_ty (open_tt A B) = open_typ_wrt_typ (back_ty A) (back_ty B).
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

Lemma degree_WFC: forall A n,
   degree_typ_wrt_typ n A -> WFC (trans_ty A) n.
Proof with auto.
  inductions A;intros...
  - inversion H;subst.
    constructor...
  - constructor...
  - inversion H;subst. constructor...
  - inversion H;subst. constructor...
Qed.

Lemma back_ty_mu: forall A,
  back_ty (typ_mu A) = t_mu (back_ty A).
Proof with auto.
  reflexivity.
Qed.

Theorem unfolding_lemma: forall A B,
  AmberSubtyping nil (t_mu A) (t_mu B) ->
  AmberSubtyping nil (open_typ_wrt_typ A (t_mu A)) (open_typ_wrt_typ B (t_mu B)).
Proof with auto.
  intros.
  forwards (?&?): AmberSubtyping_lc_typ H.
  apply AmberSubtyping_to_IsoSubtyping in H.
  simpl in H.
  apply amber_unfolding in H.
  apply IsoSubtyping_to_AmberSubtyping in H.
  rewrite open_tt_back_ty_distr in H.
  2:{ apply degree_WFC. inversion H0;subst.
      pick_fresh X. specialize (H3 X).
      apply degree_typ_wrt_typ_of_lc_typ in H3.
      apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H3... }
  rewrite open_tt_back_ty_distr in H.
  2:{ apply degree_WFC. inversion H1;subst.
      pick_fresh X. specialize (H3 X).
      apply degree_typ_wrt_typ_of_lc_typ in H3.
      apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H3... }
  rewrite !back_trans_ty in H.
  rewrite !back_ty_mu in H.
  rewrite !back_trans_ty in H...
Qed.

Theorem AmberSub_regular: forall G A B,
  AmberSubtyping G A B -> AmberWF G /\ AmberWFT G A /\ AmberWFT G B.
Proof with auto.
  intros.
  forwards (?&?): AmberSubtyping_lc_typ H.
  apply AmberSubtyping_to_IsoSubtyping in H.
  apply sam_regular in H.
  destruct_hypos.
  repeat split...
  - apply Isowft_AmberWFT in H2...
    rewrite back_trans_ty in H2...
  - apply Isowft_AmberWFT in H3...
    rewrite back_trans_ty in H3...
Qed.


Theorem AmberSub_trans: forall A B C,
  AmberSubtyping nil A B -> AmberSubtyping nil B C -> AmberSubtyping nil A C.
Proof with auto.
  intros.
  (* forwards (?&?): AmberSubtyping_lc_typ H. *)
  apply AmberSubtyping_to_IsoSubtyping in H.
  apply AmberSubtyping_to_IsoSubtyping in H0.
  forwards: amber_transitivity H H0.
  apply IsoSubtyping_to_AmberSubtyping in H1.
  rewrite !back_trans_ty in H1...
Qed.


Fixpoint env_to_tctx (D: env) : tctx :=
  match D with
  | nil => nil
  | (X, bind_sub) :: D' => (X, tt) :: env_to_tctx D'
  | (X, bind_typ _) :: D' =>  (X, tt) :: env_to_tctx D'
  end.

Lemma env_to_tctx_dom: forall D,
dom (env_to_tctx D) [=] dom D.
Proof with auto.
  intros.
  induction D; simpl; eauto.
  - reflexivity.
  - destruct a. destruct b.
    + simpl. fsetdec.
    + simpl. fsetdec.
Qed.




Theorem WFS_WFT: forall D A,
Rules.WFA D A -> WFT (env_to_tctx D) (back_ty A).
Proof with auto.
  intros.
  induction H; simpl; eauto.
  - apply WFT_var. rewrite env_to_tctx_dom.
    apply binds_In in H...
  - apply WFT_rec with (L:=L \u fv_tt A).
    intros. specialize_x_and_L X L.
    rewrite back_ty_open_tt in H0...
    {
      apply wfa_type in H.
      apply type_open_tt_WFC in H...
    }
Qed.


Theorem AmberWFT_WFT: forall  A,
  AmberWFT nil A -> WFT nil A.
Proof with auto.
  intros.
  apply AmberWFT_Isowft in H.
  apply wf_amber_to_WF in H.
  simpl in H.
  apply WFS_WFT in H.
  rewrite back_trans_ty in H...
Qed.


Fixpoint tctx_to_env (D: tctx) : env :=
  match D with
  | nil => nil
  | (X, tt) :: D' => (X, bind_sub) :: tctx_to_env D'
  end.

Lemma tctx_to_env_in: forall D X,
  X `in` dom D ->
  binds X bind_sub (tctx_to_env D).
Proof with auto.
  intros.
  induction D; simpl in *; eauto.
  - fsetdec.
  - destruct a. destruct u.
    apply add_iff in H. destruct H...
Qed.


Lemma WFT_lc_typ: forall D t, WFT D t -> lc_typ t.
Proof with auto.
  introv H. induction H...
Qed.


Lemma WFT_WFA: forall G A,
  WFT G A ->
  WFA (tctx_to_env G) (trans_ty A).
Proof with auto.
  intros. inductions H;simpl...
  - apply WFA_fvar. apply tctx_to_env_in...
  - simpl. apply WFA_rec with (L:=L \u typefv_typ A).
    intros. specialize_x_and_L X L.
    simpl in H0.  rewrite trans_ty_open_typ_wrt_typ in H0...
    { apply WFT_lc_typ in H. apply degree_typ_wrt_typ_of_lc_typ  in H.
      apply degree_typ_wrt_typ_open_typ_wrt_typ_inv in H...
    }
Qed.


Theorem WFT_AmberWFT: forall  A,
  WFT nil A -> AmberWFT nil A.
Proof with auto.
  intros.
  apply WFT_WFA in H.
  apply wfa_to_wf in H.
  eapply env_conv_wf_amber in H.
  2:{ constructor. }
  2:{ constructor. }
  apply Isowft_AmberWFT in H.
  rewrite back_trans_ty in H...
Qed.

Theorem AmberWFT_refl: forall G A,
  AmberWF G -> typefv_typ A [=] AtomSetImpl.empty ->
  AmberWFT G A -> AmberSubtyping G A A.
Proof with auto.
  intros.
  inductions H1...
  - simpl  in H0. exfalso. specialize (H0 X). fsetdec.
  - simpl  in H0. exfalso. specialize (H0 Y). fsetdec.
  - simpl in H0.
    constructor. apply IHAmberWFT1... { fsetdec. }
    apply IHAmberWFT2... { fsetdec. }
  - apply ASub_self...
    { apply AWFT_rec with (L:=L).
      apply Y. intros. 
      apply H1... }
Qed.