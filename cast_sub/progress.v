Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.

Require Export subtyping.


Ltac inv H := inversion H; subst; try solve [
  match goal with
  | [H : value _ |- _ ] => inversion H; auto
  end
].


Ltac specialize_x_and_L X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => specialize (H _ Q); clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.


Ltac specialize_x_and_L_keep X L :=
  repeat match goal with
         | [H : forall _, _ \notin L -> _, Q : X \notin L |- _ ] => pose proof (H _ Q);clear Q
         | [H : forall _, _ \notin L -> _ |- _ ] => assert (X \notin L) by auto
         end.

Ltac destruct_hypos :=
  repeat
    match goal with
    | [H : _ /\ _ |- _ ] => destruct H
    | [H : exists _, _ |- _ ] => destruct H
    end.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let E := gather_atoms_with (fun x : typ => typefv_typ x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => termfv_exp x) in
  let F := gather_atoms_with (fun x : tctx => dom x) in
  let G := gather_atoms_with (fun x : ctx => dom x) in
  let H := gather_atoms_with (fun x : castop => castfv_castop x) in
  let I := gather_atoms_with (fun x : cctx => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F \u G \u H \u I).


Lemma binds_tm_regular: forall x A G, WFTmE G -> binds x A G -> WFT nil A.
Proof with auto.
  intros. induction H...
  - inversion H0.
  - analyze_binds H0.
Qed.


Lemma WFT_weakening: forall D1 D t, WFT (D1 ++ D) t -> forall D2, WFT (D1 ++ D2 ++ D) t.
Proof with auto.
  intros. dependent induction H...
  - apply WFT_var... rewrite !dom_app... rewrite dom_app in H.
    apply union_iff in H. destruct H...
  - apply WFT_rec with (L:=L \u dom D1)...
    intros. rewrite_alist ((X ~ tt ++ D1) ++ D2 ++ D ). apply H0...
Qed.


Lemma WFT_typsubst: forall D1 D t X U, WFT (D1 ++ X ~ tt ++ D) t -> WFT (D1 ++ D) U -> WFT (D1 ++ D) (typsubst_typ U X t).
Proof with auto.
  intros. dependent induction H...
  - simpl. destruct (X0==X)... apply WFT_var... rewrite !dom_app in H. rewrite dom_app.
    apply union_iff in H. destruct H...
    apply union_iff in H. destruct H... simpl in H. exfalso. fsetdec.
  - simpl...
  - simpl. apply WFT_rec with (L:=L \u {{ X }} )...
    intros. rewrite typsubst_typ_open_typ_wrt_typ_var...
    { rewrite_alist ((X0 ~ tt ++ D1) ++ D). apply H0...
      rewrite_alist (nil ++ X0 ~ tt ++ (D1 ++ D)). apply WFT_weakening... }
    { apply WFT_lc_typ in H1... }
Qed.


Theorem TypCast_regular: forall D E A B c, TypCast D E A B c -> WFT D A /\ WFT D B /\ lc_castop c /\ uniq E.
Proof with auto.
  intros.
  induction H...
  - destruct_hypos...
  - repeat split... 2:{ constructor... apply WFT_lc_typ in H... }
    inversion H;subst.
    pick_fresh X. specialize_x_and_L X L. 
    rewrite typsubst_typ_intro with (X1:=X)...
    rewrite_alist (nil ++ D).
    apply WFT_typsubst...
  - repeat split... 2:{ constructor... apply WFT_lc_typ in H... }
    inversion H;subst.
    pick_fresh X. specialize_x_and_L X L. 
    rewrite typsubst_typ_intro with (X1:=X)...
    rewrite_alist (nil ++ D).
    apply WFT_typsubst...
  - destruct_hypos...
  - pick_fresh cx.
    destruct (H0 cx) as [H1' [H2' [H3' H4']]]... destruct (H2 cx) as [H1'' [H2'' [H3'' H4'']]]...
    repeat split...
    -- apply lc_c_fixc_exists with cx. unfold open_castop_wrt_castop in *. simpl. apply lc_c_arrow...
    -- inversion H4''...  
Qed.


Lemma ECTyping_regular: forall G e t e',
  EquiTypingC G e t e' ->
  WFTmE G /\ WFT nil t /\ lc_exp e' /\ lc_exp e.
Proof with auto.
  introv Hty.
  inductions Hty...
  - repeat split... applys~ binds_tm_regular x G...
  - pick_fresh x. forwards (?&?&?&?): H0 x...
    inv H1. repeat split...
    apply lc_e_abs_exists with (x1:=x)...
    { inv H1. apply WFT_lc_typ in H12... }
    apply lc_e_abs_exists with (x1:=x)...
    { inv H1. apply WFT_lc_typ in H12... }
  - destruct_hypos. inv H4...
  - destruct_hypos. repeat split...
    { apply TypCast_regular in H. destruct_hypos... }
    { apply TypCast_regular in H. destruct_hypos... }
  - destruct_hypos. repeat split...
    { apply AmberSub_regular in H. destruct_hypos.
      apply AmberWFT_WFT... }
Qed.


Theorem typing_regular: forall G e t, Typing G e t ->
  WFTmE G /\ WFT nil t /\ lc_exp e.
Proof with auto.
  intros.
  induction H...
  - repeat split... apply binds_tm_regular with (x:=x) (G:=G)...
  - pick_fresh X. specialize_x_and_L X L. destruct_hypos. repeat split...
    { inversion H0... } { inversion H0... } 
    { inversion H0;subst. apply lc_e_abs_exists with (x1:=X)...
      eapply WFT_lc_typ with (D:=nil)... }
  - destruct_hypos. repeat split... inversion H5...
  - destruct_hypos. repeat split...
    { apply TypCast_regular in H0. destruct_hypos... }
    { constructor... apply TypCast_regular in H0. destruct_hypos... }
  -  destruct_hypos. repeat split...
    { apply AmberSub_regular in H0. destruct_hypos.
      apply AmberWFT_WFT... }
Qed.


Ltac get_WFT :=
  repeat match goal with
  | [H : Typing _ ?e _ |- _ ] => apply typing_regular in H; destruct_hypos
  | [H : TypCast _ _ _ _ _ |- _ ] => apply TypCast_regular in H; destruct_hypos
  | [H : EquiTypingC _ _ _ _ |- _ ] => apply ECTyping_regular in H; destruct_hypos
  end.

Ltac get_lc :=
  repeat (get_WFT; match goal with
  | [H : WFT _ _ |- _ ] => apply WFT_lc_typ in H
  end).

#[export] Hint Extern 1 (lc_exp _ ) => get_lc : core.
#[export] Hint Extern 1 (lc_typ _ ) => get_lc : core.
#[export] Hint Extern 1 (lc_castop _ ) => get_lc : core.
#[export] Hint Extern 1 (WFT _ _ ) => get_WFT : core.


Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  Typing nil e (t_arrow U1 U2) ->
  (exists V, exists e1, e = e_abs V e1)
  \/ (exists c1 c2 e', e = e_cast (c_arrow c1 c2) e').
Proof.
  intros e U1 U2 Val Typ.
  dependent induction Typ; try solve [inversion Val] ...
  - left. exists U1 e. reflexivity.
  - inv H. right. exists c1 c2 e. reflexivity.
  - inv H. applys* IHTyp...
Qed.


Lemma canonical_form_mu : forall e A,
  value e ->
  Typing  nil e (t_mu A) ->
  (exists e1 A', e = e_cast (c_fold (t_mu A')) e1).
Proof with auto.
  intros.
  dependent induction H0...
  - inv H1.
  - inv H.
  - inv H.
    +
      inv H1. exists e A...
    +
      inv H1.
  - inv H1.
    + applys* IHTyping.
    + applys* IHTyping.
Qed.


Theorem progress: forall e t, Typing nil e t -> (value e) \/ exists e', Reduction e e'.
Proof with eauto.
  intros.
  assert (Hwf1: lc_exp e). { apply typing_regular in H. destruct_hypos... }
  assert (Hwf2: WFT nil t). { apply typing_regular in H. destruct_hypos... }
  dependent induction H...
  - 
    (* var *)
    inversion H0.
  - 
    (* abs *)
    left. constructor... { apply WFT_lc_typ in Hwf2. inversion Hwf2... }
  -
    (* app *)
    destruct IHTyping1...
    +
      (* v1 e2 ~~> v1[e2/x] 

      v1 : A1 -> A2
      e2 : A1      

      *)

      (* 
      v1 = A1 -> A2 ~ value
      v1 = castup [A3 -> A4] e1', A3 -> A4 ~~> A1 -> A2
      v1 = castdn [A1 -> A2] v1'
      *)
      destruct IHTyping2...
      *
        destruct (canonical_form_abs _ _ _ H1 H) as [[A [e ?]]|(c1 & c2 & e' & ?)];subst.
        { subst. right. exists (open_exp_wrt_exp e e2)... 
          apply Red_beta...
          { inversion Hwf1;subst. inversion H5;subst... }
        }
        { subst. right. 
          exists (e_cast c2 (e_app e' (e_cast (rev_cast c1) e2)))...
          get_lc... inv H6. inv H9.
          apply Red_cast_arr...
          { inv H1. }
        }
      *
        destruct H2 as [e2' ?]. right. exists (e_app e1 e2')...
    +
      (* e1 e2 ~~~> e1' e2 *)
      destruct H1 as [e1' ?]. right. exists (e_app e1' e2)...
  -
    (* cast *)
    destruct IHTyping... 
    +
      (* cast [c] (cast [fold (μ a. A2)] e0) *)
      inversion H0;subst...
      *
        (* unfold *)
        forwards (e'&A'&?): canonical_form_mu H...
        subst e. right.
        exists e'.
        get_lc. inv H5.
      * 
        (* seq *)
        right. exists (e_cast c2 (e_cast c1 e)).
        get_lc. inv Hwf1.
      *
        (* assump *)
        inv H5.
    +
      destruct H1 as [e' ?]...
Qed.
