Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.

Require Export rules_inf.



Ltac inv H := inversion H; subst; try solve [
  match goal with
  | [H : value _ |- _ ] => inversion H; auto
  | [H : ordinary _ |- _] => inversion H; auto
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
  constr:(A `union` B `union`  E \u C \u D \u F \u G).


Lemma binds_tm_regular: forall x A D G, WFTmE D G -> binds x A G -> WFT D A.
Proof with auto.
  intros. induction H...
  - inversion H0.
  - analyze_binds H0.
Qed.

Lemma WFT_lc_typ: forall D t, WFT D t -> lc_typ t.
Proof with auto.
  introv H. induction H...
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

Theorem TypCast_regular: forall D A B c, TypCast D A B c -> WFT D A /\ WFT D B /\ lc_castop c.
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
Qed.



Theorem typing_regular: forall D G e t, Typing D G e t ->
  WFTyE D /\ WFTmE D G /\ WFT D t /\ lc_exp e.
Proof with auto.
  intros.
  induction H...
  - repeat split... apply binds_tm_regular with (x:=x) (G:=G)...
  - pick_fresh X. specialize_x_and_L X L. destruct_hypos. repeat split...
    { inversion H1... } { inversion H1... } 
    { inversion H1;subst. apply lc_e_abs_exists with (x1:=X)...
      eapply WFT_lc_typ with (D:=D)... }
  - destruct_hypos. repeat split... inversion H7...
  - pick_fresh X. specialize_x_and_L X L. destruct_hypos. repeat split...
    { inversion H1... } { apply lc_e_fixpoint_exists with (x1:=X)...
      eapply WFT_lc_typ with (D:=D)... }
  - destruct_hypos. repeat split...
    { apply TypCast_regular in H0. destruct_hypos... }
    { constructor... apply TypCast_regular in H0. destruct_hypos... }
Qed.


Ltac get_WFT :=
  repeat match goal with
  | [H : Typing _ _ ?e _ |- _ ] => apply typing_regular in H; destruct_hypos
  | [H : TypCast _ _ _ |- _ ] => apply TypCast_regular in H; destruct_hypos
  end.

Ltac get_lc :=
  repeat (get_WFT; match goal with
  | [H : WFT _ _ |- _ ] => apply WFT_lc_typ in H
  end).

#[export] Hint Extern 1 (lc_exp _ ) => get_lc : core.
#[export] Hint Extern 1 (lc_typ _ ) => get_lc : core.
#[export] Hint Extern 1 (WFT _ _ ) => get_WFT : core.


Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  Typing nil nil e (t_arrow U1 U2) ->
  (exists V, exists e1, e = e_abs V e1)
  \/ (exists c1 c2 e', e = e_cast (c_arrow c1 c2) e').
Proof.
  intros e U1 U2 Val Typ.
  dependent induction Typ; try solve [inversion Val] ...
  - left. exists U1 e. reflexivity.
  - inv H. right. exists c1 c2 e. reflexivity.
Qed.



Lemma canonical_form_mu : forall e A,
  value e ->
  Typing nil nil e (t_mu A) ->
  (exists e1, e = e_cast (c_fold (t_mu A)) e1).
Proof with auto.
  intros.
  dependent induction H0...
  - inv H1.
  - inv H.
  - inv H.
  - inv H.
    +
      inv H1. exists e...
    +
      inv H1.
Qed.


Theorem progress: forall e t, Typing nil nil e t -> ( value e) \/ exists e', Reduction e e'.
Proof with eauto.
  intros.
  assert (Hwf1: lc_exp e). { apply typing_regular in H. destruct_hypos... }
  assert (Hwf2: WFT nil t). { apply typing_regular in H. destruct_hypos... }
  dependent induction H...
  - 
    (* var *)
    inversion H1.
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

      destruct (canonical_form_abs _ _ _ H1 H) as [[A [e ?]]|(c1 & c2 & e' & ?)];subst.
      { subst. right. exists (open_exp_wrt_exp e e2)... 
        apply Red_beta...
        { inversion Hwf1;subst. inversion H4;subst... }
      }
      { subst. right. 
        exists (e_cast c2 (e_app e' (e_cast (rev_cast c1) e2)))...
        get_lc... inv H7.
        (* apply Red_cast_arr... *)
      }
      
    +
      (* e1 e2 ~~~> e1' e2 *)
      destruct H1 as [e1' ?]. right. exists (e_app e1' e2)...
  (* -
    (* fix *)
    right. exists (open_exp_wrt_exp e (e_fixpoint A e))... *)
    
  -
    (* cast *)
    destruct IHTyping...
    +
      (* cast [c] (cast [fold (μ a. A2)] e0) *)
      inversion H1;subst...
      *
        (* cast [c] lit *)
        inversion H;subst...
        inv H0. 
        { (* cast [id] lit *)
          right. exists (e_lit i)... }
      *
        inv H.
        inv H0.
        { (* cast [id] (λ x: A0. e0) *)
          right. exists (e_abs A0 e0)... }
        { get_lc. inv Hwf1.
          inv H12.
          (* left... apply V_arrow... *)
        }
      *
        inv H. inv H10.
        inv H0.
        { (* cast [id] (cast [fold (μ a. A2)] e0) *)
          right. exists (e_cast (c_fold (t_mu A2)) e0)... }
        { (* cast [unfold (μ a. A2)] (cast [fold (μ a. A2)] e0) *)
          right. exists e0. apply Red_castelim...
        }
        { (* cast [fold (μ a. A)] (cast [fold (μ a. A2)]) e0 *)
          left. rewrite H4...
        }
      *
        (* cast [c] (cast [c1 -> c2] e0) *)
        inv H0.
        { (* cast [id] (cast [c1 -> c2] e0) *)
          get_lc. right. exists ((e_cast (c_arrow c1 c2) e0))...
        }
        { (* cast [c0 -> c3] (cast [c1 -> c2] e0) *)
          get_lc. inv H1. inv Hwf1. inv H12. 
        }
        { (* cast [unfold (μ a. A0)] (cast [c1 -> c2]  e0)
            impossible *)
          inv H. inv H12.
        }
    +
      destruct H1 as [e' ?]...
      right. exists (e_cast c e')...
      inv Hwf1. apply Red_cast...

Qed.