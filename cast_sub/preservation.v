Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.

Require Export equiRec.


Lemma WFTmE_uniq: forall E,
  WFTmE E ->
  uniq E.
Proof with auto.
  intros.
  induction H...
Qed.


(* Lemma WFTmE_weakening: forall D E F G,
  WFTmE D (F ++ E ) ->
  WFTmE D (F ++ G ++ E).
Proof with auto.
  intros.
  induction F...
  - inversion H...
  - inversion H;subst.
    constructor...
Qed. *)


Lemma Typing_weakening: forall F E1 E2 e T,
  WFTmE (E1 ++ F ++ E2) ->
  Typing (E1 ++ E2) e T ->
  Typing (E1 ++ F ++ E2) e T.
Proof with auto.
  intros. dependent induction H0...
  -
    apply Typing_abs with (L:=L \u dom (E1 ++ F ++ E2))...
    intros. specialize_x_and_L x L.
    rewrite_alist ((x ~ A1 ++ E1) ++ F ++ E2).
    apply H0... simpl. constructor...
    { apply typing_regular in H1. destruct_hypos.
      inversion H1... }
  -
    apply Typing_app with (A1:=A1)...
  -
    apply Typing_cast with (A:=A)...
Qed.




Lemma revE_dist: forall E1 E2,
  reverse_E (E1 ++ E2) = (reverse_E E1) ++ (reverse_E E2).
Proof.
  apply map_app.
Qed.




Lemma typing_through_subst_ee : forall F U E x T e u,
  Typing (F ++ x ~ U ++ E) e T ->
  Typing E u U ->
  Typing (F ++  E) (subst_exp u x e) T.
Proof with eauto.
  intros.
  remember (F ++ x ~ U ++ E) as E'.
  generalize dependent F. 
  induction H;intros;subst;simpl in *...
  -
    (* int *)
    apply Typing_int...
    apply WFTmE_strengthening in H...

  -
    destruct (x0==x)...
    +
      subst...
      analyze_binds_uniq H1...
      { apply WFTmE_uniq in H... }
      rewrite_alist (nil ++ F ++ E). 
      apply Typing_weakening...
      apply WFTmE_strengthening in H...
    +
      analyze_binds H1...
      constructor... { apply WFTmE_strengthening in H... }
      constructor... { apply WFTmE_strengthening in H... }
  -
    apply Typing_abs with (L:=L \u {{x}})...
    intros. rewrite subst_exp_open_exp_wrt_exp_var...
    rewrite_alist (([(x0, A1)] ++ F) ++ E).
    apply H1...
Qed.



Lemma In_revE: forall cx A B E,
  In (cx, (A, B)) E -> In (cx, (B, A)) (reverse_E E).
Proof with auto.
  intros. induction E...
  - destruct a as [cx' [A' B']]. simpl in *. destruct H.
    -- left. inversion H; subst...
    -- right...
Qed.


Theorem TypCast_rev: forall E C A B c, 
  TypCast E C A B c ->
  TypCast E (reverse_E C) B A (rev_cast c).
Proof with auto.
  intros. induction H;simpl...
  -
    apply TCast_seq with (B:=B)...
  -
    apply TCast_var... apply In_revE...
  -
    apply TCast_fix with (L:=L \u dom E \u castfv_castop c1 \u castfv_castop c2)...
    + intros. specialize_x_and_L cx L...
      rewrite <- rev_cast_open...
    + intros. specialize_x_and_L cx L...
      rewrite <- rev_cast_open...
Qed.


Theorem preservation: forall e T,
  Typing nil e T -> forall e', 
  Reduction e e' -> Typing nil e' T.
Proof with auto.
  intros. dependent induction H; try solve [inversion H1|inversion H0]...
  - 
    (* app *)
    dependent induction H1; subst...
    +
      (* beta *)
      inversion H; subst...
      pick_fresh X. specialize_x_and_L X L.
      rewrite subst_exp_intro with (x1:=X)...
      apply typing_through_subst_ee with (F:=nil) (U:=A1) (E:=nil)...
    +
      (* app-1 *)
      apply IHTyping1 in H1...
      apply Typing_app with (A1:=A1)...
    +
      (* app-2 *)
      apply IHTyping2 in H1...
      apply Typing_app with (A1:=A1)...
    +
      (* push-cast *)
      inv H. inv H10.
      { apply Typing_cast with (A:=B1)...
        apply Typing_app with (A1:=A0)...
        apply Typing_cast with (A:=A1)...
        apply TypCast_rev in H13... }

  -
    (* cast *)
    inv H1.
    +
      (* cast [c1;c2] e ~> cast c1 (cast [c2] e) *)
      inv H0.
      apply Typing_cast with (A:=B0)...
      apply Typing_cast with (A:=A)...
    +
      (* cast [c] e ~> cast [c] e' *)
      apply Typing_cast with (A:=A)...
    +
      (* cast [c] (cast [c2] e') ~> e', c ~ c2 *)
      inv H. inv H9.
      inv H0...
    +
      (* cast [id] e' ~> e' *)
      inv H0...
    + 
      (* cast [fixc c] e' ~>  *)
      inv H0. eapply Typing_cast. apply H.
      {
        pick_fresh cx'.
        specialize_x_and_L cx' L.
        rewrite_alist (nil ++ [(cx', (t_arrow A1 B1, t_arrow A2 B2))] ++ nil) in H10.
        rewrite_alist (nil ++ [(cx', (t_arrow A1 B1, t_arrow A2 B2))] ++ nil) in H3.
        assert (TypCast nil (nil ++ nil) (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2)))...
        forwards: subst_castop H10 H2.
        forwards: subst_castop H3 H2.
        rewrite <- castsubst_castop_intro in H5, H7...
        apply TCast_arrow;auto.
      } 
Qed.