Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.

Require Export progress.

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

Lemma WFTmE_uniq: forall D E,
  WFTmE D E ->
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


Lemma Typing_weakening: forall G F E1 E2 e T,
  WFTmE G (E1 ++ F ++ E2) ->
  Typing G (E1 ++ E2) e T ->
  Typing G (E1 ++ F ++ E2) e T.
Proof with auto.
  intros. dependent induction H0...
  -
    apply Typing_abs with (L:=L \u dom (E1 ++ F ++ E2))...
    intros. specialize_x_and_L x L.
    rewrite_alist ((x ~ A1 ++ E1) ++ F ++ E2).
    apply H0... simpl. constructor...
    { apply typing_regular in H1. destruct_hypos.
      inversion H3... }
  -
    apply Typing_app with (A1:=A1)...
  -
    apply Typing_fix with (L:=L \u dom (E1 ++ F ++ E2))...
    intros. specialize_x_and_L x L.
    rewrite_alist ((x ~ A ++ E1) ++ F ++ E2).
    apply H0... simpl. constructor...
  -
    apply Typing_cast with (A:=A)...
Qed.


Lemma typing_through_subst_ee : forall G F U E x T e u,
  Typing G (F ++ x ~ U ++ E) e T ->
  Typing G E u U ->
  Typing G (F ++  E) (subst_exp u x e) T.
Proof with eauto.
  intros.
  remember (F ++ x ~ U ++ E) as E'.
  generalize dependent F. 
  induction H;intros;subst;simpl in *...
  -
    (* int *)
    apply Typing_int...
    apply WFTmE_strengthening in H1...

  -
    destruct (x0==x)...
    +
      subst...
      analyze_binds_uniq H2...
      { apply WFTmE_uniq in H1... }
      rewrite_alist (nil ++ F ++ E). 
      apply Typing_weakening...
      apply WFTmE_strengthening in H1...
    +
      analyze_binds H2...
      constructor... { apply WFTmE_strengthening in H1... }
      constructor... { apply WFTmE_strengthening in H1... }
  -
    apply Typing_abs with (L:=L \u {{x}})...
    intros. rewrite subst_exp_open_exp_wrt_exp_var...
    rewrite_alist (([(x0, A1)] ++ F) ++ E).
    apply H1...
  -
    apply Typing_fix with (L:=L \u {{x}})...
    intros. rewrite subst_exp_open_exp_wrt_exp_var...
    rewrite_alist (([(x0, A)] ++ F) ++ E).
    apply H1...
Qed.


(* Theorem TypReduction_det: forall t1 t2 G, TypReduction G t1 t2 -> forall t3, TypReduction G t1 t3 -> t2 = t3.
Proof with auto.
  intros. generalize dependent t3. 
  dependent induction H; intros; try solve [inversion H0; auto].
  - inversion H0;subst... { inversion H2. }
  - inversion H1;subst...
    2:{ inversion H3. }
    apply IHTypReduction1 in H5.
    apply IHTypReduction2 in H7.
    subst...
  - inversion H1;subst...
    { inversion H0. } { inversion H0. }
Qed. *)

Theorem typCast_rev: forall E A B c, 
  TypCast E A B c ->
  TypCast E B A (rev_cast c).
Proof with auto.
  intros. induction H;simpl...
Qed.

Lemma DualCast_det: forall c1 c2 ,
  DualCast c1 c2 ->
  forall G A B A',
  TypCast G A B c1 ->
  TypCast G B A' c2 ->
  A = A'.
Proof with auto.
  intros c1 c2 H. dependent induction H;intros.
  - inv H0. inv H...
  - inv H1. inv H2.
    rewrite (IHDualCast1 _ _ _ _ H8 H10).
    rewrite (IHDualCast2 _ _ _ _ H9 H12)...
  - inv H0. inv H1...
Qed.


Lemma DualCast_det2: forall c1 c2 ,
  DualCast c1 c2 ->
  forall G A B A',
  TypCast G A B c2 ->
  TypCast G B A' c1 ->
  A = A'.
Proof with auto.
  intros c1 c2 H. dependent induction H;intros.
  - inv H0. inv H...
  - inv H1. inv H2.
    rewrite (IHDualCast1 _ _ _ _ H8 H10).
    rewrite (IHDualCast2 _ _ _ _ H9 H12)...
  - inv H0. inv H1...
Qed.


Theorem preservation: forall e T,
  Typing nil nil e T -> forall e', 
  Reduction e e' -> Typing nil nil e' T.
Proof with auto.
  intros. dependent induction H; try solve [inversion H1]...
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
      inv H. inv H11.
      { apply Typing_cast with (A:=B1)...
        apply Typing_app with (A1:=A0)...
        apply Typing_cast with (A:=A1)...
        apply typCast_rev... }

  -
    (* fix *)
    assert (Typing nil nil (e_fixpoint A e) A). { apply Typing_fix with (L:=L)... } 
    inversion H1; subst...
    pick_fresh X. specialize_x_and_L X L.
    rewrite subst_exp_intro with (x1:=X)...
    apply typing_through_subst_ee with (F:=nil) (U:=A) (E:=nil)...
  -
    (* cast *)
    inv H1.
    +
      (* cast [c] e ~> cast [c] e' *)
      apply Typing_cast with (A:=A)...
    +
      (* cast [c] (cast [c2] e') ~> e', c ~ c2 *)
      inv H.
      assert (A0 = B). 
      { apply DualCast_det2
        with (c1:=c) (c2:=c2) (G:= nil) (B:= A)... }
      subst...
    +
      (* cast [id] e' ~> e' *)
      inv H0...
Qed.