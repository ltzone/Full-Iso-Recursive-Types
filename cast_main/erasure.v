Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Import Coq.Relations.Relation_Operators.
Require Export LibTactics.

Require Export progress.

Fixpoint erase (t:exp) :=    
  match t with
  | e_var_f x => e_var_f x
  | e_var_b x => e_var_b x
  | e_abs t1 t2 => e_abs t1 (erase t2)
  | e_app t1 t2 => e_app (erase t1) (erase t2)
  | e_lit l => e_lit l
  | e_cast c e => erase e
  end.

Lemma erase_open_ee: forall e1 e2, erase (open_exp_wrt_exp e1 e2) = open_exp_wrt_exp (erase e1) (erase e2).
Proof with auto.
  unfold open_exp_wrt_exp.
  intros. generalize 0.
  induction e1;intros;simpl...
  - destruct (lt_eq_lt_dec n n0)...
    destruct s...
  - 
    f_equal. rewrite IHe1...
  -
    rewrite IHe1_1. rewrite IHe1_2...
Qed.


Lemma erase_close_ee: forall x e, erase (close_exp_wrt_exp x e) = close_exp_wrt_exp x (erase e).
Proof with auto.
  unfold close_exp_wrt_exp.
  intros. generalize 0.
  induction e;intros;simpl...
  - destruct (lt_dec n n0)...
  -
    destruct (x == t)...
  -
    f_equal. rewrite IHe...
  -
    rewrite IHe1. rewrite IHe2...
Qed.

Lemma erase_lc_exp: forall e, lc_exp e -> lc_exp (erase e).
Proof with auto.
  intros.
  induction H;simpl...
  -
    apply lc_e_abs... intros.
    specialize (H1 x).
    rewrite erase_open_ee in H1...
Qed.


Lemma erase_value: forall v, value v -> value (erase v).
Proof with auto.
  intros.
  induction H;simpl...
  -
    constructor...
    apply erase_lc_exp in H0...
  (* -
    constructor...
    apply erase_lc_exp in H0... *)
Qed.

(* Lemma erase_cvalue: forall m v, cvalue m v -> value (erase v).
Proof with auto.
  intros.
  induction H;simpl...
  -
    apply erase_value...
Qed. *)


#[global] Hint Resolve erase_lc_exp erase_value : core.


Notation "e1 '==>*' e2" := (clos_refl_trans exp Reduction e1 e2) (at level 40).

Lemma Red_appl_multi: forall e1 e2 e3,
  e1 ==>* e2 -> lc_exp e3 ->
  (e_app e1 e3) ==>* (e_app e2 e3).
Proof with auto.
  intros.
  induction H...
  - apply rt_step...
  - apply rt_refl...
  - eapply rt_trans. 
    { apply IHclos_refl_trans1. }
    { auto. }
Qed.



Lemma Red_appr_multi: forall v1 e1 e2,
  e1 ==>* e2 -> value v1 ->
  (e_app v1 e1) ==>* (e_app v1 e2).
Proof with auto.
  intros.
  induction H...
  - apply rt_step...
  - apply rt_refl...
  - eapply rt_trans. 
    { apply IHclos_refl_trans1. }
    { auto. }
Qed.



Lemma soundness_erase: forall e1 e2,
  Reduction e1 e2 ->
  (erase e1) ==>* (erase e2).
Proof with auto.
  intros.
  induction H;simpl; try apply rt_refl...
  - 
    rewrite erase_open_ee...
    apply rt_step.
    apply Red_beta...
    { apply erase_lc_exp in H0... }
  -
    apply Red_appl_multi...
  -
    apply Red_appr_multi...
Qed.


Lemma erase_fv: forall e, termfv_exp (erase e) [=] termfv_exp e.
Proof with auto.
  intros.
  induction e; simpls;try reflexivity...
  -
    rewrite IHe1, IHe2. reflexivity.
Qed.
