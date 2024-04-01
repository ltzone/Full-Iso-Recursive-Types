(* The following formalizations adapt our Coq development to 
   the Coq development of "Revisiting Iso-recursive Subtyping"
*)
Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import subtyping.AmberBase.
Require Export rules_inf.


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

Lemma AmberWF_to_Isowfe: forall AE,
  AmberWF AE -> wfe_amber AE.
Proof.
  intros.
  induction H; simpl; eauto.
  - constructor...
Admitted.


Lemma AmberSubtyping_to_IsoSubtyping: forall G A B,
  AmberSubtyping G A B -> AmberBase.sub_amber G (trans_ty A) (trans_ty B).
Proof.
  intros.
  induction H; simpl; eauto.
  - apply sam_nat...
Admitted.

Theorem unfolding_lemma: forall A B,
  AmberSubtyping nil (t_mu A) (t_mu B) ->
  AmberSubtyping nil (open_typ_wrt_typ A (t_mu A)) (open_typ_wrt_typ B (t_mu B)).
Proof.
Admitted.
