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
  let H := gather_atoms_with (fun x : castop => castfv_castop x) in
  let I := gather_atoms_with (fun x : cctx => dom x) in
  constr:(A `union` B `union`  E \u C \u D \u F \u G \u H \u I).




Theorem AmberSub_regular: forall AE A B,
  AmberSubtyping AE A B ->
  AmberWF AE /\ AmberWFT AE A /\ AmberWFT AE B.
Admitted.


Fixpoint AE_to_E (AE: list (atom * atom)) :=
  match AE with
  | nil => nil
  | (X, Y) :: AE' => X ~ tt ++ AE_to_E AE'
  end.


Fixpoint rename_env (E : list (atom * atom)) (A : typ) : typ :=
  match E with
  | nil => A
  | cons (X,Y) E' => typsubst_typ (t_var_f X) Y (rename_env E' A)
  end.

Lemma AmberWFT_WFT: forall AE A,
  AmberWFT AE A -> WFT (AE_to_E AE) (rename_env AE A).
Proof with auto.
Admitted.

Theorem AmberSub_WFT: forall A B,
AmberSubtyping nil A B ->
WFT nil A /\ WFT nil B.
Proof with auto.
  intros.
  forwards (?&Ha&Hb): AmberSub_regular H.
  forwards*: AmberWFT_WFT Ha.
  forwards*: AmberWFT_WFT Hb.
Qed.


Theorem unfolding_lemma: forall E A B,
 AmberSubtyping E (t_mu A) (t_mu B) ->
 AmberSubtyping E (open_typ_wrt_typ A (t_mu A)) (open_typ_wrt_typ B (t_mu B)).
Admitted.