Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntax_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme castop_ind' := Induction for castop Sort Prop.

Combined Scheme castop_mutind from castop_ind'.

Scheme castop_rec' := Induction for castop Sort Set.

Combined Scheme castop_mutrec from castop_rec'.

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Scheme mode_ind' := Induction for mode Sort Prop.

Combined Scheme mode_mutind from mode_ind'.

Scheme mode_rec' := Induction for mode Sort Set.

Combined Scheme mode_mutrec from mode_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_var_f X1 => 1
    | t_var_b n1 => 1
    | t_int => 1
    | t_top => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_mu A2 => 1 + (size_typ A2)
  end.

Fixpoint size_castop (c1 : castop) {struct c1} : nat :=
  match c1 with
    | c_var_f cx1 => 1
    | c_var_b n1 => 1
    | c_id => 1
    | c_unfold A1 => 1 + (size_typ A1)
    | c_fold A1 => 1 + (size_typ A1)
    | c_arrow c2 c3 => 1 + (size_castop c2) + (size_castop c3)
    | c_seq c2 c3 => 1 + (size_castop c2) + (size_castop c3)
    | c_fixc c2 => 1 + (size_castop c2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_lit i1 => 1
    | e_abs A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_cast c1 e2 => 1 + (size_castop c1) + (size_exp e2)
  end.

Fixpoint size_mode (m1 : mode) {struct m1} : nat :=
  match m1 with
    | m_pos => 1
    | m_neg => 1
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_t_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (t_var_f X1)
  | degree_wrt_typ_t_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (t_var_b n2)
  | degree_wrt_typ_t_int : forall n1,
    degree_typ_wrt_typ n1 (t_int)
  | degree_wrt_typ_t_top : forall n1,
    degree_typ_wrt_typ n1 (t_top)
  | degree_wrt_typ_t_arrow : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_arrow A1 B1)
  | degree_wrt_typ_t_mu : forall n1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (t_mu A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

#[export] Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_castop_wrt_typ : nat -> castop -> Prop :=
  | degree_wrt_typ_c_var_f : forall n1 cx1,
    degree_castop_wrt_typ n1 (c_var_f cx1)
  | degree_wrt_typ_c_var_b : forall n1 n2,
    degree_castop_wrt_typ n1 (c_var_b n2)
  | degree_wrt_typ_c_id : forall n1,
    degree_castop_wrt_typ n1 (c_id)
  | degree_wrt_typ_c_unfold : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_castop_wrt_typ n1 (c_unfold A1)
  | degree_wrt_typ_c_fold : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_castop_wrt_typ n1 (c_fold A1)
  | degree_wrt_typ_c_arrow : forall n1 c1 c2,
    degree_castop_wrt_typ n1 c1 ->
    degree_castop_wrt_typ n1 c2 ->
    degree_castop_wrt_typ n1 (c_arrow c1 c2)
  | degree_wrt_typ_c_seq : forall n1 c1 c2,
    degree_castop_wrt_typ n1 c1 ->
    degree_castop_wrt_typ n1 c2 ->
    degree_castop_wrt_typ n1 (c_seq c1 c2)
  | degree_wrt_typ_c_fixc : forall n1 c1,
    degree_castop_wrt_typ n1 c1 ->
    degree_castop_wrt_typ n1 (c_fixc c1).

Inductive degree_castop_wrt_castop : nat -> castop -> Prop :=
  | degree_wrt_castop_c_var_f : forall n1 cx1,
    degree_castop_wrt_castop n1 (c_var_f cx1)
  | degree_wrt_castop_c_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_castop_wrt_castop n1 (c_var_b n2)
  | degree_wrt_castop_c_id : forall n1,
    degree_castop_wrt_castop n1 (c_id)
  | degree_wrt_castop_c_unfold : forall n1 A1,
    degree_castop_wrt_castop n1 (c_unfold A1)
  | degree_wrt_castop_c_fold : forall n1 A1,
    degree_castop_wrt_castop n1 (c_fold A1)
  | degree_wrt_castop_c_arrow : forall n1 c1 c2,
    degree_castop_wrt_castop n1 c1 ->
    degree_castop_wrt_castop n1 c2 ->
    degree_castop_wrt_castop n1 (c_arrow c1 c2)
  | degree_wrt_castop_c_seq : forall n1 c1 c2,
    degree_castop_wrt_castop n1 c1 ->
    degree_castop_wrt_castop n1 c2 ->
    degree_castop_wrt_castop n1 (c_seq c1 c2)
  | degree_wrt_castop_c_fixc : forall n1 c1,
    degree_castop_wrt_castop (S n1) c1 ->
    degree_castop_wrt_castop n1 (c_fixc c1).

Scheme degree_castop_wrt_typ_ind' := Induction for degree_castop_wrt_typ Sort Prop.

Combined Scheme degree_castop_wrt_typ_mutind from degree_castop_wrt_typ_ind'.

Scheme degree_castop_wrt_castop_ind' := Induction for degree_castop_wrt_castop Sort Prop.

Combined Scheme degree_castop_wrt_castop_mutind from degree_castop_wrt_castop_ind'.

#[export] Hint Constructors degree_castop_wrt_typ : core lngen.

#[export] Hint Constructors degree_castop_wrt_castop : core lngen.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_e_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (e_var_f x1)
  | degree_wrt_typ_e_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (e_var_b n2)
  | degree_wrt_typ_e_lit : forall n1 i1,
    degree_exp_wrt_typ n1 (e_lit i1)
  | degree_wrt_typ_e_abs : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_abs A1 e1)
  | degree_wrt_typ_e_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_app e1 e2)
  | degree_wrt_typ_e_cast : forall n1 c1 e1,
    degree_castop_wrt_typ n1 c1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_cast c1 e1).

Inductive degree_exp_wrt_castop : nat -> exp -> Prop :=
  | degree_wrt_castop_e_var_f : forall n1 x1,
    degree_exp_wrt_castop n1 (e_var_f x1)
  | degree_wrt_castop_e_var_b : forall n1 n2,
    degree_exp_wrt_castop n1 (e_var_b n2)
  | degree_wrt_castop_e_lit : forall n1 i1,
    degree_exp_wrt_castop n1 (e_lit i1)
  | degree_wrt_castop_e_abs : forall n1 A1 e1,
    degree_exp_wrt_castop n1 e1 ->
    degree_exp_wrt_castop n1 (e_abs A1 e1)
  | degree_wrt_castop_e_app : forall n1 e1 e2,
    degree_exp_wrt_castop n1 e1 ->
    degree_exp_wrt_castop n1 e2 ->
    degree_exp_wrt_castop n1 (e_app e1 e2)
  | degree_wrt_castop_e_cast : forall n1 c1 e1,
    degree_castop_wrt_castop n1 c1 ->
    degree_exp_wrt_castop n1 e1 ->
    degree_exp_wrt_castop n1 (e_cast c1 e1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (e_var_f x1)
  | degree_wrt_exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_var_b n2)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs A1 e1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_cast : forall n1 c1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_cast c1 e1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_exp_wrt_typ_mutind from degree_exp_wrt_typ_ind'.

Scheme degree_exp_wrt_castop_ind' := Induction for degree_exp_wrt_castop Sort Prop.

Combined Scheme degree_exp_wrt_castop_mutind from degree_exp_wrt_castop_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_exp_wrt_typ : core lngen.

#[export] Hint Constructors degree_exp_wrt_castop : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_t_var_f : forall X1,
    lc_set_typ (t_var_f X1)
  | lc_set_t_int :
    lc_set_typ (t_int)
  | lc_set_t_top :
    lc_set_typ (t_top)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_arrow A1 B1)
  | lc_set_t_mu : forall A1,
    (forall X1 : typevar, lc_set_typ (open_typ_wrt_typ A1 (t_var_f X1))) ->
    lc_set_typ (t_mu A1).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

#[export] Hint Constructors lc_typ : core lngen.

#[export] Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_castop : castop -> Set :=
  | lc_set_c_var_f : forall cx1,
    lc_set_castop (c_var_f cx1)
  | lc_set_c_id :
    lc_set_castop (c_id)
  | lc_set_c_unfold : forall A1,
    lc_set_typ A1 ->
    lc_set_castop (c_unfold A1)
  | lc_set_c_fold : forall A1,
    lc_set_typ A1 ->
    lc_set_castop (c_fold A1)
  | lc_set_c_arrow : forall c1 c2,
    lc_set_castop c1 ->
    lc_set_castop c2 ->
    lc_set_castop (c_arrow c1 c2)
  | lc_set_c_seq : forall c1 c2,
    lc_set_castop c1 ->
    lc_set_castop c2 ->
    lc_set_castop (c_seq c1 c2)
  | lc_set_c_fixc : forall c1,
    (forall cx1 : castvar, lc_set_castop (open_castop_wrt_castop c1 (c_var_f cx1))) ->
    lc_set_castop (c_fixc c1).

Scheme lc_castop_ind' := Induction for lc_castop Sort Prop.

Combined Scheme lc_castop_mutind from lc_castop_ind'.

Scheme lc_set_castop_ind' := Induction for lc_set_castop Sort Prop.

Combined Scheme lc_set_castop_mutind from lc_set_castop_ind'.

Scheme lc_set_castop_rec' := Induction for lc_set_castop Sort Set.

Combined Scheme lc_set_castop_mutrec from lc_set_castop_rec'.

#[export] Hint Constructors lc_castop : core lngen.

#[export] Hint Constructors lc_set_castop : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_exp (e_var_f x1)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : termvar, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_abs A1 e1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_cast : forall c1 e1,
    lc_set_castop c1 ->
    lc_set_exp e1 ->
    lc_set_exp (e_cast c1 e1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_exp_mutind from lc_exp_ind'.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_exp_mutind from lc_set_exp_ind'.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_exp_mutrec from lc_set_exp_rec'.

#[export] Hint Constructors lc_exp : core lngen.

#[export] Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (t_var_f X1)).

#[export] Hint Unfold body_typ_wrt_typ : core.

Definition body_castop_wrt_typ c1 := forall X1, lc_castop (open_castop_wrt_typ c1 (t_var_f X1)).

Definition body_castop_wrt_castop c1 := forall cx1, lc_castop (open_castop_wrt_castop c1 (c_var_f cx1)).

#[export] Hint Unfold body_castop_wrt_typ : core.

#[export] Hint Unfold body_castop_wrt_castop : core.

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (t_var_f X1)).

Definition body_exp_wrt_castop e1 := forall cx1, lc_exp (open_exp_wrt_castop e1 (c_var_f cx1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (e_var_f x1)).

#[export] Hint Unfold body_exp_wrt_typ : core.

#[export] Hint Unfold body_exp_wrt_castop : core.

#[export] Hint Unfold body_exp_wrt_exp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof. Admitted.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof. Admitted.

#[export] Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_castop_min_mutual :
(forall c1, 1 <= size_castop c1).
Proof. Admitted.

(* end hide *)

Lemma size_castop_min :
forall c1, 1 <= size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof. Admitted.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_mode_min_mutual :
(forall m1, 1 <= size_mode m1).
Proof. Admitted.

(* end hide *)

Lemma size_mode_min :
forall m1, 1 <= size_mode m1.
Proof. Admitted.

#[export] Hint Resolve size_mode_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof. Admitted.

#[export] Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_castop_close_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  size_castop (close_castop_wrt_typ_rec n1 X1 c1) = size_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_castop_close_castop_wrt_typ_rec :
forall c1 X1 n1,
  size_castop (close_castop_wrt_typ_rec n1 X1 c1) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_close_castop_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_castop_close_castop_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_castop_close_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1,
  size_castop (close_castop_wrt_castop_rec n1 cx1 c1) = size_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_castop_close_castop_wrt_castop_rec :
forall c1 cx1 n1,
  size_castop (close_castop_wrt_castop_rec n1 cx1 c1) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_close_castop_wrt_castop_rec : lngen.
#[export] Hint Rewrite size_castop_close_castop_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  size_exp (close_exp_wrt_castop_rec n1 cx1 e1) = size_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_castop_rec :
forall e1 cx1 n1,
  size_exp (close_exp_wrt_castop_rec n1 cx1 e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_close_exp_wrt_castop_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof. Admitted.

#[export] Hint Resolve size_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_castop_close_castop_wrt_typ :
forall c1 X1,
  size_castop (close_castop_wrt_typ X1 c1) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_close_castop_wrt_typ : lngen.
#[export] Hint Rewrite size_castop_close_castop_wrt_typ using solve [auto] : lngen.

Lemma size_castop_close_castop_wrt_castop :
forall c1 cx1,
  size_castop (close_castop_wrt_castop cx1 c1) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_close_castop_wrt_castop : lngen.
#[export] Hint Rewrite size_castop_close_castop_wrt_castop using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_castop :
forall e1 cx1,
  size_exp (close_exp_wrt_castop cx1 e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_close_exp_wrt_castop : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_castop using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof. Admitted.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_typ_rec_mutual :
(forall c1 A1 n1,
  size_castop c1 <= size_castop (open_castop_wrt_typ_rec n1 A1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_typ_rec :
forall c1 A1 n1,
  size_castop c1 <= size_castop (open_castop_wrt_typ_rec n1 A1 c1).
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_castop_rec_mutual :
(forall c1 c2 n1,
  size_castop c1 <= size_castop (open_castop_wrt_castop_rec n1 c2 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_castop_rec :
forall c1 c2 n1,
  size_castop c1 <= size_castop (open_castop_wrt_castop_rec n1 c2 c1).
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_castop_rec_mutual :
(forall e1 c1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_castop_rec n1 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_castop_rec :
forall e1 c1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_castop_rec n1 c1 e1).
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof. Admitted.

#[export] Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_castop_open_castop_wrt_typ :
forall c1 A1,
  size_castop c1 <= size_castop (open_castop_wrt_typ c1 A1).
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_typ : lngen.

Lemma size_castop_open_castop_wrt_castop :
forall c1 c2,
  size_castop c1 <= size_castop (open_castop_wrt_castop c1 c2).
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_castop : lngen.

Lemma size_exp_open_exp_wrt_typ :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_castop :
forall e1 c1,
  size_exp e1 <= size_exp (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_castop : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (t_var_f X1) A1) = size_typ A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (t_var_f X1) A1) = size_typ A1.
Proof. Admitted.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_typ_rec_var_mutual :
(forall c1 X1 n1,
  size_castop (open_castop_wrt_typ_rec n1 (t_var_f X1) c1) = size_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_typ_rec_var :
forall c1 X1 n1,
  size_castop (open_castop_wrt_typ_rec n1 (t_var_f X1) c1) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_castop_open_castop_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_castop_rec_var_mutual :
(forall c1 cx1 n1,
  size_castop (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1) = size_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_castop_open_castop_wrt_castop_rec_var :
forall c1 cx1 n1,
  size_castop (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_castop_rec_var : lngen.
#[export] Hint Rewrite size_castop_open_castop_wrt_castop_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (t_var_f X1) e1) = size_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (t_var_f X1) e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_castop_rec_var_mutual :
(forall e1 cx1 n1,
  size_exp (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1) = size_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_castop_rec_var :
forall e1 cx1 n1,
  size_exp (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_castop_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_castop_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = size_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (t_var_f X1)) = size_typ A1.
Proof. Admitted.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_castop_open_castop_wrt_typ_var :
forall c1 X1,
  size_castop (open_castop_wrt_typ c1 (t_var_f X1)) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_typ_var : lngen.
#[export] Hint Rewrite size_castop_open_castop_wrt_typ_var using solve [auto] : lngen.

Lemma size_castop_open_castop_wrt_castop_var :
forall c1 cx1,
  size_castop (open_castop_wrt_castop c1 (c_var_f cx1)) = size_castop c1.
Proof. Admitted.

#[export] Hint Resolve size_castop_open_castop_wrt_castop_var : lngen.
#[export] Hint Rewrite size_castop_open_castop_wrt_castop_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (t_var_f X1)) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_castop_var :
forall e1 cx1,
  size_exp (open_exp_wrt_castop e1 (c_var_f cx1)) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_castop_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_castop_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (e_var_f x1)) = size_exp e1.
Proof. Admitted.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof. Admitted.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_castop_wrt_typ_S_mutual :
(forall n1 c1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ (S n1) c1).
Proof. Admitted.

(* end hide *)

Lemma degree_castop_wrt_typ_S :
forall n1 c1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ (S n1) c1.
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_castop_wrt_castop_S_mutual :
(forall n1 c1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop (S n1) c1).
Proof. Admitted.

(* end hide *)

Lemma degree_castop_wrt_castop_S :
forall n1 c1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop (S n1) c1.
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof. Admitted.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_castop_S_mutual :
(forall n1 e1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop (S n1) e1).
Proof. Admitted.

(* end hide *)

Lemma degree_exp_wrt_castop_S :
forall n1 e1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop (S n1) e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof. Admitted.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_castop_wrt_typ_O :
forall n1 c1,
  degree_castop_wrt_typ O c1 ->
  degree_castop_wrt_typ n1 c1.
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_O : lngen.

Lemma degree_castop_wrt_castop_O :
forall n1 c1,
  degree_castop_wrt_castop O c1 ->
  degree_castop_wrt_castop n1 c1.
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_castop_O :
forall n1 e1,
  degree_exp_wrt_castop O e1 ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ (S n1) (close_castop_wrt_typ_rec n1 X1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_typ_rec :
forall c1 X1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ (S n1) (close_castop_wrt_typ_rec n1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_close_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1 n2,
  degree_castop_wrt_typ n2 c1 ->
  degree_castop_wrt_typ n2 (close_castop_wrt_castop_rec n1 cx1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_castop_rec :
forall c1 cx1 n1 n2,
  degree_castop_wrt_typ n2 c1 ->
  degree_castop_wrt_typ n2 (close_castop_wrt_castop_rec n1 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_close_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1 n2,
  degree_castop_wrt_castop n2 c1 ->
  degree_castop_wrt_castop n2 (close_castop_wrt_typ_rec n1 X1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_typ_rec :
forall c1 X1 n1 n2,
  degree_castop_wrt_castop n2 c1 ->
  degree_castop_wrt_castop n2 (close_castop_wrt_typ_rec n1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_close_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop (S n1) (close_castop_wrt_castop_rec n1 cx1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_castop_rec :
forall c1 cx1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop (S n1) (close_castop_wrt_castop_rec n1 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_close_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_castop_rec n1 cx1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_castop_rec :
forall e1 cx1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_castop_rec n1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_castop n2 e1 ->
  degree_exp_wrt_castop n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_castop n2 e1 ->
  degree_exp_wrt_castop n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop (S n1) (close_exp_wrt_castop_rec n1 cx1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_castop_rec :
forall e1 cx1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop (S n1) (close_exp_wrt_castop_rec n1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_close_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_castop n2 e1 ->
  degree_exp_wrt_castop n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_castop n2 e1 ->
  degree_exp_wrt_castop n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_castop_rec n1 cx1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_castop_rec :
forall e1 cx1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_castop_rec n1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_castop_wrt_typ_close_castop_wrt_typ :
forall c1 X1,
  degree_castop_wrt_typ 0 c1 ->
  degree_castop_wrt_typ 1 (close_castop_wrt_typ X1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_close_castop_wrt_typ : lngen.

Lemma degree_castop_wrt_typ_close_castop_wrt_castop :
forall c1 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ n1 (close_castop_wrt_castop cx1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_close_castop_wrt_castop : lngen.

Lemma degree_castop_wrt_castop_close_castop_wrt_typ :
forall c1 X1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 (close_castop_wrt_typ X1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_close_castop_wrt_typ : lngen.

Lemma degree_castop_wrt_castop_close_castop_wrt_castop :
forall c1 cx1,
  degree_castop_wrt_castop 0 c1 ->
  degree_castop_wrt_castop 1 (close_castop_wrt_castop cx1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_close_castop_wrt_castop : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_castop :
forall e1 cx1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_castop cx1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_castop : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_castop_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (close_exp_wrt_typ X1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_castop_close_exp_wrt_castop :
forall e1 cx1,
  degree_exp_wrt_castop 0 e1 ->
  degree_exp_wrt_castop 1 (close_exp_wrt_castop cx1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_close_exp_wrt_castop : lngen.

Lemma degree_exp_wrt_castop_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (close_exp_wrt_exp x1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_castop :
forall e1 cx1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_castop cx1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_castop : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof. Admitted.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_typ_rec_inv_mutual :
(forall c1 X1 n1,
  degree_castop_wrt_typ (S n1) (close_castop_wrt_typ_rec n1 X1 c1) ->
  degree_castop_wrt_typ n1 c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_typ_rec_inv :
forall c1 X1 n1,
  degree_castop_wrt_typ (S n1) (close_castop_wrt_typ_rec n1 X1 c1) ->
  degree_castop_wrt_typ n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_close_castop_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_castop_rec_inv_mutual :
(forall c1 cx1 n1 n2,
  degree_castop_wrt_typ n2 (close_castop_wrt_castop_rec n1 cx1 c1) ->
  degree_castop_wrt_typ n2 c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_close_castop_wrt_castop_rec_inv :
forall c1 cx1 n1 n2,
  degree_castop_wrt_typ n2 (close_castop_wrt_castop_rec n1 cx1 c1) ->
  degree_castop_wrt_typ n2 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_close_castop_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_typ_rec_inv_mutual :
(forall c1 X1 n1 n2,
  degree_castop_wrt_castop n2 (close_castop_wrt_typ_rec n1 X1 c1) ->
  degree_castop_wrt_castop n2 c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_typ_rec_inv :
forall c1 X1 n1 n2,
  degree_castop_wrt_castop n2 (close_castop_wrt_typ_rec n1 X1 c1) ->
  degree_castop_wrt_castop n2 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_close_castop_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_castop_rec_inv_mutual :
(forall c1 cx1 n1,
  degree_castop_wrt_castop (S n1) (close_castop_wrt_castop_rec n1 cx1 c1) ->
  degree_castop_wrt_castop n1 c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_close_castop_wrt_castop_rec_inv :
forall c1 cx1 n1,
  degree_castop_wrt_castop (S n1) (close_castop_wrt_castop_rec n1 cx1 c1) ->
  degree_castop_wrt_castop n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_close_castop_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_castop_rec_inv_mutual :
(forall e1 cx1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_castop_rec n1 cx1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_castop_rec_inv :
forall e1 cx1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_castop_rec n1 cx1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_castop n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_castop n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_castop n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_castop n2 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_castop_rec_inv_mutual :
(forall e1 cx1 n1,
  degree_exp_wrt_castop (S n1) (close_exp_wrt_castop_rec n1 cx1 e1) ->
  degree_exp_wrt_castop n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_castop_rec_inv :
forall e1 cx1 n1,
  degree_exp_wrt_castop (S n1) (close_exp_wrt_castop_rec n1 cx1 e1) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_close_exp_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_castop n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_castop n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_castop n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_castop n2 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_castop_rec_inv_mutual :
(forall e1 cx1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_castop_rec n1 cx1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_castop_rec_inv :
forall e1 cx1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_castop_rec n1 cx1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof. Admitted.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_castop_wrt_typ_close_castop_wrt_typ_inv :
forall c1 X1,
  degree_castop_wrt_typ 1 (close_castop_wrt_typ X1 c1) ->
  degree_castop_wrt_typ 0 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_close_castop_wrt_typ_inv : lngen.

Lemma degree_castop_wrt_typ_close_castop_wrt_castop_inv :
forall c1 cx1 n1,
  degree_castop_wrt_typ n1 (close_castop_wrt_castop cx1 c1) ->
  degree_castop_wrt_typ n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_close_castop_wrt_castop_inv : lngen.

Lemma degree_castop_wrt_castop_close_castop_wrt_typ_inv :
forall c1 X1 n1,
  degree_castop_wrt_castop n1 (close_castop_wrt_typ X1 c1) ->
  degree_castop_wrt_castop n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_close_castop_wrt_typ_inv : lngen.

Lemma degree_castop_wrt_castop_close_castop_wrt_castop_inv :
forall c1 cx1,
  degree_castop_wrt_castop 1 (close_castop_wrt_castop cx1 c1) ->
  degree_castop_wrt_castop 0 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_close_castop_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_castop_inv :
forall e1 cx1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_castop cx1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_castop_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_castop n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_castop_close_exp_wrt_castop_inv :
forall e1 cx1,
  degree_exp_wrt_castop 1 (close_exp_wrt_castop cx1 e1) ->
  degree_exp_wrt_castop 0 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_close_exp_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_castop_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_castop n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_castop_inv :
forall e1 cx1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_castop cx1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_typ_rec_mutual :
(forall c1 A1 n1,
  degree_castop_wrt_typ (S n1) c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_castop_wrt_typ n1 (open_castop_wrt_typ_rec n1 A1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_typ_rec :
forall c1 A1 n1,
  degree_castop_wrt_typ (S n1) c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_castop_wrt_typ n1 (open_castop_wrt_typ_rec n1 A1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_castop_rec_mutual :
(forall c1 c2 n1 n2,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ n1 c2 ->
  degree_castop_wrt_typ n1 (open_castop_wrt_castop_rec n2 c2 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_castop_rec :
forall c1 c2 n1 n2,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ n1 c2 ->
  degree_castop_wrt_typ n1 (open_castop_wrt_castop_rec n2 c2 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_typ_rec_mutual :
(forall c1 A1 n1 n2,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 (open_castop_wrt_typ_rec n2 A1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_typ_rec :
forall c1 A1 n1 n2,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 (open_castop_wrt_typ_rec n2 A1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_castop_rec_mutual :
(forall c1 c2 n1,
  degree_castop_wrt_castop (S n1) c1 ->
  degree_castop_wrt_castop n1 c2 ->
  degree_castop_wrt_castop n1 (open_castop_wrt_castop_rec n1 c2 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_castop_rec :
forall c1 c2 n1,
  degree_castop_wrt_castop (S n1) c1 ->
  degree_castop_wrt_castop n1 c2 ->
  degree_castop_wrt_castop n1 (open_castop_wrt_castop_rec n1 c2 c1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_castop_rec_mutual :
(forall e1 c1 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_castop_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_castop_rec n2 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_castop_rec :
forall e1 c1 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_castop_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_castop_rec n2 c1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_castop_rec_mutual :
(forall e1 c1 n1,
  degree_exp_wrt_castop (S n1) e1 ->
  degree_castop_wrt_castop n1 c1 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_castop_rec n1 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_castop_rec :
forall e1 c1 n1,
  degree_exp_wrt_castop (S n1) e1 ->
  degree_castop_wrt_castop n1 c1 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_castop_rec n1 c1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 e2 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 e2 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_castop_rec_mutual :
(forall e1 c1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_castop_rec n2 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_castop_rec :
forall e1 c1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_castop_rec n2 c1 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_castop_wrt_typ_open_castop_wrt_typ :
forall c1 A1,
  degree_castop_wrt_typ 1 c1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_castop_wrt_typ 0 (open_castop_wrt_typ c1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_open_castop_wrt_typ : lngen.

Lemma degree_castop_wrt_typ_open_castop_wrt_castop :
forall c1 c2 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ n1 c2 ->
  degree_castop_wrt_typ n1 (open_castop_wrt_castop c1 c2).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_open_castop_wrt_castop : lngen.

Lemma degree_castop_wrt_castop_open_castop_wrt_typ :
forall c1 A1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 (open_castop_wrt_typ c1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_open_castop_wrt_typ : lngen.

Lemma degree_castop_wrt_castop_open_castop_wrt_castop :
forall c1 c2,
  degree_castop_wrt_castop 1 c1 ->
  degree_castop_wrt_castop 0 c2 ->
  degree_castop_wrt_castop 0 (open_castop_wrt_castop c1 c2).
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_open_castop_wrt_castop : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_castop :
forall e1 c1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_castop_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_castop : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_castop_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_castop_open_exp_wrt_castop :
forall e1 c1,
  degree_exp_wrt_castop 1 e1 ->
  degree_castop_wrt_castop 0 c1 ->
  degree_exp_wrt_castop 0 (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_open_exp_wrt_castop : lngen.

Lemma degree_exp_wrt_castop_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 e2 ->
  degree_exp_wrt_castop n1 (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_castop :
forall e1 c1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_castop : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof. Admitted.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_typ_rec_inv_mutual :
(forall c1 A1 n1,
  degree_castop_wrt_typ n1 (open_castop_wrt_typ_rec n1 A1 c1) ->
  degree_castop_wrt_typ (S n1) c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_typ_rec_inv :
forall c1 A1 n1,
  degree_castop_wrt_typ n1 (open_castop_wrt_typ_rec n1 A1 c1) ->
  degree_castop_wrt_typ (S n1) c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_open_castop_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_castop_rec_inv_mutual :
(forall c1 c2 n1 n2,
  degree_castop_wrt_typ n1 (open_castop_wrt_castop_rec n2 c2 c1) ->
  degree_castop_wrt_typ n1 c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_typ_open_castop_wrt_castop_rec_inv :
forall c1 c2 n1 n2,
  degree_castop_wrt_typ n1 (open_castop_wrt_castop_rec n2 c2 c1) ->
  degree_castop_wrt_typ n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_open_castop_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_typ_rec_inv_mutual :
(forall c1 A1 n1 n2,
  degree_castop_wrt_castop n1 (open_castop_wrt_typ_rec n2 A1 c1) ->
  degree_castop_wrt_castop n1 c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_typ_rec_inv :
forall c1 A1 n1 n2,
  degree_castop_wrt_castop n1 (open_castop_wrt_typ_rec n2 A1 c1) ->
  degree_castop_wrt_castop n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_open_castop_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_castop_rec_inv_mutual :
(forall c1 c2 n1,
  degree_castop_wrt_castop n1 (open_castop_wrt_castop_rec n1 c2 c1) ->
  degree_castop_wrt_castop (S n1) c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_castop_wrt_castop_open_castop_wrt_castop_rec_inv :
forall c1 c2 n1,
  degree_castop_wrt_castop n1 (open_castop_wrt_castop_rec n1 c2 c1) ->
  degree_castop_wrt_castop (S n1) c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_open_castop_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_castop_rec_inv_mutual :
(forall e1 c1 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_castop_rec n2 c1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_castop_rec_inv :
forall e1 c1 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_castop_rec n2 c1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_castop n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_castop n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_castop n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_castop_rec_inv_mutual :
(forall e1 c1 n1,
  degree_exp_wrt_castop n1 (open_exp_wrt_castop_rec n1 c1 e1) ->
  degree_exp_wrt_castop (S n1) e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_castop_rec_inv :
forall e1 c1 n1,
  degree_exp_wrt_castop n1 (open_exp_wrt_castop_rec n1 c1 e1) ->
  degree_exp_wrt_castop (S n1) e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_open_exp_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_castop n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_castop n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_castop_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_castop n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_castop_rec_inv_mutual :
(forall e1 c1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_castop_rec n2 c1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_castop_rec_inv :
forall e1 c1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_castop_rec n2 c1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_castop_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof. Admitted.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_castop_wrt_typ_open_castop_wrt_typ_inv :
forall c1 A1,
  degree_castop_wrt_typ 0 (open_castop_wrt_typ c1 A1) ->
  degree_castop_wrt_typ 1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_open_castop_wrt_typ_inv : lngen.

Lemma degree_castop_wrt_typ_open_castop_wrt_castop_inv :
forall c1 c2 n1,
  degree_castop_wrt_typ n1 (open_castop_wrt_castop c1 c2) ->
  degree_castop_wrt_typ n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_typ_open_castop_wrt_castop_inv : lngen.

Lemma degree_castop_wrt_castop_open_castop_wrt_typ_inv :
forall c1 A1 n1,
  degree_castop_wrt_castop n1 (open_castop_wrt_typ c1 A1) ->
  degree_castop_wrt_castop n1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_open_castop_wrt_typ_inv : lngen.

Lemma degree_castop_wrt_castop_open_castop_wrt_castop_inv :
forall c1 c2,
  degree_castop_wrt_castop 0 (open_castop_wrt_castop c1 c2) ->
  degree_castop_wrt_castop 1 c1.
Proof. Admitted.

#[export] Hint Immediate degree_castop_wrt_castop_open_castop_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_castop_inv :
forall e1 c1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_castop e1 c1) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_castop_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_castop n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_castop_open_exp_wrt_castop_inv :
forall e1 c1,
  degree_exp_wrt_castop 0 (open_exp_wrt_castop e1 c1) ->
  degree_exp_wrt_castop 1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_open_exp_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_castop_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_castop n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_castop n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_castop_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_castop_inv :
forall e1 c1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_castop e1 c1) ->
  degree_exp_wrt_exp n1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_castop_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof. Admitted.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof. Admitted.

#[export] Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_typ_rec_inj_mutual :
(forall c1 c2 X1 n1,
  close_castop_wrt_typ_rec n1 X1 c1 = close_castop_wrt_typ_rec n1 X1 c2 ->
  c1 = c2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_typ_rec_inj :
forall c1 c2 X1 n1,
  close_castop_wrt_typ_rec n1 X1 c1 = close_castop_wrt_typ_rec n1 X1 c2 ->
  c1 = c2.
Proof. Admitted.

#[export] Hint Immediate close_castop_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_castop_rec_inj_mutual :
(forall c1 c2 cx1 n1,
  close_castop_wrt_castop_rec n1 cx1 c1 = close_castop_wrt_castop_rec n1 cx1 c2 ->
  c1 = c2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_castop_rec_inj :
forall c1 c2 cx1 n1,
  close_castop_wrt_castop_rec n1 cx1 c1 = close_castop_wrt_castop_rec n1 cx1 c2 ->
  c1 = c2.
Proof. Admitted.

#[export] Hint Immediate close_castop_wrt_castop_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof. Admitted.

#[export] Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_castop_rec_inj_mutual :
(forall e1 e2 cx1 n1,
  close_exp_wrt_castop_rec n1 cx1 e1 = close_exp_wrt_castop_rec n1 cx1 e2 ->
  e1 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_castop_rec_inj :
forall e1 e2 cx1 n1,
  close_exp_wrt_castop_rec n1 cx1 e1 = close_exp_wrt_castop_rec n1 cx1 e2 ->
  e1 = e2.
Proof. Admitted.

#[export] Hint Immediate close_exp_wrt_castop_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof. Admitted.

#[export] Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof. Admitted.

#[export] Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_castop_wrt_typ_inj :
forall c1 c2 X1,
  close_castop_wrt_typ X1 c1 = close_castop_wrt_typ X1 c2 ->
  c1 = c2.
Proof. Admitted.

#[export] Hint Immediate close_castop_wrt_typ_inj : lngen.

Lemma close_castop_wrt_castop_inj :
forall c1 c2 cx1,
  close_castop_wrt_castop cx1 c1 = close_castop_wrt_castop cx1 c2 ->
  c1 = c2.
Proof. Admitted.

#[export] Hint Immediate close_castop_wrt_castop_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof. Admitted.

#[export] Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_castop_inj :
forall e1 e2 cx1,
  close_exp_wrt_castop cx1 e1 = close_exp_wrt_castop cx1 e2 ->
  e1 = e2.
Proof. Admitted.

#[export] Hint Immediate close_exp_wrt_castop_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof. Admitted.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (t_var_f X1) A1) = A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (t_var_f X1) A1) = A1.
Proof. Admitted.

#[export] Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_typ_rec_open_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  X1 `notin` typefv_castop c1 ->
  close_castop_wrt_typ_rec n1 X1 (open_castop_wrt_typ_rec n1 (t_var_f X1) c1) = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_typ_rec_open_castop_wrt_typ_rec :
forall c1 X1 n1,
  X1 `notin` typefv_castop c1 ->
  close_castop_wrt_typ_rec n1 X1 (open_castop_wrt_typ_rec n1 (t_var_f X1) c1) = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_typ_rec_open_castop_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_castop_wrt_typ_rec_open_castop_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_castop_rec_open_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1,
  cx1 `notin` castfv_castop c1 ->
  close_castop_wrt_castop_rec n1 cx1 (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1) = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_castop_rec_open_castop_wrt_castop_rec :
forall c1 cx1 n1,
  cx1 `notin` castfv_castop c1 ->
  close_castop_wrt_castop_rec n1 cx1 (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1) = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_castop_rec_open_castop_wrt_castop_rec : lngen.
#[export] Hint Rewrite close_castop_wrt_castop_rec_open_castop_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e1) = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_castop_rec_open_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  cx1 `notin` castfv_exp e1 ->
  close_exp_wrt_castop_rec n1 cx1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_castop_rec_open_exp_wrt_castop_rec :
forall e1 cx1 n1,
  cx1 `notin` castfv_exp e1 ->
  close_exp_wrt_castop_rec n1 cx1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1) = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_castop_rec_open_exp_wrt_castop_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_castop_rec_open_exp_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (t_var_f X1)) = A1.
Proof. Admitted.

#[export] Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_castop_wrt_typ_open_castop_wrt_typ :
forall c1 X1,
  X1 `notin` typefv_castop c1 ->
  close_castop_wrt_typ X1 (open_castop_wrt_typ c1 (t_var_f X1)) = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_typ_open_castop_wrt_typ : lngen.
#[export] Hint Rewrite close_castop_wrt_typ_open_castop_wrt_typ using solve [auto] : lngen.

Lemma close_castop_wrt_castop_open_castop_wrt_castop :
forall c1 cx1,
  cx1 `notin` castfv_castop c1 ->
  close_castop_wrt_castop cx1 (open_castop_wrt_castop c1 (c_var_f cx1)) = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_castop_open_castop_wrt_castop : lngen.
#[export] Hint Rewrite close_castop_wrt_castop_open_castop_wrt_castop using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (t_var_f X1)) = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_castop_open_exp_wrt_castop :
forall e1 cx1,
  cx1 `notin` castfv_exp e1 ->
  close_exp_wrt_castop cx1 (open_exp_wrt_castop e1 (c_var_f cx1)) = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_castop_open_exp_wrt_castop : lngen.
#[export] Hint Rewrite close_exp_wrt_castop_open_exp_wrt_castop using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (e_var_f x1)) = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (t_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (t_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof. Admitted.

#[export] Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_typ_rec_close_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  open_castop_wrt_typ_rec n1 (t_var_f X1) (close_castop_wrt_typ_rec n1 X1 c1) = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_typ_rec_close_castop_wrt_typ_rec :
forall c1 X1 n1,
  open_castop_wrt_typ_rec n1 (t_var_f X1) (close_castop_wrt_typ_rec n1 X1 c1) = c1.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_typ_rec_close_castop_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_castop_wrt_typ_rec_close_castop_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_castop_rec_close_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1,
  open_castop_wrt_castop_rec n1 (c_var_f cx1) (close_castop_wrt_castop_rec n1 cx1 c1) = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_castop_rec_close_castop_wrt_castop_rec :
forall c1 cx1 n1,
  open_castop_wrt_castop_rec n1 (c_var_f cx1) (close_castop_wrt_castop_rec n1 cx1 c1) = c1.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_castop_rec_close_castop_wrt_castop_rec : lngen.
#[export] Hint Rewrite open_castop_wrt_castop_rec_close_castop_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (t_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (t_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_castop_rec_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  open_exp_wrt_castop_rec n1 (c_var_f cx1) (close_exp_wrt_castop_rec n1 cx1 e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_castop_rec_close_exp_wrt_castop_rec :
forall e1 cx1 n1,
  open_exp_wrt_castop_rec n1 (c_var_f cx1) (close_exp_wrt_castop_rec n1 cx1 e1) = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_castop_rec_close_exp_wrt_castop_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_castop_rec_close_exp_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (e_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (e_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (t_var_f X1) = A1.
Proof. Admitted.

#[export] Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_castop_wrt_typ_close_castop_wrt_typ :
forall c1 X1,
  open_castop_wrt_typ (close_castop_wrt_typ X1 c1) (t_var_f X1) = c1.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_typ_close_castop_wrt_typ : lngen.
#[export] Hint Rewrite open_castop_wrt_typ_close_castop_wrt_typ using solve [auto] : lngen.

Lemma open_castop_wrt_castop_close_castop_wrt_castop :
forall c1 cx1,
  open_castop_wrt_castop (close_castop_wrt_castop cx1 c1) (c_var_f cx1) = c1.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_castop_close_castop_wrt_castop : lngen.
#[export] Hint Rewrite open_castop_wrt_castop_close_castop_wrt_castop using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (t_var_f X1) = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_castop_close_exp_wrt_castop :
forall e1 cx1,
  open_exp_wrt_castop (close_exp_wrt_castop cx1 e1) (c_var_f cx1) = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_castop_close_exp_wrt_castop : lngen.
#[export] Hint Rewrite open_exp_wrt_castop_close_exp_wrt_castop using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (e_var_f x1) = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 (t_var_f X1) A2 = open_typ_wrt_typ_rec n1 (t_var_f X1) A1 ->
  A2 = A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 (t_var_f X1) A2 = open_typ_wrt_typ_rec n1 (t_var_f X1) A1 ->
  A2 = A1.
Proof. Admitted.

#[export] Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_typ_rec_inj_mutual :
(forall c2 c1 X1 n1,
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop c1 ->
  open_castop_wrt_typ_rec n1 (t_var_f X1) c2 = open_castop_wrt_typ_rec n1 (t_var_f X1) c1 ->
  c2 = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_typ_rec_inj :
forall c2 c1 X1 n1,
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop c1 ->
  open_castop_wrt_typ_rec n1 (t_var_f X1) c2 = open_castop_wrt_typ_rec n1 (t_var_f X1) c1 ->
  c2 = c1.
Proof. Admitted.

#[export] Hint Immediate open_castop_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_castop_rec_inj_mutual :
(forall c2 c1 cx1 n1,
  cx1 `notin` castfv_castop c2 ->
  cx1 `notin` castfv_castop c1 ->
  open_castop_wrt_castop_rec n1 (c_var_f cx1) c2 = open_castop_wrt_castop_rec n1 (c_var_f cx1) c1 ->
  c2 = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_castop_rec_inj :
forall c2 c1 cx1 n1,
  cx1 `notin` castfv_castop c2 ->
  cx1 `notin` castfv_castop c1 ->
  open_castop_wrt_castop_rec n1 (c_var_f cx1) c2 = open_castop_wrt_castop_rec n1 (c_var_f cx1) c1 ->
  c2 = c1.
Proof. Admitted.

#[export] Hint Immediate open_castop_wrt_castop_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 (t_var_f X1) e2 = open_exp_wrt_typ_rec n1 (t_var_f X1) e1 ->
  e2 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 (t_var_f X1) e2 = open_exp_wrt_typ_rec n1 (t_var_f X1) e1 ->
  e2 = e1.
Proof. Admitted.

#[export] Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_castop_rec_inj_mutual :
(forall e2 e1 cx1 n1,
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp e1 ->
  open_exp_wrt_castop_rec n1 (c_var_f cx1) e2 = open_exp_wrt_castop_rec n1 (c_var_f cx1) e1 ->
  e2 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_castop_rec_inj :
forall e2 e1 cx1 n1,
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp e1 ->
  open_exp_wrt_castop_rec n1 (c_var_f cx1) e2 = open_exp_wrt_castop_rec n1 (c_var_f cx1) e1 ->
  e2 = e1.
Proof. Admitted.

#[export] Hint Immediate open_exp_wrt_castop_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 (e_var_f x1) e2 = open_exp_wrt_exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 (e_var_f x1) e2 = open_exp_wrt_exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1.
Proof. Admitted.

#[export] Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ A2 (t_var_f X1) = open_typ_wrt_typ A1 (t_var_f X1) ->
  A2 = A1.
Proof. Admitted.

#[export] Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_castop_wrt_typ_inj :
forall c2 c1 X1,
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop c1 ->
  open_castop_wrt_typ c2 (t_var_f X1) = open_castop_wrt_typ c1 (t_var_f X1) ->
  c2 = c1.
Proof. Admitted.

#[export] Hint Immediate open_castop_wrt_typ_inj : lngen.

Lemma open_castop_wrt_castop_inj :
forall c2 c1 cx1,
  cx1 `notin` castfv_castop c2 ->
  cx1 `notin` castfv_castop c1 ->
  open_castop_wrt_castop c2 (c_var_f cx1) = open_castop_wrt_castop c1 (c_var_f cx1) ->
  c2 = c1.
Proof. Admitted.

#[export] Hint Immediate open_castop_wrt_castop_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ e2 (t_var_f X1) = open_exp_wrt_typ e1 (t_var_f X1) ->
  e2 = e1.
Proof. Admitted.

#[export] Hint Immediate open_exp_wrt_typ_inj : lngen.

Lemma open_exp_wrt_castop_inj :
forall e2 e1 cx1,
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp e1 ->
  open_exp_wrt_castop e2 (c_var_f cx1) = open_exp_wrt_castop e1 (c_var_f cx1) ->
  e2 = e1.
Proof. Admitted.

#[export] Hint Immediate open_exp_wrt_castop_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp e2 (e_var_f x1) = open_exp_wrt_exp e1 (e_var_f x1) ->
  e2 = e1.
Proof. Admitted.

#[export] Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof. Admitted.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof. Admitted.

#[export] Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_castop_wrt_typ_of_lc_castop_mutual :
(forall c1,
  lc_castop c1 ->
  degree_castop_wrt_typ 0 c1).
Proof. Admitted.

(* end hide *)

Lemma degree_castop_wrt_typ_of_lc_castop :
forall c1,
  lc_castop c1 ->
  degree_castop_wrt_typ 0 c1.
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_typ_of_lc_castop : lngen.

(* begin hide *)

Lemma degree_castop_wrt_castop_of_lc_castop_mutual :
(forall c1,
  lc_castop c1 ->
  degree_castop_wrt_castop 0 c1).
Proof. Admitted.

(* end hide *)

Lemma degree_castop_wrt_castop_of_lc_castop :
forall c1,
  lc_castop c1 ->
  degree_castop_wrt_castop 0 c1.
Proof. Admitted.

#[export] Hint Resolve degree_castop_wrt_castop_of_lc_castop : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof. Admitted.

(* end hide *)

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_castop_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_castop 0 e1).
Proof. Admitted.

(* end hide *)

Lemma degree_exp_wrt_castop_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_castop 0 e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_castop_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof. Admitted.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof. Admitted.

#[export] Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof. Admitted.

(* end hide *)

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof. Admitted.

#[export] Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_castop_of_degree_size_mutual :
forall i1,
(forall c1,
  size_castop c1 = i1 ->
  degree_castop_wrt_typ 0 c1 ->
  degree_castop_wrt_castop 0 c1 ->
  lc_castop c1).
Proof. Admitted.

(* end hide *)

Lemma lc_castop_of_degree :
forall c1,
  degree_castop_wrt_typ 0 c1 ->
  degree_castop_wrt_castop 0 c1 ->
  lc_castop c1.
Proof. Admitted.

#[export] Hint Resolve lc_castop_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_castop 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof. Admitted.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_castop 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof. Admitted.

#[export] Hint Resolve lc_exp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac castop_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_castop_wrt_typ_of_lc_castop in J1;
              let J2 := fresh in pose proof H as J2; apply degree_castop_wrt_castop_of_lc_castop in J2; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_castop_of_lc_exp in J2;
              let J3 := fresh in pose proof H as J3; apply degree_exp_wrt_exp_of_lc_exp in J3; clear H
          end).

Ltac mode_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Lemma lc_t_mu_exists :
forall X1 A1,
  lc_typ (open_typ_wrt_typ A1 (t_var_f X1)) ->
  lc_typ (t_mu A1).
Proof. Admitted.

Lemma lc_c_fixc_exists :
forall cx1 c1,
  lc_castop (open_castop_wrt_castop c1 (c_var_f cx1)) ->
  lc_castop (c_fixc c1).
Proof. Admitted.

Lemma lc_e_abs_exists :
forall x1 A1 e1,
  lc_typ A1 ->
  lc_exp (open_exp_wrt_exp e1 (e_var_f x1)) ->
  lc_exp (e_abs A1 e1).
Proof. Admitted.

#[export] Hint Extern 1 (lc_typ (t_mu _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_t_mu_exists X1) : core.

#[export] Hint Extern 1 (lc_castop (c_fixc _)) =>
  let cx1 := fresh in
  pick_fresh cx1;
  apply (lc_c_fixc_exists cx1) : core.

#[export] Hint Extern 1 (lc_exp (e_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_abs_exists x1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof. Admitted.

#[export] Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_castop_wrt_typ :
forall c1 A1,
  body_castop_wrt_typ c1 ->
  lc_typ A1 ->
  lc_castop (open_castop_wrt_typ c1 A1).
Proof. Admitted.

#[export] Hint Resolve lc_body_castop_wrt_typ : lngen.

Lemma lc_body_castop_wrt_castop :
forall c1 c2,
  body_castop_wrt_castop c1 ->
  lc_castop c2 ->
  lc_castop (open_castop_wrt_castop c1 c2).
Proof. Admitted.

#[export] Hint Resolve lc_body_castop_wrt_castop : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 A1,
  body_exp_wrt_typ e1 ->
  lc_typ A1 ->
  lc_exp (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve lc_body_exp_wrt_typ : lngen.

Lemma lc_body_exp_wrt_castop :
forall e1 c1,
  body_exp_wrt_castop e1 ->
  lc_castop c1 ->
  lc_exp (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve lc_body_exp_wrt_castop : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_t_mu_1 :
forall A1,
  lc_typ (t_mu A1) ->
  body_typ_wrt_typ A1.
Proof. Admitted.

#[export] Hint Resolve lc_body_t_mu_1 : lngen.

Lemma lc_body_c_fixc_1 :
forall c1,
  lc_castop (c_fixc c1) ->
  body_castop_wrt_castop c1.
Proof. Admitted.

#[export] Hint Resolve lc_body_c_fixc_1 : lngen.

Lemma lc_body_e_abs_2 :
forall A1 e1,
  lc_exp (e_abs A1 e1) ->
  body_exp_wrt_exp e1.
Proof. Admitted.

#[export] Hint Resolve lc_body_e_abs_2 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof. Admitted.

#[export] Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_castop_unique_mutual :
(forall c1 (proof2 proof3 : lc_castop c1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_castop_unique :
forall c1 (proof2 proof3 : lc_castop c1), proof2 = proof3.
Proof. Admitted.

#[export] Hint Resolve lc_castop_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof. Admitted.

#[export] Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof. Admitted.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof. Admitted.

#[export] Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_castop_of_lc_set_castop_mutual :
(forall c1, lc_set_castop c1 -> lc_castop c1).
Proof. Admitted.

(* end hide *)

Lemma lc_castop_of_lc_set_castop :
forall c1, lc_set_castop c1 -> lc_castop c1.
Proof. Admitted.

#[export] Hint Resolve lc_castop_of_lc_set_castop : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof. Admitted.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof. Admitted.

#[export] Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof. Admitted.

#[export] Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_castop_of_lc_castop_size_mutual :
forall i1,
(forall c1,
  size_castop c1 = i1 ->
  lc_castop c1 ->
  lc_set_castop c1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_castop_of_lc_castop :
forall c1,
  lc_castop c1 ->
  lc_set_castop c1.
Proof. Admitted.

#[export] Hint Resolve lc_set_castop_of_lc_castop : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof. Admitted.

#[export] Hint Resolve lc_set_exp_of_lc_exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof. Admitted.

#[export] Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_typ_rec_degree_castop_wrt_typ_mutual :
(forall c1 X1 n1,
  degree_castop_wrt_typ n1 c1 ->
  X1 `notin` typefv_castop c1 ->
  close_castop_wrt_typ_rec n1 X1 c1 = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_typ_rec_degree_castop_wrt_typ :
forall c1 X1 n1,
  degree_castop_wrt_typ n1 c1 ->
  X1 `notin` typefv_castop c1 ->
  close_castop_wrt_typ_rec n1 X1 c1 = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_typ_rec_degree_castop_wrt_typ : lngen.
#[export] Hint Rewrite close_castop_wrt_typ_rec_degree_castop_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_castop_rec_degree_castop_wrt_castop_mutual :
(forall c1 cx1 n1,
  degree_castop_wrt_castop n1 c1 ->
  cx1 `notin` castfv_castop c1 ->
  close_castop_wrt_castop_rec n1 cx1 c1 = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_castop_wrt_castop_rec_degree_castop_wrt_castop :
forall c1 cx1 n1,
  degree_castop_wrt_castop n1 c1 ->
  cx1 `notin` castfv_castop c1 ->
  close_castop_wrt_castop_rec n1 cx1 c1 = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_castop_rec_degree_castop_wrt_castop : lngen.
#[export] Hint Rewrite close_castop_wrt_castop_rec_degree_castop_wrt_castop using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_castop_rec_degree_exp_wrt_castop_mutual :
(forall e1 cx1 n1,
  degree_exp_wrt_castop n1 e1 ->
  cx1 `notin` castfv_exp e1 ->
  close_exp_wrt_castop_rec n1 cx1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_castop_rec_degree_exp_wrt_castop :
forall e1 cx1 n1,
  degree_exp_wrt_castop n1 e1 ->
  cx1 `notin` castfv_exp e1 ->
  close_exp_wrt_castop_rec n1 cx1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_castop_rec_degree_exp_wrt_castop : lngen.
#[export] Hint Rewrite close_exp_wrt_castop_rec_degree_exp_wrt_castop using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` typefv_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof. Admitted.

#[export] Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_castop_wrt_typ_lc_castop :
forall c1 X1,
  lc_castop c1 ->
  X1 `notin` typefv_castop c1 ->
  close_castop_wrt_typ X1 c1 = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_typ_lc_castop : lngen.
#[export] Hint Rewrite close_castop_wrt_typ_lc_castop using solve [auto] : lngen.

Lemma close_castop_wrt_castop_lc_castop :
forall c1 cx1,
  lc_castop c1 ->
  cx1 `notin` castfv_castop c1 ->
  close_castop_wrt_castop cx1 c1 = c1.
Proof. Admitted.

#[export] Hint Resolve close_castop_wrt_castop_lc_castop : lngen.
#[export] Hint Rewrite close_castop_wrt_castop_lc_castop using solve [auto] : lngen.

Lemma close_exp_wrt_typ_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` typefv_exp e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_castop_lc_exp :
forall e1 cx1,
  lc_exp e1 ->
  cx1 `notin` castfv_exp e1 ->
  close_exp_wrt_castop cx1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_castop_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_castop_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` termfv_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof. Admitted.

#[export] Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_typ_rec_degree_castop_wrt_typ_mutual :
(forall c1 A1 n1,
  degree_castop_wrt_typ n1 c1 ->
  open_castop_wrt_typ_rec n1 A1 c1 = c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_typ_rec_degree_castop_wrt_typ :
forall c1 A1 n1,
  degree_castop_wrt_typ n1 c1 ->
  open_castop_wrt_typ_rec n1 A1 c1 = c1.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_typ_rec_degree_castop_wrt_typ : lngen.
#[export] Hint Rewrite open_castop_wrt_typ_rec_degree_castop_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_castop_rec_degree_castop_wrt_castop_mutual :
(forall c2 c1 n1,
  degree_castop_wrt_castop n1 c2 ->
  open_castop_wrt_castop_rec n1 c1 c2 = c2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_castop_wrt_castop_rec_degree_castop_wrt_castop :
forall c2 c1 n1,
  degree_castop_wrt_castop n1 c2 ->
  open_castop_wrt_castop_rec n1 c1 c2 = c2.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_castop_rec_degree_castop_wrt_castop : lngen.
#[export] Hint Rewrite open_castop_wrt_castop_rec_degree_castop_wrt_castop using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_castop_rec_degree_exp_wrt_castop_mutual :
(forall e1 c1 n1,
  degree_exp_wrt_castop n1 e1 ->
  open_exp_wrt_castop_rec n1 c1 e1 = e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_castop_rec_degree_exp_wrt_castop :
forall e1 c1 n1,
  degree_exp_wrt_castop n1 e1 ->
  open_exp_wrt_castop_rec n1 c1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_castop_rec_degree_exp_wrt_castop : lngen.
#[export] Hint Rewrite open_exp_wrt_castop_rec_degree_exp_wrt_castop using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof. Admitted.

#[export] Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_castop_wrt_typ_lc_castop :
forall c1 A1,
  lc_castop c1 ->
  open_castop_wrt_typ c1 A1 = c1.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_typ_lc_castop : lngen.
#[export] Hint Rewrite open_castop_wrt_typ_lc_castop using solve [auto] : lngen.

Lemma open_castop_wrt_castop_lc_castop :
forall c2 c1,
  lc_castop c2 ->
  open_castop_wrt_castop c2 c1 = c2.
Proof. Admitted.

#[export] Hint Resolve open_castop_wrt_castop_lc_castop : lngen.
#[export] Hint Rewrite open_castop_wrt_castop_lc_castop using solve [auto] : lngen.

Lemma open_exp_wrt_typ_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 A1 = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_castop_lc_exp :
forall e1 c1,
  lc_exp e1 ->
  open_exp_wrt_castop e1 c1 = e1.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_castop_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_castop_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof. Admitted.

#[export] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typefv_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  typefv_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (typefv_typ A1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  typefv_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (typefv_typ A1).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite typefv_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_close_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  typefv_castop (close_castop_wrt_typ_rec n1 X1 c1) [=] remove X1 (typefv_castop c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_close_castop_wrt_typ_rec :
forall c1 X1 n1,
  typefv_castop (close_castop_wrt_typ_rec n1 X1 c1) [=] remove X1 (typefv_castop c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_close_castop_wrt_typ_rec : lngen.
#[export] Hint Rewrite typefv_castop_close_castop_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_close_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1,
  typefv_castop (close_castop_wrt_castop_rec n1 cx1 c1) [=] typefv_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_close_castop_wrt_castop_rec :
forall c1 cx1 n1,
  typefv_castop (close_castop_wrt_castop_rec n1 cx1 c1) [=] typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_close_castop_wrt_castop_rec : lngen.
#[export] Hint Rewrite typefv_castop_close_castop_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_close_castop_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  castfv_castop (close_castop_wrt_typ_rec n1 X1 c1) [=] castfv_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_close_castop_wrt_typ_rec :
forall c1 X1 n1,
  castfv_castop (close_castop_wrt_typ_rec n1 X1 c1) [=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_close_castop_wrt_typ_rec : lngen.
#[export] Hint Rewrite castfv_castop_close_castop_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_close_castop_wrt_castop_rec_mutual :
(forall c1 cx1 n1,
  castfv_castop (close_castop_wrt_castop_rec n1 cx1 c1) [=] remove cx1 (castfv_castop c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_close_castop_wrt_castop_rec :
forall c1 cx1 n1,
  castfv_castop (close_castop_wrt_castop_rec n1 cx1 c1) [=] remove cx1 (castfv_castop c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_close_castop_wrt_castop_rec : lngen.
#[export] Hint Rewrite castfv_castop_close_castop_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  typefv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (typefv_exp e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  typefv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (typefv_exp e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite typefv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  typefv_exp (close_exp_wrt_castop_rec n1 cx1 e1) [=] typefv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_castop_rec :
forall e1 cx1 n1,
  typefv_exp (close_exp_wrt_castop_rec n1 cx1 e1) [=] typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_close_exp_wrt_castop_rec : lngen.
#[export] Hint Rewrite typefv_exp_close_exp_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  typefv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] typefv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  typefv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite typefv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  castfv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] castfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  castfv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite castfv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  castfv_exp (close_exp_wrt_castop_rec n1 cx1 e1) [=] remove cx1 (castfv_exp e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_close_exp_wrt_castop_rec :
forall e1 cx1 n1,
  castfv_exp (close_exp_wrt_castop_rec n1 cx1 e1) [=] remove cx1 (castfv_exp e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_close_exp_wrt_castop_rec : lngen.
#[export] Hint Rewrite castfv_exp_close_exp_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  castfv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] castfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  castfv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite castfv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  termfv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  termfv_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite termfv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 cx1 n1,
  termfv_exp (close_exp_wrt_castop_rec n1 cx1 e1) [=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_castop_rec :
forall e1 cx1 n1,
  termfv_exp (close_exp_wrt_castop_rec n1 cx1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_close_exp_wrt_castop_rec : lngen.
#[export] Hint Rewrite termfv_exp_close_exp_wrt_castop_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  termfv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (termfv_exp e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  termfv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (termfv_exp e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite termfv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma typefv_typ_close_typ_wrt_typ :
forall A1 X1,
  typefv_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (typefv_typ A1).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite typefv_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma typefv_castop_close_castop_wrt_typ :
forall c1 X1,
  typefv_castop (close_castop_wrt_typ X1 c1) [=] remove X1 (typefv_castop c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_close_castop_wrt_typ : lngen.
#[export] Hint Rewrite typefv_castop_close_castop_wrt_typ using solve [auto] : lngen.

Lemma typefv_castop_close_castop_wrt_castop :
forall c1 cx1,
  typefv_castop (close_castop_wrt_castop cx1 c1) [=] typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_close_castop_wrt_castop : lngen.
#[export] Hint Rewrite typefv_castop_close_castop_wrt_castop using solve [auto] : lngen.

Lemma castfv_castop_close_castop_wrt_typ :
forall c1 X1,
  castfv_castop (close_castop_wrt_typ X1 c1) [=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_close_castop_wrt_typ : lngen.
#[export] Hint Rewrite castfv_castop_close_castop_wrt_typ using solve [auto] : lngen.

Lemma castfv_castop_close_castop_wrt_castop :
forall c1 cx1,
  castfv_castop (close_castop_wrt_castop cx1 c1) [=] remove cx1 (castfv_castop c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_close_castop_wrt_castop : lngen.
#[export] Hint Rewrite castfv_castop_close_castop_wrt_castop using solve [auto] : lngen.

Lemma typefv_exp_close_exp_wrt_typ :
forall e1 X1,
  typefv_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (typefv_exp e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite typefv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma typefv_exp_close_exp_wrt_castop :
forall e1 cx1,
  typefv_exp (close_exp_wrt_castop cx1 e1) [=] typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_close_exp_wrt_castop : lngen.
#[export] Hint Rewrite typefv_exp_close_exp_wrt_castop using solve [auto] : lngen.

Lemma typefv_exp_close_exp_wrt_exp :
forall e1 x1,
  typefv_exp (close_exp_wrt_exp x1 e1) [=] typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite typefv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma castfv_exp_close_exp_wrt_typ :
forall e1 X1,
  castfv_exp (close_exp_wrt_typ X1 e1) [=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite castfv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma castfv_exp_close_exp_wrt_castop :
forall e1 cx1,
  castfv_exp (close_exp_wrt_castop cx1 e1) [=] remove cx1 (castfv_exp e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_close_exp_wrt_castop : lngen.
#[export] Hint Rewrite castfv_exp_close_exp_wrt_castop using solve [auto] : lngen.

Lemma castfv_exp_close_exp_wrt_exp :
forall e1 x1,
  castfv_exp (close_exp_wrt_exp x1 e1) [=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite castfv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma termfv_exp_close_exp_wrt_typ :
forall e1 X1,
  termfv_exp (close_exp_wrt_typ X1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite termfv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma termfv_exp_close_exp_wrt_castop :
forall e1 cx1,
  termfv_exp (close_exp_wrt_castop cx1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_close_exp_wrt_castop : lngen.
#[export] Hint Rewrite termfv_exp_close_exp_wrt_castop using solve [auto] : lngen.

Lemma termfv_exp_close_exp_wrt_exp :
forall e1 x1,
  termfv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (termfv_exp e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite termfv_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_typ_rec_lower_mutual :
(forall c1 A1 n1,
  typefv_castop c1 [<=] typefv_castop (open_castop_wrt_typ_rec n1 A1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_typ_rec_lower :
forall c1 A1 n1,
  typefv_castop c1 [<=] typefv_castop (open_castop_wrt_typ_rec n1 A1 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_castop_rec_lower_mutual :
(forall c1 c2 n1,
  typefv_castop c1 [<=] typefv_castop (open_castop_wrt_castop_rec n1 c2 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_castop_rec_lower :
forall c1 c2 n1,
  typefv_castop c1 [<=] typefv_castop (open_castop_wrt_castop_rec n1 c2 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_castop_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_typ_rec_lower_mutual :
(forall c1 A1 n1,
  castfv_castop c1 [<=] castfv_castop (open_castop_wrt_typ_rec n1 A1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_typ_rec_lower :
forall c1 A1 n1,
  castfv_castop c1 [<=] castfv_castop (open_castop_wrt_typ_rec n1 A1 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_castop_rec_lower_mutual :
(forall c1 c2 n1,
  castfv_castop c1 [<=] castfv_castop (open_castop_wrt_castop_rec n1 c2 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_castop_rec_lower :
forall c1 c2 n1,
  castfv_castop c1 [<=] castfv_castop (open_castop_wrt_castop_rec n1 c2 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_castop_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_castop_rec_lower_mutual :
(forall e1 c1 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_castop_rec n1 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_castop_rec_lower :
forall e1 c1 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_castop_rec n1 c1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_castop_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_castop_rec_lower_mutual :
(forall e1 c1 n1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_castop_rec n1 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_castop_rec_lower :
forall e1 c1 n1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_castop_rec n1 c1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_castop_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_castop_rec_lower_mutual :
(forall e1 c1 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_castop_rec n1 c1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_castop_rec_lower :
forall e1 c1 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_castop_rec n1 c1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_castop_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma typefv_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  typefv_typ A1 [<=] typefv_typ (open_typ_wrt_typ A1 A2).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_open_typ_wrt_typ_lower : lngen.

Lemma typefv_castop_open_castop_wrt_typ_lower :
forall c1 A1,
  typefv_castop c1 [<=] typefv_castop (open_castop_wrt_typ c1 A1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_typ_lower : lngen.

Lemma typefv_castop_open_castop_wrt_castop_lower :
forall c1 c2,
  typefv_castop c1 [<=] typefv_castop (open_castop_wrt_castop c1 c2).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_castop_lower : lngen.

Lemma castfv_castop_open_castop_wrt_typ_lower :
forall c1 A1,
  castfv_castop c1 [<=] castfv_castop (open_castop_wrt_typ c1 A1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_typ_lower : lngen.

Lemma castfv_castop_open_castop_wrt_castop_lower :
forall c1 c2,
  castfv_castop c1 [<=] castfv_castop (open_castop_wrt_castop c1 c2).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_castop_lower : lngen.

Lemma typefv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_typ_lower : lngen.

Lemma typefv_exp_open_exp_wrt_castop_lower :
forall e1 c1,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_castop_lower : lngen.

Lemma typefv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  typefv_exp e1 [<=] typefv_exp (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_exp_lower : lngen.

Lemma castfv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_typ_lower : lngen.

Lemma castfv_exp_open_exp_wrt_castop_lower :
forall e1 c1,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_castop_lower : lngen.

Lemma castfv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  castfv_exp e1 [<=] castfv_exp (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_exp_lower : lngen.

Lemma termfv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_typ e1 A1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_typ_lower : lngen.

Lemma termfv_exp_open_exp_wrt_castop_lower :
forall e1 c1,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_castop e1 c1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_castop_lower : lngen.

Lemma termfv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  termfv_exp e1 [<=] termfv_exp (open_exp_wrt_exp e1 e2).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  typefv_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] typefv_typ A2 `union` typefv_typ A1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  typefv_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] typefv_typ A2 `union` typefv_typ A1.
Proof. Admitted.

#[export] Hint Resolve typefv_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_typ_rec_upper_mutual :
(forall c1 A1 n1,
  typefv_castop (open_castop_wrt_typ_rec n1 A1 c1) [<=] typefv_typ A1 `union` typefv_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_typ_rec_upper :
forall c1 A1 n1,
  typefv_castop (open_castop_wrt_typ_rec n1 A1 c1) [<=] typefv_typ A1 `union` typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_castop_rec_upper_mutual :
(forall c1 c2 n1,
  typefv_castop (open_castop_wrt_castop_rec n1 c2 c1) [<=] typefv_castop c2 `union` typefv_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_castop_open_castop_wrt_castop_rec_upper :
forall c1 c2 n1,
  typefv_castop (open_castop_wrt_castop_rec n1 c2 c1) [<=] typefv_castop c2 `union` typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_castop_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_typ_rec_upper_mutual :
(forall c1 A1 n1,
  castfv_castop (open_castop_wrt_typ_rec n1 A1 c1) [<=] castfv_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_typ_rec_upper :
forall c1 A1 n1,
  castfv_castop (open_castop_wrt_typ_rec n1 A1 c1) [<=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_castop_rec_upper_mutual :
(forall c1 c2 n1,
  castfv_castop (open_castop_wrt_castop_rec n1 c2 c1) [<=] castfv_castop c2 `union` castfv_castop c1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_castop_open_castop_wrt_castop_rec_upper :
forall c1 c2 n1,
  castfv_castop (open_castop_wrt_castop_rec n1 c2 c1) [<=] castfv_castop c2 `union` castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_castop_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  typefv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] typefv_typ A1 `union` typefv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  typefv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] typefv_typ A1 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_castop_rec_upper_mutual :
(forall e1 c1 n1,
  typefv_exp (open_exp_wrt_castop_rec n1 c1 e1) [<=] typefv_castop c1 `union` typefv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_castop_rec_upper :
forall e1 c1 n1,
  typefv_exp (open_exp_wrt_castop_rec n1 c1 e1) [<=] typefv_castop c1 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_castop_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  typefv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] typefv_exp e2 `union` typefv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typefv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  typefv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] typefv_exp e2 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  castfv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] castfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  castfv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_castop_rec_upper_mutual :
(forall e1 c1 n1,
  castfv_exp (open_exp_wrt_castop_rec n1 c1 e1) [<=] castfv_castop c1 `union` castfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_castop_rec_upper :
forall e1 c1 n1,
  castfv_exp (open_exp_wrt_castop_rec n1 c1 e1) [<=] castfv_castop c1 `union` castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_castop_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  castfv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] castfv_exp e2 `union` castfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castfv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  castfv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] castfv_exp e2 `union` castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  termfv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  termfv_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_castop_rec_upper_mutual :
(forall e1 c1 n1,
  termfv_exp (open_exp_wrt_castop_rec n1 c1 e1) [<=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_castop_rec_upper :
forall e1 c1 n1,
  termfv_exp (open_exp_wrt_castop_rec n1 c1 e1) [<=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_castop_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  termfv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] termfv_exp e2 `union` termfv_exp e1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma termfv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  termfv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] termfv_exp e2 `union` termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma typefv_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  typefv_typ (open_typ_wrt_typ A1 A2) [<=] typefv_typ A2 `union` typefv_typ A1.
Proof. Admitted.

#[export] Hint Resolve typefv_typ_open_typ_wrt_typ_upper : lngen.

Lemma typefv_castop_open_castop_wrt_typ_upper :
forall c1 A1,
  typefv_castop (open_castop_wrt_typ c1 A1) [<=] typefv_typ A1 `union` typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_typ_upper : lngen.

Lemma typefv_castop_open_castop_wrt_castop_upper :
forall c1 c2,
  typefv_castop (open_castop_wrt_castop c1 c2) [<=] typefv_castop c2 `union` typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_open_castop_wrt_castop_upper : lngen.

Lemma castfv_castop_open_castop_wrt_typ_upper :
forall c1 A1,
  castfv_castop (open_castop_wrt_typ c1 A1) [<=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_typ_upper : lngen.

Lemma castfv_castop_open_castop_wrt_castop_upper :
forall c1 c2,
  castfv_castop (open_castop_wrt_castop c1 c2) [<=] castfv_castop c2 `union` castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_open_castop_wrt_castop_upper : lngen.

Lemma typefv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  typefv_exp (open_exp_wrt_typ e1 A1) [<=] typefv_typ A1 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_typ_upper : lngen.

Lemma typefv_exp_open_exp_wrt_castop_upper :
forall e1 c1,
  typefv_exp (open_exp_wrt_castop e1 c1) [<=] typefv_castop c1 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_castop_upper : lngen.

Lemma typefv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  typefv_exp (open_exp_wrt_exp e1 e2) [<=] typefv_exp e2 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_open_exp_wrt_exp_upper : lngen.

Lemma castfv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  castfv_exp (open_exp_wrt_typ e1 A1) [<=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_typ_upper : lngen.

Lemma castfv_exp_open_exp_wrt_castop_upper :
forall e1 c1,
  castfv_exp (open_exp_wrt_castop e1 c1) [<=] castfv_castop c1 `union` castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_castop_upper : lngen.

Lemma castfv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  castfv_exp (open_exp_wrt_exp e1 e2) [<=] castfv_exp e2 `union` castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_open_exp_wrt_exp_upper : lngen.

Lemma termfv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  termfv_exp (open_exp_wrt_typ e1 A1) [<=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_typ_upper : lngen.

Lemma termfv_exp_open_exp_wrt_castop_upper :
forall e1 c1,
  termfv_exp (open_exp_wrt_castop e1 c1) [<=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_castop_upper : lngen.

Lemma termfv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  termfv_exp (open_exp_wrt_exp e1 e2) [<=] termfv_exp e2 `union` termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` typefv_typ A1 ->
  typefv_typ (typsubst_typ A2 X1 A1) [=] typefv_typ A1).
Proof. Admitted.

(* end hide *)

Lemma typefv_typ_typsubst_typ_fresh :
forall A1 A2 X1,
  X1 `notin` typefv_typ A1 ->
  typefv_typ (typsubst_typ A2 X1 A1) [=] typefv_typ A1.
Proof. Admitted.

#[export] Hint Resolve typefv_typ_typsubst_typ_fresh : lngen.
#[export] Hint Rewrite typefv_typ_typsubst_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_castop_typsubst_castop_fresh_mutual :
(forall c1 A1 X1,
  X1 `notin` typefv_castop c1 ->
  typefv_castop (typsubst_castop A1 X1 c1) [=] typefv_castop c1).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_typsubst_castop_fresh :
forall c1 A1 X1,
  X1 `notin` typefv_castop c1 ->
  typefv_castop (typsubst_castop A1 X1 c1) [=] typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_typsubst_castop_fresh : lngen.
#[export] Hint Rewrite typefv_castop_typsubst_castop_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_castop_castsubst_castop_fresh_mutual :
(forall c1 A1 X1,
  castfv_castop (typsubst_castop A1 X1 c1) [=] castfv_castop c1).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_castsubst_castop_fresh :
forall c1 A1 X1,
  castfv_castop (typsubst_castop A1 X1 c1) [=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_castsubst_castop_fresh : lngen.
#[export] Hint Rewrite typefv_castop_castsubst_castop_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma castfv_castop_castsubst_castop_fresh_mutual :
(forall c1 c2 cx1,
  cx1 `notin` castfv_castop c1 ->
  castfv_castop (castsubst_castop c2 cx1 c1) [=] castfv_castop c1).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_castsubst_castop_fresh :
forall c1 c2 cx1,
  cx1 `notin` castfv_castop c1 ->
  castfv_castop (castsubst_castop c2 cx1 c1) [=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_castsubst_castop_fresh : lngen.
#[export] Hint Rewrite castfv_castop_castsubst_castop_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typefv_exp (typsubst_exp A1 X1 e1) [=] typefv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_typsubst_exp_fresh :
forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typefv_exp (typsubst_exp A1 X1 e1) [=] typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_typsubst_exp_fresh : lngen.
#[export] Hint Rewrite typefv_exp_typsubst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_exp_castsubst_exp_fresh_mutual :
(forall e1 A1 X1,
  castfv_exp (typsubst_exp A1 X1 e1) [=] castfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_castsubst_exp_fresh :
forall e1 A1 X1,
  castfv_exp (typsubst_exp A1 X1 e1) [=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_castsubst_exp_fresh : lngen.
#[export] Hint Rewrite typefv_exp_castsubst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_fresh_mutual :
(forall e1 c1 cx1,
  cx1 `notin` castfv_exp e1 ->
  castfv_exp (castsubst_exp c1 cx1 e1) [=] castfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_subst_exp_fresh :
forall e1 c1 cx1,
  cx1 `notin` castfv_exp e1 ->
  castfv_exp (castsubst_exp c1 cx1 e1) [=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_subst_exp_fresh : lngen.
#[export] Hint Rewrite typefv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma castfv_exp_castsubst_exp_fresh_mutual :
(forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_castsubst_exp_fresh :
forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_castsubst_exp_fresh : lngen.
#[export] Hint Rewrite castfv_exp_castsubst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma castfv_exp_subst_exp_fresh_mutual :
(forall e1 c1 cx1,
  termfv_exp (castsubst_exp c1 cx1 e1) [=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_subst_exp_fresh :
forall e1 c1 cx1,
  termfv_exp (castsubst_exp c1 cx1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_subst_exp_fresh : lngen.
#[export] Hint Rewrite castfv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` termfv_exp e1 ->
  termfv_exp (subst_exp e2 x1 e1) [=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_subst_exp_fresh :
forall e1 e2 x1,
  x1 `notin` termfv_exp e1 ->
  termfv_exp (subst_exp e2 x1 e1) [=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_subst_exp_fresh : lngen.
#[export] Hint Rewrite termfv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (typefv_typ A1) [<=] typefv_typ (typsubst_typ A2 X1 A1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_typ_typsubst_typ_lower :
forall A1 A2 X1,
  remove X1 (typefv_typ A1) [<=] typefv_typ (typsubst_typ A2 X1 A1).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_typsubst_typ_lower : lngen.

(* begin hide *)

Lemma typefv_castop_typsubst_castop_lower_mutual :
(forall c1 A1 X1,
  remove X1 (typefv_castop c1) [<=] typefv_castop (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_typsubst_castop_lower :
forall c1 A1 X1,
  remove X1 (typefv_castop c1) [<=] typefv_castop (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_typsubst_castop_lower : lngen.

(* begin hide *)

Lemma typefv_castop_castsubst_castop_lower_mutual :
(forall c1 c2 cx1,
  typefv_castop c1 [<=] typefv_castop (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_castsubst_castop_lower :
forall c1 c2 cx1,
  typefv_castop c1 [<=] typefv_castop (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_castsubst_castop_lower : lngen.

(* begin hide *)

Lemma castfv_castop_typsubst_castop_lower_mutual :
(forall c1 A1 X1,
  castfv_castop c1 [<=] castfv_castop (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_typsubst_castop_lower :
forall c1 A1 X1,
  castfv_castop c1 [<=] castfv_castop (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_typsubst_castop_lower : lngen.

(* begin hide *)

Lemma castfv_castop_castsubst_castop_lower_mutual :
(forall c1 c2 cx1,
  remove cx1 (castfv_castop c1) [<=] castfv_castop (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_castsubst_castop_lower :
forall c1 c2 cx1,
  remove cx1 (castfv_castop c1) [<=] castfv_castop (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_castsubst_castop_lower : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (typefv_exp e1) [<=] typefv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_typsubst_exp_lower :
forall e1 A1 X1,
  remove X1 (typefv_exp e1) [<=] typefv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_typsubst_exp_lower : lngen.

(* begin hide *)

Lemma typefv_exp_castsubst_exp_lower_mutual :
(forall e1 c1 cx1,
  typefv_exp e1 [<=] typefv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_castsubst_exp_lower :
forall e1 c1 cx1,
  typefv_exp e1 [<=] typefv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_castsubst_exp_lower : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  typefv_exp e1 [<=] typefv_exp (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_subst_exp_lower :
forall e1 e2 x1,
  typefv_exp e1 [<=] typefv_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma castfv_exp_typsubst_exp_lower_mutual :
(forall e1 A1 X1,
  castfv_exp e1 [<=] castfv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_typsubst_exp_lower :
forall e1 A1 X1,
  castfv_exp e1 [<=] castfv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_typsubst_exp_lower : lngen.

(* begin hide *)

Lemma castfv_exp_castsubst_exp_lower_mutual :
(forall e1 c1 cx1,
  remove cx1 (castfv_exp e1) [<=] castfv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_castsubst_exp_lower :
forall e1 c1 cx1,
  remove cx1 (castfv_exp e1) [<=] castfv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_castsubst_exp_lower : lngen.

(* begin hide *)

Lemma castfv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  castfv_exp e1 [<=] castfv_exp (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_subst_exp_lower :
forall e1 e2 x1,
  castfv_exp e1 [<=] castfv_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma termfv_exp_typsubst_exp_lower_mutual :
(forall e1 A1 X1,
  termfv_exp e1 [<=] termfv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_typsubst_exp_lower :
forall e1 A1 X1,
  termfv_exp e1 [<=] termfv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_typsubst_exp_lower : lngen.

(* begin hide *)

Lemma termfv_exp_castsubst_exp_lower_mutual :
(forall e1 c1 cx1,
  termfv_exp e1 [<=] termfv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_castsubst_exp_lower :
forall e1 c1 cx1,
  termfv_exp e1 [<=] termfv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_castsubst_exp_lower : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (termfv_exp e1) [<=] termfv_exp (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_subst_exp_lower :
forall e1 e2 x1,
  remove x1 (termfv_exp e1) [<=] termfv_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ (typsubst_typ A2 X1 A1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_typ_typsubst_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ (typsubst_typ A2 X1 A1).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_typsubst_typ_notin : lngen.

(* begin hide *)

Lemma typefv_castop_typsubst_castop_notin_mutual :
(forall c1 A1 X1 X2,
  X2 `notin` typefv_castop c1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_castop (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_typsubst_castop_notin :
forall c1 A1 X1 X2,
  X2 `notin` typefv_castop c1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_castop (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_typsubst_castop_notin : lngen.

(* begin hide *)

Lemma typefv_castop_castsubst_castop_notin_mutual :
(forall c1 c2 cx1 X1,
  X1 `notin` typefv_castop c1 ->
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_castsubst_castop_notin :
forall c1 c2 cx1 X1,
  X1 `notin` typefv_castop c1 ->
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_castsubst_castop_notin : lngen.

(* begin hide *)

Lemma castfv_castop_typsubst_castop_notin_mutual :
(forall c1 A1 X1 cx1,
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_castop (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_typsubst_castop_notin :
forall c1 A1 X1 cx1,
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_castop (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_typsubst_castop_notin : lngen.

(* begin hide *)

Lemma castfv_castop_castsubst_castop_notin_mutual :
(forall c1 c2 cx1 cx2,
  cx2 `notin` castfv_castop c1 ->
  cx2 `notin` castfv_castop c2 ->
  cx2 `notin` castfv_castop (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_castsubst_castop_notin :
forall c1 c2 cx1 cx2,
  cx2 `notin` castfv_castop c1 ->
  cx2 `notin` castfv_castop c2 ->
  cx2 `notin` castfv_castop (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_castsubst_castop_notin : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_typsubst_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 `notin` typefv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_typsubst_exp_notin : lngen.

(* begin hide *)

Lemma typefv_exp_castsubst_exp_notin_mutual :
(forall e1 c1 cx1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_castop c1 ->
  X1 `notin` typefv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_castsubst_exp_notin :
forall e1 c1 cx1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_castop c1 ->
  X1 `notin` typefv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_castsubst_exp_notin : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_subst_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma castfv_exp_typsubst_exp_notin_mutual :
(forall e1 A1 X1 cx1,
  cx1 `notin` castfv_exp e1 ->
  cx1 `notin` castfv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_typsubst_exp_notin :
forall e1 A1 X1 cx1,
  cx1 `notin` castfv_exp e1 ->
  cx1 `notin` castfv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_typsubst_exp_notin : lngen.

(* begin hide *)

Lemma castfv_exp_castsubst_exp_notin_mutual :
(forall e1 c1 cx1 cx2,
  cx2 `notin` castfv_exp e1 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 `notin` castfv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_castsubst_exp_notin :
forall e1 c1 cx1 cx2,
  cx2 `notin` castfv_exp e1 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 `notin` castfv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_castsubst_exp_notin : lngen.

(* begin hide *)

Lemma castfv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 cx1,
  cx1 `notin` castfv_exp e1 ->
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_subst_exp_notin :
forall e1 e2 x1 cx1,
  cx1 `notin` castfv_exp e1 ->
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma termfv_exp_typsubst_exp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_typsubst_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_typsubst_exp_notin : lngen.

(* begin hide *)

Lemma termfv_exp_castsubst_exp_notin_mutual :
(forall e1 c1 cx1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_castsubst_exp_notin :
forall e1 c1 cx1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_castsubst_exp_notin : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` termfv_exp e1 ->
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_subst_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` termfv_exp e1 ->
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma typefv_typ_typsubst_typ_upper_mutual :
(forall A1 A2 X1,
  typefv_typ (typsubst_typ A2 X1 A1) [<=] typefv_typ A2 `union` remove X1 (typefv_typ A1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_typ_typsubst_typ_upper :
forall A1 A2 X1,
  typefv_typ (typsubst_typ A2 X1 A1) [<=] typefv_typ A2 `union` remove X1 (typefv_typ A1).
Proof. Admitted.

#[export] Hint Resolve typefv_typ_typsubst_typ_upper : lngen.

(* begin hide *)

Lemma typefv_castop_typsubst_castop_upper_mutual :
(forall c1 A1 X1,
  typefv_castop (typsubst_castop A1 X1 c1) [<=] typefv_typ A1 `union` remove X1 (typefv_castop c1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_typsubst_castop_upper :
forall c1 A1 X1,
  typefv_castop (typsubst_castop A1 X1 c1) [<=] typefv_typ A1 `union` remove X1 (typefv_castop c1).
Proof. Admitted.

#[export] Hint Resolve typefv_castop_typsubst_castop_upper : lngen.

(* begin hide *)

Lemma typefv_castop_castsubst_castop_upper_mutual :
(forall c1 c2 cx1,
  typefv_castop (castsubst_castop c2 cx1 c1) [<=] typefv_castop c2 `union` typefv_castop c1).
Proof. Admitted.

(* end hide *)

Lemma typefv_castop_castsubst_castop_upper :
forall c1 c2 cx1,
  typefv_castop (castsubst_castop c2 cx1 c1) [<=] typefv_castop c2 `union` typefv_castop c1.
Proof. Admitted.

#[export] Hint Resolve typefv_castop_castsubst_castop_upper : lngen.

(* begin hide *)

Lemma castfv_castop_typsubst_castop_upper_mutual :
(forall c1 A1 X1,
  castfv_castop (typsubst_castop A1 X1 c1) [<=] castfv_castop c1).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_typsubst_castop_upper :
forall c1 A1 X1,
  castfv_castop (typsubst_castop A1 X1 c1) [<=] castfv_castop c1.
Proof. Admitted.

#[export] Hint Resolve castfv_castop_typsubst_castop_upper : lngen.

(* begin hide *)

Lemma castfv_castop_castsubst_castop_upper_mutual :
(forall c1 c2 cx1,
  castfv_castop (castsubst_castop c2 cx1 c1) [<=] castfv_castop c2 `union` remove cx1 (castfv_castop c1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_castop_castsubst_castop_upper :
forall c1 c2 cx1,
  castfv_castop (castsubst_castop c2 cx1 c1) [<=] castfv_castop c2 `union` remove cx1 (castfv_castop c1).
Proof. Admitted.

#[export] Hint Resolve castfv_castop_castsubst_castop_upper : lngen.

(* begin hide *)

Lemma typefv_exp_typsubst_exp_upper_mutual :
(forall e1 A1 X1,
  typefv_exp (typsubst_exp A1 X1 e1) [<=] typefv_typ A1 `union` remove X1 (typefv_exp e1)).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_typsubst_exp_upper :
forall e1 A1 X1,
  typefv_exp (typsubst_exp A1 X1 e1) [<=] typefv_typ A1 `union` remove X1 (typefv_exp e1).
Proof. Admitted.

#[export] Hint Resolve typefv_exp_typsubst_exp_upper : lngen.

(* begin hide *)

Lemma typefv_exp_castsubst_exp_upper_mutual :
(forall e1 c1 cx1,
  typefv_exp (castsubst_exp c1 cx1 e1) [<=] typefv_castop c1 `union` typefv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_castsubst_exp_upper :
forall e1 c1 cx1,
  typefv_exp (castsubst_exp c1 cx1 e1) [<=] typefv_castop c1 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_castsubst_exp_upper : lngen.

(* begin hide *)

Lemma typefv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  typefv_exp (subst_exp e2 x1 e1) [<=] typefv_exp e2 `union` typefv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma typefv_exp_subst_exp_upper :
forall e1 e2 x1,
  typefv_exp (subst_exp e2 x1 e1) [<=] typefv_exp e2 `union` typefv_exp e1.
Proof. Admitted.

#[export] Hint Resolve typefv_exp_subst_exp_upper : lngen.

(* begin hide *)

Lemma castfv_exp_typsubst_exp_upper_mutual :
(forall e1 A1 X1,
  castfv_exp (typsubst_exp A1 X1 e1) [<=] castfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_typsubst_exp_upper :
forall e1 A1 X1,
  castfv_exp (typsubst_exp A1 X1 e1) [<=] castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_typsubst_exp_upper : lngen.

(* begin hide *)

Lemma castfv_exp_castsubst_exp_upper_mutual :
(forall e1 c1 cx1,
  castfv_exp (castsubst_exp c1 cx1 e1) [<=] castfv_castop c1 `union` remove cx1 (castfv_exp e1)).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_castsubst_exp_upper :
forall e1 c1 cx1,
  castfv_exp (castsubst_exp c1 cx1 e1) [<=] castfv_castop c1 `union` remove cx1 (castfv_exp e1).
Proof. Admitted.

#[export] Hint Resolve castfv_exp_castsubst_exp_upper : lngen.

(* begin hide *)

Lemma castfv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  castfv_exp (subst_exp e2 x1 e1) [<=] castfv_exp e2 `union` castfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma castfv_exp_subst_exp_upper :
forall e1 e2 x1,
  castfv_exp (subst_exp e2 x1 e1) [<=] castfv_exp e2 `union` castfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve castfv_exp_subst_exp_upper : lngen.

(* begin hide *)

Lemma termfv_exp_typsubst_exp_upper_mutual :
(forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [<=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_typsubst_exp_upper :
forall e1 A1 X1,
  termfv_exp (typsubst_exp A1 X1 e1) [<=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_typsubst_exp_upper : lngen.

(* begin hide *)

Lemma termfv_exp_castsubst_exp_upper_mutual :
(forall e1 c1 cx1,
  termfv_exp (castsubst_exp c1 cx1 e1) [<=] termfv_exp e1).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_castsubst_exp_upper :
forall e1 c1 cx1,
  termfv_exp (castsubst_exp c1 cx1 e1) [<=] termfv_exp e1.
Proof. Admitted.

#[export] Hint Resolve termfv_exp_castsubst_exp_upper : lngen.

(* begin hide *)

Lemma termfv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  termfv_exp (subst_exp e2 x1 e1) [<=] termfv_exp e2 `union` remove x1 (termfv_exp e1)).
Proof. Admitted.

(* end hide *)

Lemma termfv_exp_subst_exp_upper :
forall e1 e2 x1,
  termfv_exp (subst_exp e2 x1 e1) [<=] termfv_exp e2 `union` remove x1 (termfv_exp e1).
Proof. Admitted.

#[export] Hint Resolve termfv_exp_subst_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 A2)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma typsubst_castop_close_castop_wrt_typ_rec_mutual :
(forall c1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_castop A1 X1 (close_castop_wrt_typ_rec n1 X2 c1) = close_castop_wrt_typ_rec n1 X2 (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_close_castop_wrt_typ_rec :
forall c1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_castop A1 X1 (close_castop_wrt_typ_rec n1 X2 c1) = close_castop_wrt_typ_rec n1 X2 (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_typ_rec : lngen.

(* begin hide *)

Lemma typsubst_castop_close_castop_wrt_castop_rec_mutual :
(forall c1 A1 cx1 X1 n1,
  typsubst_castop A1 cx1 (close_castop_wrt_castop_rec n1 X1 c1) = close_castop_wrt_castop_rec n1 X1 (typsubst_castop A1 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_close_castop_wrt_castop_rec :
forall c1 A1 cx1 X1 n1,
  typsubst_castop A1 cx1 (close_castop_wrt_castop_rec n1 X1 c1) = close_castop_wrt_castop_rec n1 X1 (typsubst_castop A1 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_castop_rec : lngen.

(* begin hide *)

Lemma castsubst_castop_close_castop_wrt_typ_rec_mutual :
(forall c2 c1 X1 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  cx1 `notin` typefv_castop c1 ->
  castsubst_castop c1 X1 (close_castop_wrt_typ_rec n1 cx1 c2) = close_castop_wrt_typ_rec n1 cx1 (castsubst_castop c1 X1 c2)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_close_castop_wrt_typ_rec :
forall c2 c1 X1 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  cx1 `notin` typefv_castop c1 ->
  castsubst_castop c1 X1 (close_castop_wrt_typ_rec n1 cx1 c2) = close_castop_wrt_typ_rec n1 cx1 (castsubst_castop c1 X1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_typ_rec : lngen.

(* begin hide *)

Lemma castsubst_castop_close_castop_wrt_castop_rec_mutual :
(forall c2 c1 cx1 cx2 n1,
  degree_castop_wrt_castop n1 c1 ->
  cx1 <> cx2 ->
  cx2 `notin` castfv_castop c1 ->
  castsubst_castop c1 cx1 (close_castop_wrt_castop_rec n1 cx2 c2) = close_castop_wrt_castop_rec n1 cx2 (castsubst_castop c1 cx1 c2)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_close_castop_wrt_castop_rec :
forall c2 c1 cx1 cx2 n1,
  degree_castop_wrt_castop n1 c1 ->
  cx1 <> cx2 ->
  cx2 `notin` castfv_castop c1 ->
  castsubst_castop c1 cx1 (close_castop_wrt_castop_rec n1 cx2 c2) = close_castop_wrt_castop_rec n1 cx2 (castsubst_castop c1 cx1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_castop_rec : lngen.

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 A1 cx1 X1 n1,
  typsubst_exp A1 cx1 (close_exp_wrt_castop_rec n1 X1 e1) = close_exp_wrt_castop_rec n1 X1 (typsubst_exp A1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_close_exp_wrt_castop_rec :
forall e1 A1 cx1 X1 n1,
  typsubst_exp A1 cx1 (close_exp_wrt_castop_rec n1 X1 e1) = close_exp_wrt_castop_rec n1 X1 (typsubst_exp A1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_castop_rec : lngen.

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  typsubst_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (typsubst_exp A1 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  typsubst_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (typsubst_exp A1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 c1 X1 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  cx1 `notin` typefv_castop c1 ->
  castsubst_exp c1 X1 (close_exp_wrt_typ_rec n1 cx1 e1) = close_exp_wrt_typ_rec n1 cx1 (castsubst_exp c1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_close_exp_wrt_typ_rec :
forall e1 c1 X1 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  cx1 `notin` typefv_castop c1 ->
  castsubst_exp c1 X1 (close_exp_wrt_typ_rec n1 cx1 e1) = close_exp_wrt_typ_rec n1 cx1 (castsubst_exp c1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_castop_rec_mutual :
(forall e1 c1 cx1 cx2 n1,
  degree_castop_wrt_castop n1 c1 ->
  cx1 <> cx2 ->
  cx2 `notin` castfv_castop c1 ->
  castsubst_exp c1 cx1 (close_exp_wrt_castop_rec n1 cx2 e1) = close_exp_wrt_castop_rec n1 cx2 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_close_exp_wrt_castop_rec :
forall e1 c1 cx1 cx2 n1,
  degree_castop_wrt_castop n1 c1 ->
  cx1 <> cx2 ->
  cx2 `notin` castfv_castop c1 ->
  castsubst_exp c1 cx1 (close_exp_wrt_castop_rec n1 cx2 e1) = close_exp_wrt_castop_rec n1 cx2 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_castop_rec : lngen.

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 c1 x1 cx1 n1,
  castsubst_exp c1 x1 (close_exp_wrt_exp_rec n1 cx1 e1) = close_exp_wrt_exp_rec n1 cx1 (castsubst_exp c1 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_close_exp_wrt_exp_rec :
forall e1 c1 x1 cx1 n1,
  castsubst_exp c1 x1 (close_exp_wrt_exp_rec n1 cx1 e1) = close_exp_wrt_exp_rec n1 cx1 (castsubst_exp c1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` typefv_exp e1 ->
  subst_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp e1 X1 e2)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` typefv_exp e1 ->
  subst_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp e1 X1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_castop_rec_mutual :
(forall e2 e1 cx1 x1 n1,
  degree_exp_wrt_castop n1 e1 ->
  x1 `notin` castfv_exp e1 ->
  subst_exp e1 cx1 (close_exp_wrt_castop_rec n1 x1 e2) = close_exp_wrt_castop_rec n1 x1 (subst_exp e1 cx1 e2)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_close_exp_wrt_castop_rec :
forall e2 e1 cx1 x1 n1,
  degree_exp_wrt_castop n1 e1 ->
  x1 `notin` castfv_exp e1 ->
  subst_exp e1 cx1 (close_exp_wrt_castop_rec n1 x1 e2) = close_exp_wrt_castop_rec n1 x1 (subst_exp e1 cx1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_castop_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` termfv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` termfv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_exp_rec : lngen.

Lemma typsubst_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (typsubst_typ A1 X1 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_close_typ_wrt_typ : lngen.

Lemma typsubst_castop_close_castop_wrt_typ :
forall c1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_castop A1 X1 (close_castop_wrt_typ X2 c1) = close_castop_wrt_typ X2 (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_typ : lngen.

Lemma typsubst_castop_close_castop_wrt_castop :
forall c1 A1 cx1 X1,
  lc_typ A1 ->  typsubst_castop A1 cx1 (close_castop_wrt_castop X1 c1) = close_castop_wrt_castop X1 (typsubst_castop A1 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_castop : lngen.

Lemma castsubst_castop_close_castop_wrt_typ :
forall c2 c1 X1 cx1,
  lc_castop c1 ->  cx1 `notin` typefv_castop c1 ->
  castsubst_castop c1 X1 (close_castop_wrt_typ cx1 c2) = close_castop_wrt_typ cx1 (castsubst_castop c1 X1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_typ : lngen.

Lemma castsubst_castop_close_castop_wrt_castop :
forall c2 c1 cx1 cx2,
  lc_castop c1 ->  cx1 <> cx2 ->
  cx2 `notin` castfv_castop c1 ->
  castsubst_castop c1 cx1 (close_castop_wrt_castop cx2 c2) = close_castop_wrt_castop cx2 (castsubst_castop c1 cx1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_castop : lngen.

Lemma typsubst_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` typefv_typ A1 ->
  typsubst_exp A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_typ : lngen.

Lemma typsubst_exp_close_exp_wrt_castop :
forall e1 A1 cx1 X1,
  lc_typ A1 ->  typsubst_exp A1 cx1 (close_exp_wrt_castop X1 e1) = close_exp_wrt_castop X1 (typsubst_exp A1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_castop : lngen.

Lemma typsubst_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  lc_typ A1 ->  typsubst_exp A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (typsubst_exp A1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_exp : lngen.

Lemma castsubst_exp_close_exp_wrt_typ :
forall e1 c1 X1 cx1,
  lc_castop c1 ->  cx1 `notin` typefv_castop c1 ->
  castsubst_exp c1 X1 (close_exp_wrt_typ cx1 e1) = close_exp_wrt_typ cx1 (castsubst_exp c1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_typ : lngen.

Lemma castsubst_exp_close_exp_wrt_castop :
forall e1 c1 cx1 cx2,
  lc_castop c1 ->  cx1 <> cx2 ->
  cx2 `notin` castfv_castop c1 ->
  castsubst_exp c1 cx1 (close_exp_wrt_castop cx2 e1) = close_exp_wrt_castop cx2 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_castop : lngen.

Lemma castsubst_exp_close_exp_wrt_exp :
forall e1 c1 x1 cx1,
  lc_castop c1 ->  castsubst_exp c1 x1 (close_exp_wrt_exp cx1 e1) = close_exp_wrt_exp cx1 (castsubst_exp c1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` typefv_exp e1 ->
  subst_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_exp e1 X1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_typ : lngen.

Lemma subst_exp_close_exp_wrt_castop :
forall e2 e1 cx1 x1,
  lc_exp e1 ->  x1 `notin` castfv_exp e1 ->
  subst_exp e1 cx1 (close_exp_wrt_castop x1 e2) = close_exp_wrt_castop x1 (subst_exp e1 cx1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_castop : lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` termfv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp e1 x1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (typsubst_typ A2 X1 A1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (typsubst_typ A2 X1 A1).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_castop_degree_castop_wrt_typ_mutual :
(forall c1 A1 X1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_castop_wrt_typ n1 (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_degree_castop_wrt_typ :
forall c1 A1 X1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_castop_wrt_typ n1 (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_degree_castop_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_castop_degree_castop_wrt_castop_mutual :
(forall c1 A1 X1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_degree_castop_wrt_castop :
forall c1 A1 X1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_degree_castop_wrt_castop : lngen.

(* begin hide *)

Lemma castsubst_castop_degree_castop_wrt_typ_mutual :
(forall c1 c2 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ n1 c2 ->
  degree_castop_wrt_typ n1 (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_degree_castop_wrt_typ :
forall c1 c2 cx1 n1,
  degree_castop_wrt_typ n1 c1 ->
  degree_castop_wrt_typ n1 c2 ->
  degree_castop_wrt_typ n1 (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_degree_castop_wrt_typ : lngen.

(* begin hide *)

Lemma castsubst_castop_degree_castop_wrt_castop_mutual :
(forall c1 c2 cx1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 c2 ->
  degree_castop_wrt_castop n1 (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_degree_castop_wrt_castop :
forall c1 c2 cx1 n1,
  degree_castop_wrt_castop n1 c1 ->
  degree_castop_wrt_castop n1 c2 ->
  degree_castop_wrt_castop n1 (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_degree_castop_wrt_castop : lngen.

(* begin hide *)

Lemma typsubst_exp_degree_exp_wrt_typ_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma typsubst_exp_degree_exp_wrt_castop_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_degree_exp_wrt_castop :
forall e1 A1 X1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_degree_exp_wrt_castop : lngen.

(* begin hide *)

Lemma typsubst_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma castsubst_exp_degree_exp_wrt_typ_mutual :
(forall e1 c1 cx1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_castop_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_degree_exp_wrt_typ :
forall e1 c1 cx1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_castop_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma castsubst_exp_degree_exp_wrt_castop_mutual :
(forall e1 c1 cx1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_castop_wrt_castop n1 c1 ->
  degree_exp_wrt_castop n1 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_degree_exp_wrt_castop :
forall e1 c1 cx1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_castop_wrt_castop n1 c1 ->
  degree_exp_wrt_castop n1 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_degree_exp_wrt_castop : lngen.

(* begin hide *)

Lemma castsubst_exp_degree_exp_wrt_exp_mutual :
(forall e1 c1 cx1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_degree_exp_wrt_exp :
forall e1 c1 cx1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_castop_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 e2 ->
  degree_exp_wrt_castop n1 (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_castop :
forall e1 e2 x1 n1,
  degree_exp_wrt_castop n1 e1 ->
  degree_exp_wrt_castop n1 e2 ->
  degree_exp_wrt_castop n1 (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_degree_exp_wrt_castop : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  typsubst_typ A1 X1 A2 = A2).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` typefv_typ A2 ->
  typsubst_typ A1 X1 A2 = A2.
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_fresh_eq : lngen.
#[export] Hint Rewrite typsubst_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_castop_fresh_eq_mutual :
(forall c1 A1 X1,
  X1 `notin` typefv_castop c1 ->
  typsubst_castop A1 X1 c1 = c1).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_fresh_eq :
forall c1 A1 X1,
  X1 `notin` typefv_castop c1 ->
  typsubst_castop A1 X1 c1 = c1.
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_fresh_eq : lngen.
#[export] Hint Rewrite typsubst_castop_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma castsubst_castop_fresh_eq_mutual :
(forall c2 c1 cx1,
  cx1 `notin` castfv_castop c2 ->
  castsubst_castop c1 cx1 c2 = c2).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_fresh_eq :
forall c2 c1 cx1,
  cx1 `notin` castfv_castop c2 ->
  castsubst_castop c1 cx1 c2 = c2.
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_fresh_eq : lngen.
#[export] Hint Rewrite castsubst_castop_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_exp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typsubst_exp A1 X1 e1 = e1).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` typefv_exp e1 ->
  typsubst_exp A1 X1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_fresh_eq : lngen.
#[export] Hint Rewrite typsubst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma castsubst_exp_fresh_eq_mutual :
(forall e1 c1 cx1,
  cx1 `notin` castfv_exp e1 ->
  castsubst_exp c1 cx1 e1 = e1).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_fresh_eq :
forall e1 c1 cx1,
  cx1 `notin` castfv_exp e1 ->
  castsubst_exp c1 cx1 e1 = e1.
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_fresh_eq : lngen.
#[export] Hint Rewrite castsubst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` termfv_exp e2 ->
  subst_exp e1 x1 e2 = e2).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` termfv_exp e2 ->
  subst_exp e1 x1 e2 = e2.
Proof. Admitted.

#[export] Hint Resolve subst_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X1 A2)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X1 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_castop_fresh_same_mutual :
(forall c1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_castop (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_fresh_same :
forall c1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_castop (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_fresh_same : lngen.

(* begin hide *)

Lemma castsubst_castop_fresh_same_mutual :
(forall c2 c1 cx1,
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_castop (castsubst_castop c1 cx1 c2)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_fresh_same :
forall c2 c1 cx1,
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_castop (castsubst_castop c1 cx1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_exp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_fresh_same : lngen.

(* begin hide *)

Lemma castsubst_exp_fresh_same_mutual :
(forall e1 c1 cx1,
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_exp (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_fresh_same :
forall e1 c1 cx1,
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_fresh_same : lngen.

(* begin hide *)

Lemma typsubst_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X2 A2)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` typefv_typ A2 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_typ (typsubst_typ A1 X2 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_fresh : lngen.

(* begin hide *)

Lemma typsubst_castop_fresh_mutual :
(forall c1 A1 X1 X2,
  X1 `notin` typefv_castop c1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_castop (typsubst_castop A1 X2 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_fresh :
forall c1 A1 X1 X2,
  X1 `notin` typefv_castop c1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_castop (typsubst_castop A1 X2 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_fresh : lngen.

(* begin hide *)

Lemma castsubst_castop_fresh_mutual :
(forall c2 c1 cx1 cx2,
  cx1 `notin` castfv_castop c2 ->
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_castop (castsubst_castop c1 cx2 c2)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_fresh :
forall c2 c1 cx1 cx2,
  cx1 `notin` castfv_castop c2 ->
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_castop (castsubst_castop c1 cx2 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_fresh : lngen.

(* begin hide *)

Lemma typsubst_exp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X2 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_typ A1 ->
  X1 `notin` typefv_exp (typsubst_exp A1 X2 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_fresh : lngen.

(* begin hide *)

Lemma castsubst_exp_fresh_mutual :
(forall e1 c1 cx1 cx2,
  cx1 `notin` castfv_exp e1 ->
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_exp (castsubst_exp c1 cx2 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_fresh :
forall e1 c1 cx1 cx2,
  cx1 `notin` castfv_exp e1 ->
  cx1 `notin` castfv_castop c1 ->
  cx1 `notin` castfv_exp (castsubst_exp c1 cx2 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x2 e2)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` termfv_exp e2 ->
  x1 `notin` termfv_exp e1 ->
  x1 `notin` termfv_exp (subst_exp e1 x2 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_fresh : lngen.

Lemma typsubst_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (typsubst_typ A2 X1 A1).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_lc_typ : lngen.

Lemma typsubst_castop_lc_castop :
forall c1 A1 X1,
  lc_castop c1 ->
  lc_typ A1 ->
  lc_castop (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_lc_castop : lngen.

Lemma castsubst_castop_lc_castop :
forall c1 c2 cx1,
  lc_castop c1 ->
  lc_castop c2 ->
  lc_castop (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_lc_castop : lngen.

Lemma typsubst_exp_lc_exp :
forall e1 A1 X1,
  lc_exp e1 ->
  lc_typ A1 ->
  lc_exp (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_lc_exp : lngen.

Lemma castsubst_exp_lc_exp :
forall e1 c1 cx1,
  lc_exp e1 ->
  lc_castop c1 ->
  lc_exp (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_lc_exp : lngen.

Lemma subst_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_lc_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_typ A1 X1 A3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_typ A1 X1 A3).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_open_castop_wrt_typ_rec_mutual :
(forall c1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_castop A1 X1 (open_castop_wrt_typ_rec n1 A2 c1) = open_castop_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_open_castop_wrt_typ_rec :
forall c1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_castop A1 X1 (open_castop_wrt_typ_rec n1 A2 c1) = open_castop_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_open_castop_wrt_castop_rec_mutual :
(forall c2 A1 c1 X1 n1,
  typsubst_castop A1 X1 (open_castop_wrt_castop_rec n1 c1 c2) = open_castop_wrt_castop_rec n1 (typsubst_castop A1 X1 c1) (typsubst_castop A1 X1 c2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_open_castop_wrt_castop_rec :
forall c2 A1 c1 X1 n1,
  typsubst_castop A1 X1 (open_castop_wrt_castop_rec n1 c1 c2) = open_castop_wrt_castop_rec n1 (typsubst_castop A1 X1 c1) (typsubst_castop A1 X1 c2).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_open_castop_wrt_typ_rec_mutual :
(forall c2 c1 A1 cx1 n1,
  lc_castop c1 ->
  castsubst_castop c1 cx1 (open_castop_wrt_typ_rec n1 A1 c2) = open_castop_wrt_typ_rec n1 A1 (castsubst_castop c1 cx1 c2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_open_castop_wrt_typ_rec :
forall c2 c1 A1 cx1 n1,
  lc_castop c1 ->
  castsubst_castop c1 cx1 (open_castop_wrt_typ_rec n1 A1 c2) = open_castop_wrt_typ_rec n1 A1 (castsubst_castop c1 cx1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_open_castop_wrt_castop_rec_mutual :
(forall c3 c1 c2 cx1 n1,
  lc_castop c1 ->
  castsubst_castop c1 cx1 (open_castop_wrt_castop_rec n1 c2 c3) = open_castop_wrt_castop_rec n1 (castsubst_castop c1 cx1 c2) (castsubst_castop c1 cx1 c3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_open_castop_wrt_castop_rec :
forall c3 c1 c2 cx1 n1,
  lc_castop c1 ->
  castsubst_castop c1 cx1 (open_castop_wrt_castop_rec n1 c2 c3) = open_castop_wrt_castop_rec n1 (castsubst_castop c1 cx1 c2) (castsubst_castop c1 cx1 c3).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_typ_rec :
forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (typsubst_typ A1 X1 A2) (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_castop_rec_mutual :
(forall e1 A1 c1 X1 n1,
  typsubst_exp A1 X1 (open_exp_wrt_castop_rec n1 c1 e1) = open_exp_wrt_castop_rec n1 (typsubst_castop A1 X1 c1) (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_castop_rec :
forall e1 A1 c1 X1 n1,
  typsubst_exp A1 X1 (open_exp_wrt_castop_rec n1 c1 e1) = open_exp_wrt_castop_rec n1 (typsubst_castop A1 X1 c1) (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (typsubst_exp A1 X1 e1) (typsubst_exp A1 X1 e2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 X1 n1,
  typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (typsubst_exp A1 X1 e1) (typsubst_exp A1 X1 e2).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 c1 A1 cx1 n1,
  lc_castop c1 ->
  castsubst_exp c1 cx1 (open_exp_wrt_typ_rec n1 A1 e1) = open_exp_wrt_typ_rec n1 A1 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_open_exp_wrt_typ_rec :
forall e1 c1 A1 cx1 n1,
  lc_castop c1 ->
  castsubst_exp c1 cx1 (open_exp_wrt_typ_rec n1 A1 e1) = open_exp_wrt_typ_rec n1 A1 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_open_exp_wrt_castop_rec_mutual :
(forall e1 c1 c2 cx1 n1,
  lc_castop c1 ->
  castsubst_exp c1 cx1 (open_exp_wrt_castop_rec n1 c2 e1) = open_exp_wrt_castop_rec n1 (castsubst_castop c1 cx1 c2) (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_open_exp_wrt_castop_rec :
forall e1 c1 c2 cx1 n1,
  lc_castop c1 ->
  castsubst_exp c1 cx1 (open_exp_wrt_castop_rec n1 c2 e1) = open_exp_wrt_castop_rec n1 (castsubst_castop c1 cx1 c2) (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 c1 e1 cx1 n1,
  castsubst_exp c1 cx1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (castsubst_exp c1 cx1 e1) (castsubst_exp c1 cx1 e2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_open_exp_wrt_exp_rec :
forall e2 c1 e1 cx1 n1,
  castsubst_exp c1 cx1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (castsubst_exp c1 cx1 e1) (castsubst_exp c1 cx1 e2).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_typ_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp e1 x1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_castop_rec_mutual :
(forall e2 e1 c1 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_castop_rec n1 c1 e2) = open_exp_wrt_castop_rec n1 c1 (subst_exp e1 x1 e2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_castop_rec :
forall e2 e1 c1 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_castop_rec n1 c1 e2) = open_exp_wrt_castop_rec n1 c1 (subst_exp e1 x1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_exp e1 x1 e3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_exp e1 x1 e3).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma typsubst_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  typsubst_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (typsubst_typ A1 X1 A3) (typsubst_typ A1 X1 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_open_typ_wrt_typ : lngen.

Lemma typsubst_castop_open_castop_wrt_typ :
forall c1 A1 A2 X1,
  lc_typ A1 ->
  typsubst_castop A1 X1 (open_castop_wrt_typ c1 A2) = open_castop_wrt_typ (typsubst_castop A1 X1 c1) (typsubst_typ A1 X1 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_open_castop_wrt_typ : lngen.

Lemma typsubst_castop_open_castop_wrt_castop :
forall c2 A1 c1 X1,
  typsubst_castop A1 X1 (open_castop_wrt_castop c2 c1) = open_castop_wrt_castop (typsubst_castop A1 X1 c2) (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_open_castop_wrt_castop : lngen.

Lemma castsubst_castop_open_castop_wrt_typ :
forall c2 c1 A1 cx1,
  lc_castop c1 ->
  castsubst_castop c1 cx1 (open_castop_wrt_typ c2 A1) = open_castop_wrt_typ (castsubst_castop c1 cx1 c2) A1.
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_open_castop_wrt_typ : lngen.

Lemma castsubst_castop_open_castop_wrt_castop :
forall c3 c1 c2 cx1,
  lc_castop c1 ->
  castsubst_castop c1 cx1 (open_castop_wrt_castop c3 c2) = open_castop_wrt_castop (castsubst_castop c1 cx1 c3) (castsubst_castop c1 cx1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_open_castop_wrt_castop : lngen.

Lemma typsubst_exp_open_exp_wrt_typ :
forall e1 A1 A2 X1,
  lc_typ A1 ->
  typsubst_exp A1 X1 (open_exp_wrt_typ e1 A2) = open_exp_wrt_typ (typsubst_exp A1 X1 e1) (typsubst_typ A1 X1 A2).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_typ : lngen.

Lemma typsubst_exp_open_exp_wrt_castop :
forall e1 A1 c1 X1,
  typsubst_exp A1 X1 (open_exp_wrt_castop e1 c1) = open_exp_wrt_castop (typsubst_exp A1 X1 e1) (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_castop : lngen.

Lemma typsubst_exp_open_exp_wrt_exp :
forall e2 A1 e1 X1,
  typsubst_exp A1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (typsubst_exp A1 X1 e2) (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_exp : lngen.

Lemma castsubst_exp_open_exp_wrt_typ :
forall e1 c1 A1 cx1,
  lc_castop c1 ->
  castsubst_exp c1 cx1 (open_exp_wrt_typ e1 A1) = open_exp_wrt_typ (castsubst_exp c1 cx1 e1) A1.
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_typ : lngen.

Lemma castsubst_exp_open_exp_wrt_castop :
forall e1 c1 c2 cx1,
  lc_castop c1 ->
  castsubst_exp c1 cx1 (open_exp_wrt_castop e1 c2) = open_exp_wrt_castop (castsubst_exp c1 cx1 e1) (castsubst_castop c1 cx1 c2).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_castop : lngen.

Lemma castsubst_exp_open_exp_wrt_exp :
forall e2 c1 e1 cx1,
  castsubst_exp c1 cx1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (castsubst_exp c1 cx1 e2) (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_open_exp_wrt_typ :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_typ e2 A1) = open_exp_wrt_typ (subst_exp e1 x1 e2) A1.
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_typ : lngen.

Lemma subst_exp_open_exp_wrt_castop :
forall e2 e1 c1 x1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_castop e2 c1) = open_exp_wrt_castop (subst_exp e1 x1 e2) c1.
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_castop : lngen.

Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp e1 x1 e3) (subst_exp e1 x1 e2).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_exp : lngen.

Lemma typsubst_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (typsubst_typ A1 X1 A2) (t_var_f X2) = typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_var_f X2)).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_open_typ_wrt_typ_var : lngen.

Lemma typsubst_castop_open_castop_wrt_typ_var :
forall c1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_castop_wrt_typ (typsubst_castop A1 X1 c1) (t_var_f X2) = typsubst_castop A1 X1 (open_castop_wrt_typ c1 (t_var_f X2)).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_open_castop_wrt_typ_var : lngen.

Lemma typsubst_castop_open_castop_wrt_castop_var :
forall c1 A1 X1 cx1,
  open_castop_wrt_castop (typsubst_castop A1 X1 c1) (c_var_f cx1) = typsubst_castop A1 X1 (open_castop_wrt_castop c1 (c_var_f cx1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_open_castop_wrt_castop_var : lngen.

Lemma castsubst_castop_open_castop_wrt_typ_var :
forall c2 c1 cx1 X1,
  lc_castop c1 ->
  open_castop_wrt_typ (castsubst_castop c1 cx1 c2) (t_var_f X1) = castsubst_castop c1 cx1 (open_castop_wrt_typ c2 (t_var_f X1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_open_castop_wrt_typ_var : lngen.

Lemma castsubst_castop_open_castop_wrt_castop_var :
forall c2 c1 cx1 cx2,
  cx1 <> cx2 ->
  lc_castop c1 ->
  open_castop_wrt_castop (castsubst_castop c1 cx1 c2) (c_var_f cx2) = castsubst_castop c1 cx1 (open_castop_wrt_castop c2 (c_var_f cx2)).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_open_castop_wrt_castop_var : lngen.

Lemma typsubst_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_exp_wrt_typ (typsubst_exp A1 X1 e1) (t_var_f X2) = typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_var_f X2)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_typ_var : lngen.

Lemma typsubst_exp_open_exp_wrt_castop_var :
forall e1 A1 X1 cx1,
  open_exp_wrt_castop (typsubst_exp A1 X1 e1) (c_var_f cx1) = typsubst_exp A1 X1 (open_exp_wrt_castop e1 (c_var_f cx1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_castop_var : lngen.

Lemma typsubst_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_exp_wrt_exp (typsubst_exp A1 X1 e1) (e_var_f x1) = typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_open_exp_wrt_exp_var : lngen.

Lemma castsubst_exp_open_exp_wrt_typ_var :
forall e1 c1 cx1 X1,
  lc_castop c1 ->
  open_exp_wrt_typ (castsubst_exp c1 cx1 e1) (t_var_f X1) = castsubst_exp c1 cx1 (open_exp_wrt_typ e1 (t_var_f X1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_typ_var : lngen.

Lemma castsubst_exp_open_exp_wrt_castop_var :
forall e1 c1 cx1 cx2,
  cx1 <> cx2 ->
  lc_castop c1 ->
  open_exp_wrt_castop (castsubst_exp c1 cx1 e1) (c_var_f cx2) = castsubst_exp c1 cx1 (open_exp_wrt_castop e1 (c_var_f cx2)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_castop_var : lngen.

Lemma castsubst_exp_open_exp_wrt_exp_var :
forall e1 c1 cx1 x1,
  open_exp_wrt_exp (castsubst_exp c1 cx1 e1) (e_var_f x1) = castsubst_exp c1 cx1 (open_exp_wrt_exp e1 (e_var_f x1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_exp e1 x1 e2) (t_var_f X1) = subst_exp e1 x1 (open_exp_wrt_typ e2 (t_var_f X1)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_exp_open_exp_wrt_castop_var :
forall e2 e1 x1 cx1,
  lc_exp e1 ->
  open_exp_wrt_castop (subst_exp e1 x1 e2) (c_var_f cx1) = subst_exp e1 x1 (open_exp_wrt_castop e2 (c_var_f cx1)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_castop_var : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp e1 x1 e2) (e_var_f x2) = subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma typsubst_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_spec_rec :
forall A1 A2 X1 n1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_spec_rec_mutual :
(forall c1 A1 X1 n1,
  typsubst_castop A1 X1 c1 = open_castop_wrt_typ_rec n1 A1 (close_castop_wrt_typ_rec n1 X1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_spec_rec :
forall c1 A1 X1 n1,
  typsubst_castop A1 X1 c1 = open_castop_wrt_typ_rec n1 A1 (close_castop_wrt_typ_rec n1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_spec_rec_mutual :
(forall c1 c2 cx1 n1,
  castsubst_castop c2 cx1 c1 = open_castop_wrt_castop_rec n1 c2 (close_castop_wrt_castop_rec n1 cx1 c1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_spec_rec :
forall c1 c2 cx1 n1,
  castsubst_castop c2 cx1 c1 = open_castop_wrt_castop_rec n1 c2 (close_castop_wrt_castop_rec n1 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  typsubst_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_spec_rec :
forall e1 A1 X1 n1,
  typsubst_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_spec_rec_mutual :
(forall e1 c1 cx1 n1,
  castsubst_exp c1 cx1 e1 = open_exp_wrt_castop_rec n1 c1 (close_exp_wrt_castop_rec n1 cx1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_spec_rec :
forall e1 c1 cx1 n1,
  castsubst_exp c1 cx1 e1 = open_exp_wrt_castop_rec n1 c1 (close_exp_wrt_castop_rec n1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_spec_rec : lngen.

(* end hide *)

Lemma typsubst_typ_spec :
forall A1 A2 X1,
  typsubst_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_spec : lngen.

Lemma typsubst_castop_spec :
forall c1 A1 X1,
  typsubst_castop A1 X1 c1 = open_castop_wrt_typ (close_castop_wrt_typ X1 c1) A1.
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_spec : lngen.

Lemma castsubst_castop_spec :
forall c1 c2 cx1,
  castsubst_castop c2 cx1 c1 = open_castop_wrt_castop (close_castop_wrt_castop cx1 c1) c2.
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_spec : lngen.

Lemma typsubst_exp_spec :
forall e1 A1 X1,
  typsubst_exp A1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) A1.
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_spec : lngen.

Lemma castsubst_exp_spec :
forall e1 c1 cx1,
  castsubst_exp c1 cx1 e1 = open_exp_wrt_castop (close_exp_wrt_castop cx1 e1) c1.
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_spec : lngen.

Lemma subst_exp_spec :
forall e1 e2 x1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof. Admitted.

#[export] Hint Resolve subst_exp_spec : lngen.

(* begin hide *)

Lemma typsubst_typ_typsubst_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_typ A2 ->
  X2 <> X1 ->
  typsubst_typ A2 X1 (typsubst_typ A3 X2 A1) = typsubst_typ (typsubst_typ A2 X1 A3) X2 (typsubst_typ A2 X1 A1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_typsubst_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` typefv_typ A2 ->
  X2 <> X1 ->
  typsubst_typ A2 X1 (typsubst_typ A3 X2 A1) = typsubst_typ (typsubst_typ A2 X1 A3) X2 (typsubst_typ A2 X1 A1).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_typsubst_typ : lngen.

(* begin hide *)

Lemma typsubst_castop_typsubst_castop_mutual :
(forall c1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_castop A1 X1 (typsubst_castop A2 X2 c1) = typsubst_castop (typsubst_typ A1 X1 A2) X2 (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_typsubst_castop :
forall c1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_castop A1 X1 (typsubst_castop A2 X2 c1) = typsubst_castop (typsubst_typ A1 X1 A2) X2 (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_typsubst_castop : lngen.

(* begin hide *)

Lemma typsubst_castop_castsubst_castop_mutual :
(forall c1 A1 c2 cx1 X1,
  typsubst_castop A1 X1 (castsubst_castop c2 cx1 c1) = castsubst_castop (typsubst_castop A1 X1 c2) cx1 (typsubst_castop A1 X1 c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_castsubst_castop :
forall c1 A1 c2 cx1 X1,
  typsubst_castop A1 X1 (castsubst_castop c2 cx1 c1) = castsubst_castop (typsubst_castop A1 X1 c2) cx1 (typsubst_castop A1 X1 c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_castsubst_castop : lngen.

(* begin hide *)

Lemma castsubst_castop_typsubst_castop_mutual :
(forall c1 c2 A1 X1 cx1,
  X1 `notin` typefv_castop c2 ->
  castsubst_castop c2 cx1 (typsubst_castop A1 X1 c1) = typsubst_castop A1 X1 (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_typsubst_castop :
forall c1 c2 A1 X1 cx1,
  X1 `notin` typefv_castop c2 ->
  castsubst_castop c2 cx1 (typsubst_castop A1 X1 c1) = typsubst_castop A1 X1 (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_typsubst_castop : lngen.

(* begin hide *)

Lemma castsubst_castop_castsubst_castop_mutual :
(forall c1 c2 c3 cx2 cx1,
  cx2 `notin` castfv_castop c2 ->
  cx2 <> cx1 ->
  castsubst_castop c2 cx1 (castsubst_castop c3 cx2 c1) = castsubst_castop (castsubst_castop c2 cx1 c3) cx2 (castsubst_castop c2 cx1 c1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_castsubst_castop :
forall c1 c2 c3 cx2 cx1,
  cx2 `notin` castfv_castop c2 ->
  cx2 <> cx1 ->
  castsubst_castop c2 cx1 (castsubst_castop c3 cx2 c1) = castsubst_castop (castsubst_castop c2 cx1 c3) cx2 (castsubst_castop c2 cx1 c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_castsubst_castop : lngen.

(* begin hide *)

Lemma typsubst_exp_typsubst_exp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_exp A1 X1 (typsubst_exp A2 X2 e1) = typsubst_exp (typsubst_typ A1 X1 A2) X2 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_typsubst_exp :
forall e1 A1 A2 X2 X1,
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  typsubst_exp A1 X1 (typsubst_exp A2 X2 e1) = typsubst_exp (typsubst_typ A1 X1 A2) X2 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_typsubst_exp : lngen.

(* begin hide *)

Lemma typsubst_exp_castsubst_exp_mutual :
(forall e1 A1 c1 cx1 X1,
  typsubst_exp A1 X1 (castsubst_exp c1 cx1 e1) = castsubst_exp (typsubst_castop A1 X1 c1) cx1 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_castsubst_exp :
forall e1 A1 c1 cx1 X1,
  typsubst_exp A1 X1 (castsubst_exp c1 cx1 e1) = castsubst_exp (typsubst_castop A1 X1 c1) cx1 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_castsubst_exp : lngen.

(* begin hide *)

Lemma typsubst_exp_subst_exp_mutual :
(forall e1 A1 e2 x1 X1,
  typsubst_exp A1 X1 (subst_exp e2 x1 e1) = subst_exp (typsubst_exp A1 X1 e2) x1 (typsubst_exp A1 X1 e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_subst_exp :
forall e1 A1 e2 x1 X1,
  typsubst_exp A1 X1 (subst_exp e2 x1 e1) = subst_exp (typsubst_exp A1 X1 e2) x1 (typsubst_exp A1 X1 e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_subst_exp : lngen.

(* begin hide *)

Lemma castsubst_exp_typsubst_exp_mutual :
(forall e1 c1 A1 X1 cx1,
  X1 `notin` typefv_castop c1 ->
  castsubst_exp c1 cx1 (typsubst_exp A1 X1 e1) = typsubst_exp A1 X1 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_typsubst_exp :
forall e1 c1 A1 X1 cx1,
  X1 `notin` typefv_castop c1 ->
  castsubst_exp c1 cx1 (typsubst_exp A1 X1 e1) = typsubst_exp A1 X1 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_typsubst_exp : lngen.

(* begin hide *)

Lemma castsubst_exp_castsubst_exp_mutual :
(forall e1 c1 c2 cx2 cx1,
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  castsubst_exp c1 cx1 (castsubst_exp c2 cx2 e1) = castsubst_exp (castsubst_castop c1 cx1 c2) cx2 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_castsubst_exp :
forall e1 c1 c2 cx2 cx1,
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  castsubst_exp c1 cx1 (castsubst_exp c2 cx2 e1) = castsubst_exp (castsubst_castop c1 cx1 c2) cx2 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_castsubst_exp : lngen.

(* begin hide *)

Lemma castsubst_exp_subst_exp_mutual :
(forall e1 c1 e2 x1 cx1,
  castsubst_exp c1 cx1 (subst_exp e2 x1 e1) = subst_exp (castsubst_exp c1 cx1 e2) x1 (castsubst_exp c1 cx1 e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_subst_exp :
forall e1 c1 e2 x1 cx1,
  castsubst_exp c1 cx1 (subst_exp e2 x1 e1) = subst_exp (castsubst_exp c1 cx1 e2) x1 (castsubst_exp c1 cx1 e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_subst_exp : lngen.

(* begin hide *)

Lemma subst_exp_typsubst_exp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` typefv_exp e2 ->
  subst_exp e2 x1 (typsubst_exp A1 X1 e1) = typsubst_exp A1 X1 (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_typsubst_exp :
forall e1 e2 A1 X1 x1,
  X1 `notin` typefv_exp e2 ->
  subst_exp e2 x1 (typsubst_exp A1 X1 e1) = typsubst_exp A1 X1 (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_typsubst_exp : lngen.

(* begin hide *)

Lemma subst_exp_castsubst_exp_mutual :
(forall e1 e2 c1 cx1 x1,
  cx1 `notin` castfv_exp e2 ->
  subst_exp e2 x1 (castsubst_exp c1 cx1 e1) = castsubst_exp c1 cx1 (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_castsubst_exp :
forall e1 e2 c1 cx1 x1,
  cx1 `notin` castfv_exp e2 ->
  subst_exp e2 x1 (castsubst_exp c1 cx1 e1) = castsubst_exp c1 cx1 (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_castsubst_exp : lngen.

(* begin hide *)

Lemma subst_exp_subst_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` termfv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_subst_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` termfv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_subst_exp : lngen.

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 (t_var_f X2) A2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (typsubst_typ A1 X1 (open_typ_wrt_typ_rec n1 (t_var_f X2) A2)).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_close_castop_wrt_typ_rec_open_castop_wrt_typ_rec_mutual :
(forall c1 A1 X1 X2 n1,
  X2 `notin` typefv_castop c1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_castop A1 X1 c1 = close_castop_wrt_typ_rec n1 X2 (typsubst_castop A1 X1 (open_castop_wrt_typ_rec n1 (t_var_f X2) c1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_close_castop_wrt_typ_rec_open_castop_wrt_typ_rec :
forall c1 A1 X1 X2 n1,
  X2 `notin` typefv_castop c1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_castop A1 X1 c1 = close_castop_wrt_typ_rec n1 X2 (typsubst_castop A1 X1 (open_castop_wrt_typ_rec n1 (t_var_f X2) c1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_typ_rec_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_close_castop_wrt_castop_rec_open_castop_wrt_castop_rec_mutual :
(forall c1 A1 X1 cx1 n1,
  cx1 `notin` castfv_castop c1 ->
  typsubst_castop A1 X1 c1 = close_castop_wrt_castop_rec n1 cx1 (typsubst_castop A1 X1 (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_castop_close_castop_wrt_castop_rec_open_castop_wrt_castop_rec :
forall c1 A1 X1 cx1 n1,
  cx1 `notin` castfv_castop c1 ->
  typsubst_castop A1 X1 c1 = close_castop_wrt_castop_rec n1 cx1 (typsubst_castop A1 X1 (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_castop_rec_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_close_castop_wrt_typ_rec_open_castop_wrt_typ_rec_mutual :
(forall c2 c1 cx1 X1 n1,
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop c1 ->
  degree_castop_wrt_typ n1 c1 ->
  castsubst_castop c1 cx1 c2 = close_castop_wrt_typ_rec n1 X1 (castsubst_castop c1 cx1 (open_castop_wrt_typ_rec n1 (t_var_f X1) c2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_close_castop_wrt_typ_rec_open_castop_wrt_typ_rec :
forall c2 c1 cx1 X1 n1,
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop c1 ->
  degree_castop_wrt_typ n1 c1 ->
  castsubst_castop c1 cx1 c2 = close_castop_wrt_typ_rec n1 X1 (castsubst_castop c1 cx1 (open_castop_wrt_typ_rec n1 (t_var_f X1) c2)).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_typ_rec_open_castop_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_close_castop_wrt_castop_rec_open_castop_wrt_castop_rec_mutual :
(forall c2 c1 cx1 cx2 n1,
  cx2 `notin` castfv_castop c2 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  degree_castop_wrt_castop n1 c1 ->
  castsubst_castop c1 cx1 c2 = close_castop_wrt_castop_rec n1 cx2 (castsubst_castop c1 cx1 (open_castop_wrt_castop_rec n1 (c_var_f cx2) c2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_castop_close_castop_wrt_castop_rec_open_castop_wrt_castop_rec :
forall c2 c1 cx1 cx2 n1,
  cx2 `notin` castfv_castop c2 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  degree_castop_wrt_castop n1 c1 ->
  castsubst_castop c1 cx1 c2 = close_castop_wrt_castop_rec n1 cx2 (castsubst_castop c1 cx1 (open_castop_wrt_castop_rec n1 (c_var_f cx2) c2)).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_castop_rec_open_castop_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_var_f X2) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_var_f X2) e1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec_mutual :
(forall e1 A1 X1 cx1 n1,
  cx1 `notin` castfv_exp e1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_castop_rec n1 cx1 (typsubst_exp A1 X1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec :
forall e1 A1 X1 cx1 n1,
  cx1 `notin` castfv_exp e1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_castop_rec n1 cx1 (typsubst_exp A1 X1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (typsubst_exp A1 X1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 c1 cx1 X1 n1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_castop c1 ->
  degree_castop_wrt_typ n1 c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_typ_rec n1 X1 (castsubst_exp c1 cx1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 c1 cx1 X1 n1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_castop c1 ->
  degree_castop_wrt_typ n1 c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_typ_rec n1 X1 (castsubst_exp c1 cx1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec_mutual :
(forall e1 c1 cx1 cx2 n1,
  cx2 `notin` castfv_exp e1 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  degree_castop_wrt_castop n1 c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_castop_rec n1 cx2 (castsubst_exp c1 cx1 (open_exp_wrt_castop_rec n1 (c_var_f cx2) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec :
forall e1 c1 cx1 cx2 n1,
  cx2 `notin` castfv_exp e1 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  degree_castop_wrt_castop n1 c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_castop_rec n1 cx2 (castsubst_exp c1 cx1 (open_exp_wrt_castop_rec n1 (c_var_f cx2) e1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 c1 cx1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_exp_rec n1 x1 (castsubst_exp c1 cx1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma castsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 c1 cx1 x1 n1,
  x1 `notin` termfv_exp e1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_exp_rec n1 x1 (castsubst_exp c1 cx1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp e1 x1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp e1 x1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e2)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec_mutual :
(forall e2 e1 x1 cx1 n1,
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp e1 ->
  degree_exp_wrt_castop n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_castop_rec n1 cx1 (subst_exp e1 x1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec :
forall e2 e1 x1 cx1 n1,
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp e1 ->
  degree_exp_wrt_castop n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_castop_rec n1 cx1 (subst_exp e1 x1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e2)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_castop_rec_open_exp_wrt_castop_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x2) e2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x2) e2)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma typsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` typefv_typ A2 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_typ A1 X1 A2 = close_typ_wrt_typ X2 (typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_var_f X2))).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma typsubst_castop_close_castop_wrt_typ_open_castop_wrt_typ :
forall c1 A1 X1 X2,
  X2 `notin` typefv_castop c1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_castop A1 X1 c1 = close_castop_wrt_typ X2 (typsubst_castop A1 X1 (open_castop_wrt_typ c1 (t_var_f X2))).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_typ_open_castop_wrt_typ : lngen.

Lemma typsubst_castop_close_castop_wrt_castop_open_castop_wrt_castop :
forall c1 A1 X1 cx1,
  cx1 `notin` castfv_castop c1 ->
  lc_typ A1 ->
  typsubst_castop A1 X1 c1 = close_castop_wrt_castop cx1 (typsubst_castop A1 X1 (open_castop_wrt_castop c1 (c_var_f cx1))).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_close_castop_wrt_castop_open_castop_wrt_castop : lngen.

Lemma castsubst_castop_close_castop_wrt_typ_open_castop_wrt_typ :
forall c2 c1 cx1 X1,
  X1 `notin` typefv_castop c2 ->
  X1 `notin` typefv_castop c1 ->
  lc_castop c1 ->
  castsubst_castop c1 cx1 c2 = close_castop_wrt_typ X1 (castsubst_castop c1 cx1 (open_castop_wrt_typ c2 (t_var_f X1))).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_typ_open_castop_wrt_typ : lngen.

Lemma castsubst_castop_close_castop_wrt_castop_open_castop_wrt_castop :
forall c2 c1 cx1 cx2,
  cx2 `notin` castfv_castop c2 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  lc_castop c1 ->
  castsubst_castop c1 cx1 c2 = close_castop_wrt_castop cx2 (castsubst_castop c1 cx1 (open_castop_wrt_castop c2 (c_var_f cx2))).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_close_castop_wrt_castop_open_castop_wrt_castop : lngen.

Lemma typsubst_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1 X1 X2,
  X2 `notin` typefv_exp e1 ->
  X2 `notin` typefv_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_typ X2 (typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_var_f X2))).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma typsubst_exp_close_exp_wrt_castop_open_exp_wrt_castop :
forall e1 A1 X1 cx1,
  cx1 `notin` castfv_exp e1 ->
  lc_typ A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_castop cx1 (typsubst_exp A1 X1 (open_exp_wrt_castop e1 (c_var_f cx1))).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_castop_open_exp_wrt_castop : lngen.

Lemma typsubst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 X1 x1,
  x1 `notin` termfv_exp e1 ->
  lc_typ A1 ->
  typsubst_exp A1 X1 e1 = close_exp_wrt_exp x1 (typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1))).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma castsubst_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 c1 cx1 X1,
  X1 `notin` typefv_exp e1 ->
  X1 `notin` typefv_castop c1 ->
  lc_castop c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_typ X1 (castsubst_exp c1 cx1 (open_exp_wrt_typ e1 (t_var_f X1))).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma castsubst_exp_close_exp_wrt_castop_open_exp_wrt_castop :
forall e1 c1 cx1 cx2,
  cx2 `notin` castfv_exp e1 ->
  cx2 `notin` castfv_castop c1 ->
  cx2 <> cx1 ->
  lc_castop c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_castop cx2 (castsubst_exp c1 cx1 (open_exp_wrt_castop e1 (c_var_f cx2))).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_castop_open_exp_wrt_castop : lngen.

Lemma castsubst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 c1 cx1 x1,
  x1 `notin` termfv_exp e1 ->
  lc_castop c1 ->
  castsubst_exp c1 cx1 e1 = close_exp_wrt_exp x1 (castsubst_exp c1 cx1 (open_exp_wrt_exp e1 (e_var_f x1))).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` typefv_exp e2 ->
  X1 `notin` typefv_exp e1 ->
  lc_exp e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_exp e1 x1 (open_exp_wrt_typ e2 (t_var_f X1))).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_exp_close_exp_wrt_castop_open_exp_wrt_castop :
forall e2 e1 x1 cx1,
  cx1 `notin` castfv_exp e2 ->
  cx1 `notin` castfv_exp e1 ->
  lc_exp e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_castop cx1 (subst_exp e1 x1 (open_exp_wrt_castop e2 (c_var_f cx1))).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_castop_open_exp_wrt_castop : lngen.

Lemma subst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` termfv_exp e2 ->
  x2 `notin` termfv_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2))).
Proof. Admitted.

#[export] Hint Resolve subst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma typsubst_typ_t_mu :
forall X2 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` typefv_typ A1 `union` typefv_typ A2 `union` singleton X1 ->
  typsubst_typ A1 X1 (t_mu A2) = t_mu (close_typ_wrt_typ X2 (typsubst_typ A1 X1 (open_typ_wrt_typ A2 (t_var_f X2)))).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_t_mu : lngen.

Lemma typsubst_castop_c_fixc :
forall cx1 c1 A1 X1,
  lc_typ A1 ->
  cx1 `notin` castfv_castop c1 ->
  typsubst_castop A1 X1 (c_fixc c1) = c_fixc (close_castop_wrt_castop cx1 (typsubst_castop A1 X1 (open_castop_wrt_castop c1 (c_var_f cx1)))).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_c_fixc : lngen.

Lemma castsubst_castop_c_fixc :
forall cx2 c2 c1 cx1,
  lc_castop c1 ->
  cx2 `notin` castfv_castop c1 `union` castfv_castop c2 `union` singleton cx1 ->
  castsubst_castop c1 cx1 (c_fixc c2) = c_fixc (close_castop_wrt_castop cx2 (castsubst_castop c1 cx1 (open_castop_wrt_castop c2 (c_var_f cx2)))).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_c_fixc : lngen.

Lemma typsubst_exp_e_abs :
forall x1 A2 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` termfv_exp e1 ->
  typsubst_exp A1 X1 (e_abs A2 e1) = e_abs (typsubst_typ A1 X1 A2) (close_exp_wrt_exp x1 (typsubst_exp A1 X1 (open_exp_wrt_exp e1 (e_var_f x1)))).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_e_abs : lngen.

Lemma castsubst_exp_e_abs :
forall x1 A1 e1 c1 cx1,
  lc_castop c1 ->
  x1 `notin` termfv_exp e1 ->
  castsubst_exp c1 cx1 (e_abs A1 e1) = e_abs (A1) (close_exp_wrt_exp x1 (castsubst_exp c1 cx1 (open_exp_wrt_exp e1 (e_var_f x1)))).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_e_abs : lngen.

Lemma subst_exp_e_abs :
forall x2 A1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` termfv_exp e1 `union` termfv_exp e2 `union` singleton x1 ->
  subst_exp e1 x1 (e_abs A1 e2) = e_abs (A1) (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_exp_e_abs : lngen.

(* begin hide *)

Lemma typsubst_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = typsubst_typ A2 X1 (open_typ_wrt_typ_rec n1 (t_var_f X1) A1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = typsubst_typ A2 X1 (open_typ_wrt_typ_rec n1 (t_var_f X1) A1).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_intro_rec : lngen.
#[export] Hint Rewrite typsubst_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_castop_intro_rec_mutual :
(forall c1 X1 A1 n1,
  X1 `notin` typefv_castop c1 ->
  open_castop_wrt_typ_rec n1 A1 c1 = typsubst_castop A1 X1 (open_castop_wrt_typ_rec n1 (t_var_f X1) c1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_castop_intro_rec :
forall c1 X1 A1 n1,
  X1 `notin` typefv_castop c1 ->
  open_castop_wrt_typ_rec n1 A1 c1 = typsubst_castop A1 X1 (open_castop_wrt_typ_rec n1 (t_var_f X1) c1).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_intro_rec : lngen.
#[export] Hint Rewrite typsubst_castop_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma castsubst_castop_intro_rec_mutual :
(forall c1 cx1 c2 n1,
  cx1 `notin` castfv_castop c1 ->
  open_castop_wrt_castop_rec n1 c2 c1 = castsubst_castop c2 cx1 (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_castop_intro_rec :
forall c1 cx1 c2 n1,
  cx1 `notin` castfv_castop c1 ->
  open_castop_wrt_castop_rec n1 c2 c1 = castsubst_castop c2 cx1 (open_castop_wrt_castop_rec n1 (c_var_f cx1) c1).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_intro_rec : lngen.
#[export] Hint Rewrite castsubst_castop_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma typsubst_exp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e1)).
Proof. Admitted.

(* end hide *)

Lemma typsubst_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = typsubst_exp A1 X1 (open_exp_wrt_typ_rec n1 (t_var_f X1) e1).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_intro_rec : lngen.
#[export] Hint Rewrite typsubst_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma castsubst_exp_intro_rec_mutual :
(forall e1 cx1 c1 n1,
  cx1 `notin` castfv_exp e1 ->
  open_exp_wrt_castop_rec n1 c1 e1 = castsubst_exp c1 cx1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1)).
Proof. Admitted.

(* end hide *)

Lemma castsubst_exp_intro_rec :
forall e1 cx1 c1 n1,
  cx1 `notin` castfv_exp e1 ->
  open_exp_wrt_castop_rec n1 c1 e1 = castsubst_exp c1 cx1 (open_exp_wrt_castop_rec n1 (c_var_f cx1) e1).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_intro_rec : lngen.
#[export] Hint Rewrite castsubst_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp e2 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1)).
Proof. Admitted.

(* end hide *)

Lemma subst_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp e2 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1).
Proof. Admitted.

#[export] Hint Resolve subst_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_intro_rec using solve [auto] : lngen.

Lemma typsubst_typ_intro :
forall X1 A1 A2,
  X1 `notin` typefv_typ A1 ->
  open_typ_wrt_typ A1 A2 = typsubst_typ A2 X1 (open_typ_wrt_typ A1 (t_var_f X1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_typ_intro : lngen.

Lemma typsubst_castop_intro :
forall X1 c1 A1,
  X1 `notin` typefv_castop c1 ->
  open_castop_wrt_typ c1 A1 = typsubst_castop A1 X1 (open_castop_wrt_typ c1 (t_var_f X1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_castop_intro : lngen.

Lemma castsubst_castop_intro :
forall cx1 c1 c2,
  cx1 `notin` castfv_castop c1 ->
  open_castop_wrt_castop c1 c2 = castsubst_castop c2 cx1 (open_castop_wrt_castop c1 (c_var_f cx1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_castop_intro : lngen.

Lemma typsubst_exp_intro :
forall X1 e1 A1,
  X1 `notin` typefv_exp e1 ->
  open_exp_wrt_typ e1 A1 = typsubst_exp A1 X1 (open_exp_wrt_typ e1 (t_var_f X1)).
Proof. Admitted.

#[export] Hint Resolve typsubst_exp_intro : lngen.

Lemma castsubst_exp_intro :
forall cx1 e1 c1,
  cx1 `notin` castfv_exp e1 ->
  open_exp_wrt_castop e1 c1 = castsubst_exp c1 cx1 (open_exp_wrt_castop e1 (c_var_f cx1)).
Proof. Admitted.

#[export] Hint Resolve castsubst_exp_intro : lngen.

Lemma subst_exp_intro :
forall x1 e1 e2,
  x1 `notin` termfv_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp e2 x1 (open_exp_wrt_exp e1 (e_var_f x1)).
Proof. Admitted.

#[export] Hint Resolve subst_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
