(* generated by Ott 0.32, locally-nameless lngen from: ./spec/rules.ott ./spec/equi.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition typevar : Set := var.
Definition termvar : Set := var.
Definition castvar : Set := var.
Definition label : Set := nat.
Definition int : Set := nat.

Inductive typ : Set :=  (*r types *)
 | t_var_b : nat -> typ (*r type variable *)
 | t_var_f : typevar -> typ (*r type variable *)
 | t_int : typ (*r int type *)
 | t_top : typ (*r top type *)
 | t_arrow : typ -> typ -> typ (*r function type *)
 | t_mu : typ -> typ (*r recursive type *).

Inductive castop : Set :=  (*r cast operators *)
 | c_var_b : nat -> castop (*r cast variable *)
 | c_var_f : castvar -> castop (*r cast variable *)
 | c_id : castop (*r id operator *)
 | c_unfold : typ -> castop (*r unfold operator *)
 | c_fold : typ -> castop (*r castdn *)
 | c_arrow : castop -> castop -> castop (*r arrow operator *)
 | c_seq : castop -> castop -> castop (*r composition of casts *)
 | c_fixc : castop -> castop (*r fixpoint *).

Definition ctx : Set := list ( atom * typ ).

Inductive exp : Set :=  (*r expressions *)
 | e_var_b : nat -> exp (*r variable *)
 | e_var_f : termvar -> exp (*r variable *)
 | e_lit : int -> exp (*r literal value *)
 | e_abs : typ -> exp -> exp (*r function abstraction *)
 | e_app : exp -> exp -> exp (*r function applications *)
 | e_cast : castop -> exp -> exp.

Definition acctx : Set := list (atom * atom).

Definition tctx : Set := list ( atom * unit ).

Definition actx : Set := list ((typ * typ)).

Definition cctx : Set := list ( atom * (typ * typ)).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_typ_wrt_typ_rec (k:nat) (A5:typ) (A_6:typ) {struct A_6}: typ :=
  match A_6 with
  | (t_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_var_b nat
        | inleft (right _) => A5
        | inright _ => t_var_b (nat - 1)
      end
  | (t_var_f X) => t_var_f X
  | t_int => t_int 
  | t_top => t_top 
  | (t_arrow A B) => t_arrow (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec k A5 B)
  | (t_mu A) => t_mu (open_typ_wrt_typ_rec (S k) A5 A)
end.

Fixpoint open_castop_wrt_castop_rec (k:nat) (c_5:castop) (c__6:castop) {struct c__6}: castop :=
  match c__6 with
  | (c_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => c_var_b nat
        | inleft (right _) => c_5
        | inright _ => c_var_b (nat - 1)
      end
  | (c_var_f cx) => c_var_f cx
  | c_id => c_id 
  | (c_unfold A) => c_unfold A
  | (c_fold A) => c_fold A
  | (c_arrow c1 c2) => c_arrow (open_castop_wrt_castop_rec k c_5 c1) (open_castop_wrt_castop_rec k c_5 c2)
  | (c_seq c1 c2) => c_seq (open_castop_wrt_castop_rec k c_5 c1) (open_castop_wrt_castop_rec k c_5 c2)
  | (c_fixc c) => c_fixc (open_castop_wrt_castop_rec (S k) c_5 c)
end.

Fixpoint open_castop_wrt_typ_rec (k:nat) (A5:typ) (c_5:castop) {struct c_5}: castop :=
  match c_5 with
  | (c_var_b nat) => c_var_b nat
  | (c_var_f cx) => c_var_f cx
  | c_id => c_id 
  | (c_unfold A) => c_unfold (open_typ_wrt_typ_rec k A5 A)
  | (c_fold A) => c_fold (open_typ_wrt_typ_rec k A5 A)
  | (c_arrow c1 c2) => c_arrow (open_castop_wrt_typ_rec k A5 c1) (open_castop_wrt_typ_rec k A5 c2)
  | (c_seq c1 c2) => c_seq (open_castop_wrt_typ_rec k A5 c1) (open_castop_wrt_typ_rec k A5 c2)
  | (c_fixc c) => c_fixc (open_castop_wrt_typ_rec k A5 c)
end.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_cast c e) => e_cast c (open_exp_wrt_exp_rec k e_5 e)
end.

Fixpoint open_exp_wrt_castop_rec (k:nat) (c5:castop) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (open_exp_wrt_castop_rec k c5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_castop_rec k c5 e1) (open_exp_wrt_castop_rec k c5 e2)
  | (e_cast c e) => e_cast (open_castop_wrt_castop_rec k c5 c) (open_exp_wrt_castop_rec k c5 e)
end.

Fixpoint open_exp_wrt_typ_rec (k:nat) (A5:typ) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (open_typ_wrt_typ_rec k A5 A) (open_exp_wrt_typ_rec k A5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_cast c e) => e_cast (open_castop_wrt_typ_rec k A5 c) (open_exp_wrt_typ_rec k A5 e)
end.

Definition open_castop_wrt_typ A5 c_5 := open_castop_wrt_typ_rec 0 c_5 A5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_exp_wrt_castop c5 e_5 := open_exp_wrt_castop_rec 0 e_5 c5.

Definition open_castop_wrt_castop c_5 c__6 := open_castop_wrt_castop_rec 0 c__6 c_5.

Definition open_typ_wrt_typ A5 A_6 := open_typ_wrt_typ_rec 0 A_6 A5.

Definition open_exp_wrt_typ A5 e_5 := open_exp_wrt_typ_rec 0 e_5 A5.

(** closing up abstractions *)
Fixpoint close_typ_wrt_typ_rec (k:nat) (A5:var) (A_6:typ) {struct A_6}: typ :=
  match A_6 with
  | (t_var_b nat) => 
       if (lt_dec nat k) 
         then t_var_b nat
         else t_var_b (S nat)
  | (t_var_f X) => if (A5 === X) then (t_var_b k) else (t_var_f X)
  | t_int => t_int 
  | t_top => t_top 
  | (t_arrow A B) => t_arrow (close_typ_wrt_typ_rec k A5 A) (close_typ_wrt_typ_rec k A5 B)
  | (t_mu A) => t_mu (close_typ_wrt_typ_rec (S k) A5 A)
end.

Fixpoint close_castop_wrt_castop_rec (k:nat) (c_5:var) (c__6:castop) {struct c__6}: castop :=
  match c__6 with
  | (c_var_b nat) => 
       if (lt_dec nat k) 
         then c_var_b nat
         else c_var_b (S nat)
  | (c_var_f cx) => if (c_5 === cx) then (c_var_b k) else (c_var_f cx)
  | c_id => c_id 
  | (c_unfold A) => c_unfold A
  | (c_fold A) => c_fold A
  | (c_arrow c1 c2) => c_arrow (close_castop_wrt_castop_rec k c_5 c1) (close_castop_wrt_castop_rec k c_5 c2)
  | (c_seq c1 c2) => c_seq (close_castop_wrt_castop_rec k c_5 c1) (close_castop_wrt_castop_rec k c_5 c2)
  | (c_fixc c) => c_fixc (close_castop_wrt_castop_rec (S k) c_5 c)
end.

Fixpoint close_castop_wrt_typ_rec (k:nat) (A5:var) (c_5:castop) {struct c_5}: castop :=
  match c_5 with
  | (c_var_b nat) => c_var_b nat
  | (c_var_f cx) => c_var_f cx
  | c_id => c_id 
  | (c_unfold A) => c_unfold (close_typ_wrt_typ_rec k A5 A)
  | (c_fold A) => c_fold (close_typ_wrt_typ_rec k A5 A)
  | (c_arrow c1 c2) => c_arrow (close_castop_wrt_typ_rec k A5 c1) (close_castop_wrt_typ_rec k A5 c2)
  | (c_seq c1 c2) => c_seq (close_castop_wrt_typ_rec k A5 c1) (close_castop_wrt_typ_rec k A5 c2)
  | (c_fixc c) => c_fixc (close_castop_wrt_typ_rec k A5 c)
end.

Fixpoint close_exp_wrt_exp_rec (k:nat) (e_5:var) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
       if (lt_dec nat k) 
         then e_var_b nat
         else e_var_b (S nat)
  | (e_var_f x) => if (e_5 === x) then (e_var_b k) else (e_var_f x)
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (close_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (close_exp_wrt_exp_rec k e_5 e1) (close_exp_wrt_exp_rec k e_5 e2)
  | (e_cast c e) => e_cast c (close_exp_wrt_exp_rec k e_5 e)
end.

Fixpoint close_exp_wrt_castop_rec (k:nat) (c5:var) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (close_exp_wrt_castop_rec k c5 e)
  | (e_app e1 e2) => e_app (close_exp_wrt_castop_rec k c5 e1) (close_exp_wrt_castop_rec k c5 e2)
  | (e_cast c e) => e_cast (close_castop_wrt_castop_rec k c5 c) (close_exp_wrt_castop_rec k c5 e)
end.

Fixpoint close_exp_wrt_typ_rec (k:nat) (A5:var) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (close_typ_wrt_typ_rec k A5 A) (close_exp_wrt_typ_rec k A5 e)
  | (e_app e1 e2) => e_app (close_exp_wrt_typ_rec k A5 e1) (close_exp_wrt_typ_rec k A5 e2)
  | (e_cast c e) => e_cast (close_castop_wrt_typ_rec k A5 c) (close_exp_wrt_typ_rec k A5 e)
end.

Definition close_castop_wrt_typ c_5 A5 := close_castop_wrt_typ_rec 0 c_5 A5.

Definition close_exp_wrt_exp e__6 e_5 := close_exp_wrt_exp_rec 0 e__6 e_5.

Definition close_exp_wrt_castop e_5 c5 := close_exp_wrt_castop_rec 0 e_5 c5.

Definition close_castop_wrt_castop c__6 c_5 := close_castop_wrt_castop_rec 0 c__6 c_5.

Definition close_typ_wrt_typ A_6 A5 := close_typ_wrt_typ_rec 0 A_6 A5.

Definition close_exp_wrt_typ e_5 A5 := close_exp_wrt_typ_rec 0 e_5 A5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_typ *)
Inductive lc_typ : typ -> Prop :=    (* defn lc_typ *)
 | lc_t_var_f : forall (X:typevar),
     (lc_typ (t_var_f X))
 | lc_t_int : 
     (lc_typ t_int)
 | lc_t_top : 
     (lc_typ t_top)
 | lc_t_arrow : forall (A B:typ),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_typ (t_arrow A B))
 | lc_t_mu : forall (A:typ),
      ( forall X , lc_typ  ( open_typ_wrt_typ A (t_var_f X) )  )  ->
     (lc_typ (t_mu A)).

(* defns LC_castop *)
Inductive lc_castop : castop -> Prop :=    (* defn lc_castop *)
 | lc_c_var_f : forall (cx:castvar),
     (lc_castop (c_var_f cx))
 | lc_c_id : 
     (lc_castop c_id)
 | lc_c_unfold : forall (A:typ),
     (lc_typ A) ->
     (lc_castop (c_unfold A))
 | lc_c_fold : forall (A:typ),
     (lc_typ A) ->
     (lc_castop (c_fold A))
 | lc_c_arrow : forall (c1 c2:castop),
     (lc_castop c1) ->
     (lc_castop c2) ->
     (lc_castop (c_arrow c1 c2))
 | lc_c_seq : forall (c1 c2:castop),
     (lc_castop c1) ->
     (lc_castop c2) ->
     (lc_castop (c_seq c1 c2))
 | lc_c_fixc : forall (c:castop),
      ( forall cx , lc_castop  ( open_castop_wrt_castop c (c_var_f cx) )  )  ->
     (lc_castop (c_fixc c)).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:termvar),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall (i:int),
     (lc_exp (e_lit i))
 | lc_e_abs : forall (A:typ) (e:exp),
     (lc_typ A) ->
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_cast : forall (c:castop) (e:exp),
     (lc_castop c) ->
     (lc_exp e) ->
     (lc_exp (e_cast c e)).
(** free variables *)
Fixpoint typefv_typ (A5:typ) : vars :=
  match A5 with
  | (t_var_b nat) => {}
  | (t_var_f X) => {{X}}
  | t_int => {}
  | t_top => {}
  | (t_arrow A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_mu A) => (typefv_typ A)
end.

Fixpoint castfv_castop (c_5:castop) : vars :=
  match c_5 with
  | (c_var_b nat) => {}
  | (c_var_f cx) => {{cx}}
  | c_id => {}
  | (c_unfold A) => {}
  | (c_fold A) => {}
  | (c_arrow c1 c2) => (castfv_castop c1) \u (castfv_castop c2)
  | (c_seq c1 c2) => (castfv_castop c1) \u (castfv_castop c2)
  | (c_fixc c) => (castfv_castop c)
end.

Fixpoint typefv_castop (c_5:castop) : vars :=
  match c_5 with
  | (c_var_b nat) => {}
  | (c_var_f cx) => {}
  | c_id => {}
  | (c_unfold A) => (typefv_typ A)
  | (c_fold A) => (typefv_typ A)
  | (c_arrow c1 c2) => (typefv_castop c1) \u (typefv_castop c2)
  | (c_seq c1 c2) => (typefv_castop c1) \u (typefv_castop c2)
  | (c_fixc c) => (typefv_castop c)
end.

Fixpoint termfv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i) => {}
  | (e_abs A e) => (termfv_exp e)
  | (e_app e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_cast c e) => (termfv_exp e)
end.

Fixpoint castfv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {}
  | (e_lit i) => {}
  | (e_abs A e) => (castfv_exp e)
  | (e_app e1 e2) => (castfv_exp e1) \u (castfv_exp e2)
  | (e_cast c e) => (castfv_castop c) \u (castfv_exp e)
end.

Fixpoint typefv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {}
  | (e_lit i) => {}
  | (e_abs A e) => (typefv_typ A) \u (typefv_exp e)
  | (e_app e1 e2) => (typefv_exp e1) \u (typefv_exp e2)
  | (e_cast c e) => (typefv_castop c) \u (typefv_exp e)
end.

(** substitutions *)
Fixpoint typsubst_typ (A5:typ) (X5:typevar) (A_6:typ) {struct A_6} : typ :=
  match A_6 with
  | (t_var_b nat) => t_var_b nat
  | (t_var_f X) => (if eq_var X X5 then A5 else (t_var_f X))
  | t_int => t_int 
  | t_top => t_top 
  | (t_arrow A B) => t_arrow (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_mu A) => t_mu (typsubst_typ A5 X5 A)
end.

Fixpoint castsubst_castop (c_5:castop) (cx5:castvar) (c__6:castop) {struct c__6} : castop :=
  match c__6 with
  | (c_var_b nat) => c_var_b nat
  | (c_var_f cx) => (if eq_var cx cx5 then c_5 else (c_var_f cx))
  | c_id => c_id 
  | (c_unfold A) => c_unfold A
  | (c_fold A) => c_fold A
  | (c_arrow c1 c2) => c_arrow (castsubst_castop c_5 cx5 c1) (castsubst_castop c_5 cx5 c2)
  | (c_seq c1 c2) => c_seq (castsubst_castop c_5 cx5 c1) (castsubst_castop c_5 cx5 c2)
  | (c_fixc c) => c_fixc (castsubst_castop c_5 cx5 c)
end.

Fixpoint typsubst_castop (A5:typ) (X5:typevar) (c_5:castop) {struct c_5} : castop :=
  match c_5 with
  | (c_var_b nat) => c_var_b nat
  | (c_var_f cx) => c_var_f cx
  | c_id => c_id 
  | (c_unfold A) => c_unfold (typsubst_typ A5 X5 A)
  | (c_fold A) => c_fold (typsubst_typ A5 X5 A)
  | (c_arrow c1 c2) => c_arrow (typsubst_castop A5 X5 c1) (typsubst_castop A5 X5 c2)
  | (c_seq c1 c2) => c_seq (typsubst_castop A5 X5 c1) (typsubst_castop A5 X5 c2)
  | (c_fixc c) => c_fixc (typsubst_castop A5 X5 c)
end.

Fixpoint subst_exp (e_5:exp) (x5:termvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_cast c e) => e_cast c (subst_exp e_5 x5 e)
end.

Fixpoint castsubst_exp (c5:castop) (cx5:castvar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (castsubst_exp c5 cx5 e)
  | (e_app e1 e2) => e_app (castsubst_exp c5 cx5 e1) (castsubst_exp c5 cx5 e2)
  | (e_cast c e) => e_cast (castsubst_castop c5 cx5 c) (castsubst_exp c5 cx5 e)
end.

Fixpoint typsubst_exp (A5:typ) (X5:typevar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (typsubst_typ A5 X5 A) (typsubst_exp A5 X5 e)
  | (e_app e1 e2) => e_app (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_cast c e) => e_cast (typsubst_castop A5 X5 c) (typsubst_exp A5 X5 e)
end.


Fixpoint rev_cast (c:castop) :=
  match c with
  | c_id => c_id
  | c_arrow c1 c2 => c_arrow (rev_cast c1) (rev_cast c2) 
  | c_fixc c => c_fixc (rev_cast c)
  | c_unfold t => c_fold t
  | c_fold t => c_unfold t
  | c_seq c1 c2 => c_seq (rev_cast c2) (rev_cast c1)
  | c_var_f x => c_var_f x
  | c_var_b x => c_var_b x
  end.

Fixpoint domA (E : list (atom * atom)) : atoms :=
  match E with
  | nil => {}
  | (X,Y)::E' => singleton X \u singleton Y \u domA E'
  end.



Notation unfold_mu t := 
    (open_typ_wrt_typ t (t_mu t)).



(** definitions *)

(* defns WellFormedType *)
Inductive WFT : tctx -> typ -> Prop :=    (* defn WFT *)
 | WFT_top : forall (D:tctx),
     WFT D t_top
 | WFT_int : forall (D:tctx),
     WFT D t_int
 | WFT_var : forall (D:tctx) (X:typevar),
      X  `in` (dom  D )  ->
     WFT D (t_var_f X)
 | WFT_arrow : forall (D:tctx) (A B:typ),
     WFT D A ->
     WFT D B ->
     WFT D (t_arrow A B)
 | WFT_rec : forall (L:vars) (D:tctx) (A:typ),
      ( forall X , X \notin  L  -> WFT  (cons ( X ,tt )  D )   ( open_typ_wrt_typ A (t_var_f X) )  )  ->
     WFT D (t_mu A).

(* defns WellFormedTypeEnv *)
Inductive WFTyE : tctx -> Prop :=    (* defn WFTyE *)
 | WFTyE_empty : 
     WFTyE  nil 
 | WFTyE_cons : forall (D:tctx) (X:typevar),
     WFTyE D ->
      X  `notin` (dom  D )  ->
     WFTyE  (cons ( X ,tt )  D ) .

(* defns TypCast *)
Inductive TypCast : tctx -> cctx -> typ -> typ -> castop -> Prop :=    (* defn TypCast *)
 | TCast_id : forall (D:tctx) (E:cctx) (A:typ),
     WFT D A ->
      uniq  E  ->
     TypCast D E A A c_id
 | TCast_arrow : forall (D:tctx) (E:cctx) (A1 B1 A2 B2:typ) (c1 c2:castop),
     TypCast D E A1 A2 c1 ->
     TypCast D E B1 B2 c2 ->
     TypCast D E (t_arrow A1 B1) (t_arrow A2 B2) (c_arrow c1 c2)
 | TCast_unfold : forall (D:tctx) (E:cctx) (A:typ),
     WFT D (t_mu A) ->
      uniq  E  ->
     TypCast D E (t_mu A)  (open_typ_wrt_typ  A (t_mu A) )  (c_unfold (t_mu A))
 | TCast_fold : forall (D:tctx) (E:cctx) (A:typ),
     WFT D (t_mu A) ->
      uniq  E  ->
     TypCast D E  (open_typ_wrt_typ  A (t_mu A) )  (t_mu A) (c_fold (t_mu A))
 | TCast_seq : forall (D:tctx) (E:cctx) (A C:typ) (c1 c2:castop) (B:typ),
     TypCast D E A B c1 ->
     TypCast D E B C c2 ->
     TypCast D E A C (c_seq c1 c2)
 | TCast_var : forall (D:tctx) (E:cctx) (A B:typ) (cx:castvar),
     WFT D A ->
     WFT D B ->
      uniq  E  ->
      In ( cx , ( A ,  B ))  E  ->
     TypCast D E A B (c_var_f cx)
 | TCast_fix : forall (L:vars) (D:tctx) (E:cctx) (A1 B1 A2 B2:typ) (c1 c2:castop),
      ( forall cx , cx \notin  L  -> TypCast D  (cons ( cx , ( (t_arrow A1 B1) ,  (t_arrow A2 B2) ))  E )  A1 A2  ( open_castop_wrt_castop c1 (c_var_f cx) )  )  ->
      ( forall cx , cx \notin  L  -> TypCast D  (cons ( cx , ( (t_arrow A1 B1) ,  (t_arrow A2 B2) ))  E )  B1 B2  ( open_castop_wrt_castop c2 (c_var_f cx) )  )  ->
     TypCast D E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc  (c_arrow c1 c2) ).

(* defns WellFormedTermEnv *)
Inductive WFTmE : ctx -> Prop :=    (* defn WFTmE *)
 | WFTmE_empty : 
     WFTmE  nil 
 | WFTmE_cons : forall (G:ctx) (x:termvar) (A:typ),
     WFTmE G ->
     WFT  nil  A ->
      ~ AtomSetImpl.In  x  (dom  G )  ->
     WFTmE  (cons ( x , A )  G ) .

(* defns AmberWellFormedEnv *)
Inductive AmberWF : acctx -> Prop :=    (* defn AmberWF *)
 | AWF_nil : 
     AmberWF  nil 
 | AWF_cons : forall (AE:acctx) (X Y:typevar),
     AmberWF AE ->
      ~ AtomSetImpl.In  X  (domA  AE )  ->
      ~ AtomSetImpl.In  Y  (domA  AE )  ->
      X  <>  Y  ->
     AmberWF  (cons ( X , Y  )  AE ) .

(* defns AmberWellFormedType *)
Inductive AmberWFT : acctx -> typ -> Prop :=    (* defn AmberWFT *)
 | AWFT_nat : forall (AE:acctx),
     AmberWF AE ->
     AmberWFT AE t_int
 | AWFT_top : forall (AE:acctx),
     AmberWF AE ->
     AmberWFT AE t_top
 | AWFT_varl : forall (AE:acctx) (X Y:typevar),
     AmberWF AE ->
      In ( X ,  Y )  AE  ->
     AmberWFT AE (t_var_f X)
 | AWFT_varr : forall (AE:acctx) (Y X:typevar),
     AmberWF AE ->
      In ( X ,  Y )  AE  ->
     AmberWFT AE (t_var_f Y)
 | AWFT_arrow : forall (AE:acctx) (A1 A2:typ),
     AmberWFT AE A1 ->
     AmberWFT AE A2 ->
     AmberWFT AE (t_arrow A1 A2)
 | AWFT_rec : forall (L:vars) (AE:acctx) (A:typ) (Y:typevar),
      ( forall X , X \notin  L  ->  (* (forall L, X `notin` L ->  *)
        
          (forall Y, Y `notin` L \u singleton X ->
            AmberWFT (cons ( X ,  Y )  AE  )   ( open_typ_wrt_typ A (t_var_f X) )  )  )  ->
     AmberWFT AE (t_mu A).

(* defns AmberSubtyping *)
Inductive AmberSubtyping : acctx -> typ -> typ -> Prop :=    (* defn AmberSubtyping *)
 | ASub_nat : forall (AE:acctx),
     AmberWF AE ->
     AmberSubtyping AE t_int t_int
 | ASub_top : forall (AE:acctx) (A:typ),
     AmberWF AE ->
     AmberWFT AE A ->
     AmberSubtyping AE A t_top
 | ASub_arrow : forall (AE:acctx) (A1 A2 B1 B2:typ),
     AmberSubtyping AE B1 A1 ->
     AmberSubtyping AE A2 B2 ->
     AmberSubtyping AE (t_arrow A1 A2) (t_arrow B1 B2)
 | ASub_var : forall (AE:acctx) (X Y:typevar),
     AmberWF AE ->
      In ( X ,  Y )  AE  ->
     AmberSubtyping AE (t_var_f X) (t_var_f Y)
 | ASub_rec : forall (L:vars) (AE:acctx) (A B:typ),
      ( forall Y , Y \notin  L  ->  ( forall X , X \notin   L  \u {{ Y }}  -> AmberSubtyping  (cons ( X , Y  )  AE )   ( open_typ_wrt_typ A (t_var_f X) )   ( open_typ_wrt_typ B (t_var_f Y) )  )  )  ->
     AmberSubtyping AE (t_mu A) (t_mu B)
 | ASub_self : forall (AE:acctx) (A:typ),
     AmberWF AE ->
     AmberWFT AE (t_mu A) ->
     AmberSubtyping AE (t_mu A) (t_mu A).

(* defns Typing *)
Inductive Typing : ctx -> exp -> typ -> Prop :=    (* defn Typing *)
 | Typing_int : forall (G:ctx) (i:int),
     WFTmE G ->
     Typing G (e_lit i) t_int
 | Typing_var : forall (G:ctx) (x:termvar) (A:typ),
     WFTmE G ->
      binds  x A G  ->
     Typing G (e_var_f x) A
 | Typing_abs : forall (L:vars) (G:ctx) (A1:typ) (e:exp) (A2:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A2 )  ->
     Typing G (e_abs A1 e) (t_arrow A1 A2)
 | Typing_app : forall (G:ctx) (e1 e2:exp) (A2 A1:typ),
     Typing G e1 (t_arrow A1 A2) ->
     Typing G e2 A1 ->
     Typing G (e_app e1 e2) A2
 | Typing_cast : forall (G:ctx) (c:castop) (e:exp) (B A:typ),
     Typing G e A ->
     TypCast  nil   nil  A B c ->
     Typing G (e_cast c e) B
 | Typing_sub : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e A ->
     AmberSubtyping  nil  A B ->
     Typing G e B.

(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | V_lit : forall (i:int),
     value (e_lit i)
 | V_abs : forall (A:typ) (e:exp),
     lc_typ A ->
     lc_exp (e_abs A e) ->
     value  ( (e_abs A e) ) 
 | V_fold : forall (A:typ) (e:exp),
     lc_typ A ->
     value e ->
     value  ( (e_cast (c_fold A) e) ) 
 | V_arrow : forall (c1 c2:castop) (e:exp),
     lc_castop c1 ->
     lc_castop c2 ->
     value e ->
     value  ( (e_cast (c_arrow c1 c2) e) ) .

(* defns Reduction *)
Inductive Reduction : exp -> exp -> Prop :=    (* defn Reduction *)
 | Red_beta : forall (A:typ) (e e':exp),
     lc_typ A ->
     lc_exp (e_abs A e) ->
     value e' ->
     Reduction (e_app  ( (e_abs A e) )  e')  (open_exp_wrt_exp  e e' ) 
 | Red_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     Reduction e1 e1' ->
     Reduction (e_app e1 e2) (e_app e1' e2)
 | Red_appr : forall (v1 e2 e2':exp),
     value v1 ->
     Reduction e2 e2' ->
     Reduction (e_app v1 e2) (e_app v1 e2')
 | Red_cast_arr : forall (c1 c2:castop) (e1 e2:exp),
     lc_castop c2 ->
     lc_castop c1 ->
     value e1 ->
     value e2 ->
     Reduction (e_app  ( (e_cast (c_arrow c1 c2) e1) )  e2) (e_cast c2  ( (e_app e1  ( (e_cast  (rev_cast  c1 )  e2) ) ) ) )
 | Red_cast_seq : forall (c1 c2:castop) (e:exp),
     lc_castop c2 ->
     lc_castop c1 ->
     value e ->
     Reduction (e_cast (c_seq c1 c2) e) (e_cast c2  ( (e_cast c1 e) ) )
 | Red_cast : forall (c:castop) (e e':exp),
     lc_castop c ->
     Reduction e e' ->
     Reduction (e_cast c e) (e_cast c e')
 | Red_castelim : forall (A B:typ) (v:exp),
     lc_typ A ->
     lc_typ B ->
     value v ->
     Reduction (e_cast (c_unfold A)  ( (e_cast (c_fold B) v) ) ) v
 | Red_castid : forall (v:exp),
     value v ->
     Reduction (e_cast c_id v) v
 | Red_castfix : forall (c:castop) (e:exp),
     lc_castop (c_fixc c) ->
     value e ->
     Reduction (e_cast (c_fixc c) e) (e_cast  (open_castop_wrt_castop  c   (c_fixc c) )  e).

(* defns eqe *)
Inductive eqe2 : tctx -> actx -> typ -> typ -> Prop :=    (* defn eqe2 *)
 | e2_assump : forall (D:tctx) (H:actx) (A B:typ),
      In ( A ,  B )  H  ->
     WFT D A ->
     WFT D B ->
     eqe2 D H A B
 | e2_refl : forall (D:tctx) (H:actx) (A:typ),
     WFT D A ->
     eqe2 D H A A
 | e2_trans : forall (D:tctx) (H:actx) (A C B:typ),
     eqe2 D H A B ->
     eqe2 D H B C ->
     eqe2 D H A C
 | e2_symm : forall (D:tctx) (H:actx) (B A:typ),
     eqe2 D H A B ->
     eqe2 D H B A
 | e2_fld : forall (D:tctx) (H:actx) (A:typ),
     WFT D (t_mu A) ->
     eqe2 D H (t_mu A)  (open_typ_wrt_typ  A (t_mu A) ) 
 | e2_arrfix : forall (D:tctx) (H:actx) (A1 A2 B1 B2:typ),
     eqe2 D  (cons ( (t_arrow A1 A2) ,  (t_arrow B1 B2) )  H )  A1 B1 ->
     eqe2 D  (cons ( (t_arrow A1 A2) ,  (t_arrow B1 B2) )  H )  A2 B2 ->
     eqe2 D H (t_arrow A1 A2) (t_arrow B1 B2).

(* defns ACSubtyping *)
Inductive ACSubtyping : acctx -> typ -> typ -> Prop :=    (* defn ACSubtyping *)
 | ACSub_top : forall (AE:acctx) (A:typ),
     AmberWF AE ->
     AmberWFT AE A ->
     ACSubtyping AE A t_top
 | ACSub_refl : forall (AE:acctx) (A:typ),
     AmberWF AE ->
     AmberWFT AE A ->
     ACSubtyping AE A A
 | ACSub_trans : forall (AE:acctx) (A C B:typ),
     ACSubtyping AE A B ->
     ACSubtyping AE B C ->
     ACSubtyping AE A C
 | ACSub_var : forall (AE:acctx) (X Y:typevar),
     AmberWF AE ->
      In ( X ,  Y )  AE  ->
     ACSubtyping AE (t_var_f X) (t_var_f Y)
 | ACSub_eq : forall (AE:acctx) (A B:typ),
     AmberWF AE ->
     eqe2  nil   nil  A B ->
     ACSubtyping AE A B
 | ACSub_arrow : forall (AE:acctx) (A1 A2 B1 B2:typ),
     ACSubtyping AE B1 A1 ->
     ACSubtyping AE A2 B2 ->
     ACSubtyping AE (t_arrow A1 A2) (t_arrow B1 B2)
 | ACSub_rec : forall (L:vars) (AE:acctx) (A B:typ),
      ( forall Y , Y \notin  L  ->  ( forall X , X \notin   L  \u {{ Y }}  -> ACSubtyping  (cons ( X , Y  )  AE )   ( open_typ_wrt_typ A (t_var_f X) )   ( open_typ_wrt_typ B (t_var_f Y) )  )  )  ->
     ACSubtyping AE (t_mu A) (t_mu B).

(* defns EquiTyping *)
Inductive EquiTyping : ctx -> exp -> typ -> Prop :=    (* defn EquiTyping *)
 | ETyping_int : forall (G:ctx) (i:int),
     WFTmE G ->
     EquiTyping G (e_lit i) t_int
 | ETyping_var : forall (G:ctx) (x:termvar) (A:typ),
     WFTmE G ->
      binds  x A G  ->
     EquiTyping G (e_var_f x) A
 | ETyping_abs : forall (L:vars) (G:ctx) (A1:typ) (e:exp) (A2:typ),
      ( forall x , x \notin  L  -> EquiTyping  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A2 )  ->
     EquiTyping G (e_abs A1 e) (t_arrow A1 A2)
 | ETyping_app : forall (G:ctx) (e1 e2:exp) (A2 A1:typ),
     EquiTyping G e1 (t_arrow A1 A2) ->
     EquiTyping G e2 A1 ->
     EquiTyping G (e_app e1 e2) A2
 | ETyping_eq : forall (G:ctx) (e:exp) (B A:typ),
     EquiTyping G e A ->
     eqe2  nil   nil  A B ->
     EquiTyping G e B
 | ETyping_sub : forall (G:ctx) (e:exp) (B A:typ),
     EquiTyping G e A ->
     ACSubtyping  nil  A B ->
     EquiTyping G e B.

(* defns EquiTypingC *)
Inductive EquiTypingC : ctx -> exp -> typ -> exp -> Prop :=    (* defn EquiTypingC *)
 | ECTyping_int : forall (G:ctx) (i:int),
     WFTmE G ->
     EquiTypingC G (e_lit i) t_int (e_lit i)
 | ECTyping_var : forall (G:ctx) (x:termvar) (A:typ),
     WFTmE G ->
      binds  x A G  ->
     EquiTypingC G (e_var_f x) A (e_var_f x)
 | ECTyping_abs : forall (L:vars) (G:ctx) (A1:typ) (e:exp) (A2:typ) (e':exp),
      ( forall x , x \notin  L  -> EquiTypingC  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A2  ( open_exp_wrt_exp e' (e_var_f x) )  )  ->
     EquiTypingC G (e_abs A1 e) (t_arrow A1 A2) (e_abs A1 e')
 | ECTyping_app : forall (G:ctx) (e1 e2:exp) (A2:typ) (e1' e2':exp) (A1:typ),
     EquiTypingC G e1 (t_arrow A1 A2) e1' ->
     EquiTypingC G e2 A1 e2' ->
     EquiTypingC G (e_app e1 e2) A2 (e_app e1' e2')
 | ECTyping_eq : forall (G:ctx) (e:exp) (B:typ) (c:castop) (e':exp) (A:typ),
     EquiTypingC G e A e' ->
     TypCast  nil   nil  A B c ->
     EquiTypingC G e B (e_cast c e')
 | ECTyping_isub : forall (G:ctx) (e:exp) (B:typ) (e':exp) (A:typ),
     EquiTypingC G e A e' ->
     AmberSubtyping  nil  A B ->
     EquiTypingC G e B e'.


(** infrastructure *)
#[export] Hint Constructors WFT WFTyE TypCast WFTmE AmberWF AmberWFT AmberSubtyping Typing value Reduction eqe2 ACSubtyping EquiTyping EquiTypingC lc_typ lc_castop lc_exp : core.


