(* generated by Ott 0.32, locally-nameless lngen from: ./spec/rules.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition typevar : Set := var.
Definition termvar : Set := var.
Definition label : Set := nat.
Definition int : Set := nat.

Inductive typ : Set :=  (*r types *)
 | t_var_b : nat -> typ (*r type variable *)
 | t_var_f : typevar -> typ (*r type variable *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top type *)
 | t_arrow : typ -> typ -> typ (*r function type *)
 | t_mu : typ -> typ (*r recursive type *).

Inductive castop : Set :=  (*r cast operators *)
 | c_id : castop (*r id operator *)
 | c_unfold : typ -> castop (*r unfold operator *)
 | c_fold : typ -> castop (*r castdn *)
 | c_arrow : castop -> castop -> castop (*r arrow operator *).

Inductive exp : Set :=  (*r expressions *)
 | e_var_b : nat -> exp (*r variable *)
 | e_var_f : termvar -> exp (*r variable *)
 | e_top : exp (*r top *)
 | e_lit : int -> exp (*r lit *)
 | e_abs : typ -> exp -> exp (*r abstraction with argument annotation *)
 | e_fixpoint : typ -> exp -> exp (*r fixpoint *)
 | e_app : exp -> exp -> exp (*r applications *)
 | e_cast : castop -> exp -> exp.

Definition tctx : Set := list ( atom * unit ).

Definition ctx : Set := list ( atom * typ ).

Inductive mode : Set :=  (*r modes *)
 | m_pos : mode (*r positive *)
 | m_neg : mode (*r negative *).

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

Fixpoint open_castop_wrt_typ_rec (k:nat) (A5:typ) (c_5:castop) {struct c_5}: castop :=
  match c_5 with
  | c_id => c_id 
  | (c_unfold A) => c_unfold (open_typ_wrt_typ_rec k A5 A)
  | (c_fold A) => c_fold (open_typ_wrt_typ_rec k A5 A)
  | (c_arrow c1 c2) => c_arrow (open_castop_wrt_typ_rec k A5 c1) (open_castop_wrt_typ_rec k A5 c2)
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
  | e_top => e_top 
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_fixpoint A e) => e_fixpoint A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_cast c e) => e_cast c (open_exp_wrt_exp_rec k e_5 e)
end.

Fixpoint open_exp_wrt_typ_rec (k:nat) (A5:typ) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | e_top => e_top 
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (open_typ_wrt_typ_rec k A5 A) (open_exp_wrt_typ_rec k A5 e)
  | (e_fixpoint A e) => e_fixpoint (open_typ_wrt_typ_rec k A5 A) (open_exp_wrt_typ_rec k A5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_cast c e) => e_cast (open_castop_wrt_typ_rec k A5 c) (open_exp_wrt_typ_rec k A5 e)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_typ_wrt_typ A5 A_6 := open_typ_wrt_typ_rec 0 A_6 A5.

Definition open_exp_wrt_typ A5 e_5 := open_exp_wrt_typ_rec 0 e_5 A5.

Definition open_castop_wrt_typ A5 c_5 := open_castop_wrt_typ_rec 0 c_5 A5.

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

Fixpoint close_castop_wrt_typ_rec (k:nat) (A5:var) (c_5:castop) {struct c_5}: castop :=
  match c_5 with
  | c_id => c_id 
  | (c_unfold A) => c_unfold (close_typ_wrt_typ_rec k A5 A)
  | (c_fold A) => c_fold (close_typ_wrt_typ_rec k A5 A)
  | (c_arrow c1 c2) => c_arrow (close_castop_wrt_typ_rec k A5 c1) (close_castop_wrt_typ_rec k A5 c2)
end.

Fixpoint close_exp_wrt_exp_rec (k:nat) (e_5:var) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
       if (lt_dec nat k) 
         then e_var_b nat
         else e_var_b (S nat)
  | (e_var_f x) => if (e_5 === x) then (e_var_b k) else (e_var_f x)
  | e_top => e_top 
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (close_exp_wrt_exp_rec (S k) e_5 e)
  | (e_fixpoint A e) => e_fixpoint A (close_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (close_exp_wrt_exp_rec k e_5 e1) (close_exp_wrt_exp_rec k e_5 e2)
  | (e_cast c e) => e_cast c (close_exp_wrt_exp_rec k e_5 e)
end.

Fixpoint close_exp_wrt_typ_rec (k:nat) (A5:var) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | e_top => e_top 
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (close_typ_wrt_typ_rec k A5 A) (close_exp_wrt_typ_rec k A5 e)
  | (e_fixpoint A e) => e_fixpoint (close_typ_wrt_typ_rec k A5 A) (close_exp_wrt_typ_rec k A5 e)
  | (e_app e1 e2) => e_app (close_exp_wrt_typ_rec k A5 e1) (close_exp_wrt_typ_rec k A5 e2)
  | (e_cast c e) => e_cast (close_castop_wrt_typ_rec k A5 c) (close_exp_wrt_typ_rec k A5 e)
end.

Definition close_castop_wrt_typ c_5 A5 := close_castop_wrt_typ_rec 0 c_5 A5.

Definition close_exp_wrt_exp e__6 e_5 := close_exp_wrt_exp_rec 0 e__6 e_5.

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
     (lc_castop (c_arrow c1 c2)).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:termvar),
     (lc_exp (e_var_f x))
 | lc_e_top : 
     (lc_exp e_top)
 | lc_e_lit : forall (i:int),
     (lc_exp (e_lit i))
 | lc_e_abs : forall (A:typ) (e:exp),
     (lc_typ A) ->
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e))
 | lc_e_fixpoint : forall (A:typ) (e:exp),
     (lc_typ A) ->
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_fixpoint A e))
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

Fixpoint typefv_castop (c_5:castop) : vars :=
  match c_5 with
  | c_id => {}
  | (c_unfold A) => (typefv_typ A)
  | (c_fold A) => (typefv_typ A)
  | (c_arrow c1 c2) => (typefv_castop c1) \u (typefv_castop c2)
end.

Fixpoint termfv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | e_top => {}
  | (e_lit i) => {}
  | (e_abs A e) => (termfv_exp e)
  | (e_fixpoint A e) => (termfv_exp e)
  | (e_app e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_cast c e) => (termfv_exp e)
end.

Fixpoint typefv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {}
  | e_top => {}
  | (e_lit i) => {}
  | (e_abs A e) => (typefv_typ A) \u (typefv_exp e)
  | (e_fixpoint A e) => (typefv_typ A) \u (typefv_exp e)
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

Fixpoint typsubst_castop (A5:typ) (X5:typevar) (c_5:castop) {struct c_5} : castop :=
  match c_5 with
  | c_id => c_id 
  | (c_unfold A) => c_unfold (typsubst_typ A5 X5 A)
  | (c_fold A) => c_fold (typsubst_typ A5 X5 A)
  | (c_arrow c1 c2) => c_arrow (typsubst_castop A5 X5 c1) (typsubst_castop A5 X5 c2)
end.

Fixpoint subst_exp (e_5:exp) (x5:termvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | e_top => e_top 
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (subst_exp e_5 x5 e)
  | (e_fixpoint A e) => e_fixpoint A (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_cast c e) => e_cast c (subst_exp e_5 x5 e)
end.

Fixpoint typsubst_exp (A5:typ) (X5:typevar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | e_top => e_top 
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (typsubst_typ A5 X5 A) (typsubst_exp A5 X5 e)
  | (e_fixpoint A e) => e_fixpoint (typsubst_typ A5 X5 A) (typsubst_exp A5 X5 e)
  | (e_app e1 e2) => e_app (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_cast c e) => e_cast (typsubst_castop A5 X5 c) (typsubst_exp A5 X5 e)
end.


Fixpoint rev_cast (c : castop) : castop :=
  match c with
  | c_id => c_id
  | (c_unfold A) => (c_fold A)
  | (c_fold A) => (c_unfold A)
  | (c_arrow c1 c2) =>  c_arrow (rev_cast c1) (rev_cast c2)
  end.



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
      ~  X  `notin` (dom  D )  ->
     WFTyE  (cons ( X ,tt )  D ) .

(* defns Ordinary *)
Inductive ordinary : typ -> Prop :=    (* defn ordinary *)
 | Ord_int : 
     ordinary t_int
 | Ord_top : 
     ordinary t_top
 | Ord_var : forall (X:typevar),
     ordinary (t_var_f X)
 | Ord_rec : forall (A:typ),
     lc_typ (t_mu A) ->
     ordinary  (t_mu A) .

(* defns TypCast *)
Inductive TypCast : tctx -> typ -> typ -> castop -> Prop :=    (* defn TypCast *)
 | TCast_id : forall (D:tctx) (A:typ),
     WFT D A ->
     TypCast D A A c_id
 | TCast_arrow : forall (D:tctx) (A1 B1 A2 B2:typ) (c1 c2:castop),
     TypCast D A1 A2 c1 ->
     TypCast D B1 B2 c2 ->
     TypCast D (t_arrow A1 B1) (t_arrow A2 B2) (c_arrow c1 c2)
 | TCast_unfold : forall (D:tctx) (A:typ),
     WFT D (t_mu A) ->
     TypCast D (t_mu A)  (open_typ_wrt_typ  A (t_mu A) )  (c_unfold (t_mu A))
 | TCast_fold : forall (D:tctx) (A:typ),
     WFT D (t_mu A) ->
     TypCast D  (open_typ_wrt_typ  A (t_mu A) )  (t_mu A) (c_fold (t_mu A)).

(* defns WellFormedTermEnv *)
Inductive WFTmE : tctx -> ctx -> Prop :=    (* defn WFTmE *)
 | WFTmE_empty : forall (D:tctx),
     WFTmE D  nil 
 | WFTmE_cons : forall (D:tctx) (G:ctx) (x:termvar) (A:typ),
     WFTmE D G ->
     WFT D A ->
      ~ AtomSetImpl.In  x  (dom  G )  ->
     WFTmE D  (cons ( x , A )  G ) .

(* defns Typing *)
Inductive Typing : tctx -> ctx -> exp -> typ -> Prop :=    (* defn Typing *)
 | Typing_int : forall (D:tctx) (G:ctx) (i:int),
     WFTyE D ->
     WFTmE D G ->
     Typing D G (e_lit i) t_int
 | Typing_var : forall (D:tctx) (G:ctx) (x:termvar) (A:typ),
     WFTyE D ->
     WFTmE D G ->
      binds  x A G  ->
     Typing D G (e_var_f x) A
 | Typing_abs : forall (L:vars) (D:tctx) (G:ctx) (A1:typ) (e:exp) (A2:typ),
      ( forall x , x \notin  L  -> Typing D  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A2 )  ->
     Typing D G (e_abs A1 e) (t_arrow A1 A2)
 | Typing_app : forall (D:tctx) (G:ctx) (e1 e2:exp) (A2 A1:typ),
     Typing D G e1 (t_arrow A1 A2) ->
     Typing D G e2 A1 ->
     Typing D G (e_app e1 e2) A2
 | Typing_fix : forall (L:vars) (D:tctx) (G:ctx) (A:typ) (e:exp),
      ( forall x , x \notin  L  -> Typing D  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A )  ->
     Typing D G (e_fixpoint A e) A
 | Typing_cast : forall (D:tctx) (G:ctx) (c:castop) (e:exp) (B A:typ),
     Typing D G e A ->
     TypCast D A B c ->
     Typing D G (e_cast c e) B.

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

(* defns DualCast *)
Inductive DualCast : castop -> castop -> Prop :=    (* defn DualCast *)
 | DCast_id : 
     DualCast c_id c_id
 | DCast_arrow : forall (c1 c2 c1' c2':castop),
     DualCast c1 c1' ->
     DualCast c2 c2' ->
     DualCast (c_arrow c1 c2) (c_arrow c1' c2')
 | DCast_rec : forall (A:typ),
     lc_typ A ->
     DualCast (c_unfold A) (c_fold A).

(* defns Reduction *)
Inductive Reduction : exp -> exp -> Prop :=    (* defn Reduction *)
 | Red_beta : forall (A:typ) (e e':exp),
     lc_typ A ->
     lc_exp (e_abs A e) ->
     lc_exp e' ->
     Reduction (e_app  ( (e_abs A e) )  e')  (open_exp_wrt_exp  e e' ) 
 | Red_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     Reduction e1 e1' ->
     Reduction (e_app e1 e2) (e_app e1' e2)
 | Red_appr : forall (v1 e2 e2':exp),
     value v1 ->
     Reduction e2 e2' ->
     Reduction (e_app v1 e2) (e_app v1 e2')
 | Red_fix : forall (A:typ) (e:exp),
     lc_typ A ->
     lc_exp (e_fixpoint A e) ->
     Reduction (e_fixpoint A e)  (open_exp_wrt_exp  e (e_fixpoint A e) ) 
 | Red_cast_arr : forall (c1 c2:castop) (e1 e2:exp),
     lc_castop c2 ->
     lc_exp e1 ->
     lc_castop c1 ->
     lc_exp e2 ->
     Reduction (e_app  ( (e_cast (c_arrow c1 c2) e1) )  e2) (e_cast c2  ( (e_app e1  ( (e_cast  (rev_cast  c1 )  e2) ) ) ) )
 | Red_cast : forall (c:castop) (e e':exp),
     lc_castop c ->
     Reduction e e' ->
     Reduction (e_cast c e) (e_cast c e')
 | Red_castelim : forall (c1 c2:castop) (v:exp),
     DualCast c1 c2 ->
     value v ->
     Reduction (e_cast c1  ( (e_cast c2 v) ) ) v
 | Red_castid : forall (v:exp),
     value v ->
     Reduction (e_cast c_id v) v.


(** infrastructure *)
#[export] Hint Constructors WFT WFTyE ordinary TypCast WFTmE Typing value DualCast Reduction lc_typ lc_castop lc_exp : core.

