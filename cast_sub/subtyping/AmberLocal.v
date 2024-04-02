Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export Rules.
Require Export Infra.
Require Export AmberBase.
Require Import Lia.

Inductive WFC :  typ -> nat -> Prop :=
| WC_nat: forall k,
    WFC typ_nat k
| WF_top: forall k,
    WFC typ_top k
| WF_fvar: forall X k,
    WFC (typ_fvar X) k
| WF_bvar: forall b k,
    b < k ->
    WFC (typ_bvar b) k
| WF_arrow: forall A B k,
    WFC A k ->
    WFC B k ->
    WFC (typ_arrow A B) k
| WF_rec: forall A n,
    WFC A (S n) ->
    WFC (typ_mu A) n
.

#[global] Hint Constructors WFC : core.


Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top              
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => if X == Z then typ_bvar K else typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_mu T        => typ_mu (close_tt_rec (S K) Z T)
  end.

Definition close_tt T X := close_tt_rec 0 X T.

Lemma close_wfc : forall A X,
    WFC A 0 ->
    WFC (close_tt A X) 1.
Proof with auto.  
  intros A.
  unfold close_tt.
  generalize 0.
  induction A;intros;try solve [dependent destruction H;simpl in *;auto]...
  -
    simpl...
    destruct (a==X)...
Qed.


Lemma open_wfc : forall A (X:atom),
    WFC A 1 -> 
    WFC (open_tt A X) 0.
Proof with auto.  
  intros A.
  unfold open_tt.
  generalize 0.
  induction A;intros;try solve [dependent destruction H;simpl in *;auto]...
  -
    simpl...
    destruct (n0==n)...
    inversion H;subst. constructor. lia.
Qed.

Lemma WFC_add_one : forall A k,
    WFC A k -> WFC A (S k).
Proof with auto.
  intros.
  induction H...
Qed.


Lemma close_open_reverse_rec: forall T X,
    (X \notin fv_tt T) -> forall k, T = close_tt_rec k X (open_tt_rec k (typ_fvar X) T).
Proof with auto.
  intros T.
  induction T;intros;simpl in *;try solve [f_equal;auto]...
  -   
    destruct (k==n)...
    simpl...
    destruct (X==X)...
    destruct n0...
  -
    destruct (a==X)...
    apply notin_singleton_1 in H...
    destruct H...
Qed.

Lemma close_open_reverse: forall T X,
    (X \notin fv_tt T) ->  T = close_tt (open_tt T (typ_fvar X)) X.
Proof with auto.
  intros.
  apply close_open_reverse_rec...
Qed.

Lemma close_type_wfc: forall A,
    type A -> WFC A 0.
Proof with auto.
  intros.
  induction H;intros...
  constructor...
  (* apply WFC_add_one. *)
  pick fresh X.
  specialize_x_and_L X L.
  apply close_wfc with (X:=X) in H0.
  rewrite <- close_open_reverse in H0...
Qed.


Fixpoint weight (T:typ) : nat :=
  match T with
  | typ_nat => 1
  | typ_top => 1
  | typ_fvar _ => 1
  | typ_bvar _ => 1
  | typ_arrow A B => 1 + weight A + weight B
  | typ_mu A => 1 + weight A
  end.

Lemma open_tt_weight: forall T (X:atom),
    weight (open_tt T X) = weight T.
Proof with auto.  
  intros. unfold open_tt. generalize 0.
  induction T;intros;simpl in *;try solve [auto]...
  -
    destruct (n0==n)...
Qed.


Lemma type_wfc_close_aux: forall k A,
  weight A <= k ->
  WFC A 0 -> type A.
Proof with auto.
  induction k.
  { intros. destruct A; simpl in H;lia. }
  intros.
  inversion H0;subst...
  - exfalso. lia.
  - simpl in H. 
    apply IHk in H1;try lia...
    apply IHk in H2;try lia...
  - simpl in H.
    apply type_mu with (L:={}).
    intros.
    apply IHk...
    2:{ apply open_wfc... }
    rewrite open_tt_weight...
    lia.
Qed.

Lemma type_wfc_close: forall A,
  WFC A 0 -> type A.
Proof with auto.
  intros.
  apply type_wfc_close_aux with (k:=weight A)...
Qed.





Lemma type_open_tt_WFC :forall T X,
    X \notin fv_tt T ->
    type (open_tt T X) ->
    WFC T 1.
Proof with auto.
  intros.
  apply close_type_wfc in H0.
  apply close_wfc with (X:=X) in H0...
  rewrite <- close_open_reverse in H0...
Qed.

