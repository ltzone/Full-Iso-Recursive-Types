Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.
Require Import Relation_Operators.
Require Import Operators_Properties.

Require Export subtheorems.



(* Type safety of Full Iso-Recursive Types *)

Theorem progress: forall e t, Typing nil nil nil e t -> 
  (value e) \/ exists e', Reduction e e'.
Proof.
  apply progress.
Qed.

Theorem preservation: forall e T,
  Typing nil nil nil e T -> forall e', 
  Reduction e e' -> Typing nil nil nil e' T.
Proof.
  apply preservation.
Qed.


(*************************************************************************************************************************)
(* Soundness and Completeness of TypCast *)



Theorem TypCast_soundness: forall D A B c, 
  TypCast D nil A B c ->
  Tyeq A B.
Proof with auto.
  intros.
  apply soundness with (A:=to_assump nil)...
  { intros. simpl in H0. inv H0. }
  eapply soundness_eqe;eassumption.
Qed.



Lemma binds_lookup2: forall (A:Type) (a: A) (E: list (atom * A))
  (HA: forall (a1 a2:A), {eq a1 a2} + {a1 <> a2}),
  { x : atom | binds x a E } + (forall x, ~ binds x a E ).
Proof with auto.
  intros.
  induction E.
  - right. introv C. inv C.
  - destruct a0. destruct (HA a a1).
    + left. exists a0. left. subst. reflexivity.
    + destruct IHE as [[s' ?] | ?].
      * left. exists s'. right. apply b.
      * right. introv C. destruct C.
        { inv H. apply n. reflexivity. }
        { apply n0 with (x:=x). apply H. }
Qed.






Theorem TypCast_completeness: forall D A B, 
  WFTyE D ->
  WFT D A -> WFT D B ->
  Tyeq A B ->
  exists c, TypCast D nil A B c.
Proof with auto.
  intros.
  eapply completeness_eqe with (G:=nil)...
Admitted.




(*************************************************************************************************************************)
(* Typing Equivalence to the equi-recursive type system *)

(* Lemma AmberSub_e2i: forall D G A B e e',
  ACSubtyping nil A B ->
  EquiTyping D G e A ->
  erase e' = e ->
  Typing D nil G e' A ->
  exists e'', 
    Typing D nil G e'' B /\
    erase e' = e.
Proof with auto.
  intros.
  inductions H.
  + exists (erase ) *)



Theorem typing_i2e: forall D G e t, Typing D nil G e t -> EquiTyping D G (erase e) t.
Proof with auto.
  intros.
  dependent induction H; simpls...
  - 
    apply ETyping_abs with (L:=L)...
    intros. specialize_x_and_L x L. rewrite erase_open_ee in H0...
  -
    apply ETyping_app with (A1:=A1)...
  -
    apply ETyping_fix with (L:=L)...
    intros. specialize_x_and_L x L. rewrite erase_open_ee in H0...
  -
    apply ETyping_sub with (A:=A)...
    apply TypCast_soundness in H0...
  -
    apply ETyping_sub with (A:=A)...
    apply AmberSub_i2e...
Qed.


Lemma WFT_Tyeq: forall D A B, WFT D A -> Tyeq A B -> WFT D B.
(* needs to be proved *)
Admitted.


Inductive eqea : list (typ * typ) -> typ -> typ -> Prop :=
| ea_assump1: forall E t1 t2,
    In (t1,t2) E ->
    eqea E t1 t2
| ea_refl: forall E t, eqea E t t
| ea_fld: forall E t s, 
  eqea E (unfold_mu t) s ->
  eqea E (t_mu t) s
| ea_unfld: forall E t s, 
    eqea E s (unfold_mu t)  ->
    eqea E s (t_mu t) 
| ea_arrfix: forall E t1 t2 t1' t2',
    eqea ((t_arrow t1 t2, t_arrow t1' t2'):: E) t1 t1' -> 
    eqea ((t_arrow t1 t2, t_arrow t1' t2'):: E) t2 t2' ->
    eqea E (t_arrow t1 t2) (t_arrow t1' t2')
.

#[global]
Hint Constructors eqea : core.




Lemma eqec_TypCast: forall E D A B c,
WFT E A -> WFT E B -> uniq D ->
eqec D A B c -> TypCast E D A B c.
Proof with auto.
introv HwfA HwfB Hwfe H.
inductions H;intros...
- assert (WFT E B) by admit.
  apply TCast_seq with (B:=B)...
- inv HwfA. inv HwfB...
- inv HwfA. inv HwfB...
  apply TCast_fix with (L:=L \u dom E0  )...
Admitted.


Lemma eqec_symm: forall A B c,
  eqec nil A B c -> eqec nil B A (rev_cast c).
Admitted.



(* 

Fixpoint typsubst_env (X:atom) (A1 A2:typ) (E: cctx):=
  match E with
  | nil => nil
  | (Y, (A,B)) :: E' => (Y, (typsubst_typ A1 X A, typsubst_typ A2 X B))::(typsubst_env X A1 A2 E')
  end.


Lemma eqec_narrowing: forall E1 E2 E T1 T2 c,
    eqec (E1 ++ E2) T1 T2 c ->
    uniq (E1 ++ E ++ E2) -> eqec (E1 ++ E ++ E2) T1 T2 c.
Admitted.

Lemma eqec_typsubst_refl: forall D A A' B' X c', lc_typ A ->
  X `notin` typefv_typ A' \u typefv_typ B' ->
  eqec nil  A' B' c' ->
  exists  c', eqec (typsubst_env  X A' B' D) (typsubst_typ A' X A) (typsubst_typ B' X A) c'.
Proof with auto.
  intros. gen A' B' c'.
  inductions H;intros;simpl;try solve[exists c_id;auto]...
  - simpl. destruct (X0 == X)...
    + exists c'. rewrite_env (nil ++ (typsubst_env X A' B' D) ++ nil)...
      apply eqec_narrowing... admit.
    + exists c_id. constructor...
  - forwards (c1' &?): IHlc_typ1 H2...
    forwards (c2' &?): IHlc_typ2 H2...
    exists (c_arrow c1' c2')...
  - 
    (* destruct (H0 X) as [c1' ?]... *)
    exists (c_seq (c_seq (c_unfold (t_mu (typsubst_typ A' X A))) c') (c_fold (t_mu (typsubst_typ B' X A))))...
    eapply ec_trans. 2:{ constructor. admit. }
    eapply ec_trans. { constructor. admit. }
    replace (unfold_mu (typsubst_typ A' X A)) with
    (open_typ_wrt_typ  (typsubst_typ A' X A)( (typsubst_typ A' X (t_mu A))) )...
    rewrite <- typsubst_typ_open_typ_wrt_typ...
    replace (unfold_mu (typsubst_typ B' X A)) with
    (open_typ_wrt_typ  (typsubst_typ B' X A)( (typsubst_typ B' X (t_mu A))) )...
    rewrite <- typsubst_typ_open_typ_wrt_typ...
Admitted.


Lemma eqec_typsubst: forall D A B A' B' X c c',
  X `notin` typefv_typ A' \u typefv_typ B' ->
  eqec D A B c ->
  eqec nil  A' B' c' ->
  exists  c', eqec (typsubst_env  X A' B' D) (typsubst_typ A' X A) (typsubst_typ B' X B) c'.
Proof with auto.
  intros. gen A' B' c'.
  inductions H0;intros...
  -
    exists (c_var_f cx). constructor.
    admit.
  - eapply eqec_typsubst_refl;eassumption.
  - forwards (c1'&?): IHeqec1 H1...
    assert (eqec nil B' B' c_id). { constructor... admit. }
    forwards (c2'&?): IHeqec2 H2...
    exists (c_seq c1' c2')...
Admitted. *)


(* 


Lemma eqec_open_mu: forall A B X c,
  X `notin` typefv_typ A \u typefv_typ B ->
  eqec nil (open_typ_wrt_typ A (t_var_f X)) (open_typ_wrt_typ B (t_var_f X)) c ->
  exists c', eqec nil (t_mu A) (t_mu B) c'.
Proof with auto.
  intros.
  inductions H0.
  - inv H0.
  - forwards: open_typ_wrt_typ_inj x...
    subst. exists c_id...
    constructor... admit.
  - forwards(c1'&?): IHeqec1 X (close_typ_wrt_typ X B0) A...
    { rewrite typefv_typ_close_typ_wrt_typ... }
    { rewrite open_typ_wrt_typ_close_typ_wrt_typ... }
    forwards(c2'&?): IHeqec2 X B (close_typ_wrt_typ X B0)...
    { rewrite typefv_typ_close_typ_wrt_typ... }
    { rewrite open_typ_wrt_typ_close_typ_wrt_typ... }
    exists (c_seq c1' c2')...
    applys ec_trans H0 H1.
  - destruct A; inv x0.
    { unfold open_typ_wrt_typ in x0. simpl in x0.
      destruct (lt_eq_lt_dec n 0);inv x0. destruct s;inv x0. }
    exists (c_unfold (t_mu (t_mu A))).
    replace (t_mu B) with (unfold_mu (t_mu A)). constructor... admit.
    unfold unfold_mu.
    cbn [open_typ_wrt_typ_rec]. f_equal.
    apply open_typ_wrt_typ_inj with (X1:=X)...
    { rewrite typefv_typ_open_typ_wrt_typ_rec_upper_mutual... }
    rewrite <- x. unfold unfold_mu.
    Search open_typ_wrt_typ_rec.
    
    
    Search open_typ_wrt_typ t_var_f.
    cbv [open_typ_wrt_typ_rec]. f_equal.
    simpl. f_equal.
    unfold unfold_mu in x.
    replace (unfold_mu (open_typ_wrt_typ_rec 1 (t_var_f X) A))
    with (open_typ_wrt_typ (t_mu A) (t_var_f X)) in x...
    2:{
    (* unfold unfold_mu.   *)
    rewrite open_typ_wrt_typ_lc_typ with (A1:=(t_mu (open_typ_wrt_typ_rec 1 (t_var_f X) A)))
    (A2:= (open_typ_wrt_typ_rec 1 (t_var_f X) A))...
      
    unfold open_typ_wrt_typ in *. 
        rewrite <- x0. 
        rewrite open_typ_wrt_typ_lc_typ with 
          (A1:=t_mu (open_typ_wrt_typ_rec 1 (t_var_f X) A))
          (A2:= )). Search lc_typ open_typ_wrt_typ.
    rewrite x0.  }
     *)


(* Instead of directly proving the congruence lemma on eqe/eqec

We can prove this lemma on the Tyeq relation, and then use the 
soundness and completeness of TypCast to lift the result to eqe/eqec

*)

Lemma Tyeq_subst: forall A B C D X, lc_typ C -> lc_typ D -> Tyeq C D ->
  Tyeq A B -> Tyeq (typsubst_typ C X A) (typsubst_typ D X B).
Proof.
  cofix IH.
  introv Hc Hd H H0. inv H0.
  - simpl. apply Tyeq_arrow.
    + applys IH H;try assumption.
    + applys IH H;try assumption.
  - simpl. rewrite typsubst_typ_open_typ_wrt_typ. 2:{ auto. }
    simpl.
    eapply Tyeq_trans.
    { apply Tyeq_mu_l. }
    rewrite <- !typsubst_typ_open_typ_wrt_typ with (A2:=t_mu t). 2:{ auto. } 2:{ auto. }
    applys IH H;try assumption. apply Tyeq_refl.
  - simpl. rewrite typsubst_typ_open_typ_wrt_typ. 2:{ auto. }
    simpl.
    eapply Tyeq_trans.
    2:{ apply Tyeq_mu_r. }
    rewrite <- !typsubst_typ_open_typ_wrt_typ with (A2:=t_mu t). 2:{ auto. } 2:{ auto. }
    applys IH H;try assumption. apply Tyeq_refl.
  - eapply Tyeq_trans.
    2:{ apply IH. apply Hc. apply Hd. assumption. eassumption. } 
    apply Tyeq_refl.
  - eapply Tyeq_trans.
    2:{ apply IH.  apply Hc. apply Hd. assumption. eassumption. } 
    apply IH;try assumption. apply Tyeq_refl.
Qed.



(* Lemma Tyeq_mu_cong: forall A B X, lc_typ A -> lc_typ B -> Tyeq A B ->
  Tyeq (t_mu (close_typ_wrt_typ X A)) (t_mu (close_typ_wrt_typ X B)).
Proof.
  cofix IH.
  intros. 
  eapply Tyeq_trans.
  { apply Tyeq_mu_l. }
  eapply Tyeq_trans.
  2:{ apply Tyeq_mu_r. }
  rewrite <- !typsubst_typ_spec.
  apply Tyeq_subst;try apply H1.
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  eapply Tyeq_trans. { apply Tyeq_refl. }
  { apply IH;[..|apply H1]. auto. auto. } Guarded. apply Tyeq_refl.
Qed. *)



Module Tyeq_subst.


CoInductive Tyeq': typ -> typ -> Prop :=
| Tyeq_arrow : forall t1 t1' t2 t2' : typ,
Tyeq' t1 t1' ->
Tyeq' t2 t2' -> 
Tyeq' (t_arrow t1 t2) (t_arrow t1' t2')
| Tyeq_mu_l : forall t : typ, Tyeq' (t_mu t) (unfold_mu t)
| Tyeq_mu_r : forall t : typ, Tyeq' (unfold_mu t) (t_mu t)
| Tyeq_refl : forall t : typ, Tyeq' t t
| Tyeq_trans : forall t1 t2 t3 : typ,
Tyeq' t1 t2 -> Tyeq' t2 t3 -> Tyeq' t1 t3
| Tyeq_subst : forall t1 t2 t1' t2' X,
lc_typ t1' -> lc_typ t2' ->
Tyeq' t1' t2' ->
Tyeq' t1 t2 ->
Tyeq' (typsubst_typ t1' X t1) (typsubst_typ t2' X t2)
.



(* make typsubst_Tyeq an inductive constructor of the coinductive relation *)
Inductive WHNF_eqWi (R: typ -> typ -> Prop): typ -> typ -> Prop :=
| wh_done: forall t1 t2, Tyeq t1 t2 -> WHNF_eqWi R t1 t2
| wh_arrow: forall  t1 t2 t1' t2',
    R t1 t1' -> (* coinductive WHNF_eqP *)
    R t2 t2' ->
    WHNF_eqWi R (t_arrow t1 t2) (t_arrow t1' t2')
| wh_trans: forall  t1 t2 t3, 
    R  t1 t2 ->
    R t2 t3 ->
    WHNF_eqWi R t1 t3
| wh_subst: forall t1 t2 t1' t2' X,
    lc_typ t1' -> lc_typ t2' ->
    R t1' t2' ->
    R t1 t2 ->
    WHNF_eqWi R (typsubst_typ t1' X t1) (typsubst_typ t2' X t2)
| wh_unfold: forall t1 t2,
    R (unfold_mu t1) (unfold_mu t2) ->
    WHNF_eqWi R (t_mu t1) (t_mu t2)
| wh_mu_cong: forall t1 t2 X,
    lc_typ t1 -> lc_typ t2 -> 
    R t1 t2 -> 
    R (t_mu (close_typ_wrt_typ X t1)) (t_mu (close_typ_wrt_typ X t2)) ->
    WHNF_eqWi R (t_mu (close_typ_wrt_typ X t1)) (t_mu (close_typ_wrt_typ X t2))
.

#[export]
Hint Constructors WHNF_eqWi : core.

(* 

Inductive WHNF_eqWii (R: typ -> typ -> Prop): typ -> typ -> Prop :=
| whi_done: forall t1 t2, WHNF_eqW t1 t2 -> WHNF_eqWii R t1 t2 *)
(* | wh_arrow: forall  t1 t2 t1' t2',
    R t1 t1' -> (* coinductive WHNF_eqP *)
    R t2 t2' ->
    WHNF_eqWi R (t_arrow t1 t2) (t_arrow t1' t2')
| wh_trans: forall  t1 t2 t3, 
    R  t1 t2 ->
    R t2 t3 ->
    WHNF_eqWi R t1 t3
| wh_subst: forall t1 t2 t1' t2' X,
    lc_typ t1' -> lc_typ t2' ->
    R t1' t2' ->
    R t1 t2 ->
    WHNF_eqWi R (typsubst_typ t1' X t1) (typsubst_typ t2' X t2)
| wh_unfold: forall t1 t2,
    R (unfold_mu t1) (unfold_mu t2) ->
    WHNF_eqWi R (t_mu t1) (t_mu t2)
| wh_mu_cong: forall t1 t2 X,
    lc_typ t1 -> lc_typ t2 -> 
    R t1 t2 -> R (t_mu (close_typ_wrt_typ X t1)) (t_mu (close_typ_wrt_typ X t2)) ->
    WHNF_eqWi R (t_mu (close_typ_wrt_typ X t1)) (t_mu (close_typ_wrt_typ X t2)) *)


(* #[export]
Hint Constructors WHNF_eqWii : core. *)



CoInductive WHNF_eqW : typ -> typ -> Prop :=
| wh_introw: forall (R: typ -> typ -> Prop),
    (forall t1 t2, R t1 t2 -> R t2 t1) ->
    (* (forall t1 t2 X,  *)
      (* R t1 t2 -> *)
       (* R (t_mu (close_typ_wrt_typ X t1)) (t_mu (close_typ_wrt_typ X t2)) ->  *)
      (* lc_typ t1 /\ lc_typ t2 /\ *)
    (* WHNF_eqW (t_mu (close_typ_wrt_typ X t1)) (t_mu (close_typ_wrt_typ X t2))) -> *)
      (* ((forall t1' t2' X, Tyeq t1' t2' ->  *)
           (* Tyeq (t_mu (close_typ_wrt_typ X t1')) (t_mu (close_typ_wrt_typ X t2'))) -> *)
           (* ) /\ *)
           (* Tyeq t1 t2) -> *)
           (* Tyeq t1 t2) -> *)
    (forall t1 t2, R t1 t2 -> 
          Tyeq' t1 t2) ->
    (* (forall t1 t2, R t1 t2 -> 
          Tyeq t1 t2) -> *)
    forall t1 t2,
      WHNF_eqWi R t1 t2 ->
      WHNF_eqW t1 t2
.


(* Lemma Tyeq_eqW: forall t1 t2,
  Tyeq t1 t2 -> WHNF_eqW t1 t2.
Proof with auto.
  intros.
  apply (wh_introw (fun _ _ => False)).
  { intros. destruct H0. }
  { intros. destruct H0. }
  (* { intros. destruct H0. } *)
  apply wh_done...
Qed.  *)

Lemma WNNF_eqW_symm: forall t1 t2,
  WHNF_eqW t1 t2 -> WHNF_eqW t2 t1.
Admitted.




Lemma eqW_Tyeq: forall t1 t2,
  WHNF_eqW t1 t2 -> Tyeq t1 t2.
Proof with auto.
  intros.
  inv H.
  inv H2.
  - exact H3.
  - apply syntax_ott.Tyeq_arrow.
    +  apply H2...
    +  apply H2...
  - eapply syntax_ott.Tyeq_trans with (t2:=t3)...
    (* + apply H1...
    + apply H1... *)
  - apply theorems.Tyeq_subst;try assumption...
  - apply syntax_ott.Tyeq_trans with (t2:=unfold_mu t0)...
    apply syntax_ott.Tyeq_trans with (t2:=unfold_mu t3)...
    (* apply H1... *)
  -
    eapply syntax_ott.Tyeq_trans.
    { apply syntax_ott.Tyeq_mu_l. }
    eapply syntax_ott.Tyeq_trans.
    2:{ apply syntax_ott.Tyeq_mu_r. }
    rewrite <- !typsubst_typ_spec.
    apply theorems.Tyeq_subst. 

    { apply lc_t_mu_exists with (X1:=X)...
      rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
    { apply lc_t_mu_exists with (X1:=X)...
      rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
    apply H2...
    apply H2...
Qed.

Lemma Tyeq'_symm: forall t1 t2,
  Tyeq' t1 t2 -> Tyeq' t2 t1.
Admitted.

Lemma Tyeq'_eqW: forall t1 t2,
  Tyeq' t1 t2 -> WHNF_eqW t1 t2.
Proof with auto.
  intros.
  pose proof (wh_introw Tyeq' Tyeq'_symm) as rule.
  inv H.
  - apply rule...
    { intros.  }
    apply wh_done.




Lemma eqW_cong_mu: forall A B X, lc_typ A -> lc_typ B -> 
  Tyeq A B ->
  (* Tyeq (t_mu (close_typ_wrt_typ X A)) (t_mu (close_typ_wrt_typ X B)) -> *)
  WHNF_eqW (t_mu (close_typ_wrt_typ X A)) (t_mu (close_typ_wrt_typ X B)).
Proof with auto.
  intros.
  cofix proof.
  (* WHNF_eqW itself cannot be used to instantiate *)
  (* pose proof (wh_introw WHNF_eqW WNNF_eqW_symm eqW_Tyeq) as rule. *)
  pose proof (wh_introw Tyeq) as rule.
  (* pose proof (wh2_introw WHNF_eqW) as rule2. *)
  apply rule.
  { apply Tyeq_symm. }
  (* { apply WNNF_eqW_symm. } *)
  { intros. auto. }
  
  (* { apply eqW_Tyeq. } *)
  apply wh_mu_cong...
Qed.



Lemma eqW_cong_mu_final: forall A B X, lc_typ A -> lc_typ B -> 
  WHNF_eqW A B ->
  WHNF_eqW (t_mu (close_typ_wrt_typ X A)) (t_mu (close_typ_wrt_typ X B)).
Proof with auto.
  intros.
  cofix IH.
  pose proof (wh_introw Tyeq Tyeq_symm) as rule.
  inv H1. inv H4.
  - apply eqW_cong_mu...



Qed.



  apply eqW_Tyeq. auto.

  rewrite <- !typsubst_typ_spec.
  apply rule. { auto. }







Lemma eqW_cong_mu: forall A B X, lc_typ A -> lc_typ B -> 
  WHNF_eqW A B ->
  WHNF_eqW (unfold_mu (close_typ_wrt_typ X A)) (unfold_mu (close_typ_wrt_typ X B)).
Proof with auto.
  intros.
  (* WHNF_eqW itself cannot be used to instantiate *)
  (* pose proof (wh_introw WHNF_eqW WNNF_eqW_symm eqW_Tyeq) as rule. *)
  pose proof (wh_introw Tyeq Tyeq_symm) as rule.
  cofix proof.
  apply wh_mu_cong.
  rewrite <- !typsubst_typ_spec.
  apply rule. { auto. }

  



  apply wh_subst.
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  { eapply Tyeq_trans.
    { apply Tyeq_mu_l. }
    eapply Tyeq_trans.
    2:{ apply Tyeq_mu_r. }
    apply eqW_Tyeq. apply proof. Guarded.
    
    apply rule.
    apply wh_unfold. apply proof. }
  apply H1.
Qed.


  }


  apply Tyeq_subst;try apply H1.
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  inv H1.
  - apply rule...
    apply Tyeq_arrow...
    + apply H1...
    + apply H




Lemma interp_W: forall t1 t2, WHNF_eqW t1 t2 -> Tyeq t1 t2.
Proof with auto.
  (* cofix IH.
  intros. inv H. inv H2.
  - apply H3.
  - apply Tyeq_arrow...
    + apply IH. apply H1...
    + apply IH. apply H1...
  - apply Tyeq_trans with (t2:=t3)...
    (* + apply IH. apply H1...
    + apply IH. apply H1... *)
  - apply Tyeq_subst;try assumption.
Qed. *)
Admitted.


Lemma done_aux: forall R t1 t2, Tyeq t1 t2 -> WHNF_eqWi R t1 t2.
Proof.
  intros.
  apply wh_done. exact H.
Qed.


Lemma Tyeq_mu_cong: forall A B X, lc_typ A -> lc_typ B -> Tyeq A B ->
  Tyeq (t_mu (close_typ_wrt_typ X A)) (t_mu (close_typ_wrt_typ X B)).
Proof.
  intros.
  pose proof (wh_introw Tyeq Tyeq_symm) as rule.



  eapply Tyeq_trans.
  { apply Tyeq_mu_l. }
  eapply Tyeq_trans.
  2:{ apply Tyeq_mu_r. }
  rewrite <- !typsubst_typ_spec.
  apply Tyeq_subst;try apply H1.
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  apply interp_W.
  apply wh_introw with (R:=fun t1 t2 => False).
  - intros. inv H2.
  - intros. inv H2.
  - apply done_aux. 

  cofix IH.
  intros. 
  eapply Tyeq_trans.
  { apply Tyeq_mu_l. }
  eapply Tyeq_trans.
  2:{ apply Tyeq_mu_r. }
  rewrite <- !typsubst_typ_spec.
  apply Tyeq_subst;try apply H1.
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  { apply lc_t_mu_exists with (X1:=X)...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ;auto. }
  apply IH;assumption. 
Admitted.
End Tyeq_subst.



Lemma TypCast_eqec: forall E D A B c,
  WFTyE D -> WFT D A -> WFT D B ->
  TypCast D E A B c ->
  eqec E A B c.
Admitted.



Lemma eqec_mu_cong: forall D A B X c,
  WFTyE D -> WFT D A -> WFT D B ->
  eqec nil A B c ->
  exists c', eqec nil (t_mu (close_typ_wrt_typ X A)) (t_mu (close_typ_wrt_typ X B)) c'.
Proof with auto.
  introv Hwf Hwfa Hwfn Heq.
  apply eqec_TypCast with (E:=D) in Heq...
  apply TypCast_soundness in Heq.
  apply Tyeq_subst.Tyeq_mu_cong with (X:=X) in Heq...
  forwards (c'&?): TypCast_completeness Hwf Heq...
  { admit. } { admit. }
  apply TypCast_eqec in H...
  2:{ admit. } 2:{ admit. }
  exists c'...
Admitted.


Lemma Asub_AAsub: forall D A B,
  ACSubtyping D A B -> exists A' B' c1 c2,
  AmberSubtyping D A' B' /\ eqec nil A A' c1 /\ eqec nil B' B c2.
Proof with auto.
  intros.
  inductions H...
  - exists A, t_top, c_id, c_id.
    repeat split...
    + apply ASub_top... admit. admit.
  - exists A, A, c_id, c_id.
    repeat split...
    + apply ASub_refl. admit. admit.
  - forwards (A'&B'&c1&c2&?&?&?): IHACSubtyping1.
    forwards (B''&C'&c1'&c2'&?&?&?): IHACSubtyping2.
    forwards: ec_trans H3 H5.
    forwards: eqec_TypCast (@nil (atom * unit)) H7... admit. admit.
    forwards: TypCast_soundness H8.
    assert (Tyeq' B' B'') by admit.
    forwards (A'_ & C'_ & ? &? & ? ): sub_eq_commutes H1 H10 H4.
    exists A'_ C'_.
    admit. (* need completeness back *)
  - exists (t_var_f X) (t_var_f Y) c_id c_id.
    repeat split...
    + apply ASub_var... admit. admit.
  - 
    forwards (c&?): TypCast_completeness (@nil (atom * unit)) H...
    admit. admit.
    exists B B c c_id.
    repeat split... 3:{ constructor... admit. }
    admit. admit.
  -
    forwards (A1'&A2'&c1a&c2a&?&?&?): IHACSubtyping1.
    forwards (B1'&B2'&c1b&c2b&?&?&?): IHACSubtyping2.
    exists (t_arrow A2' B1') (t_arrow A1' B2') 
      (c_arrow (rev_cast c2a) c1b) (c_arrow (rev_cast c1a) c2b).
    repeat split;
    auto using eqec_symm.
  -
    pick_fresh X. pick_fresh Y.
    specialize_x_and_L X L.
    specialize_x_and_L Y (union L (singleton X)).
    destruct H0 as (A' & B' & c1 & c2 & Hsub & Hc1 & Hc2).
    exists (t_mu (close_typ_wrt_typ Y A')) (t_mu (close_typ_wrt_typ X B')).
    forwards (c1' & ?): eqec_mu_cong (@nil (atom*unit)) Y Hc1...
    { admit. } { admit. }
    forwards (c2' & ?): eqec_mu_cong (@nil (atom*unit)) X Hc2...
    { admit. } { admit. }
    rewrite close_typ_wrt_typ_open_typ_wrt_typ in H0...
    rewrite close_typ_wrt_typ_open_typ_wrt_typ in H1...
    exists c1', c2'. repeat split...
    + apply ASub_rec with (L:=L)... intros.
      rewrite <- typsubst_typ_spec...
      rewrite <- typsubst_typ_spec...
      admit.
      (* subsitution lemma *)
Admitted.






Theorem typing_e2i: forall D G e t, EquiTyping D G e t -> exists e', Typing D nil G e' t /\ erase e' = e.
(* depends on completeness and WFT_Tyeq *)
Proof with auto.
  intros.
  dependent induction H; simpls...
  -
    exists (e_lit i). split...
  -
    exists (e_var_f x). split...
  -
    pick_fresh x. specialize_x_and_L x L.
    destruct H0 as [e' [Hty He]].
    exists (e_abs A1 (close_exp_wrt_exp x e')). split...
    +
      apply Typing_abs with (L:=L \u dom G \u {{x}})...
      intros. rewrite <- subst_exp_spec.
      rewrite_alist (nil ++ (x0 ~ A1 ++ G)).
      apply typing_through_subst_ee with (U:=A1). 
      2:{ get_WFT... inv H2. apply Typing_var... constructor... }
      rewrite_alist (x ~ A1 ++ x0 ~ A1 ++ G). apply Typing_weakening...
      { get_WFT. inv H2. constructor... constructor... }
    +
      simpl. rewrite erase_close_ee.
      rewrite He. rewrite close_exp_wrt_exp_open_exp_wrt_exp...
  -
    destruct IHEquiTyping1 as [e1' [Hty1 He1]].
    destruct IHEquiTyping2 as [e2' [Hty2 He2]].
    exists (e_app e1' e2'). split;simpl;try congruence.
    apply Typing_app with (A1:=A1)...
  -
    pick_fresh x. specialize_x_and_L x L.
    destruct H0 as [e' [Hty He]].
    exists (e_fixpoint A (close_exp_wrt_exp x e')). split...
    +
      apply Typing_fix with (L:=L \u dom G \u {{x}})...
      intros. rewrite <- subst_exp_spec.
      rewrite_alist (nil ++ (x0 ~ A ++ G)).
      apply typing_through_subst_ee with (U:=A). 
      2:{ get_WFT... inv H2. apply Typing_var... constructor... }
      rewrite_alist (x ~ A ++ x0 ~ A ++ G). apply Typing_weakening...
      { get_WFT. inv H2. constructor... constructor... }
    +
      simpl. rewrite erase_close_ee.
      rewrite He. rewrite close_exp_wrt_exp_open_exp_wrt_exp...
  -
    destruct IHEquiTyping as [e' [Hty He]].
    forwards (A' & B' & c1 & c2 & ? & ? & ?): Asub_AAsub H0.
    exists (e_cast c2 (e_cast c1 e')). split...
    applys Typing_cast. 2:{ applys eqec_TypCast H3... admit. admit. }
    applys Typing_sub H1.
    applys Typing_cast Hty. { applys eqec_TypCast H2... admit. }
    (* need wf condition *)
Admitted.


(*************************************************************************************************************************)
(* Semantic Equivalence to the equi-recursive type system *)


(* From Iso to Equi, actually we do not even need the Iso terms to be well typed *)
Theorem reduction_i2e: forall e1 e2,
  Reduction e1 e2 ->
  (erase e1) ==>* (erase e2).
Proof with auto.
  apply soundness_erase.
Qed.




(*************************************************************************************************************************)
(* To prove reduction_e2i, we define a new Equi Typing relation, that annotate equi-typing judgements with the related full iso terms *)



Definition terminate (e:exp) : Prop :=
  exists v, value v /\ e ==>* v.

Lemma terminate_app_inv1: forall A e1 e2,
  Typing nil nil nil (e_app e1 e2) A ->
  terminate (e_app e1 e2) -> terminate e1.
Proof with auto.
  introv Htyp. intros.
  destruct H as [v [Hval Hred]].
  apply clos_rt_rt1n in Hred.
  dependent induction Hred.
  { inv Hval. }
  inv H.
  + exists (e_abs A0 e). split... apply rt_refl.
  + assert (terminate e1').
    { applys* IHHred.
      applys preservation. apply Htyp.
      constructor... }
    destruct H0 as [v' [Hval' Hred']].
    exists v'. split...
    apply rt_trans with (y:=e1')...
    apply rt_step...
  + exists e1. split... apply rt_refl.
  + exists (e_cast (c_arrow c1 c2) e0).
    split... apply rt_refl.
Qed.



Lemma terminate_app_inv2: forall A e1 e2,
  Typing nil nil nil (e_app e1 e2) A ->
  terminate (e_app e1 e2) -> terminate e2.
Proof with auto.
  introv Htyp. intros.
  destruct H as [v [Hval Hred]].
  apply clos_rt_rt1n in Hred.
  dependent induction Hred.
  { inv Hval. }
  inv H.
  + exists e2. split... apply rt_refl.
  + applys* IHHred e1'.
    { applys preservation. apply Htyp.
      constructor... }
  + assert (terminate e2').
    { applys* IHHred.
      applys preservation. apply Htyp.
      constructor... }
    destruct H0 as [v' [Hval' Hred']].
    exists v'. split...
    apply rt_trans with (y:=e2')...
    apply rt_step...
  + exists e2. split... apply rt_refl.
Qed.

Lemma eqec_eqe: forall D A B c,
  eqec D A B c -> eqe (to_assump D) A B.
Proof with auto.
  intros.
  induction H...
  - apply e_assump1. forwards: in_remove_cx H...
  - apply e_trans with (t2:= B)...
  - apply e_arrfix.
    rewrite_alist (nil ++ [(t_arrow A1 B1, t_arrow A2 B2)] ++ to_assump E)...
    apply eqe_weakening...
    rewrite_alist (nil ++ [(t_arrow A1 B1, t_arrow A2 B2)] ++ to_assump E)...
    apply eqe_weakening...
  - pick_fresh cx. specialize_x_and_L cx L.
    simpl in H0, H2.
    apply e_arrfix...
Qed.





Lemma EquiTypingC_sem: forall D G e  t e',
  EquiTypingC D G e  t e' ->
  Typing D nil G e' t /\ EquiTyping D G e t.
Proof with auto.
  introv Typ.
  dependent induction Typ;intros...
  - split...
    + apply Typing_abs with (L:=L).
      intros. apply H0...
    + apply ETyping_abs with (L:=L).
      intros. apply H0...
  - split...
    + destruct_hypos. apply Typing_app with (A1:=A1)...
    + destruct_hypos. apply ETyping_app with (A1:=A1)...
  - split...
    + apply Typing_fix with (L:=L).
      intros. apply H0...
    + apply ETyping_fix with (L:=L).
      intros. apply H0...
  - split...
    + destruct_hypos. apply Typing_cast with (A:=A)...
      forwards* : eqec_TypCast H.
      { admit. }
    + destruct_hypos. 
      (* apply ETyping_sub with (A:=B)...
      2:{ apply ACSub_refl. admit. } *)
      apply ETyping_sub with (A:=A)...
      apply ACSub_eq.
      eapply soundness with (A:=nil). { intros. inv H2. }
      eapply eqec_eqe with (D:=nil);eassumption.
Admitted.





Lemma ECTyping_weakening: forall D G1 G G2 e t e',
  EquiTypingC D (G1 ++ G2) e  t e' ->
  WFTmE D (G1 ++ G ++ G2) ->
  EquiTypingC D (G1 ++ G ++ G2) e t e'.
Proof with auto.
  introv Hty Hwf.
  gen G .
  inductions Hty;intros...
  - apply ECTyping_abs with (L:=L \u dom (G1 ++ G ++ G2))...
    intros. rewrite_alist ((x ~ A1 ++ G1) ++ G ++ G2).
    apply H0...
    rewrite_alist (x ~ A1 ++ G1 ++ G ++ G2).
    constructor... 
    { specialize_x_and_L x L. forwards (?&?): EquiTypingC_sem H.
      get_WFT. inv H4... }
  - apply ECTyping_app with (A1:=A1)...
  - apply ECTyping_fix with (L:=L \u dom (G1 ++ G ++ G2))...
    intros. rewrite_alist ((x ~ A ++ G1) ++ G ++ G2).
    apply H0...
    rewrite_alist (x ~ A ++ G1 ++ G ++ G2).
    constructor... 
    { specialize_x_and_L x L. forwards (?&?): EquiTypingC_sem H.
      get_WFT. inv H4... }
  - apply ECTyping_eq with (A:=A)...
  - apply ECTyping_sub with (A:=A)...
Qed.

Lemma ETyping_regular: forall D G e t,
  EquiTyping D G e t -> WFTmE D G /\ WFT D t /\ lc_exp e.
Proof with auto.
  introv Htyp.
  inductions Htyp...
  - repeat split... applys~ binds_tm_regular x G...
  - pick_fresh x. forwards (?&?&?): H0 x...
    inv H1. repeat split...
    apply lc_e_abs_exists with (x1:=x)...
  - destruct_hypos. inv H3...
  - pick_fresh x. forwards (?&?&?): H0 x...
    inv H1. repeat split...
    apply lc_e_fixpoint_exists with (x1:=x)...
  - destruct_hypos. repeat split...
    (* applys~ WFT_Tyeq D A. *)
    admit.
  (* - destruct_hypos. repeat split...
    applys~ WFT_Tyeq D A. *)
(* Qed. *)
Admitted.


Lemma Red_ctx_cast: forall c e e', lc_castop c ->
  e ==>* e' -> e_cast c e ==>* e_cast c e'.
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0.
  induction H0...
  - apply rt_refl.
  - applys rt_trans IHclos_refl_trans_1n.
    apply rt_step. constructor...
Qed.

Lemma Red_ctx_appl: forall e1 e1' e2, lc_exp e2 ->
  e1 ==>* e1' -> e_app e1 e2 ==>* e_app e1' e2.
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0.
  induction H0...
  - apply rt_refl.
  - applys rt_trans IHclos_refl_trans_1n.
    apply rt_step. constructor...
Qed.

Lemma Red_ctx_appr: forall e1 e2 e2', value e1 ->
  e2 ==>* e2' -> e_app e1 e2 ==>* e_app e1 e2'.
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0.
  induction H0...
  - apply rt_refl.
  - applys rt_trans IHclos_refl_trans_1n.
    apply rt_step. constructor...
Qed.




Lemma subst_castop_eqec:
  forall  (E1 E2 : list (atom * (typ * typ))) 
	(a b c d : typ) (cx : atom) (c1 c2 : castop),
  eqec (E1 ++ cx ~ (a, b) ++ E2) c d c1 ->
  eqec (E1 ++ E2) a b c2 ->
  eqec (E1 ++ E2) c d (castsubst_castop c2 cx c1).
Admitted.


Lemma ECTyping_value: forall e t e',
  EquiTypingC nil nil e t e' -> value e ->
  exists v', e' ==>* v' /\ value v' /\
   EquiTypingC nil nil e t v'. (* <---- This is important! *)
Proof with auto.
  introv Hty Hval.
  inductions Hty...
  - eexists. repeat split.
    + apply rt_refl.
    + constructor...
    + constructor...
  - inv Hval.
  - inv Hval. eexists;repeat split;[apply rt_refl| |].
    + constructor...
      pick_fresh x. specialize_x_and_L x L.
      forwards (?&?): EquiTypingC_sem H.
      get_lc... apply lc_e_abs_exists with (x1:=x)...
    + apply ECTyping_abs with (L:=L)...
  - inv Hval...
  - inv Hval...
  - gen e e'. inductions H;intros.
    + inv H.
    + forwards (v' & ? & ? & ?): IHHty Hval...
      exists v'. split...
      applys rt_trans (e_cast c_id v').
      2:{ apply rt_step. constructor... }
      applys Red_ctx_cast...
    + 
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      forwards (v1 & ? & ? & ?): IHeqec1 Hty1...
      { intros. exists v'... repeat split... apply rt_refl. }
      assert (Hty': EquiTypingC nil nil  e B (e_cast c1 v')).
      { applys ECTyping_eq A... }
      forwards (v2 & ? & ? & ?): IHeqec2 Hty'...
      { intros. exists v1... }
      exists v2. split...
      applys rt_trans (e_cast c2 (e_cast c1 v'))...
      applys rt_trans (e_cast (c_seq c1 c2) v')...
      2:{ apply rt_step. constructor... admit. admit. }
      applys Red_ctx_cast... admit.
    + 
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      forwards (?&?): EquiTypingC_sem Hty1.
      forwards (v''& A' &?): canonical_form_mu H2... subst v'.
      inv H1. exists v''. repeat split...
      * applys rt_trans (e_cast (c_unfold (t_mu A)) (e_cast (c_fold (t_mu A')) v'')).
        { applys Red_ctx_cast... }
        apply rt_step. constructor...
      * clear IHHty H0 H2  H3 Hty. inductions Hty1.
        { inv H0... } 
        { inverts keep H0.
          + eapply ECTyping_sub with (A:=unfold_mu A1).
            2:{ apply unfolding_lemma... }
            eapply IHHty1 with (A'0:=A')...
            { forwards: EquiTypingC_sem Hty1. destruct_hypos.
              get_WFT... }
          + eapply IHHty1 with (A'0:=A')...
        }
    +
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      exists (e_cast (c_fold (t_mu A)) v')...
      repeat split...
      * applys Red_ctx_cast...
      * apply ECTyping_eq with (A:=unfold_mu A)...
    +
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      exists (e_cast (c_arrow c1 c2) v')...
      repeat split...
      * applys Red_ctx_cast... admit.
      * constructor... admit. admit.
      * applys ECTyping_eq Hty1...
    +
      assert (Heqec: 
        eqec nil (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2))).
      { apply ec_arrfix with (L:=L)... }
      forwards (v' & ? & ? & Hty1): IHHty Hval...
      exists (e_cast (c_arrow 
                (open_castop_wrt_castop c1 (c_fixc (c_arrow c1 c2)))
                (open_castop_wrt_castop c2 (c_fixc (c_arrow c1 c2)))) v')...
      repeat split...
      * applys rt_trans (e_cast (c_fixc (c_arrow c1 c2)) v').
        { applys Red_ctx_cast... admit. }
        apply rt_step. constructor... admit.
      * constructor... admit. admit. 
      * apply ECTyping_eq with (A:=t_arrow A1 B1)...
        pick_fresh cx. specialize_x_and_L cx L.
        rewrite castsubst_castop_intro with (cx1:=cx) (c1:=c1)...
        rewrite castsubst_castop_intro with (cx1:=cx) (c1:=c2)...
        replace (   (c_arrow
        (castsubst_castop (c_fixc (c_arrow c1 c2)) cx
           (open_castop_wrt_castop c1 (c_var_f cx)))
        (castsubst_castop (c_fixc (c_arrow c1 c2)) cx
           (open_castop_wrt_castop c2 (c_var_f cx))))) with 
        (castsubst_castop (c_fixc (c_arrow c1 c2)) cx 
            (c_arrow (open_castop_wrt_castop c1 (c_var_f cx))
            (open_castop_wrt_castop c2 (c_var_f cx))))...
        rewrite_alist (@nil (atom * (typ * typ)) ++ nil).
        applys subst_castop_eqec. 2:{ apply Heqec. }
        constructor...
Admitted.





Lemma ECTyping_subst: forall D G1 G2 e1 t e1' e2  A e2' x,
  EquiTypingC D (G1 ++ x ~ A ++ G2) e1 t e1' ->
  EquiTypingC D G2 e2 A e2' ->
  (* EquiTypingC D G2 e2 m2 A e2' -> *)
  EquiTypingC D (G1 ++ G2) (subst_exp e2 x e1) t (subst_exp e2' x e1').
Proof with eauto using WFTmE_strengthening.
  introv Hty1 Hty2.
  gen e2 e2'.
  inductions Hty1;intros;simpl...
  - destruct (x0 == x)...
    + subst. rewrite_alist (nil ++ G1 ++ G2). 
      apply ECTyping_weakening;rewrite app_nil_l...
      analyze_binds_uniq H1... { applys~ WFTmE_uniq... }
      (* inv Hty2... *)
  - apply ECTyping_abs with (L:=L \u dom (G1 ++ G2) \u {{x}})...
    intros. rewrite_alist ((x0 ~ A1 ++ G1) ++ G2).
    rewrite !subst_exp_open_exp_wrt_exp_var... 
    2:{ forwards(?&?): EquiTypingC_sem Hty2. get_lc... }
    2:{ forwards(?&?): EquiTypingC_sem Hty2. apply ETyping_regular in H3. destruct_hypos. get_lc... }
    apply H0 with (A0:=A)...
  - apply ECTyping_fix with (L:=L \u dom (G1 ++ G2) \u {{x}})...
    intros. rewrite_alist ((x0 ~ A0 ++ G1) ++ G2).
    rewrite !subst_exp_open_exp_wrt_exp_var... 
    2:{ forwards(?&?): EquiTypingC_sem Hty2. get_lc... }
    2:{ forwards(?&?): EquiTypingC_sem Hty2. apply ETyping_regular in H3. destruct_hypos. get_lc... }
    apply H0 with (A1:=A)...
Qed.



Lemma value_lc_exp: forall v, value v -> lc_exp v.
Proof with auto.
  introv Hval. inductions Hval...
Qed.


Lemma reduction_app: forall A e1 e1' e2 e2' A1 A2,
EquiTypingC nil nil (e_abs A e1) (t_arrow A1 A2) e1' ->
EquiTypingC nil nil e2 A1 e2' ->
value e1' -> value e2 ->
exists e', (e_app e1' e2') ==>* e' /\ EquiTypingC nil nil (open_exp_wrt_exp e1 e2) A2 e'.
Proof with auto.
  introv Hty1 Hty2 Hval1 Hval2.
  gen e2 e2'. inductions Hty1;intros.
  - 
    clear H0.
    forwards (v2' & Hred2 & Hval2' & Hty2'): ECTyping_value Hty2...
    forwards (Hty2e' & Hty2i'): EquiTypingC_sem Hty2'.
    forwards (Hty2e & Hty2i): EquiTypingC_sem Hty2.
    exists (open_exp_wrt_exp e' v2'). split.
    {
      applys rt_trans (e_app (e_abs A1 e') v2'). 
      { applys Red_ctx_appr... }
      constructor. constructor... { apply value_lc_exp... }
    }
    { pick_fresh X. specialize_x_and_L X L.
      rewrite subst_exp_intro  with (x1:=X) (e1:=e1)...
      rewrite subst_exp_intro  with (x1:=X) (e1:=e')...
      rewrite_alist (@nil (atom * typ) ++ nil ).
      apply ECTyping_subst with (A:=A1)...
    }
  -
    (* assert (exists B1 B2, A0 = t_arrow B1 B2) by admit.
    destruct H0 as [B1 [B2 ?]]. subst. *)
    forwards (v2' & Hred2 & Hval2' & Hty2'): ECTyping_value Hty2...
    forwards (Hty2e' & Hty2i'): EquiTypingC_sem Hty2'.
    forwards (Hty2e & Hty2i): EquiTypingC_sem Hty2.
    inv H; try solve [inv Hval1]. inv Hval1.
    lets: IHHty1 Hval2...
    assert (EquiTypingC nil nil e2 A3 (e_cast (rev_cast c1) v2')). 
    { eapply ECTyping_eq. apply Hty2'. apply eqec_symm in H4... }
    forwards (v'' & Hred' & Hty'): H0 H1...
    exists (e_cast c2 v'').
    split.
    +
      applys rt_trans (e_app (e_cast (c_arrow c1 c2) e') v2').
      { applys Red_ctx_appr... }
      applys rt_trans (e_cast c2 (e_app e' (e_cast (rev_cast c1) v2'))).
      { constructor. constructor... }
      applys Red_ctx_cast...
    +
      eapply ECTyping_eq;eassumption.
  -
    inv H.
    forwards Hty2': ECTyping_sub Hty2 H4.
    forwards (e0 & Hred' & Hty'): IHHty1 A e1 A3 A4 Hty2'...
    exists e0. split*.
Qed.




Theorem reduction_e2i: forall e1 e1' e2 t,
  EquiTypingC nil nil e1 t e1' ->
  Reduction e1 e2 ->
  exists e2', e1' ==>* e2' /\ EquiTypingC nil nil e2 t e2'.
Proof with auto.
  introv Hty Hred.
  gen e1' t. induction Hred;intros; try solve [inductions Hty]...
  -
    inductions Hty.
    + clear IHHty1. clear IHHty2.
      forwards (v1' & Hred1 & Hval1' & Hty1'): ECTyping_value Hty1...
      forwards (Hty1e' & Hty1i'): EquiTypingC_sem Hty1'.
      forwards (v'' & Hred' & Hty'): reduction_app Hty1' Hty2...
      exists v''. split...
      { applys rt_trans Hred'. applys Red_ctx_appl... admit. }

    + forwards* (e2' & Hred' & Hty'): IHHty.
      exists (e_cast c e2'). split.
      { applys Red_ctx_cast... admit. } { eapply ECTyping_eq;eassumption. }
    + 
      forwards* (e2' & Hred' & Hty'): IHHty.
  -
    inductions Hty.
    + forwards* (e1'' & Hred' & Hty'): IHHred.
      exists (e_app e1'' e2'). split.
      { applys Red_ctx_appl... admit. } { eapply ECTyping_app. apply Hty'. apply Hty2. }
    + forwards* (e'' & Hred' & Hty'): IHHty. { apply IHHred. }
      exists (e_cast c e''). split.
      { applys Red_ctx_cast... admit. } { eapply ECTyping_eq;eassumption. }
    + 
      forwards* (e2' & Hred' & Hty'): IHHty.
      { intros. apply IHHred... }
  -
    inductions Hty.
    + 
      forwards (v1' & Hred1 & Hval1' & Hty1'): ECTyping_value Hty1...
      forwards* (e2'' & Hred' & Hty'): IHHred.
      exists (e_app v1' e2''). split.
      { applys rt_trans (e_app v1' e2'0). applys Red_ctx_appl... admit.
        applys Red_ctx_appr... } { eapply ECTyping_app;eassumption. }
    + forwards* (e'' & Hred' & Hty'): IHHty. { apply IHHred. }
      exists (e_cast c e''). split.
      { applys Red_ctx_cast... admit. } { eapply ECTyping_eq;eassumption. }
    + 
      forwards* (e'' & Hred' & Hty'): IHHty.
        { intros. apply IHHred... }
  -
    inductions Hty.
    + 
      assert (Hty: EquiTypingC nil nil (e_fixpoint A e) A (e_fixpoint A e')).
      { apply ECTyping_fix with (L:=L)... }
      pick_fresh X. specialize_x_and_L X L.
      exists (open_exp_wrt_exp e' (e_fixpoint A e')). split.
      { apply rt_step. constructor... admit.  }
      { rewrite subst_exp_intro  with (x1:=X) (e1:=e)...
        rewrite subst_exp_intro  with (x1:=X) (e1:=e')...
        rewrite_alist (@nil (atom * typ) ++ nil ).
        apply ECTyping_subst with (A:=A)...
      }
    + forwards* (e'' & Hred' & Hty'): IHHty.
      exists (e_cast c e''). split.
      { applys Red_ctx_cast... admit. } { eapply ECTyping_eq;eassumption. }
    + forwards* (e'' & Hred' & Hty'): IHHty.
  -
    admit.
  -
    admit.
  -
    admit.
  -
    admit.
  - 
    admit.
  -
    admit.
Admitted.

(*************************************************************************************************************************)
(* Semantic Equivalence to the equi-recursive type system *)


Theorem erase_typing: forall D G e t e', 
  EquiTypingC D G e t e' -> erase e' = e.
Proof with auto.
  intros.
  induction H...
  - simpl. f_equal.
    pick_fresh x. specialize_x_and_L x L.
    rewrite erase_open_ee in H0.
    simpl in H0. apply open_exp_wrt_exp_inj in H0...
    rewrite erase_fv. fsetdec.
  - simpl. f_equal...
  - simpl. f_equal.
    pick_fresh x. specialize_x_and_L x L.
    rewrite erase_open_ee in H0.
    simpl in H0. apply open_exp_wrt_exp_inj in H0...
    rewrite erase_fv. fsetdec.
Qed.

Theorem erase_reduction: forall e t e' v,
  EquiTypingC nil nil e t e' ->
  e ==>* v -> value v ->
  exists v', e' ==>* v' /\ EquiTypingC nil nil v t v' 
  (* /\ value v' *)
  .
Proof with auto.
  intros.
  apply clos_rt_rt1n in H0. gen e'.
  induction H0;intros.
  -
    exists e'. repeat split...
    apply rt_refl...
  -
    forwards: reduction_e2i H2 H.
    destruct H3 as [e1 [Hred1 Hty1]].
    forwards [v' [Hred2 Hty2]]: IHclos_refl_trans_1n Hty1...
    exists v'. repeat split...
    eapply rt_trans;eassumption.  
Qed.





(* Inductive diverge : exp -> Prop :=
  | DivergesIntro : forall (e : exp),
      (* There exists an infinite sequence of small steps *)
      (* (exists e', (Reduction e e' /\ diverge e')) *)
      forall e', Reduction e e' -> diverge e'
      -> diverge e.
 *)


Definition diverge (e:exp) : Prop :=
  ~ (exists v, value v /\ e ==>* v).

Theorem erase_diverge: forall e t e',
  EquiTypingC nil nil e t e' ->
  diverge e -> diverge e'.
Proof with auto.
  (* cofix IH. *)
  intros. intros Hc.
  apply H0. destruct Hc as [v [Hval Hred]].
  exists (erase v). split...
  apply erase_typing in H. subst.
  clear - Hred.
  induction Hred.
  - apply reduction_i2e in H...
  - apply rt_refl.
  - apply rt_trans with (y:=erase y)...
Qed.