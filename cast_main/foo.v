



Inductive cast_repr: actx -> typ -> typ -> list castop -> Prop :=
| crepr_base: forall D A B, 
    AmberSubtyping D A B ->
    cast_repr D A B nil
| crepr_cast: forall D A A' B' B cs c,
    cast_repr D A A' cs ->
    eqec nil A' B' c ->
    AmberSubtyping D B' B ->
    cast_repr D A B (c::cs).
(* | crepr_sub: forall D A B C cs,
    cast_repr D A B cs ->
    AmberSubtyping D B C ->
    cast_repr D A C cs. *)

#[global]
Hint Constructors cast_repr : core.

Fixpoint combine_arr1 (cs: list castop) :=
  match cs with
  | (c::cs') =>  combine_arr1 cs' ++ (c_arrow c c_id) :: nil
  | nil => nil
  end.

Fixpoint combine_arr2 (cs: list castop) :=
  match cs with
  | (c::cs') => (c_arrow c_id c) :: combine_arr2 cs'
  | nil => nil
  end.


(* Fixpoint combine_arr (cs1 cs2: list castop) : list castop :=
  match cs1 with
  | (c1::cs1') =>
    match cs2 with 
    | (c2::cs2') =>  (c_arrow c1 c2) :: combine_arr cs1' cs2'
    | nil => combine_arr1 cs1
    end
  | nil =>
    combine_arr2 cs2
  end. *)

Definition cast_combine cs1 cs2 := 
  List.map (fun '(c1, c2) => c_arrow c1 c2) (List.combine cs1 cs2).

Fixpoint combine_arr_aux (cs1 cs2 cst1 cst2: list castop) : list castop :=
  match cs2 with
  | (c2::cs2') =>
    match cs1 with 
    | (c1::cs1') => combine_arr_aux cs1' cs2' (c1 :: cst1 ) (c2 :: cst2)
    | nil => combine_arr2 cs2 ++ cast_combine cst1 cst2
    end
  | nil =>
    (cast_combine cst1 cst2) ++ combine_arr1 cs1
  end.

Notation combine_arr cs1 cs2 := (combine_arr_aux cs1 cs2 nil nil).


Lemma combine_arr1_app: forall cs1 cs2,
  combine_arr1 (cs1 ++ cs2) = combine_arr1 cs2 ++ combine_arr1 cs1.
Proof with auto.
  induction cs1...
  - simpl...
  - intros. simpl. rewrite IHcs1...
Qed.


Lemma combine_arr1_nil: forall cs,
  combine_arr cs nil = combine_arr1 cs.
Proof with auto.
  induction cs...
Qed.



Lemma list_last: forall {A:Type} (l:list A),
  l <> nil -> exists l' x, l = l' ++ [x].
Proof with auto.
  intros.
  inductions l.
  - exfalso...
  - destruct l.
    + exists (@nil A). exists a...
    + forwards (?&?&?): IHl. intros C. inv C...
      exists (a::x). exists x0... rewrite H0. simpl.
      rewrite <- cons_app_assoc...
Qed.

Lemma cast_repr_split: forall AE A B cs1 cs2,
  cast_repr AE A B (cs1 ++ cs2) ->
  (* exists A' B' c, cast_repr AE A A' cs2 /\ 
      cast_repr AE B' B cs1 /\ eqec nil A' B' c. *)
  exists C, cast_repr AE A C cs2 /\ 
      cast_repr AE C B cs1.
Proof with auto.
  intros. gen AE A B cs2.
  inductions cs1;intros...
  - 
    exists B. split...
    (* exists B, B ,c_id. repeat split... *)
    + constructor... apply ASub_refl... admit. admit.
    (* + constructor... admit. *)
  - inv H. 
    (* forwards (A1' &B1' & c' & ? &? &?): IHcs1 H2. *)
    forwards (C &? &?): IHcs1 H2.
    exists C. repeat split...
    + applys crepr_cast H1 H6 H7.
Admitted.

(* Print AmberSubtyping. *)

Lemma ASub_trans: forall AE A B C,
  AmberSubtyping AE A B -> AmberSubtyping AE B C -> AmberSubtyping AE A C.
Admitted.

Lemma cast_repr_merge: forall AE A C B cs1 cs2,
  cast_repr AE A C cs2 ->
  cast_repr AE C B cs1 ->
  cast_repr AE A B (cs1 ++ cs2).
Proof with auto.
  intros. gen AE A B C cs2.
  inductions cs1;intros...
  - simpl. inv H0. clear H0. gen B. inductions H;intros.
    + constructor... eapply ASub_trans;try eassumption.
    + eapply crepr_cast. apply H. apply H0.
    eapply ASub_trans;try eassumption.
  - simpl. inv H0. forwards: IHcs1 H3 H.
    applys crepr_cast H1 H7...
Qed.


Lemma eqec_symm: forall D A B c,
eqec D A B c -> eqec (reverse_E D) B A (rev_cast c).
Admitted.

(* Lemma combine_arr_app_app: forall cs1 cs2 cs,
  combine_arr (cs1 ++ cs2) cs = combine_arr cs1 cs ++ (combine_arr cs2 cs).
Proof with auto.
  induction cs1;intros...
  - simpl...
  simpl. rewrite IHcs1... *)

Lemma combine_arr_cons: forall c1 c2 cs1 cs2,
  combine_arr (cs1 ++ c1 :: nil) (c2::cs2) =  (c_arrow c1 c2):: combine_arr cs1 cs2 .
(* Proof with auto.
  induction cs2;intros...
  -  inductions cs1.
    + simpl...
    + simpl...
  - inductions cs1.
    + simpl in IHcs2. destruct cs2.
      * simpl... 
      * simpl...
    + simpl...
  simpl. rewrite IHcs1... *)
  Admitted.

Lemma cast_repr_sub: forall AE A B cs C,
  cast_repr AE A B cs ->
  AmberSubtyping AE B C ->
  cast_repr AE A C cs.
Proof with auto.
  intros.
  inv H.
  + constructor... eapply ASub_trans;eassumption.
  + eapply crepr_cast with (A':=A') (B':=B')...
    eapply ASub_trans;eassumption.
Qed.


Lemma combine_arr_sem_aux: forall k AE A1 A2 B1 B2 cs1 cs2,
S (length cs1) <= k ->
cast_repr AE B1 A1 cs1 ->
cast_repr AE A2 B2 cs2 ->
cast_repr AE (t_arrow A1 A2) (t_arrow B1 B2) (combine_arr (List.map rev_cast cs1) cs2).
Proof with auto.
  intros. gen k cs1 cs2 A1 B1 AE A2 B2.
  inductions k;intros.
  { destruct cs1; simpl in H; exfalso; lia. }
  destruct cs1.
  + inductions cs2;intros.
    * unfold combine_arr. cbn.
      constructor...
      inv H0. inv H1...
    * inv H1. forwards: IHcs2 H0 H4. simpl in *.
      unfold cast_combine in *. simpl in *.
      replace ( match cs2 with
      | nil => nil
      | _ :: _ => combine_arr2 cs2 ++ nil
      end) with (combine_arr2 cs2) in H2...
      2:{ destruct cs2... } rewrite app_nil_r.
      applys crepr_cast (t_arrow B1 B') H2...
     { apply ec_arr... apply ec_refl. admit. }
     { constructor... apply ASub_refl. admit. admit. }
  + inductions cs2;intros.
    * 
      simpl. inv H0. forwards: IHk H4 H1. { simpl in H. simpl. lia. }
      rewrite combine_arr1_nil in H2. 
      applys cast_repr_merge H2.
      { eapply crepr_cast with (A':=t_arrow B' A2) (B':=t_arrow A' A2)...
        + constructor... constructor... apply ASub_refl. admit. admit.
        + constructor... { apply eqec_symm with (D:=nil)... }
          constructor... admit.
        + constructor... { apply ASub_refl. admit. admit. }
          { apply ASub_refl. admit. admit. }
      }
    *
      inv H1.
      destruct (list_last (c::cs1)) as [cs1' [c1' ?]]... { intros C. inv C. }
      rewrite H2 in *.
      forwards (C1&?&?): cast_repr_split H0.
      forwards: IHk H5 H4. { rewrite app_length in H. simpl in H. lia. }
      rewrite List.map_app. simpl.
      rewrite combine_arr_cons.
      inv H3. inv H11.
      eapply crepr_cast with (A':=t_arrow B'0 A') (B':=t_arrow A'0 B').
      { eapply cast_repr_sub; try eassumption. constructor...
        apply ASub_refl. admit. admit. }
      { constructor... apply eqec_symm with (D:=nil)... }
      { constructor... }
Admitted.

Lemma combine_arr_sem: forall AE A1 A2 B1 B2 cs1 cs2,
cast_repr AE B1 A1 cs1 ->
cast_repr AE A2 B2 cs2 ->
cast_repr AE (t_arrow A1 A2) (t_arrow B1 B2) (combine_arr (List.map rev_cast cs1) cs2).
Proof with auto.
  intros.
  apply combine_arr_sem_aux with (k:=S (length cs1))...
Qed.

Lemma unfold_fv: forall A,
  lc_typ (t_mu A) ->
  typefv_typ (t_mu A) [=] typefv_typ (unfold_mu A).
Proof with auto.
  intros. 
  apply KeySetProperties.subset_antisym.
  +
    rewrite <- typefv_typ_open_typ_wrt_typ_lower.
    reflexivity.
  +
    rewrite typefv_typ_open_typ_wrt_typ_upper.
    simpl. fsetdec.
Qed.



(* 
Inductive WHNF_eqWi_fv (R:  typ -> typ -> Prop): typ -> typ -> Prop :=
| wh_fv_done: forall t1 t2, typefv_typ t1 [=] typefv_typ t2 ->
    WHNF_eqWi_fv R t1 t2
| wh_fv_arrow: forall  t1 t2 t1' t2',
    R t1 t1' -> (* coinductive WHNF_eqP *)
    R t2 t2' ->
    WHNF_eqWi_fv R (t_arrow t1 t2) (t_arrow t1' t2')
| wh_fv_trans: forall  t1 t2 t3, 
    R  t1 t2 ->
    R  t2 t3 ->
    WHNF_eqWi_fv R t1 t3
.

#[export]
Hint Constructors WHNF_eqWi : core.

CoInductive WHNF_eqW_fv : typ -> typ -> Prop :=
| wh_fv_introw: forall (R:  typ -> typ -> Prop),
    (forall t1 t2, R  t1 t2 -> R t2 t1) ->
    (forall t1 t2, R t1 t2 -> 
      (exists A,
          (forall t1 t2, In (t1, t2) A
            (* A *)
              -> WHNF_eqW_fv t1 t2) /\
          eqe A t1 t2)) ->
    forall t1 t2,
      WHNF_eqWi_fv R t1 t2 ->
      WHNF_eqW_fv t1 t2.


  Theorem soundW_fv: forall t1 t2 A,
  (forall t1 t2, In (t1, t2) A -> WHNF_eqW_fv t1 t2) ->
  (* (forall t1 t2, In (t1, t2) (reverse_A A) -> WHNF_eqW t1 t2) -> *)
  eqe A t1 t2 ->
  WHNF_eqW_fv t1 t2.
  Admitted.

Theorem interp_W_fv: forall t1 t2,
  (WHNF_eqW_fv t1 t2 -> typefv_typ t1 [=] typefv_typ t2).
Proof.
  intros.
  inversion H;subst.
  inversion H2;subst.
  - apply H3.
  - forwards (A1&He1&He2): H1 H3.
    forwards Hwhnf1: soundW_fv He1 He2.
    forwards (A2&He3&He4): H1 H4.
    forwards Hwhnf2: soundW_fv He3 He4.
    apply Tyeq_arrow.
    + apply interp_W. 
      (* apply WHNF_eqW_symm.  *)
      exact Hwhnf1.
    + apply interp_W. exact Hwhnf2.

  - forwards (A1&He1&He2): H1 H3.
    lets He1': interp_W_aux_transform He1.
    forwards Hwhnf1: soundW He1' He2.
    forwards (A2&He3&He4): H1 H4.
    lets He3': interp_W_aux_transform He3.
    forwards Hwhnf2: soundW He3' He4.
    apply Tyeq_trans with (t2:=t3).
    + apply interp_W. exact Hwhnf1.
    + apply interp_W. exact Hwhnf2.
(* 
  - forwards (A1&He1&He2): H0 H2.
    forwards Hwhnf1: soundW He1 He2.
    forwards (A2&He3&He4): H0 H3.
    forwards Hwhnf2: soundW He3 He4.
    apply Tyeq_trans with (t2:=t3).
    + apply interp_W. exact Hwhnf1.
    + apply interp_W. exact Hwhnf2. *)
  (* - 
    forwards (A1&He1&He2): H0 H2.
    forwards Hwhnf1: soundW He1 He2.
    apply Tyeq_symm. apply interp_W.
    Guarded. assumption. *)
Qed.

Theorem soundness_fv: forall A t1 t2,
  (forall t1 t2, In (t1, t2) A -> typefv_typ t1 [=] typefv_typ t2) ->
  eqe A t1 t2 ->
  typefv_typ t1 [=] typefv_typ t2.
Proof.
  intros.
  apply interp_W.
  apply soundW with (A:=A). 2:{ exact H0. }
  intros.
  forwards: H H1.
  apply wh_introw with (R:=fun m x y => False).
  2:{ intros. destruct H3. }
  2:{ apply done_aux. apply H2. }
  intros. destruct H3.
Qed.


#[export]
Hint Constructors WHNF_eqWi : core.

CoInductive WHNF_eqW : typ -> typ -> Prop :=
| wh_introw: forall (R: mode -> typ -> typ -> Prop),
    (forall m t1 t2, R (flip m) t1 t2 -> R m t2 t1) ->
    (forall m t1 t2, R m t1 t2 -> 
      (exists A,
          (forall t1 t2, In (t1, t2) 
            (match m with m_pos => A | m_neg => reverse_A A end)
            (* A *)
              -> WHNF_eqW t1 t2) /\
          eqe A t1 t2)) ->
    forall t1 t2,
      WHNF_eqWi R t1 t2 ->
      WHNF_eqW t1 t2. *)


(* Inductive tyR : typ -> typ -> Prop :=
| tyR_refl : forall A, tyR A A
| tyR_trans : forall A B C, tyR A B -> tyR B C -> tyR A C
| tyR_unfold : forall A, tyR (t_mu A) (unfold_mu A)
| tyR_fold : forall A, tyR (unfold_mu A) (t_mu A)
| tyR_arr : forall A1 A2 B1 B2,
    tyR A1 A2 -> tyR B1 B2 -> tyR (t_arrow A1 B1) (t_arrow A2 B2)
. *)


(* Inductive tyR : typ -> typ -> castop -> Prop :=
| tyR_refl : forall A, tyR A A c_id
| tyR_trans : forall A B C c1 c2, tyR A B c1 -> tyR B C c2 -> tyR A C (c_seq c1 c2)
| tyR_unfold : forall A, tyR (t_mu A) (unfold_mu A) (c_unfold (t_mu A))
| tyR_fold : forall A, tyR (unfold_mu A) (t_mu A) (c_fold (t_mu A))
| tyR_arr : forall A1 A2 B1 B2 c1 c2,
    tyR A1 A2 c1 -> tyR B1 B2 c2-> 
    tyR (t_arrow A1 B1) (t_arrow A2 B2) (c_arrow c1 c2)
| tyR_fix : forall A1 A2 B1 B2 c1 c2,
    tyR A1 A2 (open_castop_wrt_castop c1 (c_fixc (c_arrow c1 c2))) -> 
    tyR B1 B2 (open_castop_wrt_castop c2 (c_fixc (c_arrow c1 c2))) -> 
    tyR (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2))
. *)


(* Lemma eqec_fv : forall E c A B, 
  tyR A B c ->
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
     typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  (* introv Heq.
  inversion Heq;subst.
  inversion H1;subst.
  + *)
  introv HR Heq Henv. gen E. inductions HR;intros...
  (* - forwards: Henv H... *)
  - reflexivity.
  - rewrite IHHeq1...
  - rewrite unfold_fv... reflexivity.
  - rewrite <- unfold_fv... reflexivity.
  - simpl. 
    rewrite IHHeq1, IHHeq2...
    reflexivity.
  -
    simpl.
    assert (eqec E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2)))...
    { apply ec_arrfix with (L:=L)... }

    
    pick_fresh cx. specialize_x_and_L cx L.
    rewrite H0...
    2:{ intros. rewrite cons_app_one in H3. rewrite <- app_assoc in H3.
        applys Henv H3. }
    rewrite H2...
    2:{ intros. rewrite cons_app_one in H3. rewrite <- app_assoc in H3.
        applys Henv H3. }
    reflexivity.
Qed. *)



(* Idea:

If we also restrict transitivity to have empty environment,
then using (Length E, size A + size B) will be enough for the proof

*)

(* Lemma eqe_fv : forall E A B c k, 
  List.length E + size_castop c  <= k ->
  eqec E A B ->
  (forall E1 E2 A' B', E = E1 ++ [(A', B')] ++ E2 -> 
    exists c', eqec E2 A' B' c' )->
  typefv_typ A [=] typefv_typ B.
 *)


(* Proof with auto.
  introv Hsiz Heq Henv. gen A B E.
  inductions k.
  { intros. destruct A, B; simpl in Hsiz; exfalso; lia. }
  intros. inv Heq;intros.
  -
    apply in_split in H. destruct H as [E1' [E2' ?]].
    forwards: Henv H.
    forwards: IHk H0...
    { rewrite H in Hsiz. rewrite app_length in Hsiz. simpl in Hsiz. lia. }
    { intros. subst. applys Henv (E1' ++ (A, B) :: E1).
      rewrite !app_assoc. simpl. reflexivity. }
  -
    reflexivity.
  -
     *)



(* Lemma eqec_fv : forall E c A B k, 
  List.length E + size_typ A + size_typ B  <= k ->
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
     typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  introv Hsiz Heq Henv. gen A B c E.
  inductions k.
  { intros. destruct c; simpl in Hsiz; exfalso; lia. }
  intros.  inv Heq;intros.
  7:{
    simpl in Hsiz.
    pick_fresh cx. specialize_x_and_L cx L.
    forwards: IHk H. { admit. } { admit. }
    rewrite H1...
    2:{ intros. rewrite cons_app_one in H3. rewrite <- app_assoc in H3.
        applys Henv H3. }
    rewrite H2...
    2:{ intros. rewrite cons_app_one in H3. rewrite <- app_assoc in H3.
        applys Henv H3. }
    reflexivity.
  }
  - forwards: Henv H...
  - reflexivity.
  
     
    forwards: IHk H. lia. 


  - rewrite unfold_fv... reflexivity.
  - rewrite <- unfold_fv... reflexivity.
  3:{ } *)


Fixpoint lmc (c:castop) :=
  match c with
  | c_fixc c' => S (lmc c')
  (* | c_seq c1 c2 => S (lmc c1 + lmc c2) *)
  | _ => 1
  end.

(* Lemma eqec_fv : forall A B k j, 
  isContra m_pos A = true ->
  lmc A <= j -> size_typ A <= k ->
    (* lmc c = 1 -> *)
  Tyeq' A B ->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  introv Hcontra Hsiz1 Hsiz2 Heq.
  gen A B j.
  inductions k.
  { intros. destruct A; inv Hsiz2. }
  intros. gen A B. inductions j.
  { intros. destruct A; inv Hsiz1. }
  intros. inv Heq; simpl in Hsiz1, Hsiz2; try solve [reflexivity].
  - forwards: IHk H. 
    { simpl in Hcontra. destruct A1; simpl in Hcontra;simpl;auto; inv Hcontra. } { lia. } { lia. } { apply H0. }
    forwards: IHj H0. { simpl in Hcontra. destruct A; inv Hcontra. } { lia. } { lia. } { apply H1. }
    fsetdec. *)

(* Lemma eqec_contra_castop: forall E A B c,
  eqec E A B c ->
  lmc c = 1.
Proof with auto.
  intros.
  inductions H;simpl;try lia... *)
(* 


Fixpoint isContra (m:mode) (c:castop) :=
  match m with
  | m_pos =>
      (* is Contra *)
      match c with
      | c_arrow c1 c2 => isContra m_neg c1 && isContra m_neg c2
      | c_fixc c' => isContra c'
      | c_seq c1 c2 => isContra c1 && isContra c2
      | c_var_f _ => true
      | c_var_b _ => false
      | _ => true
      | 
      end
  | m_neg =>
      (* is Rec *)
      | c_var_f _ => true *)





Lemma eqec_fv_1 : forall E c A B k, 
  lmc c <= 1 -> 
  size_castop c <= k ->
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
      typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  introv Hsiz1 Hsiz2
  (* Hcontra *)
    Heq Henv.
  gen k A B c E.
  inductions k.
  { intros. destruct c; inv Hsiz2. }
  intros.
  inv Heq; simpl in Hsiz1, Hsiz2.
  +
    forwards: Henv H...
  +
    reflexivity.
  +
    forwards: IHk H... ; try lia...
    { admit. intros.  }
    forwards: IHk H0; try lia...
    fsetdec.
  + rewrite unfold_fv... reflexivity.
  + rewrite <- unfold_fv... reflexivity.
  +
    forwards: IHk H; try lia...
    forwards: IHk H0; try lia...
    simpl. fsetdec.
  +
    simpl.
    assert (eqec E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2)))...
    assert (Heq1: eqec E (t_arrow A1 B1) (t_arrow A2 B2)  (open_castop_wrt_castop (c_arrow c1 c2) (c_arrow c1 c2))).
    { admit. }
    forwards: IHj Heq1...
    { simpl. lia. }


Lemma eqec_fv_1 : forall E c A B k j, 
  lmc c <= j -> 
  size_castop c <= k ->
  (* lmc c = 1 -> *)
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
      typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  introv Hsiz1 Hsiz2
    (* Hcontra *)
    Heq Henv.
  gen j k A B c E.
  inductions j.
  { intros. destruct c; inv Hsiz1. }
  inductions k.
  { intros. destruct c; inv Hsiz2. }
  intros.
  inv Heq; simpl in Hsiz1, Hsiz2.
  +
    forwards: Henv H...
  +
    reflexivity.
  +
    forwards: IHk H. ; try lia...
    { admit. intros.  }
    forwards: IHk H0; try lia...
    fsetdec.
  + rewrite unfold_fv... reflexivity.
  + rewrite <- unfold_fv... reflexivity.
  +
    forwards: IHk H; try lia...
    forwards: IHk H0; try lia...
    simpl. fsetdec.
  +
    simpl.
    assert (eqec E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2)))...
    assert (Heq1: eqec E (t_arrow A1 B1) (t_arrow A2 B2)  (open_castop_wrt_castop (c_arrow c1 c2) (c_arrow c1 c2))).
    { admit. }
    forwards: IHj Heq1...
    { simpl. lia. }
Abort.




Lemma eqec_fv_aux : forall E c A B k , 
  size_castop c <= k ->
  (* lmc c = 1 -> *)
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
     typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  introv Hsiz
   Hcontra
    Heq Henv.
  gen A B c E.
  inductions k.
  { intros. destruct c; inv Hsiz. }
  intros.
  inv Heq; simpl in Hsiz.
  +
    forwards: Henv H...
  +
    reflexivity.
  +
    forwards: IHk H; try lia...
    forwards: IHk H0; try lia...
    fsetdec.
  + rewrite unfold_fv... reflexivity.
  + rewrite <- unfold_fv... reflexivity.
  +
    forwards: IHk H; try lia...
    forwards: IHk H0; try lia...
    simpl. fsetdec.
  +


Lemma eqec_fv : forall E c A B k j, 
  lmc c <= j -> size_castop c <= k ->
  (* lmc c = 1 -> *)
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
     typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  introv Hsiz1 Hsiz2
   (* Hcontra *)
    Heq Henv.
  gen A B c E j.
  inductions k.
  { intros. destruct c; inv Hsiz2. }
  intros. gen A B c E k. inductions j.
  { intros. destruct c; inv Hsiz1. }
  intros.
  inv Heq; simpl in Hsiz1, Hsiz2.
  +
    forwards: Henv H...
  +
    reflexivity.
  +
    forwards: IHk H; try lia...
    forwards: IHk H0; try lia...
    fsetdec.
  + rewrite unfold_fv... reflexivity.
  + rewrite <- unfold_fv... reflexivity.
  +
    forwards: IHk H; try lia...
    forwards: IHk H0; try lia...
    simpl. fsetdec.
  +
    simpl.
    assert (eqec E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2)))...
    assert (Heq1: eqec E (t_arrow A1 B1) (t_arrow A2 B2) (open_castop_wrt_castop (c_arrow c1 c2) (c_arrow c1 c2))).
    { admit. }
    forwards: IHj Heq1...
    { simpl. lia. }
    intros. eapply IHk. 2:{ apply Heq0. }

Abort.
    





Lemma eqec_fv : forall E c A B, 
  (* WHNF_eqW A B -> *)
  eqec E A B c ->
  (forall A' B' cx', In (cx', (A', B')) (E) -> 
     (* size_typ A' <= size_typ A ->
     size_typ B' <= size_typ B -> *)
     typefv_typ A' [=] typefv_typ B')->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  (* introv Heq.
  inversion Heq;subst.
  inversion H1;subst.
  + *)
  introv Heq Henv. inductions Heq...
  - forwards: Henv H...
  - reflexivity.
  - rewrite IHHeq1...
    (* 2:{ intros. apply Henv in H... } *)
    (* rewrite IHHeq2... *)
  - rewrite unfold_fv... reflexivity.
  - rewrite <- unfold_fv... reflexivity.
  - simpl. 
    rewrite IHHeq1, IHHeq2...
    reflexivity.
  -
    simpl.
    assert (eqec E (t_arrow A1 B1) (t_arrow A2 B2) (c_fixc (c_arrow c1 c2)))...
    { apply ec_arrfix with (L:=L)... }

    
    pick_fresh cx. specialize_x_and_L cx L.
    rewrite H0...
    2:{
        intros. inv H4.
        2:{ apply Henv in H5... }
        inv H5.
        admit.
    }
    rewrite H2...
    2:{
        intros. inv H4.
        2:{ apply Henv in H5... }
        inv H5.
        admit.
    }
Admitted.


Lemma eqec_fv' : forall c A B, 
  (* WHNF_eqW A B -> *)
  eqec nil A B c ->
  typefv_typ A [=] typefv_typ B.
Proof with auto.
  intros.
  forwards: eqec_fv H...
  intros. inv H0.
Qed.


Lemma ACSub_repr: forall D A B,
  ACSubtyping D A B ->
  exists cs, cast_repr D A B cs.
Proof with auto.
  intros. inductions H...
  - exists (@nil castop).
    apply crepr_base.
    apply ASub_top... admit. admit.
  - exists (@nil castop)...
    apply crepr_base. admit.
  - 
    (* trans *)
    destruct IHACSubtyping1 as [cs1 IH1].
    destruct IHACSubtyping2 as [cs2 IH2].
    exists (cs2 ++ cs1).
    eapply cast_repr_merge;eassumption.
  -
    (* var *)
    exists (@nil castop)...
    apply crepr_base.
    apply ASub_var... admit. 
    admit.
  -
    (* tyeq *)
    (* Check TypCast_completeness. H. *)
    admit.
  -
    (* arrow *)
    destruct IHACSubtyping1 as [cs1 IH1].
    destruct IHACSubtyping2 as [cs2 IH2].
    exists (combine_arr (List.map rev_cast cs1) cs2).
    apply combine_arr_sem...
  -
    (* mu *)
    pick_fresh X. pick_fresh Y.
    specialize_x_and_L X L.
    specialize_x_and_L Y (union L (singleton X)).
    destruct H0 as [cs' ?].
     (* exists cs'. *)
    clear H. gen A B. inductions cs';intros.
    + inductions H0. 
      { exists (@nil castop). apply crepr_base.
        apply ASub_rec with (L:=L \u {{X}} \u {{Y}}). intros.
        admit. }
    + inv H0.



      (* X notin fv B' -> fv B' = fv A' so X not in fv A' *)
      forwards: eqec_fv' H6.
      assert (X `notin` typefv_typ A').
      {  rewrite H. admit. }
      (* Y notin fv A' -> fv B' = fv A' so Y not in fv B' *)
      assert (Y `notin` typefv_typ B').
      { rewrite <- H.

      admit. }
      rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (A1:=A') (X1:=X) in H2.
      (* rewrite <- open_typ_wrt_typ_close_typ_wrt_typ with (A1:=B') (X1:=Y) in H7. *)
      forwards: IHcs' H2.
      { rewrite typefv_typ_close_typ_wrt_typ... }
      { rewrite typefv_typ_close_typ_wrt_typ... fsetdec. }
      destruct H4 as [cs ?].
      exists ((c_seq 
        (c_unfold (t_mu A'))
        (c_seq a (
          c_fold (t_mu B')
        ))
       ) :: cs).
      apply crepr_cast with
        (A':=t_mu (close_typ_wrt_typ X A'))
        (B':=t_mu (close_typ_wrt_typ Y B'))...
      {
        rewrite !close_typ_wrt_typ_lc_typ... 2:{ admit. } 2:{ admit. }
        rewrite !close_typ_wrt_typ_lc_typ in H4... 2:{ admit. }
        eapply ec_trans. { apply ec_unfold. admit. }
        eapply ec_trans. 2:{ apply ec_fold. admit. }
        rewrite open_typ_wrt_typ_lc_typ... 2:{ admit. }
        rewrite open_typ_wrt_typ_lc_typ... { admit. }
      }
      {
        rewrite <- open_typ_wrt_typ_lc_typ with (A1:=t_var_f Y) (A2:=B') in H7. 2:{ admit. }
        apply ASub_rec with (L:=L \u {{X}} \u {{Y}}).
        intros X' ? Y' ?. rewrite close_typ_wrt_typ_lc_typ... 2:{ admit. }


        admit.
      }
Admitted.





Lemma cast_repr_e2i: forall D G cs A B e e',
  cast_repr nil A B cs ->
  Typing D nil G e' A ->
  erase e' = e ->
  exists e'', Typing D nil G e'' B /\ erase e'' = e.
Proof with auto.
  introv Hrepr Htyp Herase.
  inductions Hrepr.
  + exists e'. split*.
  + forwards (e'' & Hty' & Herase'): IHHrepr...
    exists (e_cast c e''). split*.
    apply Typing_sub with (A:=B')...
    apply Typing_cast with (A:=A')...
    applys eqec_TypCast H...
    { forwards: AmberSub_WFT H0. destruct_hypos...
      rewrite_alist (nil ++ D ++ nil).
      apply WFT_weakening... }
Qed.



