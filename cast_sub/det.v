Require Import Program.Equality.
Require Import Metalib.Metatheory.
Require Export LibTactics.
Require Import Lia.
Require Import Relation_Operators.
Require Import Operators_Properties.

Require Export equiAux.

Inductive lc_cast: castop -> Prop :=
| lc_cast_var_f : forall x, lc_cast (c_var_f x)
| lc_cast_id : lc_cast c_id
| lc_cast_seq : forall c1 c2, lc_cast c1 -> lc_cast c2 -> lc_cast (c_seq c1 c2)
| lc_cast_arrow : forall c1 c2, lc_cast c1 -> lc_cast c2 -> lc_cast (c_arrow c1 c2)
| lc_cast_fix : forall c1 c2, 
      lc_cast (open_castop_wrt_castop c1 (c_fixc (c_arrow c1 c2))) ->
      lc_cast (open_castop_wrt_castop c2 (c_fixc (c_arrow c1 c2))) ->
      lc_cast (c_fixc (c_arrow c1 c2))
| lc_cast_unfold : forall A, lc_cast (c_unfold A)
| lc_cast_fold : forall A, lc_cast (c_fold A)
.
#[export]
Hint Constructors lc_cast:core.

Lemma lc_cast_subst: forall c x c', lc_castop c ->
  lc_cast c -> lc_cast c' -> lc_cast (castsubst_castop c x c').
Proof with auto.
  intros.
  inductions H1;simpl...
  - destruct (x0 == x)...
  - apply lc_cast_fix;simpl.
    + pose proof castsubst_castop_open_castop_wrt_castop
        c1 c (c_fixc (c_arrow c1 c2)) x.
      simpl in H1.
      rewrite <- H1...
    + pose proof castsubst_castop_open_castop_wrt_castop
        c2 c (c_fixc (c_arrow c1 c2)) x.
      simpl in H1.
      rewrite <- H1...
Qed.

Lemma TypCast_lc_cast: forall D G A B c,
  TypCast D G A B c -> lc_cast c.
Proof with auto.
  intros.
  inductions H...
  - apply lc_cast_fix.
    + pick_fresh cx. rewrite castsubst_castop_intro with (cx1:=cx)...
      apply lc_cast_subst... admit.
      constructor...
      rewrite castsubst_castop_intro with (cx1:=cx)...
      apply lc_cast_subst... admit.
      constructor...
      rewrite castsubst_castop_intro with (cx1:=cx)...
      apply lc_cast_subst... admit.
      constructor...
Admitted.

Inductive R: castop -> typ -> typ -> Prop :=
| R_id : forall t, R c_id t t
| R_seq : forall c1 c2 A B C,
    R c1 A B -> R c2 B C -> R (c_seq c1 c2) A C
| R_arrow : forall c A1 B1 A2 B2,
    (forall c1, R c1 A1 A2) ->
    (forall c2, R c2 B1 B2) ->
    R c (t_arrow A1 B1) (t_arrow A2 B2)
.

Goal forall D G A B c, TypCast D G A B c -> R c A B.
introv Hcast. gen D G.
inductions c;intros;inv Hcast.
5:{
  apply R_arrow;intros.
  - apply IHc1...
  - apply IHc2...

}



(* Theorem TypCast_det: forall c,
  forall D G1 G2 A1 A2 B1 B2,
  TypCast D G1 A1 B1 c -> 
  TypCast D G2 A2 B2 c ->
  G1 = G2 -> A1 = A2 -> B1 = B2.
Proof with auto.
  intros.
  inductions H. *)

Theorem TypCast_det: forall k c,
  size_castop c <= k ->
  forall D G1 G2 A B B',
  (forall cx A1 B1 A2 B2,
    In (cx, (A1, B1)) G1 ->
    In (cx, (A2, B2)) G2 ->
    B1 = B2) ->
  TypCast D G1 A B c -> 
  TypCast D G2 A B' c -> B = B'.
Proof with auto.
  inductions k.
  { introv Hsiz. destruct c; simpl in Hsiz; exfalso; lia. }
  introv Hsiz Hcond Hty1 Hty2.
  assert (Hlc: lc_castop c)...
  inv Hlc;inv Hty1; inv Hty2;simpl in Hsiz...
  - forwards: Hcond H7 H11...
  - forwards: IHk H7 H9... { lia. }
    forwards: IHk H8 H11... { lia. }
    subst...
  - admit.
  - 
    pick_fresh cx. specialize_x_and_L cx L.
    specialize_x_and_L cx L0.
    forwards H1a: TypCast_symm2 H1.
    forwards H1b: TypCast_symm2 H8.
    simpl in H1a, H1b.
    forwards: IHk H1 H8.
    assert (
      TypCast D ((cx, (t_arrow A1 B1, t_arrow A3 B3)) :: G)

    )
  
  - forwards (?&?): typcast_var_det H5 H7 H11...





Theorem TypCast_det: forall D G A B c,
  TypCast D G A B c -> 
    (forall B', TypCast D G A B' c -> B = B')
    /\ (forall A', TypCast D G A' B c -> A = A').
Proof with auto.
  introv Htc.
  inductions Htc;
    try destruct IHHtc1 as [IH1a IH1b];
    try destruct IHHtc2 as [IH2a IH2b];
    split;introv Htc';inv Htc'...
  - rewrite (IH1a _ H5).
    rewrite (IH2a _ H7)...
  - rewrite (IH1b _ H5).
    rewrite (IH2b _ H7)...
  - forwards: IH1a H5. subst...
  - forwards: IH2b H6. subst...
  - forwards (?&?): typcast_var_det H1 H2 H11...
  - forwards (?&?): typcast_var_det H1 H2 H11...
  - 
    pick_fresh cx. specialize_x_and_L cx L.
    specialize_x_and_L cx L0.
    destruct H0 as [IH1a IH1b].
    destruct H2 as [IH2a IH2b].
    apply IH1a in H9.


