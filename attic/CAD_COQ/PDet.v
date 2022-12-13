(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)


Require Import Tactic.
(*Load phi.*)
Require Import CAD_types.
Require Import Utils.
Require Import Setoid.
Require Import ZArith.
Require Import Even.
Require Import Pol_ring.
(*Require Import phi.*)
Require Import Mylist.

(*Notation  ZCoef:=Pol.*)
Notation  pol:= Pol.
Notation add :=Pol_add.
Notation "a !* x" := (Pol_mul_Rat  x a )(at level 40, left associativity).


Add New Ring PolRing : PRth Abstract.
Add New Ring CoefRing : cRth Abstract. 



Section ListAux.

Variable A: Set.
Theorem length_app:
 forall (l1 l2 : list A),  length (app l1  l2) = (length l1 + length l2)%nat.
intros l1; elim l1; simpl; auto.
Qed.

End ListAux.


(* lists of Pols pairwise PolEq equal*)
Inductive Pol_list_equiv:(list Pol) -> (list Pol) ->Prop :=
|Nil_equiv : Pol_list_equiv (@nil Pol) (@nil Pol)
|Cons_equiv : forall a1 a2 l1 l2, a1!=a2 -> Pol_list_equiv l1 l2 ->
(Pol_list_equiv (a1::l1) (a2::l2)).


Infix "*=" := Pol_list_equiv (at level 70, no associativity).


Lemma Pol_list_equiv_refl : forall l, l *=l.
Proof.
intro l;induction l;constructor;trivial;reflexivity.
Qed.


Lemma Pol_list_equiv_sym : forall l1 l2,
l1 *= l2 -> l2 *=l1.
Proof.
intros l1 ;induction l1;intro l2;induction l2;intro H;inversion H;constructor;
[apply PolEq_sym;trivial|apply IHl1;trivial].
Qed.


Lemma Pol_list_equiv_trans1 : forall l1 l2,
l1*=l2 -> forall l3, l2 *= l3 -> l1 *= l3.
Proof.
intro l1;induction l1;intro l2;destruct l2;intros Heq12 l3 Heq23.
inversion Heq23;trivial.
inversion Heq12.
inversion Heq23;trivial.
inversion_clear Heq23.
constructor;inversion_clear Heq12.
apply PolEq_trans with p;trivial.
apply IHl1 with l2;trivial.
Qed.


Lemma Pol_list_equiv_trans:forall l1 l2 l3,
l1*=l2 -> l2 *= l3 -> l1 *= l3.
Proof.
intros;apply Pol_list_equiv_trans1 with l2;assumption.
Qed.

Add Relation (list Pol) Pol_list_equiv 
reflexivity proved by Pol_list_equiv_refl
symmetry proved by Pol_list_equiv_sym
transitivity proved  by Pol_list_equiv_trans
as Pol_list_relation.


Add Morphism (@app Pol) with signature
 Pol_list_equiv ==> Pol_list_equiv ==> Pol_list_equiv as app_morph. 
Proof.
intros l1 l2;induction 1;intros m1 m2;induction 1;
simpl;try constructor;trivial.
apply IHPol_list_equiv;constructor.
apply IHPol_list_equiv;constructor;trivial.
Qed.


Lemma Pol_list_equiv_length : forall l m, l *= m -> length l = length m.
Proof.
intros l m;induction 1;simpl;trivial;auto with arith.
Qed.


(*Transparent phi.*)


Ltac toto := match goal with |- context [if ?X then _ else _ ] => case X end.


(*
Add Morphism phi  with signature (@eq nat) ==>(@eq nat) ==> Pol_Eq ==> Pol_Eq  as phi_Morphism.
intros d n P Q;unfold phi;case (le_gt_dec (d+2)n); intros.
Proof.
reflexivity. 
case n;simpl.
reflexivity.
intros;case n0; trivial.
intros;toto;
intros;simpl;
rewrite H;setoid ring.
Show Script.
Qed.
*)

Section det.
Variable phi : nat -> nat -> Pol -> Pol.

(*
Notation scal:=(fun x y =>Pol_mul_Rat y x).
*)
Definition scal(x:Coef)(y:Pol):= Pol_mul_Rat y x.
(*Notation add := Pol_add.*)

Hypothesis phi_m: forall deg n a b c d,
 phi deg n (add (scal a b) (scal c  d)) != a !* phi deg n b + c !* phi deg n d.



Fixpoint rec_det (f: Pol -> Pol) (rec: list Pol -> Pol)  (l1 l2: list pol)  {struct l1}: Pol :=
  match l1 with
    nil =>  P0 
  | a:: l3 => f a * rec (app l2 l3)  - rec_det f  rec  l3 (app l2 (a::nil)) 
  end.

Variable deg:nat.


Fixpoint det_aux (n: nat) (l: list Pol) {struct n}: Pol :=
  match n with
    O => P1
  | S n1 => rec_det (phi deg n) (det_aux n1) l nil
  end.
 


Definition det l :=  det_aux(length l) l.



Theorem rec_det_m: forall f rec a b c d l1 l2,
  (forall a b c d l, (1 + length l = length l1 + length l2)%nat ->
    rec ((add (scal a b) (scal c d)):: l) != a !* rec (b :: l) + c !* rec (d :: l)) ->
  rec_det f rec l1 ((add (scal a b) (scal c d)):: l2)  != a !* rec_det f rec l1 (b :: l2) + c !* rec_det f rec  l1 (d :: l2).
intros f rec a b c d l1 l2; generalize l2; elim l1; simpl; clear l1 l2.
(*intros;Pcsimpl;setoid ring.*)
intros;Pcsimpl;setoid ring.

intros a1 l3 Rec l2 H.
repeat (rewrite Rec||rewrite H);try rewrite length_app;try omega.
intros;rewrite H.
rewrite H0;simpl;omega.
setoid ring.
repeat rewrite Pscal_Pmul_l.
setoid ring.
Qed.



Theorem det_aux_m: forall n a b c d l,
  (n= 1 + length l)%nat ->  det_aux n (((add (scal a b) (scal c d))) :: l) != a !* det_aux n (b :: l) + c !* det_aux n (d :: l).

intros n; elim n; simpl; auto.
intros; discriminate.
intros n1 Rec  a b c d l H; injection H; clear H; intros H.
generalize (phi_m  deg (S n1)); intro Hphi.
repeat (rewrite Rec || rewrite Hphi|| rewrite rec_det_m); auto; repeat rewrite Pscal_Pmul_l.
intros a1 b1 c1 d1 l1;simpl.
rewrite plus_0_r;intros H1; rewrite Rec.
rewrite H; auto.
reflexivity.
setoid ring.
Qed.



Theorem det_m0: forall a b c d l, det ((add (scal a b) (scal c d)) :: l) != a !* det (b :: l) + c !* det (d :: l).
intros; unfold det; rewrite det_aux_m; auto.
simpl length.
case ( even_odd_dec (S (length l)));intro;try rewrite det_aux_m;
auto;setoid ring.
Qed.


Theorem rec_det_r: forall f rec a b  l1 l2 l3,
  (forall a b l'1 l'2, (1 + length l'1 + length l'2 = length l1 + length l2 + length l3)%nat ->
               rec (app l'2( a :: b :: l'1)) != -  rec (app l'2 ( b :: a :: l'1))) ->
  rec_det f rec l1 (app l2 ( a :: b :: l3)) != - rec_det f rec l1 (app l2 (b :: a :: l3)).
intros f rec a b l1; elim l1; simpl; auto; clear l1.
intros;constructor.
setoid ring.

intros a1 l1 Rec l2 l3 H.
assert (tmp: forall a b l4, ( app (app l2 ( a :: b :: l3))  l4) = ((app l2 (a :: b :: (app l3  l4))))).
intros; rewrite app_ass; auto.
repeat rewrite tmp; simpl.
rewrite H; auto with arith.
rewrite length_app; simpl; 
rewrite <- (plus_comm (length l3));auto with arith.
rewrite Rec.
 intros a2 b1 l'1 l'2; rewrite length_app; simpl.
rewrite (fun x => plus_comm x 1).
intros H1; apply H.
rewrite H1; auto with zarith.
setoid ring.
Qed.


Theorem rec_det_t: forall f rec a b  l1 l2 l3,
  (forall a b  l'1 l'2 , (1 + length l'1 + length l'2 = length l1 + length l2 + length l3)%nat -> 
rec (app l'2 (a :: b :: l'1)) != -  rec (app l'2 ( b :: a :: l'1))) ->
  rec_det f rec (app l1 (a :: b :: l2)) l3 != - rec_det f rec (app l1 (b :: a :: l2)) l3.
intros f rec a b l1; elim l1; simpl; auto; clear l1.
intros l2 l3 H.
repeat rewrite app_ass; simpl.
rewrite rec_det_r; auto.
intros a0 b0 l'1 l'2; simpl; rewrite plus_0_r.
intros H1; apply H; auto.
setoid ring.
intros a1 l1 Rec l2 l3 H.
assert (tmp: forall a b l4, (app (app l2(  a :: b :: l3))  l4) = ((app l2  (a :: b :: (app l3  l4))))).
intros; rewrite app_ass; auto.
repeat rewrite <- app_ass; rewrite H.
rewrite length_app; auto with zarith.
rewrite Rec.
intros a2 b1 l'1 l'2; rewrite length_app; simpl.
rewrite (fun x => plus_comm x 1).
intros H1; apply H.
rewrite H1; auto with zarith.
setoid ring.
Qed.

Theorem det_aux_t0: forall n a b  l1 l2, (n = 2 + length l1 + length l2)%nat  -> 
    det_aux n (app l1  (a :: b :: l2))!= - det_aux n (app l1   (b :: a :: l2)).
intros n; elim n; simpl; auto.
intros; discriminate.
intros n1 Rec a b l1 l2 H.
rewrite rec_det_t; auto.
intros a2 b1 l'1 l'2; simpl; rewrite plus_0_r.
intros H1; rewrite <- H1 in H; clear H1.
rewrite Rec; auto.

injection H; intros; rewrite plus_comm; auto.
setoid ring.
setoid ring.
Qed.

Theorem det_aux_t: forall n a b  l1 l2 l3, (n = 2 + length l1 + length l2 + length l3)%nat  -> 
    det_aux n (app l1 (app  (a :: l2)  (b :: l3))) != - det_aux n (app l1 (app   (b :: l2) ( a :: l3))).
intros n a b l1 l2; generalize a b l1; elim l2; clear a b l1 l2; simpl; auto.
intros a b l1 l2; rewrite plus_0_r; intros H1; apply det_aux_t0; auto.
intros a1 l2 Rec a2 b1 l1 l3 H.
rewrite (@det_aux_t0 n a2 a1 l1 (app l2 (b1::l3))).
rewrite length_app; simpl; auto with zarith.
assert (h1: det_aux n (app l1 (b1 :: a1 :: app l2 (a2 :: l3))) !=
- det_aux n (app l1 (a1 :: b1 :: app l2 (a2 :: l3))));
[apply det_aux_t0 with (b := a1)| rewrite h1].
rewrite length_app; simpl; auto with zarith.

generalize (Rec a2 b1 (app l1 ( a1 ::   nil)) l3); repeat rewrite app_ass; simpl.
intros H1;rewrite H1 ; auto.

rewrite length_app; simpl; auto with zarith.
setoid ring.
Qed.

Theorem det_t: forall a b l1 l2 l3, det (app l1 (app  (a :: l2)  (b :: l3))) != 
- det (app l1 (app   (b :: l2)  (a :: l3))).
intros; unfold det.
repeat rewrite length_app;simpl length.
case ( even_odd_dec ( length l1 + (S (length l2) + S (length l3))));intro;
repeat (rewrite <- det_aux_t; auto;try omega; try setoid ring).
Qed.

Theorem det_m: forall a b c d l1 l2, 
    det (app l1  (add (scal a b) (scal c d):: l2)) != a !* det (app l1 ( b :: l2))  + c !* det ( app l1  (d :: l2)).
intros a b c d l1 l2; case l1.
simpl; apply det_m0 .
intros a1 l3.
generalize (det_t a1 (add (scal a b) (scal c d))   nil l3 l2); simpl; intros tmp; rewrite tmp; clear tmp.
rewrite det_m0.
generalize (det_t b a1   nil l3 l2); simpl; intros tmp; rewrite tmp; clear tmp.
generalize (det_t d a1   nil l3 l2); simpl; intros tmp; rewrite tmp; clear tmp.
repeat rewrite Pscal_Pmul_l;setoid ring.
Qed.

Theorem det_zero: forall a l1 l2 l3, det (app l1 (app  (a :: l2)  (a :: l3))) != P0.
intros a l1 l2 l3.
case (Pmul_integral (P1+P1) (det (app l1 (app  (a :: l2) (a :: l3))))); auto.
assert (tmp: forall x, (P1 + P1)* x != x + x).
intros;setoid ring.
rewrite tmp; clear tmp.
assert (det (app l1 (app (a :: l2) (a :: l3))) + det (app l1 (app (a :: l2) (a :: l3))) != 
det (app l1 (app (a :: l2) (a :: l3))) + - det (app l1 (app (a :: l2) (a :: l3)))).
apply Padd_ext; [setoid ring| apply det_t].
rewrite H;setoid ring.
intros; absurd (P1 + P1 != P0 );auto; apply P2_diff_P0.
Qed.


Definition  even_odd_dec : forall n, {even n} + {odd n}.
induction n.
auto with arith.
elim IHn; auto with arith.
Defined.



Theorem rec_det_diag: forall f rec l1 l2 a1 a2,
  (forall a, In a l1 -> f a != P0) -> f a2 != P0 ->
   rec_det f rec (app l1  (a1::a2::nil)) l2 != match even_odd_dec (length l1) with 
      left _ => (f a1) * rec (app l2 (app l1 (a2::nil)))
    | right _ => - (f a1) * rec (app l2 (app l1 ( a2::nil))) end.
intros f rec l1 l2 a1 a2; generalize l2; elim l1; clear l1 l2.
intros l2 H1 H2.
simpl.
Pcsimpl.
rewrite H2;rewrite Psub_def;setoid ring.
intros a l3 Rec l2 H1 H2;simpl rec_det.
rewrite Rec; auto with datatypes zarith.
rewrite (H1 a); auto with datatypes zarith.
rewrite app_ass;simpl length.
case (even_odd_dec (length l3));intros.
case(even_odd_dec (S (length l3))).
intros.
inversion e0.
absurd (even (length l3));auto.
red;intros;apply (not_even_and_odd (length l3));auto.
intros;simpl;setoid ring.
case(even_odd_dec (S (length l3)));intros.
simpl;setoid ring.
inversion o0.
absurd (even(length l3));auto.
red;intros;apply (not_even_and_odd (length l3));auto.
Qed.


Theorem list_last_element: 
  forall (A: Set) (l : list A),
  l = nil \/ exists l1, exists a1, l = (app l1 (a1 :: nil)).
intros A l; elim l; simpl; auto.
intros a1 l1 [HH | (l2, (a2, HH))]; auto; right.
exists l1; exists a1; rewrite HH; auto.
exists (a1::l2); exists a2; rewrite HH; auto.
Qed.

Theorem nth_app_l: forall (A: Set) a n (l1 l2: list A), (n < length l1)%nat -> nth n (app l1  l2) a = nth n l1 a.
intros A a n l1; generalize n; elim l1; clear n l1.
simpl; intros n l2 H;contradict H; auto with arith.
intros a1 l1 Rec n l2; case n; simpl; auto.
intros n1 H; apply Rec; auto with arith.
Qed.

Theorem nth_app_r: forall (A: Set) a n (l1 l2: list A), (length l1 <= n)%nat -> nth n (app l1 l2) a = nth (n - length l1) l2 a.
intros A a n l1; generalize n; elim l1; clear n l1.
simpl; intros n l2 H; eq_tac; auto with zarith.
intros a1 l1 Rec n l2; case n; simpl.
intros H; contradict H; auto with arith.
intros n1 H; apply Rec; auto with arith.
Qed.

Theorem in_nth_inv: forall (A: Set) (a: A) l p, (In a l) -> exists i, (i < length l)%nat /\  a = nth i l p.
intros A a l p; elim l; simpl; clear l.
intros tmp; case tmp.
intros a1 l1 Rec1 [HH1 | HH1].
exists 0%nat; auto with arith.
case Rec1; auto.
intros i (Hi1, Hi2).
exists (S i); auto with arith.
Qed.

Definition Zpolpower_nat (i:nat):= match (even_odd_dec i) with
   left _ => Pc c1
   | right _ => - (Pc c1) end.

Opaque phi.


Theorem det_aux_diag: forall l a n p,
  (forall i:nat, (1 < i)%nat -> (i <= n)%nat -> phi deg  i a != P0) -> 
  (forall (i j:nat), (j < i)%nat  -> (i < n)%nat -> phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat -> (i < length l )%nat -> phi deg (S (S i)) (nth i l p) != (Zpolpower_nat  i))->
  (length l + 1 = n)%nat -> det_aux n (app l  (a :: nil)) != phi deg 1 a.
intros l a n p; generalize l; elim n;simpl;clear l n. 
intros l _ _ _ H1; rewrite plus_comm in H1; discriminate.
intros n Rec l H0 H2 H3 H4.
case (list_last_element _ l); intros H5.
rewrite H5; simpl.
replace n with 0%nat;simpl.
Pcsimpl.
(*rewrite Pol_sub_c0;rewrite Pmul_Rat_c1;setoid ring.*)
apply eq_add_S.
rewrite <- H4; rewrite H5; simpl; auto.
case H5; clear H5; intros l2 (a1, H5).
subst l.
assert (Eq0: n = (S (pred n))).
generalize H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.
case n; simpl; auto with zarith.
assert (Eq1: pred n = (length l2)).
apply eq_add_S; apply eq_add_S.
rewrite <- Eq0; rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.
rewrite app_ass;simpl.
rewrite rec_det_diag; simpl; auto with zarith.

intros a2 HH.
case (in_nth_inv _ a2 l2 p); auto.
intros i (Hi1, Hi2).
rewrite Eq0.
replace a2 with (nth i (app l2 ( a1 :: nil)) p).
apply H2; auto with arith.
rewrite Eq1; auto.
rewrite nth_app_l; auto with arith.
case (even_odd_dec (length l2));intros.

rewrite Rec; auto.

intros i j HH HH1.
rewrite <- (H2 i j); auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth j l2 p) (nth j (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l.
apply lt_le_trans with (1 := HH).
rewrite <- Eq1; clear Eq1; rewrite Eq0 in HH1; auto with arith.

intros i HH HH1; rewrite <- H3; auto. 
rewrite length_app; simpl; auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth i l2 p) (nth i (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l; auto.
apply eq_add_S; auto with arith.
rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.

rewrite Eq0.
replace a1 with (nth (pred n) (app l2 (a1 :: nil)) p).
rewrite H3; auto with zarith.
rewrite Eq1.
unfold Zpolpower_nat.
case (even_odd_dec (length l2));intros.
apply Pmul_1_l.
elim  (not_even_and_odd (length l2));trivial.
rewrite nth_app_r.
rewrite Eq1; rewrite <- minus_n_n; auto.
rewrite Eq1; auto with arith.

rewrite Rec; auto.

intros i j HH HH1.
rewrite <- (H2 i j); auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth j l2 p) (nth j (app l2 (a1 :: nil)) p)); auto.
setoid ring.

apply sym_equal; apply nth_app_l.
apply lt_le_trans with (1 := HH).
rewrite <- Eq1; clear Eq1; rewrite Eq0 in HH1; auto with arith.

intros i HH HH1; rewrite <- H3; auto. 
rewrite length_app; simpl; auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth i l2 p) (nth i (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l; auto.
apply eq_add_S; auto with arith.
rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.

rewrite Eq0.
replace a1 with (nth (pred n) (app l2 (a1 :: nil)) p).
rewrite H3; auto with zarith.
rewrite Eq1.
unfold Zpolpower_nat.
case (even_odd_dec (length l2));intros.
elim  (not_even_and_odd (length l2));trivial.
setoid ring.
rewrite nth_app_r.
rewrite Eq1; rewrite <- minus_n_n; auto.
rewrite Eq1; auto with arith.
Qed.


Theorem det_diag: forall l a p,
  (forall i, (1 < i)%nat -> (i <= length l + 1)%nat -> phi  deg i a != P0)-> 
  (forall i j, (j < i)%nat-> (i < length l + 1)%nat -> phi deg (S (S i)) (nth j l p) != P0)->
  (forall i, (i < length l )%nat-> phi deg (S (S i)) (nth i l p) != (Zpolpower_nat i))->
   det (app l ( a :: nil)) != phi deg 1 a.
intros l a p H2 H3 H4.
unfold det; rewrite length_app.
apply det_aux_diag with p; simpl; auto with arith.
Qed.

(*
Ltac list_blast := simpl;try (repeat rewrite app_ass);try (repeat rewrite app_comm_cons);
try (repeat rewrite app_ass);simpl;try reflexivity.


Lemma nth_app_cons : forall A n l1 l2 a b, 
length l1 = n -> @nth A n (app l1 (a::l2)) b = a.
Proof.
intro A;induction n;intros l1 l2 a b Defn.
replace l1 with (@nil A);[reflexivity|destruct l1].
trivial.
discriminate.
destruct l1;simpl.
discriminate.
apply IHn.
simpl in Defn;auto with arith.
Qed.


Ltac falso := apply False_ind;omega.


Theorem det_aux_trig: forall k1 k2 l1 l2  n p c,
  length l1 = k1 -> length l2 = k2 -> (k1 + k2)%nat = n ->
  (forall i:nat, (1 < i)%nat -> (i <= k1)%nat ->
    forall j, j < k2 -> phi deg  i (nth j l2 p) != P0) ->
 
  (forall (i j:nat), (j < i)%nat  -> (i < k1)%nat ->
    phi deg (S (S i)) (nth j l1 p) != P0) ->

  (forall i:nat, (i < n)%nat -> (i < length l1 )%nat ->
    phi deg (S (S i)) (nth i l1 p) != c)->
  det_aux n (app l1 l2) != (Pol_pow c (N_of_nat k1))*(det_aux n l2).
Proof.
intro k1;elim k1.
intros k2 l1 l2 n p c H1 H2 H3.
destruct l1.
simpl in H3.
subst k2;clear H1.
intros H4 H5 H6.
simpl.
setoid ring.
simpl in H1;discriminate.
intros n Rec k2 l1 l2 n0 p c H1 H2 H3 H4 H5 H6.
case (list_last_element _ l1).
intro H7.
subst l1.
discriminate.
intro H7.
case H7.
clear H7;intros l3 (a1,H7).
subst l1.
replace (app (app l3 (a1 :: nil)) l2) with (app l3 (a1::l2)) by list_blast.
assert (l3_length : length l3 = n) by 
(rewrite length_app in H1;simpl in H1;omega).
rewrite (Rec (S k2) l3 (a1::l2) n0 p c);trivial.
simpl;omega.
omega.
intros i H7 H8 j H9.
destruct j.
simpl.
replace a1 with (nth (length l3) (app l3 (a1::nil)) p).
destruct i;try destruct i;try falso.
apply H5.






Goal forall n, forall l:list nat, length l = S n -> False.
intros;case(list_last_element _ l).
intro H1.
subst l.
subst l1.
simpl.




intros l a n p.
generalize l.
 elim n.
simpl.
clear l n.
intros l _ _ _ H1.
rewrite plus_comm in H1; discriminate.
clear l n.
intros n Rec l H0 H2 H3 H4.
case (list_last_element _ l).
 intros H5.
rewrite H5; simpl.
replace n with 0%nat;simpl.
Pcsimpl.
(*rewrite Pol_sub_c0;rewrite Pmul_Rat_c1;setoid ring.*)
apply eq_add_S.
rewrite <- H4; rewrite H5; simpl; auto.
intro H5.
case H5.
 clear H5; intros l2 (a1, H5).
subst l.
assert (Eq0: n = (S (pred n))).
generalize H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.
case n; simpl; auto with zarith.
assert (Eq1: pred n = (length l2)).
apply eq_add_S; apply eq_add_S.
rewrite <- Eq0; rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.
rewrite app_ass;simpl.
rewrite rec_det_diag; simpl; auto with zarith.

intros a2 HH.
case (in_nth_inv _ a2 l2 p); auto.
intros i (Hi1, Hi2).
rewrite Eq0.
replace a2 with (nth i (app l2 ( a1 :: nil)) p).
apply H2; auto with arith.
rewrite Eq1; auto.
rewrite nth_app_l; auto with arith.
case (even_odd_dec (length l2));intros.

rewrite Rec; auto.

intros i j HH HH1.
rewrite <- (H2 i j); auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth j l2 p) (nth j (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l.
apply lt_le_trans with (1 := HH).
rewrite <- Eq1; clear Eq1; rewrite Eq0 in HH1; auto with arith.

intros i HH HH1; rewrite <- H3; auto. 
rewrite length_app; simpl; auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth i l2 p) (nth i (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l; auto.
apply eq_add_S; auto with arith.
rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.

rewrite Eq0.
replace a1 with (nth (pred n) (app l2 (a1 :: nil)) p).
rewrite H3; auto with zarith.
rewrite Eq1.
unfold Zpolpower_nat.
case (even_odd_dec (length l2));intros.
apply Pmul_1_l.
elim  (not_even_and_odd (length l2));trivial.
rewrite nth_app_r.
rewrite Eq1; rewrite <- minus_n_n; auto.
rewrite Eq1; auto with arith.

rewrite Rec; auto.

intros i j HH HH1.
rewrite <- (H2 i j); auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth j l2 p) (nth j (app l2 (a1 :: nil)) p)); auto.
setoid ring.

apply sym_equal; apply nth_app_l.
apply lt_le_trans with (1 := HH).
rewrite <- Eq1; clear Eq1; rewrite Eq0 in HH1; auto with arith.

intros i HH HH1; rewrite <- H3; auto. 
rewrite length_app; simpl; auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth i l2 p) (nth i (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l; auto.
apply eq_add_S; auto with arith.
rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.

rewrite Eq0.
replace a1 with (nth (pred n) (app l2 (a1 :: nil)) p).
rewrite H3; auto with zarith.
rewrite Eq1.
unfold Zpolpower_nat.
case (even_odd_dec (length l2));intros.
elim  (not_even_and_odd (length l2));trivial.
setoid ring.
rewrite nth_app_r.
rewrite Eq1; rewrite <- minus_n_n; auto.
rewrite Eq1; auto with arith.
Qed.
*)


Theorem rec_det_morph : forall f rec  l1 l1',
 l1 *= l1' ->  forall l2 l2' , l2 *= l2' ->
(forall l1 l1' , l1*=l1' -> rec l1 != rec l1' ) ->
(forall a b, a != b -> f a != f b) ->
rec_det f rec l1 l2 != rec_det f rec l1' l2'.
Proof.
intros f rec l1 l1'.
induction 1; intros m2 m2';induction 1;simpl;intros.
reflexivity.
reflexivity.
rewrite (H2 _ _ H).
rewrite (H1 _ _ H0).
rewrite (IHPol_list_equiv (a1::nil) (a2::nil));
try constructor;trivial.
constructor.
reflexivity.

rewrite (H4 a1 a2 H).
rewrite (H3 (a0::(app l0 l1)) (a3::(app l3 l2)));[constructor;trivial|idtac].
rewrite H2;rewrite H0;reflexivity.
rewrite (IHPol_list_equiv (a0::app l0 (a1 :: nil)) (a3 :: app l3 (a2 :: nil)));trivial.
 constructor;trivial.
apply app_morph;trivial.
constructor;trivial.
constructor.
reflexivity.
Qed.


Add Morphism phi  with signature (@eq nat) ==>(@eq nat) ==> Pol_Eq ==> Pol_Eq as phi_Morphism.
Admitted.
(*
intros d n P Q;unfold phi;case (le_gt_dec (d+2)n); intros.
Proof.
reflexivity. 
case n;simpl.
reflexivity.
intros;case n0; trivial.
intros;toto;
intros;simpl;
rewrite H;setoid ring.
Show Script.
Qed.
*)



Theorem det_aux_morph : forall n, (forall l1 l2, l1 *= l2 ->  det_aux n l1 != det_aux n l2).
Proof.
induction n;intros l1 l2 H;induction H;simpl;try reflexivity.
apply Psub_comp.
rewrite H.
rewrite (IHn l1 l2 H0).
reflexivity.
apply rec_det_morph;try assumption.
constructor;[assumption|constructor].
intros a b Hab;rewrite Hab;reflexivity.
Qed.


Add Morphism det with signature Pol_list_equiv ==> Pol_Eq as det_morph.
Proof.
intros l1 l2 H.
unfold det.
rewrite (Pol_list_equiv_length l1 l2 H).
apply det_aux_morph;assumption.
Qed.


Theorem det_sum_simpl : forall l1 l2 l3 a b c,
det (app l1 (app (((b + (c !* a)))::l2) (a::l3))) != det (app l1 (app (b::l2) (a::l3))).
Proof.
intros.
rewrite <- (app_comm_cons l2 (a::l3) (b+( c !* a))).
assert (G: app l1 (b +(scal  c a) :: app l2 (a :: l3)) *= app l1 (((scal c1 b) + (scal c a)) :: app l2 (a :: l3))).
apply app_morph.
reflexivity.
constructor.
2:reflexivity.
unfold scal;Pcsimpl.
rewrite G.
rewrite det_m.
Pcsimpl.
repeat rewrite app_comm_cons.
rewrite det_zero.
Pcsimpl;setoid ring.
Qed.


Theorem det_scal : forall l1 l2 a c,
det (app l1 ((c !* a) :: l2)) != c !* (det (app l1 (a::l2))).
Proof.
intros l1 l2 a c.
transitivity  (det (app l1 (((c !* a) + (c0 !* P1)) :: l2))).
apply det_morph;apply app_morph.
reflexivity.
constructor.
unfold scal;Pcsimpl;setoid ring.
reflexivity.
fold (scal c a).
fold (scal c(det (app l1 (a :: l2)))).
fold (scal c0 P1).
rewrite det_m.
unfold scal;Pcsimpl;setoid ring.
Qed.




End det.



