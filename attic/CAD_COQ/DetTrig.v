
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)

Require Import Tactic.
Require Import CAD_types.
Require Import Utils.
Require Import Setoid.
Require Import ZArith.
Require Import Even.
Require Import Pol_ring.
(*Require Import phi.*)
Require Import Mylist.
Require Import PDet.
Require Import PolMonOSum.
(* version setoid de In *)
(* on generalise lus que ca dans Myllist?*)
Require Import phi.

Definition P1 := Eval compute in (X*X*X).
Definition P2 := Eval compute in (X*X).
Eval compute in (det phi 3 (P1::P2::nil)).


Hypothesis cpow_1 : forall c, cpow c 1%N ==c.
Hypothesis cintegral : forall a b, czero_test (a **b) = orb (czero_test a) (czero_test b).



Set Implicit Arguments.


Lemma N_of_nat_add: forall n m, N_of_nat (n + m)  = (N_of_nat n +  N_of_nat m)%N.
Admitted.



Fixpoint PIn(P:Pol)(l:list Pol){struct l}:Prop:=
  match l with
   |nil => False
   |b :: m => b != P \/ PIn P m
  end.



(* ca sert ca?oui*)
Add Morphism (@cons Pol)
 with signature Pol_Eq ==> Pol_list_equiv ==>Pol_list_equiv as cons_comp.
intros.
constructor;trivial.
Qed.


(* trivial lemma specifying the In predicate of st lib List*)
Lemma PIn_app :forall a l, PIn a l -> exists l1, exists l2, l *= app l1 (a::l2).
Proof with (trivial;reflexivity).
intros  a l H_In.
induction l.
elim H_In.
elim H_In;intro G.
exists (@nil Pol);exists l.
simpl;rewrite G...
elim (IHl G);intros l3 Hex.
elim Hex.
intros l4 Heq.
exists (a0:: l3).
exists l4.
simpl.
rewrite Heq...
Qed.

Lemma PIn_PIn_app_r : forall P l1, PIn P l1 -> forall l2, PIn P (app l1 l2).
Proof.
intros P;induction l1;intros H l2;elim  H;rewrite <- app_comm_cons;intro G.
left;trivial.
right.
apply (IHl1 G).
Qed.

Lemma PIn_PIn_app_l : forall P l2 l1, PIn P l1 -> PIn P (app l2 l1).
Proof.
intros P;induction l2;intros l1 H.
auto.
rewrite <- app_comm_cons.
right.
apply (IHl2 l1 H).
Qed.



Add Morphism PIn with signature Pol_Eq ==> Pol_list_equiv ==> iff as PIn_comp.
intros P Q Heq  l1 l2 Hequiv.
induction Hequiv;simpl.
reflexivity.
split;intro G;inversion G.
left.
rewrite <- H.
rewrite <- Heq;auto.
right.
rewrite <- IHHequiv;auto.
left.
rewrite  H.
rewrite  Heq;auto.
right.
rewrite  IHHequiv;auto.
Qed.



Notation "| l |":= (length l)(at level 30, no associativity).






Lemma  cpow_0 : forall c, cpow c 0%N == c1.
Admitted.




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



(* det_aux1 and rec_det sat their fixpont eq *)





Fixpoint det_aux1(phi:nat -> nat -> Pol -> Pol)(deg : nat)(n : nat)(l : list Pol)
  {struct n}:Pol:=
  if eq_nat_dec (length l) n then 
    (match n with
      O => P1
      | S n1 => rec_det (phi deg n) (det_aux1 phi deg n1) l nil
    end)
    else P0.





Lemma det_aux1_eq : forall phi deg n l,
  det_aux1 phi deg n l = 
  if eq_nat_dec (length l) n then 
    (match n with
      O => P1
      | S n1 => rec_det (phi deg n) (det_aux1 phi deg n1) l nil
    end)
    else P0.
Proof. 
intros;case n;reflexivity.
Qed.


Lemma rec_det_eq : forall f rec l1 l2,
rec_det f rec l1 l2 = 
  match l1 with
    nil =>  P0 
  | a:: l3 => f a * rec (app l2 l3)  - rec_det f  rec  l3 (app l2 (a::nil)) 
  end.
Proof.
intros.
case l1;reflexivity.
Qed.


(* to ease setoid rw...*)


Lemma Oprod_l : forall x y, x != P0 -> x * y != P0.
intros x y H.
rewrite H.
setoid ring.
Qed.

    
Lemma Oprod_r : forall x y, x != P0 -> y * x != P0.
intros x y H.
rewrite H.
setoid ring.
Qed.

Lemma Ominus : forall x y, x !=P0 -> y !=P0 -> x - y != P0.
intros x y H1 H2.
rewrite H1;rewrite H2;setoid ring.
Qed.

Lemma minus_simpl : forall x y, x != P0 -> x - y != P0 -> y != P0.
intros x y H1 H2.
rewrite H1 in H2.
setoid_replace y with (y + P0);[idtac| setoid ring].
rewrite <- H2.
setoid_replace (y + (P0 -y)) with P0;[rewrite H2|idtac];setoid ring.
Qed.


(* destruction of det_aux1 *)
Ltac case_det_aux1 n l := 
rewrite det_aux1_eq;induction (eq_nat_dec (length l) n);try reflexivity.


(* nth of app lists*)
Lemma nth_app_l : forall A l1 l2 p j,
  j < @length A l1 -> nth j (app l1 l2) p = nth j l1 p.
intros A;induction l1;intros l2 p j G.
simpl in G;apply False_ind;omega.
destruct j.
reflexivity.
simpl.
simpl in G.
apply IHl1;omega.
Qed.

Lemma nth_ex : forall A l p j,
j >= @length A l -> nth j l p = p.
Proof.
intros A;induction l;intros p j H.
destruct j;reflexivity.
destruct j.
simpl in H;apply False_ind;omega.
simpl.
apply IHl.
simpl in H;omega.
Qed.

Lemma nth_app_r :  forall A l1 l2 p j,
  j >= @length A l1 -> nth j (app l1 l2) p = nth (j - (length l1)) l2 p.
intros A;induction l1;intros l2 p j G.
replace (j - (@length A nil))%nat with j;auto with arith.
destruct j.
simpl in G;apply False_ind;omega.
destruct l2.
repeat rewrite nth_ex;simpl in * |- *;trivial;try omega.
rewrite <- app_nil_end;trivial.
replace (S j - (|a :: l1 |))%nat with (j - (|l1|))%nat;[idtac|reflexivity].
rewrite <- IHl1.
reflexivity.
simpl in G;omega.
Qed.




(* base case*)

(* surtout pas! bug setoid?
Add Morphism phi  with signature  (@eq nat) ==> Pol_Eq ==> Pol_Eq as toto.
intros; apply phi_Morphism;trivial.
Qed.*)



Add Morphism phi  with signature (@eq nat) ==> (@eq nat) ==> Pol_Eq ==> Pol_Eq as toto.
intros; apply phi_Morphism;trivial.
Qed.


Section DET_TRIG.

(*Variable phi : nat -> nat ->Pol ->Pol.


Hypothesis phi_m: forall deg n a b c d,
 phi deg n (add (scal a b) (scal c  d)) != a !* phi deg n b + c !* phi deg n d.
Hypothesis phi_morph:forall (x x0 : nat) (x1 x2 : pol), x1 != x2 -> phi x x0 x1 != phi x x0 x2.

Add Morphism phi  with signature (@eq nat) ==>(@eq nat) ==> Pol_Eq ==> Pol_Eq as phi_Morphism.
exact phi_morph.
Qed.

*)


Lemma rec_det_ext: forall (d1 d2:nat) f1 f2 f3 f4 ,
(forall (n:nat) P, f1 d1 n P != f2 d2 n P) -> 
      (forall l : list pol, f3 l != f4  l )-> 
forall m  l  l2, 
 rec_det  (f1 d1 m) f3  l l2 != rec_det (f2 d2 m) f4 l l2.
induction l.
simpl.
intros;Pcsimpl.
intros;simpl.
rewrite H.
rewrite H0.

rewrite IHl;auto.
setoid ring.
Qed.


Lemma  det_aux_f_comp : forall m d1 d2 f1 f2,
(forall n P, f1 d1 n P != f2 d2 n P)
 -> forall  l , det_aux  f1 d1 m l != det_aux f2 d2 m l. 
induction m.
intros;simpl;Pcsimpl.
simpl.
intros.
apply  rec_det_ext;auto.
Qed.



Lemma  det_f_comp : forall d1 d2 f1 f2,
(forall n P, f1 d1 n P != f2 d2 n P)
 -> forall l, det f1 d1 l != det f2 d2 l. 
intros; unfold det;apply det_aux_f_comp;auto.
Qed.


Definition Pincl (l m:list Pol) := forall a, PIn a l -> PIn a m.
Hint Unfold Pincl : Plist.


Lemma Pincl_refl : forall l, Pincl l l.
Proof. 
intros;auto with Plist.
Qed.

Hint Resolve Pincl_refl: Plist.

Lemma Pincl_tl : forall a l m, Pincl l m -> Pincl l (a :: m).
Proof. 
intros;auto with Plist.
unfold Pincl.
intros P HP.
simpl;right.
auto.
Qed.

Hint Immediate Pincl_tl:Plist.

Lemma Pincl_tran : forall l m n:list Pol, Pincl l m -> Pincl m n -> Pincl l n.
Proof. 
unfold Pincl;intros l m n Hlm Hmn a Ha.
auto.
Qed.

Lemma Pincl_appl : forall l m n:list Pol, Pincl l n -> Pincl l (app n m).
Proof. 
unfold Pincl;intros l m n Hln a Ha.
apply PIn_PIn_app_r.
auto.
Qed.

Hint Immediate Pincl_appl : Plist.

Lemma Pincl_appr : forall l m n:list Pol, Pincl l n -> Pincl l (app m n).
Proof. 
unfold Pincl;intros l m n Hln a Ha.
apply PIn_PIn_app_l.
auto.
Qed.
	
Hint Immediate Pincl_appr:Plist.

Lemma Pincl_cons :
 forall a l m, PIn a m -> Pincl l m -> Pincl (a :: l) m.
Proof. 
unfold Pincl in |- *; simpl in |- *; intros a l m H H0 a0 H1.
elim H1;intro G.
rewrite <- G;assumption.
apply (H0 _ G).
Qed.

Hint Resolve Pincl_cons :Plist.



Lemma PIn_app_PIn:forall l1 l2 P, PIn P (app l1 l2) -> PIn P l1 \/ PIn P l2.
Proof with auto.
induction l1;destruct l2;intros P H;simpl in H...
rewrite<-  (app_nil_end l1) in H;left...
elim H;intro G.
left;constructor...
elim (IHl1 _ _ G);intro G'.
left;simpl;right...
right...
Qed.


Lemma Pincl_app : forall l m n:list Pol, Pincl l n -> Pincl m n -> Pincl (app l  m) n.
Proof. 
  unfold Pincl in |- *; simpl in |- *; intros l m n H H0 a H1.
  elim (PIn_app_PIn _ _ _ H1).
  apply H.
  apply H0.
Qed.

Hint Resolve Pincl_app : Plist.



Lemma strong_rec_det_ext: forall (d1 d2:nat) f1 f2 f3 f4 l1 l2,
(forall (n:nat) P, PIn P (app l2 l1) -> f1 d1 n P != f2 d2 n P) ->
(forall l, Pincl l (app l2 l1) -> f3 l != f4 l)->
forall m ,
 rec_det  (f1 d1 m) f3  l1 l2 != rec_det (f2 d2 m) f4 l1 l2.
induction l1.
simpl.
intros;Pcsimpl.
intros;simpl.
rewrite H.
apply PIn_PIn_app_l.
simpl;left;reflexivity.
rewrite H0.
apply Pincl_app.
apply Pincl_appl.
apply Pincl_refl.
apply Pincl_appr.
apply Pincl_tl;apply Pincl_refl.
rewrite IHl1;auto.
intros n P HP.
apply H.
rewrite app_ass in HP.
rewrite <- app_comm_cons in HP.
simpl in HP.
assumption.
intros l Hl.
apply H0.
rewrite app_ass in Hl.
rewrite <- app_comm_cons in Hl.
simpl in Hl.
assumption.
setoid ring.
Qed.




Lemma  strong_det_aux_f_comp : forall m d1 d2 f1 f2 l,
(forall n P, PIn P l -> f1 d1 n P != f2 d2 n P)
 -> det_aux  f1 d1 m l != det_aux f2 d2 m l.
induction m.
intros;simpl;Pcsimpl.
simpl.
intros.
apply  strong_rec_det_ext.
simpl.
assumption.
intros l0 Hl0.
apply IHm.
intros n P HP.
apply H.
simpl in Hl0.
unfold Pincl in Hl0.
apply Hl0.
assumption.
Qed.


Lemma strong_det_f_comp : forall d1 d2 f1 f2 l,
(forall n P, PIn P l -> f1 d1 n P != f2 d2 n P)
 -> det f1 d1 l != det f2 d2 l.
Proof.
intros d1 d2 f1 f2 l H.
unfold det.
apply strong_det_aux_f_comp.
assumption.
Qed.


(* * minors are nul*)

Theorem minor: forall m n l p deg b x,
(forall i:nat, (1 < i)%nat -> (i <= S n)%nat -> phi deg i x != P0) ->
  (forall i:nat, (1 < i)%nat -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < S (n-j) -> i>1  -> (j < n)%nat -> 
    phi deg i (nth j l p) != P0) ->
  PIn b l -> n = length l -> m > 1 -> m <= n -> 
  det_aux1 phi deg (S m) (x::l) != P0. 
induction m;intros n l p deg b x H1 H2 H3 H4 H5 H6 H7.
apply False_ind;omega.
destruct l.
simpl in H5; apply False_ind;omega.
case_det_aux1 (S (S m)) (x :: p0 :: l).
rewrite rec_det_eq.
apply Ominus.
rewrite H1;auto with arith;setoid ring.
inversion H4.
rewrite rec_det_eq.
apply Ominus.
rewrite H;rewrite H2;auto with arith;setoid ring.
simpl app.

assert (Aux : forall l1 l2,
 l = app l2 l1 ->
rec_det (phi deg (S (S m))) (det_aux1 phi deg (S m)) l1 (x::p0::l2)!=P0).
induction l1;intros l2 G.
reflexivity.
rewrite rec_det_eq.
apply Ominus.
simpl app.

induction (le_gt_dec 2 m).
rewrite (IHm  m (p0::app l2 l1) p deg b x);intuition.
destruct j.
replace (nth 0 (p0 ::app l2 l1)) with (nth 0 (p0::l));trivial.
apply H3;auto with arith;omega.
replace (nth (S j) (p0 ::app l2 l1) p) with (nth j (app l2 l1) p);trivial.
rewrite G in H3.
induction (le_gt_dec (length l2) j).
rewrite nth_app_r;trivial.
replace (nth (j - (length l2)) l1 p) with (nth (S j - (length l2)) (a0::l1) p).
rewrite <- (nth_app_r l2 (a0::l1) p);auto with arith.
replace  (nth (S j) (app l2 (a0 :: l1)) p) with 
 (nth (S (S j)) (p0 ::(app l2 (a0 :: l1))) p);trivial.
apply H3;omega.
replace (S j - (length l2))%nat with (S (j - (length l2)))%nat;try reflexivity.
omega.
rewrite nth_app_l;try omega.
rewrite <- (nth_app_l  l2 (a0::l1));trivial.
replace  (nth j (app l2 (a0 :: l1)) p) with  (nth (S j) (p0::(app l2 (a0 :: l1))) p);trivial.
apply H3;auto with arith;omega.
left;trivial.
transitivity (length (app l2 (a0::l1))).
rewrite <- G.
simpl in *|-*;omega.
simpl;repeat rewrite length_app;simpl;auto with arith.
setoid ring.

generalize (app l2 l1);intro l'.
destruct m.
case_det_aux1 1 (x::p0::l').
simpl in a1;discriminate.
setoid ring.
destruct m.
case_det_aux1 2 (x::p0::l');[idtac|setoid ring].
destruct l';[idtac|discriminate].
rewrite rec_det_eq.
apply Oprod_r.
apply Ominus.
rewrite H1;try omega;setoid ring.
rewrite rec_det_eq.
apply Ominus.
rewrite H;rewrite H2;try omega;setoid ring.
reflexivity.
apply False_ind;omega.
simpl app.
apply IHl1.
rewrite app_ass.
trivial.
apply Aux;trivial.
fold PIn in H.
simpl app.
destruct m.
apply False_ind;omega.
destruct m.
rewrite rec_det_eq.
destruct l;[simpl in a;discriminate|destruct l;[idtac|simpl in a;discriminate]].
apply Ominus.
simpl app.
rewrite det_aux1_eq.
case (eq_nat_dec (|x::p1::nil|) 2);intro G;
[rewrite rec_det_eq|apply False_ind;elim G].
apply Oprod_r.
apply Ominus.
rewrite H1;auto with arith;setoid ring.
rewrite rec_det_eq.
apply Ominus;[idtac|reflexivity].
elim H;[intro G1|apply False_ind].
rewrite G1;rewrite H2;auto with arith;setoid ring.
reflexivity.
rewrite rec_det_eq.
apply Ominus;try reflexivity.
simpl app.
case_det_aux1 2 (x :: p0 :: nil).
apply Oprod_l;try setoid ring.
case H;[intro G;rewrite G|apply False_ind].
apply H2;auto with arith.
setoid ring.
assert (Aux : forall l1 l2,
p0::l = app l2 l1 -> rec_det (phi deg (S (S(S (S m))))) (det_aux1 phi deg (S (S (S m)))) l1 (x::l2) !=P0).
induction l1;intros l2 G.
reflexivity.
rewrite rec_det_eq.
apply Ominus.
assert (G1 : a0 != b \/(PIn b l1)\/(PIn b l2)). 
rewrite G in H4.
elim (PIn_app_PIn l2 (a0 :: l1) b H4);intro G1.
right;right;trivial.
simpl in G1.
intuition.
elim G1;clear G1;intro G2.
rewrite G2;rewrite H2;auto with arith;setoid ring.
simpl app.
rewrite (IHm (S (S m)) (app l2 l1) p deg b x);auto.
intros;apply H1;omega.
intros;apply H2;omega.
intros i j L1 L2 L3.
rewrite G in H3.
induction (le_gt_dec (length l2) j).
rewrite nth_app_r;trivial.
replace (nth (j - (length l2)) l1 p) with (nth (S j - (length l2)) (a0::l1) p).
rewrite <- (nth_app_r l2 (a0::l1) p);auto with arith.
apply H3;omega.
replace (S j - (length l2))%nat with (S (j - (length l2)))%nat;try reflexivity.
omega.
rewrite nth_app_l;try omega.
rewrite <- (nth_app_l  l2 (a0::l1));trivial.
apply H3;auto with arith;omega.
case G2;intro G2';[apply PIn_PIn_app_l|apply PIn_PIn_app_r];trivial.
rewrite G in a.
simpl in a;rewrite length_app in a;simpl in a.
rewrite length_app;omega.
auto with arith.
setoid ring.
simpl app.
apply IHl1.
rewrite app_ass.
trivial.
apply Aux.
trivial.
Qed.


(* the rec_det version*)

Lemma minor_rec : forall l1 n l l2 a b deg p,
  (forall i : nat, i > 1 -> i <=  n -> phi deg i b != P0) ->
  (forall i j : nat,
       i < n - (S j) -> j < n -> phi deg (S (S i)) (nth j (a :: l) p) != P0)->
  (|a :: l | = n)->
  (n > 1) ->
  (|b :: a :: l | = S n) ->
  l = app l2 l1 ->
   rec_det (phi deg (S n)) (det_aux1 phi deg n) l1 (b :: a :: l2)
   != P0.
  Proof.
    induction l1;intros n l l2 c b deg p H1 H2 H3 H4 H5 H6.
    reflexivity.
    rewrite rec_det_eq.
    destruct n.
    discriminate.
    destruct n.
    apply False_ind;omega.
    rewrite H6 in H2.
    rewrite H6 in H3.
    apply Ominus.
    apply Oprod_r.
    simpl app.
    destruct n.
    destruct l1;destruct l2;simpl app in * |- *;
      match goal with
	|- det_aux1 phi deg 2 ?l != P0 => case_det_aux1 2 l; try discriminate
      end.
    rewrite rec_det_eq.
    apply Ominus.
    rewrite H1;auto with arith;setoid ring.
    rewrite rec_det_eq.
    simpl rec_det.
    replace c with (nth O (c::a::nil) p);trivial.
    rewrite H2;auto with arith;setoid ring.
    apply minor with (S (S n)) p c;intuition.
    replace c with (nth O (c::(app l2 (a::l1))) p);trivial.
    destruct i.
    apply False_ind;omega.
    destruct i.
    apply False_ind;omega.
    apply H2;omega.
    destruct i.
    apply False_ind;omega.
    destruct i.
    apply False_ind;omega.
    destruct j.
    simpl.
    replace c with (nth O (c::(app l2 (a::l1))) p);trivial.
    apply H2;omega.
    replace (c::app l2 l1) with (app (c::l2) l1);trivial.
     replace (c::app l2 (a::l1)) with (app (c::l2) (a::l1)) in H2;trivial.
    induction (le_gt_dec (length (c::l2)) (S j)).
    rewrite nth_app_r;try omega.
    replace (nth (S j - |c :: l2 |) l1 p) with (nth (S ((S j) - |c :: l2 |)) (a::l1) p);trivial.
    replace (S (S j - |c :: l2 |)) with (S (S j) - |c :: l2 |)%nat;try omega.
    rewrite <- (@nth_app_r Pol (c::l2) (a::l1) p (S (S j)));try omega.
    apply H2;omega.
    rewrite nth_app_l;try omega.
    rewrite <- (@nth_app_l Pol (c::l2) (a::l1) p (S j));try omega.
    apply H2;omega.
    left;reflexivity.
    simpl in *|-*;rewrite length_app in H3;simpl in H3.
    rewrite length_app;omega.
    simpl app.
    apply (IHl1 (S (S n)) l (app l2 (a::nil)) c b deg p);intuition.
    rewrite  H6.
    apply H2; omega.
    rewrite app_ass.
    simpl;assumption.
    Qed.



Require Import Div2.


Theorem det_aux_trigQ: forall l n p deg Q b,
  (forall i:nat, i> 1 -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < (n- (S j))   -> (j < n)%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat ->
    phi deg (S (n - i)) (nth i l p) !=
  if even_odd_dec (S (n - i)) then  Q else - Q)  ->
  (length l = n)%nat -> n>1 -> 
    det_aux1 phi deg (S n) (b::l) != 
    (Zpolpower_nat (div2 (S n)))*(Pol_pow Q (N_of_nat n))*(phi deg 1 b).
Proof.
induction l;intros n p deg Q b H1 H2 H3 H4 H5.
simpl in H4;subst n;apply False_ind;omega.
destruct l.
simpl in H4;subst n;apply False_ind;omega.
case_det_aux1 (S n) (b::a::p0::l).
rewrite rec_det_eq.
transitivity
 (P0 -  rec_det (phi deg (S n)) (det_aux1 phi deg n) (a :: p0 :: l)
 (app nil (b :: nil))).
apply Psub_comp;try reflexivity.
rewrite H1;auto with arith;setoid ring.
rewrite rec_det_eq.
assert (Aux :  rec_det (phi deg (S n)) (det_aux1 phi deg n) (p0 :: l)
      (app (app nil (b :: nil)) (a :: nil)) != P0).
simpl app.
apply minor_rec with (p0::l) p;intuition.
rewrite Aux.
setoid ring.
simpl app.
destruct n;try discriminate.
destruct n;try discriminate.
destruct n.
destruct l;[idtac|simpl in *|-*;discriminate].
case_det_aux1 2 (b::p0::nil).
rewrite rec_det_eq.
simpl app.

transitivity (
 - P1 * phi deg 3 a *
(P0 - 
 rec_det (phi deg 2) (det_aux1 phi deg 1) (p0 :: nil) (b :: nil))).
apply Pmul_comp;try reflexivity.
apply Psub_comp;try reflexivity.
rewrite H1;try omega;setoid ring.
transitivity (phi deg 3 a * (rec_det (phi deg 2) (det_aux1 phi deg 1) (p0 :: nil) (b :: nil))).
setoid ring.
rewrite rec_det_eq.
simpl app.
simpl rec_det.
case_det_aux1 1 (b::nil).
rewrite rec_det_eq.
simpl rec_det.
simpl det_aux1.

rewrite (H3 1);auto with arith.
rewrite (H3 O);auto with arith.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
simpl in b0;apply False_ind;omega.
simpl in b0;apply False_ind;omega.
rewrite (IHl (S (S n)) p deg Q b);intuition.
replace (nth j (p0 :: l) p) with (nth (S j) (a::p0 :: l) p);trivial.
apply H2;omega.
replace  (nth i (p0 :: l) p) with  (nth (S i)  (a:: p0 :: l) p);trivial.
replace (S (S (S n) - i)) with (S (S (S (S n)) - (S i)));try omega.
rewrite H3;auto with arith;reflexivity.
rewrite (H3 O);auto with arith.
replace (S (S (S (S n)) - 0)) with (S (S (S (S n))));auto with arith.
replace (N_of_nat  (S (S (S n))))with ((N_of_nat (S (S n))) + 1)%N;
[rewrite Ppow_plus;simpl Pol_pow|simpl;repeat rewrite Pplus_one_succ_r;trivial].
unfold Zpolpower_nat.
case (even_odd_dec  (S (S (S (S n)))));intro G1;inversion G1;
case ( even_odd_dec (S (S (S n))));intro G2.
apply False_ind;apply (not_even_and_odd  (S (S (S n))));trivial.
setoid ring.

rewrite <- (odd_div2 (S (S (S n))));trivial. 
case (even_odd_dec (div2 (S (S (S n)))));intro G3.
case (even_odd_dec (S (div2 (S (S (S n))))));intro G4.
apply False_ind;apply (not_even_and_odd ((div2 (S (S (S n))))));trivial.
inversion G4;trivial.

setoid ring.
case (even_odd_dec (S (div2 (S (S (S n))))));intro G4.
setoid ring.
apply False_ind;apply (not_even_and_odd ((div2 (S (S (S n))))));trivial.
inversion G4;trivial.

rewrite <- (even_div2 (S (S (S n))));trivial.
case (even_odd_dec (div2 (S (S (S n)))));intro G3;setoid ring.
apply False_ind;apply (not_even_and_odd (S (S (S n))));trivial.
simpl in H4;simpl in b0;apply False_ind;omega.
Qed.


(* cas n= 1 marche aussi ... refaire la preuve ci-dessus!*)

Theorem  det_aux_trigQ1 : forall b a deg Q,
  phi deg 2 b != P0 ->
  phi deg 2 a != Q ->
 det_aux1 phi deg 2 (b :: a :: nil) != - Q * (phi deg 1 b).
Proof.
  intros b a deg Q H1 H2.
  case_det_aux1 2 (b :: a::nil);simpl in *|-;try (apply False_ind;omega).
  repeat rewrite rec_det_eq.
  simpl app.
  rewrite H1.
  rewrite H2.
  case_det_aux1 1 (a::nil);simpl in *|-;try (apply False_ind;omega). 
  rewrite rec_det_eq;simpl rec_det.
  simpl;Pcsimpl;setoid ring.
Qed.




(* pouver des egalites de listes avec cons et app dans le desordre*)
Ltac list_blast := simpl;try (repeat rewrite app_ass);try (repeat rewrite app_comm_cons);
try (repeat rewrite app_ass);simpl;try reflexivity.

(* a mettre dans Pol_ring*)
Lemma Pol_powP0 :
forall n1, Pol_pow P0 (N_of_nat (S n1)) != P0.
Proof.
intro n0.
caseEq (N_of_nat (S n0)).
intro G.
simpl N_of_nat in G.
discriminate.
intros p0 G.
simpl.
generalize p0;intro p1.
induction p1;simpl;Pcsimpl;try rewrite IHp1;setoid ring.
Qed.

Ltac length_blast := 
repeat progress(
  match goal with
    | H : context [length nil] |- _ => simpl length in H
    | H : context [length (app ?l1 ?l2)] |- _ => rewrite length_app in H
    | H : context [length (?x :: ?y)]  |- _ => (simpl length in H)
    | |- context [length (app ?l1 ?l2)] => rewrite length_app
    | |- context [length (?x :: ?y) ] => simpl length
    | |- context [length (@nil Pol)] => simpl length
end).


Ltac falso := apply False_ind;omega.


(* pour des matrices bloc + st trig inf

|0 0 0 0 0
|0 0 0 0 .
|. . . . .
|. . . . .

*)



Definition eps(n:nat) := cpow (-- c1) (N_of_nat n).
Lemma det_skip: forall d l1 l2,
length l1 > 0 -> length l2 > 0 ->
det phi  d (app l1 l2) !=
(eps (length(l1) *(length l2))) !* (det phi d (app l2 l1)).
Admitted.




Lemma det_aux_det_aux1 : forall deg l n, 
  length l = n -> det_aux1 phi deg n l = det_aux phi deg n l.
  intros deg;induction l;intros n H.
  destruct n;simpl in H;try discriminate.
  reflexivity.
  simpl in *|-;subst n.
  case_det_aux1 (S (length l)) (a::l);simpl in *|-;try falso.
  
  Admitted.
  


Lemma Zpolpower_nat_even : forall n, Zpolpower_nat (n*2) != P1.
  intro n.
  unfold Zpolpower_nat.
  assert (c:even (n*2)).
  apply even_mult_r.
  auto with arith.
  induction (even_odd_dec (n * 2));try reflexivity.
  elim (not_even_and_odd (n*2) c b).
Qed.

(*

Lemma aux : forall deg p Q n l2 l3 p0 k ,

 ( forall (n : nat) (l1 l2 l3 l4 : list pol),
        S (S n) = |l2 | ->
        S k = |l1 | ->
        l1 = app l3 l4 ->
        |l4 | > 0 ->
        (forall i j : nat,
         i < |l1 | -> j < |l2 | -> phi deg (S (S j)) (nth i l1 p) != P0) ->
        (forall i : nat,
         i < |l2 | ->
         phi deg (S (S (|l2 | - S i))) (nth i l2 p)
         != (if even_odd_dec (S (S (|l2 | - S i))) then Q else - Q)) ->
        (forall i j : nat,
         i < |l2 | -> j < |l2 | - S i -> phi deg (S (S j)) (nth i l2 p) != P0) ->
        rec_det (phi deg (|l1 | + |l2 |)) (det_aux1 phi deg (k + |l2 |))
          (app l4 l2) l3
        != Zpolpower_nat (div2 (|l2 | * k)) *
           Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
           rec_det (phi (deg - |l2 |) (S k)) (det_aux1 phi (deg - |l2 |) k)
             l4 l3) ->
   S (S n) = |l2 | ->
  ( forall i : nat,
       i < |l2 | ->
       phi deg (S (S (|l2 | - S i))) (nth i l2 p)
       != (if even_odd_dec (S (S (|l2 | - S i))) then Q else - Q)) ->
(   forall i j : nat,
       i < |l2 | -> j < |l2 | - S i -> phi deg (S (S j)) (nth i l2 p) != P0) ->
    (S k) = |l3 | -> 
  ( forall i j : nat,
       i < |l3 | + 1 ->
       j < |l2 | -> phi deg (S (S j)) (nth i (app l3 (p0 :: nil)) p) != P0) ->

   rec_det (phi deg (|l3 | + 1 + |l2 |)) (det_aux1 phi deg (S k + |l2 |)) l2
     (app l3 (p0 :: nil)) != P0.
  intros deg p Q;induction n;intros.
  destruct l2;length_blast;try discriminate.
  destruct l2;length_blast;try discriminate.
  destruct l2;length_blast;try discriminate.
  clear H0.
  rewrite rec_det_eq.
  rewrite rec_det_eq.
  simpl rec_det.
  replace (S k + 2)%nat with (S (k+2))%nat;[idtac|omega].
  case_det_aux1 (S(k + 2))%nat (app (app l3 (p0 :: nil)) (p2 :: nil)).
  rewrite (H O (app l3 (p0 :: nil)) (p2 :: nil)

  simpl app.
  
*)  
(* m est pair?*)
    

Axiom triche : forall A:Prop, A.
Theorem rec_det_partial_trig : forall deg p Q k n l1 l2 l3 l4,
  S (S n) = length l2 ->
  (S k) = length l1  ->
  l1 = app l3 l4 ->
  length l4 > 0 ->
  (forall i j, i < length l1 -> j< length l2 -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i, i < length l2  ->
    phi deg (S (S ((length l2) -  (S i))))%nat (nth i l2 p) !=
    if even_odd_dec (S (S ((length l2) -  (S i))))%nat then  Q else - Q)  ->


  (forall i j, i <length l2 -> j < ((length l2) - (S i))%nat ->
    phi deg (S (S j)) (nth i l2 p) != P0) ->
  

  rec_det (phi deg ((length l1) + (length l2))%nat)
  (det_aux1 phi deg (k + length l2)) (app l4 l2) l3 !=
 (Zpolpower_nat ((div2 ((length l2)* k)))%nat)*
  (Zpolpower_nat (div2 (S (length l2))))* (Pol_pow Q (N_of_nat (length l2)))*
  (rec_det
    (phi (deg - (length l2))%nat (S k))
      (det_aux1 phi (deg -(length l2))%nat k) l4 l3).
  Proof.
    intros deg p Q;induction k ;intros n l1 l2 l3 l4 H1 H2 H3 H4 H5 H6 H7;
    subst l1.
    assert (l1_dec : exists a, l4 = a::nil). 
    destruct l3;destruct l4;simpl in H2;try discriminate;try falso.
    destruct l4.
    exists p0;reflexivity.
    simpl in H2;falso.
    simpl in H4;falso.
    rewrite length_app in H2;simpl in H2;falso.
    case l1_dec;intros a G;subst l4.
    setoid_replace (Zpolpower_nat (div2 (|l2 | * 0))) with P1.
    replace (0 + |l2 |)%nat with (|l2|) by auto with arith.
    destruct l3;[idtac|rewrite length_app in H2;simpl in H2;falso].
    clear H2 H4 l1_dec.
    simpl app in *.
    transitivity (det_aux1 phi deg (S (|l2 |)) (a::l2)).
    replace (|a :: nil | + |l2 |)%nat with (S (length l2)) by
      (simpl;auto with arith).
    simpl rec_det.
     symmetry.
     case_det_aux1  (S (|l2 |)) (a :: l2);simpl in *|-; try falso.
     simpl rec_det.
     Pcsimpl.
     rewrite <- H1.
     rewrite (@det_aux_trigQ l2 (S (S n)) p deg Q a).
     intros i H8 H9.
     replace a with (nth O (a::nil) p) by reflexivity.
     destruct i;try falso;destruct i;try falso.
     apply H5.
     auto with arith.
     rewrite <- H1.
     auto with arith.
     intros i j H8 H9.
     apply H7.
     rewrite <- H1;trivial.
     omega.
     intros i H8.
     rewrite H1.
     replace (S (|l2 | - i)) with (S (S (|l2 | - S i))) by  omega.
     apply H6.
     rewrite <- H1;trivial.
     symmetry;trivial.
     auto with arith.
     cut ( phi deg 1 a != phi (deg - S (S n)) 1 a).
     intro super.
     rewrite super.
     setoid ring.
     unfold phi.
     case (le_gt_dec (deg + 2) 1);intro G1.
     falso.
     case (le_gt_dec (deg - S (S n) + 2) 1);intro G2.
     falso.
     reflexivity.
     setoid_replace ( Pol_subC (c1 !* phi (deg - |l2 |) 1 a) c0)
       with (c1 !* phi (deg - |l2 |) 1 a).
     Pcsimpl.
     Pcsimpl.
     (replace (|l2 | * 0)%nat with O by auto with arith);
     reflexivity.
     destruct l4.
     simpl in H4;falso.
     simpl app.
     rewrite rec_det_eq.
     destruct l3.
     destruct l4.
     simpl app. 
     simpl (rec_det (phi (deg - |l2 |) (S (S k)))
        (det_aux1 phi (deg - |l2 |) (S k)) (p0 :: nil) nil).
     Pcsimpl.
     setoid ring.
     assert (great : det_aux1 phi deg (S k + |l2 |) l2 != P0).
     destruct l2.
     simpl in H1;discriminate.
     transitivity ( det_aux1 phi (deg - (S k)) (S n) (p1 :: l2)).
     apply triche.
     rewrite (@det_aux_trigQ l2 n p (deg -(S k)) P0 p1).
     intros i G1 G2.
     

     simpl app in H5.
     simpl length.
     rewrite <- H1.
     replace (1 + S (S n))%nat with (S (S (S n))) by omega.
     rewrite H5.

     assert (great1:det_aux1 phi deg (S k + |l2 |) (app l3 (app l4 l2))
       != P0).
     case l3.
     simpl app.
     destruct l4.
     destruct l2.
     simpl in H1;discriminate.
     cut (det_aux1 phi deg (S k + |p1 :: l2 |) (p1 :: l2)!=
       (det_aux1 phi (deg - (S k)) (|p1::l2|) (p1::l2))).
     intro cooool.
     rewrite cooool.
     rewrite <- H1.
     rewrite (@det_aux_trigQ l2 (S n) p (deg -(S k)) P0 p1).
     intros i H8 H9.
     replace p1 with (nth O (p1::l2) p) by reflexivity.
     assert (H10 :  phi (deg - S k) i (nth 0 (p1 :: l2) p) != 
       phi deg ((S k) + i) (nth 0 (p1 :: l2) p)) by apply triche.
     destruct i;try falso.
     destruct i;try falso.
     rewrite H10.
     replace (S k + S (S i))%nat with (S (S (k + i)))%nat by omega.
     apply H7.
     simpl;omega.
     rewrite <- H1.
     
     omega.

    (***ici***)


     
     
     unfold Zpolpower_nat;simpl.
     
     
   



Theorem det_aux_trigQ: forall l n p deg Q b,
  (forall i:nat, i> 1 -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < (n- (S j))   -> (j < n)%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat ->
    phi deg (S (n - i)) (nth i l p) !=
  if even_odd_dec (S (n - i)) then  Q else - Q)  ->
  (length l = n)%nat -> n>1 -> 
    det_aux1 phi deg (S n) (b::l) != 
    (Zpolpower_nat (div2 (S n)))*(Pol_pow Q (N_of_nat n))*(phi deg 1
      b).

     case_det_aux1 (S (|l2 |)) (a :: l2);simpl length in *;try falso.
     clear a0.
     


     rewrite <- H1.
     induction ( eq_nat_dec (S (S n)) (S (S n))) ;try falso.
     clear a1 a0.
     
     

    


    destruct l4;simpl in H2;try discriminate;
    length_blast.
    simpl app in *|- *.
    simpl plus.
    transitivity (det_aux1 phi deg (S (|l2 |)) (p0::l2)).
    case_det_aux1  (S (|l2 |)) (p0 :: l2);simpl in *|-; try falso.
    simpl rec_det.
    rewrite Pol_sub_c0'.
    Pcsimpl.
    transitivity
      ( Zpolpower_nat (div2 (S (|l2 |)))
	* Pol_pow Q (N_of_nat (|l2 |)) *(phi deg 1 p0)).
    apply (@det_aux_trigQ l2 (length l2) p deg Q p0);length_blast;intuition.
    change p0 with (nth O (p0::nil) p).
    destruct i;try destruct i;try discriminate;try falso.
    apply H5;auto with arith.
    replace (S (|l2 | - i)) with  (S (S (|l2 | - S i)));try omega.
    apply H6;trivial.
    setoid_replace ( Zpolpower_nat 0) with P1;
      [idtac|unfold Zpolpower_nat;simpl;reflexivity].
    setoid ring.
    apply Pmul_comp;try reflexivity.
    unfold phi.
    induction (le_gt_dec (deg + 2) 1);
      induction (le_gt_dec (deg - |l2 | + 2) 1);try reflexivity;try falso.
    simpl in H4;try falso.
    replace  (|l2 | * 0)%nat with 0 by auto with arith.
    reflexivity.
    simpl in H4;falso.
    rewrite length_app in H2;simpl in H2;falso.
    destruct l4;try destruct l4;simpl in H4;try falso.
    simpl app in  *|-*.
    length_blast.
    rewrite rec_det_eq.
    symmetry.
    rewrite rec_det_eq.
    simpl ( rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (p0 :: nil))).
    cut (rec_det (phi deg (|l3 | + 1 + |l2 |)) (det_aux1 phi deg (S k + |l2 |))
        l2 (app l3 (p0 :: nil)) != P0).
    intro G;rewrite G.
    setoid ring.
    symmetry.

    case_det_aux1  (S k + |l2 |)%nat (app l3 l2);length_blast.
 replace (S k + |l2 |)%nat with (S(k + (length l2)))%nat;
      [idtac|omega].
 replace (S (k + |l2 |))%nat with (|l3 | + |l2 |)%nat.
 rewrite (IHk n l3 l2 (@nil Pol) l3);intuition.
 rewrite <- (nth_app_l l3 (p0::nil) p);trivial.
apply H5;auto with arith.
simpl app.
generalize (Zpolpower_nat (div2 (S (|l2 |))));intro p1.
generalize ( Pol_pow Q (N_of_nat (|l2 |)));intro p2.
case_det_aux1 (S k) (app l3 nil);length_blast;try falso.
rewrite <- app_nil_end.
generalize (rec_det (phi (deg - |l2 |) (S k)) (det_aux1 phi (deg - |l2 |) k) l3 nil).
intro p3.
cut ( phi deg (|l3 | + 1 + |l2 |) p0 !=  phi (deg - |l2 |) (S (S k)) p0 ).
intro test.
rewrite test.
setoid ring.
cut ( Zpolpower_nat (div2 (|l2 | * k)) != Zpolpower_nat (div2 (|l2 | * S k))).
intro test2.
rewrite test2.
setoid ring.
clear H4.
clear a.
clear H2.


  assert (test : (phi (deg - |l2 |) (S (S k)) p0)*
 (Zpolpower_nat (div2 ((|l2 |)* k)))
 !=
      phi deg (|l3 | + 1 + |l2 |) p0).
    rewrite <- H2.
    unfold phi.
    induction (le_gt_dec (deg - |l2 | + 2) (S (S k)));
      induction (le_gt_dec (deg + 2) (S (S k) + |l2 |));try falso.
    setoid ring.
    replace  (S (S k) + |l2 |)%nat with (S (S (k+(length l2))))%nat;
      [idtac|omega].
    induction (Even.even_odd_dec (S (S k)));
      induction ( Even.even_odd_dec (S (S (k + |l2 |)))).
    replace (deg - |l2 | - (S (S k) - 2))%nat with 
(deg - (S (S (k + |l2 |)) - 2))%nat;[idtac|omega].
    setoid_replace ( Zpolpower_nat (div2  ((|l2 |) * k))) with P1.
    setoid ring.
    unfold Zpolpower_nat.
    induction (even_odd_dec (div2 ((|l2 |) * k))).
    reflexivity.
    inversion a1.
    inversion H0.
    replace (S (S (k + |l2 |)))%nat with ((S(S(k))) + (|l2|))%nat in a2;
      [idtac|omega].
    clear H H3 H6 H7 H5 IHk.
    apply False_ind.
    clear - H8 a1 a2 b1.
    assert (G1: even (|l2|)).
    apply (even_plus_even_inv_r (S (S k)));trivial.

    assert (G2 : k = double (div2 k)).
    apply (even_double k);trivial.
    assert (G3 : (|l2|) = double (div2 (|l2|))).
      apply (even_double(|l2|) );trivial.
      assert (G4: (|l2 | * k)%nat = double (div2 (|l2 | * k))%nat).
      apply even_double.
      apply  even_mult_r;trivial.
      assert (G5: (|l2 | * k = double (double ((div2 (|l2 |))*(div2 k))))%nat).
      set (y:= div2 (|l2 |)) in *|-*.
      set (x:=  div2 k) in *|-*.
      rewrite G3.
      rewrite G2.
      unfold double.
      ring.
      assert (G6 : (div2 (|l2 | * k)) = (double (div2 (|l2 |) * div2 k))).
      Lemma double_inj : forall n m, double n = double m -> n = m.
	intros.
	unfold double in H.
	omega.
Qed.
apply double_inj.
omega.
Lemma even_double : forall n, even (double n).
  induction n.
unfold double.
constructor.
unfold double.
replace (S n + S n)%nat with ((n+n) + 2)%nat;try omega.
apply even_even_plus.
auto.
constructor;constructor;constructor.
Qed.
apply (not_even_and_odd (div2 (|l2 | * k)));trivial.
rewrite G6;apply even_double.
(* Focus*)


      transitivity ((  double (div2 k))*(double (div2 (|l2 |)))
    
: forall n : nat, even n -> n = double (div2 n)
: forall n m : nat, even (n + m) -> even n -> even m

Print double.



Theorem rec_det_partial_trig : forall deg p Q k n l1 l2 l3 l4,
  S (S n) = length l2 ->
  (S k) = length l1  ->
  l1 = app l3 l4 ->
  length l4 > 0 ->
  (forall i j, i < length l1 -> j< length l2 -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i, i < length l2  ->
    phi deg (S (S ((length l2) -  (S i))))%nat (nth i l2 p) !=
    if even_odd_dec (S (S ((length l2) -  (S i))))%nat then  Q else - Q)  ->

  (forall i j, i <length l2 -> j < ((length l2) - (S i))%nat ->
    phi deg (S (S j)) (nth i l2 p) != P0) ->
  
  rec_det (phi deg ((length l1) + (length l2))%nat)
  (det_aux1 phi deg (k + length l2)) (app l4 l2) l3 !=
 (Zpolpower_nat ((div2 ((length l2)* k)))%nat)*
  (Zpolpower_nat (div2 (S (length l2))))* (Pol_pow Q (N_of_nat (length l2)))*
  (rec_det
    (phi (deg - (length l2))%nat (S k))
      (det_aux1 phi (deg -(length l2))%nat k) l4 l3).
  Proof.
    intros deg p Q;induction k ;intros n l1 l2 l3 l4 H1 H2 H3 H4 H5 H6 H7;
    subst l1.
    destruct l3;destruct l4;simpl in H2;try discriminate;try falso.

   (* setoid_replace  (Zpolpower_nat (div2 (S (|l2 |)) * div2 1)) with P1.
Impossible to unify "nat" with "pol"*)
    (replace (div2 ( (|l2 |) * 0))%nat with 0;
      [idtac|replace ((|l2 |) * 0)%nat with 0;[reflexivity|auto with arith]]).
    destruct l4;simpl in H2;try discriminate;
    length_blast.
    simpl app in *|- *.
    simpl plus.
    transitivity (det_aux1 phi deg (S (|l2 |)) (p0::l2)).
    case_det_aux1  (S (|l2 |)) (p0 :: l2);simpl in *|-; try falso.
    simpl rec_det.
    rewrite Pol_sub_c0'.
    Pcsimpl.
    transitivity ( Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *(phi deg 1 p0)).
    apply (@det_aux_trigQ l2 (length l2) p deg Q p0);length_blast;intuition.
    change p0 with (nth O (p0::nil) p).
    destruct i;try destruct i;try discriminate;try falso.
    apply H5;auto with arith.
    replace (S (|l2 | - i)) with  (S (S (|l2 | - S i)));try omega.
    apply H6;trivial.
    setoid_replace ( Zpolpower_nat 0) with P1;
      [idtac|unfold Zpolpower_nat;simpl;reflexivity].
    setoid ring.
    apply Pmul_comp;try reflexivity.
    unfold phi.
    induction (le_gt_dec (deg + 2) 1);
      induction (le_gt_dec (deg - |l2 | + 2) 1);try reflexivity;try falso.
    simpl in H4;try falso.
    length_blast;falso.
    destruct l4;try destruct l4;simpl in H4;try falso.
    simpl app in  *|-*.
    length_blast.
    rewrite rec_det_eq.
    symmetry.
    rewrite rec_det_eq.
    simpl ( rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (p0 :: nil))).
    cut ( rec_det (phi deg (|l3 | + 1 + |l2 |)) (det_aux1 phi deg (S k + |l2 |))
        l2 (app l3 (p0 :: nil)) != P0).
    intro G;rewrite G.
    setoid ring.
    symmetry.
   
    case_det_aux1  (S k + |l2 |)%nat (app l3 l2);length_blast.
 replace (S k + |l2 |)%nat with (S(k + (length l2)))%nat;
      [idtac|omega].
 replace (S (k + |l2 |))%nat with (|l3 | + |l2 |)%nat.
 rewrite (IHk n l3 l2 (@nil Pol) l3);intuition.
 rewrite <- (nth_app_l l3 (p0::nil) p);trivial.
apply H5;auto with arith.
simpl app.
generalize (Zpolpower_nat (div2 (S (|l2 |))));intro p1.
generalize ( Pol_pow Q (N_of_nat (|l2 |)));intro p2.
case_det_aux1 (S k) (app l3 nil);length_blast;try falso.
rewrite <- app_nil_end.
generalize (rec_det (phi (deg - |l2 |) (S k)) (det_aux1 phi (deg - |l2 |) k) l3 nil).
  assert (test : (phi (deg - |l2 |) (S (S k)) p0)*
 (Zpolpower_nat (div2 ((|l2 |)* k)))
 !=
      phi deg (|l3 | + 1 + |l2 |) p0).
    rewrite <- H2.
    unfold phi.
    induction (le_gt_dec (deg - |l2 | + 2) (S (S k)));
      induction (le_gt_dec (deg + 2) (S (S k) + |l2 |));try falso.
    setoid ring.
    replace  (S (S k) + |l2 |)%nat with (S (S (k+(length l2))))%nat;
      [idtac|omega].
    induction (Even.even_odd_dec (S (S k)));
      induction ( Even.even_odd_dec (S (S (k + |l2 |)))).
    replace (deg - |l2 | - (S (S k) - 2))%nat with 
(deg - (S (S (k + |l2 |)) - 2))%nat;[idtac|omega].
    setoid_replace ( Zpolpower_nat (div2  ((|l2 |) * k))) with P1.
    setoid ring.
    unfold Zpolpower_nat.
    induction (even_odd_dec (div2 ((|l2 |) * k))).
    reflexivity.
    inversion a1.
    inversion H0.
    replace (S (S (k + |l2 |)))%nat with ((S(S(k))) + (|l2|))%nat in a2;
      [idtac|omega].
    clear H H3 H6 H7 H5 IHk.
    apply False_ind.
    clear - H8 a1 a2 b1.
    assert (G1: even (|l2|)).
    apply (even_plus_even_inv_r (S (S k)));trivial.

    assert (G2 : k = double (div2 k)).
    apply (even_double k);trivial.
    assert (G3 : (|l2|) = double (div2 (|l2|))).
      apply (even_double(|l2|) );trivial.
      assert (G4: (|l2 | * k)%nat = double (div2 (|l2 | * k))%nat).
      apply even_double.
      apply  even_mult_r;trivial.
      assert (G5: (|l2 | * k = double (double ((div2 (|l2 |))*(div2 k))))%nat).
      set (y:= div2 (|l2 |)) in *|-*.
      set (x:=  div2 k) in *|-*.
      rewrite G3.
      rewrite G2.
      unfold double.
      ring.
      assert (G6 : (div2 (|l2 | * k)) = (double (div2 (|l2 |) * div2 k))).
      Lemma double_inj : forall n m, double n = double m -> n = m.
	intros.
	unfold double in H.
	omega.
Qed.
apply double_inj.
omega.
Lemma even_double : forall n, even (double n).
  induction n.
unfold double.
constructor.
unfold double.
replace (S n + S n)%nat with ((n+n) + 2)%nat;try omega.
apply even_even_plus.
auto.
constructor;constructor;constructor.
Qed.
apply (not_even_and_odd (div2 (|l2 | * k)));trivial.
rewrite G6;apply even_double.
(* Focus*)


      transitivity ((  double (div2 k))*(double (div2 (|l2 |)))
    
: forall n : nat, even n -> n = double (div2 n)
: forall n m : nat, even (n + m) -> even n -> even m

Print double.



Theorem rec_det_partial_trig : forall deg p Q k n l1 l2 l3 l4,
  S (S n) = length l2 ->
  (S k) = length l1  ->
  l1 = app l3 l4 ->
  length l4 > 0 ->
  (forall i j, i < length l1 -> j< length l2 -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i, i < length l2  ->
    phi deg (S (S ((length l2) -  (S i))))%nat (nth i l2 p) !=
    if even_odd_dec (S (S ((length l2) -  (S i))))%nat then  Q else - Q)  ->

  (forall i j, i <length l2 -> j < ((length l2) - (S i))%nat ->
    phi deg (S (S j)) (nth i l2 p) != P0) ->
  
  rec_det (phi deg ((length l1) + (length l2))%nat)
  (det_aux1 phi deg (k + length l2)) (app l4 l2) l3 !=
  (Zpolpower_nat ((div2 ((length l2)* k)))%nat)*
  (Zpolpower_nat (div2 (S (length l2))))* (Pol_pow Q (N_of_nat (length l2)))*
  (rec_det
    (phi (deg - (length l2))%nat (S k))
      (det_aux1 phi (deg -(length l2))%nat k) l4 l3).
  Proof.
    intros deg p Q;induction k ;intros n l1 l2 l3 l4 H1 H2 H3 H4 H5 H6 H7;
    subst l1.
    destruct l3;destruct l4;simpl in H2;try discriminate;try falso;
   (* setoid_replace  (Zpolpower_nat (div2 (S (|l2 |)) * div2 1)) with P1.
Impossible to unify "nat" with "pol"*)
    (replace (div2 ( (|l2 |) * 0))%nat with 0;
      [idtac|replace ((|l2 |) * 0)%nat with 0;[reflexivity|auto with arith]]).
    destruct l4;simpl in H2;try discriminate;
    length_blast.
    simpl app in *|- *.
    simpl plus.
    transitivity (det_aux1 phi deg (S (|l2 |)) (p0::l2)).
    case_det_aux1  (S (|l2 |)) (p0 :: l2);simpl in *|-; try falso.
    simpl rec_det.
    rewrite Pol_sub_c0'.
    Pcsimpl.
    transitivity ( Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *(phi deg 1 p0)).
    apply (@det_aux_trigQ l2 (length l2) p deg Q p0);length_blast;intuition.
    change p0 with (nth O (p0::nil) p).
    destruct i;try destruct i;try discriminate;try falso.
    apply H5;auto with arith.
    replace (S (|l2 | - i)) with  (S (S (|l2 | - S i)));try omega.
    apply H6;trivial.
    setoid_replace ( Zpolpower_nat 0) with P1;
      [idtac|unfold Zpolpower_nat;simpl;reflexivity].
    setoid ring.
    apply Pmul_comp;try reflexivity.
    unfold phi.
    induction (le_gt_dec (deg + 2) 1);
      induction (le_gt_dec (deg - |l2 | + 2) 1);try reflexivity;try falso.
    simpl in H4;try falso.
    length_blast;falso.
    destruct l4;try destruct l4;simpl in H4;try falso.
    simpl app in  *|-*.
    length_blast.
    rewrite rec_det_eq.
    symmetry.
    rewrite rec_det_eq.
    simpl ( rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (p0 :: nil))).
    cut ( rec_det (phi deg (|l3 | + 1 + |l2 |)) (det_aux1 phi deg (S k + |l2 |))
        l2 (app l3 (p0 :: nil)) != P0).
    intro G;rewrite G.
    setoid ring.
    symmetry.
   
    case_det_aux1  (S k + |l2 |)%nat (app l3 l2);length_blast.
 replace (S k + |l2 |)%nat with (S(k + (length l2)))%nat;
      [idtac|omega].
 replace (S (k + |l2 |))%nat with (|l3 | + |l2 |)%nat.
 rewrite (IHk n l3 l2 (@nil Pol) l3);intuition.
 rewrite <- (nth_app_l l3 (p0::nil) p);trivial.
apply H5;auto with arith.
simpl app.
generalize (Zpolpower_nat (div2 (S (|l2 |))));intro p1.
generalize ( Pol_pow Q (N_of_nat (|l2 |)));intro p2.
case_det_aux1 (S k) (app l3 nil);length_blast;try falso.
rewrite <- app_nil_end.
generalize (rec_det (phi (deg - |l2 |) (S k)) (det_aux1 phi (deg - |l2 |) k) l3 nil).
  assert (test : (phi (deg - |l2 |) (S (S k)) p0)*
 (Zpolpower_nat (div2 ((|l2 |)* k)))
 !=
      phi deg (|l3 | + 1 + |l2 |) p0).
    rewrite <- H2.
    unfold phi.
    induction (le_gt_dec (deg - |l2 | + 2) (S (S k)));
      induction (le_gt_dec (deg + 2) (S (S k) + |l2 |));try falso.
    setoid ring.
    replace  (S (S k) + |l2 |)%nat with (S (S (k+(length l2))))%nat;
      [idtac|omega].
    induction (Even.even_odd_dec (S (S k)));
      induction ( Even.even_odd_dec (S (S (k + |l2 |)))).
    replace (deg - |l2 | - (S (S k) - 2))%nat with 
(deg - (S (S (k + |l2 |)) - 2))%nat;[idtac|omega].
    setoid_replace ( Zpolpower_nat (div2  ((|l2 |) * k))) with P1.
    setoid ring.
    unfold Zpolpower_nat.
    induction (even_odd_dec (div2 ((|l2 |) * k))).
    reflexivity.
    inversion a1.
    inversion H0.
    replace (S (S (k + |l2 |)))%nat with ((S(S(k))) + (|l2|))%nat in a2;
      [idtac|omega].
    clear H H3 H6 H7 H5 IHk.
    apply False_ind.
    clear - H8 a1 a2 b1.
    assert (G1: even (|l2|)).
    apply (even_plus_even_inv_r (S (S k)));trivial.

    assert (G2 : k = double (div2 k)).
    apply (even_double k);trivial.
    assert (G3 : (|l2|) = double (div2 (|l2|))).
      apply (even_double(|l2|) );trivial.
      assert (G4: (|l2 | * k)%nat = double (div2 (|l2 | * k))%nat).
      apply even_double.
      apply  even_mult_r;trivial.
      assert (G5: (|l2 | * k = double (double ((div2 (|l2 |))*(div2 k))))%nat).
      set (y:= div2 (|l2 |)) in *|-*.
      set (x:=  div2 k) in *|-*.
      rewrite G3.
      rewrite G2.
      unfold double.
      ring.
      assert (G6 : (div2 (|l2 | * k)) = (double (div2 (|l2 |) * div2 k))).
      Lemma double_inj : forall n m, double n = double m -> n = m.
	intros.
	unfold double in H.
	omega.
Qed.
apply double_inj.
omega.
Lemma even_double : forall n, even (double n).
  induction n.
unfold double.
constructor.
unfold double.
replace (S n + S n)%nat with ((n+n) + 2)%nat;try omega.
apply even_even_plus.
auto.
constructor;constructor;constructor.
Qed.
apply (not_even_and_odd (div2 (|l2 | * k)));trivial.
rewrite G6;apply even_double.
(* Focus*)


      transitivity ((  double (div2 k))*(double (div2 (|l2 |)))
    
: forall n : nat, even n -> n = double (div2 n)
: forall n m : nat, even (n + m) -> even n -> even m

Print double.




    





    simpl ( rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (p0 :: nil))).
    assert (test :  (phi (deg - |l2 |) (S (S k)) p0) !=  phi deg (|l3 | + 1 + |l2 |) p0).
    rewrite H2.
    rewrite <- H1.
  unfold phi.
  induction ( le_gt_dec (deg - S (S n) + 2) (|l3 | + 1))%nat;
    induction ( le_gt_dec (deg + 2) (|l3 | + 1 + S (S n)))%nat;length_blast;try falso.
  reflexivity.
  caseEq ( |l3 | + 1)%nat.
  intro G.
  simpl.
  case ( Even.even_odd_dec (S (S n)));intro G1.

  transitivity (phi deg 2 p0).
  unfold phi.
  induction (le_gt_dec (deg + 2) 2).
  destruct (Even.even_odd_dec 2).
simpl.

  rewrite 
       


    


    destruct l3;length_blast;try discriminate.
    simpl app in *|-*.
    transitivity P0;[idtac|simpl rec_det;setoid ring].
    simpl plus.
    assert (aux : det_aux1 phi deg  (S (|l2 |)) (p0::l2) !=
      Zpolpower_nat (div2 (S (|l2|))) * Pol_pow Q (N_of_nat (|l2|)) * phi deg 1 p0).
    apply (@det_aux_trigQ l2 (|l2|) p deg Q p0);intuition.    
    change p0 with (nth O (p0::nil) p).
    destruct i;try destruct i;try discriminate;try falso.
    apply H4;auto with arith.
    replace (S (|l2 | - i)) with (S (S (|l2 | - S i)));
      [idtac|omega].
    apply H5;auto with arith.
    generalize aux;clear aux.
    case_det_aux1 (S (|l2 |)) (p0 :: l2);length_blast;try falso.
    intro aux;rewrite rec_det_eq in aux.
    simpl app in *|- *.
    assert (aux2 : phi deg (S (|l2 |)) p0 * det_aux1 phi deg (|l2 |) l2 !=
       Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
           phi deg 1 p0).
    destruct l2.
    

    case_det_aux1 (S (|l2 |)) (p0 :: l2).
    rewrite rec_det_eq.
 


    destruct l2;simpl app in *|-*;length_blast;simpl plus;try falso.
    rewrite H2.
    rewrite <- app_nil_end.
    replace (deg - 0)%nat with deg ;[idtac|auto with arith].
    replace  (|l3 | + |l4 | + 0)%nat with  (|l3 | + |l4 |)%nat;
    [idtac|auto with arith].
    replace (k+0)%nat with k;[idtac|auto with arith].
    generalize ( rec_det (phi deg (|l3 | + |l4 |)) (det_aux1 phi deg k) l4 l3);
      intro A;unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
    destruct l4.
    simpl app in *|-*.
    transitivity P0;[idtac|  simpl rec_det;setoid ring].
    destruct l2.
    reflexivity.
    destruct l2.
    length_blast.
   
    
    rewrite rec_det_eq.
    
    apply Ominus.
    apply Oprod_r.
    replace  (k + |p0 :: l2 |)%nat with (length  (app l3 l2)).
    transitivity(det phi deg (app l3 l2)).
    rewrite  det_aux_det_aux1;trivial.
    unfold det;reflexivity.
    unfold det.
    rewrite <- det_aux_det_aux1;trivial.















Theorem rec_det_partial_trig : forall deg p Q n k l1 l2 l3 l4 l5 a b,
  S (S n) = length l2 ->
  (S k) = length l1  ->
  l1 = app l3 l4 ->

  (forall i j, i < length l1 -> j< length l2 -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i, i < length l2  ->
    phi deg (S (S ((length l2) -  (S i))))%nat (nth i l2 p) !=
    if even_odd_dec (S (S ((length l2) -  (S i))))%nat then  Q else - Q)  ->

  (forall i j, i <length l2 -> j < ((length l2) - (S i))%nat ->
    phi deg (S (S j)) (nth i l2 p) != P0) ->
  
  l2 = a :: b :: l5 ->

  rec_det (phi deg ((length l1) + (length l2))%nat)
  (det_aux1 phi deg (k + length l2)) (app l4 l2) l3 !=
  (Zpolpower_nat (div2 (S (length l2))))* (Pol_pow Q (N_of_nat (length l2)))*
  (rec_det
    (phi (deg - (length l2))%nat (S k))
      (det_aux1 phi (deg -(length l2))%nat k) l4 l3).
  Proof.
    intros deg p Q;induction n ;intros k l1 l2 l3 l4 l5 a b H1 H2 H3 H4 H5 H6 H7;
    subst l1; subst l2. 
    destruct l4;simpl app in *|-*;length_blast;simpl plus.


(* il faut monter un lemme = 0 pour le cas l4 = nil*)



(*Focus! cf plus bas*)
 
(* pour le sous-but 2:
   destruct l3;destruct l4;length_blast;try discriminate;try falso.
    simpl app in *|-*.
    simpl plus in *|-*.
    rewrite (rec_det_eq  (phi (deg - S (S (|l5 |))) 1)).
    simpl (rec_det (phi (deg - S (S (|l5 |))) 1)
         (det_aux1 phi (deg - S (S (|l5 |))) 0) nil 
         (app nil (p0 :: nil))).
    simpl app.
    simpl (det_aux1 phi  (deg - S (S (|l5 |)))%nat 0 nil).
    transitivity (det_aux1 phi deg (S (S (S (|l5 |)))) (p0 :: a :: b :: l5)).
    case_det_aux1 (S (S (S (|l5 |)))) (p0 :: a :: b :: l5).
    length_blast;falso.
    rewrite (@det_aux_trigQ (a::b::l5) (S (S (length l5))) p deg Q p0);
      length_blast;intuition.
      change p0 with (nth O (p0::nil) p).
  destruct i;try destruct i;try falso.
 apply H3;try omega.
  replace (S (S (S (|l5 |)) - i))%nat with  (S (S (S (S (|l5 |)) - S i)))%nat;
     [idtac|omega].
apply H4;trivial.
apply Pmul_comp;try reflexivity.
setoid ring.
unfold phi.
induction ( le_gt_dec (deg + 2)%nat 1);
  induction (le_gt_dec (deg - S (S (|l5 |)) + 2)%nat);try reflexivity;try falso.

*)




    transitivity P0;[idtac|simpl rec_det;setoid ring].
    destruct l3;try destruct l3;length_blast;try discriminate.
    transitivity ( rec_det (phi deg (1 + 0 + S (S (|l5 |))))
      (det_aux1 phi deg (S (S (|l5 |)))) (a :: b :: l5) 
      (p0 :: nil) + 
      (det_aux1 phi deg (S (S (S (|l5 |)))) (p0::a::b::l5)) -
      (det_aux1 phi deg (S (S (S (|l5 |)))) (p0::a::b::l5))).
    setoid ring.
    assert (aux : 
     det_aux1 phi deg (S (S (S (|l5 |)))) (p0 :: a :: b :: l5) !=
 rec_det (phi deg (1 + 0 + S (S (|l5 |))))
     (det_aux1 phi deg (S (S (|l5 |)))) (a :: b :: l5) 
     (p0 :: nil) + det_aux1 phi deg (S (S (S (|l5 |)))) (p0 :: a :: b :: l5)).
(*    rewrite (@det_aux_trigQ (a::b::l5) (S (S (|l5 |))) p deg Q p0).
?????Error: Impossible to unify "nat" with "pol"*)
    transitivity  
      ((Zpolpower_nat (div2 (S(S (S (|l5 |))) )))*
	(Pol_pow Q (N_of_nat (S (S (|l5 |)))))*(phi deg 1 p0)).
    simpl app in *|- *.
   apply (@det_aux_trigQ (a::b::l5) (S (S (|l5 |))) p deg Q p0);length_blast;intuition.
   change p0 with (nth O (p0::nil) p).
  destruct i;try destruct i;try falso.
   apply H3;try omega.
   replace (S (S (S (|l5 |)) - i))%nat with  (S (S (S (S (|l5 |)) - S i)))%nat;
     [idtac|omega].
   apply H4;trivial.
   case_det_aux1 (S (S (S (|l5 |)))) (p0 :: a :: b :: l5);
   [idtac|length_blast;falso].
   change (1 + 0 + S (S (|l5 |)))%nat with (S (S (S (|l5 |))))%nat.
   rewrite (rec_det_eq (phi deg (S (S (S (|l5 |)))))
        (det_aux1 phi deg (S (S (|l5 |)))) (p0 :: a :: b :: l5)).
   simpl app in *|-*.
   setoid ring.
   assert (u: phi deg 1 p0 != phi deg (S (S (S (|l5 |)))) p0).
   

   generalize (rec_det (phi deg (S (S (S (|l5 |)))))
        (det_aux1 phi deg (S (S (|l5 |)))) (a :: b :: l5) 
        (p0 :: nil)).
   setoid ring.

   



(* base case*)
Theorem det_aux_trigQ: forall l n p deg Q b,
  (forall i:nat, i> 1 -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < (n- (S j))   -> (j < n)%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat ->
    phi deg (S (n - i)) (nth i l p) !=
  if even_odd_dec (S (n - i)) then  Q else - Q)  ->
  (length l = n)%nat -> n>1 -> 
    det_aux1 phi deg (S n) (b::l) != 
    (Zpolpower_nat (div2 (S n)))*(Pol_pow Q (N_of_nat n))*(phi deg 1 b).
Proof.
   rewrite det

    symm

case_det_aux1 (S (S (S (|l5 |)))) (p0 :: a :: b :: l5).
    simpl plus.
    rewrite (rec_det_eq
      (phi deg (S (S (S (|l5 |))))) 
      (det_aux1 phi deg (S (S (|l5 |)))) 
       (p0 :: a :: b :: l5)).
    simpl app.
    transitivity (
 (phi deg (S (S (S (|l5 |)))) p0 *
    det_aux1 phi deg (S (S (|l5 |))) (a :: b :: l5))
 -
   (phi deg (S (S (S (|l5 |)))) p0 *
    det_aux1 phi deg (S (S (|l5 |))) (a :: b :: l5) -
    rec_det (phi deg (S (S (S (|l5 |))))) (det_aux1 phi deg (S (S (|l5 |))))
      (a :: b :: l5) (p0 :: nil))).
    generalize (rec_det (phi deg (S (S (S (|l5 |))))) (det_aux1 phi deg (S (S (|l5 |))))
     (a :: b :: l5) (p0 :: nil)).
    intro p1;setoid ring.
    generalize ( phi deg (S (S (S (|l5 |)))) p0 *
   det_aux1 phi deg (S (S (|l5 |))) (a :: b :: l5)).
    intro p1.
    setoid ring.
    


    transitivity  ((phi deg (S (S (S (|l5 |)))) p0 *
    det_aux1 phi deg (S (S (|l5 |))) (app nil (a :: b :: l5)))
     -
   (phi deg (S (S (S (|l5 |)))) p0 *
    det_aux1 phi deg (S (S (|l5 |))) (a :: b :: l5) -
    rec_det (phi deg (S (S (S (|l5 |))))) (det_aux1 phi deg (S (S (|l5 |))))
      (a :: b :: l5) (p0 :: nil))).
    generalize (rec_det (phi deg (S (S (S (|l5 |))))) (det_aux1 phi deg (S (S (|l5 |))))
     (a :: b :: l5) (p0 :: nil)).
    intro p1;setoid ring.
    

    case_det_aux1  (S (S (S (|l5 |)))) (p0 :: a :: b :: l5).
    symmetry;rewrite rec_det_eq.
    
   (phi deg (S (S (S (|l5 |)))) p0 *
   det_aux1 phi deg (S (S (|l5 |))) (app nil (a :: b :: l5))) - 
   (Zpolpower_nat (div2 (S (S (length l5)))))*
   (Pol_pow Q (N_of_nat (S (S (length l5)))))*
   (phi deg 1 p0)
    














(* base case*)
Theorem det_aux_trigQ: forall l n p deg Q b,
  (forall i:nat, i> 1 -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < (n- (S j))   -> (j < n)%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat ->
    phi deg (S (n - i)) (nth i l p) !=
  if even_odd_dec (S (n - i)) then  Q else - Q)  ->
  (length l = n)%nat -> n>1 -> 
    det_aux1 phi deg (S n) (b::l) != 
    (Zpolpower_nat (div2 (S n)))*(Pol_pow Q (N_of_nat n))*(phi deg 1 b).







    rewrite rec_det_eq.
    rewrite rec_det_eq.
    simpl (rec_det (phi deg (|l3 | + 0 + S (S (|@nil Pol|))))
      (det_aux1 phi deg (S (S (|@nil Pol|)))) nil
      (app (app l3 (a :: nil)) (b :: nil))).
    simpl length in *|-*.
    apply Ominus.
    case_det_aux1 2 (app l3 (b::nil)).
    
    


    rewrite rec_det_eq.

    apply Ominus.
    change a with (nth O (a::b::l5) p).
    replace (|l3 | + 0 + S (S (|l5 |)))%nat with (S (S ((|l3 |) +  (|l5 |))))%nat;
      [idtac|omega].
    rewrite H5.



 
    destruct l3;try destruct l3;length_blast;try discriminate.
    simpl plus.
    destruct l2;try destruct l2;try discriminate.
    length_blast.
    rewrite rec_det_eq.
    simpl app in *|- *.
    assert (Aux1 :  det_aux1 phi deg (S (S (|l2 |))) (p0 :: p2 :: l2) != P0).
    apply (@minor (S (|l2 |)) (S (|l2 |)) (p2::l2) p deg p2 p0);intuition.
    change p0 with (nth O (p0::nil) p).
    destruct i;try destruct i;try falso.
    apply H3;omega.
    change p2 with (nth 1 (p1::p2::l2) p).
    destruct i;try destruct i;try falso.
    apply H5;try omega.

  case_det_aux1 (S (S (|l2 |))) (p0 :: p2 :: l2).






Theorem minor: forall m n l p deg b x,
(forall i:nat, (1 < i)%nat -> (i <= S n)%nat -> phi deg i x != P0) ->
  (forall i:nat, (1 < i)%nat -> (i < S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < S (n-j) -> i>1  -> (j < n)%nat -> 
    phi deg i (nth j l p) != P0) ->
  PIn b l -> n = length l -> m > 1 -> m <= n -> 
  det_aux1 phi deg (S m) (x::l) != P0. 


    rewrite rec_det_eq.
    simpl app in *|- *.
    apply Ominus.
    change p0 with (nth O (p0::nil) p).
    rewrite H3;auto with arith;setoid ring.
    rewrite rec_det_eq.
    apply Ominus.
    
    change p2 with (nth 1 (p1::p2::l2) p).
    rewrite H5.
  
    apply (@minor_rec 



    change p1 with (nth O (p1::p2::l2) p).
 rewrite H5.

    assert (Aux1 :det_aux1 phi deg (S (S (|l2 |))) (p0 :: p2 :: l2) != P0).
    case_det_aux1 (S (|l2 |)) (p0 :: l2).




    [idtac|length_blast;falso].
    change p1 with (nth O (p1::l2) p).
    length_blast.
    rewrite H5.

    simpl (rec_det (phi (deg - |l2 |) 1) (det_aux1 phi (deg - |l2 |) 0) nil l3).
    replace  (|l3 | + 0 + |l2 |)%nat with  (|l3 | + |l2 |)%nat;
      [idtac|omega].
    induction l2.
    simpl rec_det;setoid ring.
    rewrite rec_det_eq.


    destruct l4;try destruct l4;destruct l3;length_blast;try discriminate;try falso.
    simpl app in * |- *.
    simpl plus in *|- *.
    destruct l2;length_blast.
    unfold Zpolpower_nat; simpl.
    replace (deg - O)%nat with deg;[idtac|omega].
    repeat rewrite  Pol_sub_c0';Pcsimpl;setoid ring.
    destruct l2.
    unfold Zpolpower_nat; simpl.
    repeat rewrite  Pol_sub_c0';Pcsimpl.
    change x with (nth O (x::nil) p).
    rewrite H3;try omega.
    setoid ring.
    change p0 with (nth O (p0::nil) p).

    length_blast.
    rewrite (H4 O);auto with arith.
    simpl;Pcsimpl;setoid ring.
    unfold phi.
    induction (le_gt_dec (deg + 2) 1);
    induction (le_gt_dec (deg - 1 + 2) 1);setoid ring;try falso.
    replace (rec_det (phi deg (S (S (|p1::l2 |))))
      (det_aux1 phi deg (S (|p1::l2 |))) (x :: p0::p1::l2) nil)
    with (det_aux1 phi deg (S (S (length (p1::l2) ))) (x::p0::p1::l2)).
    simpl rec_det.
    rewrite Pol_sub_c0';Pcsimpl.
    setoid_replace (phi (deg - S (S (|l2 |))) 1 x) with (phi deg 1 x).
   apply (@det_aux_trigQ (p0::p1::l2) (S (length (p1::l2))) p deg Q x);length_blast;intuition.
    change x with (nth O (x::nil) p).
    destruct i;try destruct i;try falso.
    apply H3;auto with arith.
    replace  (S (S (S (|l2 |)) - i)) with (S (S (S (S (|l2 |)) - S i)));[idtac|omega].
    apply H4;auto with arith.
    unfold phi.
    induction (le_gt_dec (deg - S (S (|l2 |)) + 2) 1);
      induction (le_gt_dec (deg + 2) 1);try falso;reflexivity.
    case_det_aux1 (S (S (|p1 :: l2 |))) (x :: p0 :: p1 :: l2).
    length_blast;falso.
    destruct l4.
    simpl app in *|- *.
    symmetry ;rewrite rec_det_eq.
    simpl (    rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (x :: nil))).

    simpl app in *|- *.
    rewrite rec_det_eq.
    assert (Aux :
      det_aux1 phi deg (S k + |l2 |) (app l3 (app l4 l2)) !=
      Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
      det_aux1 phi (deg - (length l2))%nat (S k) (app l3 l4)).
    subst l1.
    replace (S k + |l2 |)%nat with (S (k + (length l2)))%nat;try omega.
    case_det_aux1 (S k + |l2 |)%nat (app l3 (app l4 l2));length_blast;
    [idtac|falso].
    induction (eq_nat_dec (|l3 | + (|l4 | + |l2 |)) (S (k + |l2 |)));try falso.
    rewrite <




Theorem tail :  forall deg p k l1 l2' l2 l3 l4 a b,
  S k = length l1 ->
  l2'= a:: b::l2 ->
  (forall i j, i < length l1 -> j< length l2' -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i j, i <(length l2') -> j <= ((length l2') - (S i))%nat ->
    phi deg (S (S j)) (nth i l2' p) != P0) ->

  l1 = app l3 l4 ->

  rec_det (phi deg ((length l1) + (length l2'))%nat)
  (det_aux1 phi deg (k + (length l2'))%nat)
  (app l4 l2') l3 != P0. 
  Proof.
    intros deg p;induction k;intros l1 l2' l2 l3 l4 a b H1 H2 H3 H4 H5;subst l2'.
    destruct l1;simpl in H1;try discriminate.
    destruct l1;simpl in H1;try discriminate.
    destruct l3;destruct l4;try discriminate.
    simpl app in *|- *.
    inversion H5;subst l4.
    simpl app in *|-*;length_blast;simpl plus.
    transitivity (det_aux1 phi deg (S (S (S (length l2)))) (p1 :: a :: b::l2)).
    case_det_aux1 (S (S (S (length l2)))) (p1 :: a :: b::l2).
    length_blast;falso.
    subst p1.
    rewrite (@det_aux_trigQ (a::b::l2) (S (S (length l2))) p deg P0 p0);
      intuition.
    destruct i;try  destruct i;try discriminate;try falso.
    change p0 with (nth O (p0::nil) p).
    apply H3;try omega.
    case (even_odd_dec (S (S (S (|l2 |)) - i)));(intro G;
    replace (S (S (S (|l2 |)) - i)) with (S (S (S (|l2 |) - i)));[idtac|omega];
      rewrite H4;try omega;setoid ring).
    rewrite Pol_powP0;setoid ring.
    simpl app;length_blast;simpl plus.
    destruct l3;simpl in H5;try discriminate.
    rewrite rec_det_eq.
 (*   change a with (nth O (a::b::l2) p).
 rewrite H4.Error: Impossible to unify "nat" with "pol"*)
    apply Ominus.
   change a with (nth O (a::b::l2) p).
    rewrite H4;auto with arith;setoid ring.
    simpl app.
    inversion H5;subst p1.
    apply (@minor_rec  (b :: l2) (S (S (|l2 |)))(b :: l2) (@nil Pol)  a p0 deg p);
      length_blast;intuition.
    change p0 with (nth O (p0::nil) p).
    destruct i;try destruct i;try discriminate;try falso.
    apply H3;try omega.
    simpl in H5;destruct l3;simpl in H5;discriminate.
    length_blast.
    destruct l4;simpl app.
    rewrite <- app_nil_end in H5.
    subst l3.
    destruct l1;simpl in H1;try discriminate.
    destruct l1;simpl in H1;try discriminate.
    length_blast.
    rewrite <- H1.
    replace  (S (S k) + S (S (|l2 |)))%nat with (S (S k + S (S (|l2 |))));
      [idtac|omega].
    apply (@minor_rec (a::b::l2) (S k + S (S (|l2 |))) (app l1 (a::b::l2))
      l1 p1 p0 deg p);length_blast;intuition.
    
    

Lemma minor_rec : forall l1 n l l2 a b deg p,
  (forall i : nat, i > 1 -> i <=  n -> phi deg i b != P0) ->
  (forall i j : nat,
       i < n - (S j) -> j < n -> phi deg (S (S i)) (nth j (a :: l) p) != P0)->
  (|a :: l | = n)->
  (n > 1) ->
  (|b :: a :: l | = S n) ->
  l = app l2 l1 ->
   rec_det (phi deg (S n)) (det_aux1 phi deg n) l1 (b :: a :: l2)
   != P0.




    induction l2.
    length_blast.
    inversion H5.
    subst p1.
    rewrite rec_det_eq.
   apply Ominus.
   change a with (nth O (a::b::nil) p).
   rewrite H4;auto with arith;setoid ring.
 rewrite rec_det_eq.
 simpl rec_det.
 simpl app.
 case_det_aux1 2 (p0 :: a :: nil);[idtac|length_blast;falso].
 rewrite rec_det_eq.
 change p0 with (nth O (p0::nil) p).
 (*rewrite H3.^^^^^^
Error: Impossible to unify "nat" with "pol"*)
 apply Ominus;try reflexivity.
 apply Oprod_r.
 apply Ominus.
 rewrite H3;auto with arith;setoid ring.
 rewrite rec_det_eq.
 simpl rec_det.
  change a with (nth O (a::b::nil) p).
   rewrite H4;auto with arith;setoid ring.
 rewrite rec_det_eq.
 
 






Theorem rec_det_partial_trig : forall deg p Q k l1 l2 l3 l4 x,
  (S k) = length l1  ->
  l1 = app l3 (x::l4) ->

  (forall i j, i < length l1 -> j< length l2 -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i, i < length l2  ->
    phi deg (S (S ((length l2) -  (S i))))%nat (nth i l2 p) !=
    if even_odd_dec (S (S ((length l2) -  (S i))))%nat then  Q else - Q)  ->

  (forall i j, i <length l2 -> j < ((length l2) - (S i))%nat ->
    phi deg (S (S j)) (nth i l2 p) != P0) ->


  rec_det (phi deg ((length l1) + (length l2))%nat)
  (det_aux1 phi deg (k + length l2)) (app (x::l4) l2) l3 !=
  (Zpolpower_nat (div2 (S (length l2))))* (Pol_pow Q (N_of_nat (length l2)))*
  (rec_det
    (phi (deg - (length l2))%nat (S k))
      (det_aux1 phi (deg -(length l2))%nat k)
      (x::l4) l3).
  Proof.
    intros deg p Q;induction k;intros l1 l2 l3 l4 x H1 H2 H3 H4 H5.
    subst l1.
    destruct l4;try destruct l4;destruct l3;length_blast;try discriminate;try falso.
    simpl app in * |- *.
    simpl plus in *|- *.
    destruct l2;length_blast.
    unfold Zpolpower_nat; simpl.
    replace (deg - O)%nat with deg;[idtac|omega].
    repeat rewrite  Pol_sub_c0';Pcsimpl;setoid ring.
    destruct l2.
    unfold Zpolpower_nat; simpl.
    repeat rewrite  Pol_sub_c0';Pcsimpl.
    change x with (nth O (x::nil) p).
    rewrite H3;try omega.
    setoid ring.
    change p0 with (nth O (p0::nil) p).

    length_blast.
    rewrite (H4 O);auto with arith.
    simpl;Pcsimpl;setoid ring.
    unfold phi.
    induction (le_gt_dec (deg + 2) 1);
    induction (le_gt_dec (deg - 1 + 2) 1);setoid ring;try falso.
    replace (rec_det (phi deg (S (S (|p1::l2 |))))
      (det_aux1 phi deg (S (|p1::l2 |))) (x :: p0::p1::l2) nil)
    with (det_aux1 phi deg (S (S (length (p1::l2) ))) (x::p0::p1::l2)).
    simpl rec_det.
    rewrite Pol_sub_c0';Pcsimpl.
    setoid_replace (phi (deg - S (S (|l2 |))) 1 x) with (phi deg 1 x).
   apply (@det_aux_trigQ (p0::p1::l2) (S (length (p1::l2))) p deg Q x);length_blast;intuition.
    change x with (nth O (x::nil) p).
    destruct i;try destruct i;try falso.
    apply H3;auto with arith.
    replace  (S (S (S (|l2 |)) - i)) with (S (S (S (S (|l2 |)) - S i)));[idtac|omega].
    apply H4;auto with arith.
    unfold phi.
    induction (le_gt_dec (deg - S (S (|l2 |)) + 2) 1);
      induction (le_gt_dec (deg + 2) 1);try falso;reflexivity.
    case_det_aux1 (S (S (|p1 :: l2 |))) (x :: p0 :: p1 :: l2).
    length_blast;falso.
    destruct l4.
    simpl app in *|- *.
    symmetry ;rewrite rec_det_eq.
    simpl (    rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (x :: nil))).

    simpl app in *|- *.
    rewrite rec_det_eq.
    assert (Aux :
      det_aux1 phi deg (S k + |l2 |) (app l3 (app l4 l2)) !=
      Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
      det_aux1 phi (deg - (length l2))%nat (S k) (app l3 l4)).
    subst l1.
    replace (S k + |l2 |)%nat with (S (k + (length l2)))%nat;try omega.
    case_det_aux1 (S k + |l2 |)%nat (app l3 (app l4 l2));length_blast;
    [idtac|falso].
    induction (eq_nat_dec (|l3 | + (|l4 | + |l2 |)) (S (k + |l2 |)));try falso.
    rewrite <- app_ass.
    caseEq (app l3 l4).
    intro G.
    destruct l3;destruct l4;try discriminate.
    intros p0 l G. 
    simpl app.
    rewrite <- a1.
    replace  (|l3 | + (|l4 | + |l2 |))%nat 
      with ((length (p0::l)) + (length l2))%nat;
      [idtac|rewrite <- G;length_blast;omega].
    rewrite (IHk (p0::l) l2 (@nil Pol) l p0 a b l5);try rewrite <- G;intuition.
    length_blast; omega.
    induction (le_gt_dec (length l3) i).
    rewrite nth_app_r;trivial.
    change (nth (i - |l3 |) l4 p) with (nth (S (i - |l3 |)) (x::l4) p).

    replace  (S (i - |l3 |))%nat with  ((S i) - |l3 |)%nat;
      [idtac|length_blast;omega].
    rewrite <- (@nth_app_r Pol l3 (x::l4) p (S i));auto with arith.
    apply H3;length_blast;omega.
    rewrite nth_app_l;trivial.
    rewrite <- (@nth_app_l Pol l3 (x::l4) p i);auto with arith.
    case_det_aux1 (S k) (app l3 l4).
    length_blast;falso.
    destruct l4.
    simpl app.



    symmetry;rewrite rec_det_eq.
    assert (Aux2 : Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
      ( rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      l4 (app l3 (x :: nil))) !=
  rec_det (phi deg (|l1 | + |l2 |)) (det_aux1 phi deg (S k + |l2 |))
        (app l4 l2) (app l3 (x :: nil))).

    simpl (  rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
     nil (app l3 (x :: nil))).
    simpl app.
    subst l1.
    rewrite <- H1;length_blast.
    destruct l3;length_blast;try discriminate.
    caseEq (app (p0::l3) (x::nil)).
    intro G;list_blast;discriminate.
    intros p1 l G.
    destruct l;simpl in G;inversion G.
    destruct l3;simpl in H2;discriminate.
    rewrite H2.
    replace (S (S k) + (|l2 |))%nat with (S (S (k + (length l2))))%nat;
    [idtac|omega].
    replace (S k + |l2 |)%nat with (S (k + |l2 |))%nat;
       [idtac|omega].
    simpl app in *|- *.
    rewrite (@minor_rec l2 (S (k + (length l2))) (app l l2) l p2 p1 deg p);
      length_blast;intuition.
    rewrite G in H3.
    change p1 with (nth O (p1::p2::l) p).
    destruct i;try destruct i;try falso.
    apply H3;auto with arith.
    omega.
    
    
    

    replace  (S (S k) + S (S (|l5 |)))%nat with (S (S (k +  S (S (|l5 |)))))%nat;
      [idtac|omega].
    replace (S k + S (S (|l5 |)))%nat with (S (k + S (S (|l5 |))))%nat;
        [idtac|omega].
    rewrite (@minor_rec (S (k + S (S (|l5 |)))) ?  (a :: b :: l5)
    





    assert (test :
   phi (deg - |l2 |) (S (S k)) x  !=
     phi deg (|l1 | + |l2 |) x ).
    rewrite <- H1.
    unfold phi;simpl;
    induction (le_gt_dec (deg - |l2 | + 2) (S (S k)));
    induction (le_gt_dec (deg +2)  ((S (S k)) + |l2 |));try falso.
    induction ( le_gt_dec (deg + 2) (S (S (k + |l2 |))));[reflexivity|falso].
    induction (le_gt_dec (deg + 2) (S (S (k + |l2 |))));[falso|idtac].


    setoid ring.
    apply Pmul_comp;try reflexivity.
    apply Pmul_comp;try reflexivity.
    



   Lemma titi : forall P Q R, Pol_mul P (Pol_sub Q  R) != P*Q - P*R.
      intros.
	setoid ring.
Qed.
    rewrite (titi
      (Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)))
      (phi (deg - |l2 |) (S (S k)) x *
    det_aux1 phi (deg - |l2 |) (S k) (app l3 l4))).
    simpl ( rec_det (phi (deg - |l2 |) (S (S k))) (det_aux1 phi (deg - |l2 |) (S k))
      nil (app l3 (x :: nil))).
    destruct l2.
    simpl rec_det.
    simpl Pol_pow.
    simpl Zpolpower_nat.
    rewrite H1.
    length_blast.
    replace  (deg - 0)%nat with deg;[idtac|auto with arith].
    replace (|l1 | + 0)%nat with (|l1 |);[idtac|auto with arith].
    replace  (S k + 0)%nat with (S k);[idtac|auto with arith].
    setoid_replace ( Zpolpower_nat 0 * P1) with P1;[idtac|unfold Zpolpower_nat;simpl;Pcsimpl;reflexivity].
    setoid ring.
    destruct l2.
    rewrite rec_det_eq.
    simpl ( rec_det (phi deg (|l1 | + |p0 :: nil |))
         (det_aux1 phi deg (S k + |p0 :: nil |)) nil
         (app (app l3 (x :: nil)) (p0 :: nil))).
    repeat rewrite <- app_nil_end.
    assert (toto : det_aux1 phi deg (S k + |p0 :: nil |) (app l3 (x :: nil)) != P0).
    length_blast.
    replace (S k + 1)%nat with (S (S k));[idtac|auto with arith].
    case_det_aux1 (S (S k)) (app l3 (x :: nil)).
    



    assert (Aux2 : rec_det (phi deg (|l1 | + |l2 |)) (det_aux1 phi deg (S k + |l2 |))
      l2 (app l3 (x :: nil)) != P0).

    reflexivity.
    destruct l2.
    rewrite rec_det_eq.
    simpl rec_det.
    rewrite <- app_nil_end.
    length_blast.
    replace (|l1 | + 1)%nat with (S (S (S k))).
    change p0 with (nth O (p0::nil) p).
    rewrite H5;auto.
    
    list_blast.

    
    




Theorem rec_det_partial_trig : forall deg p Q k l1 l2 l3 l4 x,
  (S k) = length l1  ->
  l1 = app l3 (x::l4) ->

  (forall i j, i < length l1 -> j< length l2 -> 
    phi deg (S (S j)) (nth i l1 p) != P0) ->

  (forall i, i < length l2  ->
    phi deg (S (S ((length l2) -  (S i))))%nat (nth i l2 p) !=
    if even_odd_dec (S (S ((length l2) -  (S i))))%nat then  Q else - Q)  ->

  (forall i j, i <length l2 -> j < ((length l2) - (S i))%nat ->
    phi deg (S (S j)) (nth i l2 p) != P0) ->

  rec_det (phi deg ((length l1) + (length l2))%nat)
  (det_aux1 phi deg (k + length l2)) (app (x::l4) l2) l3 !=
  (Zpolpower_nat (div2 (S (length l2))))* (Pol_pow Q (N_of_nat (length l2)))*
  (rec_det (phi deg (S k)) (det_aux1 phi deg k) (x::l4) l3).
  Proof.
    intros deg p Q;induction k;intros l1 l2 l3 l4 x H1 H2 H3 H4 H5.
    subst l1.
    destruct l4;try destruct l4;destruct l3;length_blast;try discriminate;try falso.
    simpl app in * |- *.
    simpl plus in *|- *.
    destruct l2;length_blast.
    unfold Zpolpower_nat; simpl.
    repeat rewrite  Pol_sub_c0';Pcsimpl;setoid ring.
    destruct l2.
    unfold Zpolpower_nat; simpl.
    repeat rewrite  Pol_sub_c0';Pcsimpl.
    change x with (nth O (x::nil) p).
    rewrite H3;try omega.
    change p0 with (nth O (p0::nil) p).
    length_blast.
    rewrite (H4 O);auto with arith.
    simpl;Pcsimpl;setoid ring.
    replace (rec_det (phi deg (S (S (|p1::l2 |))))
      (det_aux1 phi deg (S (|p1::l2 |))) (x :: p0::p1::l2) nil)
    with (det_aux1 phi deg (S (S (length (p1::l2) ))) (x::p0::p1::l2)).
    simpl rec_det.
    rewrite Pol_sub_c0';Pcsimpl.
    apply (@det_aux_trigQ (p0::p1::l2) (S (length (p1::l2))) p deg Q x);length_blast;intuition.
    change x with (nth O (x::nil) p).
    destruct i;try destruct i;try falso.
    apply H3;auto with arith.
    replace  (S (S (S (|l2 |)) - i)) with (S (S (S (S (|l2 |)) - S i)));[idtac|omega].
    apply H4;auto with arith.
    case_det_aux1 (S (S (|p1 :: l2 |))) (x :: p0 :: p1 :: l2).
    length_blast;falso.
    simpl app in *|- *.
    rewrite rec_det_eq.




    
    



































Lemma titi : forall l1 l2 f rec b,
  (forall x y, x != y -> f x != f y) ->
  (f b) != P0 ->
  (forall l, PIn b l -> rec l != P0) -> PIn b l2 ->
 rec_det f rec  l1 l2 != P0.
Proof.
induction l1;intros l2 f rec b H0 H1 H2 H3.
reflexivity.
destruct l2.
elim H3.
inversion H3;simpl.
rewrite H2.
left;trivial.
assert (Aux :  rec_det f rec l1 (p :: app l2 (a :: nil)) != P0).
apply IHl1 with b;try assumption.
left;trivial.
rewrite Aux.
setoid ring.
fold PIn in H.
rewrite H2.
right.
apply PIn_PIn_app_r;trivial.
assert (Aux : rec_det f rec l1 (p :: app l2 (a :: nil)) != P0).
apply IHl1 with b;try assumption.
right;apply PIn_PIn_app_r;trivial.
rewrite Aux;setoid ring.
Qed.

Lemma titi2 : forall l1 l2 f rec b,
  (forall x y, x != y -> f x != f y) ->
  (f b) != P0 ->
  (forall l u, PIn b l -> ((f u) != P0) -> rec (u :: l) != P0) -> PIn b l2 ->
 rec_det f rec  l1 l2 != P0.
Admitted.



Lemma toto2 : forall l1 l2 f rec x b,
  (forall x y, x != y -> f x != f y) ->
  (f b) != P0 ->
  (forall l u, PIn b l -> ((f u) != P0) -> rec (u::l) != P0) -> PIn b l1 ->
  rec_det f rec (x :: l1) l2 != P0.
Admitted.

Lemma toto : forall l1 l2 f rec x b,
  (forall x y, x != y -> f x != f y) ->
  (f b) != P0 ->
  (forall l, PIn b l -> rec l != P0) -> PIn b l1 ->
  rec_det f rec (x :: l1) l2 != P0.
Proof.
induction l1;intros l2 f rec x b H0 H1 H2 H3.
elim H3.
inversion H3.
simpl.
destruct l1.
simpl.
Pcsimpl.
transitivity (P0 - P0);[apply Psub_comp|setoid ring].
rewrite H2;[idtac|setoid ring].
apply PIn_PIn_app_l;left;trivial.
rewrite (H0 a b H);rewrite H1;setoid ring.
transitivity (P0 - P0);[idtac|setoid ring].
apply Psub_comp.
rewrite H2;[idtac|setoid ring].
apply PIn_PIn_app_l;left;trivial.
transitivity (P0 - P0);[idtac|setoid ring].
apply Psub_comp.
rewrite (H0 a b H);rewrite H1;setoid ring.
assert (Aux : PIn b (app (app l2 (x :: nil)) (a :: nil))).

apply PIn_PIn_app_l;left;trivial.
generalize Aux;generalize  (app (app l2 (x :: nil)) (a :: nil)).
generalize (p::l1).
induction l;intros l0 G;simpl.
setoid ring.
transitivity (P0 - P0).
apply Psub_comp.
rewrite H2.
apply PIn_PIn_app_r;trivial;setoid ring.
setoid ring.
apply IHl.
apply PIn_PIn_app_r;trivial.
setoid ring.
fold PIn in H.


generalize (refl_equal (a::l1)).
pattern (a::l1) at -1.
simpl rec_det.
case (a::l1).
intros z k  G;rewrite <- G;clear G k z.
transitivity (P0 - P0);[idtac|setoid ring].
apply Psub_comp.
rewrite H2;[idtac|setoid ring].
apply PIn_PIn_app_l.
right;trivial.
apply IHl1 with b;try assumption.
Qed.


Fixpoint det_aux1(phi:nat -> nat -> Pol -> Pol)(deg : nat)(n : nat)(l : list Pol)
  {struct n}:Pol:=
  if eq_nat_dec (length l) n then 
    (match n with
      O => P1
      | S n1 => rec_det (phi deg n) (det_aux1 phi deg n1) l nil
    end)
    else P0.
    




(*

Lemma w_rec_det_ext : forall rec1 rec2 ,
  (forall x, rec1 x != rec2 x ) -> 
  forall f l1 l2, rec_det f rec1 l1 l2 != rec_det f rec2 l1 l2.
intros rec1 rec2 H f.
induction l1;intros l2.
reflexivity.
simpl.
rewrite H.
rewrite IHl1.
reflexivity.
Qed.

Ltac dr_subst1 t f :=
  match t with
    | context c [rec_det ?x ?g ?l ?m != ?u ] =>
      let t2 := context c [rec_det x f l m] in constr:t2
  end.
Ltac dr_subst f := 
  match goal with
    | |- ?a != ? b =>
      match a with
	|context c [rec_det _ _ _ _ ] =>
	  let t2 := dr_subst a f in
	    transitivity t2;[apply w_rec_det_ext|idtac]
	|_ =>
	   match b with
	|context c [rec_det _ _ _ _ ] =>
	  let t2 := dr_subst b f in
	    transitivity t2;[idtac|apply w_rec_det_ext]
	   end
      end
  end.
*)


Lemma nth_app_l : forall A l1 l2 p j,
  j < @length A l1 -> nth j (app l1 l2) p = nth j l1 p.
intros A;induction l1;intros l2 p j G.
simpl in G;apply False_ind;omega.
destruct j.
reflexivity.
simpl.
simpl in G.
apply IHl1;omega.
Qed.

Lemma nth_ex : forall A l p j,
j >= @length A l -> nth j l p = p.
Proof.
intros A;induction l;intros p j H.
destruct j;reflexivity.
destruct j.
simpl in H;apply False_ind;omega.
simpl.
apply IHl.
simpl in H;omega.
Qed.

Lemma nth_app_r :  forall A l1 l2 p j,
  j >= @length A l1 -> nth j (app l1 l2) p = nth (j - (length l1)) l2 p.
intros A;induction l1;intros l2 p j G.
replace (j - (@length A nil))%nat with j;auto with arith.
destruct j.
simpl in G;apply False_ind;omega.
destruct l2.
repeat rewrite nth_ex;simpl in * |- *;trivial;try omega.
rewrite <- app_nil_end;trivial.
replace (S j - (|a :: l1 |))%nat with (j - (|l1|))%nat;[idtac|reflexivity].
rewrite <- IHl1.
reflexivity.
simpl in G;omega.
Qed.


Theorem minor: forall m n l p deg b x,
(forall i:nat, (1 < i)%nat -> (i <= S n)%nat -> phi deg i x != P0) ->
  (forall i:nat, (1 < i)%nat -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < S (n-j) -> i>1  -> (j < n)%nat -> 
    phi deg i (nth j l p) != P0) ->
  PIn b l -> n = length l -> m > 1 -> m <= n -> 
  det_aux1 phi deg (S m) (x::l) != P0. 
induction m;intros n l p deg b x H1 H2 H3 H4 H5 H6 H7.
apply False_ind;omega.
destruct l.
simpl in H5; apply False_ind;omega.
case_det_aux1 (S (S m)) (x :: p0 :: l).
rewrite rec_det_eq.
apply Ominus.
rewrite H1;auto with arith;setoid ring.
inversion H4.
rewrite rec_det_eq.
apply Ominus.
rewrite H;rewrite H2;auto with arith;setoid ring.
simpl app.

assert (Aux : forall l1 l2,
 l = app l2 l1 ->
rec_det (phi deg (S (S m))) (det_aux1 phi deg (S m)) l1 (x::p0::l2)!=P0).
induction l1;intros l2 G.
reflexivity.
rewrite rec_det_eq.
apply Ominus.
simpl app.

induction (le_gt_dec 2 m).
rewrite (IHm  m (p0::app l2 l1) p deg b x);intuition.
destruct j.
replace (nth 0 (p0 ::app l2 l1)) with (nth 0 (p0::l));trivial.
apply H3;auto with arith;omega.
replace (nth (S j) (p0 ::app l2 l1) p) with (nth j (app l2 l1) p);trivial.
rewrite G in H3.
induction (le_gt_dec (length l2) j).
rewrite nth_app_r;trivial.
replace (nth (j - (length l2)) l1 p) with (nth (S j - (length l2)) (a0::l1) p).
rewrite <- (nth_app_r l2 (a0::l1) p);auto with arith.
replace  (nth (S j) (app l2 (a0 :: l1)) p) with 
 (nth (S (S j)) (p0 ::(app l2 (a0 :: l1))) p);trivial.
apply H3;omega.
replace (S j - (length l2))%nat with (S (j - (length l2)))%nat;try reflexivity.
omega.
rewrite nth_app_l;try omega.
rewrite <- (nth_app_l  l2 (a0::l1));trivial.
replace  (nth j (app l2 (a0 :: l1)) p) with  (nth (S j) (p0::(app l2 (a0 :: l1))) p);trivial.
apply H3;auto with arith;omega.
left;trivial.
transitivity (length (app l2 (a0::l1))).
rewrite <- G.
simpl in *|-*;omega.
simpl;repeat rewrite length_app;simpl;auto with arith.
setoid ring.

generalize (app l2 l1);intro l'.
destruct m.
case_det_aux1 1 (x::p0::l').
simpl in a1;discriminate.
setoid ring.
destruct m.
case_det_aux1 2 (x::p0::l');[idtac|setoid ring].
destruct l';[idtac|discriminate].
rewrite rec_det_eq.
apply Oprod_r.
apply Ominus.
rewrite H1;try omega;setoid ring.
rewrite rec_det_eq.
apply Ominus.
rewrite H;rewrite H2;try omega;setoid ring.
reflexivity.
apply False_ind;omega.
simpl app.
apply IHl1.
rewrite app_ass.
trivial.
apply Aux;trivial.
fold PIn in H.
simpl app.
destruct m.
apply False_ind;omega.
destruct m.
rewrite rec_det_eq.
destruct l;[simpl in a;discriminate|destruct l;[idtac|simpl in a;discriminate]].
apply Ominus.
simpl app.
rewrite det_aux1_eq.
case (eq_nat_dec (|x::p1::nil|) 2);intro G;
[rewrite rec_det_eq|apply False_ind;elim G].
apply Oprod_r.
apply Ominus.
rewrite H1;auto with arith;setoid ring.
rewrite rec_det_eq.
apply Ominus;[idtac|reflexivity].
elim H;[intro G1|apply False_ind].
rewrite G1;rewrite H2;auto with arith;setoid ring.
reflexivity.
rewrite rec_det_eq.
apply Ominus;try reflexivity.
simpl app.
case_det_aux1 2 (x :: p0 :: nil).
apply Oprod_l;try setoid ring.
case H;[intro G;rewrite G|apply False_ind].
apply H2;auto with arith.
setoid ring.
assert (Aux : forall l1 l2,
p0::l = app l2 l1 -> rec_det (phi deg (S (S(S (S m))))) (det_aux1 phi deg (S (S (S m)))) l1 (x::l2) !=P0).
induction l1;intros l2 G.
reflexivity.
rewrite rec_det_eq.
apply Ominus.
assert (G1 : a0 != b \/(PIn b l1)\/(PIn b l2)). 
rewrite G in H4.
elim (PIn_app_PIn l2 (a0 :: l1) b H4);intro G1.
right;right;trivial.
simpl in G1.
intuition.
elim G1;clear G1;intro G2.
rewrite G2;rewrite H2;auto with arith;setoid ring.
simpl app.
rewrite (IHm (S (S m)) (app l2 l1) p deg b x);auto.
intros;apply H1;omega.
intros;apply H2;omega.
intros i j L1 L2 L3.
rewrite G in H3.
induction (le_gt_dec (length l2) j).
rewrite nth_app_r;trivial.
replace (nth (j - (length l2)) l1 p) with (nth (S j - (length l2)) (a0::l1) p).
rewrite <- (nth_app_r l2 (a0::l1) p);auto with arith.
apply H3;omega.
replace (S j - (length l2))%nat with (S (j - (length l2)))%nat;try reflexivity.
omega.
rewrite nth_app_l;try omega.
rewrite <- (nth_app_l  l2 (a0::l1));trivial.
apply H3;auto with arith;omega.
case G2;intro G2';[apply PIn_PIn_app_l|apply PIn_PIn_app_r];trivial.
rewrite G in a.
simpl in a;rewrite length_app in a;simpl in a.
rewrite length_app;omega.
auto with arith.
setoid ring.
simpl app.
apply IHl1.
rewrite app_ass.
trivial.
apply Aux.
trivial.
Qed.

Lemma minor_rec_aux : forall l1 l2 f rec x,
(forall l x, rec (x::l) != P0) ->
rec_det f rec l1 (x::l2) != P0.
Proof.
  induction l1;intros l2 f rec x H1.
  reflexivity.
  rewrite rec_det_eq.
  simpl app.
  rewrite H1.
  rewrite IHl1;trivial.
  setoid ring.
Qed.


Lemma minor_rec_aux2 : forall l1 l2 f rec x,
(forall l, length l = (length l1 + length l2)%nat -> rec l != P0) ->
rec_det f rec l1 (x::l2) != P0.
Proof.
  induction l1;intros l2 f rec x H1.
  reflexivity.
  rewrite rec_det_eq.
  simpl app.
  rewrite H1.
  simpl;rewrite length_app;simpl;omega.
  rewrite IHl1;trivial.
  rewrite length_app;simpl.
  intros;apply H1.
  simpl.
  replace (S((length l1) + (length l2)))%nat with ((length l1) + ((length l2) + 1))%nat;
    [apply H|omega].
  setoid ring.
Qed.
(*
Lemma minor_rec_aux3 :  forall l1 l2 l f rec x a b,
  rec (a::b::l) != P0 -> l = app l2 l1 -> 
rec_det f rec (x::l1) (a::b::l2) != P0.
  Proof.
    induction l1;intros l2 l f rec x  c b H1 H2;rewrite rec_det_eq;simpl app;rewrite <- H2.
    simpl rec_det.
    rewrite H1;setoid ring.
    rewrite H1.
    rewrite (IHl1 (app l2 (x::nil)) l 


    rewrite H1;
      [rewrite <- app_nil_end;simpl in *|- *;trivial | setoid ring].
    rewrite H1;
      [rewrite length_app;simpl in *|-* ; omega|idtac].
    rewrite (IHl1 (app l2 (x :: nil)) f rec a c b n);intuition.
    rewrite length_app;simpl in *|-* ; omega.
    setoid ring.
  Qed.
    
*)
 

Lemma minor_rec : forall l1 n l l2 a b deg p,
  (forall i : nat, i > 1 -> i <=  n -> phi deg i b != P0) ->
  (forall i j : nat,
       i < n - j -> j < n -> phi deg (S (S i)) (nth j (a :: l) p) != P0)->
  (|a :: l | = n)->
  (n > 1) ->
  (|b :: a :: l | = S n) ->
  l = app l2 l1 ->
   rec_det (phi deg (S n)) (det_aux1 phi deg n) l1 (b :: a :: l2)
   != P0.
  Proof.
    induction l1;intros n l l2 c b deg p H1 H2 H3 H4 H5 H6.
    reflexivity.
    rewrite rec_det_eq.
    destruct n.
    discriminate.
    destruct n.
    apply False_ind;omega.
    rewrite H6 in H2.
    rewrite H6 in H3.
    apply Ominus.
    apply Oprod_r.
    simpl app.
    destruct n.
    destruct l1;destruct l2;simpl app in * |- *;
      match goal with
	|- det_aux1 phi deg 2 ?l != P0 => case_det_aux1 2 l; try discriminate
      end.
    rewrite rec_det_eq.
    apply Ominus.
    rewrite H1;auto with arith;setoid ring.
    rewrite rec_det_eq.
    simpl rec_det.
    replace c with (nth O (c::a::nil) p);trivial.
    rewrite H2;auto with arith;setoid ring.
    apply minor with (S (S n)) p c;intuition.
    replace c with (nth O (c::(app l2 (a::l1))) p);trivial.
    destruct i.
    apply False_ind;omega.
    destruct i.
    apply False_ind;omega.
    apply H2;omega.
    destruct i.
    apply False_ind;omega.
    destruct i.
    apply False_ind;omega.
    destruct j.
    simpl.
    replace c with (nth O (c::(app l2 (a::l1))) p);trivial.
    apply H2;omega.
    replace (c::app l2 l1) with (app (c::l2) l1);trivial.
     replace (c::app l2 (a::l1)) with (app (c::l2) (a::l1)) in H2;trivial.
    induction (le_gt_dec (length (c::l2)) (S j)).
    rewrite nth_app_r;try omega.
    replace (nth (S j - |c :: l2 |) l1 p) with (nth (S ((S j) - |c :: l2 |)) (a::l1) p);trivial.
    replace (S (S j - |c :: l2 |)) with (S (S j) - |c :: l2 |)%nat;try omega.
    rewrite <- (@nth_app_r Pol (c::l2) (a::l1) p (S (S j)));try omega.
    apply H2;omega.
    rewrite nth_app_l;try omega.
    rewrite <- (@nth_app_l Pol (c::l2) (a::l1) p (S j));try omega.
    apply H2;omega.
    left;reflexivity.
    simpl in *|-*;rewrite length_app in H3;simpl in H3.
    rewrite length_app;omega.
    simpl app.
    apply (IHl1 (S (S n)) l (app l2 (a::nil)) c b deg p);intuition.
    rewrite  H6.
    apply H2; omega.
    rewrite app_ass.
    simpl;assumption.
    Qed.
(*
Lemma minor_rec : forall l1 n l l2 a b deg p,
  (forall i : nat, i > 1 -> i <= S n -> phi deg i b != P0) ->
  (forall i j : nat,
       i < n - j -> j < n -> phi deg (S (S i)) (nth j (a :: l) p) != P0)->
  (|a :: l | = n)->
  (n > 1) ->
  (|b :: a :: l | = S n) ->
  l = app l2 l1 ->
   rec_det (phi deg (S n)) (det_aux1 phi deg n) l1 (b :: a :: l2)
   != P0.
  Proof.
    induction l1;intros n l l2 c b deg p H1 H2 H3 H4 H5 H6.
    reflexivity.
    rewrite rec_det_eq.
    destruct n.
    discriminate.
    destruct n.
    apply False_ind;omega.
    rewrite H6 in H2.
    rewrite H6 in H3.
    apply Ominus.
    apply Oprod_r.
    simpl app.
    destruct n.
    destruct l1;destruct l2;simpl app in * |- *;
      match goal with
	|- det_aux1 phi deg 2 ?l != P0 => case_det_aux1 2 l; try discriminate
      end.
    rewrite rec_det_eq.
    apply Ominus.
    rewrite H1;auto with arith;setoid ring.
    rewrite rec_det_eq.
    simpl rec_det.
    replace c with (nth O (c::a::nil) p);trivial.
    rewrite H2;auto with arith;setoid ring.
    apply minor with (S (S n)) p c;intuition.
    replace c with (nth O (c::(app l2 (a::l1))) p);trivial.
    destruct i.
    apply False_ind;omega.
    destruct i.
    apply False_ind;omega.
    apply H2;omega.
    destruct i.
    apply False_ind;omega.
    destruct i.
    apply False_ind;omega.
    destruct j.
    simpl.
    replace c with (nth O (c::(app l2 (a::l1))) p);trivial.
    apply H2;omega.
    replace (c::app l2 l1) with (app (c::l2) l1);trivial.
     replace (c::app l2 (a::l1)) with (app (c::l2) (a::l1)) in H2;trivial.
    induction (le_gt_dec (length (c::l2)) (S j)).
    rewrite nth_app_r;try omega.
    replace (nth (S j - |c :: l2 |) l1 p) with (nth (S ((S j) - |c :: l2 |)) (a::l1) p);trivial.
    replace (S (S j - |c :: l2 |)) with (S (S j) - |c :: l2 |)%nat;try omega.
    rewrite <- (@nth_app_r Pol (c::l2) (a::l1) p (S (S j)));try omega.
    apply H2;omega.
    rewrite nth_app_l;try omega.
    rewrite <- (@nth_app_l Pol (c::l2) (a::l1) p (S j));try omega.
    apply H2;omega.
    left;reflexivity.
    simpl in *|-*;rewrite length_app in H3;simpl in H3.
    rewrite length_app;omega.
    simpl app.
    apply (IHl1 (S (S n)) l (app l2 (a::nil)) c b deg p);intuition.
    rewrite  H6.
    apply H2; omega.
    rewrite app_ass.
    simpl;assumption.
    Qed.
*)
Require Import Div2.



Theorem det_aux_trigQ: forall l n p deg Q b,
  (forall i:nat, i> 1 -> (i <= S n)%nat -> phi deg i b != P0) -> 
  (forall (i j:nat),  i < (n-j)   -> (j < n)%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat ->
    phi deg (S (n - i)) (nth i l p) !=
  if even_odd_dec (S (n - i)) then  Q else - Q)  ->
  (length l = n)%nat -> n>1 -> 
    det_aux1 phi deg (S n) (b::l) != 
    (Zpolpower_nat (div2 (S n)))*(phi deg 1 b)*(Pol_pow Q (N_of_nat n)).
Proof.
induction l;intros n p deg Q b H1 H2 H3 H4 H5.
simpl in H4;subst n;apply False_ind;omega.
destruct l.
simpl in H4;subst n;apply False_ind;omega.
case_det_aux1 (S n) (b::a::p0::l).
rewrite rec_det_eq.
transitivity
 (P0 -  rec_det (phi deg (S n)) (det_aux1 phi deg n) (a :: p0 :: l)
 (app nil (b :: nil))).
apply Psub_comp;try reflexivity.
rewrite H1;auto with arith;setoid ring.
rewrite rec_det_eq.
assert (Aux :  rec_det (phi deg (S n)) (det_aux1 phi deg n) (p0 :: l)
      (app (app nil (b :: nil)) (a :: nil)) != P0).
simpl app.
apply minor_rec with (p0::l) p;intuition.
rewrite Aux.
setoid ring.
simpl app.
destruct n;try discriminate.
destruct n;try discriminate.
destruct n.
destruct l;[idtac|simpl in *|-*;discriminate].
case_det_aux1 2 (b::p0::nil).
rewrite rec_det_eq.
simpl app.
transitivity (
 - P1 * phi deg 3 a *
(P0 - 
 rec_det (phi deg 2) (det_aux1 phi deg 1) (p0 :: nil) (b :: nil))).
apply Pmul_comp;try reflexivity.
apply Psub_comp;try reflexivity.
rewrite H1;try omega;setoid ring.
transitivity (phi deg 3 a * (rec_det (phi deg 2) (det_aux1 phi deg 1) (p0 :: nil) (b :: nil))).
setoid ring.
rewrite rec_det_eq.
simpl app.
simpl rec_det.
case_det_aux1 1 (b::nil).
rewrite rec_det_eq.
simpl rec_det.
simpl det_aux1.

rewrite (H3 1);auto with arith.
rewrite (H3 O);auto with arith.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
simpl in b0;apply False_ind;omega.
simpl in b0;apply False_ind;omega.
rewrite (IHl (S (S n)) p deg Q b);intuition.
replace (nth j (p0 :: l) p) with (nth (S j) (a::p0 :: l) p);trivial.
apply H2;omega.
replace  (nth i (p0 :: l) p) with  (nth (S i)  (a:: p0 :: l) p);trivial.
replace (S (S (S n) - i)) with (S (S (S (S n)) - (S i)));try omega.
rewrite H3;auto with arith;reflexivity.
rewrite (H3 O);auto with arith.
replace (S (S (S (S n)) - 0)) with (S (S (S (S n))));auto with arith.
replace (N_of_nat  (S (S (S n))))with ((N_of_nat (S (S n))) + 1)%N;
[rewrite Ppow_plus;simpl Pol_pow|simpl;repeat rewrite Pplus_one_succ_r;trivial].
unfold Zpolpower_nat.
case (even_odd_dec  (S (S (S (S n)))));intro G1;inversion G1;
case ( even_odd_dec (S (S (S n))));intro G2.
apply False_ind;apply (not_even_and_odd  (S (S (S n))));trivial.
setoid ring.

rewrite <- (odd_div2 (S (S (S n))));trivial. 
case (even_odd_dec (div2 (S (S (S n)))));intro G3.
case (even_odd_dec (S (div2 (S (S (S n))))));intro G4.
apply False_ind;apply (not_even_and_odd ((div2 (S (S (S n))))));trivial.
inversion G4;trivial.

setoid ring.
case (even_odd_dec (S (div2 (S (S (S n))))));intro G4.
setoid ring.
apply False_ind;apply (not_even_and_odd ((div2 (S (S (S n))))));trivial.
inversion G4;trivial.

rewrite <- (even_div2 (S (S (S n))));trivial.
case (even_odd_dec (div2 (S (S (S n)))));intro G3;setoid ring.
apply False_ind;apply (not_even_and_odd (S (S (S n))));trivial.
simpl in H4;simpl in b0;apply False_ind;omega.
Qed.


(* cas n= 1 marche aussi ... refaire la preuve ci-dessus!*)

Theorem  det_aux_trigQ1 : forall b a deg Q,
  phi deg 2 b != P0 ->
  phi deg 2 a != Q ->
 det_aux1 phi deg 2 (b :: a :: nil) != - (phi deg 1 b) * Q.
Proof.
  intros b a deg Q H1 H2.
  case_det_aux1 2 (b :: a::nil);simpl in *|-;try (apply False_ind;omega).
  repeat rewrite rec_det_eq.
  simpl app.
  rewrite H1.
  rewrite H2.
  case_det_aux1 1 (a::nil);simpl in *|-;try (apply False_ind;omega). 
  rewrite rec_det_eq;simpl rec_det.
  simpl;Pcsimpl;setoid ring.
Qed.


(* pouver des egalites de listes avec cons et app dans le desordre*)
Ltac list_blast := simpl;try (repeat rewrite app_ass);try (repeat rewrite app_comm_cons);
try (repeat rewrite app_ass);simpl;try reflexivity.

(* a mettre dans Pol_ring*)
Lemma Pol_powP0 :
forall n1, Pol_pow P0 (N_of_nat (S n1)) != P0.
Proof.
intro n0.
caseEq (N_of_nat (S n0)).
intro G.
simpl N_of_nat in G.
discriminate.
intros p0 G.
simpl.
generalize p0;intro p1.
induction p1;simpl;Pcsimpl;try rewrite IHp1;setoid ring.
Qed.

Ltac length_blast := 
repeat progress(
  match goal with
    | H : context [length nil] |- _ => simpl length in H
    | H : context [length (app ?l1 ?l2)] |- _ => rewrite length_app in H
    | H : context [length (?x :: ?y)]  |- _ => (simpl length in H)
    | |- context [length (app ?l1 ?l2)] => rewrite length_app
    | |- context [length (?x :: ?y) ] => simpl length
    | |- context [length (@nil Pol)] => simpl length
end).

Ltac falso := apply False_ind;omega.

(* Somme de mineurs tous strictement trig inf*)

(*

Lemma st_tri_inf :  forall deg l2 l3 n x p,
  n = ((length l2)+(length l3))%nat ->
  (forall i : nat, 1 < i -> i <= S (|l2 |) -> phi deg i x != P0) ->
  (forall i j : nat,
       j < |l3 | -> 1 < i -> i <= S (|l2 |) -> phi deg i (nth j l3 p) != P0) ->
  (forall i j : nat,
    i < S (|l2 |) - j -> j < |l2 | -> phi deg (S (S i)) (nth j l2 p) != P0) ->
  rec_det (phi deg (S n)) (det_aux1 phi deg n) l2 (x :: l3) != P0.
  Proof with length_blast.
    intros deg;induction l2;intros l3 n x p H1 H2 H4 H5.
    reflexivity.
    rewrite rec_det_eq...
    simpl app.
    rewrite (IHl2 (app l3 (a::nil)) n x p);length_blast;intuition.
    induction (le_gt_dec (length l3) j).
    rewrite nth_app_r;trivial.
    replace (j - (length l3))%nat with O;[simpl|omega].
    change a with (nth O (a::l2) p).
    destruct i;[falso|destruct i;[falso|idtac]].
    apply H5;omega.
    rewrite nth_app_l;trivial.
    apply H4;auto with arith.
    change (nth j l2 p) with (nth (S j) (a::l2) p).
    apply H5;omega.
    caseEq (x::app l3 l2).
    intros y l G.
    replace n with (S ((length l2)+(length l3))%nat).
    inversion G.
    replace y with x.
    destruct l3;length_blast.
    simpl app in *|- *.
    replace (S (S (|l2 | + 0))) with (S (S (length l2)));auto with arith.
    replace  (S (|l2 | + 0)) with (S (length l2));auto with arith.
    clear H4.
    change a with (nth O (a::l2) p).
    rewrite H5;try omega.
    setoid ring.
    replace  (S (|l2 | + S (|l3 |)))%nat with (S ((length l2) + (S (length l3))));
      [idtac|omega].
    case_det_aux1 (S (|l2 | + S (|l3 |)))  (x :: app (p0 :: l3) l2).
    rewrite rec_det_eq.

    rewrite (@det_aux_trigQ (app (p0::l3) l2) ((length l2) + (S (length l3)))%nat p deg P0 x);
      length_blast;intuition.
    apply H2;try omega.
    



    change a with (nth O (a::l2) p).
    destruct i;[falso|destruct i;[falso|idtac]].
    apply H5;omega.
    induction (le_gt_dec (length l3) j).
    rewrite nth_app_r;trivial.
    replace (j - (length l3))%nat with O;[simpl|omega].
    apply H2;omega.
    rewrite nth_app_l;trivial.
   apply H4;auto with arith.
  change (nth j l2 p) with (nth (S j) (a::l2) p).
    apply H5;omega.
   replace n with (S ((length l2)+(length l3))%nat).
   case_det_aux1 n (app (app l3 (x::nil)) l2);length_blast;[idtac|falso].
   induction (eq_nat_dec (|l3 | + 1 + |l2 |) (S (|l2 | + |l3 |)));[idtac|falso].
   rewrite rec_det_eq.
Admitted.









*)

(*
Lemma st_tri_inf :  forall deg l2 l3 n x y p,
  n = ((length l2)+(length l3))%nat ->
  (forall i : nat, 1 < i -> i <= S (|l2 |) -> phi deg i x != P0) ->
  (forall i : nat, 1 < i -> i <= S (|l2 |) -> phi deg i y != P0) ->
  (forall i j : nat,
       j < |l3 | -> 1 < i -> i <= S (|l2 |) -> phi deg i (nth j l3 p) != P0) ->
  (forall i j : nat,
    i < S (|l2 |) - j -> j < |l2 | -> phi deg (S (S i)) (nth j l2 p) != P0) ->
  rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) l2
  (app (app l3 (x :: nil)) (y :: nil)) != P0.
  Proof with length_blast.
    intros deg;induction l2;intros l3 n x y p H1 H2 H4 H5 H6.
    reflexivity.
    rewrite rec_det_eq...
    simpl app.
    rewrite (IHl2 (app l3 (x::nil)) n y a p);length_blast;intuition.
    change a with (nth O (a::l2) p).
    destruct i;[falso|destruct i;[falso|idtac]].
    apply H6;omega.
    induction (le_gt_dec (length l3) j).
    rewrite nth_app_r;trivial.
    replace (j - (length l3))%nat with O;[simpl|omega].
    apply H2;auto with arith.
    rewrite nth_app_l;trivial.
    apply H5;auto with arith.
    change (nth j l2 p) with (nth (S j) (a::l2) p).
    apply H6;omega.
    change a  with (nth O (a::l2) p).
    destruct l3.
    simpl app.
    case_det_aux1 (S n) (x::y::l2);length_blast;[idtac|falso].
    rewrite rec_det_eq;simpl app.
    
    


    rewrite H6.





list_blast;assumption.
subst l.
destruct n.
case_det_aux1 1 (x::y::app l1 l2);
[simpl in a0;falso|setoid ring].
destruct n...
destruct l1;destruct l2;simpl in H2;try discriminate.
clear IHl2;simpl in H4;simpl in H5.
simpl app.
case_det_aux1 2 (x::y::nil).
rewrite rec_det_eq.
apply Ominus;try reflexivity.
apply Oprod_r.
apply Ominus.
rewrite H4;auto with arith;try setoid ring.
rewrite rec_det_eq;simpl.
Pcsimpl.
rewrite H5;auto with arith;setoid ring.
simpl in b;falso.
falso.
falso.
rewrite (@det_aux_trigQ (y::app l1 l2) (S (S n)) p d P0 x);length_blast;intuition.
replace (nth j (y :: app l1 l2) p)  with (nth (S j) (x::y::app l1 l2) p);trivial.
destruct j.
simpl.
apply H5;simpl;try omega.
replace (x :: y :: app l1 l2) with (app (x::y::l1) l2);trivial.
replace (x :: y :: app l1 (a::l2)) with (app (x::y::l1) (a::l2)) in H6;trivial.
induction (le_gt_dec (length (x::y::l1)) (S (S j)) ).
rewrite nth_app_r;auto with arith.
replace  (nth (S (S j) - |x :: y :: l1 |) l2 p) with 
 (nth (S (S (S j) - |x :: y :: l1 |)) (a::l2) p);trivial.
replace (S (S (S j) - |x :: y :: l1 |))%nat with (S (S (S j)) - |x :: y :: l1 |)%nat;try omega.
rewrite <- (@nth_app_r Pol (x::y::l1) (a::l2) p (S (S (S j))));auto with arith.
rewrite nth_app_l;auto with arith.
rewrite <- (@nth_app_l Pol (x::y::l1) (a::l2) p);auto with arith.
apply H6;auto with arith.
omega.
transitivity P0.
replace (x :: y :: app l1 (a::l2)) with (app (x::y::l1) (a::l2)) in H6;trivial.
replace (nth i (y :: app l1 l2) p) with (nth (S i) (app (x::y::l1) l2) p);trivial.
destruct i.
simpl.
apply H5;simpl; auto with arith.
rewrite H2;auto with arith.
replace (S (S (S n) - (S i))) with (S (S ( n - i)));try omega.
induction (le_gt_dec (length (x::y::l1))  (S (S i)))...
rewrite nth_app_r;auto with arith.
replace  (nth ((S (S i)) - |x :: y :: l1 |) l2 p) with 
 (nth  (S ((S (S i)) - |x :: y :: l1 |)) (a::l2) p);trivial.
replace (S (S (S i) - |x :: y :: l1 |))%nat with 
 ((S (S (S i))) - |x :: y :: l1 |)%nat;[idtac|length_blast;try omega].
rewrite <- (@nth_app_r Pol (x::y::l1) (a::l2) p  (S (S (S i))));auto with arith.
apply H6;simpl in * |-;omega .
rewrite nth_app_l;trivial.
rewrite <- (nth_app_l (x :: y :: l1) (a :: l2) p);trivial.
apply H6;try omega.
case (even_odd_dec (S (S (S n) - i)));intro;setoid ring.
rewrite Pol_powP0.
setoid ring.
Qed.







Lemma st_tri_inf : forall deg l2 l1 l n x y p,
  l = app l1 l2 ->
  length l = n  ->
  (forall i : nat, 1 < i -> i <= S (length l) -> phi deg i x != P0)->
  (forall i : nat, 1 < i -> i <= S ( length l) -> phi deg i y != P0)->
  (forall i j : nat,
       i <  (S (S n)) - j ->
       j <  (S (S n)) ->
       j > 1 ->
       phi deg (S (S i)) (nth j (x :: y :: l) p) != P0) ->
  rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) l2 (x::y::l1) != P0.
Proof with length_blast.
intros d;induction l2;intros l1 l n x y p H1 H2 H4 H5 H6.
reflexivity.
rewrite rec_det_eq...
simpl app.
rewrite (IHl2 (app l1 (a::nil)) l n x y p);intuition.
list_blast;assumption.
subst l.
destruct n.
case_det_aux1 1 (x::y::app l1 l2);
[simpl in a0;falso|setoid ring].
destruct n...
destruct l1;destruct l2;simpl in H2;try discriminate.
clear IHl2;simpl in H4;simpl in H5.
simpl app.
case_det_aux1 2 (x::y::nil).
rewrite rec_det_eq.
apply Ominus;try reflexivity.
apply Oprod_r.
apply Ominus.
rewrite H4;auto with arith;try setoid ring.
rewrite rec_det_eq;simpl.
Pcsimpl.
rewrite H5;auto with arith;setoid ring.
simpl in b;falso.
falso.
falso.
rewrite (@det_aux_trigQ (y::app l1 l2) (S (S n)) p d P0 x);length_blast;intuition.
replace (nth j (y :: app l1 l2) p)  with (nth (S j) (x::y::app l1 l2) p);trivial.
destruct j.
simpl.
apply H5;simpl;try omega.
replace (x :: y :: app l1 l2) with (app (x::y::l1) l2);trivial.
replace (x :: y :: app l1 (a::l2)) with (app (x::y::l1) (a::l2)) in H6;trivial.
induction (le_gt_dec (length (x::y::l1)) (S (S j)) ).
rewrite nth_app_r;auto with arith.
replace  (nth (S (S j) - |x :: y :: l1 |) l2 p) with 
 (nth (S (S (S j) - |x :: y :: l1 |)) (a::l2) p);trivial.
replace (S (S (S j) - |x :: y :: l1 |))%nat with (S (S (S j)) - |x :: y :: l1 |)%nat;try omega.
rewrite <- (@nth_app_r Pol (x::y::l1) (a::l2) p (S (S (S j))));auto with arith.
rewrite nth_app_l;auto with arith.
rewrite <- (@nth_app_l Pol (x::y::l1) (a::l2) p);auto with arith.
apply H6;auto with arith.
omega.
transitivity P0.
replace (x :: y :: app l1 (a::l2)) with (app (x::y::l1) (a::l2)) in H6;trivial.
replace (nth i (y :: app l1 l2) p) with (nth (S i) (app (x::y::l1) l2) p);trivial.
destruct i.
simpl.
apply H5;simpl; auto with arith.
rewrite H2;auto with arith.
replace (S (S (S n) - (S i))) with (S (S ( n - i)));try omega.
induction (le_gt_dec (length (x::y::l1))  (S (S i)))...
rewrite nth_app_r;auto with arith.
replace  (nth ((S (S i)) - |x :: y :: l1 |) l2 p) with 
 (nth  (S ((S (S i)) - |x :: y :: l1 |)) (a::l2) p);trivial.
replace (S (S (S i) - |x :: y :: l1 |))%nat with 
 ((S (S (S i))) - |x :: y :: l1 |)%nat;[idtac|length_blast;try omega].
rewrite <- (@nth_app_r Pol (x::y::l1) (a::l2) p  (S (S (S i))));auto with arith.
apply H6;simpl in * |-;omega .
rewrite nth_app_l;trivial.
rewrite <- (nth_app_l (x :: y :: l1) (a :: l2) p);trivial.
apply H6;try omega.
case (even_odd_dec (S (S (S n) - i)));intro;setoid ring.
rewrite Pol_powP0.
setoid ring.
Qed.

*)

(*Lemma st_tri_inf : forall deg l2 l1 l n x y p,
  l = app l1 l2 ->
  length l = n  ->
  (forall i : nat, 1 < i -> i <= S (length l) -> phi deg i x != P0)->
  (forall i : nat, 1 < i -> i <= S ( length l) -> phi deg i y != P0)->
  (forall i j : nat,
       i <  S (S n) - j ->
       j <  S (S n) ->
       j >= 1 ->
       phi deg (S (S i)) (nth j (x :: y :: l) p) != P0) ->
  rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) l2 (x::y::l1) != P0.
Proof.
intros d;induction l2;intros l1 l n x y p H1 H2 H4 H5 H6.
reflexivity.
rewrite rec_det_eq.
simpl app.
rewrite (IHl2 (app l1 (a::nil)) l n x y p);intuition.
list_blast;assumption.
subst l.
destruct n.
case_det_aux1 1 (x::y::app l1 l2);
[simpl in a0;apply False_ind;omega|setoid ring].
destruct n.
rewrite length_app in H2;simpl in H2.
destruct l1;destruct l2;simpl in H2;try discriminate.
clear IHl2;simpl in H4;simpl in H5.
simpl app.
case_det_aux1 2 (x::y::nil).
rewrite rec_det_eq.
apply Ominus;try reflexivity.
apply Oprod_r.
apply Ominus.
rewrite H4;auto with arith;setoid ring.
rewrite rec_det_eq;simpl.
Pcsimpl.
rewrite H5;auto with arith;setoid ring.
simpl in b;apply False_ind;omega.
apply False_ind;omega.
apply False_ind;omega.
rewrite (@det_aux_trigQ (y::app l1 l2) (S (S n)) p d P0 x);intuition.
replace (nth j (y :: app l1 l2) p)  with (nth (S j) (x::y::app l1 l2) p);trivial.
destruct j.
apply (H6 i 1);auto with arith;try omega.
replace (x :: y :: app l1 l2) with (app (x::y::l1) l2);trivial.
replace (x :: y :: app l1 (a::l2)) with (app (x::y::l1) (a::l2)) in H6;trivial.
induction (le_gt_dec (length (x::y::l1)) (S (S j)) ).
rewrite nth_app_r;auto with arith.
replace  (nth (S (S j) - |x :: y :: l1 |) l2 p) with 
 (nth (S (S (S j) - |x :: y :: l1 |)) (a::l2) p);trivial.
replace (S (S (S j) - |x :: y :: l1 |))%nat with (S (S (S j)) - |x :: y :: l1 |)%nat;try omega.
rewrite <- (@nth_app_r Pol (x::y::l1) (a::l2) p (S (S (S j))));auto with arith.
rewrite nth_app_l;auto with arith.
rewrite <- (@nth_app_l Pol (x::y::l1) (a::l2) p);auto with arith.
apply H6;auto with arith.
omega.
case (even_odd_dec (S (S (S n) - i)));(intro G; try (setoid_replace P0 with (-P0);try setoid ring);
replace (x :: y :: app l1 (a::l2)) with (app (x::y::l1) (a::l2)) in H6;trivial;
replace (nth i (y :: app l1 l2) p) with (nth (S i) (x :: y :: app l1 l2) p);trivial;
replace (x :: y :: app l1 l2) with (app (x::y::l1) l2);trivial;
induction (le_gt_dec (length (x::y::l1))  (S i));
[rewrite nth_app_r;auto with arith;
replace  (nth ((S i) - |x :: y :: l1 |) l2 p) with 
 (nth  (S ((S i) - |x :: y :: l1 |)) (a::l2) p);trivial;
replace (S ((S i) - |x :: y :: l1 |))%nat with  ((S (S i)) - |x :: y :: l1 |)%nat;try omega;
rewrite <- (@nth_app_r Pol (x::y::l1) (a::l2) p  (S (S i)));auto with arith;
replace (S (S (S n) - i)) with (S (S ((S n) - i)));try omega;
apply (H6 ((S n) - i)%nat (S (S i)));auto with arith;omega|
rewrite nth_app_l;auto with arith;
rewrite <- (@nth_app_l Pol (x::y::l1) (a::l2) p);auto with arith;
replace (S (S (S n) - i)) with (S (S ((S n) - i)));try omega;
apply H6;auto with arith;omega]).
rewrite <- H2.
simpl;repeat rewrite length_app;simpl;omega.

rewrite Pol_powP0.
setoid ring.
Qed.

*)




Theorem det_partial_trig : forall deg Q k l1 l2 l p,
  (S k) = length l1  ->
  l = app l1 l2 ->
  (forall i j, j<length l1 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l1 p) != P0) ->
  (forall (i j:nat),  i < ((length l)-j)   -> (j < (length l))%nat -> j >= length l1 -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < (length l))%nat -> i >= length l1 ->
    phi deg (S ((length l) - i)) (nth i l p) !=
  if even_odd_dec (S ((length l) - i)) then  Q else - Q)  ->
  length l1 > 0 ->
    det_aux1 phi deg (length l) l != 
    (Zpolpower_nat (div2 (S (length l2))))*
    (det_aux1 phi deg (length l1) l1)*
      (Pol_pow Q (N_of_nat (length l2))).
Proof with length_blast.
  intros deg Q;induction k;intros l1 l2 l p H1 H2 H3 H4 H5 H6.
  destruct l1;simpl in H1;try discriminate.
  destruct l1;simpl in H1;try discriminate;subst l...
  symmetry;case_det_aux1 1 (p0::nil);[idtac|length_blast;falso].
  rewrite rec_det_eq;simpl rec_det...
  destruct l2.
  unfold Zpolpower_nat;simpl.

  rewrite Pol_sub_c0'.
  repeat rewrite Pmul_c1'.
   setoid ring.
(* bug Pcsimpl...*)
  destruct l2...
  simpl;Pcsimpl;setoid ring.
  replace p0 with (nth O (p0::nil) p);trivial.
  rewrite (H3 2);simpl;auto with arith.
(*  simpl app in *|- *.
  simpl length in *|-.*)
 replace p0 with (nth O (p0::p1::nil) p);trivial.
  rewrite (H5 1);unfold Zpolpower_nat;simpl;auto with arith.
  repeat rewrite Pol_sub_c0';Pcsimpl;setoid ring.
  repeat rewrite Pol_sub_c0';Pcsimpl;setoid ring.
  rewrite (@det_aux_trigQ (p1::p2::l2) (S (S (length l2))) p deg Q p0);intuition.
  replace p0 with (nth O (p0::nil) p);trivial.
  apply H3;simpl;auto with arith.
  simpl app in *|- *.
  replace (nth j (p1 :: p2::l2) p) with (nth (S j) (p0::p1 ::p2:: l2) p);trivial.
  apply H4;simpl;auto with arith.
   replace (nth i (p1 :: p2::l2) p) with (nth (S i) (p0::p1 :: p2::l2) p);trivial.
   replace (S (S (S (|l2 |)) - i)) with (S (|app (p0 :: nil) (p1 :: p2 :: l2) | - (S i)));trivial.
   apply H5;simpl;auto with arith.
   simpl det_aux1.
   simpl length.
   setoid ring.
(* et a on a la bonne hypothese de recurrence...on peut sortir un lemme sur rec_det *)
   Lemma rec_det_partial_trig : forall deg Q p m,
     (forall (l1 l2 l : list pol) (p : pol),
        S m = |l1 | ->
        l = app l1 l2 ->
        (forall i j : nat,
         j < |l1 | -> 1 < i -> i <= S (|l2 |) -> phi deg i (nth j l1 p) != P0) ->
        (forall i j : nat,
         i < |l | - j ->
         j < |l | -> j >= |l1 | -> phi deg (S (S i)) (nth j l p) != P0) ->
        (forall i : nat,
         i < |l | ->
         i >= |l1 | ->
         phi deg (S (|l | - i)) (nth i l p)
         != (if even_odd_dec (S (|l | - i)) then Q else - Q)) ->
        |l1 | > 0 ->
        det_aux1 phi deg (|l |) l
        != Zpolpower_nat (div2 (S (|l2 |))) * det_aux1 phi deg (|l1 |) l1 *
           Pol_pow Q (N_of_nat (|l2 |))) -> 
  
     forall l1 l2 l3 x y n,
       ((length l1) + (length l2) + (length l3))%nat = n ->
       ((length l1)+(length l3))%nat = m ->
       (forall i,  1<i -> i <= S (length l2) ->
	 phi deg i x != P0) ->

       (forall i,  1<i -> i <= S (length l2) ->
	 phi deg i y != P0) ->

       (forall i j, j<length l1 -> 1<i -> i <= S (length l2) ->
	 phi deg i (nth j l1 p) != P0) ->

       (forall i j, j<length l3 -> 1<i -> i <= S (length l2) ->
	 phi deg i (nth j l3 p) != P0) ->       
       
       (forall (i j:nat),  i < (S (length l2)-j)   -> (j < length l2)%nat ->
	 phi deg  (S (S i)) (nth j l2 p) != P0) ->


       (forall i:nat, (i < length l2) ->
	 phi deg (S ((length l2) -i)%nat) (nth i l2 p) !=
	 if even_odd_dec (S ((length l2) - i)) then  Q else - Q)  ->

       rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) (app (x::y::l1) l2) l3 !=
       (Zpolpower_nat (div2 (S (length l2))))*(Pol_pow Q (N_of_nat (length l2)))*
       rec_det 
       (phi deg ((S (S m))+(length l2))) (det_aux1 phi deg (S m)) (x::y::l1) l3.

     Proof with (simpl app);length_blast.
       intros deg Q p m H0;induction m;intros l1 l2 l3 x y n H1 H2 H3 H4 H5 H6 H7 H8.
       destruct l1;destruct l3;simpl in H2;try discriminate...
       destruct l2;simpl in H1.
       rewrite rec_det_eq...
       subst n.
       unfold Zpolpower_nat;simpl.
       repeat rewrite Pol_sub_c0'.

       Pcsimpl.
       setoid ring.
       clear H5 H6.
       destruct l2.
       destruct n;simpl in H1;try discriminate.
       simpl length;repeat rewrite <- H1.
       simpl (2+1)%nat.
       rewrite rec_det_eq...
       rewrite rec_det_eq...
       transitivity (
	  phi deg 3 x * det_aux1 phi deg 2 (y :: p0 :: nil) -
   (phi deg 3 y * det_aux1 phi deg 2 (x :: p0 :: nil) - P0)).
       apply Psub_comp;try reflexivity.
       apply Psub_comp;try reflexivity.
       rewrite rec_det_eq.
       simpl rec_det...
       case_det_aux1 2 (x::y::nil);try (simpl in *|- ;apply False_ind;omega).
       repeat rewrite rec_det_eq;simpl rec_det.
        rewrite H3;simpl;auto with arith.
	Pcsimpl.
	rewrite (H4 2);simpl;auto with arith.
	setoid ring.
	repeat rewrite rec_det_eq;simpl rec_det...
	case_det_aux1 2 (y::p0::nil);try (simpl in *|- ;apply False_ind;omega).
	case_det_aux1 2 (x::p0::nil);try (simpl in *|- ;apply False_ind;omega).
	repeat rewrite rec_det_eq;simpl rec_det...
	rewrite H4;simpl;auto with arith.
	Pcsimpl.
	rewrite (H3 2);simpl;auto with arith.
	setoid ring.
	setoid_replace (Zpolpower_nat 1) with (- P1);
	  [idtac|unfold Zpolpower_nat;reflexivity].
	setoid_replace  (phi deg 2 p0) with Q;[
	setoid ring|
	rewrite (H8 O);simpl;auto with arith;reflexivity].
	repeat rewrite Pol_sub_c0'.
	Pcsimpl.
	rewrite rec_det_eq...
	simpl in H1.
	replace (S (S (|l2 | + 0))) with (S( S( length l2)))in H1;auto with arith.
	(* bug strw*)
	transitivity (
	  phi deg (S (S n)) x *(
	    Zpolpower_nat (div2 (S n)) * phi deg 1 y * Pol_pow Q (N_of_nat n)) - 
	  (rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n))  (y :: p0 :: p1 :: l2) (x :: nil))).
	apply Psub_comp;try reflexivity.
	apply Pmul_comp;try reflexivity.

	apply (@det_aux_trigQ (p0::p1::l2) n p deg Q y);length_blast;intuition.
(*	apply H4;simpl;auto with arith.
	rewrite H1;trivial.
	simpl length in H7.
	apply H7;try rewrite H1;omega.
	simpl length in H8.*)
	replace (S (n - i))with  (S (S (S (|l2 |)) - i));
	  [idtac|rewrite H1;omega].
	apply H8;try rewrite H1;auto with arith.
	rewrite rec_det_eq...
		(* bug strw*)
	transitivity (
	  phi deg (S (S n)) x *(
	    Zpolpower_nat (div2 (S n)) * phi deg 1 y * Pol_pow Q (N_of_nat n)) -
	  ((phi deg (S (S n)) y *
	    (Zpolpower_nat (div2 (S n)) * phi deg 1 x * Pol_pow Q (N_of_nat n))) - 
	  rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n))
	  (p0 :: p1 :: l2) (x :: y :: nil))).
	apply Psub_comp;try reflexivity.
	apply Psub_comp;try reflexivity.
	apply Pmul_comp;try reflexivity.
	apply (@det_aux_trigQ (p0::p1::l2) n p deg Q x);length_blast;intuition.
(*	apply H3;simpl;auto with arith.
	rewrite H1;trivial.
	simpl length in H7.
	apply H7;try rewrite H1;omega.
	simpl length in H8.*)
	replace (S (n - i))with  (S (S (S (|l2 |)) - i));
	  [idtac|rewrite H1;auto with arith].
	apply H8;try rewrite H1;auto with arith.
	transitivity (  phi deg (S (S n)) x *
   (Zpolpower_nat (div2 (S n)) * phi deg 1 y * Pol_pow Q (N_of_nat n)) -
   (phi deg (S (S n)) y *
    (Zpolpower_nat (div2 (S n)) * phi deg 1 x * Pol_pow Q (N_of_nat n)) -P0)).
	apply Psub_comp;try reflexivity.
	apply Psub_comp;try reflexivity.
	apply (@minor_rec (p0::p1::l2) (S n)  (p0::p1::l2) (@nil Pol) y x  deg p);
	  length_blast;intuition.
	destruct j;length_blast.
	simpl.
	apply H4;subst n;try omega.
	

	apply  (@st_tri_inf deg (p0::p1::l2) (x::nil) (S n) y p);
(*	apply (@st_tri_inf deg (p0::p1::l2) (@nil Pol) (p0::p1::l2) n x y p);*)
	  length_blast;intuition.
	replace j with O;[idtac|omega].
	simpl;apply H3;auto with arith.
(*
	destruct j.
	falso.
	destruct j.
	falso.
	replace  (nth (S (S j)) (x :: y :: p0 :: p1 :: l2) p) with
	   (nth j (p0 :: p1 :: l2) p);trivial.
	apply H7;simpl length;try omega.*)
	change (2 + S (S (|l2 |)))%nat with (S(S( S (S (|l2 |))))).
	repeat rewrite rec_det_eq...
	repeat rewrite H1.
	simpl det_aux1.
	repeat rewrite Pol_sub_c0'.
	Pcsimpl;setoid ring.
	simpl app.
	rewrite rec_det_eq...
	transitivity (
	  phi deg (S (S n)) x *
	  (Zpolpower_nat (div2 (S (|l2 |))) * det_aux1 phi deg (|app l3 (y::l1) |) (app l3 (y::l1)) *
          Pol_pow Q (N_of_nat (|l2 |))) -
	     rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) (y :: app l1 l2) (app l3 (x :: nil))).
	apply Psub_comp;try reflexivity.
	apply Pmul_comp;try reflexivity.
	destruct l3...
	clear H6.
	change (y::app l1 l2) with (app (y::l1) l2).
	replace (S n) with (length  (app (y::l1) l2));[idtac|length_blast;try omega].
	apply (H0 (y::l1) l2 (app (y ::l1) l2) p);length_blast;intuition.
	destruct j.
	simpl.
	apply H4;simpl;auto with arith.
	simpl nth.
	apply H5;simpl;auto with arith.
	destruct j.
	falso.
	simpl nth.
	induction (le_gt_dec (length l1) j).
	rewrite nth_app_r;auto with arith.
	apply H7.
	length_blast;omega.
	length_blast;omega.
	rewrite nth_app_l...
	apply H5;try omega.
	trivial.
	rewrite nth_app_r;trivial.
	replace  (S (S (|l1 |) + |l2 | - i))   with (S (|l2 | -  (i - |y :: l1 |)));
	  [idtac|length_blast;omega].
	apply H8...
	omega.
(*	rewrite length_app;simpl length.
	rewrite length_app in H;simpl in H.
	simpl in H6.
	omega.
	simpl;auto with arith.
	rewrite length_app;simpl;simpl in H1;omega.*)
	replace (p0 :: app l3 (y :: app l1 l2)) with 
	  (app (p0 :: app l3 (y :: l1)) l2);[idtac|list_blast].
	replace (S n) with (length (app (p0 :: app l3 (y :: l1)) l2));[idtac|length_blast;omega].
	replace (S (|l3 | + S (|l1 |))) with ( (|p0 :: app l3 (y :: l1) |));
	  [idtac|length_blast;try omega].
	apply (H0 (p0 ::app l3 (y::l1)) l2 (app (p0 :: app l3 (y :: l1)) l2) p);
	  length_blast;intuition;clear IHm H0.
	replace (p0 :: app l3 (y :: l1)) with (app (p0::l3) (y::l1));[idtac| list_blast].
	induction (le_gt_dec (|(p0 :: l3)|) j).
	rewrite nth_app_r;trivial.
	inversion a.
	replace (nth (|p0 :: l3 | - |p0 :: l3 |) (y :: l1) p) with y.
	apply H4;simpl;try omega.
	replace (|p0 :: l3 | - |p0 :: l3 |)%nat with O;try omega;reflexivity.
	replace (S m0 - |p0 :: l3 |)%nat with (S (m0 - |p0 :: l3 |));[idtac|omega].
	simpl nth.
	apply H5;length_blast;try omega.
	rewrite nth_app_l;trivial.
	apply H6;length_blast;try omega.
	rewrite nth_app_r;trivial...
	apply H7;try omega.
	trivial.
	replace (S (S (|l3 | + S (|l1 |)) + |l2 | - i)) with
	  (S ((length l2) - (i - |p0 :: app l3 (y :: l1) |)))%nat;
	  [idtac|length_blast;try omega].
	rewrite nth_app_r;[idtac|length_blast;omega].
	apply (H8 ((i - |p0 :: app l3 (y :: l1) |)))%nat;length_blast;try omega.
(*	rewrite nth_app_r;trivial.

	  replace (S (|app (p0 :: app l3 (y :: l1)) l2 | - i))%nat with
	    (S ((length l2) - (i - |p0 :: app l3 (y :: l1) |)))%nat.
	  	rewrite length_app in H;simpl length in H; rewrite length_app in H;simpl length in H.
	  simpl in H9; rewrite length_app in H9;simpl in H9.
	  apply (H8 ((i - |p0 :: app l3 (y :: l1) |)))%nat;
	    simpl;try rewrite length_app;simpl;try omega.
	rewrite length_app in H;simpl length in H; rewrite length_app in H;simpl length in H.
	  simpl in H9; rewrite length_app in H9;simpl in H9.
	  rewrite length_app;simpl length;rewrite length_app;simpl length;try omega.
	  simpl;auto with arith.
	  simpl in H1.
	  rewrite length_app;simpl;rewrite length_app;simpl;omega.*)
	  destruct l1...
	  rewrite rec_det_eq...
	  transitivity (
 phi deg (S (S n)) x *
   (Zpolpower_nat (div2 (S (|l2 |))) *
    det_aux1 phi deg (|app l3 (y :: nil) |) (app l3 (y :: nil)) *
    Pol_pow Q (N_of_nat (|l2 |))) -
   (phi deg (S (S n)) y * det_aux1 phi deg (S n) (app (app l3 (x :: nil)) l2) -
  P0))...
	  apply Psub_comp;try reflexivity.
	  apply Psub_comp;try reflexivity.










Lemma st_tri_inf :  forall deg l2 l3 n x p,
  n = ((length l2)+(length l3))%nat ->
  (forall i : nat, 1 < i -> i <= S (|l2 |) -> phi deg i x != P0) ->
  (forall i j : nat,
       j < |l3 | -> 1 < i -> i <= S (|l2 |) -> phi deg i (nth j l3 p) != P0) ->
  (forall i j : nat,
    i < S (|l2 |) - j -> j < |l2 | -> phi deg (S (S i)) (nth j l2 p) != P0) ->
  rec_det (phi deg (S n)) (det_aux1 phi deg n) l2 (x :: l3) != P0.
  Proof with length_blast.
    intros deg;induction l2;intros l3 n x p H1 H2 H4 H5.
    reflexivity.
    rewrite rec_det_eq...
    simpl app.
    rewrite (IHl2 (app l3 (a::nil)) n x p);length_blast;intuition.
    induction (le_gt_dec (length l3) j).
    rewrite nth_app_r;trivial.
    replace (j - (length l3))%nat with O;[simpl|omega].
    change a with (nth O (a::l2) p).
    destruct i;[falso|destruct i;[falso|idtac]].
    apply H5;omega.
    rewrite nth_app_l;trivial.
    apply H4;auto with arith.
    change (nth j l2 p) with (nth (S j) (a::l2) p).
    apply H5;omega.
    caseEq (x::app l3 l2).
    intros y l G.
    replace n with (S ((length l2)+(length l3))%nat).
    inversion G.
    replace y with x.
    destruct l3;length_blast.
    simpl app in *|- *.
    replace (S (S (|l2 | + 0))) with (S (S (length l2)));auto with arith.
    replace  (S (|l2 | + 0)) with (S (length l2));auto with arith.
    clear H4.
    change a with (nth O (a::l2) p).
    rewrite H5;try omega.
    setoid ring.
    replace  (S (|l2 | + S (|l3 |)))%nat with (S ((length l2) + (S (length l3))));
      [idtac|omega].
    case_det_aux1 (S (|l2 | + S (|l3 |)))  (x :: app (p0 :: l3) l2).
    rewrite rec_det_eq.

    rewrite (@det_aux_trigQ (app (p0::l3) l2) ((length l2) + (S (length l3)))%nat p deg P0 x);
      length_blast;intuition.
    apply H2;try omega.
    

(* il faut prouver un cas de base rec_det _ _ l2 l3 avec l2 trig et l3 bloc de petit degre*) 
	  caseEq (app (app l3 (x :: nil)) (y :: nil)).
	  intro G.
	  destruct l3;simpl in G;discriminate.
	  intros q0 l4 G.
	  destruct l4.
	  destruct l3;try destruct l3;simpl in G;try discriminate.
	  destruct l3;simpl in G;try discriminate.
	  destruct l3;simpl in G.
	  inversion G.
	  subst q0 p0 l4.
	 clear H0 IHm.
	 rewrite rec_det_eq.
	 
	 change p1 with (nth O (p1::nil) p).
	 apply H6;try omega.
	 




	
	destruct j.
	simpl.
	apply H4;simpl;auto with arith.
	simpl nth.
	apply H5;simpl;auto with arith.
	destruct j.
	simpl in H9;apply False_ind;omega.
	simpl nth.
	induction (le_gt_dec (length l1) j).
	rewrite nth_app_r;auto with arith.
	apply H7.
	rewrite length_app in H;simpl in H.
	rewrite length_app in H6;simpl in H6.
	simpl in H9;try omega.

	rewrite length_app in H;simpl in H.
	rewrite length_app in H6;simpl in H6.
	simpl in H9;try omega.
	rewrite nth_app_l.
	rewrite length_app in H;simpl in H.
	rewrite length_app in H6;simpl in H6.
	simpl in H9.
	apply H5;try omega.
	trivial.
	rewrite nth_app_r;trivial.
	replace  (S (|app (y :: l1) l2 | - i)) with (S (|l2 | -  (i - |y :: l1 |))).
	apply H8.
	rewrite length_app in H;simpl in H.
	simpl in H6.
	simpl;omega.
	rewrite length_app;simpl length.

	rewrite length_app in H;simpl in H.
	simpl in H6.
	omega.
	simpl;auto with arith.
	rewrite length_app;simpl;simpl in H1;omega.


simpl in *|-;
	induction l2;simpl in H1.
	subst n.
	rewrite rec_det_eq...
	apply Ominus.
	apply Oprod_l.
	replace p0 with (nth O (p0::p1::nil) p);trivial.
	rewrite H7;simpl; try omega.
	reflexivity.
	rewrite rec_det_eq.
	simpl rec_det...
	case_det_aux1 3 (x::y::p0::nil);
	[idtac|simpl in *|-;apply False_ind;omega].
	rewrite rec_det_eq...
	apply Ominus;try reflexivity.
	apply Oprod_r.
	apply Ominus.
	apply Oprod_l.
	apply H3;auto with arith.
	rewrite rec_det_eq...
	apply Ominus;try reflexivity.
	apply Oprod_l.
	apply H4;auto with arith.
	rewrite rec_det_eq...
	apply Ominus;try reflexivity.
	apply Oprod_l.
	replace p0 with (nth O (p0::p1::nil) p);trivial.
	apply H7;simpl;auto with arith.
	rewrite rec_det_eq...
	apply Ominus.
	apply Oprod_l.
	replace p0 with (nth O (p0::p1::a::l2) p);trivial.
	apply H7;simpl;intuition.
	

	apply Ominus.
	apply Oprod_l.







	apply (@minor_rec (p0::p1::l2) (S n) (p0::p1::l2) nil y x deg p);intuition.
	apply H3;simpl;try rewrite H1;auto with arith.
	destruct j.
	simpl.
	apply H4;simpl;try rewrite H1;try omega.





	rewrite (@st_tri_inf deg (p0::p1::l2) (@nil Pol) (p0::p1::l2) n x y p);intuition.

	destruct j.
	apply False_ind;omega.
	replace  (nth (S j) (x :: y :: p0 :: p1 :: l2) p) with
	   (nth j (y :: p0 :: p1 :: l2) p);trivial.
	destruct j.
	simpl.
	apply H4;simpl;try rewrite H1;try omega.



	induction l2;simpl in H1.
	subst n.
	rewrite rec_det_eq...
	apply Ominus.
	apply Oprod_l.
	replace p0 with (nth O (p0::p1::nil) p);trivial.
	rewrite H7.
	




	destruct j.
	apply False_ind;omega.
	replace  (nth (S j) (x :: y :: p0 :: p1 :: l2) p) with
	   (nth j (y :: p0 :: p1 :: l2) p);trivial.
	destruct j.
	simpl.
	apply H4;simpl;try rewrite H1;try omega.


	rewrite rec_det_eq.
	replace p0 with (nth O (p0::p1::l2) p);trivial.
	simpl length in H7;rewrite H1 in H7...
	assert (rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) 
     (p1 :: l2) (x :: y :: p0 :: nil) != P0).
	apply (@minor_rec (p1::l2) (S n) (p0::p1::l2) (p0::nil) y x deg p);intuition.
	apply H3;simpl;try rewrite H1;auto with arith.
	destruct j.
	simpl.
	apply H4;simpl;try rewrite H1;try omega.
	



Lemma st_tri_inf : forall deg l2 l1 l n x y p,
  l = app l1 l2 ->
  length l = n  ->
  (forall i : nat, 1 < i -> i <= S (length l) -> phi deg i x != P0)->
  (forall i : nat, 1 < i -> i <= S ( length l) -> phi deg i y != P0)->
  (forall i j : nat,
       i <  S (S n) - j ->
       j <  S (S n) ->
       j >= 1 ->
       phi deg (S (S i)) (nth j (x :: y :: l) p) != P0) ->
  rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) l2 (x::y::l1) != P0.




	rewrite rec_det_eq.
	replace p0 with (nth O (p0::p1::l2) p);trivial.
	simpl length in H7;rewrite H1 in H7...
	assert (aUx :  det_aux1 phi deg (S n) (x :: y :: p1 :: l2) != P0).
	case_det_aux1 (S n) (x :: y :: p1 :: l2).
	rewrite rec_det_eq.
	apply  Ominus...
	apply  Oprod_l.
	apply H3;simpl;try rewrite H1;omega.
	rewrite rec_det_eq.
	apply  Ominus...
	apply  Oprod_l.
	apply H4;simpl;try rewrite H1;omega.
	apply (@minor_rec (p1::l2)  n (p1::l2) (@nil Pol) y x deg p);
	  intuition.
	apply H3;simpl;try rewrite H1;auto with arith.
	destruct j.
	simpl.
	apply H4;simpl;try omega.
	replace  (nth (S j) (y :: p1 :: l2) p) with  (nth (S j) (p0 :: p1 :: l2) p);trivial.
	apply H7;simpl;try omega.
	apply Ominus.
	rewrite aUx;setoid ring.
	apply (@st_tri_inf deg (p1::l2) (p0::nil) (p0::p1::l2) n x y p);intuition.
	destruct j.
	apply False_ind;omega.
	destruct j.
	simpl.
	apply H4;simpl;try rewrite H1;try omega.


	apply (@minor_rec (p1::l2) (S n) (p1::l2) (p0::nil) y x deg p);intuition.
	inversion H5.
	apply H3;simpl;try rewrite H1;try omega.



	  intuition.
	destruct j.
	apply False_ind;omega.
	destruct j.
	simpl;apply H4;simpl;try rewrite H1;auto with arith.


	rewrite rec_det_eq...
	
	destruct j.
	rewrite H1;trivial.
	rewrite H1.

	transitivity (P0 - 
	rec_det (phi deg (S n)) (det_aux1 phi deg n) (y :: p1 :: l2)
     (app nil (x :: nil))).
	apply Psub_comp;try reflexivity.
	rewrite H3;simpl;try omega.
	setoid ring.






	case_det_aux1 1 (p0::nil).

	rewrite rec_det_eq.
	simpl.
	Pcsimpl.
	

	assert (Aux: (phi deg 2 p0) != ((Zpolpower_nat (div2 2))*Q)).
	replace p0 with (nth O (p0::nil) p);trivial.
	simpl length in H8.
	rewrite (H8 O);simpl;auto with arith.
	unfold Zpolpower_nat.
	simpl.
	simpl Pol_pow.
	setoid_replace (det_aux1 phi deg 1 (p0 :: nil)) with P1.
		setoid ring.
	case_det_aux1 1 (p0::nil);try (simpl in *|- ;apply False_ind;omega).
	


	setoid ring.
       
       
       apply (@st_tri_inf deg (p0::nil) nil (p0::nil) 1 x y p);intuition.
       destruct j;try (apply False_ind;omega).
       destruct j;try (apply False_ind;omega).
       destruct i.
       simpl;apply (H4  2);auto with arith.
       destruct i;simpl in H;try (apply False_ind;omega).
        simpl.
apply (H4  3);auto with arith.
       
       

       

       






















(*
Lemma rec_det_partial_trig : forall m,
 (forall l l2,
    (forall i j, j<length l -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l p) != P0) ->
    length l = m -> det_aux1 phi deg n (app l l2) =
    (Zpolpower_nat (div2 (S (length l2))))*(Pol_pow Q (N_of_nat (length l2)))*
    det_aux1 phi deg m l) ->
forall  n l l1 l2 l3 deg p Q x y,
  m = (length l1 + length l3)%nat ->
  l = app l3 (app (x::y::l1) l2) ->
  S (S n) = length l ->
  (forall i,  1<i -> i <= S (length l2) ->
    phi deg i x != P0) ->

  (forall i,  1<i -> i <= S (length l2) ->
    phi deg i y != P0) ->

  (forall i j, j<length l1 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l1 p) != P0) ->

  (forall i j, j<length l3 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l3 p) != P0) ->

 (forall (i j:nat),  i < ((S (S n))-j)   -> (j < (S (S n)))%nat -> j >= (S (length l1)+(length l3))%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->


  (forall i:nat, (i < (S (S n)))%nat -> i >= (S (length l1)) + length l3 ->
    phi deg (S ((S (S n)) - i)) (nth i l p) !=
  if even_odd_dec (S ((S (S n)) - i)) then  Q else - Q)  ->


   n = ((length l2) + m)%nat ->
rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) (app (x::y::l1) l2) l3 !=
 (Zpolpower_nat (div2 (S (length l2))))*(Pol_pow Q (N_of_nat (length l2)))*
 rec_det 
 (phi deg ((S (S m))+(length l2))) (det_aux1 phi deg (S m)) (x::y::l1) l3.
Proof with (simpl app).
intro m H0;induction m;intros n l l1 l2 l3 deg p Q x y H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
destruct l1;destruct l3;simpl in H1;try discriminate;
simpl in H2;rewrite H2 in H3;simpl in H3;subst l.
simpl app.
replace (length l2) with n;try omega.
destruct l2;simpl in H3.
replace n with 0;try omega;simpl (2+0)%nat.
(* bug setoid rewrite*)
generalize ( rec_det (phi deg 2) (det_aux1 phi deg 1) (x :: y :: nil) nil);intro p0.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
replace (2+ n)%nat with (S (S n));try omega.
destruct n;simpl in H3;try discriminate.
rewrite rec_det_eq...
rewrite rec_det_eq...
(* bug strw*)
transitivity (
 phi deg (S (S (S n))) x * det_aux1 phi deg (S (S n)) (y :: p0 :: l2) -
   (phi deg (S (S (S n))) y * det_aux1 phi deg (S (S n)) (x :: p0 :: l2) -
P0)).
apply Psub_comp;try reflexivity.
apply Psub_comp;try reflexivity.
apply (@st_tri_inf deg (p0 :: l2) (@nil Pol) (p0::l2) (S n) x y p);auto with arith;omega.
repeat rewrite rec_det_eq...
destruct l2.
destruct n;simpl in H10;try discriminate.
rewrite (@det_aux_trigQ1  y p0 deg Q);intuition.
replace p0 with (nth 2 (x::y::p0::nil) p);trivial.
rewrite (H9 2);auto with arith.
reflexivity.
rewrite (@det_aux_trigQ1 x p0 deg Q);intuition.
replace p0 with (nth 2 (x::y::p0::nil) p);trivial.
rewrite (H9 2);auto with arith.
reflexivity.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
setoid ring.
simpl in H3;rewrite (@det_aux_trigQ (p0::p1::l2) (S n) p deg Q y);intuition.
replace (nth j (p0 :: p1::l2) p) with (nth (S (S j)) (x::y::p0 ::p1:: l2) p);trivial.
apply H8;simpl;auto with arith;try omega.
replace (nth i (p0 :: p1::l2) p) with (nth (S (S i)) (x::y::p0 ::p1:: l2) p);trivial.
replace (S (S n - i)) with  (S (S (S (S n)) - (S (S i))));try omega.
apply H9;simpl;auto with arith.
rewrite (@det_aux_trigQ (p0::p1::l2) (S n) p deg Q x);intuition.
replace (nth j (p0 :: p1::l2) p) with (nth (S (S j)) (x::y::p0 ::p1:: l2) p);trivial.
apply H8;simpl;auto with arith;try omega.
replace (nth i (p0 :: p1::l2) p) with (nth (S (S i)) (x::y::p0 ::p1:: l2) p);trivial.
replace (S (S n - i)) with  (S (S (S (S n)) - (S (S i))));try omega.
apply H9;simpl;auto with arith.
simpl det_aux1;Pcsimpl;setoid ring.
simpl app;rewrite rec_det_eq...
(* bug strp*)
transitivity ( phi deg (S (S n)) x *
(rec_det (phi deg (S n)) (det_aux1 phi deg n) (app l3 (y :: app l1 l2)) nil) -
 rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) 
     (y :: app l1 l2) (app l3 (x :: nil))).
apply Psub_comp;try reflexivity.
apply Pmul_comp;try reflexivity.
case_det_aux1 (S n) (app l3 (y :: app l1 l2)).
rewrite length_app in b;simpl in b;rewrite length_app in b.
rewrite H2 in H3.
rewrite length_app in H3;simpl in H3;rewrite length_app in H3.
apply False_ind;omega.


destruct l3.
destruct l1;simpl in H1;try discriminate...
replace n with (S ((length l2) + m));try omega.

replace (y::p0::(app l1 l2)) with (app (y::p0::l1)  l2);trivial.
(* bug strw*)
assert (Aux1 : 
rec_det (phi deg (S (S (|l2 | + m)))) (det_aux1 phi deg (S (|l2 | + m)))
     (app (y :: p0 :: l1) l2) nil != 
 Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
           rec_det (phi deg (S (S m) + |l2 |)) (det_aux1 phi deg (S m))
             (y :: p0:: l1) nil).
apply (@IHm  (|l2 | + m)%nat (app (y :: p0 :: l1) l2)   l1 l2 (@nil Pol) deg p Q);intuition.
rewrite length_app;simpl;omega.
replace p0 with (nth O (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
replace (nth j l1 p) with (nth (S j) (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
simpl in H2;rewrite H2 in H3;subst l.
replace  (nth j (app (y :: p0 :: l1) l2) p) with  (nth (S j) (x::y :: p0 :: (app l1 l2)) p);
trivial.
apply H8;simpl;try omega.
destruct j;omega.
replace  (nth i (app (y :: p0 :: l1) l2) p) with  (nth (S i) (x::y :: p0 :: (app l1 l2)) p);
trivial.
replace (S (S (S (|l2 | + m)) - i)) with (S (S (S n) - (S i)));try omega.
subst l;apply (H9 (S i));simpl;auto with arith;omega.
simpl app;rewrite (rec_det_eq (phi deg (S (S (S (|l2 | + m)))))).
symmetry;rewrite rec_det_eq.
assert (Aux2 : 
 rec_det (phi deg (S (S (S (|l2 | + m)))))
     (det_aux1 phi deg (S (S (|l2 | + m)))) (app (y :: p0 :: l1) l2)
     (x :: nil) !=




Lemma rec_det_partial_trig : forall m n(* k**) l l1 l2 l3 deg p Q x y,

  m = (length l1 + length l3)%nat ->
  l = app l3 (app (x::y::l1) l2) ->
  S (S n) = length l ->
  (forall i,  1<i -> i <= S (length l2) ->
    phi deg i x != P0) ->

  (forall i,  1<i -> i <= S (length l2) ->
    phi deg i y != P0) ->

  (forall i j, j<length l1 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l1 p) != P0) ->

  (forall i j, j<length l3 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l3 p) != P0) ->

 (forall (i j:nat),  i < ((S (S n))-j)   -> (j < (S (S n)))%nat -> j >= (S (length l1)+(length l3))%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->


  (forall i:nat, (i < (S (S n)))%nat -> i >= (S (length l1)) + length l3 ->
    phi deg (S ((S (S n)) - i)) (nth i l p) !=
  if even_odd_dec (S ((S (S n)) - i)) then  Q else - Q)  ->
(*
 (forall l,
    (forall i j, j<length l -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l p) != P0) ->
    length l = m -> det_aux1 phi deg n (app l l2) =
    (Zpolpower_nat (div2 (S (length l2))))*(Pol_pow Q (N_of_nat (length l2)))*
    det_aux1 phi deg m l) ->
   k = length l1 ->*) 
   n = ((length l2) + m)%nat ->
rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) (app (x::y::l1) l2) l3 !=
 (Zpolpower_nat (div2 (S (length l2))))*(Pol_pow Q (N_of_nat (length l2)))*
 rec_det 
 (phi deg ((S (S m))+(length l2))) (det_aux1 phi deg (S m)) (x::y::l1) l3.
Proof with (simpl app).
induction m;intros n l l1 l2 l3 deg p Q x y H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
destruct l1;destruct l3;simpl in H1;try discriminate;
simpl in H2;rewrite H2 in H3;simpl in H3;subst l.
simpl app.
replace (length l2) with n;try omega.
destruct l2;simpl in H3.
replace n with 0;try omega;simpl (2+0)%nat.
(* bug setoid rewrite*)
generalize ( rec_det (phi deg 2) (det_aux1 phi deg 1) (x :: y :: nil) nil);intro p0.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
replace (2+ n)%nat with (S (S n));try omega.
destruct n;simpl in H3;try discriminate.
rewrite rec_det_eq...
rewrite rec_det_eq...
(* bug strw*)
transitivity (
 phi deg (S (S (S n))) x * det_aux1 phi deg (S (S n)) (y :: p0 :: l2) -
   (phi deg (S (S (S n))) y * det_aux1 phi deg (S (S n)) (x :: p0 :: l2) -
P0)).
apply Psub_comp;try reflexivity.
apply Psub_comp;try reflexivity.
apply (@st_tri_inf deg (p0 :: l2) (@nil Pol) (p0::l2) (S n) x y p);auto with arith;omega.
repeat rewrite rec_det_eq...
destruct l2.
destruct n;simpl in H10;try discriminate.
rewrite (@det_aux_trigQ1  y p0 deg Q);intuition.
replace p0 with (nth 2 (x::y::p0::nil) p);trivial.
rewrite (H9 2);auto with arith.
reflexivity.
rewrite (@det_aux_trigQ1 x p0 deg Q);intuition.
replace p0 with (nth 2 (x::y::p0::nil) p);trivial.
rewrite (H9 2);auto with arith.
reflexivity.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
setoid ring.
simpl in H3;rewrite (@det_aux_trigQ (p0::p1::l2) (S n) p deg Q y);intuition.
replace (nth j (p0 :: p1::l2) p) with (nth (S (S j)) (x::y::p0 ::p1:: l2) p);trivial.
apply H8;simpl;auto with arith;try omega.
replace (nth i (p0 :: p1::l2) p) with (nth (S (S i)) (x::y::p0 ::p1:: l2) p);trivial.
replace (S (S n - i)) with  (S (S (S (S n)) - (S (S i))));try omega.
apply H9;simpl;auto with arith.
rewrite (@det_aux_trigQ (p0::p1::l2) (S n) p deg Q x);intuition.
replace (nth j (p0 :: p1::l2) p) with (nth (S (S j)) (x::y::p0 ::p1:: l2) p);trivial.
apply H8;simpl;auto with arith;try omega.
replace (nth i (p0 :: p1::l2) p) with (nth (S (S i)) (x::y::p0 ::p1:: l2) p);trivial.
replace (S (S n - i)) with  (S (S (S (S n)) - (S (S i))));try omega.
apply H9;simpl;auto with arith.
simpl det_aux1;Pcsimpl;setoid ring.
simpl app;rewrite rec_det_eq...
(* bug strp*)
transitivity ( phi deg (S (S n)) x *
(rec_det (phi deg (S n)) (det_aux1 phi deg n) (app l3 (y :: app l1 l2)) nil) -
 rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) 
     (y :: app l1 l2) (app l3 (x :: nil))).
apply Psub_comp;try reflexivity.
apply Pmul_comp;try reflexivity.
case_det_aux1 (S n) (app l3 (y :: app l1 l2)).
rewrite length_app in b;simpl in b;rewrite length_app in b.
rewrite H2 in H3.
rewrite length_app in H3;simpl in H3;rewrite length_app in H3.
apply False_ind;omega.


destruct l3.
destruct l1;simpl in H1;try discriminate...
replace n with (S ((length l2) + m));try omega.

replace (y::p0::(app l1 l2)) with (app (y::p0::l1)  l2);trivial.
(* bug strw*)
assert (Aux1 : 
rec_det (phi deg (S (S (|l2 | + m)))) (det_aux1 phi deg (S (|l2 | + m)))
     (app (y :: p0 :: l1) l2) nil != 
 Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
           rec_det (phi deg (S (S m) + |l2 |)) (det_aux1 phi deg (S m))
             (y :: p0:: l1) nil).
apply (@IHm  (|l2 | + m)%nat (app (y :: p0 :: l1) l2)   l1 l2 (@nil Pol) deg p Q);intuition.
rewrite length_app;simpl;omega.
replace p0 with (nth O (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
replace (nth j l1 p) with (nth (S j) (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
simpl in H2;rewrite H2 in H3;subst l.
replace  (nth j (app (y :: p0 :: l1) l2) p) with  (nth (S j) (x::y :: p0 :: (app l1 l2)) p);
trivial.
apply H8;simpl;try omega.
destruct j;omega.
replace  (nth i (app (y :: p0 :: l1) l2) p) with  (nth (S i) (x::y :: p0 :: (app l1 l2)) p);
trivial.
replace (S (S (S (|l2 | + m)) - i)) with (S (S (S n) - (S i)));try omega.
subst l;apply (H9 (S i));simpl;auto with arith;omega.
simpl app;rewrite (rec_det_eq (phi deg (S (S (S (|l2 | + m)))))).
symmetry;rewrite rec_det_eq.
assert (Aux2 : 
 rec_det (phi deg (S (S (S (|l2 | + m)))))
     (det_aux1 phi deg (S (S (|l2 | + m)))) (app (y :: p0 :: l1) l2)
     (x :: nil) !=


 Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |)) *
           rec_det (phi deg  (S (S m) + |l2 |)) (det_aux1 phi deg  (S m))
             (y :: p0:: l1) (x::nil)).
apply (@IHm  (S (|l2 | + m))%nat (app (x::y :: p0 :: l1) l2)   l1 l2 (x::nil) deg p Q);intuition.
simpl;omega.
rewrite length_app;simpl;omega.
replace p0 with (nth O (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
replace (nth j l1 p) with (nth (S j) (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
simpl in H2;rewrite H2 in H3;subst l.
replace  (nth j (app (y :: p0 :: l1) l2) p) with  (nth (S j) (x::y :: p0 :: (app l1 l2)) p);
trivial.
apply H8;simpl;try omega.
destruct j;omega.
replace  (nth i (app (y :: p0 :: l1) l2) p) with  (nth (S i) (x::y :: p0 :: (app l1 l2)) p);
trivial.
replace (S (S (S (|l2 | + m)) - i)) with (S (S (S n) - (S i)));try omega.
subst l;apply (H9 (S i));simpl;auto with arith;omega.



rewrite rec_det_eq.





symmetry;rewrite rec_det_eq.
transitivity (
  (Zpolpower_nat (div2 (S (|l2 |))) * Pol_pow Q (N_of_nat (|l2 |))) *
   (phi deg (S (S (S m)) + |l2 |) x) *
    (det_aux1 phi deg (S (S m)) (app nil (y :: p0 :: l1))) - 
(Zpolpower_nat (div2 (S (|l2 |)))) * (Pol_pow Q (N_of_nat (|l2 |))) *
 (rec_det (phi deg (S (S (S m)) + |l2 |)) (det_aux1 phi deg (S (S m))))
 (y :: p0 :: l1) (app nil (x :: nil))).
setoid ring.
apply Psub_comp.
rewrite (@IHm (|l2 | + m)%nat (app (y :: p0 :: l1) l2)   l1 l2 (@nil Pol) deg p Q);intuition.
rewrite length_app;simpl;omega.
replace p0 with (nth O (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
replace (nth j l1 p) with (nth (S j) (p0::l1) p);trivial.
apply H6;simpl;auto with arith.
simpl in H2;rewrite H2 in H3;subst l.
replace  (nth j (app (y :: p0 :: l1) l2) p) with  (nth (S j) (x::y :: p0 :: (app l1 l2)) p);
trivial.
apply H8;simpl;try omega.
destruct j;omega.
replace  (nth i (app (y :: p0 :: l1) l2) p) with  (nth (S i) (x::y :: p0 :: (app l1 l2)) p);
trivial.
replace (S (S (S (|l2 | + m)) - i)) with (S (S (S n) - (S i)));try omega.
subst l;apply (H9 (S i));simpl;auto with arith;omega.
rewrite rec_det_eq.











 phi deg (S (S (S n))) x * det_aux1 phi deg (S (S n)) (y :: p0 :: l2) -
   (phi deg (S (S (S n))) y * det_aux1 phi deg (S (S n)) (x :: p0 :: l2) -
P0)).
apply Psub_comp;try reflexivity.
apply Psub_comp;try reflexivity.
(* ce sont des mineurs triangulaire strict inferieurs...*)
generalize (@nil Pol).
intro l;induction l2.
rewrite rec_det_eq.
simpl rec_det.
simpl app.
rewrite <- app_nil_end.
case_det_aux1 (S (S n)) (x::y::l).
(*replace p0 with (nth 2 (x::y::p0::nil) p);trivial.*)
rewrite H8.

case_det_aux1 1 (y::nil);[idtac|simpl in *|- ;apply False_ind;omega].
rewrite rec_det_eq...
simpl (det_aux1 phi deg 0 nil).
simpl (rec_det (phi deg 1) (det_aux1 phi deg 0) nil (y :: nil)).
rewrite rec_det_eq...
simpl ( rec_det (phi deg 2) (det_aux1 phi deg 1) nil (x :: y :: nil)).
(* bug stw*)
assert (bug_srw : (phi deg 2 x) != P0).

apply H4;simpl;auto with arith.

transitivity ( Zpolpower_nat (div2 (S (S n))) * Pol_pow Q (N_of_nat (S n)) *

(P0 -  rec_det (phi deg 2) (det_aux1 phi deg 1) (y :: nil) (x :: nil))).
setoid_replace (phi deg 2 x) with P0.
case_det_aux1 (S (S n)) (y::p0::l2).
(* bug srw...*)
transitivity (P0 - rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) 
     (y :: p0 :: l2) (x :: nil)).
apply Psub_comp;try reflexivity.
case_det_aux1 (S n) (y::p0::l2).
rewrite rec_det_eq.
(* bug srw*)
transitivity (
  phi deg (S (S n)) x *
  (P0 - rec_det (phi deg (S n)) (det_aux1 phi deg n) (p0 :: l2)
      (app nil (y :: nil)))).
apply Pmul_comp;try reflexivity.
apply Psub_comp;try reflexivity.
simpl app.
destruct n;simpl in H3;try discriminate.
case_det_aux1 (S n) (p0::l2).
rewrite rec_det_eq.
simpl app.
rewrite rec_det_eq.

rewrite (H4 (S (S n)));simpl;auto with arith.

symmetry;rewrite rec_det_eq.
simpl app.
simpl (det_aux1 phi deg 0 (y :: nil)).
rewrite rec_det_eq.
simpl ( rec_det (phi deg 1) (det_aux1 phi deg 0) nil (app (x :: nil) (y :: nil))).
destruct l2;simpl app.
simpl in H3;replace n with O;try omega.
unfold Zpolpower_nat;simpl.
repeat rewrite Pscal_Pmul_l.
repeat  rewrite Pol_sub_c0'.
setoid ring.

(****)

replace x with (nth O (x::y::nil) p);trivial.
rewrite H7;simpl;auto with arith.
simpl det_aux1.
transitivity (det_aux1 phi deg (S n) (x::y::p0::l2)).
rewrite (@det_aux_trigQ (y::p0::l2) n p deg Q x);simpl in H3;intuition.
apply H4;simpl;omega.
replace (nth j (y :: p0 :: l2) p) with (nth (S j) (x::y::p0::l2) p);trivial.
apply H7;simpl length;omega.
replace (nth i (y :: p0 :: l2) p) with (nth (S i) (x::y :: p0 :: l2) p);trivial.
replace (S (n - i)) with  (S (S (S n) - (S i)));try  omega.








destruct l2;simpl in H3.
simpl app.
symmetry;rewrite rec_det_eq.
simpl app.
simpl (rec_det (phi deg 1) (det_aux1 phi deg O) nil (x::nil)).
simpl (det_aux1 phi deg 0 (@nil Pol)).
destruct l2.
rewrite rec_det_eq.
unfold Zpolpower_nat;simpl.
replace n with O;[idtac|simpl in H3;omega].
simpl;Pcsimpl;setoid ring.
(* bug Pcsimpl*)
rewrite Pol_sub_c0';Pcsimpl.
transitivity (det_aux1 phi deg (S n)   (x :: p0 :: l2)).
destruct n;simpl in H3;try discriminate.
destruct n.
destruct l2.
case_det_aux1 2 (x::p0::nil).
rewrite rec_det_eq.
simpl app.
rewrite rec_det_eq.
simpl rec_det.
simpl det_aux1.
rewrite (H4 2);auto with arith.
unfold Zpolpower_nat;simpl.
setoid ring.
replace p0 with (nth 1 (x::p0::nil) p);trivial.
rewrite (H8 1);simpl;auto with arith.
repeat rewrite Pol_sub_c0'.
Pcsimpl;setoid ring.
simpl in b;apply False_ind;omega.
destruct l2;simpl in H3;try discriminate.
rewrite (@det_aux_trigQ (p0::l2) (S (S n)) p deg Q x);intuition.
apply H4;auto with arith.
simpl;replace (length l2) with (S n);omega.
replace (nth j (p0 :: l2) p) with (nth (S j) (x::p0 :: l2) p);trivial.
apply H7;simpl;auto with arith.
replace (nth i (p0 :: l2) p) with (nth (S i) (x::p0 :: l2) p);trivial.
replace  (S (S (S n) - i)) with  (S (S (S (S n)) - (S i)));trivial.
apply H8;simpl;auto with arith.
simpl;replace (length l2) with (S n);omega.
simpl length;replace (length l2) with (S n);try omega.
setoid ring.
case_det_aux1 (S n) (x::p0::l2).
simpl in H3;simpl in b;apply False_ind;omega.
induction k.
destruct l1;simpl in H10;try discriminate.
clear H10;simpl app.
rewrite H2 in H3;subst l.
rewrite rec_det_eq.

replace  (nth j (p0 :: l2) p) with  (nth (S j) (x::p0 :: l2) p);trivial.
apply H7;simpl;auto with arith.
replace  (nth i (p0 :: l2) p) with  (nth (S i) (x::p0 :: l2) p);trivial.
replace  (S (n - i)) with  (S (S n - (S i)));try omega.
apply H8;auto with arith.
simpl;auto with arith.



transitivity (det_aux1 phi deg (S n) (x::l2)).
case_det_aux1 (S n) (x::l2).
rewrite H2 in H3.
simpl in H3;simpl in b;apply False_ind;omega.
simpl in H2.
rewrite H2 in H3;simpl in H3.
destruct n.
replace (length l2) with O;auto with arith.
destruct l2;simpl in H3;try discriminate.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
destruct n.
destruct l2;try discriminate;destruct l2;try discriminate.
case_det_aux1 2 (x::p0::nil).
rewrite rec_det_eq.
simpl app.
rewrite rec_det_eq.
simpl rec_det.
simpl app.
rewrite H4;auto with arith.
setoid ring.
case_det_aux1 1 (x::nil).
simpl.
subst l.
replace p0 with (nth 1 (x::p0::nil) p);trivial.
rewrite (H8 1);auto with arith.
simpl;setoid ring.
repeat rewrite  Pscal_Pmul_r.
Pcsimpl;setoid ring.
simpl in b;apply False_ind;omega.

simpl in b;apply False_ind;omega.
subst l.
rewrite (@det_aux_trigQ l2 (S (S n)) p deg Q x);intuition.

replace (nth j l2 p) with (nth (S j) (x::l2) p);trivial.
apply H7;simpl;auto with arith.
replace (nth i l2 p) with (nth (S i) (x::l2) p);trivial.
replace (S (S (S n) - i)) with  (S (S (S (S n)) - (S i)));try omega.
apply H8;simpl;auto with arith.
replace (length l2) with (S (S n));try omega.
simpl det_aux1.
rewrite Pol_sub_c0'.
Pcsimpl.
induction k.
destruct l1;simpl in H10;try discriminate.























Lemma rec_det_partial_trig : forall m n k l l1 l2 l3 deg p Q x,

  m = (length l1 + length l3)%nat ->
  l = app l3 (app (x::l1) l2) ->
  S n = length l ->
  (forall i,  1<i -> i <= S (length l2) ->
    phi deg i x != P0) ->

  (forall i j, j<length l1 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l1 p) != P0) ->

  (forall i j, j<length l3 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l3 p) != P0) ->

 (forall (i j:nat),  i < ((S n)-j)   -> (j < (S n))%nat -> j >= (S (length l1)+(length l3))%nat -> 
    phi deg (S (S i)) (nth j l p) != P0) ->


  (forall i:nat, (i < (S n))%nat -> i >= (S (length l1)) + length l3 ->
    phi deg (S ((S n) - i)) (nth i l p) !=
  if even_odd_dec (S ((S n) - i)) then  Q else - Q)  ->

 (forall l,
    (forall i j, j<length l -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l p) != P0) ->
    length l = m -> det_aux1 phi deg n (app l l2) =

    (Zpolpower_nat (div2 (S (length l2))))*(Pol_pow Q (N_of_nat (length l2)))*
    det_aux1 phi deg m l) ->
   k = length l1 ->
rec_det (phi deg (S n)) (det_aux1 phi deg  n) (app (x::l1) l2) l3 !=
 (Zpolpower_nat (div2 (S (length l2))))*
    (det_aux1 phi deg (S m) (app l3 (x :: l1)))*(Pol_pow Q (N_of_nat (length l2))).

Proof.
induction m;intros n k l l1 l2 l3 deg p Q x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
destruct l1;destruct l3;simpl in H1;try discriminate.
simpl app.
transitivity (det_aux1 phi deg (S n) (x::l2)).
case_det_aux1 (S n) (x::l2).
rewrite H2 in H3.
simpl in H3;simpl in b;apply False_ind;omega.
simpl in H2.
rewrite H2 in H3;simpl in H3.
destruct n.
replace (length l2) with O;auto with arith.
destruct l2;simpl in H3;try discriminate.
unfold Zpolpower_nat;simpl;Pcsimpl;setoid ring.
destruct n.
destruct l2;try discriminate;destruct l2;try discriminate.
case_det_aux1 2 (x::p0::nil).
rewrite rec_det_eq.
simpl app.
rewrite rec_det_eq.
simpl rec_det.
simpl app.
rewrite H4;auto with arith.
setoid ring.
case_det_aux1 1 (x::nil).
simpl.
subst l.
replace p0 with (nth 1 (x::p0::nil) p);trivial.
rewrite (H8 1);auto with arith.
simpl;setoid ring.
repeat rewrite  Pscal_Pmul_r.
Pcsimpl;setoid ring.
simpl in b;apply False_ind;omega.
simpl in b;apply False_ind;omega.
subst l.
rewrite (@det_aux_trigQ l2 (S (S n)) p deg Q x);intuition.

replace (nth j l2 p) with (nth (S j) (x::l2) p);trivial.
apply H7;simpl;auto with arith.
replace (nth i l2 p) with (nth (S i) (x::l2) p);trivial.
replace (S (S (S n) - i)) with  (S (S (S (S n)) - (S i)));try omega.
apply H8;simpl;auto with arith.
replace (length l2) with (S (S n));try omega.
simpl det_aux1.
rewrite Pol_sub_c0'.
Pcsimpl.
induction k.
destruct l1;simpl in H10;try discriminate.



destruct l2;simpl in H3;try discriminate.
destruct l2.
simpl in H3;rewrite H3.
simpl length.
case_det_aux1 2 (x::p0::nil).
rewrite rec_det_eq.
simpl app.
case_det_aux1 1 (p0::nil).
simpl rec_det.
Pcsimpl.
rewrite H4;auto with arith.
case_det_aux1 1 (x::nil).
simpl rec_det.
Pcsimpl.
unfold Zpolpower_nat;simpl.
subst l.
Pcsimpl;setoid ring.
rewrite (@det_aux_trigQ l2 (S n) p deg Q x);intuition.
subst l.


rewrite H2 in H3.
destruct n.
destruct l2;try discriminate.
unfold Zpolpower_nat.
simpl;Pcsimpl;setoid ring.
simpl in H3.
destruct l2;simpl in H3;try discriminate.
destruct l2.
case_det_aux1 (S (S n)) (x::p0::nil).
repeat rewrite rec_det_eq.
simpl app.
destruct n;simpl in a;try discriminate.
rewrite H5;auto with arith.
rewrite H2 in H9.
setoid ring.
replace p0 with (nth 1 (x::p0::nil) p);trivial.
rewrite (H9 1);try omega.
simpl.
repeat rewrite  Pscal_Pmul_l.
Pcsimpl;setoid ring.
rewrite H3 in b.
simpl in b;apply False_ind;omega.
simpl in H3.
rewrite (@det_aux_trigQ (p0::p1::l2) (S n) p deg Q x);intuition.

apply H5;auto with arith.
simpl.
rewrite <- H3;trivial.
subst l.
replace (nth j (p0::p1::l2) p) with (nth (S j) (x::p0::p1::l2) p);trivial.
apply H8;auto with arith;try omega.
subst l.
replace (nth i (p0::p1::l2) p) with (nth (S i) (x::p0::p1::l2) p);trivial. 
replace (S (S n - i)) with  (S (S (S n) - (S i)));auto with arith.
apply H9;simpl;auto with arith.
simpl;omega.
case_det_aux1 1 (x::nil).
simpl rec_det.
Pcsimpl.
simpl length.
replace (S (length l2)) with n;try omega.
setoid ring.
simpl in b;apply False_ind;auto with arith.
simpl app.
rewrite rec_det_eq.
destruct l1.
destruct l3;simpl in H1;try discriminate.
simpl (app nil l2).
rewrite (H10 (p0::l3)).


replace (app l3 (app l1 l2)) with (app (app l3 l1) l2);[idtac|rewrite <- app_ass;reflexivity].
rewrite (H10 (app l3 l1)).

destruct l1;destruct l2;simpl in G;try discriminate.
rewrite rec_det_eq.
simpl rec_det.
simpl in H1.
rewrite H2 in H3.
simpl in H3;repeat rewrite length_app in H3;simpl in H3.
replace (S (S m)) with (S n);try omega.
setoid_replace ( Zpolpower_nat (div2 (S (|@nil Pol |)))) with P1;
[idtac|unfold Zpolpower_nat;simpl;reflexivity].
setoid_replace (Pol_pow Q (N_of_nat (|@nil Pol |))) with P1;[idtac|simpl;reflexivity].
transitivity (rec_det (phi deg (S n)) (det_aux1 phi deg n) (x::nil) l3).
rewrite rec_det_eq;reflexivity.
rewrite rec_det_eq.

simpl rec_det.
unfold Zpolpower_nat.
simpl even_odd_dec;simpl odd.

case_det_aux1 (S n) (app l3 (x::nil)).

simpl.
Pcsimpl.
induction (eq_

symmetry;case_det_aux1 (S n) (app l3 (x::nil)).
transitivity (rec_det (phi deg (S n)) (det_aux1 phi deg n) (x::nil) l3).
symmetry;rewrite rec_det_eq.
simpl rec_det.

rewrite rec_det_eq.



assert (Aux :  det_aux1 phi deg (S n) (app l3 (x :: nil)) !=  det_aux1 phi deg n (app l3 nil)).

rewrite <- app_nil_end in H2.

subst l.
simpl in H1.
rewrite H1.

pattern (app l1 l2) at -1 in *|- *.
rewrite rec_det_eq.
replace (app l3 (app l1 l2)) with (app (app l3 l1) l2);[idtac|rewrite <- app_ass;reflexivity].
rewrite (H10 (app l3 l1)).
(***********)

induction k;intros m n l l1 l2 l3 deg p Q x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
destruct l1.
simpl in H11;apply False_ind;omega.
simpl in H1;discriminate.
destruct l1.
simpl in H12;apply False_ind;discriminate.
destruct l1.
simpl app.
rewrite rec_det_eq.




rewrite rec_det_eq.
destruct l1;simpl in H1;try discriminate.
replace (app l3 (app (p0:: l1) l2)) with (app (app l3 (p0::l1)) l2);
[idtac|list_blast].
rewrite (H11 (app l3 (p0::l1)));intuition.
rewrite (IHk m n l l1 l2 (app l3 (x::nil))  deg p Q p0);intuition.
simpl in H2;simpl;rewrite length_app;simpl;omega.
generalize H3;list_blast;auto.
replace p0 with (nth O (p0 ::l1) p);trivial.
apply H7;auto with arith.
replace (nth j l1 p) with (nth (S j) (p0::l1) p);trivial.
apply H7;simpl;omega.

destruct l1.
simpl in H11;apply False_ind;omega.
rewrite (IHm n l l1 l2 (app l3 (x::nil)) deg p Q).
simpl in H1;simpl; rewrite length_app.


*)



Theorem det_partial_trig : forall l1 l2 l n p deg Q,
  l = app l1 l2 ->
  (forall i j, j<length l1 -> 1<i -> i <= S (length l2) ->
    phi deg i (nth j l1 p) != P0) ->
  (forall (i j:nat),  i < (n-j)   -> (j < n)%nat -> j >= length l1 -> 
    phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat -> i >= length l1 ->
    phi deg (S (n - i)) (nth i l p) !=
  if even_odd_dec (S (n - i)) then  Q else - Q)  ->
  length l1 > 0 ->
  (length l = n)%nat  -> 
    det_aux1 phi deg  n l != 
    (Zpolpower_nat (div2 (S (length l2))))*
    (det_aux1 phi deg (length l1) l1)*(Pol_pow Q (N_of_nat (length l2))).
Proof.
  induction l1;intros l2 l n p deg Q H1 H2 H3 H4 H5 H6.
  simpl in H5;apply False_ind;omega.
  destruct l1.
  simpl in H1.
  subst l.
  destruct n.
  simpl in H6;discriminate.
  simpl length.
  assert (Aux : det_aux1 phi deg 1 (a:: nil) != phi deg 1 a).
  case_det_aux1 1 (a::nil).
  rewrite rec_det_eq.
  simpl rec_det.
  simpl det_aux1.
  setoid ring.
  simpl in b;apply False_ind;omega.
  rewrite Aux;clear Aux.
  replace (length l2) with n;[idtac|simpl in H6;omega].
  destruct n.
  destruct l2;[idtac|simpl in H6;discriminate].
  case_det_aux1 1 (a::nil).
  rewrite rec_det_eq.
  unfold Zpolpower_nat;simpl.
  Pcsimpl;setoid ring.
  simpl in b;apply False_ind;omega.
  destruct n.
  destruct l2;[simpl in H6;discriminate|destruct l2;
    [idtac|simpl in H6;discriminate]].
  case_det_aux1 2 (a::p0::nil).
  rewrite rec_det_eq.
  simpl app.
  case_det_aux1 1 (p0::nil).
  simpl rec_det.
  Pcsimpl.
  replace a with (nth O (a::nil) p);trivial.
  rewrite H2;auto with arith.
  setoid ring.
  replace p0 with (nth 1 (a :: p0 ::nil) p);trivial.
  rewrite (H4 1);auto with arith.
  unfold Zpolpower_nat;simpl.
  Pcsimpl.
  rewrite  Pscal_Pmul_r.
  Pcsimpl;setoid ring.
  simpl in b;apply False_ind;omega.
  simpl in b;apply False_ind;omega.
  apply det_aux_trigQ with p;intuition.
  replace a with (nth O (a::nil) p);trivial.
  apply H2;auto with arith.
  simpl in H6;omega.
  replace (nth j l2 p) with (nth (S j) (a::l2) p);trivial.
  apply H3;auto with arith.
  simpl;omega.
  replace (nth i l2 p) with (nth (S i) (a::l2) p);trivial.
  replace (S (S (S n) - i)) with (S (S (S (S n)) - (S i)));try omega.
  apply H4;simpl;try omega.
  destruct n.
  rewrite H1 in H6;simpl in H6;discriminate.
  destruct n.
  rewrite H1 in H6;simpl in H6;discriminate.
  case_det_aux1 (S (S n)) l.
  assert (Aux : forall m1 m2 k,
    S k = length l1 ->
    ((length m1) + (length m2) = (length l1))%nat ->
     (forall i j, j< length m1 -> 1<i -> i <= S (S k) ->
    phi deg i (nth j m1 p) != P0) ->
     (forall i j, j<length m2 -> 1<i -> i <= S (S k) ->
       phi deg i (nth j m2 p) != P0) ->
     rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) (app (p0::m1) l2) (a::m2) !=
      Zpolpower_nat (div2 (S (length l2))) *
      det_aux1 phi deg (S (S (length m1 + length m2)))%nat (app (a::m2) (p0::m1)) *
      Pol_pow Q (N_of_nat (|l2 |))).
  induction m1;intros m2 k G1 G2 G3 G4.
  simpl app.
  rewrite rec_det_eq.
  simpl app.
  transitivity (
    (phi deg (S (S n)) a)*
    ((Zpolpower_nat (div2 (S (|m2 |))) *
    det_aux1 phi deg (|p0:: m2 |) (p0::m2) )*
    Pol_pow Q (N_of_nat (|m2 |))) - 
 rec_det (phi deg (S (S n))) (det_aux1 phi deg (S n)) l2
     (p0 :: app m2 (a:: nil))).
  apply Psub_comp;try reflexivity.
  apply Pmul_comp;try reflexivity.
 rewrite (IHl1 m2 (p0 :: app m2 l2) (S n) p deg Q).


     
    app m1 m2 := 


(**)


  simpl length.
  rewrite <- app_nil_end in H1.
  subst l1.
  subst n.
  unfold Zpolpower_nat.
  simpl.
  Pcsimpl;setoid ring.




  simpl N_of_nat.
  simpl Pol_pow.
  

(* bloc gauche : tous les polys de l' on un degre plus petit que d - |l'| *)
  (forall P, PIn P l1 ->
  (forall i:nat, (1 < i)%nat -> (i <= S (length l1))%nat -> phi deg  i P != P0)) ->
 (* bloc droit : il est triangulaire*) 
  (forall (i j:nat), (j < i)%nat  -> (i < (length l1) - j)%nat -> 

  (forall (i j:nat), (j < i)%nat  -> (i < (length l1) - j)%nat -> 
    phi deg (S (S i)) (nth j l2 p) != P0) ->
(* sur la diagonale au dessus du bloc droit il n'y a que des q*)
  (forall j, j < length l2 ->
    (phi deg (S ((length l2) - j)) (nth j l2 p)) != 
    (if even_odd_dec (S ((length l2) - j)) then Q else - Q))->
  det phi deg (app l1 l2) !=



  Pol_pow Q (N_of_nat (|l|))*(det (fun d m => phi d (m+|l|)) deg l').
Admitted.



