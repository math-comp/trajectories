(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

Require Import CAD_types.
Require Import Mylist.
Require Import Tactic.
Require Import Utils.
Require Import Bool.
Require Import ZArith.

Require Import Pol_ring.

Require Import phi.
Require Import PDet.
Require Import PolMonOSum.
(*Require Import DetTrig.*)

Set Implicit Arguments.


Add New Ring PolRing : PRth Abstract.
Add New Ring CoefRing : cRth Abstract. 


Hypothesis cpow_1 : forall c, cpow c 1%N ==c.
Hypothesis cintegral : forall a b, czero_test (a **b) = orb (czero_test a) (czero_test b).


Lemma nat_deg_mul : forall P Q, P0test P =false -> 
P0test Q =  false -> nat_deg (P*Q) = (nat_deg P + nat_deg Q)%nat.
Admitted.


Notation pdet := (det phi).

Notation "x ^ i ":= (Pol_pow x i).
Notation "x ^^ i ":=(cpow x i) (at level 30, no associativity).

Notation "| l |" := (length l)(at level 30).
(* ca sert ca?*)
(*
Add Morphism (@cons Pol)
 with signature Pol_Eq ==> Pol_list_equiv ==>Pol_list_equiv as cons_comp.
intros.
constructor;trivial.
Qed.
*)
(* version setoid de In *)
(* on generalise lus que ca dans Myllist?*)
(*
Fixpoint PIn(P:Pol)(l:list Pol){struct l}:Prop:=
  match l with
   |nil => False
   |b :: m => b != P \/ PIn P m
  end.




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

*)
Ltac my_replace_aux := 
(match goal with
   | |- - _ != - _ => apply Popp_comp
   | |- det _ _ _ != det _ _ _ => apply det_morph;try reflexivity
   | |- app _ _ *= app _ _=> apply app_morph;try reflexivity
   | |- _ :: _ *= _ :: _ => constructor;[try setoid ring|try reflexivity]
   | |-_ =>  reflexivity;try Pcsimpl;try assumption
  end).




(* un setoid replace rudimentaire
qui ne marche que pour la premiere occurence...*)
Ltac myreplace t u:=
match goal with
| |-  ?e1 != ?e2 =>
     match e1 with
        |context c[t] => 
        let t':= context c [u] in transitivity t';[my_replace_aux|idtac]
        | _ =>
           match e2 with
           |context c[t]=>
           let t':= context c [u] in transitivity t';[idtac|my_replace_aux]
          end
     end
| |- ?e1 *= ?e2 =>
     match e1 with
        |context c[t] => 
        let t':= context c [u] in transitivity t';[my_replace_aux|idtac]
        | _ =>
           match e2 with
           |context c[t]=>
           let t':= context c [u] in transitivity t';[idtac|my_replace_aux]
          end
     end
end.

(* on ne peut pas parameter par aux :
Ltac myreplace1 := myreplace my_replace_aux.
User error: Immediate match producing tactics not allowed in local definitions*)


Lemma det_PIn_l : forall l1 l2 P Q d c, PIn Q l1 ->
pdet  d (app l1 ((P+(scal c Q))::l2)) != pdet d (app l1 (P::l2)). 
Proof with (try apply phi_m;try reflexivity;auto).
induction l1;intros l2 P Q d c H_In;simpl in H_In;elim H_In;intro G.
myreplace
(app (a :: l1) (P + scal c Q :: l2))
(app nil ((app (Q :: l1) (P + (scal c Q) :: l2)))).
rewrite G...
rewrite det_t.
unfold scal;rewrite det_sum_simpl...
rewrite det_t. (* rajouter l'hypothese de phi*)
setoid ring;simpl.
myreplace a Q;try rewrite G...
symmetry...
elim (@PIn_app Q l1 G).
intros l3 Hex.
elim Hex;intros l4 Heq.
myreplace l1 (app l3 (Q :: l4)).
rewrite Heq...
rewrite app_comm_cons.
rewrite <- ass_app.
rewrite det_t.
unfold scal.
myreplace (P ::l4) ((P+ c !* Q)::l4).
rewrite det_sum_simpl...
myreplace l1 (app l3 (Q::l4)).
myreplace 
(app (a :: app l3 (Q :: l4)) (P + c !* Q :: l2))
(app  (a::l3) (app (Q::l4) (P + c !* Q :: l2))).
rewrite det_t.
setoid ring.
rewrite ass_app...
rewrite Heq...
Qed.






Lemma det_PIn_r : forall l1 l2 P Q d c, PIn Q l2 ->
det phi d (app l1 ((P+(scal c Q))::l2)) != det phi d (app l1 (P::l2)). 
Proof with (try apply phi_m;try reflexivity;trivial).
intros l1 l2 P Q d c H_In.
elim (PIn_app Q l2 H_In).
intros l3 Hex.
elim Hex.
intros l4 Heq.
myreplace l2 (app l3 (Q::l4)).
rewrite Heq...
repeat rewrite app_comm_cons.
unfold scal;rewrite det_sum_simpl...
rewrite <- app_comm_cons.
myreplace l2 (app l3 (Q::l4))...
rewrite Heq...
Qed.

(* generalisation of det_sum_simpl to a finite linear combination 
 of redundant  polynomials*)



Lemma det_Psum : forall m f l1 l2 P d g,
(forall n, n <= m -> (f n) = P0 \/ PIn (f n) l1 \/ PIn (f n) l2) ->
det phi d (app l1 ((P + Psum (fun i =>scal  (g i)  (f i))  m)::l2))
 != det phi d (app l1 (P::l2)).
Proof with (try apply phi_m;auto;try reflexivity).
induction m;intros f l1 l2 P d g H_neutral;simpl.
elim (H_neutral O);[intro H_f0|intro Hf0|auto with arith].
rewrite H_f0.
apply det_morph.
apply app_morph;[reflexivity|constructor;[unfold scal;Pcsimpl;setoid ring|reflexivity]].
elim Hf0;intro H_In.
induction l1.
elim H_In.
rewrite det_PIn_l...
rewrite det_PIn_r...
elim (H_neutral (S m));[intro H_fsm|intro Hfsm|auto with arith].
rewrite H_fsm.
myreplace 
(P + (Psum (fun i : nat => scal (g i) (f i)) m + scal (g (S m)) P0))
(P + (Psum (fun i : nat => scal (g i) (f i)) m)).
apply app_morph...
constructor;try reflexivity.
unfold scal;Pcsimpl;setoid ring.
apply IHm;auto.
myreplace (P +
      (Psum (fun i : nat => scal (g i) (f i)) m + scal (g (S m)) (f (S m))))
((P +
      Psum (fun i : nat => scal (g i) (f i)) m) + scal (g (S m)) (f (S m))).
apply app_morph...
constructor;try reflexivity;setoid ring.
elim Hfsm;intro H_In.
rewrite det_PIn_l...
rewrite det_PIn_r...
Qed.

(* A*X^n *)
Fixpoint times_X_n(A:Pol)(n:nat){struct n}:Pol:=
match n with
|O => A
|S n => X *(times_X_n A n)
end.

Add Morphism times_X_n with signature Pol_Eq ==> (@eq nat) ==> Pol_Eq as times_X_n_comp.
intros x1 x2 Heq.
induction x;simpl.
trivial.
rewrite IHx.
reflexivity.
Qed.

(* linearity for times_X_n*)
Lemma times_X_n_scal : forall n A a, times_X_n (a!*A) n != a !* (times_X_n A n).
Proof.
induction n;intros A a;simpl.
reflexivity.
rewrite IHn.
repeat rewrite  Pscal_Pmul_l.
setoid ring.
Qed.


(*X^(n+m)P...X^m*)
Fixpoint Xfamily_n_m(m:nat)(A:Pol)(n:nat){struct n}:list Pol:=
 match n with
|O => (times_X_n A m)::nil
|S n => (times_X_n A (m + (S n)))::(Xfamily_n_m m A n)
end.

(* builds the list A*X^n ::...::A*X :: A ::nil*)
Definition Xfamily:= Xfamily_n_m O.


Add Morphism Xfamily with signature Pol_Eq ==> (@eq nat) ==> Pol_list_equiv as X_n_fam_comp.
intros x1 x2 Heq.
induction x;unfold Xfamily;simpl.
constructor;trivial;reflexivity.
constructor;[rewrite Heq|rewrite IHx];reflexivity.
Qed.

Lemma family_n_m_length : forall n m P,
 | (Xfamily_n_m m P n)| = (n +1)%nat.
Proof.
induction n;intros m P;simpl;
[idtac|rewrite IHn];reflexivity.
Qed.

Lemma family_length : forall n P, length (Xfamily P n) = (n +1)%nat.
Proof.
intros n P;unfold Xfamily;apply family_n_m_length.
Qed.

Lemma Xfamily_aux : forall n m P l,
app (Xfamily_n_m m P (S n)) l*= 
app (Xfamily_n_m (S m) P n) ((times_X_n P m)::l).
Proof.
induction n;intros m P l.
simpl.
constructor;try reflexivity.
replace (m+1)%nat with (S m);try omega.
reflexivity.
transitivity 
(app ((times_X_n P (m +(S (S n))))::
(Xfamily_n_m m P (S n))) l).
simpl.
constructor;try constructor;reflexivity.
transitivity (
times_X_n P (m + S (S n)) ::
app (Xfamily_n_m m P (S n)) l). 
rewrite app_comm_cons;reflexivity.
rewrite IHn.
simpl.
constructor;try reflexivity.
replace (m + S (S n))%nat with (S (m + (S n)))%nat;auto with arith.
reflexivity.
Qed.

Lemma Xfamily_app : forall n m P,
Xfamily P ((S n)+m)%nat *= app (Xfamily_n_m (S m) P n) (Xfamily P m).
Proof.
induction n;intros m P ;unfold Xfamily.
reflexivity.
fold Xfamily.
replace (S (S n) +m)%nat with ((S n) + (S m))%nat;[rewrite IHn|omega].
auto with arith.
rewrite Xfamily_aux.
apply app_morph;reflexivity.
Qed.

(* devrait etre dans Pring, oups cést  Pmul_Rat_aux_assoc*)
Lemma scal_assoc : forall a b C, a !* (b!* C) != (a ** b) !* C.
Proof.
intros a b C.
repeat rewrite  Pscal_Pmul_l.
rewrite Pmul_assoc.
apply Pmul_comp;[idtac|reflexivity].
simpl.
unfold Pol_mul_Rat.
case_c0_test b.
rewrite H0.
constructor.
setoid ring.
case_c0_test (b -- c1).
assert (H1': b == c1).
transitivity (c1 ++ c0);[rewrite <- H1|idtac];setoid ring.
rewrite H1'.
constructor;setoid ring.
reflexivity.
Qed.

Lemma scal_Passoc : forall c P Q, (scal c P)*Q != scal c (P*Q).
Admitted.

(* multinilearity of det when its arg contains a Xfamily **)
Lemma det_times_Xn_multilin : forall d a A n l1 l2 ,
 det phi d (app l1 (app (Xfamily (a !* A) n) l2))
!=  (cpow  a (N_of_nat (n+1))) !*
 det phi d (app l1 (app (Xfamily A n) l2)).
Proof with (try apply phi_m).
intros d a;induction n;simpl;intros l1 l2.
rewrite cpow_1.
apply det_scal...
transitivity (det phi d
  (app (app l1 ((X * times_X_n (a !* A) n) ::nil))  (app (Xfamily (a !* A) n) l2))).
apply det_morph.
rewrite app_ass.
simpl;reflexivity.
rewrite IHn.
transitivity (cpow a (N_of_nat (n + 1))
!* (det phi d
     (app (app l1 (a!* (X *( times_X_n A n)) :: nil))
        (app (Xfamily A n) l2)))).
apply Pmul_Rat_compc.
apply det_morph.
apply app_morph;[idtac|reflexivity].
apply app_morph;[reflexivity|constructor;[idtac|reflexivity]].
rewrite times_X_n_scal.
repeat rewrite  Pscal_Pmul_l;setoid ring.
transitivity (cpow a (N_of_nat (n + 1))
!* det phi d (app l1 ((a!* (X * times_X_n A n)) :: app (Xfamily A n) l2))).
rewrite app_ass.
simpl;reflexivity.
rewrite det_scal...
(*rewrite (det_scal  d l1 (app (Xfamily A n) l2) (X * times_X_n A n) a).
unfold scal.*)
rewrite scal_assoc.
assert  (Npos (P_of_succ_nat (n + 1)) = (N_of_nat (n+1) + 1)%N).
unfold N_of_nat.
case (n+1)%nat.
reflexivity.
intro.
simpl.
rewrite Pplus_one_succ_r;reflexivity.
rewrite H.
rewrite (cpow_plus a (N_of_nat (n + 1)%nat) (Npos xH)).
rewrite cpow_1.
reflexivity.
Qed.

(* devrait etre ailleurs *)
Lemma P0test_F : forall P, P0test P =false -> ~P!=P0.
intros P H.
induction P;
intro G;
inversion G.
absurd (c == c0);[idtac|assumption].
apply ceq_propF.
rewrite <- c0test_ceqb;assumption.
caseEq (P0test P);intro Test.
simpl in H.
rewrite Test in H.
absurd (c == c0);[idtac|assumption].
apply ceq_propF.
rewrite <- c0test_ceqb;assumption.
apply IHP;assumption.
Qed.

(* P0test is a morphism, devrait etre ailleurs...*)
Add Morphism P0test with signature Pol_Eq ==> (@eq bool) as P0test_comp.
intros x1 x2 Heq.
induction Heq;simpl;try simpl in IHHeq;try rewrite IHHeq;try rewrite c0test_c0;try rewrite H;trivial.
caseEq (P0test Q);intro G;trivial.
rewrite H;reflexivity.
caseEq (P0test P);intro G;trivial.
rewrite H;trivial.
caseEq (P0test P);intro G;trivial.
rewrite H;trivial.
Qed.

Ltac toto Heq G := 
match goal with
| |-  context [if ?cond then _ else _] =>  rewrite Heq in G;rewrite G
| |- context [nat_deg ?P] => absurd (P!=P0);[apply P0test_F|idtac];assumption
end.

(* nat_deg is a morphism idem...*)
Add Morphism nat_deg with signature Pol_Eq ==> (@eq nat)  as nat_deg_comp.
intros x1 x2 Heq.

induction Heq;simpl;try reflexivity;
caseEq (P0test P);intro G;trivial; try (toto Heq G);trivial.
rewrite IHHeq;trivial.
assert (Qis0:P0test Q =true).
rewrite Heq.
simpl.
rewrite G.
apply c0test_c0.
rewrite Qis0;trivial.
caseEq (P0test Q);intro Qtest.
absurd (Q != P0).
intro Abs.
rewrite Abs in Heq. 
inversion Heq.
rewrite H5 in G.
simpl in G.
rewrite c0test_c0 in G.
discriminate.
apply P0test_is_P0;assumption.

rewrite IHHeq.
simpl.
rewrite G.
rewrite nat_of_P_plus_morphism.
auto with zarith.
caseEq (P0test Q);intro Qtest.
trivial.
absurd (Q != P0).
intro Abs.
rewrite Abs in Qtest;simpl in Qtest.
rewrite c0test_c0 in Qtest.
discriminate.
assert (Pis_zero := P0test_is_P0 P G).
rewrite Pis_zero in Heq.
transitivity (PX P0 i c0);[assumption|constructor;reflexivity].
caseEq (P0test Q);intro Qtest.
assert (Qis_zero := P0test_is_P0 Q Qtest).
rewrite Qis_zero in Heq.
inversion Heq.
rewrite H5 in G.
simpl in G.
rewrite c0test_c0 in G.
discriminate.
rewrite nat_of_P_plus_morphism.
rewrite IHHeq.
simpl.
rewrite G.
auto with zarith.
Qed.

(* useful tactic for desctruction of case(x -- c1) *)
Ltac is_one x :=
 match goal with
[ H : x -- c1 == c0 |- _  ] =>
let G := fresh in
 assert ( G : x == c1) ; [transitivity (c1++c0) ;[ rewrite <- H | idtac] ; setoid ring|idtac]
| |- _ => idtac "rate"
end.

(* devrait etre dans Pring *)

Lemma Pscal_PX : forall P a i b, a !* PX P i b != PX (a !* P) i (a ** b).
Proof.
induction P;intros a i b;unfold Pol_mul_Rat;simpl;
case_c0_test a.
rewrite H0.
constructor;setoid ring.
case_c0_test (a--c1).
is_one a.
constructor;[rewrite H2|idtac];setoid ring.
rewrite cintegral.
rewrite H.
rewrite orb_b_false.
case_c0_test c;try rewrite H2;
(constructor;[idtac|constructor];setoid ring).
constructor;[rewrite H0|reflexivity].
setoid ring.
case_c0_test (a--c1).
is_one a.
constructor;[rewrite H2|idtac];setoid ring.
apply mkPX_PX.
setoid ring.
Qed.

(* a <>0 -> aP = 0 iff P=0 *)
Lemma P0test_scal : forall P a, czero_test a = false -> P0test (a!*P) = P0test P.
Proof.
induction P;intros a Ha;simpl.
unfold Pol_mul_Rat.
rewrite Ha.
simpl.
caseEq (czero_test (a -- c1));intro G;simpl.
trivial.
rewrite cintegral.
rewrite Ha.
auto with bool.
transitivity (P0test (PX (a!*P) p (a**c))).
apply P0test_comp.
apply Pscal_PX.
caseEq (P0test P);intro Ptest.
assert (Pis_0 := P0test_is_P0 P Ptest).
rewrite Pis_0.
simpl.
assert (P0test (a !* P0)=true).
rewrite Pmul_P0_c.
simpl.
apply c0test_c0.
rewrite H.
rewrite cintegral.
rewrite Ha.
auto with bool.
simpl.
assert (P0test (a !* P) =false).
rewrite (IHP a Ha).
assumption.
rewrite H.
trivial.
Qed.

Lemma nat_deg_scal : forall a P, czero_test a = false -> nat_deg (a!* P) = nat_deg P.
Proof.
intro a.
induction P;intro H;
unfold Pol_mul_Rat;
rewrite H.
case_c0_test (a -- c1).
reflexivity.
unfold Pol_mul_Rat_aux.
reflexivity.
case_c0_test (a -- c1).
reflexivity.


simpl.
caseEq (P0test P);intro P0test.
assert (Pis0 := P0test_is_P0 P P0test).
rewrite Pis0.
simpl.
assert (test : czero_test (c0**a) =true).
rewrite  (c0_test_ext (c0**a) c0).
apply c0test_c0.
setoid ring.
rewrite test.
simpl;trivial.
transitivity (nat_deg (PX (a!*P) p (c**a))).
apply nat_deg_comp.
transitivity (PX  (Pol_mul_Rat_aux P a) p (c**a)).
apply mkPX_PX;reflexivity.
constructor;[reflexivity|idtac].
unfold Pol_mul_Rat.
rewrite H.
rewrite H0.
reflexivity.
simpl.
assert (PolMonOSum.P0test  (a !* P) = false).
rewrite P0test_scal;assumption.
rewrite H1.
rewrite (IHP H).
trivial.
Qed.


Lemma mon_spec : forall n, mon (N_of_nat (S n))  != X*mon (N_of_nat n).
Admitted.

Lemma mon_X_spec : forall n, mon (N_of_nat n) != X ^ (N_of_nat n).
Admitted.

Lemma mon_add : forall n m, (mon n)*(mon m) != mon (n + m). 
Admitted.

(* relation btw times_X_n and mon *)
Lemma times_X_n_to_mon : forall n P, times_X_n P n != P*(mon (N_of_nat n)).
Proof.
induction n;intro P.
simpl;Pcsimpl.
Admitted.

(*Xfamily contains the first P*mon n*)
Lemma PIn_Xfamily : forall P, forall m n, n <= m -> PIn (P*(mon (N_of_nat n))) (Xfamily P m).
Proof.
induction m;intros n Hle;simpl.
inversion Hle;simpl.
left.
Pcsimpl.
inversion Hle.
left.
rewrite times_X_n_to_mon.
rewrite mon_spec.
setoid ring.
right.
exact (IHm n H0).
Qed.

(*
Lemma N_of_nat_add: forall n m, N_of_nat (n + m)  = (N_of_nat n +  N_of_nat m)%N.
Admitted.
*)

(* forall P, P\in family (A + sum g(i)BX^i i=0...k) -> 
P = A + sum g(i)BX^(i+j) i=0...k), for some j<= n*)
Lemma PIn_family_of_sum : forall n A B P k g,
 PIn P (Xfamily (A + (Psum (fun i => scal (g i) (B*(mon (N_of_nat i)))) k)) n) ->
exists j, (j<= n)/\(P!=A*(mon (N_of_nat j)) + (Psum (fun i => scal (g i) (B*(mon (N_of_nat (i+j))))) k)).
Proof.
induction n;simpl;intros A B P k g HIn;elim HIn;intro Heq.
exists 0;split.
auto with arith.
rewrite <- Heq.
simpl;Pcsimpl.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
replace (n+0)%nat with n;[reflexivity|auto with arith].
elim Heq.
rewrite 
(times_X_n_to_mon n (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k))
in Heq.
exists (S n);split.
auto with arith.
rewrite <- Heq.
rewrite mon_spec.
setoid ring.
apply Padd_comp;[reflexivity|idtac].
transitivity (Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k *
mon (N_of_nat (S n))).
rewrite mon_spec;setoid ring.
rewrite Psum_mul_r.
apply Psum_ext;intro m.
rewrite <- scal_Passoc.
rewrite  <-  Pmul_assoc.
rewrite mon_add.
replace (N_of_nat m + N_of_nat (S n))%N with (N_of_nat (m + S n)).
apply scal_Passoc.
apply N_of_nat_add.
elim (IHn A B P k g Heq);intros j0 Sol.
elim Sol;intros Lt_j0 EqP.
exists j0;split.
auto with arith.
assumption.
Show Proof.
Qed.

Ltac myreplace_old :=
 repeat progress
  (match goal with
   | |- - _ != - _ => apply Popp_comp
   | |- det _ _ _ != det _ _ _ => apply det_morph;try reflexivity
   | |- app _ _ *= app _ _=> apply app_morph;try reflexivity
   | |- _ :: _ *= _ :: _ => constructor;[try setoid ring|try reflexivity]
   | |-_ =>  try reflexivity;try Pcsimpl;try assumption
  end).


Lemma det_family_sum_aux : forall n l m  k d A B g,
k+n<=m ->
det phi d (app 
l (app (Xfamily (A + (Psum (fun i => scal (g i)  (B*(mon (N_of_nat i)))) k)) n)
(Xfamily B m)))
!=
det phi d (app l (app
(Xfamily A n)
(Xfamily B m))).
(*Proof.
induction n;intros l m k d A B g Hle.
simpl.
apply (@det_Psum k (fun i : nat => (B * mon (N_of_nat i)))).
right;right.
apply PIn_Xfamily.
omega.
unfold Xfamily;fold Xfamily.
myreplace 
(Xfamily
(A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
(S n))
((times_X_n
                    (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
                    (S n))::(Xfamily
              (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
              n) ).



*)

Proof.
induction n;intros l m k d A B g Hle.
simpl.
apply (@det_Psum k (fun i : nat => (B * mon (N_of_nat i)))).
right;right.
apply PIn_Xfamily.
omega.
unfold Xfamily;fold Xfamily.
transitivity (det phi d 
(app
 (app l ((times_X_n
                    (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
                    (S n))::nil))  
(app (Xfamily
              (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
              n) (Xfamily B m)))).
rewrite app_ass; reflexivity.                   
transitivity (det phi d
       (app 
       (app l
          (times_X_n A (S n) ::nil))
          (app (Xfamily A n)
             (Xfamily B m)))).

rewrite (IHn (app l
        (times_X_n
           (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
           (S n) :: nil)) m k d A B g).
omega.
rewrite app_ass.
replace (app
        (times_X_n
           (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
           (S n) :: nil) (app (Xfamily A n) (Xfamily B m)))
with
        ((times_X_n
           (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
           (S n)) ::(app (Xfamily A n) (Xfamily B m)));[idtac|
reflexivity].
transitivity 
(det phi d
(app l
((A*(mon (N_of_nat (S n))) 
  + (Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)*mon(N_of_nat (S n)))::
app (Xfamily A n) (Xfamily B m)))).
myreplace_old.
rewrite times_X_n_to_mon.
setoid ring.
transitivity
(det phi d
  (app l
     (A * mon (N_of_nat (S n)) +
      Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))*
      mon (N_of_nat (S n))) k
      :: app (Xfamily A n) (Xfamily B m)))).
myreplace_old.
rewrite <- (Psum_mul_r k (fun i :nat => scal (g i)(B*(mon (N_of_nat i))))).
setoid ring.
transitivity (det phi d
     (app l ((times_X_n A (S n)) ::
        (app (Xfamily A n) (Xfamily B m))))).
transitivity (det phi d
  (app l
     (A * mon (N_of_nat (S n)) +
      Psum
        (fun i : nat =>
         scal (g i) (B * mon (N_of_nat i) * mon (N_of_nat (S n)))) k
      :: app (Xfamily A n) (Xfamily B m)))).
myreplace_old.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n0;apply scal_Passoc.
rewrite (@det_Psum k (fun i=> (B * mon (N_of_nat i)) * mon (N_of_nat (S n)))).
intros j Hlejk.
right;right.
apply PIn_PIn_app_l.
rewrite <- Pmul_assoc.
rewrite mon_add.
rewrite <- N_of_nat_add.
apply PIn_Xfamily.
omega.
myreplace_old.
symmetry;apply times_X_n_to_mon.
repeat rewrite app_ass;reflexivity.
repeat rewrite app_ass;reflexivity.
Qed.

Lemma det_family_sum : forall n m  k d A B g,
k+n<=m ->
det phi d 
 (app (Xfamily (A + (Psum (fun i => scal (g i)  (B*(mon (N_of_nat i)))) k)) n)
(Xfamily B m))
!=
det phi d (app
(Xfamily A n)
(Xfamily B m)).
Proof.
intros.
apply (@det_family_sum_aux n (@nil Pol) m k d A B g H) .
Qed.


Definition eps(n:nat) := cpow (-- c1) (N_of_nat n). 
Hypothesis cpow_0 : forall c, cpow c N0 == c1.


Lemma Popp_Pscal : forall P, - P != -- c1 !*P.
Proof.
induction P.
simpl.
Pcsimpl.
rewrite Pscal_Pmul_l.
simpl.
unfold Pol_mul_Rat.
case_c0_test c.
rewrite H0.
Pcsimpl.
setoid ring.
case_c0_test (c -- c1).
is_one c.
rewrite H2;reflexivity.
simpl.
setoid_replace (-- c) with (-- c1** c);[reflexivity|setoid ring].
rewrite Pscal_PX.
simpl.
rewrite IHP.
apply mkPX_PX.
setoid ring.
Qed.

(* pouver des egalites de listes avec cons et app dasn le desordre*)
Ltac list_blast := simpl;try (repeat rewrite app_ass);try (repeat rewrite app_comm_cons);
try (repeat rewrite app_ass);simpl;try reflexivity.

(*buts de la forme scal a P != (-) scal b P', avec P != P',
oppose optionnel. ramene le pb dans coef et essaie de prouver
(-)b = a.*)

Ltac to_coef_goal:= try unfold scal;try (repeat rewrite Popp_Pscal);
try (repeat rewrite scal_assoc);
 apply Pmul_Rat_comp;try setoid ring;try reflexivity.


Lemma det_skip_axiom : forall d l1 l2,
length l1 > 0 -> length l2 > 0 ->
det phi  d (app l1 l2) != 
(eps (length(l1) *(length l2))) !* (det phi d (app l2 l1)).
Admitted.

(*
Lemma nat_of_P_pred : forall p, nat_of_P (p -1 )= pred (nat_of_P p).
Proof.
induction p.
*)

Lemma Pminus_one_Ppred:forall p, (p - 1)%positive = Ppred p. 
Proof.
induction p;simpl;unfold Pminus;unfold Pminus_mask;trivial.
Qed.


Lemma Pcompare_lt: forall p, (p?=p)%positive Lt = Lt.
induction p;simpl;auto.
Qed.

Lemma get_coef_deg : forall n P,
 nat_deg P <= n -> 
forall m, m>n -> get_coef m P == c0.
Proof.
induction n;intros P Hdeg m Hlt.
inversion Hdeg.
destruct m;simpl;
destruct P;try (apply False_ind;omega).
reflexivity.
simpl in H0.
caseEq (P0test P);intro TestP.
destruct p;rewrite (P0test_is_P0 P TestP);[
setoid_replace (PX P0 (xI p - 1) c0) with P0|
setoid_replace (PX P0 (xO p - 1) c0) with P0|
idtac];try apply gcoef_P0;constructor;reflexivity.
rewrite TestP in H0.
SearchAbout nat_of_P.
assert (G:= lt_O_nat_of_P p).
apply False_ind;omega.
inversion Hdeg.
induction P;simpl in H0.
apply False_ind;omega.
caseEq (P0test P);intro CaseP;rewrite CaseP in H0.
apply False_ind;omega.
destruct m.
apply False_ind;omega.
simpl.
destruct p;
(apply IHn;
simpl;
try rewrite CaseP;
try simpl in Hdeg;
try rewrite CaseP in Hdeg).
assert (Trans:nat_deg P + nat_of_P (xI p - 1)<nat_deg P + nat_of_P (xI p )).
apply plus_lt_compat_l.
apply nat_of_P_lt_Lt_compare_morphism.
simpl.
apply Pcompare_lt.
omega.
omega.
rewrite  <- (Pplus_minus (xO p) xH) in Hdeg.
rewrite nat_of_P_plus_morphism in Hdeg.
simpl in Hdeg.
omega.
simpl;trivial.
auto with arith.
unfold nat_of_P in Hdeg.
unfold Pmult_nat in Hdeg.
omega.
auto with arith.
apply IHn;trivial.
omega.
Qed.


Lemma times_X_n_P0: forall n Q, P0test Q = true -> times_X_n Q n != P0.
induction n;intros Q HQ0;simpl.
rewrite (P0test_is_P0 Q);trivial;reflexivity.
rewrite IHn;trivial.
setoid ring.
Qed.
Set Printing Notations.


Lemma P0test_X : P0test X = false.
Proof.
simpl.
rewrite c0test_c1.
reflexivity.
Qed.



Lemma times_X_n_P0test : forall n P, P0test (times_X_n P n)= P0test P.
Proof.
induction n;intros P;
caseEq (P0test P);intro Ptest;simpl;trivial.
rewrite (times_X_n_P0 n P);trivial.
setoid_replace (X*P0) with P0;[simpl|setoid ring].
rewrite c0test_c0;reflexivity.
caseEq (P0test (X * times_X_n P n));intro G;trivial.
assert (H0 := P0test_is_P0 (X * times_X_n P n) G).
elim (Pmul_integral X (times_X_n P n) H0);intro G1.
inversion G1.
inversion H5.
absurd (czero_test c1 = false).
rewrite H8.
rewrite (c0test_c0).
discriminate.
apply c0test_c1.
absurd (P0test (times_X_n P n) = false).
rewrite G1.
simpl.
rewrite c0test_c0;discriminate.
rewrite IHn;assumption.
Qed.


Lemma times_X_n_deg : forall n Q, P0test Q = false -> nat_deg
  (times_X_n Q n) = (nat_deg Q + n)%nat.
Proof.
induction n;intros Q QNot0;simpl.
auto with arith.
rewrite nat_deg_mul;trivial.
rewrite (IHn Q QNot0).
simpl.
rewrite c0test_c1.
simpl;auto with arith.
apply P0test_X.
rewrite <- QNot0.
apply times_X_n_P0test.
Qed.

(*
Lemma nth_family_aux : forall n A B, nth n (Xfamily_n_m n A n) B = times_X_n A n.
Proof.
induction n;intros A B;trivial.
unfold Xfamily_n_m.
fold Xfamily_n_m.

unfold nth;fold nth.
simpl.
rewrite (P0test_is_P0 A Atest).
*)

Lemma nth_Xfamily : forall k m n A B, k <= m ->
(nth k (Xfamily_n_m n A m) B)= times_X_n A (n + m -k)%nat.
Proof.
induction k;destruct m;intros n A B  k_le;simpl.
replace (n+0-0)%nat with n;[reflexivity|omega].
replace (n + S m - 0)%nat with (n + S m)%nat;[reflexivity|omega].
destruct k;try (apply False_ind;omega).
rewrite IHk;auto with arith.
replace (n + S m - S k)%nat with (n + m - k)%nat;trivial.
omega.
Qed.






Lemma family_n_m_deg : forall n m P Q, 
PIn P (Xfamily_n_m m Q n) -> nat_deg P <= m + ((nat_deg Q )+n)%nat.
Proof.
induction n;intros m P Q HIn;caseEq (P0test Q);
intro Qtest;
(match goal with
| [H : (P0test ?Q = true) |- _ ]=> rewrite (P0test_is_P0 Q H);simpl
| [H : (P0test ?Q = false)|- _ ] => simpl in HIn;elim HIn;clear HIn;intro HIn';try rewrite <- HIn'
end).
simpl in HIn;elim HIn;clear HIn;intro HIn'.
rewrite (P0test_is_P0 Q Qtest) in HIn';simpl in HIn';rewrite <- HIn'.
rewrite times_X_n_P0;simpl.
apply c0test_c0.
auto with arith.
elim HIn'.
rewrite times_X_n_deg;[omega|assumption].
elim HIn'.
simpl in HIn;elim HIn;clear HIn;intro HIn'.
rewrite <- HIn'.
rewrite times_X_n_P0;simpl;auto with arith.
apply le_trans with (m + (0 + n))%nat.
replace (m + (0 + n))%nat with (m + (nat_deg Q + n))%nat.
apply IHn;trivial.
rewrite (P0test_is_P0 Q Qtest);reflexivity.
auto with arith.
rewrite times_X_n_deg;trivial;omega.
apply le_trans with (m + (nat_deg Q + n))%nat.
apply IHn;trivial.
omega.
Qed.

Lemma family_deg :forall n P Q, PIn P (Xfamily Q n) -> nat_deg P <= ((nat_deg Q )+n)%nat.
Proof.
intros n  P Q ;unfold Xfamily;intro H.
replace (nat_deg Q + n)%nat with (0 + (nat_deg Q + n))%nat;
[apply family_n_m_deg;assumption|auto with arith].
Qed.










(*
Lemma det_app_rev : forall d l2 l4 l1 l3 l5 a b, 
det d  (app l1 (app (a::l2) (app l3 (app (b::l4) l5)))) !=
scal (eps ((length l2 + 1)%nat*(length l4 + 1)%nat))
(det d  (app l1 (app (b::l4) (app l3 (app (a::l2) l5))))).
Proof with (simpl;reflexivity).
intros d;induction l2.
(*cas de base : paar induction sur la deuxieme liste*)
induction l4;intros l1 l3 l5 u v;simpl.
(* cas de base_base *)
unfold scal;setoid_replace (eps 1) with (-- c1);[idtac|unfold eps;rewrite cpow_1;reflexivity].
transitivity (det d (app l1 (app (u::l3) (v::l5))));
[repeat rewrite app_comm_cons;reflexivity|idtac].
transitivity (-det d (app l1 (app (v :: l3) (u :: l5))));[apply det_t|repeat rewrite <- app_ass].
list_blast.
apply Popp_Pscal.
transitivity (det d (app l1 (app (u::l3) (v:: (a::(app l4 l5))))));[list_blast|rewrite det_t].
transitivity (- det d (app (




induction l4;intros l1 l3 l5 u v;simpl.
(* cas de base_base *)
unfold scal;setoid_replace (eps 1) with (-- c1);[idtac|unfold eps;rewrite cpow_1;reflexivity].
transitivity (det d (app l1 (app (u::l3) (v::l5))));
[repeat rewrite app_comm_cons;reflexivity|idtac].
transitivity (-det d (app l1 (app (v :: l3) (u :: l5))));[apply det_t|repeat rewrite <- app_ass].
list_blast.
apply Popp_Pscal.
(*cas de base_ind*)
induction l3.
simpl.
(* echange de u et v pour appliquer l'HI*)
transitivity (det d (app l1 (app (u::nil) (v::a::app l4 l5))));[reflexivity|rewrite det_t].
transitivity ( - det d (app (app l1 (v::nil)) (app  (u ::nil) (app nil  (app (a :: l4) l5))))).
list_blast...
rewrite IHl4.
list_blast.
unfold scal.
unfold eps.
to_coef_goal.
replace ( N_of_nat (S (length l4 + 1 + 0)%nat)) with (N_of_nat (length l4 + 1+0)%nat +1)%N.
rewrite cpow_plus.
rewrite cpow_1.
setoid ring.
replace (S (length l4 + 1 + 0)%nat) with ((length l4 + 1 + 0)+1)%nat;
[repeat rewrite N_of_nat_add|omega];auto with arith.









intros d;induction l2.
destruct l4;intros l1 l3 l5 u v;simpl.
unfold scal;setoid_replace (eps 1) with (-- c1).
transitivity (det d (app l1 (app (u::l3) (v::l5)))).
repeat rewrite app_comm_cons;reflexivity.
transitivity (-det d (app l1 (app (v :: l3) (u :: l5))));[apply det_t|repeat rewrite <- app_ass].
repeat rewrite app_comm_cons.
repeat rewrite <- app_ass.
apply Popp_Pscal.
unfold eps.
rewrite cpow_1;reflexivity.
simpl.
transitivity (det d (app l1 (app (u::l3) (v::(a::app l4 l5)))));[reflexivity|rewrite det_t].
transitivity (det d (app (app l1 (u::nil)) (a::nil) (app (
simpl.

simpl in IHl4.
rewrite (IHl4 l1 .



rewrite scal_spec.
Pcsimpl.

;simpl in Hl2, Hl4;
try (absurd (0>0);[apply gt_asym|idtac];assumption).
transitivity (det d (app l1 (app (a::(app l2 l3)) (a0::(app l4 l5))))).
myreplace.
repeat rewrite <- app_ass.
rewrite app_comm_cons;reflexivity.
rewrite det_t.
transitivity - det d (app (app l1 (a0::nil))

(replace (length l1 * 0)%nat with 0;[idtac|auto with arith];
unfold scal;setoid_replace (eps 0) with c1;[Pcsimpl|unfold eps;simpl;rewrite cpow_0;reflexivity]).

simpl in IHl4.
transitivity (det d (app l1 (app l3 (app (a :: l4) l5)))).
Focus 2.
rewrite (IHl4 l1 l3 l5).


unfold scal;rewrite cpow_0.
rewrite app_ass;Pcsimpl.

*)



Definition pol:= Pol.
Delimit Scope P_scope with Pol.
Bind Scope P_scope with pol.



Lemma PInapp_dec : forall l1 l2 P, PIn P (app l1 l2) -> (PIn P l1)
  \/PIn P l2.
Proof.
induction l1;destruct l2;intro A;simpl;intro HIn;auto.
rewrite <- app_nil_end in HIn;auto.
elim HIn;intro HIn2.
left;left;assumption.
elim (IHl1 (p::l2) A HIn2);intro IHn3.
left;right;assumption.
simpl in IHn3.
right;assumption.
Qed.

Lemma PIn_T_XfamilyT : forall n R, PIn R (Xfamily R n).
Proof.
induction n;intro R;simpl.
left;reflexivity.
right;trivial.
Qed.

Lemma Xfamily_include : forall n m R S, m <= n -> PIn R (Xfamily  S m)
  -> PIn R (Xfamily S n).
Proof.
induction n;intros m R S Hle;
simpl;inversion Hle;simpl;intro G;
auto.
fold Xfamily.
right.
apply IHn with m;assumption.
Qed.


Lemma plus_minus_ass: forall n m p, m>=p -> (n + (m-p))%nat = (n + m - p)%nat.
intros.
omega.
Qed.

Lemma minus_plus_ass: forall n m p, 
m<=n -> (n - m + p)%nat = (n + p -m)%nat.
intros.
omega.
Qed.

Lemma minus_simpl: forall n m, m<= n-> (n -m + m=n)%nat.
Proof.
intros;omega.
Qed.

Lemma minus_simpl2:forall n m, (n + m - m = n)%nat.
Proof.
intros;omega.
Qed.


Lemma minus_simpl3 : forall n m, (n + m -n)%nat = m.
Proof.
intros;omega.
Qed.

Lemma plus_le_compat_r : forall x y z, x <= y -> x +z <= y +z.
Proof.
intros;apply plus_le_compat;auto with arith.
Qed.

Lemma minus_lt_reg : forall x y z, x < y -> x>= z -> x - z < y -z.
intros.
omega.
Qed.

Lemma minus_le_reg : forall x y z, x < y -> x>= z -> x - z <= y -z.
intros.
omega.
Qed.



(*
Lemma plus_0:forall x, (x+0 = x)%nat.
Proof.
auto with arith.
Qed.
*)

Lemma S_minus : forall n , ((S n) -1 = n)%nat.
Proof.
induction n;simpl;trivial.
Qed.

Lemma S_plus : forall n, S n = (n +1)%nat.
Proof with trivial.
induction n;simpl...
rewrite IHn...
Qed.


Ltac omega_helper :=
repeat progress
(match goal with
| |- context c [plus ?x  0]=> 
  let t:= constr:x in 
  let u:= constr:(plus x  0) in
   (replace u with t;auto with arith)
| |- context c [minus (plus ?x  ?y) ?y] => 
  let t := constr:x in
  let u := constr:(minus (plus x  y) y) in
   (replace u with t;auto with arith)

(*
| |- context c [minus (S ?x) 1] => rewrite S_minus;auto with arith
| |- context c [S ?x] => rewrite S_plus;auto with arith*)
| |- lt (minus ?x ?z) (minus ?y ?z) => apply minus_lt_reg;auto with arith
| |- le (minus ?x ?z) (minus ?y ?z) => apply minus_le_reg;auto with arith
| |- lt (plus ?x ?z) (plus ?y ?z) => apply plus_lt_compat_r;auto with arith
| |- le (plus ?x ?z) (plus ?y ?z) => apply plus_le_compat_r;auto with arith
| |- context c [plus (minus ?x  ?y) ?y ]=> rewrite minus_simpl;auto with arith
| |- context c [minus (plus ?x ?y) ?y ] => rewrite minus_simpl2
| |- context c [minus (plus ?x ?y) ?x]=>rewrite minus_simpl3
| |- context c [plus (minus ?x  ?y) ?z]=>rewrite minus_plus_ass;auto with arith
| |- context c [plus ?x (minus ?y ?z)]=> rewrite plus_minus_ass;auto with arith
end).

(*
Lemma omega1 : forall u v k,v>0 -> (u + (v - 1) - k <= u + v - 1 - k)%nat.
Proof.
intros.
omega_helper.
Qed.
elim (le_gt_dec 1 v);intro Hv;inversion Hv.
simpl.
replace (u+1-1)%nat with u.
omega.
simpl.
omega.
simpl.
replace (u+0)%nat with u;[idtac|auto with arith].
apply False_ind;omega.
omega.
Qed.

*)

Lemma gt_minus_reg : forall x y u v, x>y -> u > v -> x > v -> x - v > y - u.
Proof.
intros x y u v H1 H2 H3.
omega.
Qed.
 
(*
Lemma omega1 : forall p q i j k h,
 q <= p -> h < q -> j < h ->
 k < i -> i < p - h
 -> p + q - j - 1 + 2 > S (S i)
 -> k <= p - h - 1
 -> p - h >= 1
->
   p + q - j - 1 - i > q + p - 1 - j - k.
Proof.
destruct p; intros.
inversion H5.
simpl in *|- *.
clear -H3;apply False_ind;omega.
replace (q + S p)%nat with (S (q + p))%nat;auto with arith.
destruct j.
simpl.
simpl in H4.
assert (H7:p+q>i);[clear - H4;omega|clear-H7 H2].
om
clear -H H2 H4.

omega.
*)


Lemma omega1 : forall x y k t j i,
 y <= x -> t < y ->  j < t -> i < k -> x + y - j - 1 > i-> k < x - t->
 x + y - j - 1 - i > y + x - 1 - j - k.
destruct x;intros.
inversion H4.
rewrite plus_comm.
replace (y+ S x)%nat with (S (y +x));auto with arith.
destruct j.
simpl.
simpl in H3.
rewrite plus_comm.
replace (x+y-0)%nat with (x+y)%nat;auto with arith.
replace (x+y-0)%nat with (x+y)%nat in H4;auto with arith.
replace (x+y-0)%nat with (x+y)%nat;auto with arith.
clear - H2 H3;omega.
replace (S (y+x) - S j)%nat with (y + x -j)%nat;auto with arith.
replace (S (y +x) -1)%nat  with (y + x)%nat;auto with arith.
rewrite (S_plus j).
clear - H2 H3;omega.
Qed.

Lemma omega2 : forall n m, n < m -> (S ( m - n -1) = m - n)%nat.
induction n;destruct m;intro G.
apply False_ind;omega.
simpl;auto with arith.
apply False_ind;omega.
simpl.
apply IHn.
auto with arith.
Qed.

Definition lcoef(P:Pol):= get_coef (nat_deg P) P.

Lemma times_X_n_get_coef_Pc:forall c n,
get_coef (S n) (X*(Pc c))  == get_coef n (Pc c).
Proof.
intros.
simpl.
unfold Pol_mul_Rat.
case_c0_test c.
rewrite H0;
destruct n;simpl;reflexivity.
case_c0_test (c -- c1).
destruct n;simpl.
is_one c;symmetry;assumption.
reflexivity.
unfold Pol_mul_Rat_aux.
unfold mkPX.
case_c0_test (c1**c).
absurd ((czero_test c)=false).
setoid_replace c with c0.
rewrite c0test_c0.
intuition.
rewrite <- H2;setoid ring.
assumption.
setoid_replace (c1**c) with c;try setoid ring.
Qed.


Lemma times_X_n_get_coef_PX:forall P c n,
get_coef (S n) (PX P xH c) == get_coef n P.
Proof.
intros;reflexivity.
Qed.

Lemma nth_app_l : forall A k l1 l2 a, k<length l1 -> 
@nth A k (app l1 l2) a = nth k l1 a.
Proof.
intro A;induction k;intros l1 l2 b Hk;destruct l1;simpl in Hk.
apply False_ind;omega.
rewrite <- app_comm_cons.
reflexivity.
simpl in Hk;apply False_ind;omega.
rewrite <- app_comm_cons.
simpl.
apply IHk.
auto with arith.
Qed.



Lemma nth_app_r : forall A k l1 l2 a, k>=length l1 -> 
@nth A k (app l1 l2) a = nth (k - (length l1)) l2 a.
Proof.
intro A;induction k;intros l1 l2 b Hk;destruct l1;simpl.
reflexivity.
simpl in Hk;apply False_ind;omega.
reflexivity.
rewrite IHk;auto with arith.
Qed.

Lemma rev_length : forall A l, (length (@rev A l)) = length l.
intro A;induction l;simpl;trivial.
rewrite length_app.
simpl;rewrite IHl;omega.
Qed.


Lemma nth_rev : forall A l k a, k < length l ->
@nth A k (rev l) a = nth ((length l) - 1  - k) l a.
Proof.
intro A;
induction l;intros k b Hk.
simpl.
destruct k;trivial.
inversion Hk;simpl length;simpl rev.
rewrite nth_app_r;[idtac|rewrite rev_length;auto with arith].
replace ((|l|) -(|rev l|))%nat with O;[idtac|rewrite rev_length;auto with arith].
replace (S (|l|) - 1 - (|l|))%nat with O;[idtac|omega].
reflexivity.
rewrite nth_app_l;[idtac|rewrite rev_length;auto with arith].
replace  (S (|l |) - 1 - k)%nat with (S (|l | - 1 - k));[idtac|omega].
simpl nth.
apply IHl.
omega.
Qed.


Lemma nth_rev_family_n_m:forall m k n P Q, k<m ->
nth k (rev (Xfamily_n_m n P m)) Q != times_X_n P (n + k).
Proof.
intros m k n P Q Hk.
rewrite nth_rev;rewrite family_n_m_length;auto with arith.
rewrite nth_Xfamily;[idtac|omega].
replace (n + m - (m + 1 - 1 - k))%nat with (n+k)%nat;[reflexivity|omega].
Qed.



Lemma times_X_n_lcoef:forall n Q, 
get_coef ((nat_deg Q) + n)%nat (times_X_n Q n) == lcoef Q.
Proof.
induction n;intro Q;simpl.
unfold lcoef.
replace (nat_deg Q + 0)%nat with (nat_deg Q);auto with arith;reflexivity.
replace (nat_deg Q + S n)%nat with (S (nat_deg Q + n))%nat;auto with arith.
setoid_replace (X*times_X_n Q n) with (PX (times_X_n Q n) xH c0).
rewrite times_X_n_get_coef_PX.
apply IHn.
generalize (times_X_n Q n).
intro P.
rewrite (PX_decompose 1 P).
unfold mon.
setoid ring.
Qed.

Lemma Pc_mul : forall a b, (Pc a) * (Pc b) != Pc (a**b).
intros.
simpl.
rewrite Pscal_Pc.
constructor;setoid ring.
Qed.

Lemma Pc_pow : forall n c, (Pc c) ^ n != Pc (c ^^ n).
destruct n.
intro c.
simpl.
rewrite cpow_0;reflexivity.
apply (Pind (fun i => forall c, Pc c ^ Npos i != Pc (c ^^ Npos i)));
intro c.
rewrite cpow_1.
reflexivity.
intros Hind c0.
replace (Npos (Psucc c)) with (Npos c + 1)%N.
rewrite cpow_plus.
rewrite Ppow_plus.
rewrite Hind.

rewrite (Pc_mul (c0 ^^Npos c) c0).
constructor.
rewrite cpow_1.
reflexivity.
rewrite Pplus_one_succ_r.
reflexivity.
Qed.

Section SubresPolDef.


Variables P Q : Pol.

Let p:= nat_deg P.
Let q := nat_deg Q.

Definition subres_family(j:nat) := 
app (Xfamily P (q-j-1))  (Xfamily Q (p-j-1)).

Definition j_subres(j:nat):=det phi (p+q-j-1) (subres_family j).

End SubresPolDef.

Section SubResProps.


Variables P Q:Pol.
Definition p:= nat_deg P.
Definition q := nat_deg Q.
Hypothesis q_le_p : q<=p.



(* subres j aP bQ = a^(p-j) b^(q-j) *subres j P Q *)
Lemma j_subres_scal: forall a b j, j<q ->czero_test a = false -> czero_test b =false ->
j_subres (a !* P) (b !* Q)  j != (cpow  a (N_of_nat (q-j)%nat)) ** (cpow b (N_of_nat (p-j)%nat)) !* (j_subres P Q j).
Proof.
unfold j_subres.
unfold subres_family.
intros a b j j_lt_q a_not_0 b_not_0.
repeat rewrite (nat_deg_scal);trivial.
fold p;fold q.
transitivity (det phi (p + q - j - 1) (app nil
  (app (Xfamily (a !* P) (q - j - 1))
     (Xfamily (b !* Q) (p - j - 1))))).
simpl;reflexivity.
rewrite det_times_Xn_multilin;simpl.
transitivity (cpow a (N_of_nat (q - j - 1 + 1))
!* det phi (p + q - j - 1)
     (app (Xfamily P (q - j - 1))
        (app (Xfamily (b !* Q) (p - j - 1)) nil))).
rewrite <- app_nil_end;reflexivity.
rewrite det_times_Xn_multilin.
rewrite scal_assoc.
apply Pmul_Rat_comp.
rewrite <- app_nil_end;reflexivity.
apply cmul_ext.
assert (G:(q - j - 1 + 1)%nat=(q - j)%nat).
omega.
rewrite G;reflexivity.
assert (G:(p - j - 1 + 1)%nat=(p - j)%nat).
omega.
rewrite G;reflexivity.
Qed.


Variables B H:Pol.
Definition b:= nat_deg B.
Definition h:= nat_deg H.

Hypothesis lt_h_q : h <q.
Hypothesis b_is_p_minus_q :  b= (p - q)%nat.

Hypothesis euclid_relation : P !=H+ B*Q.







Ltac myreplace2 :=
  repeat progress
    (match goal with
    | |- Xfamily _ _ *= Xfamily _ _=> apply X_n_fam_comp;try reflexivity;auto
    | |- context [subres_family _ _ _] => unfold subres_family
    | |- _ =>  myreplace_old
end).

(* pour la suite, cf bugreport hugo*) 
Ltac cool :=match goal with
| |- context ctx [Pol_mul  (sum_of_Pol ?P)  ?Q ] => let t:= 
(context ctx[ (Psum  (fun i => scal (get_coef i P) ((mon (N_of_nat i)))*Q) (nat_deg P)) ] ) in
transitivity t
end.
Lemma det_rev : forall d l1 l2,
length l1 > 0 -> length l2 > 0 ->
det phi  d (app l1 l2) != 
(eps (length l1)) !* (det phi d (app (rev l1) l2)).
Admitted.



Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).
(*
Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).*)
(*we first prove : jsubres P Q j != det (family H (q-j)) (family Q (p-j))*)
intros j Hj.
transitivity (j_subres (H+B*Q) Q j);unfold j_subres.
myreplace2.
rewrite (nat_deg_comp euclid_relation).
myreplace2...
transitivity (det phi (nat_deg (H + B * Q) + nat_deg Q - j - 1) (subres_family (H + ((sum_of_Pol B)* Q)) Q j)).
myreplace2;rewrite <- (P_mon_sum B)...
unfold subres_family.
rewrite <- (nat_deg_comp euclid_relation).
rewrite  (@nat_deg_comp (H + (sum_of_Pol B)*Q) (H+B*Q)).
(*pourquoi ici replace marche pas???*)
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app (Xfamily (H +  (Psum  (fun i => scal (get_coef i B) (mon (N_of_nat i))*Q) (nat_deg B))) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))
).
myreplace2.
apply Padd_comp...
transitivity (
Psum (fun i : nat => (scal (get_coef i B) (mon (N_of_nat i))) * Q)
     (nat_deg B)).
rewrite <- (Psum_mul_r (nat_deg B) (fun i =>  scal (get_coef i B) (mon (N_of_nat i)))).
unfold sum_of_Pol...
apply Psum_ext ;intro n...
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app
     (Xfamily
        (H +
         Psum (fun i : nat => scal (get_coef i B) (Q*(mon (N_of_nat i))))
           (nat_deg B)) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))).
myreplace2.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
rewrite scal_Passoc.
unfold scal.
setoid_replace (mon (N_of_nat n) * Q) with (Q*mon (N_of_nat n));setoid ring.
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1) (app
(Xfamily H (nat_deg Q - j - 1))
(Xfamily Q (nat_deg (H + B*Q) - j - 1)))).
apply (@det_family_sum
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg B) (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).
rewrite <- euclid_relation.
fold p q b h;rewrite b_is_p_minus_q.
omega_helper.
(* la*)
clear;omega.
clear - lt_h_q Hj;omega.
clear - lt_h_q Hj;omega.
rewrite det_skip_axiom;fold p q h;
try (repeat rewrite family_length).
auto with arith.
auto with arith.
rewrite <- euclid_relation;fold p.
rewrite <- scal_assoc.
apply Pmul_Rat_comp.
replace (p-j-1)%nat with ( (S (p -h-1)) + (h -j -1))%nat.
(* we cut the family of powers of Q into two :  the first triangular part,
of length q+h-j-1,giving the power on lcoef Q,
and the one remaining in the det*)
transitivity 
(pdet (p + q - j - 1)%nat
  (app (app (Xfamily_n_m (S (h-j-1)%nat) Q (p-h-1)) (Xfamily Q (h - j - 1)))
  (Xfamily H (q - j - 1)))).
myreplace_old.
apply (@Xfamily_app (p-h-1)%nat (h-j-1)%nat Q).
rewrite app_ass.

rewrite 
(det_rev (p+q-j-1)%nat (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)));try
rewrite family_n_m_length.
omega.
rewrite length_app.
pattern Xfamily at 1.
rewrite family_length.
clear - lt_h_q Hj;omega.
(* ok, now we develop the determinant *)
rewrite (det_trig phi 
(rev (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)))
((app (Xfamily Q (h - j - 1)) (Xfamily H (q - j - 1))))
(p - h)
P0
(p+q-j-1)
(Pc (lcoef Q))).
(* we prove that degree is low at the end of the list*)
Import PDet. (*???*)
intros T HTIn index Hindex1 Hindex2.
unfold phi.

replace (p - h - 1 + 1 + 1)%nat with (p-h+1)%nat;[idtac|omega_helper;clear - lt_h_q q_le_p;omega].
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) index);intro Hcase.
reflexivity.
destruct index.
reflexivity.
destruct index.
apply False_ind; apply (lt_irrefl 1 Hindex1).
destruct (phi.even_odd_dec (S (S index))).
replace (S (S index) -2)%nat with index;[idtac|auto with arith].
constructor.
apply (@get_coef_deg (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;
[idtac|clear - Hj;omega_helper;clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega_helper;omega].
unfold h.
apply family_deg;assumption.
clear e B  euclid_relation HTIn T b_is_p_minus_q Hindex1.
assert (Aux1 : index <= p-h-1);[clear - Hindex2;omega_helper;omega|clear Hindex2].
assert(Aux2 : p+q-j-1 > index);[clear - Hcase;omega_helper;omega|clear Hcase].
assert(Aux3 :  p  - j - index >  h - j).
omega.
clear - Aux3 lt_h_q;omega.
constructor.
assert (Rate: get_coef (p + q - j - 1 - (S (S index) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation HTIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.
rewrite Rate.
setoid ring.

(* we prove that the begining of the list is triangular*)
intros i k k_lt_i Hi.
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) (S (S i)));intro G.
reflexivity.
assert (Goal_aux : 
get_coef (p + q - j - 1 - (S (S i) - 2))
(nth k (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) P0)
 == c0).
rewrite nth_Xfamily.
 apply get_coef_deg with
(q+ (S (h - j - 1) + (p - h - 1) - k))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Aux1 i_lt_k;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.


apply get_coef_deg with (q+ (S (h - j - 1) + (p - h -1)))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).

clear - Hi;omega.
unfold q.
apply plus_le_compat_l.
generalize (h - j)%nat;intro n.
generalize (p-h)%nat;intro m.
clear;omega.
replace (S (S i) - 2)%nat with i;[idtac|clear;omega].
replace (S (h - j - 1))%nat with (h - j)%nat;[idtac|clear - Hj;omega].
omega_helper.

apply (plus_le_compat_l (p - h - 1) (p -h ) (h - j)).
omega_helper;try (clear - Aux2;omega).
unfold q.
clear;omega.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q Hj;omega.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
cl


(*rewrite family_n_m_length in Hi.*)
(*assert (Aux1: k <= p - h - 1);[clear -Hi k_lt_i;omega|idtac].*)

rewrite nth_rev_family_n_m.
clear - k_lt_i Hi;omega.
apply get_coef_deg with (q+ (S (h - j - 1) + i))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Hi;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.
(* we prove that the coefs ont the begining of the diag are all Q*)
intros T TIn i lt_i.
unfold phi.
rewrite family_n_m_length in lt_i.
assert (Aux:i<p-h);[clear - lt_i q_le_p lt_h_q;omega|clear lt_i].
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
assert (Aux2 : p+q-j+1<= S (S i));[clear - a Hj lt_h_q q_le_p;omega|clear a].
apply False_ind;omega.
assert (Goal_aux :
(get_coef (p + q - j - 1 - (S (S i) - 2))
 (nth i (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T))
== lcoef Q).
rewrite  nth_Xfamily;[idtac|clear - Aux;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux1:p-h>=1);[clear - Aux;omega|idtac].
replace (p + q - j - 1 - i)%nat with (q + (p-j-1-i))%nat.

replace ((S (h - j - 1) + (p - h - 1) - i))%nat with (p-j-1-i)%nat.

unfold q;apply times_X_n_lcoef.

replace (S (h - j -1))%nat with (h - j)%nat;[idtac|symmetry;apply omega2;assumption].
omega_helper.
replace (p-j-1)%nat with (p-1-j)%nat;trivial.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q;omega.
assert (Aux2 : p -j -1>= 1);[clear - q_le_p lt_h_q Hj;omega|idtac].
omega_helper;try (clear - Aux1;omega).
clear -Aux2;omega.
clear - Aux2;omega.
clear - Hj lt_h_q q_le_p Aux;omega.
destruct ( phi.even_odd_dec (S (S i)));rewrite Goal_aux...
rewrite family_n_m_length.
rewrite Pscal_Pmul_l.
apply Pmul_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
rewrite Pc_pow.
constructor;reflexivity.
apply det_f_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
intros n T.
unfold phi.
replace (p+q-j-1+2)%nat with (p+q-j+1)%nat;[idtac|omega].
replace (q + h - j - 1 + 2)%nat with (q + h - j +1)%nat;[idtac|omega].
destruct (le_gt_dec (p + q - j +1) (n + (p - h)));
destruct ( le_gt_dec (q + h - j +1)).
reflexivity.
apply False_ind;omega.
caseEq (n + (p - h))%nat;intro n0.
reflexivity.
intro G;destruct n0;try reflexivity.
caseEq n.
intro G1.
rewrite G1 in l;clear -l.
apply False_ind;omega.
intros n0 G2;caseEq (p-h)%nat;intro G3.
rewrite G3 in G.
replace (n+0)%nat with n in G;[idtac|omega];rewrite G in l.
clear - l lt_h_q Hj;apply False_ind;omega.
intro G4.
rewrite G4 in G;rewrite G2 in G;clear - G;apply False_ind;omega.
assert (Aux3:(p + q - j + 1=q+h-j+1+(p-h))%nat).
clear -q_le_p lt_h_q Hj;omega.
rewrite Aux3 in g.
clear -g l;apply False_ind;omega.
caseEq (n+(p-h))%nat.
intro G1;caseEq n.
intro G2;reflexivity.
intros n0 G2.
clear - G2 G1 lt_h_q q_le_p;apply False_ind;omega.
intros n0 G1.
caseEq n.
intro G2.
rewrite G2 in G1;simpl in G1.
rewrite G2 in g;simpl  in g. 
destruct n0.
assert ( Aux : Pc (get_coef (p + q - j - 1 - (S (S n0) - 2)) T) = P0).



case (le_gt_dec  (p + q - j - 1 + 2) i);intro G3.
reflexivity.
destruct i...
destruct i.
clear - G1;apply False_ind;omega.
assert (Aux: get_coef (p + q - j - 1 - (S (S i) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  TIn);intro TIn2.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation TIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.







rewrite family_n_m_length.
intros T HTIn index Hindex1 Hindex2.
replace (p - h - 1 + 1 + 1)%nat with (p-h+1)%nat;[idtac|omega_helper;clear - lt_h_q q_le_p;omega].
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) index);intro Hcase.
reflexivity.
destruct index.
reflexivity.
destruct index.
apply False_ind; apply (lt_irrefl 1 Hindex1).
destruct (phi.even_odd_dec (S (S index))).
replace (S (S index) -2)%nat with index;[idtac|auto with arith].
constructor.
apply (@get_coef_deg (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;
[idtac|clear - Hj;omega_helper;clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega_helper;omega].
unfold h.
apply family_deg;assumption.
clear e B  euclid_relation HTIn T b_is_p_minus_q Hindex1.
assert (Aux1 : index <= p-h-1);[clear - Hindex2;omega_helper;omega|clear Hindex2].
assert(Aux2 : p+q-j-1 > index);[clear - Hcase;omega_helper;omega|clear Hcase].
assert(Aux3 :  p  - j - index >  h - j).
omega.
clear - Aux3 lt_h_q;omega.
constructor.
assert (Rate: get_coef (p + q - j - 1 - (S (S index) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation HTIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.
rewrite Rate.
setoid ring.

(* we prove that the begining of the list is triangular*)
intros T TIn i k i_lt_k Hi.
unfold phi.
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
reflexivity.
assert (Goal_aux : 
get_coef (p + q - j - 1 - (S (S i) - 2))
(nth k (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T)
 == c0).
rewrite family_n_m_length in Hi.
assert (Aux1: k <= p - h - 1).
clear -Hi;omega.
rewrite nth_Xfamily...
apply get_coef_deg with (q+ (S (h - j - 1) + (p - h - 1) - k))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Aux1 i_lt_k;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.
(* we prove that the coefs ont the begining of the diag are all Q*)
intros T TIn i lt_i.
unfold phi.
rewrite family_n_m_length in lt_i.
assert (Aux:i<p-h);[clear - lt_i q_le_p lt_h_q;omega|clear lt_i].
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
assert (Aux2 : p+q-j+1<= S (S i));[clear - a Hj lt_h_q q_le_p;omega|clear a].
apply False_ind;omega.
assert (Goal_aux :
(get_coef (p + q - j - 1 - (S (S i) - 2))
 (nth i (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T))
== lcoef Q).
rewrite  nth_Xfamily;[idtac|clear - Aux;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux1:p-h>=1);[clear - Aux;omega|idtac].
replace (p + q - j - 1 - i)%nat with (q + (p-j-1-i))%nat.

replace ((S (h - j - 1) + (p - h - 1) - i))%nat with (p-j-1-i)%nat.

unfold q;apply times_X_n_lcoef.

replace (S (h - j -1))%nat with (h - j)%nat;[idtac|symmetry;apply omega2;assumption].
omega_helper.
replace (p-j-1)%nat with (p-1-j)%nat;trivial.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q;omega.
assert (Aux2 : p -j -1>= 1);[clear - q_le_p lt_h_q Hj;omega|idtac].
omega_helper;try (clear - Aux1;omega).
clear -Aux2;omega.
clear - Aux2;omega.
clear - Hj lt_h_q q_le_p Aux;omega.
destruct ( phi.even_odd_dec (S (S i)));rewrite Goal_aux...
rewrite family_n_m_length.
rewrite Pscal_Pmul_l.
apply Pmul_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
rewrite Pc_pow.
constructor;reflexivity.
apply det_f_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
intros n T.
unfold phi.
replace (p+q-j-1+2)%nat with (p+q-j+1)%nat;[idtac|omega].
replace (q + h - j - 1 + 2)%nat with (q + h - j +1)%nat;[idtac|omega].
destruct (le_gt_dec (p + q - j +1) (n + (p - h)));
destruct ( le_gt_dec (q + h - j +1)).
reflexivity.
apply False_ind;omega.
caseEq (n + (p - h))%nat;intro n0.
reflexivity.
intro G;destruct n0;try reflexivity.
caseEq n.
intro G1.
rewrite G1 in l;clear -l.
apply False_ind;omega.
intros n0 G2;caseEq (p-h)%nat;intro G3.
rewrite G3 in G.
replace (n+0)%nat with n in G;[idtac|omega];rewrite G in l.
clear - l lt_h_q Hj;apply False_ind;omega.
intro G4.
rewrite G4 in G;rewrite G2 in G;clear - G;apply False_ind;omega.
assert (Aux3:(p + q - j + 1=q+h-j+1+(p-h))%nat).
clear -q_le_p lt_h_q Hj;omega.
rewrite Aux3 in g.
clear -g l;apply False_ind;omega.
caseEq (n+(p-h))%nat.
intro G1;caseEq n.
intro G2;reflexivity.
intros n0 G2.
clear - G2 G1 lt_h_q q_le_p;apply False_ind;omega.
intros n0 G1.
caseEq n.
intro G2.
rewrite G2 in G1;simpl in G1.
rewrite G2 in g;simpl  in g. 
destruct n0.
assert ( Aux : Pc (get_coef (p + q - j - 1 - (S (S n0) - 2)) T) = P0).



Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).
(*
Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).*)
(*we first prove : jsubres P Q j != det (family H (q-j)) (family Q (p-j))*)
intros j Hj.
transitivity (j_subres (H+B*Q) Q j);unfold j_subres.
myreplace2.
rewrite (nat_deg_comp euclid_relation).
myreplace2...
transitivity (det phi (nat_deg (H + B * Q) + nat_deg Q - j - 1) (subres_family (H + ((sum_of_Pol B)* Q)) Q j)).
myreplace2;rewrite <- (P_mon_sum B)...
unfold subres_family.
rewrite <- (nat_deg_comp euclid_relation).
rewrite  (@nat_deg_comp (H + (sum_of_Pol B)*Q) (H+B*Q)).
(*pourquoi ici replace marche pas???*)
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app (Xfamily (H +  (Psum  (fun i => scal (get_coef i B) (mon (N_of_nat i))*Q) (nat_deg B))) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))
).
myreplace2.
apply Padd_comp...
transitivity (
Psum (fun i : nat => (scal (get_coef i B) (mon (N_of_nat i))) * Q)
     (nat_deg B)).
rewrite <- (Psum_mul_r (nat_deg B) (fun i =>  scal (get_coef i B) (mon (N_of_nat i)))).
unfold sum_of_Pol...
apply Psum_ext ;intro n...
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app
     (Xfamily
        (H +
         Psum (fun i : nat => scal (get_coef i B) (Q*(mon (N_of_nat i))))
           (nat_deg B)) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))).
myreplace2.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
rewrite scal_Passoc.
unfold scal.
setoid_replace (mon (N_of_nat n) * Q) with (Q*mon (N_of_nat n));setoid ring.
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1) (app
(Xfamily H (nat_deg Q - j - 1))
(Xfamily Q (nat_deg (H + B*Q) - j - 1)))).
apply (@det_family_sum
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg B) (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).
rewrite <- euclid_relation.
fold p q b h;rewrite b_is_p_minus_q.
omega_helper.
(* la*)
clear;omega.
clear - lt_h_q Hj;omega.
clear - lt_h_q Hj;omega.
rewrite det_skip_axiom;fold p q h;
try (repeat rewrite family_length).
auto with arith.
auto with arith.
rewrite <- euclid_relation;fold p.
rewrite <- scal_assoc.
apply Pmul_Rat_comp.
replace (p-j-1)%nat with ( (S (p -h-1)) + (h -j -1))%nat.
(* we cut the family of powers of Q into two :  the first triangular part,
of length q+h-j-1,giving the power on lcoef Q,
and the one remaining in the det*)
transitivity 
(pdet (p + q - j - 1)%nat
  (app (app (Xfamily_n_m (S (h-j-1)%nat) Q (p-h-1)) (Xfamily Q (h - j - 1)))
  (Xfamily H (q - j - 1)))).
myreplace_old.
apply (@Xfamily_app (p-h-1)%nat (h-j-1)%nat Q).
rewrite app_ass.
(* ok, now we develop the determinant *)
rewrite (det_trig phi 
(Xfamily_n_m (S (h - j - 1)) Q (p - h - 1))
((app (Xfamily Q (h - j - 1)) (Xfamily H (q - j - 1))))
(p + q - j - 1)
(Pc (lcoef Q))).
(* we prove that degree is low at the end of the list*)
Import PDet. (*???*)
rewrite family_n_m_length.
intros T HTIn index Hindex1 Hindex2.
replace (p - h - 1 + 1 + 1)%nat with (p-h+1)%nat;[idtac|omega_helper;clear - lt_h_q q_le_p;omega].
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) index);intro Hcase.
reflexivity.
destruct index.
reflexivity.
destruct index.
apply False_ind; apply (lt_irrefl 1 Hindex1).
destruct (phi.even_odd_dec (S (S index))).
replace (S (S index) -2)%nat with index;[idtac|auto with arith].
constructor.
apply (@get_coef_deg (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;
[idtac|clear - Hj;omega_helper;clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega_helper;omega].
unfold h.
apply family_deg;assumption.
clear e B  euclid_relation HTIn T b_is_p_minus_q Hindex1.
assert (Aux1 : index <= p-h-1);[clear - Hindex2;omega_helper;omega|clear Hindex2].
assert(Aux2 : p+q-j-1 > index);[clear - Hcase;omega_helper;omega|clear Hcase].
assert(Aux3 :  p  - j - index >  h - j).
omega.
clear - Aux3 lt_h_q;omega.
constructor.
assert (Rate: get_coef (p + q - j - 1 - (S (S index) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation HTIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.
rewrite Rate.
setoid ring.

(* we prove that the begining of the list is triangular*)
intros T TIn i k i_lt_k Hi.
unfold phi.
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
reflexivity.
assert (Goal_aux : 
get_coef (p + q - j - 1 - (S (S i) - 2))
(nth k (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T)
 == c0).
rewrite family_n_m_length in Hi.
assert (Aux1: k <= p - h - 1).
clear -Hi;omega.
rewrite nth_Xfamily...
apply get_coef_deg with (q+ (S (h - j - 1) + (p - h - 1) - k))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Aux1 i_lt_k;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.
(* we prove that the coefs ont the begining of the diag are all Q*)
intros T TIn i lt_i.
unfold phi.
rewrite family_n_m_length in lt_i.
assert (Aux:i<p-h);[clear - lt_i q_le_p lt_h_q;omega|clear lt_i].
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
assert (Aux2 : p+q-j+1<= S (S i));[clear - a Hj lt_h_q q_le_p;omega|clear a].
apply False_ind;omega.
assert (Goal_aux :
(get_coef (p + q - j - 1 - (S (S i) - 2))
 (nth i (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T))
== lcoef Q).
rewrite  nth_Xfamily;[idtac|clear - Aux;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux1:p-h>=1);[clear - Aux;omega|idtac].
replace (p + q - j - 1 - i)%nat with (q + (p-j-1-i))%nat.

replace ((S (h - j - 1) + (p - h - 1) - i))%nat with (p-j-1-i)%nat.

unfold q;apply times_X_n_lcoef.

replace (S (h - j -1))%nat with (h - j)%nat;[idtac|symmetry;apply omega2;assumption].
omega_helper.
replace (p-j-1)%nat with (p-1-j)%nat;trivial.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q;omega.
assert (Aux2 : p -j -1>= 1);[clear - q_le_p lt_h_q Hj;omega|idtac].
omega_helper;try (clear - Aux1;omega).
clear -Aux2;omega.
clear - Aux2;omega.
clear - Hj lt_h_q q_le_p Aux;omega.
destruct ( phi.even_odd_dec (S (S i)));rewrite Goal_aux...
rewrite family_n_m_length.
rewrite Pscal_Pmul_l.
apply Pmul_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
rewrite Pc_pow.
constructor;reflexivity.
apply det_f_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
intros n T.
unfold phi.
replace (p+q-j-1+2)%nat with (p+q-j+1)%nat;[idtac|omega].
replace (q + h - j - 1 + 2)%nat with (q + h - j +1)%nat;[idtac|omega].
destruct (le_gt_dec (p + q - j +1) (n + (p - h)));
destruct ( le_gt_dec (q + h - j +1)).
reflexivity.
apply False_ind;omega.
caseEq (n + (p - h))%nat;intro n0.
reflexivity.
intro G;destruct n0;try reflexivity.
caseEq n.
intro G1.
rewrite G1 in l;clear -l.
apply False_ind;omega.
intros n0 G2;caseEq (p-h)%nat;intro G3.
rewrite G3 in G.
replace (n+0)%nat with n in G;[idtac|omega];rewrite G in l.
clear - l lt_h_q Hj;apply False_ind;omega.
intro G4.
rewrite G4 in G;rewrite G2 in G;clear - G;apply False_ind;omega.
assert (Aux3:(p + q - j + 1=q+h-j+1+(p-h))%nat).
clear -q_le_p lt_h_q Hj;omega.
rewrite Aux3 in g.
clear -g l;apply False_ind;omega.
caseEq (n+(p-h))%nat.
intro G1;caseEq n.
intro G2;reflexivity.
intros n0 G2.
clear - G2 G1 lt_h_q q_le_p;apply False_ind;omega.
intros n0 G1.
caseEq n.
intro G2.
rewrite G2 in G1;simpl in G1.
rewrite G2 in g;simpl  in g. 
destruct n0.
assert ( Aux : Pc (get_coef (p + q - j - 1 - (S (S n0) - 2)) T) = P0).


Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).
(*
Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).*)
(*we first prove : jsubres P Q j != det (family H (q-j)) (family Q (p-j))*)
intros j Hj.
transitivity (j_subres (H+B*Q) Q j);unfold j_subres.
myreplace2.
rewrite (nat_deg_comp euclid_relation).
myreplace2...
transitivity (det phi (nat_deg (H + B * Q) + nat_deg Q - j - 1) (subres_family (H + ((sum_of_Pol B)* Q)) Q j)).
myreplace2;rewrite <- (P_mon_sum B)...
unfold subres_family.
rewrite <- (nat_deg_comp euclid_relation).
rewrite  (@nat_deg_comp (H + (sum_of_Pol B)*Q) (H+B*Q)).
(*pourquoi ici replace marche pas???*)
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app (Xfamily (H +  (Psum  (fun i => scal (get_coef i B) (mon (N_of_nat i))*Q) (nat_deg B))) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))
).
myreplace2.
apply Padd_comp...
transitivity (
Psum (fun i : nat => (scal (get_coef i B) (mon (N_of_nat i))) * Q)
     (nat_deg B)).
rewrite <- (Psum_mul_r (nat_deg B) (fun i =>  scal (get_coef i B) (mon (N_of_nat i)))).
unfold sum_of_Pol...
apply Psum_ext ;intro n...
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app
     (Xfamily
        (H +
         Psum (fun i : nat => scal (get_coef i B) (Q*(mon (N_of_nat i))))
           (nat_deg B)) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))).
myreplace2.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
rewrite scal_Passoc.
unfold scal.
setoid_replace (mon (N_of_nat n) * Q) with (Q*mon (N_of_nat n));setoid ring.
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1) (app
(Xfamily H (nat_deg Q - j - 1))
(Xfamily Q (nat_deg (H + B*Q) - j - 1)))).
apply (@det_family_sum
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg B) (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).
rewrite <- euclid_relation.
fold p q b h;rewrite b_is_p_minus_q.
omega_helper.
(* la*)
clear;omega.
clear - lt_h_q Hj;omega.
clear - lt_h_q Hj;omega.
rewrite det_skip_axiom;fold p q h;
try (repeat rewrite family_length).
auto with arith.
auto with arith.
rewrite <- euclid_relation;fold p.
rewrite <- scal_assoc.
apply Pmul_Rat_comp.
replace (p-j-1)%nat with ( (S (p -h-1)) + (h -j -1))%nat.
(* we cut the family of powers of Q into two :  the first triangular part,
of length q+h-j-1,giving the power on lcoef Q,
and the one remaining in the det*)
transitivity 
(pdet (p + q - j - 1)%nat
  (app (app (Xfamily_n_m (S (h-j-1)%nat) Q (p-h-1)) (Xfamily Q (h - j - 1)))
  (Xfamily H (q - j - 1)))).
myreplace_old.
apply (@Xfamily_app (p-h-1)%nat (h-j-1)%nat Q).
rewrite app_ass.
(* ok, now we develop the determinant *)
rewrite (det_trig phi 
(Xfamily_n_m (S (h - j - 1)) Q (p - h - 1))
((app (Xfamily Q (h - j - 1)) (Xfamily H (q - j - 1))))
(p + q - j - 1)
(Pc (lcoef Q))).
(* we prove that degree is low at the end of the list*)
Import PDet. (*???*)
rewrite family_n_m_length.
intros T HTIn index Hindex1 Hindex2.
replace (p - h - 1 + 1 + 1)%nat with (p-h+1)%nat;[idtac|omega_helper;clear - lt_h_q q_le_p;omega].
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) index);intro Hcase.
reflexivity.
destruct index.
reflexivity.
destruct index.
apply False_ind; apply (lt_irrefl 1 Hindex1).
destruct (phi.even_odd_dec (S (S index))).
replace (S (S index) -2)%nat with index;[idtac|auto with arith].
constructor.
apply (@get_coef_deg (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;
[idtac|clear - Hj;omega_helper;clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega_helper;omega].
unfold h.
apply family_deg;assumption.
clear e B  euclid_relation HTIn T b_is_p_minus_q Hindex1.
assert (Aux1 : index <= p-h-1);[clear - Hindex2;omega_helper;omega|clear Hindex2].
assert(Aux2 : p+q-j-1 > index);[clear - Hcase;omega_helper;omega|clear Hcase].
assert(Aux3 :  p  - j - index >  h - j).
omega.
clear - Aux3 lt_h_q;omega.
constructor.
assert (Rate: get_coef (p + q - j - 1 - (S (S index) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation HTIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.
rewrite Rate.
setoid ring.

(* we prove that the begining of the list is triangular*)
intros T TIn i k i_lt_k Hi.
unfold phi.
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
reflexivity.
assert (Goal_aux : 
get_coef (p + q - j - 1 - (S (S i) - 2))
(nth k (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T)
 == c0).
rewrite family_n_m_length in Hi.
assert (Aux1: k <= p - h - 1).
clear -Hi;omega.
rewrite nth_Xfamily...
apply get_coef_deg with (q+ (S (h - j - 1) + (p - h - 1) - k))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Aux1 i_lt_k;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.
(* we prove that the coefs ont the begining of the diag are all Q*)
intros T TIn i lt_i.
unfold phi.
rewrite family_n_m_length in lt_i.
assert (Aux:i<p-h);[clear - lt_i q_le_p lt_h_q;omega|clear lt_i].
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
assert (Aux2 : p+q-j+1<= S (S i));[clear - a Hj lt_h_q q_le_p;omega|clear a].
apply False_ind;omega.
assert (Goal_aux :
(get_coef (p + q - j - 1 - (S (S i) - 2))
 (nth i (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T))
== lcoef Q).
rewrite  nth_Xfamily;[idtac|clear - Aux;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux1:p-h>=1);[clear - Aux;omega|idtac].
replace (p + q - j - 1 - i)%nat with (q + (p-j-1-i))%nat.

replace ((S (h - j - 1) + (p - h - 1) - i))%nat with (p-j-1-i)%nat.

unfold q;apply times_X_n_lcoef.

replace (S (h - j -1))%nat with (h - j)%nat;[idtac|symmetry;apply omega2;assumption].
omega_helper.
replace (p-j-1)%nat with (p-1-j)%nat;trivial.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q;omega.
assert (Aux2 : p -j -1>= 1);[clear - q_le_p lt_h_q Hj;omega|idtac].
omega_helper;try (clear - Aux1;omega).
clear -Aux2;omega.
clear - Aux2;omega.
clear - Hj lt_h_q q_le_p Aux;omega.
destruct ( phi.even_odd_dec (S (S i)));rewrite Goal_aux...
rewrite family_n_m_length.
rewrite Pscal_Pmul_l.
apply Pmul_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
rewrite Pc_pow.
constructor;reflexivity.
apply det_f_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
intros n T.
unfold phi.
replace (p+q-j-1+2)%nat with (p+q-j+1)%nat;[idtac|omega].
replace (q + h - j - 1 + 2)%nat with (q + h - j +1)%nat;[idtac|omega].
destruct (le_gt_dec (p + q - j +1) (n + (p - h)));
destruct ( le_gt_dec (q + h - j +1)).
reflexivity.
apply False_ind;omega.
caseEq (n + (p - h))%nat;intro n0.
reflexivity.
intro G;destruct n0;try reflexivity.
caseEq n.
intro G1.
rewrite G1 in l;clear -l.
apply False_ind;omega.
intros n0 G2;caseEq (p-h)%nat;intro G3.
rewrite G3 in G.
replace (n+0)%nat with n in G;[idtac|omega];rewrite G in l.
clear - l lt_h_q Hj;apply False_ind;omega.
intro G4.
rewrite G4 in G;rewrite G2 in G;clear - G;apply False_ind;omega.
assert (Aux3:(p + q - j + 1=q+h-j+1+(p-h))%nat).
clear -q_le_p lt_h_q Hj;omega.
rewrite Aux3 in g.
clear -g l;apply False_ind;omega.
caseEq (n+(p-h))%nat.
intro G1;caseEq n.
intro G2;reflexivity.
intros n0 G2.
clear - G2 G1 lt_h_q q_le_p;apply False_ind;omega.
intros n0 G1.
caseEq n.
intro G2.
rewrite G2 in G1;simpl in G1.
rewrite G2 in g;simpl  in g. 
destruct n0.
assert ( Aux : Pc (get_coef (p + q - j - 1 - (S (S n0) - 2)) T) = P0).




Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).
(*
Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).*)
(*we first prove : jsubres P Q j != det (family H (q-j)) (family Q (p-j))*)
intros j Hj.
transitivity (j_subres (H+B*Q) Q j);unfold j_subres.
myreplace2.
rewrite (nat_deg_comp euclid_relation).
myreplace2...
transitivity (det phi (nat_deg (H + B * Q) + nat_deg Q - j - 1) (subres_family (H + ((sum_of_Pol B)* Q)) Q j)).
myreplace2;rewrite <- (P_mon_sum B)...
unfold subres_family.
rewrite <- (nat_deg_comp euclid_relation).
rewrite  (@nat_deg_comp (H + (sum_of_Pol B)*Q) (H+B*Q)).
(*pourquoi ici replace marche pas???*)
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app (Xfamily (H +  (Psum  (fun i => scal (get_coef i B) (mon (N_of_nat i))*Q) (nat_deg B))) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))
).
myreplace2.
apply Padd_comp...
transitivity (
Psum (fun i : nat => (scal (get_coef i B) (mon (N_of_nat i))) * Q)
     (nat_deg B)).
rewrite <- (Psum_mul_r (nat_deg B) (fun i =>  scal (get_coef i B) (mon (N_of_nat i)))).
unfold sum_of_Pol...
apply Psum_ext ;intro n...
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app
     (Xfamily
        (H +
         Psum (fun i : nat => scal (get_coef i B) (Q*(mon (N_of_nat i))))
           (nat_deg B)) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))).
myreplace2.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
rewrite scal_Passoc.
unfold scal.
setoid_replace (mon (N_of_nat n) * Q) with (Q*mon (N_of_nat n));setoid ring.
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1) (app
(Xfamily H (nat_deg Q - j - 1))
(Xfamily Q (nat_deg (H + B*Q) - j - 1)))).
apply (@det_family_sum
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg B) (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).
rewrite <- euclid_relation.
fold p q b h;rewrite b_is_p_minus_q.
omega_helper.
(* la*)
clear;omega.
clear - lt_h_q Hj;omega.
clear - lt_h_q Hj;omega.
rewrite det_skip_axiom;fold p q h;
try (repeat rewrite family_length).
auto with arith.
auto with arith.
rewrite <- euclid_relation;fold p.
rewrite <- scal_assoc.
apply Pmul_Rat_comp.
replace (p-j-1)%nat with ( (S (p -h-1)) + (h -j -1))%nat.
(* we cut the family of powers of Q into two :  the first triangular part,
of length q+h-j-1,giving the power on lcoef Q,
and the one remaining in the det*)
transitivity 
(pdet (p + q - j - 1)%nat
  (app (app (Xfamily_n_m (S (h-j-1)%nat) Q (p-h-1)) (Xfamily Q (h - j - 1)))
  (Xfamily H (q - j - 1)))).
myreplace_old.
apply (@Xfamily_app (p-h-1)%nat (h-j-1)%nat Q).
rewrite app_ass.
(* ok, now we develop the determinant *)
rewrite (det_trig phi 
(Xfamily_n_m (S (h - j - 1)) Q (p - h - 1))
((app (Xfamily Q (h - j - 1)) (Xfamily H (q - j - 1))))
(p + q - j - 1)
(Pc (lcoef Q))).
(* we prove that degree is low at the end of the list*)
Import PDet. (*???*)
rewrite family_n_m_length.
intros T HTIn index Hindex1 Hindex2.
replace (p - h - 1 + 1 + 1)%nat with (p-h+1)%nat;[idtac|omega_helper;clear - lt_h_q q_le_p;omega].
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) index);intro Hcase.
reflexivity.
destruct index.
reflexivity.
destruct index.
apply False_ind; apply (lt_irrefl 1 Hindex1).
destruct (phi.even_odd_dec (S (S index))).
replace (S (S index) -2)%nat with index;[idtac|auto with arith].
constructor.
apply (@get_coef_deg (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;
[idtac|clear - Hj;omega_helper;clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega_helper;omega].
unfold h.
apply family_deg;assumption.
clear e B  euclid_relation HTIn T b_is_p_minus_q Hindex1.
assert (Aux1 : index <= p-h-1);[clear - Hindex2;omega_helper;omega|clear Hindex2].
assert(Aux2 : p+q-j-1 > index);[clear - Hcase;omega_helper;omega|clear Hcase].
assert(Aux3 :  p  - j - index >  h - j).
omega.
clear - Aux3 lt_h_q;omega.
constructor.
assert (Rate: get_coef (p + q - j - 1 - (S (S index) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation HTIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.
rewrite Rate.
setoid ring.

(* we prove that the begining of the list is triangular*)
intros T TIn i k i_lt_k Hi.
unfold phi.
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
reflexivity.
assert (Goal_aux : 
get_coef (p + q - j - 1 - (S (S i) - 2))
(nth k (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T)
 == c0).
rewrite family_n_m_length in Hi.
assert (Aux1: k <= p - h - 1).
clear -Hi;omega.
rewrite nth_Xfamily...
apply get_coef_deg with (q+ (S (h - j - 1) + (p - h - 1) - k))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Aux1 i_lt_k;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.
(* we prove that the coefs ont the begining of the diag are all Q*)
intros T TIn i lt_i.
unfold phi.
rewrite family_n_m_length in lt_i.
assert (Aux:i<p-h);[clear - lt_i q_le_p lt_h_q;omega|clear lt_i].
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
assert (Aux2 : p+q-j+1<= S (S i));[clear - a Hj lt_h_q q_le_p;omega|clear a].
apply False_ind;omega.
assert (Goal_aux :
(get_coef (p + q - j - 1 - (S (S i) - 2))
 (nth i (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T))
== lcoef Q).
rewrite  nth_Xfamily;[idtac|clear - Aux;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux1:p-h>=1);[clear - Aux;omega|idtac].
replace (p + q - j - 1 - i)%nat with (q + (p-j-1-i))%nat.

replace ((S (h - j - 1) + (p - h - 1) - i))%nat with (p-j-1-i)%nat.

unfold q;apply times_X_n_lcoef.

replace (S (h - j -1))%nat with (h - j)%nat;[idtac|symmetry;apply omega2;assumption].
omega_helper.
replace (p-j-1)%nat with (p-1-j)%nat;trivial.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q;omega.
assert (Aux2 : p -j -1>= 1);[clear - q_le_p lt_h_q Hj;omega|idtac].
omega_helper;try (clear - Aux1;omega).
clear -Aux2;omega.
clear - Aux2;omega.
clear - Hj lt_h_q q_le_p Aux;omega.
destruct ( phi.even_odd_dec (S (S i)));rewrite Goal_aux...
rewrite family_n_m_length.
rewrite Pscal_Pmul_l.
apply Pmul_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
rewrite Pc_pow.
constructor;reflexivity.
apply det_f_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
intros n T.
unfold phi.
replace (p+q-j-1+2)%nat with (p+q-j+1)%nat;[idtac|omega].
replace (q + h - j - 1 + 2)%nat with (q + h - j +1)%nat;[idtac|omega].
destruct (le_gt_dec (p + q - j +1) (n + (p - h)));
destruct ( le_gt_dec (q + h - j +1)).
reflexivity.
apply False_ind;omega.
caseEq (n + (p - h))%nat;intro n0.
reflexivity.
intro G;destruct n0;try reflexivity.
caseEq n.
intro G1.
rewrite G1 in l;clear -l.
apply False_ind;omega.
intros n0 G2;caseEq (p-h)%nat;intro G3.
rewrite G3 in G.
replace (n+0)%nat with n in G;[idtac|omega];rewrite G in l.
clear - l lt_h_q Hj;apply False_ind;omega.
intro G4.
rewrite G4 in G;rewrite G2 in G;clear - G;apply False_ind;omega.
assert (Aux3:(p + q - j + 1=q+h-j+1+(p-h))%nat).
clear -q_le_p lt_h_q Hj;omega.
rewrite Aux3 in g.
clear -g l;apply False_ind;omega.
caseEq (n+(p-h))%nat.
intro G1;caseEq n.
intro G2;reflexivity.
intros n0 G2.
clear - G2 G1 lt_h_q q_le_p;apply False_ind;omega.
intros n0 G1.
caseEq n.
intro G2.
rewrite G2 in G1;simpl in G1.
rewrite G2 in g;simpl  in g. 
destruct n0.
assert ( Aux : Pc (get_coef (p + q - j - 1 - (S (S n0) - 2)) T) = P0).



Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).
(*
Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-j)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).*)
(*we first prove : jsubres P Q j != det (family H (q-j)) (family Q (p-j))*)
intros j Hj.
transitivity (j_subres (H+B*Q) Q j);unfold j_subres.
myreplace2.
rewrite (nat_deg_comp euclid_relation).
myreplace2...
transitivity (det phi (nat_deg (H + B * Q) + nat_deg Q - j - 1) (subres_family (H + ((sum_of_Pol B)* Q)) Q j)).
myreplace2;rewrite <- (P_mon_sum B)...
unfold subres_family.
rewrite <- (nat_deg_comp euclid_relation).
rewrite  (@nat_deg_comp (H + (sum_of_Pol B)*Q) (H+B*Q)).
(*pourquoi ici replace marche pas???*)
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app (Xfamily (H +  (Psum  (fun i => scal (get_coef i B) (mon (N_of_nat i))*Q) (nat_deg B))) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))
).
myreplace2.
apply Padd_comp...
transitivity (
Psum (fun i : nat => (scal (get_coef i B) (mon (N_of_nat i))) * Q)
     (nat_deg B)).
rewrite <- (Psum_mul_r (nat_deg B) (fun i =>  scal (get_coef i B) (mon (N_of_nat i)))).
unfold sum_of_Pol...
apply Psum_ext ;intro n...
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1)
  (app
     (Xfamily
        (H +
         Psum (fun i : nat => scal (get_coef i B) (Q*(mon (N_of_nat i))))
           (nat_deg B)) (nat_deg Q - j - 1))
     (Xfamily Q (nat_deg (H + B * Q) - j - 1)))).
myreplace2.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
rewrite scal_Passoc.
unfold scal.
setoid_replace (mon (N_of_nat n) * Q) with (Q*mon (N_of_nat n));setoid ring.
transitivity (
det phi (nat_deg P + nat_deg Q - j - 1) (app
(Xfamily H (nat_deg Q - j - 1))
(Xfamily Q (nat_deg (H + B*Q) - j - 1)))).
apply (@det_family_sum
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg B) (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).
rewrite <- euclid_relation.
fold p q b h;rewrite b_is_p_minus_q.
omega_helper.
(* la*)
clear;omega.
clear - lt_h_q Hj;omega.
clear - lt_h_q Hj;omega.
rewrite det_skip_axiom;fold p q h;
try (repeat rewrite family_length).
auto with arith.
auto with arith.
rewrite <- euclid_relation;fold p.
rewrite <- scal_assoc.
apply Pmul_Rat_comp.
replace (p-j-1)%nat with ( (S (p -h-1)) + (h -j -1))%nat.
(* we cut the family of powers of Q into two :  the first triangular part,
of length q+h-j-1,giving the power on lcoef Q,
and the one remaining in the det*)
transitivity 
(pdet (p + q - j - 1)%nat
  (app (app (Xfamily_n_m (S (h-j-1)%nat) Q (p-h-1)) (Xfamily Q (h - j - 1)))
  (Xfamily H (q - j - 1)))).
myreplace_old.
apply (@Xfamily_app (p-h-1)%nat (h-j-1)%nat Q).
rewrite app_ass.
(* ok, now we develop the determinant *)
rewrite (det_trig phi 
(Xfamily_n_m (S (h - j - 1)) Q (p - h - 1))
((app (Xfamily Q (h - j - 1)) (Xfamily H (q - j - 1))))
(p + q - j - 1)
(Pc (lcoef Q))).
(* we prove that degree is low at the end of the list*)
Import PDet. (*???*)
rewrite family_n_m_length.
intros T HTIn index Hindex1 Hindex2.
replace (p - h - 1 + 1 + 1)%nat with (p-h+1)%nat;[idtac|omega_helper;clear - lt_h_q q_le_p;omega].
unfold phi.
case (le_gt_dec (p + q - j - 1 + 2) index);intro Hcase.
reflexivity.
destruct index.
reflexivity.
destruct index.
apply False_ind; apply (lt_irrefl 1 Hindex1).
destruct (phi.even_odd_dec (S (S index))).
replace (S (S index) -2)%nat with index;[idtac|auto with arith].
constructor.
apply (@get_coef_deg (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;
[idtac|clear - Hj;omega_helper;clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega_helper;omega].
unfold h.
apply family_deg;assumption.
clear e B  euclid_relation HTIn T b_is_p_minus_q Hindex1.
assert (Aux1 : index <= p-h-1);[clear - Hindex2;omega_helper;omega|clear Hindex2].
assert(Aux2 : p+q-j-1 > index);[clear - Hcase;omega_helper;omega|clear Hcase].
assert(Aux3 :  p  - j - index >  h - j).
omega.
clear - Aux3 lt_h_q;omega.
constructor.
assert (Rate: get_coef (p + q - j - 1 - (S (S index) - 2)) T == c0).
apply (@get_coef_deg  (q+h-j-1)%nat T) .
elim 
(PInapp_dec (Xfamily Q (h - j- 1)) (Xfamily H (q - j- 1)) T
  HTIn);intro TIn.
replace ( q + h - j - 1)%nat with (q + (h - j - 1))%nat;[idtac|clear - Hj;omega].
unfold q.
apply family_deg;try assumption.
replace ( q + h - j - 1)%nat with (h +(q-j-1))%nat;[idtac|clear - Hj lt_h_q;omega].
unfold h.
apply family_deg;assumption.
clear B o euclid_relation HTIn T b_is_p_minus_q Hindex1.
replace (S (S index) - 2)%nat with index;auto with arith.
assert (Aux1 : p + q - j -1 > index + q + h - j -1).
assert (test1 : p+q-j>1).
omega.
assert (test2 : index + q + h -j > 1).
omega.
assert (test3 : p+q> index + q +h).
clear -Hindex2 lt_h_q q_le_p;omega.
clear - test1 test2 test3;omega.
replace (S(S index)) with (index+2)%nat in Hcase. 
assert (test3:p+q-j-1 > index);[clear - Hcase;omega|clear Hcase].
apply (plus_gt_reg_l  (p+q-j-1-index)%nat (q+h-j-1)%nat index).
rewrite le_plus_minus_r.
omega_helper.
rewrite plus_assoc...
clear - Hj;omega.
clear - Hj;omega.
auto with arith.
ring.
rewrite Rate.
setoid ring.

(* we prove that the begining of the list is triangular*)
intros T TIn i k i_lt_k Hi.
unfold phi.
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
reflexivity.
assert (Goal_aux : 
get_coef (p + q - j - 1 - (S (S i) - 2))
(nth k (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T)
 == c0).
rewrite family_n_m_length in Hi.
assert (Aux1: k <= p - h - 1).
clear -Hi;omega.
rewrite nth_Xfamily...
apply get_coef_deg with (q+ (S (h - j - 1) + (p - h - 1) - k))%nat.
caseEq (P0test Q);intro Qtest.
rewrite (P0test_is_P0 Q Qtest).
rewrite times_X_n_P0.
simpl;try apply c0test_c0.
simpl;auto with arith.

rewrite times_X_n_deg;trivial.
replace (S (h-j-1))%nat with (h-j)%nat;[idtac|clear -Hj;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux2:p-h>=1).
clear - Aux1 i_lt_k;omega.
omega_helper.
apply omega1 with h;trivial.
clear - b0;omega.
clear - Aux1 Aux2;omega.
clear -Aux2;omega.
clear - q_le_p lt_h_q;omega.
clear - Aux2;omega.
clear - Aux1 Hj;omega.
clear - Aux2;omega.
destruct (phi.even_odd_dec (S (S i)));rewrite Goal_aux;constructor;setoid ring.
(* we prove that the coefs ont the begining of the diag are all Q*)
intros T TIn i lt_i.
unfold phi.
rewrite family_n_m_length in lt_i.
assert (Aux:i<p-h);[clear - lt_i q_le_p lt_h_q;omega|clear lt_i].
induction (le_gt_dec (p + q - j - 1 + 2) (S (S i))).
assert (Aux2 : p+q-j+1<= S (S i));[clear - a Hj lt_h_q q_le_p;omega|clear a].
apply False_ind;omega.
assert (Goal_aux :
(get_coef (p + q - j - 1 - (S (S i) - 2))
 (nth i (Xfamily_n_m (S (h - j - 1)) Q (p - h - 1)) T))
== lcoef Q).
rewrite  nth_Xfamily;[idtac|clear - Aux;omega].
replace (S (S i) -2)%nat with i;[idtac|clear;omega].
assert (Aux1:p-h>=1);[clear - Aux;omega|idtac].
replace (p + q - j - 1 - i)%nat with (q + (p-j-1-i))%nat.

replace ((S (h - j - 1) + (p - h - 1) - i))%nat with (p-j-1-i)%nat.

unfold q;apply times_X_n_lcoef.

replace (S (h - j -1))%nat with (h - j)%nat;[idtac|symmetry;apply omega2;assumption].
omega_helper.
replace (p-j-1)%nat with (p-1-j)%nat;trivial.
clear - q_le_p lt_h_q Hj;omega.
clear - q_le_p lt_h_q;omega.
assert (Aux2 : p -j -1>= 1);[clear - q_le_p lt_h_q Hj;omega|idtac].
omega_helper;try (clear - Aux1;omega).
clear -Aux2;omega.
clear - Aux2;omega.
clear - Hj lt_h_q q_le_p Aux;omega.
destruct ( phi.even_odd_dec (S (S i)));rewrite Goal_aux...
rewrite family_n_m_length.
rewrite Pscal_Pmul_l.
apply Pmul_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
rewrite Pc_pow.
constructor;reflexivity.
apply det_f_comp.
replace (p-h-1+1)%nat with (p-h)%nat;[idtac|omega].
intros n T.
unfold phi.
replace (p+q-j-1+2)%nat with (p+q-j+1)%nat;[idtac|omega].
replace (q + h - j - 1 + 2)%nat with (q + h - j +1)%nat;[idtac|omega].
destruct (le_gt_dec (p + q - j +1) (n + (p - h)));
destruct ( le_gt_dec (q + h - j +1)).
reflexivity.
apply False_ind;omega.
caseEq (n + (p - h))%nat;intro n0.
reflexivity.
intro G;destruct n0;try reflexivity.
caseEq n.
intro G1.
rewrite G1 in l;clear -l.
apply False_ind;omega.
intros n0 G2;caseEq (p-h)%nat;intro G3.
rewrite G3 in G.
replace (n+0)%nat with n in G;[idtac|omega];rewrite G in l.
clear - l lt_h_q Hj;apply False_ind;omega.
intro G4.
rewrite G4 in G;rewrite G2 in G;clear - G;apply False_ind;omega.
assert (Aux3:(p + q - j + 1=q+h-j+1+(p-h))%nat).
clear -q_le_p lt_h_q Hj;omega.
rewrite Aux3 in g.
clear -g l;apply False_ind;omega.
caseEq (n+(p-h))%nat.
intro G1;caseEq n.
intro G2;reflexivity.
intros n0 G2.
clear - G2 G1 lt_h_q q_le_p;apply False_ind;omega.
intros n0 G1.
caseEq n.
intro G2.
rewrite G2 in G1;simpl in G1.
rewrite G2 in g;simpl  in g. 
destruct n0.
assert ( Aux : Pc (get_coef (p + q - j - 1 - (S (S n0) - 2)) T) = P0).






(**** ici l'extensionalit'e de det:
il faudrait pouver un truc comme : forall ...,
(forall n P, f1 d1 n P != f2 d2 n P) -> forall l, det f1 d1 l = det f2 d2 l

*)





