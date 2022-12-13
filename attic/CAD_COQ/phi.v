(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)


(*Load Pol_ring.*)
Require Import Mylist.

Require Import Arith.
Require Import ZArith.
Require Import Even.
Require Import CAD_types.
Require Import Utils.
Require Import Pol_ring.


Add New Ring PolRing : PRth Abstract.
Add  New Ring CoefRing : cRth Abstract. 

Fixpoint get_coef (k:nat) (P:Pol) {struct k}: Coef:=
           match k with
                        O => match P with 
                                 Pc c => c
                                | PX _ _ c => c
                               end
                        |S k' => match P with
                                Pc _ => c0
                               | PX Q xH _ => get_coef k' Q
                               | PX Q i _ => get_coef k' (PX Q (i-1) c0) 
                         end
                end.

Lemma gcoef_P0 : forall k , get_coef k P0 == c0.
intro k; case k;simpl; intros;setoid ring.
Qed.

(*Axiom Cheat: forall A:Prop,A.*)

Lemma Pplus_xIPminus1_assoc: forall p q , (p + (xI q - 1) = p + xI q - 1)%positive.
intros.
 rewrite (Pplus_reg_l 1(p + (xI q - 1))(p + xI q - 1 )).
auto.
 rewrite Pplus_assoc.
rewrite (Pplus_comm 1).
rewrite <- Pplus_assoc.
rewrite Pplus_minus;auto.
rewrite Pplus_minus; trivial.
destruct p;simpl;auto with arith.
Qed.


Lemma Pplus_Pminus1_assoc: forall p q , (p + (xO q - 1) = p + xO q - 1)%positive.
intros.
 rewrite (Pplus_reg_l 1(p + (xO q - 1))(p + xO q - 1 )).
auto.
 rewrite Pplus_assoc.
rewrite (Pplus_comm 1).
rewrite <- Pplus_assoc.
rewrite Pplus_minus;auto.
rewrite Pplus_minus; trivial.
destruct p;simpl;auto with arith.
Qed.


Add Morphism get_coef  with signature (@eq nat) ==> Pol_Eq ==> ceq as gcoef_Morphism.
induction x.
intros P Q  Heq; inversion Heq; simpl;trivial.
rename P0 into P2;subst.
apply ceq_sym;trivial.
intros P Q  Heq; inversion Heq;try (rename P0 into P2;subst).
simpl; setoid ring.
simpl.
generalize (gcoef_P0 x);intro.
destruct i.
rewrite (IHx (PX P2 (xI i - 1) c0) (P0)).
constructor; [setoid ring|trivial].
apply ceq_sym;trivial.
rewrite (IHx (PX P2 (xO i - 1) c0) P0).
constructor; [setoid ring|trivial].
apply ceq_sym;trivial.
rewrite <-H1; apply IHx; apply PolEq_sym;trivial.
simpl.
generalize (gcoef_P0 x);intro.
destruct i.
rewrite (IHx (PX P2 (xI i - 1) c0) P0); trivial.
constructor; [setoid ring|trivial].
rewrite (IHx (PX P2 (xO i - 1) c0) P0); trivial.
constructor; [setoid ring|trivial].
rewrite <-H1; apply IHx; trivial.
simpl.
destruct i; apply IHx; rewrite H0;setoid ring.
simpl.
destruct j.
destruct i.
simpl Pplus at 1.
simpl.
apply IHx;rewrite H0.
rewrite PX_pq_pq;simpl.
rewrite Pplus_carry_spec.
rewrite xO_succ_permute.
rewrite xI_succ_xO.
generalize (Psucc (xO (i + j))); intro.
generalize (Ppred_succ p0); intro.
assert (Psucc p0 -1 = Ppred (Psucc p0))%positive.
destruct p0;simpl;auto with arith.
rewrite  H2;rewrite H1;setoid ring.
simpl.
apply IHx;rewrite H0.
rewrite PX_pq_pq;simpl.
generalize (i+j)%positive;intro.
assert (xO p0= xI p0 -1)%positive.
destruct p0;simpl;auto with arith.
rewrite H1;setoid ring.
simpl;apply IHx;rewrite H0.
rewrite PX_pq_pq;simpl.
generalize j;intro.
assert (xO(Psucc j0) =xI j0 + 1)%positive.
destruct j;simpl; auto with arith.
rewrite H1;auto  with arith.
assert (xI j0 = xI j0 +1 -1)%positive.
rewrite Pplus_comm; rewrite <-  Pplus_xIPminus1_assoc.
rewrite Pplus_minus;auto.
rewrite <- H2; setoid ring.
destruct i;simpl;apply IHx;rewrite H0.
rewrite PX_pq_pq.
cut ((xI i + (xO j - 1)= xI (i + j) - 1)%positive).
intro h;rewrite h;setoid ring.
rewrite  Pplus_Pminus1_assoc.
simpl;auto.
rewrite PX_pq_pq.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
rewrite PX_pq_pq.
rewrite Pplus_minus; auto;unfold Pminus;simpl; setoid ring.
destruct i;simpl;apply IHx;rewrite H0.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
unfold Pminus;simpl;setoid ring.
unfold Pminus;simpl;setoid ring.
simpl.
destruct i;destruct j; simpl; apply IHx; rewrite H0; try rewrite PX_pq_pq.
unfold Pminus;simpl.
rewrite Pplus_carry_spec.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
rewrite  Pplus_xIPminus1_assoc;simpl;setoid ring.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
unfold Pminus;simpl;setoid ring.
simpl.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
unfold Pminus;simpl;setoid ring.
Qed.

Lemma Pscal_Pc: forall a c, a!* Pc c != Pc (a**c).
intros.
unfold Pol_mul_Rat;case_c0_test a;simpl.
rewrite H0; constructor; setoid ring.
case_c0_test  (a -- c1); [assert (h:a ==c1);[ apply copp_eq;trivial|rewrite h]|idtac].
constructor; setoid ring.
constructor; setoid ring.
Qed.



Lemma PX_Pmul_rat_aux_Xchange : forall P a p c, (PX (Pol_mul_Rat_aux P a) p (c ** a) != Pol_mul_Rat_aux (PX P p c) a).
induction P;intros.
simpl.
case_c0_test (c**a).
rewrite H0; constructor; try setoid ring.
 constructor;setoid ring.
setoid ring.
simpl.
repeat rewrite mkPX_PX_c.
setoid ring.
Qed.

Lemma gcoef_Pmul_Rat_aux: forall n P a, get_coef n (Pol_mul_Rat_aux P a) == a** get_coef n P.
induction n.
induction P.
intros;simpl; setoid ring.
intros;simpl Pol_mul_Rat_aux;rewrite mkPX_PX_c; setoid ring.
simpl;setoid ring.
induction P.
intros;simpl;setoid ring.
simpl Pol_mul_Rat_aux.
intros;rewrite mkPX_PX_c.

simpl.
assert (c0 == c0**a).
setoid ring.
destruct p; try rewrite H.
rewrite (PX_Pmul_rat_aux_Xchange P a  (xI p - 1)).
rewrite IHn.
rewrite <- H;setoid ring.

rewrite (PX_Pmul_rat_aux_Xchange P a  (xO p - 1)).
rewrite IHn.
rewrite <- H;setoid ring.
apply IHn.
Qed.

Lemma gcoef_Pmul_Rat: forall n P a, get_coef n (Pol_mul_Rat P a) == a** get_coef n P.
intros; unfold Pol_mul_Rat; case_c0_test a.
rewrite H0;rewrite gcoef_P0; setoid ring.
case_c0_test  (a -- c1); [assert (h:a==c1);[ apply copp_eq;trivial|rewrite h]|idtac].
setoid ring.
apply gcoef_Pmul_Rat_aux.
Qed.

Lemma gcoef_last : forall n P p c c' , get_coef (S n) (PX P p c) == get_coef (S n) (PX P p c').
induction n.
intros;simpl.
destruct p; try setoid ring.
intros.
simpl.

destruct p.
case (xI p - 1)%positive;
intros; apply gcoef_Morphism; setoid ring.
case (xO p - 1)%positive;
intros; apply gcoef_Morphism; setoid ring.

case P; intros; try setoid ring.
Qed.




Lemma gcoef_Padd: forall  n P Q ,   get_coef n (P+Q) == get_coef n P ++ get_coef n Q.
induction n;intros.
destruct P; destruct Q; rename c0 into c2; try (simpl;setoid ring; fail).
simpl Pol_add;destruct (ZPminus p p0);rewrite mkPX_PX_c;simpl; setoid ring.

destruct P; destruct Q; rename c0 into c2; try (simpl;setoid ring; fail).
generalize (ZPminus_spec p p0); destruct (ZPminus p p0) ; intro h; rewrite h.
simpl Pol_add; rewrite ZPminus0;rewrite mkPX_PX_c;simpl.
destruct p0;try rewrite PX_Padd_r; apply IHn.
simpl Pol_add;rewrite ZPminuspos;rewrite mkPX_PX_c;simpl.
caseEq p0; intros.
caseEq p1;intros;simpl.
rewrite PX_Padd_r;rewrite PX_pq_pq;rewrite IHn.
apply cadd_ext;setoid ring.
apply gcoef_Morphism.
simpl.
cut ((xI (p3 + p2) = xO (Pplus_carry p2 p3) - 1)%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
unfold Pminus;simpl.
assert (Pdouble_minus_one (Pplus_carry p2  p3) = (xO p3 + xI p2)%positive).
rewrite Pplus_carry_spec.
rewrite Pdouble_minus_one_o_succ_eq_xI.
rewrite Pplus_comm;reflexivity.
rewrite H1;auto with arith.
rewrite PX_Padd_r;rewrite PX_pq_pq;rewrite IHn.
apply cadd_ext;setoid ring.
apply gcoef_Morphism.
simpl.
cut ((xO (p3 + p2) = xI(p2 + p3) - 1)%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
unfold Pminus;simpl; rewrite Pplus_comm;trivial.
rewrite PX_Padd_r;rewrite PX_pq_pq;rewrite IHn.
apply cadd_ext;setoid ring.
apply gcoef_Morphism.
simpl.
cut ((xI p2 = (xO (Psucc p2) - 1))%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
unfold Pminus;simpl.
rewrite  Pdouble_minus_one_o_succ_eq_xI; trivial.
caseEq p1;intros;simpl.
rewrite PX_Padd_r;rewrite PX_pq_pq;rewrite IHn.
apply cadd_ext;setoid ring.
apply gcoef_Morphism.
cut (((xI p3 + (xO p2 - 1)) = (xI (p2 + p3) - 1))%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
rewrite xI_succ_xO.
rewrite Pplus_one_succ_r.
rewrite <- Pplus_assoc.
rewrite Pplus_minus.
unfold Pminus;simpl; rewrite Pplus_comm;trivial.
simpl; trivial.
rewrite PX_Padd_r;rewrite PX_pq_pq;rewrite IHn.
apply cadd_ext;setoid ring.
apply gcoef_Morphism.
cut ((xO p3 + (xO p2 - 1) =(xO (p2 + p3) - 1))%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
assert ((xO p3 + xO p2  = xO(p2 + p3))%positive).
simpl; rewrite Pplus_comm;trivial.
rewrite <- H1.
apply Pplus_Pminus1_assoc.
rewrite PX_Padd_r;rewrite PX_pq_pq;rewrite IHn.
apply cadd_ext;setoid ring.
apply gcoef_Morphism.
cut (( 1 + (xO p2 - 1)=(xI p2 - 1) )%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
rewrite xI_succ_xO; rewrite Pplus_one_succ_l;rewrite Pplus_Pminus1_assoc; trivial.
caseEq p1;intros;simpl;
rewrite IHn;
apply cadd_ext;setoid ring;
apply gcoef_Morphism.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
unfold Pminus;simpl; setoid ring.
unfold Pminus;simpl; setoid ring.

rewrite Padd_sym;simpl Pol_add;rewrite ZPminuspos;rewrite mkPX_PX_c.
simpl.
caseEq p; intros;
caseEq p1;intros;simpl;
try rewrite PX_Padd_r;try rewrite PX_pq_pq;rewrite IHn;
rewrite cadd_sym;apply cadd_ext;setoid ring;
apply gcoef_Morphism.

simpl.
cut ((xI (p3 +  p2) = xO (Pplus_carry p2 p3) - 1)%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
unfold Pminus;simpl.
assert (Pdouble_minus_one (Pplus_carry p2  p3) = (xO p3 + xI p2)%positive).
rewrite Pplus_carry_spec.
rewrite Pdouble_minus_one_o_succ_eq_xI.
rewrite Pplus_comm;reflexivity.
rewrite H1;auto with arith.
simpl.
cut ((xO (p3 + p2) = xI(p2 + p3) - 1)%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
unfold Pminus;simpl; rewrite Pplus_comm;trivial.
simpl.
cut ((xI p2 = (xO (Psucc p2) - 1))%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
unfold Pminus;simpl.
rewrite  Pdouble_minus_one_o_succ_eq_xI; trivial.
cut (((xI p3 + (xO p2 - 1)) = (xI (p2 + p3) - 1))%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
rewrite xI_succ_xO.
rewrite Pplus_one_succ_r.
rewrite <- Pplus_assoc.
rewrite Pplus_minus.
unfold Pminus;simpl; rewrite Pplus_comm;trivial.
simpl; trivial.
cut ((xO p3 + (xO p2 - 1) =(xO (p2 + p3) - 1))%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
assert ((xO p3 + xO p2  = xO(p2 + p3))%positive).
simpl; rewrite Pplus_comm;trivial.
rewrite <- H1.
apply Pplus_Pminus1_assoc.
cut (( 1 + (xO p2 - 1)=(xI p2 - 1) )%positive).
intro h1; rewrite h1; apply Eq_PX_PX; try setoid ring; try setoid ring.
rewrite xI_succ_xO; rewrite Pplus_one_succ_l;rewrite Pplus_Pminus1_assoc; trivial.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
unfold Pminus;simpl; setoid ring.
unfold Pminus;simpl; setoid ring.
Qed.



(*
Definition  even_odd_dec : forall n, {even n} + {odd n}.
induction n.
auto with arith.
elim IHn; auto with arith.
Defined.
*)












Section ListAux.

Variable A: Set.
Theorem length_app:
 forall (l1 l2 : list A),  length (app l1  l2) = (length l1 + length l2)%nat.
intros l1; elim l1; simpl; auto.
Qed.

End ListAux.

Section Det.

(* Polynomial addition plus scalar *)
Notation  pol:= Pol.
Notation add :=Pol_add.
Definition scal :Coef -> pol -> pol.
intros c P; exact (Pol_mul_Rat P c).
Defined.






Section phi.
Variable d:nat.
(*Variable n:nat.
Hypothesis n_le_d:  (n<= d)%nat.*)


Definition phi (n:nat) := if (le_gt_dec  (d+2) n) then (fun P: Pol => Pc c0) else 
                          match n with 
                                         O => (fun P: Pol => Pc c0)
                                      | S O => (fun P:Pol => P)
                                      | _ =>  match even_odd_dec n with 
                                                left _ =>  (fun P : Pol => Pc (get_coef (d - (n-2)) P))
				     		|  right _  => (fun P : Pol => Pc (-- get_coef (d - (n-2)) P))
                                                 end
                               end.


Lemma phi_scal : forall n a P, phi n (a !* P) != a !* (phi n P).
intros;unfold phi;
case (le_gt_dec (d+2) n  ); intros;simpl.
rewrite Pscal_Pc; constructor;setoid ring.
case n;simpl.
rewrite Pscal_Pc; constructor;setoid ring.
intros;case n0.
setoid ring.
intros;simpl.
match goal with |- context [if ?X then _ else _ ] => case X end;
rewrite gcoef_Pmul_Rat;
rewrite Pscal_Pc;
constructor;setoid ring;simpl;ring.
Qed.

Lemma phi_Padd: forall n  P Q, phi n (P + Q) != phi n P + phi n Q.
intros;unfold phi;
case (le_gt_dec (d+2)n); intros.
simpl;constructor; setoid ring.
intros;case n;simpl.
constructor;setoid ring.
intros;case n0.
setoid ring.

intros;simpl.
match goal with |- context [if ?X then _ else _ ] => case X end;intros;
rewrite gcoef_Padd;
simpl;try apply PolEq_refl.
constructor;setoid ring.
Qed.

Add Morphism phi  with signature (@eq nat) ==> Pol_Eq ==> Pol_Eq  as phi_Morphism.
intros n P Q;unfold phi;case (le_gt_dec (d+2)n); intros.
setoid ring.

case n;simpl.
intros;setoid ring.
intros;case n0; trivial.
intros;match goal with |- context [if ?X then _ else _ ] => case X end;
intros;simpl;
rewrite H;setoid ring.
Qed.

(* Hypothesis phi_m: forall n a b c d, phi n (add (scal a  b) (scal c  d)) = a !* phi n b + c !* phi n d.*)
Lemma  phi_m: forall n a b c d, phi n (add (scal a  b) (scal c  d)) != a !* phi n b + c !* phi n d.
intros ; unfold scal.
rewrite phi_Padd.
repeat rewrite phi_scal.
setoid ring.
Qed.



(*

(* The function that takes coeff that behaves ok *)
Variable phi: nat -> pol -> pol.

Hypothesis phi_m: forall n a b c d, phi n (add (scal a  b) (scal c  d)) = a !* phi n b + c !* phi n d.
*)
End phi.

End Det.
