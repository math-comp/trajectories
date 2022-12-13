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
Require Import phi.


Add New Ring PolRing : PRth Abstract.
Add New Ring CoefRing : cRth Abstract. 

(* somme finie de polynomes *)
Fixpoint Psum(f:nat -> Pol)(N:nat){struct N}:Pol :=
   match N with
   |O => f O
   |S N => (Psum f N) + (f (S N))
   end.

(* la somme est la meme pour deux fonction ext egales*)
Lemma Psum_ext : forall N f g,(forall n, f n != g n) ->
(Psum f N) != (Psum g N). 
Proof.
induction N;intros;simpl;rewrite H.
reflexivity.
rewrite (IHN f g);[trivial|reflexivity].
Qed.


(* on peut sortir d'une somme le produit par un pol *)
Lemma Psum_mul_r : forall N f P,
(Psum f N) * P != Psum (fun i => (f i) *P) N.
Proof.
induction N;intros f P;simpl.
reflexivity.
rewrite <- IHN.
setoid ring.
Qed.

Lemma Psum_mul_l : forall N f P,
P*(Psum f N)  != Psum (fun i => P*(f i)) N.
Proof.
induction N;intros f P;simpl.
reflexivity.
rewrite <- IHN.
setoid ring.
Qed.



(* compat de Psum avec la somme de suites*)
Lemma Psum_add : forall n f g, 
Psum (fun i => f(i) + g(i)) n !=
(Psum (fun i =>  (f i)) n) + (Psum (fun i => (g i)) n).
Proof.
induction n;intros f g;simpl.
reflexivity.
rewrite IHn.
setoid ring.
Qed.

(* ajout d'un zero en tete d'une suite *)
Definition shift_1(f:nat -> Pol)(n:nat): Pol :=
match n with
|O => P0
|S n => f n
end.

(* la somme d'une shift1 f est la meme que celle de f, si on prend un terme de plus*)
Lemma shift1_sum : forall n f, Psum f n != Psum (shift_1 f) (S n).
Proof.
induction n;intros f;simpl.
setoid ring.
rewrite IHn.
simpl.
reflexivity.
Qed.

(* ajout de k zeros en tete d úne usuite *)
Fixpoint shift_k(f:nat ->Pol)(k:nat){struct k}:nat -> Pol :=
match k with
|O => f
|S k => shift_1 (shift_k f k)
end.

(* somme de shikt k, on prend k termees de plus *)
Lemma shiftk_sum : forall k f n, Psum f n != Psum (shift_k f k) (n +k).
Proof.
induction k;simpl;intros f n.
assert (H: (n+O)%nat =n);[auto with arith|rewrite H;clear H];reflexivity.
assert (H: (n+S k)%nat = S (n+k));[auto with arith|rewrite H;clear H].
transitivity (Psum (shift_k f k) (n + k));[apply IHk|apply shift1_sum].
Qed.

(* egalite des shifts sur des suites egales terme a terme*)
Lemma shift_1_ext: forall n f g,
(forall n, f n != g n) -> shift_1 f n != shift_1 g n.
Proof.
induction n;intros f g H;simpl.
reflexivity.
trivial.
Qed.


Lemma shift_k_ext:forall k n f g,
(forall n, f n != g n) -> shift_k f k n != shift_k g k n.
Proof.
induction k;intros n f g H;simpl.
trivial.
apply shift_1_ext.
intro n0;apply IHk.
trivial.
Qed.

(* on sort un produit par un pol*)
Lemma shift_1_mul : forall n f A,
shift_1 (fun i => (f i) *A) n != (shift_1 (fun i => (f i)) n)*A.
Proof.
destruct n;intros f A;simpl;setoid ring.
Qed.

Lemma shift_k_mul : forall k n f A,
shift_k (fun i => (f i) *A) k n != (shift_k (fun i => (f i)) k n)*A.
Proof.
induction k;intros n f A;simpl.
reflexivity.
transitivity 
(shift_1 (fun j => (shift_k (fun i : nat => f i) k j)*A) n).
apply shift_1_ext;intro n0.
apply IHk.
apply 
(shift_1_mul n (fun j : nat => shift_k (fun i : nat => f i) k j)).
Qed.


(* X^n*)
Definition mon(n:N):=
match n with
|N0 => P1
|Npos i => PX (Pc c1) i c0
end.






(* PX P i p != P*(X^i) + (Pc p) *)
Lemma PX_decompose : forall i P p, PX P i p != P*(mon (Npos i)) + (Pc p).
Proof.
induction i using Pind;intros P p;simpl.
Pcsimpl.
rewrite Pol_addC_spec.
rewrite mkPX_PX_c.
simpl.
constructor;setoid ring.
Pcsimpl.
rewrite Pol_addC_spec.
setoid ring.
rewrite mkPX_PX_c.
simpl.
constructor;setoid ring.
Qed.

(* test a zero pour non normalises*)
Fixpoint P0test(P:Pol):bool:=
match P with
|Pc c => czero_test c
|PX P i p =>
match (P0test P) with
|true => czero_test p
|false => false
end
end.

(*
Add Morphism P0test with signature Pol_Eq ==> (@eq bool) as P0test_comp.

*)


Lemma P0test_is_P0 : forall P, P0test P = true -> P != P0.
Proof.
induction P;simpl;intros;
constructor.
apply c0test_c;assumption.
case_eq (P0test P);intros;rewrite H0 in H.
apply c0test_c;assumption.
discriminate.
case_eq (P0test P);intros;rewrite H0 in H.
exact (IHP H0).
discriminate.
Qed.


(* degre pour non normalises, a valeur entiere*)
Fixpoint nat_deg(P:Pol):nat :=
match P with
|Pc c => O
|PX P i p =>
   match P0test P with
   |true => O
   |false => ((nat_deg P) + (nat_of_P i))%nat
   end
end.

(*
Add Morphism nat_deg with signature Pol_Eq ==> (@eq nat) as nat_deg_comp.
Proof.
*)

(* deg (PX P i p) = deg P + i*)
Lemma nat_deg_PX : forall P i p, 
P0test P =false -> nat_deg (PX P i p) = ((nat_deg P) + (nat_of_P i))%nat.
Proof.
intros P i p H.
simpl.
rewrite H.
reflexivity.
Qed.

Hint Rewrite mkPX_PX_c Pscal_Pmul_l PX_mn_c0 :Pol_norm.

(* les coefs de P*X sont ceux de P mais shiftes de 1*)
Lemma shift1_coef : forall P n,
shift_1 (fun i => scal (get_coef i P)  (mon (N_of_nat i))*X) n
!=
(fun i => scal (get_coef i (PX P 1 c0)) (mon (N_of_nat i))) n.
Proof.
induction P;intro n;simpl;unfold scal.
destruct n;simpl.
Pcsimpl.
Pcsimpl.
autorewrite with Pol_norm.
reflexivity.
setoid ring.
apply Pmul_comp.
reflexivity.
destruct n;simpl.
reflexivity.
rewrite PX_pq_pq.
rewrite Pplus_one_succ_r.
reflexivity.
destruct n;simpl;Pcsimpl.
autorewrite with Pol_norm.
reflexivity.
setoid ring;apply Pmul_comp.
reflexivity.
destruct n;simpl.
reflexivity.
rewrite PX_pq_pq.
rewrite Pplus_one_succ_r.
reflexivity.
Qed.


(* les coefs de PX P i c0 (=P*X^i) sont ceux de P mais shiftes i fois *)
Lemma shiftk_coef : forall i P n,
 (shift_k 
(fun n => scal (get_coef n P) (mon (N_of_nat n))*(mon (Npos i))) (nat_of_P i)) n
!=
(fun n => scal (get_coef n (PX P i c0)) (mon (N_of_nat n))) n.
Proof.
induction i using Pind;intros P n;unfold scal;simpl.
destruct n;simpl;Pcsimpl.
setoid ring.
rewrite mkPX_PX_c.
rewrite Pscal_Pmul_l.
rewrite PX_mn_c0.
reflexivity.
rewrite  Pscal_Pmul_l.
apply Pmul_comp.
constructor;reflexivity.
destruct n;simpl.
reflexivity.
rewrite PX_pq_pq.
replace (P_of_succ_nat n + 1)%positive with (Psucc (P_of_succ_nat n)).
constructor;reflexivity.
apply Pplus_one_succ_r.
transitivity (shift_k
  (fun n0 : nat =>
   (mkPX (get_coef n0 P !* mon (N_of_nat n0)) (Psucc i) c0)) (nat_of_P (Psucc i)) n).
apply shift_k_ext.
intro n0.
Pcsimpl.
setoid ring;reflexivity.

replace (nat_of_P (Psucc i)) with (S (nat_of_P i)).
simpl.
transitivity
(shift_1
(shift_k
     (fun n0 : nat =>
       (scal (get_coef n0 P) (mon (N_of_nat n0))) * (mon (Npos i)) * X)
     (nat_of_P i)) n).
apply shift_1_ext;intro n0.
apply shift_k_ext;intro n1.
unfold scal.
autorewrite with Pol_norm.
reflexivity.
rewrite <- Pmul_assoc.
rewrite <- Pmul_assoc.
apply Pmul_comp.
reflexivity.
rewrite Pplus_one_succ_r.
rewrite PX_decompose.
setoid ring.
rewrite <- Pmul_assoc.
apply Pmul_comp.
reflexivity.
unfold mon.
rewrite Pplus_comm.
rewrite <- PX_pq_pq.
repeat rewrite PX_decompose.
setoid ring.
transitivity
(shift_1 (fun m =>
  (shift_k
     (fun n0 : nat =>
      scal (get_coef n0 P) (mon (N_of_nat n0)) * mon (Npos i))
     (nat_of_P i) m)*X)  n).
apply shift_1_ext;intro n0.
apply (shift_k_mul (nat_of_P i) n0 (fun n1 : nat => scal (get_coef n1 P) (mon (N_of_nat n1)) * mon (Npos i)) X).
transitivity
(shift_1
  (fun m : nat =>
   scal (get_coef m (PX P i c0)) (mon (N_of_nat m)) * X) n).
apply shift_1_ext;intro n0.
rewrite IHi.
reflexivity.
rewrite shift1_coef.
unfold scal.
rewrite Pplus_one_succ_r.
rewrite <- PX_pq_pq.
reflexivity.
rewrite nat_of_P_succ_morphism;reflexivity.
Qed.


(* la somme des coefs*monomes pour un pol *)
Definition sum_of_Pol(P:Pol) :=
 Psum 
(fun i => scal (get_coef i P) (mon (N_of_nat i))) (nat_deg P).


(* forall n, Pc = sum (coef i Pc c), i =0...n*)
Lemma P_mon_sum_Pc_gen : forall c, forall n,
 Pc c != Psum (fun i => scal (get_coef i (Pc c)) (mon (N_of_nat i))) n.
Proof.
intro c;induction n;simpl.
unfold scal;Pcsimpl.
unfold scal;Pcsimpl.
setoid ring.
assumption.
Qed.

(* forall P, P = sum (coef i P) i =0...deg P *)
Theorem P_mon_sum : forall P, P!=sum_of_Pol P.
Proof.
induction P;unfold sum_of_Pol;simpl.
unfold scal;Pcsimpl.

case_eq (P0test P);intros.
pose (H1:=P0test_is_P0 P H).
simpl.
rewrite H1.
unfold scal;Pcsimpl;constructor;reflexivity.


transitivity  (P*(mon (Npos p)) + (Pc c)).
apply PX_decompose.
transitivity ((sum_of_Pol P)*(mon (Npos p)) + (Pc c)).
apply Padd_comp;try reflexivity.
apply Pmul_comp;try reflexivity.
apply IHP.
unfold sum_of_Pol.
rewrite Psum_mul_r.
transitivity (Psum (shift_k 
(fun i : nat => scal (get_coef i P) (mon (N_of_nat i)) * mon (Npos p))
(nat_of_P p))
((nat_deg P)+(nat_of_P p)) + Pc c).
apply Padd_comp.
2:reflexivity.
apply shiftk_sum.
transitivity ((sum_of_Pol (PX P p c0)) + (Pc c));unfold sum_of_Pol.
apply Padd_comp.
2:reflexivity.
rewrite <- (nat_deg_PX P p c0 H).
generalize (nat_deg (PX P p c0)).
intro n.
apply Psum_ext.
apply shiftk_coef. 
assert (G: Pc c != Psum (fun i :nat =>scal (get_coef i (Pc c)) (mon (N_of_nat i)))
  (nat_deg (PX P p c0))).
apply P_mon_sum_Pc_gen.
rewrite G;clear G.
rewrite <- (Psum_add(nat_deg (PX P p c0))
 (fun i : nat => scal (get_coef i (PX P p c0)) (mon (N_of_nat i)))
(fun i : nat => scal (get_coef i (Pc c)) (mon (N_of_nat i)))).
replace (nat_deg P + nat_of_P p)%nat with (nat_deg (PX P p c0)).
apply Psum_ext;intro n.
assert (PXPc : (PX P p c) != ((PX P p c0) + Pc c)).
simpl;constructor;[setoid ring|reflexivity].
unfold scal;rewrite PXPc;clear PXPc.
rewrite gcoef_Padd.
repeat rewrite Pscal_Pmul_l.
assert (G: Pc (get_coef n (PX P p c0) ++ get_coef n (Pc c))
!= Pc (get_coef n (PX P p c0)) + Pc (get_coef n (Pc c)));
[simpl;reflexivity|rewrite G;clear G].
setoid ring.
apply nat_deg_PX;assumption.
Qed.
