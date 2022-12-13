Require Import Wellfounded.
Require Import Setoid.
Require Import ZArith.
Require Import Omega.
Require Import CAD_types.
Require Import Utils.
Require Import NArith.
Require Import NArithRing.
Require Import Zwf.
Require Import QArith.
Require Import Qring.
Require Import Qring.
Require Import Pol_ring2.
Require Import Recdef.
Require Import Coef_props.
Import Qnorm.

Theorem Npos_plus : forall x y, (Npos (x + y) = Npos x + Npos y)%N.
intros; simpl; auto.
Qed.

Lemma Npos_xI_expand :
  forall p, Npos (xI p) = (1 + (Npos p + Npos p))%N.
intros; simpl; rewrite Pplus_diag; auto.
Qed.

Lemma Npos_xO_expand :
  forall p, Npos (xO p) = (Npos p + Npos p)%N.
intros; simpl; rewrite Pplus_diag; auto.
Qed.

Fixpoint Coef_of_positive (p:positive) : Coef :=
  match p with
    1%positive => c1
  | xO p' => Coef_of_positive p' ++ Coef_of_positive p'
  | xI p' => c1 ++ (Coef_of_positive p' ++ Coef_of_positive p')
  end.

Definition Coef_of_N (n:N) :=
  match n with 0%N => c0 | Npos p => Coef_of_positive p end.

Lemma Coef_of_N_0 : Coef_of_N 0 == c0.
apply ceq_refl.
Qed.

Lemma Coef_of_N_S : forall n, Coef_of_N (1 + n) == c1 ++ Coef_of_N n.
intros n; case n.
setoid_rewrite Coef_of_N_0.
unfold Coef_of_N.
replace (1+0)%N with 1%N.
setoid_rewrite cadd_0_r.
apply ceq_refl.
ring.
intros p; induction p.
unfold Nplus.
simpl (1+xI p)%positive.
replace (Coef_of_N (Npos (xO (Psucc p)))) with
        ((Coef_of_N (Npos (Psucc p))) ++ Coef_of_N (Npos (Psucc p))).
rewrite Pplus_one_succ_l.
setoid_rewrite IHp.
replace (Coef_of_N (Npos (xI p))) with 
     (c1++ (Coef_of_N (Npos p)++Coef_of_N (Npos p))).
setoid ring.
reflexivity.
reflexivity.
simpl (1+Npos(xO p))%N.
apply ceq_refl.
apply ceq_refl.
Qed.

Inductive NS : N -> N -> Prop :=
   NSc : forall n, NS n (1+n).

Lemma NS_wf : well_founded NS.
apply wf_incl with (R2 := ltof N nat_of_N).
unfold inclusion.
intros x y H; inversion H.
unfold ltof.
case x.
exact (le_n 1).
intros p; induction p.
simpl.
rewrite nat_of_P_xI.
rewrite nat_of_P_xO.
rewrite nat_of_P_succ_morphism.
omega.
simpl.
rewrite nat_of_P_xO.
rewrite nat_of_P_xI.
omega.
compute.
omega.
apply well_founded_ltof.
Qed.

Lemma N_eq_dec : forall x y:N, {x=y}+{x<>y}.
intros x y.
assert (other_direction : x = y -> Ncompare x y = Eq).
intros Heq; rewrite Heq; apply Ncompare_refl.
generalize (Ncompare_Eq_eq x y) other_direction.
case (Ncompare x y).
left; auto.
intros _ Hd ; right; intros Habs; assert (Habs' := Hd Habs); discriminate.
intros _ Hd ; right; intros Habs; assert (Habs' := Hd Habs); discriminate.
Qed.

Functional Scheme Npred_ind := Induction for Npred Sort Prop.

Lemma Npred_correct : forall p p', p' = Npos p -> p' = (1 + Npred p')%N.

intros p p'; functional induction (Npred p').
intros; discriminate.
intros; reflexivity.
unfold Nplus.
rewrite <- Pplus_one_succ_l.
elim (Psucc_pred (xO _x)).
intros; discriminate.
intros H; rewrite H; reflexivity.
reflexivity.
Qed.

Lemma succ_Npred :
  forall p n, Npred n = Npos p -> n = (Npos p + 1)%N.
intros p n; functional induction (Npred n).
intros; discriminate.
simpl.
replace (Npos (p + 1)) with (1 + Npos p)%N.
intros Heq; rewrite <- Heq; auto.
rewrite Pplus_comm; auto.
intros Heq; rewrite <- Heq.
rewrite Nplus_comm.
clear Heq.
simpl.
apply f_equal with (f:= Npos).
case _x.
simpl; auto.
simpl.
intros; rewrite Psucc_o_double_minus_one_eq_xO; auto.
simpl; auto.
intros; discriminate.
Qed.

Function diff_cpow_pol (x:Coef) (n:N) {wf NS n} : Pol :=
   match Npred n with
     0%N => P0
   | _ =>  (Pc (Coef_of_N (Npred n)** cpow x (Npred (Npred n))) +
        Pc x * diff_cpow_pol x (Npred n) + X * diff_cpow_pol x (Npred n))
   end.
intros _ n p Heq.
rewrite (Npred_correct (1+p)%positive n).
rewrite Heq; constructor.
rewrite (succ_Npred _ _ Heq).
rewrite Nplus_comm; auto.
apply NS_wf.
Qed.

Theorem cpow_pos : forall (c:Coef)(n:N), cle c0 c -> cle c0 (cpow c n).
intros c n H0; case n.
setoid_rewrite cpow_0.
exact c0_cle_c1.
induction p.
rewrite Npos_xI_expand.
repeat setoid_rewrite cpow_plus.
repeat apply cle_0_mult; try exact IHp.
setoid_rewrite cpow_1; exact H0.
rewrite Npos_xO_expand.
repeat setoid_rewrite cpow_plus.
repeat apply cle_0_mult; try exact IHp.
setoid_rewrite cpow_1; exact H0.
Qed.

Lemma cpow_le_compat_r :
  forall x p, c1 <= x -> x <= cpow x (Npos p).
intros x p Hx; induction p.
rewrite Npos_xI_expand.
repeat setoid_rewrite cpow_plus.
setoid_rewrite cpow_1.
setoid_rewrite (cmul_sym x).
pose (u:= cpow x (Npos p) ** cpow x (Npos p) ** x); fold u.
setoid_rewrite <- (cmul_1_l x).
unfold u.
assert (c1 <= cpow x (Npos p)) by (apply cle_trans with x; auto).
apply cmul_le_compat_r.
apply cle_trans with (c1**cpow x (Npos p)).
setoid_rewrite cmul_1_l; auto.
apply cmul_le_compat_r.
auto.
apply cle_trans with c1; auto.
apply c0_cle_c1.
apply cle_trans with c1; auto.
apply c0_cle_c1.
rewrite Npos_xO_expand.
setoid_rewrite cpow_plus.
pose (u:= cpow x (Npos p) ** cpow x (Npos p)); fold u.
setoid_rewrite <- (cmul_1_l x).
unfold u.
apply cle_trans with (c1**cpow x (Npos p)).
repeat setoid_rewrite cmul_1_l.
assumption.
apply cmul_le_compat_r.
apply cle_trans with x; auto.
apply cle_trans with c1.
apply c0_cle_c1.
apply cle_trans with x; auto.
setoid_rewrite cpow_1;apply cle_refl.
Qed.

Lemma cpow_le_compat_l :
   forall x y n, cle c0 x -> cle x y -> cle (cpow x n) (cpow y n).
intros x y n Hx Hy; case n.
repeat setoid_rewrite cpow_0; apply cle_refl.
assert (c0 <= y) by (apply cle_trans with x; auto).
intros p.
induction p.
assert (c0 <= cpow x (Npos p)) by (apply cpow_pos; auto).
rewrite Npos_xI_expand.
repeat setoid_rewrite cpow_plus.
repeat setoid_rewrite cpow_1.
apply cle_trans with (y ** (cpow x (Npos p) ** cpow x (Npos p))).
apply cmul_le_compat_r.
assumption.
apply cmul_le_0; auto.
repeat setoid_rewrite (cmul_sym y).
apply cmul_le_compat_r.
apply cle_trans with (cpow x (Npos p) **cpow y (Npos p)).
setoid_rewrite (cmul_sym (cpow x (Npos p))(cpow y (Npos p))).
apply cmul_le_compat_r; assumption.
assert (c0 <= cpow y (Npos p)) by (apply cpow_pos; auto).
apply cmul_le_compat_r; auto.
auto.

assert (c0 <= cpow x (Npos p)) by (apply cpow_pos; auto).
rewrite Npos_xO_expand.
repeat setoid_rewrite cpow_plus.
apply cle_trans with (cpow x (Npos p) ** cpow y (Npos p)).
setoid_rewrite (cmul_sym (cpow x (Npos p))(cpow y (Npos p))).
apply cmul_le_compat_r; auto.
apply cmul_le_compat_r; auto.
apply cpow_pos; auto.

repeat setoid_rewrite cpow_1; auto.
Qed.

Theorem cpow_lt_0_compat_l: forall x n, c0 < x -> c0 < cpow x n.
intros x n Hx; case n.
setoid_rewrite cpow_0.
apply clt_decompose.
apply c0_diff_c1.
apply c0_cle_c1.
induction p.
rewrite Npos_xI_expand.
repeat setoid_rewrite cpow_plus.
setoid_rewrite cpow_1.
apply cmul_lt_0.
assumption.
apply cmul_lt_0; assumption.
rewrite Npos_xO_expand.
setoid_rewrite cpow_plus.
apply cmul_lt_0; assumption.
setoid_rewrite cpow_1; assumption.
Qed.


Theorem clt_0_inv_pow : forall x n, c0 < x -> c0 < c1/cpow x n.
intros.
apply cdiv_lt_0_compat_l.
apply cpow_lt_0_compat_l; assumption.
apply c0_clt_c1.
Qed.

Hint Resolve c0test_c PolEq_refl ceq_refl.
Hint Immediate ceq_sym PolEq_sym.

Opaque Coef_record.Czero_test Coef_record.C0 Coef_record.Ceq Coef_record.C1
       Coef_record.Cadd Coef_record.Csub Coef_record.Cmul Coef_record.Cpow.

(* First prove that polynomials with no alternations and at least one
   positive coefficient are increasing and have a limit to infinity at
   infinity. *)

Fixpoint least_non_zero_coeff (p:Pol) : Coef :=
  match p with
    Pc c => c
  | PX P i c => if czero_test c then least_non_zero_coeff P else c
  end.

Inductive no_alternation : Pol -> Set :=
  no_alternation_c1 : forall c (q:Pol), q != Pc c -> no_alternation q
| no_alternation_c2 :
    forall n a P1 P2,
      no_alternation P2 -> ~a == c0 ->
      c0 <= a**(least_non_zero_coeff P2) ->
      P1 != (X^n *(Pc a+X*P2))%Pol -> no_alternation P1.


Inductive one_alternation : Pol -> Set :=
  one_alternation_here :
    forall P a (n:N) P1,
      P != (X^n *(Pc a + X * P1))%Pol ->
      a ** least_non_zero_coeff P1 < c0 -> no_alternation P1 ->
      one_alternation P
| one_alternation_step :
    forall P a n P1,
      P != (X^n * (Pc a + X * P1))%Pol ->
      one_alternation P1 -> c0 < a ** least_non_zero_coeff P1 ->
      one_alternation P.

Theorem least_non_zero_coeff_0 :
   forall P, least_non_zero_coeff P == c0 -> P != P0.
induction P; simpl.
intros; constructor;auto.
caseEq (czero_test c).
intros Heqc Heq.
constructor.
auto.
auto.

intros Heq1 Heq2; elim (ceq_propF c c0); auto.
rewrite <- c0test_ceqb; trivial.
Qed.

Lemma least_non_zero_coeff_P0_aux :
  forall P P', P !=P' -> P0 = P' -> least_non_zero_coeff P == c0.
intros P P' H; induction H.
simpl; intros Heq; injection Heq.
intros Heq'; rewrite Heq'; auto.
intros Heq; discriminate.
intros Heq; injection Heq; intros Heq'.
simpl.
caseEq (czero_test p).
simpl in * ; auto.
intros Hcz; elim (ceq_propF p c0).
rewrite <- c0test_ceqb; auto.
rewrite Heq'; auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma c0test_morph :
  forall p q, p == q -> czero_test p = czero_test q.
intros p q H; caseEq (czero_test p).
intros Hp0; assert (ceq p 0).
auto.
caseEq (czero_test q); auto.
intros Hqn0; elim (ceq_propF q 0).
rewrite <- c0test_ceqb; auto.
apply ceq_trans with p; auto.
intros Hpn0; caseEq (czero_test q); auto.
intros Hq0; elim (ceq_propF p 0).
rewrite <- c0test_ceqb; auto.
apply ceq_trans with q; auto.
Qed.

Theorem czero_test_0 : czero_test c0 = true.
rewrite c0test_ceqb.
caseEq (ceqb c0 c0); trivial.
intros habs; elim (ceq_propF c0 c0); auto.
Qed.

Add Morphism least_non_zero_coeff with signature Pol_Eq ==> ceq
   as lnz_morphism.
intros x1 x2 H; induction H; simpl;intros;auto.
caseEq (czero_test q);auto.
intros H';
apply ceq_trans with q; auto.
apply ceq_trans with 0; auto.
caseEq (czero_test p);auto.
intros H';apply ceq_trans with 0; auto.
apply ceq_trans with p; auto.
apply ceq_sym; auto.

rewrite (c0test_morph p q); auto.
case (czero_test q); auto.
simpl in IHPol_Eq.
rewrite (c0test_morph p q); auto.
case (czero_test q); auto.
apply ceq_sym; auto.
simpl in IHPol_Eq.
rewrite czero_test_0 in IHPol_Eq.
rewrite (c0test_morph p q); auto.
case (czero_test q); auto.
Qed.

Opaque cle.

Lemma PX_interp :
   forall P n c, PX P n c != (X^(Npos n)*P+Pc c)%Pol.
intros P n c.
rewrite <- (mkPX_PX P n c c).
setoid ring.
simpl (X^(Npos n))%Pol.

rewrite Pmul_PpowXP.
unfold Pol_add, Pol_addC.
apply mkPX_PX.
setoid ring.
Qed.

Lemma Pol_mul_Rat_cst : forall a b, a !* Pc b != Pc (a**b).
intros a b; unfold Pol_mul_Rat.
caseEq (czero_test a).
intros Hatest; setoid_replace a with c0.
setoid_rewrite cmul_0_l; auto.
auto.
intros Hatest; caseEq (czero_test (a--c1)).
intros Hatest1; assert (a**b==b).
setoid_replace a with ((a --c1) ++ c1).
setoid_rewrite (c0test_c (a--c1)); auto.
setoid ring.
setoid ring.
setoid_rewrite H; auto.
simpl.
intros _; setoid_rewrite cmul_sym; auto.
Qed.

Add Morphism Pol_eval with signature Pol_Eq ==> ceq ==> ceq as Pol_eval_morphism.
intros x1 x2 H; induction H.
simpl; intros; assumption.
simpl; intros x1 x2 Heq.
setoid_rewrite H.
setoid_rewrite (IHPol_Eq x2 x2).
apply ceq_refl.
simpl; setoid ring. 
simpl; intros x1 x2 Heq; setoid_rewrite H; setoid_rewrite (IHPol_Eq x1 x1).
apply ceq_refl.
simpl; setoid ring.
simpl; intros x1 x2 Heq;setoid_rewrite H; setoid_rewrite (IHPol_Eq x1 x2).
assumption.
setoid_rewrite Heq.
apply ceq_refl.
simpl; intros x1 x2 heq; setoid_rewrite H; setoid_rewrite (IHPol_Eq x1 x2).
assumption.
simpl.
rewrite Npos_plus; setoid_rewrite cpow_plus.
setoid_rewrite heq; setoid ring.
simpl; intros x1 x2 heq; setoid_rewrite H; setoid_rewrite (IHPol_Eq x2 x1).
auto.
rewrite Npos_plus; setoid_rewrite cpow_plus.
simpl.
setoid_rewrite <- heq; setoid ring.
Qed.

Theorem Pol_addX_eval : forall (x:Coef) f P',
   (forall (Q:Pol1 Coef), Pol_eval (f Q) x == Pol_eval Q x ++ Pol_eval P' x) ->
   forall P i,
   ceq (Pol_eval (Pol_addX f P' i P) x)(
   Pol_eval P x++cpow x (Npos i)**Pol_eval P' x).
intros x f P' Hf P; induction P; intros i.
simpl; setoid ring.
simpl.
generalize (ZPminus_spec p i); case (ZPminus p i).
intros Hpi; rewrite Hpi.
setoid_rewrite mkPX_PX_c.
simpl.
setoid_rewrite Hf.
setoid ring.
intros k Hpik; rewrite Hpik.
replace (Npos (i + k)) with (Npos i + Npos k)%N.
setoid_rewrite cpow_plus.
setoid_rewrite mkPX_PX_c.
simpl.
setoid_rewrite Hf.
simpl.
setoid ring.
simpl; auto.
intros k Hpik; rewrite Hpik.
rewrite mkPX_PX_c.
simpl.
setoid_rewrite IHP.
replace (Npos (p+k))with (Npos p + Npos k)%N.
setoid_rewrite cpow_plus.
setoid ring.
simpl; auto.
Qed.

Lemma Pol_eval_mult_c :
  forall c P x, Pol_eval (Pc c * P) x == c ** Pol_eval P x.
intros c P x; induction P as [c' | P IHP i c'].
simpl; setoid_rewrite Pol_mul_Rat_cst; simpl; setoid ring.
simpl; setoid_rewrite mkPX_PX_c. 
setoid_rewrite Pol_mul_Rat_cst; simpl.
setoid_rewrite IHP; setoid ring.
Qed.

Lemma Pol_eval_plus :
  forall P' P x, Pol_eval (P + P')%Pol x == Pol_eval P x ++ Pol_eval P' x.
intros P'; induction P' as [c' | P' IHP' p' c'].
intros P; induction P.
simpl; auto.
intros; simpl; setoid ring.
intros P x; induction P.
simpl; auto.
simpl (Pc c + PX P' p' c').
simpl; setoid ring.
simpl.
generalize (ZPminus_spec p p').
caseEq (ZPminus p p').
intros Hm Hpp'.
simpl.
rewrite Hpp'.
setoid_rewrite mkPX_PX_c.
simpl.
setoid_rewrite IHP'.
setoid ring.
intros k Hm Hpk.
setoid_rewrite mkPX_PX_c.
simpl.
setoid_rewrite IHP'.
simpl.
rewrite Hpk; replace (Npos (p'+k)) with (Npos p'+Npos k)%N.
setoid_rewrite cpow_plus.
setoid ring.
simpl; auto.
intros k Hm Hpk; rewrite Hpk.
replace (Npos (p + k)) with (Npos p + Npos k)%N.
setoid_rewrite cpow_plus.
simpl.
setoid_rewrite mkPX_PX_c.
simpl.
setoid_rewrite Pol_addX_eval.
intros; apply IHP'.
setoid ring.
simpl; auto.
Qed.

Lemma Pol_eval_mult :
  forall P P' x, Pol_eval (P * P')%Pol x == (Pol_eval P x ** Pol_eval P' x).
intros P P' x; induction P' as [c' | P' IHP' i c'].
setoid_rewrite Pmul_sym.
setoid_rewrite Pol_eval_mult_c; simpl; setoid ring.
simpl.
setoid_rewrite mkPX_PX_c.
setoid_rewrite Pol_eval_plus.
simpl.
setoid_rewrite IHP'.
setoid_rewrite Pscal_Pmul_l.
setoid_rewrite Pol_eval_mult_c; simpl; setoid ring.
Qed.

Lemma Pol_eval_pow :
  forall P n x, Pol_eval (P^n)%Pol x == cpow (Pol_eval P x) n.
intros P n x; case n.
simpl; setoid_rewrite cpow_0; auto.
intros p; induction p.
simpl; repeat setoid_rewrite Pol_eval_mult.
rewrite Npos_xI_expand.
fold (Pol_pow P (Npos p)).
setoid_rewrite IHp.
repeat setoid_rewrite cpow_plus.
setoid_rewrite cpow_1.
setoid ring.
rewrite Npos_xO_expand.
setoid_rewrite Ppow_plus; setoid_rewrite Pol_eval_mult.
setoid_rewrite IHp.
setoid_rewrite cpow_plus.
auto.
auto.
Qed.

Lemma Pol_eval_X : forall x, ceq (Pol_eval X x) x.
intros; simpl.
setoid_rewrite cpow_1.
setoid ring.
Qed.

Lemma Pol_eval_c : forall c x, Pol_eval (Pc c) x = c.
auto.
Qed.

Lemma least_non_zero_P1 :
  forall P, ~P != P0 -> ~Qeq (least_non_zero_coeff P) 0.
intros P Heq Hceq; elim Heq; apply least_non_zero_coeff_0; auto.
Qed.

Lemma Qplus_0_r : forall x:Q, (x+0 == x)%Q.
intros; ring.
Qed.

Lemma Qmult_1_r : forall x:Q, (x*1 == x)%Q.
intros; ring.
Qed.


Add Morphism (@Pc Coef) with signature ceq ==> Pol_Eq as Pc_morphism.
intros; constructor; auto.
Qed.

Theorem X_mul_convert_pow : forall p, X * p != X^1*p.
intros; simpl;setoid ring.
Qed.

Lemma least_non_zero_P2 :
  forall P, exists n:N, exists P' : Pol,
   P != (X^n*(Pc(least_non_zero_coeff P)+X*P'))%Pol.
intros P; induction P.
exists 0%N; exists P0.

simpl.
unfold Pol_mul_Rat; rewrite czero_test_0.
setoid ring.

destruct IHP as [n [P' Heq]].
simpl least_non_zero_coeff.
caseEq (czero_test c).
intros Heqt; exists (n+Npos p)%N; exists P'.
rewrite (PX_interp P p c).
setoid_rewrite (c0test_c c); trivial.
match goal with |- _ != ?x => pose (u:= x); fold u end.
setoid_rewrite Heq; unfold u; rewrite Ppow_plus.
setoid ring.

intros _; exists 0%N; exists (X^(Npred (Npos p))*P)%Pol.
simpl (X^0)%Pol.
rewrite (PX_interp P p c).
rewrite X_mul_convert_pow.
setoid_replace (X^Npos p)%Pol with (X^1*X^Npred (Npos p))%Pol.
setoid ring.
rewrite <- Ppow_plus.
rewrite <- (Npred_correct p); auto.
Qed.

Theorem least_non_zero_P3 : least_non_zero_coeff P0 == c0.
apply ceq_refl.
Qed.

Theorem Pmul_0_l : forall x, P0 * x != P0.
intros; setoid ring.
Qed.

Theorem Pc_eq_X_pow_mul_decompose :
  forall Q a b n, Pc a != X^n*(Pc b + X*Q) -> a==b /\ (n = 0%N\/b==c0) /\ 
              Q != P0.
intros Q.
induction Q; intros a b n.
caseEq n.
intros Hn0.
subst n.
caseEq (czero_test c).
intros Hc0; setoid_rewrite (c0test_c c);auto.
match goal with |- Pc a != ?X -> _ =>
  setoid_replace X with (Pc b);[intros id; inversion id; auto | setoid ring]
end.
simpl (X^0); setoid ring.
intros Hcn0.
match goal with |- Pc a != ?X ->  _ =>
  setoid_replace X with (PX (Pc c) 1 b);[intros id; inversion id | setoid ring]
end.
assert (H':Pc c != P0);[auto|inversion H'].
rewrite c0test_ceqb in Hcn0.
elim (ceq_propF c c0); auto.
setoid_rewrite (PX_interp (Pc c)).
 simpl Pol_pow; setoid ring.
intros p Hn.

match goal with |- Pc a != ?v -> _ =>
    setoid_replace v with (PX (Pc b +X*Pc c) p c0)%Pol
end.
intros Heq; inversion Heq.
assert (H' : Pc b+ c!*X != P0) by auto.
unfold Pol_mul_Rat in H'.
caseEq (czero_test c); intros Hctest; rewrite Hctest in H'; simpl in H'.
inversion H'; assert (Hb: b++c0==c0) by assumption.
setoid_rewrite cadd_0_r in Hb.
setoid_rewrite Hb.
assert (Hc : c == c0) by auto.
setoid_rewrite Hc; auto.
caseEq (czero_test (c--c1)).
intros Hctest1; rewrite Hctest1 in H'.
setoid_replace (Pc b + X) with (PX P1 1 b) in H'.
inversion H'; elim P0_diff_P1;auto.
setoid_rewrite (PX_interp P1 1 b); simpl Pol_pow.
 setoid ring.
intros Hctest1; rewrite Hctest1 in H'.
assert (Hctest' : czero_test (c1**c)=false).
caseEq (czero_test (c1**c)); intros Hctest2; auto.
elim (ceq_propF c 0).
rewrite <- c0test_ceqb; auto.
setoid_rewrite <- (c0test_c (c1**c)); auto.
setoid ring.
rewrite Hctest' in H'.
simpl in H'.
inversion H'; assert (Habsc : Pc (c1**c) != Pol_ring2.P0) by assumption.
inversion Habsc.
elim (ceq_propF (c1**c) c0); auto; rewrite <- c0test_ceqb;auto.
setoid_rewrite (PX_interp (Pc b + X *Pc c)); setoid ring.
caseEq n.
intros Hn0; simpl (X^0);rewrite Pmul_1_l.
simpl.
rewrite Pscal_Pmul_l.
caseEq (czero_test c).
intros Hctest; setoid_rewrite (c0test_c _ Hctest); 
setoid_rewrite Pmul_0_l; setoid_rewrite Padd_0_r.
setoid_rewrite mkPX_PX_c; simpl.
intros Heq; inversion Heq.
assert (Hab : a==b).
apply ceq_trans with (b++c0);[assumption|setoid ring].
setoid_rewrite PX_interp.
rewrite (Npred_correct p (Npos p)); auto.
setoid_rewrite Ppow_plus.
simpl (X^1).
setoid_rewrite (Pmul_sym X).
setoid_rewrite <- Pmul_assoc.
setoid_replace (X*Q) with P0; [idtac | assumption].
repeat (auto;fail || setoid ring || split).
intros Hctest.
setoid_rewrite mkPX_PX_c; setoid_rewrite (PX_interp (X*Q)).
intros Heq.
assert (H':Pc a != PX (PX Q p c) 1 b).
setoid_rewrite (PX_interp (PX Q p c)).
setoid_rewrite (PX_interp Q).
simpl (X^1).
apply PolEq_trans with (1:= Heq).
setoid ring.
inversion H'.
assert (H'':PX Q p c != P0) by assumption.
inversion H''.
elim (ceq_propF c c0);auto.
rewrite <- c0test_ceqb; auto.

intros p' Hn; setoid_rewrite (PX_interp Q).
match goal with |- _ != ?x -> _ =>
   setoid_replace x with (PX (PX (PX Q p c) 1 b) p' c0)
end.
intros H'; inversion H'.
assert (Ha:a == c0) by assumption; 
assert (H'' : PX (PX Q p c) 1 b != P0) by assumption;
clear - IHQ Ha H''.
inversion H''.
assert (Hb: b==c0) by assumption;
assert (H'3: PX Q p c != P0) by assumption;
clear - IHQ Ha Hb H'3.
rewrite <- PX_interp.
assert (a==b) by (apply ceq_trans with c0; auto).
auto.
setoid_rewrite (PX_interp (PX (PX Q p c) 1 b)).
setoid_rewrite (PX_interp (PX Q p c)).
setoid_rewrite (PX_interp Q).
simpl (X^1); setoid ring.
Qed.

Theorem c0test_n : 
   forall x, ~ x==c0 -> czero_test x = false.
intros; caseEq (czero_test x); auto.
intros H0; elim H; apply ceq_prop; rewrite <- c0test_ceqb; rewrite H0.
exact I.
Qed.

Theorem least_non_zero_P4 :
  forall P b n Q, P != X^n * (Pc b + X * Q) -> ~b==c0 ->
            least_non_zero_coeff P == b.
intros P; induction P.
intros b n Q Heq Hbn0.
destruct (Pc_eq_X_pow_mul_decompose _ _ _ _ Heq) as [Hc [Hn HQ]].
exact Hc.

intros b n Q.
caseEq n.
intros Hn0; simpl (X^0);
match goal with |- _ != ?x -> _ => setoid_replace x with (PX Q 1 b) end.
intros Heq Hbn0; inversion Heq.
assert (Hcb : c==b) by assumption; clear - Hcb Hbn0.
setoid_rewrite Hcb; simpl; rewrite (c0test_n b); auto.
assert (Hcb : c==b) by auto; clear - Hcb Hbn0.
setoid_rewrite Hcb; simpl; rewrite (c0test_n b); auto.
assert (Hcb : c==b) by auto; clear - Hcb Hbn0.
setoid_rewrite Hcb; simpl; rewrite (c0test_n b); auto.
setoid_rewrite (PX_interp Q); simpl (X^1); setoid ring.

intros p' Hn.
match goal with |- _ != ?x -> _ => 
  setoid_replace x with (PX (PX Q 1 b) p' c0)
end.
intros Heq Hbn0; inversion Heq.
assert (Hc0 : c==c0) by assumption; assert (Hp :P !=PX Q 1 b) by assumption;
clear - Hc0 Hbn0 Hp.
assert (Hctest:czero_test c=true).
setoid_rewrite Hc0; rewrite czero_test_0; trivial.
simpl; rewrite Hctest.
setoid_rewrite Hp; simpl.
rewrite (c0test_n b); auto.
assert (Hc0: c==c0) by auto; 
 assert (Hp:P!=PX (PX Q 1 b) i c0) by assumption; clear - Hc0 Hbn0 IHP Hp.
assert (Hctest:czero_test c=true).
setoid_rewrite Hc0; rewrite czero_test_0; trivial.
simpl; rewrite Hctest.
setoid_rewrite Hp; simpl.
rewrite czero_test_0.
rewrite (c0test_n b); auto.
assert (HPQ: PX Q 1 b != PX P i c0) by assumption; clear - HPQ Hbn0.
inversion HPQ; elim Hbn0; auto.
setoid_rewrite (PX_interp (PX Q 1 b)); setoid_rewrite (PX_interp Q).
simpl (X^1); setoid ring.
Qed.

Theorem least_non_zero_P5 :
  forall P b, P != Pc b -> least_non_zero_coeff P == b.
intros P b Heq; setoid_rewrite Heq; auto.
Qed.

Theorem least_non_zero_P6 :
  forall P n Q a, P != X^n * (Pc a + X * Q) -> a == c0 ->
    least_non_zero_coeff P == least_non_zero_coeff Q.
intros P; induction P; intros n Q a.
intros Heq Ha.
destruct (Pc_eq_X_pow_mul_decompose _ _ _ _ Heq) as [Hc [Hn HQ]].
setoid_rewrite Hc; setoid_rewrite Ha; setoid_rewrite HQ; auto.
intros Heq Ha.
caseEq n.
intros Hn0; rewrite Hn0 in Heq; simpl (X^0) in Heq.
assert (H':PX P p c != PX Q 1 a).
setoid_rewrite (PX_interp Q).
simpl (X^1); setoid_rewrite Heq; setoid ring.
assert (Hatest: czero_test a = true).
setoid_rewrite Ha; apply czero_test_0.
setoid_rewrite H'; simpl; rewrite Hatest; auto.
intros p' Hn;
assert (H':PX P p c != PX (PX Q 1 a) p' c0).
rewrite Hn in Heq.
setoid_rewrite Heq; setoid_rewrite (PX_interp (PX Q 1 a));
setoid_rewrite (PX_interp Q).
simpl (X^1);setoid ring.
inversion H'.
assert (Hc0:c==c0) by assumption; assert (HPQ : P!=PX Q 1 a) by assumption;
clear - IHP Hc0 HPQ Ha.
assert (Hctest: czero_test c = true).
setoid_rewrite Hc0; apply czero_test_0.
simpl; rewrite Hctest; apply IHP with (n:=0%N)(Q:=Q)(a:=a); trivial.
apply PolEq_trans with (1:= HPQ); rewrite (PX_interp Q);
simpl Pol_pow;setoid ring.
assert (Hc0:c==c0) by auto; assert (HPQ: P!=PX(PX Q 1 a) i c0) by assumption;
clear - IHP Hc0 HPQ Ha.
simpl.
assert (Hctest : czero_test c = true).
setoid_rewrite Hc0; apply czero_test_0.
rewrite Hctest.

apply (IHP (Npos i) Q a); trivial.
rewrite HPQ; setoid_rewrite (PX_interp (PX Q 1 a));
setoid_rewrite (PX_interp Q); simpl (X^1);setoid ring.
assert (Hc0 : c==c0) by assumption; 
assert (HPQ : PX Q 1 a != PX P i c0) by assumption; 
clear - IHP Hc0 HPQ.
assert (Hctest : czero_test c = true).
setoid_rewrite Hc0; apply czero_test_0.
inversion HPQ.
assert (H' : Q != P) by assumption; clear - Hc0 Hctest H'.
setoid_rewrite H'; simpl.
setoid_rewrite Hctest; auto.
assert (H' : Q != PX P i0 c0) by assumption; clear - Hc0 Hctest H'.
setoid_rewrite H'.
simpl; rewrite Hctest;rewrite czero_test_0; auto.
assert (H':P!=PX Q i0 c0) by assumption; clear - Hctest H'.
setoid_rewrite H'; simpl; rewrite Hctest; rewrite czero_test_0; auto.
Qed.

Theorem least_non_zero_P7 :
  forall b, least_non_zero_coeff (Pc b) == b.
intros b; apply least_non_zero_P5; trivial.
Qed.

Theorem no_alternation_increasing :
  forall P, c0 <= least_non_zero_coeff P -> no_alternation P ->
  forall x y, c0 <= x <= y -> c0 <= Pol_eval P x <= Pol_eval P y.

intros P H H1;generalize H;clear H.
induction H1.
intros H x y Hint.
rewrite p.
simpl.
rewrite p in H.
simpl in H.
split; auto.
apply cle_refl.
intros Hpos x y Hint ; rewrite p in Hpos; rewrite p.
do 2 setoid_rewrite Pol_eval_mult.
do 2 setoid_rewrite Pol_eval_pow.
do 2 setoid_rewrite Pol_eval_plus.
assert (Hapos : c0 <= a)
  by (setoid_rewrite (least_non_zero_P4 (X^n*(Pc a+X*P2)) a n P2) in Hpos;
       auto).
assert (Hlp2 : c0 <= least_non_zero_coeff P2).
apply cmul_lt_0_le_reg_r with a.
apply clt_decompose; intuition.
unfold clt; intuition.
setoid_replace (c0**a) with c0.
setoid_rewrite <- (cmul_sym a); assumption.
setoid ring.
repeat setoid_rewrite Pol_eval_mult.
assert (IH':c0 <= Pol_eval P2 x <= Pol_eval P2 y).
apply IHno_alternation; auto.
split.
apply cle_0_mult.
setoid_rewrite Pol_eval_X.
apply cpow_pos; intuition.
apply cle_0_plus.
rewrite Pol_eval_c; auto.
apply cle_0_mult.
setoid_rewrite Pol_eval_X; intuition.
intuition.
repeat setoid_rewrite Pol_eval_X.
repeat setoid_rewrite Pol_eval_c.
apply cle_trans with (cpow y n ** (a ++ x ** Pol_eval P2 x)).
repeat setoid_rewrite (cmult_sym  (a ++ x ** Pol_eval P2 x)).
apply cmul_le_compat_r.
apply cpow_le_compat_l; intuition.
apply cle_0_plus.
assumption.
apply cle_0_mult; intuition.
repeat setoid_rewrite (cmul_sym (cpow y n)).
apply cmul_le_compat_r.
apply cplus_le_compat.
apply cle_refl.
apply cle_trans with (x**Pol_eval P2 y).
repeat setoid_rewrite (cmul_sym x).
apply cmul_le_compat_r; intuition.
apply cmul_le_compat_r.
intuition.
apply cle_trans with (Pol_eval P2 x); intuition.
apply cpow_pos; apply cle_trans with x; intuition.
Qed.

Theorem no_alternation_increasing' :
  forall P, c0 <= least_non_zero_coeff P -> no_alternation P ->
  forall x y, c0 <= x <= y -> Pol_eval P x <= Pol_eval P y.
intros; assert (0 <= Pol_eval P x <= Pol_eval P y).
apply no_alternation_increasing; auto.
intuition.
Qed.

Theorem no_alternation_positive :
  forall P, no_alternation P -> 0 <= least_non_zero_coeff P ->
  forall x, c0 <= x -> c0 <= Pol_eval P x.
intros P Hna Hpos x Hposx.
elim (least_non_zero_P2 P); intros n [Q Heq].
apply cle_trans with (Pol_eval P c0).
rewrite Heq; simpl.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_pow.
setoid_rewrite Pol_eval_X.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply cmul_le_0.
apply cpow_pos.
apply cle_refl.
apply cle_0_plus.
assumption.
setoid_rewrite cmul_0_l.
apply cle_refl.
apply no_alternation_increasing'; auto.
split;[apply cle_refl|assumption].
Qed.

Theorem no_alternation_positive_strict :
  forall P, no_alternation P -> c0 < least_non_zero_coeff P ->
  forall x, c0 < x -> c0 < Pol_eval P x.

intros P' H; elim H.
intros c q Hq Hqpos x Hxpos.
setoid_rewrite Hq.
setoid_rewrite Hq in Hqpos.
setoid_rewrite least_non_zero_P7 in Hqpos; auto.

intros n a P1 P2 HnaP2 IHP2 Ha Hprodpos Heq Hpos x Hxpos.
assert (least_non_zero_coeff P1 == a).
apply least_non_zero_P4 with (1:= Heq).
assumption.
assert (Hpartpos : c0 <= x ** Pol_eval P2 x).
apply cmul_le_0.
apply clt_cle_weak; auto.
apply no_alternation_positive.
assumption.
apply cmul_lt_0_le_reg_r with a.
apply clt_decompose; auto.
setoid_rewrite <- H0; apply clt_cle_weak; assumption.
setoid_rewrite cmul_0_l; setoid_rewrite cmul_sym; assumption.
apply clt_cle_weak; assumption.
setoid_rewrite Heq.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_pow.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply cmul_lt_0.
apply cpow_lt_0_compat_l.
apply Hxpos.
apply cplus_lt_0_le_lt.
apply clt_decompose.
intuition.
setoid_rewrite <- H0; apply clt_cle_weak;auto.
assumption.
Qed.

Definition continuous (f:Coef -> Coef)(x:Coef) :=
  forall eps, c0 < eps ->
     exists delta,
     c0 < delta /\ forall y, copp delta <= y--x <= delta -> 
        copp eps <= f y -- f x <= eps.

Theorem ext_continuous :
  forall f g:Coef -> Coef, (forall x, f x == g x) ->
    forall x, continuous f x -> continuous g x.
unfold continuous.
intros f g Heq x Hcf eps Hp; destruct (Hcf eps) as [delta [Hdp Hf]].
auto.
exists delta; split.
assumption.
intros y Hint; repeat setoid_rewrite <- Heq.
apply Hf; auto.
Qed.

Theorem const_continuous :
  forall c x:Coef, continuous (fun x:Coef => c) x.
intros c x eps Hp; exists c1; split.
apply clt_decompose;[apply c0_diff_c1 | apply c0_cle_c1].
assert (c0 <= eps) by (apply clt_cle_weak; assumption).
intros y _; split; setoid_rewrite csub_def; setoid_rewrite copp_def.
apply copp_le_0_compat; auto.
auto.
Qed.

Theorem id_continuous :
  forall x:Coef, continuous (fun y=>y) x.
intros x eps Hp; exists eps; split.
assumption.
intros y Hint; assumption.
Qed.

Theorem plus_continuous :
  forall f g, forall x, continuous f x -> continuous g x ->
      continuous (fun y => f y ++ g y) x.
intros f g x Hcf Hcg eps Hp; destruct (Hcf (eps/(c1++c1))) as [df [Hdfp Hf]].
apply cdiv_lt_0_compat_l.
apply c0_clt_2.
assumption.
destruct (Hcg (eps/(c1++c1))) as [dg [Hdgp Hg]].
apply cdiv_lt_0_compat_l.
apply c0_clt_2.
assumption.
assert (Hmin:exists d, clt c0 d /\ (cle d df /\ cle d dg)).
destruct (clt_le_dec df dg) as [Hdfl | Hdgl].
exists df;split; 
   [assumption |split; [apply cle_refl | apply clt_cle_weak;assumption]].
exists dg;split; [assumption | split; [assumption|apply cle_refl]].
destruct Hmin as [d [Hdp [Hddf Hddg]]].
exists d.
split.
assumption.
intros y Hint.
setoid_replace  (f y ++ g y -- (f x ++ g x)) with
  ((f y -- f x) ++ (g y -- g x)).
setoid_rewrite (cut_half eps).
setoid_replace (-- (eps / (c1 ++ c1) ++ eps / (c1 ++ c1))) with
    (--(eps/(c1++c1)) ++ --(eps/(c1++c1))).
assert (Hintf : --df <= y--x <= df).
split.
apply cle_trans with (--d).
apply copp_le_compat; assumption.
intuition.
apply cle_trans with d;intuition.
assert (Hintg : --dg <= y--x <= dg).
split.
apply cle_trans with (--d).
apply copp_le_compat; assumption.
intuition.
apply cle_trans with d;intuition.
assert (Hrf := Hf y Hintf).
assert (Hrg := Hg y Hintg).
split; apply cplus_le_compat; intuition.
cut (forall a b:Coef, -- (a++b)==--a ++ -- b);
 [intros copp_plus | idtac].
apply copp_plus.
exact Qopp_plus.
setoid ring.
Qed.

Theorem mult_continuous_aux :
  forall f g x, continuous f x -> continuous g x ->
    c0 <= f x -> c0 <= g x ->
    continuous (fun y => f y ** g y) x.
intros f g x Hcf Hcg Hposf Hposg eps Hp.
assert (Hg : 0 < g x ++ c1).
setoid_rewrite cadd_sym.
apply cplus_lt_0_le_lt.
apply c0_clt_c1.
assumption.
assert (Hf : 0 < f x ++ c1).
setoid_rewrite cadd_sym.
apply cplus_lt_0_le_lt.
apply c0_clt_c1.
assumption.
assert (Hdeng :0 < ((c1++c1)**(g x ++ c1))).
apply cmul_lt_0.
apply c0_clt_c1.
assumption.
assert (Hdenf :0 < ((c1++c1)**(f x ++ c1))).
apply cmul_lt_0.
apply c0_clt_c1.
assumption.
assert (epsf : exists e, 0 < e /\ e <= eps/((c1++c1)**(g x++c1)) /\
                 e <= c1).
destruct (clt_le_dec c1 (eps/((c1++c1)**(g x++c1)))).
exists c1;split;[apply c0_clt_c1 | split;[idtac |apply cle_refl]].
apply clt_cle_weak; assumption.
exists (eps/((c1++c1)**(g x ++ c1))).
split.
apply cdiv_lt_0_compat_l.
apply cmul_lt_0;[apply c0_clt_c1 | assumption].
assumption.
split;[apply cle_refl | assumption].
assert (epsg : exists e, c0 < e /\ e <= eps/((c1++c1)**(f x++c1)) /\
                 e <= c1).
destruct (clt_le_dec c1 (eps/((c1++c1)**(f x++c1)))).
exists c1;split;[apply c0_clt_c1 | split;[idtac |apply cle_refl]].
apply clt_cle_weak; assumption.
exists (eps/((c1++c1)**(f x ++ c1))).
split.
apply cdiv_lt_0_compat_l.
apply cmul_lt_0;[apply c0_clt_c1 | assumption].
assumption.
split;[apply cle_refl | assumption].
destruct epsf as [ef [Hefp [Hef_eps Hef_1]]].
destruct (Hcf ef) as [df [Hpf Hyf]].
exact Hefp.

destruct epsg as [eg [Hegp [Heg_eps Heg_1]]].
destruct (Hcg eg) as [dg [Hpg Hyg]].
exact Hegp.

assert (Hmin : exists d, 0 < d /\ (d <= df /\ d <= dg)).
destruct (clt_le_dec df dg) as [dfltdg | dgledf].
exists df;split;[assumption | split; [apply cle_refl | idtac]].
apply clt_cle_weak; assumption.
exists dg;split;[assumption | split; [assumption | apply cle_refl]].
destruct Hmin as [d [Hdpos [dledf dledg]]].
exists d; split; [assumption | intros y Hint].
assert (decompose: f y ** g y -- f x ** g x ==
        (f y -- f x)**g y ++ f x ** (g y -- g x)).
setoid ring.
assert (decompose2: f y ** g y -- f x ** g x ==
                    (g y -- g x)**f y ++ g x ** (f y -- f x)).
setoid ring.
assert (Hintf : --df <= y -- x <= df).
split;[apply cle_trans with (--d); [apply copp_le_compat|idtac] |
        apply cle_trans with d]; intuition.
assert (Hyf' := Hyf y Hintf).
assert (Hintg : --dg <= y -- x <= dg).
split;[apply cle_trans with (--d); [apply copp_le_compat|idtac] |
        apply cle_trans with d]; intuition.
assert (Hyg' := Hyg y Hintg).
split.
destruct (clt_le_dec c0 (g y)) as [gyp | gyn].
setoid_rewrite decompose.
setoid_replace (-- eps) with (--(eps/(c1++c1)) ++ --(eps/(c1++c1))).
apply cplus_le_compat.
apply cle_trans with (--(eps/((c1++c1)**(g x ++ c1)))**g y).
apply cle_trans with (--((eps/(c1++c1))/((g x++c1))**(g x ++ c1))).
setoid_rewrite cmul_sym.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
setoid_rewrite mul_copp.
apply copp_le_compat.
setoid_rewrite cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
repeat setoid_rewrite (cmul_sym ( eps / ((c1 ++ c1) ** (g x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd.
apply cle_trans with eg.
intuition.
assumption.
apply cdiv_le_0_compat_l.
apply cmul_lt_0.
apply c0_clt_2.
assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply cle_trans with (--ef).
apply copp_le_compat.
assumption.
intuition.
apply clt_cle_weak; assumption.
apply cle_trans with (--(eps/((c1++c1)**(f x ++ c1)))**f x).
setoid_rewrite mul_copp.
apply copp_le_compat.
apply cle_trans with (eps / ((c1 ++ c1) ** (f x ++ c1)) **(f x ++ c1)).
repeat setoid_rewrite (cmul_sym (eps / ((c1 ++ c1) ** (f x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd; setoid_rewrite csub_diag; apply c0_cle_c1.
apply cdiv_le_0_compat_l.
assumption.
apply clt_cle_weak; assumption.
setoid_rewrite <- (cmul_sym (f x ++ c1)).
setoid_rewrite <- cdiv_assoc.
apply pos_non_c0.
assumption.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
setoid_rewrite (cmul_sym (f x)).
apply cmul_le_compat_r.
apply cle_trans with (--eg).
apply copp_le_compat.
assumption.
intuition; fail.
assumption.
setoid_rewrite cadd_copp.
setoid_rewrite <- cut_half.
apply ceq_refl.
destruct (clt_le_dec c0 (f y)) as [fyp | fyn].
idtac "case g y <= 0 and 0 < f y".
setoid_rewrite decompose2.
setoid_replace (-- eps) with (--(eps/(c1++c1)) ++ --(eps/(c1++c1))).
apply cplus_le_compat.
apply cle_trans with (--(eps/((c1++c1)**(f x ++ c1)))**f y).
apply cle_trans with (--((eps/(c1++c1))/((f x++c1))**(f x ++ c1))).
setoid_rewrite cmul_sym.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
setoid_rewrite mul_copp.
apply copp_le_compat.
setoid_rewrite cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
repeat setoid_rewrite (cmul_sym ( eps / ((c1 ++ c1) ** (f x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd.
apply cle_trans with ef.
intuition;fail.
assumption.
apply cdiv_le_0_compat_l.
apply cmul_lt_0.
apply c0_clt_2.
assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply cle_trans with (--eg).
apply copp_le_compat.
assumption.
intuition.
apply clt_cle_weak; assumption.
apply cle_trans with (--(eps/((c1++c1)**(g x ++ c1)))**g x).
setoid_rewrite mul_copp.
apply copp_le_compat.
apply cle_trans with (eps / ((c1 ++ c1) ** (g x ++ c1)) **(g x ++ c1)).
repeat setoid_rewrite (cmul_sym (eps / ((c1 ++ c1) ** (g x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd; setoid_rewrite csub_diag; apply c0_cle_c1.
apply cdiv_le_0_compat_l.
assumption.
apply clt_cle_weak; assumption.
setoid_rewrite <- (cmul_sym (g x ++ c1)).
setoid_rewrite <- cdiv_assoc.
apply pos_non_c0.
assumption.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
setoid_rewrite (cmul_sym (g x)).
apply cmul_le_compat_r.
apply cle_trans with (--ef).
apply copp_le_compat.
assumption.
intuition; fail.
assumption.
setoid_rewrite cadd_copp.
setoid_rewrite <- cut_half.
apply ceq_refl.
idtac "case where both f y and g y are negative.".
setoid_rewrite decompose.
setoid_replace (-- eps) with (--(eps/(c1++c1)) ++ --(eps/(c1++c1))).
apply cplus_le_compat.
apply cle_trans with (--(eps/((c1++c1)**(g x ++ c1)))**(--g y)).
apply cle_trans with (--((eps/(c1++c1))/((g x++c1))**(g x ++ c1))).
setoid_rewrite cmul_sym.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
setoid_rewrite mul_copp.
apply copp_le_compat.
setoid_rewrite cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
repeat setoid_rewrite (cmul_sym ( eps / ((c1 ++ c1) ** (g x ++ c1)))).
apply cmul_le_compat_r.
apply cle_trans with eg.
apply cle_trans with (g x -- g y).
setoid_replace (-- g y) with (c0 ++(-- g y));[idtac | setoid ring;fail].
setoid_replace (g x -- g y) with (g x ++(-- g y));[idtac | setoid ring;fail].
apply cplus_le_compat.
assumption.
apply cle_refl.
setoid_rewrite <- (copp_copp (g x -- g y)).
setoid_rewrite  copp_csub.
setoid_rewrite <- (copp_copp eg).
apply copp_le_compat.
intuition.
apply cle_trans with c1.
assumption.
pose (u:= g x ++ c1); fold u; 
 setoid_replace c1 with (c0++c1);[unfold u; clear u| setoid ring].
apply cplus_le_compat.
assumption.
apply cle_refl.
apply cdiv_le_0_compat_l.
apply cmul_lt_0.
apply c0_clt_2.
assumption.
apply clt_cle_weak; assumption.
repeat setoid_rewrite <- (fun z => (mul_copp_copp z (g y))).
apply cmul_le_compat_r.
apply copp_le_compat.
apply cle_trans with ef.
intuition.
assumption.
setoid_replace c0 with (--c0);[apply copp_le_compat;assumption|setoid ring].
apply cle_trans with (--(eps/((c1++c1)**(f x ++ c1)))**f x).
setoid_rewrite mul_copp.
apply copp_le_compat.
apply cle_trans with (eps / ((c1 ++ c1) ** (f x ++ c1)) **(f x ++ c1)).
repeat setoid_rewrite (cmul_sym (eps / ((c1 ++ c1) ** (f x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd; setoid_rewrite csub_diag; apply c0_cle_c1.
apply cdiv_le_0_compat_l.
assumption.
apply clt_cle_weak; assumption.
setoid_rewrite <- (cmul_sym (f x ++ c1)).
setoid_rewrite <- cdiv_assoc.
apply pos_non_c0.
assumption.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
setoid_rewrite (cmul_sym (f x)).
apply cmul_le_compat_r.
apply cle_trans with (--eg).
apply copp_le_compat.
assumption.
intuition; fail.
assumption.
setoid_rewrite cadd_copp.
setoid_rewrite <- cut_half.
apply ceq_refl.
idtac "proving the upperbound".
destruct (clt_le_dec c0 (g y)).
setoid_rewrite decompose.
setoid_rewrite (cut_half eps).
apply cplus_le_compat.
apply cle_trans with (eps/((c1++c1)**(g x ++ c1))**g y).
apply cmul_le_compat_r.
apply cle_trans with ef.
intuition.
assumption.
apply clt_cle_weak; assumption.
apply cle_trans with (((eps/(c1++c1))/(g x++c1))**(g x ++ c1)).
setoid_rewrite cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
repeat setoid_rewrite (cmul_sym ( eps / ((c1 ++ c1) ** (g x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd.
apply cle_trans with eg; intuition;fail.
apply cdiv_le_0_compat_l.
apply cmul_lt_0.
apply c0_clt_2.
assumption.
apply clt_cle_weak; assumption.

setoid_rewrite (cmul_sym (eps / (c1 ++ c1) / (g x ++ c1))(g x ++ c1)).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
apply cle_trans with (eps/((c1++c1)**(f x ++ c1))**f x).
setoid_rewrite (cmul_sym (f x)).
apply cmul_le_compat_r.
apply cle_trans with eg.
intuition; fail.
assumption.
assumption.

apply cle_trans with (eps / ((c1 ++ c1) ** (f x ++ c1)) **(f x ++ c1)).
repeat setoid_rewrite (cmul_sym (eps / ((c1 ++ c1) ** (f x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd; setoid_rewrite csub_diag; apply c0_cle_c1.
apply cdiv_le_0_compat_l.
assumption.
apply clt_cle_weak; assumption.
setoid_rewrite <- (cmul_sym (f x ++ c1)).
setoid_rewrite <- cdiv_assoc.
apply pos_non_c0.
assumption.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
destruct (clt_le_dec c0 (f y)) as[fyp | fyn].
idtac "case g y <= 0 and 0 < f y".
setoid_rewrite decompose2.
setoid_rewrite (cut_half eps).
apply cplus_le_compat.
apply cle_trans with (eps/((c1++c1)**(f x ++ c1))**f y).
apply cmul_le_compat_r.
apply cle_trans with eg.
intuition;fail.
assumption.
apply clt_cle_weak; assumption.

apply cle_trans with ((eps/(c1++c1))/((f x++c1))**(f x ++ c1)).
setoid_rewrite cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
repeat setoid_rewrite (cmul_sym ( eps / ((c1 ++ c1) ** (f x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd.
apply cle_trans with ef.
intuition;fail.
assumption.
apply cdiv_le_0_compat_l.
apply cmul_lt_0.
apply c0_clt_2.
assumption.
apply clt_cle_weak; assumption.

setoid_rewrite cmul_sym.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
apply cle_trans with (eps/((c1++c1)**(g x ++ c1))**g x).
setoid_rewrite (cmul_sym (g x)).
apply cmul_le_compat_r.
apply cle_trans with ef.
intuition; fail.
assumption.
assumption.
apply cle_trans with (eps / ((c1 ++ c1) ** (g x ++ c1)) **(g x ++ c1)).
repeat setoid_rewrite (cmul_sym (eps / ((c1 ++ c1) ** (g x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd; setoid_rewrite csub_diag; apply c0_cle_c1.
apply cdiv_le_0_compat_l.
assumption.
apply clt_cle_weak; assumption.
setoid_rewrite <- cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
setoid_rewrite <- (cmul_sym (g x ++ c1)).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
idtac "case where both g y and f y are negative.".
setoid_rewrite decompose.
setoid_rewrite (cut_half eps).
apply cplus_le_compat.
apply cle_trans with (eps/((c1++c1)**(g x ++ c1))**(--g y)).
setoid_rewrite <- (mul_copp_copp (f y -- f x)).
apply cmul_le_compat_r.
apply cle_trans with ef.
setoid_rewrite <- (copp_copp ef).
apply copp_le_compat.
intuition.
assumption.
setoid_replace c0 with (--c0);[apply copp_le_compat;auto|setoid ring;fail].
apply cle_trans with (((eps/(c1++c1))/(g x++c1))**(g x ++ c1)).
setoid_rewrite cdiv_assoc.
apply pos_non_c0; apply cmul_lt_0; assumption || apply c0_clt_c1.
repeat setoid_rewrite (cmul_sym ( eps / ((c1 ++ c1) ** (g x ++ c1)))).
apply cmul_le_compat_r.
apply cle_trans with c1.
apply cle_trans with (g x -- g y).
setoid_replace (-- g y) with (c0++(--g y));[idtac|setoid ring;fail].
setoid_replace (g x -- g y) with (g x++(--g y));[idtac|setoid ring;fail].
apply cplus_le_compat.
assumption.
apply cle_refl.
apply cle_trans with eg.
setoid_rewrite <- (copp_copp (g x -- g y)).
setoid_rewrite <- (copp_copp eg).
apply copp_le_compat.
setoid_rewrite copp_csub.
intuition;fail.
assumption.
apply cplus_pos_simplify; assumption.
apply cdiv_le_0_compat_l.
apply cmul_lt_0.
apply c0_clt_2.
assumption.
apply clt_cle_weak; assumption.

setoid_rewrite (cmul_sym (eps / (c1 ++ c1) / (g x ++ c1))(g x ++ c1)).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
apply cle_trans with (eps/((c1++c1)**(f x ++ c1))**f x).
setoid_rewrite (cmul_sym (f x)).
apply cmul_le_compat_r.
apply cle_trans with eg.
intuition; fail.
assumption.
assumption.

apply cle_trans with (eps / ((c1 ++ c1) ** (f x ++ c1)) **(f x ++ c1)).
repeat setoid_rewrite (cmul_sym (eps / ((c1 ++ c1) ** (f x ++ c1)))).
apply cmul_le_compat_r.
apply cle_csub_cadd; setoid_rewrite csub_diag; apply c0_cle_c1.
apply cdiv_le_0_compat_l.
assumption.
apply clt_cle_weak; assumption.
setoid_rewrite <- (cmul_sym (f x ++ c1)).
setoid_rewrite <- cdiv_assoc.
apply pos_non_c0.
assumption.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
apply cle_refl.
Qed.

Theorem scal_mult_continuous :
  forall f a x, continuous f x -> continuous (fun z => a**f z) x.
intros f a x Hcf.
destruct (ceq_dec a c0) as [Ha0 | Han].
apply ext_continuous with (f:= fun x:Coef => c0).
intros; setoid_rewrite Ha0; setoid ring.
apply const_continuous.
destruct (clt_le_dec c0 a) as [Hap | Hang].
intros eps Hp.
assert (Hp':c0 < eps/a).
apply cdiv_lt_0_compat_l;assumption.
destruct (Hcf (eps/a) Hp') as [delta [Hdp Hd]].
exists delta;split;[assumption|intros y Hy].
assert (Hfy:=Hd y Hy).
setoid_replace (a**f y--a**f x) with ((f y--f x)**a);[idtac | setoid ring].
assert (eps == eps/a **a).
setoid_rewrite cmul_sym.
setoid_rewrite cmul_div_r.
assumption.
auto.

split.
setoid_replace (--eps) with (--(eps/a)**a).
apply cmul_le_compat_r.
intuition;fail.
apply clt_cle_weak;assumption.
setoid_rewrite mul_copp.
setoid_rewrite <- H; auto.

setoid_replace eps with ((eps/a)**a).
apply cmul_le_compat_r.
intuition;fail.
apply clt_cle_weak; assumption.
assumption.
intros eps Hp.
assert (Hp':c0 < eps/(--a)).
apply cdiv_lt_0_compat_l.
apply clt_decompose.
intros Ha; elim Han.
setoid_rewrite <- (copp_copp a);setoid_rewrite <- Ha; setoid ring.
apply cle_0_copp;assumption.
assumption.

destruct (Hcf (eps/(--a)) Hp') as [delta [Hdp Hd]].
exists delta;split;[assumption|intros y Hy].
assert (Hfy:=Hd y Hy).
setoid_replace (a**f y--a**f x) with ((--(f y--f x))**(--a));
 [idtac | setoid ring].
assert (eps == eps/(--a) **(--a)).
setoid_rewrite cmul_sym.
setoid_rewrite cmul_div_r.
intros Ha; elim Han; setoid_replace c0 with (a ++ (-- a)).
setoid_rewrite Ha; setoid ring.
setoid ring.
auto.

split.
setoid_replace (--eps) with (--(eps/(--a))**(--a)).
apply cmul_le_compat_r.
apply copp_le_compat.
intuition;fail.
apply cle_0_copp;assumption.
setoid_rewrite mul_copp.
setoid_rewrite <- H; auto.

setoid_replace eps with ((eps/(--a))**(--a)).
apply cmul_le_compat_r.
setoid_rewrite <- (copp_copp (eps / -- a)).
apply copp_le_compat.
intuition;fail.
apply cle_0_copp;assumption.
assumption.
Qed.

Theorem mult_continuous_aux2 :
  forall f g x, continuous f x -> c0 <= f x -> continuous g x ->
    continuous (fun y => f y ** g y) x.
intros f g x Hcf fxp Hcg.
destruct (clt_le_dec c0 (g x)) as [gxp|gxn].
apply mult_continuous_aux; auto.
apply clt_cle_weak; assumption.
apply ext_continuous with (fun y => (--c1)** (f y ** --g y)).
intros y; setoid ring.
apply scal_mult_continuous with (f:= fun y => f y ** -- g y).
apply mult_continuous_aux with (g:= fun y => -- g y).
assumption.
apply ext_continuous with (f := fun y => (--c1)**g y).
intros y; setoid ring.
apply scal_mult_continuous.
assumption.
assumption.
apply cle_0_copp; assumption.
Qed.

Theorem mult_continuous :
  forall f g x, continuous f x -> continuous g x ->
    continuous (fun y => f y ** g y) x.
intros f g x Hcf Hcg.
destruct (clt_le_dec c0 (f x)) as [fxp | fxn].
apply mult_continuous_aux2; auto.
apply clt_cle_weak; assumption.
apply ext_continuous with (fun y => (--c1)**((--f y)**g y)).
intros y; setoid ring.
apply scal_mult_continuous with (f:= fun y => (--f y ** g y)).
apply mult_continuous_aux2 with (f:= fun y => -- f y); auto.
apply ext_continuous with (f:= fun y => (--c1)**f y).
intros; setoid ring.
apply scal_mult_continuous; auto.
apply cle_0_copp; auto.
Qed.

Theorem pow_continuous :
  forall f n x, continuous f x -> continuous (fun y => cpow (f y) n) x.
intros f n x Hcf; case n.
apply ext_continuous with (f := fun y:Coef => c1).
intros y; setoid_rewrite cpow_0; auto.
apply const_continuous.
intros p; induction p.
apply ext_continuous with 
  (fun y => (f y) ** (cpow (f y) (Npos p) ** cpow (f y) (Npos p))).
intros y; rewrite Npos_xI_expand; 
 repeat setoid_rewrite cpow_plus; setoid_rewrite cpow_1; apply ceq_refl.
apply mult_continuous with 
     (g:= fun y => cpow (f y)(Npos p)**cpow (f y)(Npos p)).
assumption.
apply mult_continuous with
  (f :=  fun y => cpow (f y)(Npos p))
  (g :=  fun y => cpow (f y)(Npos p));assumption.
apply ext_continuous with 
  (fun y => (cpow (f y) (Npos p) ** cpow (f y) (Npos p))).
intros y; rewrite Npos_xO_expand; 
 repeat setoid_rewrite cpow_plus; apply ceq_refl.
apply mult_continuous with
  (f :=  fun y => cpow (f y)(Npos p))
  (g :=  fun y => cpow (f y)(Npos p));assumption.
apply ext_continuous with  (f:= f).
intros; setoid_rewrite cpow_1; apply ceq_refl.
assumption.
Qed.

Theorem Pol_eval_continuous :
  forall P x, continuous (Pol_eval P) x.
intros P x; induction P.
simpl.
apply const_continuous.
apply ext_continuous with (fun y => Pol_eval P y**cpow y (Npos p)++c).
intros; simpl; auto.

apply plus_continuous with (f:= fun y => Pol_eval P y**cpow y (Npos p))
  (g:= fun y:Coef => c).
apply mult_continuous with (f:= Pol_eval P)(g:=fun y=>cpow y (Npos p)).
assumption.
apply pow_continuous with (f:= fun y:Coef=>y).
apply id_continuous.
apply const_continuous.
Qed.




