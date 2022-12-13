Require Import Recdef.
Require SmallDescartesLaw.
Import Setoid.
Import ZArith.
Import Omega.
Import CAD_types.
Import Utils.
Import NArith.
Import Zwf.
Import QArith.
Import Qring.
Import Pol_ring2.
Import Qnorm.
Import SmallDescartesLaw.
Import Coef_props.

Theorem Horner_step_positive_tech :
  forall r a Q, a < c0 -> 
  (forall x y, r < x -> x <= y -> 
           c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y) ->
         r < r++c1 -- a/Pol_eval Q (r++c1).
intros r a Q Ha Hq.
setoid_replace (r ++ c1 -- a / Pol_eval Q (r ++ c1)) with
   (r++(c1 ++ (-- a / Pol_eval Q (r ++ c1)))).
apply cplus_lt_r.
apply clt_0_plus_compat.
apply c0_clt_c1.
apply cdiv_lt_0_compat_l.
assert (Hr1 : r < r++c1).
apply cplus_lt_r.
apply c0_clt_c1.
assert (Hq' := Hq (r++c1) (r++c1) Hr1 (cle_refl (r++c1))).
intuition;fail.
apply clt_0_copp; assumption.
setoid_rewrite copp_div_l.
assert (Hrr1: r<r++c1).
apply cplus_lt_r; apply c0_clt_c1.
assert (c0 < Pol_eval Q (r++c1)) by
 (elim (Hq (r++c1)(r++c1) Hrr1 (cle_refl (r++c1)));intros; assumption).
apply pos_non_c0; assumption.
setoid ring.
Qed.

Theorem Horner_step_positive :
forall a Q, a < c0 -> forall r, c0 <= r ->
  (forall x y, r < x -> x <= y -> 
           c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y) ->
  c0 < Pol_eval (Pc a + X *Q)(r++c1--a/Pol_eval Q (r++c1)).
intros a Q Halt0 r Hrpos HQincr.
assert (Hb1: r < r++c1).
apply cplus_lt_r;apply c0_clt_c1.
assert (Hb2:= cle_refl (r++c1)).
assert (HQr1 := HQincr (r++c1) (r++c1) Hb1 Hb2).
assert (Hpos' : c0 < r++c1 -- a/Pol_eval Q (r++c1)).
apply cle_lt_trans with r.
assumption.
apply Horner_step_positive_tech; assumption.

apply clt_le_trans with (a++ (r ++ c1 -- a / Pol_eval Q (r ++ c1))**
                          (Pol_eval Q (r++c1))).
setoid_replace 
  (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) ** Pol_eval Q (r ++ c1))
with
  ((r++c1)**Pol_eval Q (r++c1) ++ a --
        (Pol_eval Q (r++c1)** (a/Pol_eval Q (r++c1))));
  [idtac | setoid ring;fail].
setoid_rewrite cmul_div_r.
apply pos_non_c0;intuition.
match goal with |- _ < ?x => 
  setoid_replace x with ((r ++ c1) ** Pol_eval Q (r ++ c1));[idtac|setoid ring]
end.
apply cmul_lt_0.
apply cle_lt_trans with r; assumption.
intuition;fail.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (r ++ c1 -- a / Pol_eval Q (r ++ c1))).
apply cmul_le_compat_r.
assert (Hb3 : r++c1<=r++c1 --a/Pol_eval Q (r++c1)).
setoid_replace (r++c1 --a/Pol_eval Q (r++c1)) with
  (--(a/Pol_eval Q (r++c1))++(r++c1));[idtac |setoid ring].
apply cplus_pos_simplify; apply clt_cle_weak.
setoid_rewrite <- copp_div_l.
apply pos_non_c0; intuition; fail.
apply cdiv_lt_0_compat_l.
intuition;fail.
apply clt_0_copp; assumption.
assert (HQi' := HQincr (r++c1)(r++c1--a/Pol_eval Q (r++c1)) Hb1 Hb3).
intuition;fail.
apply clt_cle_weak; assumption.
Qed.

Theorem no_alternation_tech :
  forall Q a, a < c0 -> c0 < least_non_zero_coeff Q -> no_alternation Q ->
  c0 < c1 -- a / Pol_eval Q c1.
intros Q a Haneg Hqpos Hna.
assert (HQpos' : 0 < Pol_eval Q c1).
apply no_alternation_positive_strict.
assumption.
assumption.
apply c0_clt_c1.
apply clt_trans with (c1 ++ c0).
setoid_rewrite cadd_0_r.
apply c0_clt_c1.
setoid_replace (c1 -- a/Pol_eval Q c1) with (c1 ++ (-- (a/Pol_eval Q c1))).
apply cplus_le_lt_compat.
apply cle_refl.
setoid_rewrite <- copp_div_l.
apply pos_non_c0; assumption.
apply cdiv_lt_0_compat_l.
assumption.
apply clt_0_copp.
assumption.
setoid ring.
Qed.

Theorem alternation_here_root :
  forall Q a, a < c0 -> c0 < least_non_zero_coeff Q ->
    no_alternation Q ->
    (exists r, c0 < r /\ Pol_eval (Pc a + X * Q) r < c0 /\
      exists r2, r < r2 /\ c0 < Pol_eval (Pc a + X * Q) r2 /\
      (forall x y, r < x -> x < y ->
               Pol_eval (Pc a + X * Q) x < Pol_eval (Pc a + X * Q) y)).
intros Q a Haneg HQpos Hna.
destruct (Pol_eval_continuous (Pc a + X*Q) c0 (-- a/(c1++c1))) as [r [Hrp Hr]].
apply cdiv_lt_0_compat_l;[apply c0_clt_2 | apply clt_0_copp; assumption].
exists r.
split.
assumption.
split.
apply cle_lt_trans with (a/(c1++c1)).
setoid_replace (a/(c1++c1)) with (a ++ -- a/(c1++c1)).
pose (u:= Pol_eval (Pc a + X * Q) c0).
setoid_replace (Pol_eval (Pc a + X * Q) r) with
   (Pol_eval (Pc a + X * Q) c0 ++
   (Pol_eval (Pc a + X * Q) r -- u)).
setoid_replace (Pol_eval (Pc a + X * Q) c0) with a.
apply cplus_le_compat.
apply cle_refl.
unfold u.
assert (Hrin: --r <= r--c0 <= r).
setoid_replace (r -- c0) with r.
split.
apply cle_trans with c0.
apply copp_le_0_compat.
apply clt_cle_weak; auto.
apply clt_cle_weak; auto.
apply cle_refl.
setoid ring.
assert (Hr' := Hr r Hrin).
intuition; fail.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_X.
setoid ring.
unfold u; setoid ring.
setoid_replace (a++ --a/(c1++c1)) with (a -- a/(c1++c1)).
pose (u:= a/(c1++c1)); fold u.
setoid_rewrite (cut_half a).
unfold u; setoid ring.
setoid_rewrite copp_div_l.
apply pos_non_c0; exact c0_clt_c1.
setoid ring.
apply clt_0.
setoid_rewrite <- copp_div_l.
apply pos_non_c0; exact c0_clt_c1.
apply cdiv_lt_0_compat_l.
apply c0_clt_2.
apply clt_0_copp.
assumption.

exists (r++c1--a/Pol_eval Q (r++c1)).
assert(tech_hyp:   forall x y : Coef,
   r < x -> x <= y -> c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y).
intros x y Hx Hy.
split.
apply no_alternation_positive_strict.
assumption.
assumption.
apply clt_trans with r; assumption.
assert (Hinc := no_alternation_increasing Q (clt_cle_weak _ _ HQpos) Hna x y).
assert (c0 <= x <= y).
split;[apply cle_trans with r;apply clt_cle_weak; assumption| assumption].
intuition; fail.

split.
apply Horner_step_positive_tech.
assumption.
assumption.
split.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply clt_le_trans with (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) **
                        (Pol_eval Q (r++c1))).
setoid_replace (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) ** Pol_eval Q (r ++ c1)) with
   (a ++ ((r++c1)**Pol_eval Q (r++c1))++(Pol_eval Q (r++c1)**(--a/Pol_eval Q (r++c1)))).
assert (Hr1: c0 < r++c1).
apply clt_0_plus_compat.
assumption.
apply c0_clt_c1.
assert (H := no_alternation_positive_strict Q Hna HQpos (r++c1) Hr1).
setoid_rewrite cmul_div_r.
apply pos_non_c0; intuition;fail.

match goal with |- _ < ?u => 
   setoid_replace u with ((r++c1)**Pol_eval Q (r++c1))
end.
apply cmul_lt_0; assumption.
setoid ring.
setoid_rewrite copp_div_l.
apply pos_non_c0.
elim (tech_hyp (r++c1)(r++c1)(cplus_lt_r r c1 c0_clt_c1)(cle_refl (r++c1))).
intros; assumption.
setoid ring.
apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (r ++ c1 -- a / Pol_eval Q (r ++ c1))).
apply cmul_le_compat_r.
assert (r < r++c1) by (apply cplus_lt_r; apply c0_clt_c1).
assert (r++c1 < r++c1 -- a/Pol_eval Q (r++c1)).
setoid_replace (r ++ c1 -- a/Pol_eval Q (r++c1)) with
  ((r++c1) ++(-- a/Pol_eval Q (r++c1))).
apply cplus_lt_r.
apply cdiv_lt_0_compat_l.
apply no_alternation_positive_strict.
assumption.
assumption.
apply clt_trans with r; assumption.
apply clt_0_copp; assumption.
setoid_rewrite copp_div_l.
apply pos_non_c0.
elim (tech_hyp (r++c1)(r++c1)(cplus_lt_r r c1 c0_clt_c1)(cle_refl (r++c1))).
intros; assumption.
setoid ring.
assert (H' := tech_hyp _ _ H (clt_cle_weak _ _ H0)).
intuition;fail.
apply cle_trans with r.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply Horner_step_positive_tech.
assumption.
assumption.
intros x y Hx Hy.
repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_c.
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_X.
apply cplus_le_lt_compat.
apply cle_refl.
apply cle_lt_trans with (x**Pol_eval Q y).
repeat setoid_rewrite (cmul_sym x); apply cmul_le_compat_r.
assert (H' := tech_hyp x y Hx (clt_cle_weak _ _ Hy)); intuition; fail.
apply cle_trans with r;apply clt_cle_weak; assumption.
apply cmul_lt_compat_r.
assert (H' := tech_hyp x y Hx (clt_cle_weak _ _ Hy)).
apply clt_le_trans with (Pol_eval Q x);intuition;fail.
assumption.
Qed.

(* This is the point where we have a departure from purely constructive
 mathematics.  The statement of this polynom can still be proved in
 constructive mathematics (I think so), but it is also easy to prove
 using classical mathematics, which should make it possible to go much
 faster. *)
Axiom intermediate_value_polynom :
   forall P a b, Pol_eval P a < c0 -> c0 <= Pol_eval P b -> a < b ->
   forall eps, 0 < eps -> exists x, exists y,
        a <= x /\ x < y /\ y <= b /\ --eps < Pol_eval P x  /\
         Pol_eval P x < c0 /\ c0 <= Pol_eval P y /\ Pol_eval P y < eps /\
         y--x < eps.

Lemma cmul_n0 : forall a b, c0 < a** b -> ~a==c0.
intros a b H Heq; elim (clt_neq _ _ H).
setoid_rewrite Heq; setoid ring.
Qed.

Lemma neg_cmul_n0 :  forall a b, a ** b < c0 -> ~a==c0.
intros a b H Heq; elim (clt_neq _ _ H).
setoid_replace (a ** b) with c0.
apply ceq_refl.
setoid_rewrite Heq; setoid ring.
Qed.

Lemma cle_0 : forall a, c0 <= -- a -> a <= c0.
intros; setoid_replace c0 with (--a ++ a).
apply cplus_pos_simplify.
assumption.
setoid ring.
Qed.

Lemma cmul_neg_compat_l :
  forall a b, a <= c0 -> c0 <= b -> a**b <= c0.
intros a b Ha Hb; apply cle_0.
setoid_rewrite <- mul_copp.
apply cle_0_mult.
apply cle_0_copp; assumption.
assumption.
Qed.

Lemma cmul_neg_compat_r :  forall a b, c0 <= a -> b <= c0 -> a**b <= c0.
intros; setoid_rewrite cmul_sym; apply cmul_neg_compat_l; assumption.
Qed.

Lemma neg_cmul_neg_l : forall a b, a**b < c0 -> c0 < b -> a < c0.
intros a b Hm Hb; apply clt_0.
apply clt_decompose.
intros Habs; apply (neg_cmul_n0 _ _ Hm).
setoid_replace c0 with (--a ++ a).
setoid_rewrite <- Habs;setoid ring.
setoid ring.
apply cmul_lt_0_le_reg_r with b.
assumption.
setoid_rewrite mul_copp.
setoid_replace (c0**b) with c0.
apply cle_0_copp; apply clt_cle_weak; assumption.
setoid ring.
Qed.

Lemma neg_cmul_pos_r : forall a b, a**b < c0 -> a < c0 -> c0 < b.
intros a b Hm Hb; apply clt_decompose.
assert (b**a < c0).
setoid_rewrite cmul_sym in Hm; assumption.
intros Habs; elim (neg_cmul_n0 _ _ H);setoid_rewrite Habs;auto.
apply cmul_lt_0_le_reg_r with (--a).
apply clt_0_copp; assumption.
setoid_rewrite cmul_0_l; setoid_rewrite cmul_sym; setoid_rewrite mul_copp.
apply clt_cle_weak; apply clt_0_copp; assumption.
Qed.

Theorem increase_pol_close_0_X : 
   forall Q a r,
     c0 < r ->
     (forall x, r <= x -> c0 < Pol_eval Q x) ->
     (forall x y, r <= x -> x <= y -> Pol_eval Q x <= Pol_eval Q y) ->
     --(r**Pol_eval Q r) < Pol_eval (Pc a + X * Q) r ->
     forall x y, r <= x -> x < y -> 
        Pol_eval (X*(Pc a + X*Q)) x < Pol_eval (X*(Pc a +X*Q)) y.
intros Q a r Hr HQp HQi Hclose x y Hx Hy.
repeat (setoid_rewrite Pol_eval_mult || setoid_rewrite Pol_eval_plus ||
        setoid_rewrite Pol_eval_c || setoid_rewrite Pol_eval_X).

setoid_replace (y**(a++y**Pol_eval Q y)) with
  (x**(a++x**Pol_eval Q x) ++ 
   ((y--x)**((a++x**Pol_eval Q x)++(y**Pol_eval Q y))++
    y**x**(Pol_eval Q y --Pol_eval Q x)));[idtac |setoid ring;fail].
apply cplus_lt_r.
setoid_rewrite cadd_sym.
apply clt_0_le_lt_plus_compat.
apply cmul_le_0.
apply cmul_le_0.
apply clt_cle_weak; apply clt_trans with r.
assumption.
apply cle_lt_trans with x; assumption.
apply clt_cle_weak; apply clt_le_trans with r; assumption.
apply csub_le_0.
apply HQi.
assumption.
apply clt_cle_weak; assumption.
apply cmul_lt_0.
apply csub_lt_0; auto.
apply cle_lt_trans with (--(r**Pol_eval Q r)++r**Pol_eval Q r).
setoid_replace (-- (r ** Pol_eval Q r) ++ r ** Pol_eval Q r) with c0.
apply cle_refl.
setoid ring.
apply cplus_le_lt_compat.
apply cle_trans with (Pol_eval (Pc a + X*Q) r).
apply clt_cle_weak; assumption.
setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_c; setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cle_refl.
apply cle_trans with (r**Pol_eval Q x).
repeat setoid_rewrite (cmul_sym r).
apply cmul_le_compat_r.
apply HQi.
apply cle_refl.
assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
assumption.
apply clt_cle_weak.
apply HQp; assumption.
apply cle_lt_trans with (r**Pol_eval Q y).
repeat setoid_rewrite (cmul_sym r).
apply cmul_le_compat_r.
apply HQi.
apply cle_refl.
apply clt_cle_weak; apply cle_lt_trans with x; assumption.
apply clt_cle_weak; assumption.
apply cmul_lt_compat_r.
apply HQp.
apply clt_cle_weak; apply cle_lt_trans with x; assumption.
apply cle_lt_trans with x; assumption.
Qed.

Lemma Coef_of_N_1 : Coef_of_N 1 == c1.
replace 1%N with (1+0)%N.
setoid_rewrite Coef_of_N_S; setoid_rewrite Coef_of_N_0.
setoid ring.
auto.
Qed.

Lemma Coef_of_N_plus :
  forall n m, Coef_of_N (n + m) == Coef_of_N n ++ Coef_of_N m.
destruct n.
intros; setoid_rewrite Coef_of_N_0; 
  setoid_rewrite cadd_0_l; apply ceq_refl.
induction p.
intros m; rewrite Npos_xI_expand.
repeat rewrite <- Nplus_assoc.
repeat setoid_rewrite Coef_of_N_S.
repeat setoid_rewrite IHp.
setoid ring.
intros m; rewrite Npos_xO_expand.
repeat rewrite <- Nplus_assoc.
repeat setoid_rewrite IHp.
setoid ring.

intros m; setoid_rewrite Coef_of_N_S; setoid_rewrite Coef_of_N_1.
apply ceq_refl.
Qed.

Lemma c0_cle_Coef :
  forall n, c0 <= Coef_of_N n.
intros n; destruct n.
setoid_rewrite Coef_of_N_0.
apply cle_refl.
induction p.
rewrite Npos_xI_expand; setoid_rewrite Coef_of_N_S.
repeat setoid_rewrite Coef_of_N_plus.
repeat apply cle_0_plus.
apply c0_cle_c1.
assumption.
assumption.
rewrite Npos_xO_expand.
setoid_rewrite Coef_of_N_plus; apply cle_0_plus; assumption.
setoid_rewrite Coef_of_N_1; apply c0_cle_c1.
Qed.

Lemma c0_clt_Coef :
  forall p, c0 < Coef_of_N (Npos p).
intros p; rewrite (Npred_correct p (Npos p) (refl_equal (Npos p))).
setoid_rewrite Coef_of_N_S.
apply clt_le_trans with c1.
apply c0_clt_c1.
setoid_rewrite cadd_sym; apply cplus_pos_simplify.
apply c0_cle_Coef.
Qed.

Lemma cpow_lt_compat :
  forall x y n, n <> 0%N -> c0 < x -> x < y -> cpow x n < cpow y n.
intros x y n; case n.
intros H; elim H; auto.
intros p _; induction p.
intros; rewrite Npos_xI_expand; repeat setoid_rewrite cpow_plus.
repeat setoid_rewrite cpow_1.
assert (c0 < cpow x (Npos p)) by (apply cpow_lt_0_compat_l; assumption).
assert (IHp' := IHp H H0).
apply cmul_lt_compat.
assumption.
assumption.
apply cmul_lt_0; assumption.
apply cmul_lt_compat; assumption.
intros; rewrite Npos_xO_expand; repeat setoid_rewrite cpow_plus.
assert (c0 < cpow x (Npos p)) by (apply cpow_lt_0_compat_l; assumption).
assert (IHp' := IHp H H0).
apply cmul_lt_compat; assumption.
repeat setoid_rewrite cpow_1; auto.
Qed.

Lemma Ppred_succ : forall n, Ppred (1 + n) = n.
induction n.
simpl.
apply Pdouble_minus_one_o_succ_eq_xI.
auto.
auto.
Qed.

Lemma Npred_succ : forall n, Npred (1 + n) = n.
intros n; destruct n as [|p].
auto.
unfold Npred.
replace (1 + Npos p)%N with  (Npos (1+p));[idtac | auto].
replace (1+p)%positive with (Psucc p).
rewrite BinPos.Ppred_succ.
caseEq (Psucc p); intros;auto.
destruct p;simpl in H; discriminate.
apply Pplus_one_succ_l.
Qed.

Functional Scheme Ppred_ind := Induction for Ppred Sort Prop.
Functional Scheme Pdouble_minus_one := Induction for Ppred Sort Prop.

Lemma diff_cpow_pol_1 :
  forall x, diff_cpow_pol x 1 = P0.
intros x; rewrite diff_cpow_pol_equation; simpl; auto.
Qed.

Theorem difference_cpow :
  forall x n, (n <> 0)%N ->
    forall y,
    cpow y n -- cpow x n == (y -- x)**
    (Coef_of_N n**cpow x (Npred n)++(Pol_eval (X * (diff_cpow_pol x n)) (y--x))).
intros x n; induction n using (well_founded_ind NS_wf).
rename H into IHn.
intros Hnn0.
destruct n.
elim Hnn0; auto.
setoid_rewrite (Npred_correct p (Npos p)(refl_equal (Npos p))).
case (N_eq_dec (Npred (Npos p)) 0).
intros Hp1.
rewrite  Hp1.
rewrite diff_cpow_pol_1.
intros y.
simpl (1+0)%N.
simpl (Npred 1).
repeat setoid_rewrite cpow_1. 
setoid_rewrite cpow_0; setoid_rewrite Coef_of_N_1.
setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_c.
setoid ring.
intros Hpn1.
assert (H' := Npred_correct p (Npos p)(refl_equal (Npos p))).
destruct (Npred (Npos p)) as [ | p'].
elim Hpn1; auto.
pose (n:= Npos p').
assert (Hns : NS n (Npos p)).
setoid_rewrite H'; constructor.
setoid_rewrite (diff_cpow_pol_equation x (1 + Npos p')).
intros y.
rewrite Npred_succ.
setoid_replace (cpow y (1+Npos p')%N -- cpow x (1+Npos p'))%N with
 (y**(cpow y (Npos p') -- cpow x (Npos p'))++cpow x (Npos p')**y --
     x**(cpow x (Npos p')));[idtac | repeat (setoid_rewrite cpow_plus;
                                     setoid_rewrite cpow_1); 
                             setoid ring; fail].

setoid_rewrite IHn.
rewrite H'; constructor.
unfold n; discriminate.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_c.
set (n':= Npred (Npos p')).
replace (Npos p') with (1+(Npred (Npos p')))%N.
repeat setoid_rewrite cpow_plus.
repeat setoid_rewrite cpow_1.
fold n'.

repeat setoid_rewrite Coef_of_N_S.
set (n'':=Coef_of_N n').
set (w:=Pol_eval (diff_cpow_pol x (1+n'))(y--x)).
set (w2 := cpow x n').
setoid ring.

pattern (Npos p') at 2;
  setoid_rewrite (Npred_correct p' (Npos p') (refl_equal (Npos p'))).
auto.
Qed.

Lemma cmul_le_lt_compat :
  forall x y z t, c0 < x -> c0 <= z -> x <= y -> z < t -> x ** z < y ** t.
intros x y z t Hx Hz Hy Ht.
apply cle_lt_trans with (y**z).
apply cmul_le_compat_r; assumption.
repeat setoid_rewrite (cmul_sym y).
apply cmul_lt_compat_r.
apply clt_le_trans with x; assumption.
assumption.
Qed.

Theorem diff_cpow_pol_pos : 
  forall x y n, c0 <= x -> c0 <= y -> 
        c0 <= Pol_eval (diff_cpow_pol x n) y.
intros x y n Hx Hy; elim n using (well_founded_ind NS_wf).
clear n; intros n IHn.
rewrite (diff_cpow_pol_equation x n).
caseEq (Npred n).
intros; apply cle_refl.
intros p Hp.
assert (NS (Npos p) n).
assert (n = Npos p + 1)%N.
apply succ_Npred.
assumption.
subst n; rewrite Nplus_comm; constructor.
repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
repeat setoid_rewrite Pol_eval_c.
apply cle_0_plus.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
assumption.
apply cmul_le_0.
assumption.
apply IHn; assumption.
apply cmul_le_0.
assumption.
apply IHn; assumption.
Qed.

Theorem diff_pow_pol_incrx :
  forall n x x' y, c0 <= x -> x <= x' -> c0 <= y ->
    Pol_eval (diff_cpow_pol x n) y <= Pol_eval (diff_cpow_pol x' n) y.
intros n; elim n using (well_founded_ind NS_wf).
clear n; intros n Hrec x x' y Hx Hx' Hyc.
rewrite (diff_cpow_pol_equation x n).
rewrite (diff_cpow_pol_equation x' n).
caseEq (Npred n).
intros; apply cle_refl.
intros p Hp.
assert (NS (Npos p) n).
assert (n = Npos p + 1)%N.
apply succ_Npred.
assumption.
subst n; rewrite Nplus_comm; constructor.

repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_c.
repeat setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cplus_le_compat.
repeat setoid_rewrite (cmul_sym (Coef_of_N (Npos p))).
apply cmul_le_compat_r.
apply cpow_le_compat_l;assumption.
apply c0_cle_Coef.
apply cle_trans with (x**Pol_eval (diff_cpow_pol x' (Npos p)) y).
repeat (setoid_rewrite (cmul_sym x)).
apply cmul_le_compat_r.
apply Hrec; assumption.
assumption.
apply cmul_le_compat_r.
assumption.
apply diff_cpow_pol_pos.
apply cle_trans with x; assumption.
assumption.
repeat (setoid_rewrite (cmul_sym y)).
apply cmul_le_compat_r.
apply Hrec; assumption.
assumption.
Qed.

Theorem diff_cpow_pol_incry :
  forall x y z n, c0 <= x -> c0 <= y -> y <= z -> 
     Pol_eval (diff_cpow_pol x n) y <= Pol_eval (diff_cpow_pol x n) z.
intros x y z n Hx Hy Hz; elim n using (well_founded_ind NS_wf).
clear n; intros n IHn .
rewrite diff_cpow_pol_equation.
caseEq (Npred n).
setoid_rewrite Pol_eval_c; intros; apply cle_refl.
intros p Hp.
assert (NS (Npos p) n).
rewrite (succ_Npred p n).
rewrite Nplus_comm; constructor.
assumption.
repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_c.
repeat setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cplus_le_compat.
apply cle_refl.
repeat (setoid_rewrite (cmul_sym x)).
apply cmul_le_compat_r.
apply IHn; assumption.
assumption.
apply cle_trans with (y ** Pol_eval (diff_cpow_pol x (Npos p)) z).
repeat (setoid_rewrite (cmul_sym y)).
apply cmul_le_compat_r.
apply IHn; assumption.
assumption.
apply cmul_le_compat_r.
assumption.
apply diff_cpow_pol_pos.
assumption.
apply cle_trans with y; assumption.
Qed.

Lemma div_le_lt_r :
  forall a b c d, 0 < c -> c < b -> 0 < a -> a <= d ->
    a/b < d/c.
intros a b c d Hc Hb Ha Hd.
setoid_rewrite (cdiv_decompose a).
apply pos_non_c0; apply clt_trans with c; assumption.
setoid_rewrite (cdiv_decompose d).
apply pos_non_c0; assumption.

repeat setoid_rewrite (fun x y => cmul_sym (c1/x) y).
apply cmul_le_lt_compat.
assumption.
apply cdiv_le_0_compat_l.
apply clt_trans with c; assumption.
apply c0_cle_c1.
assumption.
apply inv_clt.
assumption.
assumption.
Qed.

Theorem copp_lt_compat : forall p q : Coef, p < q -> -- q < -- p.
intros; apply cplus_lt_reg_r with p.
apply cplus_lt_reg_r with q.
setoid_replace  (--q++p++q) with p.
setoid_replace  (--p++p++q) with q.
assumption.
setoid ring.
setoid ring.
Qed.


Theorem increase_pol_close_0_Xn : 
   forall Q a r r2 n,
     c0 < r ->
     c0 <= Pol_eval Q r ->
     (forall x, r < x -> c0 < Pol_eval Q x) ->
     (forall x y, r <= x -> x <= y -> Pol_eval Q x <= Pol_eval Q y) ->
     r < r2 ->
     c0 <= Pol_eval (Pc a + X * Q) r2 ->
     -- (cpow r n ** Pol_eval Q r) /
   (c1++Coef_of_N n ** cpow r2 (Npred n) ++
    (r2 -- r) ** Pol_eval (diff_cpow_pol r2 n) (r2 -- r)) <
   a ++ r ** Pol_eval Q r ->
     forall x y, r < x -> x < y -> 
        Pol_eval (X^n*(Pc a + X*Q)) x < Pol_eval (X^n*(Pc a +X*Q)) y.
intros Q a r r2 n Hr HQr HQp HQi Hr2 HPr2pos Hclose x y Hx Hy .
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_c.
repeat setoid_rewrite Pol_eval_pow.
repeat setoid_rewrite Pol_eval_X.

caseEq n.
intros Heq.
repeat setoid_rewrite cpow_0.
repeat setoid_rewrite cmul_1_l.
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_X.
apply cplus_le_lt_compat.
apply cle_refl.
repeat setoid_rewrite  (fun x y => cmul_sym x (Pol_eval Q y)).
apply clt_le_trans with (Pol_eval Q x ** y).
repeat setoid_rewrite (cmul_sym (Pol_eval Q x)).
apply cmul_lt_compat_r.
apply HQp; assumption.
assumption.
apply cmul_le_compat_r.
apply HQi.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply clt_trans with x.
apply clt_trans with r; assumption.
assumption.

intros p Heqp.
assert (fact : Npos p <> 0%N) by discriminate.
assert (x**Pol_eval Q x < y**Pol_eval Q y).
apply cle_lt_trans with (x**Pol_eval Q y).
repeat setoid_rewrite (cmul_sym x).
apply cmul_le_compat_r.
apply HQi.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply cmul_lt_compat_r.
apply HQp.
apply cle_lt_trans with x.
apply clt_cle_weak; assumption.
assumption.
assumption.
(* end of proof assert (x**..). *)

repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_X.
destruct (clt_le_dec (a++x**Pol_eval Q x) c0) as [Pxneg | Pxpos].

(* Start with Pxneg. *)
assert (Hxr2 : x < r2).
elim (clt_le_dec x r2).
auto.
intros Hr2x.
assert (Habs:c0 <= a++ x** Pol_eval Q x).
apply cle_trans with (1:= HPr2pos).
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cle_refl.
apply cle_trans with (x**Pol_eval Q r2).
apply cmul_le_compat_r.
assumption.
apply clt_cle_weak; apply HQp; assumption.
repeat setoid_rewrite (cmul_sym x).
apply cmul_le_compat_r.
apply HQi.
apply clt_cle_weak; assumption.
assumption.
apply clt_cle_weak; apply clt_trans with r; assumption.
elim (pos_non_c0 c0).
apply cle_lt_trans with (1:= Habs); assumption.
apply ceq_refl.

destruct (clt_le_dec c0 (a++y**Pol_eval Q y)) as [Pypos|Pyneg].
apply cle_lt_trans with c0.
apply cmul_neg_compat_r.
apply cpow_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply clt_cle_weak; assumption.
apply cmul_lt_0.
apply cpow_lt_0_compat_l.
apply clt_trans with x.
apply clt_trans with r; assumption.
assumption.
assumption.
(* start the case with both P x and P y negative. *)
assert (Hyr2 : y <= r2).
elim (clt_le_dec r2 y).
intros Hr2y.
assert (Habs:c0 < a++ y** Pol_eval Q y).
apply cle_lt_trans with (1:= HPr2pos).
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_X.
apply cplus_le_lt_compat.
apply cle_refl.
repeat setoid_rewrite (fun a b => cmul_sym a (Pol_eval Q b)).
apply cmul_le_lt_compat.
apply HQp.
assumption.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply HQi; apply clt_cle_weak; assumption.
assumption.
elim (pos_non_c0 c0).
apply clt_le_trans with (1:= Habs); assumption.
apply ceq_refl.
auto.

setoid_replace (cpow y (Npos p) ** (a ++ y **Pol_eval Q y))
with (cpow x (Npos p)**(a++x**Pol_eval Q x) ++
      ((cpow y (Npos p)--cpow x (Npos p))**
       (a++x**Pol_eval Q x)++cpow y (Npos p)**
       (y**Pol_eval Q y--x**Pol_eval Q x)));[idtac|setoid ring;fail].
apply cplus_lt_r.
setoid_rewrite difference_cpow.
assumption.
rewrite <- Heqp.
setoid_replace
  ( (y -- x) ** (Coef_of_N n ** cpow x (Npred n) ++
    Pol_eval (X * (diff_cpow_pol x n)) (y -- x)) ** (a ++ x ** Pol_eval Q x) ++
   cpow y n ** (y ** Pol_eval Q y -- x ** Pol_eval Q x)) with
  ((y--x)**((Coef_of_N n ** cpow x (Npred n) ++
    Pol_eval (X * (diff_cpow_pol x n)) (y -- x)) ** (a ++ x ** Pol_eval Q x) ++
    cpow y n**Pol_eval Q y)++cpow y n ** x**(Pol_eval Q y -- Pol_eval Q x));
  [idtac | setoid ring;fail].
setoid_rewrite cadd_sym.
apply clt_0_le_lt_plus_compat.
apply cmul_le_0.
apply cmul_le_0.
apply cpow_pos.
apply clt_cle_weak; apply clt_le_trans with x.
apply clt_trans with r; assumption.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0.
apply HQi.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply cmul_lt_0.
apply csub_lt_0.
assumption.

setoid_rewrite cadd_sym.
apply clt_le_trans with (cpow y n ** Pol_eval Q y ++
   (Coef_of_N n ** cpow x (Npred n) ++
    Pol_eval (X * diff_cpow_pol x n) (y -- x))**(a++r**Pol_eval Q r)).
apply clt_trans with (cpow r n** Pol_eval Q r ++
      ((Coef_of_N n ** cpow x (Npred n) ++
    Pol_eval (X * diff_cpow_pol x n) (y -- x)) ** (a ++ r ** Pol_eval Q r))).
apply clt_le_trans with
   (cpow r n ** Pol_eval Q r ++
   (Coef_of_N n ** cpow r2 (Npred n) ++
    Pol_eval (X * diff_cpow_pol r2 n) (r2--r)) ** (a ++ r ** Pol_eval Q r)).
match goal with |- _ < ?a ++ ?b  =>
   apply cle_lt_trans with (a ++ --a)
end.
match goal with |- _ <= ?b ++ -- ?b => setoid_replace (b++ --b) with c0;
  [apply cle_refl | setoid ring] end.
apply cplus_le_lt_compat; [apply cle_refl | idtac].
setoid_rewrite <- (cmul_sym (a++r**Pol_eval Q r)).
setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_X.
apply clt_div_mul.
setoid_rewrite cadd_sym.
apply clt_0_le_lt_plus_compat.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
apply cmul_lt_0.
setoid_rewrite Heqp.
 apply c0_clt_Coef.
apply cpow_lt_0_compat_l.
apply clt_trans with r; assumption.
apply cle_lt_trans with (2:= Hclose).
assert (Htech: c0 <
   Coef_of_N n ** cpow r2 (Npred n) ++
   (r2 -- r) ** Pol_eval (diff_cpow_pol r2 n) (r2 -- r)).
setoid_rewrite cadd_sym.
apply clt_0_le_lt_plus_compat.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply cmul_lt_0.
setoid_rewrite Heqp; apply c0_clt_Coef.
apply cpow_lt_0_compat_l.
apply clt_trans with r; assumption.
(* end of Htech *)
repeat setoid_rewrite copp_div_l.
apply pos_non_c0.
apply Htech.
apply pos_non_c0.
setoid_rewrite <- cadd_assoc.
apply clt_0_plus_compat.
apply c0_clt_c1.
assumption.

apply copp_le_compat.
apply cle_div_r.
apply cmul_le_0.
apply cpow_pos.
apply clt_cle_weak; assumption.
exact HQr.
apply cplus_lt_0_le_lt.
apply cmul_lt_0.
rewrite Heqp; apply c0_clt_Coef.
apply cpow_lt_0_compat_l.
apply clt_trans with r; assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
setoid_rewrite <- (cadd_assoc c1).
setoid_rewrite (cadd_sym c1).
setoid_rewrite <- (cadd_sym c1); apply cplus_pos_simplify.
apply c0_cle_c1.
apply cplus_le_compat.
apply cle_refl.
apply cle_copp_prem.
repeat setoid_rewrite <- cmul_copp_r.
apply cmul_le_compat_r.
apply cplus_le_compat.
repeat (setoid_rewrite (cmul_sym  (Coef_of_N n))).
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply clt_cle_weak; assumption.
apply c0_cle_Coef.
repeat (setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_X).
apply cle_trans with ((y--x)**Pol_eval (diff_cpow_pol r2 n) (r2--r)).
repeat setoid_rewrite (cmul_sym (y--x)).
apply cmul_le_compat_r.
apply cle_trans with (Pol_eval (diff_cpow_pol x n) (r2--r)).
apply diff_cpow_pol_incry.
apply clt_cle_weak;apply clt_trans with r; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
setoid_replace (y -- x) with (y ++ -- x).
setoid_replace (r2 -- r) with (r2 ++ -- r).
apply cplus_le_compat.
assumption.
apply copp_le_compat.
apply clt_cle_weak; assumption.
setoid ring.
setoid ring.
apply diff_pow_pol_incrx.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply clt_cle_weak; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
setoid_replace (y -- x) with (y ++ -- x).
setoid_replace (r2 -- r) with (r2 ++ -- r).
apply cplus_le_compat.
assumption.
apply copp_le_compat.
apply clt_cle_weak; assumption.
setoid ring.
setoid ring.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
assert (HPrneg : a++r**Pol_eval Q r <= 0).
apply cle_trans with (a++x**Pol_eval Q x).
apply cplus_le_compat.
apply cle_refl.
apply cle_trans with (r**Pol_eval Q x).
repeat setoid_rewrite (cmul_sym r).
apply cmul_le_compat_r.
apply HQi.
apply cle_refl.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply HQp.
assumption.
apply clt_cle_weak; exact Pxneg.

setoid_replace c0 with (--c0).
apply copp_le_compat; exact HPrneg.
setoid ring.
setoid_rewrite (cadd_sym (cpow r n ** Pol_eval Q r)).
setoid_rewrite (cadd_sym (cpow y n ** Pol_eval Q y)).
apply cplus_le_lt_compat.
apply cle_refl.
destruct (clt_le_dec c0 (Pol_eval Q r)) as [HQrpos | HQrneg].
repeat setoid_rewrite (fun a b => cmul_sym a (Pol_eval Q b)).
apply cmul_le_lt_compat.
assumption.
apply cpow_pos.
apply clt_cle_weak; assumption.
apply HQi.
apply cle_refl.
apply clt_cle_weak; apply clt_trans with x; assumption.
apply cpow_lt_compat.
rewrite Heqp;discriminate.
assumption.
apply clt_trans with x; assumption.
apply cle_lt_trans with c0.
apply cmul_neg_compat_r.
apply cpow_pos; apply clt_cle_weak; assumption.
assumption.
apply cmul_lt_0.
apply cpow_lt_0_compat_l.
apply clt_trans with r.
assumption.
apply clt_trans with x; assumption.
apply HQp; apply clt_trans with x; assumption.

apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (Coef_of_N n ** cpow x (Npred n) ++
    Pol_eval (X * diff_cpow_pol x n) (y -- x))).
apply cmul_le_compat_r.
apply cplus_le_compat.
apply cle_refl.
apply cle_trans with (r**Pol_eval Q x).
repeat setoid_rewrite (cmul_sym r).
apply cmul_le_compat_r.
apply HQi.
apply cle_refl.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply HQp.
assumption.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.

(* Start with Pxpos *)

apply clt_trans with (cpow x (Npos p)**(a++y**Pol_eval Q y)).
repeat setoid_rewrite (cmul_sym (cpow x (Npos p))).
apply cmul_lt_compat_r.
apply cpow_lt_0_compat_l.
apply clt_trans with r; assumption.
apply cplus_le_lt_compat.
apply cle_refl.
assumption.

apply cmul_lt_compat_r.
apply cle_lt_trans with (1:= Pxpos).
apply cplus_le_lt_compat.
apply cle_refl.
assumption.
apply cpow_lt_compat.
discriminate.

apply clt_trans with r; assumption.
assumption.
Qed.

Lemma copp_lt_0_compat :  forall a, c0 < a -> copp a < c0.
intros a Ha.
setoid_replace (-- a) with (-- a++c0).
set (u:= --a++c0).
setoid_replace c0 with (-- a ++ a).
unfold u.
apply cplus_le_lt_compat.
apply cle_refl.
assumption.
setoid ring.
setoid ring.
Qed.

Lemma cplus_neg_lt_le_compat :
  forall a b, a < c0 -> b <= c0 -> a++b < c0.
intros a b Ha Hb.
setoid_rewrite <- (copp_copp (a++b)).
apply copp_lt_0_compat.
setoid_replace (--(a++b)) with (--b ++ -- a).
apply clt_0_le_lt_plus_compat.
apply cle_0_copp.
assumption.
apply clt_0_copp.
assumption.
setoid ring.
Qed.

Lemma cmul_le_neg_r :
  forall x y, c0 <= x -> y <= 0 -> x**y<= c0.
intros x y Hx Hy.
setoid_rewrite <- (copp_copp (x**y)).
setoid_rewrite <- cmul_copp_r.
apply copp_le_0_compat.
apply cmul_le_0.
assumption.
apply cle_0_copp; assumption.
Qed.

Lemma copp_clt_compat : forall a b, a < b -> -- b < -- a.
intros; setoid_replace (--a) with (-- b ++ (b -- a)).
apply cplus_lt_r.
apply csub_lt_0.
assumption.
setoid ring.
Qed.

Lemma cplus_lt_0_neg:
  forall a b, a < c0 -> b < c0 -> a++b < c0.
intros.
apply cplus_neg_lt_le_compat.
assumption.
apply clt_cle_weak; assumption.
Qed.

Lemma clt_mul_div :
  forall a b c, c0 < a -> a**b < c -> b < c/a.
intros; apply cmul_lt_0_lt_reg_r with a.
assumption.
setoid_rewrite (cmul_sym (c/a)).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_sym; assumption.
Qed.

Lemma clt_div_mul_l : forall a b c, c0 < c -> a < b/c -> c**a < b.
intros a b c Hc Ha.
apply cmul_lt_0_lt_reg_r with (c1/c).
apply cdiv_lt_0_compat_l.
assumption.
apply c0_clt_c1.
setoid_rewrite (cmul_sym b).
setoid_rewrite <- cdiv_decompose.
apply pos_non_c0; assumption.
setoid_rewrite (cmul_sym c).
setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r; assumption.
Qed.

Lemma cmul_le_compat_neg_r :
  forall a b c, c <= c0 -> b <= a -> a ** c <= b ** c.
intros; setoid_rewrite <- (copp_copp (a**c)); 
  setoid_rewrite <- (copp_copp (b**c)).
apply copp_le_compat.
repeat setoid_rewrite <- cmul_copp_r.
apply cmul_le_compat_r.
assumption.
apply cle_0_copp;assumption.
Qed.

Lemma cmul_lt_compat_neg_r :
  forall a b c, c < c0 -> b < a -> a ** c < b ** c.
intros; setoid_rewrite <- (copp_copp (a**c)); 
  setoid_rewrite <- (copp_copp (b**c)).
apply copp_clt_compat.
repeat setoid_rewrite <- cmul_copp_r.
apply cmul_lt_compat_r.
apply clt_0_copp;assumption.
assumption.
Qed.

Lemma cdiv_lt_0 :
  forall a b,  a < c0 -> c0 < b -> a/b < c0.
intros a b Ha Hb.
setoid_rewrite cdiv_decompose.
apply pos_non_c0; assumption.
apply cmul_lt_neg_r.
apply cdiv_lt_0_compat_l.
assumption.
apply c0_clt_c1.
assumption.
Qed.

Definition coef2 := c1++c1.

Theorem c0_lt_2 : c0 < coef2.
exact c0_clt_2.
Qed.

Theorem half_div_smaller : forall x y, c0 < x -> c0 < y ->
    c0 < x/(coef2**y) /\ x/(coef2**y) < x/y.
intros x y Hx Hy.
assert (c0 < coef2 ** y).
apply cmul_lt_0.
apply c0_lt_2.
assumption.
split.
apply cmul_lt_0_lt_reg_r with (coef2**y).
assumption.
setoid_rewrite cmul_0_l.
setoid_rewrite <- (cmul_sym (coef2 ** y)).
setoid_rewrite cmul_div_r.
apply pos_non_c0.
assumption.
assumption.
apply cmul_lt_0_lt_reg_r with (coef2**y).
assumption.
setoid_rewrite <- (cmul_sym (coef2 ** y)).
setoid_rewrite cmul_div_r.
apply pos_non_c0.
assumption.
apply cmul_lt_0_lt_reg_r with y.
assumption.
setoid_replace ( x / y ** (coef2 ** y) ** y) with ((coef2**y)**(y**(x/y))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
unfold coef2.
setoid_replace ((c1++c1)**y**x) with ( x**y ++ x**y).
apply cplus_lt_r.
apply cmul_lt_0; assumption.
setoid ring.
setoid ring.
Qed.

Theorem cle_div_mul_l :
  forall a b c,   c0 < c -> a <= b/c -> c ** a <= b.
intros a b c Hc Hdiv.
apply cmul_lt_0_le_reg_r with (c1/c).
apply cdiv_lt_0_compat_l.
assumption.
apply c0_clt_c1.
setoid_rewrite (cmul_sym b).
setoid_rewrite <- cdiv_decompose.
apply pos_non_c0; assumption.
setoid_replace (c**a**(c1/c)) with (a** (c**(c1/c))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r; assumption.
setoid ring.
Qed.

Lemma clt_div_r :
  forall a b c, c0 < a -> c0 < c -> c < b ->
   a/b < a/c.
intros a b c Ha Hb Hc.
repeat setoid_rewrite (cdiv_decompose a).
apply pos_non_c0; apply clt_trans with c; assumption.
apply pos_non_c0; assumption.
apply cmul_lt_compat_r.
assumption.
apply inv_clt; assumption.
Qed.


Theorem one_alternation_root_main :
  forall P, one_alternation P -> least_non_zero_coeff P < c0 ->
  forall eps, c0 < eps -> 
  exists a, exists b, c0 < a /\ a < b /\
      --eps < Pol_eval P a /\ Pol_eval P a < c0 /\ c0 <= Pol_eval P b /\
      Pol_eval P b < eps /\
      (forall x, c0 < x -> x < a -> Pol_eval P x < c0) /\
      (forall x, b < x -> c0 < Pol_eval P x) /\
      (forall x y, a < x -> x < y -> Pol_eval P x < Pol_eval P y).
intros P H; induction H.
intros HlnP eps Hp.
assert (Han:~a==0) by (apply (neg_cmul_n0 _ _ c)).
assert (Hal : least_non_zero_coeff P == a) by 
 exact (least_non_zero_P4 P a n P1 p Han).
assert (Haneg : a < c0) by (setoid_rewrite <- Hal; assumption).
assert (Hlqp : c0 < least_non_zero_coeff P1)
  by (apply neg_cmul_pos_r with a; assumption).
destruct (alternation_here_root P1 a Haneg Hlqp n0) as
  [r [Hrp [HPrn [r2 [Hrr2 [HPr2p HPincr]]]]]].
assert (HPr2p' := clt_cle_weak _ _ HPr2p).
assert (Hfpos : c0 < c1++Coef_of_N n ** cpow r2 (Npred n) ++
          (r2 -- r) ** Pol_eval (diff_cpow_pol r2 n) (r2 -- r)).
setoid_rewrite <- (cadd_assoc c1);
setoid_rewrite (cadd_sym c1); apply clt_0_le_lt_plus_compat.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply cmul_le_0.
apply csub_le_0; apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
apply c0_clt_c1.

assert (Hex' : exists eps',
          0 < eps' /\ eps' <= eps/(cpow r2 n) /\
         eps' <=
         cpow r n ** Pol_eval P1 r /
           (c1++Coef_of_N n ** cpow r2 (Npred n) ++
            (r2 -- r) ** Pol_eval (diff_cpow_pol r2 n) (r2 -- r))).
destruct (clt_le_dec  (eps/cpow r2 n)(cpow r n ** Pol_eval P1 r /
           (c1++Coef_of_N n ** cpow r2 (Npred n) ++
            (r2 -- r) ** Pol_eval (diff_cpow_pol r2 n) (r2 -- r)))) as
  [Helt | Hflt].
exists (eps/cpow r2 n).
split.
apply cdiv_lt_0_compat_l.
apply cpow_lt_0_compat_l.
apply clt_trans with r; assumption.
assumption.
split.
apply cle_refl.
apply clt_cle_weak; assumption.
exists (cpow r n ** Pol_eval P1 r /
          (c1++Coef_of_N n ** cpow r2 (Npred n) ++
           (r2--r) ** Pol_eval (diff_cpow_pol r2 n) (r2--r))).
split.
apply cdiv_lt_0_compat_l.
exact Hfpos.
apply cmul_lt_0.
apply cpow_lt_0_compat_l.
assumption.
apply no_alternation_positive_strict; assumption.
split.
assumption.
apply cle_refl.
destruct Hex' as [eps' [Heps'1 Heps'2]].
destruct (intermediate_value_polynom (Pc a +X*P1) r r2 HPrn HPr2p' Hrr2 
            eps' Heps'1) as 
            [v1 [v2 [Hv1 [Hv2 [Hv2r2 [HPv1l [HPv1u [HPv2l 
            [HPv2u Hdiff]]]]]]]]].
exists v1.
exists v2.
assert (Hv1p : c0 < v1) by (apply clt_le_trans with r; intuition; fail).
assert (Hv2p : c0 < v2) by 
   (apply clt_le_trans with v1;[assumption|apply clt_cle_weak; assumption]).
assert (Hden1 : n<>0%N -> c0 < Coef_of_N n ** cpow v2 (Npred n) ++
    (v2 -- v1) ** Pol_eval (diff_cpow_pol v2 n) (v2 -- v1)).
intros n_non_0.
apply cplus_lt_0_le_lt.
apply cmul_lt_0.
apply clt_le_trans with c1.
apply c0_clt_c1.
destruct n as [ | p'].
elim n_non_0; reflexivity.
rewrite (Npred_correct p' (Npos p')).
  setoid_rewrite Coef_of_N_S.
setoid_rewrite cadd_sym.
apply cplus_pos_simplify.
apply c0_cle_Coef.
reflexivity.


apply cpow_lt_0_compat_l.
assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
assert(Hfr2fv2 : n<> 0%N -> -- (cpow v1 n ** Pol_eval P1 v1) /
   (c1++Coef_of_N n ** cpow v2 (Npred n) ++
    (v2 -- v1) ** Pol_eval (diff_cpow_pol v2 n) (v2 -- v1)) <=
   -- (cpow r n ** Pol_eval P1 r) /
   (c1++Coef_of_N n ** cpow r2 (Npred n) ++
    (r2 -- r) ** Pol_eval (diff_cpow_pol r2 n) (r2 -- r))).
intros n_non_0.
setoid_rewrite (cdiv_decompose (--(cpow v1 n** Pol_eval P1 v1))).
setoid_rewrite <- (cadd_assoc c1).
apply pos_non_c0; apply clt_0_plus_compat.
apply c0_clt_c1.
apply Hden1; assumption.
setoid_rewrite (cdiv_decompose (--(cpow r n** Pol_eval P1 r))).
setoid_rewrite <- (cadd_assoc c1); setoid_rewrite (cadd_sym c1);
apply pos_non_c0; apply clt_0_le_lt_plus_compat.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply c0_clt_c1.
apply cle_trans with ( c1 /
   (c1++Coef_of_N n ** cpow v2 (Npred n) ++
    (v2 -- v1) ** Pol_eval (diff_cpow_pol v2 n) (v2 -- v1))** -- (cpow r n ** Pol_eval P1 r)).
repeat setoid_rewrite (fun x y => (cmul_sym (c1/x) y)).
apply cmul_le_compat_r.
apply copp_le_compat.
apply cle_trans with (cpow r n** Pol_eval P1 v1).
repeat setoid_rewrite (cmul_sym (cpow r n)).
apply cmul_le_compat_r.
apply no_alternation_increasing'.
apply clt_cle_weak; assumption.
assumption.
split.
apply clt_cle_weak; assumption.
assumption.
apply cpow_pos; apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
assumption.
apply no_alternation_positive.
assumption.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply clt_le_trans with r; assumption.
apply cdiv_le_0_compat_l.
setoid_rewrite <- (cadd_assoc c1).
apply clt_0_plus_compat.
apply c0_clt_c1.
exact (Hden1 n_non_0).
apply c0_cle_c1.
repeat setoid_rewrite cmul_copp_r.
apply copp_le_compat.
apply cmul_le_compat_r.
apply inv_cle.
setoid_rewrite <- (cadd_assoc c1).
apply clt_0_plus_compat.
apply c0_clt_c1.
exact (Hden1 n_non_0).
apply cplus_le_compat.
repeat setoid_rewrite (cmul_sym (Coef_of_N n)).
apply cplus_le_compat.
apply cle_refl.
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
assumption.
apply c0_cle_Coef.
apply cle_trans with ( (v2 -- v1)** Pol_eval (diff_cpow_pol r2 n) (r2 -- r)).
repeat setoid_rewrite (cmul_sym (v2--v1)).
apply cmul_le_compat_r.
apply cle_trans with (Pol_eval (diff_cpow_pol v2 n)(r2--r)).
apply diff_cpow_pol_incry.
apply clt_cle_weak; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
setoid_replace (v2--v1) with (v2++ -- v1).
setoid_replace (r2 -- r) with (r2++ -- r).
apply cplus_le_compat.
assumption.
apply copp_le_compat; assumption.
setoid ring.
setoid ring.
apply diff_pow_pol_incrx.
apply clt_cle_weak; assumption.
assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
setoid_replace (v2--v1) with (v2++ -- v1).
setoid_replace (r2 -- r) with (r2++ -- r).
apply cplus_le_compat.
assumption.
apply copp_le_compat; assumption.
setoid ring.
setoid ring.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
apply cmul_le_0.
apply cpow_pos.
apply clt_cle_weak; assumption.
apply no_alternation_positive.
assumption.
apply clt_cle_weak;assumption.
apply clt_cle_weak; assumption.
split.
assumption.
split.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_0_lt_reg_r with (c1/cpow v1 n).
apply clt_0_inv_pow; assumption.
setoid_rewrite (cmul_sym (--eps)).
setoid_rewrite <- cdiv_decompose.
apply pos_non_c0;apply cpow_lt_0_compat_l; assumption.
setoid_rewrite copp_div_l.
apply pos_non_c0.
apply cpow_lt_0_compat_l; assumption.
apply cle_lt_trans with (--(eps/cpow r2 n)).
apply cle_opp_div_r.
apply clt_cle_weak; assumption.
apply cpow_lt_0_compat_l; assumption.
apply cpow_le_compat_l.
apply clt_cle_weak; auto.
apply clt_cle_weak; apply clt_le_trans with v2; assumption.
setoid_rewrite (cmul_sym (cpow v1 n)); setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply cpow_lt_0_compat_l; assumption.
setoid_rewrite cmul_1_r.
apply cle_lt_trans with (copp eps').
apply copp_le_compat.
intuition.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_neg_r.
apply cpow_lt_0_compat_l; assumption.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_le_0.
apply cpow_pos;apply clt_cle_weak; assumption.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_0_lt_reg_r with (c1/cpow v2 n).
apply clt_0_inv_pow; assumption.
setoid_rewrite (cmul_sym eps).
setoid_rewrite <- cdiv_decompose.
apply pos_non_c0;apply cpow_lt_0_compat_l; assumption.
apply clt_le_trans with (eps/cpow r2 n).
setoid_rewrite (cmul_sym (cpow v2 n)); setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply cpow_lt_0_compat_l; assumption.
setoid_rewrite cmul_1_r.
apply clt_le_trans with eps'.
assumption.
intuition.
apply cle_div_r.
apply clt_cle_weak; assumption.
apply cpow_lt_0_compat_l; assumption.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
assumption.
split.
intros x Hxp Hx.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_neg_r.
apply cpow_lt_0_compat_l; assumption.
apply clt_trans with (2:= HPv1u).
repeat (setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_c).
repeat setoid_rewrite (cadd_sym a).
apply cplus_lt_compat_r.
repeat (setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_X).
apply cmul_lt_le_compat.
assumption.
apply no_alternation_positive_strict; assumption.
assumption.
apply no_alternation_increasing'.
apply clt_cle_weak; assumption.
assumption.
split; apply clt_cle_weak; assumption.
split.
intros x Hx.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_0.
apply cpow_lt_0_compat_l; apply clt_trans with v2; assumption.
apply cle_lt_trans with (Pol_eval (Pc a + X*P1) v2).
assumption.
apply HPincr.
apply cle_lt_trans with v1; assumption.
assumption.
intros x y Hx Hy.
destruct (N_eq_dec n 0) as [n_eq_0 | n_non_0].
setoid_rewrite p.
rewrite n_eq_0.
repeat setoid_rewrite Pol_eval_mult; 
repeat setoid_rewrite Pol_eval_pow.
repeat setoid_rewrite cpow_0.
repeat setoid_rewrite cmul_1_l.
apply HPincr.
apply cle_lt_trans with v1; assumption.
assumption.

setoid_rewrite p.
apply increase_pol_close_0_Xn with (r:= v1)(r2:= v2).
assumption.
apply clt_cle_weak; apply no_alternation_positive_strict; assumption.
intros.
apply no_alternation_positive_strict.
assumption.
assumption.
apply clt_trans with v1; assumption.
intros; apply no_alternation_increasing'.
apply clt_cle_weak; assumption.
assumption.
split.
apply clt_cle_weak; apply clt_le_trans with v1; assumption.
assumption.
assumption.
assumption.
apply cle_lt_trans with (1:= Hfr2fv2 n_non_0).
apply cle_lt_trans with (--eps').
setoid_rewrite copp_div_l.
apply pos_non_c0.
setoid_rewrite <- cadd_assoc.
setoid_rewrite (cadd_sym c1).
apply clt_0_le_lt_plus_compat.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r; assumption.
apply csub_le_0; apply clt_cle_weak; assumption.
apply c0_clt_c1.

apply copp_le_compat.
intuition.
generalize HPv1l; setoid_rewrite Pol_eval_plus;
setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_c;
setoid_rewrite Pol_eval_X; auto; fail.
assumption.
assumption.

intros Hlnz eps Hp.
assert (Han : ~a==c0).
apply (cmul_n0 _ _ c).
assert (Hal := least_non_zero_P4 P _ _ _ p  Han).
assert (Haneg : a < c0).
setoid_rewrite <- Hal; assumption.

assert (HP1l : least_non_zero_coeff P1 < c0).
apply clt_0.
apply neg_cmul_pos_r with a.
setoid_rewrite cmul_sym; setoid_rewrite mul_copp.
apply clt_0; setoid_rewrite copp_copp; setoid_rewrite cmul_sym; assumption.
assumption.
destruct (IHone_alternation HP1l c1 c0_clt_c1) as 
  [raux [raux2 [raux_pos [raux2_pos [_ [Praux_neg 
    [Praux2_pos [_ [Pauxneg [Pauxpos Pauxinc]]]]]]]]]]; 
clear IHone_alternation.
assert (Hbp1_pos : c0 < -- a/(raux2)).
apply cdiv_lt_0_compat_l.
apply clt_trans with raux; assumption.
apply clt_0_copp; exact Haneg.
destruct (intermediate_value_polynom P1 raux raux2 Praux_neg Praux2_pos 
      raux2_pos (--a/(raux2)) Hbp1_pos) as
  [r [r3 [Hrauxr [Hrr3 [Hr3raux2 [_
    [HP1rneg [HP1r3pos [HP1r3close _]]]]]]]]].
assert (Hr2 :exists r2, r < r2 /\ c0 < Pol_eval P1 r2 /\
         r2 ** Pol_eval P1 r2 < -- a).
destruct (ceq_dec c0 (Pol_eval P1 r3)) as [HPr3c0 | HPr3nc0].
elim (Pol_eval_continuous P1 r3 (-- a/(c1++coef2**r3))).
intros delta [Hdpos Hallclose].
assert (Hdelta : exists delta', c0 < delta' /\ delta' <= r3 /\
         delta' <= delta).
destruct (clt_le_dec delta r3) as [Hdr3 | Hr3d].
exists delta.
split.
assumption.
split.
apply clt_cle_weak; assumption.
apply cle_refl.
exists r3.
split.
apply clt_trans with r.
apply clt_le_trans with raux; assumption.
assumption.
split.
apply cle_refl.
assumption.
destruct Hdelta as [delta' [Hdelta'p [Hdelta'r3 Hdelta']]].
exists (r3++delta'); split.
apply clt_trans with r3.
assumption.
apply cplus_lt_r.
assumption.
split.
setoid_rewrite HPr3c0.
apply Pauxinc.
apply cle_lt_trans with r; assumption.
apply cplus_lt_r; assumption.
destruct (Hallclose (r3++delta)) as [_ Hinf].
setoid_replace (r3++delta--r3) with delta.
split.
apply cle_trans with c0.
apply copp_le_0_compat; apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply cle_refl.
setoid ring.
generalize Hinf.
setoid_replace ( Pol_eval P1 (r3 ++ delta) -- Pol_eval P1 r3) with
  (Pol_eval P1 (r3++delta)).
intros Hinf'.
assert (c0 < r3++delta').
apply clt_trans with r3.
apply clt_trans with r.
apply clt_le_trans with raux; assumption.
assumption.
apply cplus_lt_r.
assumption.
apply clt_div_mul_l.
assumption.
apply cle_lt_trans with (-- a/(c1++coef2**r3)).
apply cle_trans with (2:= Hinf').
destruct (ceq_dec delta' delta) as [Hdd'| Hdnd'].
setoid_rewrite Hdd'; apply cle_refl.
apply clt_cle_weak; apply Pauxinc.
apply clt_trans with r3.
apply cle_lt_trans with r; assumption.
apply cplus_lt_r; assumption.
apply cplus_le_lt_compat.
apply cle_refl.
apply clt_decompose; assumption.
apply clt_div_r.
apply clt_0_copp.
apply Haneg.
assumption.
setoid_replace (coef2**r3) with (r3++r3).
setoid_replace (c1++(r3++r3)) with (r3 ++ (r3++c1)).
apply cplus_le_lt_compat.
apply cle_refl.
apply cle_lt_trans with r3.
assumption.
apply cplus_lt_r.
apply c0_clt_c1.
setoid ring.
unfold coef2; setoid ring.
setoid_rewrite <- HPr3c0; setoid ring.
apply cdiv_lt_0_compat_l.
apply clt_0_plus_compat.
apply c0_clt_c1.
apply cmul_lt_0.
apply c0_lt_2.
apply clt_trans with r.
apply clt_le_trans with raux; assumption.
assumption.
apply clt_0_copp.
assumption.

exists r3.
split.
assumption.
split.
apply clt_decompose; assumption.
apply clt_div_mul_l.
apply clt_trans with r.
apply clt_le_trans with raux; assumption.
assumption.
apply clt_le_trans with (1:= HP1r3close).
apply cle_div_r.
apply cle_0_copp.
apply clt_cle_weak; apply Haneg.
apply clt_trans with r.
apply clt_le_trans with raux; assumption.
assumption.
assumption.
(* end of assert Hr2 *)


destruct Hr2 as
  [r2 [Hrr2 [HP1r2pos HP1r2close]]].
clear r3 Hrr3 Hr3raux2 HP1r3pos HP1r3close.

assert (Hrpos : c0 < r).

apply clt_le_trans with raux; assumption.

assert (Hr2pos : c0 < r2).
apply clt_trans with r; assumption.
set (u := r2++c1 -- a/Pol_eval P1(r2++c1)).
cut (exists eps',
               0 < eps' /\
               eps' <= eps/\
               eps' <= (cpow r n ** Pol_eval P1 r2)/
               (c1++Coef_of_N n ** cpow u (Npred n) ++
               (u -- r2)**Pol_eval (diff_cpow_pol u n) (u--r2))**
               cpow r2 n );
  [intros Hex' | idtac].
destruct Hex' as [eps' Heps'].
assert (Hr2pos' : c0 <= r2).
apply clt_cle_weak; apply clt_trans with r; intuition;fail.
assert (Hincr_above_r2 : forall x y, r2 < x -> x<= y -> c0 < Pol_eval P1 x /\
          Pol_eval P1 x <= Pol_eval P1 y).
assert (Hinc : forall x y, r < x -> x < y -> Pol_eval P1 x < Pol_eval P1 y).
intros; apply Pauxinc.
apply cle_lt_trans with r; assumption.
assumption.
(* end of assert Hinc. *)

intros x y Hx Hy; split.
apply cle_lt_trans with (Pol_eval P1 r2).
apply clt_cle_weak; intuition; fail.
apply Hinc; intuition;fail.
case (ceq_dec x y).
intros Hxy; setoid_rewrite Hxy; apply cle_refl.
intros Hxny.
apply clt_cle_weak; apply Hinc.
apply clt_trans with r2; intuition; fail.
apply clt_decompose; assumption.
assert (Hexpos := Horner_step_positive a P1 Haneg r2 Hr2pos' Hincr_above_r2).
clear Hr2pos' Hincr_above_r2.
assert (HPr2neg : Pol_eval P r2 < c0).
setoid_rewrite p.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_pow.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply cmul_lt_neg_r.
apply cpow_lt_0_compat_l.
intuition;fail.
setoid_replace c0 with (a++--a).
apply cplus_le_lt_compat.
apply cle_refl.
exact HP1r2close.
setoid ring.
(* end of assert HPr2neg *)

assert (Hpos : forall x : Coef, r2 < x -> c0 < Pol_eval P1 x).
intros; apply clt_trans with (Pol_eval P1 r2).
intuition;fail.
apply Pauxinc.
apply cle_lt_trans with r; assumption.
assumption.

assert (Hr2u : r2 < u).
apply clt_trans with (r2++c1).
apply cplus_lt_r.
apply c0_clt_c1.
unfold u.
setoid_replace (r2 ++ c1 -- a / Pol_eval P1 (r2 ++ c1)) with
   (r2++c1 ++ -- (a/Pol_eval P1(r2++c1))).
apply cplus_lt_r.
setoid_rewrite <- copp_div_l.
apply pos_non_c0.
apply clt_trans with (Pol_eval P1 r2).
assumption.
apply Pauxinc.
apply cle_lt_trans with r; assumption.
apply cplus_lt_r.
apply c0_clt_c1.
apply  cdiv_lt_0_compat_l.

apply Hpos.
apply cplus_lt_r; apply c0_clt_c1.
apply clt_0_copp.
assumption.
setoid ring.
(* end of assert Hru *)

assert (HPfpos : c0 <= Pol_eval P u).
apply clt_cle_weak.
setoid_rewrite p.
setoid_rewrite Pol_eval_mult.
apply cmul_lt_0.
setoid_rewrite Pol_eval_pow.
setoid_rewrite Pol_eval_X.
apply cpow_lt_0_compat_l.
apply clt_trans with r2; intuition; fail.
assumption.
destruct Heps' as [Heps'pos [Heps'lteps Heps'ltPf]].

destruct (intermediate_value_polynom P r2 u HPr2neg HPfpos Hr2u eps' Heps'pos)
  as  [v1 [v2  Hv1v2]].
exists v1.
exists v2.
assert (HincP1 : forall x y, r<x -> x< y -> Pol_eval P1 x < Pol_eval P1 y).
intros; apply Pauxinc;[apply cle_lt_trans with r;assumption|assumption].
split.
apply clt_le_trans with r2; intuition;fail.
split.
intuition;fail.
split.
apply cle_lt_trans with (--eps').
apply copp_le_compat.
intuition;fail.
intuition;fail.
split.
intuition; fail.
split.
intuition; fail.
split.
apply clt_le_trans with eps'; intuition ; fail.
split.

destruct Hv1v2 as [Hr2v1 [Hv1v2 [Hv2u [HPv1close [HPv1neg [HPv2pos [HPv2close
                   Hv2mv1]]]]]]].
assert (HP'neg : a ++ v1 ** Pol_eval P1 v1 < c0).
apply cmul_lt_0_lt_reg_r with (cpow v1 n).
apply cpow_lt_0_compat_l.
apply clt_le_trans with r2; intuition; fail.
setoid_rewrite cmul_0_l.
setoid_rewrite <- (cmul_sym (cpow v1 n)).
generalize HPv1neg.
setoid_rewrite p;
setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_pow;
setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_c;
setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_X.
auto.

intros x Hxp Hxltv1.
setoid_rewrite p.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_pow.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
destruct (clt_le_dec r2 x) as [Hr2ltx|Hxler2].
apply cmul_lt_neg_r.
apply cpow_lt_0_compat_l; assumption.
apply clt_trans with (a++v1**Pol_eval P1 v1).
apply cplus_le_lt_compat.
apply cle_refl.
apply clt_trans with (x** Pol_eval P1 v1).
repeat (setoid_rewrite (cmul_sym x)).
apply cmul_lt_compat_r.
assumption.

apply HincP1.
apply clt_trans with r2; assumption.
assumption.
apply cmul_lt_compat_r.
assert (HposP1 : forall x , r2 <x -> c0 < Pol_eval P1 x) by intuition.
apply HposP1.
apply clt_trans with x; assumption.
assumption.
apply HP'neg.

apply cmul_lt_neg_r.
apply cpow_lt_0_compat_l.
assumption.

destruct (clt_le_dec raux x) as [rauxltx | xleraux].
destruct (clt_le_dec (Pol_eval P1 x) c0) as [P1xneg | P1xpos].
apply cplus_lt_0_neg.
assumption.
apply cmul_lt_neg_r; assumption.

apply clt_trans with (a ++ v1**Pol_eval P1 v1).
apply cplus_le_lt_compat.
apply cle_refl.
apply clt_le_trans with (x**Pol_eval P1 v1).
repeat setoid_rewrite (cmul_sym x).
apply cmul_lt_compat_r.
assumption.
apply Pauxinc; assumption.
apply cmul_le_compat_r.
apply clt_cle_weak; assumption.
apply cle_trans with (Pol_eval P1 x).
assumption.
apply clt_cle_weak; apply Pauxinc; assumption.
assumption.


apply cplus_lt_0_neg.
exact Haneg.
apply cmul_lt_neg_r.
assumption.
case (ceq_dec x raux).
intros Hxraux; setoid_rewrite Hxraux; assumption.
intros Hxnraux.
apply Pauxneg.
assumption.
apply clt_decompose; assumption.

assert (c0 < v2).
apply clt_trans with v1.
apply clt_le_trans with r2.
assumption.
intuition;fail.
intuition;fail.
assert (Hdenv1v2 : c0 < c1 ++ Coef_of_N n ** cpow v2 (Npred n) ++
   (v2 -- v1) ** Pol_eval (diff_cpow_pol v2 n) (v2 -- v1)).
setoid_rewrite <- (cadd_assoc c1).
setoid_rewrite (cadd_sym c1).
apply clt_0_le_lt_plus_compat.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; intuition;fail.
apply diff_cpow_pol_pos.
apply clt_cle_weak; assumption.
apply csub_le_0.
apply clt_cle_weak; intuition;fail.
apply c0_clt_c1.
(* end of assert Hdenv1v2 *)
assert (Hdiffur2v1v2 : v2--v1 <=  u--r2).
setoid_replace (u--r2) with (u ++ -- r2).
setoid_replace (v2--v1) with (v2 ++ -- v1).
apply cplus_le_compat.
intuition; fail.
apply copp_le_compat; intuition; fail.
setoid ring.
setoid ring.
assert 
  (Hdenur2 : c1 ++ Coef_of_N n ** cpow v2 (Npred n) ++
              (v2 -- v1) ** Pol_eval (diff_cpow_pol v2 n) (v2 -- v1)
             <= c1++ Coef_of_N n ** cpow u (Npred n) ++
             (u -- r2)** Pol_eval (diff_cpow_pol u n) (u -- r2)).
apply cplus_le_compat.
apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (Coef_of_N n)).
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
intuition; fail.
apply c0_cle_Coef.
apply cle_trans with ((v2--v1)**Pol_eval (diff_cpow_pol u n) (u--r2)).
repeat setoid_rewrite (cmul_sym (v2--v1)).
apply cmul_le_compat_r.
apply cle_trans with (Pol_eval (diff_cpow_pol v2 n)(u--r2)).
apply diff_cpow_pol_incry.
apply clt_cle_weak; assumption.
apply csub_le_0; apply clt_cle_weak; intuition; fail.
assumption.
apply diff_pow_pol_incrx.
apply clt_cle_weak; assumption.
intuition;fail.
apply csub_le_0; apply cle_trans with v2.
apply clt_cle_weak; apply cle_lt_trans with v1;intuition;fail.
intuition;fail.
apply csub_le_0; apply clt_cle_weak; intuition;fail.
apply cmul_le_compat_r.
assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_le_trans with v2; intuition;fail.
apply csub_le_0.
apply clt_cle_weak; apply clt_le_trans with v2.
apply cle_lt_trans with v1; intuition;fail.
intuition; fail.
(* end assert Hdiffur2v1v2 *)
split.
intros x Hxv2.
apply cle_lt_trans with (Pol_eval P v2).
intuition; fail.
setoid_rewrite p; repeat setoid_rewrite Pol_eval_mult;
repeat setoid_rewrite Pol_eval_plus; repeat setoid_rewrite Pol_eval_mult;
repeat setoid_rewrite Pol_eval_pow; repeat setoid_rewrite Pol_eval_X.
repeat setoid_rewrite Pol_eval_c.
apply cmul_le_lt_compat.
apply cpow_lt_0_compat_l.
assumption.
apply cmul_lt_0_le_reg_r with (cpow v2 n).
apply cpow_lt_0_compat_l.
assumption.
setoid_rewrite cmul_0_l.
setoid_rewrite <- (cmul_sym (cpow v2 n)).
cut (c0 <= Pol_eval P v2).
setoid_rewrite p; repeat setoid_rewrite Pol_eval_mult;
repeat setoid_rewrite Pol_eval_plus; repeat setoid_rewrite Pol_eval_mult;
repeat setoid_rewrite Pol_eval_pow; repeat setoid_rewrite Pol_eval_X.
repeat setoid_rewrite Pol_eval_c.
auto.
intuition;fail.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply cplus_le_lt_compat.
apply cle_refl.
apply cmul_le_lt_compat.
assumption.
apply clt_cle_weak; apply clt_trans with (Pol_eval P1 r2).
assumption.
apply Pauxinc.
apply cle_lt_trans with r; assumption.
apply cle_lt_trans with v1; intuition;fail.
apply clt_cle_weak; assumption.
apply Pauxinc.
apply clt_trans with v1.
apply clt_le_trans with r2.
apply cle_lt_trans with r; assumption.
intuition; fail.
intuition; fail.
assumption.
intros x y Hx Hy.
setoid_rewrite p.

assert (c0 <= Pol_eval (Pc a + X*P1) v2).
apply cmul_lt_0_le_reg_r with (cpow v2 n).
apply cpow_lt_0_compat_l.
assumption.
setoid_rewrite cmul_0_l.
setoid_rewrite <- (cmul_sym (cpow v2 n)).
cut (c0 <= Pol_eval P v2).
setoid_rewrite p; setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_pow.
setoid_rewrite Pol_eval_X; auto.
intuition;fail.

apply increase_pol_close_0_Xn with (r:= v1) (r2:= v2).
apply clt_le_trans with r2; intuition;fail.
apply clt_cle_weak; apply clt_le_trans with (Pol_eval P1 r2).
assumption.
destruct (ceq_dec r2 v1) as [Hr2v1 | Hv1r2].
setoid_rewrite Hr2v1; apply cle_refl.
apply clt_cle_weak; apply HincP1.
assumption.
apply clt_decompose; intuition; fail.
intros;apply clt_trans with (Pol_eval P1 r2).
assumption.

apply Pauxinc.
apply cle_lt_trans with r; assumption.
apply cle_lt_trans with v1; intuition;fail.
intros x0 y0 Hx0 Hy0.
destruct (ceq_dec x0 y0) as [Hx0y0 | Hdiff].
setoid_rewrite Hx0y0; apply cle_refl.
apply clt_cle_weak; apply Pauxinc.
apply cle_lt_trans with r.
assumption.
apply clt_le_trans with r2.
assumption.
apply cle_trans with v1; intuition;fail.
apply clt_decompose; assumption.
intuition;fail.
assumption.
apply cmul_lt_0_lt_reg_r with (cpow v1 n).
apply cpow_lt_0_compat_l.
apply clt_le_trans with r2; intuition; fail.
apply cle_lt_trans with (--eps').
setoid_rewrite copp_div_l.
setoid_rewrite <- cadd_assoc.
apply pos_non_c0.
setoid_rewrite (cadd_sym c1).
apply clt_0_le_lt_plus_compat.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; intuition;fail.
apply diff_cpow_pol_pos.
apply clt_cle_weak; assumption.
apply csub_le_0.
apply clt_cle_weak; intuition;fail.
apply c0_clt_c1.

setoid_rewrite mul_copp.
apply copp_le_compat.
apply cle_trans with (1:= Heps'ltPf).
setoid_replace (cpow r n ** Pol_eval P1 r2 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2))) with (cpow r n ** Pol_eval P1 r2 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2))).
setoid_rewrite (cdiv_decompose (cpow r n ** Pol_eval P1 r2)).
apply pos_non_c0.
setoid_replace (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
   (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)) with
    ((Coef_of_N n ** cpow u (Npred n) ++
   (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2))++c1).
apply clt_0_le_lt_plus_compat.
assert (r2 <= u).
unfold u.
apply clt_cle_weak; apply Horner_step_positive_tech.
assumption.
intros x0 y0 Hx0 Hy0; split.
apply clt_trans with (Pol_eval P1 r2).
assumption.
apply Pauxinc.
apply cle_lt_trans with r;assumption.
assumption.
destruct (ceq_dec x0 y0) as [Hxy | Hxny].
setoid_rewrite Hxy; apply cle_refl.
apply clt_cle_weak; apply Pauxinc.
apply clt_trans with r2.
apply cle_lt_trans with r;assumption.
assumption.
apply clt_decompose; assumption.
assert (c0 <= u).
apply cle_trans with r2.
apply clt_cle_weak; assumption.
assumption.
(* end of assert. *)
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos; assumption.
apply cmul_le_0.
apply csub_le_0; assumption.
apply diff_cpow_pol_pos.
assumption.
apply csub_le_0; assumption.
apply c0_clt_c1.
setoid ring.
setoid_rewrite (cdiv_decompose (cpow v1 n ** Pol_eval P1 v1)).
apply pos_non_c0.


exact Hdenv1v2.
apply cle_trans with (c1 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)) **
   (cpow r n ** Pol_eval P1 r2)**cpow v1 n).
repeat setoid_rewrite (cmul_sym (c1 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)) **
   (cpow r n ** Pol_eval P1 r2))).
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply clt_cle_weak; apply clt_trans with r; assumption.
intuition;fail.
apply cmul_le_0.
apply cdiv_le_0_compat_l.
apply clt_le_trans with (1:=Hdenv1v2)(2:=Hdenur2).
apply c0_cle_c1.
apply cmul_le_0.
apply cpow_pos.
apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply cle_trans with (c1 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)) **
   (cpow v1 n ** Pol_eval P1 v1)).
repeat setoid_rewrite (cmul_sym (c1 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)))).
apply cmul_le_compat_r.
apply cle_trans with (cpow r n ** Pol_eval P1 v1).
repeat setoid_rewrite (cmul_sym (cpow r n)).
apply cmul_le_compat_r.


destruct (ceq_dec r2 v1) as [Hr2v1 | Hv1r2].
setoid_rewrite Hr2v1; apply cle_refl.
apply clt_cle_weak; apply HincP1.
assumption.
apply clt_decompose; intuition;fail.
apply cpow_pos; apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply clt_le_trans with r2; intuition;fail.
(* Proof that Pol_eval P1 v1 is positive *)
apply cle_trans with (Pol_eval P1 r2).
apply clt_cle_weak; assumption.
destruct (ceq_dec r2 v1) as [Hxy | Hxny].
setoid_rewrite Hxy; apply cle_refl.
apply clt_cle_weak; apply Pauxinc.
apply cle_lt_trans with r;assumption.
apply clt_decompose; intuition; fail.
apply cdiv_le_0_compat_l.
apply clt_le_trans with (1:= Hdenv1v2)(2:=Hdenur2).
apply c0_cle_c1.
apply cmul_le_compat_r.
apply inv_cle.
exact Hdenv1v2.
exact Hdenur2.
apply cmul_le_0.
apply cpow_pos.
apply clt_cle_weak; apply clt_le_trans with r2; intuition;fail.
(* Proof that Pol_eval P1 v1 is positive *)
apply cle_trans with (Pol_eval P1 r2).
apply clt_cle_weak; assumption.
destruct (ceq_dec r2 v1) as [Hxy | Hxny].
setoid_rewrite Hxy; apply cle_refl.
apply clt_cle_weak; apply Pauxinc.
apply cle_lt_trans with r;assumption.
apply clt_decompose; intuition; fail.
(* end of proof *)
apply cpow_pos.
apply clt_cle_weak; apply clt_le_trans with r2; intuition;fail.
apply ceq_refl.
setoid_rewrite <- (cmul_sym (cpow v1 n)).
assert (HPv1close : --eps' < Pol_eval P v1) by intuition.
generalize HPv1close; setoid_rewrite p;
setoid_rewrite Pol_eval_mult;
 setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_plus; 
setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_c; 
setoid_rewrite Pol_eval_X; auto.
assumption.
assumption.
assert (Hpos : forall x : Coef, r2 < x -> c0 < Pol_eval P1 x).
intros; apply clt_trans with (Pol_eval P1 r2).
intuition;fail.
apply Pauxinc.
apply cle_lt_trans with r; assumption.
assumption.
assert (Hr2u : r2 < u).
apply clt_trans with (r2++c1).
apply cplus_lt_r.
apply c0_clt_c1.
unfold u.
setoid_replace (r2 ++ c1 -- a / Pol_eval P1 (r2 ++ c1)) with
   (r2++c1 ++ -- (a/Pol_eval P1(r2++c1))).
apply cplus_lt_r.
setoid_rewrite <- copp_div_l.
apply pos_non_c0.
apply clt_trans with (Pol_eval P1 r2).
assumption.
apply Pauxinc.
apply cle_lt_trans with r; assumption.
apply cplus_lt_r.
apply c0_clt_c1.
apply  cdiv_lt_0_compat_l.

apply Hpos.
apply cplus_lt_r; apply c0_clt_c1.
apply clt_0_copp.
assumption.
setoid ring.

destruct (clt_le_dec eps (cpow r n ** Pol_eval P1 r2 /
     (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
      (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)) ** 
     cpow r2 n)) as [Hef | Hfe].
exists eps.

split.
assumption.
split.
apply cle_refl.
apply clt_cle_weak; assumption.

exists (cpow r n ** Pol_eval P1 r2 /
   (c1 ++ Coef_of_N n ** cpow u (Npred n) ++
    (u -- r2) ** Pol_eval (diff_cpow_pol u n) (u -- r2)) ** 
   cpow r2 n).
split.
apply cmul_lt_0.
apply cdiv_lt_0_compat_l.
setoid_rewrite <- (cadd_assoc c1).
setoid_rewrite (cadd_sym c1).
apply clt_0_le_lt_plus_compat.
apply cle_0_plus.
apply cmul_le_0.
apply c0_cle_Coef.
apply cpow_pos.
apply clt_cle_weak; apply clt_trans with r2; assumption.
apply cmul_le_0.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply diff_cpow_pol_pos.
apply clt_cle_weak; apply clt_trans with r2; assumption.
apply csub_le_0.
apply clt_cle_weak; assumption.
apply c0_clt_c1.
apply cmul_lt_0.
apply cpow_lt_0_compat_l.
assumption.
assumption.
apply cpow_lt_0_compat_l.
assumption.
split.
assumption.
apply cle_refl.
Qed.
