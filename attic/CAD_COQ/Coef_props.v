Require Import Wellfounded.
Require Import Setoid.
Require Import CAD_types.
Require Import Utils.
Require Import NArith.
Require Import NArithRing.
Require Import Zwf.
Require Import QArith.
Require Import Recdef.
Require Import Qnorm.
Require Import Pol_ring2.

Definition cdiv : Coef -> Coef -> Coef :=
   Qdiv.

Infix "/" := cdiv.

Theorem cmul_div_r : 
  forall p q, ~q==c0 -> cmul q (cdiv p q) == p.
exact Qmult_div_r.
Qed.

Theorem cdiv_mul_l :
  forall p q, ~q==c0 -> cdiv (cmul p q) q == p.
exact Qdiv_mult_l.
Qed.

Definition cle : Coef -> Coef -> Prop := Qle.

Infix "<=" := cle.

Notation "x <= y <= z" := (cle x y /\ cle y z).

Theorem cle_trans : forall x y z, cle x y -> cle y z -> cle x z.
exact Qle_trans.
Qed.

Theorem cle_refl : forall x, cle x x.
exact Qle_refl.
Qed.

Theorem cle_antisym : forall x y, x <= y -> y <= x -> x==y.
exact Qle_antisym.
Qed.

Theorem cle_Qle : forall x y, cle x y -> Qle x y.
auto.
Qed.

Theorem Qle_cle : forall x y, Qle x y -> cle x y.
auto.
Qed.

Theorem cle_morph_aux : forall x1 x2 : Coef,
   x1 == x2 -> forall x3 x4 : Coef, x3 == x4 -> cle x1 x3 -> cle x2 x4.
unfold Coef_record.Ceq, ceq_compat, cle, Qle, Qeq.
intros x1 x2 H1 x3 x4 H2 H.

apply Zmult_le_reg_r with (Zpos (Qden x1)).
unfold Zgt;auto.
replace (Qnum x2 * ' Qden x4 * ' Qden x1)%Z with
        (Qnum x2 * ' Qden x1 * ' Qden x4)%Z;[idtac | ring].
rewrite <- H1.
apply Zmult_le_reg_r with (Zpos (Qden x3)).
compute; auto.
replace (Qnum x4 * ' Qden x2 * ' Qden x1 * ' Qden x3)%Z with
   (Qnum x4 * ' Qden x3 * ' Qden x2 * ' Qden x1)%Z;[idtac|ring].
rewrite <- H2.
replace (Qnum x1 * ' Qden x2 * ' Qden x4 * ' Qden x3)%Z with
     (Qnum x1 * ' Qden x3 * ' Qden x4 * ' Qden x2)%Z;[idtac | ring].
replace (Qnum x3 * ' Qden x4 * ' Qden x2 * ' Qden x1)%Z with
     (Qnum x3 * ' Qden x1 * ' Qden x4 * ' Qden x2)%Z;[idtac | ring].
apply Zmult_le_compat_r.
apply Zmult_le_compat_r.
assumption.
compute; intros; discriminate.
compute; intros; discriminate.
Qed.
Add Morphism cle with signature ceq ==> ceq ==> iff as Qle_morphism.
intros x1 x2 H1 x3 x4 H2; split; intros H.
apply cle_morph_aux with x1 x3; auto.
apply cle_morph_aux with x2 x4; auto.
apply ceq_sym; assumption.
apply ceq_sym; assumption.
Qed.

Definition clt : Coef -> Coef -> Prop := Qlt.

Infix "<" := clt.

Lemma clt_le_dec : forall x y:Coef, {clt x y}+{cle y x}.
exact Qlt_le_dec.
Qed.

Lemma clt_trans : forall x y z, clt x y -> clt y z -> clt x z.
exact Qlt_trans.
Qed.

Lemma clt_decompose : forall x y, ~ceq x y -> cle x y -> clt x y.
unfold Coef_record.Ceq, ceq_compat, cle, Qle, clt, Qlt, Qeq.
intros; auto with zarith.
Qed.

Lemma clt_cle_weak : forall x y, x < y -> x <= y.
unfold Coef_record.Ceq, ceq_compat, cle, Qle, clt, Qlt, Qeq.
intros; auto with zarith.
Qed.

Theorem clt_morph_aux : forall x1 x2 : Coef,
   x1 == x2 -> forall x3 x4 : Coef, x3 == x4 -> clt x1 x3 -> clt x2 x4.
unfold Coef_record.Ceq, ceq_compat, cle, Qle, clt, Qlt, Qeq.
intros x1 x2 H1 x3 x4 H2 H.

apply Zmult_lt_reg_r with (Zpos (Qden x1)).
unfold Zlt;auto.
replace (Qnum x2 * ' Qden x4 * ' Qden x1)%Z with
        (Qnum x2 * ' Qden x1 * ' Qden x4)%Z;[idtac | ring].
rewrite <- H1.
apply Zmult_lt_reg_r with (Zpos (Qden x3)).
compute; auto.
replace (Qnum x4 * ' Qden x2 * ' Qden x1 * ' Qden x3)%Z with
   (Qnum x4 * ' Qden x3 * ' Qden x2 * ' Qden x1)%Z;[idtac|ring].
rewrite <- H2.
replace (Qnum x1 * ' Qden x2 * ' Qden x4 * ' Qden x3)%Z with
     (Qnum x1 * ' Qden x3 * ' Qden x4 * ' Qden x2)%Z;[idtac | ring].
replace (Qnum x3 * ' Qden x4 * ' Qden x2 * ' Qden x1)%Z with
     (Qnum x3 * ' Qden x1 * ' Qden x4 * ' Qden x2)%Z;[idtac | ring].
apply Zmult_lt_compat_r.
compute; auto.
apply Zmult_lt_compat_r.
compute; auto.
assumption.
Qed.

Add Morphism clt with signature ceq ==> ceq ==> iff as Qlt_morphism.
intros x1 x2 H1 x3 x4 H2; split; intros H.
apply clt_morph_aux with x1 x3; auto.
apply clt_morph_aux with x2 x4; auto.
apply ceq_sym; assumption.
apply ceq_sym; assumption.
Qed.

Lemma cmul_le_compat_r : 
   forall x y z:Coef, cle x y -> cle c0 z -> cle (x**z) (y**z).
exact Qmult_le_compat_r.
Qed.

Lemma cmul_le_0 : forall x y, cle c0 x -> cle c0 y -> cle c0 (x**y).
intros; setoid_replace c0 with (c0 ** y).
apply cmul_le_compat_r; auto.
setoid ring.
Qed.

Lemma cmul_lt_0_le_reg_r :
  forall x y z, clt c0 z -> cle (x**z) (y**z) -> cle x y.
exact Qmult_lt_0_le_reg_r.
Qed.

Lemma cle_0_mult :
   forall x y, cle c0 x -> cle c0 y -> cle c0 (x ** y).
intros x y Hx Hy; assert (ceq c0 (c0**y)).
setoid ring.
setoid_rewrite H.
apply cmul_le_compat_r; auto.
Qed.

Lemma cplus_le_compat :
    forall x y z t, cle x y -> cle z t -> cle (x++z) (y++t).
exact Qplus_le_compat.
Qed.

Lemma cle_0_plus :
  forall x y, cle c0 x -> cle c0 y -> cle c0 (x ++ y).
intros x y Hx Hy.
assert (ceq c0 (c0++c0)).
setoid ring.
setoid_rewrite H.
apply cplus_le_compat; auto.
Qed.

Lemma Q0_le_1 : (0 <= 1)%Q.
unfold Qle, Qnum, Qden; omega.
Qed.

Lemma c0_cle_c1: cle c0 c1.
exact Q0_le_1.
Qed.

Lemma copp_le_compat :
  forall p q, cle p q -> cle (copp q) (copp p).
exact Qopp_le_compat.
Qed.

Lemma copp_le_0_compat :
  forall p, cle c0 p -> cle (copp p) c0.
intros; setoid_replace c0 with (copp c0).
apply copp_le_compat; auto.
setoid ring.
Qed.

Lemma cle_0_copp : forall x, x <= c0 -> c0 <= copp x.
intros; setoid_replace c0 with (copp c0).
apply copp_le_compat; auto.
setoid ring.
Qed.

Lemma copp_le_0_compat_copp:
  forall p, cle p c0 -> cle c0 (copp p).
intros; setoid_replace c0 with (copp c0).
apply copp_le_compat; auto.
setoid ring.
Qed.

Lemma mul_copp : forall p q, copp p ** q == copp (p ** q).
intros; setoid ring.
Qed.

Lemma copp_copp : forall p, copp (copp p) == p.
intros; setoid ring.
Qed.

Theorem  clt_neq : forall x y, x < y -> ~x==y.
unfold clt, Qlt, Coef_record.Ceq, ceq_compat, Qeq.
auto with zarith.
Qed.

Theorem cmul_lt_0 : forall x y, c0 < x -> c0 < y -> c0 < x ** y.
intros x y Hx Hy.
apply clt_decompose.
unfold Coef_record.Ceq, ceq_compat; intros H; elim (Qmult_integral x y);
intros.
elim (clt_neq _ _ Hx); apply Qeq_sym; auto.
elim (clt_neq _ _ Hy); apply Qeq_sym; auto.
apply Qeq_sym; auto.
apply cmul_le_0; apply clt_cle_weak; auto.
Qed.

Theorem cplus_lt_0_le_lt : forall x y, c0 < x -> c0 <= y -> 0 < x ++ y.
unfold clt, cle, Qlt, Qle, Coef_record.C0, ceq_compat, cops,
  Coef_record.Cadd, Qplus.
intros [x1 x2] [y1 y2]; unfold Qden, Qnum.
repeat rewrite Zmult_0_l.
repeat rewrite Zmult_1_r.
intros; apply Zlt_le_trans with (x1 * Zpos y2)%Z.
apply Zmult_lt_0_compat.
assumption.
compute; auto.
assert (0 <= y1*Zpos x2)%Z.
apply Zmult_le_0_compat.
assumption.
intros; discriminate.
omega.
Qed.

Theorem cdiv_le_0_compat_l :
  forall p q, c0 < q -> c0 <= p -> c0 <= p/q.
intros p q Hlt Hle.
apply cmul_lt_0_le_reg_r with q.
assumption.
setoid_rewrite cmul_0_l.
setoid_rewrite cmul_sym; setoid_rewrite cmul_div_r.
assert (Habs:~c0==q) by (apply clt_neq; auto).
intros Habs2; elim Habs; apply ceq_sym;auto.
assumption.
Qed.

Theorem cdiv_lt_0_compat_l :
  forall p q, c0 < q -> c0 < p -> c0 < p/q.
intros p q Hlq Hlp.
assert (Hqn0: ~ q == 0).
intros H; elim (clt_neq _ _ Hlq); apply ceq_sym; exact H.
unfold cdiv.
unfold Qdiv.
setoid_replace c0 with (0 * /q)%Q.
apply Qmult_lt_compat_r.
apply clt_decompose.
intros H; elim (clt_neq _ _ Hlq).
setoid_rewrite <- (cmul_1_l q).
setoid_replace c1 with (q**/q).
replace 0 with c0 in H.
setoid_rewrite <- H; setoid ring.
reflexivity.
unfold Coef_record.Ceq, Coef_record.Cmul, ceq_compat, Coef_record.C1, cops.
apply Qeq_sym; apply Qmult_inv_r.
assumption.
apply cmul_lt_0_le_reg_r with q.
assumption.
setoid_rewrite (cmul_sym (/q) q).
setoid_replace (q**/q) with c1.
setoid_replace (0**q) with c0.
exact c0_cle_c1.
change (c0**q==c0); apply cmul_0_l.
unfold Coef_record.Ceq, Coef_record.Cmul, ceq_compat, Coef_record.C1, cops.
apply Qmult_inv_r.
exact Hqn0.
exact Hlp.
change (c0 == c0 ** /q).
setoid ring.
Qed.

Theorem c0_clt_2 : c0 < c1++c1.
apply cplus_lt_0_le_lt.
apply clt_decompose; [apply c0_diff_c1 | apply c0_cle_c1].
apply c0_cle_c1.
Qed.

Lemma cut_half : forall x, x == x/(c1++c1) ++ x/(c1++c1).
intros x0; setoid_replace (x0/(c1++c1)++x0/(c1++c1)) with
   ((c1++c1) ** (x0/(c1++c1))).
setoid_rewrite cmul_div_r.
intros Habs.
elim (clt_neq _ _ c0_clt_2).
apply ceq_sym; assumption.
apply ceq_refl.
setoid ring.
Qed.

Lemma cplus_pos_simplify : forall x y, c0 <= x -> y <= x ++ y.
intros x y H;
pose (u:=x++y); fold u.
setoid_replace y with (c0 ++ y);[unfold u|setoid ring].
apply cplus_le_compat;[assumption |apply cle_refl].
Qed.

Lemma mul_copp_copp : forall x y, copp x ** copp y == x ** y.
intros; setoid ring.
Qed.

Lemma csub_diag : forall x, x -- x == c0.
intros; setoid ring.
Qed.

Lemma cle_csub_cadd : forall a b c, a -- b <= c -> a <= b ++ c.
intros; setoid_replace a with (b ++ (a--b));[idtac|setoid ring].
apply cplus_le_compat;[apply cle_refl|assumption].
Qed.

Lemma cdiv_decompose :  forall x y, ~y==c0 -> x/y == c1/y**x.
intros x y Hy; setoid_replace (x/y) with ((c1/y**y)**(x/y)).
setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
exact Hy.
apply ceq_refl.
setoid_rewrite (cmul_sym (c1/y) y).
setoid_rewrite cmul_div_r.
exact Hy.
setoid ring.
Qed.

Lemma cdiv_assoc : forall x y z, ~y**z == c0 -> (x/y)/z == x/(y**z).
intros x y z Hnz.
assert (Hy:~y==c0).
intros Ha; elim Hnz;setoid_rewrite Ha;setoid ring.
assert (Hz:~z==c0).
intros Ha; elim Hnz;setoid_rewrite Ha;setoid ring.
setoid_replace ((x/y)/z) with ((y**z)**(c1/(y**z))**((x/y)/z)).
setoid_rewrite (cmul_sym (y**z)).
repeat setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
assumption.
setoid_rewrite cmul_div_r.
assumption.
setoid_rewrite (cdiv_decompose x (y**z)).
assumption.
apply ceq_refl.
setoid_rewrite cmul_div_r.
assumption.
setoid ring.
Qed.

Lemma pos_non_c0 : forall x, c0 < x -> ~x==c0.
intros x Hx Ha; elim (clt_neq _ _ Hx);setoid_rewrite Ha; apply ceq_refl.
Qed.

Lemma c0_clt_c1 : c0 < c1.
apply clt_decompose.
apply c0_diff_c1.
apply c0_cle_c1.
Qed.

Definition ceq_dec : forall x y : Coef, {ceq x y} + {~ ceq x y}
:= Qeq_dec.

Lemma cadd_copp : forall x y : Coef, -- x ++ -- y == -- (x++y).
intros; setoid ring.
Qed.

Lemma copp_csub : forall x y : Coef, --(x -- y) == y -- x.
intros; setoid ring.
Qed.

Lemma copp_div_l :
  forall x y, ~y==0 -> copp x / y == copp (x / y).
intros; setoid_rewrite (cdiv_decompose x y).
assumption.
setoid_rewrite (cdiv_decompose (--x)).
assumption.
setoid_rewrite <- copp_mul_r.
apply ceq_refl.
Qed.

Theorem cplus_le_lt_compat :
  forall x y z t, x <= y -> z < t -> x++z < y++t.
unfold clt, cle, Coef, Qlt, Qle.
intros [xn xd] [yn yd] [zn zd] [tn td]; lazy zeta. 
unfold Coef_record.Cadd, cops, Qplus, Qden, Qnum.
intros.
replace ('(yd*td)) with ('yd *'td)%Z; [idtac | apply refl_equal].
replace ('(xd*zd)) with ('xd *'zd)%Z; [idtac | apply refl_equal].
replace ((xn*'zd +zn*'xd)*('yd*'td))%Z with
  (xn*'yd*'zd*'td +zn*'td*'yd*'xd)%Z;[idtac | ring].
replace ((yn*'td+tn*'yd)*('xd *'zd))%Z with
  (yn*'xd*'zd*'td +tn*'zd*'yd*'xd)%Z;[idtac | ring].
apply Zplus_le_lt_compat.
repeat apply Zmult_le_compat_r.
assumption.
intro; discriminate.
intro; discriminate.
repeat apply Zmult_lt_compat_r.
exact (refl_equal Lt).
exact (refl_equal Lt).
assumption.
Qed.

Lemma clt_0_le_lt_plus_compat :
 forall x y, c0 <= x -> c0 < y -> c0 < x ++ y.
intros; setoid_replace c0 with (c0 ++ c0).
apply cplus_le_lt_compat; assumption.
setoid ring.
Qed.

Lemma clt_0_plus_compat :
  forall x y, c0 < x -> c0 < y -> c0 < x ++ y.
intros; apply clt_0_le_lt_plus_compat.
apply clt_cle_weak; assumption.
assumption.
Qed.

Lemma clt_0_copp : forall x, x < c0 -> c0 < --x.
intros.
setoid_replace c0 with (--x ++ x).
set (u:= -- x ++ x); setoid_replace (--x) with (--x ++ c0); unfold u.
apply cplus_le_lt_compat.
apply cle_refl.
assumption.
setoid ring.
setoid ring.
Qed.

Theorem cmul_lt_compat_r :
  forall x y z, c0 < z -> x < y -> x**z < y**z.
exact Qmult_lt_compat_r.
Qed.

Theorem clt_le_trans : forall x y z, x < y -> y <= z -> x < z.
intros x y z Hy Hz.
case (ceq_dec y z).
intros Heq; setoid_rewrite <- Heq; assumption.
intros; apply clt_trans with y.
assumption.
apply clt_decompose; assumption.
Qed.

Theorem cle_lt_trans : forall x y z, x <= y -> y < z -> x < z.
intros x y z Hy Hz.
case (ceq_dec x y).
intros Heq; setoid_rewrite Heq; assumption.
intros; apply clt_trans with y.
apply clt_decompose; assumption.
assumption.
Qed.

Theorem clt_0 : forall x, c0 < copp x -> x < c0.
intros; setoid_replace x with (x++c0).
set (u:= x++c0); setoid_replace c0 with (x++--x); unfold u.
apply cplus_le_lt_compat.
apply cle_refl.
assumption.
setoid ring.
setoid ring.
Qed.

Theorem cplus_lt_compat_r :
  forall x y z, x < y -> x++z < y++z.
intros; repeat setoid_rewrite <- (cadd_sym z).
apply cplus_le_lt_compat.
apply cle_refl.
assumption.
Qed.

Lemma cmul_lt_0_lt_reg_r: 
   forall x y z : Coef, c0 < z -> x ** z < y ** z -> x < y.
intros; apply clt_decompose.
intros Habs; elim (clt_neq _ _ H0); setoid_rewrite Habs.
apply ceq_refl.
apply cmul_lt_0_le_reg_r with z.
assumption.
apply clt_cle_weak; assumption.
Qed.

Lemma inv_clt : forall x y, c0 < x -> x < y -> c1/y < c1/x .
intros x y Hx Hy.
apply cmul_lt_0_lt_reg_r with (x**y).
apply cmul_lt_0.
assumption.
apply clt_trans with x; assumption.
setoid_replace (c1/y**(x**y)) with (x ** (y**(c1/y))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply clt_trans with x; assumption.
setoid_rewrite cmul_1_r.
setoid_replace (c1/x**(x**y)) with (y**(x**(c1/x))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r.
assumption.
setoid ring.
setoid ring.
Qed.

Lemma inv_cle : forall x y, c0 < x -> x <= y -> c1/y <= c1/x.
intros x y Hx Hy; elim (ceq_dec x y).
intros Heq; apply cmul_lt_0_le_reg_r with (x**y).
apply cmul_lt_0.
assumption.
apply clt_le_trans with x; assumption.
setoid_replace (c1/y**(x**y)) with (x ** (y**(c1/y))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply clt_le_trans with x; assumption.
setoid_rewrite cmul_1_r.
setoid_replace (c1/x**(x**y)) with (y**(x**(c1/x))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r.
setoid_rewrite Heq; apply cle_refl.
setoid ring.
setoid ring.
intros Hn.
apply clt_cle_weak.
apply inv_clt.
assumption.
apply clt_decompose; assumption.
Qed.


Lemma cle_opp_div_r : forall a b c, c0 <= a -> c0 < b -> b <= c ->
  --(a/b) <= --(a/c).
intros a b c Ha Hb Hc; apply copp_le_compat.
repeat setoid_rewrite (cdiv_decompose a).
apply pos_non_c0; apply clt_le_trans with b; assumption.
apply pos_non_c0; assumption.
apply cmul_le_compat_r.
apply inv_cle; assumption.
assumption.
Qed.

Lemma cle_div_r : forall a b c, c0 <= a -> c0 < c -> c <= b ->
  a/b <= a/c.
intros a b c Ha Hb Hc.
repeat setoid_rewrite (cdiv_decompose a).
apply pos_non_c0; apply clt_le_trans with c; assumption.
apply pos_non_c0; assumption.
apply cmul_le_compat_r.
apply inv_cle; assumption.
assumption.
Qed.


Theorem cmul_lt_compat : forall x y z t,
   c0 < x -> x < y -> c0 < z -> z < t ->  x ** z < y ** t.
intros x y z t Hx Hy Hz Ht.
apply clt_trans with (y**z).
apply cmul_lt_compat_r; assumption.
repeat setoid_rewrite (cmul_sym y).
apply cmul_lt_compat_r.
apply clt_trans with x; assumption.
assumption.
Qed.

Lemma cmul_lt_neg_r :
  forall x y, c0 < x -> y < c0 -> x**y < c0.
intros; setoid_rewrite (cmul_sym x).
setoid_replace c0 with (c0 ** x).
apply cmul_lt_compat_r;assumption.
setoid ring.
Qed.

Theorem cplus_lt_reg_r :
  forall x y z, x ++ z < y ++ z -> x < y.
intros.
setoid_replace x with ((x++z)++(--z));[idtac|setoid ring].
setoid_replace y with ((y++z)++(--z));[idtac|setoid ring].
apply cplus_lt_compat_r; assumption.
Qed.

Lemma csub_le_0 :
   forall a b, a <= b -> c0 <= b--a.
intros; setoid_replace (b--a) with (b++--a).
setoid_replace c0 with (a++--a).
apply cplus_le_compat.
assumption.
apply cle_refl.
setoid ring.
setoid ring.
Qed.

Lemma csub_lt_0 :
   forall a b, a < b -> c0 < b--a.
intros; setoid_replace (b--a) with (b++--a).
setoid_replace c0 with (a++--a).
apply cplus_lt_compat_r.
assumption.
setoid ring.
setoid ring.
Qed.

Theorem clt_div_mul :
   forall x y z, c0 < y ->  x/y < z -> x < z**y.
intros; apply cmul_lt_0_lt_reg_r with (c1/y).
apply cdiv_lt_0_compat_l.
assumption.
apply c0_clt_c1.
setoid_rewrite (cmul_sym x).
setoid_rewrite <- cdiv_decompose. 
apply pos_non_c0; assumption.
setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r; assumption.
Qed.

Theorem clt_copp_prem : 
  forall x y, -- x < -- y -> y < x.
intros; apply cplus_lt_reg_r with (--x).
apply cplus_lt_reg_r with (--y).
setoid_replace (x++ --x ++ --y) with (--y);[idtac|setoid ring].
setoid_replace (y++ --x ++ --y) with (--x);[idtac|setoid ring].
assumption.
Qed.

Theorem cmul_lt_le_compat :
  forall x y z t, c0 < x -> c0 < z -> x < y -> z <= t -> x ** z < y ** t.
intros; case (ceq_dec z t).
intros heq; setoid_rewrite <- heq; apply cmul_lt_compat_r; assumption.
intros; apply cmul_lt_compat; try assumption.
apply clt_decompose; assumption.
Qed.

Theorem cmul_copp_r : forall a b, a ** -- b == -- (a ** b).
intros; setoid ring.
Qed.

Theorem cle_copp_prem :
   forall x y, copp x <= copp y -> y <= x.
intros; setoid_rewrite <- (copp_copp x); setoid_rewrite <- (copp_copp y).
apply copp_le_compat.
assumption.
Qed.

Theorem cplus_lt_r :
   forall x y, c0 < y -> x < x++y.
intros; apply clt_decompose.
intros Ha; elim (pos_non_c0 _ H).
setoid_replace c0 with ((x++y)--x).
setoid ring.
setoid_rewrite <- Ha; setoid ring.
setoid_rewrite cadd_sym.
apply cplus_pos_simplify.
apply clt_cle_weak; auto.
Qed.
