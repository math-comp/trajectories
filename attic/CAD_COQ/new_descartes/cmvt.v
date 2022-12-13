Require Import QArith List Omega ZArith pol Zwf Recdef.

(* After a use of simpl, products of positive integers are replaced by
 products of positive numbers encapsulated in a Zpos constructor.  This
 precludes uses of some theorems.  We can undo this using the following
 tactic. *)

Ltac expand_Zpos_mult := 
  repeat match goal with |- context [Zpos(?a * ?b)] => 
     change (Zpos(a*b)) with ((Zpos a)*(Zpos b))%Z
  end.

(* We want to prove a simple and contructive approximation of the
 middle value theorem: if a polynomial is negative in a and positive in b,
 and a < b, then for any positive epsilon, there exists c and d, so that 
 a <= c < d <= b, the polynomial is negative in c and positive and d,
 and the variation between c and d is less than epsilon.  To prove this,
 we use a second polynomial, obtained by taking the the absolute value
 of each coefficient.

  We will use absolute values on rational numbers, the
  absolute value is defined using a max function, called Qmax.

  We first need a host of lemmas on the type of rational numbers, which
  is rather bare. *)

Lemma Qmult_lt_0_compat :
  forall x y, 0 < x -> 0 < y -> 0 < x * y.
intros x y Hx Hy.
assert (H0: 0 == 0 * y) by ring; rewrite H0.
apply Qmult_lt_compat_r; auto.
Qed.

Definition Qmax (x y:Q) := if Qlt_le_dec x y then y else x.

Lemma Qmax_le_l : forall x y, x <= Qmax x y.
intros x y; unfold Qmax; case (Qlt_le_dec x y); intro; apply Qle_refl ||
  apply Qlt_le_weak; assumption.
Qed.

Lemma Qmax_le_r : forall x y, y <= Qmax x y.
intros x y; unfold Qmax; case (Qlt_le_dec x y); intro; apply Qle_refl || auto.
Qed.

Lemma neg_opp_pos : forall x, x < 0 -> 0 < - x.
intros x; unfold Qlt, Qopp; simpl; intro; omega.
Qed.


Definition Qabs (x:Q) := Qmax x (-x).

Lemma Qabs_le : forall x, x <= Qabs x.
intros x; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); intro;
 apply Qle_refl || apply Qlt_le_weak; auto.
Qed.

(* This is a basic decomposition lemma, already present for most other
 numeric types. *)

Lemma Qplus_le_lt_compat :
  forall a b c d, a <= b -> c < d -> a + c < b + d.
intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] H1 H2.
  apply Qlt_le_trans with ((a1#a2) + (d1#d2)). 
unfold Qle, Qlt, Qplus in *; simpl in *.
repeat rewrite Zmult_plus_distr_l.
replace (a1* 'd2 * '(a2 * c2))%Z with (a1 * 'c2 * '(a2*d2))%Z.
apply Zplus_lt_compat_l.
replace (c1*'a2*'(a2*d2))%Z with  (('a2*'a2) *(c1*'d2))%Z.
replace (d1*'a2*'(a2*c2))%Z with (('a2*'a2)*(d1*'c2))%Z.
apply Zmult_lt_compat_l; auto.
compute; apply refl_equal.
replace ('(a2*c2))%Z with ('a2 *'c2)%Z by auto; ring.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto; ring.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto.
replace ('(a2*c2))%Z with ('a2 *'c2)%Z by auto; ring.
unfold Qlt, Qle, Qplus in *; simpl in *.
repeat rewrite Zmult_plus_distr_l.
replace (d1* 'b2 * '(a2 * d2))%Z with (d1 * 'a2 * '(b2*d2))%Z.
apply Zplus_le_compat_r.
replace (a1*'d2*'(b2*d2))%Z with  (('d2*'d2) *(a1*'b2))%Z.
replace (b1*'d2*'(a2*d2))%Z with (('d2*'d2)*(b1*'a2))%Z.
apply Zmult_le_compat_l; auto.
compute; intros; discriminate.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto; ring.
replace ('(b2*d2))%Z with ('b2 *'d2)%Z by auto; ring.
replace ('(b2*d2))%Z with ('b2 *'d2)%Z by auto.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto; ring.
Qed.

Lemma lt_opp_pos : forall x, -x < x -> 0 < x.
intros x ltx; 
assert (half_pos:0 < /(2#1)) by (unfold Qlt; simpl; omega).
setoid_replace x with ((x+x)*/(2#1)) by field.
setoid_replace 0 with ((x+-x)*/(2#1)) by ring.
apply Qmult_lt_compat_r; auto.
apply Qplus_le_lt_compat; try apply Qle_refl; auto.
Qed.

Lemma le_opp_pos : forall x, -x <= x -> 0 <= x.
intros x lex; assert (H02 : 0 == 0*/(2#1)) by ring;
assert (half_pos:0 <= /(2#1)) by (unfold Qle; simpl; omega).
rewrite H02.
setoid_replace x with ((x+x)*/(2#1)) by field.
apply Qmult_le_compat_r; auto.
setoid_replace 0 with (x+-x) by ring.
apply Qplus_le_compat; try apply Qle_refl; auto.
Qed.

Lemma Qabs_le_0 : forall x, 0 <= Qabs x.
intros x; unfold Qabs, Qmax.
case (Qlt_le_dec x (-x));[intros xneg | intros xpos].
apply Qlt_le_weak; apply lt_opp_pos; rewrite Qopp_opp; auto.
apply le_opp_pos; auto.
Qed.

Lemma Qopp_lt_compat : forall x y, x < y -> -y < -x.
intros x y xy; rewrite <- (Qplus_0_r (-x));
setoid_replace (-y) with (-x + (-y+x)) by ring.
setoid_replace 0 with (-y + y) by ring.
do 2 (apply Qplus_le_lt_compat; try apply Qle_refl); auto.
Qed.

Lemma Qopp_lt_lr : forall x y, x < - y -> y < - x.
intros x y xy; setoid_replace y with (- - y) by ring.
apply Qopp_lt_compat; assumption.
Qed.

Lemma Qopp_lt_rl : forall x y, -x < y -> - y < x.
intros x y xy; setoid_replace x with (- - x) by ring.
apply Qopp_lt_compat; assumption.
Qed.

Lemma Qopp_le_lr : forall x y, x <= - y -> y <= - x.
intros x y xy; setoid_replace y with (- - y) by ring.
apply Qopp_le_compat; assumption.
Qed.

Lemma Qopp_le_rl : forall x y, -x <= y -> - y <= x.
intros x y xy; setoid_replace x with (- - x) by ring.
apply Qopp_le_compat; assumption.
Qed.

Lemma pos_Qabs : forall x, 0 <= x -> Qabs x = x.
intros x xpos; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); auto.
intros xmx; assert (abs: 0 < -x) 
  by (apply lt_opp_pos; rewrite Qopp_opp; assumption).
apply Qopp_lt_compat in abs; change (-0) with 0 in abs;
 rewrite Qopp_opp in abs; apply Qlt_not_le in abs; contradiction.
Qed.

Lemma neg_Qabs : forall x, x <= 0 -> Qabs x = -x.
intros x xneg; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); auto.
intros mxx; unfold Qopp.
assert (Hx0 : x==0) by (apply Qle_antisym; auto; apply le_opp_pos; auto).
destruct x; unfold Qeq in Hx0; simpl in Hx0 |- *; rewrite Zmult_1_r in Hx0.
rewrite Hx0; simpl; auto.
Qed.

Lemma opp_Qabs_le :  forall x, -x <= Qabs x.
intros x; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); intro; auto;
 apply Qle_refl.
Qed.

Lemma Qabs_mult : forall x y, Qabs (x * y) == Qabs x * Qabs y.
intros x y; unfold Qabs, Qmax.
destruct (Qlt_le_dec x (- x)) as [hx | hx];
destruct (Qlt_le_dec y (- y)) as [hy | hy];
destruct (Qlt_le_dec (x * y) (-(x*y))) as [hp | hp]; try ring.
assert (nx:0 < -x) by (apply lt_opp_pos; rewrite Qopp_opp; auto).
assert (ny:0 < -y) by (apply lt_opp_pos; rewrite Qopp_opp; auto).
case Qlt_not_le with (1:=hp).
setoid_replace (-(x*y)) with (x*(-y)) by ring.
setoid_replace (x*y) with (-x*(-y)) by ring.
apply Qmult_le_compat_r; apply Qlt_le_weak; auto.
assert (nx:0 < -x) by (apply lt_opp_pos; rewrite Qopp_opp; auto).
assert (py:0 <= y) by (apply le_opp_pos; auto).
case (Qle_lt_or_eq _ _ py); intros hy'.
case Qle_not_lt with (1:=hp).
setoid_replace (-(x*y)) with (-x*y) by ring.
apply Qmult_lt_compat_r; auto.
rewrite <- hy'; ring.
assert (px:0<=x) by (apply le_opp_pos; auto).
case (Qle_lt_or_eq _ _ px); intros hx'.
case Qle_not_lt with (1:=hp).
setoid_replace (-(x*y)) with (x*(-y)) by ring.
repeat rewrite (Qmult_comm x); apply Qmult_lt_compat_r; auto.
rewrite <- hx'; ring.
case (Qlt_not_le _ _ hp).
setoid_replace (-(x*y)) with (-x*y) by ring.
apply Qmult_le_compat_r; auto; apply le_opp_pos; auto.
Qed.

Lemma Qabs_plus : forall x y, Qabs (x + y) <= Qabs x + Qabs y.
intros x y; unfold Qabs, Qmax; case (Qlt_le_dec x (-x));
 case (Qlt_le_dec y (-y)); case (Qlt_le_dec (x+y) (-(x+y))); 
 try (setoid_replace (-(x+y)) with (-x+ -y) by ring);
 try (intros; apply Qle_refl); intros xy xx yy.

case (Qle_not_lt _ _ xy); apply Qplus_le_lt_compat; auto;
 apply Qlt_le_weak; auto.
repeat rewrite (Qplus_comm x); apply Qplus_le_compat; auto; apply Qle_refl.
repeat rewrite <- (Qplus_comm y); apply Qplus_le_compat; 
 try (apply Qlt_le_weak; solve[auto]); apply Qle_refl.
apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; try apply Qle_refl; apply Qlt_le_weak; auto.
apply Qplus_le_compat; auto.
Qed.

Lemma Qabs_interval : forall x y z, x < y -> y < z ->
  Qabs y < Qmax (Qabs x) (Qabs z).
intros x y z xy yz; unfold Qabs at 1, Qmax at 1; case (Qlt_le_dec y (-y)).
intros yneg; apply Qlt_le_trans with (Qabs x); try apply Qmax_le_l.
assert (yneg': 0 < -y) by (apply lt_opp_pos; rewrite Qopp_opp; assumption).
assert (yneg'' : y < 0).
assert (H0 : 0 == y + -y) by ring; rewrite H0; clear H0.
set (u:= y + -y); 
 assert (H0 : y == y + 0) by ring; rewrite H0; clear H0; unfold u.
apply Qplus_le_lt_compat; auto; apply Qle_refl.
assert (xneg: x < 0) by (apply Qlt_trans with y; auto).
assert (xneg' : x < -x).
apply Qlt_trans with 0; auto; apply neg_opp_pos; auto.
unfold Qabs, Qmax; case (Qlt_le_dec x (-x)).
intros _; setoid_replace (-x) with ((-y + -x)+y) by ring.
set (u:= (-y+-x)+y); setoid_replace (-y) with ((-y + -x)+x) by ring;
 unfold u; clear u.
apply Qplus_le_lt_compat; try apply Qle_refl; auto.
intro; case (Qlt_not_le _ _ xneg'); auto.
intros ypos; apply le_opp_pos in ypos; 
 assert (zpos : 0 < z) by (apply Qle_lt_trans with y; auto).
apply Qlt_le_trans with (Qabs z); try apply Qmax_le_r.
rewrite pos_Qabs; auto; apply Qlt_le_weak; auto.
Qed.

Lemma inv_pos : forall x, 0 < x -> 0 < /x.
intros [ [| x| x] y]; unfold Qlt, Qinv; simpl; compute; auto.
Qed.

Lemma Qabs_non_pos : forall x, Qabs x <= 0 -> x == 0.
intros x; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)).
intros l1 l2; apply Qle_antisym; rewrite <- (Qopp_opp x); 
rewrite <- (Qopp_opp 0); apply Qopp_le_compat; auto.
apply le_opp_pos.
rewrite Qopp_opp; apply Qlt_le_weak; auto.
intros l1 l2; apply Qle_antisym; auto; apply le_opp_pos; auto.
Qed.

Lemma Qmult_le_reg_r : forall a b, 0 < b -> 0 <= a * b -> 0 <= a.
intros a b pb ab; assert (~ b==0) 
  by (intros q; rewrite q in pb; discriminate pb).
rewrite <- (Qdiv_mult_l a b); auto.
assert (d0 : 0 == 0 * /b) by ring; rewrite d0; clear d0.
unfold Qdiv; apply Qmult_le_compat_r; auto; 
 apply Qlt_le_weak; apply inv_pos; auto.
Qed.

Lemma Qmult_le_reg_l : forall a b, 0 < b -> 0 <= b * a -> 0 <= a.
intros a b pb ab; apply (Qmult_le_reg_r a b); auto; rewrite Qmult_comm; auto.
Qed.

(* Polynomial are only represented by the list of their coefficients.
  To any polynomial, we associate the absolute polynomial, whose
  coefficients are the absolute values of the initial coefficients. *)

Fixpoint Qabs_pol (l:list Q) :list Q :=
 match l with nil => nil | a::tl => Qabs a::Qabs_pol tl end.

(* The value of the absolute polynomial is always larger than the value
 of the initial polynomial. *)

Hint Resolve Qabs_le Qabs_le_0 opp_Qabs_le Qle_refl Qlt_le_weak Qinv_lt_0_compat.

Lemma Qabs_pol_bound :
  forall l x, Qabs (eval_pol l x) <= eval_pol (Qabs_pol l) (Qabs x).
induction l; intros x; simpl; unfold Qabs, Qmax;
  try solve [case (Qlt_le_dec 0 (-0)); simpl; intros; apply Qle_refl].
destruct (Qlt_le_dec (a + x * eval_pol l x) (-(a+x*eval_pol l x))) as
 [test|test]; (case_eq (Qlt_le_dec a (-a)); [intros aneg ta | intros apos ta]);
(case_eq (Qlt_le_dec x (-x)); [intros xneg tx | intros xpos tx]).
rewrite Qopp_plus; apply Qplus_le_compat; try apply Qle_refl.
setoid_replace (-(x*eval_pol l x)) with (-x*eval_pol l x) by ring.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
rewrite Qopp_plus; apply Qplus_le_compat; try apply Qle_refl.
setoid_replace (-(x*eval_pol l x)) with (x*-eval_pol l x) by ring.
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=-eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
rewrite Qopp_plus; apply Qplus_le_compat; auto.
setoid_replace (-(x*eval_pol l x)) with (-x*eval_pol l x) by ring.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
rewrite Qopp_plus; apply Qplus_le_compat; auto.
setoid_replace (-(x*eval_pol l x)) with (x*-eval_pol l x) by ring.
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=-eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
apply Qplus_le_compat; try (apply Qlt_le_weak; assumption).
setoid_replace (x*eval_pol l x) with (-x*-eval_pol l x) by ring.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
apply Qplus_le_compat; try (apply Qlt_le_weak; assumption).
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto);auto.
apply Qplus_le_compat; try apply Qle_refl.
setoid_replace (x*eval_pol l x) with (-x*-eval_pol l x) by ring.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
apply Qplus_le_compat; try apply Qle_refl.
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); auto.
Qed.

Lemma Qabs_pol_pos :
  forall l x, 0 <= x -> 0 <= eval_pol (Qabs_pol l) x.
induction l; intros x px; simpl;
  [apply Qle_refl | apply Qle_trans with (0+0*x)].
ring_simplify; apply Qle_refl.
apply Qplus_le_compat; [apply Qabs_le_0 | rewrite (Qmult_comm x)].
apply Qmult_le_compat_r; auto.
Qed.

Lemma Qabs_pol_increase :
  forall l x y, 0 <= x -> x <= y ->
    eval_pol (Qabs_pol l) x <= eval_pol (Qabs_pol l) y.
induction l; intros x y px xy; simpl.
apply Qle_refl.
apply Qplus_le_compat; 
  [apply Qle_refl | apply Qle_trans with (x*eval_pol (Qabs_pol l) y)].
repeat rewrite (Qmult_comm x); apply Qmult_le_compat_r; auto.
apply Qmult_le_compat_r; auto.
apply Qabs_pol_pos; apply Qle_trans with x; auto.
Qed.

(* A polynomial that has distinct values cannot be the null
 polynomial. *)

Lemma cm1 :
  forall l x y, eval_pol l x < eval_pol l y  -> exists a, l = a::(tail l).
intros l; case l.
simpl;intros x y abs; case (Qlt_not_le _ _ abs); apply Qle_refl.
intros a l' x y _; exists a; auto.
Qed.

(* To describe polynomial addition, multiplication by a scalar, and
  multiplication, we simply specify these operations so that their
  interpretation through polynomial evaluation returns the corresponding
  scalar operation. *)

Definition add_pol :
  forall l1 l2, {l' | forall x, eval_pol l1 x + eval_pol l2 x ==
  eval_pol l' x}.
induction l1 as [ | a l1 IHl1]; destruct l2 as [ | b l2].
exists (@nil Q); simpl; intros; ring.
exists (b::l2); simpl; intros; ring.
exists (a::l1); simpl; intros; ring.
destruct (IHl1 l2) as [l' q].
exists ((a+b)::l'); simpl; intros; rewrite <- q; ring.
Defined.

Definition s_mult_pol :
  forall a l, {l' | forall x, a * eval_pol l x == eval_pol l' x}.
intros a; induction l as [ | b l IHl]; simpl.
exists (@nil Q); simpl; intros; ring.
destruct IHl as [l' q]; exists ((a*b)::l'); simpl; intros; rewrite <- q; ring.
Defined.

Lemma mult_pol :
  forall l1 l2, {l' | forall x, eval_pol l1 x * eval_pol l2 x ==
   eval_pol l' x}.
induction l1 as [ | a l1 IHl1].
exists (@nil Q); simpl; intros; ring.
simpl.
intros l2; destruct (s_mult_pol a l2) as [l2a q].
destruct (IHl1 (0::l2)) as [l1l2x q1].
destruct (add_pol l1l2x l2a) as [l' q2].
exists l'; simpl; intros.
rewrite <- q2; rewrite <- q1; rewrite <- q; simpl; ring.
Qed.

Lemma translate_pol :
  forall l a, exists l', forall x, eval_pol l x == eval_pol l' (x - a).
induction l as [ | b l IHl]; intros a; simpl.
exists (@nil Q); simpl; intros; ring.
destruct (IHl a) as [l' q].
destruct (mult_pol (a::1::nil) l') as [l2 q2].
destruct (add_pol (b::nil) l2) as [l3 q3].
exists l3; intros x; rewrite <- q3; simpl;
   rewrite <- q2; rewrite q; simpl; ring.
Qed.

Add Morphism Qabs with signature Qeq ==> Qeq as Qabs_mor.
intros x1 x2 x1x2; unfold Qabs, Qmax; 
  destruct (Qlt_le_dec x1 (-x1)) as [hx1 | hx1];
  destruct (Qlt_le_dec x2 (-x2)) as [hx2 | hx2];
  rewrite x1x2 in hx1 |- *; intros; try apply Qeq_refl.
case Qlt_not_le with (1:= hx1); auto.
case Qlt_not_le with (1:= hx2); auto.
Qed.

Add Morphism eval_pol with signature @eq (list Q) ==> Qeq ==> Qeq as eval_pol_mor.
intros l x y; induction l.
simpl; intros; apply Qeq_refl.
simpl; intros Hxy; rewrite IHl; auto; rewrite Hxy; apply Qeq_refl.
Qed.

Lemma cm2 :
  forall l b, { c |
  forall x, 0 <= x -> x <= b -> Qabs (eval_pol l x - eval_pol l 0) <= c * x}.
intros l b.
destruct l as [ | a l].
exists 0; simpl; intros; ring_simplify; apply Qle_refl.
simpl; exists (eval_pol (Qabs_pol l) b); intros x px xb; simpl.
match goal with |- Qabs(?v) <= _ =>
  assert (q: v == x*eval_pol l x) by ring; rewrite q
end.
rewrite Qabs_mult; rewrite (pos_Qabs x); auto; rewrite (Qmult_comm x).
apply Qmult_le_compat_r; auto.
apply Qle_trans with (2 := Qabs_pol_increase l x b px xb).
pattern x at 2; replace x with (Qabs x); [apply Qabs_pol_bound | idtac].
apply pos_Qabs; auto.
Defined.

Lemma QZ_bound : forall x:Q, 0 <= x -> {n | x <= n#1}.
intros [n d]; exists(Zdiv n (Zpos d)+1)%Z.
assert (dpos : (('d) > 0)%Z) by apply (refl_equal Gt).
unfold Qle; simpl; rewrite Zmult_1_r; rewrite Zmult_plus_distr_l.
pattern n at 1; rewrite (Z_div_mod_eq n ('d)); auto.
rewrite (Zmult_comm ('d)); apply Zplus_le_compat; auto with zarith.
rewrite Zmult_1_l; destruct (Z_mod_lt n ('d)) as [_ H2]; auto; 
apply Zlt_le_weak; apply H2.
Defined.

Lemma Qdiv_lt_0_compat : forall x y, 0 < x -> 0 < y -> 0 < x / y.
intros x [[ | p | p] d] Hx Hy; unfold Qdiv, Qinv; simpl.
unfold Qlt in Hy; simpl in Hy; elimtype False; omega.
rewrite Qmult_comm;
assert (H0 : 0 == 0 * x) by ring; rewrite H0.
apply Qmult_lt_compat_r; auto.
unfold Qlt in Hy; simpl in Hy; discriminate Hy.
Qed.

Lemma cm3 :
  forall b, 0 < b -> forall l, 
   {c |
    forall x y, 0 <= x -> x <= y -> y <= b -> 
    Qabs (eval_pol l y - eval_pol l x) <= c*(y-x)}.
intros b pb; induction l.
exists 0; intros x y px xy yb; simpl; ring_simplify.
assert (d0 : 0-0 == 0) by ring.
rewrite d0; apply Qle_refl.
destruct IHl as [c cp].
exists (eval_pol (Qabs_pol l) b+c*b); intros x y px xy yb; simpl.
match goal with |- Qabs (?e) <= _ =>
  setoid_replace e with 
     ((y-x)*eval_pol l y + x*(eval_pol l y - eval_pol l x)) by ring end.
apply Qle_trans with
   (1:= Qabs_plus ((y-x)*eval_pol l y) (x*(eval_pol l y - eval_pol l x))).
rewrite Qmult_plus_distr_l; apply Qplus_le_compat.
assert (xmy: 0 <= y - x).
setoid_replace 0 with (x+ -x) by ring.
unfold Qminus; apply Qplus_le_compat; auto.
rewrite Qabs_mult; rewrite (pos_Qabs (y-x)); auto.
rewrite (Qmult_comm (y-x)); apply Qmult_le_compat_r; auto.
assert (py: 0 <= y) by (apply Qle_trans with x; auto).
apply Qle_trans with (2:= Qabs_pol_increase l y b py yb).
pattern y at 2; rewrite <- (pos_Qabs y py).
apply Qabs_pol_bound.
setoid_replace (c*b*(y-x)) with (b * (c*(y-x))) by ring.
rewrite Qabs_mult; rewrite (pos_Qabs x px).
apply Qle_trans with (b*Qabs (eval_pol l y - eval_pol l x)).
apply Qmult_le_compat_r; auto.
apply Qle_trans with y; auto.
repeat rewrite (Qmult_comm b); apply Qmult_le_compat_r; auto.
Qed.

Definition find_pair : forall A:Type, forall P:A->Prop, forall Q:A->A->Prop,
    forall l:list A, forall a b:A, P a -> ~P b ->
    (forall l1 l2 x y, a::l++b::nil=l1++x::y::l2 -> Q x y) ->
    (forall x, In x l -> {P x}+{~P x}) ->
    {c :A & { d | Q c d /\ P c /\ ~P d}}.
intros A P Q; induction l; simpl; intros a' b' Pa Pb connect dec.
exists a'; exists b'; split; auto.
apply (connect nil nil); auto.
case (dec a); auto.
intros Pa1; destruct (IHl a b' Pa1 Pb) as [c [d [cd [Pc Pd]]]].
intros l1 l2 x y q; apply (connect (a'::l1) l2); rewrite q; simpl;auto.
intros x inx; apply (dec x); auto.
exists c; exists d; auto.
exists a'; exists a; split; auto.
apply (connect nil (l++b'::nil)); auto.
Qed.

Function ns (p n:Z) {measure Zabs_nat n} : list Z :=
   if Z_le_dec n 0 then p::nil else (p-n)%Z::ns p (n-1)%Z.
intros; apply Zabs_nat_lt; omega.
Defined.

Lemma ns_head : forall p n, (0 <= n)%Z -> exists l, ns p n = (p - n)%Z::l.
intros p n; functional induction ns p n.
intros; assert (n = 0)%Z by omega; subst n; ring_simplify (p-0)%Z; exists nil; auto.
intros _; destruct IHl  as [l' pl'].
omega.
exists ((p-(n-1))%Z::l'); rewrite pl'; auto.
Qed.

Lemma ns_step : forall p n, forall l1 l2 x y, (0 <= n)%Z ->
  ns p n = l1++x::y::l2 -> y = (x + 1)%Z.
intros p n; functional induction ns p n.
intros; repeat (destruct l1; try discriminate).
assert (np1 : (0 <= n-1)%Z) by omega.
intros l1 l2 x y np q; destruct l1 as [ | a l1].
destruct (ns_head p (n-1)  np1) as [l' ql'].
rewrite ql' in q; simpl in q; injection q; intros; subst y x; ring.
apply (IHl l1 l2); auto.
simpl in q; injection q; auto.
Qed.

Lemma ns_tail : forall p n, exists l, ns p n = l++p::nil.
intros p n; functional induction ns p n.
exists nil; auto.
destruct IHl as [l ql]; rewrite ql; exists ((p-n)%Z::l); auto.
Qed.

Lemma ns_bounds : forall p n x l1 l2, (0 <= n)%Z -> ns p n = l1++x::l2 -> 
        (p -n <= x <= p)%Z.
intros p n; functional induction ns p n.
intros x [ | a l1].
simpl; intros l2 np q; injection q;intros; omega.
intros; destruct l1; discriminate.
intros x [ | a l1];
simpl; intros l2 np q; injection q; intros; try omega.
assert (p - (n-1) <= x <= p)%Z.
apply (IHl x l1 l2); auto; omega.
omega.
Qed.


Lemma map_contiguous :
forall A B : Type, forall f : A -> B, forall l,
forall l1 l2 a b, map f l = l1++a::b::l2 ->
  {l'1 :list A & {l'2 : list A & {x:A & {y:A | l1 = map f l'1 /\ l2= map f l'2 /\ a = f x /\
        b = f y /\ l = l'1++x::y::l'2}}}}.
intros A B f l; induction l.
simpl; intros; destruct l1; discriminate.
intros l1 l2 b1 b2; destruct l1 as [ | a' l1].
  simpl; intros q.
destruct l as [|a'' l]; try discriminate q; simpl in q.
injection q; intros.
exists nil; exists l; exists a; exists a''; auto.
simpl; intros q.
injection q; intros q' q''.
destruct (IHl _ _ _ _ q') as [r1 [r2 [x [y [q1 [ q2 [qx [qy ql]]]]]]]].
exists (a::r1); exists r2; exists x; exists y; repeat apply conj; auto.
simpl; rewrite q'', q1; auto.
simpl; rewrite ql; auto.
Qed.

Lemma map_app :
  forall A B:Type, forall f : A -> B, forall l1 l2, map f (l1++l2) = map f l1 ++ map f l2.
intros A B f l1; induction l1; simpl; auto.
intros l2; rewrite IHl1; auto.
Qed.

Lemma non_empty_tail : 
  forall (A:Type) (a:A) l, exists l', exists b, a::l = l'++(b::nil).
intros A a l; generalize a; clear a; induction l.
exists nil; exists a; auto.
intros a'; destruct (IHl a) as [l' [b q]]; rewrite q.
exists (a'::l'); exists b; auto.
Qed.

Lemma Qfrac_add_Z_l : forall a b c, (a#1) + (b#c) == (a*'c+b#c).
intros;unfold Qeq; simpl; ring.
Qed.

Lemma constructive_mvt :
  forall l x y, x < y -> eval_pol l x < 0 -> 0 <= eval_pol l y  ->
       forall epsilon, 0 < epsilon ->
       exists x', exists y',  -epsilon <= eval_pol l x' /\
         eval_pol l x' < 0 /\ 0 <= eval_pol l y' /\
         eval_pol l y' <= epsilon /\ x <= x' /\ x' < y' /\ y' <= y.
intros l a b ab nla plb.
destruct (translate_pol l a) as [l' q].
assert (ba':0 < b-a).
setoid_replace 0 with (a-a) by ring.
unfold Qminus; repeat rewrite <- (Qplus_comm (-a));
apply Qplus_le_lt_compat; auto.
assert (ba:~ b-a == 0).
intros abs; case (Qlt_not_eq 0 (b-a) ba'); rewrite abs; apply Qeq_refl.
destruct (cm3 (b-a) ba' l') as [c pc].
assert (mpolapos : 0 < -eval_pol l a) by (apply Qopp_lt_lr; assumption).
assert (t1 : a-a == 0) by ring.
assert (cpos: 0 < c).
setoid_replace 0 with (0 */(b-a)) by ring.
setoid_replace c with ((c*(b-a-(a-a)))/(b-a)) by (field;auto).
apply Qmult_lt_compat_r; auto.
apply Qlt_le_trans with (Qabs (eval_pol l' (b-a) - eval_pol l' (a-a))).
match goal with |- 0 < Qabs(?a) => assert (ineq: 0 < a) end.
repeat rewrite <- q; setoid_replace 0 with (0+0) by ring.
apply Qplus_le_lt_compat; auto.
rewrite pos_Qabs; auto.
apply pc; try solve[rewrite t1; auto | auto].
assert (cn0 : ~c==0) by (apply Qnot_eq_sym; apply Qlt_not_eq ; auto).
intros epsilon pe.
assert (en0 : ~ epsilon == 0) by (apply Qnot_eq_sym; apply Qlt_not_eq; auto).
assert (pdiv: 0 < (b-a)*c/epsilon) by (repeat apply Qmult_lt_0_compat; auto).
destruct (QZ_bound ((b-a)*c/(epsilon))) as [n qn]; auto.
assert (pn : (0 < n)%Z).
destruct ((b-a)*c/epsilon) as [nu de]; unfold Qle in qn, pdiv;
simpl in qn, pdiv.  unfold Qlt in pdiv; simpl in pdiv; rewrite Zmult_1_r in pdiv, qn.
assert (pdiv' := Zlt_le_trans _ _ _ pdiv qn).
apply Zmult_lt_0_reg_r with ('de)%Z; try solve [compute; auto with zarith].
assert (mkl: 
  exists l, forall l1 l2 x y, a::l++b::nil = l1++x::y::l2 ->
      y-x == (b-a)/(n#1) /\ exists k, x == a + (b-a)*(k#1)/(n#1) /\ (0<= k <= n-1)%Z).
case (Z_eq_dec n 1).
intros n1; exists nil; intros l1 l2 x y; destruct l1; simpl;
  intros ql.
injection ql; intros; subst x y n; split;
 [field | exists 0%Z; split; [field | omega]].
repeat (destruct l1; try discriminate).
intros nn1; exists (map  (fun x => a + (b-a)*((x#1)/(n#1))) (ns (n-1) (n-2))).
intros l1 l2  x y; destruct l1.
assert (0 <= n-2)%Z by omega.
destruct (ns_head (n-1) (n-2)) as [a1 qa1];auto; rewrite qa1; simpl.
replace ((n-1)-(n-2))%Z with 1%Z by ring.
intros ql; injection ql; intros; subst x y; split.
field; unfold Qeq; simpl; omega.
exists 0%Z; split;[field; unfold Qeq; simpl; omega | omega].
simpl; intros q'; injection q'; clear q'.
destruct l2 as [| d l2].
replace (x::y::nil) with ((x::nil)++(y::nil)). rewrite  <- app_ass.
intros q' _; elim (app_inj_tail  _ _ _ _ q'); clear q'; intros q' q''.
destruct (ns_tail (n-1)(n-2)) as [l3 ql3].
rewrite ql3 in q'.
rewrite map_app in q'; simpl in q'.
elim (app_inj_tail _ _ _ _ q'); clear q'; intros q' q3'.
subst x y.
assert (t0:(n-1#1)/(n#1) == 1 - /(n#1)).
setoid_replace 1 with ((n#1)/(n#1)).
setoid_replace (/(n#1)) with (1/(n#1)).
unfold Qdiv.
match goal with |- _ == ?a =>
    setoid_replace a with (((n#1) - 1) * /(n#1)) by ring end.
apply Qmult_comp.
unfold Qeq; simpl; ring.
apply Qeq_refl.
field; unfold Qeq; simpl; omega.
field; unfold Qeq; simpl; omega.
rewrite t0.
split.
field; unfold Qeq; simpl; omega.
exists (n-1)%Z; split.
unfold Qdiv; rewrite Qmult_assoc; apply Qeq_refl.
omega.
simpl; auto.
unfold Qdiv.
destruct (non_empty_tail  _ d l2) as [l3 [e qe]].
rewrite qe.
replace (l1++x::y::l3++e::nil) with ((l1++x::y::l3)++(e::nil)).
intros q' _.
destruct (app_inj_tail _ _ _ _ q') as [q'' _].
destruct (map_contiguous _ _ (fun x => a+(b-a)*((x#1)*/(n#1)))
             _ _ _ _ _ q'') as [l'1 [l'2 [n1 [n2 [_ [_ [qx [qy st]]]]]]]].
subst x y; setoid_replace (n2#1) with ((n1#1)+1).
split.
ring.
exists n1; split. 
rewrite Qmult_assoc; apply Qeq_refl.
apply ns_bounds in st; omega.
rewrite Qfrac_add_Z_l; rewrite Zmult_1_r.
apply ns_step in st; try omega; rewrite st; apply Qeq_refl.
rewrite app_ass; auto.
destruct mkl as [sl qsl].
destruct (find_pair Q (fun x => eval_pol l x < 0) 
                  (fun x y => y - x == (b-a)/(n#1) /\
                     exists k, x == a + (b-a)*(k#1) /(n#1) /\
                     (0 <= k <= n-1)%Z)
                 sl a b) 
  as [a' [b' [[A1 [k [A4 A5]]][A2 A3]]]]; auto.
apply Qle_not_lt; auto.
intros x _; case (Qlt_le_dec (eval_pol l x) 0); auto.
intros H; right; apply Qle_not_lt; auto.
clear qsl sl.
exists a'; exists b'.
assert (aa':a <= a').
(setoid_replace a with (a+0) by ring); rewrite A4.
apply Qplus_le_compat; try apply Qle_refl.
repeat apply Qmult_le_0_compat; auto.
unfold Qle; simpl; omega.
apply Qlt_le_weak; apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
assert (bb': b' <= b).
setoid_replace b with (a + (b-a) * (n#1) * /(n#1)) by
 field; unfold Qeq; simpl; try omega.
(setoid_replace b' with (a' + (b' - a')) by ring); rewrite A1, A4.
rewrite <- Qplus_assoc; apply Qplus_le_compat; try apply Qle_refl.
unfold Qdiv;
 match goal with |- ?f <= _ => setoid_replace f with ((b-a)* ((k#1)+1) * /(n#1))
 end.
apply Qmult_le_compat_r.
repeat rewrite (Qmult_comm (b-a)); apply Qmult_le_compat_r.
rewrite Qfrac_add_Z_l; unfold Qle; simpl; omega.
auto.
apply Qlt_le_weak; apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
field; unfold Qeq; simpl; omega.
assert (ab': a' < b').
setoid_replace a' with (a' + 0) by ring.
(setoid_replace b' with (a' + (b' - a')) by ring); rewrite A1.
apply Qplus_le_lt_compat; try apply Qle_refl; apply Qmult_lt_0_compat; auto.
apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
assert (epsban: (b-a)*c / (n#1) <= epsilon).
apply Qmult_lt_0_le_reg_r with ((n#1) / epsilon).
apply Qmult_lt_0_compat; auto.
unfold Qlt; simpl; omega.
match goal with |- ?f1 <= ?f2 =>
  (setoid_replace f2 with (n#1) by field; auto);
  (setoid_replace f1 with ((b-a)*c /epsilon) by
   (field; split; auto; unfold Qeq; simpl; omega)); auto
end.
split;[idtac | split; auto].
(* start with epsilon and a'. *)
apply Qopp_le_rl.
apply Qle_trans with (eval_pol l b' - eval_pol l a').
setoid_replace (-eval_pol l a') with (0 - eval_pol l a') by ring.
apply Qplus_le_compat; auto; apply Qnot_lt_le; auto.
repeat rewrite q.
rewrite <- (pos_Qabs (eval_pol l' (b'-a) - eval_pol l' (a'-a))).
apply Qle_trans with (c*((b'-a)-(a'-a))).
apply pc; auto.
(setoid_replace 0 with (a - a) by ring); apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; auto.
apply Qplus_le_compat; auto.
setoid_replace (b' -a -(a'-a)) with (b' -a') by ring.
rewrite A1.
unfold Qdiv; rewrite Qmult_assoc; rewrite (Qmult_comm c); exact epsban.
repeat rewrite <- q.
(setoid_replace 0 with (0+0) by ring);apply Qplus_le_compat.
apply Qnot_lt_le; auto.
apply Qopp_le_lr.
(setoid_replace 0 with (-0) by ring);apply Qlt_le_weak; assumption.
split.
apply Qnot_lt_le; auto.
split; auto.
apply Qle_trans with (eval_pol l' (b' -a) -eval_pol l' (a' -a)).
setoid_replace (eval_pol l b') with (eval_pol l b' + 0) by ring.
apply Qplus_le_compat.
rewrite q; apply Qle_refl.
rewrite <- q; apply Qopp_le_lr; auto.
rewrite <- (pos_Qabs (eval_pol l' (b'-a) - eval_pol l' (a'-a))).
apply Qle_trans with (c*((b'-a)-(a'-a))).
apply pc; auto.
(setoid_replace 0 with (a - a) by ring); apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; auto.
apply Qplus_le_compat; auto.
setoid_replace (b' -a -(a'-a)) with (b' -a') by ring.
rewrite A1.
unfold Qdiv; rewrite Qmult_assoc; rewrite (Qmult_comm c); exact epsban.
repeat rewrite <- q.
(setoid_replace 0 with (0+0) by ring);apply Qplus_le_compat.
apply Qnot_lt_le; auto.
apply Qopp_le_lr.
apply Qlt_le_weak; assumption.
Qed.