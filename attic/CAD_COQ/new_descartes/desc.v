Require Import QArith List Omega ZArith (* sos *) pol cmvt.

Open Scope Q_scope.

(* Defining function over lists of rationals that find lists containing
  exactly one alternation, from negative to positive values. *)

Fixpoint all_zero (l:list Q) : bool :=
  match l with nil => true
  | a::tl => if Qeq_dec a 0 then all_zero tl else false
 end.

Fixpoint all_pos_or_zero (l:list Q) : bool :=
  match l with nil => true
  | a::tl => if Qlt_le_dec a 0 then false else all_pos_or_zero tl
  end.

Fixpoint all_neg_or_zero (l:list Q) : bool :=
  match l with nil => true
  | a::tl => if Qlt_le_dec 0 a then false else all_neg_or_zero tl
  end.

(* alternate_1 is true for lists containing at least one strictly positive
  value followed by only positive values, and preceeded by only negative
  or zero values. *)
Fixpoint alternate_1 (l:list Q) : bool :=
  match l with nil => false
  | a::tl => if Qlt_le_dec 0 a then all_pos_or_zero tl else alternate_1 tl
  end.

(* alternate is true for lists that contain one negative value, followed
 by an arbitrary number of non-positive values, followed
 by one strictly positive value, followed by only non-negative values.
*)
Fixpoint alternate (l:list Q) : bool :=
 match l with nil => false
 | a::tl => if Qlt_le_dec a 0 then alternate_1 tl else 
   if Qeq_dec a 0 then alternate tl else false
 end.

Lemma Qle_not_eq_lt : forall a b:Q, a <= b -> ~a==b -> a < b.
unfold Qlt, Qeq, Qle; intros; omega.
Qed.

Hint Resolve Qle_not_eq_lt.

Lemma alternate1_decompose :
  forall l, alternate_1 l = true ->
    (exists l1, exists l2, exists l3, exists a, exists b,
      l = l1 ++ a::l2 ++ b::l3 /\
      all_neg_or_zero l1 = true /\ a < 0 /\ all_zero l2 = true /\ 0 < b /\
      all_pos_or_zero l3 = true) \/
    exists l2, exists l3, exists b,
      l = l2++b::l3 /\
      all_zero l2 = true /\ 0 < b /\ all_pos_or_zero l3 = true.
induction l; simpl; try (intros; solve[discriminate]).
case_eq (Qlt_le_dec 0 a).
intros; right; exists (@nil Q); exists l; exists a; auto.
intros Ha Htest Hl; case (IHl Hl).
intros [l1 [l2 [l3 [a' [b [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]].
left; exists (a::l1); exists l2; exists l3; exists a'; exists b.
split; subst l; simpl; auto.
rewrite Htest; auto.
intros [l2 [l3 [b [H1 [H2 [H3 H4]]]]]]; case_eq (Qeq_dec a 0); intros Ha1 Heq.
right; exists (a::l2); exists l3; exists b; split; subst l; auto.
simpl; rewrite Heq; auto.
left;exists (@nil Q); exists l2; exists l3; exists a; exists b; subst; auto 10.
Qed.

Lemma Qmult_le_0_compat :
 forall x y, 0 <= x -> 0 <= y -> 0 <= x * y.
intros x y Hx Hy; case (Qle_lt_or_eq _ _ Hx); clear Hx; intros Hx.
case (Qle_lt_or_eq _ _ Hy); clear Hy; intros Hy.
assert (H0 : 0 == 0 * y) by ring; rewrite H0.
apply Qlt_le_weak; apply Qmult_lt_compat_r; auto.
rewrite <- Hy; assert (H0 : x * 0 == 0) by ring; rewrite H0; apply Qle_refl.
rewrite <- Hx; assert (H0 : 0 * y == 0) by ring; rewrite H0; apply Qle_refl.
Qed.

  
Lemma l1 : forall l, all_pos_or_zero l = true ->
  forall x, 0 < x -> 0 <= eval_pol l x.
induction l.
simpl; intros; apply Qle_refl.
simpl; case (Qlt_le_dec a 0); intros Ha Hl x Hx.
discriminate.
rewrite <- (Qplus_0_l 0).
apply Qplus_le_compat; auto.
apply Qmult_le_0_compat; auto.
Qed.

Lemma l2 : forall l, all_pos_or_zero l = true ->
  forall x y, 0 < x -> x < y -> eval_pol l x <= eval_pol l y.
induction l.
simpl; intros; apply Qle_refl.
simpl; case (Qlt_le_dec a 0); intros Ha Hl x y Hx Hy.
discriminate.
apply Qplus_le_compat.
apply Qle_refl.
apply Qle_trans with (y * eval_pol l x).
case (Qle_lt_or_eq _ _ (l1 l Hl x Hx)); intros Hpx.
apply Qlt_le_weak; apply Qmult_lt_compat_r; auto.
repeat rewrite <- Hpx.
assert (H0 : x * 0 == 0) by ring; rewrite H0.
assert (H1 : y * 0 == 0) by ring; rewrite H1.
apply Qle_refl.
repeat (rewrite (Qmult_comm y)).
case (Qle_lt_or_eq _ _ (IHl Hl x y Hx Hy)); intros Hp.
apply Qlt_le_weak; apply Qmult_lt_compat_r; auto.
apply Qlt_trans with x; auto.
rewrite Hp; apply Qle_refl.
Qed.

Lemma half_lt : forall a b, 0 < a -> 0 <  b -> a / ((2#1)* b) < a / b.
intros a b Ha Hb; unfold Qdiv; repeat rewrite (Qmult_comm a).
apply Qmult_lt_compat_r; auto.
unfold Qlt; destruct b as [[|n|n] d]; simpl.
unfold Qlt in Hb; simpl in Hb; omega.
repeat rewrite (Pmult_comm d).
replace (' (xO n * d))%Z with ((2 * ' n) * ' d)%Z by solve[auto].
replace ('(n*d))%Z with ('n * 'd)%Z by solve[auto].
assert (0 < 'n * ' d)%Z by auto.
rewrite <- Zmult_assoc; omega.
discriminate Hb.
Qed.

Definition inv (l:list Q) : Prop :=
  forall epsilon, 0 < epsilon ->
    exists x, (forall y, 0 < y -> y <= x -> eval_pol l y <= eval_pol l x) /\
      (forall y z, x <= y -> y < z ->  eval_pol l y <= eval_pol l z) /\
      0 < x /\ x * eval_pol l x < epsilon.

Lemma l3 : forall l, all_pos_or_zero l = true -> inv l.
 intros l Hl epsilon Heps; assert (H1 := l1 l Hl); assert (H2 := l2 l Hl).
assert (H01: 0 < 1) by (unfold Qlt; simpl; omega).
case (Qle_lt_or_eq _ _ (H1 1 H01)).
intros Hp1; case (Qlt_le_dec 1 (epsilon / eval_pol l 1)).
intros H1p1; exists 1.
split.
intros y H0y Hy1; case (Qle_lt_or_eq _ _ Hy1); clear Hy1; intros Hy1.
apply H2; auto.
rewrite Hy1; apply Qle_refl.
split.
intros y z Hy Hyz; apply H2; auto.
apply Qlt_le_trans with 1; auto.
assert (Hdec : epsilon == (epsilon / eval_pol l 1) * eval_pol l 1).
rewrite Qmult_comm; rewrite Qmult_div_r.
auto with qarith.
intros Habs; unfold Qeq in Habs; unfold Qlt in Hp1; simpl in *; omega.
split; auto.
rewrite Hdec; apply Qmult_lt_compat_r; auto.
intros H1p1.
exists (epsilon / ((2#1)*eval_pol l 1)).
assert (Hepspl1 : 0 < epsilon/ ((2#1)*eval_pol l 1)).
apply Qdiv_lt_0_compat; auto.
apply Qmult_lt_0_compat; auto.
split.
intros y Hy Hy2; case (Qle_lt_or_eq _ _ Hy2); clear Hy2; intros Hy2.
apply H2; auto.
rewrite Hy2; apply Qle_refl.
split.
intros y z Hy Hyz; apply H2; auto.
apply Qlt_le_trans with (epsilon /((2#1)*eval_pol l 1)); auto.
split; auto.
apply Qlt_le_trans with (epsilon /eval_pol l 1 * eval_pol l 1).
assert (Heps1: epsilon == epsilon / eval_pol l 1 * eval_pol l 1).
rewrite Qmult_comm; rewrite Qmult_div_r.
auto with qarith.
assert (Habs : ~ 0 == eval_pol l 1) by (apply Qlt_not_eq; auto).
intro H'; case Habs; rewrite H'; apply Qeq_refl.
destruct (Qeq_dec (eval_pol l (epsilon / ((2#1)*eval_pol l 1))) 0)
  as [Hb1 |Hb1].
rewrite Hb1; ring_simplify; rewrite <- Heps1; auto.
apply Qlt_le_trans with (epsilon /eval_pol l 1 *
      eval_pol l (epsilon / ((2#1)*eval_pol l 1))).
apply Qmult_lt_compat_r.
case (Qle_lt_or_eq _ _ (H1 _ Hepspl1)); intro; auto.
case Hb1; apply Qeq_sym; auto.
apply half_lt; auto.
repeat rewrite (Qmult_comm (epsilon /eval_pol l 1)).
case (Qeq_dec (eval_pol l (epsilon /((2#1)*eval_pol l 1)))
              (eval_pol l 1)); intros Hb2.
rewrite Hb2; apply Qle_refl.
assert (Hepspl2 : epsilon / ((2#1)*eval_pol l 1) < 1).
apply Qlt_le_trans with (epsilon/eval_pol l 1); auto.
apply half_lt; auto.
case (Qle_lt_or_eq _ _ (H2 _ _ Hepspl1 Hepspl2)).
intros Hx.
apply Qlt_le_weak; apply Qmult_lt_compat_r; auto.
apply Qdiv_lt_0_compat; auto.
intros Hx; rewrite Hx; apply Qle_refl.
rewrite Qmult_comm; rewrite Qmult_div_r; auto.
assert (Hx: ~ 0 == eval_pol l 1) by (apply Qlt_not_eq; auto).
intro Hy; case Hx; rewrite Hy; apply Qeq_refl.
intros; exists 1.
split.
intros y Hy Hy'.
case (Qle_lt_or_eq _ _ Hy'); clear Hy'; intros Hy'.
apply H2; auto.
rewrite Hy'; apply Qle_refl.
split.
intros y z Hy Hz; apply H2; auto.
apply Qlt_le_trans with (1:= H01); auto.
rewrite <- H; (setoid_replace (1*0) with 0 by ring); auto.
Qed.

Lemma add_1_lt : forall x, x < x + 1.
intros x; assert (H:x+0 < x + 1) by
 (apply Qplus_le_lt_compat; [ apply Qle_refl | unfold Qlt; simpl; omega]).
 rewrite Qplus_0_r in H; auto.
Qed.

Lemma Qpos_non_zero : forall x, 0 < x -> ~ x == 0.
intros x pos eq0; apply (Qlt_not_eq _ _ pos).
rewrite eq0; apply Qeq_refl.
Qed.

Lemma inv_pos : forall x, 0 < x -> 0 < /x.
intros [ [| x| x] y]; unfold Qlt, Qinv; simpl; compute; auto.
Qed.

Axiom constructive_mvt :
  forall l x y, x < y -> eval_pol l x < 0 -> 0 < eval_pol l y  ->
       forall epsilon, 0 < epsilon ->
       exists x', exists y',  -epsilon < eval_pol l x' /\
         eval_pol l x' < 0 /\ 0 < eval_pol l y' /\
         eval_pol l y' < epsilon /\ x < x' /\ x' < y' /\ y' < y.

Definition inv2 (l:list Q) : Prop :=
  forall epsilon, 0 < epsilon ->
    exists x, (forall y, 0 < y -> y <= x -> eval_pol l y <= eval_pol l x) /\
      (forall y z, x <= y -> y < z ->  eval_pol l y <= eval_pol l z) /\
      0 < x /\ 0 < eval_pol l x /\ x * eval_pol l x < epsilon.

Lemma min3 :
  forall a b c, 0 < a -> 0 < b -> 0 < c ->
   exists d, d <= a /\ d <= b /\ d <= c /\ 0 < d.
intros a b c Ha Hb Hc; case (Qlt_le_dec a b); intros Hab.
case (Qlt_le_dec a c); intros Hac.
exists a; repeat apply conj; apply Qle_refl || (apply Qlt_le_weak; assumption)
             || assumption.
exists c; repeat apply conj; apply Qle_refl || assumption
             || (apply Qlt_le_weak; eapply Qle_lt_trans; eauto).
case (Qlt_le_dec b c); intros Hbc.
exists b; repeat apply conj; apply Qle_refl || assumption
             || (apply Qlt_le_weak; assumption).
exists c; repeat apply conj; apply Qle_refl || assumption
             || (eapply Qle_trans; eauto).
Qed.

Lemma l5 : forall a l, a < 0 -> inv2 l -> inv2 (a::l).
intros a l aneg il.
assert (aneg' := aneg); apply neg_opp_pos in aneg.
destruct (il _ aneg) as [x [H1 [H2 [H3 [H4 H5]]]]].
assert (eval_pol (a::l) x < 0).
simpl.
assert (H0 : 0 == a + - a) by ring; rewrite H0; apply Qplus_le_lt_compat; auto.
assert
  (H1' : forall y, 0 < y -> y <= x -> y * eval_pol l y <= x * eval_pol l x).
intros y Hy Hyx; apply Qle_trans with (y * eval_pol l x).
repeat rewrite (Qmult_comm y); apply Qmult_le_compat_r; auto.
apply Qmult_le_compat_r; auto; apply Qlt_le_weak; auto.
assert (H2' : 
          forall y z, x <= y -> y < z -> y * eval_pol l y <= z * eval_pol l z).
intros y z Hy Hyz; apply Qle_trans with (y * eval_pol l z).
repeat rewrite (Qmult_comm y); apply Qmult_le_compat_r; auto.
apply Qlt_le_weak; apply Qlt_le_trans with x; auto.
apply Qmult_le_compat_r; auto; apply Qlt_le_weak; auto.
apply Qlt_le_trans with (eval_pol l x); auto.
apply H2; apply Qle_refl || (apply Qle_lt_trans with y; auto).
assert (H0 : 0 == a + -a) by ring.
assert (negval : eval_pol (a::l) x < 0).
rewrite H0; simpl; apply Qplus_le_lt_compat; auto; apply Qle_refl.
assert (max_x_val : exists b, x < b /\ (-a /eval_pol l x) < b).
case (Qlt_le_dec x (-a/eval_pol l x)); intros cmp.
exists (-a /eval_pol l x + 1); split.
apply Qlt_trans with (1:=cmp); apply add_1_lt.
apply add_1_lt.
exists (x+1); split.
apply add_1_lt.
apply Qle_lt_trans with (1:=cmp); apply add_1_lt.
destruct max_x_val as [y [yx val]].
assert(posval : 0 < eval_pol (a::l) y).
rewrite H0; simpl; apply Qplus_le_lt_compat; auto.
apply Qle_lt_trans with (-a /eval_pol l x * eval_pol l x).
rewrite Qmult_comm; rewrite Qmult_div_r; auto.
apply Qpos_non_zero; auto.
apply Qle_lt_trans with (-a /eval_pol l x * eval_pol l y).
repeat rewrite (Qmult_comm (-a/eval_pol l x)).
apply Qmult_le_compat_r; auto.
apply Qlt_le_weak; apply Qdiv_lt_0_compat; auto.
apply Qmult_lt_compat_r; auto.
apply Qlt_le_trans with (1:= H4).
apply H2; auto; apply Qle_refl.
intros epsilon Hepsilon.
assert (negval' : eval_pol (0::a::l) x < 0).
assert (H6 : eval_pol (a::l) x == x * (eval_pol (a::l) x / x)).
rewrite Qmult_div_r; apply Qeq_refl || apply Qpos_non_zero; auto.
assert (H7: eval_pol (0::a::l) x == (x*eval_pol (a::l) x))
  by (simpl; rewrite Qplus_0_l; apply Qeq_refl).
rewrite H7.
assert (H0' : 0 == 0 * x) by ring; rewrite H0'.
rewrite Qmult_comm; apply Qmult_lt_compat_r; auto.
assert (posval' : 0 < eval_pol (0::a::l) y).
assert (H0' : 0 == 0 * y) by ring; set (u:=eval_pol (0 :: a::l) y);
 rewrite H0'; unfold u.
assert (H7: eval_pol (0::a::l) y == (y*eval_pol (a::l) y))
  by (simpl; rewrite Qplus_0_l; apply Qeq_refl).
rewrite H7; rewrite (Qmult_comm y); apply Qmult_lt_compat_r; auto.
apply Qlt_trans with x; auto.
destruct (constructive_mvt (0::a::l) x y yx negval' posval' epsilon Hepsilon) as
  [dummy [v [_ [ _ [posv [smallv [xd [dv vy]]]]]]]].
assert (xv : x < v) by (apply Qlt_trans with dummy; auto); clear xd dv dummy.
simpl in smallv; rewrite Qplus_0_l in smallv.
exists v; repeat apply conj; auto.
intros y' pos y'v.
case (Qlt_le_dec y' x).
intros y'x.
apply Qle_trans with (eval_pol (a::l) x).
simpl; apply Qplus_le_compat; try apply Qle_refl.
apply H1'; auto.
simpl; apply Qplus_le_compat; try apply Qle_refl.
apply H2'; try apply Qle_refl.
auto.
intros xy'.
case (Qle_lt_or_eq _ _ y'v); intros H'.
simpl; apply Qplus_le_compat; try apply Qle_refl.
apply H2'; auto.
rewrite H'; apply Qle_refl.
intros y' z vy' y'z; simpl; apply Qplus_le_compat; try apply Qle_refl.
apply H2'; auto.
apply Qlt_le_weak; apply Qlt_le_trans with v; auto.
apply Qlt_trans with x; auto.
assert (0 < v) by (apply Qlt_trans with x; auto).
setoid_replace (eval_pol (a::l) v) with ((eval_pol (0::a::l) v)/v).
apply Qmult_lt_0_compat; auto.
simpl; field.
apply Qpos_non_zero; auto.
Qed.

Lemma l4 : forall l, alternate_1 l = true -> inv2 l.
induction l; simpl.
intros; discriminate.
case (Qlt_le_dec 0 a).
intros Ha Halp epsilon Heps; destruct (l3 _ Halp (epsilon/(2#1))) 
  as [x [H1 [H2 [H3 H4]]]].
apply Qdiv_lt_0_compat; auto; 
 assert (0 < 2#1) by (unfold Qlt; simpl; omega); auto.
assert (eps2apos : 0 < epsilon/((2#1)*a)).
apply Qdiv_lt_0_compat; auto.
assert (Heq : 0 == 0 * a) by ring; rewrite Heq; apply Qmult_lt_compat_r; auto.
assert (0 < 2#1) by (unfold Qlt; simpl; omega); auto.
assert (H1pos : 0 < 1) by (unfold Qlt; simpl; omega); auto.
assert (Hexb:= min3 _ _ _ eps2apos H3 H1pos).
destruct Hexb as [b [Hb1 [Hb2 [Hb3 Hb4]]]].
exists b; split.
intros y Hy Hb; case (Qle_lt_or_eq _ _ Hb); clear Hb; intros Hb.
apply l2; auto.
simpl; case (Qlt_le_dec a 0); auto.
intros abs; case (Qlt_not_le _ _ Ha); apply Qlt_le_weak; auto.
rewrite Hb; apply Qle_refl.
split.
intros y z Hy Hz; apply l2; auto.
simpl; case (Qlt_le_dec a 0); auto.
intros abs; case (Qlt_not_le _ _ Ha); apply Qlt_le_weak; auto.
apply Qlt_le_trans with b; auto.
split; auto.
split.
simpl; apply Qlt_le_trans with (a + 0).
rewrite Qplus_0_r; auto.
apply Qplus_le_compat.
apply Qle_refl.
apply Qmult_le_0_compat.
apply Qlt_le_weak; auto.
apply l1; auto.
simpl; rewrite Qmult_plus_distr_r.
assert (Heq: epsilon == epsilon/(2#1) + epsilon /(2#1)).
unfold Qeq; simpl.
replace ('(Qden epsilon * 2 * (Qden epsilon * 2)))%Z with
    ('Qden epsilon * 2 * ('Qden epsilon * 2))%Z by solve [auto].
replace ('(Qden epsilon * 2))%Z with ('Qden epsilon * 2)%Z by solve[auto].
ring.
rewrite Heq; apply Qplus_le_lt_compat.
clear Heq; assert (Heq : epsilon / (2#1) == epsilon / ((2#1)*a) * a).
unfold Qdiv; rewrite Qinv_mult_distr.
repeat rewrite <- Qmult_assoc.
assert (Heq: /a * a == 1).
rewrite Qmult_comm; apply Qmult_inv_r.
assert (H' : ~ 0 == a) by (apply Qlt_not_eq; auto); intro H''; case H';
rewrite H'';apply Qeq_refl.
rewrite Heq; ring.
rewrite Heq; apply Qmult_le_compat_r; auto.
apply Qle_lt_trans with (2:= H4).
apply Qle_trans with (1*(b*eval_pol l b)).
apply Qmult_le_compat_r; auto.
apply Qmult_le_0_compat.
apply Qlt_le_weak; auto.
apply l1; auto.
rewrite Qmult_1_l.
case (Qle_lt_or_eq _ _ Hb2).
intros Hbx; apply Qle_trans with (b*eval_pol l x).
repeat rewrite (Qmult_comm b); apply Qmult_le_compat_r.
apply l2; auto.
apply Qlt_le_weak; auto.
apply Qmult_le_compat_r; auto.
apply l1; auto.
intros Hbx; rewrite Hbx; apply Qle_refl.
intros Ha Halt.
case (Qle_lt_or_eq _ _ Ha); clear Ha; intros Ha.
apply l5; auto.
apply IHl in Halt; clear IHl; rename Halt into IHl.
intros epsilon Hepsilon.
destruct (IHl epsilon Hepsilon) as [v [H1v [H2v [vpos [pol_pos Hpv]]]]].
assert (eps'pos : 0 < epsilon/v) by (apply Qdiv_lt_0_compat; auto).
destruct (IHl _ eps'pos) as [x [H1 [H2 [H3 [H4 H5]]]]].
case (Qlt_le_dec x v); intros xv.
exists x.
split.
intros y posy yx; simpl; rewrite Ha; repeat rewrite Qplus_0_l.
apply Qle_trans with (y * eval_pol l x).
repeat rewrite (Qmult_comm y);apply Qmult_le_compat_r;auto.
apply Qmult_le_compat_r; auto.
split.
intros y z xy yz; simpl; rewrite Ha; repeat rewrite Qplus_0_l.
apply Qle_trans with (y * eval_pol l z).
repeat rewrite (Qmult_comm y);apply Qmult_le_compat_r;auto.
apply Qle_trans with x; auto; apply Qlt_le_weak; auto.
apply Qmult_le_compat_r.
apply Qlt_le_weak; auto.
apply Qlt_le_weak; apply Qlt_le_trans with (eval_pol l x); auto.
apply H2; auto.
apply Qle_lt_trans with y; auto.
split; auto.
split.
simpl; rewrite Ha; rewrite Qplus_0_l;apply Qmult_lt_0_compat; auto.
apply Qlt_le_trans with (v* (epsilon/v)).
simpl; rewrite Ha; rewrite Qplus_0_l.
apply Qlt_trans with (x*(epsilon/v)).
repeat rewrite (Qmult_comm x); apply Qmult_lt_compat_r; auto.
rewrite Qmult_comm; auto.
apply Qmult_lt_compat_r; auto.
rewrite Qmult_div_r; auto.
apply Qpos_non_zero; apply Qlt_trans with x; auto.
exists v; split.
intros y posy yv; simpl; rewrite Ha; repeat rewrite Qplus_0_l.
apply Qle_trans with (y * eval_pol l v).
repeat rewrite (Qmult_comm y); apply Qmult_le_compat_r; auto.
apply Qmult_le_compat_r; auto; apply Qlt_le_weak; auto.
split.

intros y z vy yz; simpl; rewrite Ha; repeat rewrite Qplus_0_l.
apply Qle_trans with (y * eval_pol l z).
repeat rewrite (Qmult_comm y); apply Qmult_le_compat_r; auto.
apply Qlt_le_weak; auto.
apply Qlt_le_trans with (1:=vpos); auto.
apply Qmult_le_compat_r; apply Qlt_le_weak; auto.
apply Qlt_le_trans with (eval_pol l v); auto.
apply H2v.
apply Qle_refl.
apply Qle_lt_trans with y; auto.
split.
auto.
split.
simpl; rewrite Ha; rewrite Qplus_0_l.
apply Qmult_lt_0_compat; auto.
assert (Hepsv : epsilon == v * (epsilon/v))
  by (rewrite Qmult_div_r; apply Qeq_refl || apply Qpos_non_zero; auto).
rewrite Hepsv; repeat rewrite (Qmult_comm v); simpl; 
  rewrite Ha; rewrite Qplus_0_l.
apply Qmult_lt_compat_r; auto. 
apply Qle_lt_trans with (2:= H5).
apply Qle_trans with (v*eval_pol l x).
repeat rewrite (Qmult_comm v); apply Qmult_le_compat_r; auto.
apply Qmult_le_compat_r; auto.
Qed.

Lemma Qlt_minus : forall x y, x < y -> 0 < y - x.
intros x y xy; assert (d : 0 == x - x) by ring; rewrite d; unfold Qminus;
repeat rewrite <-(Qplus_comm (-x)); apply Qplus_le_lt_compat; auto;
 apply Qle_refl.
Qed.

Lemma desc : forall l, alternate l = true ->
  exists x1, exists x2, exists k, 0 < x1 /\ x1 < x2 /\ 0 < k /\
   (forall x, 0 < x -> x <= x1 -> eval_pol l x < 0) /\
   (forall x y, x1 <= x -> x < y -> k * (y - x) <= eval_pol l y - eval_pol l x ) /\
   0 < eval_pol l x2.
induction l; simpl.
intros; discriminate.
destruct (Qlt_le_dec a 0) as [aneg | apos0]; intros Halt1.
destruct (l4 _ Halt1 _ (neg_opp_pos _ aneg))
  as [x1 [H1x1 [H2x1 [H3x1 [H4x1 H5x1]]]]].
exists x1.
assert (Hex2 :exists x2, x1 <= x2 /\ (-a/eval_pol l x1 + 1 <= x2)).
destruct (Qlt_le_dec (-a/eval_pol l x1 +1) x1) as [vx1 | x1v].
exists x1; split; exact (Qlt_le_weak _ _ vx1) || apply Qle_refl.
exists (-a/eval_pol l x1 + 1); split; assumption || apply Qle_refl.
destruct Hex2 as [x2 [x1x2 vx2]].
cut (x1<x2).
exists x2.
exists (eval_pol l x1).
split; auto.
split; auto.
split; auto.
split.
intros x posx xx1; assert (H0 : 0 == a + -a) by ring; rewrite H0; clear H0.
apply Qplus_le_lt_compat; try apply Qle_refl.
apply Qle_lt_trans with (x1*eval_pol l x1); auto.
apply Qle_trans with (x*eval_pol l x1).
repeat rewrite (Qmult_comm x); apply Qmult_le_compat_r; auto; 
 apply Qlt_le_weak; auto.
apply Qmult_le_compat_r; auto; apply Qlt_le_weak; auto.
split.
intros x y x1x xy.
assert (H0 : a+y*eval_pol l y-(a+x*eval_pol l x) ==
  (y*eval_pol l y - x*eval_pol l x)) by ring; rewrite H0; clear H0.
apply Qle_trans with (y*eval_pol l x - x*eval_pol l x).
assert (H0 : y*eval_pol l x - x*eval_pol l x ==
             (y-x)*eval_pol l x) by ring; rewrite H0; clear H0.
rewrite (Qmult_comm (y-x)); apply Qmult_le_compat_r.
destruct (Qle_lt_or_eq _ _ x1x) as [x1x' | x1x'].
 apply H2x1; auto; apply Qle_refl.
rewrite x1x'; apply Qle_refl.
apply Qlt_le_weak; apply Qlt_minus; auto.
unfold Qminus; apply Qplus_le_compat; try apply Qle_refl.
repeat rewrite (Qmult_comm y);apply Qmult_le_compat_r;
  try apply H2x1; eauto using Qlt_le_weak, Qlt_trans, Qlt_le_trans.
assert (H0 : 0 == a + -a) by ring; rewrite H0; clear H0.
apply Qplus_le_lt_compat; try apply Qle_refl.
assert (p1p2 :  eval_pol l x1 <= eval_pol l x2).
apply H2x1; auto; apply Qle_refl.
apply Qlt_le_trans with ((-a/eval_pol l x1 + 1)*eval_pol l x2).
set (u:= -a/eval_pol l x1 + 1).
assert (H0 : -a == -a + 0) by ring; rewrite H0; unfold u.
rewrite Qmult_plus_distr_l; rewrite Qmult_1_l.
apply Qplus_le_lt_compat;[idtac |
  apply Qlt_le_trans with (1:=H4x1); auto].
apply Qle_trans with (-a/eval_pol l x1 * eval_pol l x1).
rewrite Qmult_comm; rewrite Qmult_div_r; try apply Qle_refl; 
 apply Qpos_non_zero; auto.
repeat rewrite (Qmult_comm (-a/eval_pol l x1)); apply Qmult_le_compat_r; auto;
 apply Qlt_le_weak; apply Qdiv_lt_0_compat; auto; apply neg_opp_pos; auto.
apply Qmult_le_compat_r; auto; 
 apply Qlt_le_weak; apply Qlt_le_trans with (eval_pol l x1); auto.
assert (vx2' : -a / eval_pol l x1 < x2).
apply Qlt_le_trans with (2:=vx2); apply add_1_lt.
assert (H0 : x1 == x1 *eval_pol l x1 /eval_pol l x1)
 by (rewrite Qdiv_mult_l; apply Qeq_refl || apply Qpos_non_zero; auto);
 rewrite H0; clear H0.
apply Qlt_trans with (2:=vx2').
unfold Qdiv; apply Qmult_lt_compat_r; auto; apply inv_pos; auto.
destruct (Qeq_dec a 0) as [Ha | an0];[idtac | discriminate].
destruct (IHl Halt1) as [v1 [v2 [k [v1pos [v1v2 [kpos [low [incr pos]]]]]]]].
assert (negval : eval_pol l v1 < 0) by (apply low; auto; apply Qle_refl).
assert (v2pos : 0 < v2) by (apply Qlt_trans with v1; eauto).
assert (epsv2 : 0 < k * v1 / (2#1)) by
  (apply Qdiv_lt_0_compat; try (apply Qmult_lt_0_compat; auto);
  unfold Qlt; simpl; omega).
destruct (constructive_mvt l v1 v2 v1v2 negval pos _ epsv2) as
  [x1 [x2 [x1close [px1neg [px2pos [px2close [v1x1 [x1x2 x2v2]]]]]]]].
set (k' := k*v1/(2#1)).
exists x1; exists x2; exists k'; split.
apply Qlt_trans with v1; auto.
split; auto.
split; auto.
split.
intros x xpos xx1; rewrite Ha; rewrite Qplus_0_l;
assert (H0 : 0 == x*0) by ring; rewrite H0; clear H0;
repeat rewrite (Qmult_comm x); apply Qmult_lt_compat_r; auto;
destruct (Qlt_le_dec x v1) as [xv1 | v1x].
apply low; auto; apply Qlt_le_weak; auto.
case (Qle_lt_or_eq _ _ xx1); clear xx1; intros xx1.
apply Qlt_trans with (eval_pol l x1); auto.
assert (H0:eval_pol l x == eval_pol l x + 0) by ring; rewrite H0; clear H0;
assert (H0:eval_pol l x1 == eval_pol l x + (eval_pol l x1 -eval_pol l x))
 by ring; rewrite H0; clear H0; apply Qplus_le_lt_compat; try apply Qle_refl.
apply Qlt_le_trans with (k*(x1-x)); try apply Qmult_lt_0_compat;
auto; apply Qlt_minus;auto.
rewrite xx1; solve [auto].
split.
intros x y x1x xy.
assert (H0 : a + y * eval_pol l y - (a+x*eval_pol l x) ==
         y*eval_pol l y-x*eval_pol l x) by ring; rewrite H0; clear H0.
assert (H0 : y*eval_pol l y-x*eval_pol l x ==
            (y - x)* eval_pol l y + x * (eval_pol l y - eval_pol l x))
  by ring; rewrite H0; clear H0.
assert (Hk : (y-x) * eval_pol l y + x * k * (y - x) <=
        (y-x) * eval_pol l y + x * (eval_pol l y - eval_pol l x)).
apply Qplus_le_compat; try apply Qle_refl; rewrite <- Qmult_assoc;
repeat rewrite (Qmult_comm x); apply Qmult_le_compat_r;
eauto using Qlt_le_weak, Qlt_le_trans, Qlt_trans.
apply Qle_trans with (2:= Hk); rewrite (Qmult_comm (y-x)).
apply Qle_trans with (eval_pol l x1 * (y-x) + x*k*(y-x)).
apply Qle_trans with (eval_pol l x1 * (y-x) + v1*k*(y-x)).
unfold k'; rewrite <- Qmult_plus_distr_l.
apply Qmult_le_compat_r.
apply Qle_trans with (-(k*v1/(2#1)) + v1*k).
assert (Hv1k2: v1*k == k*v1/(2#1) + k*v1/(2#1)).
unfold Qeq; simpl. expand_Zpos_mult; ring.
rewrite Hv1k2; rewrite Qplus_comm; rewrite <- Qplus_assoc.
assert (H0 : k*v1/(2#1) == k*v1/(2#1) + 0) by ring; rewrite H0;
apply Qplus_le_compat; rewrite <- H0; clear H0; try apply Qle_refl.
assert (H0: k*v1/(2#1)+-(k*v1/(2#1)) == 0) by ring; rewrite H0; apply Qle_refl.
apply Qplus_le_compat; try apply Qle_refl.
apply Qlt_le_weak; auto.
apply Qlt_le_weak; apply Qlt_minus; auto.
apply Qplus_le_compat; try apply Qle_refl.
repeat apply Qmult_le_compat_r.
apply Qle_trans with x1; auto; apply Qlt_le_weak; auto.
apply Qlt_le_weak; auto.
apply Qlt_le_weak; apply Qlt_minus; auto.
apply Qplus_le_compat; try apply Qle_refl.
apply Qmult_le_compat_r; try apply Qle_refl.
assert (H0 : eval_pol l x1 == 0 + eval_pol l x1) by ring; rewrite H0; clear H0.
assert (H0 : eval_pol l y == (eval_pol l y - eval_pol l x1)+eval_pol l x1)
  by ring; rewrite H0; clear H0.
apply Qplus_le_compat; try apply Qle_refl.
apply Qle_trans with (k*(y-x1)).
assert (H0 : 0 == 0 * (y-x1)) by ring; rewrite H0; clear H0.
apply Qmult_le_compat_r; try (apply Qlt_minus; auto).
apply Qlt_le_weak; auto.
apply Qlt_le_weak; apply Qlt_minus.
apply Qle_lt_trans with x; auto.
apply incr; auto.
apply Qle_lt_trans with x; auto.
apply Qlt_le_weak; apply Qlt_minus; auto.
rewrite Ha; rewrite Qplus_0_l.
apply Qmult_lt_0_compat.
eauto using Qlt_trans.
auto.
Qed.

