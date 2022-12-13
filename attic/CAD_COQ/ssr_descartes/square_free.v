Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype prime.
Require Import div ssralg poly polydiv polyorder ssrnum zmodp polyrcf.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory. (*Num.Theory Num.Def.*)
Import Pdiv.Idomain.

Open Scope ring_scope.

Section more_deriv.

Lemma derivXsubCexpSn : forall (R : idomainType) (c : R) (n : nat),
   (('X-c%:P) ^+(n.+1))^`() = (n.+1)%:R *: ('X-c%:P) ^+ n.
Proof.
move=> R c; elim=> [|m Hm]; first by rewrite scaler_nat expr0 expr1 derivXsubC.
rewrite exprSr derivM derivXsubC Hm -scalerAl -exprSr mulr1 scaler_nat -mulrSr.
by rewrite -scaler_nat.
Qed.

Lemma derivXsubCexpn : forall (R : idomainType) (c : R) (n : nat),
   (0 < n)%N -> (('X-c%:P) ^+n)^`() = n%:R *: ('X-c%:P) ^+ (n.-1).
Proof. by move=> R c; elim=> [|m Hm H] //=; rewrite derivXsubCexpSn. Qed.

End more_deriv.

Section poly_simple_roots.

Variable R : idomainType.
Hypothesis HR : [char R] =i pred0.

Lemma mu_x_gcdp : forall (p : {poly R}) (x : R), (p != 0) -> (root p x) ->
   \mu_x (gcdp p p^`()) == (\mu_x p) .-1.
Proof.
move=> p x Hp zero_x.
(*about p*)
have [q Hq Hpp] := (@mu_spec R p x Hp).
(*mu x > 0*)
have Hmu : ((\mu_x p)%R > 0)%N by rewrite mu_gt0.
(*about p'*)
have Hpderiv : (deriv p) =
   ('X - x%:P) ^+ (\mu_x p).-1 * ((\mu_x p)%:R *: q + ('X-x%:P) * (deriv q)).
  by rewrite mulrDr mulrA -exprSr prednK // -scalerCA -derivXsubCexpn //
     -derivM mulrC {1}Hpp.
(**********)
rewrite eq_sym -muP.
  apply/andP; split.
(*(X-x)^m-1 divides pgcd*)
    rewrite dvdp_gcd.
    apply/andP; split.
(*(X-x)^m-1 divides p*)
      by rewrite {2}Hpp -(@prednK (\mu_x p)) // exprS mulrA; apply dvdp_mulIr.
(*(X-x)^m-1 divides p'*)
    by rewrite Hpderiv; apply dvdp_mulIl.
(*(X-x)^m doesn't divide pgcd*)
  rewrite prednK // dvdp_gcd negb_and.
  apply/orP; right.
(*(X-x)^m doesn't divide p'*)
  rewrite Hpderiv -{1}(@prednK (\mu_x p)) // exprSr dvdp_mul2l.
(*(X-x) doesn't divide the remaining factor of p'*)
    rewrite dvdp_addl; last by apply dvdp_mulr.
    rewrite (@eqp_dvdr _  q ((\mu_x p)%:R *: q) ('X -x%:P)).
      by rewrite dvdp_XsubCl.
    apply eqp_scale.
    have/charf0P ->:= HR.
    by rewrite -lt0n //.
  by rewrite -size_poly_gt0 size_exp_XsubC prednK //.
by rewrite gcdp_eq0 negb_and Hp.
Qed.

Lemma mu_gcdp_eq1 : forall (p : {poly R}) (x : R), (p != 0) -> root p x ->
   (\mu_x (divp p (gcdp p p^`())) == 1)%N.
Proof.
move=> p x Hp zero_x.
rewrite -(@eqn_add2r ((\mu_x)%R p)) (@addnC 1%N _) addn1 
  -{1}(@prednK ((\mu_x)%R p)) ?mu_gt0 //.
rewrite addnS -(eqP (mu_x_gcdp Hp zero_x)) -mu_mul.
  rewrite divpK ?mu_mulC //; last by apply dvdp_gcdl.
  by apply lc_expn_scalp_neq0.
rewrite divpK.
  rewrite -size_poly_gt0 -mul_polyC size_Cmul ?size_poly_gt0 //.
  by apply lc_expn_scalp_neq0.
by apply dvdp_gcdl.
Qed.

Lemma same_roots_1 : forall (p : {poly R}) (x : R), root p x ->
   root (divp p (gcdp p p^`())) x.
Proof.
move=> p x zero_x.
case h: (p==0).
  by move/eqP: h => H; move : zero_x; rewrite H deriv0 gcd0p div0p.
move/negbT: h => H; rewrite -mu_gt0.
  by move/eqP : (mu_gcdp_eq1 H zero_x) => ->.
rewrite divpN0; first by apply: leq_gcdpl.
by move/negPf : H => H; rewrite gcdp_eq0 H.
Qed.

Lemma same_roots_2 : forall (p : {poly R}) (x : R),
   root (divp p (gcdp p p^`())) x -> root p x.
Proof.
move=> p x zero_x.
rewrite -(@rootZ R x (lead_coef (gcdp p p^`()) ^+ scalp (R:=R) p
   (gcdp p p^`())) p).
  rewrite -divpK.
    by rewrite rootM zero_x.
  by apply dvdp_gcdl.
by apply lc_expn_scalp_neq0.
Qed.

Lemma gcdp_simple_roots : forall (p : {poly R}) (x : R), (p != 0) ->
   root (divp p (gcdp p p^`())) x ->
   (\mu_x (divp p (gcdp p p^`())) == 1)%N.
Proof.
by move=> p x Hp zero_x; apply (mu_gcdp_eq1 Hp); apply same_roots_2.
Qed.
(*p!=0 beause of mu_polyC.*)

End poly_simple_roots.
