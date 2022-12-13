Require Import QArith ZArith Zwf Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigop fingroup choice binomial.
Require Export ssralg infra pol cmvt desc.

Import GroupScope .
Import GRing.Theory .
Import OrderedRing.Theory.
Open Local Scope ring_scope .

Set Printing Width 50.

(* Two predicates to describe that a polynomial has only one root,
  one_root1 l a b :
     there exists c, d, and k, so that a,c,d,b is ordered, k is positive,
     the polynomial value is positive between a and c, negative between d and b
     the slope is less than -k between c and d.
  This statement is specifically suited to speak about roots inside the
  interval a b.

  one_root2 l a :
     there exists c, d, and k, so that a is smaller than c, k is positive,
     the polynomical value is negative between a and c, and the slope is
     larger than k above c.

  A consequence of one_root2 is that there can be only one root above c, hence
  only one root above a.
    
*)
Definition one_root1 (l : seq Qcb) (a b : Qcb) :=
  exists c, exists d, exists k, 
     a < c /\ c < d /\ d < b /\ 0 < k /\
     (forall x, a < x -> x <= c -> 0 < eval_pol l x) /\
     (forall x, d < x -> x < b -> eval_pol l x < 0) /\
     (forall x y, c < x -> x <= y -> y < d ->
        k * (y - x) <= eval_pol l x - eval_pol l y ).

Definition one_root2 (l : seq Qcb) (a : Qcb) :=
   exists c, exists k,
     a < c /\ 0 < k /\
     (forall x, a < x -> x <= c -> eval_pol l x < 0) /\
     (forall x y, c <= x -> x < y -> 
         k * (y - x) <= eval_pol l y - eval_pol l x).

Lemma alt_one_root2 : forall l, alternate l -> one_root2 l 0.
move => l a.
move: (desc l a) => [x1 [k [x1p [kp [neg sl]]]]].
move: (above_slope _ _ 0 _ kp sl) => [x2 [pos x1x2]].
by exists x1; exists k; split; first done; split; first done; split; done.
Qed.

Lemma one_root2_translate :
  forall l a b, one_root2 (translate_pol' l a) b -> one_root2 l (a + b).
Proof.
move=> l a b [x1 [k [x1a [kp [neg sl]]]]].
exists (a + x1); exists k.
split; first by rewrite  lter_add2r.
split; first by [].
split.
  move=> x abx xax1; rewrite (_ : x = x - a + a); last first.
    by rewrite addrNK.
  rewrite  -translate_pol'q; apply: neg.
    by rewrite lter_subr addrC.
  by rewrite lter_subl.
move=> x y ax1x xy.
have t: forall z, z = (z - a) + a by move=> z; rewrite addrNK.
rewrite {2}(t y) {2}(t x) -!(translate_pol'q l) (_ : y - x = y - a - (x - a)).
  apply: sl; first by rewrite lter_sublA.
  by  rewrite lter_add2l.
by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
Qed.

Lemma one_root1_translate :
  forall l a b c, one_root1 (translate_pol' l c) a b ->
    one_root1 l (c + a) (c + b).
Proof.
move=> l a b c [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c + x1); exists (c + x2); exists k.
split; first by rewrite lter_add2r.
split; first by rewrite lter_add2r.
split; first by rewrite lter_add2r.
split; first by [].
split.
  move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
   by rewrite -translate_pol'q; apply pos; rewrite lter_subl.
split.
  move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
    by rewrite -translate_pol'q; apply: neg; rewrite -?ler_addlA // lter_subl.
move=> x y cx1x xy ycx2.
have t: forall z, z = (z - c) + c by move=> z; rewrite addrNK.
rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
  by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
by rewrite -!(translate_pol'q l); apply: sl; rewrite ?ler_add2l // lter_subl.
Qed.

Lemma one_root1_expand :
  forall l a b c, 0 < c -> one_root1 (expand l c) a b ->
    one_root1 l (c * a) (c * b).
Proof.
move=> l a b c cp [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c * x1); exists (c * x2); exists (k / c).
have tc : 0 < c^-1 by rewrite invf_gte0.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in cp.*)
split; first by rewrite lter_mulpl.
split; first by rewrite lter_mulpl.
split; first by rewrite lter_mulpl.
split; first by rewrite mulr_gte0pp.
split.
  move=> x acx xx1c.
    rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulfVK // eq_sym ltrWN.
   rewrite -eval_expand; apply: pos.
     by rewrite ltef_divpr // mulrC.
   by rewrite ltef_divpl //= mulrC.
split.
  move=> x cx2x xcb; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulfVK // eq_sym ltrWN.
  rewrite -eval_expand; apply: neg; first by rewrite ltef_divpr 1?mulrC.
  by rewrite ltef_divpl 1?mulrC.
have t: forall z, z = c * (z/c).
   by move=> z; rewrite [c * _]mulrC mulfVK // eq_sym ltrWN.
move=> x y cx1x xy ycx2; rewrite -mulrA mulr_addr mulrN ![c^-1 * _]mulrC
  {2}(t x) {2}(t y) -!(eval_expand l); apply: sl.
   by rewrite ltef_divpr // mulrC.
 by rewrite ltef_mulpr.
by rewrite ltef_divpl // mulrC.
Qed.

Lemma diff_xn_ub :
  forall n z, 0 < z -> exists k, 0 <= k /\
   forall x y:Qcb, 0 < x -> x <= y -> y <= z ->
      y ^+ n - x ^+ n <= k * (y - x).
Proof.
move => n; elim: n => {n} [z z0| n IHn z z0].
  by exists 0.
case: (IHn z z0) => k [k0 kp].
exists (z*k + z ^+ n); split => [ | x y x0 xy yz].
  apply: lter_addpl => /=; first by apply:expf_ge0; rewrite ltrW.
  by apply: mulr_gte0pp=> //=; apply: ltrW.
rewrite !exprS.
rewrite (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulr_addl mulr_addr addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulr_addl lter_add //=.
  rewrite -mulrA; apply: ler_trans (_ : y * (k * (y - x)) <= _).
  rewrite lter_mulpl //=; first by apply: lter_le_trans xy; apply: ltrW.
    by apply: kp.
  apply: lter_mulpr => //; by apply: mulr_ge0pp => //; rewrite subr_gte0.
rewrite (mulrC (_ - _)); apply: lter_mulpr; first by rewrite subr_gte0.
case: {IHn kp} n=> /=; first by rewrite !expr0 lterr.
by move => n; rewrite lef_expS2 ?(ltrW z0) ?(ltrW x0) //=; apply: ler_trans yz.
Qed.

Lemma reciprocate_size :  forall l, size (reciprocate_pol l) = size l.
by move => l; rewrite /reciprocate_pol size_rev.
Qed.

Lemma one_root_reciprocate :
  forall l, one_root2 (reciprocate_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l [x1 [k [x1gt1 [kp [neg sl]]]]].
have x10 : 0 < x1 by apply: lter_trans x1gt1.
have ux1 : GRing.unit x1 by apply/negP; move/eqP => q; rewrite q lterr in x10.
have uk: GRing.unit k by apply/negP; move/eqP => q; rewrite q lterr in kp.
set y' := x1 - eval_pol (reciprocate_pol l) x1 / k.
have y'1: x1 < y'.
  rewrite /y' -(lter_add2r (-x1)) addNr addrA addNr add0r -mulNr.
  apply: mulr_gte0pp=> /=; last by  rewrite invf_gte0.
  by rewrite oppr_cp0 /=; apply: neg=> //; rewrite lterr.
have nx1 : eval_pol (reciprocate_pol l) x1 < 0 by apply: neg; rewrite // lterr.
have y'pos : 0 <= eval_pol (reciprocate_pol l) y'.
  rewrite -[_ _ y']addr0 -{2}(addNr (eval_pol (reciprocate_pol l) x1)) addrA
   -{2}(opprK (_ _ x1)) subr_gte0 /=.
  apply: lter_trans (_ : k * (y' - x1) <= _)=> /=.
     by rewrite /y' (addrC x1) addrK mulrN mulrC mulrVK // lterr.
  by apply sl => //; rewrite lterr.
have ltr1: 0 < (1:Qcb) by [].
move: (diff_xn_ub (size l - 1) _ ltr1) => {ltr1} [u [u0 up]].
have [u' [u1 u'u]] : exists u', 1 <= u' /\ u <= u'.
  case cmp: (1 <= u); first by exists u; rewrite lerr cmp.
  by exists 1; rewrite lerr; split=> //; rewrite ltrW // -lerNgt cmp.
have u'0 : 0 < u' by apply: lter_le_trans u1.
have u'unit : GRing.unit u' by apply/negP; move/eqP=> q; rewrite q lterr in u'0.
have divu_ltr : forall x, 0 <= x -> x / u' <= x.
  move => x x0; rewrite ltef_divpl // mulrC /=.
  by rewrite -{1}(mul1r x) lter_mulp.

(*   rewrite ler_eqVlt in x0; case/orP: x0 => [x0 | x0]. *)
(*      rewrite /=.  -lter_mulpl. *)







(* -(eqP x0) mulr0 lterr. *)
(*   rewrite -ltef_divpl // mulrV //. *)

(*   by apply/negP; move/eqP=> q; rewrite q lterr in x0. *)
have y'0: 0 < y' by apply: lter_trans y'1.
pose y := y' + 1.
have y'y : y' < y by rewrite /y -{1}(addr0 y') lter_add2r.
have y1 : x1 < y by apply: lter_trans y'1 _.
have ypos : 0 < eval_pol (reciprocate_pol l) y.
  apply: ler_lte_trans y'pos _=> /=.
  rewrite -subr_gte0 /=; apply: lter_le_trans (_ : k * (y - y') <= _)=> /=.
    by rewrite mulr_cp0p //= subr_gte0.
  by apply: sl=> //; apply: ltrW.
have y0: 0 < y by apply: lter_trans y'y.
pose k' :=  ((k * x1 ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
have k'p : 0 < k'.
  rewrite /k'; apply: mulr_gte0pp; last by[].
  apply: mulr_gte0pp=> /=.
    by apply: mulr_gte0pp => //; apply: expf_gt0.
  by apply: expf_gt0; rewrite (invf_gte0 y).
pose e := k'/u'.
have ep: 0 < e by rewrite /e; apply: mulr_gte0pp => //; rewrite invf_gte0.
move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [e1e2 [e1e e2e]]]]]].
move: (constructive_ivt (reciprocate_pol l) _ _ y'1 nx1 y'pos _ e1p) =>
  [a [b' [cla [nega [posb' [clb' [x1a [ab b'y']]]]]]]].
move: (cm3 y y0 (reciprocate_pol l)) => [c cp].
have a0 : 0 < a by apply: lter_le_trans x1a.
have c0 : 0 < c.
  rewrite -(@ltef_mulpr _ (b' -a)) ?mul0r /=; last by rewrite subr_gte0.
  apply: lter_le_trans
   (_ : `|eval_pol (reciprocate_pol l) b' - eval_pol (reciprocate_pol l) a| 
          <= _)=> /=; last first.
  by apply: cp; last apply: ltrW(ler_lte_trans b'y' y'y); apply: ltrW.
  have d: 0 < eval_pol (reciprocate_pol l) b' - eval_pol (reciprocate_pol l) a.
    by rewrite subr_gte0 /=; apply: lter_le_trans posb'.
  by rewrite  absr_gt0 eq_sym ltrWN.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in c0.*)
have [b [b'b [clb blty]]] : exists b, b' < b /\ c * (b - b') < e2 /\ b <= y.
  move: (cut_epsilon _ e2p) => [e3 [e4 [e3p [_ [_ [e3e2 _]]]]]].
  case cmp: (b' + e2/c <= y).
    exists (b' + e3/c).
    split.
      by rewrite lter_addrr //= mulf_gte0 /= e3p invf_gte0 /= c0.
    split.
       by rewrite (addrC b') addrK mulrA (mulrC c) mulfK // eq_sym ltrWN.
    apply: ltrW (lter_le_trans _ cmp); rewrite lter_add2r /=. 
    by apply: lter_mulpr=> //=; rewrite invf_gte0.
  exists y.
  split; first by apply: ler_lte_trans b'y' y'y.
  split; last by rewrite lterr.
    by rewrite mulrC -ltef_divp //= -lter_addrA /= -lerNgt addrC cmp.
pose n := Qcb_make (Z_of_nat (size l)) - 1.
have b'0 : 0 < b' by apply: lter_trans ab.
have b0 : 0 < b by apply: lter_trans b'b.
have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q lterr in a0.
have ub': GRing.unit b' by apply/negP; move/eqP=> q; rewrite q lterr in b'0.
have b'v0: 0 < b'^-1 by rewrite invf_gte0.
have bv0 : 0 < b^-1 by rewrite invf_gte0.
have bb'v: b^-1 < b'^-1.
 by apply: ltef_invpp => //.
have ub: GRing.unit b by apply/negP; move/eqP=> q; rewrite q lterr in b0.
exists b^-1; exists a^-1; exists k'.
split=> //.
split; first by apply: ltef_invpp=> //=; apply: lter_trans b'b.
split.
  by rewrite -invr1; apply: ltef_invpp => //; apply: lter_le_trans x1a.
split; first by [].
split.
  move => x x0 xb.
  have ux: GRing.unit x by apply/negP; move/eqP=>q; rewrite q lterr in x0.
  have xv0: 0 < x^-1 by rewrite invf_gte0.
  have xexp0 : 0 < x^-1 ^+ (size l - 1) by apply: expf_gt0.
  have b'x: b' < x^-1.
    by rewrite -(invrK b') //; apply: ltef_invpp => //; apply: (ler_lte_trans xb).
  rewrite -(ltef_mulpl _ _ _ xexp0) /= mulr0 -{2}[x]invrK -reciprocateq;
   last by rewrite unitr_inv.
  apply: (ler_lte_trans posb'); rewrite -subr_gte0 /=.
  apply: lter_le_trans (_ : k * (x^-1 - b') <= _)=> /=.
    by rewrite mulr_gte0pp //= ?(ltrW kp) // subr_gte0.
  by apply: sl; first apply:ltrW(ler_lte_trans x1a _).
split.
  move => x a1x xlt1.
  have x0 : 0 < x by apply: lter_trans a1x; rewrite invf_gte0.
  have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0.
  have uxv : GRing.unit x^-1 by rewrite unitr_inv.
  have xv0 : 0 < x^-1 by rewrite invf_gte0.
  have x1a0 : x^-1 < a.
    by rewrite -[a]invrK; apply: ltef_invpp => //; rewrite invf_gte0.
  have xexp0 : 0 < x^-1 ^+ (size l - 1) by apply: expf_gt0.
   rewrite -(ltef_mulpl _ _ _ xexp0) mulr0 -{2}[x]invrK -reciprocateq;

   last by rewrite unitr_inv.
  case cmp: (x^-1 <= x1); last (move/negbT:cmp => cmp).
    by apply: neg => //; rewrite -invr1; apply: ltef_invpp.
  apply: lter_trans nega; rewrite -subr_gte0.
  apply: lter_le_trans (_ : k * (a - x^-1) <= _).
    by rewrite -(mulr0 k) lter_mulpl //= subr_gte0.
  by apply: sl; first apply:ltrW.
move => x z bvx xz zav; rewrite ler_eqVlt in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 lterr.
have x0: 0 < x by apply: lter_trans bvx.
have z0 : 0 < z by apply: (lter_trans x0).
have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0.
have uz: GRing.unit z by apply/negP;move/eqP=>q; rewrite q lterr in z0.
have invo_rec : forall l, reciprocate_pol (reciprocate_pol l) = l.
  by move => l'; rewrite /reciprocate_pol revK.
rewrite -(invo_rec l) (reciprocateq _ x) // (reciprocateq _ z) //.
rewrite reciprocate_size.
rewrite (_ : _ * _ - _ = (x ^+ (size l - 1) - z ^+ (size l - 1)) *
                     eval_pol (reciprocate_pol l) x ^-1 +
                     (eval_pol (reciprocate_pol l) x ^-1 -
                      eval_pol (reciprocate_pol l) z ^-1) *
                      z ^+ (size l - 1)); last first.
  by rewrite !mulr_addl !mulNr ![eval_pol _ _ * _]mulrC !addrA addrNK.
set t1 := _ * eval_pol _ _.
set t3 := (eval_pol _ _ - _).
set t2 := t3 * _.
pose k1 := -k'; pose k2 := k' + k'.
have times2 : forall a:Qcb, a + a = (1 + 1) * a.
  by move => a'; rewrite mulr_addl !mul1r.
have k2p : k2 = (k * x1 ^+ 2 * y ^-1 ^+ (size l - 1)).
  rewrite /k2 /k' times2 -(mulrC (1 + 1)^-1) mulrA mulfV; first  by rewrite mul1r.
    have twop : 0 < ((1 + 1):Qcb) by rewrite lter_addpl.
    by rewrite eq_sym (ltrWN twop).
rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
rewrite mulr_addl; apply: lter_add; last first.
  have maj' : t3 * y^-1 ^+ (size l - 1) <= t3 * z^+ (size l - 1).
    have maj : y^-1 ^+(size l - 1) <= z ^+ (size l - 1).
      case: (size l - 1)%N => [ | n']; first by rewrite !expr0 lterr.
      rewrite lef_expS2 /=.
          apply: ltrW(lter_trans _ xz); apply: ler_lte_trans bvx.
          by apply: ltef_invpp.
        by apply: ltrW; rewrite invf_gte0.
      by apply: ltrW.
    rewrite lter_mulpl // /t3.
    apply: lter_le_trans (_ : k * (x^-1 - z^-1) <= _); last first.
      apply: sl.
        rewrite -[x1]invrK // ltef_invpp //. 
          by rewrite invf_gte0.
        apply: ltrW(lter_le_trans zav _).
        by apply: ltef_invpp => //.
      by apply: ltef_invpp.
    apply: mulr_gte0pp=> /=; first by rewrite ltrW.
    by rewrite subr_gte0; apply: ltef_invpp=> //=; apply: ltrW.
  apply: lter_trans maj'; rewrite /t3 k2p mulrAC.
  rewrite ltef_mulpr; last by apply expf_gt0; rewrite invf_gte0.
  apply: lter_trans (_ : k * (x^-1 - z^-1) <= _).
    rewrite ![k * _]mulrC mulrAC ltef_mulpr; last by [].
    rewrite -[x^-1](mulrK uz) -{2}[z^-1](mulrK ux) -(mulrC x) -(mulrC z).
    rewrite (mulrAC x) -!(mulrA _ (x^-1)) -mulr_subl (mulrC (z - x)).
    rewrite ltef_mulpr /=; last by rewrite subr_gte0.
    apply: lter_trans (_ : x1/z <= _).
      rewrite lter_mulpl //=; first by apply: ltrW.
      apply: lter_trans x1a _; rewrite -(invrK a); apply: ltef_invpp=> //=; last exact: ltrW.
      by rewrite invf_gte0.
    rewrite ltef_mulpr //. 
      rewrite -[x1]invrK //; apply: ltef_invpp => //.
        by rewrite invf_gte0.
      apply: ltrW(lter_trans xz _).
      by apply: lter_le_trans zav _; apply: ltef_invpp.
    by rewrite invf_gte0.
  apply: sl.
    apply: ltrW(ler_lte_trans x1a _).
    by rewrite -[a]invrK; apply: ltef_invpp => //; rewrite invf_gte0.
  by apply: ltef_invpp  => //.
rewrite /t1/k1/k' {t2 t3}.
have xzexp : (x ^+ (size l - 1) <= z ^+ (size l - 1)).
  case sizep : (size l - 1)%N => [ | n'].
    by rewrite !expr0 lterr.
  by rewrite lef_expS2 //= ltrW.
case: (lerP 0 (eval_pol (reciprocate_pol l) x^-1)) => sign; last first.
apply: lter_trans (_ : 0 <= _).

    rewrite mulNr lter_oppl oppr0; apply: mulr_ge0pp; last first.
      by rewrite subr_gte0 /= ltrW.
    apply: ltrW; exact k'p.
  apply: mulr_gte0nn.
    by rewrite subr_lte0.
  by apply: ltrW.
rewrite mulNr lter_oppl -mulNr oppr_sub.
have rpxe : eval_pol (reciprocate_pol l) x^-1 <= e.
  apply:lter_trans (_ : eval_pol (reciprocate_pol l) b <= _) => /=.
    rewrite -subr_gte0 /= ; apply: lter_trans (_ : k * (b - x^-1) <= _).
      apply: mulr_ge0pp; first by apply: ltrW.
      rewrite subr_gte0 -[b]invrK //; apply: ltef_invpp => //=.
      by apply: ltrW.
    apply: sl. 
    rewrite -[x1]invrK //; apply: ltef_invpp => //.
        by rewrite invf_gte0.
      by apply: ltrW(lter_le_trans (lter_trans xz zav) _); apply: ltef_invpp.
    by rewrite -[b]invrK //; apply: ltef_invpp.
  rewrite -[_ _ b]addr0 -(addrN (eval_pol (reciprocate_pol l) b')) addrA.
  rewrite (addrC (eval_pol _ b)) -addrA; apply: lter_trans e1e2.
  apply: lter_add; first by [].
  apply: lter_abs; apply: lter_trans (ltrW clb).
  by apply: cp; last done; apply: ltrW.
apply: lter_trans (_ : (z^+ (size l - 1) - x ^+ (size l - 1)) * e <= _).
  move: xzexp; rewrite -subr_gte0 ler_eqVlt; case/orP=> [xzexp | xzexp] /=.
    by rewrite /= -(eqP xzexp) subrr !mul0r lterr.
  rewrite -mulr_subr mulr_gte0pp //=; first by rewrite subr_gte0 /= ltrW.
  by rewrite subr_gte0.
rewrite [_ * e]mulrC; apply: lter_trans (_ : e * (u' * (z - x)) <= _)=> /=.
  rewrite lter_mulpl => //=; first by apply: ltrW; apply: lter_trans e2e.
  apply: lter_trans (_ : u * (z - x) <= _).
    apply: up => //.
      by apply: ltrW.
    apply: ltrW(lter_trans zav _); rewrite -invr1; apply: ltef_invpp => //.
    by apply: lter_le_trans x1gt1 _.
  by rewrite ltef_mulpr // subr_gte0.
rewrite mulrA ltef_mulpr; last by rewrite subr_gte0.
by rewrite /= /e divrK  ?lterr.
Qed.

Lemma Bernstein_isolate : forall a b l, a < b ->
   alternate (Mobius l a b) -> one_root1 l a b.
Proof.
rewrite /Mobius => a b l altb alt.
rewrite (_ : a = a + (a - a)); last by rewrite addrN addr0.
rewrite (_ : b = a + (b - a)); last by rewrite (addrC b) addrA addrN add0r.
apply one_root1_translate.
rewrite addrN (_ : (b-a) = (b-a) * 1); last by rewrite mulr1.
rewrite (_ : 0 =  (b-a) * 0); last by rewrite mulr0.
apply one_root1_expand; first by rewrite -(addrN a) lter_add2l.
apply one_root_reciprocate.
rewrite -[1]addr0; apply one_root2_translate.
by apply: alt_one_root2.
Qed.
