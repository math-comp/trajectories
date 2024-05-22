From mathcomp Require Import all_ssreflect all_algebra archimedean.
(*Require Import QArith ZArith Zwf Omega.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun order.
From mathcomp Require Import bigop fingroup choice binomial poly.
From mathcomp Require Export ssralg rat ssrnum. *)
Require Import pol desc.
(* Require Import infra pol civt desc. *)

(* Import GroupScope . *)
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope .

(* Set Printing Width 50. *)

(******************************************************************************)
(* Two predicates to describe that a polynomial has only one root:            *)
(*   one_root1 l a b == there exists c, d, k, s.t. a, c, d, b are ordered,    *)
(*                      k is positive, the polynomial value is positive       *)
(*                      between a and c, negative between d and b, the slope  *)
(*                      is less than -k between c and d;                      *)
(*                      This statement is specifically suited to speak about  *)
(*                      roots inside the interval a b.                        *)
(*     one_root2 l a == there exists c, d, k, s.t. a is smaller than c,       *)
(*                      k is positive, the polynomial value is negative       *)
(*                      between a and c, and the slope is larger than k above *)
(*                      c;                                                    *)
(*                      A consequence of one_root2 is that there can be only  *)
(*                      one root above c, hence only one root above a.        *)
(******************************************************************************)

Local Open Scope order_scope .

Definition one_root1 {R : archiFieldType} (p : {poly R}) (a b : R) :=
  exists c d k : R, [/\ [/\ a < c, c < d, d < b & 0 < k],
    (forall x, a < x -> x <= c -> 0 < p.[x]),
    (forall x, d < x -> x < b -> p.[x] < 0) &
    (forall x y, c < x -> x <= y -> y < d -> k * (y - x) <= p.[x] - p.[y])]%R.

Definition one_root2 {R : archiFieldType} (p : {poly R}) (a : R) :=
   exists c k : R, [/\ a < c, 0 < k,
     (forall x, a < x -> x <= c -> p.[x] < 0) &
     (forall x y, c <= x -> x < y -> k * (y - x) <= p.[y] - p.[x])]%R.

Lemma alt_one_root2 (R : archiFieldType) (l : {poly R}) : alternate l ->
  one_root2 l 0.
Proof.
move/desc => [[x1 k] /= [/andP[x1p kp] neg] sl]; exists x1, k; split => //.
- by move=> x xgt0 xlex1; apply: neg; rewrite xgt0 xlex1.
- by move=> x y xlex1 xlty; apply: sl; rewrite xlex1 (ltW xlty).
Qed.

Definition translate_pol {R : ringType} (l : {poly R}) (a : R) : {poly R} :=
  l \Po ('X + a%:P).

Lemma size_translate_pol {R : idomainType} (l : {poly R}) a :
  size (translate_pol l a)  = size l.
Proof. by rewrite size_comp_poly2// size_XaddC. Qed.

Lemma translate_polq {R : comRingType} (l : {poly R}) a x :
  (translate_pol l a).[x] = l.[x + a].
Proof. by rewrite /translate_pol horner_comp 3!hornerE. Qed.

Lemma one_root2_translate {R : archiFieldType} (l : {poly R}) a b :
  one_root2 (translate_pol l a) b -> one_root2 l (a + b).
Proof.
move=> [x1 [k [x1a kp neg sl]]]; exists (a + x1), k; split => //.
- by rewrite ltrD2l.
- move=> x abx xax1; rewrite (_ : x = x - a + a); last by rewrite addrNK.
  by rewrite -translate_polq; apply: neg; rewrite ?ltrBrDl ?lerBlDl.
- move=> x y ax1x xy.
  have t z : z = (z - a) + a by rewrite addrNK.
  rewrite {2}(t y) {2}(t x).
  rewrite -!(translate_polq l) (_ : y - x = y - a - (x - a)); last first.
    by rewrite [x + _]addrC opprD opprK addrA addrNK.
  by apply: sl; rewrite ?lerBrDl ?ltr_leD.
Qed.

Lemma one_root1_translate {R : archiFieldType} (l : {poly R}) a b c :
  one_root1 (translate_pol l c) a b -> one_root1 l (c + a) (c + b).
Proof.
move=> [x1 [x2 [k [[ax1 x1x2 x2b kp] pos neg sl]]]].
exists (c + x1), (c + x2), k; split.
- by rewrite !ltrD2l.
- move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  by rewrite -translate_polq; apply pos; rewrite ?ltrBrDl ?lerBlDl.
- move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -translate_polq; apply: neg; rewrite -?ler_addlA //.
    by rewrite ltrBrDl.
  by rewrite ltrBlDl.
- move=> x y cx1x xy ycx2.
  have t z : z = (z - c) + c by rewrite addrNK.
  rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
    by rewrite [x + _]addrC opprD opprK addrA addrNK.
  rewrite -!(translate_polq l); apply: sl; rewrite ?lerD2l.
  + by rewrite ltrBrDl.
  + by rewrite lerB.
  + by rewrite ltrBlDl.
Qed.

Lemma diff_xn_ub {R : archiFieldType} (n : nat) :
  forall z, (0 < z)%R -> exists2 k, (0 <= k)%R &
   forall x y : R, (0 < x)%R -> x <= y -> (y <= z) ->
      y ^+ n - x ^+ n <= k * (y - x).
Proof.
elim: n => [z z0| n IHn z z0].
  by exists 0%R => // x y x0 xy yz; rewrite !expr0 subrr mul0r.
have [k k0 kp] := IHn z z0.
exists (z * k + z ^+ n) => [| x y x0 xy yz].
  by rewrite addr_ge0// ?exprn_ge0// ?mulr_ge0// ltW.
rewrite !exprS.
rewrite (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulrDr mulrDl addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulrDl lerD //=.
  rewrite -mulrA (@le_trans _ _ (y * (k * (y - x))))//.
    rewrite (ler_wpM2l (le_trans (ltW x0) xy))//.
    exact: kp.
  by rewrite !(mulrCA _ k) ler_wpM2l// ler_wpM2r// subr_ge0.
rewrite (mulrC (_ - _)) ler_wpM2r ?subr_ge0// lerXn2r//.
- by rewrite nnegrE ltW.
- by rewrite nnegrE ltW.
- exact: le_trans yz.
Qed.

Definition reciprocate_pol (l : seq rat) := rev l.

Lemma reciprocate_size l : size (reciprocate_pol l) = size l.
Proof. by rewrite /reciprocate_pol size_rev. Qed.

Lemma cut_epsilon {R : archiFieldType} (eps : R) : (0 < eps)%R ->
  exists eps1 eps2 : R, [/\ (0 < eps1)%R, (0 < eps2)%R, (eps1 + eps2 <= eps)%R,
    eps1 < eps & eps2 < eps].
Proof.
move=> p; exists (eps / 2%:R), (eps / 2%:R).
have p1 : (0 < eps / 2%:R)%R by rewrite divr_gt0// ltr0n.
have cmp : eps / 2%:R < eps.
   by rewrite ltr_pdivrMr// ?ltr0n// ltr_pMr// ltr1n.
split => //.
by rewrite -splitr.
Qed.

Lemma ler_horner_norm_pol {R : realFieldType} (l : {poly R}) x :
  (0 <= x)%R -> `|l.[x]| <= \sum_(i < size l) (`|l`_i| * x ^+ i).
Proof.
move=> xge0; elim/poly_ind: l => [ | l a Ih].
  by rewrite !hornerE normr0 size_poly0 big_ord0.
rewrite hornerE.
have [->|ln0] := eqVneq l 0%R.
  rewrite mul0r !hornerE size_polyC.
  have [->|an0] := eqVneq a 0%R; first by rewrite normr0 big_ord0.
  by rewrite big_ord1 /= expr0 mulr1 coefC eqxx.
rewrite size_MXaddC (negbTE ln0) /= big_ord_recl expr0 mulr1.
rewrite (le_trans (ler_normD _ _))//.
rewrite coefD coefMX eqxx add0r coefC eqxx hornerE [X in X <= _]addrC.
rewrite lerD// !hornerE.
have exteq (i : 'I_(size l)) : true ->
    `|(l * 'X + a%:P)`_(lift ord0 i)| * x ^+ lift ord0 i =
    (`|l`_i| * x ^+ i) * x.
  move=> _; rewrite lift0 coefD coefC /= addr0 coefMX /=.
  by rewrite exprS (mulrC x) mulrA.
rewrite normrM (ger0_norm xge0).
by rewrite (eq_bigr _ exteq) -mulr_suml ler_wpM2r.
Qed.

Lemma cm3 {R : realFieldType} (b : R) :
  (0 < b)%R -> forall l : {poly R}, {c | forall x y : R,
    (0 <= x)%R -> (x <= y)%R -> (y <= b)%R -> `|l.[y] - l.[x]| <= c * (y - x)}.
Proof.
move=> pb; elim/poly_ind=> [ | l u [c cp]].
  by exists 0%R => x y; rewrite !hornerE oppr0 normr0 lexx.
exists ((\sum_(i < size l) `|nth 0 l i| * b ^+ i) + c * b).
move=> x y xge0 xy yb.
rewrite !hornerE addrAC opprD addrA addrNK.
rewrite [A in `|A|](_ : _ = l.[y] * y - l.[y] * x + l.[y] * x - l.[x] * x);
  last by rewrite -[_ - _ + _]addrA addNr addr0.
have py : (0 <= y)%R by rewrite (le_trans xge0).
have psyx : (0 <= y - x)%R by rewrite subr_ge0.
rewrite -addrA (le_trans (ler_normD _ _)) //.
rewrite -mulrBr -mulrBl !normrM (ger0_norm xge0) (ger0_norm psyx).
rewrite [X in _ <= X]mulrDl lerD//.
  rewrite ler_wpM2r// (le_trans (ler_horner_norm_pol l y py))//.
  apply: ler_sum => i _.
  rewrite ler_wpM2l ?normr_ge0//.
  by rewrite lerXn2r// nnegrE (le_trans _ yb).
rewrite mulrAC ler_pM//; first exact: cp.
by rewrite (le_trans xy).
Qed.

Lemma one_root_reciprocate {R : archiFieldType} (l : {poly R}) :
  one_root2 (reciprocal_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> [x1 [k [x1gt1 kp neg sl]]].
have x10 : (0 < x1)%R by rewrite (lt_trans _ x1gt1)// ltr01.
set y' := x1 - (reciprocal_pol l).[x1] / k.
have y'1 : x1 < y'.
  rewrite /y' -(ltrD2l (-x1)) addNr addrA addNr add0r -mulNr.
  by rewrite divr_gt0 // oppr_gt0; exact: neg.
have nx1 : (reciprocal_pol l).[x1] < 0%R by apply: neg; rewrite // ltxx.
have y'pos : (0 <= (reciprocal_pol l).[y'])%R.
  rewrite -[_ _ y']addr0 -{2}(addNr (reciprocal_pol l).[x1]) addrA
   -{2}(opprK (_ _ x1)) subr_gte0 /=.
  apply: le_trans (_ : k * (y' - x1) <= _)=> /=.
    by rewrite /y' (addrC x1) addrK mulrN mulrC mulrVK // unitfE gt_eqF.
  exact: sl.
have [u u0 up] := diff_xn_ub (size l - 1) _ (@ltr01 R).
have [u' u1 u'u] : exists2 u', (1 <= u')%R & (u <= u')%R.
  case cmp: (1 <= u)%R; first by exists u => //; rewrite lexx cmp.
  by exists 1%R; rewrite ?lexx // ltW // ltNge cmp.
have u'0 : (0 < u')%R by apply: lt_le_trans u1.
have divu_ltr (x : R) : (0 <= x)%R -> (x / u' <= x)%R.
  by move=> x0; rewrite ler_pdivrMr// ler_peMr.
have y'0 : (0 < y')%R by apply: lt_trans y'1.
pose y := y' + 1.
have y'y : y' < y by rewrite /y ltrDl ltr01.
have y1 : x1 < y by apply: lt_trans y'1 _.
have ypos : (0 < (reciprocal_pol l).[y])%R.
  apply: le_lt_trans y'pos _=> /=.
  rewrite -subr_gte0 /=; apply: lt_le_trans (_ : k * (y - y') <= _)=> /=.
    by rewrite mulr_gt0// subr_gt0.
  by apply: sl=> //; apply: ltW.
have y0 : (0 < y)%R by apply: lt_trans y'y.
pose k' :=  ((k * x1 ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
have k'p : (0 < k')%R.
  rewrite /k' !mulr_gt0// ?invr_gt0 ?addr_gt0 ?ltr01//.
  by rewrite exprn_gt0// invr_gt0.
pose e : R := k' / u'.
have ep: (0 < e)%R by rewrite divr_gt0.
have [e1 [e2 [e1p e2p e1e2e e1e e2e]]] := cut_epsilon _ ep.
have [[a b']] := @constructive_ivt _ (@reciprocal_pol _ l) _ _ _ y'1 nx1 y'pos e1p.
rewrite {1}/pair_in_interval.
move=> /and5P[/and3P[cla ? clb']].
rewrite /pair_in_interval.
move=> /and3P[x1a ab b'y' nega posb' bma].
have [c cp] := cm3 y y0 (reciprocal_pol l).
have a0 : (0 < a)%R by apply: lt_le_trans x1a.
have c0 : (0 < c)%R.
  rewrite -(@pmulr_lgt0 _ (b' - a)) ?subr_gt0//.
  rewrite (@lt_le_trans _ _  (`|(reciprocal_pol l).[b'] -
                                (reciprocal_pol l).[a] |))//; last first.
    apply: cp.
    - exact: ltW.
    - exact: ltW.
    - by rewrite (le_trans b'y')// ltW.
  by rewrite normr_gt0// gt_eqF// subr_gt0.
have [b [b'b clb blty]] : exists b, [/\ b' < b, c * (b - b') < e2 & b <= y].
  have [e3 [e4 [e3p e4p e3e4e2 e3e2 e4e2]]] := cut_epsilon _ e2p.
  case cmp : (b' + e2 / c <= y).
    exists (b' + e3 / c); split.
    - by rewrite ltrDl// divr_gt0.
    - by rewrite (addrC b') addrK mulrA (mulrC c) mulfK // gt_eqF.
    - apply: le_trans cmp; rewrite lerD2l//.
      by rewrite ler_pM// ltW// invr_gt0.
  exists y; split => //.
  - by rewrite (le_lt_trans b'y').
  - by rewrite mulrC -ltr_pdivlMr// ltrBlDl ltNge cmp.
pose n := ((size l))%:R - 1.
have b'0 : (0 < b')%R by apply: lt_trans ab.
have b0 : (0 < b)%R by apply: lt_trans b'b.
have b'v0 : (0 < b'^-1)%R by rewrite invr_gte0.
have bv0 : (0 < b^-1)%R by rewrite invr_gte0.
have bb'v : b^-1 < b'^-1 by rewrite ltf_pV2.
exists b^-1, a^-1, k'; split => //.
- split => //.
  + by rewrite (lt_le_trans bb'v)// lef_pV2// ltW.
  + by rewrite invf_lt1// (lt_le_trans _ x1a).
- move => x x0 xb.
  have xv0 : (0 < x^-1)%R by rewrite invr_gt0.
  have xexp0 : (0 < x^-1 ^+ (size l - 1))%R by rewrite exprn_gt0.
  have b'x : b' < x^-1.
    by rewrite -(invrK b')// ltf_pV2// (le_lt_trans _ bb'v).
  rewrite -(pmulr_rgt0 _ xexp0) -{2}[x]invrK -horner_reciprocal; last first.
    by rewrite unitfE gt_eqF.
  apply: (le_lt_trans posb'); rewrite -subr_gte0 /=.
  apply: lt_le_trans (_ : k * (x^-1 - b') <= _)=> /=.
    by rewrite mulr_gt0// subr_gt0.
  by apply: sl => //; rewrite (le_trans x1a)// ltW.
- move => x a1x xlt1.
  have x0 : (0 < x)%R by apply: lt_trans a1x; rewrite invr_gt0.
  have xv0 : (0 < x^-1)%R by rewrite invr_gt0.
  have x1a0 : (x^-1 < a)%R by rewrite -[a]invrK ltf_pV2// posrE// invr_gt0.
  have xexp0 : (0 < x^-1 ^+ (size l - 1))%R by apply: exprn_gt0.
  rewrite -(pmulr_rlt0 _ xexp0) -{2}[x]invrK -horner_reciprocal//; last first.
    by rewrite unitfE gt_eqF.
  case cmp: (x^-1 <= x1); last (move/negbT:cmp => cmp).
    by apply: neg => //; rewrite -invr1 ltf_pV2// ?posrE ltr01//.
  apply: lt_trans nega; rewrite -subr_gte0.
  apply: lt_le_trans (_ : k * (a - x^-1) <= _).
    by rewrite mulr_gt0// subr_gt0.
  apply: sl => //.
  rewrite -ltNge in cmp.
  exact: ltW.
- move=> x z bvx + zav; rewrite le_eqVlt => /predU1P[->|xz].
    by rewrite !addrN mulr0 lexx.
  have x0 : (0 < x)%R by apply: lt_trans bvx.
  have z0 : (0 < z)%R by apply: (lt_trans x0).
  have := horner_reciprocal1 l (unitf_gt0 x0) => ->.
  have := horner_reciprocal1 l (unitf_gt0 z0) => ->.
  rewrite (_ : _ * _ - _ = (x ^+ (size l - 1) - z ^+ (size l - 1)) *
                       (reciprocal_pol l).[x ^-1] +
                       ((reciprocal_pol l).[x ^-1] -
                        (reciprocal_pol l).[z ^-1]) *
                        z ^+ (size l - 1)); last first.
    by rewrite !mulrDl !mulNr ![_.[_] * _]mulrC !addrA addrNK.
  set t1 := _ * _.[_].
  set t3 := (_.[_] - _).
  set t2 := t3 * _.
  pose k1 := -k'; pose k2 := k' + k'.
  have times2 : forall a : rat, a + a = (1 + 1) * a.
    by move => a'; rewrite mulrDl !mul1r.
  have k2p : k2 = (k * x1 ^+ 2 * y ^-1 ^+ (size l - 1)).
    rewrite /k2 /k' -mulr2n -mulr_natl.
    rewrite -(mulrC (1 + 1)^-1) mulrA mulfV; first  by rewrite mul1r.
    have twop : (0 < (1 + 1))%Q by [].
    by rewrite gt_eqF// ltr0n.
  rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
  have x1ltvz : x1 < z ^-1.
    by rewrite (le_lt_trans x1a) // -[a]invrK ltef_pV2 ?posrE ?invr_gt0 ?ltW.
  rewrite mulrDl; apply: lerD; last first.
    have maj' : t3 * y^-1 ^+ (size l - 1) <= t3 * z^+ (size l - 1).
      have maj : y^-1 ^+(size l - 1) <= z ^+ (size l - 1).
        case: (size l - 1)%N => [ | n']; first by rewrite !expr0 lexx.
        have /pow_monotone : (0 <= y ^-1 <= z)%R.
          rewrite ltW /=; last by rewrite invr_gt0 (lt_trans x10).
          apply: ltW (le_lt_trans _ xz); apply: ltW (le_lt_trans _ bvx).
          by rewrite lef_pV2 ?posrE.
        by move=> /(_ n'.+1) /andP[].
      rewrite lter_pM2l // /t3.
      apply: (lt_le_trans _ (_ : k * (x ^-1 - z ^-1) <= _)); last first.
        apply: sl; first by apply: ltW.
        by rewrite ltf_pV2.
      by rewrite mulr_gt0 // subr_gt0 ltf_pV2.
    apply: le_trans maj'; rewrite /t3 k2p mulrAC.
    rewrite lter_pM2r; last by apply: exprn_gt0; rewrite invr_gt0.
    apply: ltW (lt_le_trans _ (_ :k * (x ^-1 - z ^-1) <= _)).
      rewrite ![k * _]mulrC mulrAC lter_pM2r; last by [].
      rewrite -[x ^-1](mulrK (unitf_gt0 z0)).
      rewrite  -[X in _ < _ - X](mulrK (unitf_gt0 x0)) -(mulrC x) -(mulrC z).
      rewrite (mulrAC x) -!(mulrA _ (x^-1)) -mulrBl (mulrC (z - x)).
      rewrite lter_pM2r; last by rewrite subr_gte0.
      apply: lt_le_trans (_ : x1 / z <= _); first by rewrite lter_pM2l.
      rewrite lter_pM2r; last by rewrite invr_gte0.
      by apply: ltW (lt_trans x1ltvz _); rewrite ltef_pV2 ?posrE.
    apply: sl; first by apply: ltW.
    by rewrite ltef_pV2 ?posrE.
  rewrite /t1/k1/k' {t2 t3}.
  have xzexp : (x ^+ (size l - 1) <= z ^+ (size l - 1)).
    case sizep : (size l - 1)%N => [ | n'].
      by rewrite !expr0 ltexx.
    have /pow_monotone : (0 <= x <= z)%R.
      by rewrite !ltW.
    by move=>/(_ n'.+1)=> /andP[].
  case: (lerP 0 ((reciprocal_pol l).[x^-1])) => sign; last first.
    apply: le_trans (_ : 0 <= _)%R.
      rewrite mulNr lterNl oppr0; apply: mulr_ge0; last first.
        by rewrite subr_gte0 ltW.
      exact (ltW k'p).
    by rewrite nmulr_lge0 // subr_lte0.
  rewrite mulNr lterNl -mulNr opprB.
  have rpxe : (reciprocal_pol l).[x^-1] <= e.
    apply:le_trans (_ : (reciprocal_pol l).[b] <= _) => /=.
      rewrite -subr_gte0 /= ; apply: le_trans (_ : k * (b - x^-1) <= _).
        rewrite mulr_ge0 //.
          exact: ltW.
        by rewrite subr_ge0 ltW // -(invrK b) ltef_pV2 ?posrE.
      apply: sl.
        by apply: (ltW (lt_trans x1ltvz _)); rewrite ltef_pV2 ?posrE.
      by rewrite -(invrK b) ltef_pV2 ?posrE.
    rewrite -[_ _ b]addr0 -(addrN ((reciprocal_pol l).[b'])) addrA.
    rewrite (addrC (_.[b])) -addrA; apply: le_trans e1e2e.
    apply: lerD; first by [].
    apply: (le_trans (ler_norm _)).
    by apply/ltW/(le_lt_trans _ clb)/cp=> //; apply/ltW.
  apply: le_trans (_ : (z^+ (size l - 1) - x ^+ (size l - 1)) * e <= _).
    move: xzexp; rewrite -subr_gte0 le_eqVlt => /predU1P[<-|xzexp] /=.
      by rewrite !mul0r.
  by rewrite lter_pM2l.
rewrite [_ * e]mulrC; apply: le_trans (_ : e * (u' * (z - x)) <= _)=> /=.
  rewrite ler_pM2l//.
  apply: le_trans (_ : u * (z - x) <= _).
    apply: up => //.
      by apply: ltW.
    apply: ltW (lt_trans zav _).
    by rewrite invf_lt1 //; by apply: lt_le_trans x1a.
  by rewrite ler_pM2r// subr_gt0.
rewrite mulrA.
rewrite ler_pM2r// ?subr_gt0//.
by rewrite /e divrK// unitfE gt_eqF.
Qed.

(* TODO(rei)
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
*)
