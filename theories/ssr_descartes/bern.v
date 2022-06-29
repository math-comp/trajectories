(*Require Import QArith ZArith Zwf Omega.*)
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun order.
From mathcomp Require Import bigop fingroup choice binomial poly.
From mathcomp Require Export ssralg rat ssrnum.
Require Import infra pol civt desc.

Import GroupScope .
Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope .

(* Set Printing Width 50. *)

(******************************************************************************)
(* Two predicates to describe that a polynomial has only one root,
  one_root1 l a b ==
     there exists c, d, and k, so that a,c,d,b is ordered, k is positive,
     the polynomial value is positive between a and c, negative between d and b
     the slope is less than -k between c and d.
  This statement is specifically suited to speak about roots inside the
  interval a b.

  one_root2 l a ==
     there exists c, d, and k, so that a is smaller than c, k is positive,
     the polynomial value is negative between a and c, and the slope is
     larger than k above c.

  A consequence of one_root2 is that there can be only one root above c, hence
  only one root above a.*)
(******************************************************************************)

Local Open Scope order_scope .

Definition one_root1 (l : {poly rat}) (a b : rat) :=
  exists c, exists d, exists k : rat,
     a < c /\ c < d /\ d < b /\ (0 < k)%Q /\
     (forall x, a < x -> x <= c -> (0 < l.[x])%Q) /\
     (forall x, d < x -> x < b -> (l.[x] < 0)%Q) /\
     (forall x y, c < x -> x <= y -> y < d ->
        k * (y - x) <= l.[x] - l.[y]).

Definition one_root2 (l : {poly rat}) (a : rat) :=
   exists c, exists k : rat,
     a < c /\ (0 < k)%Q /\
     (forall x, a < x -> x <= c -> l.[x] < 0)%Q /\
     (forall x y, c <= x -> x < y ->
         k * (y - x) <= l.[y] - l.[x]).

Lemma alt_one_root2 : forall l : {poly rat}, alternate l -> one_root2 l 0.
move => l a.
(*move: (desc l a) => [x1 [k [x1p [kp [neg sl]]]]].
move: (above_slope _ _ 0 _ kp sl) => [x2 [pos x1x2]].
by exists x1; exists k; split; first done; split; first done; split; done.
Qed.*) Admitted.

Definition translate_pol' (l : {poly rat}) (a : rat) : {poly rat}.
(*   mkseq (fun i : nat =>
     \sum_(k < size l) 'C(k, i)%:R * nth 0 l k * a ^+ (k - i)) (size l).*) Admitted.

Lemma eval_pol_big :
  forall (l : {poly rat}) x, l.[x] = \sum_(i < size l) nth 0 l i * x ^+ i.
Proof.
(*move => l x; elim: l=> [ | a l IHl]; first by rewrite big_ord0.
rewrite /= big_ord_recl /= mulr1 IHl; congr (fun v => a + v).
rewrite big_distrr; apply:eq_bigr => i _.
by rewrite /= [x * _]mulrC -mulrA [_ * x]mulrC exprS.
Qed.*) Admitted.

Lemma size_translate_pol' : forall l a, size (translate_pol' l a)  = size l.
Proof. (*by move => l a; rewrite /translate_pol' size_mkseq. Qed.*) Admitted.

Lemma pascalQ : forall a b n,
  (a + b) ^+ n = \sum_(i < n.+1) ('C(n, i)%:R * (a ^+ (n - i) * b ^+ i)) :> rat.
Proof.
move=> a b n.
rewrite exprDn_comm; last first.
  by rewrite /GRing.comm mulrC.
apply eq_bigr => i _.
rewrite mulrCA.
rewrite mulr_natl.
by rewrite mulrnAr.
Qed.

Lemma translate_pol'q :
  forall (l : {poly rat}) a x, (translate_pol' l a).[x] = l.[x + a].
Proof.
(*move => l a x; rewrite !eval_pol_big size_translate_pol' /translate_pol'.
apply: trans_equal (_ : \sum_(k < size l)
                      (\sum_(i < size l) 'C(k, i)%:R * l`_k * a^+ (k - i) * x^+ i)
                       = _).
  rewrite exchange_big /=.
  by apply: eq_bigr => i _; rewrite nth_mkseq //= big_distrl.
apply sym_equal.
apply: trans_equal (_ : \sum_(i < size l)
                \sum_(0 <= j < i.+1) l`_i * 'C(i, j)%:R * (x^+(i-j) * a ^+j) = _).
  apply: eq_bigr => i _; rewrite big_mkord pascalQ big_distrr /=.
  by apply: eq_bigr => j _; rewrite /= !mulrA.
have jgti : forall i : 'I_(size l),
      \sum_(i.+1 <= j < size l) l`_i * 'C(i, j)%:R * (x ^+ (i - j) * a ^+ j) = 0%R.
  move => i; apply: big1_seq => j /=; rewrite mem_index_iota.
  by move/andP => [ilj _]; rewrite bin_small // mulr0 mul0r.
apply: trans_equal (_ : \sum_(i < size l)
        \sum_(j < size l) l`_i * 'C(i, j)%:R * (x ^+ (i - j) * a ^+ j) = _).
  apply: eq_bigr => i _.
  rewrite -(@big_mkord rat 0%Q +%R (size l) (fun i => true)
   (fun j => l`_i * 'C(i, j)%:R *(x ^+ (i - j) * a ^+ j))).
  by rewrite  (@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti addr0.
apply: eq_bigr => i _.
rewrite -(@big_mkord rat 0%Q +%R (size l) (fun i => true)
   (fun j => l`_i * 'C(i, j)%:R *(x ^+ (i - j) * a ^+ j))).
rewrite !(@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti addr0 big_mkord.
rewrite -(@big_mkord rat 0%Q +%R (size l) (fun i => true)
   (fun j => 'C(i, j)%:R * l`_i * a ^+ (i - j) * x ^+ j)).
have jgti' :
   \sum_(i.+1 <= j < size l) 'C(i, j)%:R * l`_i * a ^+ (i - j) * x ^+ j = 0%Q.
  apply: big1_seq => j /=; rewrite mem_index_iota.
  by move/andP => [ilj _]; rewrite bin_small // !mul0r.
rewrite !(@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti' addr0 big_mkord.
set f := fun j:'I_i.+1 => (Ordinal ((leq_subr j i): ((i - j) < i.+1))%N).
have finv: forall j:'I_i.+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //; have : (j < i.+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp); apply: eq_bigr => j _.
have jli : (j <= i)%N by have : (j < i.+1)%N.
rewrite subKn // [x ^+ _ * _]mulrC ['C(i, j)%:R * _]mulrC !mulrA -bin_sub; last first.
  by rewrite leq_subr.
by rewrite subKn//.
Qed.*) Admitted.

Lemma reciprocalq :
  forall (l : {poly rat}) x, x \is a GRing.unit ->
     (reciprocal_pol l).[x] = x ^+ (size l - 1) * l.[x^-1].
Proof.
(*move=> [ | a l] x xp; rewrite !eval_pol_big size_reciprocate.
  by rewrite !big_ord0 mulr0.
rewrite big_distrr /=.
set f := fun j:'I_(size l).+1 =>
          Ordinal (leq_subr j (size l):size l - j <(size l).+1)%N.
have finv: forall j:'I_(size l).+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //;
      have : (j < (size l).+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp) {tmp}; apply: eq_bigr => j _.
have jls : (j < (size l).+1)%N by [].
rewrite /reciprocate_pol nth_rev; last by apply: leq_subr.
rewrite /= !subSS subKn // subn0 mulrA [(x ^+ (size l)) * _]mulrC -mulrA.
congr ((a :: l)`_j * _).
have tmp : size l = ((size l - j) + j)%N by rewrite subnK //.
by rewrite {3}tmp {tmp} expr_inv exprn_addr mulrK //; apply: unitr_exp.
Qed.*) Admitted.

Lemma one_root2_translate :
  forall l a b, one_root2 (translate_pol' l a) b -> one_root2 l (a + b).
Proof.
move=> l a b [x1 [k [x1a [kp [neg sl]]]]].
exists (a + x1); exists k.
split; first by rewrite ltr_add2l.
split; first by [].
split.
  move=> x abx xax1; rewrite (_ : x = x - a + a); last first.
    by rewrite addrNK.
  rewrite -translate_pol'q; apply: neg.
    by rewrite ltr_subr_addl.
  by rewrite ler_subl_addl.
move=> x y ax1x xy.
have t: forall z, z = (z - a) + a by move=> z; rewrite addrNK.
rewrite {2}(t y) {2}(t x) -!(translate_pol'q l) (_ : y - x = y - a - (x - a)).
  apply: sl.
    by rewrite ler_subr_addl.
  by rewrite ltr_le_sub//.
by rewrite [x + _]addrC opprD opprK addrA addrNK.
Qed.

Lemma one_root1_translate :
  forall l a b c, one_root1 (translate_pol' l c) a b ->
    one_root1 l (c + a) (c + b).
Proof.
move=> l a b c [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c + x1); exists (c + x2); exists k.
split; first by rewrite ltr_add2l.
split; first by rewrite ltr_add2l.
split; first by rewrite ltr_add2l.
split; first by [].
split.
  move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -translate_pol'q; apply pos.
    by rewrite ltr_subr_addl.
  by rewrite ler_subl_addl.
split.
  move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -translate_pol'q; apply: neg; rewrite -?ler_addlA //.
    by rewrite ltr_subr_addl.
  by rewrite ltr_subl_addl.
move=> x y cx1x xy ycx2.
have t: forall z, z = (z - c) + c by move=> z; rewrite addrNK.
rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
  by rewrite [x + _]addrC opprD opprK addrA addrNK.
rewrite -!(translate_pol'q l); apply: sl; rewrite ?ler_add2l //.
by rewrite ltr_subr_addl.
by rewrite ler_sub.
by rewrite ltr_subl_addl.
Qed.

Definition expand (p : {poly rat}) (k : rat) :=
  \poly_(i < size p)(p`_i * k ^+i).

Lemma one_root1_expand :
  forall l a b (c : rat), (0 < c)%Q -> one_root1 (expand l c) a b ->
    one_root1 l (c * a) (c * b).
Proof.
move=> l a b c cp [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c * x1); exists (c * x2); exists (k / c).
have tc : (0 < c^-1)%Q by rewrite invr_gt0.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in cp.*)
split; first by rewrite ltr_pmul2l.
split; first by rewrite ltr_pmul2l.
split; first by rewrite ltr_pmul2l.
split; first by rewrite divr_gt0.
split.
  move=> x acx xx1c.
    rewrite (_ : x = c * (x/c)); last first.
      by rewrite mulrC mulfVK // eq_sym lt_eqF.
(* NB(rei): eval_expand?*)
(*   rewrite -eval_expand; apply: pos.
     by rewrite ltef_divpr // mulrC.
   by rewrite ltef_divpl //= mulrC.*)
  admit.
split.
  move=> x cx2x xcb; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulfVK // eq_sym lt_eqF.
  (*rewrite -eval_expand; apply: neg; first by rewrite ltef_divpr 1?mulrC.
  by rewrite ltef_divpl 1?mulrC.*) admit.
have t: forall z, z = c * (z/c).
   by move=> z; rewrite [c * _]mulrC mulfVK // eq_sym lt_eqF.
(*move=> x y cx1x xy ycx2; rewrite -mulrA mulrDr mulrN ![c^-1 * _]mulrC
  {2}(t x) {2}(t y) -!(eval_expand l); apply: sl.
   by rewrite ltef_divpr // mulrC.
 by rewrite ltef_mulpr.
by rewrite ltef_divpl // mulrC.*) Admitted.

Lemma diff_xn_ub :
  forall (n : nat) (z : rat), (0 < z)%Q -> exists k : rat, (0 <= k)%Q /\
   forall x y : rat, (0 < x)%Q -> x <= y -> (y <= z) ->
      y ^+ n - x ^+ n <= k * (y - x).
Proof.
move => n; elim: n => [z z0| n IHn z z0].
  exists 0%Q; split => // x y x0 xy yz.
  by rewrite !expr0 subrr mul0r.
case: (IHn z z0) => k [k0 kp].
exists (z*k + z ^+ n); split => [ | x y x0 xy yz].
  apply: addr_ge0 => //=.
    by rewrite mulr_ge0// ltW.
  by apply: exprn_ge0 => //; exact: ltW.
rewrite !exprS.
rewrite (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulrDr mulrDl addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulrDl ler_add //=.
  rewrite -mulrA; apply: le_trans (_ : y * (k * (y - x)) <= _).
  rewrite ler_wpmul2l//.
    by rewrite (le_trans _ xy)// ltW.
    by apply: kp.
  rewrite !(mulrCA _ k) ler_wpmul2l//.
  by rewrite ler_wpmul2r// ?subr_ge0.
rewrite (mulrC (_ - _)).
rewrite ler_wpmul2r// ?subr_ge0//.
rewrite ler_expn2r//.
by rewrite nnegrE ltW.
by rewrite nnegrE ltW.
by apply: le_trans yz.
Qed.

Definition reciprocate_pol (l: seq rat) := rev l.

Lemma reciprocate_size :  forall l, size (reciprocate_pol l) = size l.
by move => l; rewrite /reciprocate_pol size_rev.
Qed.

Lemma cut_epsilon : forall eps:rat, (0 < eps)%R ->
  exists eps1 : rat, exists eps2, (0 < eps1 /\ 0 < eps2 /\ eps1 + eps2 <= eps)%R /\
      eps1 < eps /\ eps2 < eps.
move => eps p; exists (eps/(2%:R)); exists (eps/(2%:R)).
have p1 : (0 < eps/(2%:R))%R.
  by rewrite divr_gt0.
split.
  split => //.
  split => //.
  rewrite -mulrDr.
  by rewrite ger_pmulr//.
suff cmp : eps/2%:R < eps by [].
rewrite ltr_pdivr_mulr//.
by rewrite ltr_pmulr//.
Qed.

Lemma cm3 :
  forall b : rat, (0 < b)%Q -> forall l : {poly rat}, 
   {c | forall x y : rat, (0 <= x)%R -> (x <= y)%R -> (y <= b)%R -> 
    `|(l.[y] - l.[x])| <= c * (y - x)}.
Proof.
(*move=> b pb; elim=> [|u l [c cp]] /=.
  by exists 0 => x y; rewrite subrr absr0 mul0r lerr.
exists ((eval_pol (abs_pol l) b) + c * b) => x y px hxy hyb. 
rewrite addrAC oppr_add addrA subrr add0r addrC.
set el := eval_pol l in cp *.
rewrite (_ : y *_ - _ = y * el y - x * el y + x * el y - x * el x); last first.
  by rewrite -[_ - _ + _]addrA addNr addr0.
have py : 0 <= y by rewrite (ler_trans px).
have psyx : 0 <= y - x by rewrite lter_subrA /= add0r.
rewrite -addrA; apply: (ler_trans (absr_add_le _ _)).
rewrite -mulNr -mulr_addl -mulrN -mulr_addr !absf_mul (ger0_abs px).
rewrite (ger0_abs psyx) [_ * (y - x)]mulr_addl; apply: lter_add=> /=.
(*rewrite absr_nneg // [_ * (y - x)]mulr_addl; apply: lerT.*)
  rewrite mulrC lter_mulpr //=; apply: (ler_trans (ler_absr_eval_pol l y)).
  by rewrite eval_pol_abs_pol_increase // ?absrpos // ger0_abs.
rewrite (mulrC c); apply ler_trans with (x * c * (y - x)).
  by rewrite -mulrA lter_mulpl //= cp.
rewrite -!mulrA lter_mulpr //= ?(ler_trans hxy) //.
by apply: ler_trans (cp _ _ px hxy hyb); apply: absr_ge0.
Qed.*) Admitted.


Lemma one_root_reciprocate :
  forall l, one_root2 (reciprocal_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l [x1 [k [x1gt1 [kp [neg sl]]]]].
have x10 : (0 < x1)%R.
  by rewrite (lt_trans _ x1gt1).
(*have ux1 : GRing.unit x1 by apply/negP; move/eqP => q; rewrite q lterr in x10.*)
(*have uk: GRing.unit k by apply/negP; move/eqP => q; rewrite q lterr in kp.*)
set y' := x1 - (reciprocal_pol l).[x1] / k.
have y'1: x1 < y'.
  rewrite /y' -(ltr_add2l (-x1)) addNr addrA addNr add0r -mulNr.
  apply: divr_gt0 => //.
  rewrite oppr_gt0.
  by apply: neg => //.
have nx1 : (reciprocal_pol l).[x1] < 0%Q by apply: neg; rewrite // lterr.
have y'pos : (0 <= (reciprocal_pol l).[y'])%R.
  rewrite -[_ _ y']addr0 -{2}(addNr (reciprocal_pol l).[x1]) addrA
   -{2}(opprK (_ _ x1)) subr_gte0 /=.
  apply: le_trans (_ : k * (y' - x1) <= _)=> /=.
    by rewrite /y' (addrC x1) addrK mulrN mulrC mulrVK // unitfE gt_eqF.
  by apply sl => //.
have ltr1: (0 < 1)%Q by [].
move: (diff_xn_ub (size l - 1) _ ltr1) => {ltr1} [u [u0 up]].
have [u' [u1 u'u]] : exists u', (1 <= u' /\ u <= u')%R.
  case cmp: (1 <= u)%R; first by exists u; rewrite lexx cmp.
  by exists 1%Q; rewrite lexx; split=> //; rewrite ltW // ltNge cmp.
have u'0 : (0 < u')%R by apply: lt_le_trans u1.
(*have u'unit : GRing.unit u' by apply/negP; move/eqP=> q; rewrite q lterr in u'0.*)
have divu_ltr : forall x : rat, (0 <= x)%R -> (x / u' <= x)%R.
  move => x x0.
  rewrite ler_pdivr_mulr//.
  by rewrite ler_pemulr//.
(*   rewrite ler_eqVlt in x0; case/orP: x0 => [x0 | x0]. *)
(*      rewrite /=.  -lter_mulpl. *)

(* -(eqP x0) mulr0 lterr. *)
(*   rewrite -ltef_divpl // mulrV //. *)

(*   by apply/negP; move/eqP=> q; rewrite q lterr in x0. *)
have y'0 : (0 < y')%R by apply: lt_trans y'1.
pose y := y' + 1.
have y'y : y' < y by rewrite /y -{1}(addr0 y') ltr_add2l.
have y1 : x1 < y by apply: lt_trans y'1 _.
have ypos : (0 < (reciprocal_pol l).[y])%R.
  apply: le_lt_trans y'pos _=> /=.
  rewrite -subr_gte0 /=; apply: lt_le_trans (_ : k * (y - y') <= _)=> /=.
    by rewrite mulr_gt0// subr_gt0.
  by apply: sl=> //; apply: ltW.
have y0 : (0 < y)%R by apply: lt_trans y'y.
pose k' :=  ((k * x1 ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
have k'p : (0 < k')%R.
  rewrite /k' !mulr_gt0//.
  rewrite exprn_gt0//.
  by rewrite invr_gt0//.
pose e := k'/u'.
have ep: (0 < e)%R by rewrite divr_gt0//.
move: (cut_epsilon _ ep) => [e1 [e2 [[e1p [e2p e1e2e] [e1e e2e]]]]].
move: (@constructive_ivt _ (reciprocal_pol l) _ _ _ y'1 nx1 y'pos e1p).
move=> [[a b']].
rewrite {1}/pair_in_interval.
move=> /and5P[/and3P[cla ? clb']].
rewrite /pair_in_interval.
move=> /and3P[x1a ab b'y' nega posb' ?].
(*  [a [b' [cla [nega [posb' [clb' [x1a [ab b'y']]]]]]]].*)
move: (cm3 y y0 (reciprocal_pol l)) => [c cp].
have a0 : (0 < a)%R by apply: lt_le_trans x1a.
have c0 : (0 < c)%R.
(*  rewrite -(@ltef_mulpr _ (b' -a)) ?mul0r /=; last by rewrite subr_gte0.
  apply: lter_le_trans
   (_ : `|eval_pol (reciprocate_pol l) b' - eval_pol (reciprocate_pol l) a| 
          <= _)=> /=; last first.
  by apply: cp; last apply: ltrW(ler_lte_trans b'y' y'y); apply: ltrW.
  have d: 0 < eval_pol (reciprocate_pol l) b' - eval_pol (reciprocate_pol l) a.
    by rewrite subr_gte0 /=; apply: lter_le_trans posb'.
  by rewrite  absr_gt0 eq_sym ltrWN.*) admit.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in c0.*)
have [b [b'b [clb blty]]] : exists b, b' < b /\ c * (b - b') < e2 /\ b <= y.
(*  move: (cut_epsilon _ e2p) => [e3 [e4 [e3p [_ [_ [e3e2 _]]]]]].
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
    by rewrite mulrC -ltef_divp //= -lter_addrA /= -lerNgt addrC cmp.*) admit.
pose n := ((size l))%:R - 1.
have b'0 : (0 < b')%R by apply: lt_trans ab.
have b0 : (0 < b)%R by apply: lt_trans b'b.
(*have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q lterr in a0.
have ub': GRing.unit b' by apply/negP; move/eqP=> q; rewrite q lterr in b'0.*)
have b'v0: (0 < b'^-1)%R by rewrite invr_gte0.
have bv0 : (0 < b^-1)%R by rewrite invr_gte0.
have bb'v: b^-1 < b'^-1.
 (*
 by apply: ltef_invpp => //.*) admit.
(*have ub: GRing.unit b by apply/negP; move/eqP=> q; rewrite q lterr in b0.*)
exists b^-1; exists a^-1; exists k'.
split=> //.
split; first by admit. (*apply: ltef_invpp=> //=; apply: lter_trans b'b.*)
split.
  (*by rewrite -invr1; apply: ltef_invpp => //; apply: lter_le_trans x1a.*) admit.
split; first by [].
split.
  move => x x0 xb.
(*  have ux: GRing.unit x by apply/negP; move/eqP=>q; rewrite q lterr in x0.
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
  by apply: sl; first apply:ltrW.*) admit.
split.
  admit.
move => x z bvx xz zav ; rewrite le_eqVlt in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 lexx.
have x0: (0 < x)%R by apply: lt_trans bvx.
have z0 : (0 < z)%R by apply: (lt_trans x0).
(*have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0.
have uz: GRing.unit z by apply/negP;move/eqP=>q; rewrite q lterr in z0.*)
have invo_rec : forall l, reciprocal_pol (reciprocal_pol l) = l.
  (*by move => l'; rewrite /reciprocate_pol revK.*) admit.
rewrite -(invo_rec _ l).
rewrite (reciprocalq _ x) //; last first.
  by rewrite unitfE gt_eqF.
rewrite (reciprocalq _ z) //; last first.
  by rewrite unitfE gt_eqF.
rewrite reciprocal_size; last first.
  admit.
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
  rewrite /k2 /k' times2 -(mulrC (1 + 1)^-1) mulrA mulfV; first  by rewrite mul1r.
    have twop : (0 < (1 + 1))%R by admit. (*rewrite lter_addpl.*)
  by rewrite gt_eqF//.
rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
rewrite mulrDl; apply: ler_add; last first.
  have maj' : t3 * y^-1 ^+ (size l - 1) <= t3 * z^+ (size l - 1).
    have maj : y^-1 ^+(size l - 1) <= z ^+ (size l - 1).
      case: (size l - 1)%N => [ | n']; first by rewrite !expr0 lexx.
      (*rewrite lef_expS2 /=.
          apply: ltrW(lter_trans _ xz); apply: ler_lte_trans bvx.
          by apply: ltef_invpp.
        by apply: ltrW; rewrite invf_gte0.
      by apply: ltrW.*) admit.
(*    rewrite lter_mulpl // /t3.
    apply: lter_le_trans (_ : k * (x^-1 - z^-1) <= _); last first.
      apply: sl.
        rewrite -[x1]invrK // ltef_invpp //. 
          by rewrite invf_gte0.
        apply: ltrW(lter_le_trans zav _).
        by apply: ltef_invpp => //.
      by apply: ltef_invpp.
    apply: mulr_gte0pp=> /=; first by rewrite ltrW.
    by rewrite subr_gte0; apply: ltef_invpp=> //=; apply: ltrW.*) admit.
  apply: le_trans maj'; rewrite /t3 k2p mulrAC.
(*  rewrite ltef_mulpr; last by apply expf_gt0; rewrite invf_gte0.
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
  by apply: ltef_invpp  => //.*) admit.
rewrite /t1/k1/k' {t2 t3}.
have xzexp : (x ^+ (size l - 1) <= z ^+ (size l - 1)).
  case sizep : (size l - 1)%N => [ | n'].
    by rewrite !expr0 ltexx.
(*  by rewrite lef_expS2 //= ltrW.*) admit.
case: (lerP 0 ((reciprocal_pol l).[x^-1])) => sign; last first.
  (*apply: le_trans (_ : 0 <= _).

    rewrite mulNr lter_oppl oppr0; apply: mulr_ge0pp; last first.
      by rewrite subr_gte0 /= ltrW.
    apply: ltrW; exact k'p.
  apply: mulr_gte0nn.
    by rewrite subr_lte0.
  by apply: ltrW.
*)
  admit.
rewrite mulNr lter_oppl -mulNr opprB.
have rpxe : (reciprocal_pol l).[x^-1] <= e.
  apply:le_trans (_ : (reciprocal_pol l).[b] <= _) => /=.
    rewrite -subr_gte0 /= ; apply: le_trans (_ : k * (b - x^-1) <= _).
      rewrite mulr_ge0//.
        exact: ltW.
      rewrite subr_ge0//.
      admit.
    apply: sl.
    rewrite -[x1]invrK //. (*; apply: ltef_invpp => //.
        by rewrite invf_gte0.
      by apply: ltrW(lter_le_trans (lter_trans xz zav) _); apply: ltef_invpp.
    by rewrite -[b]invrK //; apply: ltef_invpp.*) admit.
    admit.
  rewrite -[_ _ b]addr0 -(addrN ((reciprocal_pol l).[b'])) addrA.
  rewrite (addrC (_.[b])) -addrA; apply: le_trans e1e2e.
  apply: ler_add; first by [].
(*  apply: lter_abs; apply: lter_trans (ltrW clb).
  by apply: cp; last done; apply: ltrW.*) admit.
apply: le_trans (_ : (z^+ (size l - 1) - x ^+ (size l - 1)) * e <= _).
  move: xzexp; rewrite -subr_gte0 le_eqVlt; case/orP=> [xzexp | xzexp] /=.
    by rewrite /= -(eqP xzexp) !mul0r.
  (*rewrite -mulr_subr mulr_gte0pp //=; first by rewrite subr_gte0 /= ltrW.
  by rewrite subr_gte0.*) admit.
rewrite [_ * e]mulrC; apply: le_trans (_ : e * (u' * (z - x)) <= _)=> /=.
  rewrite ler_pmul2l//.
  apply: le_trans (_ : u * (z - x) <= _).
    apply: up => //.
      by apply: ltW.
    apply: ltW (lt_trans zav _).
    (*; rewrite -invr1; apply: ltef_invpp => //.
    by apply: lter_le_trans x1gt1 _.*) admit.
  by rewrite ler_pmul2r// subr_gt0.
rewrite mulrA.
rewrite ler_pmul2r// ?subr_gt0//.
rewrite /e divrK// ?unitfE.
by rewrite gt_eqF//.
Admitted.

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
