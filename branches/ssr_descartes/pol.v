(* Require Import QArith ZArith Zwf Omega.*)
Require Import ssreflect ssrbool eqtype  ssrfun ssrnat binomial div seq choice.
Require Import fintype bigop fingroup ssralg poly orderedalg.
(* Require Export infra. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Import GroupScope .
Import GRing.Theory.
Import OrderedRing.Theory.
Open Local Scope ring_scope .

Set Printing Width 50.

(*
Section ToBeAddedInOrderedAlg.

Section Idomain.

Variable (R : oIdomainType).
Lemma absr_sum : forall m  (G : nat -> R),
  `|\sum_(i < m) G i| <= \sum_(i < m) `|G i|.
Proof.
elim=> [|m ihm] G; first by rewrite !big_ord0 absr0 lerr.
rewrite !big_ord_recr /=; apply: ler_trans (absr_add_le _ _) _=> /=.
by rewrite ler_add2l; apply: ihm.
Qed.

Lemma ge0_sum : forall m (G : nat -> R), 
  (forall i, ((i < m)%N ->  0 <= G i)) -> 0 <= \sum_(i < m) G i.
Proof.
elim=> [|m ihm] G hp; first by rewrite big_ord0 lerr.
rewrite big_ord_recr /=; apply: addr_ge0; last by apply: hp; exact: ltnSn.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

Lemma ge_sum :  forall m (G1 G2 : nat -> R), 
  (forall i, ((i < m)%N ->  G1 i <= G2 i)) -> \sum_(i < m) G1 i <= \sum_(i < m) G2 i.
Proof.
elim=> [|m ihm] G1 G2 hp; first by rewrite !big_ord0 lerr.
rewrite ! big_ord_recr /=; apply: ler_add=> /=; last by apply: hp; exact: ltnSn.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

End Idomain.


Variable F : oFieldType.

Lemma gt1expn : forall n (x : F), 1 <= x -> 1 <= x^+n.
Proof.
elim=> [| m ihm] x hx; first by rewrite expr0 lerr.
rewrite exprS; apply: ler_trans (hx) _; rewrite -{1}(mulr1 x).
rewrite ler_pmul2r ?exprn_ege1 //; apply: ltr_le_trans hx; exact: ltr01.
Qed.

Lemma absrge1 : forall x : F, 1 < x -> x^-1 < 1.
Proof.
move=> x lt1x; rewrite -(mul1r (x^-1)) ltef_divpl /= ?mul1r //. 
apply: lter_trans lt1x; exact: ltr01.
Qed.

Lemma absf_inv : forall x : F, `|x ^-1| = `|x|^-1.
Proof.
move=> x; case e: (x == 0); first by rewrite (eqP e) absr0 invr0 absr0.
have axn0 : ~~ (`|x| == 0) by rewrite absr_eq0 e.
by apply: (mulfI axn0); rewrite mulfV // -absf_mul mulfV ?e // absr1.
Qed.

Lemma expf_gt1 : forall m (x : F), x > 1 -> x^+m.+1 > 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr1.
apply: lter_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
apply: lter_mulpl=> /=; last exact: ihm.
apply: lter_trans hx; exact: ltr01.
Qed.

Lemma expf_ge1 : forall m (x : F), x >= 1 -> x^+m >= 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr0 lerr.
apply: lter_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
apply: lter_mulpl=> /=; last exact: ihm.
apply: lter_trans hx; apply: ltrW; exact: ltr01.
Qed.

End ToBeAddedInOrderedAlg.
*)
Section MoreMapPoly.

Variables (aR rR : ringType).

Variable f : aR -> rR.

Lemma map_polyC : forall c,
  map_poly f c%:P = if c == 0 then 0 else (f c)%:P.
Proof.
move=> a; rewrite /map_poly /= size_polyC.
case a0 : (a == 0); apply/polyP=> i; rewrite coef_poly //=.
by rewrite ltnNge lt0n !coefC; case: (i == 0)%N.
Qed.


End MoreMapPoly.

Section PolsOnAbstractRationals.

Variable Q : oFieldType.

(*Polynomial obtained from p by taking the absolute values of the coefficients*)

Definition abs_pol (p : {poly Q}) := map_poly (fun x => `|x|) p.

Lemma size_abs_pol p : size (abs_pol p) = size p.
Proof.
move=> p; case p0 : (p == 0).
  by rewrite  (eqP p0) /abs_pol /= map_polyC eqxx.
by rewrite /abs_pol /map_poly size_poly_eq // absr_eq0 lead_coef_eq0 p0.
Qed.

Lemma ler_absr_eval_pol : forall (p : {poly Q})(x : Q), 
  `|p.[x]| <= (abs_pol p).[`|x|].
Proof.
move=> p x; rewrite !horner_coef size_abs_pol.
rewrite (_ : \sum_(i < size p) _ * _ = \sum_(i < size p) `|p`_i * x ^+ i|).
  by apply: absr_sum_le.
apply: congr_big => // [] [i hi] _.
by rewrite coef_poly /= hi absr_mul absr_exp.
Qed.

Lemma ler0_eval_pol_abs_pol :
  forall l x, 0 <= x -> 0 <= (abs_pol l).[x].
Proof.
move=> p x hx; rewrite /abs_pol /map_poly horner_poly. 
apply: sumr_ge0 => [] [i hi] /=. 
by apply: mulr_ge0; rewrite ?absr_ge0 // exprn_ge0.
Qed.

Lemma eval_pol_abs_pol_increase : 
  forall l x y, 0 <= x -> x <= y ->
    (abs_pol l).[x] <= (abs_pol l).[y].
move=> p x y hx hxy; rewrite /abs_pol /map_poly !horner_poly.
apply: ler_sum => [] [i lei] /= _; apply: ler_pmul2rW; rewrite ?absr_ge0 //.
exact: ler_le_pexp2.
Qed.

Lemma cm3 :
  forall (p : {poly Q}) b, 0 < b ->
   {c | forall x y, 0 <= x -> x <= y -> y <= b -> 
    `|(p.[y] - p.[x])| <= c * (y - x)}.
Proof.
move=> p b bp; elim/poly_ind: p => [| p u [c cp]].
  by exists 0 => x y xp xy xc; rewrite mul0r !hornerC subrr absr0 lerr.
exists ((abs_pol p).[b] + c * b) => x y px hxy hyb. 
rewrite !horner_lin addrAC oppr_add addrA addrNK.
have py : 0 <= y by rewrite (ler_trans px).
have psyx : 0 <= y - x by rewrite subr_ge0.
rewrite (_ : _ * y - _ = y * p.[y] - x * p.[y] + x * p.[y] - x * p.[x]); last first.
  by rewrite -[_ - _ + _]addrA addNr addr0 mulrC [_ * y]mulrC.
rewrite -addrA; apply: (ler_trans (absr_add_le _ _)).
rewrite -mulNr -mulr_addl -mulrN -mulr_addr !absr_mul (ger0_abs px).
rewrite (ger0_abs psyx) [_ * (y - x)]mulr_addl; apply: ler_add=> /=.
  rewrite mulrC ler_pmul2lW //.
  apply: (ler_trans (ler_absr_eval_pol p y)).
  by rewrite eval_pol_abs_pol_increase // ?absrpos // ger0_abs.
rewrite (mulrC c); apply ler_trans with (x * c * (y - x)).
  by rewrite -mulrA ler_pmul2rW //= cp.
rewrite -!mulrA ler_pmul2lW //= ?(ler_trans hxy) //.
by apply: ler_trans (cp _ _ px hxy hyb); apply: absr_ge0.
Qed.


Definition translate_pol (l : {poly Q}) (a:Q) :=
  \poly_(i < size l)
     \sum_(k < size l) nth 0 l k * a ^+ (k - i) *+ 'C(k, i).

Lemma size_translate_pol : forall l a,
  size (translate_pol l a)  = size l.
Proof.
  move => l a; rewrite /translate_pol.
case sl: (size l) => [| s]; last first.
  rewrite size_poly_eq //= big_ord_recr big1 /=.
  - rewrite add0r binn subnn mulr1 mulr1n -[s]/(s.+1.-1) -sl.
    by rewrite -/(lead_coef l) lead_coef_eq0 -size_poly_eq0 sl.
  by move=> [i hi] /= _; rewrite bin_small.
apply/eqP; rewrite size_poly_eq0; apply/eqP; apply/polyP=> i.
by rewrite coef_poly.
Qed.

Lemma eval_translate_pol : forall (p : {poly Q}) (a x : Q),
  (translate_pol p a).[x] = p.[x + a].
Proof.
move=> p a x; rewrite /translate_pol /= horner_poly.
rewrite horner_coef.
transitivity (\sum_(i < size p)
      \sum_(k < size p)
          p`_k * a ^+ (k - i) *+ 'C(k, i) * x ^+ i).
- by apply: congr_big => // i _; rewrite big_distrl.
rewrite exchange_big /=; apply: congr_big => // [[i hi]]  _ /=.
transitivity 
  (p`_i * \sum_(i0 < size p) a ^+ (i - i0) *+ 'C(i, i0) * x ^+ i0).
- rewrite big_distrr /=; apply: congr_big => // j _; rewrite mulrA.
  by congr (_ * _); rewrite mulrnAr.
congr (_ * _); rewrite addrC exprn_addl.
transitivity
  (\sum_(0 <= i0 < (size p)) a ^+ (i - i0) *+ 'C(i, i0) * x ^+ i0).
- symmetry; exact: big_mkord.
rewrite (big_cat_nat _ _ _ _ hi) ?leq0n //=. 
rewrite (_ : \sum_(i.+1 <= i0 < size p) _ = 0); last first.
- apply: big1_seq => /= [] k; rewrite mem_index_iota; case/andP=> hik hksp.
  by rewrite bin_small // mulr0n mul0r.
by rewrite big_mkord addr0; apply: congr_big=> // k _; rewrite mulrnAl.
Qed.

Lemma pol_eval_translate_pol : forall (p : {poly Q}) (a x : Q),
  p.[x] = (translate_pol p a).[x - a].
Proof. by move=> p a xl; rewrite eval_translate_pol addrNK. Qed.

Lemma translate_polC : forall (a b : Q), translate_pol a%:P b = a%:P.
Proof.
move=> a b; rewrite /translate_pol size_polyC.
case a0 : (a == 0); first by rewrite (eqP a0).
rewrite /= big_ord_recl big_ord0 coefC eqxx subnn bin0 expr0.
by rewrite mulr1n mulr1 addr0 poly_cons_def mul0r add0r.
Qed.

Lemma translate_pol_scal : forall (p : {poly Q})(a b : Q),
  translate_pol (a%:P * p) b = a%:P * (translate_pol p b).
Proof.
move=> p a b; case a0 : (a == 0).
  by rewrite (eqP a0) !mul0r translate_polC.
rewrite /translate_pol size_polyC_mul; last by rewrite a0.
rewrite !poly_def big_distrr /=; apply: congr_big => //[]  [i hi] _ /=.
rewrite [a%:P * (_ *: _)]mul_polyC scalerA; congr (_ *: _); rewrite big_distrr /=.
by apply: congr_big => //[]  [j hj] _ /=; rewrite coef_Cmul !mulrnAr mulrA.
Qed.

Lemma pol_ucont : forall (p : {poly Q}) a b, a < b -> 
  {c : Q | 
    forall x y : Q, 
      a <= x -> x <= y -> y <= b -> `|p.[y] - p.[x]| <= c * (y - x)}.
Proof.
move=> p a b.
wlog : p b / 0 < b.

  move=> hwlog hab; case: (ltrP 0 b) => hb0; first by exact: hwlog.
  have ha1 : a < 1.
    apply: ltr_trans hab _ => /=; apply: ler_lt_trans hb0 _ => /=.
    exact: ltr01.
  case: (hwlog p 1 (@ltr01 Q) ha1) => c hc; exists c => x y ax xy yb.
  apply: hc => //; apply: ler_trans yb _; apply: ler_trans hb0 _; apply: ltrW.
  exact: ltr01.
move=> hb0 hab.
have sp : b - a > 0 by rewrite subr_gte0.
case: (cm3 (translate_pol p a) sp) => c hc.
exists c => x y ax xy yb.
rewrite !(pol_eval_translate_pol p a).
have -> :  y - x = (y - a) - (x - a).
 by rewrite oppr_sub -addrA [- _ + _]addrA addNr add0r.
by apply: hc; rewrite ?subr_gte0 // lter_add2l.
Qed.


Lemma pol_cont : forall (l : {poly Q}) (x eps :Q), 0 < eps ->
  exists delta, 0 < delta /\ forall y,  `|(y - x)| < delta ->
    `|l.[y] - l.[x]| < eps.
Proof.
have side :  forall (l : {poly Q}) (x:Q) eps, 0 < eps ->
  exists delta, 0 < delta /\ forall y, x <= y -> `|(y - x)| < delta ->
    `|(l.[y] - l.[x])| < eps.
  move => l x e ep. (* move: (translate_pol l (x-1)) => [l' pl']*)
  have zlt2 : (0 : Q) < 1 + 1 by rewrite -(addr0 0) ltr_add //= ltr01.
  case: (cm3 (translate_pol l (x -1)) zlt2) => c pc.
  have yxx1 : forall y, y - x = y - (x - 1) - (x - (x - 1)).
    by move => y; rewrite !oppr_add !opprK !addrA addrNK addrK.
  have leb0 : 0 <= x - (x - 1).
    by rewrite oppr_add opprK addrA addrN add0r ltrW // ltr01.
  case c0 : (c == 0).
    exists 1; split; rewrite ?ltr01 //.
    move => y xy1 ycx.
    have cxy : (c * (y - x) < e) by rewrite (eqP c0) mul0r.
    rewrite 2!(pol_eval_translate_pol l (x - 1)).
    apply: ler_lt_trans cxy => /=.
    rewrite yxx1; apply: pc=> //; first by rewrite ler_add //= lerr.
    rewrite oppr_add addrA ler_add ?opprK /= ?lerr //= ltrW //. 
    by case/absr_lt: ycx.
  have cp : (0 < c). 
    move: (negbT c0) =>{c0} c0.
    rewrite ltr_neqAle eq_sym c0 /=.
    have tmp : (1:Q) <= 1 + 1.
      by rewrite -{1}(addr0 1) ler_add /= ?lerr // ltrW ?ltr01.
    have := pc 0 1 (lerr _) (ltrW (ltr01 _)) tmp; move {tmp}.
    rewrite oppr0 addr0 mulr1=>tmp; apply: ler_trans tmp; exact: absr_ge0.
  have ecp: (0 < e / c) by rewrite ltr_pdivl_mulr // mul0r. 
  have ie1: exists e1, 0 < e1 /\ e1 <= 1 /\ e1 <= e/c.
    case cmp : (e/c < 1).
      exists (e/c).
      by split; first done; split; last apply:lerr; apply ltrW.
    by exists 1; rewrite ltr01 lerr; do 2 split => //; rewrite lerNgt cmp.
  move: ie1 => [e1 [e1p [e11 e1ec]]].
  exists e1; split; first by [].
  move => y xy xcy.
  have cp' : 0 < c^-1 by rewrite invr_gte0.  
  have xcy' : (c * (y - x)) < e.
    rewrite mulrC -ltr_pdivl_mulr //; apply: ltr_le_trans e1ec.
    by case/absr_lt: xcy.
  apply: ler_lt_trans xcy'; rewrite (yxx1 y) 2!(pol_eval_translate_pol l (x - 1)).
  apply: pc => //; first by rewrite ler_add //= lerr.
    rewrite oppr_add addrA ler_add //= ?opprK ?lerr // ltrW //; apply: ltr_le_trans e11=> /=.
  by case/absr_lt: xcy.
move => l x e ep.
move: (side l x e ep) => [delta1 [dp1 de1]].
pose l' := \poly_(i < size l) (l`_i * (- 1)^+i).
(*move: (mirror_pol l) => [l' pl'].*)
move: (side l' (-x) e ep) => [delta2 [dp2 de2]].
have : exists delta, 0 < delta /\ delta <= delta1 /\ delta <= delta2.
  case cmp: (delta1 < delta2).
    by exists delta1; split; last (split; first apply:lerr; apply: ltrW).
  exists delta2; split; first done; last (split; last apply:lerr).
  by rewrite lerNgt cmp.
move => [delta [dp [dd1 dd2]]].
  exists delta; split; first by [].
move => y ycx; case cmp: (y < x).
  have mirror : forall u, l.[u] = l'.[- u].
  - move=> u; rewrite /l' horner_coef horner_poly; apply: congr_big=> // i _.
  by rewrite -mulrA; congr (_ * _); rewrite -exprn_mull mulrN mulNr opprK mul1r.
  rewrite 2!mirror; apply: de2; first by rewrite ler_opp2 ltrW.
  by rewrite -oppr_add absr_opp; apply: ltr_le_trans dd2.
apply: de1; first by rewrite lerNgt cmp.
by apply: ltr_le_trans dd1.
Qed.


Lemma mkseq_shift :
  forall T (f : nat ->T) n, mkseq f n.+1 = f 0%nat::mkseq (fun x => f x.+1) n.
Proof.
move => T f n; rewrite /mkseq -[n.+1]/(1+n)%nat iota_add addnC iota_addl /=.
by congr (cons (f 0%nat)); rewrite -map_comp; apply: eq_in_map; move => x _ /=.
Qed.


Definition reciprocate_pol (l: {poly Q}) := \poly_(i < size l)l`_(size l - i.+1).


Lemma reciprocateq :
  forall (l : {poly Q}) x, x != 0 ->
     (reciprocate_pol l).[x] = x ^+ (size l - 1) * l.[x^-1].
Proof.
move=> l x xn0 ; rewrite /reciprocate_pol horner_poly.
case sl : (size l) => [| n].
  rewrite sub0n expr0 mul1r big_ord0; move/eqP: sl; rewrite size_poly_eq0.
  by move/eqP->; rewrite horner0.
rewrite horner_coef subn1 /=  big_distrr /=.
set f := fun j:'I_(n).+1 =>
          Ordinal (leq_subr j (n):n - j <(n).+1)%N.
have finv: forall j:'I_(n).+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //;
      have : (j < (n).+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp) {tmp} sl; apply: eq_bigr => [[j hj]] _ /=.
rewrite subSS subKn // -mulrCA; congr (_ * _).
have xej : x^+j != 0 by exact: expf_neq0.
apply: (mulIf xej); rewrite {xej} -mulrA -exprn_mull mulVf // exp1rn mulr1.
by rewrite -exprn_addr subnK.
Qed.

Definition expand (l : {poly Q})(r : Q) :=
  \poly_(i < size l)(l`_i * r ^+i).


(* The correction lemma for expand. *)
Lemma eval_expand : forall l r x, 
  (expand l r).[x] = l.[r * x].
Proof.
move => l r x.
rewrite /expand horner_poly horner_coef; apply: congr_big=> // [[i hi]] _ /=.
by rewrite exprn_mull mulrA.
Qed.

(* The Berstein coefficients of polyniomal l for the interval (a, b) *)

Definition Bernstein_coeffs (l: {poly Q})(a b : Q) : {poly Q} :=
  translate_pol (reciprocate_pol (expand (translate_pol l a) (b - a))) 1.

End PolsOnAbstractRationals.
