From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint rat polyrcf.
From mathcomp Require Import polyorder polydiv.

(** * Descartes. 
   polynomials link with the ssr library *)
(*
Copyright INRIA (20112012) Marelle Team (Jose Grimm;  Yves Bertot; Assia Mahboubi).
$Id: pol.v,v 1.35 2012/12/14 11:59:35 grimm Exp $
*)


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A technical binomial identity for the proof of de Casteljau *)

Lemma binom_exchange j k q :
  'C(j + k + q, j + k) * 'C(j + k, j) = 'C(k + q, k) * 'C(j + k + q, j).
Proof.
have bin_fact1: forall n m,  'C(n+m,m) * (m`! * n`!) = (n+m)`!.
  by move => n m; move: (bin_fact (leq_addl n m)); rewrite addnK.
move: (bin_fact1 (k+q) j) (bin_fact1 q (j+k)).
rewrite (mulnC j`!) (addnC k)(addnC j)  - (bin_fact1 q k) - (bin_fact1 k j).
rewrite (mulnAC _ _ j`!) !mulnA - (addnA q) (addnC q) => <-.
move /eqP; rewrite !eqn_pmul2r ? fact_gt0 //;move /eqP ->; apply: mulnC.
Qed.

Lemma util_C (n i j : nat) : (i <= j) -> (j <= n) ->
  ('C(n-i, j-i) * 'C(n, i) = 'C(n, j) * 'C(j, i)).
Proof.
move => ij jn.
move: (binom_exchange i (j - i) (n - j)).
by rewrite (subnKC ij)(subnKC jn) (addnC (j-i)) (addnBA _ ij)  (subnK jn).
Qed.

Import Order.Theory.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

(** ** Properties of ordered fields  *)

Section MoreRealField.

(** True on characteristic zero *)

Lemma size_deriv (R:numDomainType) (p: {poly R}): size p^`() = (size p).-1.
Proof.
have [lep1|lt1p] := leqP (size p) 1.
  by rewrite {1}[p]size1_polyC // derivC size_poly0 -subn1 (eqnP lep1).
rewrite size_poly_eq // mulrn_eq0 -subn2 -subSn // subn2.
by rewrite lead_coef_eq0 -size_poly_eq0 -(subnKC lt1p).
Qed.

Variable R : realFieldType.
Implicit Types (x y : R).

Definition half x := (x / 2%:R).

Lemma two_unit: (2%:R \is a @GRing.unit R).
Proof. by rewrite unitfE// pnatr_eq0. Qed.

Lemma half_gt0 x : 0 < x -> 0 < half x.
Proof.  by move=> lta; rewrite mulr_gt0 // invr_gt0 ltr0n. Qed.

Lemma half_ltx x: 0 < x -> half x < x.
Proof.
by move=>lta; rewrite ltr_pdivr_mulr ?ltr0n // mulr_natr mulr2n ltr_addr.
Qed.

Lemma double_half x : half x + half x = x.
Proof.
by rewrite /half -splitr.
Qed.

Lemma half_inj (x y : R) : half x = half y -> x = y.
Proof. by move => eq; rewrite - (double_half x) - (double_half y) eq. Qed.

Lemma half_lin (x y : R) : (half x) + (half y) = half (x + y).
Proof. by rewrite /half mulrDl. Qed.

Lemma half_lin1 (x y : R) : (half x) - (half y) = half (x - y).
Proof. by rewrite /half mulrBl. Qed.

Lemma mid_between (a b: R): a < b -> a < half (a + b) < b.
Proof.
move => h. rewrite - half_lin - {1} (double_half a) - {3} (double_half b).
by rewrite  ltr_add2l  ltr_add2r ltr_pmul2r ?h //invr_gt0 ltr0n.
Qed.

Lemma maxS (x y: R) (z := (Num.max x y) +1) : (x<z) && (y <z).
Proof.
have p1 : forall u v:R, u <= v -> u < v + 1.
       by move=> u v  h; rewrite (le_lt_trans h) // ltr_addl ltr01.
by rewrite !p1// ?le_maxr// lexx // orbT.
Qed.

Lemma pmul2w1 (a b c d : R) : 0 <= a -> 0 <= d -> a <= b -> c <= d ->
   a * c <= b * d.
Proof.
move => a0 d0 ab cd.
apply: (le_trans (ler_wpmul2l a0 cd)).
by apply: (le_trans (ler_wpmul2r d0 ab)).
Qed.

Lemma inv_comp x y:  0 < x -> 0 < y -> (x < y^-1) = (y < x^-1).
Proof.
move=> xp yp.
rewrite -(ltr_pmul2r yp) - [y < _](ltr_pmul2l xp).
by rewrite mulVf ?(gt_eqF yp) //  mulfV // (gt_eqF xp).
Qed.

Lemma inv_compr x y: 0 < x -> 0 < y -> (y^-1 < x) = (x^-1 < y).
Proof.
move=> xp yp.
rewrite -(ltr_pmul2r yp) - [_ < y](ltr_pmul2l xp).
by rewrite mulVf ?(gt_eqF yp) //  mulfV // (gt_eqF xp).
Qed.

End MoreRealField.

(** ** Big Max on ordered structures *)

Notation "\max_ ( i <- r | P ) F" :=
  (\big[Num.max/0%R]_(i <- r | P%B) F%R) : ring_scope.

Notation "\max_ ( i <- r ) F" :=
  (\big[Num.max/0%R]_(i <- r) F%R) : ring_scope.
Notation "\max_ ( i < n ) F" :=
 (\big[Num.max/0%R]_(i < n) F%R) : ring_scope.

(* NB: ce n'est pas des choses qu'on a dans mathcomp-analysis? *)
Section BigMax.
Variable R : realDomainType.

Implicit Types (F: R -> R) (s: seq R) (f g : nat -> R).

Lemma bigmaxr_ge0 s F: 0 <= \max_(i <- s) F i.
Proof.
elim: s; first by rewrite big_nil.
by move=> s IHs  Hri0; rewrite big_cons le_maxr Hri0 orbT.
Qed.

Lemma bigmaxr_le s F j:
  j \in s -> F j <= \max_(i <- s) F i.
Proof.
elim: s; first by rewrite in_nil.
move=> i s IHs Hri0; rewrite big_cons.
case Hi: (j == i); first  by rewrite (eqP Hi) le_maxr lexx.
move: Hri0; rewrite in_cons Hi orFb => ins.
by  apply: le_trans (IHs ins) _; rewrite le_maxr lexx orbT.
Qed.

Lemma bigmaxr_le0 s F:
  \max_(i <- s) F i <= 0 -> forall i, i \in s -> F i <= 0.
Proof.
elim: s; first by move=> _ i;rewrite in_nil.
move=> k s IHs; rewrite big_cons le_maxl; case /andP => Fk Hr1 i.
rewrite in_cons; case /orP; [ move /eqP ->; apply: Fk | by apply: IHs].
Qed.


Lemma bigmaxr_gt0 s F:
  \max_(i <- s) F i > 0 -> { i | i \in s & F i > 0}.
Proof.
elim :s => [| a l Hrec]; first by rewrite big_nil ltxx.
rewrite big_cons lt_maxr.
case  (ltrP 0 (F a)); first by exists a => //; rewrite in_cons eqxx.
rewrite leNgt => /negbTE ->; rewrite orFb => /Hrec [b bl fp0].
by exists b => //;rewrite in_cons bl orbT.
Qed.

Lemma bigmaxr_arg  s F:
  {j | j \in s & 0 <=  F j} -> {j | j \in s & \max_(i <- s) F i = F j}.
Proof.
elim:s; first by case => w ;rewrite in_nil.
move => a l Hrec ew; rewrite big_cons.
case (lerP (\max_(i <- l) F i)  (F a)) => cmpm.
  by exists a; [ rewrite in_cons eqxx | apply /eqP; rewrite eq_maxl].
move: (ltW cmpm); rewrite - eq_maxr; move /eqP => ->.
suff aux: { w : R | w \in l & 0 <= F w}.
 move: (Hrec aux) => [j jl jm]; exists j =>//;  rewrite in_cons jl orbT//.
move: ew => [w]; rewrite in_cons => h1 h2.
case e: (w == a); last first.
  exists w  => //; move: h1; case /orP => //; rewrite e //.
rewrite (eqP e) in h2; move: (le_lt_trans h2 cmpm) => aux.
by move: (bigmaxr_gt0 aux) =>[j ja jb]; exists j =>//; apply: ltW.
Qed.

Lemma bigmaxr_lerP s F m:
  m >= 0 -> reflect (forall i, i \in s -> F i <= m) (\max_(i <- s) F i <= m).
Proof.
move=> h; apply: (iffP idP) => leFm => [i ir | ].
  by apply: le_trans leFm; apply: bigmaxr_le.
rewrite big_seq_cond; elim /big_ind:_ => //.
  by  move=> x y xm ym; rewrite le_maxl; apply /andP.
by  move=> i; rewrite andbT; apply: leFm.
Qed.

Lemma bigmaxr_arg1 s F j:
  j \in s -> 0 <= F j -> (forall i, i \in s -> F i <= F j)  ->
  \max_(i <- s) F i  = F j.
Proof.
move => js fjp; move / (bigmaxr_lerP s F fjp) => le1.
by apply /eqP; rewrite eq_le le1  (bigmaxr_le _ js).
Qed.

Lemma bigmaxf_nil f: \max_(i< 0) (f i) = 0.
Proof.  by rewrite big_ord0.  Qed.

Lemma bigmaxf_rec f n :
   \max_(i < n.+1) f i = Num.max (f n) (\max_(i < n) f i).
Proof.
move: f.
elim: n => [ f /=|s Hrec f]; first by rewrite  big_ord_recl big_ord0 big_ord0.
symmetry; rewrite  big_ord_recl maxCA big_ord_recl.
pose g i := f i.+1.
have aux: forall k, \max_(i < k) f (lift ord0 i) = (\max_(i < k) g i).
  move=> k; apply: eq_big => // i.
by rewrite aux aux Hrec.
Qed.

Lemma bigmaxf_ge0  f n: 0 <= \max_(i < n) f i.
Proof.
elim: n => [| n IHn]; first by rewrite big_ord0.
by rewrite bigmaxf_rec le_maxr IHn orbT.
Qed.

Lemma bigmaxf_le f n j: (j < n)%N -> f j <= \max_(i < n) f i.
Proof.
elim: n => [ //| n IHn]; rewrite bigmaxf_rec.
case Hi: (j == n); first  by rewrite (eqP Hi) le_maxr lexx.
rewrite ltnS leq_eqVlt Hi orFb => aux;apply: (le_trans (IHn aux)).
by rewrite le_maxr lexx orbT.
Qed.

Lemma bigmaxf_le0 f n: \max_(i < n) f i <= 0 ->
   forall i, (i <n)%N -> f i <= 0.
Proof.
elim: n => [_ i //| n Hr]; rewrite bigmaxf_rec le_maxl; case /andP => Fk H i.
rewrite ltnS leq_eqVlt; case /orP; [ move /eqP ->; apply: Fk | by apply: Hr].
Qed.

Lemma bigmaxf_gt0 f n:  \max_(i < n ) f i > 0 -> { i | (i <n)%N  & f i > 0}.
Proof.
elim :n => [| a IH]; first by rewrite big_ord0 ltxx.
case  (ltrP 0 (f a)); first by exists a.
rewrite bigmaxf_rec lt_maxr leNgt; move /negbTE => ->; rewrite orFb => aux.
by move: (IH aux) => [b bl fp0]; exists b => //; apply:ltn_trans (ltnSn a).
Qed.

Lemma bigmaxf_arg f n :
  {j | (j  <n)%N & 0 <=  f j} -> {j | (j <n)%N & \max_(i < n) f i = f j}.
Proof.
elim:n => [ [j] // | n Hr Hf]; rewrite bigmaxf_rec.
case (lerP (\max_(i < n) f i)  (f n)) => cmpm.
  by exists n => //;  apply /eqP;  rewrite  eqr_maxl.
move: (ltW cmpm); rewrite - eq_maxr/=; move /eqP => <-.
suff aux: { j | (j < n)%N & 0 <= f j}.
  move: (Hr aux) => [j jl jm]; exists j.
    by rewrite ltnS ltnW.
  rewrite /Num.max/= jm; case: ifPn => //.
  by rewrite -jm cmpm.
move: Hf => [j]; rewrite ltnS leq_eqVlt.
case e: (j == n); last by rewrite orFb; exists j  => //.
rewrite (eqP e) => _ h2; move: (le_lt_trans h2 cmpm) => aux.
by move: (bigmaxf_gt0 aux) =>[k ja jb]; exists k =>//; apply: ltW.
Qed.

Lemma bigmaxf_lerP f n m:
  m >= 0 -> reflect (forall i, (i < n)%N -> f i <= m) (\max_(i <n) f i <= m).
Proof.
move=> h; apply: (iffP idP) => leFm => [i ir | ].
  by apply: le_trans leFm; apply: bigmaxf_le.
rewrite big_seq_cond; elim /big_ind:_ => //.
  by  move=> x y xm ym; rewrite le_maxl; apply /andP.
by move=> [i hi] _; apply: leFm.
Qed.

Lemma bigmaxf_arg1 f n j:
  (j < n)%N  -> 0 <= f j -> (forall i, (i < n)%N -> f i <= f j)  ->
  \max_(i < n) f i  = f j.
Proof.
move => js fjp; move / (bigmaxf_lerP f n fjp) => le1.
by apply /eqP; rewrite eq_le le1  (bigmaxf_le _ js).
Qed.

Lemma normr_sumprod  f g n :
  `| \sum_(i< n) (f i * g i) |
    <= (\max_(i< n)  `|f i|) * \sum_ (i<n) `| g i|.
Proof.
apply: le_trans (_: \sum_(i < n) `| f i * g i| <= _).
  apply: ler_norm_sum.
have ->:  \sum_(i < n) `|f i * g i|  =  \sum_(i < n) `|f i|  * `|g i|.
  by apply: eq_big => // i; rewrite normrM.
rewrite  mulr_sumr; apply: ler_sum => i _; apply: ler_wpmul2r.
  by rewrite normr_ge0.
by apply: (bigmaxf_le (fun i => `|f i|)).
Qed.

Lemma normr_sumprod1 f g n b:
  0 <= b -> (forall i, (i<n)%N ->  `|f i| <= b) ->
  `| \sum_(i< n) (f i * g i) |  <= b * \sum_ (i<n) `| g i|.
Proof.
move=> b0 h; apply: (le_trans (normr_sumprod f g n)).
apply: ler_wpmul2r;  first by rewrite sumr_ge0 // => i _; rewrite absr_ge0.
exact /(bigmaxf_lerP (fun z => `|f z|)  n b0).
Qed.

End BigMax.

(** ** bigops *)

Section BigOps.
Variables (R : comRingType) (idx : R) (op : Monoid.com_law idx).

Lemma big_ord_rev (n : nat) (P : nat -> bool) (F : nat -> R):
  \big[op/idx]_(i < n | P i) F i =
  \big[op/idx]_(i < n | P (n - i.+1)%N) F ( n - i.+1)%N.
Proof. by rewrite -big_mkord big_rev_mkord subn0. Qed.

Lemma bigop_simpl1  (n m : nat) (F : nat -> R):
   (forall j, (m <= j)%N -> F j = idx) ->
   \big[op/idx]_(j < n) F j = \big[op/idx]_(j < m | (j < n)%N) F j.
Proof.
set s :=  (n + m)%N => h.
rewrite (big_ord_widen s F (leq_addr m n)).
rewrite (big_ord_widen_cond s (fun j => (j < n)%N) F (leq_addl n m)).
rewrite (bigID (fun i0:ordinal s => (i0 < m)%N) _ F) /=.
rewrite [X in op _ X] big1 ? Monoid.mulm1 //.
by move => j; rewrite  -leqNgt; case/andP => _; by apply: h.
Qed.

Lemma shorten_sum (f: nat -> R) (n m : nat):
    (n <= m)%N -> (forall i, (n <= i < m)%N -> f i = idx) ->
  \big[op/idx]_(i < m) f i = \big[op/idx]_(i < n) f i.
Proof.
move => nm fz.
rewrite - (big_mkord xpredT) (big_cat_nat _ _ _ (leq0n n) nm) /= big_mkord.
rewrite  [X in (op _  X)]big1_seq ? Monoid.mulm1 // => i; case /andP => _.
by rewrite mem_index_iota; apply: fz.
Qed.

Lemma big_ord1 (F: 'I_1 -> R) : \big[op/idx]_(i < 1) (F i) = F ord0.
Proof. by rewrite big_ord_recl big_ord0 Monoid.mulm1. Qed.

End BigOps.

Section  RingPoly.
Variable R : ringType.

Lemma polyd0 (F: nat -> R): \poly_(i < 0) (F i) = 0.
Proof.
apply /eqP;rewrite - size_poly_eq0; rewrite - leqn0; exact: (size_poly 0 F).
Qed.

Lemma sum_powers_of_x (n: nat) (x:R):
  (x-1) * (\sum_(i < n) x^+ i) = x ^+ n - 1.
Proof.
elim: n => [| n Ihn].
  by rewrite big_ord0 expr0 mulr0 subrr.
rewrite  (big_ord_recr n) /= mulrDr Ihn  mulrBl mul1r - exprS.
by rewrite addrAC addrCA subrr addr0.
Qed.

Lemma power_monom (c:R) n :
  ('X + c%:P) ^+ n = \poly_(i< n.+1) (c^+(n - i)%N *+ 'C(n, i)).
Proof.
rewrite addrC exprDn_comm; last by apply:  commr_polyX.
rewrite poly_def; apply: eq_big => // [[i lin]] _ /=.
by rewrite - mul_polyC - polyC_exp polyCMn mulrnAl.
Qed.

End RingPoly.

(** ** Shift and scale *)

Definition shift_poly  (R:ringType) (c:R)(p: {poly R}) :=  p \Po ('X + c%:P).
Definition scaleX_poly (R:ringType) (c:R)(p: {poly R}) :=  p \Po ('X * c%:P).

Notation "p \shift c" := (shift_poly c p) (at level 50) : ring_scope.
Notation "p \scale c" := (scaleX_poly c p) (at level 50) : ring_scope.

Section ComPoly.
Variable R : comRingType.
Implicit Types (p : {poly R}) (c : R).

Lemma poly_comp_exp (p r: {poly R}) i:
  (p ^+i) \Po r = (p \Po r) ^+ i.
Proof.
elim: i => [| i ihi]; first by rewrite !expr0 comp_polyC.
by rewrite !exprS  comp_polyM ihi. 
Qed.

Lemma shift_polyD1 (c1 c2 : R): 
  ('X + c1%:P) \shift c2 = ('X + (c2 + c1)%:P). 
Proof. 
by rewrite /shift_poly comp_polyD comp_polyX comp_polyC polyCD addrA. 
Qed.

Lemma shift_polyB1 (c1 c2 : R): 
  (c1%:P - 'X) \shift c2 = (c1 - c2)%:P -'X. 
Proof.
rewrite /shift_poly comp_polyB comp_polyC comp_polyX opprD.
by rewrite - addrCA addrC polyCB.
Qed.

Lemma shift_polyE c p: 
  p \shift c = 
  \poly_(i < size p) \sum_(k < size p) p`_k * c ^+ (k - i) *+ 'C(k, i).
Proof.
rewrite /shift_poly comp_polyE poly_def; symmetry.
transitivity (\sum_(i < size p)
   \sum_(k < size p) ((p`_k)%:P * (c ^+ (k - i) *+ 'C(k, i) *: 'X^i))).
  apply: eq_big => // [[i ip]] _ /=; rewrite - mul_polyC.
  rewrite rmorph_sum big_distrl;  apply: eq_big => // [[k kp]] _ /=. 
  rewrite -  mulrnAr polyCM -mul_polyC mulrA //.   
rewrite exchange_big; apply: eq_big => // [[i ip]] _ /=.
rewrite  -big_distrr - mul_polyC; congr (_ * _).
rewrite power_monom poly_def /=. 
have aux: forall j, (i < j < size p)%N ->(c ^+ (i - j) *+ 'C(i, j)) *: 'X^j = 0.
  move=> j; case /andP => ij js; rewrite bin_small ?mulr0n ? scale0r//. 
by rewrite (shorten_sum _ ip aux).
Qed.

Lemma horner_shift_poly c p x: (p \shift c).[x] = p.[x + c].
Proof. by  rewrite horner_comp !hornerE. Qed.

Lemma horner_shift_poly1 c p x : p.[x] = (p \shift c).[x - c].
Proof. by rewrite horner_shift_poly addrNK. Qed.

Lemma shift_polyC c a: a%:P \shift c = a%:P.
Proof. by rewrite /shift_poly comp_polyC. Qed.

Lemma shift_poly_is_linear c: linear (shift_poly c).
Proof. by move=> a u v; rewrite /shift_poly comp_polyD comp_polyZ. Qed.

Lemma shift_poly_multiplicative c: multiplicative (shift_poly c).
Proof.   
split. move=> x y; exact: comp_polyM. by rewrite /shift_poly comp_polyC.
Qed.

(*HB.instance Definition _ c := GRing.isLinear.Build _ _ _ _ _ (shift_poly_is_linear c).

Canonical shift_poly_additive c := Additive (shift_poly_is_linear c).
Canonical shift_poly_linear c := Linear (shift_poly_is_linear c).
Canonical shift_poly_rmorphism c := AddRMorphism (shift_poly_multiplicative c).*)

Lemma shift_polyD  c1 c2 p:
  p \shift (c2 + c1) = (p\shift c1) \shift c2.
Proof. by rewrite /shift_poly - comp_polyA - shift_polyD1. Qed.

Lemma shift_poly_scal a b p :
  (a%:P * p) \shift b = a%:P * (p \shift b).
Proof. by rewrite shift_poly_multiplicative  shift_polyC. Qed.

Lemma shift_polyDK c p:
   p \shift c \shift -c = p.
Proof.
by rewrite - shift_polyD addrC subrr /shift_poly addr0 comp_polyXr.
Qed.

Lemma shift_polyX c p i:
  ((p^+i) \shift c) =  (p \shift c) ^+i.
Proof. by rewrite /shift_poly - poly_comp_exp. Qed.

Lemma shift_polyXn c i:
  ('X^i \shift c) = ('X + c%:P)^+i.
Proof. by rewrite (shift_polyX c 'X i) /shift_poly comp_polyX. Qed.


Lemma shift_poly_nth p i c: (i < size p)%N ->
  (shift_poly c p)`_i =
  \sum_(k < size p) p`_k * c^+(k - i) *+ 'C(k, i).
Proof.  by move=> ltis; rewrite shift_polyE coef_poly ltis. Qed.

Lemma shift_poly_nth1 c p i m: (size p <= m)%N ->
  (shift_poly c p)`_i =
  \sum_(k < m) p`_k * c^+(k - i) *+ 'C(k, i).
Proof.
move=> ltpm; rewrite shift_polyE coef_poly.
case sip: (i < size p)%N; last first.
  rewrite big1 => // [[j jm]]  _ /=; case (leqP i j) => ij.
    move: sip; case (ltnP i (size p)) => // sip1 _.
    by move: (leq_trans sip1 ij)  => /(nth_default 0) ->; rewrite mul0r mul0rn.
  rewrite bin_small //.
have aux: forall k, (size p <= k < m)%N ->p`_k * c ^+ (k - i) *+ 'C(k, i) = 0.
  move=> k; case /andP => ij js; move: ij  => /(nth_default 0) ->.
  by rewrite mul0r mul0rn.
symmetry;apply: (shorten_sum _ ltpm aux).
Qed.

(* We give here the coefficients of scale and shift *)
Lemma scaleX_polyE c p:
 p \scale c = \poly_(i < size p)(p`_i * c ^+i).
Proof.
rewrite /scaleX_poly comp_polyE poly_def; apply: eq_bigr => i _.
by rewrite -scalerA - exprZn - (mul_polyC c) commr_polyX.
Qed.

Lemma horner_scaleX_poly c p x :  (p \scale c).[x] = p.[c * x].
Proof. by rewrite horner_comp ! hornerE  mulrC. Qed.

End ComPoly.

(** ** Reciprocal *)

Definition reciprocal_pol (R:ringType) (p: {poly R}):=
    \poly_(i < size p) p`_(size p - i.+1).

(* The Bernstein coefficients of polynomial l for the interval (a, b) *)

Definition recip (R : ringType) (deg : nat) (q : {poly R}) : {poly R} :=
  'X ^+ (deg.+1 - size q) * reciprocal_pol q.

Definition Mobius (R:ringType) (deg : nat) (a b : R) (p: {poly R}) : {poly R} :=
  recip deg ((p \shift a) \scale (b - a)) \shift 1.

Lemma reciprocal_Xn (R : idomainType) n : reciprocal_pol ('X^n) = (GRing.one R)%:P.
Proof.
rewrite /reciprocal_pol size_polyXn poly_def big_ord_recl.
rewrite subSS subn0 coefXn expr0 eqxx scale1r big1 ?addr0 // => i _.
rewrite lift0 subSS coefXn /=.
have /negbTE -> : (n - i.+1)%N != n.
  by rewrite neq_ltn -(ltn_add2r i.+1) subnK// -addSnnS ltn_addr.
by rewrite -mul_polyC mul0r.
Qed.

Section ReciprocalPoly.

Variable (R : idomainType).
Implicit Type p : {poly R}.

Lemma size_scaleX c p : c != 0 -> size (p \scale c) = size p.
Proof. by move=> cu; rewrite size_comp_poly2 // size_XmulC. Qed.

Lemma reciprocal_size p: p`_0 != 0 -> size (reciprocal_pol p) = size p.
Proof.
rewrite /reciprocal_pol => td0.
apply: size_poly_eq; rewrite prednK ?subnn // size_poly_gt0.
by  apply /eqP => pz; case /eqP:td0; rewrite pz  coefC.
Qed.

Lemma reciprocal_idempotent p: p`_0 != 0 ->
  reciprocal_pol (reciprocal_pol p) = p.
Proof.
move=> h;rewrite - polyP {1}/reciprocal_pol (reciprocal_size h) => i.
rewrite coef_poly /reciprocal_pol coef_poly.
case: (ltnP i (size p)); last by move => /(nth_default 0).
move => isp; rewrite - (subnKC isp).
by rewrite  -subn_gt0 addSn addnC -addnS addnK addKn addnS addnC -addnS addnK.
Qed.

Lemma size_poly_coef_eq0 :
  forall p q : {poly R}, (forall i, (p`_i == 0) = (q`_i == 0)) ->
  size p = size q.
Proof.
by move=> p q c; apply/eqP; rewrite eqn_leq;apply/andP; split;
  apply/leq_sizeP => j cj; apply/eqP; (rewrite c || rewrite -c);
  apply/eqP; move: j cj; apply/leq_sizeP.
Qed.

(*
Lemma reciprocal_pol_scale_swap :
  forall p (c : R), c!= 0 -> p`_0 != 0 ->
  reciprocal_pol (p \scale c) = (c ^ (size p).-1)%:P
                * (reciprocal_pol p \scale c^-1).
Proof.
(* Without the condition on the first coefficient.
move=> p c cu (* p0 *); rewrite [_ \scale c^-1]/scaleX_poly comp_polyE.
rewrite [_ (_ \scale _)]/reciprocal_pol poly_def size_scaleX //.
have t : (size (reciprocal_pol p) <= size p)%N by apply: size_poly.
rewrite (big_ord_widen _
           (fun i : nat => (reciprocal_pol p)`_i *: ('X * (c^-1)%:P) ^+ i) t).
rewrite (big_mkcond (fun i : 'I_(size p) => (i < _)%N)) big_distrr /=.
apply: eq_bigr; move => [i ci] _ /=.
Search _ nth (_ \scale _).
rewrite scaleX_polyE coef_poly.
have -> : (size p - i.+1 < size p)%N.
  move: ci; case h : (size p) => [ | n]; first by rewrite ltn0.
  by move=> _; rewrite subSS (leq_ltn_trans _ (ltnSn _)) // leq_subr.
case t' : (i < size (reciprocal_pol p))%N; last first.
*)
rewrite reciprocal_size /reciprocal_pol // size_scaleX // poly_def.
rewrite big_distrr; apply eq_bigr => i _.
rewrite exprMn_comm; last by apply: mulrC. 
rewrite coef_poly ltn_ord scaleX_polyE coef_poly /=.
have -> : (size p - i.+1 < size p)%N.
  case h' : (size p) i => [ | n] i' //; first by case i'.
  by rewrite (leq_ltn_trans _ (ltnSn n)) // subSS // leq_subr.
rewrite -polyC_exp (mulrC 'X^i) !mul_polyC !scalerA; congr (_ *: _).
rewrite mulrAC exprVn -exprnP mulrC; congr (_ * _).
case: i => i ci /=.
case h : (size p == i.+1).
  by rewrite (eqP h) subnn expr0 /= mulfV // expf_eq0 (negbTE cu) andbF.
case: (size p) ci h => //= n in1 dif; rewrite subSS expfB //.
by move: in1; rewrite leq_eqVlt eq_sym dif orFb ltnS.
Qed.
*)

Lemma horner_reciprocal p x :
  x \is a GRing.unit -> (reciprocal_pol p).[x] = x ^+ (size p - 1) * p.[x^-1].
Proof.
move=> xn0; rewrite /reciprocal_pol horner_poly.
case sp : (size p) => [| n].
  rewrite sub0n expr0 mul1r big_ord0; move/eqP: sp; rewrite size_poly_eq0.
  by move/eqP->; rewrite horner0.
rewrite horner_coef subn1 /=  big_distrr /=.
pose  f (j : 'I_n.+1) := Ordinal (leq_subr j n:n - j < n.+1)%N.
have finv: forall j:'I_n.+1, xpredT j -> f (f j) = j.
  by  move => j _; apply: val_inj => /=; rewrite subKn //; have : (j < n.+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp) {tmp} sp; apply: eq_bigr => [[j hj]] _ /=.
rewrite subSS subKn // -mulrCA; congr (_ * _).
rewrite ltnS in hj; rewrite - {2}(subnK hj) exprD -mulrA exprVn.
by rewrite divrr ? mulr1 // unitrX.
Qed.

Lemma horner_reciprocal1 p x :
  x \is a GRing.unit -> p.[x] = x ^+ (size p - 1) * (reciprocal_pol p).[x^-1].
Proof.
move=> xz; rewrite horner_reciprocal ?unitrV //.
by rewrite mulrA invrK - exprMn divrr // expr1n mul1r.
Qed.

Lemma reciprocal_monom (a b: R): a != 0 ->
  reciprocal_pol ('X * a%:P + b%:P) = ('X * b%:P + a%:P).
Proof.
move=> /negbTE h; rewrite /reciprocal_pol.
have ->: size ('X * a%:P + b%:P) = 2%N.
  by rewrite - commr_polyX size_MXaddC size_polyC polyC_eq0 h.
apply/polyP=> i.
rewrite coef_poly !coefD !coefMC !coefC !coefX.
case :i; first by rewrite mul1r mul0r add0r addr0.
case; first by  rewrite mul1r mul0r add0r addr0.
by move=> n /=; rewrite mul0r add0r.
Qed.

Lemma reciprocalC (c : R) : reciprocal_pol c%:P = c%:P.
Proof.
rewrite /reciprocal_pol  - polyP => i; rewrite coef_poly.
case cz: (c==0); first by move /eqP in cz; rewrite cz !coef0 if_same.
rewrite size_polyC cz !coefC; case:i => [| i]//.
Qed.

Lemma reciprocalM p q :
  reciprocal_pol (p * q) = reciprocal_pol p * reciprocal_pol q.
Proof.
move: (reciprocalC 0) => aux.
case (poly0Vpos p); first by move => ->; rewrite mul0r aux mul0r.
case (poly0Vpos q); first by move => -> _; rewrite mulr0 aux mulr0.
set m:=  (size p + size q).-1; move=> pa pb.
have mp: (size p + size q)%N = m .+1.
  by symmetry;rewrite  /m prednK // addn_gt0 pa pb.
have qa: (size p <= m)%N by rewrite /m - (prednK pa) addnS leq_addr.
have qb: (size q <= m)%N by rewrite /m addnC - (prednK pb) addnS leq_addr.
have pnz: p != 0 by  rewrite - size_poly_eq0 - lt0n.
have qnz: q != 0 by  rewrite - size_poly_eq0 - lt0n.
rewrite /reciprocal_pol size_mul //.
rewrite - polyP => i; rewrite coef_poly coefM coefM.
case: (ltnP i  (size p + size q).-1) => ipq; last first.
  rewrite big1 // => [] [] j ij _ /=; rewrite ! coef_poly.
  case lt1: (j < size p)%N; last by rewrite mul0r.
  case lt2: (i - j < size q)%N; last by rewrite mulr0.
  move: (leq_add lt1 lt2).
  by rewrite addnS addSn mp ltnS subnKC ? ltnS // ltnNge ipq.
set mi:= ((size p + size q).-1 - i.+1)%N.
pose f j :=  (p`_j * q`_(mi - j)).
have aux1: forall j,  (size p <=j) %N -> f j = 0.
  by move=> j; rewrite /f; move => /(nth_default 0) => ->; rewrite mul0r.
rewrite (bigop_simpl1 _  mi.+1 aux1).
pose g1 j := (\poly_(i0 < size p) p`_(size p - i0.+1))`_j.
pose g2 j := (\poly_(i0 < size q) q`_(size q - i0.+1))`_j.
pose g j := g1 j * g2 (i - j)%N.
have aux2: forall j : nat, (size p <= j)%N -> g j = 0.
  by move => j; rewrite /g/g1 coef_poly ltnNge;  move => ->; rewrite mul0r.
rewrite (bigop_simpl1 _ i.+1 aux2).
transitivity (\sum_(j < size p | (j < i.+1)%N)
   p`_(size p - j.+1) * g2 (i - j)%N); last first.
  by apply: eq_big => // [[j ji]] _ /=; rewrite /g/g1 coef_poly ji.
symmetry; rewrite (big_ord_rev _ (size p) (fun j => (j < i.+1)%N)
  (fun j =>  p`_(size p - j.+1) * g2 (i - j)%N)) /=.
rewrite big_mkcond [X in _ = X] big_mkcond; apply: eq_bigr => [[k kp]] _ /=.
case Ha: ((size p - k.+1) < i.+1)%N; last first.
  case Hb: (k < mi.+1)%N => //; rewrite /f.
  suff:(size q <= (mi - k))%N by move => /(nth_default 0) => ->; rewrite mulr0.
  rewrite ltnS in Hb; rewrite -(leq_add2l k) (subnKC Hb) -(leq_add2l i.+1).
  rewrite (subnKC ipq) addSn addnA -ltnS mp /= -mp -addSn -addSn leq_add2r.
  by rewrite -addnS -(subnK kp) -addSn leq_add2r ltnNge -ltnS Ha.
rewrite  (subnSK kp) (subKn (ltnW kp))  (subnBA _ kp) - addSnnS.
move: Ha; rewrite ltnS leq_subLR addSnnS addnC  => Ha.
have ->: (k < mi.+1)%N = (i.+1 + k <= m)%N.
  by rewrite /mi ltnS - (leq_add2l (i.+1)) (subnKC ipq) mp.
rewrite /g2 coef_poly; case Hb: (i.+1 + k <= m)%N; last first.
  suff: ~~(i.+1 + k - size p < size q)%N by move /negbTE => ->;rewrite mulr0.
  by rewrite -ltnNge ltnS - (leq_add2l (size p)) (subnKC Ha) mp ltnNge Hb.
rewrite /f - (ltn_add2l (size p)) (subnKC Ha) mp ltnS Hb; congr (_ * (q`_ _)).
apply /eqP; rewrite - (eqn_add2r (i.+1 + k)%N)- subnDA (subnK Hb).
have m1:  m = (size p + (size q).-1)%N by rewrite /m  -(ltn_predK pa) addnS.
rewrite addnC -(ltn_predK pa) subSS - {1} (subnK Ha) (addnC  _ (size p)).
by rewrite - addnA m1 subnKC // leq_subLR - m1.
Qed.

Lemma reciprocal_Xn_root0 (p : {poly R}) :
  reciprocal_pol p = reciprocal_pol (p %/ 'X^(\mu_0 p)).
Proof.
rewrite -(addr0 'X) -oppr0.
have Hmu0 := root_mu p 0.
rewrite Pdiv.IdomainMonic.dvdp_eq in Hmu0; last first.
  by rewrite monic_exp// monicXsubC.
by rewrite {1}(eqP Hmu0) reciprocalM {2}oppr0 addr0 reciprocal_Xn
    polyC1 mulr1 polyC0.
Qed.

Lemma reciprocalX p n : reciprocal_pol (p ^+ n) = (reciprocal_pol p) ^+ n.
Proof.
elim: n=> [| n Hrec]; first rewrite !expr0 reciprocalC //.
by rewrite ! exprS reciprocalM Hrec.
Qed.

Lemma pdivmu0_0th_neq0 (p : {poly R}) : p != 0 -> (p %/ 'X^(\mu_0 p))`_0 != 0.
Proof.
move=> Hp.
have H0noroot : ~~(root (p %/ 'X^(\mu_0 p)) 0).
  rewrite -mu_gt0.
    rewrite -eqn0Ngt -(addr0 'X) -(@oppr0 {poly R}) -polyC0 mu_div
      ?subn_eq0; by rewrite leqnn.
  rewrite Pdiv.CommonIdomain.divp_eq0 negb_or Hp /= negb_or.
  rewrite -size_poly_gt0 {1}size_polyXn /= -leqNgt dvdp_leq //.
  by rewrite -(addr0 'X) -oppr0 -polyC0 root_mu.
rewrite -horner_coef0. apply: negbT.
by move/rootPf : H0noroot.
Qed.

Lemma reciprocal_reciprocal (p : {poly R}) :
  reciprocal_pol (reciprocal_pol p) = p %/ ('X^(\mu_0 p)).
Proof.
case Hp0 : (p == 0).
  move/eqP : Hp0 => ->.
  by rewrite !reciprocalC div0p polyC0.
rewrite (@reciprocal_Xn_root0 p) reciprocal_idempotent //.
apply: pdivmu0_0th_neq0.
by apply: negbT.
Qed.

Lemma reciprocal0 (p : {poly R}) : (reciprocal_pol p == 0) = (p == 0).
Proof.
apply/idP/idP => Hp.
  have H : (p %/ ('X^(\mu_0 p)) == 0).
    by rewrite -reciprocal_reciprocal -polyC0 -reciprocalC (eqP Hp).
  rewrite Pdiv.CommonIdomain.divp_eq0 in H.
  move/orP : H; case => [| /orP [] H] //.
    by rewrite -size_poly_eq0 size_polyXn -(Bool.negb_involutive (_.+1 == 0%N))
      -lt0n /= in H.
  have H2 := (root_mu p 0).
  case Hp0 : (p == 0) => //.
  rewrite gtNdvdp // in H2.
    by apply: negbT.
  by rewrite oppr0 addr0.
by rewrite (eqP Hp) -polyC0 reciprocalC.
Qed.

(*
Lemma reciprocal_nth : forall (p : {poly R}) k, (k < size p)%N ->
   (reciprocal_pol p)`_k = p`_((size p) - k.+1).
Proof.
move=> p k Hk.
by rewrite /reciprocal_pol coef_poly Hk.
Qed.
*)

Lemma reciprocal_nth_2 (p : {poly R}) k : (k < size p)%N ->
  (reciprocal_pol p)`_(size p - k.+1) = p`_k.
Proof.
move=> Hk.
rewrite /reciprocal_pol coef_poly.
have Hk2 : (size p - k.+1 < size p)%N.
  by rewrite -(ltn_add2r k.+1) subnK // -addSnnS ltn_addr.
rewrite Hk2 !subnS -!subn1 !subnBA; last by rewrite subn_gt0.
  by rewrite addn1 -subnDA addn1 addnC addnK.
exact: ltnW.
Qed.

Lemma reciprocal_eq (p q : {poly R}) : p`_0 != 0 -> q`_0 != 0 ->
  (p == q) = (reciprocal_pol p == reciprocal_pol q).
Proof.
move=> p0 q0; apply/idP/idP => [/eqP ->//|/eqP pq].
apply/eqP/poly_inj.
have Hsize : size p = size q.
  by rewrite -reciprocal_size // -(@reciprocal_size q) // pq.
apply: (@eq_from_nth _ 0) => // i ip.
rewrite -reciprocal_nth_2// -(@reciprocal_nth_2 q) //.
  by rewrite pq Hsize.
by rewrite -Hsize.
Qed.

End ReciprocalPoly.

(** ** Cauchy bound *)

Section CauchyBound.

Variable F : realFieldType.

Variables (n : nat) (E : nat -> F) (x : F).
Hypothesis pnz : E n != 0.
Hypothesis xr: root (\poly_(i < n.+1) E i) x.

Lemma CauchyBound_aux : x^+n = - \sum_(i < n) ((E i / E n) * x^+ i).
Proof.
move: xr; move /rootP => xr1.
have ->: \sum_(i < n) E i / E n * x ^+ i  = \sum_(i < n) (E i * x ^+ i / E n).
  by apply: eq_bigr => i _ ; rewrite mulrAC.
rewrite -(mulfK pnz (x ^+ n)); apply /eqP;  rewrite -addr_eq0 - mulr_suml.
rewrite  - mulrDl mulf_eq0  -{2} xr1; apply /orP; left.
by rewrite horner_poly (big_ord_recr n)  //= addrC mulrC.
Qed.


Lemma CauchyBound1 : `| x | <= 1 + \max_(i < n) (`|E i / E n|).
Proof.
move: (bigmaxf_ge0  (fun i => `|E i / E n|) n) => cp.
case: (lerP `|x| 1)=> cx1; first by rewrite ler_paddr //.
rewrite addrC -ler_subl_addr.
move: (normr_sumprod (fun i => E i / E n) (fun i =>  x ^+ i) n).
move: CauchyBound_aux => eq; move: (f_equal (fun z => `| z |) eq).
rewrite normrN; move => <-;
have ->:  \sum_(i < n) `|x ^+ i| =  (\sum_(i < n) `|x| ^+ i).
  by apply: eq_big => // i _; rewrite normrX.
move: cp.
case:n => [| m]; first by  rewrite  big_ord0 mulr0 expr0 normr1 ler10.
move: (sum_powers_of_x (m.+1) `|x|); set aux:= (\sum_(i < m.+1) _) => pa.
set c := \max_(i < m.+1) `|E i / E m.+1| => cp r1.
have a1p: 0 < `|x| - 1 by rewrite subr_gt0.
have r2 : c* aux <= c* ( (`|x| ^+ m.+1) /(`|x| - 1)).
  by rewrite  (ler_wpmul2l cp) // ler_pdivl_mulr // mulrC pa ger_addl lerN10.
move:  (le_trans r1 r2); rewrite mulrA  ler_pdivl_mulr // mulrC.
rewrite normrX ler_pmul2r //.
by apply:(lt_trans ltr01); rewrite exprn_egt1.
Qed.

Lemma CauchyBound2 : `| x | <= \sum_(i < n.+1) `|E i / E n|.
Proof.
case: (lerP `|x| 1)=> cx1.
  apply: (le_trans cx1).
  rewrite big_ord_recr /= divff // normr1 ler_addr.
  rewrite sumr_ge0 // => i _; rewrite  absr_ge0 //.
move: (CauchyBound_aux).
case e: n=> [| m].
  by rewrite expr0 big_ord0 oppr0; move /eqP; rewrite oner_eq0.
case x0 : (x == 0).
  by  move: cx1; rewrite (eqP x0) normr0 ltr10.
have xmn0 : (x^+m != 0) by rewrite expf_eq0 x0 andbF.
move => h1; have h2 :  x =  - \sum_(i < m.+1) ( x^-(m - i) *(E i / E m.+1)).
  apply: (mulIf xmn0); rewrite mulNr big_distrl /= -exprS h1; congr (- _).
  apply: congr_big; [by [] | by [] |] => [[i hi]] _ /=.
  have mi : m = (m - i + i)%N  by rewrite subnK //.
  by rewrite (mulrC (x ^-(m -i)) _) {4} mi exprD -!mulrA mulKf //
    expf_eq0 x0 andbF.
rewrite (f_equal (fun z => `| z |) h2) normrN.
apply: le_trans (_: (\sum_(i < m.+1) `|E i / E m.+1|) <= _); last first.
  by rewrite (big_ord_recr m.+1) /= ler_addl normr_ge0.
have pa:  (forall i, (i<m.+1)%N ->  `| x ^- (m - i) | <= 1).
  move => i lin.
  have pa: 0 < `|x ^+ (m - i)| by rewrite normr_gt0  expf_eq0 x0 andbF.
  rewrite normrV.
   rewrite invr_le1 //; last by apply: unitf_gt0.
   rewrite normrX; apply:exprn_ege1; exact (ltW cx1).
   by apply: unitrX; rewrite unitfE x0.
rewrite - [\sum_(i < m.+1) `|E i / E m.+1| ] mul1r.
exact :(normr_sumprod1 (fun i => E i / E m.+1) ler01 pa).
Qed.

Lemma CauchyBound : `| x | <= `|E n|^-1 * \sum_(i < n.+1) `|E i|.
Proof.
move: (CauchyBound2). rewrite  big_distrr /=.
have -> //: \sum_(i < n.+1) `|E i / E n| = \sum_(i < n.+1) (`|E n|^-1 * `|E i|).
by apply: eq_bigr => i _ ; rewrite normrM normrV ? unitfE // mulrC.
Qed.

End CauchyBound.

(** ** Continuity *)


Section PolsOnOrderedField.

Variable R : realFieldType.

Definition norm_pol (p : {poly R}) := map_poly (fun x => `|x|) p.

Lemma pow_monotone n (x y : R) : 0 <= x <= y ->  0 <= x ^+ n <= y ^+ n.
Proof.
move => /andP [xp xy].
by rewrite ler_expn2r// ?andbT ?exprn_ge0// nnegrE (le_trans _ xy).
Qed.

Lemma diff_xn_ub n (z x y: R): -z  <= x -> x <= y -> y <= z ->
     `| y ^+ n - x ^+ n| <=  (z^+(n.-1) *+ n) * (y - x).
Proof.
move => zx xy yz.
rewrite subrXX mulrC normrM [`|_ - _|]ger0_norm ?ler_wpmul2r // ?subr_ge0 //.
apply: (le_trans (ler_norm_sum _ _ _)).
rewrite - [n in _*+ n] card_ord  - sumr_const ler_sum // => [][i lin] _.
rewrite normrM !normrX.
have l1: 0<=`|x| <=z by rewrite normr_ge0 /= ler_norml zx /= (le_trans xy yz).
have l2: 0<=`|y| <=z by rewrite normr_ge0 /= ler_norml yz /= (le_trans zx xy).
have /andP [pa pb] := pow_monotone i l1.
have /andP [pc pd] := pow_monotone  (n.-1 - i)%N l2.
by move: (ler_pmul pc pa pd pb); rewrite - exprD subnK //; move: lin; case n.
Qed.

Lemma pol_lip p (z x y: R):  -z <= x -> x <= y -> y <= z ->
   `|(p.[y] - p.[x])| <= (norm_pol p^`()).[z] * (y - x).
Proof.
move => zx xy yz.
rewrite horner_poly !horner_coef - sumrB.
apply: (@le_trans _ _ (\sum_(i<size p) `|(p`_i * y ^+ i - p`_i * x ^+ i)|)).
  apply: ler_norm_sum.
set aux := (X in _ <= X).
have ->: aux =  ((\sum_(i<size p) `|p`_i| * (z^+(i.-1) *+ i)) * (y - x)).
  congr(_ * _); case (poly0Vpos  p).
    by move => ->; rewrite deriv0 size_poly0  !big_ord0.
  move => s1; rewrite - (prednK s1) size_deriv big_ord_recl mulr0n mulr0 add0r.
  apply: eq_bigr => i _; rewrite coef_deriv normrMn mulrnAl mulrnAr //.
rewrite big_distrl /= ler_sum // => i _;rewrite - mulrBr normrM  -mulrA.
apply: (ler_wpmul2l (normr_ge0 p`_i)); exact: (diff_xn_ub i zx xy yz).
Qed.

Lemma pol_ucont (p : {poly R}) a b (c := (norm_pol p^`()).[(Num.max (- a) b)]) :
   forall x y, a <= x -> x <= y -> y <= b -> `|p.[y] - p.[x]| <= c * (y - x).
Proof.
move => x y ax xy yb.
apply: pol_lip => //.
apply: (le_trans _ ax); by rewrite ler_oppl le_maxr lexx.
apply: (le_trans  yb); by rewrite  le_maxr lexx orbT.
Qed.

Lemma pol_cont (p : {poly R}) (x eps :R):  0 < eps ->
 { delta | 0 < delta & forall y,  `|(y - x)| < delta ->
    `|p.[y] - p.[x]| < eps }.
Proof.
move => ep.
move: (pol_ucont p (a:= x-1)(b:=x+1)); set c := _ .[_ ] => /= hc.
have pa: x-1 <= x by move: (ler_add2l x (-1) 0); rewrite addr0 lerN10.
have pb: x <= x+1 by move: (ler_add2l x 0 1); rewrite ler01 addr0.
have cp: 0<=c.
  move: (hc _ _ pa pb (lexx (x+1))).
  by rewrite  addrAC addrN add0r mulr1; apply: le_trans; rewrite normr_ge0.
exists (Num.min 1  (eps /(c+1))).
  rewrite lt_minr ltr01 /= divr_gt0 // ? ep //.
  by apply: (lt_le_trans ltr01); move: (ler_add2r 1 0 c); rewrite add0r cp.
move => y.
rewrite lt_minr; case /andP => xy1 xy2.
apply: (@le_lt_trans _ _ (c *  `|(y - x)|)); last first.
   move: cp; rewrite le0r; case /orP; first by move /eqP => ->; rewrite mul0r.
   move => cp.
   rewrite - (ltr_pmul2l cp) in xy2; apply: (lt_le_trans xy2).
   rewrite mulrCA  ger_pmulr //.
   have c1: c <= c + 1  by move: (ler_add2l c 0 1); rewrite ler01 addr0.
   have c1p := (lt_le_trans cp c1).
   by rewrite -(ler_pmul2r c1p) mulfVK ? (gt_eqF c1p) // mul1r.
move: (ltW xy1); rewrite ler_distl;case /andP => le1 le2.
case /orP: (le_total x y) => xy.
   move: (xy); rewrite - subr_ge0 => xy'.
   move: (hc _ _ pa xy le2).
   rewrite subr_ge0.
   rewrite -subr_ge0 in xy'.
   by rewrite (ger0_norm xy').
move: (xy); rewrite - subr_ge0 => xy'.
move: (hc _ _ le1 xy pb); rewrite distrC (distrC y x).
rewrite subr_ge0.
rewrite -subr_ge0 in xy'.
by rewrite (ger0_norm xy').
Qed.

End PolsOnOrderedField.

Section PolsOnArchiField.

(** ** Constructive Intermediate value Theorem *)

Variable R : archiFieldType.
(** We want to prove a simple and contructive approximation of the
 middle value theorem: if a polynomial is negative in a and positive in b,
 and a < b, then for any positive epsilon, there exists c and d, so that
 a <= c < d <= b, the polynomial is negative in c and positive in d,
 and the variation between c and d is less than epsilon.
 Note: we also add: the distance between c and d is small.
*)

Definition pol_next_approx (p : {poly R}) (ab : R * R) :=
  let: (a,b) := ab in let c :=half(a+b) in
    if (p.[a] * p.[c]  <= 0) then (a,c) else (c,b).

Fixpoint pol_approx (p : {poly R}) (ab : R * R) (n:nat) :=
  if n is m.+1 then  pol_next_approx p (pol_approx p ab m) else ab.

Definition pair_in_interval (a x y b : R) := [&& a <= x, x < y & y <= b].

Lemma pol_approx_prop (p : {poly R}) (a b: R) n:
  p.[a] < 0 -> 0 <= p.[b] -> a < b ->
  let:(u,v) := (pol_approx p (a,b) n) in
  [&& (v-u) == (b-a) / (2%:R ^+ n), pair_in_interval a u v b,
      p.[u] < 0 & 0 <= p.[v] ].
Proof.
move => pan pbp lab.
elim:n;first by rewrite /= expr0 divr1 eqxx /pair_in_interval pan pbp lab !lexx.
move => n /=; case (pol_approx p (a,b) n) => u v /and4P [/eqP d1 pi pun pvp].
have aux: half ((b - a) / 2%:R ^+ n) == (b - a) / 2%:R ^+ n.+1.
  by rewrite /half exprS -mulrA - invrM // ? unitrX ? two_unit.
rewrite /pol_next_approx /pair_in_interval;case /and3P: pi => [au uv vb].
case cp:(p.[u] * p.[half (u + v)] <= 0).
  case /andP: (mid_between uv) => [h1 h2].
  rewrite -{2}(double_half u) half_lin half_lin1 opprD.
  rewrite addrA {1} (addrC u) addrK d1 aux pun - (nmulr_rle0 _ pun) cp.
  by rewrite au h1 (ltW (lt_le_trans h2 vb)).
case /andP: (mid_between uv) => [h1 h2].
rewrite -{1}(double_half v) half_lin half_lin1 opprD - addrA (addrA _ (-u)).
rewrite (addrC _ (-u)) addrK d1 aux pvp h2 vb (ltW (le_lt_trans au h1)).
by rewrite -(nmulr_rgt0 _ pun) ltNge cp.
Qed.

Lemma constructive_ivt (p : {poly R}) (a b : R) (eps : R) :
  a < b -> p.[a] < 0 -> 0 <= p.[b] ->  0 < eps ->
    { xy |  let:(u,v):= xy in
      [&& pair_in_interval (- eps) (p.[u]) (p.[v]) eps,
          (pair_in_interval a u v b),
          (p.[u] < 0), (0 <= p.[v]) & (v - u) <= eps] }.
Proof.
move=> ab nla plb ep.
move: (pol_ucont p (a:=a) (b:= b)); set c1 := _ .[_ ] => /= pc.
set c := Num.max 1 c1.
have lc1: 1 <= c by rewrite le_maxr lexx.
have cpos:= (lt_le_trans ltr01 lc1).
set k := Num.bound ((b - a) * c / eps).
move: (upper_nthrootP(leqnn k)) => hh.
exists (pol_approx p (a, b) k); move: (pol_approx_prop k nla plb ab).
case:(pol_approx p (a, b) k) => u v /and4P [/eqP pa eq1 pun pvp].
case/and3P: (eq1) => [ha hb hc].
have c2p: 0 < v-u by rewrite subr_gt0.
have hh1: (v-u) * c < eps.
   rewrite pa;set x := (X in _ / X).
   have xp: 0 < x by rewrite exprn_gt0 // ltr0n.
   rewrite mulrAC  -(ltr_pmul2r xp) (mulrVK (unitf_gt0 xp)).
   move: hh.
   rewrite -/x.
   by rewrite ltr_pdivr_mulr// (mulrC _ x).
have hh2 : v-u < eps.
  by apply: le_lt_trans hh1; rewrite - {1} (mulr1 (v-u)) (ler_pmul2l c2p).
have dvp: p.[u] < p.[v] by apply (lt_le_trans  pun pvp).
have hh5: p.[v] - p.[u] <= eps.
  move: (pc _ _ ha (ltW hb) hc);rewrite gtr0_norm ? subr_gt0 // mulrC => hh4.
  apply:(le_trans _ (ltW hh1)); apply: (le_trans hh4).
  rewrite (ler_pmul2l c2p) le_maxr lexx orbT //.
rewrite eq1 /pair_in_interval pun pvp dvp  (ltW hh2) ler_oppl.
rewrite  (le_trans _ hh5) ?(le_trans _ hh5) //.
   by rewrite -{1} (addr0 p.[v]) ler_add2l oppr_ge0 ltW.
by rewrite -{1} (add0r (- p.[u])) ler_add2r.
Qed.

Lemma constructive_ivt_bis  (p : {poly R})(a b : R) (eps: R):
  a < b -> p.[a] < 0 -> 0 <= p.[b] ->  0 < eps ->
    { xy |
      (- eps <= p.[xy.1]) && (p.[xy.1] < 0) && (0 <= p.[xy.2]) &&
      (p.[xy.2] <= eps) && (a <= xy.1) && (xy.1 < xy.2) && (xy.2 <= b) }.
Proof.
move=> ab nla plb ep.
move:(constructive_ivt ab nla plb ep) => [xy etc].
exists xy.
set u := xy.1; set v := xy.2; move: etc.
have ->: xy = (u,v) by rewrite /u /v; case xy.
by case/and5P => [/and3P[-> _ ->] /and3P[-> -> ->] -> ->  _].
Qed.

Lemma constructive_ivt_ter  (p : {poly R})(a b : R) (eps: R):
  a < b -> p.[a] < 0 -> 0 <= p.[b]  ->  0 < eps ->
    { xy |
      (- eps <= p.[xy.1]) && (p.[xy.1] < 0) && (0 <= p.[xy.2]) &&
      (p.[xy.2] <= eps) && (a <= xy.1) && (xy.1 < xy.2) && (xy.2 <= b) }.
Proof.
move=> ab nla plb ep.
have ba' : 0 < b - a by rewrite -(addrN a) ltr_add2r.
have evalba : 0 < p.[b] - p.[a] by rewrite subr_gt0;  exact: lt_le_trans plb.
move: (pol_ucont p (a:=a) (b:= b)).
set c := _ .[_ ] => /= pc.
have cpos : 0 < c.
  rewrite - (ltr_pmul2r ba') mul0r.
  by apply: lt_le_trans (pc a b _ _ _) => //; rewrite ? ger0_norm // ltW.
have pdiv : (0 < (b - a) * c / eps) by rewrite ltr_pdivl_mulr // mul0r mulr_gt0.
move: (archi_boundP (ltW pdiv)); set n := Num.bound _ => qn.
have fact1 : (0 : R) < n%:R by exact: lt_trans qn => /=.
case: n qn fact1 => [|n]; rewrite ?ltxx // => qn _.
pose sl := map (fun x => a + (b - a) * (x%:R / (n.+1%:R))) (iota 0 n.+2).
pose a'_index := find (fun x => p.[x] >= 0) sl.
have has_sl : has (fun x => p.[x] >= 0) sl.
  rewrite has_map; apply/hasP; exists n.+1.
    by rewrite mem_iota add0n ltnSn ltnW.
  by rewrite /= divff ? pnatr_eq0 // mulr1 addrCA subrr addr0.
case: {2}a'_index (refl_equal a'_index) => [|ia'].
  rewrite /a'_index => ha'; have:= (nth_find 1 has_sl); rewrite ha' /=.
  by rewrite mul0r mulr0 addr0 leNgt nla.
set b':=  sl`_ia'.+1; set a' :=  sl`_ia'.
move=> ha'; exists (a', b'); simpl.
have ia's : (ia' < size sl)%N by rewrite -ha' /a'_index find_size.
have ia'iota : (ia' < size (iota 0 n.+2))%N by move: ia's; rewrite size_map.
have:= (nth_find 0 has_sl); rewrite -/a'_index ha' => pb'p.
have:= (ltnSn ia'); rewrite -{2}ha'.
move/(@before_find _ 0 (fun x : R => 0 <= p.[x]) sl); move/negbT.
rewrite -ltNge => pa'n.
move:(ltW ba') => ba'w.
have aa' : a <= a'.
  rewrite /a'/sl (nth_map 0%N) // ler_addl mulr_ge0 //.
  by rewrite mulr_ge0 // ?invr_ge0 ?ler0n.
have ia'_sharp : (ia' < n.+1)%N.
  move: ia'iota; rewrite leq_eqVlt; rewrite size_iota; case/orP=> //.
  move/eqP; case=> abs.
  move: pa'n; rewrite abs (nth_map 0%N) ?size_iota // nth_iota //.
  rewrite add0n divff ?mulr1 ?pnatr_eq0 // addrCA subrr addr0 => {} abs.
  by move: plb; rewrite leNgt abs.
have b'b : b' <= b.
  rewrite /b'/sl (nth_map 0%N) ?size_iota ?ltnS // nth_iota // add0n.
  have e : b = a + (b - a) by rewrite addrCA subrr addr0.
  rewrite {2}e {e} ler_add2l //= -{2}(mulr1 (b -a)) ler_wpmul2l //.
    rewrite ler_pdivr_mulr ?ltr0Sn // mul1r -subr_gte0 /=.
    have -> : (n.+1 = ia'.+1 + (n.+1 - ia'.+1))%N by rewrite subnKC.
    by rewrite mulrnDr addrAC subrr add0r subSS ler0n.
have b'a'_sub : b' - a' = (b - a) / (n.+1)%:R.
  have side : (ia' < n.+2)%N by apply: ltn_trans (ltnSn _).
  rewrite /b' /a' /sl (nth_map 0%N) ?size_iota // nth_iota // add0n.
  rewrite (nth_map 0%N) ?size_iota // nth_iota // add0n.
  rewrite opprD addrAC addrA subrr add0r addrC -mulrBr.
  by congr (_ * _); rewrite -mulrBl mulrSr addrAC subrr add0r div1r.
have a'b' :  a' < b'.
  move/eqP: b'a'_sub; rewrite subr_eq; move/eqP->; rewrite ltr_addr.
  by rewrite mulr_gt0 // invr_gt0 ltr0Sn.
rewrite pa'n a'b' b'b aa' pb'p.
have : `|p.[b'] - p.[a']| <= eps.
    have := (pc sl`_ia' sl`_ia'.+1 aa' (ltW a'b') b'b).
    rewrite b'a'_sub => hpc; apply: le_trans hpc _ => /=.
    rewrite mulrA ler_pdivr_mulr ?ltr0Sn // mulrC [eps * _]mulrC.
    rewrite -ler_pdivr_mulr //; apply: (ltW  qn).
case/ler_normlP => h1 h2.
rewrite ler_oppl/= !andbT.
rewrite -[in X in X && _](ler_add2l p.[b']) (le_trans h2) ? ler_addr //.
by rewrite -(ler_add2r (- p.[a'])) (le_trans h2) // ler_addl oppr_gte0 ltW.
Qed.

End PolsOnArchiField.
