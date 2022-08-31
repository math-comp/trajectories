From mathcomp Require Import all_ssreflect all_algebra vector reals ereal classical_sets.
Require Import preliminaries.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Remove the module, it is only here to print the results at the end. *)
Module Convex.
Section C.

Variable R: realType.
Variable E: lmodType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Definition segment (x y: E) := image `[0: R, 1] (fun t => (t *: x) + (1 - t) *: y).

Lemma segment_sym (u v x: E): segment u v x -> segment v u x.
Proof.
have te: forall t: R, 1 - (1 - t) = t by move=>t; rewrite opprB [t-1]addrC addrA subrr add0r.
move=>[t t01 <-]; exists (1-t).
   2: by rewrite addrC te.
apply /andP; move: t01=>/andP; (do 4 rewrite bnd_simp); move=>[t0 t1]; split.
   by rewrite subr_ge0.
by rewrite -subr_ge0 te.
Qed.

Definition convex (C: set E) := forall x y, C x -> C y -> subset (segment x y) C.

Lemma segment_convex (x y: E): convex (segment x y).
Proof.
move=> x0 y0 [t0 /andP [t00 t01]] <- [t1 /andP [t10 t11]] <- z [t /andP [t0' t1']] <-.
do 2 rewrite scalerDr scalerA scalerA.
rewrite [_ *: _ + _]addrC addrA addrC -addrA -scalerDl addrA -scalerDl addrC.
have e: (1 - t) * (1 - t1) + t * (1 - t0) = 1 - (t * t0 + (1 - t) * t1).
   do 2 rewrite mulrBr mulr1.
   rewrite -addrA -addrA [- t+_]addrC [t+_]addrC addrA addrA addrA -addrA subrr addr0 -addrA.
   by congr GRing.add; rewrite opprD addrC.
rewrite e; exists (t * t0 + (1 - t) * t1)=>//.
apply /andP; split; rewrite bnd_simp.
   apply addr_ge0; apply mulr_ge0=>//.
   by rewrite subr_ge0.
rewrite -subr_ge0 -e.
by apply addr_ge0; apply mulr_ge0=>//; rewrite subr_ge0.
Qed.

Lemma convexI (C D: set E): convex C -> convex D -> convex (C `&` D).
Proof.
move=> Cc Dc x y [Cx Dx] [Cy Dy] z xzy.
by split; [ apply (Cc x y) | apply (Dc x y) ].
Qed.


Definition conv (A: set E): set E := (fun a: E => exists (s: seq E) (k: 'I_(size s) -> R), \sum_i k i = 1 /\ \sum_i (k i) *: s`_i = a /\ (forall i, k i >= 0) /\ (forall i: 'I_(size s), s`_i \in A)).

Lemma conv_ext (A: set E): subset A (conv A).
Proof.
move=> x Ax.
exists [:: x]; exists (fun _ => 1).
split; [ by rewrite big_ord1 |]; split; [ by rewrite big_ord1 scale1r=>/= |]; split=>[_| [i /= ilt]].
   exact ler01.
case: i ilt=>// _.
by apply mem_set.
Qed.

Lemma conv_sub_convex (A C: set E): subset A C -> convex C -> subset (conv A) C.
Proof.
move=>AsC Cc x [s [k [k1 [kx [k0 kA]]]]]; subst x.
remember (size s) as n; move: Heqn=>/esym Heqn.
elim: n s Heqn k k1 k0 kA=> [| n IHn] s sn k k1 k0 kA.
   by exfalso; move: (oner_neq0 R)=>/eqP; apply; rewrite -k1 big_ord0.
case: s sn kA=> // a s sn kA.
move: k1; (do 2 rewrite big_ord_recl)=>/= k1.
case t1: (k ord0 == 1).
move: t1 k1=>/eqP -> /(f_equal (fun x => x-1)); rewrite subrr [1+_]addrC addrK=>/psumr_eq0P.
   have h: forall i : ordinal_finType n, true -> 0 <= k (lift ord0 i) by move=> i _; apply k0.
   move=>/(_ h) k0'.
   rewrite (congr_big _ (fun _ => true) (fun _ => 0 *: 0) Logic.eq_refl)=>//.
      2: by move=>i _; rewrite (k0' _ Logic.eq_refl) scale0r scale0r.
   rewrite -scaler_sumr scale0r addr0 scale1r.
   by apply AsC; move: (kA ord0)=>/set_mem.
move: k1=>/(f_equal (fun x => x-(k ord0))); rewrite [k ord0 + _]addrC addrK=>k1.
have k0le1: 0 <= 1 - k ord0.
   by rewrite -k1; apply sumr_ge0=>i _; apply k0.
have k0ne1: 1-k ord0 != 0.
   rewrite subr_eq0; apply /eqP=>k01.
   by move: t1; rewrite -k01 eq_refl.
inversion sn.
apply (Cc a ((GRing.inv (1-(k ord0))) *: \sum_(i < n) k (lift ord0 i) *: s`_i)).
   by apply AsC; apply set_mem; move: (kA ord0).
   2:{
   exists (k ord0).
      apply /andP; split; rewrite bnd_simp=>//.
      by rewrite -subr_ge0.
   by congr GRing.add; rewrite scalerA divff // scale1r.
   }
rewrite scaler_sumr.
move:IHn=>/(_ s H0 (fun i => (1 - k ord0)^-1 * k (lift ord0 i))).
rewrite -mulr_sumr k1 mulrC=>/(_ (mulfV k0ne1)).
have k0': forall i : 'I_n, 0 <= (1 - k ord0)^-1 * k (lift ord0 i) by move=> i; apply mulr_ge0=>//; rewrite invr_ge0.
move=>/(_ k0').
have kA': forall i : 'I_n, s`_i \in A by move=> i; move: (kA (lift ord0 i)).
move=>/(_ kA') inC.
refine (eq_ind _ _ inC _ _); apply congr_big=>// i _.
by rewrite scalerA.
Qed.

Lemma conv_segment (x y: E): segment x y = conv [set x; y].
Proof.
rewrite eqEsubset; split.
   move=> z [t /andP [t0 t1]] <-.
   rewrite bnd_simp in t0; rewrite bnd_simp in t1.
   exists [:: x; y].
   exists (fun i => match i with | @Ordinal _ 0 _ => t| _ => 1-t end).
   split.
      by rewrite big_ord_recl big_ord1 -botEord /= [1-t]addrC addrA subrr add0r.
   split.
      by rewrite big_ord_recl big_ord1 -botEord.
   split; move=>[i ilt].
      2: by apply mem_set; case: i ilt=>[| i] ilt; [ left | right; case: i ilt].
   by case: i ilt=>// i ilt; rewrite subr_ge0.
apply conv_sub_convex.
   2: by apply segment_convex.
move=>z; case=>->.
   exists 1.
      2: by rewrite scale1r subrr scale0r addr0.
   apply /andP; split; rewrite bnd_simp=>//.
   exact (@ler01 R).
exists 0.
   2: by rewrite scale0r subr0 scale1r add0r.
apply /andP; split; rewrite bnd_simp=>//.
exact (@ler01 R).
Qed.

Lemma conv_convex (A: set E): convex (conv A).
Proof.
move=> x y [sx [kx [kx1 [kxx [kx0 kxA]]]]] [sy [ky [ky1 [kyy [ky0 kyA]]]]] z [t /andP [t0 t1] tz]; subst x y z.
rewrite bnd_simp in t0; rewrite bnd_simp in t1.
exists (sx ++ sy); rewrite size_cat.
exists (fun i => match split i with | inl i => t * kx i | inr i => (1-t) * ky i end).
split.
   rewrite big_split_ord (congr_big _ (fun _ => true) (fun i => t * kx i) Logic.eq_refl) //.
      2: by move=> i _; rewrite (unsplitK (inl i)).
   rewrite -mulr_sumr kx1 mulr1 (congr_big _ (fun _ => true) (fun i => (1-t) * ky i) Logic.eq_refl) //.
      2: by move=> i _; rewrite (unsplitK (inr i)).
   rewrite -mulr_sumr ky1 mulr1 addrC.
   have -> : GRing.add_monoid R t (- t + 1) = t + (-t+1) by lazy.
   by rewrite addrA subrr add0r.
split.
   rewrite big_split_ord (congr_big _ (fun _ => true) (fun i => t *: (kx i *: sx`_i)) Logic.eq_refl) //.
      2: by move=> i _; rewrite nth_cat_ord (unsplitK (inl i)) scalerA.
   rewrite -scaler_sumr (congr_big _ (fun _ => true) (fun i => (1-t) *: (ky i *: sy`_i)) Logic.eq_refl) //.
      2: by move=> i _; rewrite nth_cat_ord (unsplitK (inr i)) scalerA.
   by rewrite -scaler_sumr; lazy.
split=> i.
   by case: (split i)=>o; apply mulr_ge0=>//; rewrite subr_ge0.
by rewrite nth_cat_ord; case: (split _).
Qed.

Lemma convex_convE (C: set E): convex C <-> C = conv C.
Proof.
split=> Cc.
   by rewrite eqEsubset; split; [ apply conv_ext | apply conv_sub_convex ].
by rewrite Cc; apply conv_convex.
Qed.

Lemma conv_mono (A B: set E): subset A B -> subset (conv A) (conv B).
Proof.
move=>AB; apply conv_sub_convex.
   by apply (subset_trans AB), conv_ext.
by apply conv_convex.
Qed.

(* TODO: find how to speak about multilinear maps. *)
Lemma conv_add (A B: set E): conv [set a + b | a in A & b in B] = [set a + b | a in (conv A) & b in (conv B)]%classic.
Proof.
rewrite eqEsubset; split.
   apply conv_sub_convex.
      by apply image2_subset; apply conv_ext.
   move=> x y [ax axA [bx bxA xe]] [ay ayA [by' byA ye]] z [t t01 ze]; subst x y z.
   exists (t *: ax + (1-t) *: ay).
      by apply (conv_convex axA ayA); exists t.
   exists (t *: bx + (1-t) *: by').
      by apply (conv_convex bxA byA); exists t.
   by rewrite scalerDr scalerDr -addrA -addrA; congr GRing.add; rewrite addrA addrA; congr GRing.add; apply addrC.
move=> x [a [sa [ka [ka1 [kaa [ka0 kaA]]]]] [b [sb [kb [kb1 [kbb [kb0 kbA]]]]] xe]]; subst x a b.
exists ([seq i+j | i <- sa, j <- sb]); rewrite size_allpairs.
exists (fun i=> let (i, j) := split_prod i in ka i * kb j).
split.
   rewrite big_prod_ord -ka1.
   apply congr_big=>// i _.
   rewrite -[ka i]mulr1 -kb1 mulr_sumr.
   apply congr_big=>// j _.
   by move: (unsplit_prodK (i, j))=>/pair_equal_spec [-> ->].
split.
   rewrite big_prod_ord.
   rewrite -[\sum_i kb i *: sb`_i]scale1r -ka1 scaler_suml -big_split.
   apply congr_big=>// i _.
   rewrite scaler_sumr -[ka i *: sa`_i]scale1r -kb1 scaler_suml -big_split.
   apply congr_big=>// j _.
   by rewrite (nth_allpairs _ 0 0) unsplit_prodK scalerDr scalerA scalerA mulrC.
split=>i.
   case: split_prod=>o o0; apply mulr_ge0=>//.
rewrite (nth_allpairs _ 0 0); case: split_prod=>o o0.
apply mem_set.
exists (sa`_o).
   by apply set_mem.
exists (sb`_o0)=>//.
by apply set_mem.
Qed.

Lemma conv_scale (A: set E) (t: R): conv [set t *: a | a in A] = [set t *: a | a in (conv A)]%classic.
Proof.
rewrite eqEsubset; split.
   apply conv_sub_convex.
      by apply image_subset, conv_ext.
   move=> tx ty [x xA txe] [y yA tye] z [u u01 ze]; subst tx ty z.
   exists (u *: x + (1-u) *: y).
      by apply (conv_convex xA yA); exists u.
   by rewrite scalerDr; congr GRing.add; rewrite scalerA scalerA mulrC.
move=> tx [x [s [k [k1 [kx [k0 kA]]]]] txe]; subst tx x.
rewrite scaler_sumr.
exists [seq t *: a | a <- s].
rewrite size_map; exists k.
split=>//.
split.
   apply congr_big=>// [[i ilt]] _.
   by rewrite (nth_map 0) // scalerA scalerA mulrC.
split=>// i.
rewrite (nth_map 0) //.
apply mem_set; exists (s`_i)=> //.
by apply set_mem.
Qed.

Lemma convexT: convex setT.
Proof. by []. Qed.

Lemma convex0: convex set0.
Proof. by []. Qed.

Lemma convex1 x: convex [set x].
Proof.
move=> u v /= -> -> y [t t01 <-].
by rewrite -scalerDl [1-t]addrC addrA subrr add0r scale1r.
Qed.


End C.

Section C.
Variable R: realType.
Variable E F: lmodType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Variable f: {linear E -> F}.

Lemma imset_conv_lin (A: set E): image (conv A) f = conv (image A f). 
Proof.
rewrite eqEsubset; split.
   move=> x [y [s [k [k1 [ky [k0 kA]]]]] xe]; subst x y.
   rewrite raddf_sum.
   exists (map f s); rewrite size_map; exists k.
   split=>//.
   split.
      apply congr_big=>// i _.
      by rewrite (nth_map 0) // -linearZZ.
   split=>// i; rewrite (nth_map 0) // inE.
   by exists (s`_i)=>//; apply set_mem.
apply conv_sub_convex.
   apply image_subset, conv_ext.
move=> fx fy [x xA fxe] [y yA fye] z [t t01] ze; subst fx fy z.
rewrite -linearZZ -linearZZ -raddfD.
exists (t *: x + (1-t) *: y)=>//.
by apply (conv_convex xA yA); exists t.
Qed.

Lemma preimset_conv_lin_sub (A: set F): subset (conv (preimage f A)) (preimage f (conv A)). 
Proof.
move=> x [s [k [k1 [kx [k0 kA]]]]]; subst x=>/=; rewrite raddf_sum.
exists (map f s); rewrite size_map; exists k.
split=>//.
split.
   apply congr_big=>// i _.
   by rewrite (nth_map 0) // -linearZZ.
split=>// i; rewrite (nth_map 0) //.
by apply mem_set; move: (kA i)=>/set_mem.
Qed.

Lemma ker_convex: convex (preimage f [set 0]).
Proof.
move=> x y /= fx0 fy0 z [t t01 ze]; subst z=>/=.
by rewrite linearD linearZZ linearZZ fx0 fy0 scaler0 scaler0 addr0.
Qed.

Lemma preimage_conv_linE (A: set F): subset A (range f) -> preimage f (conv A) = conv (preimage f A).
Proof.
rewrite eqEsubset; split.
   2: by apply preimset_conv_lin_sub.
move=> x [s [k [k1 [kx [k0 kA]]]]].
have: all (fun x => x \in range f) s.
   apply /allP=>a /(nthP 0) [i ilt <-].
   apply mem_set, H, set_mem.
   by move: (kA (Ordinal ilt)).
move=>/lift_range [s' se]; subst s.
move: k k0 kx k1 kA; rewrite size_map=>k k0 kx k1 kA.
rewrite -preimage_add_ker conv_add.
move: ker_convex=>/convex_convE <-.
exists (\sum_i k i *: s'`_i).
   exists s', k.
   do 3 split=>//.
   move=> i; apply mem_set=>/=; apply set_mem.
   by move: (kA i); rewrite (nth_map 0).
exists (x - \sum_i k i *: s'`_i)=>/=.
   rewrite linearD linearN.
   suff: f x = f (\sum_(i < size s') k i *: s'`_i) by move=>->; rewrite subrr.
   by rewrite -kx linear_sum; apply congr_big=>// [[t a]] _; rewrite linearZZ (nth_map 0).
by rewrite addrA [_+x]addrC -addrA subrr addr0.
Qed.

End C.


Section vect.

Variable R: realType.
Variable E: vectType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

(* TODO: excessivement immonde *)
Lemma caratheodory (A: set E) x: x \in conv A -> exists s: seq E, x \in conv [set` s] /\ (size s <= (dimv (@fullv R E)).+1)%N /\ all (fun x => x \in A) s.
Proof.
move=>/set_mem [s [k [k1 [kx [k0 kA]]]]]; subst x.
remember (size s) as n; move: Heqn=>/esym Heqn.
elim: n s Heqn k k1 k0 kA=> [| n IHn] s ns k k1 k0 kA.
   exists nil; split=>//.
      by rewrite big_ord0; apply mem_set; exists nil, k; split=>//; split; [ by rewrite big_ord0 |]; split=>// i; inversion i; move: H; rewrite ltn0.
case nsgt: (size s <= (dimv (@fullv R E)).+1)%N.
   exists s; split.
      apply mem_set; exists s; rewrite ns; exists k; do 3 split=>//.
      by move=> i; apply mem_set; apply mem_nth; rewrite ns.
   split=>//.
      by apply /allP=>a /(nthP 0); rewrite ns=> [[i ilt <-]]; move: (kA (Ordinal ilt)).
have: exists mu: 'I_(size s) -> R, \sum_(i < size s) mu i = 0 /\ \sum_(i < size s) (mu i) *: s`_i = 0 /\ exists i, mu i <> 0.
   clear IHn.
   move: nsgt; rewrite ns ltnNge=>/negP/negP nsgt.
   case: s ns kA=> // a s ns kA; inversion ns; subst n; clear ns.
   case sf: (free (in_tuple [seq b-a | b <- s])).
      have: basis_of fullv (in_tuple [seq b-a | b <- s]).
         rewrite basisEfree; apply /andP; split=>//; apply /andP; split.
            by apply subvf.
         rewrite size_map.
         by refine (leq_trans _ nsgt).
      rewrite in_tupleE basisEdim size_map=>/andP [_ nsge].
      by move: nsgt; rewrite ltnNge nsge.
   move: sf=>/negP /freeN_combination; rewrite in_tupleE size_map=> [[mu [musum [i mui]]]].
   rewrite /= -addn1 addnC.
   exists (fun i => match split i with | inl i => - \sum_i mu i | inr i => mu i end).
   split.
      rewrite big_split_ord big_ord1 (unsplitK (inl _)).
      have->: forall n m, GRing.add_monoid R n m = n + m by [].
      rewrite addrC; apply /eqP; rewrite subr_eq0; apply /eqP.
      apply congr_big=>// j _.
      by rewrite (unsplitK (inr _)).
   split.
      rewrite big_split_ord big_ord1 (unsplitK (inl _)) /= scaleNr addrC scaler_suml -sumrB -{3}musum.
      apply congr_big=>// j _.
      by rewrite (unsplitK (inr _)) (nth_map 0) // scalerBr.
   by exists (rshift 1 i); rewrite (unsplitK (inr _)); apply /eqP.
clear nsgt; rewrite ns; move=>[mu [muR [muE [i mui]]]].
wlog: mu muR muE mui / mu i > 0.
   move=> H.
   case mupos: (0 < mu i).
      by apply (H mu).
   apply (H (fun i => - mu i)).
      + by rewrite sumrN muR oppr0.
      + by rewrite -{3}oppr0 -{3}muE -sumrN; apply congr_big=>// j _; rewrite scaleNr.
      + by move=> /(f_equal (@GRing.opp R)); rewrite opprK oppr0.
      + move: mui=>/eqP; rewrite [mu i != 0]real_neqr_lt. move=>/orP; case; [ by rewrite oppr_gt0 | by rewrite mupos ].
         by apply num_real.
         by apply num_real.
move=>/(@Order.TotalTheory.arg_minP _ _ _ i (fun i => 0 < mu i) (fun i => (k i) / (mu i))) [im muip muim]; clear i mui.
wlog: s ns k k1 k0 kA mu muR muE im muip muim / (im == ord0)%N.
   set f := fun i: nat => if i == nat_of_ord im then 0%N else if i == 0%N then nat_of_ord im else i.
   have fcan: cancel f f.
      move=> j; rewrite /f.
      case jim: (j == im); case j0: (j == 0%N); case im0: (0%N == im); rewrite ?eq_refl; rewrite ?jim ?j0; move: jim j0 im0=>/eqP jim /eqP j0 /eqP im0; try subst j; try subst im =>//; try reflexivity; exact im0.
   have flt: forall i: 'I_n.+1, (f i < n.+1)%N by move=>[j jlt]; rewrite /f; case jim: (j == im); case j0: (j == 0%N).
   have fbij: bijective (fun i => Ordinal (flt i)) by exists (fun i => Ordinal (flt i)); move=> [j jlt]; apply val_inj, fcan.
   move=>/(_ (mkseq (fun i => nth 0 s (f i)) n.+1)); rewrite size_mkseq=>/(_ Logic.eq_refl (fun i => k (Ordinal (flt i)))).
   have k1': \sum_i k (Ordinal (flt i)) = 1.
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      by rewrite big_map -k1; apply congr_big=>// [[j jlt]] _; congr k; apply val_inj, fcan.
   move=> /(_ k1').
   have k0': forall i : 'I_n.+1, 0 <= k (Ordinal (flt i)) by [].
   move=>/(_ k0').
   have kA': forall i : 'I_n.+1, (mkseq (fun i0 : nat => s`_(f i0)) n.+1)`_i \in A.
      by move=>j; rewrite nth_mkseq //; move: (kA (Ordinal (flt j))).
   move=>/(_ kA' (fun i => mu (Ordinal (flt i)))).
   have mu'R: \sum_(i0 < n.+1) mu (Ordinal (flt i0)) = 0.
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      by rewrite big_map -{4}muR; apply congr_big=>// [[j jlt]] _; congr mu; apply val_inj, fcan.
   move=>/(_ mu'R).
   have mu'E: \sum_(i0 < n.+1) mu (Ordinal (flt i0)) *: (mkseq (fun i1 : nat => s`_(f i1)) n.+1)`_i0 = 0.
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      rewrite big_map -{6}muE; apply congr_big=>// [[j jlt]] _.
      rewrite nth_mkseq //; congr (mu _ *: s`_(_)); [ apply val_inj |]; apply fcan.
   move=>/(_ mu'E (Ordinal (flt im))).
   have muip': 0 < mu (Ordinal (flt (Ordinal (flt im)))) by refine (eq_ind _ (fun x => 0 < x) muip _ _); congr mu; destruct im; apply val_inj; apply /esym; apply fcan.
   move=>/(_ muip').
   have muim': forall j : ordinal_finType n.+1,
  0 < mu (Ordinal (flt j)) ->
  k (Ordinal (flt (Ordinal (flt im)))) /
  mu (Ordinal (flt (Ordinal (flt im)))) <=
  k (Ordinal (flt j)) / mu (Ordinal (flt j)).
      move=>j mujp.
      refine (eq_ind _ (fun i => k i / mu i <= k (Ordinal (flt j)) / mu (Ordinal (flt j))) (muim _ mujp) _ _).
      destruct im; apply /esym; apply val_inj, fcan.
   move=>/(_ muim').
   have im0: Ordinal (flt im) == ord0.
      by apply /eqP; apply val_inj=>/=; rewrite /f; rewrite eq_refl.
   move=>/(_ im0) [s' [s'conv [s'size s'A]]].
   exists s'; split=>//.
      refine (eq_ind _ (fun x => x \in conv [set` s']) s'conv _ _).
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      rewrite big_map; apply congr_big=>// [[j jlt]] _.
      rewrite nth_mkseq //.
      by congr (k _ *: s`_(_)); [ apply val_inj |]; apply fcan.
move=>/eqP ime; subst im.
case: s ns kA muE=> // a s ns kA muE.
inversion ns; subst n; clear ns.
have leS: forall n m, (n <= m -> n < m.+1)%N by move=> n m; rewrite ltnS.
move: (IHn s Logic.eq_refl (fun i => k (lift ord0 i) - k ord0 / mu ord0 * mu (lift ord0 i))); clear IHn.
have mu0: mu ord0 != 0 by apply /eqP=>mu0; move: muip; rewrite mu0 lt0r eq_refl.
have k0mu0: k ord0 / mu ord0 * mu ord0 = k ord0 by rewrite -{2}[mu ord0]divr1 mulf_div [_*1]mulrC -mulf_div divr1 mulfV // mulr1.
have k1': \sum_i (k (lift ord0 i) - k ord0 / mu ord0 * mu (lift ord0 i)) = 1
   by rewrite -[1]subr0 -{2}(mulr0 (k ord0 / mu ord0)) -k1 -{3}muR mulr_sumr -sumrB big_ord_recl k0mu0 subrr add0r; apply congr_big.
move=>/(_ k1').
have kp: forall i : 'I_(size s), 0 <= k (lift ord0 i) - k ord0 / mu ord0 * mu (lift ord0 i).
   move=>j; rewrite subr_ge0.
   case mujp: (0 < mu (lift ord0 j)).
      by rewrite -ler_pdivl_mulr //; apply muim.
   refine (Order.POrderTheory.le_trans _ (k0 (lift ord0 j))).
   apply mulr_ge0_le0.
      apply divr_ge0=>//.
      by move: muip; rewrite lt0r=>/andP [_ ->].
   rewrite real_leNgt.
      by rewrite mujp.
      by apply num_real.
   by apply num_real.
move=>/(_ kp).
have kA': forall i : 'I_(size s), s`_i \in A by move=>j; move: (kA (lift ord0 j)).
move=>/(_ kA') [s' [s'conv s'ok]].
exists s'; split=>//.
apply (eq_ind _ (fun x => x \in conv [set` s']) s'conv).
by rewrite -[\sum_i k i *: (a :: s)`_i]subr0 -{5}(scaler0 _ (k ord0 / mu ord0)) -{5}muE scaler_sumr -sumrB big_ord_recl scalerA k0mu0 subrr add0r; apply congr_big=>// i _; rewrite scalerA scalerBl.
Qed.


End vect.

Section prod.

Variable R: realType.
Variable E F: lmodType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Lemma conv_prod (A: set E) (B: set F): conv (A `*` B) = ((conv A) `*` (conv B))%classic.
Proof.
rewrite eqEsubset; split.
   apply conv_sub_convex.
      by apply setSM; apply conv_ext.
   move=> [xa xb] [ya yb] [xaA xbB] [yaA ybB] z [t ht01 <-] /=; split.
      by apply (conv_convex xaA yaA); exists t.
   by apply (conv_convex xbB ybB); exists t.
move=>[x y] [[sx [kx [kx1 [/= <- [kx0 kxA]]]]]] [sy [ky [ky1 [/= <- [ky0 kyA]]]]].
exists (allpairs (fun x y=> (x, y)) sx sy).
rewrite size_allpairs; exists (fun i => let (i, j) := split_prod i in kx i * ky j).
split.
   rewrite big_prod_ord -kx1; apply congr_big=>// i _.
   rewrite -[kx i]mulr1 -ky1 mulr_sumr; apply congr_big=>// j _.
   by move: (unsplit_prodK (i, j))=>[-> ->].
split.
   transitivity (\sum_i (let (i0, j) := split_prod i in (kx i0 * ky j) *: sx`_i0, let (i0, j) := split_prod i in (kx i0 * ky j) *: sy`_j)).
      by apply congr_big=> // i _; rewrite (nth_allpairs _ 0 0); case: split_prod=>o o0.
   rewrite big_pair; apply pair_equal_spec; split; rewrite big_prod_ord.
      by apply congr_big=>// i _; rewrite -[kx i *: sx`_i]scale1r -ky1 scaler_suml; apply congr_big=>// j _; move: (unsplit_prodK (i, j))=>[-> ->]; rewrite mulrC scalerA.
   by rewrite -[\sum_(i < size sy) ky i *: sy`_i]scale1r -kx1 scaler_suml; apply congr_big=>// i _; rewrite scaler_sumr; apply congr_big=>// j _; move: (unsplit_prodK (i, j))=>[-> ->]; rewrite scalerA.
split=>i.
   by case: split_prod=>o o0; apply mulr_ge0.
by rewrite (nth_allpairs _ 0 0); case: split_prod=>o o0; apply mem_set; split; apply set_mem=>/=.
Qed.

End prod.

Section face.

Variable R: realType.
Variable E: lmodType R.
Variable A: set E.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Definition ext := classical_sets.mkset (fun x => forall u v, u \in A -> v \in A -> x \in segment u v -> x = u \/ x = v).

Definition face (F: set E) := (F `<=` A)%classic /\ convex F /\ forall x u v, x \in F -> u \in A -> v \in A -> x \in segment u v -> x != u -> x != v -> u \in F /\ v \in F.

Definition face' (F: set E) := (F `<=` A)%classic /\ convex F /\ forall x u v, x \in F -> u \in A -> v \in A -> x \in segment u v -> x != v -> u \in F.

Lemma face'P (F: set E): face F <-> face' F.
Proof.
split; move=>[FA [Fconv Fface]]; split=>//; split=>// x u v xF uA vA xuv.
   move=>xv; case xu: (x == u).
      by move: xu=>/eqP xu; subst u.
   by move: xu=>/negP/negP xu; move: (Fface x u v xF uA vA xuv xu xv)=> [uF _].
move=>xu xv; split; [ apply (Fface x u v) | apply (Fface x v u) ]=>//.
by apply mem_set, segment_sym, set_mem.
Qed.

(* TODO: is it possible to use psatz ? *)

Lemma ext_carac (x: E): convex A -> x \in A -> [<-> x \in ext;
  forall u v, u \in A -> v \in A -> x = 1/2 *: (u+v) -> u = v;
  convex (A `\ x)%classic;
  face [set x]].
Proof.
move=>Aconv xA.
have ne20: (2: R) != 0 by rewrite pnatr_eq0.
split.
   move=>xext u v uA vA xe.
   move: xext=>/set_mem /(_ u v uA vA).
   have xuv: x \in segment u v.
      apply mem_set; subst x; exists (1 / 2).
         apply /andP; split; rewrite bnd_simp.
            by rewrite div1r invr_ge0 ler0z.
         rewrite ler_pdivr_mulr.
            rewrite mul1r; apply ler1z.
         by rewrite ltr0z.
      by rewrite {3}(splitr 1) -addrA subrr addr0 scalerDr.
   move: uA vA=>_ _ /(_ xuv); move: xuv=>_.
   wlog: u v xe / x = u.
      move=> h; case=> xe'.
         by apply h=>//; left.
      apply /esym; apply h=>//.
         by rewrite addrC.
         by left.
      move: xe=> -> xu _.
      move: xu=>/(f_equal (fun x => 2 *: x));   rewrite scalerA -{1}[2]divr1 mulf_div mul1r mulr1 divff // scale1r.
   have ->: 2 = 1+1 by [].
   by rewrite scalerDl scale1r addrC; move=>/(f_equal (fun x => x-u)); do 2 rewrite -addrA subrr addr0.
split.
   move=>xext u v [uA ux] [vA vx] y yuv.
   split.
      by apply (Aconv _ _ uA vA).
   move: yuv=> [t t01 ye] /= yx; subst y x.
   have te: forall (t: R), 1 - (1-t) = t by move=>t'; rewrite opprB [t'-1]addrC addrA subrr add0r.
   have xe': forall (t: R) (u v: E), (1 - t) *: v + (1 - (1 - t)) *: u = t *: u + (1-t) *: v by move=>t' u' v'; rewrite addrC te.
   wlog: u v t xext xA uA ux vA vx t01 / 2*t <= 1.
      move=>h.
      case tle: (2*t <= 1).
         by apply (h u v t).
      apply (h v u (1-t)); rewrite ?xe'=>//.
         + move: t01=>/andP [t0 t1]; apply /andP; split; [ move: t1 | move: t0 ]; do 2 rewrite bnd_simp; [ move=>t1 | move=>t0 ].
            by rewrite subr_ge0.
         by rewrite -subr_ge0 te.
         + rewrite -subr_ge0 mulrDr mulrN opprB [2*t-_]addrC addrA.
           have e2: 2 = 1+1 by [].
           rewrite {1}e2 mulr1 -{3}[1]opprK opprB addrA subrr add0r addrC subr_ge0.
           by move: tle; rewrite real_leNgt; (try apply num_real)=> /negP /negP; rewrite -subr_gt0 lt0r=>/andP [_ tle']; rewrite -subr_ge0.
   move=>tle.
   move: xext=>/(_ ((2*t) *: u + (1-2*t) *: v) v).
   have wA: (2 * t) *: u + (1 - 2 * t) *: v \in A.
      by apply mem_set, (Aconv _ _ uA vA); exists (2*t)=>//; apply /andP; split; rewrite bnd_simp //; move: t01=>/andP [t0 _]; apply mulr_ge0=>//; rewrite ler0z.
   move: vA=>/mem_set vA /(_ wA vA).
   rewrite div1r scalerDr scalerDr scalerA mulrA scalerA [_*(_-_)]mulrDr -{1}mulrN mulrA mulr1 [2^-1+_]addrC [(_+2^-1)*:_]scalerDl -addrA -addrA -scalerDl -{3 4}[2^-1]mulr1 -mulrDr mulVf // mul1r mul1r -scalerDl [_+1]addrC.
   move=>/(_ Logic.eq_refl) /(f_equal (fun x => x-v)).
   rewrite [1-_]addrC scalerDl scale1r -addrA -addrA subrr addr0 scaleNr -scalerN-scalerDr.
   apply /eqP; rewrite scaler_eq0; apply /negP=>/orP; case.
      rewrite mulf_eq0=>/orP; case=> e0.
         by move: ne20; rewrite e0.
      move: e0 vx=>/eqP e0; subst t; apply=>/=.
      by rewrite scale0r add0r subr0 scale1r.
   rewrite subr_eq0=>/eqP uv; subst v.
   move: ux; apply=>/=.
   by rewrite -scalerDl [1-t]addrC addrA subrr add0r scale1r.
split.
   move=> Axconv.
   split; [ by move=>u /= ->; apply set_mem |]; split; [ by apply convex1 |]=> y u v /set_mem -> /set_mem uA /set_mem vA /set_mem xuv xu xv; exfalso.
   have uAx: (A `\ x)%classic u by split=>//= ux; subst u; move: xu; rewrite eq_refl.
   have vAx: (A `\ x)%classic v by split=>//= vx; subst v; move: xv; rewrite eq_refl.
   have: (A `\ x)%classic x by apply (Axconv _ _ uAx vAx).
   by move=>[_ /= f].
move=>xface; apply /mem_set=>u v uA vA xuv.
suff: (x == u) || (x == v) by move=>/orP; case=> /eqP ->; [ left | right ].
apply /negP=>/negP; rewrite negb_or=>/andP [xu xv].
move: xface=>[_ [_ /(_ x u v)]].
have xx: x \in [set x]%classic by apply /mem_set.
move=>/(_ xx uA vA xuv xu xv) [/set_mem /= ux /set_mem /= vx]; subst u.
by move: xu; rewrite eq_refl.
Qed.

End face.
Section face.

Variable R: realType.
Variable E: lmodType R.
Variable A: set E.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Lemma face_trans (F: set E) (G: set E): face A F -> face F G -> face A G.
Proof.
move=>[AF [Fconv Fface]] [FG [Gconv Gface]].
split.
   by move=> x Gx; apply AF, FG.
split=>// x u v xG uA vA xuv xu xv.
have [uF vF]: (u \in F /\ v \in F).
   apply (Fface x)=>//.
   by apply mem_set, FG, set_mem.
by apply (Gface x).
Qed.

Definition hyperplan_appui (f: {linear E -> GRing.regular_lmodType R}) (a: R) := (exists x, x \in A /\ f x = a) /\ ((forall x, x \in A -> f x <= a) \/ (forall x, x \in A -> a <= f x)).

Lemma hyperplan_appui_face (f: {linear E -> GRing.regular_lmodType R}) (a: R): convex A -> hyperplan_appui f a <-> (exists x, x \in A /\ f x = a) /\ face A (A `&` (preimage f [set a])).
Proof.
move=>Aconv; split; move=>[hex hface]; split=>//.
   wlog: f a hex hface / (forall x : E, x \in A -> f x <= a).
      move=>h; move: (hface); case=>hf.
         by apply (h f a).
      move: h=>/(_ (GRing.comp_linear f (GRing.opp_linear E)) (- a)).
      have hf': forall x : E, x \in A -> GRing.comp_linear f (GRing.opp_linear E) x <= - a by move=>x xA /=; rewrite -scaleN1r linearZZ scaleN1r ler_oppl opprK; apply hf.
      have hex': exists x : E, x \in A /\ GRing.comp_linear f (GRing.opp_linear E) x = - a.
         by move: hex=>[x [xA fx]]; exists x; split=>//=; rewrite -fx -scaleN1r linearZZ scaleN1r.
      move=>/(_ hex' (or_introl hf') hf'); congr (face A (A `&` _)).
      by rewrite eqEsubset; split=>x /= /eqP; rewrite -scaleN1r linearZZ scaleN1r; [ rewrite eqr_opp | rewrite -eqr_opp ]=>/eqP.
   move=> hf; apply face'P; split; [ by apply subIsetl |]; split.
      apply convexI=>//; apply convex_convE; rewrite -preimage_conv_linE; [ congr (f @^-1` _)%classic |].
         by apply (@convex_convE R (GRing.regular_lmodType R) [set a]%classic), convex1.
      by move: hex=> [x [xA fx]] b ->; exists x.
   move=> x u v /set_mem [xA xa] uA vA /set_mem [t t01 tx] xv; apply mem_set; (split; [ by apply set_mem |]); apply /eqP; rewrite -Order.POrderTheory.lte_anti; apply /andP; (split; [ by apply hf |]).
   have t0: t != 0.
      by apply /eqP=>t0; subst t; move: tx xv; rewrite scale0r add0r subr0 scale1r=>->; rewrite eq_refl.
   have tgt: 0 < t.
      by rewrite lt0r t0=>/=; move: t01=>/andP [t0' _]; rewrite bnd_simp in t0'.
   move: tx=>/(f_equal (fun x=> t^-1 *: (x-(1-t)*: v))); rewrite -addrA subrr addr0 scalerA mulVf // scale1r=>->; rewrite linearZZ linearD xa -scaleNr linearZZ ler_pdivl_mull // addrC -subr_ge0 -addrA -mulNr -{1}[a]mul1r -mulrDl scaleNr -scalerN -mulrDr; apply mulr_ge0.
      by rewrite subr_ge0; move: t01=>/andP [_ /idP]; rewrite bnd_simp.
   by rewrite addrC Num.Internals.subr_ge0; apply hf.
have: forall x y, x \in A -> y \in A -> f x < a -> a < f y -> False.
move=> u v uA vA fua afv; move: hface=>/face'P [_ [_ /(_ ((f v - a)/(f v - f u) *: u + (a - f u)/(f v - f u) *: v) u v)]].
   move: (Order.POrderTheory.lt_trans fua afv); rewrite -subr_gt0=>fufv.
   have inuv: ((f v - a) / (f v - f u)) *: u + ((a - f u) / (f v - f u)) *: v \in segment u v.
      apply mem_set; exists ((f v - a) / (f v - f u)).
         apply /andP; split; rewrite bnd_simp.
            by apply divr_ge0; [ move: afv; rewrite -subr_gt0 | move: fufv ]; rewrite lt0r=>/andP [_ h].
         rewrite ler_pdivr_mulr // mul1r; apply ler_sub=>//.
         by rewrite -subr_ge0; move: fua; rewrite -subr_gt0 lt0r=>/andP [_ h].
      congr (_ + _ *: v).
      move: fufv; rewrite lt0r=>/andP [fufv _].
      move: (oner_neq0 R)=>ne10.
      by rewrite -[1](divff fufv) -mulrBl; congr (_ / _); rewrite opprB addrA addrC addrA addrA [-_+_]addrC subrr add0r addrC.
   have Aa: ((f v - a) / (f v - f u)) *: u + ((a - f u) / (f v - f u)) *: v \in (A `&` f @^-1` [set a])%classic.
      apply mem_set; split.
         by apply (Aconv u v); by apply set_mem. 
      move: fufv; rewrite lt0r=>/andP [fufv _].
      by rewrite /= linearD linearZZ linearZZ [_*:_]mulrC [_*:_]mulrC mulrA mulrA -mulrDl addrC mulrBr mulrBr addrA -[_ - _ + _]addrA [-_+_]addrC [f u * _]mulrC subrr addr0 -mulrBl [_*a]mulrC -mulrA mulfV // mulr1.
   move=>/(_ Aa uA vA inuv).
   have nev: ((f v - a) / (f v - f u)) *: u + ((a - f u) / (f v - f u)) *: v != v.
      apply /eqP=>/(f_equal (fun x => (f v - f u) *: (x - ((a - f u) / (f v - f u)) *: v))).
      move: fufv; rewrite lt0r=>/andP [fufv _].
      rewrite -addrA subrr addr0 scalerA mulrA [_*(_-_)]mulrC scalerBr scalerA mulrA [(_-_)*(a-_)]mulrC -mulrA -mulrA mulfV // mulr1 mulr1 -scalerBl opprB addrA -[_-_+_]addrA [-_+_]addrC subrr addr0=>/eqP; rewrite -subr_eq0 -scalerBr scaler_eq0=>/orP; case.
         by move=>fva; move: afv; rewrite -subr_gt0 lt0r fva.
      by rewrite subr_eq0; move=>/eqP uv; subst v; move: fufv; rewrite subrr eq_refl.
   by move=>/(_ nev) /set_mem [_ /= fuae]; move: fua; rewrite fuae -subr_gt0 lt0r subrr eq_refl.
move=>h.
move: (boolp.EM (exists x: E, x \in A /\ f x < a)); case.
   move: (boolp.EM (exists x: E, x \in A /\ a < f x)); case.
      by move=>[y [yA afy]] [x [xA fxa]]; elim (h x y xA yA fxa afy).
   by move=>allge _; left=> x xA; rewrite Order.TotalTheory.leNgt; apply /negP=>fxa; apply allge; exists x; split.
by move=>allge; right=> x xA; rewrite Order.TotalTheory.leNgt; apply /negP=>fxa; apply allge; exists x; split.
Qed.

End face.
Section cone.

Variable R: realType.
Variable E: lmodType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Definition cone0 (A: set E) := ([set t *: a | t in [set t: R | 0 < t] & a in A] `<=` A)%classic.
Definition cone (x: E) (A: set E) := cone0 [set a-x | a in A]%classic.

Lemma cone0_convex (A: set E): cone0 A -> (convex A <-> ([set a+b | a in A & b in A] `<=` A)%classic).
Proof.
move=>Acone; split=>Aconv.
   move=>x [u uA] [v vA] <-.
   have uA2: A (2 *: u) by apply Acone; exists 2; [ rewrite /= ltr0z | exists u ].
   have vA2: A (2 *: v) by apply Acone; exists 2; [ rewrite /= ltr0z | exists v ].
   apply (Aconv _ _ uA2 vA2); exists (2^-1).
      apply /andP; split; rewrite bnd_simp.
         by rewrite invr_ge0 ler0z le0z_nat.
      by rewrite invf_le1 ?ler1z ?ltr0z.
   have ne20: (2: R) != 0 by rewrite pnatr_eq0.
   have->: 1-2^-1 = (2^-1: R) by apply (@scalerI R (GRing.regular_lmodType R) _ ne20); rewrite /GRing.scale /= mulrBr divff // mulr1 -addrA subrr addr0.
   by rewrite scalerA scalerA mulVf // scale1r scale1r.
move=>x y xA yA z [t /andP]; (do 2 rewrite bnd_simp)=>[[t0 t1]] <-.
move: t0; rewrite le0r=>/orP; case.
   by move=>/eqP ->; rewrite scale0r add0r subr0 scale1r.
move=>t0; move: t1; rewrite -subr_ge0 le0r=>/orP; case.
   by rewrite subr_eq0; move=>/eqP <-; rewrite subrr scale1r scale0r addr0.
move=> t1; apply Aconv; exists (t*:x); [| exists ((1-t)*:y) ]=>//; apply Acone.
   by exists t=>//; exists x.
by exists (1-t)=>//; exists y.
Qed.

(* Note: cone0_of A is NOT pointed due to lemma cone0_of_convE. *)
(* TODO: maybe change the 0 <= k i to 0 < k i in the definition of conv. *)

Definition cone0_of (A: set E): set E := (fun a: E => exists x (s: seq E) (k: 'I_(size (x::s)) -> R), \sum_i (k i) *: (x::s)`_i = a /\ (forall i, 0 < k i) /\ (forall i: 'I_(size (x::s)), (x::s)`_i \in A)).

Lemma cone0_of_cone0 (A: set E): cone0 (cone0_of A).
Proof.
move=>x [t /= t0] [a [y [s [k [<- [k0 kA]]]]]] <-.
rewrite scaler_sumr; exists y, s; exists (fun i => t * k i); split.
   by apply congr_big=>// i _; apply /esym; apply scalerA.
split=>// i.
by apply mulr_gt0.
Qed.

Lemma cone0_of_convE (A: set E): cone0_of A = [set t *: a | t in [set t | 0 < t] & a in (conv A)]%classic.
Proof.
rewrite eqEsubset; split=>x.
   move=>[y [s [k [<- [k0 kA]]]]]; set t := \sum_i k i.
   have k0': forall i : ordinal_finType (size (y :: s)), true -> 0 <= k i by move=>i _; apply Order.POrderTheory.ltW.
   have: 0 <= t by apply sumr_ge0.
   rewrite le0r=>/orP; case.
      by move=>/eqP /psumr_eq0P; move=> /(_ k0') /(_ ord0 Logic.eq_refl) k00; exfalso; move: (k0 ord0); rewrite lt0r k00 eq_refl.
   move=>t0; exists t=>//; exists (t^-1 *: \sum_i k i *: (y :: s)`_i).
      exists (y::s), (fun i => t^-1 * k i); split.
      by rewrite -mulr_sumr mulVf //; move: t0; rewrite lt0r=>/andP[t0 _].
      split.
         by rewrite scaler_sumr; apply congr_big=>// i _; apply /esym; apply scalerA.
      split=>// i; apply mulr_ge0.
         2: by apply (k0' i).
      by rewrite invr_ge0; apply Order.POrderTheory.ltW.
   rewrite scalerA divff.
      by apply scale1r.
   by move: t0; rewrite lt0r=>/andP[t0 _].
move=>[t /= t0] [a [s [k [k1 [<- [k0 kA]]]]]] <-.
rewrite scaler_sumr (@mathcomp_extra.bigID_idem _ _ _ _ _ _ _ _ (fun i=> 0 < k i)); [| apply addrA | apply addrC | apply addr0 ].
have ->: \sum_(i < size s | true && ~~ (0 < k i)) t *: (k i *: s`_i) = \sum_(i < size s | true && ~~ (0 < k i)) 0 *: 0.
   apply congr_big=>// i /andP [_ ki0]; move: (k0 i); rewrite Order.POrderTheory.le_eqVlt=>/orP; case.
      by move=>/eqP <-; rewrite scale0r scale0r scaler0.
   by move=> ki0'; move:ki0; rewrite ki0'.
rewrite -[\sum_(_ < _ | _) 0 *: 0]scaler_sumr scale0r addr0 -big_filter /=.
remember [seq i <- index_enum (ordinal_finType (size s)) | 0 < k i] as I; move: HeqI=>/esym HeqI.
case: I HeqI=> [| i I] HeqI.
exfalso; move: k1 (oner_neq0 R); rewrite (@mathcomp_extra.bigID_idem _ _ _ _ _ _ _ _ (fun i=> 0 < k i)); [| apply addrA | apply addrC | apply addr0 ]. rewrite -big_filter HeqI big_nil add0r=><- /eqP; apply. 
   transitivity (\sum_(i < size s | true && ~~ (0 < k i)) (0*0:R)).
      2: by rewrite -mulr_sumr mul0r.
   by apply congr_big=>// i /= kile; move: (k0 i); rewrite le0r mul0r=>/orP; case=> [ /eqP // | kigt ]; move: kigt kile=>->.
have: subseq (i::I) (index_enum (ordinal_finType (size s))) by rewrite -HeqI; apply filter_subseq.
case: s k k1 k0 kA i I HeqI=> [| b s] k k1 k0 kA i I HeqI.
   by inversion i.
move=> /subseq_incl; move=> /(_ ord0); rewrite size_index_enum card_ord; move=> [f [fn flt]].
rewrite /cone0_of.
exists (b::s)`_i, [seq (b::s)`_(nth i (i::I) (lift ord0 j)) | j <- index_enum (ordinal_finType (size I))].
rewrite /= size_map size_index_enum card_ord; exists (fun j => t * k (nth i (i::I) j)).
split.
   rewrite -{2}(map_nth_ord i (i :: I)) big_map.
   apply congr_big=>// j _; rewrite scalerA; congr GRing.scale.
   case: j; case=> //= j jlt.
   move: jlt; rewrite ltnS=>jlt.
   rewrite (nth_map (Ordinal jlt)); [ congr (_`_(nth i I _)) |].
      2: by rewrite size_index_enum card_ord.
   rewrite /index_enum; case: index_enum_key=>/=; rewrite -enumT /=.
   have je: j = Ordinal jlt by [].
   by rewrite {2 3}je; rewrite nth_ord_enum.
split.
   move=> j; apply mulr_gt0=>//; rewrite -HeqI.
   by apply (@nth_filter _ (fun i => 0 < k i)); rewrite HeqI.
case; case=>//= j jlt.
move: jlt; rewrite ltnS=>jlt.
by rewrite (nth_map (Ordinal jlt)) // size_index_enum card_ord.
Qed.
      
Lemma cone0_of_sub_cone0_convex (A B: set E): (A `<=` B -> cone0 B -> convex B -> cone0_of A `<=` B)%classic.
Proof.
rewrite cone0_of_convE=>AB Bcone Bconv x [t t0 [a aA <-]].
apply Bcone; exists t=>//; exists a=>//.
by apply (conv_sub_convex AB).
Qed.

End cone.


Section Fun.

Variable R: realType.
Variable E: lmodType R.
Variable f: E -> \bar R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition fconvex := forall (x y: E) (t: R), t \in (`[0, 1]%R: interval R) -> f(t *: x + (1-t) *: y) <= EFin t * f x + EFin (1-t)%R * f y.

Definition fconvex_strict := forall (x y: E) (t: R), x <> y -> t \in (`]0, 1[%R: interval R) -> f(t *: x + (1-t) *: y) < EFin t * f x + EFin (1-t)%R * f y.

Lemma fconvex_max_ext (C: set E) (x: E): fconvex_strict -> convex C -> x \in C -> f x < +oo -> (forall y, y \in C -> f(y) <= f(x)) -> x \in ext C.
Proof.
move=> fconv Cconv xC fxoo xmax.
move: (ext_carac Cconv xC)=>/all_iffLR /(_ 1%N 0%N) /=; apply=> u v uC vC xmid.
apply /eqP/negP=> /negP /eqP uv.
move: (fconv u v (2^-1)%R uv).
have ne20: ((2:R) != 0)%R by rewrite pnatr_eq0.
have symhalf: ((1:R)-2^-1 = 2^-1)%R by rewrite -[(2^-1)%R]mul1r -{1}(divff ne20) -mulNr -mulrDl -addrA subrr addr0.
have lt02: ((0:R) < 2)%R by rewrite pmulrz_rgt0 //; exact ltr01.
have inhalf: (2^-1 \in `]0:R, 1[)%R.
   apply /andP; split; rewrite bnd_simp.
      by rewrite invr_gt0.
   rewrite invf_lt1 // -{1}[1%R]addr0; apply ler_lt_add=>//; exact ltr01.
move=>/(_ inhalf); rewrite symhalf -scalerDr.
move: xmid; rewrite div1r=><-.
apply /negP; rewrite -Order.TotalTheory.leNgt.
move: xmax (xmax u uC) fxoo=>/(_ v vC).
generalize (f x) (f u) (f v)=> a b c ca ba aoo.
case: b ba=> [ b | |] ba.
   2: by move: ba; rewrite [+oo <= a]Order.TotalTheory.leNgt aoo.
   2:{ rewrite {1}/mule /mule_subdef.
   have ->: ((2^-1:R)%:E == 0%:E) = false by rewrite eqe invr_eq0; apply /negP=>eq20; move: ne20; rewrite eq20.
   rewrite lte_fin.
   by move: inhalf=>/andP [h _]; move: h; rewrite bnd_simp=>->.
   }
case: c ca=> [ c | |] ca.
   2: by move: ca; rewrite [+oo <= a]Order.TotalTheory.leNgt aoo.
   2:{ rewrite {2}/mule /mule_subdef.
   have ->: ((2^-1:R)%:E == 0%:E) = false by rewrite eqe invr_eq0; apply /negP=>eq20; move: ne20; rewrite eq20.
   rewrite lte_fin.
   by move: inhalf=>/andP [h _]; move: h; rewrite bnd_simp=>->.
   }
case: a aoo ba ca=> // a aoo ba ca.
move: ca ba; (do 3 rewrite lee_fin)=>ca ba.
rewrite -mulrDr -[a]mul1r -{2}(mulVf ne20) -mulrA -subr_ge0 -mulrN -mulrDr.
apply mulr_ge0.
   by apply Order.POrderTheory.ltW; move: inhalf=>/andP [h _]; move: h; rewrite bnd_simp.
rewrite subr_ge0 mulrDl mul1r.
by apply ler_add.
Qed.


End Fun.




End Convex.

(* TODO: move to another file *)
Require Import Coq.Program.Wf.

Section Bezier.

Variable R: realType.
Variable E: lmodType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

(* Note: in convex.v, this definition generates only one obligation. Why do I have three here ? *)
Program Fixpoint bezier (x: E) (s: seq E) (t: R) {measure (size s)}: E :=
  match s with
  | nil => x
  | y :: s => (1-t) *: (bezier x (belast y s) t) + t *: (bezier y s t)
  end.
Next Obligation.
Proof. by move=> _ s0 _ _ y s <-; rewrite size_belast. Defined.
Next Obligation.
Proof. by move=> _ s0 _ _ y s <-. Defined.
Next Obligation.
Proof. by apply measure_wf, Wf_nat.lt_wf. Qed.

(* Note: in convex.conv, bezier _ [::] _ reduces automatically. Why is it not the case now ? *)
Lemma bezier_nil x t: bezier x [::] t = x.
Proof.
rewrite /bezier /bezier_func.
by rewrite WfExtensionality.fix_sub_eq_ext.
Qed.

Lemma bezier_cons x y s t: bezier x (y :: s) t = (1-t) *: (bezier x (belast y s) t) + t *: (bezier y s t).
Proof.
rewrite /bezier /bezier_func.
by rewrite WfExtensionality.fix_sub_eq_ext.
Qed.

Lemma bezier0 x s: bezier x s 0 = x.
Proof.
remember (size s) as n; move: Heqn=>/esym Heqn.
elim: n s Heqn=>[| n IHn].
   move=> s /size0nil ->; apply bezier_nil.
case=>// a s sn.
rewrite bezier_cons subr0 scale1r scale0r addr0.
by apply IHn; rewrite size_belast; inversion sn.
Qed.

Lemma bezier1 x s: bezier x s 1 = last x s.
Proof.
remember (size s) as n; move: Heqn=>/esym Heqn.
elim: n x s Heqn=>[| n IHn] x.
   by move=> s /size0nil ->; apply bezier_nil.
case=> // a s sn.
rewrite bezier_cons subrr scale1r scale0r add0r /=.
by apply IHn; inversion sn.
Qed.

Lemma bezier_sub_conv x s: subset (bezier x s @` `[0, 1]) (Convex.conv (fun y => y \in (x :: s))).
Proof.
move=> y [t t01 <-].
remember (size s) as n; move: Heqn=>/esym Heqn.
elim: n x s Heqn=>[| n IHn] x.
   move=> s /size0nil ->; rewrite bezier_nil.
   apply Convex.conv_ext.
   by rewrite inE; apply /eqP.
case=> // a s sn; rewrite bezier_cons.
inversion sn.
have /Convex.conv_mono lsub: subset (fun y : E => y \in x :: belast a s) (fun y : E => y \in x :: a :: s) by move=> z; (do 2 rewrite in_cons)=>/orP; case=> [ -> // | /mem_belast -> ]; rewrite orbT.
have /(IHn _ x) /lsub l: size (belast a s) = n by rewrite size_belast.
have /Convex.conv_mono rsub: subset (fun y : E => y \in a :: s) (fun y : E => y \in x :: a :: s) by move=> z; (do 3 rewrite in_cons)=>/orP; case=>[ -> // | -> ]; rewrite orbT // orbT.
move: H0=>/(IHn _ a) /rsub r.
move: (@Convex.conv_convex _ _ (fun y : E => y \in x :: a :: s) (bezier x (belast a s) t) (bezier a s t) l r); apply.
exists (1-t).
   2: by rewrite -{2}[1]add0r addrKA opprK add0r.
apply /andP; move: t01=>/andP.
(repeat rewrite bnd_simp)=>[[t0 t1]]; split.
   by rewrite subr_ge0.
rewrite ler_subl_addl -{1}[1]add0r.
by apply ler_add.
Qed.

End Bezier.
