From mathcomp Require Import all_ssreflect all_algebra vector reals ereal classical_sets.
Require Import preliminaries.
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
have te: forall t: R, 1 - (1 - t) = t by move=>t; rewrite GRing.opprB [t-1]GRing.addrC GRing.addrA GRing.subrr GRing.add0r.
move=>[t t01 <-]; exists (1-t).
   2: by rewrite GRing.addrC te.
apply /andP; move: t01=>/andP; (do 4 rewrite bnd_simp); move=>[t0 t1]; split.
   by rewrite Num.Theory.subr_ge0.
by rewrite -Num.Theory.subr_ge0 te.
Qed.

Definition convex (C: set E) := forall x y, C x -> C y -> subset (segment x y) C.

Lemma segment_convex (x y: E): convex (segment x y).
Proof.
move=> x0 y0 [t0 /andP [t00 t01]] <- [t1 /andP [t10 t11]] <- z [t /andP [t0' t1']] <-.
do 2 rewrite GRing.scalerDr GRing.scalerA GRing.scalerA.
rewrite [_ *: _ + _]GRing.addrC GRing.addrA GRing.addrC -GRing.addrA -GRing.scalerDl GRing.addrA -GRing.scalerDl GRing.addrC.
have e: (1 - t) * (1 - t1) + t * (1 - t0) = 1 - (t * t0 + (1 - t) * t1).
   do 2 rewrite GRing.mulrBr GRing.mulr1.
   rewrite -GRing.addrA -GRing.addrA [- t+_]GRing.addrC [t+_]GRing.addrC GRing.addrA GRing.addrA GRing.addrA -GRing.addrA GRing.subrr GRing.addr0 -GRing.addrA.
   by f_equal; rewrite GRing.opprD GRing.addrC.
rewrite e; exists (t * t0 + (1 - t) * t1)=>//.
apply /andP; split; rewrite bnd_simp.
   apply Num.Theory.addr_ge0; apply Num.Theory.mulr_ge0=>//.
   by rewrite Num.Theory.subr_ge0.
rewrite -Num.Theory.subr_ge0 -e.
by apply Num.Theory.addr_ge0; apply Num.Theory.mulr_ge0=>//; rewrite Num.Theory.subr_ge0.
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
split; [ by rewrite big_ord1 |]; split; [ by rewrite big_ord1 GRing.scale1r=>/= |]; split=>[_| [i /= ilt]].
   exact Num.Theory.ler01.
destruct i=>//.
by apply mem_set.
Qed.

Lemma conv_sub_convex (A C: set E): subset A C -> convex C -> subset (conv A) C.
Proof.
move=>AsC Cc x [s [k [k1 [kx [k0 kA]]]]]; subst x.
remember (size s) as n; symmetry in Heqn.
move: s Heqn k k1 k0 kA; induction n=> s sn k k1 k0 kA.
   by exfalso; move: (GRing.oner_neq0 R)=>/eqP; apply; rewrite -k1 big_ord0.
destruct s as [| a s]=>//.
move: k1; (do 2 rewrite big_ord_recl)=>/= k1.
case t1: (k ord0 == 1).
move: t1 k1=>/eqP -> /(f_equal (fun x => x-1)); rewrite GRing.subrr [1+_]GRing.addrC GRing.addrK=>/Num.Theory.psumr_eq0P.
   have h: forall i : ordinal_finType n, true -> 0 <= k (lift ord0 i) by move=> i _; apply k0.
   move=>/(_ h) k0'.
   rewrite (congr_big _ (fun _ => true) (fun _ => 0 *: 0) Logic.eq_refl)=>//.
      2: by move=>i _; rewrite (k0' _ Logic.eq_refl) GRing.scale0r GRing.scale0r.
   rewrite -GRing.scaler_sumr GRing.scale0r GRing.addr0 GRing.scale1r.
   by apply AsC; move: (kA ord0)=>/set_mem.
move: k1=>/(f_equal (fun x => x-(k ord0))); rewrite [k ord0 + _]GRing.addrC GRing.addrK=>k1.
have k0le1: 0 <= 1 - k ord0.
   by rewrite -k1; apply Num.Theory.sumr_ge0=>i _; apply k0.
have k0ne1: 1-k ord0 != 0.
   rewrite GRing.subr_eq0; apply /eqP=>k01.
   by move: t1; rewrite -k01 eq_refl.
inversion sn.
apply (Cc a ((GRing.inv (1-(k ord0))) *: \sum_(i < n) k (lift ord0 i) *: s`_i)).
   by apply AsC; apply set_mem; move: (kA ord0).
   2:{
   exists (k ord0).
      apply /andP; split; rewrite bnd_simp=>//.
      by rewrite -Num.Theory.subr_ge0.
   by f_equal; rewrite GRing.scalerA GRing.divff // GRing.scale1r.
   }
rewrite GRing.scaler_sumr.
move:IHn=>/(_ s H0 (fun i => (1 - k ord0)^-1 * k (lift ord0 i))).
rewrite -GRing.mulr_sumr k1 GRing.mulrC=>/(_ (GRing.mulfV k0ne1)).
have k0': forall i : 'I_n, 0 <= (1 - k ord0)^-1 * k (lift ord0 i) by move=> i; apply Num.Theory.mulr_ge0=>//; rewrite Num.Theory.invr_ge0.
move=>/(_ k0').
have kA': forall i : 'I_n, s`_i \in A by move=> i; move: (kA (lift ord0 i)).
move=>/(_ kA') inC.
refine (eq_ind _ _ inC _ _); apply congr_big=>// i _.
by rewrite GRing.scalerA.
Qed.

Lemma conv_segment (x y: E): segment x y = conv [set x; y].
Proof.
rewrite eqEsubset; split.
   move=> z [t /andP [t0 t1]] <-.
   rewrite bnd_simp in t0; rewrite bnd_simp in t1.
   exists [:: x; y].
   exists (fun i => match i with | @Ordinal _ 0 _ => t| _ => 1-t end).
   split.
      by rewrite big_ord_recl big_ord1 -botEord /= [1-t]GRing.addrC GRing.addrA GRing.subrr GRing.add0r.
   split.
      by rewrite big_ord_recl big_ord1 -botEord.
   split; move=>[i ilt].
      2: by apply mem_set; destruct i; [ left | right; destruct i ].
   by destruct i=>//; rewrite Num.Theory.subr_ge0.
apply conv_sub_convex.
   2: by apply segment_convex.
move=>z; case=>->.
   exists 1.
      2: by rewrite GRing.scale1r GRing.subrr GRing.scale0r GRing.addr0.
   apply /andP; split; rewrite bnd_simp=>//.
   exact (@Num.Theory.ler01 R).
exists 0.
   2: by rewrite GRing.scale0r GRing.subr0 GRing.scale1r GRing.add0r.
apply /andP; split; rewrite bnd_simp=>//.
exact (@Num.Theory.ler01 R).
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
   rewrite -GRing.mulr_sumr kx1 GRing.mulr1 (congr_big _ (fun _ => true) (fun i => (1-t) * ky i) Logic.eq_refl) //.
      2: by move=> i _; rewrite (unsplitK (inr i)).
   rewrite -GRing.mulr_sumr ky1 GRing.mulr1 GRing.addrC.
   have -> : GRing.add_monoid R t (- t + 1) = t + (-t+1) by lazy.
   by rewrite GRing.addrA GRing.subrr GRing.add0r.
split.
   rewrite big_split_ord (congr_big _ (fun _ => true) (fun i => t *: (kx i *: sx`_i)) Logic.eq_refl) //.
      2: by move=> i _; rewrite nth_cat_ord (unsplitK (inl i)) GRing.scalerA.
   rewrite -GRing.scaler_sumr (congr_big _ (fun _ => true) (fun i => (1-t) *: (ky i *: sy`_i)) Logic.eq_refl) //.
      2: by move=> i _; rewrite nth_cat_ord (unsplitK (inr i)) GRing.scalerA.
   by rewrite -GRing.scaler_sumr; lazy.
split=> i.
   by destruct (split i); apply Num.Theory.mulr_ge0=>//; rewrite Num.Theory.subr_ge0.
by rewrite nth_cat_ord; destruct (split _).
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
   by rewrite GRing.scalerDr GRing.scalerDr -GRing.addrA -GRing.addrA; f_equal; rewrite GRing.addrA GRing.addrA; f_equal; apply GRing.addrC.
move=> x [a [sa [ka [ka1 [kaa [ka0 kaA]]]]] [b [sb [kb [kb1 [kbb [kb0 kbA]]]]] xe]]; subst x a b.
exists ([seq i+j | i <- sa, j <- sb]); rewrite size_allpairs.
exists (fun i=> let (i, j) := split_prod i in ka i * kb j).
split.
   rewrite big_prod_ord -ka1.
   apply congr_big=>// i _.
   rewrite -[ka i]GRing.mulr1 -kb1 GRing.Theory.mulr_sumr.
   apply congr_big=>// j _.
   by move: (unsplit_prodK (i, j))=>/pair_equal_spec [-> ->].
split.
   rewrite big_prod_ord.
   rewrite -[\sum_i kb i *: sb`_i]GRing.scale1r -ka1 GRing.Theory.scaler_suml -big_split.
   apply congr_big=>// i _.
   rewrite GRing.Theory.scaler_sumr -[ka i *: sa`_i]GRing.scale1r -kb1 GRing.Theory.scaler_suml -big_split.
   apply congr_big=>// j _.
   by rewrite (nth_allpairs _ 0 0) unsplit_prodK GRing.scalerDr GRing.scalerA GRing.scalerA GRing.mulrC.
split=>i.
   by destruct split_prod; apply Num.Theory.mulr_ge0.
rewrite (nth_allpairs _ 0 0); destruct split_prod.
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
   by rewrite GRing.scalerDr; f_equal; rewrite GRing.scalerA GRing.scalerA GRing.mulrC.
move=> tx [x [s [k [k1 [kx [k0 kA]]]]] txe]; subst tx x.
rewrite GRing.scaler_sumr.
exists [seq t *: a | a <- s].
rewrite size_map; exists k.
split=>//.
split.
   apply congr_big=>// [[i ilt]] _.
   by rewrite (nth_map 0) // GRing.scalerA GRing.scalerA GRing.mulrC.
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
by rewrite -GRing.scalerDl [1-t]GRing.addrC GRing.addrA GRing.subrr GRing.add0r GRing.scale1r.
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
   rewrite GRing.raddf_sum.
   exists (map f s); rewrite size_map; exists k.
   split=>//.
   split.
      apply congr_big=>// i _.
      by rewrite (nth_map 0) // -GRing.linearZZ.
   split=>// i; rewrite (nth_map 0) // inE.
   by exists (s`_i)=>//; apply set_mem.
apply conv_sub_convex.
   apply image_subset, conv_ext.
move=> fx fy [x xA fxe] [y yA fye] z [t t01] ze; subst fx fy z.
rewrite -GRing.linearZZ -GRing.linearZZ -GRing.raddfD.
exists (t *: x + (1-t) *: y)=>//.
by apply (conv_convex xA yA); exists t.
Qed.

Lemma preimset_conv_lin_sub (A: set F): subset (conv (preimage f A)) (preimage f (conv A)). 
Proof.
move=> x [s [k [k1 [kx [k0 kA]]]]]; subst x=>/=; rewrite GRing.raddf_sum.
exists (map f s); rewrite size_map; exists k.
split=>//.
split.
   apply congr_big=>// i _.
   by rewrite (nth_map 0) // -GRing.linearZZ.
split=>// i; rewrite (nth_map 0) //.
by apply mem_set; move: (kA i)=>/set_mem.
Qed.

Lemma ker_convex: convex (preimage f [set 0]).
Proof.
move=> x y /= fx0 fy0 z [t t01 ze]; subst z=>/=.
by rewrite GRing.linearD GRing.linearZZ GRing.linearZZ fx0 fy0 GRing.scaler0 GRing.scaler0 GRing.addr0.
Qed.

Lemma preimage_conv_linE (A: set F): subset A (range f) -> preimage f (conv A) = conv (preimage f A).
Proof.
rewrite eqEsubset; split.
   2: by apply preimset_conv_lin_sub.
move=> x [s [k [k1 [kx [k0 kA]]]]].
have: List.Forall (fun x => x \in range f) s.
   apply List.Forall_forall=>a /in_seqP /(nthP 0) [i ilt <-].
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
   rewrite GRing.linearD GRing.linearN.
   suff: f x = f (\sum_(i < size s') k i *: s'`_i) by move=>->; rewrite GRing.subrr.
   by rewrite -kx GRing.linear_sum; apply congr_big=>// [[t a]] _; rewrite GRing.linearZZ (nth_map 0).
by rewrite GRing.addrA [_+x]GRing.addrC -GRing.addrA GRing.subrr GRing.addr0.
Qed.

End C.


Section vect.

Variable R: realType.
Variable E: vectType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

(* TODO: excessivement immonde *)
Lemma caratheodory (A: set E) x: x \in conv A -> exists s: seq E, x \in conv (fun x => List.In x s) /\ (size s <= (dimv (@fullv R E)).+1)%N /\ List.Forall (fun x => x \in A) s.
Proof.
move=>/set_mem [s [k [k1 [kx [k0 kA]]]]]; subst x.
remember (size s) as n; symmetry in Heqn.
move: s Heqn k k1 k0 kA; induction n=>s ns k k1 k0 kA //.
   exists nil; split.
      by rewrite big_ord0; apply mem_set; exists nil, k; split=>//; split; [ by rewrite big_ord0 |]; split=>// i; inversion i; move: H; rewrite ltn0.
   by split; [ by rewrite leq0n |]; apply List.Forall_nil.
case nsgt: (size s <= (dimv (@fullv R E)).+1)%N.
   exists s; split.
      apply mem_set; exists s; rewrite ns; exists k; do 3 split=>//.
      by move=> i; apply mem_set; apply /in_seqP; apply mem_nth; rewrite ns.
   split=>//.
   by apply List.Forall_forall=>a /in_seqP /(nthP 0); rewrite ns=> [[i ilt <-]]; move: (kA (Ordinal ilt)).
have: exists mu: 'I_(size s) -> R, \sum_(i < size s) mu i = 0 /\ \sum_(i < size s) (mu i) *: s`_i = 0 /\ exists i, mu i <> 0.
   clear IHn.
   move: nsgt; rewrite ns ltnNge=>/negP/negP nsgt.
   destruct s as [| a s]=>//; inversion ns; subst n; clear ns.
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
      rewrite GRing.addrC; apply /eqP; rewrite GRing.subr_eq0; apply /eqP.
      apply congr_big=>// j _.
      by rewrite (unsplitK (inr _)).
   split.
      rewrite big_split_ord big_ord1 (unsplitK (inl _)) /= GRing.scaleNr GRing.addrC GRing.scaler_suml -GRing.sumrB -{3}musum.
      apply congr_big=>// j _.
      by rewrite (unsplitK (inr _)) (nth_map 0) // GRing.scalerBr.
   by exists (rshift 1 i); rewrite (unsplitK (inr _)); apply /eqP.
clear nsgt; rewrite ns; move=>[mu [muR [muE [i mui]]]].
wlog: mu muR muE mui / mu i > 0.
   move=> H.
   case mupos: (0 < mu i).
      by apply (H mu).
   apply (H (fun i => - mu i)).
      + by rewrite GRing.sumrN muR GRing.oppr0.
      + by rewrite -{3}GRing.oppr0 -{3}muE -GRing.sumrN; apply congr_big=>// j _; rewrite GRing.scaleNr.
      + by move=> /(f_equal (@GRing.opp R)); rewrite GRing.opprK GRing.oppr0.
      + move: mui=>/eqP; rewrite [mu i != 0]Num.Theory.real_neqr_lt. move=>/orP; case; [ by rewrite Num.Theory.oppr_gt0 | by rewrite mupos ].
         by apply Num.Theory.num_real.
         by apply Num.Theory.num_real.
move=>/(@Order.TotalTheory.arg_minP _ _ _ i (fun i => 0 < mu i) (fun i => (k i) / (mu i))) [im muip muim]; clear i mui.
wlog: s ns k k1 k0 kA mu muR muE im muip muim / (im == ord0)%N.
   set f := fun i: nat => if i == nat_of_ord im then 0%N else if i == 0%N then nat_of_ord im else i.
   have fcan: cancel f f.
      move=> j; unfold f.
      case jim: (j == im); case j0: (j == 0%N); case im0: (0%N == im); rewrite ?eq_refl; rewrite ?jim ?j0; move: jim j0 im0=>/eqP jim /eqP j0 /eqP im0; try subst j; try subst im =>//; try reflexivity; exact im0.
   have flt: forall i: 'I_n.+1, (f i < n.+1)%N by move=>[j jlt]; unfold f; case jim: (j == im); case j0: (j == 0%N).
   have fbij: bijective (fun i => Ordinal (flt i)) by exists (fun i => Ordinal (flt i)); move=> [j jlt]; apply ord_eq, fcan.
   move=>/(_ (mkseq (fun i => nth 0 s (f i)) n.+1)); rewrite size_mkseq=>/(_ Logic.eq_refl (fun i => k (Ordinal (flt i)))).
   have k1': \sum_i k (Ordinal (flt i)) = 1.
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      by rewrite big_map -k1; apply congr_big=>// [[j jlt]] _; f_equal; apply ord_eq, fcan.
   move=> /(_ k1').
   have k0': forall i : 'I_n.+1, 0 <= k (Ordinal (flt i)) by [].
   move=>/(_ k0').
   have kA': forall i : 'I_n.+1, (mkseq (fun i0 : nat => s`_(f i0)) n.+1)`_i \in A.
      by move=>j; rewrite nth_mkseq //; move: (kA (Ordinal (flt j))).
   move=>/(_ kA' (fun i => mu (Ordinal (flt i)))).
   have mu'R: \sum_(i0 < n.+1) mu (Ordinal (flt i0)) = 0.
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      by rewrite big_map -{4}muR; apply congr_big=>// [[j jlt]] _; f_equal; apply ord_eq, fcan.
   move=>/(_ mu'R).
   have mu'E: \sum_(i0 < n.+1) mu (Ordinal (flt i0)) *: (mkseq (fun i1 : nat => s`_(f i1)) n.+1)`_i0 = 0.
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      rewrite big_map -{6}muE; apply congr_big=>// [[j jlt]] _.
      rewrite nth_mkseq //; (do 2 f_equal); [ apply ord_eq |]; apply fcan.
   move=>/(_ mu'E (Ordinal (flt im))).
   have muip': 0 < mu (Ordinal (flt (Ordinal (flt im)))) by refine (eq_ind _ (fun x => 0 < x) muip _ _); f_equal; destruct im; apply ord_eq; symmetry; apply fcan.
   move=>/(_ muip').
   have muim': forall j : ordinal_finType n.+1,
  0 < mu (Ordinal (flt j)) ->
  k (Ordinal (flt (Ordinal (flt im)))) /
  mu (Ordinal (flt (Ordinal (flt im)))) <=
  k (Ordinal (flt j)) / mu (Ordinal (flt j)).
      move=>j mujp.
      refine (eq_ind _ (fun i => k i / mu i <= k (Ordinal (flt j)) / mu (Ordinal (flt j))) (muim _ mujp) _ _).
      destruct im; symmetry; apply ord_eq, fcan.
   move=>/(_ muim').
   have im0: Ordinal (flt im) == ord0.
      by apply /eqP; apply ord_eq; unfold f; rewrite eq_refl.
   move=>/(_ im0) [s' [s'conv [s'size s'A]]].
   exists s'; split=>//.
      refine (eq_ind _ (fun x => x \in conv ((List.In (A:=E))^~ s')) s'conv _ _).
      rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
      rewrite big_map; apply congr_big=>// [[j jlt]] _.
      rewrite nth_mkseq //.
      by do 2 f_equal; [ apply ord_eq |]; apply fcan.
move=>/eqP ime; subst im.
destruct s as [| a s ]=>//.
inversion ns; subst n; clear ns.
have leS: forall n m, (n <= m -> n < m.+1)%N by move=> n m; rewrite ltnS.
move: (IHn s Logic.eq_refl (fun i => k (lift ord0 i) - k ord0 / mu ord0 * mu (lift ord0 i))); clear IHn.
have mu0: mu ord0 != 0 by apply /eqP=>mu0; move: muip; rewrite mu0 Num.Theory.lt0r eq_refl.
have k0mu0: k ord0 / mu ord0 * mu ord0 = k ord0 by rewrite -{2}[mu ord0]GRing.divr1 GRing.mulf_div [_*1]GRing.mulrC -GRing.mulf_div GRing.divr1 GRing.mulfV // GRing.mulr1.
have k1': \sum_i (k (lift ord0 i) - k ord0 / mu ord0 * mu (lift ord0 i)) = 1
   by rewrite -[1]GRing.subr0 -{2}(GRing.mulr0 (k ord0 / mu ord0)) -k1 -{3}muR GRing.mulr_sumr -GRing.sumrB big_ord_recl k0mu0 GRing.subrr GRing.add0r; apply congr_big.
move=>/(_ k1').
have kp: forall i : 'I_(size s), 0 <= k (lift ord0 i) - k ord0 / mu ord0 * mu (lift ord0 i).
   move=>j; rewrite Num.Theory.subr_ge0.
   case mujp: (0 < mu (lift ord0 j)).
      by rewrite -Num.Theory.ler_pdivl_mulr //; apply muim.
   refine (Order.POrderTheory.le_trans _ (k0 (lift ord0 j))).
   apply Num.Theory.mulr_ge0_le0.
      apply Num.Theory.divr_ge0=>//.
      by move: muip; rewrite Num.Theory.lt0r=>/andP [_ ->].
   rewrite Num.Theory.real_leNgt.
      by rewrite mujp.
      by apply Num.Theory.num_real.
   by apply Num.Theory.num_real.
move=>/(_ kp).
have kA': forall i : 'I_(size s), s`_i \in A by move=>j; move: (kA (lift ord0 j)).
move=>/(_ kA') [s' [s'conv s'ok]].
exists s'; split=>//.
apply (eq_ind _ (fun x => x \in conv ((List.In (A:=E))^~ s')) s'conv).
by rewrite -[\sum_i k i *: (a :: s)`_i]GRing.subr0 -{5}(GRing.scaler0 _ (k ord0 / mu ord0)) -{5}muE GRing.scaler_sumr -GRing.sumrB big_ord_recl GRing.scalerA k0mu0 GRing.subrr GRing.add0r; apply congr_big=>// i _; rewrite GRing.scalerA GRing.scalerBl.
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
   rewrite -[kx i]GRing.mulr1 -ky1 GRing.mulr_sumr; apply congr_big=>// j _.
   by move: (unsplit_prodK (i, j))=>[-> ->].
split.
   transitivity (\sum_i (let (i0, j) := split_prod i in (kx i0 * ky j) *: sx`_i0, let (i0, j) := split_prod i in (kx i0 * ky j) *: sy`_j)).
      by apply congr_big=> // i _; rewrite (nth_allpairs _ 0 0); destruct split_prod.
   rewrite big_pair; apply pair_equal_spec; split; rewrite big_prod_ord.
      by apply congr_big=>// i _; rewrite -[kx i *: sx`_i]GRing.scale1r -ky1 GRing.scaler_suml; apply congr_big=>// j _; move: (unsplit_prodK (i, j))=>[-> ->]; rewrite GRing.mulrC GRing.scalerA.
   by rewrite -[\sum_(i < size sy) ky i *: sy`_i]GRing.scale1r -kx1 GRing.scaler_suml; apply congr_big=>// i _; rewrite GRing.scaler_sumr; apply congr_big=>// j _; move: (unsplit_prodK (i, j))=>[-> ->]; rewrite GRing.scalerA.
split=>i.
   by destruct split_prod; apply Num.Theory.mulr_ge0.
by rewrite (nth_allpairs _ 0 0); destruct split_prod; apply mem_set; split; apply set_mem=>/=.
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
have ne20: (2: R) != 0 by rewrite mulrz_neq0; apply /andP; split=>//; apply GRing.oner_neq0.
split.
   move=>xext u v uA vA xe.
   move: xext=>/set_mem /(_ u v uA vA).
   have xuv: x \in segment u v.
      apply mem_set; subst x; exists (1 / 2).
         apply /andP; split; rewrite bnd_simp.
            by rewrite GRing.div1r Num.Theory.invr_ge0 ler0z.
         rewrite Num.Theory.ler_pdivr_mulr.
            rewrite GRing.mul1r; apply ler1z.
         by rewrite ltr0z.
      by rewrite {3}(Num.Theory.splitr 1) -GRing.addrA GRing.subrr GRing.addr0 GRing.scalerDr.
   move: uA vA=>_ _ /(_ xuv); move: xuv=>_.
   wlog: u v xe / x = u.
      move=> h; case=> xe'.
         by apply h=>//; left.
      symmetry; apply h=>//.
         by rewrite GRing.addrC.
         by left.
      move: xe=> -> xu _.
      move: xu=>/(f_equal (fun x => 2 *: x));   rewrite GRing.scalerA -{1}[2]GRing.divr1 GRing.mulf_div GRing.mul1r GRing.mulr1 GRing.divff // GRing.scale1r.
   have ->: 2 = 1+1 by [].
   by rewrite GRing.scalerDl GRing.scale1r GRing.addrC; move=>/(f_equal (fun x => x-u)); do 2 rewrite -GRing.addrA GRing.subrr GRing.addr0.
split.
   move=>xext u v [uA ux] [vA vx] y yuv.
   split.
      by apply (Aconv _ _ uA vA).
   move: yuv=> [t t01 ye] /= yx; subst y x.
   have te: forall (t: R), 1 - (1-t) = t by move=>t'; rewrite GRing.opprB [t'-1]GRing.addrC GRing.addrA GRing.subrr GRing.add0r.
   have xe': forall (t: R) (u v: E), (1 - t) *: v + (1 - (1 - t)) *: u = t *: u + (1-t) *: v by move=>t' u' v'; rewrite GRing.addrC te.
   wlog: u v t xext xA uA ux vA vx t01 / 2*t <= 1.
      move=>h.
      case tle: (2*t <= 1).
         by apply (h u v t).
      apply (h v u (1-t)); rewrite ?xe'=>//.
         + move: t01=>/andP [t0 t1]; apply /andP; split; [ move: t1 | move: t0 ]; do 2 rewrite bnd_simp; [ move=>t1 | move=>t0 ].
            by rewrite Num.Theory.subr_ge0.
         by rewrite -Num.Theory.subr_ge0 te.
         + rewrite -Num.Theory.subr_ge0 GRing.mulrDr GRing.mulrN GRing.opprB [2*t-_]GRing.addrC GRing.addrA.
           have e2: 2 = 1+1 by [].
           rewrite {1}e2 GRing.mulr1 -{3}[1]GRing.opprK GRing.opprB GRing.addrA GRing.subrr GRing.add0r GRing.addrC Num.Theory.subr_ge0.
           by move: tle; rewrite Num.Theory.real_leNgt; (try apply Num.Theory.num_real)=> /negP /negP; rewrite -Num.Theory.subr_gt0 Num.Theory.lt0r=>/andP [_ tle']; rewrite -Num.Theory.subr_ge0.
   move=>tle.
   move: xext=>/(_ ((2*t) *: u + (1-2*t) *: v) v).
   have wA: (2 * t) *: u + (1 - 2 * t) *: v \in A.
      by apply mem_set, (Aconv _ _ uA vA); exists (2*t)=>//; apply /andP; split; rewrite bnd_simp //; move: t01=>/andP [t0 _]; apply Num.Theory.mulr_ge0=>//; rewrite ler0z.
   move: vA=>/mem_set vA /(_ wA vA).
   rewrite GRing.div1r GRing.scalerDr GRing.scalerDr GRing.scalerA GRing.mulrA GRing.scalerA [_*(_-_)]GRing.mulrDr -{1}GRing.mulrN GRing.mulrA GRing.mulr1 [2^-1+_]GRing.addrC [(_+2^-1)*:_]GRing.scalerDl -GRing.addrA -GRing.addrA -GRing.scalerDl -{3 4}[2^-1]GRing.mulr1 -GRing.mulrDr GRing.mulVf // GRing.mul1r GRing.mul1r -GRing.scalerDl [_+1]GRing.addrC.
   move=>/(_ Logic.eq_refl) /(f_equal (fun x => x-v)).
   rewrite [1-_]GRing.addrC GRing.scalerDl GRing.scale1r -GRing.addrA -GRing.addrA GRing.subrr GRing.addr0 GRing.scaleNr -GRing.scalerN-GRing.scalerDr.
   apply /eqP; rewrite GRing.scaler_eq0; apply /negP=>/orP; case.
      rewrite GRing.mulf_eq0=>/orP; case=> e0.
         by move: ne20; rewrite e0.
      move: e0 vx=>/eqP e0; subst t; apply=>/=.
      by rewrite GRing.scale0r GRing.add0r GRing.subr0 GRing.scale1r.
   rewrite GRing.Theory.subr_eq0=>/eqP uv; subst v.
   move: ux; apply=>/=.
   by rewrite -GRing.scalerDl [1-t]GRing.addrC GRing.addrA GRing.subrr GRing.add0r GRing.scale1r.
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
      have hf': forall x : E, x \in A -> GRing.comp_linear f (GRing.opp_linear E) x <= - a by move=>x xA /=; rewrite -GRing.scaleN1r GRing.linearZZ GRing.scaleN1r Num.Theory.ler_oppl GRing.opprK; apply hf.
      have hex': exists x : E, x \in A /\ GRing.comp_linear f (GRing.opp_linear E) x = - a.
         by move: hex=>[x [xA fx]]; exists x; split=>//=; rewrite -fx -GRing.scaleN1r GRing.linearZZ GRing.scaleN1r.
      move=>/(_ hex' (or_introl hf') hf') hface'.
      apply (eq_ind _ _ hface'); f_equal.
      by rewrite eqEsubset; split=>x /= /eqP; rewrite -GRing.scaleN1r GRing.linearZZ GRing.scaleN1r; [ rewrite GRing.eqr_opp | rewrite -GRing.eqr_opp ]=>/eqP.
   move=> hf; apply face'P; split; [ by apply subIsetl |]; split.
      apply convexI=>//; apply convex_convE; rewrite -preimage_conv_linE; f_equal.
         by apply (@convex_convE R (GRing.regular_lmodType R) [set a]%classic), convex1.
      by move: hex=> [x [xA fx]] b ->; exists x.
   move=> x u v /set_mem [xA xa] uA vA /set_mem [t t01 tx] xv; apply mem_set; (split; [ by apply set_mem |]); apply /eqP; rewrite -Order.POrderTheory.lte_anti; apply /andP; (split; [ by apply hf |]).
   have t0: t != 0.
      by apply /eqP=>t0; subst t; move: tx xv; rewrite GRing.scale0r GRing.add0r GRing.subr0 GRing.scale1r=>->; rewrite eq_refl.
   have tgt: 0 < t.
      by rewrite Num.Theory.lt0r t0=>/=; move: t01=>/andP [t0' _]; rewrite bnd_simp in t0'.
   move: tx=>/(f_equal (fun x=> t^-1 *: (x-(1-t)*: v))); rewrite -GRing.addrA GRing.subrr GRing.addr0 GRing.scalerA GRing.mulVf // GRing.scale1r=>->; rewrite GRing.linearZZ GRing.linearD xa -GRing.scaleNr GRing.linearZZ Num.Theory.ler_pdivl_mull // GRing.addrC -Num.Theory.subr_ge0 -GRing.addrA -GRing.mulNr -{1}[a]GRing.mul1r -GRing.mulrDl GRing.scaleNr -GRing.scalerN -GRing.mulrDr; apply Num.Theory.mulr_ge0.
      by rewrite Num.Theory.subr_ge0; move: t01=>/andP [_ /idP]; rewrite bnd_simp.
   by rewrite GRing.addrC Num.Internals.subr_ge0; apply hf.
have: forall x y, x \in A -> y \in A -> f x < a -> a < f y -> False.
move=> u v uA vA fua afv; move: hface=>/face'P [_ [_ /(_ ((f v - a)/(f v - f u) *: u + (a - f u)/(f v - f u) *: v) u v)]].
   move: (Order.POrderTheory.lt_trans fua afv); rewrite -Num.Theory.subr_gt0=>fufv.
   have inuv: ((f v - a) / (f v - f u)) *: u + ((a - f u) / (f v - f u)) *: v \in segment u v.
      apply mem_set; exists ((f v - a) / (f v - f u)).
         apply /andP; split; rewrite bnd_simp.
            by apply Num.Theory.divr_ge0; [ move: afv; rewrite -Num.Theory.subr_gt0 | move: fufv ]; rewrite Num.Theory.lt0r=>/andP [_ h].
         rewrite Num.Theory.ler_pdivr_mulr // GRing.mul1r; apply Num.Theory.ler_sub=>//.
         by rewrite -Num.Theory.subr_ge0; move: fua; rewrite -Num.Theory.subr_gt0 Num.Theory.lt0r=>/andP [_ h].
      do 2 f_equal.
      move: fufv; rewrite Num.Theory.lt0r=>/andP [fufv _].
      move: (GRing.oner_neq0 R)=>ne10.
      by rewrite -[1](GRing.divff fufv) -GRing.mulrBl; f_equal; rewrite GRing.opprB GRing.addrA GRing.addrC GRing.addrA GRing.addrA [-_+_]GRing.addrC GRing.subrr GRing.add0r GRing.addrC.
   have Aa: ((f v - a) / (f v - f u)) *: u + ((a - f u) / (f v - f u)) *: v \in (A `&` f @^-1` [set a])%classic.
      apply mem_set; split.
         by apply (Aconv u v); by apply set_mem. 
      move: fufv; rewrite Num.Theory.lt0r=>/andP [fufv _].
      by rewrite /= GRing.linearD GRing.linearZZ GRing.linearZZ [_*:_]GRing.mulrC [_*:_]GRing.mulrC GRing.mulrA GRing.mulrA -GRing.mulrDl GRing.addrC GRing.mulrBr GRing.mulrBr GRing.addrA -[_ - _ + _]GRing.addrA [-_+_]GRing.addrC [f u * _]GRing.mulrC GRing.subrr GRing.addr0 -GRing.mulrBl [_*a]GRing.mulrC -GRing.mulrA GRing.mulfV // GRing.mulr1.
   move=>/(_ Aa uA vA inuv).
   have nev: ((f v - a) / (f v - f u)) *: u + ((a - f u) / (f v - f u)) *: v != v.
      apply /eqP=>/(f_equal (fun x => (f v - f u) *: (x - ((a - f u) / (f v - f u)) *: v))).
      move: fufv; rewrite Num.Theory.lt0r=>/andP [fufv _].
      rewrite -GRing.addrA GRing.subrr GRing.addr0 GRing.scalerA GRing.mulrA [_*(_-_)]GRing.mulrC GRing.scalerBr GRing.scalerA GRing.mulrA [(_-_)*(a-_)]GRing.mulrC -GRing.mulrA -GRing.mulrA GRing.mulfV // GRing.mulr1 GRing.mulr1 -GRing.scalerBl GRing.opprB GRing.addrA -[_-_+_]GRing.addrA [-_+_]GRing.addrC GRing.subrr GRing.addr0=>/eqP; rewrite -GRing.subr_eq0 -GRing.scalerBr GRing.scaler_eq0=>/orP; case.
         by move=>fva; move: afv; rewrite -Num.Theory.subr_gt0 Num.Theory.lt0r fva.
      by rewrite GRing.Theory.subr_eq0; move=>/eqP uv; subst v; move: fufv; rewrite GRing.subrr eq_refl.
   by move=>/(_ nev) /set_mem [_ /= fuae]; move: fua; rewrite fuae -Num.Theory.subr_gt0 Num.Theory.lt0r GRing.subrr eq_refl.
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
         by rewrite Num.Theory.invr_ge0 ler0z le0z_nat.
      by rewrite Num.Theory.invf_le1 ?ler1z ?ltr0z.
   have ne20: (2: R) != 0 by rewrite mulrz_neq0; apply /andP; split=>//; apply GRing.oner_neq0.
   have->: 1-2^-1 = (2^-1: R) by apply (@GRing.scalerI R (GRing.regular_lmodType R) _ ne20); unfold GRing.scale=>/=; rewrite GRing.mulrBr GRing.divff // GRing.mulr1 -GRing.addrA GRing.subrr GRing.addr0.
   by rewrite GRing.scalerA GRing.scalerA GRing.mulVf // GRing.scale1r GRing.scale1r.
move=>x y xA yA z [t /andP]; (do 2 rewrite bnd_simp)=>[[t0 t1]] <-.
move: t0; rewrite Num.Theory.le0r=>/orP; case.
   by move=>/eqP ->; rewrite GRing.scale0r GRing.add0r GRing.subr0 GRing.scale1r.
move=>t0; move: t1; rewrite -Num.Theory.subr_ge0 Num.Theory.le0r=>/orP; case.
   by rewrite GRing.Theory.subr_eq0; move=>/eqP <-; rewrite GRing.subrr GRing.scale1r GRing.scale0r GRing.addr0.
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
rewrite GRing.scaler_sumr; exists y, s; exists (fun i => t * k i); split.
   by apply congr_big=>// i _; symmetry; apply GRing.scalerA.
split=>// i.
by apply Num.Theory.mulr_gt0.
Qed.

Lemma cone0_of_convE (A: set E): cone0_of A = [set t *: a | t in [set t | 0 < t] & a in (conv A)]%classic.
Proof.
rewrite eqEsubset; split=>x.
   move=>[y [s [k [<- [k0 kA]]]]]; set t := \sum_i k i.
   have k0': forall i : ordinal_finType (size (y :: s)), true -> 0 <= k i by move=>i _; apply Order.POrderTheory.ltW.
   have: 0 <= t by apply Num.Theory.sumr_ge0.
   rewrite Num.Theory.le0r=>/orP; case.
      by move=>/eqP /Num.Theory.psumr_eq0P; move=> /(_ k0') /(_ ord0 Logic.eq_refl) k00; exfalso; move: (k0 ord0); rewrite Num.Theory.lt0r k00 eq_refl.
   move=>t0; exists t=>//; exists (t^-1 *: \sum_i k i *: (y :: s)`_i).
      exists (y::s), (fun i => t^-1 * k i); split.
      by rewrite -GRing.Theory.mulr_sumr GRing.mulVf //; move: t0; rewrite Num.Theory.lt0r=>/andP[t0 _].
      split.
         by rewrite GRing.scaler_sumr; apply congr_big=>// i _; symmetry; apply GRing.scalerA.
      split=>// i; apply Num.Theory.mulr_ge0.
         2: by apply (k0' i).
      by rewrite Num.Theory.invr_ge0; apply Order.POrderTheory.ltW.
   rewrite GRing.scalerA GRing.divff.
      by apply GRing.scale1r.
   by move: t0; rewrite Num.Theory.lt0r=>/andP[t0 _].
move=>[t /= t0] [a [s [k [k1 [<- [k0 kA]]]]]] <-.
rewrite GRing.scaler_sumr (@mathcomp_extra.bigID_idem _ _ _ _ _ _ _ _ (fun i=> 0 < k i)); [| apply GRing.addrA | apply GRing.addrC | apply GRing.addr0 ].
have ->: \sum_(i < size s | true && ~~ (0 < k i)) t *: (k i *: s`_i) = \sum_(i < size s | true && ~~ (0 < k i)) 0 *: 0.
   apply congr_big=>// i /andP [_ ki0]; move: (k0 i); rewrite Order.POrderTheory.le_eqVlt=>/orP; case.
      by move=>/eqP <-; rewrite GRing.scale0r GRing.scale0r GRing.scaler0.
   by move=> ki0'; move:ki0; rewrite ki0'.
rewrite -[\sum_(_ < _ | _) 0 *: 0]GRing.scaler_sumr GRing.scale0r GRing.addr0 -big_filter /=.
remember [seq i <- index_enum (ordinal_finType (size s)) | 0 < k i] as I; symmetry in HeqI.
destruct I as [| i I].
exfalso; move: k1 (GRing.oner_neq0 R); rewrite (@mathcomp_extra.bigID_idem _ _ _ _ _ _ _ _ (fun i=> 0 < k i)); [| apply GRing.addrA | apply GRing.addrC | apply GRing.addr0 ]. rewrite -big_filter HeqI big_nil GRing.add0r=><- /eqP; apply. 
   transitivity (\sum_(i < size s | true && ~~ (0 < k i)) (0*0:R)).
      2: by rewrite -GRing.mulr_sumr GRing.mul0r.
   by apply congr_big=>// i /= kile; move: (k0 i); rewrite Num.Theory.le0r GRing.mul0r=>/orP; case=> [ /eqP // | kigt ]; move: kigt kile=>->.
have: subseq (i::I) (index_enum (ordinal_finType (size s))) by rewrite -HeqI; apply filter_subseq.
destruct s as [| b s].
   by inversion i.
move=> /subseq_incl; move=> /(_ ord0); rewrite size_index_enum card_ord; move=> [f [fn flt]].
unfold cone0_of.
exists (b::s)`_i, [seq (b::s)`_(nth i (i::I) (lift ord0 j)) | j <- index_enum (ordinal_finType (size I))].
rewrite /= size_map size_index_enum card_ord; exists (fun j => t * k (nth i (i::I) j)).
split.
   rewrite -{2}(map_nth_ord i (i :: I)) big_map.
   apply congr_big=>// j _; rewrite GRing.scalerA; f_equal.
   destruct j as [j jlt]; destruct j=>//=.
   move: jlt; rewrite ltnS=>jlt.
   rewrite (nth_map (Ordinal jlt)); do 3 f_equal.
      2: by rewrite size_index_enum card_ord.
   unfold index_enum; destruct index_enum_key=>/=; rewrite -enumT /=.
   have je: j = Ordinal jlt by [].
   by rewrite {2 3}je; rewrite nth_ord_enum.
split.
   move=> j; apply Num.Theory.mulr_gt0=>//; rewrite -HeqI.
   by apply (@nth_filter _ (fun i => 0 < k i)); rewrite HeqI.
move=> [j jlt]; destruct j=>//=.
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
unfold bezier, bezier_func.
by rewrite WfExtensionality.fix_sub_eq_ext.
Qed.

Lemma bezier_cons x y s t: bezier x (y :: s) t = (1-t) *: (bezier x (belast y s) t) + t *: (bezier y s t).
Proof.
unfold bezier, bezier_func.
by rewrite WfExtensionality.fix_sub_eq_ext.
Qed.

Lemma bezier0 x s: bezier x s 0 = x.
Proof.
remember (size s) as n; symmetry in Heqn.
move: s Heqn.
induction n.
   move=> s /size0nil ->; apply bezier_nil.
move=> s sn.
destruct s=>//.
rewrite bezier_cons GRing.subr0 GRing.scale1r GRing.scale0r GRing.addr0.
by apply IHn; rewrite size_belast; inversion sn.
Qed.

Lemma bezier1 x s: bezier x s 1 = last x s.
Proof.
remember (size s) as n; symmetry in Heqn.
move: x s Heqn.
induction n.
   by move=> x s /size0nil ->; apply bezier_nil.
move=> x s sn.
destruct s=>//.
rewrite bezier_cons GRing.subrr GRing.scale1r GRing.scale0r GRing.add0r /=.
by apply IHn; inversion sn.
Qed.

Lemma bezier_sub_conv x s: subset (bezier x s @` `[0, 1]) (Convex.conv (fun y => y \in (x :: s))).
Proof.
move=> y [t t01 <-].
remember (size s) as n; symmetry in Heqn.
move: s x Heqn; induction n.
   move=> s x /size0nil ->; rewrite bezier_nil.
   apply Convex.conv_ext.
   by rewrite inE; apply /eqP.
move=> s x sn.
destruct s as [| a s ]=>//; rewrite bezier_cons.
inversion sn.
have /Convex.conv_mono lsub: subset (fun y : E => y \in x :: belast a s) (fun y : E => y \in x :: a :: s) by move=> z; (do 2 rewrite in_cons)=>/orP; case=> [ -> // | /mem_belast -> ]; rewrite orbT.
have /(IHn _ x) /lsub l: size (belast a s) = n by rewrite size_belast.
have /Convex.conv_mono rsub: subset (fun y : E => y \in a :: s) (fun y : E => y \in x :: a :: s) by move=> z; (do 3 rewrite in_cons)=>/orP; case=>[ -> // | -> ]; rewrite orbT // orbT.
move: H0=>/(IHn _ a) /rsub r.
move: (@Convex.conv_convex _ _ (fun y : E => y \in x :: a :: s) (bezier x (belast a s) t) (bezier a s t) l r); apply.
exists (1-t).
   2: by rewrite -{2}[1]GRing.add0r GRing.addrKA GRing.opprK GRing.add0r.
apply /andP; move: t01=>/andP.
(repeat rewrite bnd_simp)=>[[t0 t1]]; split.
   by rewrite Num.Theory.subr_ge0.
rewrite Num.Theory.ler_subl_addl -{1}[1]GRing.add0r.
by apply Num.Theory.ler_add.
Qed.

End Bezier.
