From mathcomp Require Import all_ssreflect all_algebra vector reals classical_sets.
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

Definition conv (A: set E): set E := (fun s: seq (R * E) => \sum_(i <- s) (let (t, a) := i in t *: a)) @` (mkset (fun s: seq (R*E) => \sum_(i <- s) (let (t, _) := i in t) = 1 /\ List.Forall (fun x: R*E => let (t, a) := x in 0 <= t /\ a \in A) s)).

Lemma conv_ext (A: set E): subset A (conv A).
Proof.
move=> x Ax.
exists [:: (1, x)].
   2: by rewrite big_seq1 GRing.scale1r.
split.
   by rewrite big_seq1.
apply List.Forall_cons.
   2: by apply List.Forall_nil.
split.
   exact Num.Theory.ler01.
by apply mem_set.
Qed.

Lemma conv_sub_convex (A C: set E): subset A C -> convex C -> subset (conv A) C.
Proof.
move=>AsC Cc x [s [s1 sA] <-]; clear x.
remember (size s) as n; symmetry in Heqn.
move: s Heqn s1 sA; induction n=> s sn s1 sA.
   move: sn s1 (GRing.oner_neq0 R)=>/size0nil ->.
   by rewrite big_nil=>-> /eqP.
destruct s=>//.
destruct p as [t a].
rewrite big_cons.
inversion sA; subst l x.
move: sA H1 H2=> _ [t0 aA] sA.
move: s1; rewrite big_cons=>s1.
case t1: (0 < 1-t).
   apply (Cc a ((GRing.inv (1-t)) *: (\sum_(j <- s) (let (t2, a0) := j in t2 *: a0)))).
      by apply AsC; apply set_mem.
      2:{
      move: t1; rewrite Num.Theory.lt0r=>/andP [tn0 tge0].
      exists t.
         apply /andP; split; rewrite bnd_simp=>//.
         by rewrite -Num.Theory.subr_ge0.
      by f_equal; rewrite GRing.scalerA GRing.divff // GRing.scale1r.
      }
   rewrite GRing.scaler_sumr.
   move:IHn=>/(_ [seq (let (t', a) := i: R*E in (t' / (1-t), a)) | i <- s]).
   rewrite size_map; inversion sn=>/(_ Logic.eq_refl).
   rewrite big_map (congr_big s (fun _ => true) (fun i => (1-t)^-1 * (let (t', a) := i in t'))) //.
      2: by move=> [t' b] _; apply GRing.mulrC.
   rewrite -GRing.mulr_sumr GRing.mulrC.
   move: s1=>/(f_equal (fun u => u-t)); rewrite [t+_]GRing.addrC GRing.addrK=> ->.
   move: (t1); rewrite Num.Theory.lt0r=>/andP [tn0 tge0]=> /(_ (GRing.divff tn0)).
   rewrite big_map (congr_big s (fun _ => true) (fun i => (1-t)^-1 *: (let (t', a') := i in t' *: a'))) //.
      2: by move=> [t' a'] _; rewrite GRing.mulrC; rewrite GRing.scalerA.
   apply; apply List.Forall_forall=> [[t' a']] /List.in_map_iff [[t'' a'']] [t'a' tin]; inversion t'a'; subst t' a'.
   move: sA=>/List.Forall_forall /(_ (t'', a'') tin) [t''ge0 a''A].
   split=>//.
   by apply Num.Theory.divr_ge0.
clear n sn IHn Cc t0; move: t1=>/negP/negP; rewrite -Num.Theory.real_leNgt //.
   2, 3: by apply Num.Theory.num_real.
move=> t1.
have se: s = [seq (let (t, a) := i: R*E in (0, a)) | i <- s].
   clear C AsC a aA; induction s=>//=.
   destruct a; inversion sA; clear sA; subst x l.
   suff: (s0 == 0).
      move=>/eqP s00; subst s0; f_equal; apply IHs=>//.
      by move: s1; rewrite big_cons GRing.add0r.
      move: s1=> /(f_equal (fun u => u-t)); rewrite [t+_]GRing.addrC GRing.addrK big_cons=>s1.
   move: s1 t1 H1=><- s0le [s0ge _]; apply /eqP; apply Order.POrderTheory.le_anti; apply /andP; split=>//.
   clear IHs s0ge.
   rewrite -[s0]GRing.addr0; refine (Order.POrderTheory.le_trans _ s0le); apply Num.Theory.ler_add=>//.
   clear s0le; induction s.
      by rewrite big_nil.
   inversion H2; subst x l; destruct a; rewrite big_cons.
   apply Num.Theory.addr_ge0.
      by move: H1=>[s10 _].
   by apply IHs.
rewrite se big_map (congr_big s (fun _ => true) (fun _ => 0)) //.
   2: by move=> [t' a'] _; apply GRing.scale0r.
rewrite mathcomp_extra.big_const_idem; rewrite GRing.addr0 //.
move: s1; rewrite se big_map (congr_big s (fun _ => true) (fun _ => 0)) //.
   2: by move=> [t' a'] _.
rewrite mathcomp_extra.big_const_idem; rewrite GRing.addr0 // =>->; rewrite GRing.scale1r.
by apply AsC; apply set_mem.
Qed.

Lemma conv_segment (x y: E): segment x y = conv [set x; y].
Proof.
rewrite eqEsubset; split.
   move=> z [t /andP [t0 t1]] <-.
   rewrite bnd_simp in t0; rewrite bnd_simp in t1.
   exists [:: (t, x); (1-t, y)].
      2: by rewrite big_cons big_seq1. 
   split.
      by rewrite big_cons big_seq1 [1-t]GRing.addrC GRing.addrA GRing.subrr GRing.add0r.
   apply List.Forall_cons.
      by split=>//; apply mem_set; left.
   apply List.Forall_cons=>//.
   by split; [ rewrite Num.Theory.subr_ge0 | apply mem_set; right ].
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
move=> x y [sx [sx1 sxA] sxx] [sy [sy1 syA] syy] z [t /andP [t0 t1] <-].
rewrite bnd_simp in t0; rewrite bnd_simp in t1.
exists ([seq (let (u, a) := i: R*E in (t*u, a)) | i <- sx] ++ [seq (let (u, a) := i: R*E in ((1-t)*u, a)) | i <- sy]).
split.
   rewrite big_cat.
   rewrite big_map (congr_big sx (fun _ => true) (fun i => t * (let (u, a) := i in u))) //.
      2: by move=> [u a] _.
   rewrite -GRing.mulr_sumr sx1 big_map (congr_big sy (fun _ => true) (fun i => (1-t) * (let (u, a) := i in u))) //.
      2: by move=> [u a] _.
   rewrite -GRing.mulr_sumr sy1 GRing.mulr1 GRing.mulr1 GRing.addrC.
   have -> : GRing.add_monoid R t (- t + 1) = t + (-t+1) by lazy.
   by rewrite GRing.addrA GRing.subrr GRing.add0r.
   apply List.Forall_forall=> i iin.
   by move: (List.in_app_or _ _ _ iin); case; [ move: sxA | move: syA ] =>/List.Forall_forall sF /List.in_map_iff [[u a] [ie /sF [u0 ua]]]; subst i; split=>//; apply Num.Theory.mulr_ge0=>//; rewrite Num.Theory.subr_ge0.
rewrite big_cat.
rewrite big_map (congr_big sx (fun _ => true) (fun i => t *: (let (u, a) := i in u *: a))) //.
   2: by move=> [u a] _; rewrite GRing.scalerA.
rewrite -GRing.scaler_sumr sxx big_map (congr_big sy (fun _ => true) (fun i => (1-t) *: (let (u, a) := i in u *: a))) //.
   2: by move=> [u a] _; rewrite GRing.scalerA.
rewrite -GRing.scaler_sumr syy.
by lazy.
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

(* TODO: move to mathcomp *)

Lemma image2_subset {aT bT rT : Type} [f : aT -> bT -> rT] [A B: set aT] [C D : set bT]: (A `<=` B)%classic -> (C `<=` D)%classic -> ([set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D])%classic.
Proof.
by move=>AB CD x [a aA [c cC xe]]; subst x; exists a; (try by apply AB); exists c; (try by apply CD).
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
move=> x [a aA [b bA xe]]; subst x.
move: aA bA=>[sa [sa1 saA] ae] [sb [sb1 sbA] be]; subst a b.
exists ([seq (let (t, a) := i: R*E in let (u, b) := j: R*E in (t*u, a+b)) | i <- sa, j <- sb]).
   split.
      rewrite big_allpairs_dep -sa1.
      apply congr_big=>// [[t a]] _.
      rewrite -[t]GRing.mulr1 -{2}sb1 GRing.Theory.mulr_sumr.
      by apply congr_big=>// [[u b]] _; rewrite GRing.mulr1.
   apply List.Forall_forall=>x /List.in_concat[y [/List.in_map_iff [[t a] [ye tain]] xin]]; subst y; move: xin=>/List.in_map_iff [[u b] [xe ubin]]; subst x.
   move: saA sbA=>/List.Forall_forall /(_ _ tain) [t0 aA] /List.Forall_forall /(_ _ ubin) [u0 bA].
   split.
      by apply Num.Theory.mulr_ge0.
   by apply mem_set; exists a; (try by apply set_mem); exists b; (try by apply set_mem).
rewrite big_allpairs_dep (congr_big sa (fun _ => true) (fun i => (let (t, a) := i in t *: a) + (let (t, a) := i in t *: \sum_(j <- sb) (let (u, b) := j in u *: b)))) //.
   rewrite mathcomp_extra.big_split_idem //.
      2: by move=> x y z; move: (GRing.addrA x y z); lazy.
      2: by move=> x y; move: (GRing.addrC x y); lazy.
      2: by move: GRing.addr0=>/(_ E 0); lazy.
   rewrite [\big[GRing.add_monoid E/0]_(i <- sa) (let (t, _) := i in t *: (\sum_(j <- sb) (let (u, b) := j in u *: b)))](congr_big sa (fun _ => true) (fun i => (let (t, _) := i in t) *: (\sum_(j <- sb) (let (u, b) := j in u *: b)))) //.
      2: by move=>[t a] _.
   by rewrite -GRing.scaler_suml sa1 GRing.scale1r; lazy.
move=>[t a] _.
rewrite (congr_big sb (fun _ => true) (fun j => (let (u, b) := j in u) *: (t *: a) + t *: (let (u, b) := j in u *: b))) //.
   2: by move=> [u b] _; rewrite GRing.scalerA GRing.scalerA [u*t]GRing.mulrC GRing.scalerDr.
rewrite mathcomp_extra.big_split_idem //.
   2: by move=> x y z; move: (GRing.addrA x y z); lazy.
   2: by move=> x y; move: (GRing.addrC x y); lazy.
   2: by move: GRing.addr0=>/(_ E 0); lazy.
by rewrite -GRing.scaler_suml sb1 GRing.scale1r -GRing.scaler_sumr; lazy.
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
move=> tx [x xA txe]; subst tx.
move: xA=>[s [s1 sA] xe]; subst x; rewrite GRing.scaler_sumr.
exists [seq (let (u, a) := i: R*E in (u, t *: a)) | i <- s].
   2: by rewrite big_map; apply congr_big=> // [[u a]] _; rewrite GRing.scalerA GRing.scalerA GRing.mulrC.
split.
   by rewrite big_map -s1; apply congr_big=>// [[u a]] _.
apply List.Forall_forall=>x /List.in_map_iff [[u a] [xe uain]]; subst x.
move: sA=>/List.Forall_forall /(_ _ uain) [u0 aA].
by split=>//; apply mem_set; exists a=>//; apply set_mem.
Qed.

Lemma convexT: convex setT.
Proof. by []. Qed.

Lemma convex0: convex set0.
Proof. by []. Qed.

End C.

(*TODO: move to mathcomp.*)
Lemma lift_range {aT rT: Type} [f: aT -> rT] (s: seq rT): List.Forall (fun u => u \in range f) s -> exists s', map f s' = s.
Proof.
induction s.
   by exists nil.
move=> assub; inversion assub; clear assub; subst x l.
move: H1; lazy; destruct boolp.pselect=>// _; move: e=> [a' _ ae] ; subst a.
move: IHs=>/(_ H2) [s' se]; subst s.
by exists (a' :: s').
Qed.

Section C.
Variable R: realType.
Variable E F: lmodType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Variable f: {linear E -> F}.

Lemma imset_conv_lin (A: set E): image (conv A) f = conv (image A f). 
Proof.
rewrite eqEsubset; split.
   move=> x [y [s [s1 sA] ye] xe]; subst x y.
   rewrite GRing.raddf_sum (congr_big s (fun _ => true) (fun i => (let (t', a) := i in t' *: (f a)))) //.
      2: by move=> [u a] _; rewrite -GRing.linearZZ.
   exists [seq (let (u, a) := i: R*E in (u, f a)) | i <- s].
      2: by rewrite big_map; apply congr_big=>// [[u a] _].
   split.
      by rewrite big_map -s1; apply congr_big=>// [[u a] _].
   apply List.Forall_forall=>ua /List.in_map_iff [[u a] [uae uain]]; subst ua.
   move: sA=>/List.Forall_forall/(_ (u, a) uain) [u0 /set_mem aA]; split=>//.
   by apply mem_set; exists a.
apply conv_sub_convex.
   apply image_subset, conv_ext.
move=> fx fy [x xA fxe] [y yA fye] z [t t01] ze; subst fx fy z.
rewrite -GRing.linearZZ -GRing.linearZZ -GRing.raddfD.
exists (t *: x + (1-t) *: y)=>//.
by apply (conv_convex xA yA); exists t.
Qed.

Lemma preimset_conv_lin_sub (A: set F): subset (conv (preimage f A)) (preimage f (conv A)). 
Proof.
move=> x [s [s1 sA] xe]; subst x=>/=; rewrite GRing.raddf_sum.
exists [seq (let (t, a) := i: R*E in (t, f a)) | i <- s].
   2: by rewrite big_map; apply congr_big=>// [[t a]] _; rewrite -GRing.linearZZ.
split.
   by rewrite big_map -s1; apply congr_big=>// [[t a]] _.
apply List.Forall_forall=>x /List.in_map_iff [[t a] [xe tain]]; subst x.
by move: sA=>/List.Forall_forall /(_ _ tain).
Qed.

Lemma ker_convex: convex (preimage f [set 0]).
Proof.
move=> x y /= fx0 fy0 z [t t01 ze]; subst z=>/=.
by rewrite GRing.linearD GRing.linearZZ GRing.linearZZ fx0 fy0 GRing.scaler0 GRing.scaler0 GRing.addr0.
Qed.

(* TODO: move to mathcomp *)
Lemma preimage_add_ker (A: set F): ([set a + b | a in f @^-1` A & b in f @^-1` [set 0]] = f @^-1` A)%classic.
Proof.
rewrite eqEsubset; split.
   move=> x [a /= aA] [b /= bker] xe; subst x.
   by rewrite GRing.linearD bker GRing.addr0.
move=> x /= fx.
exists x=>//.
by exists 0; [ apply GRing.linear0 | apply GRing.addr0 ].
Qed.

Lemma preimage_conv_linE (A: set F): subset A (range f) -> preimage f (conv A) = conv (preimage f A).
Proof.
rewrite eqEsubset; split.
   2: by apply preimset_conv_lin_sub.
move=> x [s [s1 /List.Forall_forall sA] fxe].
have: List.Forall (fun x => x \in range (fun i => let (t, a) := i: R*E in (t, f a))) s.
   apply List.Forall_forall=>[[t a] /sA [t1 /set_mem /H [a' _ ae]]]; subst a.
   by apply mem_set; exists (t, a').
move=>/lift_range [s' se]; subst s.
rewrite -preimage_add_ker conv_add.
move: ker_convex=>/convex_convE <-.
exists (\sum_(i <- s') (let (t, a) := i in t *: a)).
   exists s'=>//.
   split.
      by rewrite -s1 big_map; apply congr_big=>// [[t a]] _.
   by apply List.Forall_forall=>[[t a]] /(List.in_map (fun i => let (t, a) := i: R*E in (t, f a))) /sA.
exists (x - \sum_(i <- s') (let (t, a) := i in t *: a))=>/=.
   rewrite GRing.linearD GRing.linearN.
   suff: f x = f (\sum_(i <- s') (let (t, a) := i in t *: a)) by move=>->; rewrite GRing.subrr.
   by rewrite -fxe GRing.linear_sum big_map; apply congr_big=>// [[t a]] _; rewrite GRing.linearZZ.
by rewrite GRing.addrA [_+x]GRing.addrC -GRing.addrA GRing.subrr GRing.addr0.
Qed.

End C.

Lemma index_enum_cast_ord n m (e: n = m): index_enum (ordinal_finType m) = [seq (cast_ord e i) | i <- index_enum (ordinal_finType n)].
Proof.
subst m.
rewrite -{1}(map_id (index_enum (ordinal_finType n))).
apply eq_map=>[[x xlt]].
unfold cast_ord; f_equal; apply bool_irrelevance.
Qed.

Section vect.

Variable R: realType.
Variable E: vectType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

(*TODO: move to mathcomp. *)
(*TODO: find a non-ugly proof. *)

Lemma freeN_combination n (s: n.-tuple E): ~free s -> exists k: 'I_n -> R, \sum_i k i *: s`_i = 0 /\ exists i, k i != 0.
Proof.
move=>/negP; rewrite freeNE=>/existsP [[i ilt] /coord_span /= sin].
move: (ilt) s sin; (have ne: (n = i.+1 + (n-i.+1))%N by rewrite subnKC); rewrite ne=> ilt' s sin.
simple refine (let k: 'I_(i.+1 + (n - i.+1)) -> R := _ in _).
   move=>/split; case=> [[j jlt] | [j jlt]].
      exact (if j == i then 1 else 0).
   refine (- (coord (drop_tuple i.+1 s) (@Ordinal _ j _) s`_i)).
   rewrite addnC -{3}[i.+1]/(0+i.+1)%N subnDr.
   by have->: (n-i.+1-0 = n-i.+1)%N by move: PeanoNat.Nat.sub_0_r.
simpl in k; exists k; split.
   2:{ exists (Ordinal ilt'); unfold k.
   move: (splitP (Ordinal ilt')).
   destruct (split _); move=>sp; inversion sp; subst o.
      by destruct j; move: H1=>/=->; rewrite eq_refl; apply GRing.oner_neq0.
   by move: H0; rewrite leqnn.
   }
rewrite big_split_ord big_ord_recr (congr_big (index_enum (ordinal_finType i)) (fun _ => true) (fun i => 0 *: 0)) //.
rewrite -GRing.scaler_suml GRing.scaler0.
   2:{ move=> [j jlt] _; unfold k.
   move: (splitP (lshift (n - i.+1) (widen_ord (leqnSn i) (Ordinal jlt)))).
   destruct split; move=>sp; inversion sp; subst o.
      destruct j0; move: H1=>/=<-.
      case ji: (j == i).
         by move: ji (jlt)=>/eqP ji; subst j; rewrite ltnn.
      by do 2 rewrite GRing.scale0r.
   by symmetry in H0; move: H0; rewrite ltnNge=>/negP/negP; rewrite ltnNge=>/negP jle; elim jle; apply ltnW.
   }
move: (splitP (lshift (n - i.+1) (@ord_max i))); unfold k at 1; destruct split; move=>sp; inversion sp; subst o.
   2: by move: H0; rewrite leqnn.
destruct j; move: H1=>/=<-; rewrite eq_refl.
clear m i0 sp H0.
rewrite GRing.add0r GRing.scale1r.
suff: \sum_(i1 < n - i.+1) k (rshift i.+1 i1) *: s`_(i.+1 + i1) = -s`_i
   by move=>->; apply GRing.subrr.
rewrite sin -GRing.sumrN.
have ne': (i.+1 + (n - i.+1) - i.+1 = n - i.+1)%N by rewrite -ne.
rewrite (index_enum_cast_ord ne') big_map; apply congr_big=>// [[x xlt]] _.
rewrite nth_drop -GRing.scaleNr; f_equal.
move: (splitP (rshift i.+1 (cast_ord ne' (Ordinal xlt)))); unfold k; destruct split; move=>sp; inversion sp; subst o.
   by move: H0; rewrite ltnNge leq_addr.
destruct k0; do 2 f_equal.
suff xm: x = m by subst m; f_equal; apply bool_irrelevance.
move: H1=>/= /(f_equal (fun x: nat => (x - i.+1)%N)).
have np0: forall n, (n = n + 0)%N by move=>a; rewrite addnC.
rewrite {2 4}(np0 i.+1) subnDl subnDl.
have n0: forall n: nat, (n-0 = n)%N.
   by move=>a; rewrite (np0 (a-0)%N); apply subnK.
by rewrite n0 n0.
Qed.

(*Lemma caratheodory (A: set E) x: x \in conv A -> exists s: seq E, x \in conv (fun x => List.In x s) /\ (size s <= (dimv (@fullv R E)).+1)%N /\ List.Forall (fun x => x \in A) s.
Proof.
move=>/set_mem [s [s0 /List.Forall_forall sA] xe]; subst x.
case ns: (size s <= (dimv (@fullv R E)).+1)%N.
   exists [seq (let (t, a) := i: R*E in a) | i <- s]; split.
      apply mem_set; exists s; split=>//.
      by apply List.Forall_forall=>[[t a]] tain; move: (tain)=> /sA [t1 _]; split=>//; apply mem_set; move: tain=>/(List.in_map (fun i => let (t, a) := i: R*E in a)).
   split.
      by rewrite size_map.
   by apply List.Forall_forall=>a /List.in_map_iff [[t b] [ae / sA [_ bA]]]; subst a.
remember (size s) as n; symmetry in Heqn.
move: s s0 sA Heqn ns; induction n=>s s0 sA ns // nsgt.
have: exists mu: 'I_(size s) -> R, \sum_(i < size s) mu i = 0 /\ \sum_(i < size s) (mu i) *: s`_i = 0 /\ exists i, mu i <> 0.
move: nsgt; rewrite ltnNge=>/negP/negP nsgt.
destruct s as [| [t a] s]=>//.
case sf: (free (in_tuple [seq (let (u, b) := i: R*E in b-a) | i <- s])).
   inversion ns.
   have: basis_of fullv (in_tuple [seq (let (u, b) := i: R*E in b-a) | i <- s]).
      rewrite basisEfree; apply /andP; split=>//; apply /andP; split.
         by apply subvf.
      rewrite size_map; rewrite H0.
      by refine (leq_trans _ nsgt).
   rewrite in_tupleE basisEdim size_map H0=>/andP [_ nsge].
   by move: nsgt; rewrite ltnNge nsge.
move: sf=>/negP /freeN_combination; rewrite in_tupleE size_map=> [[k [ksum [i ki]]]].
 *)


End vect.
   
End Convex.

(* TODO: move to another file *)
Require Import Coq.Program.Wf.

Section Bezier.

Variable R: realType.
Variable E: vectType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Program Fixpoint bezier (x: E) (s: seq E) (t: R) {measure (size s)}: E :=
  match s with
  | nil => x
  | y :: s => (1-t) *: (bezier x (belast y s) t) + t *: (bezier y s t)
  end.
Next Obligation.
Proof. by rewrite size_belast. Defined.

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
   by move=> s /size0nil ->.
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
   by move=> x s /size0nil ->.
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
   move=> s x /size0nil ->.
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

Print Convex.
