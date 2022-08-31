From mathcomp Require Import all_ssreflect all_algebra vector reals classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move to mathcomp *)

Lemma image2_subset {aT bT rT : Type} [f : aT -> bT -> rT] [A B: set aT] [C D : set bT]: (A `<=` B)%classic -> (C `<=` D)%classic -> ([set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D])%classic.
Proof.
by move=>AB CD x [a aA [c cC xe]]; subst x; exists a; (try by apply AB); exists c; (try by apply CD).
Qed.

Lemma ord_eq n i j (hi: (i < n)%N) (hj: (j < n)%N): i = j -> Ordinal hi = Ordinal hj.
Proof. by move=>ij; subst j; f_equal. Qed.

Lemma enum_rank_index {T: finType} i: nat_of_ord (enum_rank i) = index i (enum T).
Proof.
unfold enum_rank, enum_rank_in, insubd, odflt, oapp.
rewrite insubT.
   2: by lazy.
rewrite cardE index_mem.
destruct T, c, mixin.
unfold enum.
rewrite mem_filter.
by apply /andP; split.
Qed.

(* TODO: do we keep this as more newcomer friendly than having to look deep into the library ? *)
Lemma enum_prodE {T1 T2: finType}: enum (prod_finType T1 T2) = prod_enum T1 T2.
Proof. by rewrite enumT Finite.EnumDef.enumDef. Qed.

Lemma index_allpairs {T1 T2: eqType} (s1: seq T1) (s2: seq T2) x1 x2: x1 \in s1 -> x2 \in s2 -> index (x1, x2) [seq (x1, x2) | x1 <- s1, x2 <- s2] = ((index x1 s1) * (size s2) + index x2 s2)%N.
Proof.
move=>ins1 ins2.
induction s1=>//=.
rewrite index_cat.
case ax: (a == x1).
   move: ax=>/eqP ax; subst a; unfold muln, muln_rec, addn, addn_rec=>/=.
   move: ins2=>/(map_f (fun x => (x1, x))) ->.
   by apply index_map=> x y eq; inversion eq.
move: ins1; rewrite in_cons=>/orP; case=> [ /eqP xa | ins1 ].
   by subst a; move: ax; rewrite eq_refl.
case in12: ((x1, x2) \in [seq (a, x0) | x0 <- s2]).
   by move: in12=>/mapP [x xin xeq]; inversion xeq; subst a; move: ax; rewrite eq_refl.
by rewrite size_map (IHs1 ins1) addnA.
Qed.

Lemma enum_rank_prod {T T': finType} i j: (nat_of_ord (@enum_rank (prod_finType T T') (i, j)) = (enum_rank i) * #|T'| + enum_rank j)%N.
Proof.
do 3 rewrite enum_rank_index.
rewrite enumT Finite.EnumDef.enumDef cardE=>/=.
by apply index_allpairs; rewrite enumT.
Qed.

Lemma unsplit_prodp (m n: nat) (i: 'I_m) (j: 'I_n): (i*n+j < m*n)%N.
Proof.
rewrite -addnS.
apply (@leq_trans (i*n+n)%N).
   by rewrite leq_add2l.
rewrite addnC.
have->: (n+i*n = i.+1 * n)%N by unfold muln, muln_rec, addn, addn_rec.
by apply leq_mul.
Qed.

Definition unsplit_prod (m n: nat) (i:'I_m * 'I_n): 'I_(m*n) := let (i, j) := i in Ordinal (unsplit_prodp i j).

(* TODO: shall we extend the lemmas on Nat.div to divn ? *)
Definition split_prodpl (m n: nat) (i: 'I_(m*n)): (Nat.div i n < m)%N.
Proof.
destruct i.
destruct m.
   by exfalso; move: i; unfold muln, muln_rec=>/=; rewrite ltn0.
destruct n.
   by exfalso; move: i; rewrite mulnC; unfold muln, muln_rec=>/=; rewrite ltn0.
apply /leP; apply PeanoNat.Nat.div_lt_upper_bound=>//=.
by move: i; rewrite mulnC=>/leP.
Qed.

Definition split_prodpr (m n: nat) (i: 'I_(m*n)): (Nat.modulo i n < n)%N.
Proof.
destruct i.
destruct m.
   by exfalso; move: i; unfold muln, muln_rec=>/=; rewrite ltn0.
destruct n.
   by exfalso; move: i; rewrite mulnC; unfold muln, muln_rec=>/=; rewrite ltn0.
by apply /leP; apply PeanoNat.Nat.mod_upper_bound.
Qed.

Definition split_prod (m n: nat) (i: 'I_(m*n)): 'I_m * 'I_n := (Ordinal (split_prodpl i), Ordinal (split_prodpr i)).

(* TODO: find a suitable name *)
Lemma big_prod_ord [R' : Type] [idx : R'] (op : Monoid.com_law idx) [m n : nat] (P : pred 'I_(m * n)) (F : ordinal_finType (m * n) -> R'): \big[op/idx]_(i | P i) F i = \big[op/idx]_(i | true) \big[op/idx]_(j | P (unsplit_prod (i, j))) F (unsplit_prod (i, j)).
Proof.
induction m.
   by do 2 rewrite big_ord0.
rewrite big_ord_recl.
move: P F.
unfold muln, muln_rec=>/=.
fold muln_rec muln addn_rec addn=>P F.
rewrite big_split_ord; f_equal.
   apply congr_big=>// i.
      by f_equal; apply ord_eq.
   by move=>_; f_equal; apply ord_eq.
rewrite IHm; apply congr_big=>// i _.
have e: forall j, rshift n (unsplit_prod (i, j)) = Ordinal (unsplit_prodp (lift ord0 i) j).
   move=>j; f_equal; apply ord_eq=>/=.
   unfold bump; rewrite leq0n.
   by rewrite addnA.
by apply congr_big=>// [ j | j _ ]; f_equal.
Qed.

Lemma split_prodK (n m: nat): cancel (@split_prod n m) (@unsplit_prod n m).
Proof.
move=> [i ilt].
apply ord_eq=>/=.
rewrite mulnC; symmetry; unfold muln, muln_rec, addn, addn_rec.
by apply PeanoNat.Nat.div_mod_eq.
Qed.

Lemma unsplit_prodK (n m: nat): cancel (@unsplit_prod n m) (@split_prod n m).
Proof.
move=> [[i ilt] [j jlt]].
apply pair_equal_spec; split; apply ord_eq=>/=.
   unfold muln, muln_rec, addn, addn_rec.
   rewrite PeanoNat.Nat.div_add_l.
      2: by move=>m0; subst m; move: jlt; rewrite ltn0.
   rewrite PeanoNat.Nat.div_small.
      2: by apply /leP.
   by symmetry; apply plus_n_O.
rewrite addnC; unfold muln, muln_rec, addn, addn_rec.
rewrite PeanoNat.Nat.mod_add.
   2: by move=>m0; subst m; move: jlt; rewrite ltn0.
rewrite PeanoNat.Nat.mod_small=>//.
by apply /leP.
Qed.

Lemma nth_cat_ord [T : Type] (x0 : T) (s1 s2 : seq T) (i: 'I_(size s1 + size s2)): nth x0 (s1 ++ s2) i = match split i with inl i=> nth x0 s1 i | inr i=> nth x0 s2 i end.
Proof. by move: (nth_cat x0 s1 s2 i)=>->; unfold split; destruct (ltnP i (size s1)). Qed.

Lemma nth_allpairs [T1 T2 rT : Type] (f : T1 -> T2 -> rT) (s1: seq T1) (s2: seq T2) (x1: T1) (x2: T2) (x: rT) (i: 'I_(size s1 * size s2)): nth x (allpairs f s1 s2) i = let (i, j) := split_prod i in f (nth x1 s1 i) (nth x2 s2 j).
Proof.
induction s1=>/=.
   by exfalso; move: i; unfold muln, muln_rec=>/= i; inversion i; move: H; rewrite ltn0.
move: i=>/=; unfold muln, muln_rec=>/=; fold muln_rec; fold muln; fold addn_rec; fold addn.
have->: (size s2 + size s1 * size s2 = size (map (f a) s2) + size (allpairs f s1 s2))%N.
   rewrite size_map.
   by move: (allpairs_tupleP f (in_tuple s1) (in_tuple s2))=>/eqP->.
move=>i; rewrite nth_cat_ord.
rewrite -{2 3}[i]splitK.
unfold split; destruct ltnP=>/=.
   rewrite (set_nth_default (f a x2)) //.
   destruct i as [i ilt']; move: i0=>/=; rewrite size_map=> ilt.
   rewrite (nth_map x2) //.
   move: ilt=>/leP ilt.
   by rewrite PeanoNat.Nat.div_small // PeanoNat.Nat.mod_small.
move: i i0; rewrite size_map=>i i0.
have ilt: ((i - size s2) < size s1 * size s2)%N.
   move: (allpairs_tupleP f (in_tuple s1) (in_tuple s2))=>/eqP<-.
   apply (split_subproof i0).
rewrite (IHs1 (Ordinal ilt)); destruct i as [i ilt']=> /=.
rewrite addnC -{6 9}[size s2]mul1n PeanoNat.Nat.div_add ; fold addn_rec; fold addn.
rewrite addnC add1n PeanoNat.Nat.mod_add=>//.
   by move=> s20; move: ilt; rewrite /= s20 mulnC ltn0.
by move=> s20; move: ilt; rewrite /= s20 mulnC ltn0.
Qed.

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

(* TODO: move to mathcomp *)
Lemma preimage_add_ker (R: fieldType) (E F: lmodType R) (f: {linear E -> F}) (A: set F): ([set (a + b)%R | a in f @^-1` A & b in f @^-1` [set 0%R]] = f @^-1` A)%classic.
Proof.
rewrite eqEsubset; split.
   move=> x [a /= aA] [b /= bker] xe; subst x.
   by rewrite GRing.linearD bker GRing.addr0.
move=> x /= fx.
exists x=>//.
by exists 0%R; [ apply GRing.linear0 | apply GRing.addr0 ].
Qed.

Lemma in_seqP [T: eqType] (s: seq T) x: reflect (List.In x s) (x \in s).
Proof.
induction s; apply (iffP idP)=>//=; rewrite in_cons.
   by move=>/orP; case=>[ /eqP -> | /IHs h ]; [ left | right ].
by case=> [ -> | /IHs -> ]; rewrite ?eq_refl ?orbT.
Qed.


Lemma index_enum_cast_ord n m (e: n = m): index_enum (ordinal_finType m) = [seq (cast_ord e i) | i <- index_enum (ordinal_finType n)].
Proof.
subst m.
rewrite -{1}(map_id (index_enum (ordinal_finType n))).
apply eq_map=>[[x xlt]].
unfold cast_ord; f_equal; apply bool_irrelevance.
Qed.

Lemma perm_map_bij [T: finType] [f : T -> T] (s: seq T): bijective f -> perm_eq (index_enum T) [seq f i | i <- index_enum T].
Proof.
unfold index_enum; destruct index_enum_key=>/=.
move=>fbij.
unfold perm_eq.
rewrite -enumT -forallb_tnth; apply /forallP=>i /=.
inversion fbij.
rewrite enumT enumP count_map -size_filter (@eq_in_filter _ _ (pred1 (g (tnth
               (cat_tuple (enum_tuple T) (map_tuple [eta f] (enum_tuple T)))
               i)))).
   by rewrite size_filter enumP.
move=> x _ /=.
apply/eqP/eqP.
   by move=>/(f_equal g) <-.
by move=>->.
Qed.

(*TODO: move to mathcomp. *)
(*TODO: find a non-ugly proof. *)

Lemma freeN_combination (R: fieldType) (E: vectType R) n (s: n.-tuple E): ~free s -> exists k: 'I_n -> R, (\sum_i k i *: s`_i = 0)%R /\ exists i, k i != 0%R.
Proof.
move=>/negP; rewrite freeNE=>/existsP [[i ilt] /coord_span /= sin].
move: (ilt) s sin; (have ne: (n = i.+1 + (n-i.+1))%N by rewrite subnKC); rewrite ne=> ilt' s sin.
simple refine (let k: 'I_(i.+1 + (n - i.+1)) -> R := _ in _).
   move=>/split; case=> [[j jlt] | [j jlt]].
      exact (if j == i then 1%R else 0%R).
   refine (-%R (coord (drop_tuple i.+1 s) (@Ordinal _ j _) s`_i)).
   rewrite addnC -{3}[i.+1]/(0+i.+1)%N subnDr.
   by have->: (n-i.+1-0 = n-i.+1)%N by move: PeanoNat.Nat.sub_0_r.
simpl in k; exists k; split.
   2:{ exists (Ordinal ilt'); unfold k.
   move: (splitP (Ordinal ilt')).
   destruct (split _); move=>sp; inversion sp; subst o.
      by destruct j; move: H1=>/=->; rewrite eq_refl; apply GRing.oner_neq0.
   by move: H0; rewrite leqnn.
   }
rewrite big_split_ord big_ord_recr (congr_big (index_enum (ordinal_finType i)) (fun _ => true) (fun i => 0 *: 0)%R) //.
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
suff: (\sum_(i1 < n - i.+1) k (rshift i.+1 i1) *: s`_(i.+1 + i1) = - s`_i)%R
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

Lemma ord_S_split n (i: 'I_n.+1): {j: 'I_n | i = lift ord0 j} + {i = ord0}.
Proof.
destruct i as [i ilt]; destruct i.
   by right; apply ord_eq.
by left; exists (Ordinal (ltnSE ilt)); apply ord_eq.
Qed.

Lemma subseq_incl (T: eqType) (s s': seq T) x: subseq s s' -> {f: 'I_(size s) -> 'I_(size s') | (forall i, nth x s' (f i) = nth x s i) /\ {homo f : y x / (x < y)%O >-> (x < y)%O}}.
Proof.
move: s; induction s'=>s sub.
   by move:sub=>/eqP -> /=; exists id; split=>// i j.
destruct s as [| b s].
   move=>/=; simple refine (exist _ _ _).
      by move=> i; destruct i.
   by split; move=> i; destruct i.
move: sub=>/=; case sa: (b == a).
   move: sa=>/eqP <- /IHs' [f [fn flt]].
   exists (fun i => match ord_S_split i with | inleft j => lift ord0 (f (proj1_sig j)) | inright _ => ord0 end).
   split.
      by move=> i; destruct ord_S_split as [ [j ie] | ie ]; subst i=>/=.
   move=> i j; destruct ord_S_split as [ [i' ie] | ie ]; destruct ord_S_split as [ [j' je] | je ]; subst i j=>//=.
   do 2 rewrite ltEord=>/=.
   by unfold bump=>/=; (do 4 rewrite add1n); do 2 rewrite ltnS; apply flt.
by move=>/IHs' [f [fn flt]]; exists (fun i => lift ord0 (f i)).
Qed.

Lemma hom_lt_inj {disp disp' : unit} {T : orderType disp} {T' : porderType disp'} [f : T -> T']: {homo f : x y / (x < y)%O >-> (x < y)%O} -> injective f.
Proof.
move=>flt i j.
move: (Order.TotalTheory.le_total i j).
wlog: i j / (i <= j)%O.
   move=>h /orP; case=>le fij.
      by apply (h i j)=>//; rewrite le.
   by symmetry; apply (h j i)=>//; rewrite le.
rewrite Order.POrderTheory.le_eqVlt=>/orP; case=> [ /eqP ij | /flt fij ]=>// _ fije.
by move: fij; rewrite fije Order.POrderTheory.lt_irreflexive.
Qed.

Lemma size_index_enum (T: finType): size (index_enum T) = #|T|.
Proof.
unfold index_enum; destruct index_enum_key=>/=.
by rewrite -enumT cardT.
Qed.

Lemma map_map [T0 T1 T2: Type] (s: seq T0) (f: T0 -> T1) (g: T1 -> T2): [seq g j | j <- [seq f i | i <- s]] = [seq (g (f i)) | i <- s].
Proof. by induction s=>//=; f_equal. Qed.

Lemma eq_fun_map [T1 T2 : eqType] (f g : T1 -> T2) [s : seq T1]: (forall x, f x = g x) -> [seq f i | i <- s] = [seq g i | i <- s].
Proof. by move=>fg; induction s=>//=; f_equal. Qed.

Lemma map_nth_ord [T : Type] (x: T) (s : seq T): [seq nth x s (nat_of_ord i) | i <- index_enum (ordinal_finType (size s))] = s.
Proof.
unfold index_enum; destruct index_enum_key=>/=; rewrite -enumT.
induction s=>//=.
   by destruct (enum 'I_0) as [| s q]=>//; inversion s.
   by rewrite enum_ordSl /= map_map /=; f_equal.
Qed.

Lemma nth_filter [T : Type] (P: {pred T}) x (s: seq T) n: (n < size [seq i <- s | P i])%N -> P (nth x [seq i <- s | P i] n).
Proof.
move: n; induction s=> n //=.
case Pa: (P a).
   2: by apply IHs.
by destruct n=>//=; rewrite ltnS; apply IHs.
Qed.

Lemma big_pair [R : Type] (idr : R) (opr : R -> R -> R) [S : Type] (ids : S) (ops : S -> S -> S) [I : Type] 
  (r : seq I) (F : I -> R) (G: I -> S): \big[(fun (x y: R*S)=> (opr x.1 y.1, ops x.2 y.2))/(idr, ids)]_(i <- r) (F i, G i) = (\big[opr/idr]_(i <- r) F i, \big[ops/ids]_(i <- r) G i).
Proof.
induction r.
   by do 3 rewrite big_nil.
by do 3 rewrite big_cons; rewrite IHr.
Qed.

