From mathcomp Require Import all_ssreflect all_algebra vector reals classical_sets.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move to mathcomp ? *)

Lemma image2_subset {aT bT rT : Type} [f : aT -> bT -> rT] [A B: set aT] [C D : set bT]: (A `<=` B)%classic -> (C `<=` D)%classic -> ([set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D])%classic.
Proof.
by move=>AB CD x [a aA [c cC xe]]; subst x; exists a; (try by apply AB); exists c; (try by apply CD).
Qed.

Lemma enum_rank_index {T: finType} i: nat_of_ord (enum_rank i) = index i (enum T).
Proof.
rewrite /enum_rank /enum_rank_in /insubd /odflt /oapp insubT.
   2: by lazy.
rewrite cardE index_mem.
destruct T, c, mixin.
rewrite /(enum _) mem_filter.
by apply /andP; split.
Qed.

(* TODO: do we keep this as more newcomer friendly than having to look deep into the library ? *)
Lemma enum_prodE {T1 T2: finType}: enum (prod_finType T1 T2) = prod_enum T1 T2.
Proof. by rewrite enumT Finite.EnumDef.enumDef. Qed.

Lemma index_allpairs {T1 T2: eqType} (s1: seq T1) (s2: seq T2) x1 x2: x1 \in s1 -> x2 \in s2 -> index (x1, x2) [seq (x1, x2) | x1 <- s1, x2 <- s2] = ((index x1 s1) * (size s2) + index x2 s2)%N.
Proof.
move=>ins1 ins2.
elim: s1 ins1=>//= a s1 IHs1 ins1.
rewrite index_cat.
case ax: (a == x1).
   move: ax=>/eqP ax; subst a; rewrite /muln /muln_rec /addn /addn_rec /=.
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
have->: (n+i*n = i.+1 * n)%N by rewrite /muln /muln_rec /addn /addn_rec.
by apply leq_mul.
Qed.

Definition unsplit_prod (m n: nat) (i:'I_m * 'I_n): 'I_(m*n) := let (i, j) := i in Ordinal (unsplit_prodp i j).

(* TODO: shall we extend the lemmas on Nat.div to divn ? *)
Definition split_prodpl (m n: nat) (i: 'I_(m*n)): (Nat.div i n < m)%N.
Proof.
case: i=>[i ilt].
case: m ilt=>[| m] ilt.
   by exfalso; move: ilt; rewrite /muln /muln_rec ltn0.
case: n ilt=>[| n] ilt.
   by exfalso; move: ilt; rewrite mulnC /muln /muln_rec ltn0.
apply /leP; apply PeanoNat.Nat.div_lt_upper_bound=>//=.
by move: ilt; rewrite mulnC=>/leP.
Qed.

Definition split_prodpr (m n: nat) (i: 'I_(m*n)): (Nat.modulo i n < n)%N.
Proof.
case: i=>[i ilt].
case: m ilt=>[| m] ilt.
   by exfalso; move: ilt; rewrite /muln /muln_rec ltn0.
case: n ilt=>[| n] ilt.
   by exfalso; move: ilt; rewrite mulnC /muln /muln_rec ltn0.
by apply /leP; apply PeanoNat.Nat.mod_upper_bound.
Qed.

Definition split_prod (m n: nat) (i: 'I_(m*n)): 'I_m * 'I_n := (Ordinal (split_prodpl i), Ordinal (split_prodpr i)).

(* TODO: find a suitable name *)
Lemma big_prod_ord [R' : Type] [idx : R'] (op : Monoid.com_law idx) [m n : nat] (P : pred 'I_(m * n)) (F : ordinal_finType (m * n) -> R'): \big[op/idx]_(i | P i) F i = \big[op/idx]_(i | true) \big[op/idx]_(j | P (unsplit_prod (i, j))) F (unsplit_prod (i, j)).
Proof.
elim: m P F=>[| m IHm] P F.
   by do 2 rewrite big_ord0.
rewrite big_ord_recl.
move: P F.
rewrite /muln /muln_rec /= -/muln_rec -/muln -/addn_rec -/addn=>P F.
rewrite big_split_ord. congr (_ _ _).
   apply congr_big=>// i.
      by congr P; apply val_inj.
   by move=>_; congr F; apply val_inj.
rewrite IHm; apply congr_big=>// i _.
have e: forall j, rshift n (unsplit_prod (i, j)) = Ordinal (unsplit_prodp (lift ord0 i) j).
   move=>j; apply val_inj=>/=.
   rewrite /bump leq0n.
   by rewrite addnA.
by apply congr_big=>// [ j | j _ ]; f_equal.
Qed.

Lemma split_prodK (n m: nat): cancel (@split_prod n m) (@unsplit_prod n m).
Proof.
move=> [i ilt].
apply val_inj=>/=.
apply/esym; rewrite mulnC /muln /muln_rec /addn /addn_rec.
by apply PeanoNat.Nat.div_mod_eq.
Qed.

Lemma unsplit_prodK (n m: nat): cancel (@unsplit_prod n m) (@split_prod n m).
Proof.
move=> [[i ilt] [j jlt]].
apply pair_equal_spec; split; apply val_inj=>/=.
   rewrite /muln /muln_rec /addn /addn_rec PeanoNat.Nat.div_add_l.
      2: by move=>m0; subst m; move: jlt; rewrite ltn0.
   rewrite PeanoNat.Nat.div_small.
      2: by apply /leP.
   by apply/esym; apply plus_n_O.
rewrite addnC /muln /muln_rec /addn /addn_rec PeanoNat.Nat.mod_add.
   2: by move=>m0; subst m; move: jlt; rewrite ltn0.
rewrite PeanoNat.Nat.mod_small=>//.
by apply /leP.
Qed.

Lemma nth_cat_ord [T : Type] (x0 : T) (s1 s2 : seq T) (i: 'I_(size s1 + size s2)): nth x0 (s1 ++ s2) i = match split i with inl i=> nth x0 s1 i | inr i=> nth x0 s2 i end.
Proof. by move: (nth_cat x0 s1 s2 i)=>->; rewrite /split; case: (ltnP i (size s1)). Qed.

Lemma nth_allpairs [T1 T2 rT : Type] (f : T1 -> T2 -> rT) (s1: seq T1) (s2: seq T2) (x1: T1) (x2: T2) (x: rT) (i: 'I_(size s1 * size s2)): nth x (allpairs f s1 s2) i = let (i, j) := split_prod i in f (nth x1 s1 i) (nth x2 s2 j).
Proof.
elim: s1 i=>/= [| a s1 IHs1] i.
   by exfalso; move: i=>[i ilt]; move: ilt; rewrite /muln /muln_rec /= ltn0.
move: i; rewrite /muln /muln_rec /= -/muln_rec -/muln -/addn_rec -/addn.
have->: (size s2 + size s1 * size s2 = size (map (f a) s2) + size (allpairs f s1 s2))%N.
   rewrite size_map.
   by move: (allpairs_tupleP f (in_tuple s1) (in_tuple s2))=>/eqP->.
move=>i; rewrite nth_cat_ord.
rewrite -{2 3}[i]splitK.
rewrite /split; case: ltnP=>/= i0.
   rewrite (set_nth_default (f a x2)) //.
   case: i i0=> [i ilt'] /=; rewrite size_map=> ilt.
   rewrite (nth_map x2) //.
   move: ilt=>/leP ilt.
   by rewrite PeanoNat.Nat.div_small // PeanoNat.Nat.mod_small.
move: i i0; rewrite size_map=> [[i ilt']] i0.
have ilt: ((i - size s2) < size s1 * size s2)%N.
   move: (allpairs_tupleP f (in_tuple s1) (in_tuple s2))=>/eqP<-.
   apply (split_subproof i0).
rewrite (IHs1 (Ordinal ilt))=> /=.
rewrite addnC -{6 9}[size s2]mul1n PeanoNat.Nat.div_add ; fold addn_rec; fold addn.
rewrite addnC add1n PeanoNat.Nat.mod_add=>//.
   by move=> s20; move: ilt; rewrite /= s20 mulnC ltn0.
by move=> s20; move: ilt; rewrite /= s20 mulnC ltn0.
Qed.

(*TODO: move to mathcomp.*)
Lemma lift_range {aT rT: Type} [f: aT -> rT] (s: seq rT): all (fun u => u \in range f) s -> exists s', map f s' = s.
Proof.
elim: s=>[| a s IHs].
   by exists nil.
move=> /andP [/set_mem [a' _ ae] /IHs [s' se]]; subst a s.
by exists (a' :: s').
Qed.

(* TODO: move to mathcomp *)
Lemma preimage_add_ker (R: fieldType) (E F: lmodType R) (f: {linear E -> F}) (A: set F): ([set (a + b)%R | a in f @^-1` A & b in f @^-1` [set 0%R]] = f @^-1` A)%classic.
Proof.
rewrite eqEsubset; split.
   move=> x [a /= aA] [b /= bker] xe; subst x.
   by rewrite linearD bker addr0.
move=> x /= fx.
exists x=>//.
by exists 0%R; [ apply linear0 | apply addr0 ].
Qed.

Lemma index_enum_cast_ord n m (e: n = m): index_enum (ordinal_finType m) = [seq (cast_ord e i) | i <- index_enum (ordinal_finType n)].
Proof.
subst m.
rewrite -{1}(map_id (index_enum (ordinal_finType n))).
apply eq_map=>[[x xlt]].
rewrite /cast_ord; congr Ordinal; apply bool_irrelevance.
Qed.

Lemma perm_map_bij [T: finType] [f : T -> T] (s: seq T): bijective f -> perm_eq (index_enum T) [seq f i | i <- index_enum T].
Proof.
rewrite /index_enum; case: index_enum_key=>/=.
move=>fbij.
rewrite /perm_eq -enumT -forallb_tnth; apply /forallP=>i /=.
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
   2:{ exists (Ordinal ilt'); rewrite /k.
   move: (splitP (Ordinal ilt')).
   case: (split _)=>o sp; inversion sp; subst o.
      by case: j H1 {sp}=> j jlt /= ->; rewrite eq_refl; apply oner_neq0.
   by move: H0; rewrite leqnn.
   }
rewrite big_split_ord big_ord_recr (congr_big (index_enum (ordinal_finType i)) (fun _ => true) (fun i => 0 *: 0)%R) //.
rewrite -scaler_suml scaler0.
   2:{ move=> [j jlt] _; rewrite /k.
   move: (splitP (lshift (n - i.+1) (widen_ord (leqnSn i) (Ordinal jlt)))).
   case split=>o; move=>sp; inversion sp; subst o.
      case: j0 H1 {sp}=> j0 j0lt /=<-.
      case ji: (j == i).
         by move: ji (jlt)=>/eqP ji; subst j; rewrite ltnn.
      by do 2 rewrite scale0r.
   by move: H0=>/esym; rewrite ltnNge=>/negP/negP; rewrite ltnNge=>/negP jle; elim jle; apply ltnW.
   }
move: (splitP (lshift (n - i.+1) (@ord_max i))); rewrite {1}/k; case split=>o sp; inversion sp; subst o.
   2: by move: H0; rewrite leqnn.
case: j H1 {sp}=> j jlt /=<-; rewrite eq_refl.
clear j jlt H0.
rewrite add0r scale1r.
suff: (\sum_(i1 < n - i.+1) k (rshift i.+1 i1) *: s`_(i.+1 + i1) = - s`_i)%R
   by move=>->; apply subrr.
rewrite sin -sumrN.
have ne': (i.+1 + (n - i.+1) - i.+1 = n - i.+1)%N by rewrite -ne.
rewrite (index_enum_cast_ord ne') big_map; apply congr_big=>// [[x xlt]] _.
rewrite nth_drop -scaleNr; congr (_ *: _).
move: (splitP (rshift i.+1 (cast_ord ne' (Ordinal xlt)))); rewrite /k; case: split=>o sp; inversion sp; subst o.
   by move: H0; rewrite ltnNge leq_addr.
case: k0 H1 sp=>k0 k0lt H1 sp; congr (- coord _ _ _).
apply val_inj=>/=; apply /esym.
move: H1=>/= /(f_equal (fun x: nat => (x - i.+1)%N)).
have np0: forall n, (n = n + 0)%N by move=>a; rewrite addnC.
rewrite {2 4}(np0 i.+1) subnDl subnDl.
have n0: forall n: nat, (n-0 = n)%N.
   by move=>a; rewrite (np0 (a-0)%N); apply subnK.
by rewrite n0 n0.
Qed.

Lemma ord_S_split n (i: 'I_n.+1): {j: 'I_n | i = lift ord0 j} + {i = ord0}.
Proof.
case: i; case=>[| i] ilt.
   by right; apply val_inj.
by left; exists (Ordinal (ltnSE ilt)); apply val_inj.
Qed.

Lemma subseq_incl (T: eqType) (s s': seq T) x: subseq s s' -> {f: 'I_(size s) -> 'I_(size s') | (forall i, nth x s' (f i) = nth x s i) /\ {homo f : y x / (x < y)%O >-> (x < y)%O}}.
Proof.
elim: s' s=> [| a s' IHs'] s sub.
   by move:sub=>/eqP -> /=; exists id; split=>// i j.
case: s sub=> [ _ | b s sub].
   move=>/=; simple refine (exist _ _ _).
      by move=> i; case: i.
   by split; move=> i; case: i.
move: sub=>/=; case sa: (b == a).
   move: sa=>/eqP <- /IHs' [f [fn flt]].
   exists (fun i => match ord_S_split i with | inleft j => lift ord0 (f (proj1_sig j)) | inright _ => ord0 end).
   split.
      by move=> i; case: ord_S_split=> [ [j ie] | ie ]; subst i=>/=.
   move=> i j; case: ord_S_split=> [ [i' ie] | ie ]; case: ord_S_split=> [ [j' je] | je ]; subst i j=>//=.
   do 2 rewrite ltEord=>/=.
   by rewrite /bump /= add1n add1n add1n add1n ltnS ltnS; apply flt.
by move=>/IHs' [f [fn flt]]; exists (fun i => lift ord0 (f i)).
Qed.

Lemma hom_lt_inj {disp disp' : unit} {T : orderType disp} {T' : porderType disp'} [f : T -> T']: {homo f : x y / (x < y)%O >-> (x < y)%O} -> injective f.
Proof.
move=>flt i j.
move: (Order.TotalTheory.le_total i j).
wlog: i j / (i <= j)%O.
   move=>h /orP; case=>le fij.
      by apply (h i j)=>//; rewrite le.
   by apply/esym; apply (h j i)=>//; rewrite le.
rewrite Order.POrderTheory.le_eqVlt=>/orP; case=> [ /eqP ij | /flt fij ]=>// _ fije.
by move: fij; rewrite fije Order.POrderTheory.lt_irreflexive.
Qed.

Lemma size_index_enum (T: finType): size (index_enum T) = #|T|.
Proof. by rewrite cardT enumT. Qed.

Lemma map_nth_ord [T : Type] (x: T) (s : seq T): [seq nth x s (nat_of_ord i) | i <- index_enum (ordinal_finType (size s))] = s.
Proof.
rewrite /index_enum; case: index_enum_key=>/=; rewrite -enumT.
elim: s=>/= [| a s IHs].
   by case: (enum 'I_0)=> [| s q] //; inversion s.
by rewrite enum_ordSl /= -map_comp /=; congr cons.
Qed.

Lemma nth_filter [T : Type] (P: {pred T}) x (s: seq T) n: (n < size [seq i <- s | P i])%N -> P (nth x [seq i <- s | P i] n).
Proof.
elim: s n=> [| a s IHs] n //=.
case Pa: (P a).
   2: by apply IHs.
by case: n=>//=; rewrite ltnS; apply IHs.
Qed.

Lemma big_pair [R : Type] (idr : R) (opr : R -> R -> R) [S : Type] (ids : S) (ops : S -> S -> S) [I : Type] 
  (r : seq I) (F : I -> R) (G: I -> S): \big[(fun (x y: R*S)=> (opr x.1 y.1, ops x.2 y.2))/(idr, ids)]_(i <- r) (F i, G i) = (\big[opr/idr]_(i <- r) F i, \big[ops/ids]_(i <- r) G i).
Proof.
elim: r=>[| a r IHr].
   by do 3 rewrite big_nil.
by do 3 rewrite big_cons; rewrite IHr.
Qed.

(* TODO: takes forever to compile. *)
From mathcomp Require Import ereal.
Local Open Scope ereal_scope.

Ltac case_ereal x :=
  let H0 := fresh "x_eq_0" in
  let He0 := fresh "Heqx_eq_0" in
  let Hgt := fresh "x_gt_0" in
  let Hegt := fresh "Heqx_gt_0" in
  let Heqlt := fresh "Heqx_lt_0" in
  case: x=> [ x | |];
      [ remember (x%:E == 0) as H0; case: H0 He0=>/esym He0;
      [| remember (0 < x%:E) as Hgt; case: Hgt Hegt=>/esym Hegt;
          [| (have /Order.TotalTheory.lt_total: (x%:E != 0) by apply /negP; rewrite He0); rewrite Hegt orbF=>Heqlt ]] | |].

Lemma muleA (R: realDomainType) (a b c: \bar R): a * (b * c) = a * b * c.
Proof.
rewrite /mule /mule_subdef.
case_ereal a; case_ereal b; case_ereal c; (try by (congr (_%:E); apply mulrA)); rewrite ?(mule_eq0 a%:E b%:E) ?Heqx_eq_0 ?Heqx_eq_1 ?Heqx_eq2 //= ?mulr0 // ?mul0r // ?eq_refl ?lt0y // ?(mule_eq0 a%:E b%:E) ?(mule_eq0 b%:E c%:E) ?Heqx_eq_0 ?Heqx_eq_1 ?orbT ?orbF // ?(mule_gt0 Heqx_gt_0 Heqx_gt_1) //.
   1, 2: by rewrite mulrC (pmule_lgt0 b%:E Heqx_gt_0) Heqx_gt_1.
   1, 2: by rewrite (pmule_lgt0 a%:E Heqx_gt_1) Heqx_gt_0.
   1, 2: by rewrite (mule_lt0_lt0 Heqx_lt_0 Heqx_lt_1).
   1, 4: by rewrite mulrC (pmule_lgt0 c%:E Heqx_gt_0) Heqx_gt_1.
   1, 3: by rewrite (pmule_lgt0 b%:E Heqx_gt_1) Heqx_gt_0.
   1, 2: by rewrite (mule_lt0_lt0 Heqx_lt_0 Heqx_lt_1).
Qed.


