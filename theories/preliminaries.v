From elpi Require Import elpi.

#[projections(primitive)] Record r := { fst : nat -> nat; snd : bool }.
Axiom t : r.
Elpi Command test.
Elpi Query lp:{{
  coq.say "quotation for primitive fst t" {{ t.(fst) 3 }},
  coq.say "quotation for compat fst t" {{ fst t 3 }},
  coq.locate "r" (indt I),
  coq.env.projections I [some P1,some P2],
  coq.say "compatibility constants" P1 P2,
  coq.env.primitive-projections I [some (pr Q1 N1), some (pr Q2 N2)],
  coq.say "fst primproj" Q1 N1,
  coq.say "snd primproj" Q2 N2
}}.



Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra vector reals classical_sets Rstruct.
From infotheo Require Import convex.

Import GRing.Theory Num.Theory convex.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: move to mathcomp ? *)

Lemma enum_rank_index {T : finType} i :
  nat_of_ord (enum_rank i) = index i (enum T).
Proof.
rewrite /enum_rank [enum_rank_in]unlock /insubd /odflt /oapp insubT//.
by rewrite cardE index_mem mem_enum.
Qed.

(* TODO: do we keep this as more newcomer friendly than having to look
   deep into the library ? *)
Lemma enum_prodE {T1 T2 : finType} :
  enum [finType of T1 * T2] = prod_enum T1 T2.
Proof.
by rewrite /enum_mem unlock /= /prod_enum -(@eq_filter _ predT) ?filter_predT.
Qed.

Lemma index_allpairs {T1 T2: eqType} (s1: seq T1) (s2: seq T2) x1 x2 :
    x1 \in s1 -> x2 \in s2 ->
  index (x1, x2) [seq (x1, x2) | x1 <- s1, x2 <- s2] =
    ((index x1 s1) * (size s2) + index x2 s2)%N.
Proof.
move=>ins1 ins2.
elim: s1 ins1=>//= a s1 IHs1 ins1. (* HERE*)
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

Lemma enum_rank_prod {T T': finType} (i : T) (j : T') :
  (nat_of_ord (enum_rank (i, j)) = (enum_rank i) * #|T'| + enum_rank j)%N.
Proof.
do 3 rewrite enum_rank_index.
rewrite enum_prodE cardE /=.
by apply index_allpairs; rewrite enumT.
Qed.

Lemma nth_cat_ord [T : Type] (x0 : T) (s1 s2 : seq T) (i: 'I_(size s1 + size s2)) :
  nth x0 (s1 ++ s2) i = match split i with inl i=> nth x0 s1 i | inr i=> nth x0 s2 i end.
Proof. by move: (nth_cat x0 s1 s2 i)=>->; rewrite /split; case: (ltnP i (size s1)). Qed.

Lemma nth_allpairs [T1 T2 rT : Type] (f : T1 -> T2 -> rT)
    (s1: seq T1) (s2: seq T2) (x1: T1) (x2: T2) (x: rT) (i: 'I_(size s1 * size s2)) :
  nth x (allpairs f s1 s2) i = let (i, j) := split_prod i in f (nth x1 s1 i) (nth x2 s2 j).
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
   by rewrite (nth_map x2)// divn_small// modn_small.
move: i i0; rewrite size_map=> [[i ilt']] i0.
have ilt: ((i - size s2) < size s1 * size s2)%N.
   move: (allpairs_tupleP f (in_tuple s1) (in_tuple s2))=>/eqP<-.
   apply (split_subproof i0).
rewrite (IHs1 (Ordinal ilt))=> /=.
rewrite addnC divnDr// divnn/= modnDr.
have [s20|] := ltnP 0 (size s2); first  by rewrite addn1.
rewrite leqn0 => /eqP s20.
by move: ilt; rewrite s20 muln0.
Qed.

(*TODO: move to mathcomp.*)
Lemma lift_range {aT rT: Type} [f: aT -> rT] (s: seq rT) :
  all (fun u => u \in range f) s -> exists s', map f s' = s.
Proof.
elim: s=>[| a s IHs].
   by exists nil.
move=> /andP [/set_mem [a' _ ae] /IHs [s' se]]; subst a s.
by exists (a' :: s').
Qed.

Lemma index_enum_cast_ord n m (e: n = m) :
  index_enum [finType of 'I_m] = [seq (cast_ord e i) | i <- index_enum [finType of 'I_n]].
Proof.
subst m.
rewrite -{1}(map_id (index_enum [finType of 'I_n])).
apply eq_map=>[[x xlt]].
rewrite /cast_ord; congr Ordinal; apply bool_irrelevance.
Qed.

Lemma perm_map_bij [T: finType] [f : T -> T] (s: seq T) :
  bijective f -> perm_eq (index_enum T) [seq f i | i <- index_enum T].
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

(* TODO: this lemma has been moved to infotheo 0.5.1 *)
Section freeN_combination.
Import ssrnum vector.
Import Order.POrderTheory Num.Theory.
Variable (R : fieldType) (E : vectType R).
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Import GRing.

Lemma freeN_combination n (s : n.-tuple E) : ~~ free s ->
  exists k : 'I_n -> R, (\sum_i k i *: s`_i = 0) /\ exists i, k i != 0.
Proof.
exact: freeN_combination.
Qed.

End freeN_combination.

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

Lemma hom_lt_inj {disp disp' : unit} {T : orderType disp} {T' : porderType disp'} [f : T -> T'] :
  {homo f : x y / (x < y)%O >-> (x < y)%O} -> injective f.
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

Lemma map_nth_ord [T : Type] (x: T) (s : seq T) :
  [seq nth x s (nat_of_ord i) | i <- index_enum [finType of 'I_(size s)]] = s.
Proof.
rewrite /index_enum; case: index_enum_key=>/=; rewrite -enumT.
elim: s=>/= [| a s IHs].
   by case: (enum 'I_0)=> [| s q] //; inversion s.
by rewrite enum_ordSl /= -map_comp /=; congr cons.
Qed.

Lemma nth_filter [T : Type] (P: {pred T}) x (s: seq T) n :
  (n < size [seq i <- s | P i])%N -> P (nth x [seq i <- s | P i] n).
Proof.
elim: s n=> [| a s IHs] n //=.
case Pa: (P a).
   2: by apply IHs.
by case: n=>//=; rewrite ltnS; apply IHs.
Qed.

Lemma big_pair [R : Type] (idr : R) (opr : R -> R -> R) [S : Type] (ids : S) (ops : S -> S -> S) [I : Type]
  (r : seq I) (F : I -> R) (G: I -> S) :
  \big[(fun (x y: R*S)=> (opr x.1 y.1, ops x.2 y.2))/(idr, ids)]_(i <- r) (F i, G i) =
  (\big[opr/idr]_(i <- r) F i, \big[ops/ids]_(i <- r) G i).
Proof.
elim: r=>[| a r IHr].
   by do 3 rewrite big_nil.
by do 3 rewrite big_cons; rewrite IHr.
Qed.

From infotheo Require Import fdist.
Local Open Scope fdist_scope.

Lemma Convn_pair [T U : convType] [n : nat] (g : 'I_n -> T * U) (d : {fdist 'I_n}) :
  Convn d g = (Convn d (fst \o g), Convn d (snd \o g)).
Proof.
elim: n g d => [|n IHn] g d.
   by have := fdistI0_False d.
rewrite /Convn; case: (Bool.bool_dec _ _) => [_|d0]; first by rewrite -surjective_pairing.
have := IHn (g \o fdist_del_idx ord0) (fdist_del (Bool.eq_true_not_negb _ d0)).
by rewrite/Convn => ->.
Qed.
