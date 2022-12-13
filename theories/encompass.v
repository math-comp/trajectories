Require Export preliminaries_hull axiomsKnuth.
From mathcomp Require Import all_ssreflect all_algebra vector reals ereal classical_sets.
From mathcomp Require Import zmodp.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section spec.
Variable plane : zmodType.
Variable oriented : plane -> plane -> plane -> bool.

Definition is_left (p q r : plane) := (r == p) || (r == q) || (oriented p q r).
Hint Unfold is_left : core.

Definition all_left (t1 t2 : plane) : seq plane -> bool := all (is_left t1 t2).

Fixpoint encompass_aux (l l' : seq plane) : bool :=
  match l' with
  | nil => false
  | t1 :: nil => true
  | t1 :: ((t2 :: l') as l'') => all_left t1 t2 l && encompass_aux l l''
  end.
Definition encompass (l s : seq plane) :=
  match l with
  | nil => false
  | t1 :: l' => encompass_aux s ((last t1 l') :: l)
  end.

Definition convexHullSpec (l1 l2 : seq plane) :=
  uniq l2 && all (fun x => x \in l1) l2 && encompass l2 l1.

(* TOTHINK: replace encompass : seq -> seq -> bool by a predicate
   seq -> plane -> bool? *)

Lemma encompass_aux_all (l l' : seq plane) : encompass_aux l l' = 
  (l' != [::]) && all (fun x => encompass_aux [:: x] l') l.
Proof.
elim: l'=>// a'; case=>[ _ | b' l' IHl'].
   by elim: l.
rewrite /= -/(encompass_aux l (b' :: l')) IHl' -all_predI; apply eq_all=>x.
by rewrite /= andbT.
Qed.

Lemma encompass_all (l l' : seq plane) : encompass l l' =
  (l != [::]) && all (fun x => encompass l [:: x]) l'.
Proof.
case: l=>// a l.
by rewrite {1}/encompass encompass_aux_all.
Qed.

Lemma encompass_aux_all_index (l l' : seq plane): encompass_aux l l' =
  (l' != [::]) &&
  [forall i : 'I_(size l'),
    (val (Zp_succ i) == 0)%N || all_left l'`_i l'`_(Zp_succ i) l].
Proof.
elim: l'=>// a; case.
   by move=>/= _; apply/esym; apply/forallP=>i; rewrite modn1 eq_refl.
move=>b l' IHl' /=; rewrite -/(encompass_aux l (b :: l')) IHl' /=.
apply/idP/idP=>H.
   apply/forallP; case; case=>/=.
      by move: H=>/andP [H _].
   move=> n; rewrite ltnS=> nlt.
   move: H=>/andP [_ /forallP] /(_ (Ordinal nlt)).
   move: nlt (nlt); rewrite {1}ltnS leq_eqVlt=>/orP; case.
      by move=>/eqP -> mm _; rewrite modnn eq_refl.
   move=>nm nm1.
   by rewrite /= modn_small ?ltnS// modn_small ?ltnS.
move:H=>/forallP H.
apply/andP; split; first by move:H=>/(_ ord0).
apply/forallP=>[[i ilt]].
move:H=>/(_ (lift ord0 (Ordinal ilt))).
move: ilt (ilt); rewrite {1}ltnS leq_eqVlt=>/orP; case.
   by move=>/eqP -> mm _; rewrite modnn eq_refl.
move=>ilt ilt1.
by rewrite /= modn_small ?ltnS// modn_small ?ltnS.
Qed.

Lemma encompass_all_index (l l' : seq plane): encompass l l' =
  (l != [::]) && [forall i : 'I_(size l), all_left l`_i l`_(Zp_succ i) l'].
Proof.
case: l=>// a l /=.
rewrite -/(encompass_aux l' (a :: l)) encompass_aux_all_index.
apply/idP/idP=>H.
   apply/forallP=>[[i ilt]].
   move: ilt (ilt); rewrite {1}ltnS leq_eqVlt=>/orP; case.
      move=>/eqP-> /= _; rewrite modnn nth_last /=.
      by move:H=>/andP[H _].
   move=>ilt ilt1 /=.
   move:H=>/andP[_ /andP [_ /forallP]] /(_ (Ordinal ilt1)) /=.
   by rewrite modn_small ?ltnS.
move:H=>/forallP H.
apply/andP; split.
   by move:H=>/(_ ord_max); rewrite /= modnn nth_last /=. 
apply/forallP=>[[i ilt]].
move: ilt (ilt); rewrite {1}ltnS leq_eqVlt=>/orP; case.
   by move=>/eqP-> /= _; rewrite modnn.
move=>ilt ilt1 /=.
by move:H=>/(_ (Ordinal ilt1))/=; rewrite modn_small ?ltnS.
Qed.

End spec.

Module SpecKA (KA : KnuthAxioms).
Section Dummy.
Variable R : realType.
Let plane := pair_vectType (regular_vectType R) (regular_vectType R).

Let oriented := KA.OT (R:=R).
Let Ax1 := KA.Axiom1 (R:=R).
Let Ax2 := KA.Axiom2 (R:=R).
Let Ax5 := KA.Axiom5 (R:=R).
Let Ax5' := KA.Axiom5' (R:=R).

Lemma encompassll_spec (l : seq plane) : uniq l ->
  encompass oriented l l =
  (l != [::]) &&
    [forall i: 'I_(size l), [forall j: 'I_(size l), [forall k: 'I_(size l),
      ((i < j < k)%N) ==> oriented l`_i l`_j l`_k]]].
Proof.
move=>/uniqP; move=>/(_ (GRing.zero _)) lu; apply/idP/idP.
   rewrite encompass_all=>/andP[-> /allP] ll /=.
   have sD: forall i j, (i.+1 < size l)%N -> (j < size l)%N -> (j != i) -> (j != i.+1) -> oriented l`_i l`_i.+1 l`_j.
      move=>i j isl jl ji jis.
      have/ll: l`_j \in l by rewrite mem_nth.
      have il: (i < size l)%N by rewrite (leq_trans _ isl).
      rewrite encompass_all_index=>/andP[_ /forallP] /(_ (Ordinal il))/=.
      have ->: val (Zp_succ (Ordinal il)) = i.+1 by destruct l=>//=; rewrite modn_small ?ltnS.
      rewrite andbT=>/orP; case=>// /orP; case=>/eqP/lu; rewrite 2!inE.
         by move=>/(_ jl il)/eqP jie; move:ji; rewrite jie.
      by move=>/(_ jl isl)/eqP jie; move:jis; rewrite jie.
   apply/forallP=>[[i ilt]].
   apply/forallP=>[[j jlt]].
   apply/forallP=>[[k klt]].
   apply/implyP=>/=/andP[ij jk].
   elim: k klt jk=>// k IHk klt jk.
   have klt': (k < size l)%N by refine (leq_trans _ klt).
   move:IHk=>/(_ klt') IHk.
   move:jk; rewrite leq_eqVlt=>/orP; case.
      rewrite eqSS=>/eqP jk; subst j.
      do 2 apply Ax1.
      apply sD=>//; apply/negPn=>/eqP ie; subst i.
         by move:ij; rewrite ltnn.
      by move:ij=>/(leq_trans (leqnSn _)); rewrite ltnn.
   rewrite ltnS=>jk; move:IHk=>/(_ jk) IHk.
   move:ij; rewrite leq_eqVlt=>/orP; case.
      move=>/eqP ij; subst j.
      apply sD=>//; apply/negPn=>/eqP.
         by move=>ie; subst i; move:jk=>/(leq_trans (leqnSn _))/(leq_trans (leqnSn _)); rewrite ltnn.
      by move=>/eqP; rewrite eqSS=>/eqP ie; subst i; move:jk=>/(leq_trans (leqnSn _)); rewrite ltnn.
   move=>ij.
   apply (@Ax5 _ l`_i.+1 _ l`_k).
   - (apply sD=>//; first by apply (leq_trans ij); apply (leq_trans (leqnSn _))); apply/negPn=>/eqP ie; subst j.      
      by move:ij=>/(leq_trans (leqnSn _)); rewrite ltnn.
   by move:ij; rewrite ltnn.
   - (apply sD=>//; first by apply (leq_trans ij); apply (leq_trans (leqnSn _))); apply/negPn=>/eqP ie; subst k.      
      by move:jk=>/(leq_trans (leqnSn _))/(leq_trans ij)/(leq_trans (leqnSn _)); rewrite ltnn.
   by move:jk=>/(leq_trans (leqnSn _))/(leq_trans ij); rewrite ltnn.
   - (apply sD=>//; first by apply (leq_trans ij); apply (leq_trans (leqnSn _))); apply/negPn.
      by move=>/eqP ik; subst i; move:ij=>/(leq_trans (leqnSn _))/(leq_trans (leqnSn _))/(leq_trans (leqnSn _))/(leq_trans jk); rewrite ltnn.
   by rewrite eqSS=>/eqP ki; subst i; move:ij=>/(leq_trans (leqnSn _))/(leq_trans (leqnSn _))/(leq_trans jk); rewrite ltnn.
   - exact IHk.
   - do 2 apply Ax1.
     apply sD=>//; apply/negPn=>/eqP ie; subst i.
      by move:ij=>/(leq_trans (leqnSn _))/(leq_trans (leqnSn _))/(leq_trans jk); rewrite ltnn.
   by move:ij=>/(leq_trans (leqnSn _))/(leq_trans (leqnSn _))/(leq_trans (leqnSn _))/(leq_trans jk); rewrite ltnn.
rewrite encompass_all=>/andP[l0 sD] /=; rewrite l0.
have id: forall x, x \in l -> exists n, (n < size l)%N /\ (x = l`_n).
   move=>x xl; exists (index x l); split.
      by rewrite index_mem.
   by move:(nth_index (GRing.zero _) xl)=>/esym.
apply/allP=>x/id[i [il xe]]; subst x.
rewrite encompass_all_index; rewrite l0; apply/forallP=>[[j jlt]].
rewrite/all_left/=/is_left/= andbT.
case ij: (i == j).
   by rewrite -orbA; apply/orP; left; apply/eqP; congr nth; apply/eqP.
destruct l as [| a l]=>//=.
case ijs: (i == j.+1 %% (size l).+1)%N.
   by apply/orP; left; apply/orP; right; apply/eqP; congr nth; move:ijs=>/eqP<-.
apply/orP; right; move: jlt; rewrite leq_eqVlt=>/orP; case.
   rewrite eqSS=>/eqP je; subst j; rewrite modnn; (do 2 apply Ax1).
   move:sD=>/forallP /(_ ord0) /forallP /(_ (Ordinal il)) /forallP /(_ (Ordinal (leqnn _))) /implyP; apply; apply/andP; split=>/=.
      by rewrite lt0n; move:ijs; rewrite modnn=>->.
   move:il; rewrite leq_eqVlt=>/orP; case.
      by rewrite eqSS ij.
   by rewrite ltnS.
move=>jlt.
move:ijs; rewrite modn_small=>//ijs.
case ji: (j.+1 < i)%N.
   move:sD=>/forallP /(_ (Ordinal (leq_trans (leqnSn _) jlt))) /forallP /(_ (Ordinal jlt)) /forallP /(_ (Ordinal il)) /implyP; apply=>/=.
   by apply/andP; split.
apply Ax1.
move:sD=>/forallP /(_ (Ordinal il)) /forallP /(_ (Ordinal (leq_trans (leqnSn _) jlt))) /forallP /(_ (Ordinal jlt)) /implyP; apply=>/=.
apply/andP; split=>//.
rewrite ltnNge; apply/negP.
rewrite leq_eqVlt=>/orP; case.
   by rewrite eq_sym ij.
rewrite leq_eqVlt=>/orP; case.
   by rewrite eq_sym ijs.
by rewrite ji.
Qed.

Lemma encompassll_subseq (l l' : seq plane): uniq l ->
  encompass oriented l l ->
  subseq l' l ->
  l' != [::] ->
  encompass oriented l' l'.
Proof.
move=>lu; rewrite (encompassll_spec lu)=> ll l'l l'0.
move: (subseq_uniq l'l lu)=>l'u; rewrite (encompassll_spec l'u) l'0 /=.
apply/forallP=>i.
apply/forallP=>j.
apply/forallP=>k.
apply/implyP=>/andP[ij jk].
move: l'l=>/subseq_incl; move=>/(_ (GRing.zero _)) [f [fl flt]].
move:ll=>/andP[_] /forallP /(_ (f i)) /forallP /(_ (f j)) /forallP /(_ (f k)) /implyP; rewrite 3!fl; apply.
by apply /andP; split; apply flt.
Qed.

End Dummy.
End SpecKA.


