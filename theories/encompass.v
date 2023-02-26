From mathcomp Require Import all_ssreflect all_algebra vector reals ereal classical_sets.
From mathcomp Require Import zmodp.
Require Export preliminaries preliminaries_hull axiomsKnuth.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section spec.
Variable plane : zmodType.
Variable oriented : plane -> plane -> plane -> bool.

Definition is_left (p q r : plane) := (r == p) || (r == q) || oriented p q r.
Hint Unfold is_left : core.

Definition all_left (x y : plane) : seq plane -> bool := all (is_left x y).

Fixpoint encompass_aux (l l' : seq plane) : bool :=
  match l' with
  | nil => false
  | t1 :: nil => true
  | t1 :: ((t2 :: l') as l'') => all_left t1 t2 l && encompass_aux l l''
  end.

Definition encompass (s l : seq plane) :=
  match l with
  | nil => false
  | t1 :: l' => encompass_aux s (last t1 l' :: l)
  end.

Definition convexHullSpec (l1 l2 : seq plane) :=
  uniq l2 && all (mem l1) l2 && encompass l1 l2.

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

Lemma encompass_all (l s : seq plane) : encompass s l =
  (l != [::]) && all (fun x => encompass [:: x] l) s.
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

Lemma encompass_all_index (l s : seq plane) : encompass s l =
  (l != [::]) && [forall i : 'I_(size l), all_left l`_i l`_(Zp_succ i) s].
Proof.
case: l=>// a l /=.
rewrite -/(encompass_aux s (a :: l)) encompass_aux_all_index.
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
move=> /uniqP-/(_ 0%R) lu; apply/idP/idP.
  rewrite encompass_all => /andP[-> /allP] ll /=.
  have sD i j : (i.+1 < size l)%N -> (j < size l)%N -> j != i -> j != i.+1 ->
      oriented l`_i l`_i.+1 l`_j.
    move=> isl jl ji jis.
    have /ll : l`_j \in l by rewrite mem_nth.
    have il : (i < size l)%N by rewrite (leq_trans _ isl).
    rewrite encompass_all_index => /andP[_] /forallP /(_ (Ordinal il)) /=.
    have -> : val (Zp_succ (Ordinal il)) = i.+1.
      by destruct l => //=; rewrite modn_small ?ltnS.
    rewrite andbT => /orP[|//] /orP[|] /eqP/lu; rewrite 2!inE.
       by move=>/(_ jl il)/eqP; rewrite (negbTE ji).
    by move=>/(_ jl isl)/eqP; rewrite (negbTE jis).
  apply/'forall_'forall_forallP => -[i ilt] [j jlt] [k klt].
  apply/implyP => /= /andP[ij jk].
  elim: k => // k IHk in klt jk *.
  have {}IHk := IHk (ltnW klt).
  move: jk; rewrite leq_eqVlt => /orP[|].
    rewrite eqSS => /eqP jk; subst j.
    do 2 apply Ax1.
    apply: sD => //; first by rewrite ltn_eqF.
    by rewrite ltn_eqF// (leq_trans ij).
  rewrite ltnS => jk; have {}IHk := IHk jk.
  move: ij; rewrite leq_eqVlt =>/orP[/eqP ij|ij].
    subst j.
    apply: sD => //.
      by rewrite gtn_eqF// ltnS (leq_trans _ jk)// -addn2 leq_addr.
    by rewrite gtn_eqF// (leq_trans jk).
  apply: (@Ax5 _ l`_i.+1 _ l`_k).
  - apply: sD => //; first by rewrite (leq_trans ij)// ltnW.
      by rewrite gtn_eqF// (ltn_trans _ ij).
    by rewrite gt_eqF.
  - apply: sD; first by rewrite (leq_trans ij)// ltnW.
        by rewrite (ltn_trans _ klt).
      by rewrite gtn_eqF// (ltn_trans _ jk)// (ltn_trans _ ij).
    by rewrite gtn_eqF// (ltn_trans ij).
  - apply: sD => //; first by rewrite (leq_trans ij)// ltnW.
      rewrite gtn_eqF// ltnS (leq_trans _ (ltnW jk))// (leq_trans _ ij)//.
      by rewrite -addn2 leq_addr.
    by rewrite gtn_eqF// (leq_trans ij)// (leq_trans (ltnW jk)).
  - exact IHk.
  - do 2 apply Ax1.
    apply: sD => //.
      by rewrite ltn_eqF// (ltn_trans _ jk)// (leq_trans _ ij).
    by rewrite ltn_eqF// ltnS (leq_trans _ (ltnW jk))// ltnW// (ltn_trans _ ij).
rewrite encompass_all => /andP[l0 sD] /=; rewrite l0.
have id x : x \in l -> exists2 n, (n < size l)%N & l`_n = x.
   by move=> xl; exists (index x l); [rewrite index_mem|rewrite nth_index].
apply/allP => _ /id[i il <-].
rewrite encompass_all_index; rewrite l0; apply/forallP => [[j jlt]].
rewrite /all_left/= /is_left/= andbT.
have [->|ij] := eqVneq i j.
   by rewrite -orbA; apply/orP; left; apply/eqP; congr nth; apply/eqP.
destruct l as [| a l] => //=.
have [ijs|ijs] := eqVneq i (j.+1 %% (size l).+1)%N.
   by apply/orP; left; apply/orP; right; apply/eqP; congr nth; rewrite -ijs.
apply/orP; right; move: jlt; rewrite leq_eqVlt => /orP[|].
   rewrite eqSS => /eqP je; subst j; rewrite modnn; (do 2 apply Ax1).
   move: sD => /'forall_'forall_forallP
               /(_ ord0 (Ordinal il) (Ordinal (leqnn _)))
               /implyP; apply => /=.
   rewrite lt0n.
   move: ijs; rewrite modnn => ->/=.
   move: il; rewrite leq_eqVlt => /orP[|].
      by rewrite eqSS (negbTE ij).
   by rewrite ltnS.
move=> jlt.
move:ijs; rewrite modn_small => // ijs.
case: (ltnP j.+1 i) => ji.
   move: sD => /'forall_'forall_forallP
               /(_ (Ordinal (leq_trans (leqnSn _) jlt)) (Ordinal jlt) (Ordinal il))
               /implyP; apply => /=.
   by rewrite ltnS leqnn.
apply: Ax1.
move: sD => /'forall_'forall_forallP
            /(_ (Ordinal il) (Ordinal (leq_trans (leqnSn _) jlt)) (Ordinal jlt))
            /implyP; apply => /=.
rewrite ltnS leqnn andbT ltnNge.
rewrite leq_eqVlt eq_sym (negbTE ij)/=.
rewrite leq_eqVlt eq_sym (negbTE ijs)/=.
by rewrite ltnNge ji.
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
