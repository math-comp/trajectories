From mathcomp Require Import all_ssreflect all_algebra vector reals ereal classical_sets.
From mathcomp Require Import zmodp.
Require Export preliminaries preliminaries_hull axiomsKnuth.

(******************************************************************************)
(*   encompass oriented s l == oriented is a ternary relation, s and l        *)
(*                             are lists of points such that                  *)
(*                             oriented l_i l_i.+1 s_k for all i and k        *)
(*   encompass_aux oriented l h == h describes an open convex region that     *)
(*                             contains l                                     *)
(*   encompass oriented l h == h describes a convex hull for the set of       *)
(*                             points l where the last segment is formed by   *)
(*                             the last and first elements                    *)
(******************************************************************************)

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section spec.
Variable plane : zmodType.
Variable oriented : plane -> plane -> plane -> bool.

Definition is_left (p q r : plane) := [|| r == p, r == q | oriented p q r].
Hint Unfold is_left : core.

Definition all_left (x y : plane) : seq plane -> bool := all (is_left x y).

Fixpoint encompass_aux (l h : seq plane) : bool :=
  match h with
  | nil => false
  | t1 :: nil => true
  | t1 :: ((t2 :: _) as h') => all_left t1 t2 l && encompass_aux l h'
  end.

Definition encompass (s h : seq plane) :=
  match h with
  | nil => false
  | t :: h' => encompass_aux s (last t h' :: h)
  end.

Lemma encompassl0 l : encompass l [::] = false.
Proof. by []. Qed.

Definition convexHullSpec (l h : seq plane) :=
  uniq h && all (mem l) h && encompass l h.

(* TOTHINK: replace encompass : seq -> seq -> bool by a predicate
   seq -> plane -> bool? *)

Lemma encompass_auxE (l h : seq plane) :
  encompass_aux l h = (h != [::]) && all (fun x => encompass_aux [:: x] h) l.
Proof.
elim: h =>// a'; case=> [ _ | b' l' IHl'].
   by elim: l.
rewrite /= -/(encompass_aux l (b' :: l')) IHl' -all_predI; apply eq_all=>x.
by rewrite /= andbT.
Qed.

Lemma encompassE (s h : seq plane) :
  encompass s h = (h != [::]) && all (fun x => encompass [:: x] h) s.
Proof. by case: h =>// a l; rewrite {1}/encompass encompass_auxE. Qed.

Lemma encompass_aux_all_index (l h : seq plane) :
  encompass_aux l h = (h != [::]) &&
    [forall i : 'I_(size h), (i.+1mod == 0%N :> nat) || all_left h`_i h`_i.+1mod l].
Proof.
elim: h=>// a; case.
   by move=>/= _; apply/esym/forallP => i; rewrite modn1 eq_refl.
move=>b l' IHl' /=; rewrite -/(encompass_aux l (b :: l')) IHl' /=.
apply/idP/idP => [/andP[Habl H]|/forallP H].
  apply/forallP => -[] [//|n/=].
  rewrite ltnS => nlt.
  move: H => /forallP/(_ (Ordinal nlt)).
  move: nlt (nlt); rewrite {1}ltnS leq_eqVlt => /predU1P[-> mm _|nm nm1].
    by rewrite modnn eqxx.
  by rewrite modn_small ?ltnS// modn_small ?ltnS.
apply/andP; split; first by move: H => /(_ ord0).
apply/forallP => -[i ilt].
move: H => /(_ (lift ord0 (Ordinal ilt))).
move: ilt (ilt); rewrite {1}ltnS leq_eqVlt => /predU1P[-> mm _|ilt ilt1].
  by rewrite modnn eqxx.
by rewrite modn_small ?ltnS// modn_small ?ltnS.
Qed.

Lemma encompass_all_index (l s : seq plane) : encompass s l =
  (l != [::]) && [forall i : 'I_(size l), all_left l`_i l`_i.+1mod s].
Proof.
case: l => // a l /=.
rewrite -/(encompass_aux s (a :: l)) encompass_aux_all_index.
apply/idP/idP => [H|/forallP H].
   apply/forallP => -[i ilt].
   move: ilt (ilt); rewrite {1}ltnS leq_eqVlt => /predU1P[-> /= _|ilt ilt1].
     by rewrite modnn nth_last /=; move: H => /andP[H _].
   move: H => /andP[_ /andP [_ /forallP]] /(_ (Ordinal ilt1)) /=.
   by rewrite modn_small ?ltnS.
apply/andP; split.
   by move: H => /(_ ord_max); rewrite /= modnn nth_last.
apply/forallP => -[i ilt].
move: ilt (ilt); rewrite {1}ltnS leq_eqVlt => /predU1P[-> /= _|ilt ilt1].
  by rewrite modnn.
by move: H => /(_ (Ordinal ilt1))/=; rewrite modn_small ?ltnS.
Qed.

End spec.

Module SpecKA (KA : KnuthAxioms).
Section Dummy.
Variable R : realType.
Let plane : vectType _ := (R^o * R^o)%type.

Let oriented := KA.OT (R:=R).
Let Ax1 := KA.Axiom1 (R:=R).
Let Ax2 := KA.Axiom2 (R:=R).
Let Ax5 := KA.Axiom5 (R:=R).
Let Ax5' := KA.Axiom5' (R:=R).

Lemma encompassll_spec (l : seq plane) : uniq l ->
  encompass oriented l l =
  (l != [::]) &&
    [forall i : 'I_(size l), [forall j : 'I_(size l), [forall k : 'I_(size l),
      (i < j < k)%N ==> oriented l`_i l`_j l`_k]]].
Proof.
move=> /uniqP-/(_ 0%R) lu; apply/idP/idP.
  rewrite encompassE => /andP[-> /allP] ll /=.
  have sD i j : (i.+1 < size l)%N -> (j < size l)%N -> j != i -> j != i.+1 ->
      oriented l`_i l`_i.+1 l`_j.
    move=> isl jl ji jis.
    have /ll : l`_j \in l by rewrite mem_nth.
    have il : (i < size l)%N by rewrite (leq_trans _ isl).
    rewrite encompass_all_index => /andP[_] /forallP /(_ (Ordinal il)) /=.
    rewrite Zp_succE andbT/= modn_small// => /or3P[| |//] /eqP/lu; rewrite 2!inE.
       by move=> /(_ jl il)/eqP; rewrite (negbTE ji).
    by move=>/(_ jl isl)/eqP; rewrite (negbTE jis).
  apply/'forall_'forall_'forall_implyP => -[i ilt] [j jlt] [k klt] /= /andP[ij jk].
  elim: k => // k IHk in klt jk *.
  have {}IHk := IHk (ltnW klt).
  move: jk; rewrite leq_eqVlt => /predU1P[[jk]|].
    subst j.
    do 2 apply: Ax1.
    apply: sD => //; first by rewrite ltn_eqF.
    by rewrite ltn_eqF// (leq_trans ij).
  rewrite ltnS => jk; have {}IHk := IHk jk.
  move: ij; rewrite leq_eqVlt => /predU1P[ij|ij].
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
rewrite encompassE => /andP[l0 sD] /=; rewrite l0 /=.
have id x : x \in l -> exists2 n, (n < size l)%N & l`_n = x.
   by move=> xl; exists (index x l); [rewrite index_mem|rewrite nth_index].
apply/allP => _ /id[i il <-].
rewrite encompass_all_index; rewrite l0; apply/forallP => -[j jlt].
rewrite /all_left/= /is_left/= andbT.
have [->|ij] := eqVneq i j.
   exact/or3P/Or31.
destruct l as [|a l] => //=.
have [ijs|ijs] := eqVneq i (j.+1 %% (size l).+1)%N.
   by apply/or3P/Or32; rewrite -ijs.
apply/or3P/Or33; move: jlt; rewrite leq_eqVlt => /predU1P[[je]|jlt].
   subst j; rewrite modnn.
   do 2 apply Ax1.
   move: sD => /'forall_'forall_'forall_implyP
               /(_ ord0 (Ordinal il) (Ordinal (leqnn _)));
               apply => /=.
   rewrite lt0n.
   move: ijs; rewrite modnn => ->/=.
   move: il; rewrite leq_eqVlt => /predU1P[[/eqP]|].
      by rewrite (negbTE ij).
   by rewrite ltnS.
move:ijs; rewrite modn_small => // ijs.
have [ji|ji] := ltnP j.+1 i.
   move: sD => /'forall_'forall_'forall_implyP
               /(_ (Ordinal (leq_trans (leqnSn _) jlt)) (Ordinal jlt) (Ordinal il)).
   apply => /=.
   by rewrite ltnS leqnn.
apply: Ax1.
move: sD => /'forall_'forall_'forall_implyP
            /(_ (Ordinal il) (Ordinal (leq_trans (leqnSn _) jlt)) (Ordinal jlt)).
apply => /=.
rewrite ltnS leqnn andbT ltnNge.
rewrite leq_eqVlt eq_sym (negbTE ij)/=.
rewrite leq_eqVlt eq_sym (negbTE ijs)/=.
by rewrite ltnNge ji.
Qed.

Lemma encompassll_subseq (l l' : seq plane) : uniq l ->
  encompass oriented l l ->
  subseq l' l ->
  l' != [::] ->
  encompass oriented l' l'.
Proof.
move=> lu; rewrite (encompassll_spec lu) => ll l'l l'0.
have l'u := subseq_uniq l'l lu; rewrite (encompassll_spec l'u) l'0 /=.
apply/'forall_'forall_'forall_implyP => i j k /andP[ij jk].
move: l'l => /subseq_incl-/(_ 0%R) [f [fl flt]].
move: ll => /andP[_] /'forall_'forall_'forall_implyP
  /(_ (f i)) /(_ (f j)) /(_ (f k)); rewrite 3!fl; apply.
by apply/andP; split; apply: flt.
Qed.

End Dummy.
End SpecKA.
