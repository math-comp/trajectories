From mathcomp Require Import all_ssreflect ssrnum zmodp order constructive_ereal.
Require Import preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.
Local Open Scope order_scope.

(******************************************************************************)
(*   Zp_succ (i : 'I_n) == the ordinal i.+1 : 'I_n                            *)
(******************************************************************************)

Definition Zp_succ p : 'I_p -> 'I_p :=
  match p with
    0 => id
  | q.+1 => fun i : 'I_q.+1 => inZp i.+1
  end.

Notation "n .+1mod" := (Zp_succ n) (at level 2, left associativity,
  format "n .+1mod").

Lemma Zp_succE n (i : 'I_n) : val (i .+1mod) = i.+1 %% n.
Proof. by case: n i => // -[]. Qed.

Lemma Zp_succ_max n : (@ord_max n).+1mod = ord0.
Proof. by apply: val_inj => /=; rewrite modnn. Qed.

Lemma subseq_iota (n m : nat) (l : seq nat) : subseq l (iota n m) =
  (l == [::]) || (n <= nth 0 l 0)%N &&
  [forall i : 'I_(size l), (nth 0 l i < nth 0 (rcons l (n+m)) i.+1)%N].
Proof.
elim:l n m=>[| a l IHl] n m; first by case: (iota n m).
elim: m n=>[| m IHm] n.
   rewrite /addn/addn_rec-plus_n_O.
   move:(size_iota n 0)=>/size0nil->/=; apply/esym/negbTE.
   rewrite negb_and orbC -implybE; apply/implyP=>/forallP lmono; rewrite -ltnNge.
   elim:l a {IHl} lmono=>[| b l IHl] a; first by move=>/(_ ord0).
   by move=>lmono; apply (ltn_trans (lmono ord0)); apply IHl=>i/=; apply (lmono (lift ord0 i)).
rewrite/iota-/(iota n.+1 m)/subseq.
case: ifP.
   move=>/eqP an; subst a.
   rewrite -/(subseq l (iota n.+1 m)) (IHl n.+1 m)/= leqnn/=.
   destruct l=>/=.
      by apply/esym/forallP; case; case=>//= _; rewrite -{1}(addn0 n) ltn_add2l.
   apply/andP/forallP.
      by move=>[nn0 /forallP nl] i; case (ord_S_split i)=>[ [j]->/= | ->// ]; rewrite -addSnnS; apply nl.
   move=>nl; split; first by apply (nl ord0).
   by apply/forallP=>i; rewrite addSnnS; apply (nl (lift ord0 i)).
move=>an.
rewrite -/(subseq (a :: l) (iota n.+1 m)) IHm; congr andb=>/=.
   by rewrite ltn_neqAle eq_sym an.
by rewrite addSnnS.
Qed.

Lemma count_card (T : eqType) (x : T) (l : seq T) (P : pred T) :
  count P l = #|[set i : 'I_(size l) | P (nth x l i)]|.
Proof.
elim:l.
   by move=>/=; apply/esym /eqP; rewrite cards_eq0 -subset0; apply/subsetP=>[[i ilt]].
move=>a l IHl /=.
rewrite (cardsD1 (Ordinal (ltn0Sn _))) IHl.
rewrite cardsE.
have fi: injective (fun i : 'I_(size l)=> lift ord0 i) by move=>[i ilt] [j jlt]/(congr1 val)/=/eqP; rewrite/bump/= 2!add1n eqSS=>/eqP ij; apply val_inj.
rewrite -(card_imset _ fi)/=.
have/eqP->: [set i : 'I_(size l).+1 | P (nth x (a :: l) i)] :\ Ordinal (ltn0Sn (size l)) == [set lift ord0 i | i in fun x0 : 'I_(size l) => P (nth x l x0)].
   rewrite eqEsubset; apply/andP; split; apply/subsetP=>i; rewrite in_setD1 inE.
      move=>/andP[i0 Pi].
      case: (ord_S_split i); last by move=>ie; subst i; move: i0=>/negP; elim.
      move=>[j ie]; subst i.
      by apply /imsetP=>/=; exists j.
   move=>/imsetP/=[j Pj ie]; subst i.
   by apply/andP; split.
by apply/eqP; rewrite eqn_add2r inE; apply/eqP.
Qed.

Lemma filter_incl_surj (T : eqType) (x : T) (l : seq T) (P : pred T) :
  let l' := [seq x <- l | P x] in forall (f : 'I_(size l') -> 'I_(size l)),
      (forall i : 'I_(size l'), nth x l (f i) = nth x l' i) ->
      {homo f : x0 y / x0 < y >-> x0 < y} ->
      forall j : 'I_(size l), P (nth x l j) ->
      exists i : 'I_(size l'), j = f i.
Proof.
set l' := [seq x0 <- l | P x0]=>/= f fi fh j Pj.
suff: exists i, ~~ (j != f i) by move=>[i /negPn/eqP ->]; exists i.
apply /existsP.
rewrite -negb_forall; apply /negP=>/forallP jf.
suff: size l' < count P l by rewrite size_filter lt_irreflexive.
rewrite (count_card x).
(* Huh ??? *)
have what: (size l' < (size l').+1) by move:(leqnn (size l').+1).
apply (lt_le_trans what).
rewrite -(card_ord (size l').+1).
have/card_codom<-: injective (fun i =>
   match ord_S_split i with
   | inleft j => f (proj1_sig j)
   | _ => j
   end).
   move=>a b.
   case:(ord_S_split a).
      move=>[a'/= ae]; subst a.
      case:(ord_S_split b).
         move=>[b'/= be]; subst b=>fab.
         apply val_inj; apply/eqP; rewrite/=/bump/= 2!add1n eqSS.
         by apply/negP=>/negP/lt_total/orP; case=>/fh; rewrite fab lt_irreflexive.
      by move=>->/esym je; move:(jf a'); rewrite je eq_refl.
   case:(ord_S_split b).
      by move=>[b'/= be]; subst b=>fab je; move:(jf b'); rewrite je eq_refl.
   by move=>-> -> _.
apply subset_leq_card; apply/subsetP=>k /codomP [a ->].
case: (ord_S_split a).
   move=>[a'/= _]; rewrite inE fi.
   have/mem_nth: val a' < size l' by case: a'.
   by move=>/(_ x); rewrite mem_filter=>/andP[h _].
by move=>_; rewrite inE.
Qed.

Lemma homo_lt_total {disp disp' : unit} {T : orderType disp}
   {T' : orderType disp'} [f : T -> T'] : {homo f : x y / x < y >-> x < y} ->
   forall x y, f x < f y -> x < y.
Proof.
move=>fh x y fxy.
case xy: (x == y); first by move:xy fxy=>/eqP ->; rewrite lt_irreflexive.
move:xy=>/negbT/lt_total/orP; case=>// /fh fyx.
by move:(lt_trans fxy fyx); rewrite lt_irreflexive.
Qed.

Lemma homo_lt_inj {disp disp' : unit} {T : orderType disp}
   {T' : orderType disp'} [f : T -> T'] : {homo f : x y / x < y >-> x < y} ->
   injective f.
Proof.
move=>fh x y fxy.
case xy: (x == y); first by move:xy=>/eqP.
by move:xy=>/negbT/lt_total/orP; case=>/fh; rewrite fxy lt_irreflexive.
Qed.

Lemma filter_succ (T : eqType) (x : T) (l : seq T) (P : pred T) :
  let l' := [seq x <- l | P x] in forall (f : 'I_(size l') -> 'I_(size l)),
      (forall i : 'I_(size l'), nth x l (f i) = nth x l' i) ->
      {homo f : x0 y / x0 < y >-> x0 < y} ->
      forall (i' : 'I_(size l')) k,
         (f i' < k < (f i'.+1mod + (i'.+1 == size l')*(size l))%N)%N ->
         ~~ P (nth x l (k %% size l)).
Proof.
(*Huh???*)
set l' := [seq x0 <- l | P x0]=>/= f fi fh i' k ikj; apply /negP=>Pkl.
have kl: k %% size l < size l.
   apply ltn_pmod; destruct l=>//.
   by move:(i')=>[a/= alt].
move: (@filter_incl_surj _ _ _ _ _ fi fh (Ordinal kl) Pkl)=>[[a alt] /(congr1 val)/= ke].
(*Way too long*)
destruct i' as [i' i'lt].
move:(i'lt); rewrite leq_eqVlt => /predU1P[ie|].
   move:ikj; rewrite ie eq_refl mul1n.
   case klt: (k < size l).
      move:(alt); rewrite -{1}ie leq_eqVlt=>/orP; case.
         rewrite eqSS=>/eqP ae; subst a.
         move: ke; rewrite modn_small ?klt//; move=>->/andP.
         have->:Ordinal alt = Ordinal i'lt by apply val_inj.
         move=>[h _].
         by move: (lt_irreflexive (f (Ordinal i'lt)))=>/negbT/negP; apply.
      rewrite ltnS=>ai' /andP[fik _].
      have/fh fai:Ordinal alt < Ordinal i'lt by [].
      move:(ltn_trans fai fik); rewrite/= -ke modn_small ?klt//.
      by rewrite ltnn.
   move:klt; rewrite ltNge=>/negbT/negbNE lk.
   move=>/andP[_]; rewrite addnC -ltn_subLR// =>kf.
   have kmod: (k %% size l = k - size l)%N.
      rewrite -{1}[k](subnK lk) modnDr modn_small//.
      by apply (ltn_trans kf).
   move:ke; rewrite kmod=>ke.
   have ie' : val (Ordinal i'lt).+1mod = 0%N.
     by move: ie i'lt {kf}=><- i'lt/=; apply modnn.
   destruct a as [| a].
      have ae: Zp_succ (Ordinal i'lt) = Ordinal alt by apply val_inj.
      by move: kf; rewrite ke -ae ltnn.
   have /fh fia : (Ordinal i'lt).+1mod < Ordinal alt.
      suff: val (Ordinal i'lt).+1mod < a.+1 by [].
      by rewrite ie'; apply ltn0Sn.
   have fai: f (Ordinal alt) < f (Ordinal i'lt).+1mod.
     by have: val (f (Ordinal alt)) < val (f (Ordinal i'lt).+1mod) by rewrite/= -ke.
   by move:(lt_trans fai fia); rewrite ltxx.
move=>i'lt'; move:ikj.
case ile: ((Ordinal i'lt).+1 == size l').
   by move:ile=>/=/eqP ile; move:i'lt'; rewrite ile ltnn.
rewrite/=/muln/muln_rec/= addnC/addn/addn_rec/= => /andP[fk kf].
have kl': (k < size l)%N by apply (ltn_trans kf).
move:Pkl kl ke; rewrite modn_small// =>Pkl kl ke.
move:fk kf; rewrite ke=>/(@homo_lt_total _ _ _ _ _ fh) ia /(@homo_lt_total _ _ _ _ _ fh) ai.
have ia': (i' < a)%N by [].
have ai': (a < i'.+1)%N.
   have ai': val (Ordinal alt) < val (Ordinal i'lt).+1mod by [].
   move:f fi fh alt i'lt ile {ia} ke i'lt' ai ai'; rewrite/Zp_succ -/l'; generalize (size l'); case=>// n _ _ _ /= _ _ _ _ i'lt _.
   by rewrite modn_small.
by move: (leq_ltn_trans ia' ai'); rewrite ltnn.
Qed.

Lemma uniq_subseq_size (T: eqType) (l l': seq T) :
  all (fun x => x \in l) l' -> uniq l' -> (size l' <= size l)%N.
Proof.
elim: l' l=>// a l' IHl' l /andP[al /allP l'l] /andP [al' l'uniq].
move:(al)=>/size_rem/(f_equal S).
rewrite prednK; last by case: l l'l al.
move=><-; rewrite ltnS; apply IHl'=>//.
apply/allP=>b bl'; move:(bl')=>/l'l bl.
apply/negPn/negP=>/count_memPn brem.
move:al=>/perm_to_rem /allP /(_ b).
rewrite mem_cat bl/= =>/(_ Logic.eq_refl); rewrite brem.
case ab: (a == b); first by move=>_; move: al'=>/negP; apply; move: ab=>/eqP->.
by move=>/=/eqP/count_memPn/negP; apply.
Qed.

Section ereal_tblattice.
Variable (R : realDomainType).
Local Open Scope ereal_scope.

(* PRed to MathComp-Analysis: https://github.com/math-comp/analysis/pull/859 *)
(*
Definition ereal_blatticeMixin :
  Order.BLattice.mixin_of (Order.POrder.class (@ereal_porderType R)).
exists (-oo); exact leNye.
Defined.
Canonical ereal_blatticeType := BLatticeType (\bar R) ereal_blatticeMixin.


Definition ereal_tblatticeMixin :
  Order.TBLattice.mixin_of (Order.POrder.class (ereal_blatticeType)).
exists (+oo); exact leey.
Defined.
Canonical ereal_tblatticeType := TBLatticeType (\bar R) ereal_tblatticeMixin.
(* /PRed *)
*)

(* Note: Should be generalized to tbLatticeType+orderType, but such a structure is not defined. *)
Lemma ereal_joins_lt
    (J : Type) (r : seq J) (P : {pred J}) (F : J -> \bar R) (u : \bar R) :
    -oo < u ->
  (forall x, P x -> F x < u) -> \join_(x <- r | P x) F x < u.
Proof. by move=>u0 ltFm; elim/big_rec: _ => // i x Px xu; rewrite ltUx ltFm. Qed.

Lemma ereal_meets_gt
  (J : Type) (r : seq J) (P : {pred J}) (F : J -> \bar R) (u : \bar R) :
  u < +oo ->
  (forall x, P x -> u < F x) -> u < \meet_(x <- r | P x) F x.
Proof. by move=>u0 ltFm; elim/big_rec: _ => // i x Px xu; rewrite ltxI ltFm. Qed.

End ereal_tblattice.

Section bigop_partition.

Lemma perm_eq_partition {aT rT : eqType} (l : seq aT) (s : seq rT) (f : aT -> rT) :
  uniq s -> all (fun x=> f x \in s) l -> perm_eq [seq x | y <- s, x <- [seq x <- l | f x == y]] l.
Proof.
elim: s l; first by case.
move=>y s IHs l yus /allP fl /=.
move: (perm_filterC (fun x=> f x == y) l)=>/(_ l); rewrite perm_refl; apply perm_trans.
rewrite map_id; apply perm_cat=>//.
have->: [seq x | y0 <- s, x <- [seq x <- l | f x == y0]] = [seq x | y0 <- s, x <- [seq x <- [seq x <- l | predC (fun x : aT => f x == y) x] | f x == y0]].
   clear IHs fl.
   elim: s y yus=>// y' s IHl y /andP[]; rewrite in_cons negb_or=> /andP [yy' ys] /andP[_ us] /=; congr cat; last by apply/IHl/andP; split.
   rewrite 2!map_id -filter_predI; apply eq_filter=>x.
   apply/idP/idP.
      by move=>/=/eqP->; rewrite eq_refl eq_sym.
   by move=>/andP[].
apply IHs; first by move:yus=>/andP[].
by apply/allP=>x; rewrite mem_filter=>/andP [/= /negPf fxy /fl]; rewrite in_cons=>/orP; case=>//; rewrite fxy.
Qed.

Lemma big_partition {aT rT : eqType} {R : Type} {idx : R} {op : Monoid.com_law idx} {F : aT -> R} {l : seq aT} {s : seq rT} {f : aT -> rT} :
  uniq s -> all (fun x=> f x \in s) l ->
  \big[op/idx]_(i <- l) F i = \big[op/idx]_(y <- s) \big[op/idx]_(i <- l | f i == y) F i.
Proof.
move=>us fs.
move:(@big_allpairs_dep _ idx op _ _ _ (fun i j=> j) s (fun i=> [seq j <- l | f j == i]) F); congr eq.
   by apply/perm_big/perm_eq_partition.
by apply congr_big=>//y _; rewrite big_filter.
Qed.

End bigop_partition.
