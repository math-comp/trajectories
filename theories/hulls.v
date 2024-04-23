Require Export encompass conv.
From mathcomp Require Import all_ssreflect all_algebra vector reals normedtype.
From mathcomp Require Import classical_sets boolp mathcomp_extra.
Require Import counterclockwise.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp.algebra_tactics Require Import ring.
From mathcomp.zify Require Import zify.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Section hull_def.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Definition hull (R : realType) (T : lmodType R) (X : set T) : set T :=
  [set p : T | exists n (g : 'I_n -> T) (d : 'I_n -> R),
    [/\ (forall i, 0 <= d i)%R,
    (\sum_(i < n) d i = 1%R),
    g @` setT `<=` X &
    p = \sum_(i < n) (d i) *: (g i)] ].
End hull_def.

Module Spec := SpecKA(ccw_KA).

Section spec.
Variable R : realType.
Let Plane := Plane R.

Open Scope ring_scope.
Open Scope order_scope.

Section hull_prop.
Local Open Scope classical_set_scope.
Variable A : lmodType R.
Implicit Types X Y : set A.

Lemma subset_hull X : X `<=` hull X.
Proof.
move=> x xX; rewrite /hull; exists 1%N, (fun=> x), (fun=>1%R).
split=> //.
- by rewrite big_ord_recl big_ord0 addr0.
- by move=> d [i _ <-].
- by rewrite big_ord_recl big_ord0 scale1r addr0.
Qed.

Lemma hull0 : hull set0 = set0 :> set A.
Proof.
rewrite funeqE => d; rewrite propeqE; split => //.
move=> [n [g [e [e0 e1 gX ->{d}]]]].
destruct n as [|n]; first by rewrite big_ord0 in e1; move:(@ltr01 R); rewrite e1 ltxx.
exfalso; apply: (gX (g ord0)); exact/imageP.
Qed.

Lemma hull_eq0 X : (hull X == set0) = (X == set0).
Proof.
apply/idP/idP=> [/eqP abs|]; last by move=> /eqP ->; rewrite hull0.
apply/negPn/negP => /set0P[/= d] => dX.
move: abs; rewrite funeqE => /(_ d); rewrite propeqE /set0 => -[H _]; apply H.
exact/subset_hull.
Qed.

Lemma hull_monotone X Y : X `<=` Y -> hull X `<=` hull Y.
Proof.
move=> H a [n [g [d [d0 d1 gX ae]]]]; exists n, g, d; split => //.
by eapply subset_trans; first exact: gX.
Qed.

Lemma hull2 (x y : A) :
  hull [set x; y]%classic = ((fun t => x <| t |> y) @` `[0%R, 1%R])%classic.
Proof.
rewrite eqEsubset; split; last first.
   move=> z [t /andP [t0 t1]] <-.
   rewrite bnd_simp in t0, t1.
   exists 2%N, (fun i => if i == 0 then x else y),
               (fun i => if i == 0 then t else `1- t).
   split; first by case; case=>//= n _; rewrite subr_ge0.
   - by rewrite big_ord_recl big_ord1/= addrCA subrr addr0.
   - by move=>a[]; case; case=>/= [|n] _ _ <-; [left|right].
   - by rewrite big_ord_recl big_ord1.
move=>z [n][g][d][d0 d1 gxy ->].
move:d1=>/esym/eqP; rewrite -subr_eq0 (bigID [pred i | g i == x])//= opprD.
rewrite addrCA addrC subr_eq0=>/eqP/esym=>d1.
exists (\sum_(i < n | g i == x) d i).
   rewrite inE; apply/andP; rewrite 2!bnd_simp {2}d1 -[(_<=1)%R]subr_ge0 opprB.
   by rewrite addrCA subrr addr0; split; apply sumr_ge0.
rewrite/conv {2}d1 opprB addrCA subrr addr0 [RHS](bigID [pred i | g i == x])//=.
congr (_ + _); rewrite scaler_suml; apply: congr_big=>// i.
   by move=> /eqP ->.
have /gxy[->|->//] : range g (g i) by [].
by rewrite eqxx.
Qed.

Lemma hull_convex X : forall x y,
  (hull X) x -> (hull X) y -> hull [set x; y] `<=` hull X.
Proof.
move=> + + [n][g][d][d0 d1 gX->] [m][h][e][e0 e1 hX ->].
rewrite hull2=>_ _ x [t] /andP.
rewrite !bnd_simp -[(_ <= 1)%R]subr_ge0 => [[t0 t1]] <-.
exists (n + m)%N, (fun i=> match split i with inl i => g i | inr i => h i end),
                  (fun i=> match split i with inl i => t * (d i)
                                            | inr i => (`1- t) * e i end); split.
- by move=>i; case: (split i)=>j; apply mulr_ge0.
- rewrite big_split_ord/= -{1}(add_onemK t); congr +%R.
    rewrite -{3}(mulr1 t) -{1}d1 mulr_sumr; apply congr_big=>// i _.
    case: (splitP (lshift m i)).
      by move=>j ij; congr (_ * d _); apply val_inj.
    by move=> k/= ink; move: (ltn_ord i); rewrite ink -ltn_subRL subnn ltn0.
  rewrite -{2}(mulr1 (`1- t)) -{1}e1 mulr_sumr; apply congr_big=>// i _.
  case: (splitP (rshift n i))=>/=.
    by move=> j/= nij; move: (ltn_ord j); rewrite -nij -ltn_subRL subnn ltn0.
  by move=>j /eqP; rewrite eqn_add2l=>/eqP ij; congr (_ * e _); apply val_inj.
- by move=>y/= [i] _; case: split=>j <-; [ apply gX | apply hX ].
- rewrite big_split_ord /conv; congr +%R; rewrite scaler_sumr;
   apply congr_big => // i _; rewrite scalerA.
  + case: (splitP (lshift m i)).
      by move=> j ij; congr (_ * d _ *: g _); apply val_inj.
    by move=> k/= ink; move: (ltn_ord i); rewrite ink -ltn_subRL subnn ltn0.
  + case: (splitP (rshift n i)) =>/=.
      by move=> j/= nij; move: (ltn_ord j); rewrite -nij -ltn_subRL subnn ltn0.
    by move=> j /eqP; rewrite eqn_add2l => /eqP ij; congr (_ * e _ *: h _); apply val_inj.
Qed.

End hull_prop.

Let oriented := fun p q r : Plane => 0%:R <= det p q r.

Lemma is_left_oriented (p q r : Plane) :
  encompass.is_left oriented p q r = oriented p q r.
Proof.
apply/idP/idP; last by rewrite/encompass.is_left; move=>->; rewrite !orbT.
by move=>/or3P[| |//] /eqP re; subst r; rewrite /oriented det_cyclique; [ rewrite det_cyclique |]; rewrite det_alternate.
Qed.

Lemma encompass_correct (l : seq Plane) (p : Plane) :
  uniq l ->
  (3 <= size l)%N ->
  encompass (ccw (R:=R)) l l ->
  encompass oriented [:: p] l ->
  exists t : 'I_(size l) -> R,
    (forall i, 0 <= t i)%R /\ (\sum_i t i = 1%:R) /\ p = \sum_i t i *: l`_i.
Proof.
move: l p.
have orientedW: forall a b c, encompass.is_left oriented a b c -> oriented a b c.
   move=>a b c /or3P[| |//] /eqP<-; rewrite /oriented.
         by rewrite 2!det_cyclique det_alternate.
      by rewrite det_cyclique det_alternate.
have H3 a b c p : uniq [:: a; b; c] ->
    encompass (ccw (R:=R)) [:: a; b; c] [:: a; b; c] ->
    encompass oriented [::p] [:: a; b; c] ->
    exists t : 'I_3 -> R, (forall i, 0 <= t i)%R /\ (\sum_i t i = 1%:R) /\ p = \sum_i t i *: [:: a; b; c]`_i.
  rewrite/uniq !in_cons negb_or 2!in_nil 2!orbF=>/andP [/andP[/negPf ab /negPf ac] /andP[/negPf bc _]] /andP[/andP [_ /andP [h _]] _] /= /andP [/andP [/orientedW cap _]] /andP [/andP [/orientedW abp _]] /andP [/andP [/orientedW bcp _] _].
  move: h; rewrite/encompass.is_left bc eq_sym ab =>/= cab.
  exists (fun i => [:: det c p b / det c a b; det c a p / det c a b; det p a b / det c a b]`_i); split.
      case; case; [| case; [| case=>//]]; move=>/= _; (apply mulr_ge0; [| by rewrite invr_ge0; apply ltW]).
      - by rewrite 2!det_cyclique.
      - by [].
      - by rewrite det_cyclique.
   move: cab; rewrite /ccw lt0r=>/andP[cab _].
   split.
      by rewrite !big_ord_recr big_ord0 /= add0r -2!mulrDl addrC addrA -decompose_det divff.
   rewrite !big_ord_recr big_ord0 /= add0r.
   apply (scalerI cab).
   rewrite 2!scalerDr 3!scalerA 3!mulrA 3![det c a b * _]mulrC -3!mulrA divff// 3!mulr1.
   apply/pair_eqP; apply/andP; split; apply/eqP; rewrite !develop_det /xcoord /ycoord; cbn; ring.
move=> l p.
elim: l=>// a; case=>// b; case=>// c; case.
   by move=>IHl abc _; apply H3.
move=>d l IHl lu sl ll lp.
case labp: (oriented b (last d l) p).
   move:H3=>/(_ a b (last d l) p); case.
      - move: lu; apply subseq_uniq=>/=.
        by rewrite eq_refl eq_refl -/(subseq [:: last d l] (c :: d :: l)) sub1seq in_cons mem_last orbT.
      - apply (Spec.encompassll_subseq lu)=>//.
        by rewrite /= eq_refl /= eq_refl -/(subseq [:: last d l] (c :: d :: l)) sub1seq in_cons mem_last orbT.
      - apply/andP; split.
         by move:lp=>/andP[lp _]; move:lp.
      apply/andP; split.
         by move:lp=>/andP[_ /andP[ap _]].
      by rewrite /=/encompass.is_left labp !orbT.
   move=>f [f0 [f1 fp]].
   exists (fun i:'I_(size l).+4 => (i == ord0)%:R * f ord0 + (i == lift ord0 ord0)%:R * f (lift ord0 ord0) + (i == ord_max)%:R * f ord_max).
   split.
      move=>i.
      apply addr_ge0; [apply addr_ge0|]; apply mulr_ge0; try apply f0; apply ler0n.
   split; rewrite big_ord_recr /= eq_refl mul1r 2!mul0r 2!add0r big_ord_recl /= mul1r 2!mul0r 2!addr0 big_ord_recl /= mul1r 2!mul0r addr0 add0r.
      rewrite -f1 ![\sum_i f _]big_ord_recl big_ord0 addr0 -!addrA; congr (_ + (_ + _)).
      rewrite -[f (lift _ (lift _ _))]add0r; congr (_ + f _); last by apply val_inj.
      rewrite -{3}(mul0r (\sum_(i < (size l).+1) 0)) mulr_sumr.
      apply congr_big=>// [[i ilt]] _.
   have ->: (widen_ord (leqnSn (size l).+3) (lift ord0 (lift ord0 (Ordinal ilt))) == ord_max) = false.
         by apply /negP=>/eqP/(f_equal val)/=; rewrite /bump/= 2!add1n=>/eqP; rewrite 2!eqSS=>/eqP ile; move:ilt; rewrite -ile ltnn.
      by rewrite 3!mul0r 2!addr0.
   rewrite fp ![\sum_i f _ *: _]big_ord_recl big_ord0 addr0 -!addrA; congr (_ + (_ + _)).
   rewrite (nth_last _ (d :: l))/= -[f (lift _ (lift _ _)) *: _]add0r; congr (_ + f _ *: _); last by apply val_inj.
   rewrite -{1}(scale0r (\sum_(i < (size l).+1) 0)) scaler_sumr.
   apply congr_big=>// [[i ilt]] _.
   have ->: (widen_ord (leqnSn (size l).+3) (lift ord0 (lift ord0 (Ordinal ilt))) == ord_max) = false.
      by apply /negP=>/eqP/(f_equal val)/=; rewrite /bump/= 2!add1n=>/eqP; rewrite 2!eqSS=>/eqP ile; move:ilt; rewrite -ile ltnn.
   by rewrite 2!mul0r 2!addr0 2!scale0r.
case: IHl.
   - by move: lu=>/andP[_ lu].
   - by [].
   - move: ll=>/Spec.encompassll_subseq; apply=>//; apply subseq_cons.
   - apply/andP; split.
      2: by move: lp=>/andP[_ /andP [_ lp]].
   rewrite/= andbT; apply/or3P/Or33.
   by rewrite/oriented det_inverse 2!det_cyclique leNgt oppr_lt0; apply/negP=>/ltW; move: labp; rewrite /oriented=>->.
move=>f [f0 [f1 fp]].
exists (fun i=>
   match ord_S_split i with
   | inleft j => f (proj1_sig j)
   | inright _ => 0%:R
   end).
split.
   by move=>i; case: (ord_S_split i).
split; rewrite big_ord_recl; (case (ord_S_split ord0); [ by move=>[j H] | move=>_]); [| rewrite scale0r]; rewrite add0r.
   rewrite -f1; apply congr_big=>// [[i ilt]] _.
   case (ord_S_split _)=>// [[j jlt]] /=; congr (f _); apply val_inj=>/=.
   by move:jlt=>/(f_equal val)=>/=/eqP; rewrite /bump/= 2!add1n eqSS=>/eqP.
rewrite fp; apply congr_big=>// [[i ilt]] _.
case (ord_S_split _)=>// [[j jlt]] /=; congr (f _ *: _); apply val_inj=>/=.
by move:jlt=>/(f_equal val)=>/=/eqP; rewrite /bump/= 2!add1n eqSS=>/eqP.
Qed.

Lemma detD (p q r : Plane) : det 0 p (q+r) = det 0 p q + det 0 p r.
Proof. by rewrite 3!det_scalar_productE /scalar_product/=; ring. Qed.

Lemma det_sum (p : Plane) (n : nat) (f : 'I_n -> Plane) :
  det 0 p (\sum_(i < n) f i) = \sum_(i < n) det 0 p (f i).
Proof.
elim: n f.
   by move=>f; rewrite 2!big_ord0 -det_cyclique det_alternate.
move=>n IHn f.
by rewrite 2!big_ord_recl detD IHn.
Qed.

Lemma encompass_complete (l : seq Plane) (p : Plane) :
  uniq l ->
  (3 <= size l)%N ->
  encompass (ccw (R:=R)) l l ->
  (exists t : 'I_(size l) -> R,
    (forall i, 0 <= t i)%R /\
    (\sum_i t i = 1%:R) /\
    p = \sum_i t i *: l`_i) ->
  encompass oriented [:: p] l.
Proof.
move=>lu ls ll [f [f0 [f1 fp]]]; subst p.
rewrite encompass_all_index; apply/andP; split.
   by case: l lu ls ll f f0 f1.
apply/forallP=>[[i ilt]].
rewrite/= andbT is_left_oriented /oriented.
wlog: l lu ls ll f f0 f1 i ilt / l`_i == 0%R.
   move=>h.
   set l' := [seq x - l`_i | x <- l].
   have subl': forall a b, (a < size l) -> (b < size l) -> l'`_a - l'`_b = l`_a - l`_b.
      by move=>a b al bl; rewrite (nth_map 0)// (nth_map 0)// opprD [-_ - - _]addrC -!addrA; congr GRing.add; rewrite addrA subrr add0r.
   suff: (0%:R <= det l'`_i l'`_(Zp_succ (Ordinal ilt)) (\sum_(i0 < size l) f i0 *: l'`_i0))%R.
      congr (_ <= _)%R; rewrite 2!det_scalar_productE; congr (scalar_product _ (rotate _)).
      - by apply subl'=>//; case: (Zp_succ (Ordinal ilt)).
      - rewrite [l'`_i](nth_map 0)// subrr subr0 -[l`_i]scale1r.
      have->: (1 = 1%:R)%R by [].
      rewrite -f1 scaler_suml -sumrB; apply congr_big=>// [[j jlt]] _.
      by rewrite -scalerBr (nth_map 0).
   move:h=>/(_ l'); rewrite size_map; apply.
      - rewrite map_inj_uniq=>//; apply addIr.
      - by [].
      - rewrite Spec.encompassll_spec.
         2: by rewrite map_inj_uniq=>//; apply addIr.
      apply/andP; split.
         by destruct l.
      rewrite size_map.
      apply/forallP=>[[a alt]].
      apply/forallP=>[[b blt]].
      apply/forallP=>[[c clt]].
      apply/implyP=>abc.
      rewrite /ccw_KA.OT /ccw det_scalar_productE subl'// subl'//.
      by move:ll; rewrite Spec.encompassll_spec=>// /andP[_] /forallP /(_ (Ordinal alt)) /forallP /(_ (Ordinal blt)) /forallP /(_ (Ordinal clt)) /implyP /(_ abc); rewrite /ccw_KA.OT /ccw det_scalar_productE.
      - apply f0.
      - exact f1.
      - by rewrite (nth_map 0)// subrr.
move=>/eqP li0; rewrite li0 det_sum; apply sumr_ge0=>[[j jlt]] _.
rewrite det_scalar_productE 2!subr0 rotateZ scalar_productZR; apply mulr_ge0.
   apply f0.
move:ll; rewrite encompassE =>/andP[_ /allP ll].
have/ll: l`_(Ordinal jlt) \in l by rewrite mem_nth.
rewrite encompass_all_index=>/andP[_] /forallP /(_ (Ordinal ilt))/=; rewrite andbT.
rewrite li0// => /or3P[/eqP ->|/eqP ->|].
- by rewrite -{2}(scale0r 0) rotateZ scalar_productZR mul0r.
- by rewrite scalar_product_rotatexx.
- by rewrite /ccw det_scalar_productE 2!subr0=>/ltW.
Qed.

Lemma encompassP (l : seq Plane) (p : Plane) :
  uniq l ->
  (3 <= size l)%N ->
  encompass (ccw (R:=R)) l l ->
  reflect (p \in hull (fun x => x \in l)) (encompass oriented [:: p] l).
Proof.
move=>lu ls ll; apply/(iffP idP).
   move=>/(encompass_correct lu ls ll)[f [f0 [f1 ->]]].
   rewrite inE/hull/=; exists (size l), (fun i=> l`_i), f; split => //.
   by move =>// x/= [i] _ <-{x}; exact: (@mem_nth Plane).
rewrite inE/hull/= =>[[n [g [d [d0 d1 gl pe]]]]].
apply encompass_complete=>//.
exists (fun i=> \sum_(j < n | g j == l`_i) d j); split.
   by move=>i; apply sumr_ge0.
split.
   rewrite -(big_map (fun i: 'I_(size l) => l`_i) xpredT (fun x=> \sum_(j < n | g j == x) d j)).
   rewrite (map_comp (fun i : nat => l`_i) (@nat_of_ord (size l))).
   move:(val_enum_ord (size l)); rewrite enumT=>->.
   rewrite map_nth_iota0// take_size -big_partition//.
   by apply/allP=>i _; apply gl.
transitivity (\sum_(i < size l) \sum_(j < n | g j == l`_i) d j *: g j).
   rewrite -(big_map (fun i: 'I_(size l) => l`_i) xpredT (fun x=> \sum_(j < n | g j == x) d j *: g j)).
   rewrite (map_comp (fun i : nat => l`_i) (@nat_of_ord (size l))).
   move:(val_enum_ord (size l)); rewrite enumT=>->.
   rewrite map_nth_iota0// take_size -big_partition//.
   by apply/allP=>i _; apply gl.
apply congr_big=>//i _.
rewrite scaler_suml.
by apply congr_big=>//j/eqP->.
Qed.

End spec.
