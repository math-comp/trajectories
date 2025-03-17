From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq  choice fintype order.
From mathcomp Require Import binomial  bigop ssralg poly ssrnum ssrint rat.

From mathcomp Require Import polydiv polyorder path interval polyrcf.

(** Descates method 1 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
(** ** Sign changes *)

Section SignChange.

Variable R :realDomainType.
Implicit Type l: (seq R).
Implicit Type p: {poly R}.

Definition all_eq0 l := all (fun x => x == 0) l.
Definition all_ge0 l:= all (fun x => 0 <= x) l.
Definition all_le0 l := all (fun x => x <= 0) l.
Definition all_ss a l := all (fun x => 0 <= x * a) l.
Definition opp_seq l := [seq - z | z <- l].
Definition filter0 l := [seq z <- l | z != 0].

(** Some helper lemmas *)

Lemma product_neg (a b : R): a * b < 0 -> a != 0 /\ b != 0.
Proof.
case (eqVneq a 0) => [->|]; first by rewrite mul0r ltxx.
case (eqVneq b 0) => [->|] //; by rewrite mulr0 ltxx.
Qed.

Lemma square_pos (a: R): a != 0 -> 0 < a * a.
Proof. by move => anz; rewrite lt0r sqr_ge0 sqrf_eq0 anz. Qed.

Lemma prodNsimpl_ge (a b x: R): b * a < 0 -> 0 <= x * b -> x * a <= 0.
Proof.
move => pa; move: (square_pos (proj1 (product_neg pa))) => pb.
by rewrite - (nmulr_lle0 _ pa) mulrA - (mulrA _ _ b) mulrAC pmulr_lle0.
Qed.

Lemma prodNsimpl_gt (a b x: R): b * a < 0 -> 0 < x * b -> x * a < 0.
Proof.
move => pa; move: (square_pos (proj1 (product_neg pa))) => pb.
by rewrite - (nmulr_llt0 _ pa) mulrA - (mulrA _ _ b) mulrAC pmulr_llt0.
Qed.

Lemma prodNsimpl_lt (a b x: R): b * a < 0 -> x * b < 0 -> 0 < x * a.
Proof.
move => pa; move: (square_pos (proj1 (product_neg pa))) => pb.
by rewrite - (nmulr_lgt0 _ pa) mulrA - (mulrA _ _ b) mulrAC pmulr_lgt0.
Qed.

Lemma all_rev l q: all q l = all q (rev l).
Proof. by elim:l => [// | a l hr]; rewrite rev_cons all_rcons /= hr. Qed.

Lemma has_split q l: has q l ->
     exists l1 a l2, [/\ l = l1 ++ a :: l2, q a & all (fun z => ~~(q z)) l1].
Proof.
elim:l => // a l Hrec /=; case ha: (q a) => /=.
  by move => _; exists [::], a, l; split => //.
move /Hrec => [l1 [b [l2 [-> pb pc]]]].
by exists (a::l1),b,l2; split => //=; rewrite ha pc.
Qed.

Lemma has_split_eq l: has (fun z => z != 0) l ->
  exists l1 a l2, [/\ l = l1 ++ a :: l2, a !=0 & all_eq0 l1].
Proof.
move/has_split => [l1 [a [l2 [-> pa pb]]]]; exists l1,a,l2; split => //.
by apply /allP => x; move /(allP pb); case (x==0).
Qed.

Lemma has_split_eq_rev l: has (fun z => z != 0) l ->
  exists l1 a l2, [/\ l = l1 ++ a :: l2, a !=0 & all_eq0 l2].
Proof.
have <- : (has (fun z : R => z != 0)) (rev l) = has (fun z : R => z != 0) l.
  by elim:l => [// | a l hr]; rewrite rev_cons has_rcons /= hr.
move/has_split_eq => [l1 [a [l2 [lv pa pb]]]]; exists (rev l2),a,(rev l1).
by rewrite -(cat1s a) catA cats1 -rev_cons -rev_cat -lv revK /all_eq0 -all_rev.
Qed.

Lemma opp_seqK l: opp_seq (opp_seq l) = l.
Proof.
by rewrite/opp_seq -map_comp; apply map_id_in => a /=; rewrite opprK.
Qed.

Definition tail_coef p := p `_(\mu_0 p).
Definition lead_tail_coef p := (tail_coef p) * (lead_coef p).

Lemma tail_coef0a p: ~~ (root p 0) ->  tail_coef  p = p`_0.
Proof. by move /muNroot; rewrite /tail_coef => ->. Qed.

Lemma tail_coef0b p: p`_0 != 0 ->  tail_coef  p = p`_0.
Proof. rewrite - {1} horner_coef0; apply: tail_coef0a. Qed.

Lemma tail_coefM (p q: {poly R}):
   tail_coef (p*q) = (tail_coef p) * (tail_coef q).
Proof.
rewrite /tail_coef.
case pnz: (p!=0); last by rewrite (eqP(negbFE pnz)) mul0r mu0 coef0 mul0r.
case qnz: (q!=0); last by rewrite (eqP(negbFE qnz)) mulr0 mu0 coef0 mulr0.
rewrite (mu_mul 0 (mulf_neq0 pnz qnz)).
move: (mu_spec 0 pnz) (mu_spec 0 qnz); rewrite subr0.
set a := (\mu_0 p); set b:= (\mu_0 q); move => [pa v1 ->] [qa v2 ->].
by rewrite mulrACA -exprD 3! coefMXn ! ltnn ! subnn  - ! horner_coef0 hornerM.
Qed.

Lemma lead_tail_coefM (p q: {poly R}):
  lead_tail_coef (p*q) = (lead_tail_coef p)  * (lead_tail_coef q).
Proof. by rewrite /lead_tail_coef -mulrACA -tail_coefM lead_coefM. Qed.

Lemma lead_tail_coef_opp p: lead_tail_coef (- p) = (lead_tail_coef p).
Proof.
rewrite - mulrN1 lead_tail_coefM; set one := (X in _ * lead_tail_coef(X)).
suff : lead_tail_coef one = 1 by  move ->; rewrite mulr1.
have ->: one = ((-1)%:P) by rewrite polyCN.
by rewrite /lead_tail_coef /tail_coef lead_coefC mu_polyC coefC mulN1r opprK.
Qed.

Lemma mu_spec_supp p: p != 0 ->
   exists q, [/\  p = q * 'X^ (\mu_0 p), (~~ root q 0),
     lead_coef p = lead_coef q, tail_coef p = tail_coef q &
     tail_coef q = q`_0].
Proof.
move /(mu_spec 0) => [q pa]; set n := (\mu_0 p) => ->; exists q.
rewrite lead_coefM tail_coefM {1 2} subr0 (eqP (monicXn R n)) mulr1 /tail_coef.
by rewrite mu_exp mu_XsubC mul1n subr0 coefXn eqxx mulr1 (muNroot pa).
Qed.

Lemma tail_coefE p: tail_coef p = (head 0 (filter0 p)).
Proof.
have [-> |] := (eqVneq p 0); first by rewrite /tail_coef mu0 coef0 polyseq0 /=.
move /(mu_spec_supp) => [q [pa pb pc pd pe]]; rewrite  /filter0.
case (eqVneq q 0) => qnz; first by move: pb; rewrite qnz root0.
have q0nz: q`_0 != 0 by rewrite - horner_coef0.
rewrite pd pe pa polyseqMXn// -cat_nseq filter_cat (eq_in_filter (a2 := pred0)).
  by rewrite filter_pred0 cat0s nth0; move: q0nz; case q; case => //= a l _ ->.
have /allP h: all (pred1 (0:R)) (nseq (\mu_0 p) 0).
  by rewrite all_pred1_nseq.
by move => x /h /= ->.
Qed.

Fixpoint changes (s : seq R) : nat :=
  (if s is a :: q then (a * (head 0 q) < 0)%R + changes q else 0)%N.
Definition schange (l: seq R) := changes (filter0 l).

Lemma schange_sgr l: schange l = schange [seq sgr z | z <- l].
Proof.
rewrite /schange /filter0 filter_map; set s1 := [seq z <- l | z != 0].
set s := (filter (preim _ _)); have -> : s l = s1.
  apply: eq_in_filter => x xl /=.
  by rewrite sgr_def; case xz: (x!=0); rewrite ?mulr0n ?eqxx ?mulr1n ?signr_eq0.
elim: s1 => [ // | a l1 /= ->]; case l1 => /=; first by rewrite !mulr0.
by move => b l2; rewrite - sgrM sgr_lt0.
Qed.


Lemma schange0_odd l: last 0 l != 0 ->
   odd (schange l + (0 < head 0 (filter0 l) * last 0 l)%R).
Proof.
rewrite /schange.
have -> : filter0 l = [seq z <- 0::l | z != 0].
  by rewrite /filter0 {2}  /filter eqxx.
rewrite (lastI 0 l); set b := (last 0 l) => bnz; rewrite filter_rcons bnz.
set s := [seq z <- belast 0 l | z != 0].
have: all (fun z => z != 0) s by apply : filter_all.
elim: s; first by rewrite /= mulr0 ltxx square_pos //.
move => c s /=; set C:= changes _; set d:= head 0 _ => hr /andP [cnz etc].
have dnz: d != 0 by move: etc; rewrite /d; case s => // s' l' /= /andP [].
rewrite addnC addnA addnC; move: (hr etc).
rewrite -sgr_gt0 - (sgr_gt0 (c*b)) - sgr_lt0 ! sgrM.
rewrite /sgr - if_neg   - (if_neg (c==0))- (if_neg (b==0)) bnz dnz cnz.
by case: (d<0); case: (b<0); case: (c<0); rewrite ?mulrNN ? mulr1 ?mul1r ?ltr01
    ?ltrN10 ? ltr10 ? ltr0N1 ?addn0 ? addnS ?addn0//=; move => ->.
Qed.

Lemma schange_odd p : p != 0 -> odd (schange p + (0 < lead_tail_coef p)%R).
Proof.
rewrite - lead_coef_eq0 /lead_tail_coef tail_coefE /schange lead_coefE nth_last.
by move => h; rewrite schange0_odd.
Qed.

Lemma schange_cat l1 a l2: a != 0 ->
  schange (l1++a::l2) = (schange (l1++[::a]) + schange (a::l2)) %N.
Proof.
move => anz.
rewrite /schange /filter0 filter_cat cats1 filter_rcons anz.
set w := [seq z <- a :: l2 | z != 0].
elim [seq z <- l1 | z != 0]; first by rewrite /= mulr0 ltxx.
move => b l /= ->.  rewrite - addnA. congr addn.
by rewrite -cats1 /w; case l => //=; rewrite anz.
Qed.

Lemma schange_nz l i j:  l`_i * l`_j < 0 -> (0 < (schange l))%N.
Proof.
move=> pn; move: (product_neg pn) => [xnz ynz].
have aux: forall k, l`_k !=0 -> l`_k \in (filter0 l).
  move => k kz; rewrite mem_filter kz /= mem_nth //.
  by case (leqP (size l) k) => h //; move: kz;rewrite nth_default // eqxx.
move: pn (aux _ xnz) (aux _ ynz); set x := l`_i; set y := l`_j.
move: (filter_all (fun z => z!=0) l); rewrite /schange -/(filter0 l).
case (filter0 l) => //.
move => a l2 pa pb pc pd.
wlog : x y pb pc pd / a * x < 0.
   move => H; case (ltrgt0P (a * x)) => h; try apply: (H x y pb pc pd h).
     apply: (H y x) => //; [by rewrite mulrC | exact: (prodNsimpl_gt pb h)].
   move: pa => /= /andP [anz _].
   by move /eqP: h; rewrite mulf_eq0 (negbTE anz) (negbTE xnz).
move: pc; rewrite inE; case /orP.
  by move /eqP <- => h; move: (lt_trans pb (prodNsimpl_lt pb h)); rewrite ltxx.
move:  pa; clear; move:a x; elim l2 => //.
move => a l H b x /= /andP [bnz bl]  ca bcn.
case (ltrgt0P (b * a)); last first.
  by move /eqP; rewrite mulf_eq0 (negbTE bnz)=> /= ane; move: bl; rewrite ane.
  move=> ->.
  by rewrite add1n ltnS.
rewrite mulrC; move => ba; move: (prodNsimpl_gt bcn ba) => aca.
rewrite (ltNge (a * b)) (ltW ba) add0n.
apply:  (H a x bl) => //; move: ca; rewrite inE; case /orP => // /eqP xa.
by  move: (lt_trans bcn ba); rewrite xa mulrC ltxx.
Qed.

Fixpoint schange_index_aux l i y :=
  if l is x::l' then
    if (((y==0) && (x != 0)) || (x*y < 0)) then i :: schange_index_aux l' i.+1 x
      else schange_index_aux l' i.+1 y
    else [::].

Definition schange_index l := schange_index_aux l 0 0.

Notation SIA := schange_index_aux.  (* local short notation *)

(** We study the sign change function *)

Lemma schangei_addm l n m a:
   SIA l (n+m)%N a = [seq (z+m)%N | z <- SIA l n a].
Proof.
move: n a; elim: l => [  n z // | a l hrec n y /=].
by case hyp: ((y == 0) && (a != 0) || (a * y < 0))=> //=; rewrite - addSn hrec.
Qed.

Lemma schangei_s0 l1 l2: all_eq0 l1 ->
  schange_index (l1 ++ l2) = SIA l2 (size l1) 0.
Proof.
elim l1 => // a l hrec /= /andP [/eqP -> /hrec].
rewrite /schange_index /= mul0r eqxx ltxx andbF orbF.
by rewrite - addn1 - (addn1 (size l)) ! schangei_addm => <-.
Qed.

Lemma schangeE l: (size (schange_index l)).-1 = (schange l).
Proof.
transitivity ((size (schange_index (filter (fun z => z != 0) l))).-1).
  have aux: forall l, (all_eq0 l) ->  filter (fun z => z != 0) l = [::].
    by elim => // a l' Hr /= /andP [-> /Hr ->].
  rewrite /schange; case alz: (all_eq0 l).
    by rewrite  (aux _ alz) - {1} (cats0 l) schangei_s0.
  move: (negbT alz); rewrite - (has_predC) => /has_split_eq.
  move => [l1 [b [l2 [-> pb pc]]]]; rewrite filter_cat aux //= pb.
  rewrite schangei_s0 // /schange_index /= eqxx pb /=.
  move: b (size l1).+1 1%N pb; elim: l2 => // a l' Hrec b n m bnz /=.
  case (eqVneq a 0).
    by move => ->; rewrite mul0r eqxx ltxx andbF /=; apply: Hrec.
  move =>h; rewrite h /= (negbTE bnz) /=.
  by case h':(a * b < 0); [ simpl; congr S |]; apply: Hrec.
move: (filter_all (fun z => z != 0) l); rewrite -/(filter0 l).
rewrite /schange; case (filter0 l) => // a s /= /andP [anz ar].
rewrite /schange_index /SIA -/SIA eqxx anz andbT orTb /=.
move: 1%N a anz ar; elim:s; first by move => a n _ _ /=; rewrite mulr0 ltxx.
move => a s Hrec n b bnz /= /andP [anz ar]; rewrite mulrC anz (negbTE  bnz) /=.
case h:(b * a < 0) => /=;  rewrite Hrec // add0n.
have:  (0 < b * a) by rewrite lt0r mulf_neq0 // leNgt h.
case (ltrgt0P a) => ap //; last by move: anz; rewrite ap eqxx.
  by rewrite (pmulr_lgt0) // => bp; rewrite ! (pmulr_rlt0).
by rewrite (nmulr_lgt0) // => bp; rewrite ! (nmulr_rlt0).
Qed.

Lemma schangei0 l: all_eq0 l <-> schange_index l = [::].
Proof.
split; first by move /schangei_s0 => h; move: (h [::]); rewrite /= cats0.
suff: forall l n, SIA l n 0 = [::] -> all_eq0 l by apply.
elim  => [ // | a l' hrec n].
by rewrite /= eqxx mulr0 ltxx orbF andTb; case az: (a==0) => //= /hrec.
Qed.

Lemma schangei_s0n l1 a l2: a !=0 -> all_eq0 l1 ->
  schange_index (l1 ++a :: l2) = size l1 :: (SIA l2 (size l1).+1  a).
Proof. by move => anz alz; rewrite (schangei_s0 _ alz) /= eqxx anz. Qed.

Lemma schangei_snn l i s:
 schange_index l = i::s -> exists l1 a l2,
  [/\ l = l1 ++a :: l2, a != 0, i = size l1, all_eq0 l1 &
     SIA l2 (size l1).+1 a = s].
Proof.
case alt: (all_eq0 l); first by move /schangei0:alt => -> //.
move: (allPn (negbT alt)) => /hasP /has_split_eq [l1 [a [l2 [ -> az al0]]]].
rewrite (schangei_s0n _ az al0) => /eqP;rewrite eqseq_cons.
by move => /andP [/eqP <- /eqP <-];exists l1, a, l2.
Qed.

Lemma schangei_reca a l n: a != 0 -> ((all_ss a l) = (SIA l n a == [::])).
Proof.
move => anz; move: n; elim: l => [// | b l h n].
by rewrite /= (negbTE anz)/= (h n.+1) ltNge; case sab: (0 <= b * a).
Qed.


Lemma schangei_rec a l1 l2 n: a != 0 -> all_ss a l1 ->
  SIA (l1++l2) n a = SIA l2 (n + size l1)%N a.
Proof.
move => anz; move: n; elim : l1;first by move =>n /=; rewrite addn0.
move =>b l hrec n /= /andP [pa pb].
by rewrite ltNge pa (negbTE anz) /= (hrec _ pb) addnS addSn.
Qed.

Lemma schangei_recb a l1 b l2 n: b * a  < 0 -> all_ss a l1 ->
  SIA (l1++ b::l2) n a = (n+size l1)%N :: SIA l2 (n + size l1).+1 b.
Proof.
move => h1 h2; move : (product_neg h1) => [bz az].
by rewrite (schangei_rec _ _ az h2) /= bz h1 orbT.
Qed.

Lemma schangei_recc a l i s n: a!= 0 ->
  SIA l n a = i :: s -> exists l1 b l2,
    [/\ l = l1 ++ b :: l2, b *a  <0, b!= 0, (all_ss a l1) &
     (i = n+size l1)%N  /\  SIA l2 (n + size l1).+1 b = s].
Proof.
move => anz;case alz: (all_ss a l).
  by move: alz; rewrite (schangei_reca _ n anz) => /eqP ->.
move: (negbT alz); rewrite - (has_predC) => /has_split [l1 [b [l2 [-> pb pc]]]].
move: pb => /=; rewrite - ltNge => abn.
case bz: (b!=0); last by move: abn; rewrite (eqP (negbFE bz)) mul0r ltxx.
have pc': all_ss a l1 by apply /allP => t /(allP pc) /= /negbNE.
rewrite (schangei_recb l2 n abn pc') => /eqP h.
by exists l1,b, l2; move: h; rewrite eqseq_cons => /andP [/eqP <- /eqP ->].
Qed.

Lemma schangei_tail l i s:
  schange_index l = rcons s i -> exists l1 a l2,
  [/\ l = l1 ++ a :: l2, (i <= size l1)%N, 0 < a * l`_i & all_eq0 l2].
Proof.
move => h.
suff [l1 [a [l2 [-> pa pb pc]]]]: exists l1 (a : R) l2,
  [/\ l = l1 ++ a :: l2, a != 0, i = size l1 & all_ss a l2].
  have:has (fun z => z != 0) (a::l2) by rewrite /= pa.
  move /has_split_eq_rev => [la [b [lb [qa qb qc]]]].
  exists (l1++la),b, lb.
  rewrite pb size_cat leq_addr nth_cat ltnn subnn /= qa catA; split => //.
  have: b \in a :: l2 by  rewrite qa mem_cat mem_head orbT.
  rewrite lt0r (mulf_neq0 qb pa) /= in_cons =>/orP []; last by move /(allP pc).
  by move /eqP => ->; rewrite sqr_ge0.
move: h;case: s.
  move /schangei_snn => [l1 [a [l2 [ -> pb pc pd pe]]]]; exists l1, a, l2.
  by split => //; move: pe => /eqP; rewrite -schangei_reca.
move => j s; move /schangei_snn => [l1 [a [l2 [-> pb pc _]]]] h.
suff [l0 [b [l3 [-> qb -> qd]]]]: exists l0 b l3, [/\ l2 = l0 ++ b :: l3, b !=0,
   i = ((size l1).+1 + size l0)%N & all_ss b l3 ].
  by exists (l1++a::l0),b,l3; rewrite - catA cat_cons addSnnS size_cat //=.
move: l2 a pb (size l1).+1 h; clear; elim: s.
  move => l b bnz n /= h.
  move: (schangei_recc bnz h)=> [l1 [c [l2 [-> pa cz pb [pc pd]]]]].
  by exists l1,c,l2; split => //; move:pd => /eqP; rewrite - schangei_reca.
move => a l Hrec l2 b bnz n.
move /(schangei_recc bnz) => [l1 [c [l3 [-> pa cz pb [pc]]]]].
move /(Hrec _ _  cz _) => [l0 [d [l4 [-> qa -> qc]]]].
by exists ( l1 ++ c :: l0), d,l4; rewrite -catA cat_cons addSnnS size_cat addnA.
Qed.

Lemma schangei_correct l (i : nat):
  i \in schange_index l -> l`_i != 0 /\ l`_i * (0::l)`_i <= 0.
Proof.
move: {2 3} (schange_index l) (refl_equal (schange_index l)); case => //.
have aux: forall i l n a,
   i \in SIA l n a -> exists2 j:nat,  j \in SIA l 0 a & i = (j + n)%N.
  by move => i' l' n a; rewrite -(add0n n) schangei_addm; move /mapP.
move => k s /schangei_snn [l1 [a [l2 [-> anz il1 l1z sv]]]].
rewrite inE; case/ orP.
  move /eqP ->; rewrite !nth_cat il1 ltnn subnn /=; split => //.
  rewrite -cat_cons nth_cat /= ltnS leqnn -last_nth.
  suff : (last 0 l1 == 0) by move => /eqP ->; rewrite mulr0.
  by move: (mem_last 0 l1); rewrite inE => /orP; case => //; move /(allP l1z).
rewrite - sv => isv.
move : (aux i l2 (size l1).+1 a isv) => [j j2 j1].
rewrite j1 addnC nth_cat - cat_cons nth_cat addSn - addnS ltnNge leq_addr /=.
rewrite addnC addnK /= addSn ltnNge ltnS leq_addl /= -addnS addnK.
move: j2; clear il1 l1z isv j1 sv k s l1 l i.
move: {1} 0%N {1} (SIA l2 0 a) (refl_equal (SIA l2 0 a)) => n s.
move:s l2  a n j anz; elim.
  by move => l2 a n j _; rewrite -(add0n n) schangei_addm; case (SIA l2 0 a).
move => a s Hrec l b n j bnz => eq1;symmetry in eq1.
move: (schangei_recc bnz eq1)=> [l1 [c [l3 [pa pb cz pc [pd pe]]]]] => js.
have: (j + n)%N \in SIA l n b.
   by rewrite-{2} (add0n n) schangei_addm; apply /mapP; exists j.
rewrite eq1 in_cons => /orP [].
  rewrite pd addnC eqn_add2l => /eqP ->.
  rewrite pa - cat_cons nth_cat ltnn subnn; split => //.
  rewrite /= - (cat_cons) nth_cat /= ltnS leqnn -last_nth.
  move: (mem_last b l1)=> /orP;case; first by move/eqP => ->;apply: ltW.
  by rewrite mulrC; move/(allP pc); apply prodNsimpl_ge; rewrite mulrC.
rewrite - pe - addnS (addnC n) schangei_addm; move /mapP.
move => [j0 ka] /eqP; rewrite eqn_add2r => /eqP => ->.
move: ka; rewrite -(add0n (size l1).+1) schangei_addm => /mapP [k jv ->].
symmetry in pe; move: (Hrec l3 c (n + size l1).+1 k cz pe jv).
rewrite pa  - cat_cons ! nth_cat - addSnnS leqNgt ltnS leq_addl /=.
by rewrite addnK /= addSnnS leqNgt ltnS leq_addl /=  addnK.
Qed.

Lemma pol_mul_cs (p: {poly R}) (x: R):
  p !=0 -> x > 0 -> ( (schange p) < (schange (p * ('X - x%:P))%R))%N.
Proof.
move => pnz xn.
set q := _ * _.
have spp: size p = (size p).-1.+1.
  by move: pnz; rewrite -size_poly_eq0; case sz:(size p).
set s := (schange_index p).
have pa: forall k:nat, k \in s -> p`_k * q`_k < 0.
  move => k ks.
  move: (schangei_correct ks) => [eq1 eq2].
  have rhsp: 0 < p`_k * (p`_k * x) by rewrite mulrA pmulr_lgt0 // square_pos.
  rewrite /q mulrBr coefB coefMC mulrBr subr_lt0 coefMX (le_lt_trans _ rhsp)//.
  by move: eq2; case k.
have: schange_index p = s by [].
have lcpnz: lead_coef p != 0 by rewrite lead_coef_eq0.
have lpp: lead_coef p \in  polyseq p by apply: mem_nth; rewrite {2} spp.
move: (eq_refl s); rewrite {1}/s; case s.
  by  move /eqP /schangei0 => ap; move:lcpnz; move /(allP ap): lpp => ->.
move => i l0 _ sv0.
have pb: 0 < p`_(last 0%N s) * q`_(size p).
  have -> : q`_(size p) = lead_coef p.
    move: (monicXsubC x) => mc; rewrite- (lead_coef_Mmonic p mc) lead_coefE.
    by rewrite (size_Mmonic pnz mc) size_XsubC addn2.
  move: (lastI i l0) lcpnz; rewrite - sv0 => sv1.
  move:(schangei_tail sv1) => [l1 [a [l2 [pv sl1 pn]]]].
  have ->: last 0%N s = (last i l0) by rewrite /s sv1 last_rcons.
  have: lead_coef p = last 0 p by rewrite (last_nth 0) spp.
  rewrite pv last_cat last_cons; case l2.
    move => /= ->; move: pn; rewrite pv - cat1s catA mulrC.
    by rewrite (nth_cat 0 (l1 ++ [:: a])) size_cat addn1 ltnS sl1.
  by move => b l anz lpv; rewrite (allP lpv) // anz /= mem_last.
have rec0: forall l1 l2, l2`_0 != 0 -> (schange (l2) <= schange (l1++l2))%N.
  by move => l1; case => // a l2 /= anz; rewrite (schange_cat _ _ anz) leq_addl.
have ncat: forall l1 l2 b, (l1++l2)`_( (size l1) +b) = l2`_b.
  by move=> l1 l2 b; rewrite nth_cat addKn -ltn_subRL subnn.
move: pa pb;rewrite -{1} schangeE /s sv0 /=.
move: sv0 => /schangei_snn [l1 [a [l2 [-> pa pb pc pd]]]] ha hb.
have he: (l1 ++ a :: l2)`_i = a by rewrite nth_cat pb ltnn subnn.
have skm: forall k, (l1 ++ a :: l2)`_(k + i) = (a::l2)`_k.
  by move => k; rewrite addnC pb ncat.
have hc: a * q`_i < 0 by rewrite -he;apply: ha; rewrite mem_head.
have[l2a [l2b [l2v sl]]]: exists l2a l2b, l2a ++ l2b = q /\ size l2a = i.
   exists (take i q), (drop i q); split; first by exact: cat_take_drop.
   apply: size_takel; case /orP:(leq_total i (size q)) => //.
   by move/(nth_default 0) => h; move: hc; rewrite h mulr0 ltxx.
move: (hc); rewrite -l2v nth_cat -sl ltnn subnn => hc'.
apply: (leq_trans _ (rec0 l2a l2b (proj2 (product_neg hc')))).
have sv:[seq (z + i)%N | z <- SIA l2 1 a] = l0 by rewrite pb -pd -schangei_addm.
have: forall k, k \in (SIA l2 1 a) -> (a::l2)`_(k-0)%N * l2b`_(k-0%N) < 0.
  move => k ka; rewrite - skm subn0.
  have ->: l2b`_k = q`_(k+i) by rewrite -l2v - sl addnC ncat.
  by apply: ha;rewrite inE - sv (mem_map (@addIn i)) ka orbT.
have: 0 < (a :: l2)`_((last 0%N (SIA l2 1 a)) -0) * l2b`_(size l2).+1.
   move: hb; rewrite -sv /= (last_map (fun z=> (z + i)%N) (SIA l2 1 a) 0%N).
  by rewrite subn0 skm - l2v size_cat -pb - sl ncat.
rewrite - sv size_map.
move: rec0 ncat hc' pa; clear; move => rec0 ncat hc' pa.
move: {2 3 4 5} (SIA l2 1 a) pa (erefl  (SIA l2 1 a)) hc'.
rewrite - (addn0 1%N); move: {2  4 5 6 7} 0%N.
move => n s;  move: s a n  l2 l2b; elim.
  move => a n l l' _ anz pnz;set j := (size l).+1 %N.
  rewrite /last subnn {1}/nth  mulrC ; move => lt2 _.
  move:(prodNsimpl_gt pnz lt2);apply: schange_nz.
move => i s  Hrec a n l l' anz.
move /(schangei_recc anz)=> [l1 [b [l2 [-> pa pb pc [pd pe]]]]].
move => qa qb qc /=.
have imn: (i - n = (size l1).+1) %N by rewrite pd addnAC add1n addnK.
have: (i\in  i :: s) by  rewrite mem_head.
move /qc; rewrite imn -cat1s catA  nth_cat subnn ltnn - imn => e1.
set ni := (i - n )%N.
move: (cat_take_drop ni l').
set l1' := take ni l'; set l2' := drop ni l' => e2.
have e3: size l1' = ni.
  move: e1;rewrite size_take; case (leqP (size l') ni) => //.
  by move/(nth_default 0) => ->; rewrite mulr0 ltxx.
move: (prodNsimpl_lt qa pa); rewrite mulrC => e4.
move: (prodNsimpl_gt e1 e4) => e5.
move: (proj2 (product_neg e5)); set w := l'`_ni => wnz.
have [u l2v]: exists u, l2' = w::u.
  move: wnz;rewrite /w - e2 nth_cat e3 ltnn subnn.
  case l2'; [  by rewrite eqxx | by move => a1 b1 _; exists b1].
move: (schange_cat l1' u wnz); rewrite - l2v e2 => ->.
suff: ((size s) < schange l2')%N.
  set l1'' := (l1' ++ [:: w]).
  have : l1''`_0 * l1''`_ni < 0.
    move: e5; rewrite -e2 l2v  /l1'' !nth_cat e3 ltnn subnn; case i => //.
  by move/schange_nz => e6 e7; move: (leq_add e6 e7); rewrite add1n.
clear u l2v.
have r0: b * l2'`_0 < 0 by move: e1; rewrite - e2 nth_cat e3 ltnn subnn.
move: pe; rewrite -pd - add1n => r1.
have r2 : (forall k, k \in s -> (b :: l2)`_(k - i) * l2'`_(k - i) < 0).
  move => k ks; have: k \in i::s by  rewrite inE ks orbT.
  move: ks; rewrite -{1} r1 schangei_addm; move /mapP => [k' k'v kv].
  have ->: (k - i)%N = k' by rewrite kv addnK.
  move/ qc; rewrite - e2 - cat1s catA.
  have ->: (k - n = k' + (size l1).+1)%N.
    by rewrite kv pd addnAC add1n addnA addnK.
  by rewrite addnC ncat -imn -/ni -e3 ncat.
have r3:  0 < (b :: l2)`_(last i s - i) * l2'`_(size l2).+1.
  move:qb; rewrite - e2 size_cat - addSn - imn -/ni -e3 ncat.
  suff: ((last n (i :: s) - n) = ni + (last i s - i)) %N.
    by move => ->; rewrite /ni imn - cat1s catA ncat.
  have lni: (n<=i) %N by rewrite pd addnAC leq_addl.
  rewrite -r1 schangei_addm; case (SIA l2 1 b); first by rewrite /= subnn addn0.
  move => n0 l0 /=; set la := last _ _.
  have eq1: (i <= la)%N.
    by rewrite /la (last_map  (fun z=> (z + i)%N)) leq_addl.
  by rewrite - {1} (subnK eq1) - (addnBA _ lni) addnC.
exact: (Hrec b i l2 l2' pb r1 r0 r3 r2).
Qed.

End SignChange.

Section SignChangeRcf.
Variable R : rcfType.
Implicit Type p : {poly R}.

Lemma noproots_cs p:  (forall x, 0 <x -> ~~ root p x) -> 0 < lead_tail_coef p.
Proof.
move => h.
have [pz |pnz]:= (eqVneq p 0); first by move: (h _ ltr01); rewrite pz root0.
move: (mu_spec_supp pnz) => [q [pa pb pc pd pe]].
have: {in `[0, +oo[, (forall x, ~~ root q x)}.
  move=> x; rewrite in_itv/= andbT le0r; case/orP; first by move=>/eqP ->.
  by move /h; rewrite pa rootM negb_or  => /andP [].
move/sgp_pinftyP => ha; move: (ha 0).
rewrite in_itv/= lexx /= => H.
rewrite /lead_tail_coef pc pd pe - sgr_gt0 sgrM -/(sgp_pinfty q).
by rewrite - horner_coef0 - H // - sgrM sgr_gt0 lt0r sqr_ge0 mulf_neq0.
Qed.

Definition fact_list p s q :=
 [/\  p = (\prod_(z <- s) ('X - z.1%:P) ^+ (z.2)) * q,
      (all (fun z => 0 < z) [seq z.1 | z <- s]),
      (sorted <%R [seq z.1 | z <- s]) &
      (all (fun z => (0<z)%N ) [seq z.2 | z <- s])].

Lemma poly_split_fact p : { sq : (seq (R * nat) * {poly R}) |
  fact_list p (sq.1) (sq.2) &
    ( (p != 0 -> (forall x, 0 <x -> ~~ root (sq.2) x))
   /\ (p = 0 -> sq.1 = [::] /\ sq.2 = 0)) }.
Proof.
case pnz: (p != 0); last  first.
  by exists ([::],p) => //; split => //; rewrite big_nil mul1r.
pose sa := [seq z <- rootsR p |  0 <z ].
pose sb := [seq  (z, \mu_z p) | z <- sa].
have sav: sa = [seq z.1 | z <- sb].
   by rewrite /sb -map_comp; apply/esym/map_id_in.
have pa: (all (fun z => 0 < z) [seq z.1 | z <- sb]).
  by rewrite - sav; apply /allP => x; rewrite mem_filter => /andP [].
have pb : (sorted <%R [seq z.1 | z <- sb]).
  rewrite -sav.
  by apply: sorted_filter => //; [apply: lt_trans |apply: sorted_roots].
have pc: (all (fun z => (0<z)%N ) [seq z.2 | z <- sb]).
  apply /allP => x /mapP [t] /mapP [z]; rewrite mem_filter => /andP [z0 z2].
  move => -> -> /=; rewrite mu_gt0 //; apply: (root_roots z2).
suff: { q | p = (\prod_(z <- sa) ('X - z%:P) ^+ (\mu_z p))  * q &
  forall x : R, 0 < x -> ~~ root q x}.
  move => [q qa qb]; exists (sb,q) => //.
    by split => //;rewrite qa /= big_map; congr (_ * _); apply eq_big.
  by split => // pz; move: pnz; rewrite pz eqxx.
clear sb sav pa pb pc.
have: all (root p) sa.
    apply/allP=> x;rewrite mem_filter =>/andP [_]; apply /root_roots.
have: uniq sa by apply:filter_uniq; apply: uniq_roots.
have: forall x, root p x -> 0 < x -> x \in sa.
  by move=> x rx xp;rewrite mem_filter xp -(roots_on_rootsR pnz) rx.
move: sa=> s.
elim: s p pnz=>[p _ H _ _| ].
   exists p; first by by rewrite big_nil mul1r.
   move => x xp;apply/negP =>nr; by move: (H _ nr xp).
move => a l Hrec /= p p0 rp /andP [nal ul] /andP [ap rap].
have [q rqa pv] := (mu_spec a p0).
case q0: (q != 0); last by move:p0; rewrite pv (eqP(negbFE q0)) mul0r eqxx.
have q1 x: root q x -> 0 < x -> x \in l.
  move=> rx xp; case xa: (x == a); first by rewrite -(eqP xa) rx in rqa.
  by rewrite -[_ \in _]orFb -xa -in_cons rp // pv rootM rx.
have q2: all (root q) l.
  apply/allP=> x xl.
  case xa: (x ==a); first by move: nal; rewrite - (eqP xa) xl.
  move /(allP rap): xl.
  by rewrite  pv rootM -[\mu__ _]prednK ?mu_gt0 // root_exp_XsubC xa orbF.
have [r qv rq]:= (Hrec q  q0  q1 ul q2).
exists r => //; rewrite {1} pv {1} qv mulrAC; congr (_ * _).
rewrite big_cons mulrC; congr (_ * _).
rewrite (big_nth 0).
rewrite [in RHS](big_nth 0).
rewrite 2!big_mkord; apply: eq_bigr => i _.
set b := l`_i;congr (_ ^+ _).
have rb: root q b by apply /(allP q2); rewrite mem_nth //.
have nr: ~~ root (('X - a%:P) ^+ \mu_a p) b.
   rewrite /root horner_exp !hornerE expf_neq0 // subr_eq0; apply /eqP => ab.
   by move: rqa; rewrite - ab rb.
rewrite pv mu_mul ? (muNroot nr) // ?addn0//.
by rewrite  mulf_neq0 // expf_neq0 // monic_neq0 // monicXsubC.
Qed.

Definition pos_roots p := (s2val (poly_split_fact p)).1.
Definition pos_cofactor p := (s2val (poly_split_fact p)).2.
Definition npos_roots p :=  (\sum_(i <- (pos_roots p)) (i.2)) %N.

Lemma pos_split1 p (s := pos_roots p) (q:= pos_cofactor p):
  p != 0 -> [/\ fact_list p s q, (forall x, 0 <x -> ~~ root q x) &  q != 0].
Proof.
move => h; rewrite /s/q /pos_roots / pos_cofactor.
move: (poly_split_fact p) => H; move: (s2valP' H) (s2valP H) => [h1 _] h2.
split => //; first by apply: h1.
by apply/eqP => qz; move:h2 => [] pv; move: h; rewrite {1} pv qz mulr0 eqxx.
Qed.


Lemma monicXsubCe (c:R) i : ('X - c%:P) ^+ i  \is monic.
Proof. apply:monic_exp; exact: monicXsubC. Qed.

Lemma monic_prod_XsubCe I rI (P : pred I) (F : I -> R) (G : I -> nat):
  \prod_(i <- rI | P i) ('X - (F i)%:P )^+ (G i) \is monic.
Proof. by apply: monic_prod => i _; exact: monicXsubCe. Qed.

Lemma npos_root_parity p: p != 0 ->
  odd (npos_roots p + (0< lead_tail_coef p)%R).
Proof.
move => pnz; move: (pos_split1 pnz) => [[pv pb pc] pd qp qnz].
rewrite {2} pv;set r := \prod_(z <- _) _.
have rm: r \is monic by apply:monic_prod_XsubCe.
rewrite lead_tail_coefM (pmulr_lgt0 _ (noproots_cs qp)) /lead_tail_coef.
move: (refl_equal (sgr r`_0)); rewrite - {2} horner_coef0 horner_prod.
set X := \prod_(z <- _) _; have ->: X = \prod_(i <- pos_roots p) (- i.1)^+ i.2.
  by apply: eq_big => // i _; rewrite horner_exp hornerXsubC sub0r.
have ->: Num.sg (\prod_(i <- pos_roots p) (- i.1) ^+ i.2) =
 (-1) ^+ \sum_(i <-  pos_roots p) (i.2).
  move: pb; elim (pos_roots p) => [ _ | i rr /= Hr /andP [pa pb]].
    by rewrite !big_nil sgr1.
  by rewrite !big_cons sgrM sgrX Hr // sgrN  (gtr0_sg pa) exprD.
move => aux.
case (eqVneq r`_0 0) => nr0.
  by move: aux; rewrite nr0 sgr0 => /eqP; rewrite eq_sym signr_eq0.
rewrite (eqP rm) mulr1 (tail_coef0b nr0) -sgr_gt0 aux - signr_odd signr_gt0.
by case h: (odd(npos_roots p)); [  rewrite addn0 | rewrite addn1 /= h].
Qed.

Lemma size_prod_XsubCe I rI (F : I -> R) (G : I -> nat)  :
  size (\prod_(i <- rI) ('X - (F i)%:P)^+ (G i)) =
  (\sum_(i <- rI) (G i)).+1.
Proof.
elim: rI => [| i r /=]; rewrite ? big_nil ? size_poly1 // !big_cons.
rewrite size_monicM ? monicXsubCe  ? monic_neq0 // ?monic_prod_XsubCe //.
by rewrite size_exp_XsubC => ->; rewrite addSn addnS.
Qed.

Lemma schange_parity p:  p != 0 -> odd (npos_roots p) = odd (schange p).
Proof.
move => pnz.
move: (npos_root_parity pnz) (schange_odd pnz).
case h: (0 < lead_tail_coef p)%R; last by rewrite  !addn0 => ->.
by rewrite ! addn1 /= => /negbTE -> /negbTE ->.
Qed.

Lemma descartes p:  p != 0 ->
  (odd (npos_roots p) = odd (schange p) /\
  ((npos_roots p) <= (schange p)) %N).
Proof.
move => pa; split; first by apply:schange_parity.
move: (pos_split1 pa); rewrite /npos_roots; move => [[p1 p2 p3 p4] p5 qnz].
have [s [sa <- <-]]: exists s, [/\ (all [eta <%R 0] s),
    size s =  (\sum_(i <- pos_roots p) i.2)%N &
    \prod_(z <- s) ('X - z%:P) * pos_cofactor p = p].
  rewrite {3}p1;move: p2;elim: (pos_roots p) => [_ | a l Hrec /= /andP [q1 q2]].
    by exists [::]; rewrite ! big_nil.
  move: (Hrec q2) => [s [s1 s2 s3]]; exists ((nseq a.2 a.1) ++ s).
  rewrite all_cat s1 ! big_cons -s2 size_cat size_nseq andbT; split => //.
    have:  all (pred1 a.1) (nseq a.2 a.1).
      by rewrite all_pred1_nseq.
    by move => h; apply /allP => x; move /(allP h) => /= /eqP ->//.
  rewrite big_cat /= - ! mulrA -s3 ;congr ( _ * _).
  rewrite (big_nth 0) big_mkord (eq_bigr (fun _ => ('X - a.1%:P)))=>[|[i]] /=.
    by rewrite prodr_const card_ord size_nseq.
  by rewrite size_nseq nth_nseq=> ->.
move: (pos_cofactor p) sa qnz ;clear; elim s; first by move => p _ pnz  //.
move => a l Hrec p /= /andP [ap alp] pnz.
rewrite big_cons - mulrA mulrC; move: (Hrec _ alp pnz); set q := _ * _ => e1.
have qnz: q !=0
  by rewrite mulf_neq0 //; apply: monic_neq0; apply: monic_prod_XsubC.
exact (leq_ltn_trans  e1 (pol_mul_cs qnz ap)).
Qed.

End SignChangeRcf.
