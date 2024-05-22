From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq  choice fintype order.
From mathcomp Require Import binomial  bigop ssralg poly ssrnum ssrint rat archimedean.
From mathcomp Require Import polyrcf.
Require Import pol.

(** Defining function over lists of rationals that find lists containing
  exactly one alternation, from negative to positive values. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Order.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.

(** ** Sign changes *)

Section SignChange.

Variable R :realDomainType.
Implicit Type l: (seq R).

Definition all_eq0 l := all (fun x => x == 0) l.
Definition all_ge0 l:= all (fun x => 0 <= x) l.
Definition all_le0 l := all (fun x => x <= 0) l.
Definition all_ss a l := all (fun x => 0 <= x * a) l.
Definition opp_seq l := [seq - z | z <- l].

Fixpoint alternate_1 l :=
  if l is a::tl then
     if 0 < a then all_ge0 tl else alternate_1 tl
  else false.

Fixpoint alternate l :=
  if l is a::tl then
   if a < 0 then alternate_1 tl else
   if  a == 0 then alternate tl else false
  else false.

Fixpoint schange_index_aux l i y :=
  if l is x::l' then
    if (((y==0) && (x != 0)) || (x*y < 0)) then i :: schange_index_aux l' i.+1 x
      else schange_index_aux l' i.+1 y
    else [::].

Definition schange_index l := schange_index_aux l 0 0.

Notation SIA := schange_index_aux.  (* local short notation *)


(** Some helper lemmas *)

Lemma product_neg (a b : R): a * b < 0 -> a != 0 /\ b != 0. 
Proof.
move => h.
case bz: (b!=0); last by move: h; rewrite (eqP (negbFE bz)) mulr0 ltxx.
case az: (a!=0); last by move: h; rewrite (eqP (negbFE az)) mul0r ltxx.
done.
Qed.

Lemma schange_simpl (a b x: R): b * a < 0 -> 0 <= x * b -> x * a <= 0.
Proof.
move => pa.
rewrite - (nmulr_lle0 _ pa) mulrA - (mulrA _ _ b) mulrAC pmulr_lle0 //.
by rewrite lt0r sqr_ge0 sqrf_eq0 (proj1 (product_neg pa)).
Qed.


Lemma schange_simpl1 (a b x: R): b * a < 0 -> 0 < x * b -> x * a < 0.
Proof.
move => pa.
rewrite - (nmulr_llt0 _ pa) mulrA - (mulrA _ _ b) mulrAC pmulr_llt0 //.
by rewrite lt0r sqr_ge0 sqrf_eq0 (proj1 (product_neg pa)).
Qed.


Lemma schange_simpl2 (a b x: R): b * a < 0 -> x * b < 0 -> 0 < x * a.
Proof.
move => pa.
rewrite - (nmulr_lgt0 _ pa) mulrA - (mulrA _ _ b) mulrAC pmulr_lgt0 //.
by rewrite lt0r sqr_ge0 sqrf_eq0 (proj1 (product_neg pa)).
Qed.

Lemma all_rev l p: all p l = all p (rev l).
Proof. by elim:l => [// | a l hr]; rewrite rev_cons all_rcons /= hr. Qed.

Lemma has_split p l: has p l ->
     exists l1 a l2, [/\ l = l1 ++ a :: l2, p a & all (fun z => ~~(p z)) l1].
Proof.
elim:l => // a l Hrec /=; case ha: (p a) => /=.
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

Lemma opp_seqK l :opp_seq (opp_seq l) = l.
Proof.
by rewrite/opp_seq -map_comp; apply map_id_in => a /=; rewrite opprK.
Qed.

(** We give here a specification for alternate *)

Lemma alternate1_p l1 x l2:
  all_eq0 l1 -> x <0 -> alternate_1 l2 -> alternate (l1++x :: l2).
Proof.
elim:l1; first by move => _ xn h //=; rewrite xn.
by move => a l Hrec /= /andP [az lz] xz; rewrite az (eqP az) ltxx; apply: Hrec.
Qed.

Lemma alternate_1P (l: seq R):
   reflect (exists l1 x l2,
       [/\  l = l1 ++ ( x :: l2), all_le0 l1, all_ge0 l2 & x > 0] )
   (alternate_1  l).
Proof.
apply: (iffP idP).
  elim:l => [// | a l Hrec /=]; case: (ler0P a) => sa.
    move => /Hrec [l1 [x [l2 [-> l1n l2p xp]]]].
    by exists (a::l1), x, l2 => /=;rewrite sa.
  by move =>  h1; exists [::], a, l.
move=> [l1 [x [l2 [-> l1n l2p xp]]]].
move: l1 l1n; elim; first by move => _ /=; rewrite xp.
by move => a l1' Hrec /= /andP [] ap / Hrec aux;rewrite ltNge ap.
Qed.

Lemma alternate_P (l: seq R):
   reflect (exists l1 x l2 y l3,
       [/\  l = l1 ++  x :: l2 ++  (y :: l3),  x<0, y> 0
         & [/\ all_eq0 l1,  all_le0 l2& all_ge0 l3]])
   (alternate l).
Proof.
apply: (iffP idP); last first.
  move => [l1 [x [l2 [y [l3 [-> xn yp [l1p l2p l3p]]]]]]].
  have h:alternate_1 (l2 ++y :: l3) by apply /alternate_1P; exists l2, y, l3.
  move: l1p; elim l1; first by rewrite /= xn h.
  by move => a l' hrec /= /andP [ az] /hrec ->; rewrite lt_neqAle az.
elim: l => // a l Hrec /=.
rewrite lt_neqAle; case az: (a==0).
   rewrite andFb => /Hrec [l1 [x [l2 [y [l3 [-> xn yn [l1n l2z l3p]]]]]]].
   exists (a :: l1), x, l2, y,l3; split => //; split => //.
   apply /allP => t; rewrite in_cons; case /orP; last by move/(allP l1n).
   move /eqP;move/eqP: az => -> -> //.
case ane:(a <= 0) => //= /alternate_1P [l1 [x [l2 [-> l1n l2p xp]]]].
by exists [::], a, l1, x,l2; rewrite lt_neqAle az ane.
Qed.

Lemma schangei_Sn l n a: SIA l n.+1 a = [seq z.+1 | z <- SIA l n a].
Proof.
move: n a; elim: l => [  n z // | a l hrec n y /=].
by case hyp: ((y == 0) && (a != 0) || (a * y < 0))=> //=; rewrite hrec.
Qed.

Lemma schangei_addm l n m a:
   SIA l (n+m)%N a = [seq (z+m)%N | z <- SIA l n a].
Proof.
move: n a; elim: l => [  n z // | a l hrec n y /=].
by case hyp: ((y == 0) && (a != 0) || (a * y < 0))=> //=; rewrite - addSn hrec.
Qed.

Lemma schangei_opp l: schange_index l = schange_index (opp_seq l).
Proof.
rewrite /schange_index - {2}oppr0; move: 0 0%N; elim: l; first by done.
by move => a l hrec y n /=; rewrite mulrNN - hrec - hrec ! oppr_eq0.
Qed.

Lemma schangei_s0 l1 l2: all_eq0 l1 ->
  schange_index (l1 ++ l2) = SIA l2 (size l1) 0.
Proof.
elim l1 => // a l hrec /= /andP [/eqP -> /hrec].
by rewrite /schange_index /= mul0r eqxx ltxx andbF orbF !schangei_Sn => ->.
Qed.

Lemma schangei0 l:  all_eq0 l <-> schange_index l = [::].
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

Lemma schangei_rec a l1 l2 n: a != 0 -> all_ss a l1 ->
  SIA (l1++l2) n a = SIA l2 (n + size l1)%N a.
Proof.
move => anz; move: n; elim : l1;first by move =>n /=; rewrite addn0.
move =>b l hrec n /= /andP [pa pb].
by rewrite ltNge pa (negbTE anz) /= (hrec _ pb) addnS addSn.
Qed.

Lemma schangei_reca a l n: a != 0 -> ((all_ss a l) = (SIA l n a == [::])).
Proof.
move => anz; move: n; elim: l => [// | b l h n].
by rewrite /= (negbTE anz)/= (h n.+1) ltNge; case sab: (0 <= b * a).
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

Definition schange l := (size (schange_index l)).-1.

Lemma schange_index_alternate l: (schange l = 1%N) <->
   (alternate l \/ alternate (opp_seq l)).
Proof.
have aux0 : (schange l = 1%N) <->  size (schange_index l) = 2%N.
   rewrite /schange; split; last by move => ->.
   by case (size (schange_index l)) => // n /= ->.
apply:(iff_trans aux0).
have aux: forall l, alternate l -> size (schange_index l) = 2%N.
  move => l0 /alternate_P [l1 [x [l2 [y [l3 [-> xn yp [l1p l2p l3p]]]]]]].
  move: (xn); rewrite lt_neqAle => /andP [xnz _].
  move: (yp); rewrite lt0r => /andP [ynz _].
  have yxn: y * x < 0 by rewrite  pmulr_rlt0.
  have l2p': all_ss x l2 by apply /allP => z/(allP l2p); rewrite nmulr_lge0.
  have l3p': all_ss y l3 by apply /allP => z/(allP l3p); rewrite pmulr_lge0.
  move: l3p'; rewrite (schangei_reca l3 ((size l1).+1 + size l2).+1 ynz).
  by rewrite (schangei_s0n _ xnz l1p) (schangei_recb _ _ yxn l2p') => /eqP->.
have p1a: forall a l, a <0 -> all_ss a l -> all_le0 l.
   by move => a l1 anz h; apply /allP => x /(allP h); rewrite nmulr_lge0.
have p1b: forall b l, 0 <b -> all_ss b l -> all_ge0 l.
  by move => a l1 anz h; apply /allP => x /(allP h); rewrite pmulr_lge0.
have px: forall  a l, a !=0 -> all_ss a l -> all_ss (-a) (opp_seq l).
  move => a l1 anz h; apply /allP => x /mapP [y /(allP h) h1 ->].
  by rewrite mulrNN.
split; last first.
  by case; move /aux => //; rewrite - schangei_opp.
move=> h.
have [i [j]]: exists a b, (schange_index l) = [:: a; b].
   move: h; set s := (schange_index l); case: s => // a; case => // b.
   by case => // _; exists a, b.
move /schangei_snn => [l1 [a [l2 [lv anz iv pr1 pr2]]]].
move: (schangei_recc anz pr2); move =>[l3 [b [l4 [l2v ban bz l3p [jv]]]]].
move /eqP; rewrite - (schangei_reca _ _ bz) => l4p.
move:anz; rewrite neq_lt; case /orP => sa; [left | right];apply /alternate_P.
  exists l1, a, l3, b, l4; move: ban;rewrite lv l2v (nmulr_llt0 b sa) => sb.
  split => //;split; [ exact| apply: (p1a _ _ sa l3p)| apply: (p1b _ _ sb l4p)].
exists (opp_seq l1), (-a), (opp_seq l3), (-b), (opp_seq l4); move: ban.
rewrite (pmulr_llt0 b sa) => bn.
have man: - a < 0 by rewrite oppr_lt0.
have mbp: 0 < - b by rewrite oppr_gt0.
split => //.
  by rewrite lv l2v /opp_seq map_cat map_cons map_cat map_cons.
split.
    by apply /allP => x /mapP [y /(allP pr1) /eqP -> ->]; rewrite oppr0 eqxx.
  by apply (p1a (- a)) => //; apply px => //; move: sa; rewrite lt0r;case /andP.
by apply (p1b (- b)) => //; apply px.
Qed.

Lemma schange_cat l1 a l2: a != 0 ->
  schange (l1++a::l2) = (schange (l1++[::a]) + schange (a::l2)) %N.
Proof.
have aux: forall a b l n m, a * b >0 -> size (SIA l n a) = size (SIA l m b).
  move => c1 c2 l n m cp.
  rewrite -(add0n n) - (add0n m) !schangei_addm ! size_map.
  elim: l => // => u v Hrec /=.
  move: cp; case c1z: (c1 == 0); first by rewrite (eqP c1z) mul0r ltxx.
  case c2z: (c2 == 0); first by rewrite (eqP c2z) mulr0 ltxx.
  rewrite (mulrC u) (mulrC u).
  move => cp; have ->: (c1 * u  < 0) =  (c2 * u < 0).
    apply/idP/idP => h; [ rewrite mulrC in cp |];exact :(schange_simpl1 h cp).
  simpl; case: (c2 * u < 0) => //.
  by rewrite - (add0n 1%N) !schangei_addm ! size_map Hrec.
rewrite /schange -cat1s catA => anz.
have: has (fun z => z != 0) (l1 ++ [:: a]).
  by apply /hasP; exists a => //; rewrite mem_cat mem_head orbT.
move /has_split_eq => [l3 [b [l4 [lv bnz al0]]]].
rewrite lv (schangei_s0n l4 bnz al0) -catA cat_cons (schangei_s0n _ bnz al0).
rewrite /schange_index cat1s {3} /SIA eqxx anz /= - /SIA.
have : a = last b l4 by move: (f_equal (last a) lv); rewrite !last_cat.
move: (size l3).+1 => n; move: {2} (SIA l4 n b)  (erefl (SIA l4 n b)) => s.
clear lv l1; move: n b l4 bnz.
elim: s.
  move => n b l4 bnz h alb; rewrite h add0n.
  have asb: all_ss b l4 by rewrite (schangei_reca _ n bnz) h eqxx.
  rewrite schangei_rec //; apply: aux; rewrite lt0r (mulf_neq0 bnz anz)/=.
  have: a \in b :: l4 by rewrite alb mem_last.
  rewrite inE; case /orP; first by move /eqP -> ; rewrite sqr_ge0.
  by move /(allP asb); rewrite mulrC.
move => i s Hrec n b l4 bnz.
move /(schangei_recc bnz) => [l1 [c [l5 [lv pa pb pc [pd pe]]]]] pf.
have pg: a = last c l5 by rewrite pf lv last_cat last_cons.
rewrite lv - catA cat_cons ! (schangei_recb _ _ pa pc) /=.
by rewrite (Hrec (n + size l1).+1 c l5 pb pe pg) addSn.
Qed.

Lemma schange_index_tail1 s i l n a: a !=0 ->  SIA l n a = rcons s i  ->
  exists l1 b l2, [/\ l = l1 ++ b :: l2, b !=0, i = (n + size l1)%N &
   all_ss b l2 ].
Proof.
move: l n a; elim:s.
  move => l n b bnz /= h.
  move: (schangei_recc bnz h)=> [l1 [c [l2 [-> pa cz pb [pc pd]]]]].
  by exists l1,c,l2; split => //; move:pd => /eqP; rewrite - schangei_reca.
move => a l Hrec l2 n b bnz;rewrite rcons_cons.
move /(schangei_recc bnz) => [l1 [c [l3 [-> pa cz pb [pc]]]]].
move /(Hrec _ _ _  cz) => [l0 [d [l4 [-> qa -> qc]]]].
by exists ( l1 ++ c :: l0), d,l4; rewrite -catA cat_cons addSnnS size_cat addnA.
Qed.

Lemma schange_index_tail2 s i l: schange_index l = rcons s i ->
   exists l1 (a : R) l2,
  [/\ l = l1 ++ a :: l2, a != 0, i = size l1 & all_ss a l2].
Proof.
case: s.
  move /schangei_snn => [l1 [a [l2 [ -> pb pc pd pe]]]]; exists l1, a, l2.
  by split => //; move: pe => /eqP; rewrite -schangei_reca.
move => j s; move /schangei_snn => [l1 [a [l2 [-> pb pc _]]]].
move /(schange_index_tail1 pb)  => [l0 [b [l3 [-> qb -> qd]]]].
exists (l1++a::l0),b,l3; rewrite - catA cat_cons addSnnS size_cat //=.
Qed.


Lemma schange_index_tail l i s :
  schange_index l = rcons s i -> exists l1 a l2,
  [/\ l = l1 ++ a :: l2, (i <= size l1)%N, 0 < a * l`_i & all_eq0 l2].
Proof.
move => /schange_index_tail2 [l1 [a [l2 [-> pa pb pc]]]].
have:has (fun z => z != 0) (a::l2) by rewrite /= pa.
move /has_split_eq_rev => [la [b [lb [qa qb qc]]]].
exists (l1 ++ la),b, lb.
   rewrite pb size_cat leq_addr nth_cat ltnn subnn /= qa catA; split => //.
rewrite lt0r (mulf_neq0 qb pa) /=.
have: b \in a :: l2 by  rewrite qa mem_cat mem_head orbT.
rewrite in_cons =>/orP []; first by move /eqP => ->; rewrite sqr_ge0.
by move /(allP pc).
Qed.

Lemma schange_odd1 x l y: x * y < 0 -> odd (schange (x::l ++ [::y])).
Proof.
move => xy; rewrite /schange.
move: (product_neg xy) => [xnz ynz].
set s := schange_index (x :: l ++ [:: y]).
move: (refl_equal s); rewrite {1} /s; case: s.
  have xl: x \in x :: l ++ [:: y] by rewrite mem_head.
  by move /schangei0 => h; move: xnz; move/(allP h):xl => /eqP ->; rewrite eqxx.
move => i s /=.
rewrite /schange_index /= eqxx xnz orTb => /eqP; rewrite eqseq_cons => /andP.
move => [ _] /eqP.
have ->: (size s)= (((x * y>=0)%R) + size s)%N by rewrite leNgt xy.
clear i xy;move: x xnz 1%N l; elim: s.
  move => x xnz n l => /eqP; rewrite -(schangei_reca _ _ xnz) => ss.
  have: y \in (l ++ [:: y]) by rewrite mem_cat inE eqxx orbT.
  by move /(allP ss); rewrite mulrC => ->.
move => a s Hrec x xnz n l.
move/(schangei_recc xnz)=> [l1 [c [l2 [lv pa cnz pb [pc]]]]].
have cp:0 < c * c by rewrite lt0r sqr_ge0 sqrf_eq0 (proj1 (product_neg pa)).
have ->: (0 <= x * y) = ~~(0 <= c * y).
   rewrite - (nmulr_rle0 (c * y) pa) mulrACA (pmulr_rle0 _ cp).
   by rewrite - ltNge lt_neqAle eq_sym (mulf_neq0  xnz ynz).
move: (f_equal (last c) lv); rewrite !last_cat !last_cons /= addnS.
case l2; first by move => ->; rewrite (ltW cp) /= => <-.
move => i1 l4; rewrite last_cons (lastI i1 l4) - cats1 => <-.
move /(Hrec c cnz (n + size l1).+1 _).
by case b:((0 <= c * y)%R) => //= ->.
Qed.

Lemma schange_index_correct l (i: nat):
  i \in (schange_index l) -> (l`_i != 0 /\ l`_i * (0::l)`_i <= 0).
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
  by rewrite mulrC; move/(allP pc); apply schange_simpl; rewrite mulrC.
rewrite - pe - addnS (addnC n) schangei_addm; move /mapP.
move => [j0 ka] /eqP; rewrite eqn_add2r => /eqP => ->.
move: ka; rewrite -(add0n (size l1).+1) schangei_addm => /mapP [k jv ->].
symmetry in pe; move: (Hrec l3 c (n + size l1).+1 k cz pe jv).
rewrite pa  - cat_cons ! nth_cat - addSnnS leqNgt ltnS leq_addl /=.
by rewrite addnK /= addSnnS leqNgt ltnS leq_addl /=  addnK.
Qed.

Lemma schange_monotone l l' (s:= schange_index l):
     (forall k,  k \in s ->l`_k * l'`_k <0)  ->
     l`_ (last 0%N s) * l'`_(size l) > 0 ->
    (schange l < schange l') %N.
Proof.
have: schange_index l = s by [].
case: s.
   move/schangei0 => alz _; rewrite /last.
   suff: l`_0 = 0 by move => ->; rewrite mul0r ltxx.
   by move: alz; case l => // a l1 /= /andP [/eqP ->].
have rec0: forall l1 l2, l2`_0 != 0 -> (schange (l2) <= schange (l1++l2))%N.
  by move => l1; case => // a l2 /= anz; rewrite (schange_cat _ _ anz) leq_addl.
have rec1: forall l i j, l`_i * l`_j < 0 -> (0 < (schange l))%N.
  move => l1 i j; wlog : i j / (i<= j)%N.
    by case /orP:(leq_total i j)=> cij h; [ | rewrite mulrC]; apply:h.
  move => lij ov.
  move: (product_neg ov) => [anz bnz].
  have st: size (take i l1) = i.
     rewrite size_take;  case (ltnP i (size l1)) => // sl.
     by move: anz; rewrite (nth_default 0 sl) eqxx.
  move: (cat_take_drop i l1) => eq1.
  have e2: l1`_i = (drop i l1)`_0  by rewrite - {1} eq1 nth_cat st ltnn subnn.
  have e3:  (drop i l1)`_0 != 0 by rewrite - e2.
  have e4: l1`_j = (drop i l1)`_(j-i) by rewrite -{1}eq1 nth_cat st ltnNge lij.
  move:ov; rewrite e2 e4; set l3 :=  (drop i l1); set k:= (j - i)%N => ov.
  move: (rec0 (take i l1) l3 e3); rewrite eq1; apply: leq_trans.
  have st': size (take k l3) = k.
     rewrite size_take;  case (ltnP k (size l3)) => // sl.
     by move: bnz; rewrite e4 (nth_default 0 sl) eqxx.
  move: (cat_take_drop k l3) => eq2.
  have l3k: l3`_k =  (drop k l3)`_0 by rewrite - {1} eq2 nth_cat st' ltnn subnn.
  have l3knz: l3`_k != 0 by rewrite   /l3 /k - e4.
  have  [v eq6]: exists v, (drop k l3) = l3`_k:: v.
    move:l3knz; rewrite l3k ;case (drop k l3); last by move => a b _; exists b.
    by rewrite eqxx.
  have [u eq7]: exists u, (take k l3) = l3`_0:: u.
     move: st'; rewrite -{3} eq2; case (take k l3).
       by move => /= kz; move: ov; rewrite -kz ltNge sqr_ge0.
  by  move => a b _; exists b.
  rewrite -eq2 eq6 schange_cat // eq7 cat_cons.
  by move: (schange_odd1 u ov);  set w :=schange _; case w.
have ncat: forall l1 l2 b, (l1++l2)`_( (size l1) +b) = l2`_b.
  by move=> l1 l2 b; rewrite nth_cat addKn -ltn_subRL subnn.
move => i s sil ha hb.
rewrite {1} /schange sil /=; move: sil ha hb.
move /schangei_snn => [l1 [a [l2 [->pa pb pc pd]]]] ha hb.
have he: (l1 ++ a :: l2)`_i = a by rewrite nth_cat pb ltnn subnn.
have skm: forall k, (l1 ++ a :: l2)`_(k + i) = (a::l2)`_k.
  by move => k; rewrite addnC pb ncat.
have hc: a * l'`_i < 0 by rewrite -he;apply: ha; rewrite mem_head.
have[l2a [l2b [l2v sl]]]: exists l2a l2b, l2a ++ l2b = l' /\ size l2a = i.
   exists (take i l'), (drop i l'); split; first by exact: cat_take_drop.
   apply: size_takel; case /orP:(leq_total i (size l')) => //.
   by move/(nth_default 0) => h; move: hc; rewrite h mulr0 ltxx.
move: (hc); rewrite -l2v nth_cat -sl ltnn subnn => hc'.
apply: (leq_trans _ (rec0 l2a l2b (proj2 (product_neg hc')))).
have sv: [seq (z + i)%N | z <- SIA l2 1 a] = s by rewrite pb -pd -schangei_addm.
have: forall k, k \in (SIA l2 1 a) -> (a::l2)`_(k-0)%N * l2b`_(k-0%N) < 0.
  move => k ka; rewrite - skm subn0. 
  have ->: l2b`_k = l'`_(k+i) by rewrite -l2v - sl addnC ncat.
  by apply: ha;rewrite inE - sv (mem_map (@addIn i)) ka orbT.
have: 0 < (a :: l2)`_((last 0%N (SIA l2 1 a)) -0) * l2b`_(size l2).+1. 
   move: hb; rewrite -sv /= (last_map (fun z=> (z + i)%N) (SIA l2 1 a) 0%N).
  by rewrite subn0 skm - l2v size_cat -pb - sl ncat.
rewrite - sv size_map.
clear he sv skm  pb pc pd ha sl s hb l2v hc l2a he l1 l l' i.
move: {2 3 4 5} (SIA l2 1 a) pa (erefl  (SIA l2 1 a)) hc'.
rewrite - (addn0 1%N); move: {2  4 5 6 7} 0%N.
move => n s;  move: s a n  l2 l2b; elim.
  move => a n l l' _ anz pnz;set j := (size l).+1 %N.
  rewrite /last subnn {1}/nth  mulrC ; move => lt2 _.
  move:(schange_simpl1 pnz lt2);apply: rec1.
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
move: (schange_simpl2 qa pa); rewrite mulrC => e4.
move: (schange_simpl1 e1 e4) => e5.
move: (proj2 (product_neg e5)); set w := l'`_ni => wnz.
have [u l2v]: exists u, l2' = w::u.
  move: wnz;rewrite /w - e2 nth_cat e3 ltnn subnn.
  case l2'; [  by rewrite eqxx | by move => a1 b1 _; exists b1].
move: (schange_cat l1' u wnz); rewrite - l2v e2 => ->.
suff: ((size s) < schange l2')%N.
  set l1'' := (l1' ++ [:: w]).
  have : l1''`_0 * l1''`_ni < 0.
    move: e5; rewrite -e2 l2v  /l1'' !nth_cat e3 ltnn subnn; case i => //.
  by move/rec1 => e6 e7; move: (leq_add e6 e7); rewrite add1n.
clear u l2v.
have r0: b * l2'`_0 < 0 by move: e1; rewrite - e2 nth_cat e3 ltnn subnn.
move: pe; rewrite -pd - add1n => r1.
have r2 : (forall k,
     k \in s -> (b :: l2)`_(k - i) * l2'`_(k - i) < 0).
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

Lemma pol_mul_cs (p: {poly R}) (x: R):  
  p !=0 -> x > 0 -> ( (schange p) < (schange (p * ('X - x%:P))%R))%N.
Proof.  
move => pnz xn.
set q := _ * _.
have spp: size p = (size p).-1.+1.
  by move: pnz; rewrite -size_poly_eq0;  case sz:(size p).
have lcpnz: lead_coef p != 0 by rewrite lead_coef_eq0. 
set s := (schange_index p).
suff: (forall k, k \in s -> p`_k * q`_k < 0) /\  
  0 < p`_(last 0%N s) * q`_(size p).
  by move => [pa pb];apply:  schange_monotone.
have -> : q`_(size p) = lead_coef p. 
  move: (monicXsubC x) => mc; rewrite- (lead_coef_Mmonic p mc) lead_coefE.
  by rewrite (size_Mmonic pnz mc) size_XsubC addn2.
have lpp: lead_coef p \in  polyseq p by apply: mem_nth; rewrite {2} spp.
have [heads [lasts sv]]: exists a b, s = rcons a b.
  move: (eq_refl s); rewrite {1}/s; case s.
     by move /eqP /schangei0 => ap; move:lcpnz; move /(allP ap): lpp => ->.
  by move => n l _; rewrite lastI; exists (belast n l), (last n l).
move:(schange_index_tail sv) => [l1 [a [l2 [pv sl1 pn alz]]]].
have ->: last 0%N s = lasts by rewrite sv last_rcons.
have: lead_coef p = last 0 p by rewrite (last_nth 0) spp.
rewrite {1 3} pv last_cat last_cons; move: alz.
case l2; last first.
  move => b l az /= lpv; move: lcpnz.
  have: lead_coef p \in (b :: l) by rewrite lpv mem_last.
  by move /(allP az) => ->.
move => _ /= ->; split; last first.
   move: pn; rewrite pv - cat1s catA mulrC (nth_cat 0 (l1 ++ [:: a])).
   by rewrite size_cat addn1 ltnS sl1.
clear heads lasts sl1 a l2 pv sl1 pn sv. 
move => k ks.
move: (schange_index_correct ks) => [eq1 eq2].
have rhsp: 0 < p`_k * (p`_k * x).
  by rewrite mulrA (pmulr_lgt0 _ xn) lt0r sqr_ge0 sqrf_eq0 eq1.
rewrite /q mulrBr coefB coefMC mulrBr subr_lt0 coefMX (le_lt_trans _ rhsp) //.
by move: eq2; case k. 
Qed.

End SignChange.

Section DescOnOrderedRing.
Variable R :realDomainType.

(** The definitions *)

Definition pol_increasing (p : {poly R}) := {homo (horner p):  x y / x <= y}.

Definition slope_bounded (x k: R) (f: R -> R):=
 forall y z, x <= y <= z -> k * (z - y) <=  f z - f y.

(* on a< t <b, f' >= -k  *) 
Definition slope_bounded2 (a b k: R) (f: R -> R):=
 forall y z, a <= y -> y <= z  -> z <= b -> k * (z - y) <=  f y - f z.

Definition neg_in_interval1 (a b: R) (f: R -> R) :=
  forall z, a <z < b -> f z < 0.
Definition neg_in_interval2 (a b: R) (f: R -> R) :=
  forall z, a <z <= b -> f z < 0.

Definition pos_in_interval (a b: R) (f: R -> R) :=
  forall z, a <z <= b -> 0 < f z.


Definition le_below_x (x: R) (f: R -> R) := 
  (forall y, 0 <= y -> y <= x -> f y <= f x).

(* Here inv stands for "invariant" *)

Definition inv (p: {poly  R}) :=
  forall epsilon, 0 < epsilon ->
    { x |
      [/\ (le_below_x x (horner p)),
        {in <=%R x &, pol_increasing p} &
       (0 < x) && (x * p.[x] <= epsilon)] }.

Definition inv2 (p : {poly R}) :=
  forall epsilon, 0 < epsilon ->  
     {x |
      [/\ (le_below_x x (horner p)),
      {in <=%R x &, pol_increasing p} &
      [&& 0 < x, 0 < p.[x] & x * p.[x] <= epsilon]] }.


(* initial definition said nothing on b *)
Definition one_root1 (p : {poly R}) (a b : R) :=
  exists c d k,
     [/\ [&& a < c, c < d, d < b & 0 < k],
     (pos_in_interval a c (horner p)),
     (neg_in_interval1 d b (horner p)) &
     (slope_bounded2 c d k (horner p))].

Definition one_root2 (p : {poly R}) (a : R) :=
   { ck |
     [/\ (a < ck.1) && (0 < ck.2),
     (neg_in_interval2 a ck.1 (horner p)) &
     (slope_bounded ck.1 ck.2 (horner p))] }.

(** ** Basic properties  *)

Lemma slope_product_x  (f : R -> R) x k:
     0 <= x -> 0 <= k ->
    slope_bounded x k f ->
    forall y z, x <= y <= z ->
     (x * k + f y) * (z - y) <= z * f z - y * f y.
Proof.
rewrite /slope_bounded; move =>x0 kf0 incf y z /andP [xy yz].
rewrite -[z * _] (addrNK (z * f y)) -mulrBr -addrA -mulrBl mulrDl (mulrC (f y)).
move: (le_trans xy yz) => xz.
rewrite lerD2r; apply: le_trans (_ : z * (k * (z - y)) <= _).
  by rewrite - mulrA ler_wpM2r // mulr_ge0 // subr_ge0.
by rewrite ler_wpM2l ? incf ?xy ? yz//;apply:(le_trans x0).
Qed.

(* Note that {poly R} is automatically converted into (seq R) *)

Lemma all_pos_positive (p : {poly R}) x:
  all_ge0 p -> 0 <= x -> p.[x] >= 0.
Proof.
move=> h x0; rewrite horner_coef.
apply: sumr_ge0 => [] [i his _] /=.
apply: mulr_ge0; rewrite ?exprn_ge0 //; apply: (allP h); exact: mem_nth.
Qed.


Lemma all_pos_increasing (p : {poly R}):
  all_ge0 p ->  {in <=%R 0  &, pol_increasing p}.
Proof.
move=>  posp x y le0x le0y lexy; rewrite !horner_coef.
apply: ler_sum => [] [i ihs] /= _.
apply: ler_wpM2l => //; first by apply: (allP posp); exact: mem_nth.
by apply: lerXn2r.
Qed.

Lemma one_root1_uniq p a b: one_root1 p a b ->
     uniqueness (fun z => a < z < b /\ root p z).
Proof.
move => [c [d [k [leqs pa nb dab]]]].
move => z1 z2 [/andP [z1a z1b] /eqP rz1] [/andP [z2a z2b] /eqP rz2].
move: leqs => /and4P [ac cd db k0].
case: (lerP z1 c) => z1c.
  have aux:(a < z1 <= c) by rewrite z1a z1c.
  by move: (pa z1 aux); rewrite rz1 ltxx.
case: (lerP z2 c) => z2c.
  have aux:(a < z2 <= c) by rewrite z2a z2c.
  by move: (pa z2 aux); rewrite rz2 ltxx.
case: (lerP z1 d) => z1d; last first.
  have aux: (d < z1 < b) by rewrite z1d z1b.
  by move: (nb z1 aux); rewrite rz1 ltxx.
case: (lerP z2 d) => z2d; last first.
  have aux: (d < z2 < b) by rewrite z2d z2b.
  by move: (nb z2 aux); rewrite rz2 ltxx.
case /orP: (le_total z1 z2) => cp.
  apply/eqP; rewrite eq_le; apply/andP; split => //.
  move: (dab _ _  (ltW z1c) cp z2d).
  by rewrite rz1 rz2 addrN (pmulr_rle0 _ k0) subr_le0.
move: (dab _ _  (ltW z2c) cp z1d).
rewrite rz1 rz2 addrN (pmulr_rle0 _ k0) subr_le0.
move=> z1z2.
by apply/eqP; rewrite eq_le cp z1z2.
Qed.

Lemma one_root2_uniq p a: one_root2 p a ->
     uniqueness (fun z => a < z /\ root p z).
Proof.
move => [pp]; set c:=pp.1; set k := pp.2.
move => [/andP [ac kp] nii slk].
move => z1 z2 [az1 /eqP rz1][az2 /eqP rz2].
case: (lerP z1 c) => z1c.
  have aux: (a < z1 <= c) by rewrite az1 z1c.
  by move: (nii _ aux); rewrite rz1 ltxx.
case: (lerP z2 c) => z2c.
  have aux: (a < z2 <= c) by rewrite az2 z2c.
  by move: (nii _ aux); rewrite rz2 ltxx.
case /orP: (le_total z1 z2) => cp; apply/eqP; rewrite eq_le; apply/andP; split => //.
  have aux:(c <= z1  <= z2) by rewrite (ltW z1c) cp.
  move: (slk _ _ aux).
  by rewrite rz1 rz2 addrN (pmulr_rle0 _ kp) subr_le0.
have aux:(c <= z2  <= z1) by rewrite (ltW z2c) cp.
move: (slk _ _ aux).
by rewrite rz1 rz2 addrN (pmulr_rle0 _ kp) subr_le0.
Qed.

End DescOnOrderedRing.

Section DescOnOrderedField.

Variable R :realFieldType.
Implicit Type (p: {poly R}).

Lemma all_pos_inv p: all_ge0 p -> inv p.
Proof.
move=> posp eps peps.
move: (pol_cont ('X * p) 0 peps) => [e ep le].
have he := (half_gt0 ep).
have hew:= (ltW he).
exists (half e); split.
    by move=> y y0 ye; apply: all_pos_increasing.
  by move=> y y1 h h1; apply: all_pos_increasing => //; apply:(le_trans hew).
have -> :  half e* p.[half e] = ('X * p).[half e] - ('X * p).[0].
  by rewrite !hornerM !hornerX mul0r subr0.
have le1: `|half e - 0| < e by rewrite subr0 ger0_norm // half_ltx.
by move /ler_normlP:(ltW(le _ le1)) => [_ ->]; rewrite he.
Qed.

Lemma one_root2_shift p a b:
  one_root2 (p \shift a) b -> one_root2 p (a + b).
Proof.
move=>  [ck [/andP [x1a kp] neg sl]].
exists (a + ck.1,ck.2); split.
    by rewrite ltrD2l x1a kp.
  move=> x /= abxax1; rewrite -(addrNK a x) - horner_shift_poly.
  by rewrite neg // ltrBrDl lerBlDl.
move=> x y /= axy.
have aux:  y - x = y - a - (x - a).
  by rewrite opprD addrAC -!addrA opprK addrN addr0.
rewrite -{2} (addrNK a x)  -{2} (addrNK a y) -!(horner_shift_poly a _) aux.
by apply: sl; rewrite ?lerD2r // lerBrDr  addrC.
Qed.

Lemma one_root1_shift p a b c:
  one_root1 (shift_poly c p) a b ->
  one_root1 p (c + a) (c + b).
Proof.
move=>  [x1 [x2 [k [/and4P [ax1 x1x2 x2b kp] pos neg sl]]]].
exists (c + x1); exists (c + x2); exists k.
rewrite !ltrD2l; split => //; first by apply /and4P.
    move=> x cp; rewrite - (addrNK c x).
    rewrite -horner_shift_poly pos ? lerBDl  ? ltrBDl //.
  move=> x cp; rewrite - (addrNK c x).
  by rewrite -horner_shift_poly neg // ltrBrDl ltrBlDl.
move=> x y cx1x xy ycx2.
have aux:  y - x = y - c - (x - c).
  by rewrite [x + _]addrC opprD opprK addrA addrNK.
rewrite -{2} (addrNK c x)  -{2} (addrNK c y) aux -!(horner_shift_poly c _).
by rewrite sl ?lerD2r // ?lerBrDr? lerBlDr //  addrC.
Qed.

Lemma one_root1_scale p a b c:
  0 < c -> one_root1 (p \scale c) a b ->
    one_root1 p (c * a) (c * b).
Proof.
move=> cp [x1 [x2 [k [/and4P [ax1 x1x2 x2b kp] pos neg sl]]]].
exists (c * x1); exists (c * x2); exists (k / c).
have tc : 0 < c^-1 by rewrite invr_gt0.
rewrite !(ltr_pM2l cp).
have t: forall z, z = c * (z / c).
  by move=> z; rewrite [c * _]mulrC mulfVK //;move: cp;rewrite lt0r => /andP [].
split => //; first by apply/and4P; split => //; apply:mulr_gt0.
    move=> x cpp; rewrite (t x) - horner_scaleX_poly; apply: pos.
    by rewrite ltr_pdivlMr // mulrC ler_pdivrMr //(mulrC x1).
  move=> x cpp.
  rewrite (t x) -horner_scaleX_poly neg //.
  by rewrite ltr_pdivlMr // mulrC ltr_pdivrMr // (mulrC b).
move=> x y cx1x xy ycx2; rewrite -mulrA mulrDr mulrN ![c^-1 * _]mulrC
 {2}(t x) {2}(t y) -!(horner_scaleX_poly _ p); apply: sl.
    by rewrite ler_pdivlMr // mulrC.
  by rewrite ler_wpM2r // ltW.
by rewrite ler_pdivrMr // mulrC.
Qed.

End DescOnOrderedField.


(** ** Case of archifields *)

Section DescOnArchiField.

Variable R :archiFieldType.
Lemma desc_l4 (p: {poly R}) :  alternate_1 p -> inv2 p.
Proof.
move: p;elim/poly_ind => [| p a ih]; first by rewrite/alternate_1 polyseq0.
have desc_c: alternate_1 (a%:P) -> inv2 (a%:P).
  rewrite polyseqC;case: (a==0) => //=; case ha: (0< a) => // _.
  move=> eps eps0; exists (eps / a); split.
      by move => y _ _; rewrite !hornerC.
    by move => y1 y2 _ _ _ ; rewrite !hornerC.
  by rewrite hornerC ha divr_gt0 //= (divrK (unitf_gt0 ha)).
case sp : (nilp p).
  by move: sp; rewrite nil_poly; move /eqP => ->; rewrite mul0r add0r.
rewrite -{1} cons_poly_def polyseq_cons sp /=.
case: (ltrgtP 0 a) => ha.
(* case a > 0 *)
move => haposp eps eps0; rewrite /inv2 /=.
  have : all_ge0 (p * 'X + a%:P).
    by rewrite -cons_poly_def polyseq_cons sp /= ltW.
  move/all_pos_inv/(_ eps eps0)=> [x [h1x h2x /andP[h3x h4x]]]; exists x.
  have xp:= ltW h3x.
  split => //; rewrite h3x h4x !hornerE ltr_pwDr // mulr_ge0 //.
  by rewrite all_pos_positive.
(* case a < 0 *)
rewrite -oppr_gt0 in ha.
  set q := (p * 'X + a%:P).
  move=> il;move: (ih il _ ((half_gt0 ha)))=>  [x [H1 H2 /and3P [xp xpx xe]]].
  move: (le_lt_trans xe (half_ltx ha)) => xe'.
  have qxn : q.[x] < 0 by rewrite !hornerE mulrC -(opprK a) subr_lt0.
  move: (maxS x (-a/p.[x])) => /andP []; set y := (_ + _) => yx val.
  have yx':= ltW yx.
  have ppos: forall t, x <= t -> 0 < p.[t].
    move => t xt;exact (lt_le_trans xpx (H2 _ _ (lexx x) xt xt)).
  have qsincr: forall t d, x <= t -> 0 < d -> q.[t] < q.[t+d].
    move => t d xt dp; rewrite !hornerE.
    set w := _ + _.
    have aux: t <= t+d by rewrite - {1}(addr0 t) lerD2l ltW.
    have xtd:= (le_trans xt aux).
    rewrite  mulrDr -addrAC addrC ltr_pwDl ?(mulr_gt0 (ppos _ xtd) dp)//.
    rewrite !lerD2r (ler_pM2r (lt_le_trans xp xt)).
    by apply:H2 => //.
  have qincr: forall t, x<=t -> {in <=%R t &, pol_increasing q}.
    move => t xt u v ut vt; rewrite le_eqVlt; case /orP => uv.
       by move /eqP:uv => ->.
    rewrite ltW // - (addNKr  u v); apply: (qsincr _ _(le_trans xt ut)).
    by rewrite addrC subr_gt0.
  move: (H2 _ _ (lexx x) yx' yx') => lepxpy.
  have yge0: 0 <= y by rewrite ltW // (lt_le_trans xp yx').
  have posval : 0 <= q.[y].
    rewrite !hornerE -(addNr a) /= lerD2r /=.
    apply: (@le_trans _ _ (p.[x] * y)); last by rewrite ler_wpM2r.
    rewrite  // mulrC - ler_pdivrMr // ltW //.
  set r := ('X * q).
  have negval' : r.[x] < 0 by rewrite 2!hornerE pmulr_rlt0.
  have posval' : 0 <= r.[y] by rewrite 2! hornerE mulr_ge0.
  move=> epsilon Hepsilon /=.
  move: (half_gt0 Hepsilon) => he1.
  move: (constructive_ivt yx negval' posval' he1) => [ppr].
  rewrite (surjective_pairing ppr); set u:=ppr.1;set v := ppr.2.
  move /and5P => [/and3P [_ _ smallv] /and3P[xd dv v'y] _ posv _].
  have {xd dv} xv : x < v  by apply: le_lt_trans xd dv.
  have pv : 0 < v by apply: lt_trans xv.
  move: posv; rewrite  2! hornerE -{1} (mulr0 v) (ler_pM2l  pv) => posv.
  move: (pol_cont r v he1) => [d' dp' pd'].
  pose d := half d'.
  have dp : d > 0  by rewrite  half_gt0.
  have dd' : d < d' by apply: half_ltx.
  have vvd : v < v + d by rewrite ltrDl /=.
  have xvd : x < v + d by apply: lt_trans vvd.
  have lvd : 0 < p.[v + d] by apply: ppos; exact: ltW.
  move => {y yx val yx' posval posval' v'y lepxpy yge0}.
  have pa: le_below_x (v + d) (horner q).
    move => y y0 yvd; rewrite !hornerE lerD2r /=.
    case cmp: (y <= x); last first.
      have cmp': x <= y by rewrite ltW // ltNge cmp.
      apply: le_trans (_ : p.[v + d] * y <= _).
       by apply: ler_wpM2r => //; apply: H2 => //;apply: (le_trans cmp').
       by rewrite ler_wpM2l // ltW.
    apply: le_trans (_ : p.[x] * y <= _).
      by rewrite ler_wpM2r //; apply: H1.
    apply: le_trans (_ : p.[x] * (v + d) <= _); last first.
      rewrite ler_wpM2r //; first exact: le_trans yvd.
      rewrite H2 //; first (by apply: (lexx x)); by  apply:ltW.
    by rewrite ler_wpM2l // ltW.
  exists (v + d).
  rewrite (le_lt_trans posv (qsincr _ _ (ltW xv) dp)) (lt_trans pv vvd).
  split => //=; first by apply: qincr; apply: ltW.
  rewrite - (double_half epsilon).
  apply: le_trans (_ : ((half epsilon) + r.[v+d] -r.[v]) <= _).
    rewrite  [ half epsilon + _] addrC -addrA.
    rewrite [r.[v + d]] hornerE hornerX lerDl subr_ge0 //.
  rewrite -!addrA lerD2l.
  have aux:`|(v+d) - v| < d' by rewrite (addrC v) addrK ger0_norm// ltW.
  by move: (ltW (pd' _ aux)) => /ler_normlP [_].
(* case a = 0 *)
move => halt1 eps eps0.
move: (ih halt1 _ ltr01) =>  [x [plx pmonx /and3P [gx0 gpx0 lpx1]]].
have e1px : 0 < eps / x by apply: mulr_gt0=> //=; rewrite invr_gt0.
move: (ih halt1 _ e1px) => [v [plv pmonv /and3P [gv0 gpv0 lpve]]].
rewrite -ha addr0.
have aux: forall w, 0 <=w -> 0 <= p.[w] -> {in <=%R w &, pol_increasing p} ->
   {in <=%R w &, pol_increasing ((p * 'X))}.
  move => w wz pwz H s t sw tw st; rewrite !hornerE.
  move: (H _ _ sw tw st) (le_trans pwz (H _ _ (lexx w) sw sw)) => pa pb.
    by apply:(ler_pM pb (le_trans wz sw) pa st).
set w:= (Num.min x v); exists w.
have wc: w = x \/ w = v.
  by rewrite /w /minr; case: ifPn; [left|right].
have wz: 0 < w by case wc => ->.
have pw0: 0 < p.[w] by case wc => ->.
rewrite wz 3! hornerE (pmulr_lgt0 _ wz) pw0.
split.
    move => t tp tw; rewrite !hornerE mulrC (mulrC _ w).
    apply: (pmul2w1 tp (ltW pw0) tw).
    move: tp tw;case wc=> ->; [apply: plx | apply: plv].
  by apply: aux; [apply: ltW | by apply: ltW| case wc => ->].
move: lpve; rewrite  (ler_pdivlMr _ _ gx0) => lpve.
case /orP:(le_total x v)=> xv;
  rewrite /w/=.
  move/min_idPr : (xv); rewrite minC => ->.
   apply: le_trans lpve; rewrite mulrA.
   rewrite (ler_pM2r gx0);apply: (ler_pM (ltW gx0) (ltW gpx0) xv).
  exact:(pmonx _ _ (lexx x) xv xv).
move/min_idPr : (xv) => ->.
apply: le_trans lpve.
rewrite mulrA.
by rewrite (ler_pM2l (mulr_gt0 gv0 gpv0) v x).
Qed.

Lemma desc  (p: {poly R}): alternate p -> one_root2 p 0.
Proof.
move: p; elim/poly_ind => [| p a IHl]; first by rewrite polyseq0.
rewrite -cons_poly_def polyseq_cons.
case sl: (nilp p) => /=.
  by rewrite polyseqC; case: (a == 0) => //=;rewrite ! if_same.
case: (ltrP a 0) => ha alt1.
   rewrite - oppr_gt0 in ha.
  move: (desc_l4 alt1 (half_gt0 ha)) => [x [psub pmon /and3P [xp pxp pxa1]]].
  move: (le_lt_trans pxa1 (half_ltx ha)) => pxa2.
  exists (x, p.[x]); simpl; rewrite xp pxp; split => //.
    move => y /andP [posy yx].
    move: (ltW posy) => posy'.
    rewrite horner_cons -(opprK a) subr_lt0; apply: le_lt_trans pxa2.
    rewrite mulrC; apply:(pmul2w1 posy' (ltW pxp) yx (psub _ posy' yx)).
  move => y z xyz;rewrite !horner_cons opprD addrCA addrK.
  rewrite [_ + _ * _]addrC [_ * z]mulrC [_ * y]mulrC.
  have slp:slope_bounded x 0 (horner p).
    move => t u /andP[xt tu];rewrite mul0r subr_gte0 pmon //.
    exact (le_trans xt tu).
  move:(slope_product_x (ltW xp) (lexx 0) slp xyz).
  move/andP :xyz => [xy yz].
  rewrite mulr0 add0r; apply: le_trans.
  by apply: (ler_wpM2r _ (pmon _ _ (lexx x) xy xy)); rewrite subr_ge0.
move: alt1; case a0 : (a == 0) => // alt1; move: (eqP a0) => a00.
clear ha a0.
move: (IHl alt1) => [v1k []] {IHl}.
set v1 := v1k.1; set k:= v1k.2; simpl => /andP[v1pos kpos] low incr.
have negval : (p.[v1] < 0) by apply: low; rewrite ?lexx v1pos.
set k':= half (k * v1).
have posk' : 0 < k' by apply: half_gt0; apply: mulr_gt0.
set u := (- p.[v1]) / k.
move: (maxS 0 u); set v:=  Num.max 0 _ => /andP [pa pb].
set v2:= v1 + v +1.
have v0: 0 <= v by rewrite le_max lexx.
have v1v2: v1 < v2 by rewrite /v2 - addrA (ltrDl v1).
have pos1:0 <= p.[v1 + v].
  move: (kpos); rewrite lt0r => /andP [ kne0 _].
  move: kpos; rewrite - invr_gt0 => kpos.
  rewrite /v; have [caf|caf] := leP u 0.
    by rewrite  addr0 - oppr_le0 - (pmulr_lle0 _ kpos).
  case/orP:(le_total u 0); [ | move => up].
    by rewrite leNgt caf.
  have aa: v1 <= v1 <= v1 + u  by rewrite lexx  lerDl.
  rewrite -(lerDr (- p.[v1]));apply: le_trans (incr _ _ aa).
  by rewrite  (addrC v1) addrK /u (mulrC _ (k^-1)) mulVKf //.
have pos : 0 < p.[v2].
  have hh: v1 <= v1 + v <= v1 + v + 1 by rewrite !lerDl v0 ler01.
  apply: (le_lt_trans pos1);rewrite -subr_gt0.
  by apply: (lt_le_trans _ (incr _ _ hh)); rewrite addrAC addrN add0r mulr1.
clear v0 pos1 pa pb.
move: (constructive_ivt v1v2 negval (ltW pos) posk') => [x12].
rewrite (surjective_pairing x12); set x1:=x12.1;set x2 := x12.2.
move /and5P => [/and3P [x1close _ _] /and3P[v1x1 _ _]  px1neg _  _].
have x1pos : 0 < x1 by apply: lt_le_trans v1x1.
have Plow : forall x, 0 < x -> x <= x1 -> x * p.[x] < 0.
  move=> x xpos xx1; rewrite (pmulr_rlt0 _ xpos).
  case: (ltrP x v1)=> xv1; first by apply: low=> //; rewrite xpos ltW.
  apply: le_lt_trans px1neg.
  move: xx1; rewrite le_eqVlt; move/orP => [xx1 | xlx1];
    first by rewrite (eqP xx1) lexx.
  have aux : v1 <= x <= x1 by rewrite  xv1 ltW.
  rewrite -subr_gte0; move: (incr _ _ aux); apply: le_trans.
  by apply: ltW; apply: mulr_gt0 => //; rewrite subr_gt0.
exists (x1,k'); simpl; rewrite x1pos posk'; split => //.
  by move=> x /andP[x0 xx1]; rewrite horner_cons a00 addr0 mulrC;apply : Plow.
move => x y /andP[x1x xy].
rewrite ! horner_cons a00 !addr0 (mulrC _ x)  (mulrC _ y).
have: (v1 * k + p.[x]) * (y - x) <= y * p.[y] - x * p.[x].
  apply:(slope_product_x (ltW v1pos) (ltW kpos) incr).
  by rewrite xy (le_trans v1x1 x1x).
apply: le_trans; rewrite ler_wpM2r //; first by rewrite subr_ge0.
rewrite mulrC - (double_half (k * v1 )) -/k' - addrA lerDl.
rewrite - (opprK k') addrC subr_gte0 (le_trans x1close) // -subr_gte0.
have: k * (x - x1) <= p.[x] - p.[x1]  by apply: incr =>//; rewrite x1x v1x1.
by apply : le_trans; apply: mulr_ge0 => //; rewrite ?(ltW kpos) ?subr_ge0.
Qed.

Lemma one_root_reciprocal (p: {poly R}) deg :
  (0 < size p)%N ->
  (size p <= deg.+1)%N ->
  one_root2 (recip deg p) 1 -> one_root1 p 0 1.
Proof.
move=> s0 sz [x1k [/andP []]].
set x1 := x1k.1; set k := x1k.2; set q := (recip deg p).
move => x1gt1 kp neg sl.
have x10 : 0 < x1 by apply: lt_trans x1gt1; exact: ltr01.
set y' := x1 - q.[x1] / k.
have nx1 : q.[x1] < 0 by rewrite neg //x1gt1 lexx.
have knz: k != 0 by move: kp; rewrite lt0r; case /andP =>[].
have y'1: x1 < y' by rewrite /y' ltrDl oppr_gt0 pmulr_llt0 // ?invr_gt0.
have y'pos : 0 <= q.[y'].
  have aux: x1 <= x1 <= y' by rewrite (lexx x1) (ltW y'1).
  rewrite -(lerD2r (- q.[x1])) add0r; apply: le_trans (sl _ _ aux).
  by rewrite /y' (addrC x1) addrK mulrN mulrC mulfVK.
move: (@diff_xn_ub R deg 1); set u := _ *+ _; move => up.
set u':= Num.max 1 u.
have uu': u <= u' by rewrite le_max lexx orbT.
have u1: 1 <= u' by rewrite le_max lexx.
have u'0 : 0 < u' by rewrite (lt_le_trans ltr01).
have divu_ltr : forall x, 0 <= x -> x / u' <= x.
   move => x x0; rewrite ler_pdivrMr // ler_peMr //.
have y'0: 0 < y' by apply: lt_trans y'1.
pose y := y' + 1.
have y'y : y' < y by rewrite /y ltrDl.
have y1 : x1 < y by apply: lt_trans y'1 _.
have ypos : 0 <  q.[y].
  have aux: x1 <= y' <= y by rewrite (ltW y'1) (ltW y'y).
  rewrite (le_lt_trans y'pos) // -subr_gte0.
  by apply: lt_le_trans (sl _ _ aux); rewrite mulr_gt0 // subr_gt0.
have y0: 0 < y by apply: lt_trans y'y.
pose k' := half ((k * x1 ^+ 2 * y ^- 1 ^+ deg)).
have k'p : 0 < k'.
  apply: half_gt0; rewrite mulr_gt0 //; first by rewrite mulr_gt0  // exprn_gt0.
  rewrite exprn_gt0 // invr_gt0 //.
pose e := k' / u'.
have ep: 0 < e by rewrite /e; apply: mulr_gt0 => //; rewrite invr_gt0.
pose e1 := half e.
have e1p : e1 > 0 by apply: half_gt0.
have e1e : e1 < e by apply: half_ltx.
move: (constructive_ivt  y'1 nx1 y'pos e1p)=> [pv].
rewrite (surjective_pairing pv); set a:=pv.1;set b' := pv.2.
move=> /and5P[/and3P [cla _ clb'] /and3P[x1a ab b'y'] nega posb' _].
move: (pol_lip q (z:=y)); set c := (norm_pol q^`()).[y] => cp.
have cp0 : 0 < c.
  move: (lt_le_trans nega posb'); rewrite - subr_gt0 => dp.
  move: (ltW (le_lt_trans b'y' y'y)) => pb.
  move: y0; rewrite -(oppr_lt0 y) => yn0.
  move: (ltW (lt_trans yn0 (lt_le_trans x10 x1a))) => pa.
  move: (cp _ _ pa (ltW ab) pb); rewrite (gtr0_norm dp) => dp'.
  by move: (lt_le_trans  dp dp'); rewrite pmulr_lgt0 // subr_gt0.
set b := Num.min y (b' +(half e1)/c).
have blty: b <= y by  rewrite /b ge_min lexx.
have b'b: b' < b.
  rewrite lt_min (le_lt_trans b'y' y'y) /= - ltrBlDl addrN.
  by rewrite (divr_gt0 (half_gt0 e1p) cp0).
have clb:c * (b - b') < e1.
  apply: le_lt_trans (half_ltx e1p).
  by rewrite -(ler_pdivlMl _ _ cp0) mulrC lerBlDl ge_min lexx orbT.
pose n := (size p).-1.
have a0 : 0 < a by apply: lt_le_trans x1a.
have b'0 : 0 < b' by apply: lt_trans ab.
have b0 : 0 < b by apply: lt_trans b'b.
have ibp: 0 < b^-1 by rewrite invr_gt0.
have inv_mono: forall x, 0 < x -> Num.sg (q.[x]) = Num.sg (p.[x^-1]).
  move => x xp.
  rewrite /q /recip.
  rewrite hornerM (horner_reciprocal _ ( unitf_gt0 xp)) hornerXn.
  rewrite !sgrM gtr0_sg ?mul1r //.
    by rewrite gtr0_sg // ?mul1r // exprn_gt0.
  by rewrite exprn_gt0.
rewrite /one_root1 /pos_in_interval /neg_in_interval1.
have res1:pos_in_interval 0 b^-1 (horner p).
  move => x /andP[x0 xb].
  rewrite -[x]invrK -sgr_cp0 - inv_mono  ?invr_gt0 // sgr_cp0.
  rewrite (le_lt_trans posb') //  -subr_gte0 /=.
  have b'x : b' < x^-1.
    by rewrite inv_comp// (le_lt_trans xb)// ltf_pV2.
  have aa:x1 <= b' <= x^-1 by rewrite (ltW (le_lt_trans x1a ab)) (ltW b'x).
  by apply:lt_le_trans (sl _ _ aa); rewrite  mulr_gt0 // subr_gt0.
have res2: neg_in_interval1 a^-1 1 (horner p).
  move => x /andP[a1x xlt1].
  have x0 : 0 < x by apply: lt_trans a1x; rewrite invr_gt0.
  have xv0 : 0 < x^-1 by rewrite invr_gt0.
  rewrite -[x]invrK -sgr_cp0 - inv_mono  ?invr_gt0 // sgr_cp0.
  have x1a0 : x^-1 < a by rewrite inv_compr.
  case : (lerP x1 x^-1) => cmp; last first.
     apply: neg => //;rewrite (inv_comp ltr01 x0) invr1.
     by rewrite xlt1 (ltW cmp).
  have aux: (x1 <= x^-1 <= a) by rewrite cmp (ltW x1a0).
  apply: lt_trans nega; rewrite -subr_gte0.
  apply: lt_le_trans (sl _ _ aux).
  by rewrite mulr_gt0 // subr_gt0.
exists b^-1, a^-1, k'.
split => //.
  rewrite k'p ibp ltf_pV2// (inv_compr ltr01 a0) invr1.
  by rewrite (lt_trans ab b'b) (lt_le_trans x1gt1 x1a).
move => x z bvx xz zav.
  rewrite le_eqVlt in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 lexx.
have x0: 0 < x by apply: (lt_le_trans ibp bvx).
have z0 : 0 < z by apply: (lt_trans x0).
have lmrec : forall yy, 0 < yy -> p.[yy] = yy ^+ deg * q.[yy^-1].
  move => yy yy0.
  rewrite hornerM horner_reciprocal1 ?unitf_gt0 // hornerXn exprVn mulrA.
  case h : (size p == 1)%N.
    rewrite (eqP h) !subSS !subn0 mulfV // expf_neq0 //.
    by move: yy0; rewrite lt0r; case/andP.
  have h' : size p = (size p).-2.+2.
    case h'': (size p) => [ | [ | sp]] //.
      by move: s0; rewrite h'' ltn0.
    by move: h; rewrite h'' eqxx.
  rewrite -expfB; last first.
    rewrite h' subSS prednK; last by rewrite h'.
    rewrite -{2}[deg]subn0 ltn_sub2l //.
      by rewrite -ltnS (leq_trans _ sz) // h'.
    by rewrite h'.
  by rewrite h' !subSS subKn ?subn0 // -ltnS -h'.
rewrite (lmrec x x0) (lmrec z z0).
set s :=  deg.
set t1 := (x ^+ s - z ^+ s) * q.[x^-1].
set t3 := q.[x^-1] - q.[z^-1].
rewrite (_ : _ * _ - _ = t1 + t3 *  z ^+ s); last first.
  by rewrite /t1 !mulrDl !mulNr ![_.[_] *_]mulrC !addrA addrNK.
set t2 := t3 * _.
pose k1 := -k'; pose k2 := k' + k'.
have k2p : k2 = (k * x1 ^+ 2 * y ^-1 ^+ s) by apply: double_half.
rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
have xzi: z^-1 < x^-1 by rewrite ltf_pV2.
have pa : x1 <=  z^-1.
  by rewrite (le_trans x1a)// -(invrK a)// lef_pV2// posrE invr_gt0.
have pb: x1 <=  x^-1 by rewrite (ltW (le_lt_trans pa xzi)).
have pc: 0 <= k * (x^-1 - z^-1) by apply: ltW;rewrite(mulr_gt0 kp) // subr_gt0.
have pdd:(x1 <= z^-1 <= x^-1) by rewrite pa (ltW xzi).
have pd:= (sl _ _ pdd).
have t3p:=  le_trans pc pd.
have pe : 0 <= y^-1 <= z.
  by rewrite invr_ge0 ltW //= (le_trans _ (ltW xz))// (le_trans _ bvx)// lef_pV2.
case /andP: (pow_monotone s pe) => _ hh.
have maj' : t3 * y^-1 ^+ s <= t3 * z^+ s by rewrite ler_wpM2l.
rewrite mulrDl; apply: lerD; last first.
  apply: le_trans maj'; rewrite /t3 k2p mulrAC.
  rewrite ler_pM2r; last by apply: exprn_gt0; rewrite invr_gt0.
  apply: le_trans pd.
  rewrite ![k * _]mulrC mulrAC ler_pM2r //.
  have xn0 : (x != 0) by move: x0; rewrite lt0r; case /andP =>[].
  have zn0 : (z != 0) by move: z0; rewrite lt0r; case /andP =>[].
  have xVn0 : (x^-1 != 0) by move: x0; rewrite -invr_gt0 lt0r; case /andP =>[].
  rewrite -[x^-1](mulfK zn0)  -(mulrC z) - (mulrA z _ _).
  rewrite -{2}[z^-1](mulfK xn0) -(mulrA _  x _)(mulrCA _ x).
  rewrite (mulrC z^-1)  -mulrBl (mulrC (z - x)).
  rewrite ler_pM2r /=; last by rewrite subr_gte0.
  apply: le_trans (_ : x1 / z <= _); first rewrite ler_pM2l //=.
  by rewrite ler_pM2r ?invr_gt0.
move:(ltW xz) => xz'.
have xzexp : (x ^+ s - z ^+ s) <= 0.
   have aux: 0 <=x <= z by rewrite xz' ltW//.
   by case /andP :(pow_monotone s aux)=> [_]; rewrite subr_le0.
have xzexp' : (z ^+ s - x ^+ s) >= 0 by rewrite subr_ge0 - subr_le0.
rewrite /t1 /k1 /k' {maj' t2 t3}.
case: (lerP 0 ( q.[x^-1])) => sign; last first.
  apply: le_trans  (_ : 0 <= _).
   by rewrite mulNr lterNl oppr0 mulr_ge0 //?(ltW k'p)// subr_gte0 /= ltW.
  by rewrite mulr_le0 // ltW.
rewrite mulNr lterNl -mulNr opprD opprK addrC.
have rpxe : q.[x^-1] <= e.
  have bvx' : x^-1 <= b by rewrite -(invrK b)// lef_pV2.
  apply: (@le_trans _ _ q.[b]).
     have aux:(x1 <= x^-1 <= b) by rewrite pb bvx'.
    rewrite -subr_ge0 /= ;apply: le_trans (sl _ _ aux).
    rewrite mulr_ge0  ?subr_gte0 // ltW //.
  rewrite -[_ _ b]addr0 -(addrN (q).[b']) addrA.
  rewrite (addrC ( _ b)) -addrA -(double_half e) (lerD clb')//.
  have yb: - y <= b' by apply: ltW; apply: lt_trans b'0; rewrite oppr_lt0.
  move: (le_trans (cp b' b yb (ltW b'b) blty) (ltW clb)).
  by move /ler_normlP => [_].
apply: le_trans (_ : (z^+ s - x ^+ s) * e <= _).
  by rewrite ler_wpM2l // ?subr_gte0.
have un0 : (u' != 0) by  move: u'0; rewrite lt0r; case /andP =>[].
rewrite [_ * e]mulrC; apply: le_trans (_ : e * (u' * (z - x)) <= _)=> /=.
  apply: ler_wpM2l; first exact: ltW.
  apply: (@le_trans _ _ (u * (z - x))).
    have xm1: -1 <= x by exact: (ltW (lt_trans (ltrN10 R) x0)).
    have a1 : 1 <= a by apply: (ltW (lt_le_trans x1gt1 x1a)).
    rewrite - (ger0_norm xzexp'); apply: (up _ _ xm1 xz').
    apply: le_trans zav _.
    by rewrite invr_le1 // unitf_gt0.
  by rewrite ler_pM2r // subr_gte0.
rewrite mulrA ler_pM2r; last by rewrite subr_gte0.
rewrite /= /e  divfK ?lterr //.
Qed.

Lemma alternate_MX (p : {poly R}) k:
  alternate ('X ^+ k * p) -> alternate p.
Proof.
elim: k => [ | k IH]; first by rewrite expr0 mul1r.
case h : (p == 0); first by rewrite (eqP h) mulr0.
rewrite mulrC polyseqMXn //=; last by rewrite h.
by rewrite ltxx eqxx -polyseqMXn ?h // mulrC.
Qed.

Lemma Bernstein_isolate deg a b (l : {poly R}): a < b -> (0 < size l)%N ->
   (size l <= deg.+1)%N -> alternate (Mobius deg a b l) -> one_root1 l a b.
Proof.
rewrite /Mobius /recip =>  altb s0 sz.
have sss : size ((l \shift a) \scale (b - a)) = size l.
  rewrite size_scaleX; last by move: altb; rewrite -subr_gt0 lt0r; case/andP.
  by rewrite size_comp_poly2 // size_XaddC.
rewrite sss => alt.
have -> : a = a + (a - a) by rewrite addrN addr0.
have -> : b = a + (b - a) by rewrite (addrC b) addNKr.
apply: one_root1_shift.
rewrite addrN -(mulr1 (b - a)) -(mulr0 (b - a)).
apply: one_root1_scale; first by rewrite subr_gt0.
move/desc: alt => alt'; move/one_root2_shift: alt'; rewrite addr0 -sss.
by apply: one_root_reciprocal; rewrite sss.
Qed.

End DescOnArchiField.
