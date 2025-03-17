From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq  choice fintype order.
From mathcomp Require Import binomial  bigop ssralg poly ssrnum ssrint rat.

From mathcomp Require Import polydiv polyorder path interval polyrcf.

(** Descates method 2 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Order.Theory GRing.Theory.
Import Num.Theory Num.Def.
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

(* TODO(rei): same as in desc1.v?! *)
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

Lemma schange_deriv p (s := (schange p)) (s':=  schange p^`()):
   (s = s' \/ s = s'.+1).
Proof.
rewrite /s/s'.
have [-> | pnz] := (eqVneq p 0); first by rewrite deriv0; left.
move: pnz; rewrite - size_poly_gt0 => pz.
have eq: polyseq p = p`_0 :: behead p by move: pz; case p => q /=; case q => //.
have aux: forall i,  p^`()`_i = (nth 0 (behead p)) i  *+ i.+1.
  by move => i; rewrite coef_deriv nth_behead.
rewrite schange_sgr (schange_sgr p^`()).
have <-: [seq Num.sg z | z <- (behead p)] =  [seq Num.sg z | z <- p^`()].
  have aux1: size (behead p) = size p^`() by rewrite size_deriv {2} eq.
  apply: (eq_from_nth (x0 :=0)); first by rewrite !size_map.
  move => i; rewrite size_map => iz;rewrite (nth_map 0)// (nth_map 0) -?aux1//.
  by rewrite coef_deriv nth_behead sgrMn mul1r.
rewrite eq /= /schange/filter0/filter;case h: (Num.sg p`_0 != 0); last by left.
simpl; case h': (_ < 0); [ by rewrite addSn; right | by left].
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

Lemma schange_odd p: p != 0 -> odd (schange p + (0 < lead_tail_coef p)%R).
Proof.
rewrite - lead_coef_eq0 /lead_tail_coef tail_coefE /schange lead_coefE nth_last.
by move => h; rewrite schange0_odd.
Qed.
End SignChange.


Section SignChangeRcf.
Variable R :rcfType.
Implicit Type (p:{poly R}).

(* TODO(rei): same as desc1.v?! *)
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
  by rewrite /sb - map_comp; symmetry; apply: map_id_in => a.
have pa: (all (fun z => 0 < z) [seq z.1 | z <- sb]).
  by rewrite - sav; apply /allP => x; rewrite mem_filter => /andP [].
have pb : (sorted <%R [seq z.1 | z <- sb]).
  rewrite - sav.
  by apply: sorted_filter => //; [apply: lt_trans |apply: sorted_roots].
have pc: (all (fun z => (0<z)%N ) [seq z.2 | z <- sb]).
  apply /allP => x /mapP [t] /mapP [z]; rewrite mem_filter => /andP [z0 z2].
  move => -> -> /=; rewrite mu_gt0 //; apply: (root_roots z2).
suff: { q | p = (\prod_(z <- sa) ('X - z%:P) ^+ (\mu_z p))  * q &
  forall x : R, 0 < x -> ~~ root q x}.
  move => [q qa qb]; exists (sb,q) => //.
    split => //;rewrite qa /= big_map; congr (_ * _); apply eq_big.
  by split => // pz; move: pnz; rewrite pz eqxx.
clear sb sav pa pb pc.
have: all (root p) sa.
    apply/allP=> x;rewrite mem_filter =>/andP [_]; apply /root_roots.
have: uniq sa by apply:filter_uniq; apply: uniq_roots.
have: forall x, root p x -> 0 < x -> (x \in sa).
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
rewrite [RHS](big_nth 0).
rewrite 2! big_mkord; apply: eq_bigr => i _.
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
Definition npos_roots p :=  (\sum_(i <- (pos_roots p)) (i.2))%N.

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

Lemma pos_split_deg p: p != 0 ->
   size p = ((npos_roots p) + (size (pos_cofactor p))) %N.
Proof.
move /pos_split1 => [[pa _ _ ] _ _  pb].
by rewrite {1} pa size_monicM // ? monic_prod_XsubCe // size_prod_XsubCe addSn.
Qed.


Lemma npos_roots0 p: (p != 0 /\ p^`() != 0)  \/  (npos_roots p = 0)%N.
Proof.
case (eqVneq p 0) => pnz.
  right; rewrite /npos_roots /pos_roots.
  move: (poly_split_fact p) => H; move: (s2valP' H) (s2valP H) => [_ h1] _.
  by rewrite (proj1 (h1 pnz)) // big_nil.
move: (pos_split1 pnz) => [[pa pb pc pd] pe pf].
case (leqP (size p) 1%N) => sp; [right | left].
  move: pf  sp; rewrite (pos_split_deg pnz) - size_poly_gt0.
  case: (size (pos_cofactor p)) => //.
  by move =>  m _; rewrite addnS ltnS leqn0 addn_eq0 => /andP [/eqP -> _].
split => //.
by rewrite -size_poly_eq0 (size_deriv p); move: sp;case: (size p)=> //; case.
Qed.

Lemma coprimep_prod p I l (F: I-> {poly R}):
   (all (fun z => coprimep p (F z)) l) -> coprimep p (\prod_(z <- l) (F z)).
Proof.
elim l; first by rewrite big_nil /= coprimep1.
by move => b m Hrec /andP [ap /Hrec]; rewrite big_cons coprimepMr ap => ->.
Qed.

Lemma Gauss_dvdp_prod p (I:eqType) (l: seq I) (F: I-> {poly R}):
   (all (fun i => (F i)  %| p) l) ->
   (uniq [seq F i | i <- l]) ->
   (forall i j, i \in l -> j \in l -> (i == j) || coprimep (F i) (F j)) ->
   \prod_(i <- l) (F i) %| p.
Proof.
move: p; elim: l.
   by move => p _ _ _; rewrite big_nil dvd1p.
move => a l Hrec p /= /andP [ap dr] /andP [al ul] etc.
have aa: coprimep (F a) (\prod_(j <- l) F j).
   apply: coprimep_prod; apply /allP => x xl.
   have xal: x \in a :: l by rewrite inE xl orbT.
   have aa: F x \in [seq F i | i <- l] by apply/mapP; exists x.
   by move: al;case/orP: (etc _ _  (mem_head a l) xal)=> // /eqP ->; rewrite aa.
rewrite big_cons Gauss_dvdp // ap /= Hrec // => i j il jl.
by apply: etc; rewrite inE ? il ? jl orbT.
Qed.

Lemma Gauss_dvdp_prod2 p (l: seq (R * nat)):
   (all (fun z => ('X - z.1%:P)^+ (z.2)  %| p) l) ->
   (uniq [seq z.1 | z <- l]) ->
   \prod_(i <- l) ('X - i.1%:P)^+ (i.2) %| p.
Proof.
move => pa pb.
set l2:= [seq z <- l | z.2 != 0%N].
have qc: all (fun z => z.2 !=0%N) l2 by apply: filter_all.
have qa:all (fun z => ('X - (z.1)%:P) ^+ z.2 %| p) l2.
 by apply /allP => x; rewrite mem_filter => /andP [_] /(allP pa).
have qb:  uniq [seq z.1 | z <- l2].
   move: pb;rewrite /l2; elim l => [|x s IHs] //= /andP [Hx Hs].
   case (x.2 == 0%N); rewrite /= IHs // andbT; apply /negP.
   move /mapP => [y]; rewrite mem_filter => /andP [_ ys] xy.
   move: Hx; rewrite xy; move/negP;case; apply /mapP; exists y => //.
have ->: \prod_(i <- l) ('X - (i.1)%:P) ^+ i.2 =
   \prod_(i <- l2) ('X - (i.1)%:P) ^+ i.2.
  rewrite big_filter [X in _ = X] big_mkcond /=; apply: eq_bigr => i _.
  by case h: (i.2 == 0%N) => //=; rewrite (eqP h) expr0.
apply:Gauss_dvdp_prod => //.
   rewrite map_inj_in_uniq. apply: (map_uniq qb).
   move => i j il jl /= eq1.
   rewrite (surjective_pairing i) (surjective_pairing j).
   move: (size_exp_XsubC i.2  (i.1)); rewrite eq1 size_exp_XsubC.
   move /eq_add_S => ->.
   have: root  (('X - (i.1)%:P) ^+ i.2) (i.1).
     move: (allP qc _ il); rewrite -lt0n => /prednK <-.
     by rewrite root_exp_XsubC eqxx.
   rewrite eq1; move: (allP qc _ jl); rewrite -lt0n => /prednK <-.
   by rewrite root_exp_XsubC => /eqP ->.
move => i j il2 jl2.
pose zz:(R * nat) :=  (0, 0%N).
move: (nth_index zz il2)(nth_index zz jl2).
move: il2 jl2; rewrite -(index_mem) -(index_mem).
set i1 := index i l2; set j1 := index j l2 => ra rb rc rd.
set l3 :=  [seq z.1 | z <- l2].
have ss: size l2 = size l3 by rewrite /l3 size_map.
move: (ra) (rb);rewrite ss => ra' rb'.
move: (nth_uniq 0 ra' rb' qb) => aux.
case eqq: (i1 == j1). by rewrite - rc - rd (eqP eqq) eqxx.
apply /orP; right.
rewrite coprimep_expl // coprimep_expr //  coprimep_XsubC root_XsubC.
by rewrite - rc - rd -(nth_map zz 0) // -(nth_map zz 0) // -/l3 eq_sym aux eqq.
Qed.

Lemma sorted_prop (s: seq R)  i j: sorted <%R s ->
   (i < size s)%N -> (j < size s)%N -> (i < j)%N -> s`_i < s`_j.
Proof.
move: i j; elim: s => // a l Hrec i j /= pal; case: i; last first.
  move => i il; case: j => // j jl /=; rewrite ltnS; apply: Hrec => //.
  apply: (path_sorted pal).
clear Hrec; case: j => // j _ jl _;move: a j jl pal.
elim:l => // a l Hrec b j /=;case: j => [_ | j jl]; move /andP => [pa pb] //=.
by apply:(lt_trans pa); apply /Hrec.
Qed.

Lemma pos_root_deriv p: ((npos_roots p) <= (npos_roots p^`()).+1) %N.
Proof.
case (npos_roots0 p); last by move => ->.
move => [pnz dnz].
move: (pos_split1 pnz) => [[pa pb pc pd] pe pf].
set s := pos_roots p; set q := pos_cofactor p.
move: (erefl (pos_roots p)); rewrite -{2} /s; case s.
    by rewrite /npos_roots;move => ->; rewrite big_nil.
move=> a l eq1.
set r:= [seq z.1 | z <- s]; set r1:= a.1; set rs:= [seq z.1 | z <- l].
set rd:= [seq z.2 | z <- pos_roots p].
have ss: size s = (size l).+1 by  rewrite /s eq1.
pose zz:(R * nat) :=  (0, 0%N).
have p0: forall i, (i < size s)%N -> (nth zz s i).2 \in rd.
  move => i qis; apply /mapP; exists (nth zz s i)=> //.
  by apply /(nthP zz); exists i.
have p1: forall i: 'I_(size l)%N,
    {c : R | c \in `] ((r1::rs)`_i), (rs`_i)[ & (p^`()).[c] = 0}.
  move: pc;rewrite eq1 /=; move /(pathP 0); rewrite size_map => h.
  move => [i isl]; move: (h _ isl); rewrite -/r1 -/rs => lt1.
  have ha: forall j, (j< size s)%N -> (root p (r1 :: rs)`_j).
    move => j js; rewrite pa rootM /root horner_prod; apply /orP; left.
    rewrite (big_nth zz) big_mkord -/s (bigD1 (Ordinal js)) //= {1} /s eq1 /=.
    rewrite horner_exp hornerXsubC -(nth_map _ 0) /= -?ss // subrr expr0n.
    by rewrite (gtn_eqF (allP pd _ (p0 _ js))) mul0r eqxx.
  have rp: p.[(a.1 :: rs)`_i] = p.[rs`_i].
    have ->: rs`_i = (r1 :: rs)`_(i.+1) by [].
    by rewrite (eqP (ha _ _ )) ?  (eqP (ha _ _ )) //; rewrite ss ltnS // ltnW.
  exact: (rolle lt1 rp).
set l2 := [seq (s2val (p1 i), 1%N) | i <- (enum 'I_(size l)) ].
set l3 := [seq (z.1, z.2.-1) | z <-  pos_roots p].
set f2 := \prod_(z <- l2) ('X - (z.1)%:P) ^+ (z.2).
set f3 := \prod_(z <- l3) ('X - (z.1)%:P) ^+ (z.2).
have p2: forall t, (t < size s)%N -> (r1 :: rs)`_t = (nth zz s t).1.
  by move => t ts; rewrite - (nth_map zz 0) //  /s eq1.
have ->: (npos_roots p = (\sum_(i <- l2++l3)i.2).+1)%N.
  rewrite big_cat - addSn /l3 /l2 ! big_map sum1_card cardE size_enum_ord - ss.
  rewrite - (sum1_size s) -/s - big_split /=.
  rewrite /npos_roots ! (big_nth zz) ! big_mkord; apply: eq_bigr.
  by move => [i iv] _; rewrite  add1n (prednK (allP pd _ (p0 _ iv))).
have p4: (all (fun z => 0 < z) [seq z0.1 | z0 <- l2 ++ l3]).
  have aa: forall t, t \in s -> 0 < t.1.
    by move => t ts; apply: (allP pb); apply /mapP; exists t.
  apply /allP => x /mapP [y]; rewrite mem_cat => /orP []; last first.
    by move/mapP => [t /aa h -> ->].
  move/mapP => [t] _ -> -> /=; move: (s2valP (p1 t)).
  rewrite itv_boundlr => /= /andP [lt1 _]; apply: lt_trans lt1.
  have ts: (t < size s)%N by rewrite /s eq1 /= ltnS ltnW.
  by rewrite (p2 _ ts); apply: aa;rewrite mem_nth.
have pcc: forall i j, (i <size s)%N -> (j <size s)%N
    -> (nth zz s i).1 <  (nth zz s j).1 ->  (i < j)%N.
  move => i j il jl;case (ltngtP j i) => //; last by move => ->; rewrite ltxx.
  rewrite - (lt_asym (nth zz s i).1 (nth zz s j).1); move => ij -> /=.
  move: pc;rewrite -p2 // - p2 // eq1; set s1 := [seq z.1 | z <- a::l] => ha.
  have ss1 : size s = size s1 by rewrite /s1 ss size_map.
  rewrite ss1 in il jl; exact: (sorted_prop ha jl il ij).
have p5: f3 %| p^`().
  apply:Gauss_dvdp_prod2.
    apply /allP => x /mapP [y ys -> /=].
    have:  (('X - (y.1)%:P) ^+ y.2) %| p.
      rewrite pa; apply:dvdp_mulr.
      move: (nth_index zz ys) => h;  move: ys; rewrite - index_mem => ys.
      by rewrite (big_nth zz) big_mkord (bigD1 (Ordinal ys)) //= h dvdp_mulIl.
    move /dvdpP => [q1 ->]; rewrite derivM; apply:dvdp_add;apply:dvdp_mull.
      set e := y.2; case e => // n /=; rewrite exprS; apply : dvdp_mulIr.
    rewrite deriv_exp - mulrnAl; apply : dvdp_mulIr.
  rewrite /l3 -/s -map_comp.
  apply: sorted_uniq.
  exact: lt_trans.
  exact: ltxx.
  by apply: pc.
have xx: forall i: 'I_ (size l),
   [/\  (i <= size l)%N, (i < size s)%N & (i.+1 < size s)%N].
  by move => i; rewrite ss !ltnS ltnW.
have p6: f2 %| p^`().
  apply:Gauss_dvdp_prod2.
     apply/allP => x /mapP [t] _ -> /=; move: (s2valP' (p1 t)).
      by rewrite dvdp_XsubCl /root=> ->; rewrite eqxx.
  have ->:[seq z.1 | z <- l2] = [seq s2val (p1 i)| i <- enum 'I_(size l)].
    by rewrite /l2 - map_comp.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  move => i j /= h.
  move: (xx i) (xx j)=> [isl1 isl isl2] [jsl1 jsl jsl2].
  apply: val_inj => /=; apply: anti_leq.
  move: (s2valP (p1 i)) (s2valP (p1 j)); rewrite !itv_boundlr => /=.
  rewrite h; move/andP => [lt1 lt2] /andP [lt3 lt4].
  move: (lt_trans lt1 lt4)  (lt_trans lt3 lt2).
  have ->: rs`_i = (r1 :: rs)`_(i.+1) by [].
  have ->: rs`_j = (r1 :: rs)`_(j.+1) by [].
  rewrite !p2 // ? ss ? ltnS //.
  move /(pcc _ _ isl jsl2) => sa /(pcc _ _ jsl isl2).
  by rewrite ltnS => ->; rewrite -ltnS sa.
have p7: coprimep f2 f3.
   apply: coprimep_prod; apply /allP => x xl3.
   rewrite coprimep_sym; apply /coprimep_prod; apply /allP => y yl2.
   apply:coprimep_expl; apply: coprimep_expr.
   rewrite coprimep_XsubC root_XsubC; apply /negP => /eqP.
   move: xl3 => /mapP [k ks] -> /=.
   rewrite - (nth_index zz ks) -/s; set kis := (index k s).
   move: yl2; move /mapP => [i] _ -> /= h1.
   move: (s2valP (p1 i)); rewrite !itv_boundlr => /=; rewrite h1; clear h1.
   have ->: rs`_i = (r1 :: rs)`_(i.+1) by [].
   move: (xx i) => [il0 il1 il2].
   have il3: (kis < size s)%N by rewrite index_mem.
   rewrite ! p2 // => /andP [la lb].
   move: (pcc _ _ il1 il3 la) (pcc _ _ il3 il2 lb).
   by rewrite ltnS => lc ld; move: (leq_trans lc ld); rewrite ltnn.
have : (f2 * f3) %|  p^`() by rewrite Gauss_dvdp // p6 p5.
move /dvdpP => [q1]; rewrite mulrC => sd.
have sa:  p^`() = \prod_(z <- l2++l3) ('X - (z.1)%:P) ^+ z.2 * q1.
  by rewrite big_cat.
move: (pos_split1 dnz) => [[qa qb qc qd] qe qf].
set Fa := \prod_(z <- l2 ++l3) ('X - (z.1)%:P) ^+ z.2.
set Fb := \prod_(z <- pos_roots p^`()) ('X - (z.1)%:P) ^+ z.2.
set q2:=  pos_cofactor p^`().
have Fbm: Fb \is monic by apply:monic_prod_XsubCe.
suff cp: coprimep Fa q2.
  move: (Gauss_dvdpl Fb cp); rewrite - qa {1} sa dvdp_mulIl => h.
  move: (dvdp_leq (monic_neq0 Fbm) (esym h)).
  by rewrite /npos_roots ! size_prod_XsubCe.
rewrite/Fa coprimep_sym;apply/coprimep_prod /allP => x xl.
rewrite coprimep_expr// coprimep_XsubC qe //.
by apply (allP p4); apply /mapP; exists x.
Qed.

Lemma descartes_bis p:  p != 0 ->
  (odd (npos_roots p) = odd (schange p) /\
  ((npos_roots p) <= (schange p)) %N).
Proof.
move => pa; split; first by apply:schange_parity.
move: p {2}(size p) (leqnn (size p)) pa => p n; move:p; elim:n.
  by move => p;rewrite size_poly_leq0 => ->.
move => n Hrec p spn pnz.
move: (schange_parity pnz) => od.
case (npos_roots0 p); [move => [_ dnz] |  by move => ->].
move: (leq_trans (lt_size_deriv pnz) spn); rewrite ltnS=> spln.
move:(Hrec _ spln dnz); rewrite - ltnS => /(leq_trans (pos_root_deriv p)) eq3.
move: od; case (schange_deriv p); move => -> //; move: eq3;set s := schange _.
by rewrite leq_eqVlt ltnS;case /orP => // /eqP -> /=;case (odd _).
Qed.

End SignChangeRcf.
