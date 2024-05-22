Require Export counterclockwise conv encompass preliminaries.
From mathcomp Require Import all_ssreflect ssralg matrix ssrnum vector reals normedtype order boolp classical_sets constructive_ereal.

(******************************************************************************)
(*  separated a b c d == true if a = b or (ab) intersects [c,d]               *)
(*  intersect a b c d == true if [a, b] and [c, d] intersect                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp.algebra_tactics Require Import ring.
From mathcomp.zify Require Import zify.

Import GRing Num.Theory Order.POrderTheory Order.TotalTheory.

Local Open Scope order_scope.
Local Open Scope ring_scope.

Module Spec := SpecKA(ccw_KA).

Section Plane.
Variable R : realType.
Let Plane := Plane R.

Definition separate (a b c d : Plane) := (det a b c * det a b d <= 0) &&
  ((a == b) ==> between a c d) &&
  ((det a b c == 0) ==> (det a b d == 0) ==> (a != b) ==>
    [|| between a c d, between b c d | (between c a b && between d a b)]).

Lemma separateCl (a b c d : Plane) : separate a b c d = separate b a c d.
Proof.
rewrite/separate 2![det _ b _]det_inverse mulrN mulNr opprK.
rewrite -2![det a _ _]det_cyclique 2!oppr_eq0 eq_sym.
rewrite orbA (orbC (_ a c d)) -orbA.
congr (_ && _ && (_ ==> _ ==> _ ==> (_ || _))).
- by apply implyb_id2l=>/eqP->.
- by rewrite !(@betweenC _ _ a b).
Qed.

Lemma separateCr (a b c d : Plane) : separate a b c d = separate a b d c.
Proof.
rewrite/separate mulrC ![_ _ c d]betweenC; congr andb.
by rewrite -Bool.implb_curry andbC Bool.implb_curry andbC.
Qed.

Definition intersect (a b c d : Plane) := separate a b c d && separate c d a b.

Lemma intersectCl (a b c d : Plane) : intersect a b c d = intersect b a c d.
Proof. by rewrite/intersect separateCl; congr andb; apply separateCr. Qed.

Lemma intersectCr (a b c d : Plane) : intersect a b c d = intersect a b d c.
Proof. by rewrite/intersect separateCr; congr andb; apply separateCl. Qed.

Lemma intersect_correct a b c d : intersect a b c d ->
  exists p, between p a b && between p c d.
Proof.
have sm t u : t *: (u : R^o) = t * u by [].
wlog abc0: a b c d / 0 <= det a b c.
   move=>h.
   case ge0: (0 <= det a b c); first by apply h.
   move:ge0=>/negP/negP; rewrite leNgt -oppr_gt0 -det_inverse -det_cyclique negbK intersectCl=>/ltW ge0 bacd.
   by move:(h _ _ _ _ ge0 bacd)=>[p]; rewrite betweenC=>pb; exists p.
case ab: (a == b).
  by move=>/andP[/andP[/andP[_]]]; rewrite ab/==>acd _ _; exists a; rewrite betweenl.
case cd: (c == d).
  by move=>/andP[_]/andP[/andP[_]]; rewrite cd/==>cab _; exists c; rewrite betweenl andbT.
move=>/andP[/andP [/andP[absep _] ab0]] /andP[/andP[cdsep _] cd0].
move: abc0; rewrite le0r => /orP[|].
   move=>/eqP/det0_aligned; case; first by move=>abe; move:ab; rewrite abe eqxx.
   move=>[t] ce; move: cdsep cd0; rewrite cd -ce 2!det_conv -![det _ d _]det_cyclique 2!det_alternate /conv 4!sm 2!mulr0 add0r addr0 det_inverse -det_cyclique mulrN mulNr mulrACA oppr_le0.
   case tlt: ((1-t) * t < 0).
      rewrite nmulr_rge0// -expr2=>badle.
      have-> : (det b a d = 0) by apply/eqP; rewrite -sqrf_eq0; apply/eqP/le_anti/andP; split=>//; apply sqr_ge0.
      rewrite 2!mulr0 oppr0 eqxx/= =>/or3P[| |]; last first.
        by move=>/andP[acd _]; exists a; rewrite betweenl.
      by exists d; rewrite betweenr andbT.
      by move=> cdb; exists (a <| t |> b); rewrite betweenl andbT.
   move=>_ _; exists (a <| t |> b); rewrite betweenl andbT; apply between_conv.
   by exists t; rewrite eqxx andbT in01M_ge0 leNgt mulrC tlt.
move:ab0=> _ abc; move:absep; rewrite pmulr_rle0// =>abd.
set t := det a b d / (det d a b - det c a b).
have denom: det d a b - det c a b != 0 by rewrite 2![det _ a b]det_cyclique subr_eq0; apply/negP=>/eqP detE; move:(le_lt_trans abd abc); rewrite detE ltxx.
have: det a b (c <| t |> d) == 0 by rewrite -det_cyclique det_conv convrl sm -opprB mulrN /t -mulrA [_^-1 * _]mulrC divff// mulr1 det_cyclique subrr.
move=>/eqP /det0_aligned; case; first by move=>/eqP; rewrite ab.
move=>[u utE].
case u01: (in01 u).
   exists (a <| u |> b); apply/andP; split.
      apply between_conv.
      by exists u; rewrite u01 eqxx.
   rewrite utE; apply between_conv.
   exists t; rewrite eqxx andbT in01M_ge0 -(divff denom) /t -mulrBl mulrACA addrAC ![det _ a b]det_cyclique subrr add0r mulrN -mulNr -expr2; apply mulr_ge0; last first.
    by apply sqr_ge0.
   by apply mulr_ge0; [ rewrite oppr_ge0 | apply ltW ].
move:u01; rewrite in01M_ge0 leNgt=>/negbT; rewrite negbK=>u01.
move:(u01); rewrite -oppr_gt0 lt0r oppr_eq0 mulf_eq0 negb_or=>/andP[/andP [/lregP u0 /lregP u1] _].
have: det (a <| u |> b) c d == 0 by rewrite utE det_conv -[det d _ _]det_cyclique 2!det_alternate convmm.
rewrite det_conv 2![det _ c d]det_cyclique addr_eq0 2!sm=>/eqP udetE.
move:cdsep; rewrite -(nmulr_rge0 _ u01) mulrACA udetE mulNr oppr_ge0 -expr2=>det2_le0.
have /eqP cdb0: det c d b == 0 by rewrite -(mulrI_eq0 _ u1) -sqrf_eq0; apply/eqP/le_anti/andP; split=>//; apply sqr_ge0.
move:udetE=>/eqP; rewrite cdb0 mulr0 oppr0 mulrI_eq0// =>/eqP cda0.
move:cd0; rewrite cdb0 cda0 eqxx cd/= =>/or3P[cab|dab|]; last first.
- by move=>/andP[acd _]; exists a; rewrite betweenl.
- by exists d; rewrite betweenr andbT.
- by exists c; rewrite betweenl andbT.
Qed.

Lemma intersect_complete a b c d :
  (exists p, between p a b && between p c d) -> intersect a b c d.
Proof.
have sm: forall t u, t *: (u : R^o) = t*u by [].
move:a b c d.
suff: forall a b c d, (exists p : counterclockwise.Plane R, between p a b && between p c d) -> separate a b c d.
   move=> h a b c d abcd; apply/andP; split; apply h=>//.
   by move:abcd=>[p]; rewrite andbC=>pabcd; exists p.
   move=>a b c d [p] /andP[/between_conv] [t] /andP[t01] /eqP pe /between_conv [u] /andP[u01] /eqP pe'; subst p; rewrite/separate -andbA.
apply/andP; split.
   have: det (a <| t |> b) a b == 0 by rewrite det_conv -[det b a b]det_cyclique 2!det_alternate convmm.
   rewrite pe' det_conv 2![det _ a b]det_cyclique addr_eq0 2!sm=>/eqP detE.
   move:u01; rewrite in01M_ge0 le0r =>/orP[|].
      rewrite mulf_eq0 subr_eq0 => /orP[|] /eqP ue; move:detE=>/eqP.
         by rewrite ue mul0r subr0 mul1r eq_sym oppr_eq0=>/eqP->; rewrite mulr0.
      by rewrite -ue mul1r subrr mul0r oppr0=>/eqP->; rewrite mul0r.
   by move=>ui; rewrite -(pmulr_rle0 _ ui) mulrACA detE mulNr oppr_le0 -expr2; apply sqr_ge0.
case ab : (a == b)=>/=.
   by move: ab=>/eqP ab; subst b; rewrite 2!det_alternate eqxx/= andbT; apply between_conv; exists u; apply/andP; split=>//; rewrite -pe' convmm.
apply/implyP=>/eqP/det0_aligned[]; first by move=>/eqP; rewrite ab.
move=>[t'] ce; apply/implyP=> /eqP/det0_aligned[]; first by move=>/eqP; rewrite ab.
move=>[u'] de.
wlog: c d u t' u' pe' u01 ce de / t' <= u'.
   move=>h.
   case tu: (t' <= u'); first by apply (h c d u t' u').
   move:tu; rewrite leNgt=>/negbT; rewrite negbK=>/ltW ut.
   by rewrite 2![_ _ c d]betweenC andbC; apply (h d c (1-u) u' t')=>//; rewrite -?in01_onem -?convC.
move=>tu.
move:pe'; rewrite -{1}ce -{1}de /conv 3![(_ - _) *: b]scalerBl scale1r 3![_ *: _ + (_ - _)]addrCA -3!scalerBr 2![_ *: (_ + _ *: _)]scalerDr addrACA -scalerDl [u+(1-u)]addrCA subrr addr0 scale1r 2!scalerA -scalerDl=>/addrI/eqP.
rewrite -subr_eq0 -scalerBl scaler_eq0 2!subr_eq0 ab orbF=>tconv.
case t0: (t' < 0).
  apply/or3P/Or32.
  apply/between_depl; exists (a-b), t', u'; rewrite -ce -de 2!convrl 2!eqxx 2!andbT nmulr_rle0//.
  move:u01 tconv=>/andP[u0]; rewrite -[u<=1]subr_ge0 le0r subr_eq0 -invr_gt0 => /orP[|].
     by move=>/eqP<-; rewrite subrr mul1r mul0r addr0=>/eqP te; move:t01=>/andP[]; rewrite te leNgt t0.
  move=>ugt0.
  have un0: (1-u)^-1 != 0 by apply/negP=>/eqP ue; move:ugt0; rewrite ue ltxx.
  move:un0 (un0); rewrite {1}invr_eq0=>un0 /rregP ureg.
  rewrite -subr_eq0 -(mulIr_eq0 _ ureg) opprD addrA mulrBl mulrAC divff// mul1r subr_eq0=>/eqP<-; apply mulr_ge0; last by apply ltW.
  apply addr_ge0; first by move:t01=>/andP[t0' _].
  by rewrite -mulrN mulr_ge0 // oppr_ge0 ltW.
move:t0=>/negbT; rewrite -leNgt=>t0.
case u1: (1 < u').
   apply/or3P/Or31.
   apply/between_depl; exists (b - a), (1 - t'), (1 - u'); rewrite -2!convlr ce de 2!eqxx 2!andbT.
   move:u01 tconv=>/andP; rewrite le0r=>[[/orP[|]]].
      move=>/eqP-> _; rewrite subr0 mul0r mul1r add0r=>/eqP tu'.
      by move:t01; rewrite tu'=>/andP[_]/(lt_le_trans u1); rewrite ltxx.
   move:u1; rewrite -subr_lt0=>ugt1 u0 u1; rewrite nmulr_lle0//.
   have un0 : u != 0 by rewrite gt_eqF.
   move:(un0); rewrite -invr_eq0=>/rregP ureg.
   rewrite -subr_eq0 -(mulIr_eq0 _ ureg) opprD addrCA addrC mulrBl mulrAC divff// mul1r subr_eq0=>/eqP<-; rewrite -(pmulr_rge0 _ u0) mulrBr mulrCA divff// 2!mulr1 opprB addrA subr_ge0.
   move:t01=>/andP[_] t1.
   apply (le_trans t1); rewrite -subr_ge0 addrAC -opprB -mulrN1 -mulrDr [-1+_]addrC.
   by rewrite mulr_ge0// subr_ge0// -subr_le0 ltW.
move:u1=>/negbT; rewrite -leNgt=>u1.
apply/or3P/Or33.
apply/andP; split; apply between_conv.
  by exists t'; rewrite ce eqxx andbT /in01 t0/= (le_trans tu).
by exists u'; rewrite de eqxx andbT /in01 u1 (le_trans t0).
Qed.

Lemma is_left_oriented (p q r : Plane) :
  encompass.is_left (@wccw R) p q r = wccw p q r.
Proof.
apply/idP/idP; last by rewrite/encompass.is_left; move=>->; rewrite !orbT.
by move=>/or3P[| |//] /eqP re; subst r; rewrite /wccw det_cyclique;
  [rewrite det_cyclique |]; rewrite det_alternate.
Qed.

(* We prove that if a segment does not intersect the border of a
   convex set C, then either the segment is included in C, or they are
   disjoint.

   C is represented by a list of points that generate it (as given by
   the output of Jarvis' algorithm).

   We prove the result by contradiction, assuming that one point of
   the segment lies inside C and another one is outside. We
   immediately reduce to the case where the ends of the segment verify
   this property.

   Let [a, b] be the segment, with a in C and b outside. Notice that
   t \mapsto b <| t |> a is a continuous curve from a to b, hence we
   expect it to cross the border of C. Let I = \{t \in [0, 1],
   b <| t |> a \in C\} and t = sup(I). t is well defined because I is not
   empty (as 0 \in I) and bounded (by 1).  C being defined by a set of
   large inequalities,

   we show b <| t |> a \in C.  Then we show that at
   least one inequality is an equality. Let this constraint being
   given by two points x and y of the list defining C.  Then b <| t |> a
   is on the line (xy) and every other point of the list is strictly
   to the left of the line (xy), hence every other inequality is
   strict. Then, looking at the inequalities involving x and y, we
   show that b <| t |> a is between x and y, which concludes the proof.
   *)

Import Order.TBLatticeTheory.

Lemma hull_border_no_intersection (l : seq Plane) (a b : Plane) :
  (3 <= size l)%N ->
  uniq l ->
  encompass (@ccw R) l l ->
  (forall i : 'I_(size l), ~~ intersect l`_i l`_i.+1mod a b) ->
    (forall t, in01 t ->
      encompass (@ccw R) [:: a <| t |> b] l) \/
    (forall t, in01 t ->
      ~~ encompass (@wccw R) [:: a <| t |> b] l).
Proof.
have sm t u : t *: (u : R^o) = t * u by [].
move=> ls /uniqP lu ll lab.
have l0 : l != [::] by destruct l.
(* We start the proof by contradiction. *)
apply/or_asboolP/negPn; rewrite negb_or; apply/negP => /andP[/existsp_asboolPn [t /asboolPn]].
rewrite asbool_imply negb_imply 2!asboolb => /andP[t01 ltab].
move=> /existsp_asboolPn [u /asboolPn].
rewrite asbool_imply negb_imply 2!asboolb negbK => /andP[u01 luab].
(* We have two points, exactly one of them being encompassed by l,
   we may assume that they are the ends of the segment. *)
wlog : a b t u lab t01 ltab u01 luab / (t == 0) && (u == 1).
   move=> /(_ (a <| u |> b) (a <| t |> b) 0 1); apply.
   - move=> i.
     apply/negP => /intersect_correct[p]/andP[pl pab].
     move: (lab i) => /negP; apply; apply intersect_complete.
     exists p; apply/andP; split=>//; refine (between_trans _ _ pab).
       by apply between_conv; exists u; apply/andP; split => //.
     by apply between_conv; exists t; apply/andP; split => //.
   - by apply in010.
   - by rewrite conv0.
   - by apply in011.
   - by rewrite conv1.
   - by apply/andP; split.
move=>/andP[/eqP t0 /eqP u1]; subst t u; clear t01 u01.
move:ltab luab; rewrite conv0 conv1 => lb la.
(* We define I = \{t \in R, b <| t |> a is encompassed by l\}.
   We show that I is not empty and bounded. *)
set I := [set t | in01 t && encompass (@wccw R) [:: b <| t |> a] l]%classic.
have I0 : I 0 by apply/andP; split; [apply in010 | rewrite conv0 ].
have Ib : has_sup I.
   split; first by exists 0.
   by exists 1 => x /andP[/andP[_]].
move: la; rewrite encompass_all_index l0/= =>/forallP.
setoid_rewrite andbT.
setoid_rewrite is_left_oriented; rewrite /wccw => la.
(* All constraints being a large inequality, they are all satisfied by sup I. *)
have lt (i : 'I_(size l)) : wccw l`_i l`_i.+1mod (b <| sup I |> a).
  rewrite /wccw leNgt -det_cyclique det_conv convrl sm -opprB mulrN.
  rewrite subr_lt0; apply/negP=>liI.
  have abl0 : 0 < det a l`_i l`_i.+1mod - det b l`_i l`_i.+1mod.
     rewrite ltNge; apply/negP => abl.
     move: (sup_upper_bound Ib)=>/(_ 0 I0)Ige.
     move:(mulr_le0_ge0 abl Ige); rewrite mulrC=>/(lt_le_trans liI).
     rewrite ltNge=>/negP; apply.
     by rewrite det_cyclique; apply la.
  move:abl0 (abl0); rewrite {1}lt0r => /andP[abl0 _].
  rewrite -invr_gt0 => abl_gt0.
  move:(liI); rewrite -subr_gt0 -(pmulr_lgt0 _ abl_gt0) mulrBl.
  rewrite -mulrA divff// mulr1 => eps0.
  move: (sup_adherent eps0 Ib) => [t]/andP[t01].
  rewrite encompass_all_index l0/= => /forallP/(_ i).
  rewrite andbT is_left_oriented /wccw -det_cyclique det_conv convrl.
  rewrite sm -opprB mulrN -(pmulr_lge0 _ abl_gt0) mulrBl -mulrA.
  rewrite divff// mulr1 subr_ge0=>lit.
  rewrite opprB addrCA subrr addr0=>/(le_lt_trans lit).
  by rewrite ltxx.
have I1 : sup I <= 1.
  apply sup_le_ub; first by exists 0.
  by move=>x /andP[/andP[_]].
(* At least one inequality is an equality, otherwise we would find
   t > sup I that verifies all of them. *)
have : [exists i : 'I_(size l), det l`_i l`_i.+1mod (b <| sup I |> a) <= 0].
  move:I1; rewrite -subr_ge0 le0r subr_eq0 subr_gt0 => /orP[/eqP<-| I1].
    rewrite conv1; move:lb; rewrite encompass_all_index l0/= =>/forallPn[i].
    rewrite andbT !negb_or -leNgt =>/andP[_] /andP[lb det_le0].
    by apply/existsP; exists i.
  rewrite -[_ _ _]negbK; apply/negP =>/existsPn Isubopt.
  (* Each inequality defines a quantity by which we may exceed sup I
     without falsifying it.  The inequalities being strict, these
     quantities are all positive, hence their mini too.  Alas, R has
     no maximum, and hence min has no neutral elemnt, so we work in
     \bar R. *)
  set t := \meet_(i < size l | 0 < det a l`_i l`_i.+1mod - det b l`_i l`_i.+1mod)
    ((det l`_i l`_i.+1mod a) / (det l`_i l`_i.+1mod a - det l`_i l`_i.+1mod b))%:E.
  have It : ((sup I)%:E < mine t 1%:E)%E.
    rewrite ltxI lte_fin I1 andbT ereal_meets_gt// ?ltey//.
    move=>i abl_gt0; move:(abl_gt0); rewrite lt0r=>/andP[abl0 _].
    rewrite lte_fin -subr_gt0 -(pmulr_lgt0 _ abl_gt0) mulrBl mulrAC -mulrA.
    rewrite -2![det l`_i _ _]det_cyclique divff// mulr1.
    by move:(Isubopt i); rewrite -ltNge -det_cyclique det_conv convrl sm -opprB mulrN.
  have tfin : (fine (mine t 1%:E))%:E = mine t 1%:E.
    apply/(@fineK R)/fin_numP; split; apply/negP=>/eqP tinf.
      suff : (-oo < mine t 1)%E by rewrite tinf ltxx.
      rewrite ltxI; apply/andP; split; last by apply: ltNye.
      by apply ereal_meets_gt=>// i _; apply ltNye.
    suff : (mine t 1 < +oo)%E by rewrite tinf ltxx.
    by rewrite ltIx [(1 < +oo)%E]ltey orbT.
  move: It; rewrite -tfin lte_fin ltNge=>/negP; apply.
  have t01: in01 (fine (mine t 1%E)).
    apply/andP; split; rewrite -lee_fin tfin; last by rewrite lteIx le_refl orbT.
    rewrite ltexI; apply/andP; split; last by rewrite lee_fin ler01.
    apply: Order.TLatticeTheory.meets_ge => i abgt; rewrite lee_fin; apply: (mulr_ge0 (la _)).
    by apply ltW; rewrite invr_gt0 -2![det l`_i _ _]det_cyclique.
  apply: sup_upper_bound => //; apply/andP; split => //.
  rewrite encompass_all_index l0/=; apply/forallP => i.
  rewrite is_left_oriented andbT /wccw -det_cyclique det_conv convrl sm.
  rewrite -opprB mulrN subr_ge0.
  have [/[dup]|able0] := ltP 0 (det a l`_i l`_i.+1mod - det b l`_i l`_i.+1mod).
    rewrite {1}lt0r -invr_gt0=>/andP[ab0 _] abgt0.
    rewrite -subr_ge0 -(pmulr_lge0 _ abgt0) mulrBl subr_ge0 -mulrA divff// mulr1.
    rewrite -lee_fin tfin leIx; apply/orP; left.
    rewrite ![det _ l`_i _]det_cyclique /t.
    by move:abgt0; rewrite invr_gt0=>abgt; exact: Order.TLatticeTheory.meets_inf.
  rewrite {2}[det a _ _]det_cyclique (le_trans _ (la i))// mulr_ge0_le0 //.
  by move:t01 => /andP[].
move=> /existsP[i] iable0.
(* We want to show that b <| sup I |> a suits.
   We show that it is between] a and b and between l`_i and l`_(i+1).
   This gives a witness to contradict the hypo (lab i). *)
move: lab =>/(_ i)/negP; apply; apply intersect_complete.
exists (b <| sup I |> a); apply/andP; split; last first.
  rewrite betweenC; apply between_conv; exists (sup I); apply/andP; split=>//.
  apply/andP; split=>//.
  by apply sup_upper_bound.
(* First, b <| sup I |> a, l`_i and l`_(i+1) are aligned. *)
have : det l`_i l`_i.+1mod (b <| sup I |> a) = 0.
  by apply: le_anti; apply/andP; split => //; apply: lt.
move=>/det0_aligned[/lu|].
  rewrite 2!inE.
  move=>/(_ (ltn_ord i) (ltn_ord i.+1mod)); rewrite Zp_succE.
  move:(ltn_ord i); rewrite leq_eqVlt => /predU1P[il|isl].
    rewrite il modnn=>i0; move:il; rewrite i0=>s1; move:ls; rewrite s1=>/ltnW.
    by rewrite ltnn.
  by rewrite modn_small// => /n_Sn.
move=>[t] tie; apply between_conv; exists t; rewrite tie eqxx andbT.
(* b <| sup I |> a is l`_i <| t |> l`_(i+1) for some t. We show 0 <= t <= 1
   by contradiction by looking at the inequalities
   0 <= det l`_j l`_(j+1) (b <| sup I |> a) for j = i+1 and j = i-1. *)
apply/negPn/negP; rewrite negb_and -2!ltNge => /orP[t0|].
   move:lt=>/(_ (Zp_succ i)); rewrite -tie /wccw -det_cyclique det_conv det_alternate /conv scaler0 addr0 sm nmulr_rge0// =>ile.
   move:ll; rewrite encompass_all_index l0/= =>/forallP/(_ i)/allP/(_ l`_(Zp_succ (Zp_succ i))).
   have /[swap]/[apply] : l`_i.+1mod.+1mod \in l by apply mem_nth.
   rewrite /encompass.is_left /ccw ltNge ile orbF => /orP[|] /eqP/lu; rewrite 2!inE=>/(_ (ltn_ord _) (ltn_ord _)); rewrite !Zp_succE=>/eqP; rewrite -2!addn1 modnDml -addnA addn1.
      by rewrite -{2}(modn_small (ltn_ord i)) -{2}(addn0 i) eqn_modDl modn_small// mod0n=>/eqP.
   rewrite eqn_modDl modn_small// modn_small; last by apply ltnW.
   by move=>/eqP.
rewrite -subr_lt0 => t0.
have predi_ltl : ((i + (size l).-1) %% (size l) < size l)%N by apply/ltn_pmod/ltnW/ltnW.
have succ_predi : Zp_succ (Ordinal predi_ltl) = i.
   apply val_inj; rewrite Zp_succE -addn1 modnDml -addnA addn1 prednK; last by do 2 apply ltnW.
   by rewrite modnDr modn_small.
move:lt=>/(_ (Ordinal predi_ltl)); rewrite succ_predi -tie /wccw -det_cyclique det_conv -det_cyclique det_alternate /conv scaler0 add0r sm nmulr_rge0// =>ile.
move:ll; rewrite encompass_all_index l0/= =>/forallP/(_ (Ordinal predi_ltl))/allP/(_ l`_(Zp_succ i)).
have /[swap]/[apply] : l`_(Zp_succ i) \in l by apply mem_nth.
rewrite succ_predi /encompass.is_left /ccw ltNge -det_cyclique ile orbF => /orP[|] /eqP/lu; rewrite 2!inE=>/(_ (ltn_ord _) (ltn_ord _)); rewrite !Zp_succE=>/eqP.
   rewrite -addn1 eqn_modDl modn_small//; last by apply ltnW.
   rewrite modn_small; last by rewrite prednK=>//; do 2 apply ltnW.
   rewrite -eqSS prednK; last by do 2 apply ltnW.
   by move=>/eqP s2; move:ls; rewrite s2 ltnn.
by rewrite -{2}(modn_small (ltn_ord i)) -addn1 -{2}(addn0 i) eqn_modDl mod0n modn_small; last by apply ltnW.
Qed.

End Plane.
