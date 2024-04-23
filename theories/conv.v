From mathcomp Require Import all_ssreflect ssralg matrix ssrnum vector reals normedtype order boolp classical_sets.
Require Import counterclockwise.

(******************************************************************************)
(*       a <| t |> b := t *: a + (1 - t) *: b where a,b : lmodType R          *)
(*                      for instance, a <| 0 |> b = b, etc.                   *)
(*     between x y z := x \in [y,z]                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing Num.Theory Order.POrderTheory Order.TotalTheory.

Local Open Scope order_scope.
Local Open Scope ring_scope.

Section In01.
Variable R : realType.

Definition in01 (t : R) := 0 <= t <= 1.

Lemma in010 : in01 0.
Proof. by rewrite/in01 lexx ler01. Qed.

Lemma in011 : in01 1.
Proof. by rewrite/in01 lexx ler01. Qed.

Lemma in01_ge0 t : in01 t -> 0 <= t.
Proof. by move=>/andP[]. Qed.

Lemma in01M_ge0 (t : R) : in01 t = (0 <= t * (1-t)).
Proof.
apply/idP/idP.
   by move=>/andP[t0 t1]; apply mulr_ge0=>//; rewrite subr_ge0.
move=>ge0; apply/andP; split; rewrite leNgt; apply/negP=>ti; move:ge0.
   by rewrite nmulr_rge0// subr_le0=>t1; move:(lt_trans ltr01 (le_lt_trans t1 ti)); rewrite ltxx.
by move:(ti); rewrite -subr_lt0=>t1'; rewrite nmulr_lge0// =>t0; move:(lt_trans (le_lt_trans t0 ltr01) ti); rewrite ltxx.
Qed.

Lemma in01_onem t : in01 t = in01 (1 - t).
Proof. by rewrite 2!in01M_ge0 opprB addrCA subrr addr0 mulrC. Qed.

Lemma in01M t u : in01 t -> in01 u -> in01 (t * u).
Proof.
move=>/andP[t0 t1]/andP[u0 u1]; apply/andP; split; first by apply mulr_ge0.
by apply mulr_ile1.
Qed.

Lemma in01M1 t u : in01 t -> in01 u -> (t * u == 1) = (t == 1) && (u == 1).
Proof.
move=>/andP[t0 t1]/andP[u0 u1].
apply/idP/idP; last by move=>/andP[/eqP-> /eqP->]; rewrite mulr1.
case tn1: (t == 1); first by move:tn1=>/eqP->; rewrite mul1r.
case un1: (u == 1); first by move:un1=>/eqP->; rewrite mulr1 tn1.
move=>/eqP tu1/=.
suff: t * u < 1 by rewrite tu1 ltxx.
by apply mulr_ilt1=>//; rewrite -subr_gt0 lt0r subr_eq0 subr_ge0 eq_sym ?t1 ?u1 ?tn1 ?un1.
Qed.

Lemma in01_convA t u : in01 t -> in01 u -> in01 (t / (1-(1-t)*(1-u))).
Proof.
move=> t01 u01.
have c0 : 0 <= 1 - (1 - t) * (1 - u).
  by move:t01 u01; rewrite in01_onem=>t01; rewrite in01_onem=>/(in01M t01); rewrite in01_onem=>/andP[].
apply/andP; split.
   by apply divr_ge0=>//; move:t01=>/andP[].
have [->|e0] := eqVneq (1 - (1 - t) * (1 - u)) 0; first by rewrite invr0 mulr0; exact ler01.
rewrite -{4}(divff e0).
rewrite ler_wpM2r ?invr_ge0//.
rewrite mulrBr mulr1 mulrBl -addrA opprD addrA subrr add0r opprB opprK -mulrBl -subr_ge0 -addrA subrr addr0; apply mulr_ge0; last by move:u01=>/andP[].
by move:t01; rewrite in01_onem=>/andP[].
Qed.

End In01.

Section Conv.
Variable R : realType.
Variable E : lmodType R.

Definition conv (t : R) (a b : E) := t *: a + (1 - t) *: b.

End Conv.

(* NB(rei): same notation as infotheo *)
Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 49).
Notation "a <| p |> b" := (conv p a b). (* TODO(rei): needs scope *)

Section Conv.
Variable R : realType.
Variable E : lmodType R.
Implicit Types (t u v : R) (a b c d : E).

Lemma conv0 a b : a <| 0 |> b = b.
Proof. by rewrite/conv scale0r add0r subr0 scale1r. Qed.

Lemma conv1 a b : a <| 1 |> b = a.
Proof. by rewrite/conv scale1r subrr scale0r addr0. Qed.

Lemma convmm t a : a <| t |> a = a.
Proof. by rewrite/conv -scalerDl addrCA subrr addr0 scale1r. Qed.

Lemma convC t a b : a <| t |> b = b <| 1 - t |> a.
Proof. by rewrite/conv opprB addrCA subrr addr0 addrC. Qed.

Lemma convlr t a b : a <| t |> b = a + (1 - t) *: (b-a).
Proof. by rewrite scalerDr scalerN addrCA -{2}[a]scale1r -scalerBl opprB addrCA subrr addr0 addrC. Qed.

Lemma convrl t a b : a <| t |> b = b + t *: (a - b).
Proof. by rewrite convC convlr opprB addrCA subrr addr0. Qed.

End Conv.

Section Conv.
Variable R : realType.
Variable E : lmodType R.
Implicit Types (t u v : R) (a b c d : E).

Lemma convA t u a b c : in01 t -> in01 u ->
  a <| t |> (b <| u |> c) =
  (a <| t / ((1 : R^o) <| t |> u) |> b) <| (1 : R^o) <| t |> u |> c.
Proof.
move=> t01 u01.
have -> : (1 : R^o) <| t |> u = 1 - (1 - t) * (1 - u).
  by rewrite (convlr _ (1 : R^o)) -[u-1]opprB scalerN.
rewrite/conv scalerDr addrA 2!scalerA opprB addrCA subrr addr0; congr add.
have [/eqP|tu1] := eqVneq (1 - (1 - t) * (1 - u)) 0.
  rewrite {1}subr_eq0 eq_sym in01M1 -?in01_onem// -2![_-_ == 1]subr_eq0.
  rewrite 2![1-_-1]addrAC subrr 2!add0r 2!oppr_eq0=>/andP[/eqP-> /eqP->].
  by rewrite mulr0 subr0 mulr1 subrr 3!scale0r addr0.
rewrite scalerDr 2!scalerA [(1-_*_)*(1-_)]mulrBr mulrCA divff// 2!mulr1 mulrBr.
by rewrite mulr1 addrAC opprB addrCA subrr addr0.
Qed.

Lemma convA' t u a b c : in01 t -> in01 u ->
  (a <| u |> b) <| t |> c =
  a <| t * u |> (b <| t * (1 - u) / ((1 - u : R^o) <| t |> 1) |> c).
Proof.
move=>t01 u01.
rewrite convC (convC u) convA.
   2, 3: by rewrite -in01_onem.
rewrite -convC convC (convC _ c).
have -> : (1 - u : R^o) <| t |> 1 = 1 - t * u.
  by rewrite (convrl _ _ 1) addrAC subrr add0r scalerN.
rewrite opprB addrCA subrr addr0.
have [/eqP|tu1] := eqVneq (1 - t * u) 0.
    by rewrite subr_eq0 eq_sym in01M1// =>/andP[/eqP-> /eqP->]; rewrite 2!mul1r 2!conv1.
congr (_ <| _ |> (_ <| _ |> _)).
by apply (mulfI tu1); rewrite mulrBr mulr1 2![(1-t*u)*(_/_)]mulrCA divff// 2!mulr1 opprB addrCA addrAC subrr add0r mulrBr mulr1.
Qed.

Lemma in01_conv (t u v : R) : in01 t -> in01 u -> in01 v ->
  in01 ((u : R^o) <| t |> v).
Proof.
move=>/andP[t0 t1] /andP[u0 u1] /andP[v0 v1]; apply/andP; split.
   apply addr_ge0; apply mulr_ge0=>//.
   by rewrite subr_ge0.
have<-: t + (1-t) = 1 by rewrite addrCA subrr addr0.
apply: lerD; rewrite -subr_ge0.
   rewrite -{1}[t]mulr1 -mulrBr; apply mulr_ge0=>//.
   by rewrite subr_ge0.
by rewrite -{1}[1-t]mulr1 -mulrBr; apply mulr_ge0; rewrite subr_ge0.
Qed.

Lemma in01_convl (t u : R) : 0 <= t*u -> in01 (t / (t+u)).
Proof.
have H: forall a b : R, 0 <= a*b -> 0 <= a/(a+b) by move=>a b ab0; rewrite -sgr_ge0 sgrM sgrV -sgrM sgr_ge0 mulrDr -expr2; apply addr_ge0=>//; apply sqr_ge0.
move=>tu0.
have [->|tun0] := eqVneq (t + u) 0.
   by rewrite invr0 mulr0; apply in010.
apply/andP; split; first by apply H.
rewrite -{1}[t](addr0) -(subrr u) addrA mulrBl divff// -subr_ge0 opprB addrCA subrr addr0 addrC; apply H.
by rewrite mulrC.
Qed.

Lemma conv_onem (t u v : R) :
  (1-u : R^o) <| t |> (1-v) =
  1 - (u : R^o) <| t |> v.
Proof.
rewrite/conv 2!scalerBr addrACA opprD; congr add.
have sm: forall u, u *: (1 : R^o) = u*1 by [].
by rewrite 2!sm 2!mulr1 addrCA subrr addr0.
Qed.

Lemma convACA (t u v : R) (a b c d : E) : in01 t -> in01 u -> in01 v ->
  (a <| u |> b) <| t |> (c <| v |> d) =
  (a <| t * u / ((u : R^o) <| t |> v) |> c)
    <| (u : R^o) <| t |> v |>
  (b <| t * (1 - u) / ((1 - u : R^o) <| t |> (1 - v)) |> d).
Proof.
move=>/andP[t0 t1]/andP[u0 u1]/andP[v0 v1].
move:t0; rewrite le0r => /orP[|].
   by move=>/eqP->; rewrite !mul0r !conv0.
move=>t0; move:t1; rewrite -subr_ge0 le0r => /orP[|].
   rewrite subr_eq0=>/eqP<-; rewrite !mul1r !conv1.
   move:u0; rewrite le0r => /orP[|].
      by move=>/eqP->; rewrite subr0 !conv0 divff ?oner_neq0// conv1.
   rewrite lt0r=>/andP[u0 _]; rewrite divff// conv1.
   move:u1; rewrite -subr_ge0 le0r => /orP[|].
      by rewrite subr_eq0=>/eqP<-; rewrite 2!conv1.
   by rewrite lt0r=>/andP[t1 _]; rewrite divff// conv1.
move=>t1.
have c0: forall x y : R, 0 <= x -> 0 <= y -> (x : R^o) <| t |> y = 0 -> x = 0 /\ y = 0.
   move=>x y; rewrite le0r => /orP[|].
      move=>/eqP-> _ /eqP.
      rewrite/conv scaler0 add0r mulf_eq0 => /orP[|].
         by move=>t1'; move:t1; rewrite lt0r=>/andP[/negPf]; rewrite t1'.
      by move=>/eqP->.
   move=>x0 y0 c0.
   suff: 0 < (x : R^o) <| t |> y by rewrite c0 ltxx.
   rewrite /conv -(addr0 0) ; apply: ltr_leD.
      by apply mulr_gt0.
   by apply mulr_ge0=>//; apply ltW.
have [|uv0] := eqVneq ((u : R^o) <| t |> v) 0.
   by move=>/(c0 _ _ u0 v0) [-> ->]; rewrite convmm !conv0 subr0 convmm -mulrA divff ?oner_neq0// mulr1.
move:u1 v1; rewrite -2![_ <= 1]subr_ge0=>u1 v1.
have [|uv0'] := eqVneq ((1 - u : R^o) <| t |> (1 -v)) 0.
    by move=> /(c0 _ _ u1 v1)[/eqP]; rewrite subr_eq0=>/eqP<- /eqP; rewrite subr_eq0=>/eqP<-; rewrite convmm !conv1 -mulrA divff ?oner_neq0// mulr1.
rewrite{1 2 3 4 6 8}/conv 4!scalerDr 2!addrA !scalerA -conv_onem.
rewrite 2![((_ : R^o) <| _ |> _) * (1 - _)]mulrBr 2![_ * (_ * _ / _)]mulrC -!mulrA 2![_^-1 * _]mulrC divff// divff// !mulr1 /conv [t *: _ + _ + _]addrAC subrr add0r [t *: _ + _ + _]addrAC subrr add0r; congr add.
by rewrite -2!addrA; congr add; rewrite addrC.
Qed.
End Conv.

Section between.
Variable R : realType.
Let Plane : vectType _ := (R^o * R^o)%type.

Lemma det_conv (p p' q r : Plane) (t : R) :
  det (p <| t |> p') q r = (det p q r : R^o) <| t |> det p' q r.
Proof.
have sm t' u : t' *: (u : R^o) = t' * u by [].
rewrite/conv !sm -det_cyclique -[det p q r]det_cyclique -[det p' q r]det_cyclique 3!det_scalar_productE -2!scalar_productZL -scalar_productDl; congr scalar_product.
rewrite 2!scalerBr -!addrA; congr GRing.add.
rewrite !addrA [-_ + _]addrC -addrA; congr GRing.add.
by rewrite -[-(t*:r)]scaleNr -scalerBl -opprB opprK -addrA [-t+t]addrC subrr addr0 scaleN1r.
Qed.

Lemma det0_aligned (p q r: Plane) : det p q r = 0%R <->
  (p = q \/ exists t, p <| t |> q = r).
Proof.
rewrite det_scalar_productE.
symmetry; split.
   case.
      by move=>->; rewrite subrr -(scaler0 _ 0) scalar_productZL mul0r.
      by move=> [t <-]; rewrite convlr addrAC subrr add0r rotateZ scalar_productZR scalar_product_rotatexx mulr0.
wlog: p q r / p == 0%R.
   move=> h; rewrite -[q-p]subr0 -[r-p]subr0.
   move=>/(h 0%R (q-p) (r-p) (eqxx 0%R)); case=>[ /eqP | [t] ].
      by rewrite eq_sym subr_eq0 eq_sym=>/eqP=>pq; left.
    by rewrite{1}/conv scaler0 add0r=>/(f_equal (fun x=> p+x)); rewrite [r-p]addrC addrA subrr add0r=><-; right; exists t=>//; apply convlr.
move=>/eqP p0; subst p; rewrite !subr0/scalar_product/= mulrN=>/eqP; rewrite subr_eq0=>/eqP e.
have [q0|q0] := eqVneq q 0%R; first by left.
right.
move:q0; rewrite -pair_eqE /= negb_and => /orP[|] q0.
   exists (1 - xcoord r / xcoord q)=>//.
   rewrite -convC convrl add0r subr0; apply /eqP; rewrite -pair_eqE; apply /andP; split=>/=.
   - apply/eqP.
     transitivity ((xcoord r / xcoord q) * q.1) => //.
     by rewrite -mulrA [_^-1*_]mulrC divff // mulr1.
   - apply/eqP.
     transitivity ((xcoord r / xcoord q) * q.2) => //.
     by rewrite mulrC mulrA -e mulrC mulrA [_^-1*_]mulrC divff // mul1r.
exists (1 - ycoord r / ycoord q)=>//.
   rewrite -convC convrl add0r subr0; apply /eqP; rewrite -pair_eqE; apply /andP; split=>/=.
   - apply/eqP.
     transitivity ((ycoord r / ycoord q) * q.1) => //.
     by rewrite mulrC mulrA e mulrC mulrA [_^-1*_]mulrC divff // mul1r.
   - apply/eqP.
     transitivity ((ycoord r / ycoord q) * q.2) => //.
     by rewrite -mulrA [_^-1*_]mulrC divff // mulr1.
Qed.

Definition between (x y z : Plane) := [&& (det x y z == 0)%R,
  (0%R <= scalar_product (x - y) (z - y)) ,
  (0%R <= scalar_product (x - z) (y - z)) &
  ((y == z) ==> (x == z))].

Lemma between_conv x y z : between x y z <->
  exists t, in01 t && (x == y <| t |> z).
Proof.
case yz: (y == z).
   rewrite/between yz; move:yz=>/eqP yz; rewrite yz subrr -(scale0r 0) scalar_productZR mul0r det_cyclique det_alternate eqxx lexx/=.
   split; first by move=>/eqP->; exists 0; rewrite in010 convmm/=.
   by move=>[t /andP[_]]; rewrite convmm.
rewrite /between yz/= andbT.
move:yz=>/negbT yz.
have zye: forall t (y z: Plane), t *: y + (1-t) *: z - y = (1-t) *: (z-y).
   by move=>t y' z'; rewrite {1}[_*:_+_]addrC -addrA scalerBr; congr +%R; rewrite -scaleNr opprB scalerBl scale1r.
have yze: forall t (y z: Plane), t *: y + (1-t) *: z - z = t *: (y-z).
   by move=>t y' z'; rewrite -addrA scalerBr; congr +%R; rewrite scalerBl scale1r [_-_*:_]addrC -addrA subrr addr0.
split.
   rewrite det_cyclique =>/and3P[/eqP/det0_aligned]; case; first by move=> yz'; move:yz' yz=>->; rewrite eqxx.
   move=>[t <-].
   rewrite yze zye 2!scalar_productZL=> yp zp; exists t; apply/andP; split=>//.
   apply/andP; split.
      by move:zp; rewrite pmulr_lge0//; apply scalar_productrr_gt0; rewrite subr_eq0.
    by move:yp; rewrite pmulr_lge0 ?subr_ge0//; apply scalar_productrr_gt0; rewrite subr_eq0 eq_sym.
move=>[t] /andP [/andP [t0 t1]] /eqP->.
rewrite yze zye 2!scalar_productZL; apply/and3P; split.
- by rewrite det_cyclique; apply/eqP; apply det0_aligned; right; exists t.
- by rewrite mulr_ge0// ?subr_ge0// scalar_productrr_ge0.
- by rewrite mulr_ge0// scalar_productrr_ge0.
Qed.

Lemma betweenC (a b c : Plane) : between a b c = between a c b.
Proof.
rewrite /between det_inverse -det_cyclique oppr_eq0; congr andb; rewrite !andbA; congr andb.
   by apply andbC.
by rewrite eq_sym; apply implyb_id2l=>/eqP->.
Qed.

Lemma betweenl (a b : Plane) : between a a b.
Proof. rewrite/between det_alternate eqxx/= subrr -(scale0r 0) scalar_productZL mul0r lexx/= Bool.implb_same andbT; apply scalar_productrr_ge0. Qed.

Lemma betweenr (a b : Plane) : between a b a.
Proof. rewrite betweenC; apply betweenl. Qed.

Lemma between_depl (a b c : Plane) : between a b c <->
  exists (d : Plane) (t u : R),
    (t*u <= 0) && (b == a + t *: d) && (c == a + u *: d).
Proof.
split.
   move=>/between_conv[t] /andP[t01].
   have aconv: a = t *: a + (1-t) *: a by rewrite -scalerDl addrCA subrr addr0 scale1r.
   rewrite {1}aconv -subr_eq0 opprD addrACA -2!scalerBr.
   case t1: (t == 1).
      move:t1=>/eqP->; rewrite subrr scale1r scale0r addr0 subr_eq0=>/eqP->.
      exists (c-b), 0, 1.
      by rewrite mul0r lexx scale0r addr0 eqxx scale1r addrCA subrr addr0 eqxx.
   rewrite addr_eq0 -scalerN opprB=>/eqP e.
   exists (b-a), 1, (-t / (1-t)).
   move:t1=>/negbT; rewrite eq_sym -subr_eq0=>tn1.
   move:t01=>/andP[t0 t1]; rewrite mul1r mulNr oppr_le0 scale1r addrCA subrr addr0 eqxx mulrC scaleNr -scalerN opprB -scalerA e scalerA [_*(1-t)]mulrC divff// scale1r addrCA subrr addr0 eqxx 2!andbT; apply mulr_ge0=>//.
      by rewrite invr_ge0 subr_ge0.
move=>[d][t][u]/andP[/andP[tu0]].
wlog: d t u tu0 / 0 < t.
   move=>h.
   have [t0|t0] := ltP 0 t; first by apply h.
   move:t0; rewrite le_eqVlt => /orP[|].
      by move=>/eqP->; rewrite scale0r addr0=>/eqP-> _; apply betweenl.
   by rewrite -oppr_gt0 -(opprK d) 2![_ *: - - _]scalerN -2!scaleNr; apply h=>//; rewrite mulrN -mulNr opprK.
move=>t0 /eqP be /eqP ce.
move:tu0; rewrite pmulr_rle0// =>u0.
have tugt0: 0 < t-u by rewrite subr_gt0; exact (le_lt_trans u0 t0).
have tun0: t-u != 0 by apply/negP=>/eqP tu0; move:tugt0; rewrite tu0 ltxx.
apply/between_conv; exists (-u/(t-u)); apply/andP; split.
   apply/andP; split.
      by rewrite mulr_ge0 ?oppr_ge0// invr_ge0 ltW.
   by rewrite -subr_ge0 -(pmulr_rge0 _ tugt0) mulrBr mulrCA divff// 2!mulr1 -addrA subrr addr0; apply ltW.
by rewrite/conv be ce 2!scalerDr addrACA -scalerDl [_ + (1-_)]addrCA subrr addr0 scale1r -subr_eq0 opprD addrA subrr add0r oppr_eq0 2!scalerA -scalerDl mulrBl mul1r addrCA -mulrBr mulrAC -mulrA divff// mulr1 subrr scale0r.
Qed.

Lemma between_trans (a b c d e : Plane) :
  between c a b -> between d a b -> between e c d -> between e a b.
Proof.
move=>/between_conv[t]/andP[t01 /eqP->] /between_conv[u]/andP[u01 /eqP->] /between_conv[v]/andP[v01 /eqP->].
rewrite convACA// 2!convmm.
apply between_conv; exists ((t : R^o) <| v |> u); apply/andP; split=>//.
by apply in01_conv.
Qed.

End between.
