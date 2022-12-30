From mathcomp Require Import all_ssreflect all_algebra vector reals ereal classical_sets boolp Rstruct.
From infotheo Require Import convex Reals_ext.
Require Import preliminaries.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory preliminaries.
Import fdist convex.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section convex.
Variable (E : convType).

Local Open Scope classical_set_scope.
Local Open Scope convex_scope.

Definition convex_set_of (A : set E) : is_convex_set A -> {convex_set E}.
move=>Aconv.
by exists A; apply CSet.Mixin.
Defined.

Lemma is_convex_setI (C D : {convex_set E}) : is_convex_set (C `&` D).
Proof.
by apply/asboolP=>x y p [Cx Dx] [Cy Dy]; split; [ move:(convex_setP C) | move:(convex_setP D)]; move=>/asboolP; apply.
Qed.

Lemma hullX (F : convType) (C : set E) (D : set F) : hull (C `*` D) = hull C `*` hull D.
Proof.
rewrite eqEsubset; split.
   move=>+ [n][g][d][gCD]-> =>_.
   rewrite Convn_pair; split=>/=;
      exists n; [exists (fst \o g) | exists (snd \o g)]; exists d; split=>// + [i] _ <- =>_ /=;
      (suff: ((C `*` D) (g i)) by move=>[]);
      by apply gCD; exists i.
move=>[+ +][]/=[n][g][d][gC->][m][f][e][fD->]=>_ _.
exists (n * m)%N, (fun i=> let (i, j) := split_prod i in (g i, f j)), (fdistmap (unsplit_prod (n:=m)) (d `x e)%fdist); split.
   move=>+ [i] _ <- =>_.
   by case: (split_prod i)=>a b; split; [apply gC | apply fD].
rewrite Convn_pair/comp/=; congr pair; apply S1_inj; rewrite !S1_Convn big_prod_ord/=.
   apply eq_big=>// i _.
   rewrite -(scale1pt (scalept _ _)) scaleptA//.
   rewrite -(FDist.f1 e).
   (* TODO: the next 5 lines should be a single rewrite. *)
   move: (@mulr_suml R_ringType _ (index_enum (ordinal_finType m)) (fun i=> i \in ordinal_finType m) (fun i=> Reals_ext.nneg_ff (FDist.f e) i) (Reals_ext.nneg_ff (FDist.f d) i))=>/=.
   have->: @GRing.mul R_ringType = Rdefinitions.RbaseSymbolsImpl.Rmult by [].
   have->: GRing.zero (GRing.Ring.zmodType R_ringType) = Rdefinitions.RbaseSymbolsImpl.R0 by [].
   have->: (@GRing.add (GRing.Ring.zmodType R_ringType)) = Rdefinitions.RbaseSymbolsImpl.Rplus by [].
   move=>->.
   simple refine (let h : Reals_ext.nneg_fun 'I_m := _ in _).
      exists (fun i0=> Rdefinitions.RbaseSymbolsImpl.Rmult
        (Reals_ext.nneg_ff (FDist.f e) i0)
        (Reals_ext.nneg_ff (FDist.f d) i))=>j.
      by apply ssrR.mulR_ge0; apply FDist.ge0.
   have->: \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(i0 in 'I_m)
      Rdefinitions.RbaseSymbolsImpl.Rmult
        (Reals_ext.nneg_ff (FDist.f e) i0)
        (Reals_ext.nneg_ff (FDist.f d) i) =
      \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(i in 'I_m)
      Reals_ext.nneg_f h i.
      by apply eq_big=>// j _; rewrite fdist_prodE.
   rewrite scalept_sum.
   apply eq_big=>// j _.
   rewrite/h/= fdistmapE.
   have->: \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(a in 
   prod_finType (ordinal_finType n) (ordinal_finType m) | 
   a
     \in preim (unsplit_prod (n:=m))
           (pred1 (Ordinal (unsplit_prodp i j))))

           Reals_ext.nneg_ff (FDist.f (fdist_prod d (fun=> e))) a =
      \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(a in 
   prod_finType (ordinal_finType n) (ordinal_finType m) | 
   a
     \in (pred1 (i, j)))
      Reals_ext.nneg_ff (FDist.f (fdist_prod d (fun=> e))) a.
      apply eq_big=>// k; congr andb; rewrite 3!inE.
      by refine (inj_eq _ k (i, j)); exact (can_inj (@unsplit_prodK n m)). 
   rewrite (big_pred1 (i, j))// fdist_prodE/= ssrR.mulRC; congr (scalept _ (S1 (g _))).
   by move:(unsplit_prodK (i, j))=>/(congr1 fst)/esym.
rewrite bigC/=.
apply eq_big=>// j _.
rewrite -(scale1pt (scalept _ _)) scaleptA//.
rewrite -(FDist.f1 d).
(* TODO: the next 5 lines should be a single rewrite. *)
move: (@mulr_suml R_ringType _ (index_enum (ordinal_finType n)) (fun i=> i \in ordinal_finType n) (fun i=> Reals_ext.nneg_ff (FDist.f d) i) (Reals_ext.nneg_ff (FDist.f e) j))=>/=.
have->: @GRing.mul R_ringType = Rdefinitions.RbaseSymbolsImpl.Rmult by [].
have->: GRing.zero (GRing.Ring.zmodType R_ringType) = Rdefinitions.RbaseSymbolsImpl.R0 by [].
have->: (@GRing.add (GRing.Ring.zmodType R_ringType)) = Rdefinitions.RbaseSymbolsImpl.Rplus by [].
move=>->.
simple refine (let h : Reals_ext.nneg_fun 'I_n := _ in _).
   exists (fun i=> Rdefinitions.RbaseSymbolsImpl.Rmult
      (Reals_ext.nneg_ff (FDist.f d) i)
      (Reals_ext.nneg_ff (FDist.f e) j))=>i.
   by apply ssrR.mulR_ge0; apply FDist.ge0.
have->: \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(i in 'I_n)
   Rdefinitions.RbaseSymbolsImpl.Rmult
      (Reals_ext.nneg_ff (FDist.f d) i)
      (Reals_ext.nneg_ff (FDist.f e) j) =
   \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(i in 'I_n)
   Reals_ext.nneg_f h i.
   by apply eq_big=>// i _; rewrite fdist_prodE.
rewrite scalept_sum.
apply eq_big=>// i _.
rewrite/h/= fdistmapE.
have->: \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(a in 
   prod_finType (ordinal_finType n) (ordinal_finType m) | 
   a
   \in preim (unsplit_prod (n:=m))
         (pred1 (Ordinal (unsplit_prodp i j))))

         Reals_ext.nneg_ff (FDist.f (fdist_prod d (fun=> e))) a =
   \big[Rdefinitions.RbaseSymbolsImpl.Rplus/Rdefinitions.RbaseSymbolsImpl.R0]_(a in 
   prod_finType (ordinal_finType n) (ordinal_finType m) | 
   a
     \in (pred1 (i, j)))
      Reals_ext.nneg_ff (FDist.f (fdist_prod d (fun=> e))) a.
   apply eq_big=>// k; congr andb; rewrite 3!inE.
   by refine (inj_eq _ k (i, j)); exact (can_inj (@unsplit_prodK n m)). 
rewrite (big_pred1 (i, j))// fdist_prodE/= ssrR.mulRC; congr (scalept _ (S1 (f _))).
by move:(unsplit_prodK (i, j))=>/(congr1 snd)/esym.
Qed.

End convex.

Lemma add_affine (E : lmodType R_ringType) : affine (fun p : E * E => p.1 + p.2).
Proof.
move=>p/= [x0 x1] [y0 y1]/=.
by rewrite/conv/= addrACA -2!scalerDr.
Qed.

Lemma scale_affine (E : lmodType R_ringType) (t : Rdefinitions.RbaseSymbolsImpl.R) : affine (fun x : E=> t *: x).
Proof.
move=>p/= x y.
by rewrite/conv/= scalerDr; congr GRing.add; rewrite 2!scalerA mulrC.
Qed.

Section C.
Variable E F: lmodType R_ringType.
Variable f : {linear E -> F}.

Local Open Scope fun_scope.
Local Open Scope ring_scope.
Local Open Scope convex_scope.

Lemma ker_convex: is_convex_set (preimage f [set 0]).
Proof.
apply/asboolP=>x y p /= fx0 fy0.
by rewrite linearD 2!linearZZ fx0 fy0 2!GRing.scaler0 addr0.
Qed.

End C.

Section face.

Variable E: convType.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Definition ext (A : set E) := [set x | forall u v, u \in A -> v \in A -> x \in segment u v -> x = u \/ x = v]%classic.

Definition face (A F: set E) := (F `<=` A)%classic /\ is_convex_set F /\ forall x u v, x \in F -> u \in A -> v \in A -> x \in segment u v -> x != u -> x != v -> u \in F /\ v \in F.

Definition face' (A F: set E) := (F `<=` A)%classic /\ is_convex_set F /\ forall x u v, x \in F -> u \in A -> v \in A -> x \in segment u v -> x != v -> u \in F.

Lemma face'P (A F: set E): face A F <-> face' A F.
Proof.
split; move=>[FA [Fconv Fface]]; split=>//; split=>// x u v xF uA vA xuv.
   move=>xv; case xu: (x == u).
      by move: xu=>/eqP xu; subst u.
   by move: xu=>/negP/negP xu; move: (Fface x u v xF uA vA xuv xu xv)=> [uF _].
move=>xu xv; split; [ apply (Fface x u v) | apply (Fface x v u) ]=>//.
by apply mem_set, segment_sym, set_mem.
Qed.

End face.
Section face.

Variable E: lmodType R_ringType.

Local Open Scope fun_scope.
Local Open Scope ring_scope.
Local Open Scope convex_scope.

Lemma probinvn1 : probinvn 1 = 2^-1 :> R_numFieldType.
Proof.
rewrite /R_numFieldType /GRing.inv /= /Rinvx.
case:ifP=>// /negbFE.
by rewrite/Rdefinitions.IZR intr_eq0.
Qed.

Lemma onem_half: onem 2^-1 = 2^-1.
Proof.
have ne20: (2 : R_ringType) != 0 by rewrite intr_eq0.
apply (mulfI ne20).
by rewrite mulrBr mulr1 divff// -pmulrn mulr2n -addrA subrr addr0.
Qed.

Lemma ext_carac (A : {convex_set E}) (x: E): x \in A -> [<-> x \in ext A;
  forall u v, u \in A -> v \in A -> x = u <| probinvn 1 |> v -> u = v;
  is_convex_set (A `\ x)%classic;
  face A [set x]].
Proof.
move=>xA.
have ne20: (2 : R_ringType) != 0 by rewrite intr_eq0.
have ge20: (0 : R_ringType) <= 2 by apply mulrz_ge0=>//; exact ler01.
split.
   move=>xext u v uA vA xe.
   move: xext=>/set_mem /(_ u v uA vA).
   have xuv: x \in segment u v.
      by apply mem_set; subst x; exists (probinvn 1).
   move=>{uA} {vA} /(_ xuv) {xuv}.
   wlog: u v xe / x = u.
      move=> h; case=> xe'.
         by apply h=>//; left.
      apply /esym; apply h=>//; last by left.
      rewrite xe convC; congr (v <| _ |> u).
      apply val_inj=>/=.
      rewrite probinvn1 /onem.
      by apply/eqP; rewrite subr_eq -(div1r 2) -splitr.
      move: xe=> -> + _.
      move=> /(congr1 (fun x => 2 *: x)).
      rewrite scalerDr probinvn1 onem_half 2!scalerA divff// 2!scale1r.
      by rewrite -pmulrn mulr2n scalerDl scale1r=>/addrI/esym.
split.
   move=>xext.
   apply/asboolP=>u v t [uA ux] [vA vx].
   split; first by move:(convex_setP A)=>/asboolP; apply.
   wlog: u v t xext xA uA ux vA vx / (t : R_ringType) <= 2^-1.
      move=>h.
      have [tle|tle] := boolP ((t : R_ringType) <= 2^-1); first exact: (h u v t).
      rewrite convC.
      apply (h v u (onem t)%:pr)=>//.
      rewrite -onem_half; apply ler_sub=>//.
      by move: tle; rewrite -ltNge => /ltW.
   move=>tle.
   have t01: ssrR.leRb (Rdefinitions.IZR BinNums.Z0) (2*(t : R_ringType)) &&
  ssrR.leRb (2*(t : R_ringType)) (Rdefinitions.IZR (BinNums.Zpos 1%AC)).
      apply/andP; split; apply/ssrR.leRP/RleP.
         apply mulr_ge0=>//.
         by apply/RleP/prob_ge0.
      by move:tle=>/(ler_wpmul2l ge20); rewrite divff.
   move=>/esym xE.
   move: xext=>/(_ (u <| Prob.mk t01 |> v) v).
   rewrite -convA' convmm.
   have ->: p_of_rs (Prob.mk t01) (probinvn 1) = t.
      apply val_inj.
      rewrite/= p_of_rsE/=.
      have tE: (2*(t : R_ringType))/2 = t.
         by rewrite mulrAC divff// mul1r.
      rewrite -{2}tE.
      congr Rdefinitions.RbaseSymbolsImpl.Rmult.
      rewrite/R_unitRing/GRing.inv/=/Rinvx.
      case:ifP=>//.
      by rewrite ne20.
   have wA: u <| Prob.mk t01 |> v \in A.
      by apply mem_set; move:(convex_setP A)=>/asboolP; apply.
   move: vA=>/mem_set vA /(_ wA vA xE) /(congr1 (fun x => x-v)).
   rewrite subrr /conv/= -addrA -{2}(scale1r v) -scalerBl addrAC subrr add0r scaleNr -scalerBr.
   apply /eqP; rewrite scaler_eq0; apply /negP=>/orP; case.
      rewrite mulf_eq0 pnatr_eq0/= =>/eqP t0.
      move:xE.
      have ->: t = 0%:pr by apply val_inj.
      by rewrite conv0=>/esym.
   rewrite subr_eq0=>/eqP uv; subst v.
   by move:xE; rewrite convmm=>/esym.
split.
   move=>/asboolP Axconv.
   split; [ by move=>u /= ->; apply set_mem |]; split; [ by apply is_convex_set1 |]=> y u v /set_mem -> /set_mem uA /set_mem vA /set_mem [p _ xE] xu xv; exfalso.
   have uAx: (A `\ x)%classic u by split=>//= ux; subst u; move: xu; rewrite eq_refl.
   have vAx: (A `\ x)%classic v by split=>//= vx; subst v; move: xv; rewrite eq_refl.
   have: (A `\ x)%classic x by rewrite -{2}xE; apply (Axconv _ _ _ uAx vAx).
   by move=>[_ /= f].
move=>xface; apply /mem_set=>u v uA vA xuv.
suff: (x == u) || (x == v) by move=>/orP; case=> /eqP ->; [ left | right ].
apply /negP=>/negP; rewrite negb_or=>/andP [xu xv].
move: xface=>[_ [_ /(_ x u v)]].
have xx: x \in [set x]%classic by apply /mem_set.
move=>/(_ xx uA vA xuv xu xv) [/set_mem /= ux /set_mem /= vx]; subst u.
by move: xu; rewrite eq_refl.
Qed.

Lemma face_trans (A : set E) (F : set E) (G : set E) : face A F -> face F G -> face A G.
Proof.
move=>[AF [Fconv Fface]] [FG [Gconv Gface]].
split.
   by move=> x Gx; apply AF, FG.
split=>// x u v xG uA vA xuv xu xv.
have [uF vF]: (u \in F /\ v \in F).
   apply (Fface x)=>//.
   by apply mem_set, FG, set_mem.
by apply (Gface x).
Qed.

Definition hyperplan_appui (A : set E) (f: {linear E -> GRing.regular_lmodType R_ringType}) (a: R_ringType) := (exists x, x \in A /\ f x = a) /\ ((forall x, x \in A -> f x <= a) \/ (forall x, x \in A -> a <= f x)).

Lemma is_convex_set_preimage [T U : convType] (f : {affine T -> U}) (A : {convex_set U}) : is_convex_set (f @^-1` A)%classic.
Proof.
apply/asboolP=>x y p/= Ax Ay.
by rewrite affine_conv -in_setE; apply/mem_convex_set; rewrite in_setE.
Qed.

(* TOTHINK : lemmas prove is_convex_set but use {convex_set _}. *)
Lemma hyperplan_appui_face (A : {convex_set E}) (f: {linear E -> GRing.regular_lmodType R_ringType}) (a: R_ringType): hyperplan_appui A f a <-> (exists x, x \in A /\ f x = a) /\ face A (A `&` (preimage f [set a])).
Proof.
split; move=>[hex hface]; split=>//.
   wlog: f a hex hface / (forall x : E, x \in A -> f x <= a).
      move=>h; move: (hface); case=>hf.
         by apply (h f a).
      move: h=>/(_ (GRing.comp_linear f (GRing.opp_linear E)) (- a)).
      have hf': forall x : E, x \in A -> GRing.comp_linear f (GRing.opp_linear E) x <= - a by move=>x xA /=; rewrite -scaleN1r linearZZ scaleN1r ler_oppl opprK; apply hf.
      have hex': exists x : E, x \in A /\ GRing.comp_linear f (GRing.opp_linear E) x = - a.
         by move: hex=>[x [xA fx]]; exists x; split=>//=; rewrite -fx -scaleN1r linearZZ scaleN1r.
      move=>/(_ hex' (or_introl hf') hf'); congr (face A (A `&` _)).
      by rewrite eqEsubset; split=>x /= /eqP; rewrite -scaleN1r linearZZ scaleN1r; [ rewrite eqr_opp | rewrite -eqr_opp ]=>/eqP.
   move=> hf; apply face'P; split; [ by apply subIsetl |]; split.
      exact (is_convex_setI _ (convex_set_of (is_convex_set_preimage _ (convex_set_of (is_convex_set1 (a : GRing.regular_lmodType R_ringType)))))).
   move=> x u v /set_mem [xA xa] uA vA /set_mem [t _ tx] xv; apply mem_set; (split; [ by apply set_mem |]); apply /eqP; rewrite -lte_anti; apply /andP; (split; [ by apply hf |]).
   have t0: (t : R_ringType) != 0.
      by apply /eqP=>/val_inj t0; subst t; move: tx xv; rewrite conv0 => ->; rewrite eqxx.
   have tgt: 0 < (t : R_ringType) by rewrite lt0r t0=>/=; apply/RleP/prob_ge0.
   move: tx=>/(f_equal (fun x=> (t : R_ringType)^-1 *: (x-((onem t) : R_ringType)*: v))).
   rewrite -addrA subrr addr0 scalerA mulVf // scale1r=>->.
   rewrite linearZZ linearD xa -scaleNr linearZZ ler_pdivl_mull// addrC -subr_ge0 -addrA -mulNr -{1}[a]mul1r -mulrDl scaleNr -scalerN -mulrDr; apply mulr_ge0.
      by apply/RleP/prob_ge0.
   by rewrite addrC Num.Internals.subr_ge0; apply hf.
have: forall x y, x \in A -> y \in A -> f x < a -> a < f y -> False.
   move=> u v uA vA fua afv.
   move: (Order.POrderTheory.lt_trans fua afv); rewrite -subr_gt0=>fufv.
   have t01: ssrR.leRb (Rdefinitions.IZR BinNums.Z0) ((f v - a) / (f v - f u)) &&
  ssrR.leRb ((f v - a) / (f v - f u)) (Rdefinitions.IZR (BinNums.Zpos 1%AC)).
      apply/andP; split; apply/ssrR.leRP/RleP.
         by apply divr_ge0; apply ltW=>//; rewrite subr_gt0.
         rewrite ler_pdivr_mulr// mul1r -subr_ge0 opprB addrAC addrCA subrr addr0 subr_ge0.
         by apply ltW.
   move: hface=>/face'P [_ [_ /(_ (u <| Prob.mk t01 |> v) u v)]].
   have inuv: u <| Prob.mk t01 |> v \in segment u v.
      by apply mem_set; exists (Prob.mk t01).
   have uva: f (u <| Prob.mk t01 |> v) = a.
      rewrite/= affine_conv/=/conv/=.
      move: fufv; rewrite lt0r=>/andP [fufv _].
      apply (mulfI fufv).
      rewrite/GRing.regular_lmodType/GRing.scale/=.
      rewrite mulrDr mulrAC mulrCA mulrAC divff// mulr1.
      rewrite [onem _ * _]mulrBl mul1r mulrBr mulrAC mulrCA mulrAC divff// mulr1.
      rewrite -mulrBl opprB addrAC addrCA subrr addr0.
      rewrite 2!mulrBl mulrC addrAC addrCA subrr addr0.
      by rewrite -mulrBr mulrC.
   have Aa: u <| Prob.mk t01 |> v \in (A `&` f @^-1` [set a])%classic.
      apply mem_set; split=>//.
      by move:(convex_setP A)=>/asboolP; apply; rewrite -in_setE.
   move=>/(_ Aa uA vA inuv).
   have nev: u <|{| Prob.p := (f v - a) / (f v - f u); Prob.Op1 := t01 |}|> v != v.
      rewrite -subr_eq0 -{4}(scale1r v) -addrA -scalerBl addrAC subrr add0r scaleNr -scalerBr scaler_eq0 subr_eq0.
      apply/negP=>/orP; case=>/eqP.
         move=>/= t0.
         move:uva; rewrite/conv/= t0 scale0r add0r onem0 scale1r=>fva.
         by move:afv; rewrite fva lt_irreflexive.
      by move=>uv; move:fufv; rewrite uv subrr lt_irreflexive.
   by move=>/(_ nev) /set_mem [_ /= fuae]; move: fua; rewrite fuae -subr_gt0 lt0r subrr eq_refl.
move=>h.
move: (boolp.EM (exists x: E, x \in A /\ f x < a)); case.
   move: (boolp.EM (exists x: E, x \in A /\ a < f x)); case.
      by move=>[y [yA afy]] [x [xA fxa]]; elim (h x y xA yA fxa afy).
   by move=>allge _; left=> x xA; rewrite leNgt; apply /negP=>fxa; apply allge; exists x; split.
by move=>allge; right=> x xA; rewrite leNgt; apply /negP=>fxa; apply allge; exists x; split.
Qed.

End face.
Section cone.

Variable E: lmodType R_ringType.

Local Open Scope fun_scope.
Local Open Scope ring_scope.
Local Open Scope convex_scope.

Definition cone0 (A: set E) := ([set (t : R_ringType) *: a | t in (@setT Rpos) & a in A] `<=` A)%classic.
Definition cone (x: E) (A: set E) := cone0 [set a-x | a in A]%classic.

Lemma cone0_convex (A: set E): cone0 A -> (is_convex_set A <-> ([set a+b | a in A & b in A] `<=` A)%classic).
Proof.
have ne20: (2 : R_ringType) != 0 by rewrite intr_eq0.
have /RltP/ssrR.ltRP gt20: (0 : R_ringType) < 2 by rewrite ltr0z.
move=>Acone; split=>Aconv.
   move=>x [u uA] [v vA] <-.
   have uA2: A (2 *: u) by apply Acone; exists (Rpos.mk gt20)=>//; exists u.
   have vA2: A (2 *: v) by apply Acone; exists (Rpos.mk gt20)=>//; exists v.
   move:Aconv=>/asboolP/(_ _ _ (probinvn 1) uA2 vA2); congr A.
   by rewrite/conv/= probinvn1 onem_half 2!scalerA mulrC divff// 2!scale1r.
apply/asboolP.
move=>x y t xA yA.
move:(prob_ge0 t)=>/RleP; rewrite le0r=>/orP; case.
   by rewrite/conv/= =>/eqP ->; rewrite scale0r add0r onem0 scale1r.
move=>/RltP/ssrR.ltRP t0; move: (prob_le1 t)=>/RleP; rewrite -subr_ge0 le0r=>/orP; case.
   by rewrite subr_eq0 /conv/= =>/eqP <-; rewrite onem1 scale0r addr0 scale1r.
move=>/RltP/ssrR.ltRP t1; apply Aconv; exists ((t : R_ringType) *: x); [| exists ((onem t) *: y) ]=>//; apply Acone.
   by exists (Rpos.mk t0)=>//; exists x.
by exists (Rpos.mk t1)=>//; exists y.
Qed.

(* Note: cone0_of A is NOT pointed due to lemma cone0_of_convE. *)
(* TODO: maybe change the 0 <= k i to 0 < k i in the definition of conv. *)

Definition cone0_of (A: set E): set E := [set a | exists n (s : 'I_n.+1 -> E) (k: 'I_n.+1 -> Rpos),
  \sum_i (k i : R_ringType) *: (s i) = a /\ (range s `<=` A)%classic].

Lemma cone0_of_cone0 (A: set E): cone0 (cone0_of A).
Proof.
move=>x [t /= _] [a [n [s [k [<- sA]]]]] <-.
rewrite scaler_sumr; exists n, s, (fun i => mulRpos t (k i)); split => //.
by apply congr_big=>// i _; apply /esym; apply scalerA.
Qed.

Lemma cone0_of_hullE (A: set E): cone0_of A = [set (t : R_ringType) *: a | t in (@setT Rpos) & a in (hull A)]%classic.
Proof.
rewrite eqEsubset; split=>x.
   move=>[n [s [k [<- kA]]]]; set t := \sum_i (k i : R_ringType).
   have k0': forall i : ordinal_finType n.+1, true -> 0 <= (k i : R_ringType) by move=>i _; apply/ltW/RltP/Rpos_gt0.
   have: 0 <= t by apply sumr_ge0.
   rewrite le0r=>/orP; case.
      move=>/eqP /psumr_eq0P; move=> /(_ k0') /(_ ord0 Logic.eq_refl) k00; exfalso.
      by move:(Rpos_gt0 (k ord0))=>/RltP; rewrite k00 lt_irreflexive.
   move=>t0.
   have tk0: forall i, Rdefinitions.Rle (Rdefinitions.IZR BinNums.Z0) ([ffun i => t^-1 * k i] i).
      by move=>i; rewrite ffunE; apply/RleP/mulr_ge0; [ apply ltW; rewrite invr_gt0 | apply k0' ].
   have tk1 : \sum_(i < n.+1) [ffun i => t^-1 * k i] i = 1.
      transitivity (\sum_(i < n.+1) t^-1 * k i).
         by apply congr_big=>// i _; rewrite ffunE.
      rewrite -mulr_sumr mulrC divff//.
      by move:t0; rewrite lt0r=>/andP[].
   move:(t0)=>/RltP/ssrR.ltRP t0'; exists (Rpos.mk t0')=>//; exists (t^-1 *: \sum_i (k i : R_ringType) *: s i).
      exists n.+1, s, (@FDist.make _ (finfun (fun i=> t^-1 * k i)) tk0 tk1); split=> //.
      rewrite scaler_sumr avgnrE.
      apply congr_big=>// i _.
      by rewrite scalerA ffunE.
   by rewrite scalerA divff ?gt_eqF// scale1r.
move=>[t /= _] [a [n [s [d [sA ->]]]]] <-.
rewrite avgnrE scaler_sumr (@mathcomp_extra.bigID_idem _ _ _ _ _ _ _ _ (fun i=> 0 < d i)); [| apply addrA | apply addrC | apply addr0 ].
have ->: \sum_(i | true && ~~ (0 < d i)) (t : R_ringType) *: (d i *: s i) = \sum_(i | true && ~~ (0 < d i)) 0 *: 0.
   apply congr_big=>// i /andP [_]; rewrite lt0r negb_and negbK.
   move:(FDist.ge0 d i)=>/RleP->; rewrite orbF=>/eqP->.
   by rewrite 2!scale0r GRing.scaler0.
rewrite -[\sum_(_ < _ | _) 0 *: 0]scaler_sumr scale0r addr0 -big_filter /=.
remember [seq i <- index_enum (ordinal_finType n) | 0 < d i] as I; move: HeqI=>/esym HeqI.
case: I HeqI=> [| i I] HeqI.
   exfalso; move: (FDist.f1 d) (oner_neq0 R_ringType); rewrite (@mathcomp_extra.bigID_idem _ _ _ _ _ _ _ _ (fun i=> 0 < d i)); [| apply addrA | apply addrC | apply addr0 ].
   rewrite -big_filter HeqI big_nil/=.
   have ->: forall x, Rdefinitions.RbaseSymbolsImpl.Rplus Rdefinitions.RbaseSymbolsImpl.R0 x = 0+x by [].
   have ->: Rdefinitions.IZR (BinNums.Zpos 1%AC) = 1 by [].
   rewrite add0r=><- /eqP; apply. 
   transitivity (\sum_(i < n | true && ~~ (0 < d i)) (0*0:R_ringType)).
      2: by rewrite -mulr_sumr mul0r.
   by apply congr_big=>// i /= dile; move: (FDist.ge0 d i)=>/RleP; rewrite le0r mul0r=>/orP; case=> [ /eqP // | ]; move: dile=>/[swap]->.
have: subseq (i::I) (index_enum (ordinal_finType n)) by rewrite -HeqI; apply filter_subseq.
case: n s d sA i I HeqI=> [| n] s d sA i I HeqI.
   by inversion i.
move=> /subseq_incl; move=> /(_ ord0); rewrite size_index_enum card_ord; move=> [f [fn flt]].
rewrite /cone0_of/=.
exists (size I), (s \o (nth ord0 (i :: I))).
simple refine (ex_intro _ _ _).
   move=>j; apply (mulRpos t).
   simple refine (Rpos.mk _).
      exact (d (nth ord0 (i :: I) j)).
   rewrite -HeqI.
   apply/ssrR.ltRP/RltP/(@nth_filter _ (fun i=> 0 < d i)).
   by rewrite HeqI.
split.
   rewrite [in RHS]HeqI.
   rewrite -[in RHS](mask_true (s:=i :: I) (leqnn (size I).+1)) big_mask.
   apply congr_big=>// j.
      by rewrite nth_nseq; case:j=>/= j ->.
   move=>_ /=.
   by rewrite scalerA (tnth_nth ord0)/=.
move=>+/= [j] _ <- =>_.
by apply sA; eexists.
Qed.
      
Lemma cone0_of_sub_cone0_convex (A: set E) (B: {convex_set E}) :
  (A `<=` B -> cone0 B -> cone0_of A `<=` B)%classic.
Proof.
rewrite cone0_of_hullE=>AB Bcone x [t t0 [a aA <-]].
apply Bcone; exists t=>//; exists a=>//.
by apply (hull_sub_convex AB).
Qed.

End cone.


Section Fun.

Variable E: convType.
Variable f: E -> \bar R_ringType.

Local Open Scope fun_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope convex_scope.

Definition fconvex := forall (x y: E) (t: prob),
  f (x <|t|> y) <= EFin (t : R_ringType) * f x + EFin (onem t)%R * f y.

Definition fconvex_strict := forall (x y: E) (t: oprob), x <> y ->
  f (x <|t|> y) < EFin (t : R_ringType) * f x + EFin (onem t)%R * f y.

Lemma muleDl_ge0 (R : realDomainType) (x y z : \bar R) :
  0 <= y -> 0 <= z -> (y + z) * x = y * x + z * x.
Proof.
case: y=>// [y | _].
   rewrite lee_fin le0r -lte_fin=>/orP; case=>[/eqP-> _ | y0].
      by rewrite mul0e 2!add0e.
   case yne0: (y%:E == 0).
      by move:yne0 y0=>/eqP->; rewrite lt_irreflexive.
all: case: z=>// [z | _].
   1, 3: rewrite lee_fin le0r -lte_fin=>/orP; case=>[/eqP-> | z0].
      1, 3: by rewrite mul0e 2!adde0.
   1, 2: case zne0: (z%:E == 0); first by move:zne0 z0=>/eqP->;
         rewrite lt_irreflexive.
      have: 0 < y%:E + z%:E by apply adde_gt0.
      case yzne0: (y%:E + z%:E == 0); move:yzne0.
         by move=>/eqP->; rewrite lt_irreflexive.
all: case: x=>[x | |]; rewrite/adde/adde_subdef/mule/mule_subdef/=
    ?lt0y// ?yne0 ?y0// ?zne0 ?z0//.
- by rewrite mulrDl.
- by move=>-> ->. 
- by move=>-> ->.
all: case: ifP=>[/eqP/= x0 | _]; last by case: ifP.
3: by rewrite addr0.
all: by rewrite (EFin_inj x0) mulr0 addr0.
Qed.

Lemma lee_pemul (R : realDomainType) (t : R) (x y : \bar R) :
  (0 < t)%R -> (t%:E * x <= t%:E * y) = (x <= y).
Proof.
rewrite -lte_fin=>t0.
case tne0: (t%:E == 0); first by move:tne0 t0=>/eqP->; rewrite lt_irreflexive.
case:x=>[x | |]; case:y=>[y | |];
    rewrite/mule/mule_def/= ?tne0 ?t0// ?leey// ?leNye//.
move:t0; rewrite 2!lee_fin lte_fin=>t0.
by rewrite -subr_ge0 -mulrBr pmulr_rge0// subr_ge0.
Qed.

Lemma fconvex_max_ext (C: {convex_set E}) (x: E):
  fconvex_strict ->
  x \in C ->
  f x < +oo ->
  (forall y, y \in C -> f y <= f x) ->
  x \in ext C.
Proof.
move=> fconv xC fxoo xmax.
rewrite in_setE/ext/= =>u v /xmax uC /xmax vC /set_mem [t] _ xE; subst x.
move: (prob_ge0 t)=>/RleP; rewrite le0r=>/orP; case.
   by move=>/eqP/val_inj ->; right; rewrite conv0.
move=>t0.
move: (prob_le1 t)=>/RleP; rewrite -subr_ge0 le0r=>/orP; case.
   have->: Rdefinitions.IZR (BinNums.Zpos 1%AC) = Prob.p (1%R)%:pr by [].
   by rewrite subr_eq0=>/eqP/val_inj <-; left; rewrite conv1.
rewrite subr_gt0=>t1.
have t01: ssrR.ltRb (Rdefinitions.IZR BinNums.Z0) t &&
       ssrR.ltRb t (Rdefinitions.IZR (BinNums.Zpos 1%AC)).
   by apply/andP; split; apply/ssrR.ltRP/RltP.
case /boolP: (u == v); first by move=>/eqP->; rewrite convmm; left.
move=>/eqP uv.
move:(fconv u v (OProb.mk t01) uv)=>/=.
have fle: (Prob.p t)%:E * f u + (onem (Prob.p t))%:E * f v <= f (u <|t|> v).
   have ->: f (u <|t|> v) = (Prob.p t)%:E * f (u <|t|> v) + (onem (Prob.p t))%:E * f (u <|t|> v).
      rewrite -muleDl_ge0 ?lee_fin /onem ?RminusE -?EFinD.
      - by rewrite addrCA subrr addr0 mul1e.
      - by apply ltW.
      - by rewrite subr_ge0; apply/RleP/prob_le1.
   apply (@lee_add R_realDomainType); rewrite (@lee_pemul R_realDomainType)=>//.
   by rewrite subr_gt0.
by move=>/(le_lt_trans fle); rewrite lt_irreflexive.
Qed.


End Fun.
