From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly polydiv polyorder ssrnum zmodp.
From mathcomp Require Import polyrcf qe_rcf_th complex.
Require Import poly_normal pol.

(*
This file consists of several sections:
- nonnegative lists, polynomials with nonnegative coefs,
  proof of Proposition 2.39 of [bpr], monic_roots_changes_eq0
- complements for scaleX_poly
- complements for transformations in R and roots
- complements for transformations and equality
- complements for transformations in C and roots
- proof of 3 circles i)
- proof of 3 circles ii)
*)

Set Implicit Arguments.
Unset Strict Implicit.

Import Order.Theory GRing.Theory Num.Theory Num.Def.
Import Pdiv.Idomain.

Local Open Scope ring_scope.

Section about_nonneg.

Variable R : rcfType.

Local Notation C := (complex R).

Definition nonneg (s : seq R) := all (fun x => 0 <= x) s.

Lemma nonnegP (s : seq R) :
  reflect (forall k, (k < size s)%N -> 0 <= s`_k) (nonneg s).
Proof. exact/all_nthP. Qed.

Lemma nonneg_poly_deg1 (a : R) : nonneg ('X - a%:P) = (a <= 0).
Proof.
by rewrite polyseqXsubC /= ler01 oppr_ge0 !andbT.
Qed.

Import complex.

Lemma nonneg_poly_deg2 (z : C) :
  nonneg ('X^2 + (1 *- 2 * Re z) *: 'X + (Re z ^+ 2 + Im z ^+ 2)%:P) =
  ((Re z) <= 0).
Proof.
rewrite -(mul1r 'X^2) mul_polyC polyseq_deg2 /= ?oner_neq0 // ler01 !andbT.
by rewrite nmulr_rge0 ?oppr_lt0 ?ltr0n // addr_ge0 // sqr_ge0.
Qed.

Lemma nonneg_mulr (p q : {poly R}) : nonneg p -> nonneg q -> nonneg (p * q).
Proof.
have [->|Hpsize] := eqVneq p 0; first by rewrite mul0r.
have [->|Hqsize Hp Hq] := eqVneq q 0; first by rewrite mulr0.
apply/nonnegP => k lpq.
rewrite coef_mul_poly /= sumr_ge0 // => i _.
apply: mulr_ge0.
  have [Hi2|Hi2] := ltnP i (size p); first exact/nonnegP.
  by rewrite -(coefK p) coef_poly ltnNge Hi2.
have [Hi2|Hi2] := ltnP (k - i) (size q); first exact/nonnegP.
by rewrite -(coefK q) coef_poly ltnNge Hi2.
Qed.

Local Notation toC := (fun (p : {poly R}) =>
   @map_poly R _ (real_complex R) p).

Lemma nonneg_root_nonpos (p : {poly R}) : p \is monic ->
   (forall z : C, root (toC p) z -> (Re z <= 0)) -> nonneg p.
Proof.
move=> Hpmonic.
move: {2}(size p) (leqnn (size p)) => n.
elim: n p Hpmonic=> [p Hpmonic Hpsize Hproot | n IH p Hpmonic Hpsize Hproots].
(* size p <= 0 *)
  rewrite size_poly_leq0 in Hpsize.
  by rewrite (eqP Hpsize) monicE lead_coef0 eq_sym oner_eq0 in Hpmonic.
(* size p <= n.+1 *)
case: (altP (size (toC p) =P 1%N)) => Hpsize2.
(* size p = 1 *)
  rewrite size_map_poly_id0 in Hpsize2;
    last by rewrite eq_sym negbT // lt_eqF // ltcR (eqP Hpmonic) ltr01.
  have Hp := (size1_polyC (eq_leq Hpsize2)).
  rewrite Hp in Hpsize2.
  rewrite Hp monicE lead_coefE Hpsize2 -pred_Sn polyseqC in Hpmonic.
  rewrite size_polyC in Hpsize2.
  rewrite Hpsize2 /= in Hpmonic.
  by rewrite Hp /= (eqP Hpmonic) polyseqC oner_neq0 /= ler01.
(* size p != 1 *)
move/closed_rootP : Hpsize2.
case=> x Hrootx.
have [Himx|Himx] := altP (Im x =P 0).
(* real root *)
  have H := monicXsubC (Re x).
  have Hp := real_root_div_poly_deg1 Himx Hrootx.
  rewrite Pdiv.IdomainMonic.dvdp_eq // in Hp.
  rewrite (eqP Hp) nonneg_mulr //.
    apply: IH=> [ | | z Hz].
    + by rewrite monicE -(@lead_coef_Mmonic _ (p %/ ('X - (Re x)%:P))
          ('X - (Re x)%:P)) // -(eqP Hp) -monicE.
    - rewrite size_divp; last by apply: monic_neq0.
      by rewrite size_XsubC leq_subLR addnC addn1.
    + rewrite Hproots // (eqP Hp) rmorphM rootM.
      apply/orP; by left.
  by rewrite nonneg_poly_deg1 (Hproots x Hrootx).
(* pair of complex roots *)
have H : 'X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P \is monic.
  by rewrite -(mul1r 'X^2) mul_polyC monicE lead_coefE polyseq_deg2 // oner_neq0.
have H2 : size ('X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P) = 3%N.
  by rewrite -(mul1r 'X^2) mul_polyC polyseq_deg2 // oner_neq0.
have Hp := complex_root_div_poly_deg2 Himx Hrootx.
rewrite Pdiv.IdomainMonic.dvdp_eq // in Hp.
rewrite (eqP Hp) nonneg_mulr //.
  apply: IH=> [ | | z Hz].
 + by rewrite monicE -(@lead_coef_Mmonic _ _ ('X^2 + (1 *- 2 * Re x) *: 'X +
    (Re x ^+ 2 + Im x ^+ 2)%:P)) // -(eqP Hp) -monicE.
  - rewrite size_divp; last by apply: monic_neq0.
    by rewrite H2 leq_subLR addnC addn2 (@leq_trans n.+1).
  + by rewrite Hproots // (eqP Hp) rmorphM rootM Hz.
by rewrite nonneg_poly_deg2 (Hproots _ Hrootx).
Qed.

Lemma nonneg_changes0 (s : seq R) : nonneg s -> changes s = 0%N.
Proof.
elim: s => [ |a ] //.
case=> [_ _ |b l IHbl /andP [] Ha Hblnonneg].
  by rewrite /= mulr0 addn0 ltxx.
have /andP[Hb Hlnonneg] := Hblnonneg.
apply/eqP; rewrite addn_eq0 eqb0 -leNgt mulr_ge0 //=.
apply/eqP; by apply: IHbl.
Qed.

(* Proposition 2.39 *)
Lemma monic_roots_changes_eq0 (p : {poly R}) : p \is monic ->
   (forall (z : C), (root (toC p) z) -> (Re z <= 0)) ->
   changes p = 0%N.
Proof.
move=> Hpmonic H.
by rewrite nonneg_changes0 // nonneg_root_nonpos.
Qed.

End about_nonneg.

Section about_scaleX_poly. (* move this section to pol.v*)

Variable (R : comRingType).

Lemma scaleX_poly_is_linear (c : R) : linear (scaleX_poly c).
Proof. by move=> a u v; rewrite /scaleX_poly comp_polyD comp_polyZ. Qed.

Lemma scaleX_poly_multiplicative (c : R) : multiplicative (scaleX_poly c).
Proof.
split. move=> x y; exact: comp_polyM. by rewrite /scaleX_poly comp_polyC.
Qed.

HB.instance Definition _ (c : R) := GRing.isLinear.Build _ _ _ _ _ (scaleX_poly_is_linear c).

HB.instance Definition _ c := GRing.isMultiplicative.Build _ _ _ (scaleX_poly_multiplicative c).

(*Canonical scaleX_poly_rmorphism c := AddRMorphism (scaleX_poly_multiplicative c).*)

Lemma scaleX_polyC (c a : R) : a%:P \scale c = a%:P.
Proof. by rewrite /scaleX_poly comp_polyC. Qed.

End about_scaleX_poly.

Section about_transformations.
Variable R : fieldType.
(*
Lemma root_shift_1 (p : {poly R}) (a x : R) :
   (root p x) = root (p \shift a) (x-a).
Proof. by rewrite !rootE -horner_shift_poly1. Qed.
*)
Lemma root_shift_2 (p : {poly R}) (a x : R) :
  root p (x + a) = root (p \shift a) x.
Proof. by rewrite !rootE -{2}(@addrK _ a x) -horner_shift_poly1. Qed.
(*
Lemma root_scale_1 (p : {poly R}) (a x : R) : (a != 0) ->
   root p x = root (p \scale a) (x / a).
Proof.
move=> Ha.
by rewrite !rootE horner_scaleX_poly mulrC (@mulrVK _ a _ x) // unitfE.
Qed.
*)
Lemma root_scale_2 (p : {poly R}) (a x : R) :
  root p (a * x) = root (p \scale a) x.
Proof. by rewrite !rootE horner_scaleX_poly. Qed.
(*
Lemma root_reciprocal_1 (p : {poly R}) (x : R) : (x != 0) ->
   root p x = root (reciprocal_pol p) (x^-1).
Proof.
move=> Hx.
rewrite !rootE horner_reciprocal1; last by rewrite unitfE.
rewrite GRing.mulrI_eq0 //; apply: GRing.lregX.
by apply/lregP.
Qed.
*)
Lemma root_reciprocal_2 (p : {poly R}) (x : R) : x != 0 ->
  root p (x^-1) = root (reciprocal_pol p) x.
Proof.
move=> Hx.
rewrite !rootE horner_reciprocal ?unitfE//.
by rewrite mulrI_eq0 //; apply/lregX/lregP.
Qed.
(*
Lemma root_Mobius_1 (p : {poly R}) (x : R) (l r : R) :
   (l != r) -> (x != l) -> (x != r) ->
   root p x = root (Mobius p l r) ((r - x) / (x - l)).
Proof.
move=> Hlr Hxl Hxr.
rewrite /Mobius.
rewrite -root_shift_2 -(@mulrK _ (x - l) _ 1); last by rewrite unitfE subr_eq0.
rewrite mul1r -mulrDl addrA -(@addrA _ _ (-x) x) (@addrC _ (-x) x) addrA addrK.
rewrite -root_reciprocal_2.
  rewrite invrM; last by rewrite unitfE invr_eq0 subr_eq0.
    rewrite invrK -root_scale_2 mulrC divrK;
      last by rewrite unitfE subr_eq0 eq_sym.
    by rewrite -root_shift_2 -addrA (@addrC _ _ l) addrA addrK.
  by rewrite unitfE subr_eq0 eq_sym.
apply: GRing.mulf_neq0.
  by rewrite subr_eq0 eq_sym.
by rewrite invr_eq0 subr_eq0.
Qed.
*)

(* TODO(rei): define as an instance of Mobius in pol.v? *)
Definition Mobius' (R : ringType) (p : {poly R}) (a b : R) : {poly R} :=
(*  Mobius (size p).-1 a b p.? *)
  reciprocal_pol ((p \shift a) \scale (b - a)) \shift 1.

Lemma root_Mobius'_2 (p : {poly R}) (x : R) (l r : R) :
  x + 1 != 0 ->
  root p ((r + l * x) / (x + 1)) = root (Mobius' p l r) x.
Proof.
move=> Hx.
rewrite /Mobius -root_shift_2 -root_reciprocal_2 //.
rewrite -root_scale_2 -root_shift_2 -{3}(@mulrK _ (x + 1) _ l).
  by rewrite -mulrDl {2}(@addrC _ x 1) mulrDr mulr1 addrA
       -(addrA r (- l) l) (addrC (-l) l) addrA addrK.
by rewrite unitfE.
Qed.

Lemma Mobius'M (p q : {poly R}) (l r : R) :
   Mobius' (p * q) l r = Mobius' p l r * Mobius' q l r.
Proof.
by rewrite /Mobius' !rmorphM /= reciprocalM rmorphM.
Qed.

Lemma Mobius'_Xsubc (c l r : R) : (l != r) ->
  Mobius' ('X - c%:P) l r = (l - c) *: 'X + (r - c)%:P.
Proof.
move=> Hlr.
rewrite /Mobius' rmorphB /= shift_polyC rmorphB /= scaleX_polyC
   /shift_poly comp_polyX rmorphD /= scaleX_polyC /scaleX_poly
   comp_polyX -addrA -(rmorphB _ l c) /= reciprocal_monom.
  by rewrite rmorphD rmorphM /= comp_polyX !comp_polyC
    mulrDl polyC1 mul1r mulrC mul_polyC -addrA (addrC (l - c)%:P _)
    -rmorphD /= addrA addrNK.
by rewrite subr_eq0 eq_sym.
Qed.

Lemma Mobius'_Xsubc_monic (c l r : R) : l != r -> l != c ->
  (lead_coef (Mobius' ('X - c%:P) l r))^-1 *: (Mobius' ('X - c%:P) l r) =
  'X + ((r - c) / (l - c))%:P.
Proof.
move=> Hlr Hlc.
rewrite Mobius'_Xsubc //  lead_coefE.
have Hlc2 : (l - c) != 0 by rewrite subr_eq0.
have HlcP : ((l - c)%:P == 0) = false.
  apply/eqP/eqP.
  by rewrite polyC_eq0 subr_eq0.
have Hsize : size ((l - c) *: 'X + (r - c)%:P) = 2%N.
  by rewrite -(mul_polyC (l - c) 'X) size_MXaddC HlcP /= size_polyC Hlc2.
have Hcoef1 : ((l - c) *: 'X + (r - c)%:P)`_1 = l - c.
  by rewrite coefD coefC addr0 -mul_polyC coefMX coefC /=.
by rewrite Hsize -mul_polyC Hcoef1 mulrDr mul_polyC -rmorphM
   mulrC -!mul_polyC mulrA (mulrC _ 'X) -rmorphM (mulrC _ (l - c))
   mulfV //= polyC1 mulr1.
Qed.

End about_transformations.

Section about_transformations_and_equality.

Variable (R : idomainType).

Lemma shift_poly_eq (p q : {poly R}) (a : R) :
  (p == q) = (p \shift a == q \shift a).
Proof.
by rewrite /shift_poly -(subr_eq0 p q) -(@comp_poly2_eq0 _ (p-q) ('X + a%:P))
  ?size_XaddC // rmorphB subr_eq add0r.
Qed.

Lemma scale_poly_eq (p q : {poly R}) (a : R) : (a != 0) ->
  (p == q) = (p \scale a == q \scale a).
Proof.
move=> Ha.
by rewrite /scaleX_poly -(subr_eq0 p q) -(@comp_poly2_eq0 _ (p - q) ('X * a%:P))
  ?size_XmulC // rmorphB subr_eq add0r.
Qed.

Lemma pdivmu0_0th_neq0 (p : {poly R}) : p != 0 -> (p %/ 'X^(\mu_0 p))`_0 != 0.
Proof.
move=> Hp.
have H0noroot : ~~(root (p %/ 'X^(\mu_0 p)) 0).
  rewrite -mu_gt0.
    rewrite -eqn0Ngt -(addr0 'X) -(@oppr0 {poly R}) -polyC0 mu_div
      ?subn_eq0; by rewrite leqnn.
  rewrite Pdiv.CommonIdomain.divp_eq0 negb_or Hp /= negb_or.
  rewrite -size_poly_gt0 {1}size_polyXn /= -leqNgt dvdp_leq //.
  by rewrite -(addr0 'X) -oppr0 -polyC0 root_mu.
rewrite -horner_coef0. apply: negbT.
by move/rootPf : H0noroot.
Qed.

Lemma Mobius'0 (p : {poly R}) (a b : R) : a != b ->
  (p == 0) = ((Mobius' p a b) == 0).
Proof.
move=> ab; apply/idP/idP => /eqP Hp.
  by rewrite /Mobius' Hp /shift_poly /scaleX_poly !comp_polyC
     reciprocalC comp_polyC.
rewrite /Mobius' in Hp.
rewrite (shift_poly_eq p 0 a) shift_polyC (@scale_poly_eq _ _  (b - a)).
  by rewrite /scaleX_poly comp_polyC -reciprocal0 (shift_poly_eq _ _ 1)
     shift_polyC Hp.
by rewrite subr_eq0 eq_sym.
Qed.

End about_transformations_and_equality.

From mathcomp Require Import complex.

Section transformations_in_C.
Local Open Scope complex_scope.

Variable (R : rcfType).
Local Notation C:= (complex R).

Local Notation toC := (fun (p : {poly R}) => @map_poly R _ (real_complex R) p).

Lemma shift_toC (p : {poly R}) (a : R) : toC (p \shift a) = (toC p) \shift a%:C.
Proof.
by rewrite /shift_poly (map_comp_poly _ p ('X + a%:P)) rmorphD /=
   map_polyX map_polyC.
Qed.

Lemma scale_toC (p : {poly R}) (a : R) : toC (p \scale a) = (toC p) \scale a%:C.
Proof.
by rewrite /scaleX_poly (map_comp_poly _ p ('X * a%:P)) rmorphM /=
   map_polyX map_polyC.
Qed.

Lemma reciprocal_toC (p : {poly R}) :
  toC (@reciprocal_pol _ p) = reciprocal_pol (toC p).
Proof.
rewrite /reciprocal_pol poly_def rmorph_sum /= poly_def size_map_inj_poly.
- apply: eq_bigr => i _.
  rewrite -mul_polyC rmorphM /= map_polyXn /=.
  by rewrite !coef_map /= map_polyC /= mul_polyC.
- exact: complexI.
- by rewrite -complexr0.
Qed.

Lemma Mobius'_toC (p : {poly R}) (l r : R) :
  toC (Mobius' p l r) = Mobius' (toC p) l%:C r%:C.
Proof.
by rewrite {2}/Mobius' -shift_toC /= -rmorphB -scale_toC
   -reciprocal_toC -shift_toC /Mobius.
Qed.

(*
Lemma root_Mobius_C_1 :  forall (p : {poly R}) (z : C) (l r : R),
   (l != r) -> (z != l%:C) -> (z != r%:C) ->
      root (toC p) z =
      root (toC (Mobius p l r)) ((r%:C - z) / (z - l%:C)).
Proof.
move=> p z l r Hlr Hzl Hzr.
have HlrC : (l%:C != r%:C).
  by rewrite -!complexr0 eq_complex /= negb_and eq_refl orbF.
rewrite !rootE Mobius_toC /Mobius -!rootE -@root_shift_2
   -(@mulrK _ (z - l%:C) _ 1).
  rewrite mul1r -mulrDl addrA -(@addrA _ _ (-z) z) (@addrC _ (-z) z) addrA
     addrK -root_reciprocal_2.
    rewrite invrM.
        rewrite invrK -root_scale_2 mulrC divrK.
          by rewrite -root_shift_2 -addrA (@addrC _ _ l%:C) addrA addrK.
        by rewrite unitfE subr_eq0 eq_sym.
      by rewrite unitfE subr_eq0 eq_sym.
    by rewrite unitfE invr_eq0 subr_eq0.
  apply: GRing.mulf_neq0.
    by rewrite subr_eq0 eq_sym.
  by rewrite invr_eq0 subr_eq0.
by rewrite unitfE subr_eq0.
Qed.
*)

Lemma root_Mobius'_C_2 (p : {poly R}) (z : C) (l r : R) :
  z + 1 != 0 ->
  root (toC p) ((r%:C + l%:C * z) / (z + 1)) = root (toC (Mobius' p l r)) z.
Proof.
move=> Hz.
rewrite !rootE Mobius'_toC /Mobius -!rootE -root_shift_2 -root_reciprocal_2 //.
rewrite -root_scale_2 -root_shift_2 -{3}(@mulrK _ (z + 1) _ l%:C).
  by rewrite -mulrDl {2}(@addrC _ z 1) mulrDr mulr1 addrA
   -(addrA r%:C (- l%:C) l%:C) (addrC (-l%:C) l%:C) addrA addrK.
by rewrite unitfE.
Qed.

End transformations_in_C.

Lemma mul_polyC_seqmul (R : rcfType) (p : {poly R}) (a : R) :
  a != 0 ->
  polyseq (a *: p) = seqmul (nseq (size p) a) p.
Proof.
move=> Ha; elim/poly_ind : p => [ | p c IHp].
  by rewrite size_poly0 /= seqmul0 -mul_polyC mulr0 -polyC0 polyseq0.
rewrite -{2}(cons_poly_def) -mul_polyC mulrDr mulrA mul_polyC -polyCM.
rewrite -!cons_poly_def !polyseq_cons.
case Hp : (nilp p); last first.
  rewrite ifT; last first.
    rewrite nil_poly in Hp.
    by rewrite nil_poly -mul_polyC mulf_neq0 // ?Hp // polyC_eq0.
  by rewrite seqmul_cons IHp.
rewrite ifF; last first.
  rewrite nil_poly in Hp.
  by rewrite nil_poly -mul_polyC mulf_eq0 Hp orbT.
rewrite /= size_polyC.
have [->|Hc] := eqVneq c 0; first by rewrite mulr0 seqmul0 polyseqC eq_refl.
by rewrite !polyseqC mulf_neq0//= Hc seqmul_cons.
Qed.

Lemma changes_mulC  (R : rcfType) (p : {poly R}) (a : R) : a != 0 ->
   changes p = changes (a *: p).
Proof.
move=> Ha.
rewrite mul_polyC_seqmul //=.
case: p.
elim => [Hs//|b/=].
case => [_ _ |c l IHcl Hs] //=.
  by rewrite !addn0 !mulr0.
rewrite /= in IHcl.
rewrite IHcl //= /seqmul.
apply/eqP.
rewrite eqn_add2r !mulrA (mulrC a) -(mulrA b) -expr2 (mulrC _ (a^+2)) -mulrA
   eq_sym.
by rewrite (@pmulr_rlt0 _ (a ^+2) (b * c)) // exprn_even_gt0.
Qed.

Section thm_3_cercles_partie1.
Local Open Scope complex_scope.

Variables (R : rcfType) (l r : R) (Hlr_le : l < r).

Local Notation C := (complex R).

Local Notation toC := (fun (p : {poly R}) => @map_poly R _ (real_complex R) p).

Lemma HlrC : l%:C != r%:C.
Proof. by rewrite -!complexr0 eq_complex /= negb_and lt_eqF. Qed.

Definition notinC (z : C) :=
  0 <= (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l.

Lemma notinC_Re_lt0_1 : forall (z : C), z != l%:C ->
  notinC z = (Re ((r%:C - z) / (z - l%:C)) <= 0).
Proof.
case => a b Hab.
rewrite /notinC /=.
simpc.
rewrite !mulrA -(mulNr (b * b) _) -mulrDl
  -expr2 (mulrDl r (-a) _) (mulrC r (a - l)) (mulrC (-a) _) (mulrDl _ _ r)
  (mulrDl _ _ (-a)) mulrNN mulrN -expr2 !addrA (addrC (a * r) _)
  -(addrA _ (a * r) _ ) (addrC (a * r) _ ) (mulrC a r) addrA
  (addrC (- l * r) _ ) -(addrA _ (r * a) (l * a)) -(mulrDl _ _ a)
  -(addrA (- a ^+2) _ _) (addrC (- l * r)) -!addrA (addrC _ (- b^+2))
  !addrA mulNr (mulrC l r) (addrC r l) -oppr_ge0 -[X in (_ = (0 <= X))]mulNr
  !opprD !opprK pmulr_lge0 //.
rewrite invr_gt0 lt_neqAle addr_ge0 ?sqr_ge0 // andbT eq_sym paddr_eq0 ?sqr_ge0 //
   negb_and !sqrf_eq0 subr_eq0.
by rewrite -complexr0 eq_complex negb_and /= in Hab.
Qed.

Lemma notinC_Re_lt0_2 (z : C) : z + 1 != 0 ->
   (notinC ((r%:C + l%:C * z) / (z + 1))) = (Re z <= 0).
Proof.
move=> Hz.
rewrite (@notinC_Re_lt0_1 ((r%:C + l%:C * z) / (z + 1))) /=.
  rewrite -{1}(@mulrK _ (z+1) _ r%:C); last by rewrite unitfE.
  rewrite -(mulNr (r%:C + l%:C * z) _ ) -(mulrDl _ _ (z+1)^-1) mulrDr mulr1
     opprD !addrA addrK -{3}(@mulrK _ (z+1) _ l%:C); last by rewrite unitfE.
  rewrite -(mulNr (l%:C * (z+1)) _ ) -(mulrDl _ _ (z+1)^-1) mulrDr mulr1
     opprD !addrA addrK invrM.
      rewrite invrK !mulrA -(mulrA _ _ (z+1)) (mulrC _ (z+1)) !mulrA mulrK;
          last by rewrite unitfE.
      rewrite -mulNr -mulrDl (mulrC _ z) mulrK //.
      by rewrite unitfE subr_eq0 eq_sym HlrC.
    by rewrite unitfE subr_eq0 eq_sym HlrC.
  by rewrite -unitrV invrK unitfE.
rewrite -subr_eq0 -{2}(@mulrK _ (z + 1) _ l%:C); last by rewrite unitfE.
rewrite -mulNr -mulrDl mulrDr mulr1 opprD addrA addrK mulf_neq0 //.
  by rewrite subr_eq add0r eq_sym HlrC.
by rewrite invr_eq0.
Qed.

(* Theorem 10.47 i. *)
Theorem three_circles_1 (p : {poly R}) :
   (forall (z : C), root (toC p) z -> (notinC z)) ->
   changes (Mobius' p l r) = 0%N.
Proof.
move=> H.
have [/eqP|Hp0] := eqVneq p 0.
  rewrite (@Mobius'0 _ p l r) ?lt_eqF// => /eqP ->.
  by rewrite polyseq0.
rewrite (@changes_mulC R (Mobius' p l r) (lead_coef (Mobius' p l r))^-1).
  apply: monic_roots_changes_eq0 => [ | z Hz].
    by rewrite monicE lead_coefZ mulrC -unitrE unitfE lead_coef_eq0
       -Mobius'0 ?lt_eqF// Hp0.
  case/altP : (z+1 =P 0) => [/eqP Hz2 | Hz2].
    rewrite addr_eq0 eq_complex in Hz2.
    move/andP : Hz2; case => /eqP Hrez _.
    by rewrite Hrez raddfN lerN10.
  rewrite map_polyZ rootZ /= -?root_Mobius'_C_2 // in Hz.
    rewrite -notinC_Re_lt0_2 //.
    apply: H => //.
  rewrite -complexr0 eq_complex /= negb_and eq_refl orbF.
  by rewrite invr_eq0 lead_coef_eq0 -Mobius'0 ?lt_eqF// negbT.
by rewrite invr_eq0 lead_coef_eq0 -Mobius'0 ?lt_eqF// negbT.
Qed.

End thm_3_cercles_partie1.

Section thm_3_cercles_partie2.
Variable R : rcfType.

Local Notation C := (complex R).

Definition inC1 := fun (l r : R) (z : C) =>
  (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 -
  (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0.

Definition inC2 := fun (l r : R) (z : C) =>
  (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 +
  (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0.

Definition inC12 := fun (l r : R) (z : C) =>
  ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 -
  (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0) ||
  ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 +
  (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0).

Lemma inC1_or_inC2 (l r : R) (z : C) :
  (inC1 l r z) || (inC2 l r z) = (inC12 l r z).
Proof. by []. Qed.

Definition inB1 (z : C) :=
  (Re z - 1 <= 0) && ((Im z)^+2 <= 3%:R * (Re z - 1) ^+2).

Lemma inB_inB1 : forall (z : C), inB z = inB1 (z + 1).
Proof.
case => a b.
by rewrite /inB1 /= addrK addr0 /inB.
Qed.

Lemma inB1_help : forall (z : C), (inB1 z) =
   (((Num.sqrt 3%:R) * (Re z - 1) - Im z <= 0) &&
     (0 <= - (Num.sqrt 3%:R * (Re z - 1)) - Im z)).
Proof.
case=> a b.
rewrite /inB1 /=.
case/altP : (a - 1 =P 0) => Ha.
  rewrite Ha /= mulr0 oppr0 add0r lexx/= (expr2 0) !mulr0.
  by rewrite -eq_le oppr_eq0 -sqrf_eq0 eq_le sqr_ge0 andbT.
rewrite -{1}(sqr_sqrtr (a:=3%:R)); last by apply: ler0n.
rewrite -exprMn -(ler_sqrt (b^+2)).
  rewrite !sqrtr_sqr normrM (ger0_norm (x := Num.sqrt 3%:R));
    last by apply: sqrtr_ge0.
  apply/idP/idP => /andP [] => H1 H2.
    rewrite -(normrN (a - 1)) (gtr0_norm (x:= - (a - 1))) in H2.
      by rewrite ler_norml mulrN opprK -subr_le0
         -[X in (_ && X)]subr_ge0 in H2.
    by rewrite oppr_gt0 lt_def H1 eq_sym Ha.
  have Hb : `|b| <= Num.sqrt 3%:R * -(a - 1).
    by rewrite ler_norml mulrN opprK -subr_le0 -[X in (_ && X)]subr_ge0 H1 H2.
  have Ha2 : (0 <= - (a - 1)).
    rewrite -(pmulr_lge0 (x:=Num.sqrt 3%:R)); last by rewrite sqrtr_gt0 ltr0n.
    by rewrite mulrC (@le_trans _ _ `| b |).
  by rewrite -oppr_ge0 Ha2 /= -(normrN (a-1)) (ger0_norm (x:= -(a-1))).
by rewrite exprMn mulr_ge0 // ?sqr_ge0//.
Qed.

Lemma Re_invc (z : C) : Re z^-1 = Re z / ((Re z) ^+ 2 + (Im z) ^+2).
Proof. by case: z. Qed.

Lemma Im_invc : forall (z : C), Im z^-1 = (- Im z) / ((Re z) ^+ 2 + (Im z) ^+2).
Proof. by case => a b; rewrite mulNr. Qed.

Lemma inB1_notinC1201 : forall (z : C), z != 0 -> inB1 z = ~~ inC12 0 1 (z ^-1).
Proof.
case=> a b Hz.
rewrite -inC1_or_inC2 negb_or inB1_help /=.
have H : a ^+ 2 + b ^+ 2 \is a GRing.unit.
  rewrite eq_complex /= negb_and in Hz.
  case/orP: Hz=> H;
    by rewrite unitfE paddr_eq0 ?sqr_ge0 // negb_and !sqrf_eq0 H ?orbT.
have H3 : (Num.ExtraDef.sqrtr (GRing.natmul (V:=R) (GRing.one R) (3)))
          \is a GRing.unit.
  by rewrite unitfE sqrtr_eq0 -ltNge ltr0n.
rewrite /inC1 /= -leNgt add0r oppr0 mul0r !addr0 !mul1r.
rewrite [x in (0 <= ((x + _) + _))]addrC -[x in (0 <= (x + _))]addrA
   exprMn -(mulNr b) exprMn sqrrN -mulrDl
   (expr2 ((a^+2 + b^+2)^-1)) -{2}(mulr1 (a^+2 + b^+2)) -invrM //
   -mulf_div [x in (0 <= _ + x + _)]mulrC !mulrA (mulrK (x:=(a^+2 + b^+2))) //.
rewrite -[in x in _ = x](mulNr a) -mulrDl.
rewrite -{5}(opprK 1) -(opprD a (- 1)) -mulrA -invrM //.
rewrite -[in x in _ = x]mulNr -(mul1r ( - (a - 1) / (a ^+ 2 + b ^+ 2)))
   -{5}(@mulrK _ (Num.sqrt 3%:R) _ 1) //.
rewrite mul1r mulf_div -mulrDl mulrN -[in x in (_ = x)]opprD.
rewrite /inC2 /= -leNgt add0r oppr0 mul0r !addr0 !mul1r.
rewrite [x in (0 <= ((x + _) + _))]addrC -[x in (0 <= (x + _))]addrA
   exprMn -(mulNr b) exprMn sqrrN -mulrDl
   (expr2 ((a^+2 + b^+2)^-1)) -{3}(mulr1 (a^+2 + b^+2)) -invrM //
   -mulf_div [x in (0 <= _ + x + _)]mulrC !mulrA (mulrK (x:=(a^+2 + b^+2))) //
   -[in x in (_ = _ && x)]mulNr -mulrDl -{8}(opprK 1) -(opprD a (- 1)) -mulrA
   -invrM //.
rewrite -(mul1r ( - (a - 1) / (a ^+ 2 + b ^+ 2)))
    -{8}(@mulrK _ (Num.sqrt 3%:R) _ 1) //.
rewrite mul1r mulf_div -mulrDl mulNr oppr_ge0 pmulr_lge0.
  rewrite pmulr_lle0 ?mulrN //.
  by rewrite invr_gt0 lt_def -unitfE unitrM H H3 /= mulr_ge0 // ?sqrtr_ge0 //
     addr_ge0 // sqr_ge0.
by rewrite invr_gt0 lt_def -unitfE unitrM H H3 /= mulr_ge0 // ?sqrtr_ge0 //
     addr_ge0 // sqr_ge0.
Qed.

Local Open Scope complex_scope.

Lemma notinC1201_lr_scale (l r : R) : forall (z : C), l != r ->
   ~~ inC12 0 1 z = ~~ inC12 0 (r - l) ((r - l)%:C * z).
Proof.
case=> a b Hlr.
rewrite !/inC12. simpc. rewrite /=.
rewrite !exprMn !(mulrA (r - l) _ a) !(mulrA (r - l) _ b)
   -expr2 -(mulrN _ a) -mulrA -(mulrN _ (b / Num.sqrt 3%:R))
    -!(mulrDr ((r - l)^+2)) !negb_or -!leNgt.
by rewrite !pmulr_rge0 // lt_def sqr_ge0 sqrf_eq0 subr_eq0 eq_sym Hlr.
Qed.

Lemma notinC12lr_shift (l r : R) : forall (z : C), l != r ->
  ~~ inC12 0 (r - l) z = ~~ inC12 l r (z + l%:C).
Proof.
case=> a b Hlr.
rewrite !/inC12. simpc. rewrite /= !negb_or -!leNgt.
by rewrite (expr2 (a+l)) (mulrDl a l) !mulrDr (mulrDl l r)
   (mulrDl l  r) -!expr2 !opprD
   [l * a + _]addrC !addrA addrK -(addrA _ (- (r * a)) _)
   (addrC (- (r * a)) _) !addrA addrK -(addrA _ (a * l) _)
   (addrC (a * l)) (mulrC a l) -{5 9}(opprK l) mulNr -opprD
   -mulrDl [X in (_ = (0 <= X) && _)]addrC [X in (_ = _ && (0 <= X))]addrC
   !addrA (addrC (l * r)) -(addrA _ (l * r) _)
   (addrC (l * r)) (mulrC l r) !addrA addrK.
Qed.

Lemma inB_notinC12 (l r : R) (z : C) : l != r -> z + 1 != 0 ->
  inB z = ~~ inC12 l r ((r%:C + l%:C * z) / (z + 1)).
Proof.
move=> Hlr Hz.
have H : (r%:C + l%:C * z) / (z + 1) = ((r - l)%:C / (z + 1) + l%:C).
  rewrite -{2}[l%:C](@mulrK _ (z + 1)); last by rewrite unitfE.
  by rewrite -mulrDl {2}[z+1]addrC mulrDr mulr1 rmorphB /= !addrA addrNK.
by rewrite H -notinC12lr_shift // -notinC1201_lr_scale //
   -inB1_notinC1201 // -inB_inB1.
Qed.

Lemma changes_nseq : forall (s : seq R) (a : R), a != 0 ->
  changes (seqmul (nseq (size s) a) s) = changes s.
Proof.
elim => [ | c l IHl a Ha] //.
case : l IHl => [IH |b l IHbl ] //.
  by rewrite /= !mulr0 addn0.
have -> : (changes [::c, b & l]) = ((c * b < 0)%R + changes [:: b & l])%N.
  by [].
rewrite -(IHbl a) //.
suff : ((a * c) * (a * b) < 0) = (c * b < 0) by move=> <-.
rewrite (mulrC a b) -mulrA (mulrC a) -!mulrA -expr2 mulrA.
by rewrite pmulr_llt0 // exprn_even_gt0.
Qed.

Lemma seqn0_nseq : forall (s : seq R) (a : R), a != 0 ->
  seqmul (nseq (size (seqn0 s)) a) (seqn0 s) =
  seqn0 (seqmul (nseq (size s) a) s).
Proof.
elim => [ | c l IHl a Ha] //.
case Hc : (c != 0).
  have Hac : a * c != 0 by apply: mulf_neq0.
  by rewrite seqmul_cons /= Hac /= Hc /= seqmul_cons /= -IHl.
have Hac : (a * c != 0) = false by rewrite mulf_eq0 negb_or Ha Hc.
by rewrite seqmul_cons /= Hc /= Hac /= IHl.
Qed.

Lemma inBneg1 : @inB R (-1).
Proof.
by rewrite /inB !raddfN lerN10 /= oppr0 sqrrN !expr2 mulr0 !mulr1 ler0n.
Qed.

Local Notation toC := (fun (p : {poly R}) => @map_poly R _ (real_complex R) p).

(* (~~ root p r) because of (~~ root (Mobius p l r) 0) *)
Theorem three_circles_2 (l r : R) (p : {poly R}) (a : R) :
  ~~ root p r -> l < a < r -> ~~ root p a ->
  (forall z : C, root (toC p) z -> ~~ inC12 l r z) ->
  changes (seqn0 (Mobius' (p * ('X - a%:P)) l r)) = 1%N.
Proof.
move=> Hpnorootr /andP [] Hal Har Hpnoroota H.
have Hlr : l != r by rewrite lt_eqF// (lt_trans Hal).
have Hal2 : l != a by rewrite negbT // lt_eqF.
have [Hp|Hp] := eqVneq p 0.
  have : false => //.
    by rewrite -(andbN (root p a)) Hpnoroota Hp root0.
have Hlc1 : (lead_coef (Mobius' (R:=R) (p * ('X - a%:P)) l r))^-1 != 0.
  rewrite invr_neq0 // Mobius'M lead_coefM mulf_neq0 //;
  rewrite lead_coef_eq0 -Mobius'0 // negbT //.
  exact: polyXsubC_eq0.
have Hl2 : lead_coef (Mobius' p l r) != 0 by rewrite lead_coef_eq0 -Mobius'0.
rewrite -(@changes_nseq _
   (lead_coef (Mobius' (p * ('X - a%:P)) l r)) ^-1) //
    seqn0_nseq // -mul_polyC_seqmul //.
rewrite Mobius'M lead_coefM -mul_polyC invrM ?unitfE; [ | by [] |]; last first.
  by rewrite lead_coef_eq0 -Mobius'0 // negbT // polyXsubC_eq0.
rewrite rmorphM /= mulrA mulrC !mulrA
     (mulrC (Mobius' ('X - a%:P) _ _) _)
     mul_polyC -mulrA mul_polyC mulrC
     [in X in (changes (R:=R) (seqn0 (polyseq (_ * X))))]
     (@Mobius'_Xsubc_monic R a l r Hlr Hal2)
     -(opprK ((r - a) / (l - a))%:P) -polyCN.
  apply: normal_changes.
    by rewrite oppr_gt0 pmulr_rlt0 ?invr_lt0 ?subr_lt0 // subr_gt0.
  apply: normal_root_inB => [ | z Hz].
    rewrite monicE lead_coef_lreg.
      by rewrite mulrC -unitrE unitfE.
    exact/lregP/invr_neq0.
  have [/eqP Hz2|Hz2] := eqVneq (z + 1) 0.
    rewrite addr_eq0 in Hz2.
    by rewrite (eqP Hz2) inBneg1.
  rewrite (inB_notinC12 Hlr) //.
  rewrite -mul_polyC rmorphM /= map_polyC mul_polyC rootZ in Hz.
  apply: H.
    by rewrite root_Mobius'_C_2.
  by rewrite /= eq_complex negb_and/= invr_neq0.
rewrite rootZ.
  rewrite -root_Mobius'_2; last by rewrite add0r oner_neq0.
  by rewrite mulr0 addr0 add0r invr1 mulr1.
exact: invr_neq0.
Qed.

End thm_3_cercles_partie2.
