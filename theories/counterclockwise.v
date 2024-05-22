Require Export axiomsKnuth.
From mathcomp Require Import all_ssreflect ssralg matrix ssrnum vector reals.
From mathcomp Require Import normedtype order lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                | 1 p_x p_y |                                               *)
(*   det p q r == | 1 q_x q_y |                                               *)
(*                | 1 r_x r_y |                                               *)
(*   ccw p q r := counterclockwise                                            *)
(*  wccw p q r := counterclockwise or aligned (0 <= det p q r)                *)
(******************************************************************************)

From mathcomp.algebra_tactics Require Import ring.
From mathcomp.zify Require Import zify.

Import GRing Num.Theory Order.POrderTheory Order.TotalTheory.

Local Open Scope order_scope.
Local Open Scope ring_scope.

Section Plane.
Variable R : realType.
Definition Plane : vectType _ := (R^o * R^o)%type.

(* ------------------ Definitions ------------------- *)

Definition xcoord (p : Plane) : R := p.1.
Definition ycoord (p : Plane) : R := p.2.

Definition get_coord (i : 'I_3) :=
  match val i with
  | 0 => xcoord
  | 1 => ycoord
  | _ => fun=> 1
  end.

Definition get_pt (p q r : Plane) := fun j : 'I_3 => nth 0 [:: p; q; r] j.

Let det_mx (p q r : Plane) :=
  \matrix_(i < 3, j < 3) get_coord i (get_pt p q r j).

Definition det (p q r : Plane) : R := \det (det_mx p q r).

Definition ccw (p q r : Plane) : bool := 0 < det p q r.

Definition wccw (p q r : Plane) := (0 <= det p q r)%R.

Lemma direct_distincts (p q r : Plane) : ccw p q r -> p <> q.
Proof.
move=> pqr pq; subst q; move: pqr; rewrite /ccw /det.
have n: (ord0: 'I_3) != lift ord0 ord0 by apply/eqP=>e; inversion e.
rewrite -det_tr (determinant_alternate n).
  by rewrite ltxx.
by move=>i; rewrite !mxE.
Qed.

Lemma det2 (R': comRingType) (M: 'M_2): (\det M: R') =
  M ord0 ord0 * M (lift ord0 ord0) (lift ord0 ord0) -
  M ord0 (lift ord0 ord0) * M (lift ord0 ord0) ord0.
Proof.
rewrite (expand_det_row M ord0) !big_ord_recl big_ord0 /cofactor !det_mx11.
rewrite !mxE/= /bump /= !(addn0,expr0,mul1r,add0n,addr0,expr1,mulN1r,mulrN)/=.
congr (_ - (_ * M _ _)).
exact: val_inj.
Qed.

Lemma develop_det (p q r: Plane): det p q r =
  xcoord r * (ycoord p - ycoord q) -
  ycoord r * (xcoord p - xcoord q) +
  xcoord p * ycoord q - ycoord p * xcoord q.
Proof.
rewrite /det (expand_det_col (det_mx p q r) (lift ord0 (lift ord0 (@ord0 0)))).
rewrite !big_ord_recl big_ord0 !mxE/= -!addrA; congr (_ * _ + _).
  by rewrite /cofactor !det2 !mxE /get_coord/get_pt /=; ring.
by rewrite -mulrN; congr (_ * _ + _);
  rewrite /cofactor !det2 !mxE /get_coord/get_pt /=; ring.
Qed.

(* ---------------- produit scalaire (avec le deuxième argument tourné de pi/2) ----------------- *)
Definition scalar_product (p q: Plane) := p.1 * q.1 + p.2 * q.2.

Definition rotate (p : Plane) := (p.2, -p.1).

Definition swap (p : Plane) := (p.2, p.1).

Lemma det_scalar_productE (p q r: Plane):
  det p q r = scalar_product (q-p) (rotate (r-p)).
Proof.
rewrite develop_det /scalar_product /=.
rewrite /xcoord /ycoord /=.
ring.
Qed.

Lemma scalar_productC (p q: Plane): scalar_product p q = scalar_product q p.
Proof. by rewrite /scalar_product /= [p.1*_]mulrC [p.2*_]mulrC. Qed.

Lemma scalar_productZL (q r: Plane) (t: R):
  scalar_product (t *: q) r = t * scalar_product q r.
Proof. by rewrite /scalar_product /= -!mulrA -mulrDr. Qed.

Lemma scalar_productZR (q r: Plane) (t: R):
  scalar_product q (t *: r) = t * scalar_product q r.
Proof. by rewrite scalar_productC scalar_productZL scalar_productC. Qed.

Lemma scalar_productDl (p q r: Plane):
  scalar_product (p + q) r = scalar_product p r + scalar_product q r.
Proof. by rewrite /scalar_product /=; ring. Qed.

Lemma scalar_productDr (p q r : Plane):
  scalar_product r (p + q) = scalar_product r p + scalar_product r q.
Proof. by rewrite scalar_productC scalar_productDl; congr add; apply scalar_productC. Qed.

Lemma scalar_productrr_ge0 p : 0 <= (scalar_product p p).
Proof. by rewrite /scalar_product; apply addr_ge0; apply sqr_ge0. Qed.

Lemma scalar_productrr_gt0 u : u != 0 -> 0 < scalar_product u u.
Proof.
move=>u0.
rewrite lt0r; apply/andP; split; last by apply scalar_productrr_ge0.
apply/negP; rewrite /scalar_product paddr_eq0.
   2, 3: by apply sqr_ge0.
rewrite 2!sqrf_eq0=>/andP[/eqP u10 /eqP u20].
by move: u0=>/negP; apply; rewrite -pair_eqE; apply/andP; split; apply/eqP.
Qed.

Lemma rotateZ (p : Plane) (t : R) : rotate (t *: p) = t *: rotate p.
Proof.
rewrite /rotate; apply pair_equal_spec; split=>//=.
by rewrite scalerN.
Qed.

Lemma rotateD (p q : Plane) : rotate (p + q) = rotate p + rotate q.
Proof.
rewrite /rotate; apply pair_equal_spec; split=>//=.
by rewrite opprD.
Qed.

Lemma rotate_rotate (p : Plane) : rotate (rotate p) = -p.
Proof. by case p=>a b; apply pair_equal_spec; split=>//. Qed.

Lemma rotate_antisym (p q : Plane) :
  scalar_product (rotate p) q = - scalar_product p (rotate q).
Proof. by rewrite /scalar_product/rotate/=; ring. Qed.

Lemma scalar_product_rotatexx (p : Plane) : scalar_product p (rotate p) = 0.
Proof. by rewrite /scalar_product/rotate/=; ring. Qed.

Lemma scalar_product_rotate (p q : Plane) :
  scalar_product (rotate p) (rotate q) = scalar_product p q.
Proof. by rewrite/scalar_product/rotate/=; ring. Qed.

Lemma swapD (p q : Plane) : swap (p+q) = swap p + swap q.
Proof. by apply pair_equal_spec. Qed.

Lemma swapZ (p : Plane) (t : R) : swap (t *: p) = t *: swap p.
Proof. by apply pair_equal_spec. Qed.

Lemma swapN (p : Plane) : swap (- p) = - swap p.
Proof. by rewrite -mulN1r swapZ scaleN1r. Qed.

Lemma swapB (p q : Plane) : swap (p-q) = swap p - swap q.
Proof. by rewrite swapD swapN. Qed.

Lemma swap_swap (p : Plane) : swap (swap p) = p.
Proof. by rewrite /swap/=; apply/esym; apply surjective_pairing. Qed.

Lemma swap_inj : injective swap.
Proof. by move=>p q /(f_equal swap); rewrite 2!swap_swap. Qed.

Lemma swap_sym (p q : Plane) :
  scalar_product (swap p) q = scalar_product p (swap q).
Proof. by rewrite/scalar_product/swap/=; ring. Qed.

Lemma scalar_product_swap (p q : Plane) :
  scalar_product (swap p) (swap q) = scalar_product p q.
Proof. by rewrite swap_sym swap_swap. Qed.

Lemma det_swap (p q r : Plane) : det (swap p) (swap q) (swap r) = - det p q r.
Proof. by rewrite 2!develop_det/swap/= /xcoord/ycoord/=; ring. Qed.

Lemma decompose_base (p q : Plane) : q != 0 ->
  p = (scalar_product p q) / (scalar_product q q) *: q +
    (scalar_product p (rotate q)) / (scalar_product q q) *: rotate q.
Proof.
move=>q0.
move: (scalar_productrr_gt0 q0)=>/lt0r_neq0 q0'.
(* Is there an injectivity lemma I could use here ? *)
move: (q0')=>/negPf q0''.
apply/eqP; rewrite -subr_eq0 -[_ == 0]/(false || _) -q0'' -scaler_eq0 scalerDr scalerN subr_eq0 /= scalerDr !scalerA !mulrA ![_ q q * _ p _]mulrC -!mulrA divff ?q0'// !mulr1 -pair_eqE /scalar_product.
apply/andP; split; apply/eqP=>/=; cbn; ring.
Qed.

(* ------------------ calcul de determinants ------------------- *)

Lemma decompose_det (p q r t : Plane) :
  det p q r = (det t q r) + (det p t r) + (det p q t).
Proof. by rewrite !develop_det; ring. Qed.

Lemma det_inverse (p q r : Plane) : det p q r = - (det p r q).
Proof. by rewrite !develop_det; ring. Qed.

Lemma det_cyclique (p q r : Plane) : det p q r = det q r p.
Proof. by rewrite !develop_det; ring. Qed.

Lemma detDl (p1 p2 p3 q1 q2 q3 r1 r2 r3 : R) :
  det (p1+p2, p3) (q1+q2, q3) (r1+r2, r3) =
  det (p1, p3) (q1, q3) (r1, r3) + det (p2, p3) (q2, q3) (r2, r3).
Proof. by rewrite !develop_det/=; ring. Qed.

Lemma detDr (p1 p2 p3 q1 q2 q3 r1 r2 r3 : R) :
  det (p1, p2+p3) (q1, q2+q3) (r1, r2+r3) =
  det (p1, p2) (q1, q2) (r1, r2) + det (p1, p3) (q1, q3) (r1, r3).
Proof. by rewrite !develop_det/=; ring. Qed.

Lemma detZl (p1 p2 q1 q2 r1 r2 t : R) :
  det (t * p1, p2) (t * q1, q2) (t * r1, r2) =
  t * det (p1, p2) (q1, q2) (r1, r2).
Proof. by rewrite !develop_det/=; ring. Qed.

Lemma detZr (p1 p2 q1 q2 r1 r2 t : R) :
  det (p1, t * p2) (q1, t * q2) (r1, t * r2) =
  t * det (p1, p2) (q1, q2) (r1, r2).
Proof. by rewrite !develop_det/=; ring. Qed.

Lemma det_alternate (p q : Plane) : det p p q = 0.
Proof.
apply/eqP; rewrite -[_ == 0]/(false || _) .
have<-: (2%:R : R) == 0 = false by rewrite pnatr_eq0.
by rewrite -mulf_eq0 mulr_natl 2!det_cyclique mulr2n {2}det_inverse subrr.
Qed.

Lemma det0_colinear (p q r : Plane) : det p q r = 0 <->
  exists (t : Plane), t != 0 /\ scalar_product t q = scalar_product t p /\
    scalar_product t r = scalar_product t p.
Proof.
rewrite det_scalar_productE; move: p q r.
suff: forall p q : Plane, scalar_product p (rotate q) = 0 <-> (exists (t : Plane), t != 0 /\ scalar_product t p = 0 /\ scalar_product t q = 0).
   move=>h p q r; move: h=> /(_ (q-p) (r-p)) ->; split.
      by move=>[t [t0 ts]]; exists t; split=>//; split; apply/eqP; rewrite -subr_eq0 -mulN1r -scalar_productZR -scalar_productDr scaleN1r; apply /eqP; apply ts; rewrite !in_cons eq_refl ?orbT.
   by move=>[t [t0 [qp rp]]]; exists t; split=>//; rewrite -scaleN1r 2!scalar_productDr scalar_productZR mulN1r qp rp subrr.
move=> p q; split.
   2: by move=>[t [t0 [p0 q0]]]; rewrite (decompose_base p t0) [_ p t]scalar_productC p0 mul0r scale0r add0r scalar_productZL scalar_product_rotate q0 mulr0.
move=>pq.
case p0: (p == 0).
   move: p0=>/eqP p0; subst p.
   case q0: (q == 0).
      move: q0=>/eqP q0; subst q.
      exists (1, 0); split.
         by rewrite negb_and; apply/orP; left=>/=; apply: oner_neq0.
      by rewrite -(scale0r (0 : Plane)) scalar_productZR mul0r.
   exists (rotate q); split.
      apply/eqP=>/pair_equal_spec [q2 /eqP]; rewrite oppr_eq0=>/eqP q1.
      by move: q0; rewrite -pair_eqE/pair_eq q1 q2 eq_refl.
   by rewrite scalar_productC [_ _ q]scalar_productC scalar_product_rotatexx.
exists (rotate p); split.
   apply/eqP=>/pair_equal_spec [p2 /eqP]; rewrite oppr_eq0=>/eqP p1.
   by move: p0; rewrite -pair_eqE/pair_eq p1 p2 eq_refl.
split.
   by rewrite scalar_productC scalar_product_rotatexx.
by rewrite rotate_antisym pq oppr0.
Qed.

Lemma direct_uniq p q r : ccw p q r -> uniq [:: p; q; r].
Proof.
move=>pqr.
apply/andP; split.
   2: by rewrite in_cons 2!in_nil orbF 2!andbT; apply/eqP; apply (@direct_distincts q r p); rewrite /ccw 2!det_cyclique.
rewrite negb_or orbF; apply/andP; split.
   by apply/eqP; exact (direct_distincts pqr).
by rewrite eq_sym; apply/eqP; apply (@direct_distincts r p q); rewrite /ccw det_cyclique.
Qed.

Lemma convex_combination p q r s t :
  det t q r * det t s p +
  det t r p * det t s q + det t p q * det t s r =
  0.
Proof. by rewrite !develop_det; ring. Qed.



(***** Misc *)
Local Open Scope order_scope.
Import Order.
Lemma subr_gtlex0 (p q : Plane) : ((0%:R : R *l R) < q-p) = ((p : R *l R) < q).
Proof.
rewrite/lt/=/ProdLexiOrder.lt; congr (_ && (_ ==> _)).
- by rewrite subr_ge0.
- by rewrite subr_le0.
- by rewrite subr_gt0.
Qed.

End Plane.

Module ccw_KA <: KnuthAxioms.
Section Dummy.
Variable (R : realType).
Definition Plane := Plane R.
Definition OT := ccw (R:=R).

Theorem Axiom1 (p q r : Plane) : OT p q r -> OT q r p.
Proof.
congr (_ < _).
rewrite !develop_det; ring.
Qed.

Theorem Axiom2 (p q r : Plane) : OT p q r -> ~ OT p r q.
Proof.
rewrite /OT /ccw lt0r=>/andP [_ pqr].
rewrite det_inverse oppr_gt0.
by rewrite ltNge pqr.
Qed.

Theorem Axiom4 (p q r t : Plane) :
 OT t q r -> OT p t r -> OT p q t -> OT p q r.
Proof.
rewrite /OT /ccw (decompose_det p q r t)=> tqr ptr pqt.
apply addr_gt0=>//.
apply addr_gt0=>//.
Qed.

Theorem Axiom5 t s p q r :
 OT t s p ->
 OT t s q ->
 OT t s r -> OT t p q -> OT t q r -> OT t p r.
Proof.
rewrite /OT /ccw => tsp tsq tsr tpq tqr.
have->: det t p r = - det t r p by rewrite !develop_det; ring.
rewrite ltNge oppr_le0; apply /negP=>trp.
suff: 0 < det t q r * det t s p + det t r p * det t s q + det t p q * det t s r.
  by rewrite convex_combination ltxx.
rewrite addrC.
apply ltr_wpDr; [| by apply mulr_gt0].
by apply addr_ge0; apply mulr_ge0=>//; apply ltW.
Qed.

Local Open Scope order_scope.
Import Order.

Theorem Axiom5' (pivot p q r : Plane) :
  (pivot : R *l R) < p ->
  (pivot : R *l R) < q ->
  (pivot : R *l R) < r ->
  ccw pivot p q ->
  ccw pivot q r ->
  ccw pivot p r.
Proof.
rewrite /ccw 3!det_scalar_productE/scalar_product/= !mulrN !subr_gt0 -![(pivot : R *l R) < _]subr_gtlex0 {1 2 3}/lt/=/ProdLexiOrder.lt/= !implybE -!ltNge !le_eqVlt ![(_==_)||_]orbC -!Bool.orb_andb_distrib_r=>/orP; case=>p0.
   move=>/orP; case=>q0.
      move=>/orP; case=>r0.
         rewrite -(ltr_pdivrMl _ _ p0) mulrA -(ltr_pdivlMr _ _ q0) [_^-1*_]mulrC -(ltr_pdivrMl _ _ q0) mulrA -(ltr_pdivlMr _ _ r0) [_^-1*_]mulrC -(ltr_pdivrMl _ _ p0) mulrA -(ltr_pdivlMr _ _ r0) [_^-1*_]mulrC=>qlt rlt; exact (lt_trans qlt rlt).
      move:r0=>/andP[/eqP<- r0].
      by rewrite 2!mulr0 pmulr_rgt0// pmulr_rgt0//.
   move:q0=>/andP[/eqP<- q0]/orP; case.
      move=>r0 _; rewrite mul0r pmulr_rlt0// =>r0'.
      by move: (lt_trans r0 r0'); rewrite ltxx.
   by move=>/andP[/eqP<- _] _; rewrite mul0r mulr0 ltxx.
move:p0=>/andP[/eqP<- p0].
rewrite 2!mul0r pmulr_rlt0// pmulr_rlt0// =>/orP; case.
   by move=>q0 _ q0'; move:(lt_trans q0 q0'); rewrite ltxx.
by move=>/andP[/eqP<- q0]; rewrite ltxx.
Qed.

End Dummy.
End ccw_KA.

(*Lemma Axiom5bis :
 forall t s p q r : Plane,
 OT s t p ->
 OT s t q ->
 OT s t r -> OT t p q -> OT t q r -> OT t p r.
Proof.
move=> t s p q r; rewrite /OT/sensDirect -![det s t _]det_cyclique ![det _ s t]det_inverse ![det _ t s]det_cyclique !oppr_gt0=>tsp tsq tsr tpq tqr.
rewrite det_inverse oppr_gt0 -(nmulr_lgt0 _ tsq).
have ->: det t r p * det t s q = - (det t q r * det t s p + det t p q * det t s r) by rewrite !develop_det; ring.
by rewrite opprD; apply addr_gt0; rewrite oppr_gt0 nmulr_llt0.
   Qed.*)
