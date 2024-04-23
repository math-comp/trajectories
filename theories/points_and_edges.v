From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements.
Require Import generic_trajectories.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_context.

Variable (R : realFieldType).

Definition pt := pt R.
Notation Bpt := (Bpt R).
Notation p_x := (generic_trajectories.p_x R).
Notation p_y := (generic_trajectories.p_y R).

Lemma pt_eqP : Equality.axiom (pt_eqb R eq_op).
Proof.
rewrite /Equality.axiom.
move=> [a_x a_y] [b_x b_y]; rewrite /pt_eqb/=.
have [/eqP <-|/eqP anb] := boolP(a_x == b_x).
  have [/eqP <- | /eqP anb] := boolP(a_y == b_y).
    by apply: ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

HB.instance Definition _ := hasDecEq.Build _ pt_eqP.

Lemma pt_eqE (p1 p2 : pt) :
   (p1 == p2) = (p_x p1 == p_x p2) && (p_y p1 == p_y p2).
Proof. by move: p1 p2 => [? ?][? ?]. Qed.

Record edge := Bedge {left_pt : pt; right_pt : pt;
    _ : p_x left_pt < p_x right_pt}.

Definition edge_eqb (e1 e2 : edge) : bool :=
   let: Bedge a1 b1 p1 := e1 in
   let: Bedge a2 b2 p2 := e2 in
   (a1 == a2) && (b1 == b2).

Lemma edge_cond (e : edge) : p_x (left_pt e) < p_x (right_pt e).
Proof.  by move: e => [l r c]. Qed.

Lemma edge_eqP : Equality.axiom edge_eqb.
Proof.
move=> [a1 b1 p1] [a2 b2 p2] /=.
have [/eqP a1a2 | /eqP a1na2] := boolP(a1 == a2).
  have [/eqP b1b2 | /eqP b1nb2] := boolP(b1 == b2).
     move: p1 p2. rewrite -a1a2 -b1b2 => p1 p2.
     rewrite (eqtype.bool_irrelevance p1 p2).
     by apply: ReflectT.
   by apply: ReflectF=> [][].
by apply: ReflectF=>[][].
Qed.

HB.instance Definition _ := hasDecEq.Build _ edge_eqP.

Definition area3 :=
  area3 R +%R (fun x y => x - y) *%R.

(* returns true if p is under e *)
Definition point_under_edge :=
  point_under_edge R le +%R (fun x y => x - y) *%R 1 edge
  left_pt right_pt.

Definition point_strictly_under_edge :=
  point_strictly_under_edge R eq_op le +%R (fun x y => x - y) *%R 1 edge
  left_pt right_pt.

Lemma R_ltb_lt  x y : R_ltb R eq_op le x y = (x < y).
Proof. by rewrite /R_ltb -lt_neqAle. Qed.

Lemma strictE p e :
  generic_trajectories.point_strictly_under_edge R eq_op le +%R
    (fun x y => x - y) *%R 1 edge left_pt right_pt p e =
  (area3 p (left_pt e) (right_pt e) < 0).
Proof.
by rewrite /generic_trajectories.point_strictly_under_edge R_ltb_lt subrr.
Qed.

Lemma underE p e :
  generic_trajectories.point_under_edge R le +%R
    (fun x y => x - y) *%R 1 edge left_pt right_pt p e =
  (area3 p (left_pt e) (right_pt e) <= 0).
Proof. by rewrite /generic_trajectories.point_under_edge subrr. Qed.

Notation "p '<<=' e" := (point_under_edge p e)( at level 70, no associativity).
Notation "p '<<<' e" := (point_strictly_under_edge p e)(at level 70, no associativity).

Notation "p '>>=' e" := (~~(point_strictly_under_edge p e))( at level 70, no associativity).
Notation "p '>>>' e" := (~~(point_under_edge p e))(at level 70, no associativity).

Section ring_sandbox.

Definition R' := (R : Type).

Let mul : R' -> R' -> R' := @GRing.mul _.
Let add : R' -> R' -> R' := @GRing.add _.
Let sub : R' -> R' -> R' := (fun x y => x - y).
Let opp : R' -> R' := @GRing.opp _.
Let zero : R' := 0.
Let one : R' := 1.


Let R2_theory :=
   @mk_rt R' zero one add mul sub opp
    (@eq R')
    (@add0r R) (@addrC R) (@addrA R) (@mul1r R) (@mulrC R)
      (@mulrA R) (@mulrDl R) (fun x y : R' => erefl (x - y)) (@addrN R).

Add Ring R2_Ring : R2_theory.

Ltac mc_ring :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
    -?[@GRing.mul _]/mul
    -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
ring.

Let inv : R' -> R' := @GRing.inv _.
Let div : R' -> R' -> R' := fun x y => mul x (inv y).

Definition R2_sft : field_theory zero one add mul sub opp div inv (@eq R').
Proof.
constructor.
- exact R2_theory.
- have // : one <> zero by apply/eqP; rewrite oner_eq0.
- have // : forall p q : R', div p q = mul p (inv q) by [].
- have // : forall p : R', p <> zero -> mul (inv p) p = one.
  by move=> *; apply/mulVf/eqP.
Qed.

Add Field Qfield : R2_sft.

Ltac mc_field :=
rewrite ?mxE /= ?(expr0, exprS, mulrS, mulr0n) -?[@GRing.add _]/add
    -?[@GRing.mul _]/mul -[@GRing.inv _]/inv
    -?[@GRing.opp _]/opp -?[1]/one -?[0]/zero;
match goal with |- @eq ?X _ _ => change X with R' end;
field.

Example field_playground (x y : R' ) : x != 0 -> y != 0 -> (x * y) / (x * y) = 1.
Proof.
move=> xn0 yn0; mc_field.
by split; apply/eqP.
Qed.

(* returns true if p is under A B *)
Definition pue_f (a_x a_y b_x b_y c_x c_y : R')  : R' :=
     b_x * c_y + a_x * b_y + c_x * a_y -
    b_x * a_y - a_x * c_y - c_x * b_y.

Lemma pue_f_o p_x p_y a_x a_y b_x b_y:  pue_f p_x p_y a_x a_y b_x b_y = - pue_f b_x b_y a_x a_y p_x p_y.
Proof.
  rewrite /pue_f.
  mc_ring.
Qed.

Lemma pue_f_c p_x p_y a_x a_y b_x b_y:  pue_f p_x p_y a_x a_y b_x b_y =  pue_f b_x b_y p_x p_y a_x a_y.
Proof.
  rewrite /pue_f.
  mc_ring.
Qed.

Lemma pue_f_inter p_x  a_x a_y b_x b_y :  b_x != a_x -> (pue_f p_x ((p_x - a_x)* ((b_y - a_y)/(b_x - a_x)) + a_y) a_x a_y b_x b_y) == 0.
Proof.
rewrite /pue_f.
rewrite -subr_eq0 => h.
set slope := (_ / _).

rewrite (mulrDr b_x).
rewrite (mulrDr a_x).
rewrite -(orbF (_==0)).
rewrite -(negbTE   h).
rewrite -mulf_eq0 .
rewrite ! ( mulrBl (b_x - a_x), fun x y => mulrDl  x y (b_x - a_x)).

rewrite /slope !mulrA !mulfVK //.
apply/eqP; mc_ring.
Qed.

Lemma pue_f_inters p_x p_y a_x a_y b_x b_y  :  b_x != a_x -> p_y = ((p_x - a_x) * ((b_y - a_y) / (b_x - a_x)) + a_y) ->
pue_f p_x p_y a_x a_y b_x b_y == 0.
Proof.
move => h ->.
by apply pue_f_inter; rewrite h.


Qed.

Lemma pue_f_eq p_x p_y a_x a_y :
pue_f p_x p_y p_x p_y a_x a_y == 0.
Proof.
rewrite /pue_f /=.

apply /eqP.
mc_ring.
Qed.

Lemma pue_f_two_points p_x p_y a_x a_y :
pue_f p_x p_y p_x p_y a_x a_y == 0 /\ pue_f p_x p_y a_x a_y p_x p_y == 0 /\
pue_f p_x p_y a_x a_y a_x a_y == 0.
Proof.
split.
apply pue_f_eq.
split.
have := pue_f_c p_x p_y  a_x a_y p_x p_y.
move => ->.
apply pue_f_eq.
have := pue_f_c  a_x a_y  a_x a_y p_x p_y.
move => <-.
apply pue_f_eq.
Qed.

Lemma pue_f_vert p_y a_x a_y b_x b_y :
 (pue_f a_x a_y b_x b_y b_x p_y) == (b_x - a_x) * (p_y - b_y).
Proof.
rewrite /pue_f.
apply /eqP.
mc_ring.
Qed.

Lemma ax4 p_x p_y q_x q_y r_x r_y t_x t_y :
pue_f t_x t_y q_x q_y r_x r_y + pue_f p_x p_y t_x t_y r_x r_y
+ pue_f p_x p_y q_x q_y t_x t_y == pue_f p_x p_y q_x q_y r_x r_y.
Proof.
rewrite /pue_f.
apply /eqP.
  mc_ring.
Qed.

Lemma pue_f_linear l a b c d e f :
l * pue_f a b c d e f = pue_f a (l*b) c (l*d) e (l*f).
Proof.
rewrite /pue_f.
mc_ring.
Qed.

Lemma pue_f_on_edge_y a_x a_y b_x b_y m_x m_y :
pue_f m_x m_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * m_y = m_x * (b_y -a_y)- (a_x * b_y - b_x *a_y).
Proof.
move => /eqP abmeq0.
apply /eqP.
rewrite -subr_eq0.
apply /eqP.
rewrite -abmeq0 /pue_f.
mc_ring.
Qed.

Lemma pue_f_on_edge a_x a_y b_x b_y c_x c_y d_x d_y m_x m_y :
pue_f m_x m_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * pue_f m_x m_y c_x c_y d_x d_y ==
(m_x - a_x) * pue_f b_x b_y c_x c_y d_x d_y + (b_x - m_x) * pue_f a_x a_y c_x c_y d_x d_y.
Proof.
move => on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f p'_x p'_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * pue_f p'_x p'_y a_x a_y p_x p_y ==
(p'_x - a_x) * pue_f b_x b_y a_x a_y p_x p_y .
Proof.
move=> on_ed.
rewrite pue_f_linear  /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_triangle_on_edge' a_x a_y b_x b_y p_x p_y p'_x p'_y :
pue_f p'_x p'_y a_x a_y b_x b_y == 0 ->
(b_x - a_x) * pue_f p'_x p'_y p_x p_y b_x b_y ==
(b_x - p'_x) * pue_f a_x a_y p_x p_y b_x b_y .
Proof.
move => on_ed .
rewrite pue_f_linear /pue_f (pue_f_on_edge_y on_ed).
apply /eqP.
mc_ring.
Qed.

Lemma pue_f_on_edge_same_point a_x a_y b_x b_y p_x p_y p_x' p_y':
a_x != b_x ->
pue_f p_x p_y a_x a_y b_x b_y == 0 ->
pue_f p_x' p_y' a_x a_y b_x b_y == 0 ->
(p_x == p_x') -> (p_y == p_y').
Proof.
move => axnbx puep0 puep'0.
have pyeq := (pue_f_on_edge_y puep0 ).
have p'yeq := (pue_f_on_edge_y puep'0 ).
move=> xxs; have yys : (b_x - a_x) * p_y = (b_x - a_x) * p_y'.
  by rewrite pyeq (eqP xxs) p'yeq.
move: (axnbx); rewrite eq_sym -subr_eq0=> bxmax.
apply/eqP.
by apply: (mulfI bxmax).
Qed.

Lemma pue_f_ax5 p_x p_y q_x q_y a_x a_y b_x b_y c_x c_y :
  pue_f p_x p_y a_x a_y b_x b_y *
  pue_f p_x p_y q_x q_y c_x c_y +
  pue_f p_x p_y b_x b_y c_x c_y *
  pue_f p_x p_y q_x q_y a_x a_y =
  pue_f p_x p_y a_x a_y c_x c_y *
  pue_f p_x p_y q_x q_y b_x b_y.
Proof.
rewrite /pue_f; mc_ring.
Qed.

Lemma pue_f_triangle_decompose a_x a_y b_x b_y c_x c_y d_x d_y :
  pue_f a_x a_y c_x c_y d_x d_y = 0 ->
  pue_f a_x a_y b_x b_y c_x c_y =
  pue_f a_x a_y b_x b_y d_x d_y +
  pue_f b_x b_y c_x c_y d_x d_y.
Proof.
move=> online.
rewrite -(eqP (ax4 _ _ _ _ _ _ d_x d_y)).
rewrite addrC; congr (_ + _).
by rewrite addrC pue_f_o pue_f_c online oppr0 add0r -pue_f_c.
Qed.

Definition mkmx2 (a b c d : R) :=
  \matrix_(i < 2, j < 2)
    if (i == ord0) && (j == ord0) then a
    else if i == ord0 then b
           else if j == ord0 then c else d.

Definition mkcv2 (a b : R) := \col_(i < 2) if i == ord0 then a else b.

Lemma det_mkmx2 a_x a_y b_x b_y :
  \det(mkmx2 a_x a_y b_x b_y) = a_x * b_y - a_y * b_x.
Proof.
rewrite /mkmx2 (expand_det_row _ ord0) big_ord_recr /= big_ord1 /=.
by rewrite /cofactor /= expr0 expr1 mulNr !mul1r !det_mx11 !mxE /= mulrN.
Qed.

Lemma line_intersection a_x a_y b_x b_y c_x c_y d_x d_y :
  c_x != d_x ->
  0 < pue_f c_x c_y a_x a_y b_x b_y ->
  pue_f d_x d_y a_x a_y b_x b_y < 0 ->
  exists p_x p_y,
    pue_f p_x p_y a_x a_y b_x b_y = 0 /\
    pue_f p_x p_y c_x c_y d_x d_y = 0 /\
    (forall q_x q_y, pue_f q_x q_y a_x a_y b_x b_y = 0 ->
       pue_f q_x q_y c_x c_y d_x d_y = 0 -> p_x = q_x /\ p_y = q_y).
Proof.
move=> cltd cabove cunder.
set A := a_y - b_y; set B := b_x - a_x; set C := \det(mkmx2 a_x a_y b_x b_y).
have puef1_id x y : pue_f x y a_x a_y b_x b_y = A * x + B * y + C.
  by rewrite /A /B /C det_mkmx2 /pue_f; mc_ring.
set D := c_y - d_y; set E := d_x - c_x; set F := \det(mkmx2 c_x c_y d_x d_y).
have puef2_id x y : pue_f x y c_x c_y d_x d_y = D * x + E * y + F.
  by rewrite /D /E /F det_mkmx2 /pue_f; mc_ring.
set M := mkmx2 A B D E.
set V1 := mkcv2 (b_x - a_x) (b_y - a_y).
set V2 := mkcv2 (d_x - c_x) (d_y - c_y).
have sys_to_mx_eqn :
  forall x y, (A * x + B * y + C = 0 /\ D * x + E * y + F = 0) <->
   (M *m mkcv2 x y + mkcv2 C F = 0).
  move=> x y; split.
    move=> [eq1 eq2]; apply/matrixP=> i j.
    rewrite !mxE big_ord_recr /= big_ord1 /= !mxE.
    by case : j => [ [ | j ] ] //= _; case : i => [ [ | [ | i]]].
  move/matrixP=> mxq.
  split.
    have := mxq (Ordinal (isT : (0 < 2)%N)) (Ordinal (isT : (0 < 1)%N)).
    by rewrite !mxE big_ord_recr /= big_ord1 /= !mxE.
  have := mxq (Ordinal (isT : (1 < 2)%N)) (Ordinal (isT : (0 < 1)%N)).
  by rewrite !mxE big_ord_recr /= big_ord1 /= !mxE.
set sol := - (M ^-1 *m mkcv2 C F) : 'cV_2.
have soleq : sol = mkcv2 (sol ord0 ord0) (sol ord_max ord0).
  apply/matrixP=> [][[ | [ | i]]] // ip [ [ | j]] // jp; rewrite /= !mxE /=;
    (rewrite (_ : Ordinal jp = ord0); last apply: val_inj=> //).
    by rewrite (_ : Ordinal ip = ord0); last apply: val_inj.
  by rewrite (_ : Ordinal ip = ord_max); last apply: val_inj.
have detm : \det M != 0.
  have dets : \det M = A * E - D * B.
    rewrite (expand_det_col _ ord0) big_ord_recr /= big_ord1 !mxE /= /cofactor.
    by rewrite !det_mx11 /= expr1 expr0 !mulNr !mulrN !mul1r !mxE.
  have -> : \det M = pue_f d_x d_y a_x a_y b_x b_y -
                  pue_f c_x c_y a_x a_y b_x b_y.
    by rewrite dets /pue_f /A /B /D /E; mc_ring.
  rewrite subr_eq0; apply/eqP=> abs; move: cabove cunder; rewrite abs=> ca cu.
  by have := lt_trans ca cu; rewrite ltxx.
have Munit : M \in unitmx by rewrite unitmxE unitfE.
have solm : M *m sol + mkcv2 C F = 0.
  rewrite /sol mulmxN mulmxA mulmxV; last by rewrite unitmxE unitfE.
  by rewrite mul1mx addNr.
move: (solm); rewrite soleq -sys_to_mx_eqn => [][sol1 sol2].
exists (sol ord0 ord0), (sol ord_max ord0).
split; first by rewrite puef1_id.
split; first by rewrite puef2_id.
move=> qx qy; rewrite puef1_id puef2_id=> tmp1 tmp2; have := conj tmp1 tmp2.
rewrite sys_to_mx_eqn addrC => /addr0_eq solmq {tmp1 tmp2}.
suff/matrixP mq : mkcv2 qx qy = sol.
  by split; rewrite -?(mq ord0 ord0) -?(mq ord_max ord0) mxE.
by rewrite /sol -mulmxN solmq mulKmx.
Qed.

Lemma pue_f_eq_slopes ax ay bx b_y mx my :
  pue_f mx my ax ay bx b_y =
   (my - ay) * (bx - ax) - (mx - ax) * (b_y - ay) /\
  pue_f mx my ax ay bx b_y =
   -((b_y - my) * (bx - ax) - (bx - mx) * (b_y - ay)).
Proof.
split; rewrite /pue_f; mc_ring.
Qed.

Lemma edge_and_left_vertical_f px py qx qy ax ay :
  px < ax -> px = qx ->
  (0 < pue_f px py qx qy ax ay) = (qy < py).
Proof.
move=> edge_cond <-.
rewrite [X in (0 < X)](_ : _ = (ax - px) * (py - qy)); last first.
  by rewrite /pue_f; mc_ring.
by rewrite pmulr_rgt0 subr_gt0.
Qed.

Lemma edge_and_right_vertical_f px py qx qy ax ay :
  ax < px -> px = qx -> (0 < pue_f px py qx qy ax ay) = (py < qy).
Proof.
move=> edge_cond <-.
rewrite [X in (0 < X)](_ : _ = (px - ax) * (qy - py)); last first.
  by rewrite /pue_f; mc_ring.
by rewrite pmulr_rgt0 subr_gt0.
Qed.

End ring_sandbox.

Lemma area3E a b c : area3 a b c =
   pue_f (p_x a) (p_y a) (p_x b) (p_y b) (p_x c) (p_y c).
Proof. by case: a b c=> [a_x a_y] [b_x b_y] [c_x c_y]. Qed.

Lemma area3_opposite a b d:  area3 d a b = - area3 b a d.
Proof.
  move: a b d => [ax ay] [b_x b_y] [dx dy]/=.
  apply :pue_f_o.
Qed.

Lemma area3_cycle a b d : area3 d a b = area3 b d a.
Proof.
  move: a b d => [ax ay] [b_x b_y] [dx dy]/=.
  apply :pue_f_c.
Qed.

Lemma area3_vert a b c : (p_x b = p_x c) ->
area3 a b c == (p_x b - p_x a) * (p_y c - p_y b).
Proof.
move: a b c => [ax ay] [b_x b_y] [cx cy]/= <-.
apply : pue_f_vert.
Qed.

Lemma ax4_three_triangles p q r t :
area3 t q r + area3 p t r + area3 p q t
== area3 p q r.
Proof.
move : p q r t => [px py] [q_x q_y] [rx ry] [t_x t_y]/= .
apply : ax4.
Qed.


Lemma area3_two_points a b :
area3 a a b == 0 /\ area3 a b a == 0 /\
area3 a b b == 0.
Proof.
move : a b => [ax ay] [b_x b_y] /=.
apply pue_f_two_points.
Qed.

Lemma area3_on_edge a b c d m :
area3 m a b == 0 ->
(p_x b - p_x a) * area3 m c d ==
(p_x m - p_x a) * area3 b c d + (p_x b - p_x m) * area3 a c d.
Proof.
move : a b c d m => [ax ay] [b_x b_y] [cx cy] [dx dy] [mx my]/=.
apply pue_f_on_edge.
Qed.

Lemma area3_on_edge_y a b m :
area3 m a b == 0 ->
(p_x b - p_x a) * p_y m = p_x m * (p_y b - p_y a) - (p_x a * p_y b - p_x b * p_y a).
Proof.
move : a b m => [ax ay] [b_x b_y]  [mx my]/=.
apply pue_f_on_edge_y.
Qed.

Lemma area3_triangle_on_edge a b p p' :
area3 p' a b == 0 ->
(p_x b - p_x a) * area3 p' a p ==
(p_x p' - p_x a) * area3 b a p.
Proof.
move : a b p p' => [ax ay] [b_x b_y] [px py] [p'x p'y] /=.
apply pue_f_triangle_on_edge.
Qed.

Definition subpoint (p : pt) :=
  Bpt (p_x p) (p_y p - 1).

Lemma edge_and_left_vertical (p q a : pt) :
  p_x p < p_x a -> p_x p = p_x q ->
  (0 < area3 p q a) = (p_y q < p_y p).
Proof.
case: p=> [px py]; case: a=> [ax ay]; case: q=> [qx qy] /=.
by move=> c1 c2; apply edge_and_left_vertical_f.
Qed.

Lemma edge_and_left_vertical_eq (p q a : pt) :
  p_x p < p_x a -> p_x p = p_x q ->
  (area3 p q a == 0) = (p == q).
Proof.
move=> edge_cond vert_cond.
apply/idP/idP; last first.
  by move/eqP ->; rewrite (area3_two_points q a).1.
move=> abs; suff : p_y p = p_y q.
  by move: vert_cond {edge_cond abs}; case: p=> [? ?]; case q=> [? ?]/= <- <-.
apply: le_anti. rewrite (leNgt (p_y p) (p_y q)).
rewrite -(edge_and_left_vertical edge_cond vert_cond) (eqP abs).
have ec' : p_x q < p_x a by rewrite -vert_cond.
rewrite leNgt -(edge_and_left_vertical ec' (esym vert_cond)).
by rewrite area3_opposite -area3_cycle (eqP abs) oppr0 ltxx.
Qed.

Lemma edge_and_right_vertical (p q a : pt) :
  p_x a < p_x p -> p_x p = p_x q ->
  (0 < area3 p q a) = (p_y p < p_y q).
Proof.
case: p=> [px py]; case: a=> [ax ay]; case: q=> [qx qy] /=.
by move=> c1 c2; apply: edge_and_right_vertical_f.
Qed.

Lemma point_sub_right (p a : pt) :
  (p_x p < p_x a) -> 0 < area3 p (subpoint p) a.
Proof.
move=> edge_cond.
rewrite edge_and_left_vertical //; rewrite /subpoint /= lterBDr cprD.
by rewrite ltr01.
Qed.

Lemma underW p e :
  (p <<< e) ->
  (p <<= e).
Proof.
move=> /andP[] _ it; exact: it.
Qed.

Lemma underWC p e :
~~ (p <<= e) -> ~~ (p <<< e).
Proof. by move/negP=> it; apply/negP=> it'; case: it; apply : underW. Qed.

Definition valid_edge :=
  generic_trajectories.valid_edge R le edge left_pt right_pt.

Lemma valid_edge_extremities e0 p:
(left_pt e0 == p) || (right_pt e0 == p) ->
valid_edge e0 p.
Proof.
rewrite /valid_edge/generic_trajectories.valid_edge.
by move => /orP [/eqP eq |/eqP eq ];
rewrite -eq lexx ?andbT /= {eq} ltW // ; case : e0 .
Qed.

Lemma valid_edge_left g : valid_edge g (left_pt g).
Proof.
by apply: valid_edge_extremities; rewrite eqxx.
Qed.

Lemma valid_edge_right g : valid_edge g (right_pt g).
Proof.
by apply: valid_edge_extremities; rewrite eqxx orbT.
Qed.

Definition point_on_edge (p: pt) (e :edge) : bool :=
  (area3 p (left_pt e) (right_pt e) == 0) && (valid_edge e p).

Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
((left_pt e1 <<= e2) && (right_pt e1 <<= e2))
|| (~~  (left_pt e2 <<< e1) && ~~ (right_pt e2<<< e1)).

Notation "e1 '<|' e2" := (edge_below e1 e2)( at level 70, no associativity).

Definition below_alt (e1 : edge) (e2 : edge) :=
  edge_below e1 e2 \/ edge_below e2 e1.

Lemma edge_below_refl e : e <| e.
Proof.
apply/orP; left.
rewrite /point_under_edge 2!underE.
rewrite (eqP (proj1 (area3_two_points _ _))).
by rewrite (eqP (proj1 (proj2 (area3_two_points _ _)))) lexx.
Qed.

Lemma below_altC e1 e2 : below_alt e1 e2 <-> below_alt e2 e1.
Proof. by rewrite /below_alt or_comm. Qed.

Lemma below_altN e1 e2 : below_alt e1 e2 -> ~~(e2 <| e1) -> e1 <| e2.
Proof. by move=> []// ->. Qed.

Definition inter_at_ext (e1 e2 : edge) :=
  e1 = e2 \/
  forall p, p === e1 -> p === e2 -> p \in [:: left_pt e1; right_pt e1].

Definition inter_at_ext' (e1 e2 : edge) :=
  e1 = e2 \/
  forall p, p === e2 -> p === e1 -> p \in [:: left_pt e2; right_pt e2].

Lemma inter_at_ext_sym (s : seq edge) :
  {in s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s &, forall e1 e2, inter_at_ext' e1 e2}.
Proof.
move=> cnd e1 e2 e1in e2in; case: (cnd e2 e1 e2in e1in).
  by move=> ->; left.
by move=> subcnd; right=> p pe2 pe1; apply: subcnd.
Qed.

Definition no_crossing := forall e1 e2, below_alt e1 e2.

Definition no_crossing'  : Prop:=
 forall e e' : edge,
 valid_edge e (left_pt e') ->
(left_pt e' <<< e  -> e' <| e)  /\
(~ (left_pt e' <<= e)  -> e <| e').

Lemma left_on_edge e :
(left_pt e) === e.
Proof.
move : e => [ l r inE].
rewrite /point_on_edge //=.
have := area3_two_points l r.
move => [] ->  _ /=.
apply  /andP .
split.
  by [].
rewrite /=.
by apply ltW.
Qed.

Lemma right_on_edge e :
(right_pt e) === e.
Proof.
move : e => [ l r inE].
rewrite /point_on_edge //=.
have := area3_two_points r l.
move => [] _ [] -> _ /=.
apply  /andP .
split.
  rewrite /=.
  by apply ltW.
by [].
Qed.

Lemma point_on_edge_above low_e high_e a :
a === high_e ->
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
~~ (a <<< low_e).
Proof.
move : high_e => [lr hr inH] /=.
rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.
have pf := area3_on_edge (left_pt low_e) (right_pt low_e) poea.
rewrite /point_strictly_under_edge.
rewrite /generic_trajectories.point_strictly_under_edge subrr.
rewrite !R_ltb_lt -!leNgt => llrllh llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -(ler_nM2l difflh _ 0) mulr0 -opprB mulNr oppr_le0 (eqP pf).
by rewrite addr_ge0 // mulr_ge0 // subr_ge0.
Qed.

Lemma point_on_edge_above_strict low_e high_e a :
a === high_e ->
(left_pt high_e >>> low_e) ->
(right_pt high_e >>> low_e) ->
(a >>> low_e).
Proof.
move : high_e => [lr hr inH] /=.
rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.
have pf := area3_on_edge (left_pt low_e) (right_pt low_e) poea.
rewrite /point_under_edge -!ltNge !subrr => llrllh llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -(ltr_nM2l difflh _ 0) mulr0 -opprB mulNr oppr_lt0 (eqP pf).
have addr_le_gt0 (x y : R) : 0 <= x -> 0 < y -> 0 < x + y.
  move=> xge0 ygt0; rewrite -(add0r 0).
  by apply: ler_ltD.
move: diffa; rewrite le_eqVlt=> /orP[ | diffa]; last first.
  rewrite addrC addr_le_gt0 // ?mulr_gt0 ?mulr_ge0 //.
    by rewrite ltW.
  by rewrite subr_gt0 -subr_lt0.
rewrite subr_eq0=> /eqP /[dup] lraq <-; rewrite subrr mul0r add0r.
by rewrite mulr_gt0 // subr_gt0.
Qed.

Lemma point_on_edge_under low_e high_e a :
a === (low_e) ->
 (left_pt low_e) <<= high_e ->
 (right_pt low_e) <<= high_e ->
  a <<= high_e.
Proof.
move : low_e => [lr hr inH] /=.
rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.
have pf := area3_on_edge (left_pt high_e) (right_pt high_e) poea.
rewrite /point_under_edge /generic_trajectories.point_under_edge !subrr=> llrllh llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -(ler_nM2r difflh 0 _) mul0r mulrC -opprB mulNr (eqP pf) opprD.
by rewrite addr_ge0 // -mulNr mulr_le0 // oppr_le0 subr_cp0.
Qed.

Lemma point_on_edge_under_strict high_e low_e a :
a === low_e ->
(left_pt low_e <<< high_e) ->
(right_pt low_e <<< high_e) ->
(a <<< high_e).
Proof.
move : low_e => [lr hr inH] /=.
rewrite /point_on_edge /valid_edge => /andP [] /= poea /andP [] linfa ainfr.
have pf := area3_on_edge (left_pt high_e) (right_pt high_e) poea.
rewrite /point_strictly_under_edge.
rewrite/generic_trajectories.point_strictly_under_edge.
rewrite !R_ltb_lt !subrr=> llrllh llrllrh.
have diffa : (p_x lr - p_x a) <= 0.
  by rewrite subr_cp0.
have diffb : (p_x hr - p_x a) >= 0.
  by rewrite subr_cp0.
have difflh : (p_x lr - p_x hr) < 0.
  by rewrite subr_cp0.
rewrite -(ltr_nM2l difflh 0) mulr0 -opprB mulNr oppr_gt0 (eqP pf).
have addr_le_lt0 (x y : R) : x <= 0 -> y < 0 -> x + y < 0.
  move=> xle0 ylt0; rewrite -(add0r 0).
  by apply: ler_ltD.
move: diffa; rewrite le_eqVlt=> /orP[ | diffa]; last first.
  rewrite addrC addr_le_lt0 // ?nmulr_llt0 ?mulr_ge0_le0 //.
      by rewrite ltW.
  by rewrite subr_gt0 -subr_lt0.
rewrite subr_eq0=> /eqP /[dup] lraq <-; rewrite subrr mul0r add0r.
by rewrite nmulr_llt0 // subr_gt0.
Qed.

Lemma not_strictly_above' low_e high_e p':
~~ (left_pt (high_e) <<< low_e) ->
~~ (right_pt (high_e) <<< low_e) ->
p' ===  high_e ->  p_x (right_pt (low_e)) = p_x p'  ->
right_pt (low_e) <<= high_e .
Proof.
move : low_e => [ll lr inL] /=.
move => pablh pabrh poep' eqxp'p.
have /= /eqP puefcpp' := area3_vert (left_pt (Bedge inL)) eqxp'p .
have := (point_on_edge_above poep' pablh pabrh ).
rewrite /point_strictly_under_edge strictE.
rewrite -area3_cycle -leNgt puefcpp' /point_under_edge underE.
have inle: (p_x lr - p_x ll) >0.
  by rewrite subr_cp0.
rewrite (pmulr_rge0 _ inle) => inp'lr.
have :=  (ax4_three_triangles lr  (left_pt high_e) (right_pt high_e) p') => /eqP <-.
move : poep'.
rewrite /point_on_edge=> /andP [] /eqP pue0 valp'.
rewrite pue0.
have := (area3_vert (right_pt high_e) eqxp'p  ).
rewrite -area3_cycle eqxp'p => /eqP ->.
move : valp'.
rewrite /valid_edge => /andP [] xlhp' xrhp'.
have xrhp'0: p_x p' - p_x (right_pt high_e) <=0.
  by rewrite subr_cp0.
rewrite add0r.
rewrite -oppr_ge0 opprD /= addr_ge0//.
  by rewrite -mulNr mulr_ge0 // oppr_ge0.
have := (area3_vert (left_pt high_e) eqxp'p  ).
rewrite -area3_opposite area3_cycle eqxp'p => /eqP ->.
have xlhp'0: p_x p' - p_x (left_pt high_e) >= 0.
  by rewrite subr_cp0.
by rewrite  mulr_ge0.
Qed.

Lemma under_above_on e p :
  valid_edge e p -> p <<= e -> p >>= e -> p === e.
Proof.
move=> v u a; apply/andP; split => //.
apply/eqP/le_anti/andP;split.
  by move: u; rewrite /point_under_edge/generic_trajectories.point_under_edge!subrr.
move: a; rewrite /point_strictly_under_edge.
rewrite /generic_trajectories.point_strictly_under_edge subrr.
by rewrite R_ltb_lt leNgt=> it; exact: it.
Qed.

(* returns the point of the intersection between a vertical edge
 intersecting p and the edge e if it exists, None if it doesn't *)

Definition vertical_intersection_point (p : pt) (e : edge) : option pt :=
  vertical_intersection_point R le +%R (fun x y => x - y) *%R
    (fun x y => x / y) edge left_pt right_pt p e.

Lemma vertical_none p e :
  ~~ valid_edge e p -> vertical_intersection_point p e = None.
Proof.
move: p e => [px py] [[ax ay] [b_x b_y] ab] h /=.
rewrite /vertical_intersection_point.
rewrite /generic_trajectories.vertical_intersection_point /=.
by rewrite /valid_edge in h; rewrite (negbTE h).
Qed.


Lemma vertical_correct p e :
    match (vertical_intersection_point p e) with
  None => ~~ valid_edge e p | Some(i) => i === e end.
Proof.
move: p e => [ptx pty] [[ax ay] [bx b_y]  /=ab] .
rewrite /vertical_intersection_point/valid_edge.
rewrite /generic_trajectories.vertical_intersection_point.
case : ifP => /= h ; last first.
by [].
have: ax != bx.
rewrite neq_lt ab //=.
rewrite /area3.
set py := ((b_y - ay) / (bx - ax) * ptx + (ay - (b_y - ay) / (bx - ax) * ax)).
move => h2.
rewrite /point_on_edge .
apply /andP.
split; last first.
exact h.
apply pue_f_inters.
by apply /eqP /nesym /eqP .
by [].
Qed.



Lemma exists_point_valid e p :
(valid_edge e p) ->
exists p', vertical_intersection_point p e = Some (p').
Proof.
have := vertical_correct p e.
case : (vertical_intersection_point p e)=> [vp |//=].
  rewrite /point_on_edge.
  move => a b.
  by exists vp.
move => a b.
exists p.
by rewrite b in a.
Qed.

Lemma intersection_on_edge e p p' :
vertical_intersection_point p e = Some (p') ->
p'=== e /\ p_x p = p_x p'.
Proof.
have := vertical_correct p e.
case vert : (vertical_intersection_point p e)=> [vp |//=].
move: vert.
rewrite /vertical_intersection_point.
rewrite /generic_trajectories.vertical_intersection_point.
case : (generic_trajectories.valid_edge _ _ _ _ _ e p) => [| //].
move => [] /= vpq  poe [].
move => <-.
by rewrite poe -vpq /=.
Qed.

Lemma not_strictly_under' low_e high_e p' :
(left_pt (low_e)) <<= (high_e) ->
(right_pt (low_e))<<= (high_e) ->
(* This is an alternative way to say
  valid_edge low_e (right_pt high_e) *)
p' === low_e ->  p_x (right_pt (high_e)) = p_x p'  ->
~~ (right_pt (high_e) <<< low_e).
Proof.
move : high_e => [hl hr inH] /=.
move => pablh pabrh poep' eqxp'p.
have /= /eqP puefcpp' := area3_vert (left_pt (Bedge inH)) eqxp'p .
have := (point_on_edge_under poep' pablh pabrh ).
rewrite /point_under_edge/point_strictly_under_edge underE strictE.
rewrite -area3_cycle.
rewrite -leNgt puefcpp'.
have inle: (p_x hr - p_x hl) >0.
  by rewrite subr_cp0.
rewrite (pmulr_rle0 _ inle )  => inp'hr.
have :=  (ax4_three_triangles hr  (left_pt low_e) (right_pt low_e) p') => /eqP <-.
move : poep'.
rewrite /point_on_edge=> /andP [] /eqP pue0 valp'.
rewrite pue0.
have := (area3_vert (right_pt low_e) eqxp'p  ).
rewrite -area3_cycle eqxp'p => /eqP ->.
move : valp'.
rewrite /valid_edge => /andP [] xlhp' xrhp'.
have xrhp'0: p_x p' - p_x (right_pt low_e) <=0.
  by rewrite subr_cp0.
rewrite add0r addr_ge0//.
  by rewrite mulr_le0.
have := (area3_vert (left_pt low_e) eqxp'p  ).
rewrite area3_opposite -area3_cycle eqxp'p eqr_oppLR => /eqP ->.
by rewrite -mulNr mulr_le0 // oppr_le0 subr_cp0.
Qed.

Lemma pue_right_edge e p :
p_x (right_pt e) == p_x p ->
(p <<= e) = ((p_y p - p_y (right_pt e)) <= 0).
Proof.
move : e p  => [[ax ay][bx b_y] /= inE] [px py]  /=.
rewrite /point_under_edge/generic_trajectories.point_under_edge /=.
move => /eqP <- /=.
have := (pue_f_vert py ax ay bx b_y).
rewrite pue_f_c /pue_f.
move => /eqP ->.
rewrite -subr_cp0 -opprB oppr_lt0 in inE.
by rewrite subrr (pmulr_rle0 _  inE) .
Qed.

Lemma psue_right_edge e p :
p_x (right_pt e) == p_x p ->
(p <<< e) = ((p_y p - p_y (right_pt e)) < 0).
Proof.
move : e p  => [[ax ay][bx b_y] /= cnd] [px py]  /=.
rewrite /point_strictly_under_edge/generic_trajectories.point_strictly_under_edge /=.
rewrite R_ltb_lt.
move => /eqP <- /=.
have := (pue_f_vert py ax ay bx b_y).
rewrite pue_f_c /pue_f.
move => /eqP ->.
rewrite -subr_gt0 in cnd.
by rewrite subrr (pmulr_rlt0 _  cnd) .
Qed.

Lemma pue_left_edge e p :
p_x (left_pt e) == p_x p ->
(p <<= e) = (0 <= (p_y (left_pt e) - p_y p )).
Proof.
move : e p  => [[ax ay][bx b_y] /= inE] [px py]  /=.
rewrite /point_under_edge.
rewrite /generic_trajectories.point_under_edge /=.
move => /eqP <- /=.
have := (pue_f_vert ay bx b_y ax py).
rewrite -pue_f_c /pue_f.
move => /eqP ->.
rewrite -subr_cp0 in inE.
by rewrite subrr (nmulr_rle0 _  inE).
Qed.

Lemma psue_left_edge e p :
p_x (left_pt e) == p_x p ->
(p <<< e) = (0 < p_y (left_pt e) - p_y p).
Proof.
move: e p => [[ax ay][bx b_y] /= cnd] [px py] /=.
move=> /eqP <- /=.
rewrite /point_strictly_under_edge.
rewrite /generic_trajectories.point_strictly_under_edge /=.
rewrite R_ltb_lt.
have := (pue_f_vert ay bx b_y ax py).
rewrite -pue_f_c /pue_f => /eqP ->.
rewrite -subr_cp0 in cnd.
by rewrite subrr (nmulr_rlt0 _ cnd).
Qed.

Lemma not_strictly_under low_e high_e  :
(left_pt low_e) <<= high_e ->
(right_pt low_e) <<= high_e ->
valid_edge low_e (right_pt high_e)  ->
~~ (right_pt high_e <<< low_e).
Proof.
move => pableft pabright valright.
have  := exists_point_valid valright.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx.
apply :  not_strictly_under' pableft pabright poep' eqx.
Qed.

Lemma not_strictly_above low_e high_e :
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
valid_edge (high_e) (right_pt (low_e)) ->
right_pt (low_e) <<= high_e.
Proof.
move => pableft pabright valright.
have  := exists_point_valid valright.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx.
apply :  not_strictly_above' pableft pabright poep' eqx.
Qed.

Lemma on_edge_same_point e p p':
p === e -> p' === e ->
(p_x p == p_x p') -> (p_y p == p_y p').
Proof.
move : e => [l r ec].
rewrite /point_on_edge /= => /andP [] p0 _ /andP[] p'0 _.
have dif : p_x l != p_x r.
  by apply/eqP=> abs; move: ec; rewrite abs ltxx.
move: l r p0 p'0 dif {ec}=> [a_x a_y][b_x b_y] p0 p'0 dif.
move: p p' p0 p'0 => [x y] [x' y'] puep0 puep'0.
rewrite /=; apply: (pue_f_on_edge_same_point dif puep0 puep'0).
Qed.

Lemma strict_under_edge_lower_y r r' e :
  p_x r = p_x r' -> r' === e -> (r <<< e) = (p_y r < p_y r').
Proof.
move=> rr' rone.
have valre : valid_edge e r.
  by case/andP: rone; rewrite /valid_edge/generic_trajectories.valid_edge rr'.
move: (valre)=> /andP[] + _; rewrite le_eqVlt=> /orP[/eqP atl| inr].
  have req : r' = left_pt e.
    have rltr : p_x r' < p_x (right_pt e) by rewrite -rr' -atl edge_cond.
    have /esym := edge_and_left_vertical_eq rltr (esym (etrans atl rr')).
    by move/andP: rone => [] -> _ /eqP.
  by move/eqP/psue_left_edge: atl; rewrite subr_gt0 -req.
have rue' : (r <<< e) = (area3 r (left_pt e) r' < 0).
  move: rone=> /andP[] /[dup] tmp/area3_triangle_on_edge + _ => /(_ r).
(* TODO : fix area3_triangle_on_edge for cycle *)
  rewrite (area3_opposite (left_pt _)).
  rewrite (area3_opposite (left_pt _) _ (right_pt _)) !mulrN.
  rewrite inj_eq; last by apply: oppr_inj.
  move/eqP => signcond.
  move: (edge_cond e); rewrite -subr_gt0 => /pmulr_rlt0 <-.
  rewrite signcond pmulr_rlt0; last by rewrite subr_gt0 -rr'.
    rewrite /point_strictly_under_edge.
    by rewrite /generic_trajectories.point_strictly_under_edge subrr R_ltb_lt.
have inr' : p_x (left_pt e) < p_x r' by rewrite -rr'.
have /psue_right_edge : p_x (right_pt (Bedge inr')) == p_x r.
  by rewrite /= rr' eqxx.
rewrite rue' subr_lt0.
rewrite /point_strictly_under_edge.
by rewrite /generic_trajectories.point_strictly_under_edge subrr R_ltb_lt.
Qed.

Lemma under_onVstrict e p :
  valid_edge e p ->
  (p <<= e) = (p === e) || (p <<< e).
Proof.
move=> valep.
rewrite /point_under_edge /point_strictly_under_edge /point_on_edge.
rewrite /generic_trajectories.point_strictly_under_edge R_ltb_lt.
rewrite /generic_trajectories.point_under_edge subrr.
by rewrite le_eqVlt valep andbT.
Qed.

Lemma onAbove e p : p === e -> ~~ (p <<< e).
Proof.
rewrite /point_on_edge /point_strictly_under_edge.
rewrite /generic_trajectories.point_strictly_under_edge R_ltb_lt subrr.
move=> /andP[cmp valep].
by rewrite -leNgt le_eqVlt eq_sym cmp.
Qed.

Lemma strict_nonAunder e p :
  valid_edge e p ->
  (p <<< e) = (~~ (p === e)) && (p <<= e).
Proof.
move=> valep.
rewrite /point_strictly_under_edge /point_on_edge /point_under_edge.
rewrite /generic_trajectories.point_strictly_under_edge R_ltb_lt.
rewrite /generic_trajectories.point_under_edge !subrr.
by rewrite valep andbT lt_neqAle.
Qed.

Lemma under_edge_strict_lower_y (r r' : pt) e :
  p_x r = p_x r' -> r != r' -> r <<= e -> r' === e -> p_y r < p_y r'.
Proof.
move=> xs nq under on'.
have  vr : valid_edge e r.
  by move: on'; rewrite /valid_edge/generic_trajectories.valid_edge xs=> /andP[].
move: under; rewrite (under_onVstrict vr)=> /orP[on | ].
  by case/negP: nq; rewrite pt_eqE (on_edge_same_point on on') xs eqxx.
by rewrite (strict_under_edge_lower_y xs).
Qed.

Lemma above_edge_strict_higher_y (r r' : pt)  e :
  p_x r = p_x r' -> r != r' -> r >>= e -> r' === e -> p_y r' < p_y r.
Proof.
move=> xs nq above on'.
have  vr : valid_edge e r.
  by move: on'; rewrite /valid_edge/generic_trajectories.valid_edge xs=> /andP[].
move: above; rewrite (strict_under_edge_lower_y xs on') // -leNgt le_eqVlt.
move/orP=> [/eqP ys | //].
by case/negP: nq; rewrite pt_eqE xs ys !eqxx.
Qed.

Lemma under_edge_lower_y r r' e :
  p_x r = p_x r' -> r' === e -> (r <<= e) = (p_y r <= p_y r').
Proof.
move=> rr' rone.
have valre : valid_edge e r.
  by case/andP: rone; rewrite /valid_edge/generic_trajectories.valid_edge rr'.
move: (valre)=> /andP[] + _; rewrite le_eqVlt=> /orP[/eqP atl| inr].
  have req : r' = left_pt e.
    have rltr : p_x r' < p_x (right_pt e) by rewrite -rr' -atl edge_cond.
    have /esym := edge_and_left_vertical_eq rltr (esym (etrans atl rr')).
    by move/andP: rone => [] -> _ /eqP.
  by move/eqP/pue_left_edge: atl; rewrite subr_ge0 -req.
have rue' : (r <<= e) = (area3 r (left_pt e) r' <= 0).
  move: rone=> /andP[] /[dup] tmp/area3_triangle_on_edge + _ => /(_ r).
(* TODO : fix area3_triangle_on_edge for cycle *)
  rewrite (area3_opposite (left_pt _)).
  rewrite (area3_opposite (left_pt _) _ (right_pt _)) !mulrN.
  rewrite inj_eq; last by apply: oppr_inj.
  move/eqP => signcond.
  move: (edge_cond e); rewrite -subr_gt0 => /pmulr_rle0 <-.
  rewrite /point_under_edge/generic_trajectories.point_under_edge subrr.
  by rewrite signcond pmulr_rle0; last rewrite subr_gt0 -rr'.
have inr' : p_x (left_pt e) < p_x r' by rewrite -rr'.
rewrite /point_under_edge/generic_trajectories.point_under_edge subrr.
have /pue_right_edge : p_x (right_pt (Bedge inr')) == p_x r.
  by rewrite /= rr' eqxx.
move: rue'.
rewrite /point_under_edge/generic_trajectories.point_under_edge subrr=> rue'.
by rewrite rue' subr_le0.
Qed.

Lemma aligned_trans a a' b p : p_x a != p_x b ->
  area3 a' a b == 0 ->
  area3 p a b == 0 -> area3 p a' b == 0.
Proof.
rewrite -area3_cycle.
move=> bna /[dup]/area3_triangle_on_edge proc a'ab pab.
have/mulfI/inj_eq <-  : p_x a - p_x b != 0 by rewrite subr_eq0.
rewrite -area3_cycle -(eqP (proc _)).
by rewrite area3_cycle (eqP pab) !mulr0.
Qed.

Lemma area3_change_ext a b a' b' p :
  p_x a < p_x b -> p_x a' < p_x b' ->
  area3 a' a b == 0 -> area3 b' a b == 0 ->
  sg (area3 p a b) = sg (area3 p a' b').
Proof.
move=> altb altb' ona onb.
have/area3_triangle_on_edge:= ona => /(_ p)/eqP ona'.
have/area3_triangle_on_edge:= onb => /(_ p)/eqP onb0.
have/area3_triangle_on_edge: area3 b' a' a == 0.
  have bna : p_x b != p_x a by case: ltrgtP altb.
  by rewrite (aligned_trans bna) //
       area3_opposite oppr_eq0 area3_cycle.
move=>/(_ p)/eqP onb'.
have difab : 0 < p_x b - p_x a by rewrite subr_gt0.
have difab' : 0 < p_x b' - p_x a' by rewrite subr_gt0.
have [ | | aa' ] := ltrgtP (p_x a) (p_x a'); last first.
- set w := Bedge altb.
  have/on_edge_same_point tmp : a === Bedge altb by exact: left_on_edge.
  have/(tmp _) : a' === Bedge altb.
    rewrite /point_on_edge ona /valid_edge/generic_trajectories.valid_edge.
    by rewrite /= -aa' lexx ltW.
  rewrite aa'=> /(_ (eqxx _))/eqP ays.
  have aa : a = a' by move: (a) (a') aa' ays=> [? ?][? ?] /= -> ->.
  rewrite -aa area3_opposite [in RHS]area3_opposite.
  rewrite -[RHS]mul1r -(gtr0_sg difab) -sgrM mulrN onb0 [X in _ - X]aa' -mulrN.
  by rewrite sgrM (gtr0_sg difab') mul1r.
- rewrite -subr_gt0=> xalta'; rewrite -[RHS]mul1r -(gtr0_sg xalta') -sgrM.
  rewrite [in RHS]area3_opposite mulrN onb' -mulrN sgrM (gtr0_sg difab').
  rewrite -area3_opposite -[in RHS]area3_cycle.
  rewrite -(gtr0_sg difab) -sgrM ona' [in RHS]area3_opposite.
  by rewrite mulrN -mulNr opprB sgrM (gtr0_sg xalta') mul1r.
rewrite -subr_lt0=> xa'lta; apply/esym. 
rewrite area3_opposite -[X in -X]mul1r -mulNr sgrM sgrN1.
rewrite -(ltr0_sg xa'lta) -sgrM onb' sgrM (gtr0_sg difab').
rewrite area3_opposite -area3_cycle sgrN mulrN -(gtr0_sg difab).
rewrite -sgrM ona' -sgrN -mulNr opprB sgrM (ltr0_sg xa'lta).
by rewrite area3_opposite sgrN mulrN mulNr opprK mul1r.
Qed.

Lemma under_low_imp_under_high low_e high_e p  :
(left_pt low_e) <<= high_e ->
(right_pt low_e) <<= high_e ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<= low_e -> p <<= high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  /=.
move => pulh purh vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge
  /generic_trajectories.valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -area3_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => puep.

have ydiff : p_y p <= p_y p'.
  by rewrite -(under_edge_lower_y eqx' poep').

rewrite eqx' in eqx''.
have puep' := (point_on_edge_under  poep' pulh purh).
have y'diff : p_y p' <= p_y p''.
  by rewrite -(under_edge_lower_y eqx'' poep'').
have y''diff: (p_y p  <= p_y p'').
  by rewrite (le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (area3_vert hl eqx'').
have /eqP pHreq :=  (area3_vert hr eqx'').
rewrite -area3_cycle in pHreq.
rewrite area3_opposite -area3_cycle in pHleq.

move : poepf'' pHreq => /eqP ->  -> .
have :  area3 p hl p'' = - ((p_x p - p_x hl) * (p_y p'' - p_y p)).
  by rewrite -pHleq opprK.
move => ->.
rewrite add0r -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_under_edge /= {pulh purh vallow valhigh poep' poep'' poepf' puep puep'}.
rewrite underE.
rewrite addrC.
have inH' := inH.
rewrite -subr_cp0 in inH'.
rewrite -subr_ge0 in y''diff.
move => /eqP <-.
by rewrite nmulr_rle0.
Qed.

Lemma under_low_imp_strict_under_high low_e high_e p  :
(left_pt low_e) <<= high_e ->
(right_pt low_e) <<= high_e ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<< low_e -> p <<< high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  /=.
move => pulh purh vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -area3_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => puep.

have ydiff : p_y p < p_y p'.
  by rewrite -(strict_under_edge_lower_y eqx' poep').

rewrite eqx' in eqx''.
have puep' := (point_on_edge_under  poep' pulh purh).
have y'diff : p_y p' <= p_y p''.
  by rewrite -(under_edge_lower_y eqx'' poep'').
have y''diff: (p_y p  < p_y p'').
  by rewrite (lt_le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (area3_vert hl eqx'').
have /eqP pHreq :=  (area3_vert hr eqx'').
rewrite -area3_cycle in pHreq.
rewrite area3_opposite -area3_cycle in pHleq.

move : poepf'' pHreq => /eqP ->  -> .
have :  area3 p hl p'' = - ((p_x p - p_x hl) * (p_y p'' - p_y p)).
  by rewrite -pHleq opprK.
move => ->.
rewrite add0r -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_strictly_under_edge /= {pulh purh vallow valhigh poep' poep'' poepf' puep puep'}.
rewrite addrC.
have inH' := inH.
rewrite -subr_cp0 in inH'.
rewrite -subr_gt0 in y''diff.
rewrite strictE.
move => /eqP <-.
by rewrite nmulr_rlt0.
Qed.

Lemma under_low_imp_under_high_bis low_e high_e p  :
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<= low_e -> p <<= high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  .
move => pabhl pabhr vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -area3_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => /= puep.

have ydiff : p_y p <= p_y p'.
  by rewrite -(under_edge_lower_y eqx' poep').
rewrite eqx' in eqx''.
symmetry in eqx''.
have pabp' := (point_on_edge_above  poep'' pabhl pabhr).
have y'diff : p_y p' <= p_y p''.
  by rewrite leNgt -(strict_under_edge_lower_y eqx'' poep').
have y''diff: (p_y p  <= p_y p'').
  by rewrite (le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (area3_vert hl eqx'').
have /eqP pHreq :=  (area3_vert hr eqx'').

rewrite area3_opposite in pHreq.
rewrite area3_cycle in pHleq.

move : poepf'' pHleq => /eqP  ->  -> .
have :  area3 p p'' hr = - ((p_x p'' - p_x hr) * (p_y p - p_y p'')).
  by rewrite -pHreq opprK.
move => ->.
rewrite add0r addrC -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_under_edge /= {pabhl pabhr vallow valhigh poep' poep'' poepf' puep pabp'}.
rewrite addrC.
have inH' := inH.
rewrite -subr_gte0 in inH'.
rewrite -subr_le0 in y''diff.
rewrite underE.
move => /eqP <-.
by rewrite pmulr_rle0.
Qed.

Lemma under_low_imp_strict_under_high_bis low_e high_e p  :
~~ (left_pt high_e <<< low_e) ->
~~ (right_pt high_e <<< low_e) ->
valid_edge low_e p ->
valid_edge high_e p ->
p <<< low_e -> p <<< high_e.
Proof.
move : low_e high_e => [ll lr inL] [hl hr inH]  .
move => pabhl pabhr vallow valhigh.
have  := exists_point_valid vallow.
move => [] p' vip .
have  := intersection_on_edge vip => [][] poep' eqx'.
have  := exists_point_valid valhigh.
move => [] p'' vip' .
have  := intersection_on_edge vip' => [][] poep'' eqx''{vip' vip}.
have := poep''.
have := poep'.

rewrite /point_on_edge /valid_edge =>  /andP [] /= poepf' /andP []
 linfp' p'infr   /andP [] /= poepf'' /andP [] linfp'' p''infr.

rewrite -area3_cycle in poepf'.
rewrite -eqx' in linfp' p'infr.
rewrite -eqx'' in linfp'' p''infr.
move => /= puep.

have ydiff : p_y p < p_y p'.
  by rewrite -(strict_under_edge_lower_y eqx' poep').

rewrite eqx' in eqx''.
symmetry in eqx''.
have pabp' := (point_on_edge_above  poep'' pabhl pabhr).
have y'diff : p_y p' <= p_y p''
   by rewrite leNgt -(strict_under_edge_lower_y eqx'' poep').
have y''diff: (p_y p  < p_y p'').
  by rewrite (lt_le_trans  ydiff y'diff).
rewrite -eqx' in eqx''.
have := ax4_three_triangles p hl hr p''.
have /eqP pHleq :=  (area3_vert hl eqx'').
have /eqP pHreq :=  (area3_vert hr eqx'').

rewrite area3_opposite in pHreq.
rewrite area3_cycle in pHleq.

move : poepf'' pHleq => /eqP  ->  -> .
have :  area3 p p'' hr = - ((p_x p'' - p_x hr) * (p_y p - p_y p'')).
  by rewrite -pHreq opprK.
move => ->.
rewrite add0r addrC -mulrBl.
rewrite  [x in (x - _) * _ == _] addrC.
rewrite addrKA opprK.

rewrite /point_strictly_under_edge /= {pabhl pabhr vallow valhigh poep' poep'' poepf' puep pabp'}.
rewrite addrC.
have inH' := inH.
rewrite -subr_gte0 in inH'.
rewrite -subr_lt0 in y''diff.
rewrite strictE.
move => /eqP <-.
by rewrite pmulr_rlt0.
Qed.

Lemma order_edges_viz_point' low_e high_e p :
valid_edge low_e p -> valid_edge high_e p ->
low_e <| high_e ->
p <<= low_e -> p <<= high_e.
Proof.
move => vallow valhigh.
have  := (exists_point_valid  vallow  ) .
have := (exists_point_valid  valhigh  ) => [][] ph verhigh [] pl verlow.
have  := intersection_on_edge verlow => [][] poepl eqxl.
have  := intersection_on_edge verhigh => [][] poeph eqxh.
rewrite /edge_below => /orP [] /andP [].
  move => pueplow puephigh.
  apply (under_low_imp_under_high pueplow puephigh vallow valhigh).
move => pabpleft pabpright.
  apply (under_low_imp_under_high_bis pabpleft pabpright vallow valhigh).
Qed.

Lemma order_edges_strict_viz_point' low_e high_e p :
valid_edge low_e p -> valid_edge high_e p ->
low_e <| high_e ->
p <<< low_e ->  p <<< high_e.
Proof.
move => vallow valhigh.
have  := (exists_point_valid  vallow  ) .
have := (exists_point_valid  valhigh  ) => [][] ph verhigh [] pl verlow.
have  := intersection_on_edge verlow => [][] poepl eqxl.
have  := intersection_on_edge verhigh => [][] poeph eqxh.
rewrite /edge_below => /orP [] /andP [].
  set A := left_pt low_e.
  set B := right_pt low_e.
  move => pueplow puephigh.
  move =>  inf0.
  have:= inf0; rewrite /point_strictly_under_edge.
  rewrite strictE.
  move=> /ltW; rewrite -/A -/B => infeq0.
  have := (under_low_imp_strict_under_high pueplow puephigh vallow valhigh inf0).
  by rewrite /point_strictly_under_edge strictE.
move=> pueplow puephigh.
move=> inf0.
by have := (under_low_imp_strict_under_high_bis pueplow puephigh vallow valhigh inf0).
Qed.

Lemma edge_dir_intersect p1 p2 e1 :
  p_x p1 != p_x p2 ->
  ~~(p1 <<= e1) -> p2 <<< e1 ->
 exists p, area3 p (left_pt e1) (right_pt e1) = 0 /\
      area3 p p1 p2 = 0 /\
   (forall q, area3 q (left_pt e1) (right_pt e1) = 0 ->
       area3 q p1 p2 = 0 -> p = q).
Proof.
move=> dif12.
rewrite /point_under_edge underE.
rewrite area3E -ltNge => ca.
rewrite /point_strictly_under_edge strictE.
rewrite area3E => cu.
have [px [py []]] := line_intersection dif12 ca cu.
rewrite -/(p_y (Bpt px py)); set py' := (p_y (Bpt px py)).
rewrite -/(p_x (Bpt px py)) /py' {py'}.
move: ca cu; rewrite -4!area3E=> ca cu on_line1 [] on_line2 uniq.
exists (Bpt px py); rewrite on_line1 on_line2;split;[ | split]=> //.
by move=> [qx qy]; rewrite !area3E=> /uniq => U; move=> {}/U[] /= -> ->.
Qed.

Lemma intersection_middle_au e1 e2 :
  ~~ (left_pt e2 <<= e1) -> right_pt e2 <<< e1 ->
  exists p, area3 p (left_pt e1) (right_pt e1) = 0 /\ p === e2.
Proof.
move=> /[dup] ca; rewrite -ltNge subrr=> ca' /[dup] cu cu'.
rewrite /point_strictly_under_edge strictE in cu'.
have le2xnre2x : p_x (left_pt e2) != p_x (right_pt e2).
  by have := edge_cond e2; rewrite lt_neqAle=> /andP[].
have [p [p1 [p2 pu]]] := edge_dir_intersect le2xnre2x ca cu.
exists p; rewrite p1; split=> //.
rewrite /point_on_edge p2 eqxx /= /valid_edge.
rewrite /generic_trajectories.valid_edge.
have/eqP ol2 := p2.
have := area3_on_edge (left_pt e1) (right_pt e1) ol2 => /=.
rewrite p1 mulr0 eq_sym addrC addr_eq0 -mulNr opprB=> /eqP signcond.
case : (ltP (p_x p) (p_x (right_pt e2))).
  move=>/[dup]/ltW ->; rewrite andbT -subr_gt0 -subr_le0.
  rewrite -(pmulr_lgt0 _ ca') signcond.
  by rewrite nmulr_lgt0 // => /ltW.
move=>/[dup] re2lp.
rewrite -subr_le0 -(pmulr_lle0 _ ca') signcond.
by rewrite nmulr_lle0 // subr_ge0=> /(le_trans re2lp); rewrite leNgt edge_cond.
Qed.

Lemma intersection_middle_ua e1 e2 :
  left_pt e2 <<< e1 -> ~~(right_pt e2 <<= e1) ->
  exists p, area3 p (left_pt e1) (right_pt e1) = 0 /\ p === e2.
Proof.
move=> /[dup] cu cu' /[dup] ca; rewrite -ltNge subrr=> ca'.
rewrite /point_strictly_under_edge strictE in cu'.
have re2xnle2x : p_x (right_pt e2) != p_x (left_pt e2).
  by have := edge_cond e2; rewrite lt_neqAle eq_sym=> /andP[].
have [p [p1 [p2 pu]]] := edge_dir_intersect re2xnle2x ca cu.
move: p2; rewrite area3_opposite area3_cycle => /eqP.
rewrite oppr_eq0=> /[dup] ol2 /eqP p2.
exists p; rewrite p1; split=> //.
rewrite /point_on_edge p2 eqxx /= /valid_edge.
rewrite /generic_trajectories.valid_edge.
have := area3_on_edge (left_pt e1) (right_pt e1) ol2 => /=.
rewrite p1 mulr0 eq_sym addrC addr_eq0 -mulNr opprB=> /eqP signcond.
case : (ltP (p_x p) (p_x (right_pt e2))).
  move=>/[dup]/ltW ->; rewrite andbT -subr_gt0 -subr_le0.
  rewrite -(nmulr_llt0 _ cu') signcond.
  by rewrite pmulr_llt0 // => /ltW.
move=>/[dup] re2lp.
rewrite -subr_le0 -(nmulr_lge0 _ cu') signcond.
by rewrite pmulr_lge0 // subr_ge0=> /(le_trans re2lp); rewrite leNgt edge_cond.
Qed.

Definition lexPt (p1 p2 : pt) : bool :=
  (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 < p_y p2)).

Definition lexePt (p1 p2 : pt) : bool :=
    (p_x p1 < p_x p2) || ((p_x p1 == p_x p2) && (p_y p1 <= p_y p2)).

Lemma lexPtW p1 p2 :
  lexPt p1 p2 -> lexePt p1 p2.
Proof.
rewrite /lexPt /lexePt =>/orP [-> //=| /andP [] -> y_ineq].
rewrite ltW //. 
by rewrite orbT.
Qed.

Lemma lexePtNgt (p1 p2 : pt) : lexePt p1 p2 = ~~lexPt p2 p1.
Proof.
rewrite /lexePt /lexPt negb_or negb_and.
rewrite andb_orr -leNgt (andbC (_ <= _)) (eq_sym (p_x p2)) -lt_neqAle.
rewrite -leNgt (le_eqVlt (p_x p1)).
by case: (p_x p1 < p_x p2) => //; rewrite ?orbF //=.
Qed.

Lemma lexPtNge (p1 p2 : pt) : lexPt p1 p2 = ~~lexePt p2 p1.
Proof.
rewrite /lexePt /lexPt.
rewrite negb_or -leNgt negb_and (eq_sym (p_x p2)) andb_orr (andbC (_ <= _)).
rewrite -lt_neqAle le_eqVlt -ltNge.
by case: (p_x p1 < p_x p2); rewrite // ?orbF.
Qed.

Lemma lexePt_eqVlt (p1 p2 :pt) : lexePt p1 p2 = (p1 == p2) || lexPt p1 p2.
Proof.
rewrite /lexePt /lexPt.
case: (ltrgtP (p_x p1) (p_x p2))=> cnd; rewrite ?orbT //= ?orbF.
  by apply/esym/negP=> /eqP p1p2; move: cnd; rewrite p1p2 ltxx.
apply/idP/idP.
  rewrite orbC le_eqVlt=> /orP[/eqP | ->// ].
  move: cnd; case: p1 => [a b]; case: p2 => [c d]/= -> ->.
  by rewrite eqxx orbT.
by move/orP=> [/eqP -> // | /ltW].
Qed.

Lemma lexPt_irrefl : irreflexive lexPt.
Proof.
move=> x; apply/negP=> /[dup] abs.
by rewrite lexPtNge lexePt_eqVlt abs orbT.
Qed.

Lemma lexePt_refl : reflexive lexePt.
Proof.
rewrite /reflexive /lexePt=> p.
by rewrite eqxx le_refl /= orbT.
Qed.

Lemma lexPt_trans  : transitive lexPt.
Proof.
  rewrite /transitive /lexPt => p2 p1 p3 => /orP [xineq /orP [xineq2| /andP []/eqP <- yineq]|/andP []/eqP -> yineq /orP [-> //|/andP [] /eqP -> yineq2]] .
      by rewrite (lt_trans xineq xineq2).
    by rewrite xineq.
  by rewrite (lt_trans yineq yineq2) eqxx orbT.
Qed.

Lemma lexePt_lexPt_trans p1 p2 p3 : 
lexePt p1 p2 -> lexPt p2 p3 -> lexPt p1 p3.
Proof.
rewrite /lexePt /lexPt => /orP  [x_ineq|/andP  [] /eqP -> y_ineq /orP [-> // |/andP []/eqP -> y_s]].
  have : lexPt p1 p2.
    by rewrite /lexPt x_ineq.
  by apply lexPt_trans.
by rewrite( le_lt_trans y_ineq y_s) eqxx /= orbT.
Qed.

Lemma lexPt_lexePt_trans p1 p2 p3 :
lexPt p1 p2 -> lexePt p2 p3 -> lexPt p1 p3.
Proof.
move/[swap].
rewrite /lexePt /lexPt => /orP  [x_ineq|/andP  [] /eqP -> y_ineq /orP [-> // |/andP []/eqP -> y_s]].
  have : lexPt p2 p3.
    by rewrite /lexPt x_ineq.
  move/[swap]; apply lexPt_trans.
by rewrite( lt_le_trans y_s y_ineq) eqxx /= orbT.
Qed.

Lemma lexePt_trans : transitive lexePt.
move => p2 p1 p3; rewrite lexePt_eqVlt => /orP[/eqP-> // | p1p2] p2p3.
by apply/lexPtW/(lexPt_lexePt_trans p1p2).
Qed.

Lemma lexePt_xW p1 p2 : lexePt p1 p2 -> p_x p1 <= p_x p2.
Proof.
by rewrite /lexePt=> /orP[/ltW | /andP [/eqP -> _]].
Qed.

Lemma on_edge_lexePt_left_pt (p : pt) g :
  p === g -> lexePt (left_pt g) p.
Proof.
move=> on.
have : p_x (left_pt g) <= p_x p by move: on=> /andP[] _ /andP[].
rewrite le_eqVlt=> /orP[/eqP/esym /[dup] samex' /eqP samex | xlt ].
 have/eqP samey := on_edge_same_point on (left_on_edge _) samex.
  have -> : p = left_pt g.
    by apply/eqP; rewrite pt_eqE samex' samey !eqxx.
  by apply: lexePt_refl.
by rewrite /lexePt xlt.
Qed.

Lemma trans_edge_below_out p e1 e2 e3 :
  left_pt e1 = p -> left_pt e2 = p -> left_pt e3 = p ->
  e1 <| e2 -> e2 <| e3 -> e1 <| e3.
Proof.
case: e1 => [d [a_x a_y] /= cpa].
case: e2 => [d' [b_x b_y] /= cpb].
case: e3 => [d'' [c_x c_y] /= cpc] dp d'p d''p.
rewrite /edge_below /point_under_edge /point_strictly_under_edge.
rewrite !underE !strictE.
rewrite !area3E; simpl left_pt; simpl right_pt.
move: cpa cpb cpc; rewrite dp d'p d''p {dp d'p d''p}.
case: p=> [px py]; simpl p_x; simpl p_y=> cpa cpb cpc.
move=> c1' c2'.
have c1 : 0 <= pue_f px py a_x a_y b_x b_y.
  move: c1'; rewrite !(eqP (pue_f_eq _ _ _ _)) lexx ltxx !andTb -leNgt.
  by rewrite pue_f_o oppr_lte0 (pue_f_c px)=> /orP[].
have c2 : 0 <= pue_f px py b_x b_y c_x c_y.
  move: c2'; rewrite !(eqP (pue_f_eq _ _ _ _)) lexx ltxx !andTb -leNgt.
  by rewrite pue_f_o oppr_lte0 (pue_f_c px)=> /orP[].
move=> {c1' c2'}.
apply/orP; left.
rewrite (eqP (pue_f_eq _ _ _ _)) lexx andTb pue_f_o -pue_f_c oppr_lte0.
set p := Bpt px py.
have aright : 0 < area3 p (subpoint p) (Bpt a_x a_y).
  by apply: point_sub_right.
have bright : 0 < area3 p (subpoint p) (Bpt b_x b_y).
  by apply: point_sub_right.
have cright : 0 < area3 p (subpoint p) (Bpt c_x c_y).
  by apply: point_sub_right.
rewrite area3E in aright; simpl p_x in aright; simpl p_y in aright.
rewrite area3E in bright; simpl p_x in bright; simpl p_y in bright.
rewrite area3E in cright; simpl p_x in cright; simpl p_y in cright.
rewrite -(pmulr_lge0 _ bright) -pue_f_ax5.
by apply: addr_ge0; rewrite pmulr_lge0.
Qed.

Lemma no_crossingE e1 e2 :
  below_alt e1 e2 -> valid_edge e2 (left_pt e1) ->
  (left_pt e1 <<< e2 -> e1 <| e2) /\ (~~(left_pt e1 <<= e2) -> e2 <| e1).
Proof.
move=> nc ve.
case: (exists_point_valid ve) => [p pP].
move: (intersection_on_edge pP)=> [pone2 px].
move: (pone2); rewrite /point_on_edge=> /andP[] pone2' vp.
have xbnd1 : p_x (left_pt e2) <= p_x (left_pt e1) by case/andP: ve.
have xbnd2 : p_x (left_pt e1) <= p_x (right_pt e2) by case/andP: ve.
have dify : ((left_pt e1 <<< e2) \/ (~~(left_pt e1 <<= e2))) -> p_y (left_pt e1) != p_y p.
  move=> disj; apply/negP=> /eqP A.
  have {A}-A : p = left_pt e1 by case: (p) (left_pt e1) px A=> [? ?][? ?]/= -> ->.
  by move: disj; rewrite under_onVstrict // strict_nonAunder // -A pone2; case.
have pone2'': pue_f (p_x (left_pt e2)) (p_y (left_pt e2))
             (p_x (right_pt e2)) (p_y (right_pt e2))
             (p_x p) (p_y p) == 0.
  by rewrite -pue_f_c; move: pone2'; rewrite area3E pue_f_c.
move: (edge_cond e2); rewrite -(subr_gt0 (p_x _))=> ce2.
have dife2 : 0 < p_x (right_pt e2) - p_x (left_pt e2).
  by move: (edge_cond e2); rewrite -(subr_gt0 (p_x _)).
have dife2' : p_x (right_pt e2) - p_x (left_pt e2) != 0.
  by move: dife2; rewrite  lt_neqAle eq_sym=> /andP[].
have plp2 : p_x (left_pt e2) = p_x (left_pt e1) -> p = left_pt e2.
  move=> c; have:= on_edge_same_point pone2 (left_on_edge _).
  rewrite c px eqxx=> /(_ isT)=> /eqP; move: px c.
  by case: (p) (left_pt e2)=> [? ?][? ?]/= <- <- ->.
have prp2 : p_x (right_pt e2) = p_x (left_pt e1) -> p = right_pt e2.
  move=> c; have:= on_edge_same_point pone2 (right_on_edge _).
  rewrite c px eqxx=> /(_ isT)=> /eqP; move: px c.
  by case: (p) (right_pt e2)=> [? ?][? ?]/= <- <- ->.
have main : (0 < area3 (left_pt e1) (left_pt e2) (right_pt e2)) =
       (p_y p < p_y (left_pt e1)).
  move: xbnd1; rewrite le_eqVlt=> /orP[/eqP atleft | notleft ].
    have pisl : p = left_pt e2 by apply: plp2.
    move: atleft; rewrite -pisl=> atleft; rewrite edge_and_left_vertical //.
    by rewrite -atleft pisl (edge_cond e2).
  have fact1 : (0 < p_x p - p_x (left_pt e2)) by rewrite subr_gt0 -px.
  rewrite -(pmulr_rgt0 _ fact1) area3_opposite mulrN.
  rewrite -(eqP (area3_triangle_on_edge (left_pt e1) pone2')) -mulrN.
  rewrite -area3_opposite area3_cycle pmulr_rgt0 //.
  by apply: edge_and_right_vertical; rewrite -px.
have arith : forall (a b : R), a <= 0 -> b <= 0 -> a + b <= 0.
  clear=> a b al0 bl0.
  by rewrite -lerBrDr (le_trans al0) // lerBrDr add0r.
have case1 : left_pt e1 <<< e2 -> e1 <| e2.
  move=> below; case:(nc) => // /orP[]; last by rewrite below.
  move/andP=> []le2b re2b.
  have pyne1 : p_y (left_pt e1) != p_y p by apply: dify; left.
  have ys : p_y (left_pt e1) < p_y p.
    rewrite ltNge le_eqVlt -main negb_or eq_sym pyne1 /= -leNgt le_eqVlt.
    by move: (below); rewrite /point_strictly_under_edge strictE orbC => ->.
  have : 0 < area3 p (left_pt e1) (right_pt e1).
    by rewrite edge_and_left_vertical // -px (edge_cond e1).
  rewrite -(pmulr_rgt0 _ ce2).
  rewrite (eqP (area3_on_edge (left_pt e1) (right_pt e1) pone2')).
  rewrite ltNge arith //.
    apply: mulr_ge0_le0; first by rewrite -px subr_ge0.
    by move: re2b; rewrite /point_under_edge underE -area3_cycle.
  apply: mulr_ge0_le0; first by rewrite -px subr_ge0.
  by move: le2b; rewrite /point_under_edge underE -area3_cycle.
suff case2 : ~~(left_pt e1 <<= e2) -> e2 <| e1 by [].
move=> above; case: (nc) => // /orP[]; first by rewrite (negbTE above).
rewrite /point_strictly_under_edge !strictE -!leNgt => /andP[] le2a re2a.
have pyne1 : p_y (left_pt e1) != p_y p by apply: dify; right.
have ys : p_y p < p_y (left_pt e1).
  by rewrite -main;move: (above); rewrite /point_under_edge -ltNge subrr.
have : 0 < area3 (left_pt e1) p (right_pt e1).
  by rewrite edge_and_left_vertical // (edge_cond e1).
rewrite area3_opposite -area3_cycle.
rewrite -(pmulr_rgt0 _ dife2) mulrN.
move: (eqP (area3_on_edge (left_pt e1) (right_pt e1) pone2')) => ->.
by rewrite oppr_gt0 ltNge addr_ge0 // mulr_ge0 // -px subr_ge0.
Qed.


Lemma inter_at_ext_no_crossing (s : seq edge) :
  {in s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s &, no_crossing}.
Proof.
move=> nc e1 e2 e1in e2in.
have nc' := inter_at_ext_sym nc.
have ceq : e1 = e2 -> below_alt e1 e2.
  move=> <-; left; apply/orP; left; rewrite /point_under_edge !underE.
  rewrite (fun a b => eqP (proj1 (area3_two_points a b))).
  rewrite (fun a b => eqP (proj1 (proj2 (area3_two_points a b)))).
  by rewrite lexx.
have [/eqP/ceq // | e1ne2] := boolP(e1 == e2).
have [/eqP | {}nc ] := nc _ _ e1in e2in; first by rewrite (negbTE e1ne2).
have [/eqP | {}nc' ] := nc' _ _ e1in e2in; first by rewrite (negbTE e1ne2).
have [ | ] := boolP(e1 <| e2); first by left.
have [ | ] := boolP(e2 <| e1); first by right.
rewrite /edge_below.
rewrite !negb_or. rewrite 4!negb_and !negbK.
rewrite /edge_below/point_under_edge !underE.
rewrite /point_strictly_under_edge !strictE => noc.
suff [it | [p [pone1 pone2]]] :
  below_alt e1 e2 \/ exists p, p === e1 /\ p === e2; first by [].
  have : p \in [:: left_pt e1; right_pt e1] by apply: nc.
  rewrite !inE=> pext.
  set other := if p == left_pt e1 then right_pt e1 else left_pt e1.
  have dif : right_pt e1 != left_pt e1.
    apply/eqP=> abs.
    move: (edge_cond e1); rewrite lt_neqAle eq_sym => /andP[].
    by rewrite abs eqxx.
  have [ u' | /underWC a'] := boolP (other <<= e2).
    left; apply/orP; left.
    move: (pone2) u'=> /andP[] _ /under_onVstrict.
    rewrite pone2 /= /other.
    by  move: pext=> /orP[] /eqP -> ->; rewrite ?eqxx ?(negbTE dif) ?andbT.
  right; apply/orP; right.
    move: (pone2) a'=> /andP[] _/strict_nonAunder; rewrite pone2 /= /other.
    by move: pext=>/orP[]/eqP -> ->; rewrite ?eqxx ?(negbTE dif)=> ->.
move: noc {nc nc'} => /andP[] /orP[le2a | re2a].
  have le2a' : left_pt e2 >>> e1.
    by rewrite /point_under_edge/generic_trajectories.point_under_edge subrr.
  have [ re2u | re2a _] := boolP(right_pt e2 <<< e1); last first.
    by left; left; apply/orP; right; rewrite re2a underWC.
  have dif2 : p_x (left_pt e2) != p_x (right_pt e2).
    by have := edge_cond e2; rewrite lt_neqAle => /andP[].
  have [r [_ [ _ uniq]]] := edge_dir_intersect dif2 le2a' re2u.
  move=> /orP[le1u | re1u].
    have [re1u | re1a] := boolP(right_pt e1 <<= e2).
      left; left; apply/orP; left; rewrite re1u underW //.
      by rewrite /point_strictly_under_edge strictE.
    have le1u' : left_pt e1 <<< e2.
      by rewrite /point_strictly_under_edge strictE.
    have [p [pe2 pe1]] := intersection_middle_ua le1u' re1a.
    have [q [qe1 qe2]] := intersection_middle_au le2a' re2u.
    move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP qe2' _.
    have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
    by right; exists r; rewrite [X in X === e2]rq rp.
  have [le1u | le1a] := boolP(left_pt e1 <<= e2).
      left; left; apply/orP; left; rewrite le1u underW //.
      by rewrite /point_strictly_under_edge strictE.
  have [q [qe1 qe2]] := intersection_middle_au le2a' re2u.
  have re1u' : right_pt e1 <<< e2.
    by rewrite /point_strictly_under_edge strictE.
  have [p [pe2 pe1]] := intersection_middle_au le1a re1u'.
  move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP qe2' _.
  have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
  by right; exists r; rewrite [X in X === e2]rq rp.
have re2a' : right_pt e2 >>> e1.
  by rewrite /point_under_edge/generic_trajectories.point_under_edge subrr.
have [ le2u | le2a _] := boolP(left_pt e2 <<< e1); last first.
  by left; left; apply/orP; right; rewrite le2a underWC.
have dif2 : p_x (right_pt e2) != p_x (left_pt e2).
  by have := edge_cond e2; rewrite lt_neqAle eq_sym => /andP[].
have [r [_ [ _ uniq]]] := edge_dir_intersect dif2 re2a' le2u.
have transfer a b c : area3 a b c = 0 -> area3 a c b = 0.
  by move=> abc; rewrite area3_opposite area3_cycle abc oppr0.
move=> /orP[le1u | re1u].
  have [re1u | re1a] := boolP(right_pt e1 <<= e2).
    left; left; apply/orP; left; rewrite re1u underW //.
    by rewrite /point_strictly_under_edge strictE.
  have le1u' : left_pt e1 <<< e2.
    by rewrite /point_strictly_under_edge strictE.
  have [p [/transfer pe2 pe1]] := intersection_middle_ua le1u' re1a.
  have [q [qe1 qe2]] := intersection_middle_ua le2u re2a'.
  move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP /transfer qe2' _.
  have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
  by right; exists r; rewrite [X in X === e2]rq rp.
have [le1u | le1a] := boolP(left_pt e1 <<= e2).
  left; left; apply/orP; left; rewrite le1u underW //.
  by rewrite /point_strictly_under_edge strictE.
have [q [qe1 qe2]] := intersection_middle_ua le2u re2a'.
have re1u' : right_pt e1 <<< e2.
  by rewrite /point_strictly_under_edge strictE.
have [p [/transfer pe2 pe1]] := intersection_middle_au le1a re1u'.
move: (pe1) (qe2)=> /andP[] /eqP pe1' _ /andP[] /eqP /transfer qe2' _.
have rq := uniq _ qe1 qe2'; have rp := uniq _ pe1' pe2.
by right; exists r; rewrite [X in X === e2]rq rp.
Qed.

Lemma outgoing_conditions (s oe : seq edge) p he le :
  p >>> le -> p <<< he -> le \in s -> he \in s ->
  valid_edge le p -> valid_edge he p ->
  {subset oe <= s} ->
  {in s &, no_crossing} ->
  {in oe, forall g, left_pt g == p} ->
  [/\ {in oe, forall g, le <| g}, {in oe, forall g, g <| he} &
      {in oe &, no_crossing}].
Proof.
move=> pl ph lein hein vl vh oesub noc lefts; split.
+ move=> g gin; have := noc _ _ (oesub _ gin) lein.
  move=>/no_crossingE[]; first by rewrite (eqP (lefts _ _)) // sval.
  by rewrite (eqP (lefts _ _)) // => _ /(_ pl).
+ move=> g gin; have := noc _ _ (oesub _ gin) hein.
  move=>/no_crossingE[]; first by rewrite (eqP (lefts _ _)) // sval.
  by rewrite (eqP (lefts _ _)) // => /(_ ph).
exact: (sub_in2 oesub).
Qed.

Lemma common_point_edges_y_left r r1 r2 e1 e2 :
   valid_edge e1 r -> p_x r <= p_x (left_pt e1) ->
     p_x r = p_x r1 -> p_x r = p_x r2 -> left_pt e1 === e2 ->
     r1 === e1 -> r2 === e2 ->
     p_y r1 = p_y r2.
Proof.
move=> v xl rr1 rr2 e1e2 re1 re2.
have xl': p_x r = p_x (left_pt e1) by apply: le_anti; rewrite xl; case/andP:v.
have:= on_edge_same_point e1e2 re2; rewrite -xl' rr2 eqxx=> /(_ isT)/eqP <-.
have:= on_edge_same_point (left_on_edge _) re1.
by rewrite -xl' rr1 eqxx=>/(_ isT)/eqP<-.
Qed.

Lemma common_point_edges_y_right r r1 r2 e1 e2 :
 valid_edge e1 r -> p_x (right_pt e1) <= p_x r ->
     p_x r = p_x r1 -> p_x r = p_x r2 -> right_pt e1 === e2 ->
     r1 === e1 -> r2 === e2 ->
     p_y r1 = p_y r2.
Proof.
move=> v xl rr1 rr2 e1e2 re1 re2.
have xl': p_x r = p_x (right_pt e1).
  by apply: le_anti; rewrite xl andbC; case/andP:v.
have:= on_edge_same_point e1e2 re2; rewrite -xl' rr2 eqxx=> /(_ isT)/eqP <-.
have:= on_edge_same_point (right_on_edge _) re1.
  by rewrite -xl' rr1 eqxx=>/(_ isT)/eqP<-.
Qed.

Lemma expand_valid p q (pq : p_x p < p_x q) e r :
  valid_edge (Bedge pq) r ->
  valid_edge e p -> valid_edge e q -> valid_edge e r.
Proof.
move=>/andP[]pr rq /andP[] lep pre /andP[]leq qre; rewrite /valid_edge.
rewrite /generic_trajectories.valid_edge.
by rewrite (le_trans lep) ?(le_trans rq).
Qed.

Lemma keep_under (p q : pt) e1 e2 :
  inter_at_ext e1 e2 ->
  {in [:: p; q] & [:: e1; e2], forall r e, valid_edge e r} ->
  p <<< e1 -> ~~ (p <<< e2) -> ~~(q <<< e1) -> ~~(q <<< e2).
Proof.
have left_ext r r1 r2 := @common_point_edges_y_left r r1 r2 e1 e2.
have right_ext r r1 r2 := @common_point_edges_y_right r r1 r2 e1 e2.
move=> noc val pue1 pae2 qae1; apply/negP=> que2; set v := valid_edge.
have : [/\ v e1 p, v e2 p, v e1 q & v e2 q].
  by split; apply: val; rewrite !inE eqxx ?orbT.
have pr e r: valid_edge e r ->
   exists r', [/\ valid_edge e r, r' === e & p_x r = p_x r'].
    move=>/[dup]vr/exists_point_valid[r' /intersection_on_edge [one xx]].
    by exists r'; constructor.
move=>[]/pr[p1 [vp1 pone1 p1p]] /pr[p2 [vp2 pone2 p2p]].
move=> /pr[q1 [vq1 qone1 q1q]] /pr[q2 [vq2 qone2 q2q]].
move: vp1 vp2 vq1 vq2 p1p p2p q1q q2q=>vp1 vp2 vq1 vq2 p1p p2p q1q q2q.
move: pone1 pone2 qone1 qone2=>pone1 pone2 qone1 qone2 {pr v val}.
set abbrev := strict_under_edge_lower_y.
have pylt : p_y p < p_y p1 by rewrite -(abbrev _ _ _ _ pone1).
have pyge : p_y p2 <= p_y p by rewrite leNgt -(abbrev _ _ _ _ pone2).
have qyge : p_y q1 <= p_y q by rewrite leNgt -(abbrev _ _ _ _ qone1).
have qylt : p_y q < p_y q2 by rewrite -(abbrev _ _ _ _ qone2).
have yp : p_y p2 < p_y p1 by rewrite (le_lt_trans pyge).
have yq : p_y q1 < p_y q2 by rewrite (le_lt_trans qyge).
move=> {pyge qyge pylt qylt abbrev}.
have [/[dup]p1p2 + /[dup] q1q2 +] : [/\ p_x p1 == p_x p2 & p_x q1 == p_x q2].
  by rewrite -p1p p2p -q1q q2q !eqxx.
move=>/eqP/esym/eqP p2p1 /eqP/esym/eqP q2q1.
move: (pone1) (pone2) (qone1) (qone2).
move=>/andP[]pl1 _ /andP[]pl2 _ /andP[]ql1 _ /andP[] ql2 _.
have [pltq | qltp | pq ] := ltrgtP (p_x p) (p_x q).
- have [p1q1 p2q2] : p_x p1 < p_x q1 /\ p_x p2 < p_x q2.
    by rewrite -p1p -q1q -p2p -q2q .
  set e3 := Bedge p1q1; set e4 := Bedge p2q2.
  have l3a : ~~(left_pt e3 <<= e4).
    by move/(@pue_left_edge e4):p2p1=> -> /=; rewrite subr_ge0 -ltNge.
  have r3u : right_pt e3 <<< e4.
    by move/(@psue_right_edge e4):q2q1=> -> /=; rewrite subr_lt0.
  have [pi [pi4 /andP[pi3 piint]]] := intersection_middle_au l3a r3u.
  have pi1 : pi === e1.
    apply/andP; split; last first.
      apply: (expand_valid piint);
        by rewrite /valid_edge/generic_trajectories.valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (area3_change_ext _ (edge_cond e1) p1q1) //.
    by rewrite (eqP pi3) /sg !eqxx.
  have pi2 : pi === e2.
    apply/andP; split; last first.
      by apply:(expand_valid piint);
          rewrite /valid_edge/generic_trajectories.valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (area3_change_ext _ (edge_cond e2) p2q2) //.
    by rewrite pi4 /sg !eqxx.
  move: piint; rewrite /valid_edge/generic_trajectories.valid_edge.
  rewrite /e3/= -p1p -q1q=> /andP[] ppi piq.
  case: noc=> [E | /(_ pi pi1 pi2) piext]; first by move: pae2; rewrite -E pue1.
  move: (piext) ppi piq pi1 pi2 { pi3 pi4 }; rewrite !inE.
  move => /orP[]/eqP/[dup]pival -> ppi piq pi1 pi2.
    have abs := left_ext _ _ _ vp1 ppi p1p p2p pi2 pone1 pone2.
    by move: yp; rewrite abs ltxx.
  have abs := right_ext _ _ _ vq1 piq q1q q2q pi2 qone1 qone2.
  by move: yq; rewrite abs ltxx.
- have [q1p1 q2p2] : p_x q1 < p_x p1 /\ p_x q2 < p_x p2.
    by rewrite -p1p -q1q -p2p -q2q .
  set e3 := Bedge q1p1; set e4 := Bedge q2p2.
  have l3u : left_pt e3 <<< e4.
    by move/(@psue_left_edge e4):q2q1=> -> /=; rewrite subr_gt0.
  have r3a : right_pt e3 >>> e4.
    by move/(@pue_right_edge e4):p2p1=> -> /=; rewrite subr_le0 -ltNge.
  have [pi [pi4 /andP[pi3 piint]]] := intersection_middle_ua l3u r3a.
  have pi1 : pi === e1.
    apply/andP; split; last first.
      by apply: (expand_valid piint); rewrite /valid_edge
           /generic_trajectories.valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (area3_change_ext _ (edge_cond e1) q1p1) //.
    by rewrite (eqP pi3) /sg !eqxx.
  have pi2 : pi === e2.
    apply/andP; split; last first.
      by apply:(expand_valid piint);
        rewrite /valid_edge/generic_trajectories.valid_edge -?p1p -?q1q.
    rewrite -sgr_eq0 (area3_change_ext _ (edge_cond e2) q2p2) //.
    by rewrite pi4 /sg !eqxx.
  move: piint; rewrite /valid_edge/generic_trajectories.valid_edge.
  rewrite /e3/= -p1p -q1q=> /andP[] qpi pip.
  case: noc=> [E | /(_ pi pi1 pi2) piext]; first by move: pae2; rewrite -E pue1.
  move: (piext) qpi pip pi1 pi2 { pi3 pi4 }; rewrite !inE.
  move => /orP[]/eqP/[dup]pival -> qpi pip pi1 pi2.
    have abs := left_ext _ _ _ vq1 qpi q1q q2q pi2 qone1 qone2.
    by move: yq; rewrite abs ltxx.
  have abs := right_ext _ _ _ vp1 pip p1p p2p pi2 pone1 pone2.
  by move: yp; rewrite abs ltxx.
have := conj (on_edge_same_point pone1 qone1) (on_edge_same_point pone2 qone2).
rewrite -p1p -p2p pq q1q q1q2 !eqxx=> -[]/(_ isT)/eqP p1q1 /(_ isT)/eqP p2q2.
by move: yp; rewrite p1q1 p2q2; rewrite ltNge le_eqVlt yq orbT.
Qed.

Definition pvert_y (p : pt) (e : edge) :=
  match vertical_intersection_point p e with
    Some p' => p_y p'
  | None => 0
  end.

Lemma pvertE p e : valid_edge e p ->
  vertical_intersection_point p e = Some (Bpt (p_x p) (pvert_y p e)).
Proof.
move=> vep; rewrite /pvert_y.
have [p' p'P] := exists_point_valid vep; rewrite p'P.
have [one pxq] := intersection_on_edge p'P.
by rewrite pxq; case: (p') one.
Qed.

Lemma pvert_on p e : valid_edge e p ->
  Bpt (p_x p) (pvert_y p e) === e.
Proof.
move=> vep; rewrite /pvert_y.
have [p' p'P] := exists_point_valid vep; rewrite p'P.
have [one pxq] := intersection_on_edge p'P.
by rewrite pxq; case: (p') one.
Qed.

Definition on_pvert p e : p === e -> pvert_y p e = p_y p.
Proof.
move=> /[dup]/andP[] _ vpe pone.
by have := on_edge_same_point pone (pvert_on vpe) (eqxx _) => /eqP ->.
Qed.

Definition cmp_slopes e1 e2 :=
  sg((p_y (right_pt e2) - p_y (left_pt e2)) * 
     (p_x (right_pt e1) -p_x (left_pt e1)) - 
     (p_y (right_pt e1) - p_y (left_pt e1)) * 
     (p_x (right_pt e2) - p_x (left_pt e2))).

Definition pedge_below p e1 e2 := 
  (pvert_y p e1 < pvert_y p e2) || 
  ((pvert_y p e1 == pvert_y p e2) && (0 <= cmp_slopes e1 e2)).

Definition pedge_below' p e1 e2 := 
  (pvert_y p e1 < pvert_y p e2) || 
  ((pvert_y p e1 == pvert_y p e2) && (cmp_slopes e1 e2 <= 0)).

Lemma same_left_edge_below_slopes e1 e2 :
  left_pt e1 = left_pt e2 ->
  e1 <| e2 = (0 <= cmp_slopes e1 e2).
Proof.
move=> sameleft.
rewrite /edge_below/point_under_edge !underE [in X in X || _]sameleft.
rewrite (eqP (proj1 (area3_two_points _ _))) lexx /=.
rewrite /point_strictly_under_edge !strictE -[in X in _ || X]sameleft -!leNgt.
rewrite (eqP (proj1 (area3_two_points _ _))) lexx /=.
rewrite !area3E !(proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
rewrite  /cmp_slopes sameleft -opprB oppr_le0.
rewrite [X in (_ <= X - _) || _]mulrC.
rewrite [X in _ || (_ <= _ - X)]mulrC.
rewrite orbb.
by rewrite sgr_ge0.
Qed.

Lemma same_right_edge_below_slopes e1 e2 :
  right_pt e1 = right_pt e2 ->
  e1 <| e2 = (cmp_slopes e1 e2 <= 0).
Proof.
move=> sameright.
rewrite /edge_below/point_under_edge !underE [in X in X || _]sameright.
rewrite (eqP (proj1 (proj2 (area3_two_points _ _)))) lexx /=.
rewrite /point_strictly_under_edge !strictE -[in X in _ || X]sameright -!leNgt.
rewrite (eqP (proj1 (proj2 (area3_two_points _ _)))) lexx /= !andbT.
rewrite !area3E !(proj2 (pue_f_eq_slopes _ _ _ _ _ _)).
rewrite /cmp_slopes sameright oppr_le0 opprB.
rewrite !(mulrC (p_y (right_pt e2) - _)) orbb.
by rewrite sgr_le0 -oppr_ge0 [X in _ = (0 <= X)]opprB.
Qed.

Definition slope e :=
  (p_y (right_pt e) - p_y (left_pt e)) / (p_x (right_pt e) - p_x (left_pt e)).

Lemma cmp_slopesE e1 e2 :
  cmp_slopes e1 e2 = sg(slope e2 - slope e1).
Proof.
have := edge_cond e1.
  rewrite -subr_gt0 =>/gtr0_sg den1.
have := edge_cond e2.
  rewrite -subr_gt0 =>/gtr0_sg den2.
rewrite -[RHS]mul1r -den1 -[RHS]mul1r -den2 -!sgrM.
rewrite [X in sg( _ * X)]mulrBr /slope.
rewrite [X in sg(X)]mulrBr 2![in X in sg(X - _)]mulrA.
rewrite [X in sg( X * _ * _ - _)]mulrC.
rewrite 2![in X in sg(_ - X)]mulrA.
rewrite /cmp_slopes.
set V := (p_x (right_pt e1) - _).
set W := (p_x (right_pt e2) - _).
set U := (p_y _ - _).
set Z := (p_y _ - _).
have den20 : W != 0 by rewrite -sgr_eq0 den2 oner_neq0.
have den10 : V != 0 by rewrite -sgr_eq0 den1 oner_neq0.
by rewrite (mulrAC V) mulfK // (mulrAC W) mulfK // (mulrC U) (mulrC Z).
Qed.

Lemma on_edge_same_slope_right e1 e1' :
  left_pt e1' === e1 -> right_pt e1 = right_pt e1' ->
  slope e1' = slope e1.
Proof.
move=> /andP[]+ val eqr.
rewrite area3_opposite area3_cycle oppr_eq0.
rewrite area3E (proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
have := edge_cond e1.
  rewrite -subr_gt0 => den1.
have := edge_cond e1'.
  rewrite -subr_gt0 => den1'.
rewrite subr_eq0.
set W := (p_x _ - _).
set V := (p_x _ - _).
have den10 : W != 0.
  by rewrite subr_eq0 eq_sym -subr_eq0 lt0r_neq0 // den1.
have den10v : W ^-1 != 0 by rewrite invr_eq0.
have den20 : V != 0.
  by rewrite subr_eq0 eq_sym -subr_eq0 lt0r_neq0 // eqr den1'.
have den20v : V ^-1 != 0 by rewrite invr_eq0.
rewrite -(inj_eq (mulIf den10v)) mulfK //.
rewrite -(inj_eq (mulfI den20v)) 2!mulrA 2!(mulrC V ^-1) divff // mul1r.
rewrite -[X in X / V]opprB mulNr -mulrN -invrN /V opprB.
rewrite -[X in X / W]opprB mulNr -mulrN -invrN /V opprB.
by rewrite /slope eqr=> /eqP.
Qed.

Lemma on_edge_same_slope_left e1 e1' :
  right_pt e1' === e1 -> left_pt e1 = left_pt e1' ->
  slope e1' = slope e1.
Proof.
move=> /andP[]+ val eqr.
rewrite area3E (proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
have := edge_cond e1.
  rewrite -subr_gt0 => den1.
have := edge_cond e1'.
  rewrite -subr_gt0 => den1'.
rewrite subr_eq0.
set W := (p_x _ - _).
set V := (p_x _ - _).
have den10 : W != 0.
  by rewrite subr_eq0 -subr_eq0 lt0r_neq0 // den1.
have den10v : W ^-1 != 0 by rewrite invr_eq0.
have den20 : V != 0.
  by rewrite subr_eq0 -subr_eq0 lt0r_neq0 // eqr den1'.
have den20v : V ^-1 != 0 by rewrite invr_eq0.
rewrite -(inj_eq (mulIf den10v)) mulfK //.
rewrite -(inj_eq (mulfI den20v)) 2!mulrA 2!(mulrC V ^-1) divff // mul1r.
by rewrite /slope /W /V eqr=> /eqP.
Qed.

Lemma cmp_slopesNC e1 e2 : -cmp_slopes e1 e2 = cmp_slopes e2 e1.
Proof. by rewrite /cmp_slopes -sgrN [in LHS]opprB. Qed.

Lemma contact_left_slope e1 e2 :
  left_pt e1 === e2 -> 
  (right_pt e1 <<= e2) = (0 <= cmp_slopes e1 e2) /\
  (right_pt e1 <<< e2) = (0 < cmp_slopes e1 e2).
Proof.
move=> /[dup] on2 /andP[] form val.
suff area3_eq :
  sg (area3 (right_pt e1) (left_pt e2) (right_pt e2)) =
  -(cmp_slopes e1 e2).
  rewrite /point_under_edge !underE /point_strictly_under_edge !strictE.
  rewrite -sgr_le0 area3_eq oppr_le0 sgr_ge0; split;[by [] |].
  by rewrite -sgr_lt0 area3_eq oppr_lt0 sgr_gt0.
move: (val) => /andP[] _; rewrite le_eqVlt=> /orP[/eqP atr | le1ltre2].
  rewrite /cmp_slopes atr.
  have eqps : left_pt e1 = right_pt e2.
    have := on_edge_same_point (right_on_edge _) on2.
    rewrite atr eqxx => /(_ isT) /eqP; move: (right_pt e2) (left_pt e1) atr.
    by move=> [] ? ? [] ? ? /= -> ->.
  rewrite area3_opposite area3_cycle.
  rewrite sgrN.
  rewrite !area3E !(proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
  rewrite -eqps -(mulrC (p_y _ - _)).
  rewrite -[X in _ = - sg (X * _ - _)]opprB -[X in _ = - sg (_ -  _ * X)]opprB.
  by rewrite mulrN mulNr -opprD opprB.
set e2' := Bedge le1ltre2.
have signcond := area3_change_ext (right_pt e1) (edge_cond e2) le1ltre2
             form (proj1 (proj2 (area3_two_points _ _))).
rewrite {}signcond.
have on2' : left_pt e2' === e2 by exact: on2.
rewrite cmp_slopesE  -(on_edge_same_slope_right on2')// -cmp_slopesE.
rewrite cmp_slopesNC.
rewrite area3E (proj1 (pue_f_eq_slopes _ _ _ _ _ _)) /cmp_slopes.
by rewrite /e2' /= [in LHS](mulrC (p_x _ - _)).
Qed.

Lemma contact_right_slope e1 e2 :
  right_pt e1 === e2 -> 
  (left_pt e1 <<= e2) = (cmp_slopes e1 e2 <= 0) /\
  (left_pt e1 <<< e2) = (cmp_slopes e1 e2 < 0).
Proof.
move=> /[dup] on2 /andP[] form val.
suff area3_eq :
  sg (area3 (left_pt e1) (left_pt e2) (right_pt e2)) =
  cmp_slopes e1 e2.
  rewrite /point_under_edge !underE /point_strictly_under_edge !strictE.
  rewrite -area3_eq -[X in X = _ /\ _]sgr_le0; split; first by [].
  by rewrite -[LHS]sgr_lt0.
move: (val) => /andP[] + _; rewrite le_eqVlt eq_sym=> /orP[/eqP atl | le2ltre1].
  rewrite /cmp_slopes atl.
  have eqps : right_pt e1 = left_pt e2.
    have := on_edge_same_point (left_on_edge _) on2.
    rewrite atl eqxx => /(_ isT) /eqP; move: (right_pt e1) (left_pt e2) atl.
    by move=> [] ? ? [] ? ? /= -> ->.
  rewrite !area3E !(proj1 (pue_f_eq_slopes _ _ _ _ _ _)).
  rewrite eqps (mulrC (p_x _ - _)).
  rewrite -[X in _ = sg (_ * X - _)]opprB -[X in _ = sg (_ -  X * _)]opprB.
  by rewrite mulrN mulNr -opprD opprB.
set e2' := Bedge le2ltre1.
have signcond := area3_change_ext (left_pt e1) (edge_cond e2) le2ltre1
             (proj1 (area3_two_points _ _)) form.
rewrite {}signcond.
have on2' : right_pt e2' === e2 by exact: on2.
rewrite cmp_slopesE  -(on_edge_same_slope_left on2')// -cmp_slopesE.
rewrite area3_opposite area3_cycle.
rewrite area3E (proj1 (pue_f_eq_slopes _ _ _ _ _ _)) /cmp_slopes.
rewrite /e2' /= [in LHS](mulrC (p_x _ - _)) opprB.
by rewrite -4![in LHS](opprB (_ (right_pt e1))) 2!mulrNN.
Qed.

Lemma sub_edge_right (p : pt) (e : edge) : p === e ->
  p_x p < p_x (right_pt e) ->
  {e' | [/\ left_pt e' = p, right_pt e' = right_pt e &
        forall e2, cmp_slopes e' e2 = cmp_slopes e e2]}.
Proof.
move=>/[dup] one /andP[] aligned val dif; exists (Bedge dif).
split => // e2; rewrite !cmp_slopesE.
by rewrite (@on_edge_same_slope_right e (Bedge dif) one erefl).
Qed.

Lemma sub_edge_left (p : pt) (e : edge) : p === e ->
  p_x (left_pt e) < p_x p ->
  {e' | [/\ left_pt e' = left_pt e, right_pt e' = p &
        forall e2, cmp_slopes e' e2 = cmp_slopes e e2]}.
Proof.
move=>/[dup] one /andP[] aligned val dif; exists (Bedge dif).
split => // e2; rewrite !cmp_slopesE.
by rewrite (@on_edge_same_slope_left e (Bedge dif) one erefl).
Qed.

Lemma intersection_imp_crossing e1 e2 p :
  p === e1 -> p === e2 ->
  p_x (left_pt e1) < p_x p -> p_x p < p_x (right_pt e1) ->
  p_x (left_pt e2) < p_x p -> p_x p < p_x (right_pt e2) ->
  ~below_alt e1 e2 \/ cmp_slopes e1 e2 == 0.
Proof.
move=> on1 on2 l1ltp pltr1 l2ltp pltr2.
have [e2' [le2' re2' sle2']] := sub_edge_left on2 l2ltp.
have [e2'' [le2'' re2'' sle2'']] := sub_edge_right on2 pltr2.
have [e1' [le1' re1' sle1']] := sub_edge_left on1 l1ltp.
have [e1'' [le1'' re1'' sle1'']] := sub_edge_right on1 pltr1.
have /contact_left_slope/= : left_pt e2'' === e1 by rewrite le2''.
have /contact_right_slope/= : right_pt e2' === e1 by rewrite re2'.
have /contact_left_slope/= : left_pt e1'' === e2 by rewrite le1''.
have /contact_right_slope/= : right_pt e1' === e2 by rewrite re1'.
rewrite le1' le2' re2'' re1'' sle1' sle1'' sle2' sle2'' -(cmp_slopesNC e1).
rewrite !oppr_lte0 !oppr_gte0 => -[]D' D []C' C []B' B []A' A.
rewrite /below_alt/edge_below.
have [ | difslope] := boolP(cmp_slopes e1 e2 == 0); first by right.
left; rewrite D' C' A B A' B' D C -!leNgt orbC=> /orP; rewrite andbC !orbb.
by move/le_anti/esym/eqP; rewrite (negbTE difslope).
Qed.

Lemma order_below_viz_vertical low_e high_e p pl ph:
valid_edge low_e p -> valid_edge high_e p ->
vertical_intersection_point p low_e = Some pl ->
vertical_intersection_point p high_e = Some ph ->
low_e <| high_e ->
p_y pl <= p_y ph.
Proof.
move => lowv highv vert_pl vert_ph luh.
have := intersection_on_edge vert_pl => [][] poel lx_eq.
have := intersection_on_edge vert_ph => [][] poeh hx_eq.
have plhv: valid_edge high_e pl.
  move : highv.
  by rewrite /valid_edge/generic_trajectories.valid_edge -lx_eq.
have pllv: valid_edge low_e pl.
  move : lowv.
  by rewrite /valid_edge/generic_trajectories.valid_edge -lx_eq.
have := order_edges_viz_point' pllv  plhv luh.
rewrite under_onVstrict // poel /= => [] /= plinfh.
have pluh: pl <<= high_e .
  by apply plinfh.
have px_eq : p_x pl = p_x ph.
  by rewrite -lx_eq -hx_eq /=.
by rewrite -(under_edge_lower_y px_eq poeh).
Qed.

Lemma edge_below_equiv p (s : pred edge) :
  {in s, forall e, valid_edge e p && (p_x p < p_x (right_pt e))} ->
  {in s &, no_crossing} ->
  {in s & , forall e1 e2: edge, (e1 <| e2) = pedge_below p e1 e2}.
Proof.
move=> val noc e1 e2.
move=> /[dup] e1in /val /andP[] /[dup] ve1 /exists_point_valid [p1 p1P] re1.
move: (p1P); rewrite (pvertE ve1) =>/esym[] p1q.
move: (ve1)=> /pvert_on; rewrite -p1q=> on1.
move=> /[dup] e2in /val /andP[] /[dup] ve2 /exists_point_valid [p2 p2P] re2.
move: (p2P); rewrite (pvertE ve2) =>/esym[] p2q.
move: (ve2)=> /pvert_on; rewrite -p2q=> on2; rewrite /pedge_below.
have p1p2 : p_x p1 = p_x p2 by rewrite p1q p2q.
have [vylt /= | vylt' /= | vyq] := ltrgtP.
- case: (noc e1 e2 e1in e2in) => // abs.
  have := order_below_viz_vertical ve2 ve1 p2P p1P abs; rewrite leNgt.
  by rewrite p1q p2q /= vylt.
- have re1' : p_x p1 < p_x (right_pt e1) by rewrite p1q.
  have p2u : p2 <<< e1.
    by rewrite (strict_under_edge_lower_y (esym p1p2)); rewrite // p2q p1q.
  have p1a : p1 >>> e2.
    by rewrite (under_edge_lower_y p1p2); rewrite // -ltNge p2q p1q.
  apply/negP=> /orP[|] /andP[]leftc rightc.
    by move: p1a; rewrite (point_on_edge_under _ leftc rightc) // p1q.
  move: p2u; rewrite -(negbK (_ <<< _)).
  by rewrite (point_on_edge_above _ leftc rightc) // p2q.
have pp : p1 = p2 by rewrite p1q p2q vyq.
move: (ve1) => /andP[] + _; rewrite le_eqVlt=>/orP[/eqP pleft | pmid] /=.
  have p1l : p1 = left_pt e1.
    apply/esym/eqP; rewrite pt_eqE.
    by rewrite (on_edge_same_point (left_on_edge _) on1) pleft p1q eqxx.
  move: ve2 => /andP[] + _; rewrite le_eqVlt=> /orP [/eqP pleft2 | pmid2].
    have p2l : p2 = left_pt e2.
      apply/esym/eqP; rewrite pt_eqE.
      by rewrite (on_edge_same_point (left_on_edge _) on2) pleft2 p2q eqxx.
    by apply: same_left_edge_below_slopes; rewrite -p1l pp.
  have le2ltp2 : p_x (left_pt e2) < p_x p2 by rewrite p2q.
  have [e2' [le2' re2' sle2']] := sub_edge_left on2 le2ltp2.
  have re2'e1 : right_pt e2' === e1 by rewrite re2' -pp.
  rewrite /edge_below.
  have := (contact_right_slope re2'e1) => /= -[] _; rewrite le2' sle2' => ->.
  have p2ltre2 : p_x p2 < p_x (right_pt e2) by rewrite p2q.
  have [e2'' [le2'' re2'' sle2'']] := sub_edge_right on2 p2ltre2.
  have le2''e1 : left_pt e2'' === e1 by rewrite le2'' -pp.
  have := (contact_left_slope le2''e1) => -[] _; rewrite re2'' sle2'' => ->.
  rewrite -2!leNgt.
  set W := (X in _ || X); have [ | difslope] := boolP W.
    rewrite {}/W=>/le_anti/esym=>/eqP.
    by rewrite -cmp_slopesNC oppr_eq0 orbT=> /eqP->; rewrite lexx.
  rewrite orbF -p1l pp {1}/point_under_edge underE.
  move: (on2); rewrite /point_on_edge.
  move=> /andP[] /eqP -> _; rewrite lexx /=.
  by move: (on2); rewrite -pp p1l=>/contact_left_slope=>-[].
have le1ltp1 : p_x (left_pt e1) < p_x p1 by rewrite p1q.
have [e1' [le1' re1' sle1']] := sub_edge_left on1 le1ltp1.
have re1'e2 : right_pt e1' === e2 by rewrite re1' pp.
rewrite /edge_below.
set W := (X in X || _); set W' := (X in _ || X).
have := (contact_right_slope re1'e2); rewrite le1' sle1' => /= -[] eq1 _.
have p1ltre1 : p_x p1 < p_x (right_pt e1) by rewrite p1q.
have [e1'' [le1'' re1'' sle1'']] := sub_edge_right on1 p1ltre1.
have le1''e2 : left_pt e1'' === e2 by rewrite le1'' pp.
have /= := (contact_left_slope le1''e2); rewrite re1'' sle1'' => - [] /= eq2 _.
have Weq : W = (cmp_slopes e1 e2 == 0).
  rewrite /W eq1 eq2; apply/idP/eqP; first by apply/le_anti.
  by move=> ->; rewrite lexx.
have [ | difslope /=] := boolP W.
  by rewrite /= le_eqVlt Weq => /eqP ->; rewrite eqxx.
rewrite le_eqVlt eq_sym -Weq (negbTE difslope) /=.
move: (ve2) => /andP[] + _; rewrite le_eqVlt => /orP [/eqP l2p | l2ltp].
  have /eqP p2l : left_pt e2 == p1.
    rewrite pt_eqE.
    rewrite (eqP (on_edge_same_point (left_on_edge _) on2 _)) -pp l2p p1q //=.
    by rewrite !eqxx.
  have/contact_left_slope[_ eq3] : left_pt e2 === e1 by rewrite p2l.
  move: on1=>/andP[] /eqP + _; rewrite -p2l => eq4.
  rewrite /W' eq3 lt_neqAle -cmp_slopesNC eq_sym oppr_eq0 -Weq difslope andTb.
  rewrite /point_strictly_under_edge strictE.
  by rewrite -leNgt eq4 lexx -ltNge oppr_lt0.
have xpp1 : p_x p = p_x p1 by rewrite p1q.
move: on2 l2ltp re2; rewrite -pp xpp1 => on2 l2ltp re2.
have := intersection_imp_crossing on1 on2 le1ltp1 p1ltre1 l2ltp re2=> -[[]|abs].
  by apply: noc.
by case/negP: difslope; rewrite Weq.
Qed.

Lemma edge_below_equiv' p (s : pred edge) :
  {in s, forall e, valid_edge e p && (p_x (left_pt e) < p_x p)} ->
  {in s &, no_crossing} ->
  {in s & , forall e1 e2: edge, (e1 <| e2) = pedge_below' p e1 e2}.
Proof.
move=> val noc e1 e2.
move=> /[dup] e1in /val /andP[] /[dup] ve1 /exists_point_valid [p1 p1P] le1.
move: (p1P); rewrite (pvertE ve1) =>/esym[] p1q.
move: (ve1)=> /pvert_on; rewrite -p1q=> on1.
move=> /[dup] e2in /val /andP[] /[dup] ve2 /exists_point_valid [p2 p2P] le2.
move: (p2P); rewrite (pvertE ve2) =>/esym[] p2q.
move: (ve2)=> /pvert_on; rewrite -p2q=> on2; rewrite /pedge_below'.
have p1p2 : p_x p1 = p_x p2 by rewrite p1q p2q.
have [vylt /= | vylt' /= | vyq] := ltrgtP.
- case: (noc e1 e2 e1in e2in) => // abs.
  have := order_below_viz_vertical ve2 ve1 p2P p1P abs; rewrite leNgt.
  by rewrite p1q p2q /= vylt.
- have le1' : p_x (left_pt e1) < p_x p1 by rewrite p1q.
  have p2u : p2 <<< e1.
    by rewrite (strict_under_edge_lower_y (esym p1p2)); rewrite // p2q p1q.
  have p1a : p1 >>> e2.
    by rewrite (under_edge_lower_y p1p2); rewrite // -ltNge p2q p1q.
  apply/negP=> /orP[|] /andP[]leftc rightc.
    by move: p1a; rewrite (point_on_edge_under _ leftc rightc) // p1q.
  move: p2u; rewrite -(negbK (_ <<< _)).
  by rewrite (point_on_edge_above _ leftc rightc) // p2q.
have pp : p1 = p2 by rewrite p1q p2q vyq.
move: (ve1) => /andP[] _ +; rewrite le_eqVlt=>/orP[/eqP pright | pmid] /=.
  have p1r : p1 = right_pt e1.
    apply/eqP; rewrite pt_eqE.
    by rewrite (on_edge_same_point on1 (right_on_edge _)) -pright p1q eqxx.
  move: ve2 => /andP[] _; rewrite le_eqVlt=> /orP [/eqP pright2 | pmid2].
    have p2l : p2 = right_pt e2.
      apply/eqP; rewrite pt_eqE.
      by rewrite (on_edge_same_point on2 (right_on_edge _)) -pright2 p2q eqxx.
    by apply: same_right_edge_below_slopes; rewrite -p1r pp.
  have p2ltre2 : p_x p2 < p_x (right_pt e2) by rewrite p2q.
  have [e2' [le2' re2' sle2']] := sub_edge_right on2 p2ltre2.
  have le2'e1 : left_pt e2' === e1 by rewrite le2' -pp.
  rewrite /edge_below.
  have := (contact_left_slope le2'e1) => /= -[] _; rewrite re2' sle2' => ->.
  have le2ltp2 : p_x (left_pt e2) < p_x p2 by rewrite p2q.
  have [e2'' [le2'' re2'' sle2'']] := sub_edge_left on2 le2ltp2.
  have re2''e1 : right_pt e2'' === e1 by rewrite re2'' -pp.
  have := (contact_right_slope re2''e1) => -[] _; rewrite le2'' sle2'' => ->.
  rewrite -2!leNgt.
  set W := (X in _ || X); have [ | difslope] := boolP W.
    rewrite {}/W=>/le_anti/esym/eqP.
    by rewrite -cmp_slopesNC oppr_eq0 orbT=> /eqP->; rewrite lexx.
  rewrite orbF -p1r pp {2}/point_under_edge underE.
   move: (on2); rewrite /point_on_edge.
  move=> /andP[] /eqP -> _; rewrite lexx andbT.
  by move: (on2); rewrite -pp p1r=>/contact_right_slope=>-[].
have p1ltre1 : p_x p1 < p_x (right_pt e1) by rewrite p1q.
have [e1' [le1' re1' sle1']] := sub_edge_right on1 p1ltre1.
have le1'e2 : left_pt e1' === e2 by rewrite le1' pp.
rewrite /edge_below.
set W := (X in X || _); set W' := (X in _ || X).
have := (contact_left_slope le1'e2); rewrite re1' sle1' => /= -[] eq1 _.
have le1ltp1 : p_x (left_pt e1) < p_x p1 by rewrite p1q.
have [e1'' [le1'' re1'' sle1'']] := sub_edge_left on1 le1ltp1.
have re1''e2 : right_pt e1'' === e2 by rewrite re1'' pp.
have /= := (contact_right_slope re1''e2); rewrite le1'' sle1'' => - [] /= eq2 _.
have Weq : W = (cmp_slopes e1 e2 == 0).
  rewrite /W eq1 eq2; apply/idP/eqP; first by apply/le_anti.
  by move=> ->; rewrite lexx.
have [ | difslope /=] := boolP W.
  by rewrite /= le_eqVlt Weq => /eqP ->; rewrite eqxx.
rewrite le_eqVlt -Weq (negbTE difslope) /=.
move: (ve2) => /andP[] _; rewrite le_eqVlt => /orP [/eqP r2p | pltr2].
  have /eqP p2r : right_pt e2 == p1.
    rewrite pt_eqE.
    rewrite -(eqP (on_edge_same_point on2 (right_on_edge _) _)) -pp -r2p p1q //=.
    by rewrite !eqxx.
  have/contact_right_slope[_ eq3] : right_pt e2 === e1 by rewrite p2r.
  move: on1=>/andP[] /eqP + _; rewrite -p2r => eq4.
  rewrite /W' eq3 lt_neqAle -cmp_slopesNC oppr_eq0 -Weq difslope andTb.
  by rewrite /W' /point_strictly_under_edge strictE
      eq4 ltxx andbT -ltNge oppr_gt0.
have xpp1 : p_x p = p_x p1 by rewrite p1q.
move: on2 pltr2 le2; rewrite -pp xpp1 => on2 pltr2 le2.
have := intersection_imp_crossing on1 on2 le1ltp1 p1ltre1 le2 pltr2=> -[[]|abs].
  by apply: noc.
by case/negP: difslope; rewrite Weq.
Qed.

Lemma pedge_below_trans p: transitive (pedge_below p).
Proof.
move=> e2 e1 e3; rewrite /pedge_below.
move=>/orP[v12 | /andP [y12 s12]] /orP[v23 | /andP[y23 s23]].
- by rewrite (lt_trans v12 v23).
- by rewrite -(eqP y23) v12.
- by rewrite (eqP y12) v23.
rewrite orbC (eqP y12) y23.
move: s12 s23; rewrite !cmp_slopesE !sgr_ge0 !subr_ge0=> s12 s23.
by rewrite (le_trans s12 s23).
Qed.

Lemma pedge_below_trans' p: transitive (pedge_below' p).
Proof.
move=> e2 e1 e3; rewrite /pedge_below'.
move=>/orP[v12 | /andP [y12 s12]] /orP[v23 | /andP[y23 s23]].
- by rewrite (lt_trans v12 v23).
- by rewrite -(eqP y23) v12.
- by rewrite (eqP y12) v23.
rewrite orbC (eqP y12) y23.
move: s12 s23; rewrite !cmp_slopesE !sgr_le0.
rewrite (subr_le0 (slope e1)) (subr_le0 (slope e2)) (subr_le0 (slope e1)).
by move=> s12 s23; rewrite (le_trans s23 s12).
Qed.

Lemma edge_below_trans p (s : pred edge) :
  {in s, forall e, p_x p < p_x (right_pt e)} \/ 
  {in s, forall e, p_x (left_pt e) < p_x p} ->
  {in s, forall e, valid_edge e p} -> {in s &, no_crossing} ->
  {in s & & , transitive edge_below}.
Proof.
move=> [rbound | lbound] vals noc e2 e1 e3 e2in e1in e3in.
  have valb : {in s, forall e, valid_edge e p && (p_x p < p_x (right_pt e))}.
    by move=> e ein; apply/andP; split;[apply: vals | apply: rbound].
  rewrite (edge_below_equiv valb noc) // (edge_below_equiv valb noc) //.
  rewrite (edge_below_equiv valb noc) //.
  by apply: pedge_below_trans.
have valb : {in s, forall e, valid_edge e p && (p_x (left_pt e) < p_x p)}.
  by move=> e ein; apply/andP; split;[apply: vals | apply: lbound].
rewrite (edge_below_equiv' valb noc) // (edge_below_equiv' valb noc) //.
rewrite (edge_below_equiv' valb noc) //.
by apply: pedge_below_trans'.
Qed.


Lemma left_pt_above g : left_pt g >>= g.
Proof.
rewrite /point_strictly_under_edge strictE.
rewrite (eqP (proj1 (area3_two_points _ _))).
by rewrite ltxx.
Qed.

Lemma right_pt_above g : right_pt g >>= g.
Proof.
rewrite /point_strictly_under_edge strictE.
by rewrite (eqP (proj1 (proj2 (area3_two_points _ _)))) ltxx.
Qed.

Lemma left_pt_below g : left_pt g <<= g.
Proof.
rewrite /point_under_edge underE (eqP (proj1 (area3_two_points _ _))).
by rewrite lexx.
Qed.

Lemma right_pt_below g : right_pt g <<= g.
Proof.
rewrite /point_under_edge underE.
by rewrite (eqP (proj1 (proj2 (area3_two_points _ _)))) lexx.
Qed.

Lemma under_pvert_y (p : pt) (e : edge) :
  valid_edge e p -> (p <<= e) = (p_y p <= pvert_y p e).
Proof.
move=> val.
have xs : p_x p = p_x (Bpt (p_x p) (pvert_y p e)) by [].
have one : Bpt (p_x p) (pvert_y p e) === e by apply: pvert_on.
by rewrite (under_edge_lower_y xs one).
Qed.

Lemma strict_under_pvert_y (p : pt) (e : edge) :
  valid_edge e p -> (p <<< e) = (p_y p < pvert_y p e).
Proof.
move=> val.
have xs : p_x p = p_x (Bpt (p_x p) (pvert_y p e)) by [].
have one : Bpt (p_x p) (pvert_y p e) === e by apply: pvert_on.
by rewrite (strict_under_edge_lower_y xs one).
Qed.

Lemma same_x_valid (p1 p2 : pt) (g : edge) :
  p_x p1 == p_x p2 -> valid_edge g p1 = valid_edge g p2.
Proof.
by move=> /eqP xs; rewrite /valid_edge/generic_trajectories.valid_edge xs.
Qed.

Lemma same_pvert_y (p1 p2 : pt) (g : edge) :
  valid_edge g p1 ->
  p_x p1 == p_x p2 -> pvert_y p1 g = pvert_y p2 g.
Proof.
move=> vg xs; apply/eqP.
move: (vg) ; rewrite (same_x_valid _ xs) => vg2.
by have := on_edge_same_point (pvert_on vg) (pvert_on vg2) xs.
Qed.

Lemma edge_below_pvert_y g1 g2 p :
  valid_edge g1 p -> valid_edge g2 p ->
  g1 <| g2 -> pvert_y p g1 <= pvert_y p g2.
Proof.
move=> v1 v2 g1g2.
have := pvert_on v1; set p' := Bpt _ _ => p'on.
have/esym := @same_x_valid p p' g1 (eqxx _); rewrite v1 => v'1.
have/esym := @same_x_valid p p' g2 (eqxx _); rewrite v2 => v'2.
have := order_edges_viz_point' v'1 v'2 g1g2.
rewrite (under_onVstrict v'1) p'on => /(_ isT).
by rewrite under_pvert_y //.
Qed.

Lemma pvert_y_edge_below g1 g2 p :
  valid_edge g1 p -> valid_edge g2 p ->
  pvert_y p g1 < pvert_y p g2 -> ~~ (g2 <| g1).
Proof.
move=> v1 v2 cmp; apply/negP=> g2g1.
have := edge_below_pvert_y v2 v1 g2g1.
by rewrite leNgt cmp.
Qed.

Lemma edges_partition_strictly_above p g1 g2 s1 s2:
  all (valid_edge^~ p) (s1 ++ g1 :: g2 :: s2) ->
  sorted edge_below (s1 ++ g1 :: g2 :: s2) ->
  p >>= g1 -> p <<< g2 ->
  {in rcons s1 g1 &  g2 :: s2, forall g g', ~~ (g' <| g)}.
Proof.
move=> aval pth pg1 pg2.
have vg1 : valid_edge g1 p.
  by apply: (allP aval); rewrite !(mem_cat, inE) eqxx ?orbT.
have vg2 : valid_edge g2 p.
  by apply: (allP aval); rewrite !(mem_cat, inE) eqxx ?orbT.
have pg1y : pvert_y p g1 <= p_y p by rewrite leNgt -strict_under_pvert_y.
have pg2y : p_y p < pvert_y p g2 by rewrite -strict_under_pvert_y.
have g1g2 : pvert_y p g1 < pvert_y p g2 by apply: (le_lt_trans pg1y).
have mp : {in s1++ g1 :: g2 :: s2 &,
           {homo (pvert_y p) : x y / x <| y >-> x <= y}}.
    move=> u v /(allP aval) vu /(allP aval) vv uv.
    by apply: edge_below_pvert_y vu vv uv.
have sb2 : {subset [:: g1, g2 & s2] <= (s1 ++ [:: g1, g2 & s2])}.
  by move=> u uin; rewrite mem_cat uin orbT.
have g2s2y : {in g2 :: s2, forall g, pvert_y p g1 < pvert_y p g}.
  move=> g; rewrite inE => /orP[/eqP -> //| gin].
  have pthy : sorted <=%R [seq pvert_y p h | h <- g2 :: s2].
    apply: (homo_path_in mp); last first.
      move: pth.
      rewrite (_ : s1 ++ _ = (s1 ++[:: g1]) ++ g2 :: s2); last first.
        by rewrite /= -!catA.
      by move/sorted_catW=> /andP[].
    apply: (sub_all sb2).
    by apply/allP => z; rewrite !(mem_cat, inE) => /orP[] ->; rewrite ?orbT.
  have /(allP aval) gin' : g \in (s1 ++ [:: g1, g2 & s2]).
    by rewrite mem_cat !inE gin ?orbT.
  move: pthy; rewrite /= (path_sortedE le_trans) => /andP[] /allP.
  have giny : pvert_y p g \in [seq pvert_y p h | h <- s2] by apply: map_f.
  by move=> /(_ _ giny) => /(lt_le_trans g1g2).
have sb1 : {subset rcons s1 g1 <= s1 ++ [:: g1, g2 & s2]}.
  by move=> x; rewrite mem_rcons mem_cat !inE => /orP[] ->; rewrite ?orbT.
have s1g1y : {in rcons s1 g1, forall g, pvert_y p g <= pvert_y p g1}.
  move=> g; rewrite mem_rcons inE => /orP[/eqP ->| gin].
    apply: le_refl.
  case s1eq : s1 gin => [// | init s1']; rewrite -s1eq => gin.
  have pthy : sorted <=%R [seq pvert_y p h | h <- rcons s1 g1].
    rewrite s1eq /=; apply: (homo_path_in mp); last first.
      move: pth; rewrite s1eq/=.
      rewrite (_ : s1' ++ _ = (s1' ++ [:: g1]) ++ g2 :: s2); last first.
        by rewrite -catA.
      by rewrite cat_path cats1 => /andP[].
    by apply: (sub_all sb1); rewrite s1eq; apply: allss.
  have [s' [s'' s'eq]] : exists s' s'', s1 = s' ++ g :: s''.
    by move: gin=> /splitPr [s' s'']; exists s', s''.
  have dc : rcons (init :: s1') g1 = (s' ++ [:: g]) ++ rcons s'' g1.
   by rewrite -s1eq s'eq -!cats1 /= -?catA.
  case s'eq2 : s' => [ | init' s'2].
    move: pthy; rewrite s1eq dc s'eq2 /= (path_sortedE le_trans)=> /andP[].
    move=> /allP/(_ (pvert_y p g1)) + _; apply.
    by rewrite map_f // mem_rcons inE eqxx.
  move: pthy; rewrite s1eq dc s'eq2 /= map_cat cat_path => /andP[] _.
  rewrite !map_cat cats1 last_rcons (path_sortedE le_trans) => /andP[] + _.
  move=> /allP/(_ (pvert_y p g1)); apply.
  by apply: map_f; rewrite mem_rcons inE eqxx.
move=> g g' /[dup]gin /s1g1y giny /[dup] g'in /g2s2y g'iny; apply/negP=> g'g.
have vg : valid_edge g p by apply: (allP aval); apply: sb1.
have vg' : valid_edge g' p.
  by apply: (allP aval); apply: sb2; rewrite inE g'in orbT.
have:= edge_below_pvert_y vg' vg g'g; rewrite leNgt.
by rewrite (le_lt_trans _ g'iny).
Qed.

Lemma edge_below_from_point_above g1 g2 p:
  below_alt g1 g2 -> valid_edge g1 p -> valid_edge g2 p ->
  p >>= g1 -> p <<< g2 -> g1 <| g2.
Proof.
move=>[] //= g2g1 v1 v2 ab bel.
have := order_edges_strict_viz_point' v2 v1 g2g1 bel.
by rewrite (negbTE ab).
Qed.

Lemma edge_below_from_point_under g1 g2 p:
  below_alt g1 g2 -> valid_edge g1 p -> valid_edge g2 p ->
  p <<= g1 -> p >>> g2 -> g2 <| g1.
Proof.
move=>/below_altC[] //=g1g2 v1 v2 bel ab.
have := order_edges_viz_point' v1 v2 g1g2 bel.
by rewrite (negbTE ab).
Qed.

Lemma transport_below_edge r p e e':
  below_alt e e' ->
  valid_edge e r -> valid_edge e' r ->
  valid_edge e p -> valid_edge e' p ->
  pvert_y r e < pvert_y r e' ->
  p <<< e -> p <<< e'.
Proof.
move=> noc vr vr' vp vp' cmp pbelow.
have ebe'0 := pvert_y_edge_below vr vr' cmp.
have ebe' : e <| e' by case: noc ebe'0=> [// | -> ].
by apply:(order_edges_strict_viz_point' vp vp').
Qed.

Lemma transport_above_edge r p e e':
  below_alt e e' ->
  valid_edge e r -> valid_edge e' r ->
  valid_edge e p -> valid_edge e' p ->
  pvert_y r e < pvert_y r e' ->
  p >>> e' -> p >>> e.
Proof.
move=> noc vr vr' vp vp' cmp pabove.
have ebe'0 := pvert_y_edge_below vr vr' cmp.
have ebe' : e <| e' by case: noc ebe'0=> [// | -> ].
apply/negP=> abs.
by move: pabove; rewrite (order_edges_viz_point' vp vp').
Qed.

Lemma path_edge_below_pvert_y bottom s p :
  all (valid_edge^~ p) (bottom :: s) ->
  path edge_below bottom s -> path <=%R (pvert_y p bottom)
  [seq pvert_y p e | e <- s].
Proof.
move=> aval.
have hp : {in bottom :: s &,
         {homo (pvert_y p) : u v / edge_below u v >-> u <= v}}.
  move=> u v /(allP aval) vu /(allP aval) vv.
    by apply: edge_below_pvert_y vu vv.
by move/(homo_path_in hp)=> /(_ (allss (bottom :: s))).
Qed.

Lemma edge_below_gap bottom s s' le r p g g' : 
{in bottom::rcons s le ++ s' &, no_crossing} ->
all (valid_edge^~ r) (bottom :: rcons s le ++ s') ->
path edge_below bottom (rcons s le ++ s') ->
r >>> le -> r <<= g' ->
g \in rcons s le ->
valid_edge g p ->
p >>> g' ->
g' \in s' ->
valid_edge g' p -> p >>> g.
Proof.
move=> noc aval pth rabove rbelow gin vp pabove g'in vp'.
have gin2 : g \in bottom :: rcons s le ++ s'.
  by move: gin; rewrite !(inE, mem_rcons, mem_cat)=>/orP[] ->; rewrite ?orbT.
have g'in2 : g' \in bottom :: rcons s le ++ s'.
  by move: g'in; rewrite !(inE, mem_rcons, mem_cat)=> ->; rewrite ?orbT.
have lein : le \in bottom :: rcons s le ++ s'.
  by rewrite !(inE, mem_cat, mem_rcons) eqxx ?orbT.
have vl : valid_edge le r by apply: (allP aval).
have vr : valid_edge g r by apply: (allP aval).
have vr' : valid_edge g' r by apply: (allP aval).
have noc' : below_alt g g' by apply: noc.
apply: (transport_above_edge noc' vr) => //.
have aval' : all (valid_edge^~ r) (bottom :: rcons s le).
  apply/allP=> u uin; apply: (allP aval).
  move: uin; rewrite !(inE, mem_cat, mem_rcons).
  by move=> /orP[| /orP[]] ->; rewrite ?orbT.
have aval'' : all (valid_edge^~ r) (le :: s'). 
  apply/allP=> u uin; apply: (allP aval).
  move: uin; rewrite !(inE, mem_cat, mem_rcons).
  by move=> /orP[] ->; rewrite ?orbT.
have tr : transitive (relpre (pvert_y r) <=%R).
  by move=> y x z; rewrite /=; apply: le_trans.
have le_g' : pvert_y r le < pvert_y r g'.
  have le_r : pvert_y r le < p_y r by rewrite ltNge -under_pvert_y.
  have r_g' : p_y r <= pvert_y r g' by rewrite -under_pvert_y.
  by apply: lt_le_trans le_r r_g'.
have g_le : pvert_y r g <= pvert_y r le.
  move: gin; rewrite mem_rcons inE=> /orP[/eqP -> |gin]; first by rewrite lexx.
  have gin' : g \in (bottom :: s) by rewrite inE gin orbT.
  move: pth; rewrite cat_path last_rcons => /andP[] + _.
  move=> /= /path_edge_below_pvert_y => /(_ _ aval').
  rewrite path_map.
  rewrite -[path _ _ _]/(sorted _ (rcons (bottom :: s) le)).
  by move=> /(sorted_rconsE tr)/allP/(_ _ gin') /=.
by apply: le_lt_trans le_g'.
Qed.

Lemma edge_above_gap bottom s s' he r p g g' : 
{in bottom::rcons s he ++ s' &, no_crossing} ->
all (valid_edge^~ r) (bottom :: rcons s he ++ s') ->
path edge_below bottom (rcons s he ++ s') ->
r <<< he -> r >>= g ->
g \in rcons s he ->
valid_edge g p ->
p <<< g ->
g' \in s' ->
valid_edge g' p -> p <<< g'.
Proof.
move=> noc aval pth rabove rbelow gin vp pabove g'in vp'.
have gin2 : g \in bottom :: rcons s he ++ s'.
  by move: gin; rewrite !(inE, mem_rcons, mem_cat)=>/orP[] ->; rewrite ?orbT.
have g'in2 : g' \in bottom :: rcons s he ++ s'.
  by move: g'in; rewrite !(inE, mem_rcons, mem_cat)=> ->; rewrite ?orbT.
have hein : he \in bottom :: rcons s he ++ s'.
  by rewrite !(inE, mem_cat, mem_rcons) eqxx ?orbT.
have vl : valid_edge he r by apply: (allP aval).
have vr : valid_edge g r by apply: (allP aval).
have vr' : valid_edge g' r by apply: (allP aval).
have noc' : below_alt g g' by apply: noc.
apply: (transport_below_edge noc' vr) => //.
have aval' : all (valid_edge^~ r) (bottom :: rcons s he).
  apply/allP=> u uin; apply: (allP aval).
  move: uin; rewrite !(inE, mem_cat, mem_rcons).
  by move=> /orP[| /orP[]] ->; rewrite ?orbT.
have aval'' : all (valid_edge^~ r) (he :: s'). 
  apply/allP=> u uin; apply: (allP aval).
  move: uin; rewrite !(inE, mem_cat, mem_rcons).
  by move=> /orP[] ->; rewrite ?orbT.
have tr : transitive (relpre (pvert_y r) <=%R).
  by move=> y x z; rewrite /=; apply: le_trans.
have g_he : pvert_y r g < pvert_y r he.
  have r_he : p_y r < pvert_y r he by rewrite -strict_under_pvert_y.
  have g_r : pvert_y r g <= p_y r by rewrite leNgt -strict_under_pvert_y.
  by apply: le_lt_trans g_r r_he.
have he_g' : pvert_y r he <= pvert_y r g'.
  move: pth; rewrite cat_path last_rcons => /andP[] _.
  move=> /= /path_edge_below_pvert_y => /(_ _ aval'').
  rewrite path_map /=.
  by rewrite (path_sortedE tr) => /andP[] /allP/(_ _ g'in) /=.
by apply: lt_le_trans he_g'.
Qed.

Definition non_inner (g : edge) (p : pt) :=
  p === g -> p = left_pt g \/ p = right_pt g.

End working_context.

Notation "p '<<=' e" := (point_under_edge p e)( at level 70, no associativity).
Notation "p '<<<' e" := (point_strictly_under_edge p e)(at level 70, no associativity).

Notation "p '>>=' e" := (~~(point_strictly_under_edge p e))( at level 70, no associativity).
Notation "p '>>>' e" := (~~(point_under_edge p e))(at level 70, no associativity).
Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).
Notation "e1 '<|' e2" := (edge_below e1 e2)( at level 70, no associativity).
