(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr Yves.Bertot Frederique.Guilhot    *)
(*  &all    Inria, 2006                                      *)
(*************************************************************)

Require Export Reals.
Require Export NArith.
Require Export NAux.
Require Import Qabs. Require Import One_dim. Import Utils.
Import CAD_types.
Require Export Fourier.

Module Bernstein_utils(Q:RAT_STRUCT).

Module ONE_DIM := MK_ONE_DIM Q.

Import Q. Import ONE_DIM. Import ONE_DIM.QFUNS.

Notation "x ^ y" := (Pol_pow x y) : P_scope.

Open Scope N_scope.

Notation "x - y" := (Nminus x y) : N_scope.

Definition Nle (x y:N) := ~(x?=y = Gt).
Definition Nlt (x y:N) := x?=y = Lt.

Notation "x <= y" := (Nle x y) : N_scope.
Notation "x <= y <= z" := (Nle x y/\Nle y z) : N_scope.
Notation "x <= y < z" := (Nle x y/\Nlt y z) : N_scope.
Notation "x < y <= z" := (Nlt x y/\Nle y z) : N_scope.
Notation "x < y < z" := (Nlt x y/\Nlt y z) : N_scope.
Notation "x < y" := (Nlt x y) : N_scope.

Theorem Nle_refl : forall x, x <= x.
Admitted.

Theorem Nle_0_n : forall x, 0 <= x.
intros x; case x; compute; intros; discriminate.
Qed.

Theorem Nle_trans : forall x y z, x <= y -> y <= z -> x <= z.
Admitted.

Theorem Nle_plus_compat : forall x y z t, x <= y -> z <= t -> x + z <= y + t.
Admitted.

Theorem Nle_0_plus_compat :
  forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Admitted.

Theorem Nle_plus_r :
  forall x y, x <= x + y.
Admitted.

Theorem Nle_plus_l :
  forall x y, x <= y + x.
Admitted.

Theorem N_le_plus_minus :
   forall n m:N, n <= m -> m = (n+(m-n))%N.
Admitted.
    
Definition Ndiv (x y:N) : N.
Admitted.

Notation "x / y" := (Ndiv x y) : N_scope.

Theorem N_mult_div : forall x y, x <> 0 -> (x*y)/x = y.
Admitted.

Theorem rbinomial_pascal1 : forall n m, 
  rbinomial (n+1) (m+1) = rbinomial n m +r rbinomial n (m+1).
Admitted.

Theorem binomial_pascal2 :
  forall n m: N, n <= m -> rbinomial n m = 1#1.
Admitted.

Open Scope P_scope.

(* Hoho, this equality should be a rational equality. *)
Theorem Pol_eval_plus :
  forall p q x, Pol_eval (p + q) x = (Pol_eval p x) +r (Pol_eval q) x.
Admitted.

Theorem Pol_eval_mult :
  forall p q x, Pol_eval (p * q) x = (Pol_eval p x *r Pol_eval q x)%Q.
Admitted.

Theorem Pol_eval_constant :
  forall a x, Pol_eval (Pc a) x == a.
Admitted.

Theorem Pol_eval_X :
  forall x, Pol_eval X x = x.
Admitted.

Definition bernstein_pol (l r:Rat)(i p:N) : Pol :=
  Pol_mul_Rat
   ((X - Pol_of_Rat l)^i * (Pol_of_Rat r - X)^(p - i))%P
   (rbinomial p i /r (r -r l^p)).

Theorem bernstein_degree :
  forall c d i p, c<>d -> i <= p -> Pol_deg (bernstein_pol c d i p) = p.
Admitted.

Theorem bernstein_pos :
  forall c d i p x, (0<= i <= p)%N -> 
     (c < x < d)%Q -> (r0 < Pol_eval (bernstein_pol c d i p) x)%Q.
Admitted.

Theorem bernstein_val_first_bound1 :
  forall c d p, (c < d)%Q -> Pol_eval (bernstein_pol c d 0 p) c = 1#1.
Admitted.

Theorem bernstein_val_first_bound2 :
  forall c d i p, 
    (c < d)%Q -> (0 < i <= p)%N -> Pol_eval (bernstein_pol c d i p) c = r0.
Admitted.

Theorem bernstein_val_snd_bound1 :
  forall c d p, (c < d)%Q -> Pol_eval (bernstein_pol c d p p) d = 1#1.
Admitted.

Theorem bernstein_val_snd_bound2 :
  forall c d i p, 
     (c < d)%Q -> (0 <= i < p)%N -> Pol_eval (bernstein_pol c d i p) d = r0.
Admitted.

Fixpoint lcb_aux (c d:Rat)(p:N)(i:N)(l:list Coef) {struct l} : Pol :=
  match l with
    nil => P0
  | b::bs => Pc b * (bernstein_pol c d i p) + lcb_aux c d p (i+1)%N bs
  end.

Definition linear_comb_bernstein c d p l :=
  lcb_aux c d p 0 l.


Fixpoint Nlength (A:Set)(l:list A) {struct l}: N :=
  match l with nil => 0 | a::tl => (Nlength A tl + 1)%N end.

Implicit Arguments Nlength.

Theorem lcb_aux_pos :
  forall c d p l i x,
    (c < x < d)%Q -> (0 <= i)%N -> (i + Nlength l <= p)%N ->
    (forall a, In a l -> r0 <= a)%Q ->
    (r0 <= Pol_eval (lcb_aux c d p i l) x)%Q.
intros c d p l; elim l.
intros i x Hint _ _ _.
simpl.
apply rat_le_refl.
intros a tl Hrec i x Hint. simpl (Nlength (a::tl)).
intros Hipos Hi Hpos.
assert (Hi' : ((i+1)+Nlength tl <= p)%N).
replace ((i+1)+Nlength tl)%N with (i+(Nlength tl + 1))%N.
assumption.
rewrite <- Nplus_assoc; rewrite (Nplus_comm 1); trivial.
assert (Hpos' : (forall a, In a tl -> r0 <= a)%Q).
intros a' Hin; apply Hpos;right;exact Hin.
simpl.
rewrite Pol_eval_plus.
rewrite Pol_eval_mult.
match goal with |- (r0 <= ?x)%Q => apply rat_le_RatEq with (r0 +r r0) (x) end.
apply RatEq_sym; apply Rat_plus_0_right.
apply Rat_plus_le_compat.
match goal with |- (r0 <= ?x)%Q => apply rat_le_RatEq with (r0 *r r0)%Q (x) end.
apply RatEq_sym; apply Rat_mult_0_right.
apply Rat_mult_le_compat.
match goal with |- (r0 <= ?x)%Q => apply rat_le_RatEq with r0 a end.
apply RatEq_refl.
apply Hpos; left;auto.
apply RatEq_sym.
apply Pol_eval_constant.
split.
apply rat_le_refl.
apply rat_lt_le.
apply bernstein_pos.
split.
assumption.
apply Nle_trans with (i + (Nlength tl + 1))%N.
apply Nle_plus_r.
assumption.
assumption.
apply RatEq_refl.
apply Hrec.
assumption.
apply Nle_trans with i.
assumption.
apply Nle_plus_r.
rewrite <- Nplus_assoc; rewrite (Nplus_comm 1).
assumption.
intros a' Hin; apply Hpos; right; exact Hin.
apply RatEq_refl.
Qed.

Close Scope N_scope.

Theorem Pol_bound : 
  forall P: Pol, forall c d, exists a,
  forall x, c < x < d -> rabs_val (Pol_eval P x) < a.
Admitted.

Theorem non_zero_least_coeff :
  forall P: Pol, P <> P0 ->
    exists c, ~c == r0  /\
    exists k, exists Q, P = Pc c*X^k + X^(k+1)*Q.
Admitted.

Theorem Ptranslate_eval :
  forall P c x, Pol_eval (Ptranslate P c) x = Pol_eval P (x -r c).
Admitted.


Theorem rabs_le : forall x, r0 <= rabs_val x.
Admitted.

Theorem rabs_val_non_zero_lt : forall x, ~x==r0 -> r0 < rabs_val x.
Admitted.

Theorem rmin_le_l : forall a b, rmin a b <= a.
Admitted.

Theorem rmin_le_r : forall a b, rmin a b <= b.
Admitted.


Lemma zero_le_one_half : r0 < 1#2.
Admitted.

(*
Theorem Qlt_plus_compat_le :
    forall a b c d:Q, a <= c -> b < d -> a + b < c + d.
intros.
apply Rlt_Qlt.
repeat rewrite Q2R_plus.
apply Rplus_le_lt_compat.
apply Qle_Rle; assumption.
apply Qlt_Rlt; assumption.
Qed.

Theorem Qlt_plus_pos : forall a b : Q, r0 < b -> a < a + b.
intros a b Hpos.
setoid_rewrite <- (Qzero_right a).
apply Qlt_plus_compat_le.
setoid_rewrite Qzero_right.
apply Qle_refl.
assumption.
Qed.

Theorem Qlt_mult_compat_l :
   forall x y z, r0 < z -> x < y -> z*x < z*y.
intros.
apply Rlt_Qlt.
repeat rewrite Q2R_mult.
apply Rmult_lt_compat_l.
assert (Heq0 : 0%R = Q2R(0#1)).
compute;auto with real.
rewrite Heq0.
apply Qlt_Rlt;assumption.
apply Qlt_Rlt;assumption.
Qed.


Theorem Qdiv_0_lt : forall x, 0#1 < x ->  0#1 <  / x.
intros x H.
apply Rlt_Qlt.
rewrite Q2R_inv.
assert (eq0 : (Q2R (0#1) = 0)%R).
compute.
field.
auto with real.

rewrite eq0.
apply Rinv_0_lt_compat.
rewrite <- eq0.
apply Qlt_Rlt.
assumption.

intros Heq.
elim (Qlt_not_eq _ _ H).
auto with qarith.
Qed.

Lemma add_half_rabs_non_zero_lt :
  forall a b c, ~ b == 0#1 -> 0#1 < c -> a < a + 1#2*(rabs_val b/c).
intros a b c Hbnonz Hcpos.
apply Qlt_plus_pos.
assert (Heqmult : 0#1 == 1#2*0#1).
compute; trivial.
setoid_rewrite Heqmult.
apply Qlt_mult_compat_l.
compute;trivial.
assert (Heqmult2 : 0#1 == rabs_val b*0#1).
unfold Qeq, Qmult, Qnum; ring.
setoid_rewrite Heqmult2.
unfold Qdiv.
apply Qlt_mult_compat_l.
apply rabs_val_non_zero_lt.
assumption.
apply Qdiv_0_lt.
assumption.
Qed.

*)

Theorem Ptranslate_non_zero :
  forall P c, P <> P0 -> Ptranslate P c <> P0.
Admitted.

Definition N_eq_dec : forall x y:N,{x=y}+{x<>y}.
Admitted.

Theorem le_rmin :
  forall a b c, a <= b -> a <= c -> a <= rmin b c.
Admitted.

Theorem lt_rmin :
  forall a b c, a < b -> a < c -> a < rmin b c.
Admitted.

Lemma c_le_form :
   forall c v A, r0 < A -> ~ v == r0 -> c < c+r 1#2 *r rabs_val v /r A.
Admitted.

Theorem rat_le_lt_trans :
  forall x y z:Rat, x <= y -> y < z -> x < z.
Admitted.

Theorem middle_in :
  forall x y, x < y -> x < (x +r y) /r 2#1 < y.
Admitted.

Theorem non_zero_div : forall x y, ~x==r0 -> ~y==r0 -> ~x/r y== r0.
Admitted.

Theorem non_zero_frac : forall a b, (a<>0)%Z -> ~ a#b  == r0.
Admitted.

Theorem deg_non_zero_val :
  forall P : Pol, P <> P0 ->
  forall c d, c < d -> exists a, exists b, exists e,
   a < b <= d /\ c <= a /\ r0 < e /\
     forall x, a < x < b -> e < Pol_eval P x  \/
     forall x, a < x < b -> Pol_eval P x < e.
intros P Hnonz c d Hcltd; 
 generalize (non_zero_least_coeff (Ptranslate P c) 
               (Ptranslate_non_zero _ _ Hnonz));
intros [v [Hvnonz' [k [Q Heq']]]].
assert (Hvnonz : ~ v == r0).
assumption.
assert (Heq : Ptranslate P c = Pc v*X^k + X^(k+1)*Q).
assumption.
generalize (Pol_bound Q c d); intros [A HQbound'].
assert (HQbound : forall x, c < x < d -> rabs_val(Pol_eval Q x) < A).
assumption.
clear Hvnonz' HQbound' Heq'.
case (N_eq_dec k 0).
intros; subst k.
exists c.
exists (rmin d (c+r 1#2*r rdiv(rabs_val v) A)).
exists (rabs_val (rdiv v (2#1))).
split.
split.
apply lt_rmin.
assumption.
apply c_le_form.
apply rat_le_lt_trans with (rabs_val (Pol_eval Q ((c +r d)/r 2#1))).
apply rabs_le.
apply HQbound.
apply middle_in.
assumption.
assumption.
apply rmin_le_l.
split.
apply rat_le_refl.
split.
apply rabs_val_non_zero_lt.
apply non_zero_div.
assumption.
apply non_zero_frac.
omega.
Admitted.

(* Here starts the proofs proposed by Assia. *)

Parameter Pol_evalR : Pol -> R -> R.
Parameter Rat_to_R : Coef -> R.


Open Scope R_scope.

Theorem Pol_evalR_plus :
  forall p q x, Pol_evalR (p + q) x = (Pol_evalR p x) + (Pol_evalR q) x.
Admitted.

Theorem Pol_evalR_mult :
  forall p q x, Pol_evalR (p * q) x = Pol_evalR p x * Pol_evalR q x.
Admitted.

Theorem Pol_evalR_constant :
  forall a x, Pol_evalR (Pc a) x = Rat_to_R a.
Admitted.

Theorem Pol_evalR_X :
  forall x, Pol_evalR X x = x.
Admitted.

Theorem Pol_evalR_rat :
   forall P x, Pol_evalR P (Rat_to_R x) = Rat_to_R (Pol_eval P x).
Admitted.

Theorem Rat_to_R_r0 : Rat_to_R r0 = 0.
Admitted.


Theorem Pol_intermediate_value1 :
  forall a b:R, forall P, a < b -> Pol_evalR P a < 0 ->
     0 < Pol_evalR P b -> exists c, a < c < b /\ Pol_evalR P c = 0.
Admitted.

Theorem Pol_intermediate_value2 :
  forall a b:R, forall P, a < b -> 0 < Pol_evalR P a ->
     Pol_evalR P b < 0 -> exists c, a < c < b /\ Pol_evalR P c = 0.
Admitted.

Theorem Pol_Mean_value :
  forall a b:R, forall P, a < b -> exists c:R,
     a < c < b /\
      Pol_evalR (Pol_deriv P) c = (Pol_evalR P b - Pol_evalR P a)/b-a.
Admitted.

Theorem Pol_deriv_degree :
  forall P, (0 < Pol_deg P)%N  -> Pol_deg P = (Pol_deg(Pol_deriv P) + 1)%N.
Admitted.

Fixpoint list_to_Pol (l:list Coef) : Pol :=
  match l with nil => P0 | a::tl => (Pc a + X * (list_to_Pol tl))%P end.

Definition alternations_list (l:list Coef) : nat :=
  sign_changes (map rsign l).

Fixpoint deriv_list_aux (l:list Coef)(n:Z) {struct l} : list Coef :=
  match l with
    nil => nil
  | a::tl => (n#1 *r a)%Q::deriv_list_aux tl (n+1)
  end.

Definition deriv_list (l:list Coef) := 
    match l with nil => nil | a::tl => deriv_list_aux l 1 end.

Fixpoint Pnorm (P:Pol) : Pol :=
  match P with
  | Pc c => Pc c
  | PX A i a => 
    match Pnorm A with
      Pc c => if rzero_test c then Pc a else PX (Pc c) i a
    | PX A' j a' =>
      if rzero_test a' then
         PX A' (i+j) a
      else
         PX (PX A' j a') i a
    end
  end.

Theorem Pnorm_id : forall P x, Pol_eval (Pnorm P) x = Pol_eval P x.
Admitted.

Theorem Pnorm_idR : forall P x, Pol_evalR (Pnorm P) x = Pol_evalR P x.
Admitted.

Definition non_zero_pol (P:Pol) : Prop :=
  match Pnorm P with Pc c => ~c==c0 | PX _ _ _ => True end.

Theorem Pnorm_sign_plus_infinity :
  forall P,
    non_zero_pol P -> 
    exists A, forall x, A < x -> 0 < Pol_evalR P x * Rat_to_R (Pol_dom P).
Admitted.

Theorem Pnorm_ext : 
  forall P Q, (forall x, Pol_eval P x = Pol_eval Q x) -> Pnorm P = Pnorm Q.
Admitted.

Theorem Pnorm_deg : forall P, (Pol_deg (Pnorm P) <= Pol_deg P)%N.
Admitted.

Theorem list_to_Pol_id :
  forall n P, (Pol_deg (Pnorm P) <= n)%N ->
  Pnorm (list_to_Pol (Pol_to_list_dense P n)) = Pnorm P.
Admitted.

Theorem Pnorm_involutive :
  forall P, Pnorm (Pnorm P) = Pnorm P.
Admitted.

Theorem Pol_deriv_list :
  forall P, Pnorm (Pol_deriv P) = 
              Pnorm (list_to_Pol(deriv_list 
                        (Pol_to_list_dense P (Pol_deg P)))).
Admitted.

Definition alternations P :=
    sign_changes (map rsign (Pol_to_list_dense P (Pol_deg P))).

Theorem alternation_deriv :
  forall P, alternations P = alternations (Pol_deriv P) \/
    (alternations P = (alternations (Pol_deriv P) + 1)%nat).
Admitted.

(* This not new code, but just giving a name to a function that appears in
   the code to prove. *)
Fixpoint Pol_deg_coefdom_aux (deg : N) (P : Pol1 Coef) {struct P} :
          N * Coef :=
            match P with
            | Pc a => (deg, a)
            | PX P0 i _ => Pol_deg_coefdom_aux (deg + Npos i)%N P0
            end.

Theorem Pol_deg_coefdom_aux_increase :
 forall P n,
   (n <= fst (Pol_deg_coefdom_aux n P))%N.
intros P; induction P.
simpl.
intros n; apply Nle_refl.
simpl.
intros n.
apply Nle_trans with (n+Npos p)%N.
apply Nle_plus_r.
apply IHP.
Qed.

Theorem nat_of_P_non_0 :
   forall p, 0%nat <> nat_of_P p.
induction p; simpl.
rewrite nat_of_P_xI.
discriminate.
rewrite nat_of_P_xO.
omega.
compute; discriminate.
Qed.

Theorem nat_of_N_plus :
   forall x y, (nat_of_N (x + y) = nat_of_N x + nat_of_N y)%nat.
Admitted.

Theorem nat_of_N_inj : forall x y, nat_of_N x = nat_of_N y -> x = y.
intros x y; case x ; case y; simpl.
auto.
intros p Heq; elim (nat_of_P_non_0 p);auto.
intros p Heq; elim (nat_of_P_non_0 p);auto.
intros x' y' Heq; apply f_equal with (f:= Npos);
   apply nat_of_P_inj; assumption.
Qed.

Theorem Qeqdec : forall x y, {x==y}+{~x==y}.
Admitted.

Theorem Pol_0_decompose :
  forall P, Pol_eval P r0==r0 ->
     exists Q, (Pnorm P= Pnorm (X*Q))%P/\ (Pol_deg P = Pol_deg Q + 1)%N.
Admitted.

Theorem alternations_Pnorm :
  forall P, alternations (Pnorm P) = alternations P.
Admitted.

Theorem alternations_times_X :
  forall P, alternations (X*P) = alternations P.
Admitted.

Theorem neglect_sub_polynomial_infinity :
  forall P i, (Pol_deg P < i)%N -> forall b, 0 < b ->
   exists y, forall x, y < x -> Pol_evalR P x < b*x^(nat_of_N i).
Admitted.

Theorem Pol_coeff_one_alternation_neg :
  forall P, ~Pol_eval P r0 == r0 ->
   alternations P = 1%nat -> exists b, forall y, b <= y ->
   Pol_evalR P 0 * Pol_evalR P y < 0.
Admitted.

Theorem Rat_to_R_inject :
  forall x y, x == y -> Rat_to_R x = Rat_to_R y.
Admitted.

Theorem Rat_to_R_neq_inject :
  forall x y, ~x==y -> Rat_to_R x <> Rat_to_R y.
Admitted.

Theorem Pol_share_sign_deriv_infinity :
  forall P, Pol_deriv P <> P0 -> 
  exists b, forall y, b <= y -> Pol_evalR P b * Pol_evalR (Pol_deriv P) b > 0.
Admitted.

Theorem Pol_coeff_one_alternation_one_root_aux :
   forall n P, nat_of_N(Pol_deg P) = n -> alternations P = 1%nat ->
     exists x:R, 0 < x /\ Pol_evalR P x = 0 /\
      forall y, 0 < y -> Pol_evalR P y = 0 -> x = y.
induction n.
intros P.
case P.
unfold alternations; simpl; intros;discriminate.
intros p p0 c; unfold Pol_deg, Pol_deg_coefdom.
 fold (Pol_deg_coefdom_aux (0 + (Npos p0)) p).
intros Habs.
absurd (Npos p0 <= 0)%N.
compute; auto.
replace 0%nat with (nat_of_N 0) in Habs; [idtac | auto].
rewrite <- nat_of_N_inj with (1 := Habs).
simpl; apply Pol_deg_coefdom_aux_increase.
intros P Hdeg Halternations.
elim (Qeqdec (Pol_eval P r0) r0).
intros HP0eq.
elim Pol_0_decompose with (1:= HP0eq); intros Q [HPQ HdegQ].
elim (IHn Q).
intros z [Hposz [Hzroot Hzunique]].
exists z; split; [exact Hposz | split].
rewrite <- Pnorm_idR; rewrite HPQ; rewrite Pnorm_idR.
rewrite Pol_evalR_mult; rewrite Hzroot.
ring.
intros y Hypos Hyroot; apply Hzunique.
assumption.
(*rewrite <- Pnorm_idR in Hyroot; rewrite HPQ in Hyroot;
 rewrite Pnorm_idR in Hyroot.
rewrite Pol_evalR_mult in Hyroot; rewrite Pol_evalR_X in Hyroot. *)
replace (Pol_evalR Q y) with (Pol_evalR P y * /y).
rewrite Hyroot; ring.
rewrite <- (Pnorm_idR P); rewrite HPQ;  rewrite Pnorm_idR.
rewrite Pol_evalR_mult; rewrite Pol_evalR_X.
field.
auto with real.
apply eq_add_S.
rewrite <- Hdeg; rewrite HdegQ.
rewrite nat_of_N_plus; simpl.
ring.
rewrite <- Halternations.
rewrite <- (alternations_Pnorm P).
rewrite HPQ.
rewrite alternations_Pnorm.
rewrite alternations_times_X.
trivial.
intros HP0nz.
elim (alternation_deriv P).
intros Hderiv_alternate.
elim (IHn (Pol_deriv P)).
intros x' [Hposx' [Hextremum Huniquex']].
assert (exists y, forall x, y <= x -> Pol_evalR P 0 * Pol_evalR P x < 0).
apply Pol_coeff_one_alternation_neg; auto.
elim (Rle_dec (Pol_evalR P 0 * Pol_evalR P x') 0).
intros HPx'le0.
elim (Pol_intermediate_value2 0 x' (Pc (Pol_eval P r0) * P)).
intros root [[Hrootpos Hrootltx'] HProot].
exists root.
split.
assumption.
assert (HProot' : Pol_evalR P root = 0).
apply Rmult_eq_reg_l with (Pol_evalR P 0).
rewrite Pol_evalR_mult in HProot.
rewrite Pol_evalR_constant in HProot.
rewrite <- Pol_evalR_rat in HProot.
rewrite Rat_to_R_r0 in HProot.
rewrite HProot;  ring.
rewrite <- Rat_to_R_r0.
rewrite Pol_evalR_rat.
apply Rat_to_R_neq_inject.
assumption.

split;auto.

(* show unicity. *)
intros y Hypos Hyroot.
elim (Rle_dec root x').
intros Hrootlex'.

Show.
(*
Qed.
  
(* use to get the list of coefficients in a polynome : Pol_to_list_dense *)
End Bernstein_utils.

Module Type Proof_bernstein.



End Proof_bernstein.


*)
