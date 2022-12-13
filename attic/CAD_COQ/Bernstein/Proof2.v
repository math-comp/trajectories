(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr Yves.Bertot Frederique.Guilhot    *)
(*  &all    Inria, 2006                                      *)
(*************************************************************)

Require Export Reals.
Require Export Fourier.
Require Export PolTac.
Import PolAux.

Open Scope R_scope.

Theorem Rplus_pos_le :
  forall x y, 0 <= y -> x <= x + y.
intros; fourier.
Qed.


Theorem prod_pos_hyp : forall x y, 0 < x -> 0 <= x*y -> 0 <= y.
intros x y H [Hlt | Heq].
left; apply Rlt_sign_pos_pos_rev with (1:= H); auto.
right; replace y with ((x*y)*/x).
rewrite <- Heq; ring.
field; auto with real.
Qed.

Parameter Rpol : Set.

Bind Scope Rpol_scope with Rpol.
Delimit Scope Rpol_scope with P.

Parameter Pnorm : Rpol -> Rpol.

Parameter Rpol_mult : Rpol -> Rpol -> Rpol.

Parameter Rpol_plus : Rpol -> Rpol -> Rpol.

Parameter X : Rpol.

Parameter Pc : R -> Rpol.

Parameter P0 : Rpol.

Parameter Rpol_exp : Rpol -> nat -> Rpol.

Infix "^" := Rpol_exp : Rpol_scope.

Definition Rpol_decompose_Horner :
  forall P:Rpol,
    {c:R | Pnorm P = Pc c}+
    {c:R & { n:nat &
        { Q :Rpol | (0 < n)%nat /\ Pnorm P = Pnorm (Pc c + X^n * Q) /\
                   ~Pnorm Q = P0}}}.
Admitted.

Parameter smaller_degree : Rpol -> Rpol -> Prop.

Theorem smaller_degree_wf : well_founded smaller_degree.
Admitted.

Theorem smaller_degree_step :
 forall P Q c n, Pnorm P = Pnorm (Pc c + X^n * Q) ->
    Pnorm Q <> P0 -> smaller_degree Q P.
Admitted.

Parameter Rpol_eval : Rpol -> R -> R.

Infix "*" := Rpol_mult : Rpol_scope.
Infix "+" := Rpol_plus : Rpol_scope.

Axiom eval_X : forall x, Rpol_eval X x = x.

Axiom eval_c : forall x y, Rpol_eval (Pc x) y = x.

Axiom eval_mult : forall P1 P2 x, Rpol_eval (P1 * P2)%P x =
   Rpol_eval P1 x * Rpol_eval P2 x.

Axiom eval_plus : forall P1 P2 x, Rpol_eval (P1 + P2)%P x =
    Rpol_eval P1 x + Rpol_eval P2 x.

Axiom eval_exp : forall P n x, Rpol_eval (P^n) x = Rpol_eval P x^n.

Axiom Pnorm_ext : forall P Q, (forall x, Rpol_eval P x = Rpol_eval Q x) ->
  Pnorm P = Pnorm Q.

Parameter least_non_zero_coeff : Rpol -> R.

Theorem least_non_zero_P1 :
  forall P, Pnorm P <> P0 -> ~least_non_zero_coeff P = 0.
Admitted.

Theorem least_non_zero_P2 :
  forall P, 
  exists n:nat, exists Q: Rpol,
    Pnorm P = Pnorm (X^n*(Pc (least_non_zero_coeff P) + X * Q)).
Admitted.

Theorem least_non_zero_P3 :
  forall P, Pnorm P = P0 -> least_non_zero_coeff P = 0.
Admitted.

Theorem least_non_zero_P4 :
  forall P b n Q, Pnorm P = Pnorm (X^n * (Pc b + X * Q)) -> ~b=0 ->
            least_non_zero_coeff P = b.
Admitted.

Axiom least_non_zero_P5 :
  forall P b, Pnorm P = Pc b -> least_non_zero_coeff P = b.

Axiom least_non_zero_P6 :
  forall n P Q a, Pnorm P = Pnorm (X^n * (Pc a + X * Q)) -> a = 0 ->
    least_non_zero_coeff P = least_non_zero_coeff Q.

Axiom Pnorm_cte : forall c, Pnorm (Pc c) = Pc c.

Theorem least_non_zero_P7 :
  forall b, least_non_zero_coeff (Pc b) = b.
intros b; apply least_non_zero_P5; trivial.
apply Pnorm_cte.
Qed.

Axiom least_non_zero_Pnorm :
  forall P Q, Pnorm P = Pnorm Q -> 
  least_non_zero_coeff P = least_non_zero_coeff Q.

(* Parameter Rpol_degree : Rpol -> nat.

Theorem Rpol_decompose_degree :
  forall P c n Q, Pnorm P = Pnorm (Pc c + X^n * Q) ->
  Pnorm Q <> P0 -> Rpol_degree P = (Rpol_degree Q + n)%nat.
Admitted.
*)

Axiom Rpol_eval_Pnorm :
  forall P x, Rpol_eval (Pnorm P) x = Rpol_eval P x.

Axiom Pnorm_plus : forall a a' b b', Pnorm a = Pnorm a' ->
   Pnorm b = Pnorm b' -> Pnorm (a + b) = Pnorm (a' + b').

Axiom Pnorm_mult : forall a a' b b', Pnorm a = Pnorm a' ->
   Pnorm b = Pnorm b' -> Pnorm (a * b) = Pnorm (a' * b').

Axiom Pnorm_exp : forall a a' n, Pnorm a = Pnorm a' ->
  Pnorm (a^n)=Pnorm (a'^n).

Axiom Pnorm_exp1 : forall X n, Pnorm (X^n) = Pnorm X.

Hint Rewrite eval_mult eval_plus eval_c eval_X eval_exp Rpol_eval_Pnorm : Rpol.

Inductive no_alternation : Rpol -> Set :=
  no_alternation_c1 : forall c, no_alternation (Pc c)
| no_alternation_c2 :
    forall n a P Q,
      no_alternation Q -> a <> 0 -> 0 <= a*(least_non_zero_coeff Q) ->
      Pnorm P = Pnorm (X^n *(Pc a+X*Q)) -> no_alternation P.

Inductive one_alternation : Rpol -> Set :=
  one_alternation_here :
    forall P a n Q, (1 <= n)%nat ->
      Pnorm P = Pnorm (X^n *(Pc a + X * Q)) -> 
      a * least_non_zero_coeff Q < 0 -> no_alternation Q ->
      one_alternation P
| one_alternation_step :
    forall P a n Q,
      Pnorm P = Pnorm (X^n * (Pc a + X * Q)) ->
      one_alternation Q -> 0 < a * least_non_zero_coeff Q ->
      one_alternation P.

Theorem no_alternation_increasing :
  forall P, 0 <= least_non_zero_coeff P -> no_alternation P ->
  forall x y, 0 <= x <= y -> 0 <= Rpol_eval P x <= Rpol_eval P y.
Admitted.

Theorem no_alternation_increasing' :
  forall P, 0 <= least_non_zero_coeff P -> no_alternation P ->
  forall x y, 0 <= x <= y -> Rpol_eval P x <= Rpol_eval P y.
intros; assert (0 <= Rpol_eval P x <= Rpol_eval P y).
apply no_alternation_increasing; auto.
intuition.
Qed.

Theorem no_alternation_positive :
  forall P, no_alternation P -> 0 <= least_non_zero_coeff P ->
  forall x, 0 <= x -> 0 <= Rpol_eval P x.
intros P Hna Hpos x Hposx.
elim (least_non_zero_P2 P); intros n [Q Heq].
apply Rle_trans with (Rpol_eval P 0).
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
destruct (zerop n) as [Hn0 | H0ltn].
subst n.
rewrite pow_O.
rewrite Rmult_1_l; rewrite Rmult_0_l; rewrite Rplus_0_r.
assumption.
rewrite pow_i;[fourier | assumption].
elim (no_alternation_increasing P Hpos Hna 0 x); intros; auto.
split; fourier.
Qed.

Theorem no_alternation_positive_st :
  forall P, no_alternation P -> 0 < least_non_zero_coeff P ->
  forall x, 0 < x -> 0 < Rpol_eval P x.
intros P' H; elim H.
intros; autorewrite with Rpol.
rewrite least_non_zero_P7 in H0; auto.
intros n a P Q HnaQ IHQ Ha Hprodpos Heq Hpos x Hxpos.

(* elim (Rlt_le_dec 0 a).
intros Ha'. *)
assert (least_non_zero_coeff P = a).
apply least_non_zero_P4 with (1:= Heq).
assumption.
assert (Hpartpos : 0 <= x * Rpol_eval Q x).
apply Rmult_le_pos.
fourier.
apply no_alternation_positive; auto.
apply prod_pos_hyp with a; auto.
fourier.
fourier.
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
apply Rmult_lt_0_compat.
apply pow_lt; auto.
fourier.
Qed.

Theorem Rmult_minus_distr_r :
  forall x y z, ((x - y)* z= x*z - y * z)%R.
intros; ring.
Qed.

Theorem exp_grows :
  forall u n, 1 <= u -> (1 <= n)%nat -> u <= u ^ n.
intros; pattern u at 1; replace u with (u^1).
apply Rle_pow; auto.
simpl; ring.
Qed.

Axiom intermediate_value_Rpol :
  forall P x y, x < y -> Rpol_eval P x * Rpol_eval P y < 0 ->
  exists z, x < z < y /\ Rpol_eval P z = 0.


Theorem increasing_pos_horner :
  forall a Q,
  a < 0 ->
  forall r,
  0 <= r ->
  (forall x y, r < x <= y -> 0 < Rpol_eval Q x <= Rpol_eval Q y) ->
  0 < Rpol_eval (Pc a + X * Q) (r+1 -a /Rpol_eval Q (r+1)).
intros a Q Halt0 r Hrpos HQincr.
assert (Hb1: r < r+1 <= r+1).
split;fourier.
assert (HQr1pos : 0 < Rpol_eval Q (r+1)).
generalize (HQincr _ _ Hb1); intuition.
assert (Hpos : 0 < -(a/Rpol_eval Q(r+1))).
unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse.
apply Rlt_mult_inv_pos.
fourier.
assumption.
assert (Hpos' : 0 < r+1 - a/Rpol_eval Q (r+1)).
fourier.
assert (Hlt : r < r+1 <= r+1 - a/Rpol_eval Q (r+1)).
split; fourier.
autorewrite with Rpol.
apply Rlt_le_trans with (a + (r+1-a/Rpol_eval Q (r+1))*(Rpol_eval Q (r+1))).
rewrite Rmult_minus_distr_r.
match goal with |- (0 < ?x) =>
   replace x with ((r + 1) * Rpol_eval Q (r + 1))
end.
apply Rlt_sign_pos_pos.
fourier.
assumption.
field.
auto with real.
pols.
apply Rmult_le_compat_l.
generalize (HQincr _ _ Hlt); intuition.
decompose [and] Hlt; fourier.
Qed.

Theorem no_alternation_tech :
  forall Q a, a < 0 -> 0 < least_non_zero_coeff Q -> no_alternation Q ->
  0 < 1 - a / Rpol_eval Q 1.
intros Q a Haneg HQpos Hna.
assert (HQpos' : 0 < Rpol_eval Q 1).
apply no_alternation_positive_st; auto with real.
apply Rlt_trans with (1+0).
fourier.
unfold Rminus, Rdiv; apply Rplus_lt_compat_l.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rlt_mult_inv_pos.
fourier.
auto.
Qed.

Theorem alternation_here_pos_value :
  forall  Q a, a < 0 -> 0 < least_non_zero_coeff Q ->
    no_alternation Q ->
    0 < Rpol_eval (Pc a+X*Q) (1 - a / (Rpol_eval Q 1)).
intros Q a Haneg HposQ Hnoalt.
replace (1-a/Rpol_eval Q 1) with (0 + 1 - a /Rpol_eval Q (0+1)).
apply increasing_pos_horner; auto with real.
intros x y [Hlt Hle]; split.
apply no_alternation_positive_st; auto with real.
apply no_alternation_increasing'; auto with real.
replace (0+1) with 1; trivial.
ring.
Qed.

Theorem alternation_here_root :
  forall Q a, a < 0 -> 0 < least_non_zero_coeff Q ->
    no_alternation Q -> 
    (exists r, 0 < r /\ Rpol_eval (Pc a + X * Q) r = 0 /\
               (forall x y, r < x <= y ->
               0 < Rpol_eval (Pc a + X * Q) x <= Rpol_eval (Pc a + X * Q) y) /\
               forall x, 0 < x < r -> Rpol_eval (Pc a + X * Q) x < 0).
intros Q a Haneg HQpos Hna.
elim (intermediate_value_Rpol (Pc a + X * Q) 0 (1 - a/(Rpol_eval Q 1))).
intros r [Hintr Hroot].
exists r; split.
intuition.
split.
assumption.
split.
intros x y Hcmpxy.
autorewrite with Rpol.
split.
rewrite <- Hroot; autorewrite with Rpol.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (r*Rpol_eval Q x).
apply Rmult_le_compat_l.
apply no_alternation_increasing'; auto.
fourier.
split; intuition.
intuition.
apply Rmult_lt_compat_r.
apply no_alternation_positive_st; auto.
intuition; fourier.
intuition.
apply Rplus_le_compat_l.
assert (0 <= x).
intuition; fourier.
assert (0 <= y).
intuition; fourier.
apply Rle_trans with (x *  Rpol_eval Q y).
apply Rmult_le_compat_l; auto with real.
apply no_alternation_increasing'; auto.
fourier.
intuition.
apply Rmult_le_compat_r.
apply no_alternation_positive;auto.
fourier.
intuition.
intros x [Hxpos Hxltr]; rewrite <- Hroot.
autorewrite with Rpol.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (x*Rpol_eval Q r).
apply Rmult_le_compat_l; auto.
auto with real.
apply no_alternation_increasing'; auto with real.
intuition.
apply Rmult_lt_compat_r; auto with real.
apply no_alternation_positive_st; auto with real.
fourier.
apply no_alternation_tech; auto.
assert (0 < Rpol_eval(Pc a+X*Q)(1-a/Rpol_eval Q 1)).
apply alternation_here_pos_value;auto.
pattern 0 at 2; replace 0 with
   (0 * Rpol_eval (Pc a + X *Q) (1-a/Rpol_eval Q 1)).
apply Rmult_lt_compat_r.
apply alternation_here_pos_value; auto.
autorewrite with Rpol.
rewrite Rmult_0_l; rewrite Rplus_0_r; auto.
ring.
Qed.

Theorem increasing_horner_root :
 forall a r' Q, a < 0 -> 0 < r' -> Rpol_eval Q r' = 0 ->
 (forall x : R, 0 < x < r' -> Rpol_eval Q x < 0) ->
 (forall x y : R, r' < x <= y -> 0 < Rpol_eval Q x <= Rpol_eval Q y) ->
 exists r, 0 < r /\ Rpol_eval (Pc a + X * Q) r = 0 /\
   (forall x y:R, r < x <= y -> 0 < Rpol_eval (Pc a + X * Q) x <=
                                    Rpol_eval (Pc a + X * Q) y) /\
   (forall x : R, 0 < x < r -> Rpol_eval (Pc a + X * Q) x < 0).
intros a r' Q Halt0 Hr'pos Hroot' HQneg HQincr.
assert (Hr'pos' : 0 <= r').
intuition.
generalize (increasing_pos_horner a Q Halt0 r' Hr'pos' HQincr).
intros Hpos.
elim (intermediate_value_Rpol (Pc a + X * Q) r' 
         (r' + 1 - a/(Rpol_eval Q (r'+1)))).
intros r [[Hr'ltr _] Hroot].
exists r.
split.
fourier.
split.
assumption.
split.
intros x y [Hrltx Hxley]; split.
rewrite <- Hroot.
autorewrite with Rpol.
pols.
apply Rlt_le_trans with (x*Rpol_eval Q r).
assert (Hb1 : r' < r <= r).
auto with real.
assert (0 < Rpol_eval Q r).
generalize (HQincr r r Hb1);intuition.
polf.
apply Rmult_le_compat_l.
assert (Hb2 : r' < r <= x).
split;fourier.
generalize (HQincr r x Hb2); intuition.
fourier.
assert (r' < x <= y).
split; fourier.
autorewrite with Rpol.
pols.
apply Rle_trans with (x*Rpol_eval Q y).
apply Rmult_le_compat_l.
assert (Hb :r' < x <= y).
split; fourier.
generalize (HQincr x y Hb);intuition.
fourier.
assert (Hb : r' < y <= y).
split; fourier.
apply Rmult_le_compat_r.
auto.
generalize (HQincr y y Hb); intuition.
auto.
intros x [Hxpos Hxltr].
autorewrite with Rpol.
elim (Rlt_le_dec x r').
intros Hxltr'.
polr Halt0.
fourier.
RSignTac.rsign_tac0.
intros [Hr'ltx | Hr'eqx].
rewrite <- Hroot.
autorewrite with Rpol.
pols.
apply Rle_lt_trans with (x * Rpol_eval Q r).
RSignTac.rsign_tac.
assert (Hb :r' < x <= r).
auto with real.
generalize (HQincr _ _ Hb); intuition.
assert (0 < Rpol_eval Q r).
assert (Hb: r' < r <= r).
auto with real.
generalize (HQincr _ _ Hb); intuition.
polf.
rewrite <- Hr'eqx; rewrite Hroot'; pols.
assumption.
pols.
assert (0 < -(a/Rpol_eval Q (r'+1))).
assert (0 < Rpol_eval Q (r'+1)).
assert (Hb: r' < r'+1 <= r'+1).
auto with real.
generalize (HQincr _ _ Hb);intuition.
unfold Rdiv.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rlt_mult_inv_pos.
fourier.
assumption.
fourier.
RSignTac.rsign_tac0.
autorewrite with Rpol.
rewrite Hroot'.
pols.
assumption.
Qed.

Theorem one_alternation_root_main :
  forall P, one_alternation P -> least_non_zero_coeff P < 0 ->
    (exists a, 0 < a /\ Rpol_eval P a = 0 /\
               (forall x y, a < x <= y -> 0 < Rpol_eval P x <= Rpol_eval P y)
    /\
               forall x, 0 < x < a -> Rpol_eval P x < 0).
intros P H; elim H; clear H P.
intros P a n Q Hnnz Heq Hneg Hna Hneg_coeff.
assert (Halt0 : a < 0).
rewrite <- (least_non_zero_P4 P _ _ _ Heq).
assumption.
intros Heq0; rewrite Heq0 in Hneg; rewrite Rmult_0_l in Hneg.
elim (Rlt_irrefl 0); assumption.
assert (HlcQ : 0 < least_non_zero_coeff Q).
apply Rlt_sign_neg_pos_rev with a; auto.
elim (alternation_here_root Q a); auto.
intros r [Hrpos [Hroot [Hpos_part Hneg_part]]].
exists r; split.
auto.
split.
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
generalize Hroot; autorewrite with Rpol; intros Hroot'; rewrite Hroot'.
ring.
split.
intros x y [Hrltx Hxley]; split.
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
apply Rmult_lt_0_compat.
apply pow_lt; fourier.
rewrite <- Hroot; autorewrite with Rpol.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (r * Rpol_eval Q x).
apply Rmult_le_compat_l; auto with real.
apply no_alternation_increasing'; auto with real.
apply Rmult_lt_compat_r.
apply no_alternation_positive_st; auto with real.
fourier.
assumption.
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
rewrite <- (Rpol_eval_Pnorm P); rewrite Heq; autorewrite with Rpol.
apply Rmult_le_compat.
apply pow_le; fourier.
rewrite <- Hroot; autorewrite with Rpol.
apply Rplus_le_compat_l.
apply Rmult_le_compat.
fourier.
apply no_alternation_positive; auto with real.
auto with real.
apply no_alternation_increasing'; auto with real.
apply pow_incr; split; fourier.
apply Rplus_le_compat_l.
apply Rmult_le_compat.
fourier.
apply no_alternation_positive; auto with real.
fourier.
auto.
apply no_alternation_increasing'; auto with real.
split; auto; fourier.
intros x [Hxpos Hxltr].
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
replace 0 with (x^n*0).
apply Rmult_lt_compat_l.
apply pow_lt; auto.
rewrite <- Hroot; autorewrite with Rpol.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (x * Rpol_eval Q r).
apply Rmult_le_compat_l; auto with real.
apply no_alternation_increasing'; auto with real.
apply Rmult_lt_compat_r; auto with real.
apply no_alternation_positive_st; auto with real.
ring.

(* End of the case for an immediate alternation. *)
intros P a n Q Heq Hoa Hrec Hprodpos HlcPneg.
assert (Halt0 : a < 0).
rewrite <- (least_non_zero_P4 P _ _ _ Heq).
assumption.
intros Heq0; rewrite Heq0 in Hprodpos; rewrite Rmult_0_l in Hprodpos.
apply (Rlt_irrefl 0); assumption.
assert (HlcQ : least_non_zero_coeff Q < 0).
apply Rlt_sign_neg_neg_rev with a; auto.

elim Hrec; auto.
intros r' [Hr'pos [Hroot' [HQpos' HQneg']]].

elim (increasing_horner_root a r' Q Halt0 Hr'pos Hroot' HQneg' HQpos').
intros r [Hrpos [Hroot [HQpos Hneg]]].
exists r.
split.
assumption.
split.
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
generalize Hroot; autorewrite with Rpol; intros Hroot1; rewrite Hroot1.
ring.
split.
intros x y Hintxy.
rewrite <- Rpol_eval_Pnorm; rewrite Heq; autorewrite with Rpol.
generalize (HQpos x y Hintxy);autorewrite with Rpol.
intros [H1 H2].
rewrite <- (Rpol_eval_Pnorm P); rewrite Heq; autorewrite with Rpol.
assert (0 < x ^ n).
apply pow_lt.
decompose [and] Hintxy; fourier.
split.
RSignTac.rsign_tac0.
apply Rle_trans with (x^n*(a+y*Rpol_eval Q y)).
apply Rmult_le_compat_l; auto with real.
assert (0 < a+y*Rpol_eval Q y).
apply Rlt_le_trans with (a+x*Rpol_eval Q x); auto.
polf.
assert (0 <= x).
decompose [and] Hintxy; fourier.
apply pow_incr; intuition.
intros x Hintx.
rewrite <- (Rpol_eval_Pnorm P); rewrite Heq; autorewrite with Rpol.
generalize (Hneg _ Hintx); autorewrite with Rpol; intros Hnegx.
assert (0 < x^n).
apply pow_lt.
intuition.
RSignTac.rsign_tac0.
Qed.

Theorem one_alternation_non_zero :
  forall P, one_alternation P -> Pnorm P <> P0.
intros P H; induction H.
intro PnormPP0.
assert (H:~a=0).
intros Heqa.
rewrite Heqa in r.
rewrite Rmult_0_l in r.
elim (Rlt_irrefl 0).
assumption.
generalize (least_non_zero_P4 _ _ _ _ e H).
intros Heql.
elim H.
rewrite <- Heql.
apply least_non_zero_P3.
assumption.

intro PnormPP0.
assert (H':~a=0).
intros Heqa.
rewrite Heqa in r.
rewrite Rmult_0_l in r.
elim (Rlt_irrefl 0).
assumption.
generalize (least_non_zero_P4 _ _ _ _ e H').
intros Heql.
elim H'.
rewrite <- Heql.
apply least_non_zero_P3.
assumption.
Qed.

Theorem Pnorm_opp :
  forall P, least_non_zero_coeff (Pnorm ((Pc (-1)) * P))=
    -least_non_zero_coeff P.
intros P; elim P using (well_founded_ind smaller_degree_wf); clear P.
intros P Hrec; elim (Rpol_decompose_Horner P).
intros [c H].
rewrite (Pnorm_ext (Pc (-1)*P)(Pc (-c))).
rewrite (least_non_zero_P5 P c).
rewrite Pnorm_cte.
apply least_non_zero_P7.
assumption.
intros x; autorewrite with Rpol.
rewrite <- Rpol_eval_Pnorm.
rewrite H; autorewrite with Rpol.
ring.

intros [c [n [Q [Hnnz [HPeq HQnz]]]]].
elim (Req_dec c 0).
intros Heq.
replace (Pnorm (Pc (-1)*P) with (X^n *  (Pc (-1) * Q)).


Theorem one_alternation_root :
  forall P, one_alternation P ->
    (exists a, 0 < a /\ Rpol_eval P a = 0 /\
      forall x, 0 < x -> Rpol_eval P x <> 0).
intros P H.
elim (Rlt_le_dec 0 (least_non_zero_coeff P)).
intros Hlt.

