(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr Yves.Bertot Frederique.Guilhot    *)
(*  &all    Inria, 2006                                      *)
(*************************************************************)

Require Export Reals.
Require Export Field.
Require Export Fourier.
Open Scope R_scope.
Hint Resolve fact_neq_0 prod_neq_R0 :real.
 
Ltac RReplace a b := replace a with b; [idtac | ring || auto with real].
 
Ltac NReplace a b := replace a with b; [idtac | omega || auto with arith].
 
Axiom gt_div2 : forall alp, alp > 0 ->  (alp * / 2 > 0).
 
Axiom lt_div2 : forall alp, alp > 0 ->  (alp * / 2 < alp).
(**)
 
Inductive Rstar_point : R ->  Prop :=
  Rstar_point_intro: forall (x : R), x <> 0 -> x + 1 <> 0 ->  Rstar_point x .
 
Lemma continuity_pol_0_point:
 forall n a g,
 (forall (X : R),
  X <> 0 -> X + 1 <> 0 ->  g X = X * sum_f_R0 (fun (i : nat) => a i * X ^ i) n) ->
  limit1_in g Rstar_point 0 0.
induction n; intros.
assert (forall (X : R), X <> 0 -> X + 1 <> 0 ->  g X = X * a 0%nat).
intros.
rewrite (H X); auto; simpl.
ring.
unfold limit1_in, limit_in.
simpl.
unfold R_dist; intros.
elim (Req_dec (a 0%nat) 0); intros.
exists eps.
split; [try assumption | idtac].
intros.
elim H3; [intros H4 H5; (try clear H3); (try exact H4)].
rewrite (H0 x); auto.
rewrite H2.
RReplace (x * 0 - 0) 0.
rewrite Rabs_R0.
auto with real.
elim H4; auto.
elim H4; auto.
assert (0 < Rabs (/ a 0%nat)).
apply Rabs_pos_lt; auto with real.
exists (eps * Rabs (/ a 0%nat)).
split; [try assumption | idtac].
apply Rmult_gt_0_compat; auto with real.
intros.
elim H4; [intros H5 H6; (try clear H4); (try exact H5)].
rewrite (H0 x); auto.
RReplace (x * a 0%nat - 0) (x * a 0%nat).
rewrite Rabs_mult.
RReplace eps ((eps * Rabs (/ a 0%nat)) * Rabs (a 0%nat)).
apply Rmult_lt_compat_r; auto with real.
apply Rabs_pos_lt; auto with real.
RReplace x (x - 0); auto.
rewrite Rabs_Rinv; auto.
field.
apply Rabs_no_R0; auto.
elim H5; auto.
elim H5; auto.
assert
 (forall (X : R),
  X <> 0 ->
  X + 1 <> 0 ->
   g X =
   X *
   (sum_f_R0 (fun (i : nat) => a i * X ^ i) 0 +
    sum_f_R0 (fun (i : nat) => a (1 + i)%nat * X ^ (1 + i)) (S n - 1))).
intros.
rewrite <- (tech2 (fun (i : nat) => a i * X ^ i) 0%nat (S n)); auto with arith.
assert
 (forall (X : R),
  X <> 0 ->
  X + 1 <> 0 ->
   g X =
   X * a 0%nat + X * (X * sum_f_R0 (fun (i : nat) => a (1 + i)%nat * X ^ i) n)).
intros.
rewrite H0; auto.
simpl.
NReplace (n - 0)%nat n; auto.
rewrite scal_sum.
assert
 (sum_f_R0 (fun (i : nat) => a (S i) * (X * X ^ i)) n =
  sum_f_R0 (fun (i : nat) => (a (S i) * X ^ i) * X) n).
apply sum_eq; intros.
ring.
rewrite H3.
ring.
pose (f:=
 fun (X : R) => X * sum_f_R0 (fun (i : nat) => a (1 + i)%nat * X ^ i) n).
assert (limit1_in f Rstar_point 0 0).
intros.
unfold f; apply (IHn (fun (i : nat) => a (1 + i)%nat)).
auto.
assert (forall (X : R), X <> 0 -> X + 1 <> 0 ->  g X = X * a 0%nat + X * f X).
unfold f; auto.
assert
 (forall (eps : R),
  eps > 0 -> forall (x : R), Rstar_point x /\ Rabs x < eps ->  (Rabs x < eps)).
intros.
elim H5; [intros H6 H7; (try clear H5); (try exact H7)].
generalize H2; unfold limit1_in, limit_in.
simpl; unfold R_dist; intros.
elim (Req_dec (a 0%nat) 0); intros.
assert (forall (X : R), X <> 0 -> X + 1 <> 0 ->  g X = X * f X).
intros.
rewrite (H3 X); auto.
rewrite H7.
ring.
elim H5 with ( eps := eps ); [intros alp H10; (try exact H10) | auto].
elim H10; [intros H9 H11; (try clear H10); (try exact H9)].
exists (Rmin alp (/ 2)).
split; [auto | intros x; intros].
apply Rmin_Rgt_r; auto.
split; auto with real.
fourier.
elim H10; [intros H12 H13; (try clear H10); (try exact H12)].
RReplace (g x - 0) (g x).
rewrite (H8 x).
rewrite Rabs_mult.
assert (Rabs x < 1).
assert (Rmin alp (/ 2) < 1).
assert (Rmin alp (/ 2) <= / 2).
apply Rmin_r; auto.
fourier.
RReplace x (x - 0).
fourier.
assert (Rabs (f x) < eps).
RReplace (f x) (f x - 0).
apply H11.
split; [try assumption | idtac].
assert (Rmin alp (/ 2) <= alp).
apply Rmin_l; auto.
fourier.
elim (Req_dec (f x) 0); intros.
rewrite H15.
rewrite Rabs_R0.
RReplace (Rabs x * 0) 0; auto.
RReplace eps (1 * eps).
apply Rmult_gt_0_lt_compat; auto.
assert (0 < Rabs (f x)).
apply Rabs_pos_lt; auto with real.
fourier.
fourier.
elim H12; auto.
elim H12; auto.
assert (0 < Rabs (a 0%nat)).
apply Rabs_pos_lt; auto with real.
elim H5 with ( eps := Rabs (a 0%nat) ); [intros alp H10; (try exact H10) | auto].
elim H10; [intros H9 H11; (try clear H10); (try exact H9)].
assert (/ (2 * Rabs (a 0%nat)) > 0).
assert (2 * Rabs (a 0%nat) > 0).
fourier.
assert (0 < / (2 * Rabs (a 0%nat))).
apply Rinv_0_lt_compat; auto with real.
fourier.
exists (Rmin alp (eps * / (2 * Rabs (a 0%nat)))).
split; [auto | intros x; intros].
apply Rmin_Rgt_r; auto.
split; auto with real.
apply Rmult_gt_0_compat; auto.
RReplace (g x - 0) (g x).
elim H12; [intros H13 H14; (try clear H12); (try exact H13)].
rewrite (H3 x); auto.
RReplace (x * a 0%nat + x * f x) (x * (a 0%nat + f x)).
rewrite Rabs_mult.
assert (Rabs x < eps * / (2 * Rabs (a 0%nat))).
assert (Rmin alp (eps * / (2 * Rabs (a 0%nat))) <= eps * / (2 * Rabs (a 0%nat))).
apply Rmin_r; auto.
RReplace x (x - 0).
fourier.
assert (Rabs (a 0%nat + f x) < 2 * Rabs (a 0%nat)).
RReplace (f x) (f x - 0).
assert (Rabs (a 0%nat + (f x - 0)) <= Rabs (a 0%nat) + Rabs (f x - 0)).
apply Rabs_triang.
assert (Rabs (f x - 0) < Rabs (a 0%nat)).
apply H11.
split; [try assumption | idtac].
assert (Rmin alp (eps * / (2 * Rabs (a 0%nat))) <= alp).
apply Rmin_l; auto.
fourier.
RReplace (2 * Rabs (a 0%nat)) (Rabs (a 0%nat) + Rabs (a 0%nat)).
fourier.
elim (Req_dec (a 0%nat + f x) 0); intros.
rewrite H16.
rewrite Rabs_R0.
RReplace (Rabs x * 0) 0; auto.
RReplace eps ((eps * / (2 * Rabs (a 0%nat))) * (2 * Rabs (a 0%nat))).
apply Rmult_gt_0_lt_compat; auto.
assert (0 < Rabs (a 0%nat + f x)).
apply Rabs_pos_lt; auto with real.
fourier.
apply Rmult_gt_0_compat; auto.
field; auto.
assert (0 < 2).
fourier.
auto with real.
elim H13; auto.
elim H13; auto.
Qed.
 
Axiom deux : 2 <> 0.
 
Lemma limit_0_somme_point:
 forall (a : R) (f g : R ->  R),
 (forall X, X <> 0 -> X + 1 <> 0 ->  f X = a + g X) ->
 limit1_in g Rstar_point 0 0 ->  limit1_in f Rstar_point a 0.
unfold limit1_in, limit_in.
simpl.
unfold R_dist; intros.
elim H0 with ( eps := eps );
 [intros alp H2; (try clear H0); (try exact H2) | idtac].
exists alp.
split; [try assumption | idtac].
elim H2; [intros H0 H3; (try clear H2); (try exact H0)].
intros.
rewrite (H x); auto.
RReplace ((a + g x) - a) (g x - 0).
elim H2; [intros H3 H4; (try clear H2); (try exact H4)].
apply (H4 x); auto.
elim H0; [intros H3 H4; (try clear H0); (try exact H3)].
elim H3; auto.
elim H0; [intros H3 H4; (try clear H0); (try exact H3)].
elim H3; auto.
auto.
Qed.
 
Lemma limit_0_point:
 forall (f : R ->  R),
 (forall X, X <> 0 -> X + 1 <> 0 ->  f X = 0) ->  limit1_in f Rstar_point 0 0.
unfold limit1_in, limit_in; intros.
simpl.
unfold R_dist; intros.
exists eps.
split; [try assumption | idtac].
intros.
RReplace (f x - 0) 0.
rewrite Rabs_R0.
auto with real.
elim H1; [intros H2 H3; (try clear H1)].
rewrite (H x); auto.
elim H2; auto.
elim H2; auto.
Qed.
 
Lemma unicite_limit_0_point_somme:
 forall (a : R) (f g : R ->  R),
 (forall (X : R), X <> 0 -> X + 1 <> 0 ->  f X = a + g X) ->
 (forall (X : R), X <> 0 -> X + 1 <> 0 ->  f X = 0) ->
 limit1_in g Rstar_point 0 0 ->  a = 0.
intros.
apply (single_limit f Rstar_point a 0 0).
unfold adhDa; intros.
assert (alp * / 2 > 0).
apply gt_div2; auto.
unfold R_dist; intros.
exists (alp * / 2).
split; [try assumption | idtac].
apply Rstar_point_intro; auto.
auto with real.
assert (alp * / 2 + 1 > 0).
fourier.
auto with real.
RReplace (alp * / 2 - 0) (alp * / 2).
rewrite Rabs_right; auto with real.
apply lt_div2; auto.
fourier.
apply limit_0_somme_point with g; auto.
apply limit_0_point; auto.
Qed.
 
Axiom pow_eq_R0 : forall (n : nat) (a : R), a ^ S n = 0 ->  a = 0.
 
Theorem polynome_nul_point:
 forall (n : nat) (a : nat ->  R),
 (forall X, X + 1 <> 0 ->  sum_f_R0 (fun (i : nat) => a i * X ^ i) n = 0) ->
 forall j, (j <= n)%nat ->  a j = 0.
intros n a H.
assert (forall (m j : nat), (m <= n)%nat -> (j <= m)%nat ->  a j = 0).
induction m; intros.
NReplace j 0%nat; auto.
rewrite <- (H 0); auto with real.
generalize H H0 H1.
clear H H0 H1.
elim n.
simpl; intros.
ring.
intros m; intros.
rewrite (tech2 (fun (i : nat) => a i * 0 ^ i) 0%nat (S m)); auto with arith.
simpl.
NReplace (m - 0)%nat m.
assert (sum_f_R0 (fun (i : nat) => a (S i) * (0 * 0 ^ i)) m = 0).
apply sum_eq_R0; intros.
ring.
rewrite H3; ring.
elim (le_gt_dec j m); intros.
apply IHm; auto with arith.
NReplace j (S m).
assert
 (forall (X : R),
  X + 1 <> 0 ->
   sum_f_R0 (fun (i : nat) => a i * X ^ i) m +
   sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ (S m + i)) (n - S m) = 0).
intros.
rewrite <- (H X); auto.
rewrite (tech2 (fun (i : nat) => a i * X ^ i) m%nat n); auto with arith.
assert
 (forall (X : R), X + 1 <> 0 ->  sum_f_R0 (fun (i : nat) => a i * X ^ i) m = 0).
intros.
apply sum_eq_R0; intros.
rewrite IHm; auto with arith.
ring.
assert
 (forall (X : R),
  X + 1 <> 0 ->
   sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ (S m + i)) (n - S m) = 0).
intros.
rewrite <- (H2 X); auto.
rewrite H3; auto.
ring.
assert
 (forall (X : R),
  X + 1 <> 0 ->
   X ^ S m * sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ i) (n - S m) =
   sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ (S m + i)) (n - S m)).
intros.
rewrite scal_sum.
apply sum_eq; intros.
rewrite pow_add.
ring.
assert
 (forall (X : R),
  X + 1 <> 0 ->
   X ^ S m * sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ i) (n - S m) = 0).
intros.
rewrite (H5 X); auto.
assert
 (forall (X : R),
  X + 1 <> 0 ->
   X ^ S m = 0 \/
   sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ i) (n - S m) = 0).
intros.
apply Rmult_integral; auto.
assert
 (forall (X : R),
  X + 1 <> 0 ->
   X = 0 \/ sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ i) (n - S m) = 0).
intros.
elim H7 with ( X := X );
 [intros H9; (try clear H7); (try exact H9) | intros H9; (try clear H7) | auto].
left; (try assumption).
apply pow_eq_R0 with m; auto.
right; auto.
auto.
assert
 (forall (X : R),
  X <> 0 ->
  X + 1 <> 0 ->
   sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ i) (n - S m) = 0).
intros.
elim H8 with ( X := X );
 [intros H11; (try clear H8); auto | intros H11; auto | auto].
intuition.
elim (zerop (n - S m)); intros.
rewrite <- (H9 1); auto with real.
rewrite a0; simpl.
NReplace (S (m + 0))%nat (S m).
ring.
apply deux.
assert
 (forall (X : R),
  X <> 0 ->
  X + 1 <> 0 ->
   sum_f_R0 (fun (i : nat) => a (S m + i)%nat * X ^ i) 0 +
   sum_f_R0
    (fun (i : nat) => a (S m + (1 + i))%nat * X ^ (1 + i)) ((n - S m) - 1) = 0).
intros.
rewrite <- (H9 X); auto.
rewrite (tech2 (fun (i : nat) => a (S m + i)%nat * X ^ i) 0%nat (n - S m));
 auto with arith.
assert
 (forall (X : R),
  X <> 0 ->
  X + 1 <> 0 ->
   a (S m) +
   X * sum_f_R0 (fun (i : nat) => a (S m + (1 + i))%nat * X ^ i) ((n - S m) - 1)
   = 0).
intros.
rewrite <- (H10 X); auto.
simpl.
rewrite scal_sum.
NReplace (S (m + 0)) (S m).
assert
 (sum_f_R0 (fun (i : nat) => (a (S (m + S i)) * X ^ i) * X) ((n - S m) - 1) =
  sum_f_R0 (fun (i : nat) => a (S (m + S i)) * (X * X ^ i)) ((n - S m) - 1)).
apply sum_eq; intros.
ring.
rewrite H13.
ring.
assert (forall (X : R),  a (S m) = 0).
intros.
pose (g:=
 fun (X : R) =>
 X * sum_f_R0 (fun (i : nat) => a (S m + (1 + i))%nat * X ^ i) ((n - S m) - 1)).
pose (f:= fun (X : R) => a (S m) + g X).
apply (unicite_limit_0_point_somme (a (S m)) f g); auto.
apply
 (continuity_pol_0_point
   ((n - S m) - 1) (fun (i : nat) => a (S m + (1 + i))%nat) g); auto.
apply H12; auto with real.
intros.
apply (H0 n); auto with arith.
Qed.
 
Lemma vector_X_point:
 forall (p : nat) (a b : nat ->  R),
 (forall X,
  X + 1 <> 0 ->
   sum_f_R0 (fun (i : nat) => a i * X ^ i) p =
   sum_f_R0 (fun (i : nat) => b i * X ^ i) p) ->
 forall j, (j <= p)%nat ->  a j = b j.
intros.
assert (a j - b j = 0).
apply (polynome_nul_point p (fun (i : nat) => a i - b i)); auto.
intros.
RReplace 0
         (sum_f_R0 (fun (i : nat) => a i * X ^ i) p -
          sum_f_R0 (fun (i : nat) => b i * X ^ i) p).
rewrite <- minus_sum.
apply sum_eq; intros.
ring.
rewrite H; auto.
ring.
RReplace (b j) (b j + 0).
rewrite <- H1.
ring.
Qed.
 
Lemma pow_Rmult: forall (x y : R) (n : nat),  (x * y) ^ n = x ^ n * y ^ n.
intros; (induction n; simpl).
auto with real.
RReplace ((x * x ^ n) * (y * y ^ n)) ((x * y) * (x ^ n * y ^ n)).
rewrite <- IHn.
ring.
Qed.
(*Polynomes de Bernstein (l,r)*)
Parameter RBern : nat -> nat -> R -> R -> R ->  R.
 
Axiom
   RBern_def :
   forall p i l r X,
   (i <= p)%nat ->
   r - l <> 0 ->
    RBern p i l r X =
    C p i * (Rdiv (X - l) (r - l) ^ i * Rdiv (r - X) (r - l) ^ (p - i)).
 
Definition translation (a : R) (f : R ->  R) := fun (x : R) => f (x - a).
 
Definition dilatation (a : R) (f : R ->  R) := fun (x : R) => f (x * a).
 
Definition inverse (n : nat) (f : R ->  R) := fun (x : R) => x ^ n * f (/ x).
 
Lemma translation_bij:
 forall a f g,
 (forall x,  g x = translation a f x) -> forall x,  f x = translation (- a) g x.
unfold translation; intros.
rewrite H.
RReplace ((x - - a) - a) x; auto.
Qed.
 
Lemma dilatation_bij:
 forall a f g,
 a <> 0 ->
 (forall x,  g x = dilatation a f x) -> forall x,  f x = dilatation (/ a) g x.
unfold dilatation; intros.
rewrite H0.
RReplace ((x * / a) * a) x; auto.
field; auto.
Qed.
 
Definition reverse (p : nat) (b : nat ->  R) := fun (i : nat) => b (p - i)%nat.
 
Lemma sigma_reverse:
 forall (p : nat) (b : nat ->  R),  sum_f_R0 b p = sum_f_R0 (reverse p b) p.
induction p; intros.
simpl; unfold reverse.
NReplace (0 - 0)%nat 0%nat; auto.
rewrite tech5; auto.
rewrite (tech2 (reverse (S p) b) 0 (S p)); auto.
simpl; unfold reverse.
NReplace (S p - 0)%nat (S p)%nat.
NReplace (p - 0)%nat p.
assert (sum_f_R0 b p = sum_f_R0 (fun (i : nat) => b (S p - S i)%nat) p).
rewrite IHp.
apply sum_eq; intros; unfold reverse.
NReplace (S p - S i)%nat (p - i)%nat; auto.
rewrite H; ring.
omega.
Qed.
 
Lemma inverse_pol:
 forall a f p,
 (forall X,  f X = sum_f_R0 (fun (i : nat) => a i * X ^ i) p) ->
 forall X,
 X <> 0 ->
  sum_f_R0 (fun (i : nat) => a (p - i)%nat * X ^ i) p =
  inverse p (fun (x : R) => f x) X.
unfold inverse; intros.
rewrite H.
rewrite scal_sum.
rewrite sigma_reverse.
apply sum_eq; intros; unfold reverse.
NReplace (p - (p - i))%nat i; auto.
pattern p at 2.
NReplace p ((p - i) + i)%nat.
RReplace ((a i * (/ X) ^ i) * X ^ ((p - i) + i))
         (a i * (X ^ ((p - i) + i) * / X ^ i)); auto.
rewrite <- pow_RN_plus; auto.
rewrite Rinv_pow; auto.
Qed.
 
Lemma transl_Bern:
 forall (p i : nat) (l r X : R),
 (i <= p)%nat ->
 r - l <> 0 ->
  translation (- l) (fun (x : R) => RBern p i l r x) X =
  C p i * ((X / (r - l)) ^ i * (((r - l) - X) / (r - l)) ^ (p - i)).
unfold translation; intros.
rewrite RBern_def; auto.
RReplace ((X - - l) - l) X.
RReplace (r - (X - - l)) ((r - l) - X); auto.
Qed.
 
Lemma dilat_transl_Bern:
 forall (p i : nat) (l r X : R),
 (i <= p)%nat ->
 r - l <> 0 ->
  dilatation (r - l) (translation (- l) (fun (x : R) => RBern p i l r x)) X =
  C p i * (X ^ i * (1 - X) ^ (p - i)).
unfold dilatation; intros.
rewrite transl_Bern; auto.
RReplace ((X * (r - l)) / (r - l)) X.
RReplace (((r - l) - X * (r - l)) / (r - l)) (1 - X); auto.
field; auto with real.
field; auto with real.
Qed.
 
Lemma inverse_dilat_transl_Bern:
 forall (p i : nat) (l r X : R),
 (i <= p)%nat ->
 r - l <> 0 ->
 X <> 0 ->
  inverse
   p (dilatation (r - l) (translation (- l) (fun (x : R) => RBern p i l r x))) X
  = C p (p - i) * (X - 1) ^ (p - i).
unfold inverse; intros.
rewrite dilat_transl_Bern; auto.
pattern p at 1.
NReplace p ((p - i) + i)%nat.
rewrite pow_add.
rewrite <- Rinv_pow; auto.
RReplace ((X ^ (p - i) * X ^ i) * (C p i * (/ X ^ i * (1 - / X) ^ (p - i))))
         ((X ^ i * / X ^ i) * (C p i * (X ^ (p - i) * (1 - / X) ^ (p - i)))).
RReplace (X ^ i * / X ^ i) 1; auto with real.
rewrite <- pow_Rmult.
RReplace (X * (1 - / X)) (X - 1).
rewrite pascal_step1; auto.
ring.
field; auto.
Qed.
 
Lemma transl_inverse_dilat_transl_Bern:
 forall (p i : nat) (l r X : R),
 (i <= p)%nat ->
 r - l <> 0 ->
 X + 1 <> 0 ->
  translation
   (- 1)
   (inverse
     p (dilatation (r - l) (translation (- l) (fun (x : R) => RBern p i l r x))))
   X = C p (p - i) * X ^ (p - i).
intros.
change
 (inverse
   p (dilatation (r - l) (translation (- l) (fun (x : R) => RBern p i l r x)))
   (X - - 1) = C p (p - i) * X ^ (p - i)).
rewrite inverse_dilat_transl_Bern; auto.
RReplace ((X - - 1) - 1) X; auto.
RReplace (X - - 1) (X + 1); auto.
Qed.
 
Lemma transl_inverse_dilat_transl_sigma_Bern:
 forall (p : nat) (l r X : R) (b : nat ->  R),
 r - l <> 0 ->
 X + 1 <> 0 ->
  translation
   (- 1)
   (inverse
     p
     (dilatation
       (r - l)
       (translation
         (- l)
         (fun (x : R) => sum_f_R0 (fun (i : nat) => b i * RBern p i l r x) p))))
   X = sum_f_R0 (fun (i : nat) => b i * (C p (p - i) * X ^ (p - i))) p.
unfold translation, inverse, dilatation, translation; intros.
rewrite scal_sum.
apply sum_eq; (intros j; intros).
rewrite <- (transl_inverse_dilat_transl_Bern p j l r X); auto.
unfold translation, inverse, dilatation, translation; ring.
Qed.
 
Lemma vector_X_point_reverse:
 forall (p : nat) (a b : nat ->  R),
 (forall X,
  X + 1 <> 0 ->
   sum_f_R0 (fun (i : nat) => a (p - i)%nat * X ^ (p - i)%nat) p =
   sum_f_R0 (fun (i : nat) => b (p - i)%nat * X ^ (p - i)%nat) p) ->
 forall j, (j <= p)%nat ->  a (p - j)%nat = b (p - j)%nat.
intros.
apply (vector_X_point p).
intros.
rewrite sigma_reverse.
symmetry.
rewrite sigma_reverse.
unfold reverse.
rewrite (H X); auto.
omega.
Qed.
(* si b0,....,bp sont les coefficients du polynome P dans la base Bern(l,r)
   on peut calculer les coefficients de P dans la base Xi*)
 
Theorem calcul_correct:
 forall (p : nat) (l r : R) (b a : nat ->  R),
 r - l <> 0 ->
 (forall X,
  X + 1 <> 0 ->
   translation
    (- 1)
    (inverse
      p
      (dilatation
        (r - l)
        (translation
          (- l)
          (fun (x : R) => sum_f_R0 (fun (i : nat) => b i * RBern p i l r x) p))))
    X = sum_f_R0 (fun (i : nat) => a i * X ^ i) p) ->
 forall j, (j <= p)%nat ->  a (p - j)%nat = C p j * b j.
intros.
assert (C p j * b j = C p (p - j) * b (p - (p - j))%nat).
NReplace (p - (p - j))%nat j.
rewrite <- pascal_step1; auto.
rewrite H2.
pose (c:= fun (i : nat) => C p i * b (p - i)%nat).
RReplace (C p (p - j) * b (p - (p - j))%nat) (c (p - j)%nat).
apply vector_X_point_reverse; auto.
intros.
unfold c.
assert
 (sum_f_R0
   (fun (i : nat) => (C p (p - i) * b (p - (p - i))%nat) * X ^ (p - i)) p =
  sum_f_R0 (fun (i : nat) => b i * (C p (p - i) * X ^ (p - i))) p).
apply sum_eq; intros.
NReplace (p - (p - i))%nat i.
ring.
rewrite H4.
rewrite <- (transl_inverse_dilat_transl_sigma_Bern p l r X b); auto.
rewrite (H0 X); auto.
symmetry.
rewrite sigma_reverse.
unfold reverse; auto.
Qed.
