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
 
Lemma C_nn: forall (n : nat),  C n n = 1.
intros; unfold C; simpl.
NReplace (n - n)%nat 0%nat.
simpl; field.
RReplace (INR (fact n) * 1) (INR (fact n)).
auto with real.
Qed.
 
Lemma C_n0: forall (n : nat),  C n O = 1.
intros.
rewrite <- (C_nn n).
rewrite pascal_step1.
NReplace (n - 0)%nat n; auto.
omega.
Qed.

Lemma util_C:
 forall (n i j : nat),
 (i <= j)%nat -> (j <= n)%nat ->  C n i * C (n - i) (j - i) = C j i * C n j.
intros.
assert (i <= n)%nat.
omega.
unfold C.
replace  ((n - i) - (j - i))%nat with (n - j)%nat;[ | omega].
field.
repeat split; auto with real.
Qed.
 
Lemma pow_Rmult: forall (x y : R) (n : nat),  (x * y) ^ n = x ^ n * y ^ n.
intros; (induction n; simpl).
auto with real.
RReplace ((x * x ^ n) * (y * y ^ n)) ((x * y) * (x ^ n * y ^ n)).
rewrite <- IHn.
ring.
Qed.
 
Lemma sum_f_permute:
 forall (f : nat -> nat ->  R) (n p : nat),
  sum_f_R0 (fun (i : nat) => sum_f_R0 (fun (j : nat) => f i j) p) n =
  sum_f_R0 (fun (j : nat) => sum_f_R0 (fun (i : nat) => f i j) n) p.
intros f; induction n; simpl; intros.
apply sum_eq; intros; auto.
rewrite IHn.
rewrite <- sum_plus.
apply sum_eq; intros; auto.
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
(* Formalisation de l'algorithme qui permet de calculer a partir de la liste b des coefficients de P
   dans la base RBern (l r) ses coefficients dans la base RBern (l m)*)
 
Fixpoint coef_algo (b : nat ->  R) (A B : R) (n : nat) {struct n} : nat ->  R :=
 match n with
   0 => b
  | S i =>
      fun (j : nat) => A * coef_algo b A B i j + B * coef_algo b A B i (j + 1)
 end.
(* l'input de l'algorithme correspond a la premiere ligne
  l'output de l'algorithme correspond a la premiere colonne*)
 
Definition output b A B := fun (i : nat) => coef_algo b A B i 0%nat.
(* l'output2 de l'algorithme correspond a l'hypotenuse du triangle*)
 
Definition output2 p b A B := fun (i : nat) => coef_algo b A B (p - i) i.
(* linearite de l'algorithme *)
 
Lemma add_coef_algo:
 forall k b c A B n,
  coef_algo (fun (j : nat) => b j + c j) A B k n =
  coef_algo b A B k n + coef_algo c A B k n.
induction k; intros; simpl; auto.
rewrite IHk.
rewrite IHk.
ring.
Qed.
 
Lemma scal_coef_algo:
 forall k b A B x n,
  coef_algo (fun (j : nat) => x * b j) A B k n = x * coef_algo b A B k n.
induction k; intros; simpl; auto.
rewrite IHk.
rewrite IHk.
ring.
Qed.
 
Lemma output_add:
 forall k b c A B,
  output (fun (j : nat) => b j + c j) A B k = output b A B k + output c A B k.
intros; unfold output.
rewrite add_coef_algo; auto.
Qed.
 
Lemma output_scal:
 forall k b A B x,  output (fun (j : nat) => x * b j) A B k = x * output b A B k.
intros; unfold output.
rewrite scal_coef_algo; auto.
Qed.
(* (fi) avec i<=n est une famille de suites, formalisation de la suite k ->(f0 + .....+fn) (k)*)
 
Definition sum_suite (f : nat -> nat ->  R) (n : nat) :=
   fun (k : nat) => sum_f_R0 (fun (i : nat) => f i k) n.
(* l'output d'une somme finie de listes correspond a la somme finie des outputs de chacune des listes*)
 
Lemma output_sumsuite:
 forall n f A B k,
  output (sum_suite f n) A B k =
  sum_f_R0 (fun (i : nat) => output (fun (j : nat) => f i j) A B k) n.
unfold sum_suite.
induction n; intros; simpl; auto.
rewrite (output_add
          k (fun (k0 : nat) => sum_f_R0 (fun (i : nat) => f i k0) n)
          (fun (j : nat) => f (S n) j)).
rewrite IHn; auto.
Qed.
(* formalisation des suites delta i*)
 
Definition delta (n p : nat) :=
   match eq_nat_dec n p with left _ => 1 | right _ => 0 end.
 
Lemma delta_ii: forall (i : nat),  delta i i = 1.
intros; unfold delta.
elim (eq_nat_dec i i); auto.
intuition.
Qed.
 
Lemma delta_ij: forall (i j : nat), i <> j ->  delta i j = 0.
intros; unfold delta.
elim (eq_nat_dec i j); auto.
intuition.
Qed.
 
Lemma decompose_sum_3:
 forall (f : nat ->  R) (n p : nat),
 (p < n)%nat ->
 (0 < p)%nat ->
  sum_f_R0 f n =
  (sum_f_R0 f (pred p) +
   (f p + sum_f_R0 (fun (i : nat) => f (S p + i)%nat) (n - S p)))%R.
intros.
rewrite (tech2 f p n); auto.
rewrite (sum_N_predN f p); auto.
ring.
Qed.
 
Definition ps_delta (f : nat ->  R) :=
   fun (k : nat) => fun (i : nat) => f k * delta k i.
(* f0, f1 ,....,fn une liste peut s'ecrire comme somme des fi * delta i*)
 
Theorem decompose_delta:
 forall (f : nat ->  R) (n k : nat),
 (k <= n)%nat ->  sum_suite (ps_delta f) n k = f k.
intros; unfold sum_suite, ps_delta.
case (zerop n); intros.
rewrite e; simpl.
NReplace k 0%nat.
rewrite delta_ii; ring.
case (le_lt_eq_dec k n); auto; intros H1.
case (zerop k); intros H2.
rewrite decomp_sum; auto.
rewrite H2.
rewrite delta_ii.
assert (sum_f_R0 (fun (i : nat) => f (S i) * delta (S i) 0) (pred n) = 0).
apply sum_eq_R0; intros.
rewrite delta_ij; auto with arith.
ring.
rewrite H0; ring.
rewrite (decompose_sum_3 (fun (i : nat) => f i * delta i k) n k); auto.
assert (sum_f_R0 (fun (i : nat) => f i * delta i k) (pred k) = 0).
apply sum_eq_R0; intros.
rewrite delta_ij; (try omega).
ring.
assert
 (sum_f_R0 (fun (i : nat) => f (S k + i)%nat * delta (S k + i) k) (n - S k) = 0).
apply sum_eq_R0; intros.
rewrite delta_ij; (try omega).
ring.
rewrite H3; rewrite H0; rewrite delta_ii; ring.
rewrite sum_N_predN; auto.
rewrite H1.
assert (sum_f_R0 (fun (i : nat) => f i * delta i n) (pred n) = 0).
apply sum_eq_R0; intros.
rewrite delta_ij; (try omega).
ring.
rewrite H0; rewrite delta_ii; ring.
Qed.
(* application de l'algorithme a delta (i+1)*)
 
Lemma translation_delta:
 forall k A B i j,
  coef_algo (delta (S i)) A B k (S j) = coef_algo (delta i) A B k j.
induction k; intros; simpl.
elim (eq_nat_dec i j); intros.
rewrite a.
(repeat rewrite delta_ii); auto.
repeat (rewrite delta_ij; intuition).
rewrite IHk.
rewrite IHk; auto.
Qed.
(* algorithme applique a delta_i (colonne j > i)*)
 
Lemma coef_algo_delta_col_supi:
 forall k A B i j, (j > i)%nat ->  coef_algo (delta i%nat) A B k j = 0.
induction k; intros; simpl.
rewrite delta_ij; intuition.
rewrite IHk; intuition.
rewrite IHk; intuition.
ring.
Qed.
(* algorithme applique a delta_i (ligne n ,colonne  i)*)
 
Lemma coef_algo_delta_col_i:
 forall n i A B,  coef_algo (delta i%nat) A B n i = A ^ n.
induction n; intros; simpl.
rewrite delta_ii; auto.
rewrite IHn.
rewrite coef_algo_delta_col_supi; intuition.
ring.
Qed.
(* algorithme applique a delta_i (colonne k avec k < i - j, ligne j avec j < i)*)
 
Lemma coef_algo_delta_ligne_infi_k:
 forall j i A B,
 (j < i)%nat ->
 forall k, (k < i - j)%nat ->  coef_algo (delta i%nat) A B j k = 0.
induction j; intros; simpl.
rewrite delta_ij; intuition.
rewrite IHj; intuition.
rewrite IHj; intuition.
ring.
Qed.
(* algorithme applique a delta_i (colonne 0, ligne j avec j < i)*)
 
Lemma coef_algo_delta_ligne_infi:
 forall j i A B, (j < i)%nat ->  coef_algo (delta i) A B j 0%nat = 0.
induction j; intros; simpl.
rewrite delta_ij; intuition.
rewrite IHj; intuition.
rewrite coef_algo_delta_ligne_infi_k; intuition.
ring.
Qed.
(* algorithme applique a delta_i (colonne 0, ligne i + k )*)
 
Lemma coef_algo_delta_ligne_sup_i:
 forall i k A B,
  coef_algo (delta i) A B (i + k) 0%nat = (C (k + i) i * A ^ k) * B ^ i.
induction i; intros; simpl.
rewrite coef_algo_delta_col_i.
rewrite C_n0.
ring.
rewrite translation_delta.
rewrite IHi.
elim k; simpl.
NReplace (i + 0)%nat i.
rewrite coef_algo_delta_ligne_infi_k; (try omega).
repeat rewrite C_nn.
ring.
intros.
NReplace (i + S n)%nat (S (i + n))%nat.
simpl.
rewrite translation_delta.
rewrite IHi.
rewrite H.
rewrite <- (pascal (n + S i) i); auto.
NReplace (S (n + i))%nat (n + S i)%nat.
ring.
omega.
Qed.
(*ouput de delta i*)
 
Theorem output_delta_infi:
 forall i j A B, (j < i)%nat ->  output (delta i) A B j = 0.
intros; unfold output.
rewrite coef_algo_delta_ligne_infi; auto.
Qed.
 
Theorem output_delta_supi:
 forall i j A B,
 (j >= i)%nat ->  output (delta i) A B j = (C j i * A ^ (j - i)) * B ^ i.
intros; unfold output.
pattern j at 1.
NReplace j (i + (j - i))%nat.
rewrite (coef_algo_delta_ligne_sup_i i (j - i)).
NReplace ((j - i) + i)%nat j; auto.
Qed.
(*avec une liste f0,....,fn, on peut calculer un "triangle" de coefficients du tableau *)
 
Lemma coef_algo_comp_eq:
 forall f g A B n,
 (forall k, (k <= n)%nat ->  f k = g k) ->
 forall i j,
 (i <= n)%nat -> (j <= n - i)%nat ->  coef_algo f A B i j = coef_algo g A B i j.
induction i; intros; simpl; auto.
rewrite H; auto.
omega.
rewrite IHi; auto.
rewrite IHi; auto.
omega.
omega.
omega.
omega.
Qed.
 
Lemma output_comp_eq:
 forall f g A B n,
 (forall k, (k <= n)%nat ->  f k = g k) ->
 forall i, (i <= n)%nat ->  output f A B i = output g A B i.
intros; unfold output.
rewrite (coef_algo_comp_eq _ _ A B _ H); auto.
omega.
Qed.
(* output b comme somme des output delta i *)
 
Lemma sum_output_delta:
 forall b A B n k,
 (k <= n)%nat ->
  output b A B k = sum_f_R0 (fun (i : nat) => b i * output (delta i) A B k) n.
intros.
assert (output b A B k = output (sum_suite (ps_delta b) n) A B k).
apply (output_comp_eq b (sum_suite (ps_delta b) n) A B n); auto.
intros; rewrite decompose_delta; auto.
rewrite H0.
rewrite output_sumsuite; auto.
unfold ps_delta.
apply sum_eq; intros.
rewrite (output_scal k (delta i) A B (b i)); auto.
Qed.
(* algorithme applique a la suite inversee*)
 
Lemma algo_reverse:
 forall b A B p i k,
 (i <= p)%nat ->
 (k <= p - i)%nat ->
  coef_algo (reverse p b) B A i k = coef_algo b A B i (p - (i + k)).
induction i; intros.
unfold reverse; simpl; auto.
simpl.
rewrite IHi; (try omega).
rewrite IHi; (try omega).
NReplace (p - (i + k))%nat ((p - S (i + k)) + 1)%nat.
NReplace (p - (i + (k + 1)))%nat (p - S (i + k))%nat.
ring.
Qed.
(* output2 en fonction de output de la suite inversee*)
 
Lemma ouput_reverse:
 forall b A B p i,
 (i <= p)%nat ->  output2 p b A B i = reverse p (output (reverse p b) B A) i.
intros.
change (output2 p b A B i = output (reverse p b) B A (p - i)).
unfold output, output2.
rewrite algo_reverse; (try omega).
NReplace (p - ((p - i) + 0))%nat i; auto.
Qed.
(*Polynomes de Bernstein (l,r)*)
Definition RBern p i l r X :=
  C p i *  (Rdiv (X - l) (r - l) ^ i * Rdiv (r - X) (r - l) ^ (p - i)).
 
Lemma
   RBern_def :
   forall p i l r X,
   (i <= p)%nat ->
   r - l <> 0 ->
    RBern p i l r X =
    C p i * (Rdiv (X - l) (r - l) ^ i * Rdiv (r - X) (r - l) ^ (p - i)).
intros; reflexivity.
Qed.

Lemma RBern_rl:
 forall p i l r X,
 (i <= p)%nat -> r - l <> 0 ->  RBern p i r l X = RBern p (p - i) l r X.
intros.
repeat (rewrite RBern_def; auto).
NReplace (p - (p - i))%nat i.
rewrite pascal_step1; auto.
RReplace ((X - l) / (r - l)) ((l - X) / (l - r)).
RReplace ((r - X) / (r - l)) ((X - r) / (l - r)).
ring.
field.
auto with real.
field.
auto with real.
omega.
auto with real.
Qed.
 
Lemma reverse_RBern:
 forall b p l r X P,
 r - l <> 0 ->
 P = sum_f_R0 (fun (i : nat) => b i * RBern p i l r X) p ->
  P = sum_f_R0 (fun (i : nat) => reverse p b i * RBern p i r l X) p.
intros.
rewrite H0.
rewrite sigma_reverse.
apply sum_eq; intros; unfold reverse.
rewrite <- RBern_rl; auto.
Qed.
 
Section RBernstein.
Variables X l r m : R.
Hypothesis neq_rl : r - l <> 0.
Hypothesis neq_ml : m - l <> 0.
Hypothesis neq_rm : r - m <> 0.
 
Definition A := Rdiv (r - m) (r - l).
 
Definition B := Rdiv (m - l) (r - l).
Hint Unfold A B :real.
 
Lemma pow_Xl_k:
 forall k,  Rdiv (X - l) (r - l) ^ k = B ^ k * Rdiv (X - l) (m - l) ^ k.
intros; unfold B.
rewrite <- pow_Rmult.
replace ((X - l) / (r - l)) with (((m - l) / (r - l)) * ((X - l) / (m - l)));
 auto.
field.
auto.
Qed.
 
Lemma dev_rX:
 Rdiv (r - X) (r - l) = A * Rdiv (X - l) (m - l) + Rdiv (m - X) (m - l).
unfold A.
field.
auto.
Qed.
 
Lemma pow_rX_n:
 forall n,
  Rdiv (r - X) (r - l) ^ n =
  sum_f_R0
   (fun (i : nat) =>
    (C n i * (A ^ i * Rdiv (X - l) (m - l) ^ i)) *
    Rdiv (m - X) (m - l) ^ (n - i)) n.
intros.
rewrite dev_rX.
rewrite binomial.
apply sum_eq; intros.
rewrite pow_Rmult; auto.
Qed.
 
Lemma RBern_sum:
 forall p k,
 (k <= p)%nat ->
  RBern p k l r X =
  C p k *
  sum_f_R0
   (fun (i : nat) =>
    (C (p - k) i * (A ^ i * (B ^ k * Rdiv (X - l) (m - l) ^ (i + k)))) *
    Rdiv (m - X) (m - l) ^ ((p - k) - i)) (p - k).
intros.
rewrite RBern_def; auto.
rewrite pow_Xl_k.
rewrite pow_rX_n.
rewrite scal_sum.
apply Rmult_eq_compat_l.
apply sum_eq; intros.
rewrite pow_add.
ring.
Qed.
 
Lemma RBern_lr_sum_RBern_lm:
 forall p k,
 (k <= p)%nat ->
  RBern p k l r X =
  sum_f_R0
   (fun (i : nat) => (C (i + k) k * (A ^ i * B ^ k)) * RBern p (i + k) l m X)
   (p - k).
intros.
rewrite RBern_sum; auto.
rewrite scal_sum.
apply sum_eq; intros.
rewrite RBern_def; auto.
NReplace (p - (i + k))%nat ((p - k) - i)%nat.
RReplace (((C (p - k) i * (A ^ i * (B ^ k * ((X - l) / (m - l)) ^ (i + k)))) *
           ((m - X) / (m - l)) ^ ((p - k) - i)) * C p k)
         (((B ^ k * (A ^ i * (C p k * C (p - k) i))) *
           ((m - X) / (m - l)) ^ ((p - k) - i)) * ((X - l) / (m - l)) ^ (i + k)).
replace (C (p - k) i) with (C (p - k) ((i + k) - k)).
rewrite (util_C p k (i + k)); (try omega).
ring.
NReplace ((i + k) - k)%nat i; auto.
omega.
Qed.
(* Ce theoreme exprime les RBern(l r) comme somme finie des Rbern (l m)*)
 
Theorem RBern_lr_sum_k_n_RBern_lm:
 forall p i,
 (i <= p)%nat ->
  RBern p i l r X =
  sum_f i p (fun (j : nat) => (C j i * (A ^ (j - i) * B ^ i)) * RBern p j l m X).
intros; unfold sum_f.
rewrite RBern_lr_sum_RBern_lm; auto.
apply sum_eq; intros j; intros.
NReplace ((j + i) - i)%nat j; auto.
Qed.
 
Lemma RBern_sigma_coef_algo:
 forall (p k : nat),
 (k <= p)%nat ->
  RBern p k l r X =
  sum_f_R0
   (fun (i : nat) => output (delta k) A B (i + k) * RBern p (i + k) l m X)
   (p - k).
intros; unfold output.
rewrite RBern_lr_sum_RBern_lm; auto.
apply sum_eq; intros.
pattern (i + k)%nat at 3.
NReplace (i + k)%nat (k + i)%nat.
rewrite coef_algo_delta_ligne_sup_i; ring.
Qed.
 
Lemma RBern_sigma_p:
 forall (p k : nat),
 (k <= p)%nat ->
  RBern p k l r X =
  sum_f_R0 (fun (i : nat) => output (delta k) A B i * RBern p i l m X) p.
intros.
rewrite RBern_sigma_coef_algo; auto.
case (zerop k); intros.
rewrite e.
NReplace (p - 0)%nat p.
apply sum_eq; intros.
NReplace (i + 0)%nat i; auto.
rewrite (tech2
          (fun (i : nat) => output (delta k) A B i * RBern p i l m X) (k - 1) p);
 auto.
assert
 (sum_f_R0 (fun (i : nat) => output (delta k) A B i * RBern p i l m X) (k - 1) =
  0).
apply sum_eq_R0; intros.
rewrite output_delta_infi; (try omega).
ring.
rewrite H0.
NReplace (S (k - 1))%nat k.
ring_simplify.
apply sum_eq; intros.
NReplace (k + i)%nat (i + k)%nat; auto.
omega.
Qed.
(*input : b0,....,bp : calul explicite de l'output*)
 
Lemma output_sum_C:
 forall (b : nat ->  R) (p k : nat),
 (k <= p)%nat ->
  output b A B k =
  sum_f_R0 (fun (i : nat) => b i * ((C k i * A ^ (k - i)) * B ^ i)) k.
intros.
rewrite (sum_output_delta b A B p); auto.
elim (eq_nat_dec k p); intros.
rewrite a.
apply sum_eq; intros.
rewrite output_delta_supi; auto.
rewrite (tech2 (fun (i : nat) => b i * output (delta i) A B k) k p).
assert
 (sum_f_R0
   (fun (i : nat) => b (S k + i)%nat * output (delta (S k + i)) A B k) (p - S k)
  = 0).
apply sum_eq_R0; intros.
rewrite output_delta_infi; (try omega).
ring.
rewrite H0.
ring_simplify.
apply sum_eq; intros.
rewrite output_delta_supi; auto.
omega.
Qed.
(* si b0,....,bp sont les coefficients du polynome P dans la base Bern(l,r)
   alors (output b)0,....,(output b)p sont les coefficients de P dans la base Bern(l,m)*)
 
Theorem algo_correct:
 forall (b : nat ->  R) (p : nat) (P : R),
 P = sum_f_R0 (fun (i : nat) => b i * RBern p i l r X) p ->
  P = sum_f_R0 (fun (i : nat) => (output b A B) i * RBern p i l m X) p.
intros.
pose (f:=
 fun (j : nat) =>
 fun (i : nat) => b i * (output (delta i) A B j * RBern p j l m X)).
assert
 (sum_f_R0 (fun (i : nat) => b i * RBern p i l r X) p =
  sum_f_R0 (fun (i : nat) => sum_f_R0 (fun (j : nat) => f i j) p) p).
rewrite sum_f_permute.
apply sum_eq; intros k; intros.
rewrite RBern_sigma_p; auto.
rewrite scal_sum.
apply sum_eq; intros i; intros.
unfold f; ring.
rewrite H; rewrite H0.
apply sum_eq; intros i; intros.
rewrite (sum_output_delta b A B p i); auto.
rewrite Rmult_comm.
rewrite scal_sum.
apply sum_eq; intros j; intros.
unfold f; ring.
Qed.
 
End RBernstein.
 
Lemma A_rl: forall l r m, l - r <> 0 ->  A r l m = B l r m.
unfold A, B; intros.
field.
auto with real.
Qed.
 
Lemma B_rl: forall l r m, l - r <> 0 ->  B r l m = A l r m.
unfold A, B; intros.
field.
auto with real.
Qed.
(* si b0,....,bp sont les coefficients du polynome P dans la base Bern(l,r)
   alors (output2 b)0,....,(output2 b)p sont les coefficients de P dans la base Bern(m,r)*)
 
Theorem algo_correct2:
 forall (X l r m P : R) (b : nat ->  R) (p : nat),
 l - r <> 0 ->
 m - r <> 0 ->
 P = sum_f_R0 (fun (i : nat) => b i * RBern p i l r X) p ->
  P =
  sum_f_R0
   (fun (i : nat) => output2 p b (A l r m) (B l r m) i * RBern p i m r X) p.
intros.
assert
 (P =
  sum_f_R0
   (fun (i : nat) => output2 p b (A l r m) (B l r m) i * RBern p (p - i) r m X)
   p).
assert (P = sum_f_R0 (fun (i : nat) => reverse p b i * RBern p i r l X) p).
rewrite (reverse_RBern b p l r X P); auto with real.
rewrite (algo_correct X r l m H H0 (reverse p b) p P); auto.
rewrite sigma_reverse; auto.
apply sum_eq; intros.
change
 (output (reverse p b) (A r l m) (B r l m) (p - i) * RBern p (p - i) r m X =
  output2 p b (A l r m) (B l r m) i * RBern p (p - i) r m X).
rewrite ouput_reverse; auto.
rewrite B_rl; auto with real.
rewrite A_rl; auto with real.
rewrite H2; auto.
apply sum_eq; intros.
rewrite <- RBern_rl; auto with real.
Qed.
(* si b0,....,bp sont les coefficients du polynome P dans la base Bern(l,r)
   alors l'algorithme donnent les coefficients de P dans la base Bern(l,m) et dans la base Bern(m,r)*)
 
Theorem conclusion:
 forall (X l r m P : R) (b : nat ->  R) (p : nat),
 l - r <> 0 ->
 m - l <> 0 ->
 m - r <> 0 ->
 P = sum_f_R0 (fun (i : nat) => b i * RBern p i l r X) p ->
  and
   (P =
    sum_f_R0
     (fun (i : nat) => output b (A l r m) (B l r m) i * RBern p i l m X) p)
   (P =
    sum_f_R0
     (fun (i : nat) => output2 p b (A l r m) (B l r m) i * RBern p i m r X) p).
intros.
split.
apply algo_correct; auto with real.
apply algo_correct2; auto with real.
Qed.
