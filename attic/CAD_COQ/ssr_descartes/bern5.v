Require Import ZArith List.
Open Scope Z_scope.

(* Just a few programs to test the ideas.  In particular, this shows
  that the composition translate then expand, reciprocate, and again translate
  does not yield directly the binomial coefficients, in the sens that
  they do not give the coefficients in the Bernstein polynomial basis.
  The discrepancy is simply a binomial coefficient.  Fortunately this does
  not the result on signs.
*)

(* binomial coefficients *)

Fixpoint bin (a b : nat) : Z :=
  match a, b with
    O, O => 1
  | O, S q => 0
  | S p, O => 1
  | S p, S q => bin p (S q) + bin p q
  end.

(* Now, a re-definition of the arithmetic on polynomials. *)
(* Fixpoint expandr (l : list Z) (ratio : Z) : list Z :=
  match l with a::tl => a * ratio :: expandr tl ratio |  nil => nil end. *)

Fixpoint mysum (f : nat -> Z) (n:nat) :=
  match n with S p => f p + mysum f p | _ => 0 end.

Fixpoint add_list (s1 s2 : list Z) :=
  match s1 with a::s1' => 
      match s2 with b::s2' => (a+b) :: add_list s1' s2' | _ => s1 end
  | _ =>  s2 end.

Fixpoint scal_mul (x : Z) (s : list Z) :=
  match  s with a::s' => (x * a) :: scal_mul x s' | _ => nil end.

Fixpoint mul_list (s1 s2 : list Z) :=
  match s1 with a::s1' => add_list (scal_mul a s2) (0::mul_list s1' s2) 
  | _ => nil end.

Fixpoint power_list (s1 : list Z) (n : nat) :=
  match n with S p => mul_list s1 (power_list s1 p) | _ => 1::nil end.

Fixpoint compose_list (s1 s2 : list Z) :=
  match s1 with
    a::nil => a::nil
  | a::s1' => add_list (a::nil) (mul_list s2 (compose_list s1' s2))
  | _ => nil end.

Definition expandr (s1 : list Z) (ratio : Z) :=
  compose_list s1 (0::ratio::nil).

Fixpoint transr (s : list Z) (offset : Z) : list Z :=
  compose_list s (offset::1::nil).

Fixpoint recipr n (s : list Z) := 
  match n with S p => 
    match s with a::tl => (recipr p tl)++(a::nil) 
    | nil => (recipr p nil)++(0::nil) end
 | 0%nat => nil
 end.

Definition bc n s l r := transr (recipr n (expandr (transr s l) (r - l))) 1.

(* Bernstein basis of degree 5 for the interval (0,1)
   is : bin 5 i * (1 - X)^(5-i) * x ^i *)

Definition B5_ (i:nat) := 
  fun x : Z => (bin 5 i) * Zpower_nat x (5 - i) * Zpower_nat (1 - x) i.

Definition B5'_(i : nat) (l r : Z) :=
  fun x : Z => 
    bin 5 i * Zpower_nat (x - l)  (5 - i) * Zpower_nat (r - x) i.

Definition pol_from_B (a b c d e f x : Z) :=
  a * B5_(0) x + b * B5_(1) x + c * B5_(2) x + d * B5_(3) x +
  e * B5_(4) x + f * B5_(5) x.

(* Working on integers brings a stupid constraint, because of division
  by the size of interval at power 5. *)

Definition pol_from_B' (l r a b c d e f x : Z) :=
  a * B5'_(0) l r x + b * B5'_(1)l r x + c * B5'_(2)l r x + d * B5'_(3)l r x +
  e * B5'_(4)l r x + f * B5'_(5)l r x.

Functional Scheme iter_nat_ind := Induction for iter_nat Sort Prop.

(* Using Coq as a symbolic engine to compute some polynomials from
  their Bernstein coefficients. *)

Ltac expand_bernstein :=
  intros; unfold pol_from_B, B5_, pol_from_B', B5'_; simpl minus; simpl bin;
  unfold Zpower_nat; repeat rewrite iter_nat_equation; ring_simplify.

Lemma example1 :
  forall x, pol_from_B 1 4 1 (-5) 3 1 x =
    (55*x^5 - 205 * x^4 + 240*x^3 - 100 * x^ 2 + 10 * x + 1). 
intros x; expand_bernstein.
trivial.
Qed.

Lemma example2 :
  forall x, pol_from_B' 2 4 1 4 1 (-5) 3 1 x = 55 * x^5 - 960 * x ^ 4 
              + 6440 * x ^ 3 - 20800 * x ^ 2 + 32400 * x - 19488.
intros x; expand_bernstein.
reflexivity.
Qed.

(* This list of coefficients is taken from the expanded formula exhibited
 in the lemma example1. *)
Definition ex1 : list Z :=  1::10::(-100)::240::(-205)::55::nil.

Definition ex2 : list Z := (-19488)::32400::(-20800)::6440::-960::55::nil.

Fixpoint zip (f : Z -> Z -> Z) (l1 l2 : list Z) :=
  match l1, l2 with a::l1', b::l2' => f a b::zip f l1' l2' | _, _ => nil end.

Lemma bc_right1 : bc 6 ex1 (0) (1) = 
  zip Zmult (1::4::1::(-5)::3::1::nil)
    (map (fun x => bin 5 x) (seq 0 6)).
unfold bc, ex1, seq.
simpl zip.
unfold expandr; simpl compose_list.
simpl recipr.
compute.
reflexivity.
Qed.

Lemma bc_right2 : bc 6 ex2 2 4 = 
      zip Zmult (1::4::1::(-5)::3::1::nil)
          (map (fun x => (4 - 2) ^ 5 * bin 5 x) (seq 0 6)).
reflexivity.
Qed.