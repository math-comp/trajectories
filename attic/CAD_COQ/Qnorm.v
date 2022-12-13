(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.


(*rationnal numbers are the ones in QArith, and operations are systematically
  normalizing*)

Require Export QArith.
Require Import Qabs.

 Definition Npred(n :N):N :=
   match n with
     |N0 => N0
     |Npos p => match p with
		  |xH => N0
		  |_ => Npos (Ppred p)
		end
   end.



 Definition Nminus(n m:N):N :=
   match n, m with
     |N0, _ => N0
     |_, N0 => n
     |Npos p, Npos q =>  match Pminus_mask p q with
			   |IsNeg => N0
			   |IsNul => N0
			   |IsPos p => Npos p
			 end
     end.


 Definition is_gt(p q:positive):bool :=
   match Pcompare p q Eq with
     |Gt => true
     |_ => false
   end.



(* euclidian division, for positives *)

 Fixpoint quo_rem(a b :positive){struct a} : N*N :=
  match a with 
    |xH => if (is_gt b xH) then (N0, Npos xH) else (Npos xH, N0)
    |xO a' => let (q', r') := quo_rem a' b in
      match r' with
	|N0 => (Ndouble q', N0)
	|Npos p' => if (is_gt b (xO p'))
	  then  (Ndouble q', Npos (xO p'))
	  else (Nsucc (Ndouble q'), Nminus (Npos (xO p')) (Npos b))
      end
    |xI a' => let (q',r') := quo_rem a' b in
      match r' with
	|N0 => if (is_gt b xH) then (Ndouble q', Npos xH) else (Npos a, N0)
	|Npos p' => if (is_gt b (xI p'))
	  then (Ndouble q', Npos (xI p'))
	  else (Nsucc (Ndouble q'), Nminus (Npos (xI p')) (Npos b))
      end
  end.


(*if a >b > 0 computes the simplification of (a,b) ie gcd free parts (a', b')*)
(*n for the termination, will be a*)
 Fixpoint remove_gcd_term(a b n: positive){struct n}: positive*positive :=
   let (q,r) := quo_rem a b in
     match r, q, n with
       |N0, N0, _ =>  (a,b) (* n'arrive jamais *)
       |N0, Npos q', _ => (q', xH)
       |_, _, xH => (a,b) (* n'arrive jamais *)
       |Npos r', N0, xO n'  => let (l,m) := (remove_gcd_term b r' n') in (m, l)
       |Npos r', N0, xI n' => let (l,m) := (remove_gcd_term b r' n') in (m, l)
       |Npos r', Npos q', xO n' =>
	 let (l,m) := (remove_gcd_term b r' n') in
	   (Pplus (Pmult l q') m, l)
       |Npos r', Npos q', xI n' =>
	 let (l,m) := (remove_gcd_term b r' n') in
	   (Pplus (Pmult l q') m, l)
     end.

 Definition remove_gcd(a b:positive):=remove_gcd_term a b a.
 
 (* normalization of fractions*)

 Definition Qsimpl(q:Q):Q :=
   match Qnum q with
     |Z0 => 0#1
     |Zpos a => let b := Qden q in
       match Pcompare a b Eq with
	 |Eq => 1#1
	 |Lt => let (b', a'):= (remove_gcd b a) in (Zpos a')#b' 
	 |Gt => let (a', b'):= (remove_gcd a b) in (Zpos a')#b'
       end
     |Zneg a => let b := Qden q in
       match Pcompare a b Eq with
	 |Eq => (Zneg xH)#1
	 |Lt => let (b', a'):= (remove_gcd b a) in (Zneg a')#b' 
	 |Gt => let (a', b'):= (remove_gcd a b) in (Zneg a')#b'
       end
   end.


(*first normalizing operations over rationnals *)
 Definition Qplus_r(x y : Q) := Qsimpl (Qplus x y).
 Definition Qmult_r(x y : Q) := Qsimpl (Qmult x y).
 Definition Qsub_r(x y : Q) := (Qplus_r x (Qopp y)).
 Definition Qdiv_r(x y : Q) := (Qmult_r  x (Qinv y)).
 Definition Qmake_r(n :Z)(d  : positive) := (Qsimpl (Qmake n d)).
 
 (*zero test for a normalized rationnal*)
 Definition Qzero_test(q:Q):=
   let (d,n) := q in
     match d with
       |Z0 => true
       |_ => false
     end.

(*the sig of a rationnal number is th one of its denom*)
 Definition Qsign := Qnum.
 
(*no need to use normalized mult to compute a power of a norm rational*) 
 Fixpoint Qpow_pos(q:Q)(i:positive){struct i}:Q:=
   match i with
     |xH => q
     |xO p => let q' := (Qpow_pos q p) in q'*q'
     |xI p => let q' := (Qpow_pos q p) in q * q' * q'
   end.

 Definition Qpow(q:Q)(i:N) : Q :=
   match i with
     |N0 => 1#1
     |Npos p => Qpow_pos q p
   end.

 Definition Q_abs_val(q:Q):=
   match Qnum q with
     |Zneg _ => - q
     |_ => q
   end.


 Definition Qlt_dec(q q':Q):=
   match Zcompare ((Zpos (Qden q'))*(Qnum q)) ((Zpos (Qden q))*(Qnum q')) with
     |Lt => true
     |_ => false
   end.



 Module Q_NORM_SYST <: RAT_STRUCT.

  Definition Rat := Q.

(*constants, operations over rationnals,
-MkRat builds a rationnal number from an integer and a positive
-RatEq is an eq relation over rationnals
-Rat_zero_test is a decidable test to the zero constant
-Rat_sign gives the sign of a rationnal : Z0 means it is zero, Zpos _, it is pos, ...
-Rat_pow builds a power of a rationnal, if the rat argument is
  normalized then the power is normalized
*)
   
   Definition  r0 := 0#1.
   Definition  r1 := 1#1.
   Definition  MkRat := Qmake_r.
   Definition  Norm(x:Rat) := x.
   Definition  radd := Qplus_r.
   Definition  ropp := Qopp.
   Definition  rprod := Qmult_r.
   Definition  rsub := Qsub_r.
   Definition  rinv := Qinv.
   Definition  rdiv := Qdiv_r.
   Definition  RatEq := Qeq.
   Definition  rlt := Qlt_dec.
   Definition  rzero_test := Qzero_test.
   Definition  rsign(x:Q) :=
     match Qnum x with
       |Z0 => Eq
       |Zpos _ => Gt
       |Zneg _ => Lt
     end.
   Definition  rpow := Qpow.
   Definition rabs_val := Q_abs_val.


   Notation "a # b" := (MkRat a b)(at level 55, no associativity) : rscope.

   Infix "+r" := radd(at level 50, left associativity) :rscope.
   Notation "-r x" := (ropp x)(at level 50, left associativity) : rscope.
   Infix  "*r" := rprod(at level 40, left associativity) : rscope.
   Infix "-r" := rsub(at level 35, right associativity) : rscope.
   Notation "/r x" := (rinv x)(at level 40, left associativity) : rscope.
   Infix "/r":= rdiv(at level 35, right associativity) : rscope.

   Notation "x == y" := (RatEq x y)(at level 70, no associativity) : rscope.

 
 Open Scope rscope.

 End Q_NORM_SYST.
















