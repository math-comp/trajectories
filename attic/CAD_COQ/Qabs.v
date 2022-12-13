(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.



Require Export ZArith.
Require Export Mylist.
Require Import Setoid.
Require Import Utils.

Definition Is_true (b:bool) : Prop:=
match b with
|true => True
|false => False
end.


(*in order to test the efficency, depending to when the reduction of
  rationnals is performed*)

 Module Type RAT_STRUCT.
   
   Parameter Rat : Set.

   Bind Scope rscope with Rat.   
   Open Scope rscope.

 

(*constants, operations over rationnals,
-MkRat builds a rationnal number from an integer and a positive
-RatEq is an eq relation over rationnals
-rzero_test is a decidable test to the zero constant
-rsign gives the sign of a rationnal : Z0 means it is zero, Zpos _, it is pos, ...
-rpow builds a power of a rationnal, if the rat argument is
  normalized then the power is normalized
*)
   
   Parameter  r0 : Rat.
   Parameter  r1 : Rat.
   Parameter  MkRat : Z -> positive -> Rat.
   Parameter  Norm : Rat -> Rat.
   Parameter  radd : Rat -> Rat -> Rat.
   Parameter  ropp : Rat -> Rat.
   Parameter  rprod : Rat -> Rat -> Rat.
   Parameter  rsub : Rat -> Rat -> Rat.
   Parameter  rinv : Rat -> Rat.
   Parameter  rdiv : Rat -> Rat -> Rat.
   Parameter  RatEq : Rat -> Rat -> Prop.
   Parameter  rzero_test : Rat -> bool.
   Parameter  rlt : Rat -> Rat -> bool.
   Parameter  rsign : Rat -> comparison.
   Parameter  rpow : Rat -> N -> Rat.
   Parameter  rabs_val : Rat -> Rat.


   Notation "a # b" := (MkRat a b)(at level 20, no associativity) : rscope.

   Infix "+r" := radd(at level 50, left associativity) :rscope.
   Notation "-r x" := (ropp x)(at level 50, left associativity) : rscope.
   Infix  "*r" := rprod(at level 40, left associativity) : rscope.
   Infix "-r" := rsub(at level 35, right associativity) : rscope.
   Notation "/r x" := (rinv x)(at level 40, left associativity) : rscope.
   Infix "/r":= rdiv(at level 35, right associativity) : rscope.

   Notation "x == y" := (RatEq x y)(at level 70, no associativity) : rscope.

 
 Open Scope rscope.

 End RAT_STRUCT.


 Module RAT_FUNS(Q:RAT_STRUCT).

   Import Q.
   Definition rof_Z(x : Z) := (MkRat x 1).
   Definition rof_pos(i:positive) := (rof_Z (Zpos i)).
   Definition rof_N(n:N):=
     match n with
       |N0 => r0
       |Npos p => (rof_pos p)
     end.
   
   
 Definition fact'(n m:positive):positive:=  ((Psucc n)*m)%positive.

 Definition rfact(n:N):=
   match n with
     |N0 => r1
     |Npos p => rof_pos (Prec positive xH fact' p)
   end.

   (*binomial coefficient C(n,p)*)(*pareil,c'est surement ameliorable*)
 Definition rbinomial(n p:N):Rat:=
   match Ncompare n p with
     |Eq => r1
     |Lt => r1 (*should nt happen!*)
     |Gt => (rfact n) /r ((rfact p) *r (rfact (Nminus n  p)))
   end.


 Fixpoint rmax_list(l:list Rat):Rat:=
   match l with
     |nil => r0
     |r::l' =>
       match l' with
	 |nil => r
	 |_ =>
	   let m:= rmax_list l' in
	     if rlt r m 
	       then m
	       else r
       end
   end.

 Fixpoint rmin_list(l:list Rat):Rat:=
   match l with
     |nil => r0
     |r::l' =>
       match l' with
	 |nil => r
	 |_ =>
	   let m:= rmin_list l' in
	     if rlt r m 
	       then r
	       else m
       end
   end.





 Definition rle(q q':Rat) := orb (rlt q q') (rzero_test (q -r q')).


 Definition rmin(q q':Rat):=
   if rle q q' then q else q'.


 Definition rmax(q q':Rat):=
   if rle q q' then q' else q.




   End RAT_FUNS.


Module RAT_INT_OPS(Q:RAT_STRUCT).
Module QFUNS := RAT_FUNS Q.
Import Q.
Import QFUNS.

Definition req(r r':Rat):=rzero_test (rsub r r').

Definition rmin4(a b c d:Rat):=
rmin a (rmin b (rmin c d)).


Definition rmax4(a b c d:Rat):=
rmax a (rmax b (rmax c d)).


(* Very naive interval arithmetic for bound computations *)

(* [a,b]+[c,d], a<=b and c<=d *)
Definition radd_int(a b c d:Rat):=((radd a c), (radd b d)).

(* [a,b]*[c,d], a<=b and c<=d *)
Definition rprod_int(a b c d:Rat):= 
((rmin4 (rprod a c) (rprod a d) (rprod b c) (rprod b d)),
(rmax4 (rprod a c) (rprod a d) (rprod b c) (rprod b d))).

(*[a,b]^i, a<=b*)
Definition rpow_int_pos:=
fix ipow(a b:Rat)(i:positive){struct i}:Rat*Rat:=
          match i with
	|xH => (a,b)
	|xO p => let (c,d) := ipow a b p in rprod_int c d c d
	|xI p =>
	let (c,d) := ipow a b p in
	let (c',d') := (rprod_int c d c d) in
	rprod_int c' d' a b
	end.

Definition rpow_int(a b:Rat)(n:N):=
 match n with
  |N0 => (r1,r1)
  |Npos p =>rpow_int_pos a b p
end.


Definition rdiv_int(a b c d:Rat):=
(rmin4 (rdiv a c) (rdiv a b) (rdiv b c)  (rdiv b d),
rmax4 (rdiv a c) (rdiv a b) (rdiv b c)  (rdiv b d)).








End RAT_INT_OPS.
