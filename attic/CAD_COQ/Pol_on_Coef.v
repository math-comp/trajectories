(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)

(* WARNING : Not to be compiled!!!

This defines operations on polynomials defined as Pol1 Coef given

Coef:Set
cdeg : Coef -> N
c0 : coef
c1 : Coef
cadd : Cooef -> Coef -> Coef
cmul : Cooef -> Coef -> Coef
copp : Coef -> Coef
csub : Coef -> Coef -> Coef
czero_test : Cof -> bool
cpow : Coef -> N -> Coef
*)






 Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
 Notation "x ** y":= (cmul x y) (at level 40, left associativity).
 Notation "-- x" := (copp x) (at level 35, right associativity).
 Notation "x -- y" := (csub x y) (at level 50, left associativity).





 (************************************************************)
 (**              Polynomials with one  variable            **)
 (************************************************************)


(*Definition Pol := (Pol1 Coef).*)
Notation Pol := (Pol1 Coef).

Notation P0 := (Pc c0).
Notation P1 := (Pc c1).
Notation X :=  (PX (Pc c1) xH c0).
 
Definition mkPX P i c := 
  match P with
  | Pc p => if (czero_test p) then Pc c else PX P i c
  | PX P' i' c' => if (czero_test c') then PX P' (i' + i) c else PX P i c
  end.




 (*************************************************************)
 (**       Integral domain operations  over polynomials      **)  
 (*All the following defined operations preserve normalisation*)
 (*************************************************************)



(** Opposite **)
 Definition Pol_opp:=fix Pol_opp (P:Pol):Pol :=
   match P with
     |Pc p => Pc (-- p)
     |PX P i p => mkPX (Pol_opp P) i (-- p)
   end.

Notation "- P" := (Pol_opp P).


(** Addition and subtraction **)
 
(*P+Pc c*)
 Definition Pol_addC (P:Pol)(c:Coef):Pol :=
  match P with
  | Pc c1 => Pc (c1 ++ c)
  | PX P i c1 => PX P i (c++c1)
  end.

(*P - Pc c*)
 Definition Pol_subC (P:Pol) (c:Coef) : Pol :=
  match P with
  | Pc c1 => Pc (c1 -- c)
  | PX P i c1 => PX P i (c1 -- c)
  end.

 
(*Pop is Padd _ P' where P' is a fixed poynomial*)
 Definition Pol_addX(Pol_op:Pol->Pol)(P':Pol):=
   fix Pol_addX(i':positive)(P:Pol) {struct P} : Pol :=
     match P with
       | Pc c => PX P' i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pol_op (PX P k c0)) i' c
	   | Z0 => mkPX (Pol_op P) i c
	  | Zneg k => mkPX (Pol_addX k P) i c
	 end
     end.
   

(*P-P'*X^i'*)
(*Pop is Padd _ P' *)
 Definition Pol_subX(Pol_op:Pol->Pol)(P':Pol):=
   fix Pol_subX(i':positive)(P:Pol){struct P} : Pol :=
     match P with
       | Pc c => PX (- P') i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pol_op (PX P k c0)) i' c
	   | Z0 => mkPX (Pol_op P) i c
	   | Zneg k => mkPX (Pol_subX k P) i c
	 end
     end.
 
 
 (* Inv : is_norm P, is_norm P' *)
 Definition Pol_add := fix Pol_add (P P': Pol) {struct P'} : Pol :=
   match P' with
     | Pc c' => Pol_addC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX P' i' (c ++ c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Pol_add (PX P k c0) P') i' (c ++ c')
	     | Z0 => mkPX (Pol_add P P') i (c ++ c')
	     | Zneg k => mkPX (Pol_addX (fun x => Pol_add x P') P' k P) i (c ++ c')
	   end
       end
   end.
 Notation "P + P'" := (Pol_add P P').

 Definition Pol_sub :=
   fix Pol_sub (P P': Pol) {struct P'} : Pol :=
   match P' with
     | Pc c' => Pol_subC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX (- P') i' (c -- c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Pol_sub (PX P k c0) P') i' (c -- c')
	     | Z0 => mkPX (Pol_sub P P') i (c -- c')
	     | Zneg k => mkPX (Pol_subX (fun x => Pol_sub x P') P' k P) i (c -- c')
	   end
       end
   end.
 Notation "P - P'" := (Pol_sub P P').
 
 (** Multiplication *) 


(*P*(Pc c) *)
 Definition Pol_mul_Rat_aux :=
   fix Pol_mul_Rat_aux (P:Pol) (c:Coef) {struct P} : Pol :=
     match P with
       | Pc c' => Pc (c' ** c)
       | PX P i c' => mkPX (Pol_mul_Rat_aux P c) i (c'** c)
     end.

(*hack to speed up*)
 Definition Pol_mul_Rat P c :=
  if (czero_test c) then P0 else
  if (czero_test (c -- c1)) then P else Pol_mul_Rat_aux P c.

 
 Definition Pol_mul := fix Pol_mul(P P':Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => Pol_mul_Rat P c'
  | PX P' i' c' => 
     (mkPX (Pol_mul P P') i' c0) + (Pol_mul_Rat P c')
  end.

 Notation "P * P'" := (Pol_mul P P').


 (** Zero test for pols in normal form **)
 Definition Pol_zero_test(P:Pol):bool:=
   match P with
     |Pc c => (czero_test c)
     |PX _ _ _=> false
   end.


 (*P^n*)
 Definition Pol_pow':=
   fix Pol_pow'(P:Pol)(p:positive){struct p}:Pol:=
     match p with
       |xH => P
       |xO p' => let Q:=(Pol_pow' P p') in (Pol_mul Q Q)
       |xI p' => let Q:=(Pol_pow' P p') in (Pol_mul (Pol_mul Q Q) P)
     end.

 Definition Pol_pow(P:Pol)(n:N):Pol :=
   match n with
     |N0 => P1
     |Npos p => Pol_pow' P p
   end.



 (** Derivative **)
 Definition Pol_deriv := 
   fix Pol1_deriv(P:Pol):Pol :=
     match P with
       |Pc c => Pc c0
       |PX A i a => 
	 match i with
	   |xH => A +(mkPX (Pol1_deriv A) xH c0)
	   |_ => (Pol_mul_Rat (PX A (Ppred i) c0) (cof_pos i)) +
	     (mkPX (Pol1_deriv A) i c0)
	 end
     end.
   



 
  (** evaluation of a Pol1 at an element of the Coef set *)
 Definition Pol_eval :=
   fix Pol1_eval(P:Pol)(x:Coef){struct P} : Coef :=
     match P with
       |Pc c =>  c
       |PX A i a => ((Pol1_eval A x)** (cpow x (Npos i))) ++ a
     end.

