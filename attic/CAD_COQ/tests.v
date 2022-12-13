(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

(* pour commencer

 Require Import Utils.
 Require Import CAD_types.
 Require Import One_dim.
 Require Import Tarski.

 
 Require Import Qnorm.
 Module Q:= Q_NORM_SYST.
 Import Q.

 Module myCAD := CAD_gen Q.
 Import myCAD.

 Module ONE := MK_ONE_DIM Q.
 Import ONE.

 

(* Notations for polynomials *)
Infix "*":= Pol_mul.
Infix "+":= Pol_add.
Infix "-":= Pol_sub.
Notation "- x" := (Pol_opp x).
Notation "P ^ i":= (Pol_pow P i).
Notation "c ** P":= (Pol_mul_Rat P c)(at level 40, no associativity).


Fixpoint Q_of_nat(n:nat):Q:=
  match n with
    |O => r0
    |S n => r1Print mkCad. +r (Q_of_nat n)
  end.

 Definition P:=((Q_of_nat 9) ** X^6) - 
((Q_of_nat 27) ** X^4) - ((Q_of_nat 27) ** (X^3)) + ((Q_of_nat 72) ** ( X^2)) + ((Q_of_nat 18) ** X) - (Pc (Q_of_nat 45)).


Definition P2 := ((Q_of_nat 3) ** ( X^4)) - ((Q_of_nat 4) ** (X^2)) -((Q_of_nat 9) ** X) + (Pc (Q_of_nat 21)).

 
(* Printers for sign_tables *)

(* Printing real numbers : erasure of the coding of alg.numbers, keeping
  only the interval *)
Inductive short_rpoint:Set:=
|Minfty : short_rpoint   (* -infty, useless *)
|B : Rat -> short_rpoint  (* a rational point between 2 roots*)
|R : Rat -> short_rpoint (* a rational root *)
|AR : Rat -> Rat -> short_rpoint. (* an algebraic root in th interval*)


Definition print_rpoint(z:Rpoint):=
match z with
|Minf _ => Minfty
|Between b => B b
|Root r => R r
|Alg_root z =>
  let (a, b, _, _, _):= z in AR a b
end.

Definition print_col(c:Rpoint * (list (Pol*Sign))):=
  let (r, csign):= c in
    (print_rpoint r, map (fun x => snd x) csign).


(* a printed sign table is a list of columns, a column :(Rpoint, list
  short_rpoint) is indexed by the short representation of a real
  number and is a list of signs for the polynomials of the family
  considered *)
Definition print_table(t : list (Rpoint * (list (Pol * Sign)))):=
  map print_col t.


(**************************************************************************)
(************** Builds P1(n) :=(X - n)(X - (n+1))....(X - 3n) **************)
(**************************************************************************)

Definition root_prod_n_3n(n:nat):=
  let aux := fix aux(m:nat):Pol :=
    match m with
      |O => (Pc r0)
      |S O => (PX (Pc r1) xH (-r (Q_of_nat (S n))))*
	(PX (Pc r1) xH (-r (Q_of_nat (2*n +1))))
      |S m' => (PX (Pc r1) xH (-r (Q_of_nat (n+m))))*
	(PX (Pc r1) xH (-r (Q_of_nat ((2*n)+m))))*(aux m')
    end in
    aux n.

(**************************************************************************)
(*****************  Builds P2(n) :=(X -1)(X -2)...(X -2n)  *****************)
(**************************************************************************)

Definition root_prod_1_2n(n:nat):=
 let aux := fix aux(m:nat):Pol :=
    match m with
      |O => (Pc r0)
      |S O => (PX (Pc r1) xH (-r (Q_of_nat (S n))))*
	(PX (Pc r1) xH (-r (Q_of_nat n)))
      |S m'=> (PX (Pc r1) xH (-r (Q_of_nat m)))*
	(PX (Pc r1) xH (-r (Q_of_nat (n+m))))*(aux m')
    end in
    aux n.
 
(**************************************************************************)
(************  Builds the list [X, (X-1),(X-2),...,(X-(n-1))] *************)
(**************************************************************************)

Fixpoint mono_list(n:nat):list (Pol1 Q):=
  match n with
    |O => (PX (Pc r1) xH (-r r0))::nil
    |S m => (PX (Pc r1) xH (-r (Q_of_nat m)))::(mono_list m)
  end.

(**************************************************************************)
(*****************  Computing  sign tables, examples  *********************)
(**************************************************************************)

Definition test(n:nat):= 
print_table (sign_table ((root_prod_1_2n n)::(root_prod_n_3n n)::nil) 90).


(* Temps sur valpareso *)
Time Eval compute in (test 2).
(*Finished transaction in 24. secs (23.6u,0.02s)*)


Time Eval vm_compute in (test 2).
(*Finished transaction in 2. secs (2.41u,0.s)*)

Time Eval vm_compute in (test 3).
(*Finished transaction in 98. secs (95.85u,0.s)*)
(* sans la vm ca passe pas...curieux...*)

*)
(********************************************************************)
(*******          Des testes en plus de variable                *****)
(********************************************************************)





 Require Import Utils.
 Require Import CAD_types.
 Require Import One_dim.
 Require Import Up_dim.
 Require Import Tarski.

 
 Require Import Qnorm.
 Module Q:= Q_NORM_SYST.
 Import Q.

 Module myCAD := CAD_gen Q.
 Import myCAD.

(* Module ONE := MK_ONE_DIM Q.

 Module UP := MK_UP_DIM Q.
*)

 Definition onevar := CAD_build O.
 Definition twovar := CAD_build 1.

Set Implicit Arguments.

(* Pour l'affichage *)

(*
Definition cell_type(Coef berncoef cell_point:Set) :=
(mkcell_point_up Rat Coef berncoef cell_point *
          list (Pol1 Coef * Sign))%type.


Definition polsign_of_cell(Coef berncoef cell_point:Set)
  (x:cell_type Coef berncoef cell_point):=
let (_,l1):=x in
l1.

Definition sign_of_cell(Coef berncoef cell_point:Set)
  (x:cell_type Coef berncoef cell_point):=
let (_,l1):=x in
map (fun x => snd x) l1.


Definition print_sign_res(Coef berncoef cell_point:Set)
  (l:list (list (cell_type Coef berncoef cell_point))):=
  map (fun x => map (@sign_of_cell Coef berncoef cell_point) x) l.

Definition print_polsign_res(Coef berncoef cell_point:Set)
  (l:list (list (cell_type Coef berncoef cell_point))):=
  map (fun x => map (@polsign_of_cell Coef berncoef cell_point) x) l.



Definition test_sign(l:list (Pol1 (Poln 1)))(n:nat):=
  print_sign_res (Pol_cad twovar l n).



Definition test_polsign(l:list (Pol1 (Poln 1)))(n:nat):=
  print_polsign_res (Pol_cad twovar l n).


*)
Fixpoint Q_of_nat(n:nat):Q:=
  match n with
    |O => r0
    |S n => r1 +r (Q_of_nat n)
  end.


Definition X := PX (Pc (Pc r1)) 1 (Pc r0).

Definition Y := Pc (PX (Pc r1) 1  r0).

Definition Pol := (Pol1 (Poln 1)).

Bind Scope P_scope with Pol.
Open Scope P_scope.

Definition plus := Pol_add twovar.
Definition minus := Pol_sub twovar.
Definition prod := Pol_mul twovar.



Infix "+":=plus:P_scope.
Infix "-":=minus:P_scope.
Infix "*":=prod:P_scope.


Definition circle := ((X * X) + (Y * Y) - (Pc (Pc r1))).

Eval vm_compute in (Pol_cad twovar (circle::nil) 90).
Eval vm_compute in (test_sign ((Y*Y)::nil) 90).


Module UP := MK_UP_DIM Q.

Let l:= (X*X)::nil.

(* WARNING pas de compute cad*)
Let cad := UP.ccad onevar (UP.elim onevar l) 90.

Check cad.

Check (head cad).

Variable void :mkcell_point_up Q (Poln 0) (Infon 0) (cell_pointn 0).
Let c := 
match (head cad) with Some u =>u |_ => (void,nil) end.

Eval vm_compute in c.

Let z := fst c.
Let col := snd c.


Let zl':= UP.non_deg onevar z col l 90.

Eval vm_compute in zl'.

Let z' := fst zl'.
Let l' := snd zl'.

Eval vm_compute in l'.

Eval vm_compute in (UP.sign_table onevar z' l' 90).

Require Import Qabs.
Module QF := RAT_FUNS Q.
Let up := QF.rmax_list (map (UP.Pol_info_up_bound onevar z') l'). 
(*4*)
Let low := QF.rmin_list (map (UP.Pol_info_low_bound onevar z') l').
(*-4*)

Let zroots := UP.family_root onevar low up z' l' 90.

Eval vm_compute in zroots.

Variable void2 :UP.Info (Poln 0).

Let i := match (head l') with Some u => u |None => void2 end.

Eval vm_compute in i.


Let P:= fst5 i.
Let Pbar:= match i with
Five _ u _ _ _ => u end.
Let dPbar := match i with
Five _ _ u _ _ => u end.
Let slow:= match  i with
Five _ _ _  u _ => u end.
Let  sinfo := match i with
Five _ _ _ _ u => u end.

Let res := UP.root_isol onevar P z Pbar dPbar low up 90.

Eval vm_compute in res.

Eval vm_compute in (UP.Pol_low_sign onevar z' P Pbar 90).
(* ok*)
Let z2sign := UP.Pol_low_sign onevar z' P Pbar 90.

Eval vm_compute in slow.
Let sign := snd z2sign.
Let z2 := fst z2sign.
Eval vm_compute in sign.
Eval vm_compute in (UP.Pol_bern_coefs onevar (X*X) low up dPbar).


Eval vm_compute in (length (snd zroots)).

(*
(tt, Between (Poln 0) (Infon 0) ((-2) # 1)%Q,
       (Pc (2 # 1)%Q, Some Gt) :: (Pc (1 # 1)%Q, Some Gt) :: nil)*)



Eval vm_compute in (UP.one_table_up onevar l 90 c).



Definition XY:= X * Y.


Eval vm_compute in (test_sign (Y::circle::nil) 90).

Eval vm_compute in (test_sign (X::circle::nil) 90).
