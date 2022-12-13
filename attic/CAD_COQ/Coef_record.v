
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)

(*Require Import Ring_tac.
Require Import Pol.
Require Import Ring_theory.
Require Import Setoid.*)
Require Import ZArith.


Set Implicit Arguments.
(* La version de Coef.v avec des records, parce que sinon on est
  coince avec les modules pour prouvers les fonctions charges par des
  Load dans le code*)



Section  COEF_STRUCT.

      (*Carrier*)
  Variable Coef :Set.


  Record Coef_ops : Set := mk_c {
      (* Operations on coefs *)
    Cdeg : Coef -> N;
    C0 : Coef;
    C1 : Coef;
    Cadd : Coef -> Coef -> Coef;
    Cmul : Coef -> Coef -> Coef;
    Copp : Coef -> Coef;
    Csub : Coef -> Coef -> Coef;
    Czero_test : Coef -> bool;
    Cpow : Coef -> N -> Coef;
    Ceqb: Coef -> Coef -> bool;
    Cof_pos : positive -> Coef
  }.


  Variable cops : Coef_ops.
  Let cdeg := Cdeg cops.
  Let c0 := C0 cops.
  Let c1 := C1 cops.
  Let cadd := Cadd cops.
  Let cmul := Cmul cops.
  Let copp := Copp cops.
  Let csub := Csub cops.
  Let czero_test := Czero_test cops.
  Let cpow := Cpow cops.
  Let ceqb := Ceqb cops.



  (* Notations for coefs *)
  Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
  Notation "x ** y":= (cmul x y) (at level 40, left associativity).
  Notation "-- x" := (copp x) (at level 35, right associativity).
  Notation "x -- y" := (csub x y) (at level 50, left associativity).



  (* Compatibility between equalities, zerotest *)

(*
  Record Coef_eq_compat : Type := mk_ceq_comp{
    Ceq: Coef -> Coef -> Prop;
    Ceq_prop: forall x y : Coef, Bool.Is_true (ceqb x y) -> (Ceq x y);
    C0test_c0 :czero_test c0 =true;
    C0test_c: forall c , czero_test c = true-> (Ceq c c0);
    C0_diff_c1: ~(Ceq c0 c1);
    Cpow_plus: forall x i j, (Ceq (cpow x (i+j)) (cmul (cpow x i)(cpow
      x j)))
    }.

*)


  Record Coef_eq_compat : Type := mk_ceq_comp{
    Ceq: Coef -> Coef -> Prop;
    Ceq_prop: forall x y : Coef, Bool.Is_true (ceqb x y) -> (Ceq x y);
    Ceq_propF: forall x y : Coef, (ceqb x y) =false -> ~(Ceq x y);
    C0test_Ceqb : forall x:Coef, czero_test x = ceqb x c0;
    C0test_c0 :czero_test c0 =true;
    C0test_c1:czero_test c1 =false;
    Cpow_plus: forall x i j, (Ceq (cpow x (i+j)) (cmul (cpow x i)(cpow
      x j)));
    Cpow_1 : forall x, Ceq (cpow x 1) x;
    Cpow_0 : forall x, Ceq (cpow x 0) c1
    }.


  Variable ceq_compat : Coef_eq_compat.

  Let ceq := Ceq ceq_compat.

  Notation "x == y":=(ceq x y)(at level 70, no associativity).


  (* eq is a setoid eq and ext for ring operations*)

  Record Coef_setoid : Prop := mk_cset{
    Ceq_refl : forall x, x==x;
    Ceq_sym : forall x y, x == y -> y == x;
    Ceq_trans : forall x y z, x == y -> y == z -> x == z
  }.
  
  Record Coef_morph : Prop := mk_cmorph{
    Cadd_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2;
    Cmul_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2;
    Copp_ext : forall x1 x2, x1 == x2 -> -- x1 == -- x2;
    C0_test_ext : forall x1 x2, x1 == x2 -> czero_test x1 = czero_test x2 
  }.


  (* ring ops on coefs satisty ring axioms *)
  Record Coef_ring : Prop := mk_cring{
   Cadd_0_l    : forall x, c0 ++ x == x;
   Cadd_sym    : forall x y, x ++ y == y ++ x;
   Cadd_assoc  : forall x y z, x ++ (y ++ z) == (x ++ y) ++ z;
   Cmul_1_l    : forall x, c1** x == x;
   Cmul_sym    : forall x y, x ** y == y ** x;
   Cmul_assoc  : forall x y z, x ** (y ** z) == (x ** y) ** z;
   Cdistr_l    : forall x y z, (x ++ y) ** z == (x ** z) ++ (y ** z);
   Csub_def    : forall x y, x -- y == x ++ --y;
   Copp_def    : forall x, x ++ (-- x) == c0
     }.

End COEF_STRUCT.


