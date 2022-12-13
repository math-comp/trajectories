


(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.



Require Export NArith.
Require Export Mylist.
Require Import Utils.

Set Implicit Arguments.



  (************************************************************)
  (*****         Type definitions for the CAD              ****)
  (************************************************************)


Section TYPES.


  (** Type of result of sign computations *)
  Definition Sign := option comparison.
  
  (**** Polynomials in Horner form, one var with coefs in C ****)

  
  (*The set of base coefficients *)
  Variable Rat :Set.
  Variable rmin : Rat -> Rat -> Rat.
  Variable req : Rat -> Rat -> bool.


  (*The set of coefficients*)
  Variable Coef:Set.


  (* Polys in one var over C*)
  Inductive Pol1(C:Set):Set:=
    |Pc : C -> Pol1 C
    |PX : Pol1 C -> positive -> C -> Pol1 C.


  Let Pol := Pol1 Coef.

  (* Here we can also define all the operators on Pols wich are not recursive
    in the number of variables *)

  (* Couple (degree * coefdom) for a polynomial *)
  Definition Pol_deg_coefdom := 
    let aux := 
      fix aux (deg:N) (P:Pol){struct P} : N * Coef :=
	match P with
	  | Pc a => (deg,a)
	  | PX P i p => aux (deg + Npos i)%N P
	end 
	in aux N0.

(* Degree only *)
  Definition Pol_deg P := fst (Pol_deg_coefdom P).

(* Leading coef only *)
  Fixpoint Pol_dom(P:Pol) : Coef :=
   match P with
   | Pc p => p
   | PX P _ _ => Pol_dom P
   end.

(* Hack for division *)
  Definition Pol_coefdom_if_PC (c:Coef) (P:Pol) : Coef :=
   match P with
   | Pc p => p
   | PX P _ _ => c
   end.



  (************************************************************)
  (* Informations about a Pol to be computed once and for all *)
  (************************************************************)

  (* Info is (P, Pbar, dPbar, lowsign, signinfo) where :
     - P is a polynomial
     - Pbar is the square free part of P,
     - dPbar is the degree of Pbar (for later bern computations)
     - lowsign the sign of P in -inf
     - signinfo is the sign of P if it is known to be constant,
       and None else *)

  Definition build_Info := uple5 Pol Pol N Sign Sign.

  Definition mk_build_Info P Q n low sign_info : build_Info := 
    Five P Q n low sign_info. 

  Definition Pol_of_build_Info (c:build_Info) := fst5 c.



  (************************************************************)
  (* ** Representation of algebraic points in n dimensions ** *)
  (************************************************************)


 (* This will be the information encoding bernstein coefs which are
  retained, in fact build_Info at the level below *)
  Variable berncoef : Set.


  (** encoding of algebraic numbers at this level, 
      x := (a, b, P, Pbar, lb) : mkAlg 
    - a < x < b  
    - P is a polynomial such [P x = 0]
    - Pbar is the square free part of P.
    - lb is the list bernstein coefs of P over ]a b[.
    For each bern coef, we keep the polinfo because we will later
    have to compute signs of these coefs, so berncoef will be recursively
    instanciate with build_Info. *)

  Definition mkAlg := uple5 Rat Rat Pol Pol (list berncoef).



  (** Elements of R :
  either -infty : a least bound for the roots considered,
  or a rational point between two consecutive roots
  or a rational root
  or an algebraic root: mkAlg *)


  Inductive mkRpoint :Set:=
   | Minf     : Rat -> mkRpoint
   | Between  : Rat -> mkRpoint
   | Root     : Rat -> mkRpoint 
   | Alg_root : mkAlg -> mkRpoint.


(***************************************************************)
(**                 Output of the procedure                   **)
(***************************************************************)



(* We build a labelled tree representing a cylindrical sample of points *)
(* For a CAD of polys with k variables, the tree is of depth k *)

(* - The inner nodes at depth i of the tree are labelled with real *)
(*points of type mkRpoints  of dim i : the dim is relevant in the *)
(* case of alg. points  for th encoding. *)

(* - Leaves of a tree of depth n are labbelled with elements of type *)
(*  (Pol*Sign) *)


(* a n-uple of mkRpoints of successive dimension from the root to a *)
(* leave has type path : if a leave (l,(P,s)) is at the position *)
(*p:path, then s is the sign of p at the point (p,l) *)


(* path encodes elements of R^{n-1}*)
  Variable path : Set.



(* the encoding of real points along the n-th coordinate of R^n *)
  Definition next_label := mkRpoint.

(* The encoding of elements of R^n *)
  Definition next_path := (path * next_label)%type.
  Definition build_next_path(p:path)(r:mkRpoint):=(p,r).


(* A zipper-like structure for update while building a new cad tree *)


(* mkCad builds the type of cylindrical sample (cs) trees of depth n -1, *)
(* given the type C to put in their leaves                          *)
  Variable mkCad:Set -> Set.


(* building cs tree of depth n *) 
  Definition next_mkCad(C:Set):= mkCad (list (next_label * C)).


(* Given a cs tree of depth n-1, which leaves o type n and an update *)
(* function f : path -> C -> path which  compute an updated path an a *)
(* new value of type D, we build a new cs tree of depth n-1 with *)
(* leaves of type D and updated labels in the inner nodes *)

  Variable mkCad_map : forall C D : Set, 
    (path -> C -> (path * D)) -> mkCad C -> mkCad D.

(* Same for the level n *)

  Definition next_mkCad_map(C D:Set)
(f:next_path -> C ->  (next_path *  D))
 (t:next_mkCad C) : next_mkCad D :=
 let aux(p : path)(leave : list (next_label * C)) :
   path*(list (next_label * D)):=
   let f_aux (p:path)(np:next_label*C):path*(next_label*D):=
     let (nlabel,c) := np in
     let (updated_npath,d):=f (p,nlabel) c in
       (fst updated_npath,(snd updated_npath,d)) in
   @two_fold path (next_label*C) (next_label * D) f_aux p leave in
   @mkCad_map (list (next_label * C)) (list (next_label * D)) aux t.




  (* Cad gathers what is needed from level n to build the cad at level n+1 *)
  


  Record Cad : Set := mk_cad {
    Pol_0                : Pol;
    Pol_1                : Pol;
    Pol_add              : Pol -> Pol -> Pol;
    Pol_mul_Rat          : Pol -> Rat -> Pol;
    Pol_mul              : Pol -> Pol -> Pol;
    Pol_sub              : Pol -> Pol -> Pol;
    Pol_opp              : Pol -> Pol;
    Pol_of_Rat           : Rat -> Pol;
    Pol_is_Rat           : Pol -> bool;
    Pol_zero_test        : Pol -> bool;
    Pol_base_cst_sign    : Pol -> option comparison;
    Pol_pow              : Pol -> N -> Pol;
    Pol_div_Rat          : Pol -> Rat -> Pol;
    Pol_div              : Pol -> Pol -> Pol;
    Pol_gcd_gcd_free     : Pol -> Pol -> Pol * Pol * Pol;
    Pol_square_free      : Pol -> Pol;
    path_refine          : next_path -> nat -> option next_path;
(*  cell_point_up_refine : mkcell_point_up -> nat -> option mkcell_point_up;*)
    Pol_low_bound        : Pol -> path -> Rat;
(*  Pol_low_bound        : Pol -> cell_point -> Rat;*)
    Pol_value_bound      : next_path -> Pol -> Rat * Rat;
(*  Pol_value_bound      : mkcell_point_up -> Pol -> Rat * Rat;*)
    Info_of_Pol          : Sign -> Pol -> build_Info;
    Pol_low_sign         :  path -> Pol -> Pol -> nat ->
      (path * (option comparison));
(*  Pol_low_sign         : 
      cell_point -> Pol -> Pol -> nat -> (cell_point * (option comparison));*)
    Pol_sign_at          : build_Info -> next_path -> nat ->
      next_path * (Pol * Sign)%type;
(*  Pol_sign_at          :
      build_Info -> mkcell_point_up -> nat -> 
      mkcell_point_up * (Pol * option comparison);*)
    Pol_cad : list Pol -> nat -> next_mkCad  (list (Pol * Sign))
(*  Pol_cad : list Pol -> nat -> mkCad_up (mkcell_point_up * (list (Pol * Sign)))*)
  }.

End TYPES.
