(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.


Require Import Qabs.
Require Import Utils.

Require Import CAD_types.

Require Import One_dim.
Require Import Up_dim.

Require Import Formulas.
Set Implicit Arguments.


Module CAD_gen(Q:RAT_STRUCT).

Import Q.

Module ONE_DIM := MK_ONE_DIM Q.
Import ONE_DIM.

Module UP_DIM := MK_UP_DIM Q.
Import UP_DIM.

Fixpoint Poln(n:nat):Set:=
  match n with
    |O => Rat
    |S n => Pol1 (Poln n)
  end.

(*
Definition Infon(n:nat):=
  match n with
    |O => Rat
    |S O => Rat
    |S n => Info (Poln n)
  end.
*)
Definition Infon(n:nat):=
  match n with
    |O => Rat
    |S n => build_Info (Poln n)
end.


Fixpoint cell_pointn(n:nat):Set:=
  match n with
    |O=>unit
    |S n => @next_path Rat (Poln n) (Infon n) (cell_pointn n)
  end.


Fixpoint mkCadn(n:nat):Set -> Set:=
  match n with
    |O => fun A :Set => A
    |S n => @next_mkCad Rat (Poln n) (Infon n) (mkCadn n)
  end.



Fixpoint mkCad_mapn(n:nat)(C D:Set){struct n}:
  ((cell_pointn n)-> C -> ((cell_pointn n) * D))->
  mkCadn n C -> mkCadn n D:=
     match n return 
       ((cell_pointn n)-> C -> ((cell_pointn n) * D))->
       mkCadn n C -> mkCadn n D with
       |O =>
	 let res(f : unit -> C -> unit * D)(x:C):D:=snd (f tt x) in
	   fun f : unit -> C -> unit * D => (fun x:C => res f x)
       |S n => 
	 fun (f : (cell_pointn (S n))-> C -> ((cell_pointn (S n)) * D)) =>
	 @next_mkCad_map Rat (Poln n) (Infon n) (cell_pointn n)
	 (mkCadn n) (mkCad_mapn n) C D f 
     end.

(*
Fixpoint mkCad_mapn(n:nat)(C D:Set)
  (f:(cell_pointn n)-> C -> ((cell_pointn n) * D)){struct n}:
  mkCadn n C -> mkCadn n D:=
     match n return mkCadn n C -> mkCadn n D with
       |O =>  fun x:C => snd (f tt x)
       |S n => 
	 @next_mkCad_map Rat (Poln n) (Infon n) (cell_pointn n)
	 (mkCadn n) (mkCad_mapn n)
     end.
*)
(*@mkCad_mapn n (list C) (list D) (@map C D f)
    end.
*)

Fixpoint CAD_build(n:nat):
  Cad Rat (Poln n) (Infon n) (cell_pointn n) (mkCadn n):=
  match n return 
    Cad Rat (Poln n) (Infon n) (cell_pointn n) (mkCadn n) with
    |O => One_dim_cad
    |S n => @CAD_make (Poln n) (Infon n) (cell_pointn n) (mkCadn n) (mkCad_mapn n)  (CAD_build n)
  end.


Section PolEqB.
Variable n : nat.
Variable aux : Poln n -> Poln n -> bool.

Fixpoint next_eq (P Q : Poln (S n)){struct P}:bool:=
  match P, Q with
    |Pc p, Pc q => aux p q
    |PX _ _ _, Pc _ => false
    |Pc _, PX _ _ _ => false
    |PX P1 i p, PX Q1 j q => andb (next_eq P1 Q1) (aux p q)
  end.

End PolEqB.

Fixpoint Pol_eqb(n:nat):Poln n -> Poln n -> bool :=
  match n return Poln n -> Poln n -> bool with
    |O => fun a:Poln O => fun b:Poln O =>  rzero_test (rsub a b)
    |S n => next_eq (Pol_eqb n)
  end.

Definition Form_n(n:nat) := Form (Poln n).
Definition DNF_n(n:nat) := DNF (Poln n).

(*
Definition decide_dnf(n:nat)(f:DNF_n (S n))(l:list (Poln (S n))):=
  let cad := Pol_cad (CAD_build n) l in true in
    mkCad_foldn 
à finir *)







End CAD_gen.


(*
    |S O => @CAD_make (Poln (S O)) Rat unit (mkCadn (S O)) toto One_dim_cad
    |S (S n) => @CAD_make (Poln (S n)) (cell_pointn (S n)) (mkCadn (S n)) 
      (mkCad_mapn (S n)) (CAD_build (S n))
  end.
*)


(*
Fixpoint CAD_build(n:nat):
  Cad Rat (Poln n) (Infon n) (cell_pointn n) (mkCadn n):=
  match n return 
    Cad Rat (Poln n) (Infon n) (cell_pointn n) (mkCadn n) with
    |O => One_dim_cad
    |S n => @CAD_make (Poln n) (cell_pointn n) (mkCadn n) (mkCad_mapn n) 
      (CAD_build n)
  end.
*)
