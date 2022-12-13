
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)



(* WARNING : Not to be compiled!!!

This defines the type of algebraic numbers at the current level (=dimension)
and operations on bounds given 
Coef : Set.
Rat : Set
cInfo :Set.
cell_point : Set.

Pol := Pol1 Coef

Rpoint


*)


  (************************************************************)
  (****             Type definitions                       ****)
  (************************************************************)



 Definition Alg := mkAlg Rat Coef cInfo.
 Definition Rpoint := mkRpoint Rat Coef cInfo.
 Definition cell_point_up := next_path Rat Coef cInfo path.


 (************************************************************)
 (******         Misc. for sign_tables handling        *******)
 (************************************************************)

(* to add the sign of a pol to a list of signs at a tagged root*)
 Definition add_cst_sign
   (l:list (Rpoint*(list (Pol*Sign))))(P:Pol)(sign:Sign):=
   let add_sign := fun w => (fst w, (P,sign)::(snd w)) in
     map add_sign l.

(* to add the sign of a pol at the end of a list of signs *)
 Definition add_to_cst_list
   (l:list (Rpoint*(list (Pol*Sign))))(sign :list (Pol*Sign)):=
   let add_list := fun w => (fst w,  (snd w) @ sign) in
     map add_list l.




  (************************************************************)
  (***      Bounds on the value of P at a cell_point_up      **)
  (**************************g**********************************)

  Definition Pol_value_bound (z:cell_point_up)(P:Pol):=
    let (z',r):=z in
      match r with
	|Minf m => cvalue_bound z' (Pol_partial_eval P m)
	|Between b => cvalue_bound z' (Pol_partial_eval P b)
	|Root r => cvalue_bound z' (Pol_partial_eval P r)
	|Alg_root alg =>
	  let (a,b,_,_,_):= alg in
	  let g:= fix Pol_eval_int(P:Pol):(Rat*Rat):=
	    match P with
	      |Pc c => cvalue_bound z' c
	      |PX P i p =>
		let (c,d):= Pol_eval_int P in
		let (e,f):= rpow_int a b (Npos i) in
	        let (g,h):= rprod_int c d e f in
		let (k,l):= cvalue_bound z' p in
		  radd_int g h k l 
	    end in
	    g P
      end.



  (************************************************************)
  (***        Refinement of algebraic numbers encodings     ***)
  (************************************************************)


 Definition alg_refine(z:path)(alg:Alg)(n:nat):=
   let (a, b, P, Pbar, blist):= alg in
   let mid := rdiv (radd a b) (2#1) in
   let Pmid := Pol_partial_eval P mid in
   let Pbarmid := Pol_partial_eval Pbar mid in  
     match 
       (snd (snd 
	 (csign_at (cmk_Info Pmid Pbarmid (cdeg Pbarmid) None None) z n)))
       with
       |None => None
       |Some Eq => Some (z,(Root Coef cInfo mid))
       |Some _ =>
	 let (b',b''):= Pol_bern_split blist a b mid in
	 let Vb' := 
	   op_sign_changes 
	   (map (fun x => snd (snd (csign_at x z n))) b') in
	   match Vb' with
	     |None => None
	     |Some 1 => Some (z, (Alg_root (Five a mid P Pbar b')))
	     |Some _ => Some (z, (Alg_root (Five a mid P Pbar b'')))
	   end
     end.


 (** keeps only the relevant half of each int in every algebraic coordinate **)
 Definition cell_refine(z:cell_point_up)(n:nat) :=
   let (z',r):= z in
     let z':= ccell_refine z' n in
       match z' with
	 |None => None
	 |Some z' =>
	   match r with
	     |Minf m => Some (z', Minf Coef cInfo m)
	     |Between b => Some (z', Between Coef cInfo b)
	     |Root r => Some (z', Root Coef cInfo r)
	     |Alg_root alg => alg_refine z' alg n
	   end
   end.


	
