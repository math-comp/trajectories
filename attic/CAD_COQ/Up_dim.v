(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.



 (*Require Import Qabs_rec.
  Require Import CAD_rec.*)
(*Require Import CAD.*)
Require Import Qabs.
Require Import Utils.
Require Import CAD_types.


Set  Implicit Arguments.

Module MK_UP_DIM(Q:RAT_STRUCT).


  Module QFUNS:= RAT_FUNS Q.
  Module QINT := RAT_INT_OPS Q.
  Import Q.
  Import QFUNS.
  Import QINT.



  Section UP_DIM.

  
    (* coefficients *)
    Variable C:Set.
    Let Coef := Pol1 C.
    Let cdeg := @Pol_deg C.
    

    (*information retained for bern coefs *)
    Let cInfo := build_Info C.

    Let cmk_Info := @mk_build_Info C.

    Variable bern:Set.
  
    (* type of cell_points at the level n *)
    Variable cell_point_low : Set.

    Let path := next_path Rat C bern cell_point_low.
    Let crpoint_of_cell(z:path):= snd z.
    Let ccell_point_proj(z:path):=fst z.


    Variable cmkCad : Set -> Set.
    Variable cmkCad_map : forall C D:Set, 
      (cell_point_low -> C -> (cell_point_low * D)) -> cmkCad C -> cmkCad D. 

    Variable CAD_n : Cad Rat C bern cell_point_low cmkCad.

    Let c0 := Pol_0 CAD_n.
    Let c1 := Pol_1 CAD_n.
    Let cadd := Pol_add CAD_n.
    Let cmult_base_cst := Pol_mul_Rat CAD_n.
    Let cmul := Pol_mul CAD_n.
    Let csub := Pol_sub CAD_n.
    Let copp := Pol_opp CAD_n.
    Let cof_Rat := Pol_of_Rat CAD_n.
    Let cis_Rat := Pol_is_Rat CAD_n.
    Let cof_pos(p:positive) := cof_Rat (rof_pos p).
    Let czero_test := Pol_zero_test CAD_n.
    Let cbase_cst_sign := Pol_base_cst_sign CAD_n.
    Let cpow := Pol_pow CAD_n.
    Let cdiv_base_cst :=  Pol_div_Rat CAD_n.
    Let cdiv := Pol_div CAD_n.
    Let cgcd_gcd_free := Pol_gcd_gcd_free CAD_n.
    Let csquare_free := Pol_square_free CAD_n.
    Let ccell_refine := path_refine CAD_n.
    Let clow_bound := Pol_low_bound CAD_n.
    Let cvalue_bound := Pol_value_bound CAD_n.
    Let cInfo_of_Pol := Info_of_Pol CAD_n.
    Let clow_sign := Pol_low_sign CAD_n.
    Let csign_at := Pol_sign_at CAD_n.
    Let ccad := Pol_cad CAD_n.
    
    Let cPol_of_Info(info:cInfo) := fst5 info.

(*    Load Gen_functor.*)

Load Pol_on_Coef.
Load Pol_on_Coef_on_Rat.
Load Bern.
Load Alg.

  (*Are now available:
     Pol_add :Pol -> Pol->Pol
     Pol_mul :Pol->Pol->Pol
     Pol_sub :Pol->Pol->Pol
     Pol_opp :Pol->Pol
     Pol_div:Pol->Pol->Pol
     Pol_zero_test : Pol->bool
     mk_PX := Pol ->positive -> Coef -> Pol
     Pol_of_pos := positive -> Pol
     Pol_pow := Pol -> N -> Pol
     Pol_subres_list := Pol -> Pol-> list Pol
     Pol_subres_coef_list := Pol -> Pol -> list Coef
     Pol_gcd := Pol -> Pol -> Pol
     Pol_square_free := Pol -> Pol
     Pol_deriv := Pol -> Pol
     Pol_eval := Pol -> Coef -> Coef.
     Pol_trunc : Pol  -> list Pol 
     Pol_mk_coef : 
     Pol_mkPc := 
     Pol_is_base_cst 
     Pol_mult_base_cst
     Pol_div_base_cst 
     Pol_partial_eval 
     Pol_trunc
     Pol_bern_coefs
     Pol_bern_split+....*)



 
    


    (*

    Let Cad_up := mkCad_up Rat Coef cInfo mkCad.

    

    Let map_Cad_n := @map_Cad_up Rat rmin req Coef cInfo cell_point
      mkCad min_cell_point_list map_Cad (Minf Coef cInfo r0).

*)









    Let mk_cell_point(z:cell_point_low)(r:mkRpoint Rat C bern):=(z,r). 

  (* Equality test over coefs in normal forms *)
    Let ceq(P Q:Coef):= czero_test (P -- Q).

    Let Pol_base_cst_sign(P:Pol):Sign:=
      match P with
	|Pc c => cbase_cst_sign c
	|PX _ _ _ => None
      end.



    (****************************************************************)
    (**Bounds for the roots of a Pol above a cell and sign at infty**)
    (****************************************************************)


    (* P=p0+...+pnX^n, c(P)=(n+1)*(sum p_i^2)/(p_n^2) (1) majorizes the abs values
    of the roots of P *)


    (* Sum of the squares of the coefficents *)
    Let  sum_square_coef:=
      fix sum_square_val_coef (P:Pol):Coef:=
	match P with
	  |Pc p => p **  p
	  |PX P' i p => (p ** p) ++ sum_square_val_coef P' 
	end.
    
   (* Bounds on the values of the numerator in (1) above z *)
    Let Pol_num_bound(P:Pol)(z:path):=
      let n:= sum_square_coef P in
	cvalue_bound z n.

    (* c(P) above z*)
    Let Pol_bound(P:Pol)(z:path):=
      let (dP, den) := Pol_deg_coefdom P in
	let (a,b):= (Pol_num_bound P z)  in
	  let (c,d) := (cvalue_bound z (den ** den)) in
	    let (res,_) :=  rdiv_int a b c d in
	      rprod (radd (rof_N dP)  r1) res.

    (* Upper bound for the roots of P above z *)
    Let  Pol_up_bound(P:Pol)(z:path):= 
      radd (Pol_bound P z) r1.

    Let Pol_info_up_bound(z:path)(i:Info):=
      let (P,_,_,_,sinfo):=i in
	match sinfo with
	  |Some _ => r0
	  |None => Pol_up_bound P z 
	end.



    (* Lower bound for the roots of P above z *)
    Let  Pol_low_bound(P:Pol)(z:path):=
      ropp (radd (Pol_bound P z) r1).

    Let Pol_info_low_bound(z:path)(i:Info):=
      let (P,_,_,_,sinfo):=i in
	match sinfo with
	  |Some _ => r0
	  |None => Pol_low_bound P z 
	end.


  (* Sign of P in -infty above z, also computes a refinement of z *)
    Let Pol_low_sign(z:path)(P Pbar:Pol)(n:nat):=
      let z' := ccell_point_proj z in
      let r := crpoint_of_cell z in
      let m:= Pol_low_bound P z in
      let P_atm := (Pol_partial_eval P m) in
      let Pbar_atm := Pol_partial_eval Pbar m in
      let dPbar_atm := cdeg Pbar_atm in
      let (z',s) := clow_sign z' P_atm Pbar_atm n in 
      let (z, res) :=  
	csign_at 
	(cmk_Info P_atm Pbar_atm  dPbar_atm s None) (mk_cell_point z' r) n in
	(z, (P, (snd res))).
    
    Let Pol_low_sign_for_upper(z:path)(P Pbar:Pol)(n:nat):=
      let (z, slow):=(Pol_low_sign z P Pbar n) in
	(z, snd slow).



  (************************************************************)
  (**          Roots isolation above a cell_point            **)
  (************************************************************)


  (** Sign determination at a rational point above the cell_point z **)

    Let Pol_eval_sign_at_isol(P Pbar:Pol)(z:path)(c:Rat)(n:nat):=
      let Pbar_at_c := Pol_partial_eval Pbar c in
      let P_at_c := Pol_partial_eval P c in
      let dPbar_at_c := cdeg Pbar_at_c in
      let (_,s):= clow_sign (ccell_point_proj z) P_at_c Pbar_at_c n in
	csign_at (cmk_Info P_at_c Pbar_at_c dPbar_at_c s  None) z n.


  (** z is a cell_point, a a rational, computes the pair (P, sign P(z,a))
   from an Info **)
    Let Pol_info_eval_sign(n:nat)(a:Rat)(z:path)(u:Info):=
      let (P,freeP, dfreeP, lowsing, infosign):=u in
	match infosign with
	  |Some s => (P,infosign)
	  |None => (P,snd (snd (Pol_eval_sign_at_isol P freeP z a n)))
      end.



  (** While mapping sign determination over a list l of coef,
    refines successively the cell_point z **)

    Let csign_at_refine(z:path)(l:list cInfo)(n:nat):
      path*list (Coef*Sign):= 
      let sign_refine := 
	fix sign_refine(l:list cInfo)(res:path*list (Coef *Sign))
	  {struct l}:path*list (Coef*Sign):=
	  match l with
	    |nil => res
	    |hd :: tl =>
	      let (z', s):= csign_at hd z n in
		sign_refine tl (z', (s::(snd res)))
	  end in
	  sign_refine l (z,nil).


  (** Isolation of roots of P over ]c d[ above z **)
    
    Let root_isol1(P:Pol)(Pbar:Pol):=
      fix root_isol1(r:path*(list (Rpoint*(list (Pol*Sign)))))
	(c d:Rat)(blist: list cInfo)(n:nat){struct n}:
	path*(list (Rpoint *(list (Pol*Sign)))):=
	let (z,res):=r in
	  if rlt d c 
	    then (z,nil)
	    else
	      let (z,Vb) := csign_at_refine z blist n in
		let test := op_sign_changes (map (fun x => snd x) Vb) in
		  match test  with
		    |None => (z,(Alg_root (Five c d P Pbar blist), (P,None)::nil)::res)
		    |Some O => (z,res)
		|Some 1 =>
		  let (z, sP_c):=Pol_eval_sign_at_isol P Pbar z c n in
		  let (z, sP_d):=Pol_eval_sign_at_isol P Pbar z d n in
		    match  (sign_mult (snd sP_c) (snd sP_d)) with
		      |None => (z,(Alg_root (Five c d  P Pbar  blist), (P,None)::nil)::res)
                      |Some Eq =>
			match n with
			  |O=> (z,(Alg_root (Five c d P Pbar blist), (P,None)::nil)::res)
			  |S n' => 
                            let mid := rdiv (radd d c)  (2 # 1) in
                            let (b', b''):= Pol_bern_split blist c d mid in
			    let (z,res'):= root_isol1 (z,res) c  mid  b' n' in
			    let (z,sP_mid) := Pol_eval_sign_at_isol Pbar Pbar z mid n in
			      match  snd sP_mid  with
				|None =>  
				  (z, 
				    (Alg_root (Five c d P Pbar blist), (P,snd sP_mid)::nil)
				    :: res')
				|Some Eq => 
				  root_isol1 (z,((Root Coef cInfo mid,(P, snd sP_mid)::nil)::res'))
				  mid d b'' n'
				|_ => root_isol1 (z,res')  mid d b'' n'
	
		      end
			end
                      |_ =>
			(z,(Alg_root (Five c d P Pbar blist), (P,(Some Eq))::nil)::res)
		    end
		    |_ =>
		      match n with
			|O => (z,(Alg_root (Five c d P Pbar blist), (P,None)::nil)::res)
			|S n' => 
			  let mid := rdiv (radd d c)  (2 # 1) in
			  let (b', b''):= Pol_bern_split blist c d mid  in
			  let (z,res'):= root_isol1 (z,res) c  mid  b' n' in
			  let (z, sP_mid) :=Pol_eval_sign_at_isol Pbar Pbar z mid n in
			    match  snd sP_mid with
			      |None => 
				(z,(Alg_root (Five c d P Pbar blist),(P, snd sP_mid)::nil)
				  ::res)
			      |Some Eq =>
				root_isol1 
				(z,((Root Coef cInfo mid, (P,snd sP_mid)::nil)::res')) mid d b'' n'
			      |_ =>
				root_isol1 (z,res')  mid d b'' n'
			    end
		      end
		  end.
    
    (** isolation of the roots of P over the real line above z **)
    
    Let root_isol
      (P:Pol)(z:path)(Pbar:Pol)(degPbar:N)(lbound ubound:Rat)(n:nat):= 
      let (z, sign):=(Pol_low_sign z P Pbar n) in
	root_isol1 P Pbar
	(z,((Minf Coef cInfo lbound, (P,snd sign)::nil)::nil))
	lbound ubound (Pol_bern_coefs Pbar lbound ubound degPbar) n.
    
    
    (** isolation of the roots of P over ]c d[ above z
      WARNING, do not add Minf, and so returns the  empty list if P has a cst sign over ]cd[**)
    
    Let root_isol_int(P:Pol)(z:path)(Pbar:Pol)(degPbar:N)
      (c d:Rat)(n:nat) := 
      root_isol1  P Pbar
      (z,nil) c d (Pol_bern_coefs Pbar c d degPbar) n.



    (** Sign of Q at a root of P above z which is not a root of Q 
	 None means n was not large enough 
        Returns a cell_point to remember the possible refinements of z which 
	may be computed **)

    Let sign_at_non_com(z:path)(Q Qbar:Pol):=
      fix sign_at_non_com(a b:Rat)(P Pbar:Pol)
	(bern bernQ:list cInfo) (n:nat){struct n}: (cell_point_up*(Pol* Sign)):=
	let (z,Vb) := csign_at_refine z bernQ n in
	let test := op_sign_changes (map (fun x => snd x) Vb) in
	  match test with
	    |None => ((z, Alg_root (Five a b P Pbar bern)),(Q, None))
       	    |Some O => 
	      let (z, sQ_a):=Pol_eval_sign_at_isol Q Qbar z a n in
		((z,Alg_root (Five a b P Pbar bern)), (Q,snd sQ_a))
	    | _ => 
	      let mid := rdiv (radd a b)  (2 # 1) in
	      let (z, sPbar_mid) := Pol_eval_sign_at_isol Pbar Pbar z mid n in
		match snd sPbar_mid with
		  |None =>((z,Alg_root (Five a b P Pbar bern)), (Q, None))
		  |Some Eq => 
		    let (z, sQ_mid):= Pol_eval_sign_at_isol Q Qbar z mid n in
		      ((z, Alg_root (Five a b P Pbar bern)),(Q,snd sQ_mid))
		  |_ =>
		    match n with
		      |O => ((z,Alg_root (Five a b P Pbar bern)), (Q, None))
		      |S m =>
			let (z,sP_bar_mid):=Pol_eval_sign_at_isol P Pbar z mid n in
			let (z,sPbar_a):=Pol_eval_sign_at_isol P Pbar z a n in
			match (sign_mult (snd sPbar_mid) (snd sPbar_a)) with
			  |None => ((z,Alg_root (Five a b P Pbar bern)), (Q, None))
			  | Some Lt  =>
			    let (bern',_) := Pol_bern_split bern a b mid  in
			    let (bernQ',_) := Pol_bern_split bernQ a b mid  in
			      sign_at_non_com a mid P Pbar bern' bernQ' m
			  |_ =>
			    let (_,bern'') := Pol_bern_split bern a b mid  in
			    let (_,bernQ'') := Pol_bern_split bernQ a b mid  in
			      sign_at_non_com mid b P Pbar bern'' bernQ'' m
			end
		    end
		end
	  end. 



      (** refines [ab] which contains a unique root of P and G=gcd P Q
	to a intervalle which isolates for Q **)

    Let sign_at_com:= 
      fix sign_at_com (z:path)(a b:Rat)(P Pbar G Gbar:Pol)
	(bernG bernQ:list cInfo)(n:nat){struct n}:
	cell_point_up*Sign:=
	let (z,Vb) := csign_at_refine z bernQ n in
	let test := op_sign_changes  (map (fun x => snd x) Vb) in
	  match test with
	    |None => ((z,Alg_root (Five a b G Gbar bernG)), None)
	    |Some O => ((z,Alg_root (Five a b G Gbar bernG)), None) (*never!*)
	    |Some 1 => ((z,Alg_root (Five a b G Gbar bernG)), (Some Eq))
	    | _ =>
	      let mid := rdiv (radd a b)  (2 # 1) in
	      let (z, sPbar_mid) := Pol_eval_sign_at_isol Pbar Pbar z mid n in
		match (snd sPbar_mid) with
                  |None => ((z, Alg_root (Five a b G Gbar bernG)), None)
		  |Some Eq => ((z,Root Coef cInfo mid), (Some Eq))
		  | _ => 
		    match n with
			  |O => ((z,Alg_root (Five a b G Gbar bernG)), None)
		      |S n' =>
			let (z, sPbar_a):= Pol_eval_sign_at_isol Pbar Pbar z a n in
			match (sign_mult (snd sPbar_mid) (snd sPbar_a)) with
                          |None =>  ((z, Alg_root (Five a b G Gbar bernG)), None)
			  |Some Lt =>
			    let (bernG',_):=Pol_bern_split bernG a b mid  in
			    let (bernQ',_):= Pol_bern_split bernQ a b mid in
			      sign_at_com z a mid P Pbar G Gbar bernG' bernQ' n'
			  |_ =>
			    let (_,bernG''):=Pol_bern_split bernG a b mid in
			    let (_,bernQ''):=Pol_bern_split bernQ a b mid  in
			      sign_at_com z mid b P Pbar G Gbar bernG'' bernQ'' n'
			end
		    end
		end
	  end.
    

   (** refines an AlgRoot a b P Pbar ... of P to determine the sign of Q
       ie up to the point where G=gcd P Q has either a unique root or no root **)

    Let pair_refine (z:path)(Q Qbar:Pol)(dQbar:N):=
      fix pair_refine(a b:Rat)(P Pbar G:Pol)
	(bern bernG:list cInfo)(n:nat){struct n}:
	cell_point_up*(Pol*Sign):=
	let (z,Vb) := csign_at_refine z bernG n in
	let test := op_sign_changes (map (fun x => snd x) Vb) in
	  match test with
            |None => ((z,Alg_root (Five a b P Pbar bern)),(Q, None))
	    |Some O => 
	      let bernQ := Pol_bern_coefs Qbar a b dQbar in
		sign_at_non_com z Q Qbar a b P Pbar bern bernQ n
	    |Some 1 =>
	      let bernQ := Pol_bern_coefs Qbar a b dQbar in
	      let Gbar := Pol_square_free G in
	      let res :=  sign_at_com z a b P Pbar G Gbar bernG bernQ n in
		(fst res, (Q, snd res))
	    |_ =>
	      let mid := rdiv (radd a b) (2 # 1) in
	      let (z, sPbar_mid) := Pol_eval_sign_at_isol Pbar Pbar z mid n in
		match (snd sPbar_mid) with
		  |None => ((z,Alg_root (Five a b P Pbar bern)), (Q, None))
		  |Some Eq =>
		    let (z,sQbar_mid):=Pol_eval_sign_at_isol Q Qbar z mid n in
		      ((z,Root Coef cInfo mid), (Q, snd sQbar_mid))
		  |_ =>
		    match n with
		      |O => ((z,Alg_root (Five a b P Pbar bern)),(Q, None))
		      |S m =>
			let (z,sPbar_a) := Pol_eval_sign_at_isol Pbar Pbar z a n in
			match (sign_mult (snd sPbar_a) (snd sPbar_mid)) with
			  |None =>  ((z, Alg_root (Five a b P Pbar bern)),(Q, None))
			  |Some Lt =>
              		    let (bern',_):=Pol_bern_split bern a b mid in
              		    let (bernG',_):=Pol_bern_split bernG a b mid in
              			pair_refine a mid P Pbar G bern' bernG' m
             		  |_ =>
			    let (_,bern''):=Pol_bern_split bern a b mid in
			    let (_,bernG''):=Pol_bern_split bernG a b mid in
			      pair_refine
			      mid b P Pbar G bern'' bernG'' m
			end
		    end
		end
	  end.
    

    (** Sign of Q at a cell_point_up, previous failures are propagated **)
    Let sign_at_root(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:cell_point_up)(n:nat):
      cell_point_up*Sign:=
      let (z,r):=t in
      match r with
	|Minf  _ => (t, low)
	|Root r =>
	  let (res_z, res_sign) := Pol_eval_sign_at_isol Q Qbar z r n in
	  ((res_z, Root Coef cInfo r), snd res_sign)
	|Between b => 
	  let (res_z, res_sign) := Pol_eval_sign_at_isol Q Qbar z b n in
	  ((res_z,Between Coef cInfo b), snd res_sign)
	|Alg_root (Five a b P Pbar bern) =>
	  let Pbar := Pol_square_free P in
	  let G := Pol_gcd Q P in
	  let dG := Pol_deg G in
	  let bernG :=Pol_bern_coefs G a b dG in
	  let (res_z,res_s) :=  (pair_refine z Q Qbar dQbar a b P Pbar G bern bernG  n) in
	    (res_z, (snd res_s))
	    
      end.
    


   (* t is the current column : a root and the signs already computed,
    sign_list_at_root adds the sign of Q on top of these signs, and has
    possibly refined the root encoding for this purpose **)

    Let  sign_list_at_root(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:cell_point_up*(list (Pol*Sign)))(n:nat):
      cell_point_up*(list (Pol * Sign)) :=
      let (root, sign_list) :=  t in
	match sign_list with
	  |nil => 
	    let (root_res, sign_res):= sign_at_root Q Qbar dQbar low root n in
	      (root_res, (Q,sign_res)::nil)
	      |(_,None) :: _ => (root, (Q,None) :: sign_list)
	  |_ :: _ =>
	    let (root_res, sign_res):= sign_at_root Q Qbar dQbar  low root n in
	      (root_res, (Q,sign_res)::sign_list)
	end.

    

    (** finds the sign colon at b, b is between two roots and the sign column
    correspond to the root just smaller than b is lsign.
     evaluates only if necessary  **)  

    (* c'est tres maladroit de recalculer Pbar mais comment faire?*)
    Let fill_sign_between(n:nat)(b:Rat) :=
      fix fill_sign_between(z:path)(lsign:list (Pol*Sign))
	{struct lsign}:list(Pol* Sign) :=
	match lsign with
	  |nil => nil
	  |shd::stl =>
	    match shd with
	      | (_ , None) => shd ::(fill_sign_between z stl)
	      | (P,Some s) =>
		match s with
		  |Eq =>
		    let (z, sP_b) := Pol_eval_sign_at_isol P (Pol_square_free P) z b n in
		    (P,(snd sP_b))::(fill_sign_between z stl)
		  |_ => shd :: (fill_sign_between z stl)
		end
	    end
	end.



     (** Sign table for the family P::lP,  over ]low,up[
       P(low) has sign lowsign, P(up) has sign upsign 
       l contains the relevant sign table for lP .
      also computes a refinement of z **)

    Let add_roots(P:Pol)(freeP:Pol)(dfreeP:N)
      (lP:list Info)(n:nat) :=
      fix add_roots(z:path)(l:list (Rpoint*(list (Pol*Sign))))
	(low up:Rat)(lowsign upsign:Sign){struct l}:
	path * (list (Rpoint*(list (Pol*Sign)))) :=
	match l with	  |nil => (z,l)
	  |hd :: tl =>
	    let (rpt, prev_slist):=hd in
	      match rpt with
		|Between _ =>
		  let (z,resP) := root_isol_int P z freeP dfreeP  low up n in
		  let (z,slow):= Pol_low_sign z P freeP n in
		    (z,(add_to_cst_list resP prev_slist)@
		      ((Between Coef cInfo low, (P,snd slow)::prev_slist)::nil))
		|Minf _ =>
		  let (z,resP) := root_isol_int P z freeP dfreeP  low up n in
		  let (z,slow):= Pol_low_sign z P freeP n in
		    (z,(add_to_cst_list resP prev_slist)@
		      ((Minf Coef cInfo low, (P,snd slow)::prev_slist)::nil))
		|Root r =>
		  if orb (rlt up r) (rzero_test (rsub r up))
		    then
		      let (z, sign_table_low_r):=add_roots z tl low r lowsign upsign in
		      (z,(rpt,  (P,upsign)::prev_slist)::sign_table_low_r) 
		    else
		      let (z, sP_r) := Pol_eval_sign_at_isol P freeP z r n in			
		      let (z,resP) := root_isol_int P z freeP dfreeP r up n in
		       let prev_next_sign := fill_sign_between n (rdiv (radd r up) (2 # 1))
			 z prev_slist  in
		       let res_r_up := (add_to_cst_list resP prev_next_sign) in
		       let (z,table_low_r):= (add_roots z tl low r  lowsign (snd sP_r)) in
			 (z,res_r_up @
			 ((Root Coef cInfo r, (P,snd sP_r):: prev_slist)::table_low_r))
		|Alg_root (Five a b Q Qbar bern) =>
		  let (zup,refine) := sign_list_at_root P freeP dfreeP lowsign ((z,rpt),prev_slist) n in
		  let (z,rpt):=zup in
		    match rpt  with
		      |Between _ => (z,l) (*should never happen *)
		      |Minf _  => (z,(Minf Coef cInfo low, (P,None) :: prev_slist):: tl) (*should never happen*)
		      |Root r =>
			if orb (rlt up r) (rzero_test (rsub r up))
			  then
			    let (z,sign_tabl_low_r) := add_roots z tl low r lowsign upsign in
			    (z,(rpt,refine)::sign_tabl_low_r)
			  else
			    let signP_r :=
			      match refine with
				|nil => (P,None)
				|s :: tl => s
			      end in
			      let prev_next_sign :=
				fill_sign_between n (rdiv (radd r up) (2#1)) z prev_slist in
			      let (z,resP) := (root_isol_int P z freeP dfreeP r up n) in
			      let res_r_up := (add_to_cst_list resP prev_next_sign) in
			      let (z,sign_table_low_r):= (add_roots z tl low r  lowsign  (snd signP_r)) in
				(z, res_r_up @((rpt,refine):: sign_table_low_r))
		      |Alg_root (Five a' b' Q' Qbar' bern') =>
			if orb (rlt up a') (rzero_test (rsub a' up))
			  then
			    let (z,sign_table_low_a'):= add_roots z tl  low a' lowsign upsign in
			      (z,(rpt,refine)::sign_table_low_a')
			  else
			    let (z, sPa') := Pol_eval_sign_at_isol P freeP z a' n in
			    let (z, sPb' ):= Pol_eval_sign_at_isol P freeP z b' n in
			    let prev_next_sign :=
			      fill_sign_between n (rdiv (radd b' up) (2#1)) z prev_slist  in
			    let (z,resP) := (root_isol_int P z freeP dfreeP b' up n) in
			    let res_b'_up := (add_to_cst_list resP prev_next_sign) in
			      match  (snd sPb'),(snd sPa') with
				|None, _ => (z,l)
				|_,None => (z,l)
				|Some Eq, Some Eq =>
				  let prev_a'_sign := map (Pol_info_eval_sign n a' z) lP in
				  let (z,sign_table_low_a'):= add_roots z tl low a' lowsign (snd sPa') in
				    (z,res_b'_up @
				    ((Root Coef cInfo b', (P,(Some Eq))::prev_next_sign)::
				      (rpt,refine) ::
				      (Root Coef cInfo a', (P,(Some Eq))::prev_a'_sign):: sign_table_low_a'))
				|Some Eq, Some _  =>
				  let (z,sign_table_low_a'):=add_roots z tl low a' lowsign (snd sPa' ) in
				  (z,res_b'_up @
				  ((Root Coef cInfo b', (P,(Some Eq))::prev_next_sign)::
				    (rpt,refine)::sign_table_low_a'))
				|Some _, Some Eq =>
				  let prev_a'_sign := map (Pol_info_eval_sign n a' z) lP in
				  let (z,sign_table_low_a'):=add_roots z tl low a' lowsign (snd sPa') in
				    (z,res_b'_up@
				    ((rpt,refine) ::
				      (Root Coef cInfo  a', (P,(Some Eq))::prev_a'_sign)::sign_table_low_a'))
				|Some _, Some _ =>
				  let (z,sign_table_low_a'):=add_roots z tl low a' lowsign (snd sPa') in
				  (z, res_b'_up @ ((rpt,refine)::sign_table_low_a'))
			      end
		    end
	      end
	end.	

     (*head is the biggest root, computes the isolating list and a refinemet of z *)
    Let family_root(glow gup:Rat) := 
      fix family_roots(z:path)(Pol_list : list Info)(n:nat)
	{struct Pol_list}:(path * (list (Rpoint*(list (Pol*Sign))))):=
	match Pol_list with
	  |nil => (z,nil)
	  |i :: tl =>
	    let (P,Pbar,dPbar, slow, sinfo):= i in
	      match sinfo with
		|Some s =>
		  match tl with
		    |nil => (z,(Minf Coef cInfo r0, (P, sinfo)::nil)::nil)
		    |_ =>
		      let (z,prev) := family_roots z tl n in
			(z, add_cst_sign prev P sinfo)
		  end
		|None =>
		  match tl with
		    |nil => root_isol P z Pbar dPbar glow gup n
		    |_ =>
		      let (z,sup) := (Pol_eval_sign_at_isol P Pbar z gup n) in
		      let (z,prev) := family_roots z tl n in
			add_roots  P Pbar dPbar tl n z prev glow gup slow (snd sup)
		  end
	      end
	end.
    


   (** sign table above z for the family up to "up",included.
	up is not a root 
	 head corresponds to the smallest root
	 gup and glow are the points considered as +infty and -infty for 
	 the whole family above z.
     Takes the result of family roots and adds one point per non singleton cell**)



    Let sign_table1(z:path)(glow gup:Rat)(n:nat):=
      fix sign_table1(isol_list : list (Rpoint*(list (Pol*Sign))))
	(up:Rat)
	(res:list (Rpoint*(list (Pol*Sign)))){struct isol_list}:
	list (Rpoint*(list (Pol*Sign))):=
	match isol_list with
	  |nil => res
	  |hd::tl =>
	    let (rpt,hdSign):=hd in
	      match rpt with
		|Between _ => res (*should never happen *)
		|Minf _ => 
		  match (tail res) with
		    |nil => res
		    |_ => (Between Coef cInfo glow, hdSign)::res
		  end
		|Root r =>
		    match (tail res) with
		      |nil => 
			let bet := rdiv (radd r up) (2 # 1) in
			 sign_table1 tl r ((rpt, hdSign) ::res)
		      |_ =>
			let bet := rdiv (radd r up) (2 # 1) in
			  sign_table1 tl r 
			  ((rpt, hdSign) ::
			    ((Between Coef cInfo bet,fill_sign_between n bet z hdSign)::res))
		    end
		  |Alg_root (Five a b _ _ _) =>
		    match (tail res) with
		      |nil =>
			let bet := rdiv (radd b up) (2#1) in
			  sign_table1 tl a
			  ((rpt, hdSign) ::res)
		      |_ =>
			let bet := rdiv (radd b up) (2#1) in
			  sign_table1 tl a
			  ((rpt, hdSign)
			    ::((Between Coef cInfo bet,fill_sign_between n bet z hdSign) ::res))
		    end
	      end
	end.



  (** sign_table for the list of Pols on the real line above z *)
  Let sign_table(z:path)(Pol_list:list Info)(n:nat):=
  let up := rmax_list (map (Pol_info_up_bound z) Pol_list) in
  let low := rmin_list (map (Pol_info_low_bound z) Pol_list) in
  let up_signs := map (Pol_info_eval_sign n up z) Pol_list in 
  let (z,roots) := family_root low up z Pol_list n in
    (z,(sign_table1 z low up n roots up ((Between Coef cInfo up, up_signs)::nil))).




  (************************************************************)
  (**             Subresultant Elimination                   **)
  (************************************************************)

  
  (** Each element of llP is the list of truncations of a Pol in the
    initial list.
   For each R in each tr(P), computes the subres coefs sr_j(R, dR/dX)
   where X is the current variable *)

  Let subres_der_flat:=
  fix subres_der_flat(llP:list (list Pol))(res:list Coef)
    {struct llP}: list Coef:=
    match llP with
      |nil => nil
      |lP :: llP' =>
	let subres_der_ac := 
	  fix subres_der_ac(l:list Pol)(res:list Coef){struct l}:
	    list Coef :=
	    match l with
	      | nil => res
	      | P :: l' =>
		subres_der_ac l' ((Pol_subres_coef_list P (Pol_deriv P)) @ res)
	    end in
	    subres_der_ac lP (subres_der_flat llP' res)
    end.



  (** Each element of llP is the list of truncations of a Pol in the
    initial list.
    Computes all the sr_j(R,S) where R
    is in tr(P) and S in tr(Q) *)

  Let subres_flat := 
  fix subres_flat(llP:list (list Pol))(res: list Coef)
    {struct llP}:list Coef :=
    match llP with
      |nil => res
      |lP :: llP' =>
	match llP' with
	  |nil => res
	  |lQ :: _ =>
	    let subres_peer:= 
	      fix subres_peer (u v:list Pol)(res:list Coef)
		{struct u}:
		list Coef:=
		match u with
		  |nil => res
		  |R :: u' =>
		    let dr := Pol_deg R in
		      let subres := (fun x =>
			let dx := Pol_deg x in
			  match (Ncompare dr dx) with
			    |Lt => Pol_subres_coef_list x R
			    |_ => Pol_subres_coef_list R x
			  end) in
		      subres_peer u' v ((flat_map subres v) @ res)
		end in
		subres_flat llP' 
		((flat_map (fun x => subres_peer lP x nil) llP')@res)
	end
    end.




  (** Projection of the family l of polys by subresultant
  elimination.
  Multiple occurences are cleaned **)

  Let elim(l:list Pol) :=
    let l_tr_coef := map Pol_trunc l in
    let l_tr := map (fun u => fst u) l_tr_coef in
    let l_coef := flat_map (fun u => snd u) l_tr_coef in 
    let subres_der := subres_der_flat l_tr l_coef in
      clean_list ceq (subres_flat l_tr subres_der).



  (************************************************************)
  (**        Non-degenerated forms above a path        **)
  (************************************************************)


  (** Leading coef(s) of a Pol can vanish above a given cell_point.

  The non degenerated form of a Pol above a given cell_point is its
   relevant truncation, for which vanishing coefs ahave been removed, and
  the sign of the leding coef has been proved to be <>Eq 

    The computation of the non-deg forms of the Pols in the list may
  demand refinement of the cell_point to get sharp enough bounds 
  on the Pols's values. Hence the following functions also 
  returns the cell_point *)




  (** Sign of a coef:
  either the one of a base cst 
  or a sign to find in the column of signs already computed **)

  Let sign_find(c:Coef):=
    match (cbase_cst_sign c) with
      |Some s => fun x => Some s
      |_ =>
	fix sign_find(sign_list:list (Coef*Sign)):Sign :=
	  match sign_list with
	    |nil => None
	    |s::stl =>
	      if (czero_test  (c -- (fst s))) then (snd s) else sign_find stl
	  end
    end.


  (** If P has a leading coeficient none zero above z, computes the
      normal form of PX P i c.
      Also returns the non-deg leading coef and its sign.
      WARNING : not in "normal form above z" with respect to power index *)

  Let mkPX_above(P:Pol)(infodom:Coef*Sign)(i:positive)(c:Coef)
    (sign_col:list (Coef*Sign)):=
    match P with
      |PX _ _ _ => (PX P i c,infodom)
      |Pc p =>
	let (domP,sign_domP):= infodom in
	  match sign_domP with
	    |None=>(PX P i c,infodom) (*should never happen, else n too small*)
	    |Some Eq =>
              let c_sign :=sign_find c sign_col in
		match c_sign with
                  |Some Eq => (Pc c0,(c0, Some Eq))
                  |_ => (Pc c,(c,c_sign))
		end
	    |Some _ => (PX P i c,infodom)
	  end
    end.



  (** Non degenerated form of P above a cell for which the sign column
  for the elim family is sign_col.
  Also returns the non-deg leading coef and its sign *)

  Let Pol_non_deg (sign_col:list (Coef*Sign)) :=
  fix Pol_non_deg (P:Pol):Pol*(Coef*Sign):=
    match P with
      |Pc c => 
        let c_sign := sign_find  c sign_col in
          match c_sign with
            |None => (Pc c, (c,None))
            |Some Eq => (Pc c0, (c0, Some Eq))
            |Some _ => (Pc c, (c, c_sign))
          end
      |PX P i p =>
        let (P, infodom):=Pol_non_deg P in
          mkPX_above P infodom i p sign_col
    end.



(*BUG????????*)

  (** Info for the non degenerated form of P above cell_point,
   computes couple (refinement for z, Info) *)
  Let Pol_non_deg_info(z:path)
    (sign_col:list (Coef*Sign))(P:Pol)(n:nat):=
    let (P, infodom):=Pol_non_deg sign_col P in
    let (_, domsign) := infodom in
      match P, domsign with
	|_, None => (z, (Five P P N0 None None))
	|Pc _, _ =>
	  let Pbar := Pol_square_free P in
	  let dPbar := Pol_deg P in
	  (z,(Five P Pbar dPbar domsign domsign))
	|_,Some Eq=>
	  (z,(Five P0 P0 N0 (Some Eq) (Some Eq)))
	|_,_ =>
            let Pbar := Pol_square_free P in 
            let dPbar := Pol_deg Pbar in
	    (*let (z, Pbar_sign) := Pol_low_sign z P Pbar n in*) 
	      let u:=Pol_low_sign z P Pbar n in
	      let Pbar_sign := snd u in
	      let z := fst u in
	      (z, (Five P Pbar (Pol_deg Pbar) (snd Pbar_sign) None))
	end.
  
  (** the Coef c is known to be non zero at z,
   refines z to get sharp bound on the values of c:
  ie to isolates the values form 0 *)
  Let cell_refine_for(c:Coef):=
    fix cell_refine_for(z:path)(n:nat){struct n}:option path:=
      let (a,b) := cvalue_bound z c in
	match rsign (rprod a b) with 
	  |Gt => Some z
	  |_ => 
            match n with

              |O => None
              |S n => let z' := ccell_refine z n in
		match z' with
		  |None => None
		  |Some z' => cell_refine_for z' n
		end
            end
	end.

(*
  Let non_deg1:=
    fix non_deg(l:list Pol)(cad_col:cell_point*(list (Coef*Sign)))(n:nat)
      (res:(list Info)*(cell_point*(list(Coef*Sign)))){struct l}:
      (list Info)*(cell_point*(list(Coef*Sign))):=
      match l with
	|nil => res
	|P::Pol_tl=>
          let (z, u) := Pol_non_deg_info cad_col P n in
          let (info_pol, info_dom):=u in 
          let (dom, dom_sign) := info_dom in
          let (z,info_pol) :=
            (match dom_sign with
               |None => (z, info_pol)
               |Some Eq => (z, info_pol)
               |Some _ => 
                 let P:= Pol_of_Info info_pol in 
                 let zres:= cell_refine_for dom z n in
                   match zres with
                     |None => (z, Five P P N0 None None)
                     |Some z =>(z, info_pol)
                   end
             end) in
            let new_cad_col :=(z, sign_col) in
              non_deg Pol_tl new_cad_col n (info_pol::(fst res), new_cad_col)
      end.
*)

  Let non_deg1(cad_col:list (Coef*Sign)):=
    fix non_deg(l:list Pol)(z:path)(n:nat)
      (res:(list Info)){struct l}:path*(list Info):=
      match l with
	|nil => (z,res)
	|P::Pol_tl=>
          let (info_pol,info_dom) := Pol_non_deg cad_col P in
	  let (z,i):=Pol_non_deg_info z cad_col P n in
          let (dom, dom_sign) := info_dom in
	  let (z,i):=
	    (match dom_sign with
	      |None => (z,i)
	      |Some Eq => (z,i)
	      |_ => 
		let P:=Pol_of_Info i in
		let zop := cell_refine_for dom z n in
		  match zop with
		    |None => (z, Five P P N0 None None)
		    |Some z => (z, i)
		  end
	    end) in
	    non_deg Pol_tl z n (i::res)
      end.


  (** Computes the list of Info for the non degenerated forms of the pols of
  the list *)
  Let non_deg(z:path)(cad_col:(list (Coef*Sign)))
    (l:list Pol)(n:nat):=
    non_deg1 cad_col l  z n nil.



  (************************************************************)
  (********       Lifting phase of the real CAD        ********)
  (************************************************************)


  Let one_table_up(l:list Pol)(n:nat)
    (zcol:path*(list (Coef * Sign))):=
    let (z,col):=zcol in
    let (z,l'):=non_deg z col l n in
    sign_table z l' n.

(*

  Let one_table_up_push(l:list Pol)(n:nat)
    (zcol:path*(list (Coef * Sign))):=
    let (z,l):=one_table_up l n zcol in
    let aux := fun rlsign:Rpoint *(list (Pol*Sign)) =>
      let (r,lsign):=rlsign in
	((z, r),lsign) in
	map aux l.
 *)


    Let one_table_up_map(l:list Pol)(n:nat)
    (p:path)(col : list (Coef * Sign)):
    path * (list (Rpoint * (list (Pol * Sign)))) :=
    one_table_up l n (p,col).



  Let Pol_cad(l:list Pol)(n:nat) :=
    let cad := ccad (elim l) n in
      @next_mkCad_map 
      Rat C bern cell_point_low cmkCad cmkCad_map
      (list (Coef*Sign)) (list (Rpoint * (list (Pol * Sign))))
      (one_table_up_map l n) cad .




(*


  Let one_table_up_push(l:list Pol)(n:nat)
    (zcol:cell_point*(list (Coef * Sign))):=
    let (z,l):=one_table_up l n zcol in
    let aux := fun rlsign:Rpoint *(list (Pol*Sign)) =>
      let (r,lsign):=rlsign in
	((z, r),lsign) in
	map aux l.
 
  Let one_table_up_map(l:list Pol)(n:nat)
    (zcol_list:list (cell_point*(list (Coef*Sign)))):=
    map (one_table_up_push l n) zcol_list.

  



Let Pol_cad(l:list Pol)(n:nat) :=
    let cad := ccad (elim l) n in
      @cCad_map 
      (list (cell_point*(list (Coef*Sign)))) (list (list (cell_point_up *(list (Pol*Sign)))))
      (one_table_up_map l n) cad .
*)
  (************************************************************)
  (*****         Misc. for upper dimension               ******) 
  (************************************************************)


(*  Let mk_Cad_type(x:Set) := cmk_Cad_type (list x).

  Let Cad_map(A B:Set)(c:mk_Cad_type A)(f:A ->B):=
    @cCad_map (list A) (list B) c (fun x:list A => map f x).

*)
  (** Builds an Info from a Pol P, low sign is not computed **)
    Let Info_of_Pol(info_sign:Sign)(P:Pol):=
      let Pbar := Pol_square_free P in
      let dPbar := Pol_deg Pbar in
	match info_sign with
	  |Some _ => Five P Pbar dPbar info_sign info_sign
	  |_ => Five P Pbar dPbar None None
	end.

    
(*
    Let Pol_sign_at_for_upper(c:Info)(z:cell_point_up)(n:nat):=
      let (P,Pbar, dPbar, slow):=c in
	snd (sign_at_root P Pbar dPbar z n)

*)

    (* in the version of Pol_sign_at for upper dim,
   we evaluate to determine
  the sign a -inty because this -infty may not be coherent with the pol 
  (a bern coef for example) we ar computing the sign of*) 
    Let Pol_sign_at_for_upper(i:Info)(t:cell_point_up)(n:nat):=
     let (Q, Qbar, dQbar, _,_):= i in 
     let (z,rpt):=t in
      match rpt with
	|Minf m =>	  
	  let (res_z, res_sign) := Pol_eval_sign_at_isol Q Qbar z m n in
	     ((res_z, rpt),(Q,snd res_sign))

	|Root r =>
	  let (res_z, res_sign) := Pol_eval_sign_at_isol Q Qbar z r n in
	    ((res_z, rpt),(Q,snd res_sign))
	|Between b => 
	  let (res_z, res_sign) := Pol_eval_sign_at_isol Q Qbar z b n in
	   ((res_z,rpt), (Q,snd res_sign))
	|Alg_root (Five a b P Pbar bern) =>
	  let Pbar := Pol_square_free P in
	  let G := Pol_gcd Q P in
	  let dG := Pol_deg G in
	  let bernG :=Pol_bern_coefs G a b dG in
	  let (res_z, res_sign) :=  
	    pair_refine z Q Qbar dQbar a b P Pbar G bern bernG  n in
	    (res_z,(Q,snd res_sign))
	    
      end.
   


  (************************************************************)
  (******   Building of the parametric record         *********)
  (************************************************************)


  Let mkCad := next_mkCad Rat C bern cmkCad.
(*    Let mkCad := @mkCad_up cmkCad.**)

  Definition CAD_make := @mk_cad Rat Coef cInfo path mkCad
    P0 P1
    Pol_add 
    Pol_mult_base_cst
    Pol_mul
    Pol_sub
    Pol_opp
    Pol_of_Rat
    Pol_is_base_cst
    Pol_zero_test
    Pol_base_cst_sign
    Pol_pow
    Pol_div_base_cst 
    Pol_div
    Pol_gcd_gcd_free
    Pol_square_free
    cell_refine
    Pol_low_bound
    Pol_value_bound
    Info_of_Pol
    Pol_low_sign_for_upper
    Pol_sign_at_for_upper
    Pol_cad.


End UP_DIM.

End MK_UP_DIM.
