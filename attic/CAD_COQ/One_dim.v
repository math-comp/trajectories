(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.


Require Import Qabs.
Require Import Utils.
Require Import CAD_types.


Module MK_ONE_DIM(Q:RAT_STRUCT).


  Module QFUNS:= RAT_FUNS Q.
  Module QINT := RAT_INT_OPS Q.
  
  Import Q.
  Import QFUNS.
  Import QINT.

Section ONE_DIM.


(* Initialization for the loading of Gen_functor *)
  
  Let Coef:= Rat.
  Let c0 := r0.
  Let c1 := r1.
  Let cadd :=  radd .
  Let copp :=  ropp .
  Let cmul :=  rprod .
  Let csub := rsub .
  Let cdiv := rdiv .
  Let czero_test := rzero_test .
  Let cpow := rpow .
  Let cof_pos(p:positive):=rof_pos p.
  Let cof_Rat(r:Rat) := r.
  Let cbase_cst_sign := fun x:Coef => (Some (rsign  x)).

  Let cgcd_gcd_free :=
    fun x y:Coef => let m:= rmax x y in (m, rdiv x m, rdiv y m).
  Let cis_Rat := fun x:Rat => true.
  Let cmult_base_cst := cmul.
  Let cdiv_base_cst := cdiv.
  Let path := unit.
  Let cvalue_bound(x:unit)(y:Rat):=(y,y).
  Let ccell_point_up_refine(x:unit):=x.
  Let csign_at(x:Coef)(u:unit)(n:nat):=(u,(x,Some (rsign  x))).
  Let cdeg(x:Coef):=N0.
  Let ccell_refine(u:unit)(n:nat):=Some u.
  Let cInfo := Coef.
  Let cInfo_of_Pol(s:Sign)(c:Coef):=c.
  Let cPol_of_Info(c:Rat):=c.
  Let cmk_Info(a b:Rat)(n:N)(s1 s2:Sign):= a.

 

Load Pol_on_Coef.
Load Pol_on_Coef_on_Rat.
Load Bern.
Load Alg.

(*  Load Gen_functor.*)

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
     Pol_bern_split....*)


  (************************************************************)
  (***             Real root isolation                      ***)
  (************************************************************)


  (** sum of abs values of the coefs of P **)
  Definition  sum_abs_val_coef:=
  fix sum_abs_val_coef (P:Pol):Rat:=
    match P with
      |Pc p => rabs_val p
      |PX P' i p => (rabs_val p) +r sum_abs_val_coef P' 
    end.
  

  (** Cauchy upper bound for the real roots of P **)
  Definition  Pol_up_bound(P:Pol):=
  let p:= Pol_dom P in
    ((sum_abs_val_coef P)//(rabs_val p))+r r1.

  (**idem, but fits the type in the CAD record **)
  Definition Pol_up_bound_tt(P:Pol)(u:unit):=Pol_up_bound P.


  (** Cauchy lower bound for the real roots of P **)
  Definition root_low_bound1:=
  fix root_low_bound1(P:Pol)(sum:Rat){struct P}:Rat :=
    match P with
      |Pc p => sum // p
      |PX P' i p' => 
	if (rzero_test p')
	  then root_low_bound1 P' sum
	  else sum // (rabs_val p')
    end.

  Definition  Pol_low_bound (P:Pol) := 
    ropp ((root_low_bound1 P (sum_abs_val_coef P))+r r1).

  (**idem, but fits the type in the CAD record **)
  Definition Pol_low_bound_tt(P:Pol)(u:unit):=Pol_low_bound P.

  (** Sign of P at -infty **)

  Definition Pol_low_sign(P:Pol):=
  Some (rsign (Pol_eval P (Pol_low_bound P))).

  (**idem, but fits the type in the CAD record **)
  Definition Pol_low_sign_info(u:unit)(P Pbar:Pol)(n:nat):=
  (tt,Pol_low_sign P).


  (** Builds an Info from a Pol P **)
  Definition Info_of_Pol(info_sign:Sign)(P:Pol):=
    let Pbar := Pol_square_free P in
    let dPbar := Pol_deg Pbar in
      match info_sign with
	|Some _ => Five P Pbar dPbar info_sign info_sign
	|_ =>
	  let low := Pol_low_sign P in
	    Five P Pbar dPbar low None
      end.




  (**isolates roots of P over ]c d[ **)
  Definition root_isol1(P:Pol)(Pbar:Pol)(degPbar:N):=
  fix root_isol1(res:list (Rpoint*(list (Pol*Sign))))
    (c d:Rat)(blist: list Rat)(n:nat){struct n}:
    list (Rpoint*(list (Pol* Sign))):=
    if rlt d c 
      then nil
      else
	let Vb := sign_changes (map rsign blist) in
	  match Vb  with
	    |O => res
	    |1 =>
	      if negb (rzero_test ((Pol_eval P c) *r (Pol_eval P d)))
		then (Alg_root (Five c d P Pbar blist), (P, Some Eq)::nil)::res
		else
		  match n with
		    |O => (Alg_root (Five c d P Pbar blist),(P, None)::nil)::res
		    |S n' => 
		      let mid := (d +r c) // (2 # 1) in
		      let (b', b''):= Pol_bern_split blist c d mid in
		      let res':= root_isol1 res c  mid  b' n' in
			if (rzero_test (Pol_eval Pbar mid)) 
			  then
			    root_isol1 ((Root Coef cInfo mid,(P, (Some Eq))::nil)::res')
			    mid d b'' n'
			  else
			    root_isol1 res'  mid d b'' n'
		  end
	    |_ =>
	      match n with
		|O => (Alg_root (Five c d P Pbar blist), (P,None)::nil)::res
		|S n' => 
		  let mid := (d +r c) // (2 # 1) in
		  let (b', b''):= Pol_bern_split blist c d mid in
		  let res':= root_isol1 res c  mid  b' n' in
		    if rzero_test (Pol_eval Pbar mid) 
		      then
			root_isol1 ((Root Coef cInfo mid, (P,(Some Eq))::nil)::res') mid d b'' n'
		      else
			root_isol1 res'  mid d b'' n'
	      end
	  end.


  (** isolation of the roots of P over the real line **)
  Definition root_isol
    (Pinfo:Info)(lbound ubound:Rat)(n:nat):=
    let (P, Pbar, degPbar,low_sign,info_sign):=Pinfo in
      match info_sign with
	|Some s => (Between Coef cInfo lbound, (P, info_sign)::nil)::nil
	|None =>
	  root_isol1 P Pbar degPbar
	  ((Between Coef cInfo lbound,(P, low_sign)::nil)::nil)
	  lbound ubound (Pol_bern_coefs Pbar lbound ubound degPbar) n
      end.
  

  (** isolation of the roots of P over ]c d[ 
  WARNING, do not add Minf, and so returns the  empty list if P has a cst sign over ]cd[**)
  Definition root_isol_int(Pinfo:Info)(c d:Rat)(n:nat) := 
    let (P, Pbar, degPbar,low_sign,info_sign):=Pinfo in
      match info_sign with
	|Some _ => nil
	|None =>
	  root_isol1  P Pbar degPbar nil c d (Pol_bern_coefs Pbar c d degPbar) n
      end.
 
 
  (** Sign of Q at a root of P which is not a root of Q 
       None means n was not large enough **)
  Definition sign_at_non_com(Q Qbar:Pol):=
    fix sign_at_non_com(a b:Rat)(P Pbar:Pol)(bern bernQ:list Rat)
      (n:nat){struct n}: (Rpoint* Sign):=
      let test := sign_changes (map rsign bernQ) in
	match test with
	  |O => (Alg_root (Five a b P Pbar bern), (Some (rsign (Pol_eval Q a))))
	  |S _ => 
	    let mid := (a +r b) // (2 # 1) in
	    let Pbar_mid := Pol_eval Pbar mid in
	      if rzero_test Pbar_mid
		then (Root Coef cInfo mid , (Some (rsign (Pol_eval Q mid))))
		else
		  match n with
		    |O => (Alg_root (Five a b P Pbar bern), None)
		    |S m =>
		      match rsign (Pbar_mid *r (Pol_eval Pbar a)) with
			| Lt  =>
			  let (bern',_) := Pol_bern_split bern a b mid in
			  let (bernQ',_) := Pol_bern_split bernQ a b mid in
			    sign_at_non_com a mid P Pbar bern' bernQ' m
			|_ =>
			  let (_,bern'') := Pol_bern_split bern a b mid in
			  let (_,bernQ'') := Pol_bern_split bernQ a b mid in
			    sign_at_non_com mid b P Pbar bern'' bernQ'' m
		      end
		  end
	end.



    (** refines [ab] which contains a unique root of P and G=gcd P Q
      to a intervalle which isolates for Q **)

  Definition sign_at_com :=
  fix sign_at_com(a b:Rat)(P Pbar G Gbar:Pol)
    (bernG bernQ:list Rat)(n:nat){struct n}:
    Rpoint*Sign:=
    let VbQ := sign_changes (map rsign bernQ) in  
      match VbQ with
	|O => (Alg_root (Five a b G Gbar bernG), None) (*never!*)
	|S O => (Alg_root (Five a b G Gbar bernG), (Some Eq))
	|S _ =>
	  let mid := (a +r b) // (2 # 1) in
	    let Pbar_mid := (Pol_eval Pbar mid) in
	      if rzero_test Pbar_mid
		then 
		  (Root Coef cInfo mid, (Some Eq))
		else
		  match n with
		    |O => (Alg_root (Five a b G Gbar bernG), None)
		    |S n' =>
		      match rsign (Pbar_mid *r (Pol_eval Pbar a)) with
			|Lt =>
			  let (bernG',_):=Pol_bern_split bernG a b mid in
			    let (bernQ',_):= Pol_bern_split bernQ a b mid in
			      sign_at_com a mid P Pbar G Gbar bernG' bernQ' n'
			|_ =>
			  let (_,bernG''):=Pol_bern_split bernG a b mid in
			    let (_,bernQ''):=Pol_bern_split bernQ a b mid in
			      sign_at_com mid b P Pbar G Gbar bernG'' bernQ'' n'
		      end
		  end
      end.



  (** refines an AlgRoot of P to determine the sign of Q
     ie up to the point where G=gcd P Q has either a unique root or no root **)

  Definition pair_refine (Q Qbar:Pol)(dQbar:N):=
  fix pair_refine(a b:Rat)(P Pbar G:Pol)
    (bern bernG:list Rat)(n:nat){struct n}:
    Rpoint*Sign:=
    let VbG := sign_changes (map rsign bernG) in
      match VbG with
	|O => 
	  let bernQ := Pol_bern_coefs Qbar a b dQbar in
	    sign_at_non_com Q Qbar (*dQbar *)a b P Pbar bern bernQ n 
	|S O =>
	  let bernQ := Pol_bern_coefs Qbar a b dQbar in
	  let Gbar := Pol_square_free G in
	      sign_at_com a b P Pbar G Gbar bernG bernQ n
	|_ =>
	  let mid := (a +r b) // (2 # 1) in
	  let Pbar_mid := (Pol_eval Pbar mid) in
	      if rzero_test Pbar_mid
		then 
		  (Root Coef cInfo mid, Some (rsign (Pol_eval Q mid)))
		else
		  match n with
		    |O => (Alg_root (Five a b P Pbar bern), None)
		    |S m =>
		      match rsign (Pbar_mid *r (Pol_eval Pbar a)) with
			|Lt =>
			  let (bern',_):=Pol_bern_split bern a b mid in
			  let (bernG',_):=Pol_bern_split bernG a b mid in
			      pair_refine
			      a mid P Pbar G bern' bernG' m
			|_ =>
			  let (_,bern''):=Pol_bern_split bern a b mid in
			  let (_,bernG''):=Pol_bern_split bernG a b mid in
			      pair_refine
			      mid b P Pbar G bern'' bernG'' m
		      end
		  end
      end.


  (** Sign of Q at a cell_point_up, previous failures are propagated **)
  Definition sign_at(t:Rpoint)(n:nat)(Qinfo:Info):=
    let (Q,Qbar,dQbar,low,infosign) := Qinfo in
      match infosign with
	|Some s => (t,(Q,infosign))
	|None =>
	  match t with
	      |Minf m => (Between Coef cInfo m, (Q,low))
	      |Root r => 
		(Root Coef cInfo r, (Q,Some (rsign (Pol_eval Q r))))
	      |Between b =>
		(Between Coef cInfo b, (Q,Some (rsign (Pol_eval Q b))))
	      |Alg_root (Five a b P Pbar bern) =>
		let G := Pol_gcd Q P in
		let dG := Pol_deg G in
		let bernG := Pol_bern_coefs G a b dG in
		let (t,s) := 
		  pair_refine Q Qbar dQbar a b P Pbar G bern bernG  n in
		  (t,(P,s))
	    end
      end.

  (**idem, but fits the type in the CAD record **)
  Definition Pol_sign_at(c:Info)(z:cell_point_up)(n:nat):=
    let(_,t):= z in
    let (r, u):= sign_at t n c in ((tt,r),u).



  (* t is the current column : a root and the signs already computed,
  sign_list_at_root adds the sign of Q on top of these signs, and has
  possibly refined the root encoding for this purpose **)

  Definition  sign_list_at_root(Qinfo:Info)(t:Rpoint*(list (Pol*Sign)))(n:nat):  Rpoint*(list (Pol*Sign)) :=
  let (root, sign_list) :=  t in
    match sign_list with
      | nil =>
 	let (root_res, sign_res):= sign_at root n Qinfo in
	  (root_res, sign_res::nil)
      | ( _ ,None) :: _ => (root, ((Pol_of_Info Qinfo),None) :: sign_list)
      | _ :: _ =>
	let (root_res, sign_res):= sign_at  root n Qinfo in
	  (root_res, sign_res::sign_list)
    end.
  


  (** finds the sign colon at b, b is between two roots and the sign column
  correspond to the root just smaller than b is lsign.
   evaluates only if necessary  **) 

  Definition fill_sign_between :=
    fix fill_sign_between(b:Rat)(lsign:list (Pol*Sign))
      {struct lsign}:list(Pol* Sign) :=
      match lsign with
	|nil => nil
	|shd::stl =>
	  match shd with
	    | (_ , None) => shd ::(fill_sign_between b stl)
	    | (P,Some s) =>
	      match s with
		|Eq => 
		  (P, Some (rsign (Pol_eval P b)))::(fill_sign_between b stl)
		|_ => shd :: (fill_sign_between b stl)
	      end
	  end
      end.



  (** Sign table for the family P::lP,  over ]low,up[
     P(low) has sign lowsign, P(up) has sign upsign 
     l contains the relevant sign table for lP **)

  Definition add_roots(Pinfo:Info)(lP:list Info) :=
    let (P, freeP, dfreeP, low_sign, info_sign):= Pinfo in
      match info_sign with
	|Some s => 
	  fun l:list (Rpoint* (list (Pol * Sign)))=>fun low up:Rat=>fun lowsign upsign:Sign=>fun n:nat =>
	    map (fun x => (fst x, (P, info_sign)::(snd x))) l
	|None =>
	  fix add_roots(l:list (Rpoint* (list (Pol * Sign))))
	    (low up:Rat)(lowsign upsign:Sign)
	    (n:nat){struct l}:list (Rpoint * (list (Pol* Sign))) :=
	    match l with
	      |nil => nil
	      |hd :: tl =>
		let tag := fst hd in
		let prev_slist := snd hd in
		    match tag with
		      |Between b => 
			let resP := root_isol_int Pinfo low up n in
			  ((add_to_cst_list resP prev_slist)@
			    ((Between Coef cInfo b, (P,(Some (rsign (Pol_eval P low ))))::prev_slist))::nil)

		      |Minf  m =>
			let resP := root_isol_int Pinfo low up n in
			  ((add_to_cst_list resP prev_slist)@
			    ((Between Coef cInfo m, (P,(Some (rsign (Pol_eval P low ))))::prev_slist))::nil)
		      |Root  r =>
			if orb (rlt up r) (rzero_test (r  -r  up))
			  then
			    (tag, (P, upsign)::prev_slist)::
			    (add_roots tl low r lowsign upsign n)
			  else
			    let signP_r := rsign (Pol_eval P r) in			
			      let resP := root_isol_int Pinfo r up n in
				let prev_next_sign := fill_sign_between ((r+r up)//(2 # 1))
				  prev_slist in
				  let res_r_up := (add_to_cst_list resP prev_next_sign) in
				    res_r_up @
				    ((Root Coef cInfo r, (P, (Some signP_r)):: prev_slist)::
				      (add_roots tl low r  lowsign (Some signP_r) n))
		      |Alg_root (Five a b Q Qbar bern) =>
			let refine := sign_list_at_root Pinfo hd n in
			  match (fst refine) with
			    |Between b => (*dummy*)(Between Coef cInfo b, (P,None) :: prev_slist)::tl
			    |Minf  m => (Between Coef cInfo m, (P,None) :: prev_slist):: tl (*should never happen*)
			    |Root r =>
			      if orb (rlt up r) (rzero_test (r  -r  up))
				then
				  refine::
				    (add_roots  tl low r lowsign upsign n)
				else
				  let signP_r :=
				    match snd refine with
				      |nil => None
				      |s :: tl => snd s
				    end in
				    let prev_next_sign :=
				      fill_sign_between ((r+rup)//(2#1)) prev_slist  in
				      let resP := (root_isol_int Pinfo r up n) in
					let res_r_up := (add_to_cst_list resP prev_next_sign) in
					  res_r_up @
					  (refine::
					    (add_roots tl low r  lowsign 
					      signP_r n))
			    |Alg_root (Five a' b' Q' Qbar' bern') =>
			      if orb (rlt up a') (rzero_test (a'  -r  up))
				then
				  refine::
				    (add_roots tl  low a' lowsign upsign n)
				else
				  let Pa' := Pol_eval P a' in
				    let Pb' := Pol_eval P b' in
				      let prev_next_sign :=
					fill_sign_between ((b'+rup)//(2#1)) prev_slist  in
					let resP := (root_isol_int Pinfo b' up n) in
					  let res_b'_up := (add_to_cst_list resP prev_next_sign) in
					    match (rzero_test Pb'), (rzero_test Pa') with
					      |true, false =>
						res_b'_up @
						((Root Coef cInfo b', (P,(Some Eq))::prev_next_sign)::
						  refine::
						    (add_roots  tl low a' 
						      lowsign (Some (rsign Pa')) n))
					      |false, true =>
						let prev_a'_sign :=
						  map (fun x => snd (sign_at (Between Coef cInfo a') n x)) lP in
						(*  map (fun P =>(P, Some (rsign (Pol_eval P a')))) lP in*)
						  res_b'_up@
						  (refine ::
						    (Root Coef cInfo a', (P,(Some Eq))::prev_a'_sign)::
						    (add_roots  tl low a'
						      lowsign (Some (rsign Pa')) n))
					      |true, true =>
						let prev_a'_sign :=
						  map (fun x => snd (sign_at (Between Coef cInfo a') n x)) lP in
						  (*map (fun P => (P,Some (rsign (Pol_eval P a')))) lP in*)
						  res_b'_up @
						  ((Root Coef cInfo b', (P,(Some Eq))::prev_next_sign)::
						    refine ::
						      (Root Coef cInfo a', (P,(Some Eq))::prev_a'_sign)::
						      (add_roots tl low a'  
							lowsign (Some (rsign Pa')) n))
					      |false, false =>
						res_b'_up @ 
						(refine::
						  (add_roots tl low a'  
						    lowsign (Some (rsign Pa')) n))
					    end
			  end
		    end
	    end
      end.
			

	    

  (**head is the biggest root, computes the isolating list*)

  Definition family_root(global_low global_up:Rat)(n:nat) := 
  fix family_roots(Pol_list : list Info):list ( Rpoint * (list (Pol*Sign))):=
    match Pol_list with
      |nil => nil
      |Pinfo :: tl =>
	let (P, Pbar, dPbar, low_sign, info_sign):=Pinfo in
	let upsign := rsign (Pol_eval P global_up) in
	  match tl with
	    |nil => root_isol Pinfo global_low global_up n
	    |_ =>
	      let prev := family_roots tl in
		add_roots 
		Pinfo tl prev global_low global_up low_sign (Some upsign) n
	  end
    end.
  
  
  
    (** sign table for the family up to "up",included.
      up is not a root 
       head corresponds to the smallest root
       gup and glow are the points considered as +infty and -infty for 
       the whole family.*)

  Definition sign_table1 (glow gup:Rat):=
  fix sign_table1(Pol_list : list Pol)
    (isol_list : list (Rpoint*(list (Pol*Sign))))
    (up:Rat)(res:list (Rpoint*(list (Pol*Sign)))){struct isol_list}:
    list (Rpoint*(list (Pol*Sign))):=
    let Sign_eval := (fun x P =>
      (x, Some (rsign (Pol_eval P x)))) in
    match isol_list with
      |nil => res
      |hd::tl =>
	let hdTag := fst hd in
	let hdSign := snd hd in
	  match hdTag with
	    |Between b => (*dummy*)(Between Coef cInfo b, hdSign)::res
	    |Minf m=> (Between Coef cInfo glow, hdSign)::res
	    |Root   r =>
	      let bet := (r +r up)//(2 # 1) in
		match res with
		  |nil =>sign_table1 Pol_list tl r 
		    (( hdTag, hdSign) ::
			((Between Coef cInfo up, fill_sign_between bet hdSign)::res))
		  |_ =>
		    sign_table1 Pol_list tl r 
		    ((hdTag, hdSign) ::
		      ((Between Coef cInfo bet,fill_sign_between bet hdSign)::res))
		end
	    |Alg_root (Five a b _ _ _) =>
	      let bet := (b +r up)//(2#1) in
		match res with
		  |nil =>
		    sign_table1 Pol_list tl a
		    ((hdTag, hdSign)
		      ::((Between Coef cInfo gup,fill_sign_between bet hdSign) ::res))
		    |_ =>
		      sign_table1 Pol_list tl a
		      ((hdTag, hdSign)
			::(( Between Coef cInfo bet,fill_sign_between bet hdSign) ::res))
		end
	  end
    end.


(* information sur le polynome : P, Pbar, dP, lowsign(P), cst_tag(P). cst_tag(P) vaut None si P n'estpas constant, vaut le signe de P sinon*)

  Definition Info_init(low :Rat)(P:Pol):=
    let Pbar := Pol_square_free P in
    let dPbar := Pol_deg Pbar in
      match P with
	|Pc r => 
	  let s := Some (rsign r) in
	    Five P Pbar dPbar s s
	|_ =>
	  let lowsign := Some (rsign (Pol_eval P low)) in
	    Five P Pbar dPbar lowsign None
      end.



  Definition sign_table(Pol_list:list Pol)(n:nat):=
    let up := rmax_list (map Pol_up_bound Pol_list)in
    let low := rmin_list (map Pol_low_bound Pol_list) in
    let Pol_info_list := map (Info_init low) Pol_list in
    let roots := family_root low up n Pol_info_list in
	(sign_table1 low up Pol_list roots up nil).

(* dummy function to convert Rpoint into cell_point_up. pour l'instant on separe ca de sign_table1 vu que c'est provisoire *)


 Definition Rpoint_to_cell_point_up(rcol:Rpoint*(list (Pol *Sign))):=
    let (r,col):= rcol in
      (build_next_path tt r,col).

(*
  Definition Pol_cad(Pol_list:list Pol)(n:nat):=
  (tt,(sign_table Pol_list n)).
*)
  Definition Pol_base_cst_sign(P:Pol):=
    match P with
      |Pc p => Some (rsign p)
      |_ => None
    end.


  Definition CAD(A:Set):= A.


  Definition One_dim_cad := @mk_cad Rat Rat cInfo unit CAD
    P0 P1
    Pol_add Pol_mult_base_cst Pol_mul Pol_sub Pol_opp
    Pol_of_Rat Pol_is_base_cst
    Pol_zero_test  Pol_base_cst_sign Pol_pow Pol_div_base_cst Pol_div
    Pol_gcd_gcd_free   Pol_square_free 
    cell_refine
    Pol_low_bound_tt 
    Pol_value_bound Info_of_Pol
    Pol_low_sign_info Pol_sign_at 
    sign_table.

End ONE_DIM.

End MK_ONE_DIM.


