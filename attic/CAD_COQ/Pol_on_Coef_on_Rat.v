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

and an underlying Rat_structure, this means

cof_Rat : Rat -> Coef
cis_Rat : Coef -> bool
cof_pos:positive -> Coef 

*)
 Notation  "x # y" := (MkRat x y)(at level 20, no associativity).

 Notation "x // y" := (cdiv x y) (at level 40, left associativity).

 (** Builds a Pol from a Rat *)
 Definition Pol_of_Rat(r:Rat) := Pc (cof_Rat r). 

 (** Builds a constant pol from a positive **)
 Definition Pol_of_pos(p:positive):Pol:= Pc (cof_Rat (rof_pos p)).


 (** Cst pol from a rational **)
 Definition  Pol_mkPc(c:Rat):= Pc (cof_Rat c).

(** Truncations of P:truncates if the leading coef is not a base cst **)
 Definition Pol_trunc(P:Pol) :=
   let f:=
     fix Poln_trunc(P:Pol)(tlist:list Pol)(clist:list Coef){struct P}:(list Pol)*(list Coef) :=
       match P with
	 |Pc c =>
	   if (cis_Rat c) then ((P :: tlist), clist) else ((P :: (Pc c0) :: tlist), c::clist)
	 |PX Q i c => let (tres,cres):= Poln_trunc Q tlist clist in
	   (map (fun x => (mkPX  x i c)) tres, cres)
       end in
       f P nil nil.


 (**************************************************************)
 (***********         Division (pseudo)         ****************)
 (**************************************************************)


  (** division:like an euclidian division, but if the division over coef
  fails, returns 0*)
(* patch 12/07*)

 Definition Pol_div_cst :=
   fix Pol1_div_cst(A:Pol)(q:Coef){struct A}: Pol:=
     if (Pol_zero_test A) then P0
     else
     match A with
       |Pc a => Pc (a // q)
       |PX P i p => 
	 let P':= (Pol1_div_cst P q) in
	 if (Pol_zero_test P') then P0 else
	   if czero_test p then PX P' i p else
	     let p':= p // q in
	       if czero_test p' then P0 else
		 PX P' i p'
     end.
 

   (*auxiliary division of RX^i by D.invariant : 
    -- deg R < deg D
    -- R <> 0
    -- D is not constant *)
 Definition Pol_div_aux(D:Pol):=
   let (dd, cd) := Pol_deg_coefdom D in
     fix Pol_div_aux(R:Pol)(i:positive){struct i}:Pol*Pol:=
       let (dr,cr) := (Pol_deg_coefdom R) in
       	 match (Ncompare (dr + (Npos i)) dd) with
	   |Lt => (Pc c0, PX R i c0)
	   | _  => 
	     match i with
	       | xH => (Pc (cr // cd), (mkPX R xH c0) - (Pol_mul_Rat D (cr//cd)))
	       | xO p =>
		 let (Q1, R1) := (Pol_div_aux R p) in
		 let (dR1, cR1):=(Pol_deg_coefdom R1) in
		   if (czero_test cR1) then (mkPX Q1 p c0, Pc c0)
		     else
		       let (Q2, R2):=(Pol_div_aux R1 p) in 
			 ((mkPX Q1 p c0) + Q2, R2)
	       | xI p =>
		 let (Q1, R1):=(Pol_div_aux R p) in
		 let (dR1, cR1):=Pol_deg_coefdom R1 in
		   if (czero_test cR1) then 
		     ((mkPX Q1 (Psucc p) c0), Pc c0)
		     else
		       let (Q2, R2) := (Pol_div_aux R1 p) in
		       let (dr2, cr2) := (Pol_deg_coefdom R2) in
			 if (czero_test cr2) then
			   ((mkPX Q1 (Psucc p) c0)+(mkPX Q2 xH c0), Pc c0)
			   else
			     match (Ncompare (Nsucc dr2) dd) with
			       | Lt => 
				 ((mkPX Q1 (Psucc p) c0)+(mkPX Q2 xH c0), mkPX R2 xH c0)
			       | _ =>
				 let quo := (mkPX Q1 (Psucc p) c0)+ (mkPX Q2 xH c0)+(Pc (cr2//cd)) in
        		         let rem := (mkPX R2 xH c0) - (Pol_mul_Rat D (cr2//cd)) in
				   (quo,rem)
			     end
	     end
       	 end.
 		


  (** division of polynomials with coef in Coef:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ ++ R and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ## non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + c1 and deg(c1)<deg(B)
  then AX+a=(BQ1)X^i + c1X^i +a and :
    - either deg (c1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = c1X^i + a
    - or deg (c1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb c1 i i.e. c1X^i = Q2B ++2
  ## poly returned are normalized as soon as args are normalized
  **)
 
 (** First division by a non constant polynomial **)

 Definition Pol_euclide_div_PX(B:Pol):=
   let (db,cb) := Pol_deg_coefdom B in
     fix Pol_euclide_div_PX (A :Pol):Pol*Pol :=
       match A with
     	 |Pc a => (Pc c0, Pc a)
     	 |PX P i p =>
       	   let (Q1, R1):=Pol_euclide_div_PX P in
	   let (dr, r) := Pol_deg_coefdom R1 in
	     match (Pol_zero_test R1),(Ncompare (Nplus (Npos i) dr) db) with
	       |true, _ => (mkPX Q1 i c0, Pc p)
	       | _ , Lt => (mkPX Q1 i c0, mkPX R1 i p)
	       | _ , _ => let (Q2, R2) := (Pol_div_aux B R1 i) in
		 ((mkPX Q1 i c0)+Q2, R2 + Pc p)
	     end
       end.




 (** General division function **)
 Definition Pol_euclide_div(A B:Pol):Pol*Pol :=
   match B with
     |Pc q => (Pol_div_cst A q, Pc c0) 
     |_ => (Pol_euclide_div_PX B A)
   end.

 (** Only the quotient **)
 Definition Pol_div(A B:Pol):Pol:= fst (Pol_euclide_div A B).



  (************************************************************)
  (***          Subresultant polynomials                     **)
  (************************************************************)

  (** Notations are the ones of BPR **)

  (** q to the n*(n+1)/2 **)
 Definition sum_pow(q:Coef)(n:N):Coef :=
   match n with
     |N0 => c1
     |Npos p => 
       match p with
	 |xH => q
	 |xO p' => cpow q (Npos (Pmult p' (Psucc p)))
	 |xI p' => cpow q (Npos (Pmult (Psucc p') p))
       end
   end.


  (** kth subresultant coefficient **)
 Definition Pol_subres_aux (j k:N)(q q':Coef): Coef:=
   let t := (Npred (Nminus j k)) in
     (sum_pow (-- c1) t)**(cpow (q // q') t)** q.
 
 
  (*next polynomial in the sequence,after ASRi_1 and SRj_1 and arguments
      for the possible next step of computations. if is nul, then B was
      the last poly of the sequence. SRj_1 is not zero*)
 
 Definition Pol_next_subres(SRi_1 SRj_1:Pol)(srj:Coef)(i j:N):
   (uple4 Pol Coef N N) :=
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next_SR := fun x:Coef =>
     -(Pol_div_cst 
       (snd (Pol_euclide_div (Pol_mul_Rat SRi_1 x) SRj_1))
       (srj **  dom_sri_1)) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let srj_1 := dom_srj_1 in
	   (Four (next_SR (cpow dom_srj_1 2)) dom_srj_1 j k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	   (Four (next_SR (dom_srj_1 **  srk)) srk j k)
     end.

  (** next triple (S, U, V) in the rec relation for subresultants **)
 Definition Pol_next_subres_triple(Ti_1 Tj_1:(triple Pol Pol Pol))(srj:Coef)(i j:N):
   uple6 Pol Pol Pol Coef N N :=
   let (SRi_1,Ui_1,Vi_1) := Ti_1 in
   let (SRj_1,Uj_1, Vj_1) := Tj_1 in
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next :=
     (fun x => 
       let (C,R) := (Pol_euclide_div (Pol_mul_Rat SRi_1 x) SRj_1) in
       (C, Pol_div_cst R ((-- srj)** dom_sri_1)) ) in
   let next_UV :=
     (fun (x:Coef)(Pi_1 Pj_1 C:Pol) =>
       (Pol_div_cst
	 ((C * Pj_1) - (Pol_mul_Rat Pi_1 x)) (srj** dom_sri_1))) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let y:= (cpow dom_srj_1 2) in
	 let (C,SR) := next y in
	   (Six
	     SR (next_UV y Ui_1 Uj_1 C) (next_UV y Vi_1 Vj_1 C) dom_srj_1 j k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	 let y:= (dom_srj_1 **  srk) in
	 let (C,SR) := next y in
	   (Six
	     SR (next_UV y Ui_1 Uj_1 C) (next_UV y Vi_1 Vj_1 C) srk j k)
     end.


   (**Subres pol list, from A B, n ensures termination and will be deg P + 1**)

 Definition Pol_subres_list1:=
   fix Pol1_subres_list1(A B:Pol)(q:Coef)(i j:N)(m:nat){struct m}:list Pol :=
     match m with
       |O => nil
       |S n => 
	 let (SR,sr,k,l) := (Pol_next_subres A B q i j) in
	   if (Pol_zero_test SR) then nil
	     else   SR :: (Pol1_subres_list1 B SR sr k l n)
     end.

 Definition Pol_subres_list(A B:Pol) := 
   let p := Pol_deg A in
   let q := Pol_deg B in
   A :: B :: (Pol_subres_list1 A B c1 (p+1) p  (S (nat_of_N p))). 


 Definition Pol_subres_coef_list(A B:Pol):=
   let dom := (fun x => Pol_dom x) in (* for impl args*)
   let res := Pol_subres_list A B in
     map dom res.

  (** Extented subresultants **)
 Definition Pol_ext_signed_subres_list :=
  fix Pol1_ext_signed_subres_list(T T':(triple Pol Pol Pol))(q:Coef)(i j:N)(m:nat)
    {struct m}:list (triple Pol Pol Pol) :=
    let (B,_,_):= T' in
      if (Pol_zero_test B) then nil
	else
	 match m with
	   |O => nil
	   |S n => 
	     let (next_SR,next_U,next_V,sr,k,l) := (Pol_next_subres_triple T T' q i j) in
	     let next_T := Tr next_SR next_U next_V in
     	       next_T :: (Pol1_ext_signed_subres_list T' next_T sr k l n)
	 end.

 
  (** extended signed subres chain *)
   Definition Pol_ext_signed_subres_chain(P Q:Pol) :=
	let (deg_p, dom_p) := Pol_deg_coefdom P in
   	let (deg_q, dom_q) := Pol_deg_coefdom Q in
	let Tp := Tr P P1 P0 in
	let Tq := Tr Q P0 P1 in
     	  Tp :: (Tq :: 	
    	    (Pol_ext_signed_subres_list
      	      Tp Tq  c1 deg_p (Npred deg_p) (S (nat_of_N deg_p)))).
     
       



   (** Gcd of P and Q : last subresultant dP>dQ **)

   (** For polys with different degrees **)
   Definition Pol_gcd_strict (P Q:Pol) :=
     let l := (Pol_subres_list P Q) in 
     let SRj := (last_elem l Q) in
     let srj := Pol_dom SRj in
     let cP := Pol_dom P in
       Pol_div_cst (Pol_mul_Rat SRj cP) srj.
    

   Definition Pol_gcd(P Q:Pol) :=
     let (dP, cP):= Pol_deg_coefdom P in
     let (dQ,cQ) := Pol_deg_coefdom Q in
       match Ncompare dP dQ with
	 |Lt  => Pol_gcd_strict Q P
	 |Gt  => Pol_gcd_strict P Q
	 |Eq => 
           let next := ((Pol_mul_Rat Q cP) - (Pol_mul_Rat P cQ)) in
             match next with
              |Pc c0 => P
              |_ => Pol_gcd_strict P next
             end
       end.

   (** Triple gcd of P and Q, P/gcd, Q/gcd **) 

   (** For polys with different degrees **)
   Definition Pol_gcd_gcd_free_strict (P Q:Pol) :=
     let cP := Pol_dom P in
     let (Tj, Tj_1):= two_last_elems (Pol_ext_signed_subres_chain P Q) 
       ((Tr (Pc c0) (Pc c0) (Pc c0)),(Tr (Pc c0) (Pc c0) (Pc c0))) in
     let (SRj,_,_) := Tj in
     let srj := Pol_dom SRj in
     let (_,Uj_1,Vj_1) := Tj_1 in
     let cVj_1 := Pol_dom Vj_1 in
     let cUj_1 := Pol_dom Uj_1 in
       (Pol_div_cst (Pol_mul_Rat SRj cP) srj,
         Pol_div_cst (Pol_mul_Rat Vj_1 cP) cVj_1,
	 Pol_div_cst (Pol_mul_Rat Uj_1 cP) cUj_1).


  (*TODO virer les contenus constants?*)


   Definition Pol_gcd_gcd_free (P Q:Pol) :=
     match P, Q with
       |Pc p, Pc q => 
	 let (a,b) := cgcd_gcd_free p q in (Pc (snd a), Pc (snd a), Pc b)
       |_,_ => 
	 let (dQ,cQ):= Pol_deg_coefdom Q in
	 let (dP,cP):= Pol_deg_coefdom P in
	   match (Ncompare dP dQ) with
	     |Eq => 
	       let Next := (Pol_mul_Rat Q cP) - (Pol_mul_Rat P cQ) in
	       let (GCD_Q',Next'):= Pol_gcd_gcd_free_strict Q Next in
	       let (GCD,Q'):= GCD_Q' in
	       let cGCD := Pol_dom GCD in
	       let cQ' := Pol_dom Q' in
	       let cNext' := Pol_dom Next' in
	       let cNext := Pol_dom Next in
		 (GCD,
		   (Pol_mul_Rat Q' ((cGCD** cNext'** cP)// cNext)) -
		   (Pol_mul_Rat Next' ((cGCD** cQ')// cQ)),
		   Q')
	     |Gt  => Pol_gcd_gcd_free_strict P Q
	     |Lt  => Pol_gcd_gcd_free_strict Q P
	   end
     end.
    

   (** Square free part of a poly **)
 Definition Pol_square_free(P:Pol) := snd (fst (Pol_gcd_gcd_free P (Pol_deriv P))).



  (** Tests if P is a base cst **)
 Definition  Pol_is_base_cst(P:Pol):=
   match P with
     |Pc c => cis_Rat c
     |PX Q i c => false
   end.




  (** Prod and div by a rational, maps the rat operation over base coefs *)
 Definition Poln_op_base_cst (Op:Coef->Rat->Coef):=
   fix Poln_op_base_cst(P:Pol)(c:Rat){struct P}:Pol:=
     match P with
       |Pc p => Pc (Op p c)
       |PX Q i q => mkPX (Poln_op_base_cst Q c) i (Op q c)
     end.




 Definition Pol_mult_base_cst := Poln_op_base_cst cmult_base_cst.
 Definition Pol_div_base_cst :=Poln_op_base_cst cdiv_base_cst.


  (** Eval of a pol at a rational, returns a coef *)
 Definition Pol_partial_eval :=
   fix partial_eval(P:Pol)(c:Rat){struct P}:Coef:=
     match P with
       |Pc p => p
       |PX Q i q =>
	 (cmult_base_cst (partial_eval Q c) (rpow c (Npos i)))++q
     end.


