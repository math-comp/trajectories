Require Import IRing_def.
Require Import Utils.
Set Implicit Arguments.

 Inductive Pol1(C:Set):Set:=
 |Pc : C-> Pol1 C
 |PX : Pol1 C -> positive -> C -> Pol1 C.

Section MAKE_IR.

Variable IR_low : IRing.

(* Projection of the integral domain structure*)

Let Coef := C IR_low.
Let c0 := CO  IR_low.
Let c1 := CI IR_low.
Let cadd := Cadd IR_low.
Let cmul := Cmul IR_low.
Let csub := Csub IR_low.
Let copp := Copp IR_low.
Let czero_test := Czero_test IR_low.
Let cof_pos := C_of_pos IR_low.
Let cpow := Cpow IR_low.
Let cdiv := Cdiv IR_low.


 Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
 Notation "x ** y":= (cmul x y) (at level 40, left associativity).
 Notation "-- x" := (copp x) (at level 35, right associativity).
 Notation "x -- y" := (csub x y) (at level 50, left associativity).
 Notation "x // y" := (cdiv x y) (at level 40, left associativity).


Let Pol := Pol1 Coef.

Let P0 := Pc  c0.
Let P1 := Pc c1.

Definition mkPX P i c := 
  match P with
  | Pc p => if (czero_test p) then Pc c else PX P i c
  | PX P' i' c' => if (czero_test c') then PX P' (i' + i) c else PX P i c
  end.

(* all the following defined operations preserve normalization *)

 Let Pol_opp:=fix Pol_opp (P:Pol):Pol :=
   match P with
     |Pc p => Pc (-- p)
     |PX P i p => mkPX (Pol_opp P) i (-- p)
   end.
Notation "- P" := (Pol_opp P).

(** Addition and subtraction **)
 
(*P+Pc c*)
 Let Pol_addC (P:Pol)(c:Coef):Pol :=
  match P with
  | Pc c1 => Pc (c1 ++ c)
  | PX P i c1 => PX P i (c++c1)
  end.

(*P - Pc c*)
 Let Pol_subC (P:Pol) (c:Coef) : Pol :=
  match P with
  | Pc c1 => Pc (c1 -- c)
  | PX P i c1 => PX P i (c1 -- c)
  end.

 Section Pol_op_aux.

   Variable Pol_op : Pol -> Pol -> Pol.
   Variable P' : Pol.
   (* Inv : is_PX P', is_norm P', is_norm P *)
    (*P+P'*X^i*)
      Fixpoint Pol_addX(i':positive)(P:Pol) {struct P} : Pol :=
     match P with
       | Pc c => PX P' i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pol_op (PX P k c0) P') i' c
	   | Z0 => mkPX (Pol_op P P') i c
	  | Zneg k => mkPX (Pol_addX k P) i c
	 end
     end.
   
    (*P-P'*X^i'*)
   Fixpoint Pol_subX(i':positive)(P:Pol){struct P} : Pol :=
     match P with
       | Pc c => PX (- P') i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pol_op (PX P k c0) P') i' c
	   | Z0 => mkPX (Pol_op P P') i c
	   | Zneg k => mkPX (Pol_subX k P) i c
	 end
     end.
 
 
 End Pol_op_aux.

 (* Inv : is_norm P, is_norm P' *)
 Let Pol_add := fix Pol_add (P P': Pol) {struct P'} : Pol :=
   match P' with
     | Pc c' => Pol_addC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX P' i' (c ++ c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Pol_add (PX P k c0) P') i' (c ++ c')
	     | Z0 => mkPX (Pol_add P P') i (c ++ c')
	     | Zneg k => mkPX (Pol_addX Pol_add P' k P) i (c ++ c')
	   end
       end
   end.
 Notation "P + P'" := (Pol_add P P').

 Let Pol_sub :=
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
	     | Zneg k => mkPX (Pol_subX Pol_sub P' k P) i (c -- c')
	   end
       end
   end.
 Notation "P - P'" := (Pol_sub P P').
 
 (** Multiplication *) 


(*P*(Pc c) *)
Let Pol_mult_cst_aux :=
 fix Pol_mult_cst_aux (P:Pol) (c:Coef) {struct P} : Pol :=
  match P with
  | Pc c' => Pc (c' ** c)
  | PX P i c' => mkPX (Pol_mult_cst_aux P c) i (c'** c)
  end.

(*hack to speed up*)
 Let Pol_mult_cst P c :=
  if (czero_test c) then P0 else
  if (czero_test (c -- c1)) then P else Pol_mult_cst_aux P c.
 
 Let Pol_mul := fix Pol_mul(P P':Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => Pol_mult_cst P c'
  | PX P' i' c' => 
     (mkPX (Pol_mul P P') i' c0) + (Pol_mult_cst P c')
  end.

 Notation "P * P'" := (Pol_mul P P').

 Let Pol_zero_test(P:Pol):bool:=
   match P with
     |Pc c => (czero_test c)
     |PX _ _ _=> false
   end.

 Let Pol_of_pos(p:positive):Pol:= Pc (cof_pos p).

 (*P^n*)
Let Pol_pow':=
 fix Pol_pow'(P:Pol)(p:positive){struct p}:Pol:=
   match p with
     |xH => P
     |xO p' => let Q:=(Pol_pow' P p') in (Pol_mul Q Q)
     |xI p' => let Q:=(Pol_pow' P p') in (Pol_mul (Pol_mul Q Q) P)
   end.

 Let Pol_pow(P:Pol)(n:N):Pol :=
   match n with
     |N0 => P1
     |Npos p => Pol_pow' P p
   end.


   
  (*couple degree * coefdom for a polynomial in normal form *)
Let Pol_deg_coefdom:= 
fix Pol_deg_coefdom(A:Pol) : N*Coef :=
   match A with
     |Pc a => (N0,a)
     |PX P i p => let (d,c) := (Pol_deg_coefdom P) in (Nplus (Npos i) d, c)
   end.

Let Pol_deg :=
 fix Pol_deg(P:Pol):N:=
   match P with 
   |Pc _ => N0
   |PX P i _ => let d := Pol_deg P in (Nplus (Npos i) d)
 end.

Let Pol_dom :=
  fix Pol_dom(P:Pol):Coef:=
  match P with
   |Pc p => p
   |PX P _ _ => Pol_dom P
  end.
   
(*division:like an euclidian division, but if the division over coef
fails, returns None*)

Let Pol_div_cst :=
fix Pol1_div_cst(A:Pol)(q:Coef){struct A}: Pol:=
     match A with
       |Pc a => Pc (a // q)
       |PX P i p => PX (Pol1_div_cst P q) i (p // q)
     end.

Section POL1_EUCLIDE_AUX.

 Variable D : Pol.

 (*degee and leading coef of D*)
 Let dd_cd := Pol_deg_coefdom D.
 Let dd := fst dd_cd.
 Let cd := snd dd_cd.
     
  (*auxiliary division of RX^i by D.invariant : 
  -- deg R < deg D
  -- R <> 0
  -- D is not constant *)


Fixpoint Pol_div_aux(R : Pol)(i:positive){struct i}:Pol*Pol :=
     let (dr,cr) := (Pol_deg_coefdom R) in
       match (Ncompare (dr + (Npos i)) dd) with
	 |Lt => (Pc c0, PX R i c0)
	 | _  => 
	   match i with
	   | xH => (Pc (cr // cd), (mkPX R xH c0) - (Pol_mult_cst D (cr//cd)))
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
                     let rem := (mkPX R2 xH c0) - (Pol_mult_cst D (cr2//cd)) in
		     (quo,rem)
		   end
	   end
       end.
 

 End POL1_EUCLIDE_AUX.

(*straightforward division of polynomials with coef in Rat:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ +R and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ** non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + c1 and deg(c1)<deg(B)
  then AX+a=(BQ1)X^i + c1X^i +a and :
    - either deg (c1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = c1X^i + a
    - or deg (c1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb c1 i i.e. c1X^i = Q2B +R2
  ** poly returned are normalized as soon as args are normalized
  *)
 
 (*first division by a non constant polynomial*)
 Section POL1_EUCLIDE_PX.
   Variable B : Pol.
   Let dcb := Pol_deg_coefdom B.
   Let db := fst dcb.
   Let cb := snd dcb.


 Fixpoint Pol_euclide_div_PX (A :Pol):Pol*Pol :=
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




 End POL1_EUCLIDE_PX.


 (*general division function *)
 Let Pol_euclide_div(A B:Pol):Pol*Pol :=
   match B with
     |Pc q => (Pol_div_cst A q, Pc c0) 
     |_ => (Pol_euclide_div_PX B A)
   end.


 Let Pol_div(A B:Pol):Pol:= fst (Pol_euclide_div A B).


(*Pol1 is a coef_set*)


 Definition Pol1_is_coef_set :=
   mk_iring Pol P0 P1 Pol_add Pol_mul Pol_sub Pol_opp
   Pol_zero_test Pol_of_pos Pol_pow Pol_div.



  (*Derivative*)
Let Pol_deriv := 
 fix Pol1_deriv(P:Pol):Pol :=
   match P with
     |Pc c => Pc c0
     |PX A i a => match i with
		    |xH => A +(mkPX (Pol1_deriv A) xH c0)
		    |_ => (Pol_mult_cst (PX A (Ppred i) c0) (cof_pos i)) +
		      (mkPX (Pol1_deriv A) i c0)
		  end
   end.
   



  (*q to the n*(n+1)/2 *)
 Let sum_pow(q:Coef)(n:N):Coef :=
   match n with
     |N0 => c1
     |Npos p => 
       match p with
	 |xH => q
	 |xO p' => cpow q (Npos (Pmult p' (Psucc p)))
	 |xI p' => cpow q (Npos (Pmult (Psucc p') p))
       end
   end.


(*computation of the kth Pol1_subresultant coefficient*)
 Let Pol_subres_aux (j k:N)(q q':Coef): Coef:=
   let t := (Npred (Nminus j k)) in
    (sum_pow (-- c1) t)**(cpow (q // q') t)**q.
  

  (*next polynomial in the sequence,after ASRi_1 and SRj_1 and arguments
    for the possible next step of computations. if is nul, then B was
    the last poly of the sequence. SRj_1 is no nul*)
 


 Let Pol_next_subres(SRi_1 SRj_1:Pol)(srj:Coef)(i j:N):
   Pol * Coef * N * N :=
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next_SR := fun x:Coef =>
     -(Pol_div_cst 
       (snd (Pol_euclide_div (Pol_mult_cst SRi_1 x) SRj_1))
       (srj ** dom_sri_1)) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let srj_1 := dom_srj_1 in
	   (next_SR (cpow dom_srj_1 2), dom_srj_1, j, k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	   (next_SR (dom_srj_1 ** srk), srk, j, k)
     end.



 Let Pol_next_subres_triple(Ti_1 Tj_1:Pol*(Pol*Pol))(srj:Coef)(i j:N):
   (Pol*(Pol*Pol))* Coef * N * N :=
   let (SRi_1,Di_1) := Ti_1 in
   let (SRj_1,Dj_1) := Tj_1 in
   let (Ui_1,Vi_1) := Di_1 in
   let (Uj_1,Vj_1) := Dj_1 in
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next :=
     (fun x => 
       let (C,R) := (Pol_euclide_div (Pol_mult_cst SRi_1 x) SRj_1) in
       (C, Pol_div_cst R ((-- srj)**dom_sri_1)) ) in
   let next_UV :=
     (fun (x:Coef)(Pi_1 Pj_1 C:Pol) =>
       (Pol_div_cst
	 ((C * Pj_1) - (Pol_mult_cst Pi_1 x)) (srj**dom_sri_1))) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let y:= (cpow dom_srj_1 2) in
	 let (C,SR) := next y in
	   (SR, (next_UV y Ui_1 Uj_1 C, next_UV y Vi_1 Vj_1 C), dom_srj_1, j, k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	 let y:= (dom_srj_1 ** srk) in
	 let (C,SR) := next y in
	   (SR, (next_UV y Ui_1 Uj_1 C, next_UV y Vi_1 Vj_1 C), srk, j, k)
     end.


   (*builds the list, from A B n ensures termination and will be deg P + 1*)

Let Pol_subres_list1:=
 fix Pol1_subres_list1(A B:Pol)(q:Coef)(i j:N)(m:nat){struct m}:list Pol :=
   match m with
     |O => nil
     |S n => 
       let (next,l) := (Pol_next_subres A B q i j) in
       let (next',k) := next in
       let (SR, sr) := next' in
	 if (Pol_zero_test SR) then nil
	   else   SR :: (Pol1_subres_list1 B SR sr k l n)
   end.

 Let Pol_subres_list(A B:Pol) := 
   let p := Pol_deg A in
   let q := Pol_deg B in
   A :: B :: (Pol_subres_list1 A B c1 (p+1) p  (S (nat_of_N p))). 


 Definition Pol_subres_coef_list(A B:Pol):=
   let dom := (fun x => Pol_dom x) in
   let res := Pol_subres_list A B in
     map dom res.


Let Pol_ext_signed_subres_list :=
 fix Pol1_ext_signed_subres_list(T T':Pol*(Pol*Pol))(q:Coef)(i j:N)(m:nat)
   {struct m}:list (Pol*(Pol*Pol)) :=
   let (B,D):= T' in
     if (Pol_zero_test B) then nil
       else
	 match m with
	   |O => nil
	   |S n => 
	     let (next,l) := (Pol_next_subres_triple T T' q i j) in
             let (next',k) := next in
	     let (next_T, sr) := next' in
	     let (next_SR,_) := next_T in
     	       next_T :: (Pol1_ext_signed_subres_list T' next_T sr k l n)
	 end.



	 
 Section SUBRES_CHAIN.
   Variable P Q :Pol.
   Let ddp := Pol_deg_coefdom P.
   Let ddq := Pol_deg_coefdom Q.
   Let deg_p := fst ddp.
   Let deg_q := fst ddq.
   Let dom_p := snd ddp.
   Let dom_q := snd ddq.

  (*first polynomials in the subresultant chain
   
   Definition Pol1_subres_chain_init :=
     match (Rat_sign dom_p) with
       |Eq => (Pc R0, R0, Pc R0) must never happen!
       |Gt => (P, R1, Q)
       |Lt => match (Npred (Nminus deg_p deg_q)) with
		    |N0 => (P, - R1, Q) 
		    |Npos p => match p with
				 |xO _ => (P, (- R1), Q) 
				 |_ => (-- P, R1, (-- Q))
			       end
		  end
     end.
   

   Let SRq := snd subres_chain_init.
   Let SRp := fst (fst subres_chain_init).
   Let srp := snd (fst subres_chain_init).
   *)

   Definition Up := Pc c1.
   Definition Uq := Pc c0.
   Definition Vp := Pc c0.
   Definition Vq := Pc c1.

   Definition Tp := (P, (Up, Vp)).
   Definition Tq := (Q, (Uq, Vq)).
   
 
   (* extended signed subres chain *)
   Definition Pol1_ext_signed_subres_chain : list (Pol*(Pol*Pol)) :=
     Tp :: (Tq :: 
    (Pol_ext_signed_subres_list
      Tp Tq  c1 deg_p (Npred deg_p) (S (nat_of_N deg_p)))).
     
       


 End SUBRES_CHAIN.
 


   (*gcd of P and Q : last subresultant dP>dQ*)
 Definition Pol1_gcd_strict (P Q:Pol1) :=
   let l := (Pol1_subres_list P Q) in 
   let SRj := (last_elem l Q) in
   let (_, srj) := Pol1_deg_coefdom SRj in
   let (_, cP) := Pol1_deg_coefdom P in
     Pol1_div_cst (Pol1_mult_cst SRj cP) srj.
    

 Definition Pol1_gcd(P Q:Pol1) :=
   let (dP,cP):= Pol1_deg_coefdom P in
   let (dQ,cQ) := Pol1_deg_coefdom Q in
     match Ncompare dP dQ with
       |Lt  => Pol1_gcd_strict Q P
       |Gt  => Pol1_gcd_strict P Q
       |Eq => Pol1_gcd_strict P ((Pol1_mult_cst Q cP) - (Pol1_mult_cst P cQ))
     end.

  (*gcd of P and Q, and gcd free part of P with respect to Q, pourZ,
ca rajoute des contenus dans les DEUX
 Definition gcd_gcd_free (P Q:Pol1) :=
   let (_, cP) := deg_coefdom P in
   let (Tj, Tj_1):= two_last_elems (ext_signed_subres_chain P Q) 
     ((Pc R0, (Pc R0,Pc R0)),(Pc R0, (Pc R0,Pc R0))) in
   let (SRj,Dj) := Tj in
   let (_, srj) := deg_coefdom SRj in
   let (_,Dj_1) := Tj_1 in
   let (_, Vj_1) := Dj_1 in
   let (_, cVj_1) := deg_coefdom Vj_1 in 
     (div_cst (mult_cst SRj cP) srj, (div_cst (mult_cst Vj_1 cP) cVj_1)).
*)    

(*WARNING we have NOT gcd*(gcd_free)=P but up to a constant
returns, gcd, gcd_free of P, gcd_free of Q*)
 Definition Pol1_gcd_gcd_free_strict (P Q:Pol1) :=
   let (_, cP) := Pol1_deg_coefdom P in
   let (Tj, Tj_1):= two_last_elems (Pol1_ext_signed_subres_chain P Q) 
     ((Pc c0, (Pc c0,Pc c0)),(Pc c0, (Pc c0,Pc c0))) in
   let (SRj,Dj) := Tj in
   let (_, srj) := Pol1_deg_coefdom SRj in
   let (_,Dj_1) := Tj_1 in
   let (Uj_1, Vj_1) := Dj_1 in
   let (_,cVj_1) := Pol1_deg_coefdom Vj_1 in
   let (_,cUj_1) := Pol1_deg_coefdom Uj_1 in
     (Pol1_div_cst (Pol1_mult_cst SRj cP) srj,
       Pol1_div_cst (Pol1_mult_cst Vj_1 cP) cVj_1,
       Pol1_div_cst (Pol1_mult_cst Uj_1 cP) cUj_1).


(*TODO virer les contenus constants?*)


  (*gcd of P and Q : last subresultant, one preliminary step for
 polys of same deg*)
 Definition Pol1_gcd_gcd_free (P Q:Pol1) :=
   let (dQ,cQ):= Pol1_deg_coefdom Q in
   let (dP,cP):= Pol1_deg_coefdom P in
     match (Ncompare dP dQ) with
       |Eq => 
	 let Next := (Pol1_mult_cst Q cP) - (Pol1_mult_cst P cQ) in
	 let (GCD_Q',Next'):= Pol1_gcd_gcd_free_strict Q Next in
	 let (GCD,Q'):= GCD_Q' in
	 let (_,cGCD) := Pol1_deg_coefdom GCD in
	 let (_,cQ') := Pol1_deg_coefdom Q' in
	 let (_,cNext') := Pol1_deg_coefdom Next' in
	 let (_,cNext) := Pol1_deg_coefdom Next in
	   (GCD,
	     (Pol1_mult_cst Q' ((cGCD**cNext'**cP)//cNext)) -
	     (Pol1_mult_cst Next' ((cGCD**cQ')//cQ)),
	     Q')
       |Gt  => Pol1_gcd_gcd_free_strict P Q
       |Lt  => Pol1_gcd_gcd_free_strict Q P
     end.
    

 Definition Pol1_square_free(P:Pol1) := snd (fst (Pol1_gcd_gcd_free P (Pol1_deriv P))).




  (* evaluation of a Pol1 at an element of C *)
 Fixpoint Pol1_eval(P:Pol1)(x:C){struct P} : C :=
   match P with
     |Pc c =>  c
     |PX A i a => ((Pol1_eval A x)**(Cpow coef x (Npos i))) ++ a
   end.
   

(*operators for polys with more than 2 variables *)



Section  IS_BASE_CST.
 Variable Op: C -> bool. (* should be is_base_cst at level n *)

(* is base cst at level n+1 *)
 Definition  Poln_is_base_cst(P:Pol1):=
 match P with
 |Pc c => Op c
 |PX Q i c => false
 end.

 End IS_BASE_CST.


Section TRUNC. 
  Variable Op:C -> bool. (* shoul be is_base_cst at leve n+1 *)

  Fixpoint Poln_trunc(P:Pol1):list Pol1 :=
    match P with
    |Pc c =>
    if (Op c) then (P :: nil) else (P :: (Pc c0) :: nil)
    |PX Q i c => map (fun x => (mkPX  x i c)) (Poln_trunc Q)
    end.

End TRUNC.

Section MK_PC.
  Variable C_base : Set.
  Variable Op:C_base-> C.

  Definition Poln_mkPc(c:C_base):= Pc (Op c).
End MK_PC. 


Section OP_BASE_CST.
  Variable C_base : Set.
  Variable Op:C -> C_base-> C.

  Fixpoint Poln_op_base_cst(P:Pol1)(c:C_base){struct P}:Pol1:=
    match P with
    |Pc p => Pc (Op p c)
    |PX Q i q => mkPX (Poln_op_base_cst Q c) i (Op q c)
    end.


End OP_BASE_CST.


Section PART_EVAL.
   Variable C_base :Set.
   Variable C_base_pow : C_base -> N -> C_base.
   Variable mult_cst : C -> C_base -> C.

    Fixpoint partial_eval(P:Pol1)(c:C_base){struct P}:C:=
    match P with
    |Pc p => p
    |PX Q i q =>
    (mult_cst (partial_eval Q c) (C_base_pow c (Npos i)))++q
    end.

End PART_EVAL.







