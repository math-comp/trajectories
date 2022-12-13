
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)


(* WARNING : Not to be compiled!!!

This defines the bernstein manipulations and the datatypes for
  information retained in the computations given
 
Coef : Set.
Rat : Set
cInfo :Set.
cell_point : Set.

Pol := Pol1 Coef
*)





 (************************************************************)
 (* Informations about a Pol to be computed once and for all *)
 (************************************************************)


 (* Info is P Pbar dPbarlowsign signinfo
  where Pbar is the square free part of P,
  dPbar is the degree of Pbar (for later bern computations)
  lowsign the sign of P in -inf
  signinfo is the sign of P if it is known to be constant,
  and None else *)

 (* Definition Info := uple5 Pol Pol N Sign Sign.*)
 Definition Info := build_Info Coef.

  Definition mk_Info(P Q:Pol)(n:N)(low sign_info:Sign):= 
    Five  P Q n low sign_info. 

  Definition Pol_of_Info(c:Info):= fst5 c.


 (************************************************************)
 (***            Bernstein toolkit for root isolation       **)
 (************************************************************)




 (** Auxiliary  functions **)    
     
 Definition Ptranslate:=
   fix Ptranslate(P:Pol)(c: Rat){struct P}:Pol:=
     match P with
       |Pc p => P
       |PX P' i p' => 
	 let Q := Ptranslate P' c in 
	   (Q * (Pol_pow (X + (Pol_mkPc c))  (Npos i))) + (Pc p')
       end.
 

  (*P(cX)*)
 Definition dilat := 
   fix dilat(P:Pol)(c:Rat){struct P}:Pol:=
     match P with
       |Pc _ => P
       |PX P' i p => PX (Pol_mult_base_cst  (dilat P' c) (rpow c (Npos i))) i p
     end.
     
  (* X^d * P(1/X) where deg(P)=d, ie "reverse" of the polynomial *) 
 Definition Rev1:= fix Rev1 (Q P:Pol)(i:positive){struct P}:Pol:=
   match P with
     |Pc c => mkPX Q i c
     |PX P' j p => Rev1 (mkPX Q i p) P' j
   end.
     
 Definition Rev(P:Pol):=
   match P with
     |Pc c => Pc c
     |PX P' i p' => Rev1 (Pc p') P' i 
   end.
     
     
     
  (*adds i times the rational r in head of the Rat list l*)
 Definition repeat_add:= fix repeat_add(r:Coef)(i:positive)(l:list Coef){struct i}:
   list Coef :=
   match i with
     |xH => r::l
     |xO p => repeat_add r p (repeat_add r p l)
     |xI p => r::(repeat_add r p (repeat_add r p l))
   end.
     

  (*list of coef of a Poly of degree <= p, over 1, X,..., X^p, with
      all zeros, constant in head, *)

 Definition Pol_to_list_dense:= fix Pol_to_list_dense(P:Pol)(p:N){struct P}:list Coef:=
   match P with
     |Pc c =>
       match p with
	 |N0 => c::nil
	 |Npos p' => c::(repeat_add c0 p' nil)
       end
     |PX Q i q =>
       match i with
	 |xH => q::(Pol_to_list_dense Q (Npred p))
	 |_ => q :: (repeat_add c0 (Ppred i) (Pol_to_list_dense Q
	   (Nminus p (Npos i))))
       end
   end.
     

 (**divides list of coefs by the relevant binomial coefs to get the bern list*)
 Definition binomial_div:=
   fix binomial_div (l:list Coef)(p:N)(i:N){struct l}:
     list Coef:=
     match l with
       |nil => nil
       |h::t => 
	 (cdiv_base_cst h (rbinomial p i))::
	 (binomial_div t p (Npred i))
     end.
     

  (*  coefs of P in the Bernstein basis over c,d,p from b_p to b_0 if 
	p is the degree of P 
  builds the list of info pol, no infomation about constant sign is assumed *)
 Definition Pol_bern_coefs(P:Pol)(c d:Rat)(p:N):=
   let Q := (Ptranslate (Rev (dilat (Ptranslate P c) (rsub d  c)))  r1) in
     let list_coef := Pol_to_list_dense Q p in
       map (cInfo_of_Pol None) (binomial_div list_coef p p).
    


 (* bern coefs after split of the interval    
   input : list of bernstein coefs for P of deg <= p in the bern basis
	  p over c,d. and a rational e
      
	output : list of bernstein coefs for P of deg <= p in the bern basis
	p over c,e 
	and
	  list of bernstein coefs for P of deg <= p in the bern basis
	p over e,d
	*)

  (* computation of the next diag in the "Pascal triangle" of the
	  Bernstein relation *)
 Definition next_diag_bern(c d e:Rat):=
   let alpha := rdiv (rsub d e) (rsub d c) in
   let beta := rdiv (rsub e c) (rsub d c) in
     fix next_diag_bern(diag:list Coef)(b:Coef){struct diag}:
       list Coef:=
       match diag with
	 |nil => b::nil
	 |hd :: tl => 
	   let l:=next_diag_bern tl b in
	     match l with
	       |nil => nil (*should never happen*)
	       |rhd::rtl =>
		 ((hd **  (cof_Rat alpha))
		   ++ (rhd ** (cof_Rat beta)))
		 ::l
	     end
       end.


 Definition bern_split1(c d e:Rat):=
   fix bern_split1(bern_coef b' b'':list Coef){struct bern_coef}
     :(list Coef)*(list Coef):=
     match bern_coef with
       |nil  => (b',b'')
       |hd::tl => 
	 let next_b'':= next_diag_bern c d e b'' hd in
	   match next_b'' with
	     |nil => (nil,nil) (*should never happen*)
	     |hd''::tl'' => bern_split1 tl (hd''::b') next_b''
	   end
     end.

 (** computes the list of cPol_info for the bern coefs **)
 Definition Pol_bern_split(bern_coef_info:list cInfo)(c d e:Rat):=
   let bern_coef := map cPol_of_Info bern_coef_info in
   let (b',b''):= bern_split1 c d e (rev bern_coef) nil nil in 
     (map (cInfo_of_Pol None) b', map (cInfo_of_Pol None) (rev b'')).

