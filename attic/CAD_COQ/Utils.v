(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)

Unset Boxed Definitions.
Unset Boxed Values.


Require Import ZArith.
Require Export NArith.
Require Export Mylist.

Set Implicit Arguments.



    (************************************************************)
    (********                    Misc.                  *********)  
    (************************************************************)

(* some lemmas over Z *)
Lemma absurdIplusJ : forall i j: positive , (i = j + i ) %positive -> False.
intros;assert ((Zpos i) = (Zpos j + Zpos i)%Z).
rewrite <- Zpos_plus_distr;rewrite <- H;auto.
assert (Zpos j > 0)%Z;[red;auto|omega].
Qed.


Lemma ZPminus_spec : forall x y,
  match ZPminus x y with
  | Z0 => x = y
  | Zpos k => x = (y + k)%positive
  | Zneg k => y = (x + k)%positive
  end.
 Proof.
  induction x;destruct y.
  replace (ZPminus (xI x) (xI y)) with (Zdouble (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble;rewrite 
H;trivial.
  replace (ZPminus (xI x) (xO y)) with (Zdouble_plus_one (ZPminus x 
y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold 
Zdouble_plus_one;rewrite H;trivial.
  apply Pplus_xI_double_minus_one.
  simpl;trivial.
  replace (ZPminus (xO x) (xI y)) with (Zdouble_minus_one (ZPminus x 
y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold 
Zdouble_minus_one;rewrite H;trivial.
  apply Pplus_xI_double_minus_one.
  replace (ZPminus (xO x) (xO y)) with (Zdouble (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble;rewrite 
H;trivial.
  replace (ZPminus (xO x) xH) with (Zpos (Pdouble_minus_one x));trivial.
  rewrite <- Pplus_one_succ_l.
  rewrite Psucc_o_double_minus_one_eq_xO;trivial.
  replace (ZPminus xH (xI y)) with (Zneg (xO y));trivial.
  replace (ZPminus xH (xO y)) with (Zneg (Pdouble_minus_one y));trivial.
  rewrite <- Pplus_one_succ_l.
  rewrite Psucc_o_double_minus_one_eq_xO;trivial.
  simpl;trivial.
 Qed.


Lemma ZPminus0: forall p, ZPminus p p = Z0.
induction p;simpl;auto;rewrite IHp;auto.
Qed.

Lemma ZPminusneg: forall p q , ZPminus p (p + q) = Zneg q.
intros;generalize (ZPminus_spec p (p+q));destruct (ZPminus p (p+q));intro.
generalize (@absurdIplusJ p q);intro h;elim h;auto.
rewrite Pplus_comm;auto.
generalize (@absurdIplusJ p ( q + p0));intro h;elim h ;auto.
rewrite <- (Pplus_comm p);rewrite Pplus_assoc;trivial.
assert (p0 = q);[apply (Pplus_reg_l p)|subst];auto.
Qed.

Lemma ZPminuspos: forall p q , ZPminus (p + q)  p= Zpos q.
intros;generalize (ZPminus_spec (p+q) p);destruct (ZPminus  (p+q) p);intro.
generalize (@absurdIplusJ p  q);intro h;elim h ;auto.
apply sym_equal;rewrite Pplus_comm;assumption.
assert (p0 = q);[apply (Pplus_reg_l p)|subst];auto.
generalize (@absurdIplusJ p ( q + p0));intro h;elim h ;auto.
rewrite <- (Pplus_comm p);rewrite Pplus_assoc;trivial.
Qed.





(** Operations over N*)

 Definition Npred(n :N):N :=
   match n with
     |N0 => N0
     |Npos p => match p with
		  |xH => N0
		  |_ => Npos (Ppred p)
		end
   end.


 Definition Nminus(n m:N):N :=
   match n, m with
     |N0, _ => N0
     |_, N0 => n
     |Npos p, Npos q =>  match Pminus_mask p q with
			   |IsNeg => N0
			   |IsNul => N0
			   |IsPos p => Npos p
			 end
     end.

 Definition nat_of_N(n:N):nat:=
   match n with
     N0 => O
     |Npos p => nat_of_P p
   end.




Definition N_of_nat(n:nat):N:=
match n with
|O => N0
|S n => Npos (P_of_succ_nat n)
end.


(** Some operations over lists, o be moved in Mylist? *)

  (*last element of a list *)
 Fixpoint last_elem(A:Set)(l:list A)(bottom:A){struct l}:A:=
   match l with
     |nil => bottom
     |a::q =>
       match q with
	 |nil => a
	 |_ => last_elem q bottom
       end
   end.

 Implicit Arguments last_elem [A].

 Fixpoint two_last_elems(A:Set)(l:list A)(bottom:A*A){struct l}:A*A :=
   match l with
     |nil => bottom
     |a::q => 
       match q with
		|nil => bottom
		|b::q' =>
		  match q' with
		    |nil => (a,b)
		    |_ => two_last_elems q bottom
		  end
       end
   end.

 Implicit Arguments two_last_elems [A].


 Fixpoint flat_map_ac(A B:Set)(f:A -> (list B))(l:list A)(res:list B){struct l}:list B:=
   match l with
     |nil => res
     |a::l' => flat_map_ac f l' ((f a)@res)
   end.

 Definition flat_map(A B:Set)(f:A -> (list B))(l:list A):= flat_map_ac f l nil.



(** Counting he number of sign changes in a list of option comp *)

Fixpoint sign_changes_rec(sign:comparison)(l:list comparison)
  {struct l}:nat:=
  match l with
    |nil => 0
    |a :: l' =>
      match sign, a with
	|Eq, _ => sign_changes_rec a l'
	|_, Eq => sign_changes_rec sign l'
	|Lt, Gt => S (sign_changes_rec Gt l')
	|Gt, Lt => S (sign_changes_rec Lt l')
	|_,_ => sign_changes_rec a l'
      end
  end.

Definition sign_changes(l : list comparison) : nat := 
  match l with
    |nil => O
    |a ::l' => sign_changes_rec a l'
  end.



Fixpoint op_sign_changes_rec(sign:(option comparison))(l:list (option comparison))
  {struct l}:option nat:=
  match l with
    |nil => Some 0
    |a :: l' =>
      match sign, a with
	|_, None => None
	|None, _ => None
	|Some Eq, _ => op_sign_changes_rec a l'
	|_, Some Eq => op_sign_changes_rec sign l'
	|Some Lt, Some Gt =>
	  let res := op_sign_changes_rec (Some Gt) l' in
	    match res with
	      |None => None
	      |Some r => Some (S r)
	    end
	|Some Gt, Some Lt =>
	  let res := op_sign_changes_rec (Some Lt) l' in
	    match res with
	      |None => None
	      |Some r => Some (S r)
	    end
	|_,_ => op_sign_changes_rec a l'
      end
  end.




Definition op_sign_changes(l:list (option comparison)) : (option nat) :=
  match l with
    |nil => Some O
    |a :: l'=> op_sign_changes_rec a l'
  end.
     
Definition sign_mult( u v:(option comparison)):=
   match u, v with
    |None,_ => None
    | _, None => None
    |Some u, Some v =>
	match u, v with
	 |Eq, _ =>Some Eq
    	|_, Eq => Some Eq
    	|Lt, Lt => Some Gt
    	|Lt, Gt => Some Lt
    	|Gt, Lt => Some Lt
    	|Gt, Gt => Some Gt
	end
end.



(** convenient uples in Set*)

Inductive triple(A B C :Set):Set:=
|Tr:forall a:A,forall b:B, forall c:C, triple A B C.

Definition fst3(A B C:Set)(u:triple A B C):=
  match  u with
  |Tr a _ _ => a
end.


Inductive uple4(A B C D:Set):Set:=
|Four:forall a:A, forall b:B, forall c:C, forall d:D, uple4 A B C D.

Definition fst4(A B C D:Set)(u:uple4 A B C D):=
  match  u with
  |Four a _ _ _ => a
end.


Inductive uple5(A B C D E:Set):Set:=
  |Five:
    forall a:A, forall b:B, forall c:C, forall d:D, forall e:E,
      uple5 A B C D E.

Definition fst5(A B C D E:Set)(u:uple5 A B C D E):=
  match  u with
    |Five a _  _ _ _ => a
  end.


Inductive uple6(A B C D E F:Set):Set:=
  |Six:
    forall a:A, forall b:B, forall c:C, forall d:D, forall e:E, forall f:F,
      uple6 A B C D E F.

Definition fst6(A B C D E F:Set)(u:uple6 A B C D E F):=
  match  u with
    |Six a _  _ _ _ _ => a
  end.


Fixpoint clean_head(A:Set)
(Aeq:A -> A -> bool)(a:A)(l:list A){struct l}:list A:=
match l return list A with
|nil => (a::nil)
|hd::tl =>
  if (Aeq a hd)
    then clean_head Aeq a tl
    else hd :: (clean_head Aeq a tl)
end.



Fixpoint clean_list(A:Set)(Aeq:A->A->bool)(l:list A){struct l}:list A:=
match l return (list A) with
|nil => nil
|a :: tl =>clean_head Aeq a (@clean_list A Aeq tl)
end.

Fixpoint eqn(n m:nat){struct n}:bool:=
match n,m with
|O, O => true
|S n, S m => eqn n m
|_, _ => false
end.

(** Iterator for update in the CAD tree construction *)

Fixpoint two_fold(A B C:Set)
  (f: A -> B  -> (A*C))(a:A)(l:list B){struct l}: A * (list C):=
  match l with
    |nil => (a, (@nil C))
    |b::l1 =>
      let (a1, c1) := f a b  in
      let (a2, l2) := two_fold f a1 l1 in
	(a2, (c1::l2))
  end.

(*
Fixpoint two_fold(A B C D:Set)
  (f: A -> B -> C -> triple A B D)(a:A)(l:list (B*C))
  {struct l}: A * (list (B*D)):=
  match l with
    |nil => (a, nil)
    |head::l1 =>
      let (b,c):=head in
      let (a1, b1 ,d1 ) := f a b c in
      let (a2, l2) := two_fold f a1 l1 in
	(a2, ((b1,d1)::l2))
  end.
*)
(*

Fixpoint two_fold(A B C D:Set)
  (f: A -> B -> C -> triple A B D)(a:A)(b:B)(l:list C)
  {struct l}:triple A B (list D):=
  match l with
    |nil => Tr a b nil
    |c::l1 =>
      let (a1, b1, d1) := f a b c in
      let (a2, b2, l2) := two_fold f a1 b1 l1 in
	Tr a2 b2 (d1::l2)
  end.
*)


