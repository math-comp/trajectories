Require Import (*QArith*) ZArith Zwf Lia.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun order.
From mathcomp Require Import bigop fingroup choice ssralg ssrnum rat poly.
Require Export (*infra*) pol.

Import GroupScope.
Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Set Printing Width 50.

(******************************************************************************)
(* We want to prove a simple and contructive approximation of the
 intermediate value theorem: if a polynomial is negative in a and positive in b,
 and a < b, then for any positive epsilon, there exists c and d, so that
 a <= c < d <= b, the polynomial is negative in c and positive and d,
 and the variation between c and d is less than epsilon.  To prove this,
 we use a second polynomial, obtained by taking the the absolute value
 of each coefficient.
*)
(******************************************************************************)

Fixpoint abs_pol (l:list rat) :list rat :=
 match l with nil => nil | a::tl => `|a| :: abs_pol tl end.

(* Theorem binding the slope between two points inside an interval. *)
(*Lemma cm2 (l : {poly rat}) b :
  { c | forall x, 0 <= x -> x <= b -> `|l.[x] - l.[0]| <= c * x}.
Proof.
(*set al := \poly_(i < size l) `|l`_i|.
exists al.[b] => x x0 xb.
rewrite horner_poly horner_coef0 horner_coef.
have [/size0nil ->|] := eqVneq (size l) 0%N.
  by rewrite !big_ord0/= normr0 mul0r.
rewrite -lt0n => l0.
rewrite -[in leLHS](prednK l0).
rewrite big_ord_recl/= expr0 mulr1 addrAC subrr add0r.
rewrite /bump.
under eq_bigr do rewrite leq0n/= add1n.
rewrite big_distrl/=.
rewrite (le_trans (ler_norm_sum _ _ _))//.
under eq_bigr do rewrite normrM.
rewrite -[in leRHS](prednK l0).
rewrite big_ord_recl/= expr0 /bump.
under [in leRHS]eq_bigr do rewrite leq0n/= add1n.
rewrite mulr1.
rewrite ler_paddl// ?mulr_ge0//.
apply: ler_sum => j _.
rewrite -mulrA.
rewrite ler_pmul//.
rewrite ger0_norm//; last first.
  by rewrite exprn_ge0.
rewrite (@le_trans _ _ (b ^+ j.+1))//.
by rewrite ler_pexpn2r// nnegrE// (le_trans x0).*)
(*move=> l b; case: l =>[| a l].
- by exists 0; move=> /= x; rewrite mul0r oppr0 addr0 normr0 lexx.
- exists (eval_pol (abs_pol l) b) => x px xb /=; rewrite mul0r addr0.
  rewrite addrC addKr normrM ger0_norm // mulrC ler_wpM2r//.
(* NB(rei): ler_absr_eval_pol? *)
(*  rewrite (le_trans (ler_absr_eval_pol _ _)) //.
  by rewrite eval_pol_abs_pol_increase // ger0_abs.
Qed.*) (*TODO*)*) Admitted. *)

(* Cannot be abstracted since not every ordered ring has a floor ring *)
(*
TODO?
Lemma QZ_bound : forall x:Q, (0 <= x)%Q -> {n : Z | x <= n#1}%Q.
intros [n d]; exists(Zdiv n (Zpos d)+1)%Z.
assert (dpos : (('d) > 0)%Z) by apply (refl_equal Gt).
unfold Qle; simpl; rewrite Zmult_1_r; rewrite Zmult_plus_distr_l.
rewrite Zmult_1_l {1}(Z_div_mod_eq n ('d)) //.
rewrite (Zmult_comm ('d)); apply Zplus_le_compat; auto with zarith.
destruct (Z_mod_lt n ('d)) as [_ H2]; auto.
by apply Zlt_le_weak.
Defined.
*)

(* We will look at n points regularly placed between a and b,  a satisfies
  a property P and b does not, we want to find the first point among the
  n points that satisfies P and has a neighbour that does not. *)
Definition find_pair : forall A:eqType, forall P:A->bool, forall Q:A->A->Prop,
    forall l:seq A, forall a b:A, P a -> ~P b ->
    (forall l1 l2 x y, a::l ++ b::nil= l1 ++ x :: y :: l2 -> Q x y) ->
    {c :A & { d | Q c d /\ P c /\ ~P d}}.
Proof.
move => A P Q l; elim: l => [ | a l IHl] a' b' Pa Pb connect.
  by exists a'; exists b'; split => //; apply: (connect [::] [::]).
case Pa1: (P a).
  have tmp :
     forall l1 l2 x y,  a :: l ++ [:: b' ]= l1 ++ [::x, y & l2] -> Q x y.
    by move => l1 l2 x y q; apply: (connect (a'::l1) l2); rewrite /= q.
  by move: (IHl a b' Pa1 Pb tmp) => [c [d [cd Pc]]]; exists c; exists d.
exists a'; exists a; split; first by apply (connect nil (l++b'::nil)).
by rewrite Pa1.
Qed.

Fixpoint nat_ns (p : Z)(n : nat) :=
  match n with
    |0 => [:: p]
    |m.+1 => (p - (Z_of_nat m.+1))%Z :: nat_ns p m
  end.

Definition ns p n :=
  match n with
    |Zpos q => nat_ns p (nat_of_P q)
    |_ => [:: p]
  end.

Lemma ltb_Zneg0 x : (Zneg x < 0)%Z. Proof. by []. Qed.

Lemma leb_Zneg0N x : ~ (0 <= Zneg x)%Z. Proof. exact/Z.lt_nge/ltb_Zneg0. Qed.

Lemma nat_ns_head : forall (p : Z) n,
  exists l, nat_ns p n = (p - (Z_of_nat n))%Z :: l.
Proof.
move=> p; elim=>[|n [l Ih]] /=.
  exists [::].
  by rewrite Z.sub_0_r.
by rewrite Ih; exists [:: (p - Z_of_nat n)%Z & l].
Qed.

Local Open Scope Z_scope.

Lemma ns_head :  forall p n :Z, (0 <= n) -> exists l, ns p n = (p - n) :: l.
Proof.
move=> p [|n|n] /=; last 1 first.
- by move/leb_Zneg0N.
- exists [::].
  by rewrite Z.sub_0_r.
- move=> _; set m := nat_of_P n; case: (nat_ns_head p m)=> l' ->; exists l'.
  by rewrite /m Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Lemma nat_ns_step : forall p n, forall l1 l2 x y,
  nat_ns p n = l1 ++ [:: x, y & l2] -> y = x + 1.
Proof.
move=> p; elim=> [|n Ihn] l1 l2 x y /=.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
case: l1 => [|u l3] /=; last by case=> _; move/Ihn.
case=> <-; case: (nat_ns_head p n)=> [l' ->]; case=> <- _.
rewrite Zpos_P_of_succ_nat.
rewrite /Z.succ /=.
ring.
Qed.

Lemma ns_step : forall p n, forall l1 l2 x y, 0 <= n ->
  ns p n = l1 ++ [:: x, y & l2] -> y = x + 1.
Proof.
move=> p [|n|n] /=; last 1 first.
- by move=> ? ? ? ? /leb_Zneg0N.
- move=> ? ? ? ? ?.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- move=> l1 l2 x y _; exact: nat_ns_step.
Qed.

Lemma nat_ns_tail : forall p n, exists l, nat_ns p n = l ++ [:: p].
Proof.
move=> p; elim=> [|n [l' Ihn]] /=.
- by exists [::]; rewrite cat0s.
- rewrite Ihn.
  eexists.
  rewrite -cat_cons.
  reflexivity.
Qed.

Lemma ns_tail : forall p n, exists l, ns p n = l ++ p ::nil.
Proof.
move=> p [|n|n] /=.
- by exists [::]; rewrite cat0s.
- by case: (nat_ns_tail p (nat_of_P n))=> l' ->; exists l'.
- by exists [::]; rewrite cat0s.
Qed.

Local Close Scope Z_scope.

(* Lemmas about minus are missing in xssralg .. .*)
(* TODO

Lemma nat_ns_bounds : forall p n x l1 l2, nat_ns p n = l1 ++ [:: x & l2] -> 
        (p - Z_of_nat n <= x)%Z && (x <= p).
Proof.
move=> p; elim=> [|n Ihn] x l1 l2 /= h.
- rewrite oppr0 addr0. 
  suff exp : p = x by rewrite exp lerr.
  case: l1 h => /=; first by case.
  move=> z s.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP;
      rewrite eqSS.
- case: l1 h => [| u l1] /=.
  + by set sn := (' _)%Z; case=> h _; rewrite -h lerr lter_addlr /= oppr_lte0.
  + case=> _; move/Ihn; case/andP=> h1 h2; rewrite h2 andbT; apply: ler_trans h1.
    rewrite lter_add2r /= -lter_opp2 /= Zpos_P_of_succ_nat /Zsucc.
    by rewrite -[Zplus _ _]/(Z_of_nat n + 1) lter_addrr /= ler01.
Qed.

Lemma ns_bounds : forall p n x l1 l2, 0 <= n -> ns p n = l1 ++ x::l2 -> 
        (p - n <= x) && ( x <= p).
Proof.
move=> p [| n | n] x l1 l2 /=.
- move=> _ h; rewrite oppr0 addr0.
  suff exp : p = x by rewrite exp lerr.
  case: l1 h => /=; first by case.
  move=> z s.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- by move=> _; move/nat_ns_bounds; rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
- by rewrite leb_Zneg0N.
Qed. 

Lemma map_contiguous :
forall (A B : Type)(f : A -> B) l l1 l2 a b,
  map f l = l1 ++ [:: a, b & l2] ->
  {l'1 : seq A & 
    {l'2 : seq A & 
      {x : A & 
        {y : A | [/\ l1 = map f l'1, l2= map f l'2, a = f x,
          b = f y & l = l'1 ++ [:: x, y & l'2]]}}}}.
Proof.
intros A B f; elim=> [|x l Ihl] /= l1 l2 a b h; first by case: l1 h.
case: l Ihl h => [|a' l'] /= h.
- by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- case: l1 h => [|a1 l1] /= h.
    by case=> <- <- <-; exists [::]; exists l'; exists x; exists a' => /=.
  case=> e1; move/h => [l1' [l2' [x' [y' [h1 h2 h3 h4 h5]]]]].
  exists [:: x & l1']; rewrite /= -h1 h2 e1; exists l2'; exists x'; exists y'.
  by split=> //; rewrite h5.
Qed.

(*This is map_cat.
Lemma map_app :
  forall A B:Type, forall f : A -> B, forall l1 l2, map f (l1++l2) = map f l1 ++ map f l2.
intros A B f l1; induction l1; simpl; auto.
intros l2; rewrite IHl1; auto.
Qed.
*)


Lemma non_empty_tail : 
  forall (A : Type) (a : A) l, exists l', exists b, [:: a & l] = l' ++ [::b].
Proof.
move=> A a l; elim: l a => [| x l  Ihl] a.
- by exists [::]; exists a.
- case: (Ihl x)=> s [b Ihb]; rewrite Ihb; exists [:: a & s]; exists b.
  by rewrite cat_cons.
Qed.

(* wait and see ...
Lemma Qfrac_add_Z_l : forall a b c,
  (a # 1) + (b # c)%Q = ( a * ' c + b # c)%Q :> Qcb.
intros;unfold Qeq; simpl; ring.
Qed.
*)

Lemma leb_Z : forall x y:Z, x <= y -> Qcb_make x <= Qcb_make y.
Proof. 
move => x y xy; apply/QcblebP; rewrite /qcb_val /Qcb_make /Qle /Qnum /Qden.
by rewrite 2!Zmult_1_r; apply/Zle_is_le_bool.
Qed.

Lemma leb_0_Z : forall y, 0%Z <= y -> 0 <= Qcb_make y.
Proof. by move => y yp; apply: leb_Z. Qed.

Lemma ltb_Z : forall x y:Z, x < y -> Qcb_make x < Qcb_make y.
Proof. 
  move => x y xy. apply/QcblebP; rewrite /qcb_val /Qcb_make /Qle /Qnum /Qden.
rewrite 2!Zmult_1_r; move/Zle_is_le_bool; rewrite -[Zle_bool y x]/(y <= x).
by rewrite ler_nlt xy.
Qed.

Lemma ltb_0_Z : forall y, 0%Z < y -> 0 < Qcb_make y.
Proof. by move => y yp; apply: ltb_Z. Qed.

Lemma Qcb_make_add :
  forall x y, Qcb_make (x + y) == Qcb_make x + Qcb_make y.
move => x y; apply/Qcb_QeqP.
by rewrite  -[(Qcb_make _ + _)%R]/(Q2Qcb(Qplus (qcb_val (Qcb_make x))
                                  (qcb_val (Qcb_make y)))) /Qcb_make
   ?qcb_valE /Qplus /Qnum /Qden !Zmult_1_r Pmult_1_r /Q2Qcb ?qcb_valE
   (eqP (Qcb_Z _)).
Qed.

Lemma half_lt : forall a b :Qcb, 0 < a -> 0 <  b ->
   a / ((Qcb_make 2) * b) < a / b.
move => a b Ha Hb; rewrite ltef_mulpl // invr_mul //=; last first.
  by rewrite unitfE eq_sym ltrWN.
by rewrite ltef_divp //= -{1}[_^-1]mulr1 ltef_mulp //= invf_cp0.
Qed.

Lemma cut_epsilon : forall eps:Qcb, 0 < eps ->
  exists eps1, exists eps2, 0 < eps1 /\ 0 < eps2 /\ eps1 + eps2 <= eps /\
      eps1 < eps /\ eps2 < eps.
move => eps p; exists (eps/Qcb_make 2); exists (eps/Qcb_make 2).
have p1 : 0 < eps/Qcb_make 2 by rewrite ltef_divp.
split; first done; split; first done; split.
  rewrite -mulr_addr.
  have q2 : (Qcb_make 2)^-1 + (Qcb_make 2)^-1 == 1 by [].
  by rewrite (eqP q2) mulr1 lerr.
suff cmp : eps/Qcb_make 2 < eps by [].
by rewrite ltef_divp //= -{1}[eps]mulr1 ltef_mulp.
Qed.


Lemma constructive_ivt :
  forall l x y, x < y -> eval_pol l x < 0%R -> 0%R <= eval_pol l y  ->
       forall epsilon, 0 < epsilon ->
       exists x', exists y',  - epsilon <= eval_pol l x' /\
         eval_pol l x' < 0 /\ 0 <= eval_pol l y' /\
         eval_pol l y' <= epsilon /\ x <= x' /\ x' < y' /\ y' <= y.
Proof.
move=> l a b ab nla plb.
have ba' : 0 < b - a by rewrite -(addrN a) lter_add2l.
(*have mpolapos : 0 < - eval_pol l a by rewrite gtr0_ltNr0 opprK.*)
have evalba : 0 < eval_pol l b - eval_pol l a. 
  rewrite -(lter_add2l (eval_pol l a)) add0r -addrA addNr addr0. 
  exact: lter_le_trans plb.
case: (translate_pol l a) => l' q.
case: (@cm3 (b - a) ba' l') => /= c pc.
have cpos : 0 < c.
  rewrite -(ltef_mulp _ _ _ ba') /= mul0r -[b -a]addr0.
  apply: lter_le_trans (pc 0 (b - a) _ _ _); rewrite ?lerr // ?(ltrW ba') //.
  by rewrite -{2}(addrN a) -!q ger0_abs // ltrW. 
move=> eps pe.
have pdiv : (0 < (b - a) * c / eps).
  by rewrite ltef_divp // mul0r mulf_gte0 /= ba' cpos.
move: (pdiv); move/ltrW; move/QcblebP; case/QZ_bound => n qn.
(* assia : canonical structures are missing here for Z -> Qcb *)
have qn' : (((b - a) * c / eps) <= (Qcb_make n)).
    by apply/QcblebP; rewrite /Qcb_make qcb_valE.
have fact1 : 0 < n.
  have tmp : 0 < Qcb_make n.
    by apply: lter_le_trans pdiv qn'.
  move: tmp; move/QcblebP. rewrite /Qcb_make /=.
  by move/Qle_bool_iff; rewrite /Qle_bool /= Zmult_1_r; move/negP.
have mkl: 
  exists l, forall l1 l2 x y, 
    [:: a & l] ++ [:: b] = l1 ++ [:: x, y & l2] ->
    y - x = (b - a) / (Qcb_make n) /\ 
    exists k : Z, 
      x = a + (b - a)* (Qcb_make k)/ (Qcb_make n) /\ 
      (0<= k) /\ (k <= n - 1).
  case en : (n == 1).
  - rewrite (eqP en); exists [::] => l1 l2 x y /=; case: l1 => [| t1 ql1] /=.
      case=> e1 e2 e3; rewrite e1 e2 Qcb_make1 invr1 mulr1; split=> //.
      by exists 0; rewrite addrN lerr Qcb_make0 mulr0 mul0r addr0; split.
    by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- exists (map  (fun x => a + (b-a)*((Qcb_make x)/(Qcb_make n))) (ns (n-1) (n-2))).
  have fact8 : 0 <= n - 2%Z.
    move/eqP: en; move: fact1; rewrite -[1]/1%Z -[0]/0%Z.
    clear. rewrite /is_true. rewrite -Zle_is_le_bool-[(n-2%Z)%R]/(n - 2)%Z.
    rewrite -[0%Z < n]/(~~(Zle_bool n 0)); move/negP.
    rewrite /is_true -Zle_is_le_bool; omega.
  have fact2 : 0 <= n - 1.
    by rewrite  ler_eqVlt (ler_lte_trans fact8) ?orbT // lter_add2r.
  move=> l1 l2 x y; case: l1 => [|t1 ql1] /=.
    case: (ns_head (n - 1) (n - 2) fact8) => a1 qa1.
    rewrite qa1 /= (_ : (n - 1) - (n - 2)%Z = 1) ?Qcb_make1; last first.
      by rewrite addrAC [-(n - 2%Z)]oppr_add addrA opprK addrN add0r. 
    case => -> <- /=; split.
      by rewrite addrAC addrN add0r mulrA mulr1.
    exists 0; rewrite Qcb_make0 mulr0 mul0r addr0 lerr; split=> //; split=> //.
  case=> ->; case: l2 => [|d l2] /=.
    rewrite -[[:: x, y & [::]]]/([::x]++[:: y]) catA.
    rewrite !cats1 -!rot1_cons; move/rot_inj; case=> <-.
    case: (ns_tail (n - 1) (n - 2))=> l3 ->; rewrite map_cat /=.
    rewrite cats1 -rot1_cons; move/rot_inj; case=> <- h2.
    have fact3 : (Qcb_make (n - 1) / Qcb_make n) = 1 - (Qcb_make n)^-1.
      have nn0 : ~~ (Qcb_make n == 0).
         by apply/negP => nis0; move/Qcb_QeqP: nis0; 
         rewrite /Qeq /= Zmult_1_r => nis0; move: fact1;
         rewrite nis0 ltrr.
      by apply/eqP; rewrite /= (eqP (Qcb_make_add _ _)) mulr_addl mulrV /= //.
    rewrite fact3 mulr_addr mulr1 oppr_add !addrA oppr_add addrA addrN add0r.
    rewrite -mulrN opprK; split=> //.
    exists (n - 1); split; last by rewrite lerr.
    by rewrite  -mulrA fact3 mulr_addr mulr1 !addrA.
  case: (non_empty_tail  _ d l2) => l3 [e qe]; rewrite qe.
  rewrite -[ql1 ++ [:: x, y & l3 ++ [:: e]]]/(ql1 ++ [:: x, y & l3] ++ [:: e]).
  rewrite [_ ++ _ ++ [:: e]]catA !cats1 -!rot1_cons; move/rot_inj; case=> -> q''.
  case: (map_contiguous _ _ (fun x => t1+(e-t1)*((Qcb_make x)/(Qcb_make n)))
             _ _ _ _ _ q'') =>  [l'1 [l'2 [n1 [n2 [_ [_ [qx [qy st]]]]]]]].
  rewrite qx qy.
  have n21 : n2 = n1 + 1 by apply: ns_step st.
  split.
    rewrite n21 [t1 + _]addrC -addrA oppr_add [t1 + _]addrA addrN add0r -mulrN
       -mulr_addr -mulNr -[_ * _^-1 + _]mulr_addl.
    have fact5: Qcb_make (n1 + 1) - Qcb_make n1 = 1.
      by rewrite -[_ - _]/(Q2Qcb (Qcb_make _ + Qcbopp(Qcb_make _)))
          /Qcbopp /Qcb_make ?qcb_valE /Qopp /Qden /Qnum /Q2Qcb ?qcb_valE
          (eqP (Qcb_Z _)) /Qplus /Qden /Qnum /Pmult 2!Zmult_1_r -Zplus_assoc
          [Zplus _ (Zopp _)]Zplus_comm Zplus_assoc Zplus_opp_r Zplus_0_l.
    by rewrite fact5 mul1r.
  exists n1; split; first by rewrite mulrA.
  have bds : (1 <= n1) && (n1 <= (n-1)).
    have fact9 : (n - 1) - (n - 2%Z) = 1
        by rewrite oppr_add opprK addrA [ _ - n]addrC addKr.
    by rewrite -{1}fact9; apply: ns_bounds _ _ _ _ _ fact8 st.
  move/andP: bds => [bds1 bds2];split; last by [].
  have fact6: 0 <= n1 by apply: ler_trans bds1; apply: ltrW; apply ltr01.
  by [].
case: mkl => [sl qsl].
have fact7 : ~ eval_pol l b < 0.
  by apply/negP; rewrite ltrNge.
case: (find_pair _ (fun x => (eval_pol l x) < 0)
             (fun x y => y - x = (b-a)/Qcb_make n /\
                (exists k, x = a + (b-a)*Qcb_make k / Qcb_make n /\
                        0 <= k /\ k <= (n-1))) sl a b nla fact7 qsl) =>
             [a' [b' [[A1 [k [A4 A5]]] [A2 A3]]]] {qsl sl}.
exists a'; exists b'.
have aa' : a <= a'.
  rewrite -(addr0 a) A4; apply: lter_add=> /=; first by apply lerr.
  rewrite mulr_ge0pp //; first apply: mulr_ge0pp; rewrite ?(ltrW ba') //.
    by apply: leb_0_Z; case: A5.
  by rewrite invf_gte0 /=; apply: leb_0_Z; apply: ltrW.
have bb' :  b' <= b.
  have bdec : b = a + (b - a) * (Qcb_make n) / (Qcb_make n).
    have nn0 : Qcb_unit (Qcb_make n).
      apply/negP => nq0; move/Qcb_QeqP: nq0.
      rewrite /Qeq Zmult_1_r /Qcb_make qcb_valE /Qnum Zmult_0_l => nq0.
      by move: fact1; rewrite nq0 ltrr.
    by rewrite mulrK // addrA [a + _]addrC addrK.
  have b'a: b' = a' + (b' - a') by rewrite addrA [ a' + _]addrC addrK /=.
  rewrite b'a A1 A4 -addrA {3}bdec -mulr_addl; apply: lter_add; rewrite /= ?lerr //=.
  rewrite lter_mulpr //=; first by rewrite invf_gte0; apply: leb_0_Z; apply: ltrW.
  rewrite -{2}[b - a]mulr1 -mulr_addr lter_mulpl //= ?(ltrW ba') //.
  rewrite -Qcb_make1  -(eqP (Qcb_make_add _ _)) /=; apply: leb_Z.
  by case: A5=> _; rewrite -(lter_add2l 1) addrNK.
have ab' :  a' < b'.
  by rewrite -(lter_add2l (- a')) addrN A1 /=  mulf_gte0 /= invf_cp0 /= ltb_0_Z // ba'.
have epsban: (b-a)*c/Qcb_make n <= eps.
  by rewrite ltef_divpl ?ltb_0_Z // [eps * _]mulrC -ltef_divpl.
have main: eval_pol l b' - eval_pol l a' <= eps.
  rewrite !q -(@ger0_abs _ (_ - _)).
    have b'a': c * (b' - a') <= eps by rewrite A1 mulrA (mulrC c).
    apply: ler_trans b'a'; rewrite -{2}(addr0 b') -(addNr a) addrA
        -(addrA (b' - a)) -(opprK (a - a')) oppr_add opprK (addrC (-a)).
    apply: pc.
    - by rewrite subr_gte0.
    - by rewrite lter_add2l /= ltrW.
    - by rewrite lter_add2l.
  rewrite -!q lter_addpl //=; first by rewrite oppr_gte0 /= ltrW.
  by rewrite -ltrNge; apply/negP.
split; last (split; first exact A2).
  rewrite lter_oppl /=; apply: ler_trans main.
  by rewrite lter_addrl /= -ltrNge; apply/negP.
split; first by rewrite -ltrNge; move/negP: A3.
split; last by auto.
apply: ler_trans main; rewrite -{1}(addr0 (eval_pol l b')); apply: lter_add; rewrite /= ?lerr //.
by rewrite /= oppr_gte0 /= ltrW.
Qed.
*)
