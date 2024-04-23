From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype order.
From mathcomp Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import mxalgebra perm zmodp matrix ssrint.
(*From mathcomp Require Import (*refinements NB(rei) funperm*).*)
From mathcomp Require Import seq rat.
Require Import (*seqpoly*) pol square_free casteljau desc.

From mathcomp Require Import ssrnum ssrint realalg poly.
Require Import poly_normal.
Import Order.Theory GRing.Theory Num.Theory.

(* Bernstein coefficients for half intervals can be computed using the
 algorithm by de Casteljau. *)
Open Scope ring_scope.

Fixpoint casteljau (l : seq rat) (n : nat) : nat -> rat :=
  match n with
    O => fun j => nth 0 l j
  | S p => fun j => ((casteljau l p j + casteljau l p j.+1)/(1+1))%R
  end.

(* This computes the Bernstein coefficients for the left hand side
  half. *)
Definition dicho_l n l :=
  map (fun i => casteljau l i 0) (iota 0 (S n)).

Definition dicho_r n l :=
  map (fun i => casteljau l (n - i) i) (iota 0 (S n)).

(*
Fixpoint count_root n d (l : seq rat) : option nat :=
 match n with
   0 => None
 | S p =>
   match qe_rcf_th.changes (seqn0 l) with
     0%N => Some 0%N
   | 1%N => Some 1%N
   |_ => let l2 := dicho_r d l in
      match count_root p d l2, count_root p d (dicho_l d l) with
        Some v1, Some v2 =>
          if head 0 l2 == 0 then Some (v1 + v2 + 1)%N else Some (v1 + v2)%N
      | _, _ => None
      end
    end
  end.
*)

Section dicho_correct.
Variable R : numFieldType.

Lemma casteljau_correct (l : seq rat) k n :
  ratr (casteljau l k n) =
  de_casteljau (R:=R) (1/(1+1)) (1/(1+1))
    (fun i => ratr (nth 0 l i)) k n.
Proof.
elim : k n => [ n | k Ik n]; first by [].
rewrite /= rmorphM rmorphD rmorphV;  last by rewrite unitf_gt0 //.
by rewrite /= rmorphD !rmorph1 !Ik mulrDl !mul1r !(mulrC (_ ^-1)).
Qed.

Lemma dicho_l_correct (n : nat) (l : seq rat) (k : nat) :
  (size l <= n.+1)%nat -> (k <= n)%nat ->
  ratr (nth 0 (dicho_l n l) k) =
   dicho' (R := R) (1/(1+1)) (1/(1+1)) (fun i => ratr (nth 0 l i)) k.
Proof.
move => sl kn.
rewrite /dicho_l /dicho'.
have kn' : (k < size (iota 0 n.+1))%nat.
 by rewrite size_iota.
rewrite (nth_map 0%nat 0 (fun v => casteljau l v 0)) //.
by rewrite nth_iota // add0n casteljau_correct.
Qed.

Lemma dicho_r_correct (n : nat) (l : seq rat) (k : nat) :
  (size l <= n.+1)%nat -> (k <= n)%nat ->
  ratr (nth 0 (dicho_r n l) k) =
   dicho (R := R) (1/(1+1)) (1/(1+1)) n (fun i => ratr (nth 0 l i)) k.
Proof.
move => sl kn.
rewrite /dicho_r /dicho.
have kn' : (k < size (iota 0 n.+1))%nat.
 by rewrite size_iota.
rewrite (nth_map 0%nat 0 (fun v => casteljau l (n - v) v)) //.
by rewrite nth_iota // add0n casteljau_correct.
Qed.

End dicho_correct.

Inductive root_info A : Type :=
  | Exact (x : A)
  | One_in (x y : A)
  | Zero_in (x y : A)
  | Unknown (x y : A).

(*
Fixpoint isol_rec n d (a b : rat) (l : seq rat) acc : seq (root_info rat) :=
  match n with
    O => Unknown _ a b::acc
  | S p =>
    match qe_rcf_th.changes (seqn0 l) with
    | 0%nat => Zero_in _ a b::acc
    | 1%nat => One_in _ a b::acc
    | _ =>
    let c := ((a + b)/(1+1)) in
    let l2 := dicho_r d l in
    isol_rec p d a c (dicho_l d l)
        (if head 0 l2 == 0 then
           Exact _ c::isol_rec p d c b l2 acc
        else isol_rec p d c b l2 acc)
    end
  end.
*)

Definition root_info_eq (R : eqType)
 (x y : root_info R) : bool :=
  match x, y with
    Exact a, Exact b => a == b :> R
  | Zero_in a1 a2, Zero_in b1 b2 => (a1 == b1 :> R) && (a2 == b2 :> R)
  | One_in a1 a2, One_in b1 b2 => (a1 == b1 :> R) && (a2 == b2 :> R)
  | Unknown a1 a2, Unknown b1 b2 => (a1 == b1 :> R) && (a2 == b2 :> R)
  | _, _ => false
  end.

Lemma root_info_eqP : forall (R : eqType), Equality.axiom (root_info_eq R).
Proof.
by move => R [x|x y|x y|x y] [z |z t|z t|z t];
 (apply: (iffP idP);
   first (rewrite //=; try (case/andP=> /eqP -> /eqP -> //);
                            move=>/eqP ->)) => //; case=> -> //= -> /=;
   apply/andP; split.
Qed.

Section more_on_dicho.

Lemma dicho_ext :
  forall (R : comRingType) (a b : R) n f1 f2 p, (p <= n)%N ->
    (forall i, (i <= n)%N -> f1 i = f2 i) ->
    dicho a b n f1 p = dicho a b n f2 p.
Proof.
move=> R a b n f1 f2 p pn q; rewrite /dicho; apply: ext_dc => i ci1 ci2.
by apply/q/(leq_trans ci2); rewrite subnKC.
Qed.

End more_on_dicho.

Section count_root_correct.

Variable R : archiFieldType.

(*TODO(rei, gave up when moving to MathComp 2): Definition R' : archiFieldType := (R : rcfType).*)

(*
Lemma count_root_correct0 n (l : seq rat) q d (a b: R') :
  (0 < d)%N -> a < b -> q != 0 -> size l = d.+1 ->
  q = \sum_(i < d.+1) (nth 0 (map ratr l) i) *:
      bernp  a b d i -> count_root n d l = Some 0%N ->
  forall (x : R'), a < x < b -> q.[x]!=0.
Proof.
move=> dgt0; elim: n l a b => [ | n In l a b ab qn0 sl qq]; first by [].
rewrite /=.
have anb : a != b.
 by apply/negP => aqb; move: ab; rewrite ltr_neqAle aqb.
have bman0 : b - a != 0  by rewrite subr_eq0 eq_sym.
have twogt0 : (0 < 1 + 1 :> R').
 by apply: addr_gt0; apply: ltr01.
have twon0 : (1 + 1 != 0 :> R').
 by apply/negP => two0; move: twogt0; rewrite ltr_neqAle eq_sym two0.
have twoV : forall a, a = a/(1 + 1) + a/(1+1) :> R'.
  by move=> y; rewrite -mulrDl -(mulr1 y) -mulrDr mulrK // mulr1.
have altm : a < (a + b)/(1 + 1).
 by rewrite {1}[a]twoV mulrDl ltr_add2l ltr_pM2r // invr_gt0.
have mltb : (a + b)/(1 + 1) < b.
 by rewrite {2}[b]twoV mulrDl ltr_add2r ltr_pM2r // invr_gt0.
have mna : (a + b)/(1 + 1) != a.
 by apply/negP => ma; move:altm; rewrite ltr_neqAle eq_sym ma.
have mnb : (a + b)/(1 + 1) != b.
 by apply/negP => mb; move:mltb; rewrite ltr_neqAle mb.
case ch: (qe_rcf_th.changes (seqn0 l)) => [ | nch].
 move => _; apply: (ch0_correct (d := d) ab qn0 qq) => //.
  (* The following proof exactly common with isol_rec_no_root, except for hypothesis
     that are discarded at the time of tactic elim *)
 elim: {qq sl} l ch => /= [| e l Il]; first by [].
 case e0 : (e == 0).
  by rewrite (eqP e0) rmorph0 eqxx.
 case h : (_ == 0).
  move/negbT : e0 => /negP; case.
  by rewrite -(fmorph_eq0 (ratr_rmorphism (RealAlg.alg_of_rcfType R))) h.
 rewrite /=.
 move/eqP; rewrite addn_eq0 => /andP [pe /eqP pl].
 apply/eqP; rewrite addn_eq0; apply/andP; split; last first.
  by apply/eqP; apply: Il.
 set (u := ratr e).
 have sr : (head 0 (seqn0 l) < 0) = 
        (head 0 (seqn0 [seq ratr i | i <- l]) < 0 :> RealAlg.alg_of_rcfType R).
  elim : {Il pl pe} l => [ | e' l' Il']; first by rewrite /= ltrr.
  rewrite /=; case he' : (e' == 0) => /=.
   by rewrite (eqP he') rmorph0 eqxx /=.
  by rewrite fmorph_eq0 he' /= ltrq0.
 have sr' : (0 < head 0 (seqn0 l)) = 
           (0 < head 0 (seqn0 [seq ratr i | i <- l]) :> RealAlg.alg_of_rcfType R).
  elim : {Il pl pe sr} l => [ | e' l' Il']; first by rewrite /= ltrr.
  rewrite /=; case he' : (e' == 0) => /=.
   by rewrite (eqP he') rmorph0 eqxx /=.
  by rewrite fmorph_eq0 he' /= ltr0q.
 case u0 : (u < 0).
  rewrite nmulr_rlt0; last by [].
  move: u0; rewrite ltrq0 => u0.
  by rewrite -sr' -(nmulr_rlt0 _ u0).
 move: u0; rewrite ltrNge ler_eqVlt eq_sym h /= => /negbFE => u0.
 rewrite pmulr_rlt0; last by [].
 by move: u0; rewrite ltr0q => u0; rewrite -sr -(pmulr_rlt0 _ u0).
 (* end of common proof. *)
case: {ch} nch => [| _]; first by [].
case cr1 : (count_root n d (dicho_r d l)) => [ [ | v1] | //];
 case cr2 : (count_root n d (dicho_l d l)) => [ [ | v2] | //];
  case cc : ((casteljau l (d - 0) 0) == 0) => //.
move => _ x axb.
case xm : (x < (a + b) / (1 + 1)). 
 have axm : (a < x < (a + b)/(1 + 1)).
  by case/andP: axb => [ax xb]; rewrite ax xm.
 have sl' : size (dicho_l d l) = d.+1 by rewrite /dicho_l size_map size_iota.
 have qq' : q = \sum_(i < d.+1)
       [seq ratr i | i <- dicho_l d l]`_i *:
       bernp (R:=R') a ((a + b) / (1 + 1)) d i.
  have sll : (size l <= d.+1)%N by rewrite sl leqnn.
  have dlc := fun k => dicho_l_correct (RealAlg.alg_of_rcfType R) d l k sll.
  set f := fun i : 'I_d.+1 => 
    dicho' ((b - (a + b)/(1+1)) / (b - a)) (((a + b)/(1+1) - a) / (b - a))
       [eta nth 0 [seq ratr v | v <- l]] i *: bernp a ((a + b)/(1+1)) d i.
  have bodyq :
   forall i : 'I_d.+1, true ->
    [seq ratr i | i <- dicho_l d l]`_i *: bernp a ((a + b)/(1+1)) d i = f i.
   rewrite /f.
   have -> : (b - (a + b)/(1 + 1))/(b - a) = 1/(1 + 1).
    rewrite (addrC a) {1}[b]twoV !mulrDl opprD mulrBl addrA.
    by rewrite mulNr addrK -!mulrBl mulrC mulrA mulVf.
   have -> : ((a + b) / (1 + 1) - a) / (b - a) = 1/(1 + 1).
    rewrite (addrC a) {2}[a]twoV (mulrDl b) opprD addrA addrK -mulrBl.
    by rewrite mulrC mulrA mulVf.
   move=> [i id] _; congr (_ *: _).
   rewrite /nat_of_ord (nth_map 0 0) ?sl' // dlc /dicho'.
    apply: ext_dc => j j0 ji.
    by rewrite (nth_map 0 0) // (leq_ltn_trans ji) // sl.
   by rewrite -ltnS.
  rewrite (eq_bigr f bodyq) /f.
  by apply:(dicho'_correct (c :=fun i => [seq ratr v | v <- l]`_i) anb mna qq).
 by apply: (In _ _ _  altm qn0 sl' qq' cr2 _ axm).
set f := fun i : 'I_d.+1 => 
    dicho ((b - (a + b)/(1+1)) / (b - a)) (((a + b)/(1+1) - a) / (b - a))
       d [eta nth 0 [seq ratr v | v <- l]] i *: bernp ((a + b)/(1+1)) b d i.
have sll : (size l <= d.+1)%N by rewrite sl leqnn.
have drc := fun k => dicho_r_correct (RealAlg.alg_of_rcfType R) d l k sll.
have sl' : size (dicho_r d l) = d.+1 by rewrite /dicho_l size_map size_iota.
have bodyq :
   forall i : 'I_d.+1, true ->
    [seq ratr i | i <- dicho_r d l]`_i *: bernp ((a + b)/(1+1)) b d i = f i.
 rewrite /f.
 have -> : (b - (a + b)/(1 + 1))/(b - a) = 1/(1 + 1).
  rewrite (addrC a) {1}[b]twoV !mulrDl opprD mulrBl addrA.
  by rewrite mulNr addrK -!mulrBl mulrC mulrA mulVf.
 have -> : ((a + b) / (1 + 1) - a) / (b - a) = 1/(1 + 1).
  rewrite (addrC a) {2}[a]twoV (mulrDl b) opprD addrA addrK -mulrBl.
  by rewrite mulrC mulrA mulVf.
 move=> [i id] _; congr (_ *: _).
 rewrite /nat_of_ord (nth_map 0 0) ?sl' // drc /dicho.
  apply: ext_dc => j j0 ji.
  by rewrite (nth_map 0 0) // sl (leq_ltn_trans ji) // subnKC.
 by rewrite -ltnS.
have qq' : q = \sum_(i < d.+1)
       [seq ratr i | i <- dicho_r d l]`_i *:
       bernp (R:=R') ((a + b) / (1 + 1)) b d i.
 rewrite (eq_bigr f bodyq) /f.
 apply:(dicho_correct (c :=fun i => [seq ratr v | v <- l]`_i) anb mnb qq).
move/negP/negP: xm ; rewrite -lerNgt ler_eqVlt => /orP [/eqP xm | xm]; last first.
 have mxb : ((a + b)/(1 + 1) < x < b).
  by case/andP: axb => [ax xb]; rewrite xb xm.
 by apply: (In _ _ _  mltb qn0 sl' qq' cr1 _ mxb).
rewrite qq' (big_morph (fun p => horner p x) (fun p q => hornerD p q x)
               (horner0 x)).
have b0m := fun i (id : (i <= d)%N) => bern0_a mnb dgt0 id.
have all0 : forall (i : 'I_d),  true ->
   ([seq ratr i | i <- dicho_r d l]`_(lift ord0 i) *:
    bernp (R:=R') x b d (lift ord0 i)).[x] = 0.
 move => i _.
 have id: (lift ord0 i <= d)%N by case: i => [i id].
 have : (lift ord0 i != 0) by case: {id} i => [i id'].
 rewrite -(b0m _ id) xm /R' hornerZ => /eqP ->.
 by rewrite mulr0.
rewrite big_ord_recl big1; last by rewrite xm.
rewrite addr0 hornerZ mulf_neq0 //.
 by rewrite /= fmorph_eq0 cc.
by rewrite -xm (b0m _ (leq0n d)).
Qed.
*)

End count_root_correct.

Section isol_rec_correct.

Variable R : archiFieldType.

(*NB(rei): couldn't type  Unknown rat a b a few lines below
Lemma isol_rec_acc : forall n d a b l acc, exists l'',
  @isol_rec R n d a b l acc = l''++acc.
Proof.
elim => [| n In] d a b l acc.
  by rewrite /=; exists [:: Unknown rat a b].
rewrite /=; case: (qe_rcf_th.changes (seqn0 l)) => [ | n0];
 first by exists [:: Zero_in _ a b].
case: n0 => [ | n1]; first by exists [:: One_in rat a b].
case: (In d ((a + b) / (1+1)) b (dicho_r d l) acc) => [l1 l1q].
case: (casteljau l (d - 0) 0 == 0).
 case: (In d a ((a + b) / (1+1)) (dicho_l d l)
               (Exact _ ((a + b) / (1+1))::l1++acc)) => [l2 l2q].
 exists (l2++Exact _ ((a + b) / (1+1))::l1).
 by rewrite -(cat1s _ l1) l1q l2q -!catA.
case: (In d a ((a + b) / (1+1)) (dicho_l d l) (l1++acc)) => [l2 l2q].
by exists (l2++l1); rewrite l1q l2q -!catA.
Qed.*)

HB.instance Definition _ := hasDecEq.Build _ (root_info_eqP R).

(*Canonical root_info_eqType (R : eqType) :=
   Eval hnf in EqType (root_info R) (root_info_eqMixin R).

Arguments root_info_eqP {R x y}.
Prenex Implicits root_info_eqP.*)


(* NB(rei): typing issue with {realclosure _}
Lemma isol_rec_no_root n (l : seq rat) q d (a b:rat) a' b' acc :
  a < b -> q != 0 -> size l = d.+1 ->
  ~~ (Zero_in rat a' b' \in acc) ->
  Zero_in rat a' b' \in isol_rec n d a b l acc ->
  q = \sum_(i < d.+1) (nth 0 (map ratr l) i) *:
      bernp  (ratr a) (ratr b) d i ->
  forall (x : {realclosure R}), ratr a' < x < ratr b' -> q.[x]!=0.
Proof.
set two := (1 + 1: RealAlg.alg_of_rcfType R); have twon0 : two != 0.
 have twogt0' : 0 < two by apply: addr_gt0; apply:ltr01.
 by move: twogt0'; rewrite ltr_neqAle eq_sym=>/andP [].
elim: n l q d a b a' b' acc => [ | n In] l q d a b a' b' acc ab qn0 sl nin /=.
 by rewrite in_cons =>/orP [ // | ] => in_indeed; move:nin; rewrite in_indeed.
have rcfab : (ratr a < ratr b :> RealAlg.alg_of_rcfType R).
 (* could not use directly apply: ltr_rat; obviously I did not understand
    that morphism properties are rewriting properties *)
  by rewrite ltr_rat.
have rabd : ratr a != ratr b :> RealAlg.alg_of_rcfType R.
 apply/negP; move/eqP => rab.
 have aqb: a == b by apply/eqP/(fmorph_inj (ratr_rmorphism _) rab).
 by move: ab; rewrite ltr_neqAle aqb.
have rbman0 : ratr b - ratr a != 0 :> RealAlg.alg_of_rcfType R.
 by rewrite subr_eq0 eq_sym.
have twogt0 : 0 < 1 + 1 :> rat   by apply: addr_gt0; rewrite ltr01 .
have a1b1 : (a + b)/(1+1) < b :> rat.
 rewrite -(ltr_pM2r twogt0) mulfVK.
  by rewrite mulrDr mulr1 ltr_add2r.
 by move: twogt0; rewrite ltr_neqAle eq_sym=>/andP; case.
have a2b2 : a < (a + b)/(1+1) :> rat.
 rewrite -(ltr_pM2r twogt0) mulfVK.
  by rewrite mulrDr mulr1 ltr_add2l.
 by move: twogt0; rewrite ltr_neqAle eq_sym=>/andP; case.
have rmbd: (ratr a + ratr b)/(1+1) != ratr b :> RealAlg.alg_of_rcfType R.
 apply/negP;move=> /eqP.
 rewrite -(rmorph1 ((ratr_rmorphism _))) -!rmorphD -fmorphV -rmorphM => rmb.
 have mqb: (a + b)/(1 + 1) == b.
  by apply/eqP/(fmorph_inj (ratr_rmorphism _) rmb).
 by move: a1b1; rewrite ltr_neqAle mqb.
have ramd: ratr a != (ratr a + ratr b)/(1+1) :> RealAlg.alg_of_rcfType R.
 apply/negP;move=> /eqP.
 rewrite -(rmorph1 ((ratr_rmorphism _))) -!rmorphD -fmorphV -rmorphM => ram.
 have aqm: a == (a + b)/(1 + 1).
  by apply/eqP/(fmorph_inj (ratr_rmorphism _) ram).
 by move: a2b2; rewrite ltr_neqAle aqm.
have sd : size (dicho_r d l) = d.+1  by rewrite /dicho_r size_map size_iota.
 have sl' : (size l <= d.+1)%N   by rewrite leq_eqVlt sl eqxx.
have sd' : size (dicho_l d l) = d.+1 by rewrite /dicho_l size_map size_iota.
case ch: (qe_rcf_th.changes (seqn0 l)) => [ | nch].
 rewrite in_cons=> /orP [ /eqP[-> ->] | abs] qq x intx.
  apply: (ch0_correct (d := d) rcfab qn0 qq) => //.
  elim: {qq sl sd sd' sl'} l ch => /= [| e l Il]; first by [].
  case e0 : (e == 0).
   by rewrite (eqP e0) rmorph0 eqxx.
  case h : (_ == 0).
   move/negbT : e0 => /negP; case.
   by rewrite -(fmorph_eq0 (ratr_rmorphism (RealAlg.alg_of_rcfType R))) h.
  rewrite /=.
  move/eqP; rewrite addn_eq0 => /andP [pe /eqP pl].
  apply/eqP; rewrite addn_eq0; apply/andP; split; last first.
   by apply/eqP; apply: Il.
  set (u := ratr e).
  have sr : (head 0 (seqn0 l) < 0) =
         (head 0 (seqn0 [seq ratr i | i <- l]) < 0 :> RealAlg.alg_of_rcfType R).
   elim : {Il pl pe} l => [ | e' l' Il']; first by rewrite /= ltrr.
   rewrite /=; case he' : (e' == 0) => /=.
    by rewrite (eqP he') rmorph0 eqxx /=.
   by rewrite fmorph_eq0 he' /= ltrq0.
  have sr' : (0 < head 0 (seqn0 l)) =
            (0 < head 0 (seqn0 [seq ratr i | i <- l]) :> RealAlg.alg_of_rcfType R).
   elim : {Il pl pe sr} l => [ | e' l' Il']; first by rewrite /= ltrr.
   rewrite /=; case he' : (e' == 0) => /=.
    by rewrite (eqP he') rmorph0 eqxx /=.
   by rewrite fmorph_eq0 he' /= ltr0q.
  case u0 : (u < 0).
   rewrite nmulr_rlt0; last by [].
   move: u0; rewrite ltrq0 => u0.
   by rewrite -sr' -(nmulr_rlt0 _ u0).
  move: u0; rewrite ltrNge ler_eqVlt eq_sym h /= => /negbFE => u0.
  rewrite pmulr_rlt0; last by [].
  by move: u0; rewrite ltr0q => u0; rewrite -sr -(pmulr_rlt0 _ u0).
 by case/negP: nin.
case: {ch} nch.
 rewrite in_cons; case/orP; last by move=>abs; move:nin; rewrite abs.
 by move/eqP.
case zac1: (Zero_in rat a' b' \in
                   (if casteljau l (d - 0) 0 == 0
            then
             Exact rat ((a + b) / (1 + 1))
             :: isol_rec n d ((a + b) / (1 + 1)) b (dicho_r d l) acc
            else isol_rec n d ((a + b) / (1 + 1)) b (dicho_r d l) acc)).
 move => _ _ qq.
 have zac2 : Zero_in rat a' b' \in
               isol_rec n d ((a + b) / (1 + 1)) b (dicho_r d l) acc.
  move: zac1; case: (casteljau l (d - 0) 0 == 0); last by [].
  by rewrite in_cons; case/orP => [/eqP | ].
 apply: (In _ q d _ _ a' b' acc a1b1 qn0 sd nin zac2).
 move=> {zac1 In zac2}.
 have drc := fun k => dicho_r_correct (RealAlg.alg_of_rcfType R) d l k sl'.
 have bodyq :
   forall i : 'I_d.+1,
    [seq ratr i | i <- dicho_r d l]`_i *:
    bernp (ratr ((a + b)/(1+1))) (ratr b) d i =
    dicho ((ratr b - (ratr a + ratr b)/(1+1)) / (ratr b - ratr a))
    (((ratr a + ratr b)/(1+1) - ratr a) / (ratr b - ratr a)) d
    [eta nth 0 [seq ratr v | v <- l]] i *:
    bernp (R:=RealAlg.alg_of_rcfType R) ((ratr a + ratr b)/(1+1)) (ratr b) d i.
  (* TODO : find the politically correct way to do "simpl nat_of_ord" without simplifying everywhere *)
  move=> [i id]; simpl nat_of_ord.
  move: (id); rewrite ltnS => id'.
  rewrite -[X in X - _/_](mulfVK twon0) mulrDr mulr1 -mulrDl -mulrBl opprD.
  rewrite addrA (addrC _ (- ratr b)) !addrA addNr add0r (mulrC ((_ - _) / _)).
  rewrite mulrA mulVr //.
  rewrite -[X in _/_ - X](mulfVK twon0) mulrDr mulr1 -mulrDl -mulrBl opprD.
  rewrite !addrA (addrC (_ + _) (- ratr a)) !addrA addNr add0r.
  rewrite -mulrA (mulrC (_^-1)) mulrA mulrV //.
  rewrite rmorphM rmorphD rmorphV // rmorphD rmorph1.
  congr (_ *: _); rewrite (nth_map 0 0); last by rewrite sd.
  rewrite drc //; apply: (dicho_ext _ (1/two)) => //.
  by move => j jc; rewrite (nth_map  0 0) // sl ltnS.
 rewrite (eq_bigr (fun i : 'I_d.+1 =>
     dicho (R:=RealAlg.alg_of_rcfType R)
            ((ratr b - (ratr a + ratr b) / (1 + 1)) / (ratr b - ratr a))
            (((ratr a + ratr b) / (1 + 1) - ratr a) / (ratr b - ratr a)) d
            [eta nth 0 [seq ratr v | v <- l]] i *:
          bernp (R:=RealAlg.alg_of_rcfType R) ((ratr a + ratr b) / (1 + 1))
            (ratr b) d i)); last by move => i _; apply bodyq.
 by apply: (dicho_correct (c := fun i => [seq ratr v | v <- l]`_i) rabd rmbd qq).
move: zac1; set acc' := (if casteljau _ _ _ == 0 then _ else _).
move/negP/negP=> zac1 _ zac2 qq.
 apply: (In _ q d _ _ a' b' acc' a2b2 qn0 sd' zac1 zac2).
 have dlc := fun k => dicho_l_correct (RealAlg.alg_of_rcfType R) d l k sl'.
 have bodyq :
   forall i : 'I_d.+1,
    [seq ratr i | i <- dicho_l d l]`_i *:
    bernp (ratr a) (ratr ((a + b)/(1+1))) d i =
    dicho' ((ratr b - (ratr a + ratr b)/(1+1)) / (ratr b - ratr a))
    (((ratr a + ratr b)/(1+1) - ratr a) / (ratr b - ratr a))
    [eta nth 0 [seq ratr v | v <- l]] i *:
    bernp (R:=RealAlg.alg_of_rcfType R) (ratr a) ((ratr a + ratr b)/(1+1)) d i.
 move=> [i id]; simpl nat_of_ord. (* TODO : same as above *)
 move: (id); rewrite ltnS => id'.
 rewrite -[X in X - _/_](mulfVK twon0) mulrDr mulr1 -mulrDl -mulrBl opprD.
 rewrite (addrC (-ratr a)) addrA addrK (mulrC ((_ - _) / _)) mulrA mulVr //.
 rewrite -[X in _/_ - X](mulfVK twon0) mulrDr mulr1 -mulrDl -mulrBl opprD.
 rewrite !addrA (addrC (_ + _) (- ratr a)) !addrA addNr add0r.
 rewrite -mulrA (mulrC (_^-1)) mulrA mulrV //.
 rewrite rmorphM rmorphD rmorphV // rmorphD rmorph1.
 congr (_ *: _); rewrite (nth_map 0 0); last by rewrite sd'.
 rewrite dlc //; rewrite /dicho'; apply ext_dc.
 by move => j j0 ji; rewrite (nth_map 0 0) // sl (leq_ltn_trans ji) //.
move: ramd; rewrite eq_sym => ramd.
rewrite (eq_bigr (fun i : 'I_d.+1 =>
    dicho' (R:=RealAlg.alg_of_rcfType R)
           ((ratr b - (ratr a + ratr b) / (1 + 1)) / (ratr b - ratr a))
           (((ratr a + ratr b) / (1 + 1) - ratr a) / (ratr b - ratr a))
           [eta nth 0 [seq ratr v | v <- l]] i *:
         bernp (R:=RealAlg.alg_of_rcfType R) (ratr a) ((ratr a + ratr b) / (1 + 1))
             d i)); last by move => i _ ; apply bodyq.
by apply: (dicho'_correct (c := fun i => [seq ratr v | v <- l]`_i) rabd ramd).
Qed.
*)

End isol_rec_correct.

Definition big_num := 500%nat.

(* Returns the last element of the sequence of coefficients, i.e.
  the lead coefficient if the sequence is normal. *)
(*NB(rei): it looks like this has to do with evaluation, rm?
Definition lead_coef p := last 0%bigQ p.
*)

(* To be used with a monic divisor d, of degree dd *)

(*
Fixpoint divp_r (p d : seq bigQ) (dd : nat) : seq bigQ * seq bigQ :=
  if NPeano.Nat.leb (size p) dd
  then ([::], p)
  else
    match p with
      [::] => ([::], p)
    | a::p' => let (q, r) := divp_r p' d dd in
      let y := nth a (a::r) dd in
        (y::q, addp (a::r) (scal ((-1) * y) d))
    end.

Definition divp p d :=
  let d' := normalize d in
  let dd := (size d').-1 in
  let lc := lead_coef d' in
  match d' with
    [::] => ([::], p)
  | _::_ => let (q, r) := divp_r p (map (fun x => x/lc)%bigQ d') dd in
    (map (fun x => x/lc)%bigQ q, normalize r)
  end.
*)

(* Correctness proof. *)

(* Definition repr (l : list bigQ) : poly rat := *)

(*

Definition clean_divp p d :=
  let (a, b) := divp p d in (map red (normalize a), map red (normalize b)).

Fixpoint gcd_r n (p q : seq bigQ) : seq bigQ :=
  match n with
    O => p
  | S n' =>
    let (_, r) := clean_divp p q in
      match r with nil => q | _ => gcd_r n' q r end
  end.

Definition gcd (p q : seq bigQ) :=
  let r := gcd_r (maxn (size p) (size q)).+1 p q in
  let lc := lead_coef r in
  map (fun x => red (x/lc)) r.

Compute (clean_divp [::3;1] [::4;1])%bigQ.
Compute (clean_divp [::3;2;1] [::1])%bigQ.
Compute (gcd_r 4 [::3;1] [::4;1])%bigQ.

Fixpoint bigQ_of_nat (n : nat) :=
  match n with 0%nat => 0%bigQ | S p => (1 + bigQ_of_nat p)%bigQ end.

Definition derive p := 
  match product (map bigQ_of_nat (iota 0 (size p))) p with
    _::p' => p' | _ => nil
  end.

Definition no_square p :=
  fst (clean_divp p (gcd p (derive p))).

Definition isolate a b p : seq (root_info bigQ) :=
  let l := no_square p in
  let deg := (size l).-1 in
  let coefs := b_coefs deg a b l in
  let b_is_root :=
    if eq_bool (last 0%bigQ coefs) 0 then [:: Exact _ b] else [::] in
  let result := isol_rec big_num deg a b coefs b_is_root in
  if eq_bool (head 0%bigQ l) 0 then Exact _ a::result else result.

Fixpoint horner x p :=
  match p with
    nil => 0%bigQ
  | a::p' => (a + x * horner x p')%bigQ
  end.

Fixpoint ref_rec n a b pol :=
  match n with
    O => One_in _ (red a) (red b)
  | S p =>
    let c := ((a + b)/2)%bigQ in
    let v := horner c pol in
    match (v ?= 0)%bigQ with
      Lt =>  ref_rec p c b pol
    | Gt =>  ref_rec p a c pol
    | Eq => Exact _ (red c)
    end
  end.

Fixpoint first_sign l :=
  match l with
    nil => 1%bigQ
  | a::tl =>
   match (a ?= 0) with Eq => first_sign tl | Lt => -1 | Gt => 1 end%bigQ
  end.

Definition refine n a b p :=
  let deg := (List.length p).-1 in
  let coefs := b_coefs deg a b p in
  ref_rec n a b (scal (-1 * first_sign coefs) p).

(* This polynomial has 1,2, and 3 as roots. *)
Definition pol2 : list bigQ := ((-6)::11::(-6)::1::nil)%bigQ.

(* This polynomial as 1 and 2 as roots, with respective multiplicities
  1 and 2. *)

Definition pol3 : list bigQ := ((-4)::8::(-5)::1::nil)%bigQ.

Fixpoint no_root (l : list (root_info bigQ)) : bool :=
  match l with
    nil => true
  | Zero_in a b::l' => no_root l'
  | _ => false
  end.

(* this polynomial has only one root, but the curve comes close to
  the x axis around 2.5: this forces the dichotomy process a few times. *)
Definition mypol : list bigQ := ((-28/5)::11::(-6)::1::nil)%bigQ.

Compute mypol.
Compute clean_divp mypol [::1]%bigQ.
Compute no_square mypol.
Compute b_coefs 3 0 4 (no_square mypol).

(* The following isolates the single root of mypol in (0,4) *)
Compute isolate 0 4 mypol.

(* The following computation proves that mypol has no roots in (2,4) *)
Compute no_root (isolate 2 4 mypol).

Compute b_coefs 3 2 4 mypol.
Compute map (fun p => p.1 ?= p.2)%bigQ 
    (zip (dicho_r 3 (b_coefs 3 2 4 mypol)) (b_coefs 3 3 4 mypol)).
Compute let l := b_coefs 3 3 4 mypol in (changes l, l).
Compute isol_rec big_num 3 2 3 (b_coefs 3 2 3 mypol) [::].
Compute isol_rec big_num 3 0 4 (b_coefs 3 0 4 mypol) [::].

Compute isolate 2 4 mypol.

Time Compute refine 20 0 2 mypol.

Compute (horner (110139 # 131072) mypol).
Compute (horner (440557 # 524288) mypol).

(* Polynomial pol2 actually has roots in 1, 2, and 3 *)
Compute isolate 0 4 pol2.

Compute isolate 0 4 pol3.

(* When the path of computation touches the roots, they are recognized
 as such. *)
Compute isolate 1 3 pol2.

Compute refine 10 (11#10) 3 pol2.

Compute ((10000 * 20479 / 10240)%bigZ, (10000 * 10249 / 5120)%bigZ).

(* Without type information, this gives an error message that looks like a
  bug. *)

Compute clean_divp ((-2)::1::1::nil)%bigQ (4::2::nil)%bigQ.

Compute let p := ((-2)::1::1::nil)%bigQ in
        let d := (2::1::nil)%bigQ in
        let (q, r) := divp p d in
        (q, r, normalize (addp p (scal (-1) (addp (mulp q d) r)))).

Compute let p := ((-2)::1::1::nil)%bigQ in
        let q := ((-1)::3::(-3)::1::nil)%bigQ in
        gcd p q.

Compute derive ((-1)::3::(-3)::1::nil)%bigQ.

Compute gcd ((-1)::3::(-3)::1::nil)%bigQ (derive ((-1)::3::(-3)::1::nil)%bigQ).

Compute clean_divp ((-1)::3::(-3)::1::nil)%bigQ
             (1::(-2)::1::nil)%bigQ.

Time Compute no_square ((-1)::3::(-3)::1::nil)%bigQ.

(* This is a poor man's correctness proof for the decision procedure,
  but it should actually be extended to be used in any real-closed field. *)

*)
