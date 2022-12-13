(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    Inria, 2006              *)
(*************************************************************)


Require Import Setoid.
Require Import ZArith.
Require Import CAD_types.
Require Import Utils.
(* Fichiers charges pour la tactique setoid ring *)
Require Import Ring_tac.
Require Import Ring_theory.
Require Pol.
Require Import Ring_th.
Require Import ZRing_th.


(*Operations "abstraites" sur les coefficients,plus tard dans une section et 
reinstanciation au debut de chaque fichier du dev ...*)
Require Import Coef_record.

(*Structure d'anneau sur les Coefs, lemmes de compat *)
Load Coef_load.
  
(* Maintenant on declare ceq comme une relation, pour pouvoir
  l'utiliser dans les morphismes qui prennent aussi ddes arguments
  dans d'autres setoides*) 
Load Coef_relation.


  Definition cRth : ring_theory c0 c1 cadd cmul csub copp ceq.
  Proof.
  constructor.
  exact cadd_0_l. 
  exact cadd_sym.
  exact cadd_assoc.
  exact cmul_1_l.
  exact cmul_sym.
  exact cmul_assoc.
  exact cdistr_l.
  exact csub_def.
  exact copp_def.
  Qed.

 Add  New Ring CoefRing : cRth Abstract. 

(* csub est un morphisme *)
Add Morphism csub with signature ceq  ==>  ceq ==> ceq as csub_Morphism.
Proof.
  intros x1 x2 H1 y1 y2 H2.
  setoid_replace (x1 -- y1) with (x1 ++ (-- y1));[idtac|setoid ring].
    setoid_replace (x2 -- y2) with (x2 ++ (-- y2));[idtac|setoid ring].
    rewrite H1;rewrite H2;reflexivity.
Qed.



Lemma copp_0 : -- c0==c0 .
Proof.
  setoid ring.
Qed.

 Lemma cmul_0_l : forall x, c0 ** x == c0.
 Proof.
   intros;setoid ring.
 Qed.

 Lemma cmul_0_r : forall x, x**c0 == c0.
 Proof.
  intros;setoid ring.
 Qed.

Lemma cmul_1_r:forall x, x**c1==x.
 Proof.
  intros;setoid ring.
 Qed.


 Lemma copp_mul_l : forall x y, --(x ** y) == --x ** y.
 Proof.
  intros;setoid ring.
 Qed.
  
 Lemma copp_mul_r : forall x y, --(x**y) == x ** --y.
 Proof.
  intros;setoid ring.
 Qed.

 Lemma copp_add : forall x y, --(x ++ y) == --x ++ --y.
 Proof.
  intros;setoid ring.
 Qed.

 Lemma cdistr_r : forall x y z, x**(y ++ z) == x**y ++ x**z.
 Proof.
  intros; setoid ring.
 Qed.

 Lemma cadd_0_r : forall x, x ++ c0 == x.
 Proof.
  intro; setoid ring.
 Qed.
 
 Lemma cadd_assoc1 : forall x y z, (x ++ y) ++ z == (y ++ z) ++ x.
 Proof.
  intros;setoid ring.
 Qed.

 Lemma cadd_assoc2 : forall x y z, (y ++ x) ++ z == (y ++ z) ++ x.
 Proof.
  intros; setoid ring.
 Qed.

 Lemma cmul_assoc1 : forall x y z, (x ** y) ** z == (y ** z) ** x.
 Proof.
  intros;setoid ring.
 Qed.
 
 Lemma cmul_assoc2 : forall x y z, (y ** x) ** z == (y ** z) ** x.
 Proof.
  intros; setoid ring.
 Qed.

Lemma copp_opp : forall x, -- --x == x.
 Proof.
  intros;setoid ring.
 Qed.


(* ces deux lemmes ne sont pas trivalisables avec cring...*)

 Lemma cadd_reg_l : forall n m p, p ++ n == p ++ m -> n == m.
Proof.
intros.
generalize (cadd_ext (--p) (--p) (p++n) (p++m)).
repeat rewrite cadd_assoc.
assert (-- p ++ p == c0). 
rewrite cadd_sym.
setoid ring.
 rewrite H0;repeat rewrite cadd_0_l;intro h;apply h;auto.
apply ceq_refl.
Qed.

Lemma cadd_reg_r: forall n m p, n ++ p==  m++p -> n == m.
intros; apply (cadd_reg_l n m p).
repeat rewrite (cadd_sym p);auto.
Qed.

Lemma copp_eq: forall c c', c -- c'==c0 -> c==c'.
intros c c' ; rewrite (csub_def c c') ;intro H.
generalize (cadd_ext (c++ --c') c0 c' c').
rewrite cadd_0_l;intro h;rewrite <- h;auto;try setoid ring.
Qed.


(* 
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
cof_pos : positive -> Coef
*)

Load Pol_on_Coef.
Notation "a !* x" := (Pol_mul_Rat  x a )(at level 40, left associativity).


 Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.


(**Equality over polynomials,not in normal forms*)
 Inductive Pol_Eq:Pol -> Pol -> Prop :=
   |Eq_Pc_Pc : forall p q: Coef, (ceq p q)->(Pol_Eq (Pc p) (Pc q))
   |Eq_Pc_PX :
     forall p q: Coef, forall P:Pol,(ceq p q)->(Pol_Eq P P0)->forall i, (Pol_Eq (Pc p) (PX P i q))
   |Eq_PX_Pc :
     forall p q: Coef, forall P:Pol,(ceq p q)->(Pol_Eq P P0)->forall i, (Pol_Eq (PX P i  p) (Pc q))
   |Eq_PX_PX :
     forall p q:Coef, forall P Q :Pol, (ceq p q)->(Pol_Eq P Q)->forall i, (Pol_Eq (PX P i  p) (PX Q i q))
   |Eq_PXi_PXij:
     forall p q: Coef, forall P Q:Pol, forall i j, (ceq p q)-> (Pol_Eq Q (PX P i c0))->
      (Pol_Eq  (PX Q  j   q)(PX P (i+j)  p))
   |Eq_PXij_PXi:
     forall p q: Coef, forall P Q :Pol, forall i j,  (ceq p q)-> (Pol_Eq Q (PX P i c0)) ->
      (Pol_Eq (PX P (i+j)  p) (PX Q  j   q)).
 
(* Some notations *)
 (* Definition PolEq (P Q : Pol):= forall l ,(Pol_eval P l)==(Pol_eval Q l).*)

 Notation "x != y" := (Pol_Eq x y)(at level 70, no associativity).
 Notation "x + y" := (Pol_add x y)(at level 50, left associativity).
 Notation "x * y" := (Pol_mul x y)(at level 40, left associativity).
 Notation "x - y" := (Pol_sub x y)(at level 50, left associativity).
 Notation "- x" := (Pol_opp x)(at level 35, right associativity).

(* Des lemmes qui devraient etre dans Util*)

 
(*PolEq is a setoid equality*)

 Lemma PolEq_refl :forall P, P != P.
Proof.
induction P;constructor;trivial;apply ceq_refl.
Qed.

Lemma PolEq_sym: forall P Q, P != Q -> Q != P.
Proof.
induction P; intros;destruct Q;inversion H;constructor;trivial;try apply ceq_sym;trivial.
apply IHP;trivial.
Qed.


Lemma PolEq_transO : forall P, P!=P0-> forall Q, P != Q-> Q != P0.
induction P.
inversion 1;subst.
intros;destruct Q;rename c0 into c2.
inversion H0;constructor;apply ceq_sym;rewrite <- H2;trivial.
inversion H0;constructor;trivial;rewrite <- H2;apply ceq_sym;trivial.
intros H Q;generalize p c H;clear p c H; induction Q;intros;rename c0 into c2.
inversion H;inversion H0;subst;constructor;rewrite <- H9;trivial.
inversion H;inversion H0;subst;constructor;
try rewrite <- H9;trivial; try rewrite H9; auto.
generalize (IHP H6 (PX Q i0 c0) H14); intro.
inversion H1;auto.
apply (IHQ i0 c0).
constructor;[apply ceq_refl|trivial].
apply PolEq_sym;trivial.
Qed.

Lemma PolEq_trans0: forall P Q, P!=P0-> Q != P0 -> P!=Q.
induction P;intros.
destruct Q;inversion H ;inversion H0.
rename c0 into c2;constructor;auto.
rewrite H3;rewrite H6;apply ceq_refl.
constructor;trivial;rewrite H6;trivial.
generalize p c H ;clear p c H ;induction Q;intros;inversion H ;inversion H0;
rename c0 into c2.
constructor;[rewrite H3;rewrite H9;apply ceq_refl|trivial].
subst.
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
constructor;[rewrite H9;trivial|apply IHP;trivial].
rewrite Pplus_comm;constructor;trivial.
apply ceq_sym;rewrite H3;trivial.
apply PolEq_sym;apply IHQ;trivial.
constructor;trivial;apply ceq_refl.
rewrite Pplus_comm;constructor;[rewrite H3;trivial|apply IHP];trivial.
constructor;[apply ceq_refl|trivial].
Qed.

Lemma PX_morph: forall P Q p q i, P!=Q -> p==q -> PX P i p != PX Q i q.
intros P Q p q i H;induction H;intros;constructor;trivial;constructor;trivial.
Qed.



Lemma PolEq_trans: forall P Q  , P!=Q -> forall R,  Q != R -> P !=R.
induction P.
intros;destruct Q;rename c0 into c2.
destruct R;inversion H;inversion H0;subst;constructor;trivial;rewrite H3;trivial.
destruct R;inversion H0;inversion H;subst.
constructor;rewrite H10;trivial.
constructor;[rewrite H12;trivial|apply (@PolEq_transO Q );trivial].
constructor;[rewrite H3;trivial|idtac].
generalize (@PolEq_transO  Q H14 (PX R i (C0 cops)) H8);intro H1;inversion H1;trivial.
constructor;[rewrite H12;trivial|idtac].
generalize  (@PolEq_transO  (PX Q i (C0 cops)) );intro H1;apply H1.
constructor;trivial;apply ceq_refl.
apply PolEq_sym;trivial.

(*cas de recursion*) 
intro Q; generalize p c; clear p c; induction Q;intros.
generalize c p c0 H H0 ; clear c p c0 H H0;induction R;intros.
inversion H;inversion H0;constructor;trivial;rewrite H3;trivial.
inversion H ; inversion H0;subst;
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.
constructor;[rewrite H3;trivial|apply PolEq_trans0;trivial].
rewrite Pplus_comm;constructor;[rewrite H3;apply ceq_sym;trivial|apply PolEq_trans0;trivial].
constructor;trivial;apply ceq_refl.
rewrite Pplus_comm;constructor;[rewrite H3;trivial|apply PolEq_trans0;trivial].
constructor;trivial;apply ceq_refl.

generalize p0 c0 p c H H0;clear p0 c0 p c H H0 ;induction R;intros.
inversion H0;constructor;[inversion H;rewrite <- H3;trivial;apply ceq_sym;trivial|idtac].
inversion H.
apply (@PolEq_transO Q);trivial;apply PolEq_sym;trivial.
apply (IHP (PX Q i0 (C0 cops)));trivial;
constructor;trivial;apply ceq_refl.
  rename P0 into P2;
							       rename P1 into P3.
assert (H16:PX P i0 (C0 cops) != P0). apply (@PolEq_transO Q)(**);trivial.
inversion H16;trivial.
rename c0 into c2;rename c1 into c3.
inversion H;subst.
inversion H0;subst.
constructor;[rewrite H3;trivial|apply (IHP Q);assumption].
constructor;[rewrite H3;trivial|apply (IHP Q);trivial].
constructor; [rewrite H3;trivial| trivial].
assert (PX P i (C0 cops) != PX Q i (C0 cops)). constructor;trivial;apply ceq_refl.
apply PolEq_sym;apply (IHR i (C0 cops) i (C0 cops));trivial;apply PolEq_sym;trivial.
subst;inversion H0;subst.
constructor;[rewrite <- H4;trivial|apply (IHP (PX Q i (C0 cops)));trivial].
constructor;trivial;apply ceq_refl.
rewrite Pplus_assoc;constructor;[rewrite H4;trivial|apply (IHP (PX Q i (C0 cops)));trivial].
constructor; trivial;apply ceq_refl.

generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
assert (i0=i). rewrite h in H2;apply (Pplus_reg_r i0 i p);trivial.
constructor;[rewrite <- H3;trivial|apply (IHP (PX Q i (C0 cops)));trivial].
apply PolEq_sym;rewrite <- H1;assumption.
rewrite Pplus_comm;constructor;try rewrite <- H3;trivial.
apply PolEq_sym;apply (IHR p1 (C0 cops) (i+p1)%positive (C0 cops)).
constructor;trivial;apply ceq_refl.
assert ((i+p1)%positive = i0). 
apply (Pplus_reg_r (i+p1) i0 p);rewrite H2.
rewrite <- Pplus_assoc;rewrite h;rewrite (Pplus_comm p1);auto.
rewrite H1;apply PolEq_sym;trivial.
rewrite Pplus_comm;constructor;try (rewrite H3; apply ceq_sym);trivial.
rewrite <- H4;trivial.
apply (IHP (PX Q i (C0 cops)));trivial;rewrite h in H2.
assert ((i0+p1)%positive = i). 
apply (Pplus_reg_r (i0+p1) i p0);
rewrite <- H2; rewrite (Pplus_comm p0);apply sym_equal;apply Pplus_assoc.
rewrite <- H1;constructor;trivial;apply ceq_refl.

inversion H0;subst.
constructor;[rewrite H3;trivial|apply PolEq_sym;apply IHQ;apply PolEq_sym;trivial].
apply PolEq_sym;trivial.

generalize (ZPminus_spec i i0);destruct (ZPminus i i0);intro h;rewrite h.
constructor;[rewrite H4;trivial|subst].
assert (PX R i0 (C0 cops)!= PX P i0 (C0 cops)). apply PolEq_sym;apply IHQ;trivial.
apply PolEq_sym;trivial.
inversion H1;trivial.
apply PolEq_sym;trivial.
generalize (@absurdIplusJ i0 i);intro h;elim h;auto.
generalize (@absurdIplusJ j i);intro h;elim h;auto.
subst.
rewrite <- Pplus_assoc;rewrite (Pplus_comm p);rewrite Pplus_assoc.
rewrite <- (Pplus_comm p);constructor.
rewrite H4;trivial.
assert (PX P (i0 + p) (C0 cops)!= PX R i0 (C0 cops)). apply IHQ;trivial.
apply PolEq_sym;trivial.
inversion H1.
generalize (@absurdIplusJ i0 p);intro h;elim h;auto.
rewrite  Pplus_comm;auto.
generalize (@absurdIplusJ i0 (i+p));intro h;elim h;auto.
rewrite <- Pplus_assoc; rewrite <-(Pplus_comm i0);auto.
subst.
assert (i=p). apply Pplus_reg_r  with i0.
rewrite (Pplus_comm p);trivial.
subst;trivial.
rewrite <- Pplus_assoc;rewrite (Pplus_comm p);rewrite  Pplus_assoc.
rewrite <- (Pplus_comm p);constructor.
rewrite H3;trivial.
subst.
assert (PX P i (C0 cops)!= PX R (i + p) (C0 cops)).
 apply IHQ;trivial; apply PolEq_sym;trivial.
inversion H1.
generalize (@absurdIplusJ i p);intro h;elim h;auto.
rewrite  Pplus_comm;auto.
assert (i0 = p);[idtac|subst;trivial].
rewrite Pplus_comm in H11; apply (Pplus_reg_l i);auto.
rewrite (Pplus_comm i0)  in H11. rewrite <- Pplus_assoc in H11.
generalize (@absurdIplusJ j (i0 + p));intro h;elim h;auto.
rewrite Pplus_comm;auto.
rewrite Pplus_assoc;constructor;[rewrite H3;trivial|apply PolEq_sym; apply (IHR (i + i0)%positive  (C0 cops) i0 (C0 cops))].
constructor; trivial;try apply ceq_refl.
apply PolEq_sym;trivial.
Qed.



(* Pol_Eq est une relation d'equivalence sur Pol *)

Lemma PolEq_trans1 : forall P Q R, P != Q -> Q != R -> P != R.
  Proof.
    intros.
    apply PolEq_trans with Q;assumption.
  Qed.


Definition Pol_Eq_Relation_Class : Relation_Class.
 eapply (@SymmetricReflexive unit _ Pol_Eq).
 exact PolEq_sym.
 exact PolEq_refl.
Defined.

Add Relation Pol Pol_Eq
 reflexivity proved by PolEq_refl
 symmetry proved by PolEq_sym
 transitivity proved by PolEq_trans1
 as Pol_Eq_relation.

(* PX est un morphisme *)
Add Morphism (@PX Coef) with signature Pol_Eq ==> (@eq positive) ==> ceq ==> Pol_Eq as PX_Morphism.
  intros P Q i j p q.
  apply PX_morph;assumption.
Qed.

(* On remplace les setoid par des relations : ca permet de declarer
  des morphismes qui ont des arguments dans des "setoids" differents,
  et de donner la signature *)



(* Pc est un morphisme*)
Add Morphism (@Pc Coef)  with signature ceq ==> Pol_Eq as Pc_Morphism.
intros;constructor;trivial.
Qed.


Lemma  Padd_0_l    : forall x, P0 + x != x.
intros x ;case x;simpl;intros;rewrite cadd_0_l;apply PolEq_refl.
Qed.


Ltac case_c0_test c := caseEq(czero_test c);intro;[assert (c== (C0 cops));[apply c0test_c;trivial|idtac]|idtac].


Lemma mkPX_PX: forall P  i c c', c == c'  -> mkPX P i c != PX P i c'.
induction P;intros;simpl;case_c0_test c;constructor;trivial;try apply PolEq_refl.
rewrite H1;apply PolEq_refl.
rewrite H1;apply PolEq_refl.
Qed.

Lemma mkPX_PX_c: forall P c p , mkPX P p c!= PX P p c.
intros;apply mkPX_PX; apply ceq_refl.
Qed.

Lemma mkPX_ok: forall P Q i c c', c == c' -> P!=Q -> mkPX P i c != mkPX Q i c'.
intros;apply PolEq_trans with (PX P i c).
apply mkPX_PX_c.
apply PolEq_trans with (PX Q i c').
constructor;trivial.
apply PolEq_sym;apply mkPX_PX_c.
Qed.

Lemma mkPX_morph : forall P Q i c c', P!=Q -> c == c' ->
  mkPX P i c != mkPX Q i c'.
  Proof.
    intros.
    apply mkPX_ok;assumption.
  Qed.
    

Add Morphism mkPX with signature Pol_Eq ==> (@eq positive) ==> ceq ==> Pol_Eq as mkPX_Morphism.
  intros P Q i j p q.
  apply mkPX_morph;assumption.
Qed.



Lemma mkPXP_PXQ: forall P Q i c c', c == c'  -> P!= Q -> mkPX P i c != PX Q i c'.
intros;apply PolEq_trans with (mkPX Q i c).
apply mkPX_ok;trivial;apply ceq_refl.
apply mkPX_PX;trivial.
Qed.

 
Lemma  Padd_sym    : forall x y, x + y != y + x.
induction x.
simpl;destruct y;simpl;constructor;try setoid ring;try apply PolEq_refl.
intro y; generalize p c;clear p c;induction y.
simpl;intros;constructor;try setoid ring;try apply PolEq_refl.
intros p0 c2;generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.

simpl;rewrite (ZPminus0).
rewrite IHx;rewrite cadd_sym; apply PolEq_refl.
simpl;rewrite (ZPminusneg);rewrite (ZPminuspos).
apply mkPX_ok;[apply cadd_sym|rewrite <- IHx].
case x.
simpl;intro c3.
rewrite cadd_0_r;apply PolEq_refl.
intros p2 p3 c3;simpl;caseEq (ZPminus p3 p1 );intros;
 rewrite cadd_0_r;apply PolEq_refl.
simpl;rewrite ZPminuspos;rewrite ZPminusneg.
rewrite cadd_sym;rewrite IHy.
apply mkPX_ok;try setoid ring.
case y;simpl;intros ; rename c0 into c3;try rewrite cadd_0_r;try apply PolEq_refl.
caseEq (ZPminus p3 p1 );intros;rewrite cadd_0_r;try apply PolEq_refl.
Qed.

Lemma  Padd_0_r   : forall x, x+P0 != x.
intros;rewrite Padd_sym;apply Padd_0_l.
Qed.

Lemma PaddC_morph : forall P Q p q, P!=Q-> p==q->Pol_addC P p != Pol_addC Q q.
intros P Q p q H H0;inversion H;simpl;
rewrite H1;rewrite H0;try apply PolEq_refl;constructor;trivial;setoid ring.
Qed.


Add Morphism Pol_addC with signature Pol_Eq ==> ceq ==> Pol_Eq as PaddC_Morphism.
intros;apply PaddC_morph;assumption.
Qed.


Lemma  Padd_P0_r    : forall  x P, P != P0 ->  x+P != x.
induction  x;intros.
simpl;destruct P;simpl;inversion H;rename c0 into c2;rewrite H2;rewrite cadd_0_r;
try apply PolEq_refl;subst;constructor;try setoid ring;trivial.
generalize p c ;clear p c;induction P;intros p0 c2 ;inversion H.
simpl;rewrite H2;rewrite cadd_0_l.
apply PolEq_refl.
subst.
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl;rewrite ZPminuspos|rewrite Padd_sym;simpl;rewrite ZPminuspos].
rewrite H2;rewrite cadd_0_r;rewrite IHx;trivial.
apply mkPX_PX_c.
rewrite H2;rewrite cadd_0_r;rewrite IHP;trivial.
rewrite mkPX_PX_c.
rewrite Pplus_comm;constructor;try setoid ring;apply PolEq_refl.
rewrite H2;rewrite cadd_0_l;rewrite mkPX_PX_c.
rewrite Padd_sym;rewrite (IHx (PX P p1 c0 ));try apply PolEq_refl.
constructor;trivial;setoid ring.
Qed.

Lemma  Padd_P0_l   : forall  x P, P != P0 ->  P +x!= x.
intros;rewrite Padd_sym;apply Padd_P0_r;auto.
Qed.

Lemma Padd_ext_l : forall P Q R, P!=Q -> P+R != Q+R.
intros P Q R H;generalize R;clear R;induction H.

intros R; repeat rewrite <- (Padd_sym R);simpl;rewrite H;apply PolEq_refl.
intros R;generalize p q H i ;clear p q H i;induction R;intros.
simpl;rewrite H;rewrite cadd_sym;constructor;trivial;setoid ring.
generalize (ZPminus_spec i p);destruct (ZPminus i p);intro h;rewrite h;
[simpl;rewrite H;rewrite ZPminus0|simpl;rewrite H;rewrite ZPminuspos|
idtac].
rewrite mkPX_PX_c;rewrite Padd_P0_l;trivial;apply PolEq_refl.
rewrite mkPX_PX_c;rewrite Padd_P0_l; try apply PolEq_refl.
constructor;trivial;setoid ring.
rewrite (Padd_sym (PX P i q));simpl;rewrite H;rewrite ZPminuspos.
rewrite mkPX_PX_c;rewrite cadd_sym;rewrite Pplus_comm;
constructor;try setoid ring;trivial.
rewrite Padd_sym;rewrite IHPol_Eq;try apply PolEq_refl.
apply Padd_P0_l;apply PolEq_refl.


intro R;generalize p q H i;clear p q H i;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply cadd_sym|idtac].
generalize (ZPminus_spec i p);destruct (ZPminus i p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl; rewrite ZPminuspos|idtac];repeat rewrite mkPX_PX_c.

rewrite H;rewrite IHPol_Eq; rewrite Padd_P0_l;apply PolEq_refl.
rewrite H;rewrite( IHR c0 c0);try apply ceq_refl;rewrite Padd_P0_l;try apply PolEq_refl.
rewrite Padd_sym;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c.
rewrite H;rewrite Pplus_comm;constructor;try setoid ring.

apply Padd_P0_r;trivial.
intro R;generalize p q H i ;clear p q H i ;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply ceq_refl|idtac].
generalize (ZPminus_spec i p);destruct (ZPminus i p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl; rewrite ZPminuspos|idtac];repeat rewrite mkPX_PX_c;
try rewrite H;try rewrite IHPol_Eq;try apply PolEq_refl.
rewrite (IHR c0 c0);try apply ceq_refl;apply PolEq_refl.
repeat rewrite <- (Padd_sym (PX R (i + p1) c ));simpl;rewrite ZPminuspos;repeat 
rewrite mkPX_PX_c;rewrite H.
repeat rewrite (Padd_sym (PX R p1 c0 ));rewrite  IHPol_Eq; apply PolEq_refl.
intro R; generalize p q j H;clear p q j H;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply ceq_refl|idtac].
generalize (ZPminus_spec j p);destruct (ZPminus j p);intro h;try rewrite h.
simpl;rewrite ZPminus0;rewrite Pplus_comm;rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;rewrite H.
rewrite IHPol_Eq;apply PolEq_refl.
simpl;rewrite ZPminuspos.
rewrite Pplus_assoc;rewrite (Pplus_comm i);simpl; rewrite <- Pplus_assoc; rewrite ZPminuspos.
repeat rewrite mkPX_PX_c;rewrite H.
rewrite (IHR c0 c0);try apply ceq_refl;apply PolEq_refl.
rewrite Padd_sym;simpl Pol_add at 1;rewrite ZPminuspos.
generalize (ZPminus_spec i p1);destruct (ZPminus i p1);intro h1;try rewrite h1.

rewrite Pplus_comm;simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;rewrite H.
rewrite Pplus_comm;constructor;[setoid ring|rewrite Padd_sym;rewrite  IHPol_Eq].
rewrite h1;simpl;rewrite ZPminus0;rewrite mkPX_PX_c;rewrite cadd_0_l;apply PolEq_refl.

rewrite <- (Pplus_comm j); rewrite Pplus_assoc;simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.

rewrite H;rewrite Pplus_comm;constructor;try setoid ring.

rewrite Padd_sym; rewrite IHPol_Eq .
rewrite h1;simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
rewrite cadd_0_l;apply PolEq_refl.
rewrite Pplus_assoc;rewrite (Pplus_comm i j).

rewrite (Padd_sym (PX P (j + i) p0));simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;rewrite H.
rewrite (Pplus_comm j i);constructor;try setoid ring.

rewrite Padd_sym;rewrite IHPol_Eq;rewrite Padd_sym;simpl ;rewrite ZPminuspos.
rewrite mkPX_PX_c;rewrite  cadd_0_l;apply PolEq_refl.

intro R;generalize j p q H;clear j p q H;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply ceq_refl|idtac].
generalize (ZPminus_spec j p);destruct (ZPminus j p);intro h;try rewrite h.
simpl Pol_add at 2;rewrite ZPminus0;simpl;rewrite Pplus_comm;rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;rewrite H;rewrite <- IHPol_Eq;apply PolEq_refl.
rewrite Pplus_comm;rewrite <- Pplus_assoc;simpl;repeat rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;rewrite H;rewrite Pplus_comm.
rewrite (IHR p1 c0 c0);try apply ceq_refl;apply PolEq_refl.
rewrite (Padd_sym (PX Q j q ));simpl Pol_add at 2;rewrite ZPminuspos;rewrite Pplus_comm.
generalize (ZPminus_spec i p1);destruct (ZPminus i p1);intro h1;try rewrite h1.

simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;rewrite H.
rewrite Pplus_comm;constructor;[setoid ring|idtac].

rewrite Padd_sym;rewrite IHPol_Eq;rewrite h1;simpl;rewrite ZPminus0; 

rewrite mkPX_PX_c; rewrite cadd_0_l;apply PolEq_refl.
rewrite Pplus_assoc;simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;rewrite H;
rewrite Pplus_comm;constructor;try setoid ring.
rewrite Padd_sym;rewrite IHPol_Eq;rewrite h1;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;
rewrite cadd_0_l;apply PolEq_refl.

rewrite Pplus_assoc;rewrite (Padd_sym( PX P (j + i) p0 ));simpl;rewrite ZPminuspos;

repeat rewrite mkPX_PX_c;rewrite Pplus_comm;rewrite H.
constructor;try setoid ring.
rewrite Padd_sym;
rewrite IHPol_Eq;rewrite Padd_sym;simpl;rewrite ZPminuspos;
rewrite mkPX_PX_c;rewrite  cadd_0_l;apply PolEq_refl.

Qed.

Lemma Padd_ext_r : forall P Q R, P!=Q -> R+P != R+Q.
intros;repeat rewrite (Padd_sym R);apply Padd_ext_l;trivial.
Qed.

Lemma Padd_ext : forall P Q R S, P!=Q-> R!=S -> P+R!=Q+S.
intros;apply PolEq_trans with (Q+R).
apply Padd_ext_l;trivial.
apply Padd_ext_r;trivial.
Qed.

(*
*)


Add Morphism Pol_add with signature Pol_Eq ==> Pol_Eq ==>  Pol_Eq as Pol_add_Morphism.
  intros P Q H P' Q'.
  apply Padd_ext;assumption.
Qed.



Lemma Pol_addC_mkPX: forall c c' P i, Pol_addC (mkPX P i c') c  != mkPX P i (c' ++ c).
intros;destruct P;simpl;
case (czero_test c0);simpl;
constructor;
try apply ceq_refl;try apply PolEq_refl;try apply cadd_sym.
Qed.

Lemma   Padd_assoc1 : forall z y x, x + (y + z) != (x + y) + z.
induction z. destruct y. destruct x. 

simpl;rewrite cadd_assoc;apply PolEq_refl.
simpl;constructor;try setoid ring;apply PolEq_refl.

destruct x.

simpl;constructor;try setoid ring ;apply PolEq_refl.
rename c0 into c2; rename c1 into c3.

generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
simpl;rewrite ZPminus0.
rewrite  Pol_addC_mkPX;repeat rewrite mkPX_PX_c;

constructor;[setoid ring| apply PolEq_refl].

simpl; rewrite ZPminuspos;rewrite  Pol_addC_mkPX;repeat rewrite mkPX_PX_c;

constructor;[setoid ring| apply PolEq_refl].

simpl Pol_add at 2;repeat rewrite (Padd_sym (PX x p0 c3));
simpl ;rewrite ZPminuspos;rewrite  Pol_addC_mkPX;repeat rewrite mkPX_PX_c;

constructor;[setoid ring| apply PolEq_refl].

intro y; generalize p c;clear p c;induction y;intros.
destruct x.

simpl;constructor;[setoid ring|apply PolEq_refl].
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h;
[simpl;rewrite ZPminus0 | simpl;rewrite ZPminuspos|idtac];try (repeat rewrite mkPX_PX_c;constructor;
[setoid ring|apply PolEq_refl]).
rewrite (Padd_sym (PX x p0 c1 )); rewrite (Padd_sym  (PX x p0 c1 + Pc c )(PX z (p0 + p1) c0));
simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl].

generalize p c p0 c0; clear p c p0 c0;induction x;intros.
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h;
simpl;[rewrite ZPminus0| rewrite ZPminuspos| rewrite ZPminusneg];try (rewrite Padd_sym;simpl;rewrite  Pol_addC_mkPX;
repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl]).

generalize (ZPminus_spec p0 p1);destruct (ZPminus p0 p1);intro h;rewrite h.
simpl Pol_add at 2;rewrite ZPminus0;repeat rewrite mkPX_PX_c.
generalize (ZPminus_spec p p1);destruct (ZPminus p p1);intro h1;rewrite h1.
simpl Pol_add at 1;rewrite ZPminus0;simpl Pol_add at 4;rewrite ZPminus0;
repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0; repeat rewrite mkPX_PX_c;constructor;[apply cadd_assoc|apply IHz].
simpl Pol_add at 1;rewrite ZPminuspos.
simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0; rewrite mkPX_PX_c;constructor;[apply cadd_assoc|apply IHz].

rewrite Padd_sym;simpl Pol_add at 1;rewrite ZPminuspos.
rewrite (Padd_sym(PX x p c )); simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
rewrite <- (Padd_sym (PX z (p + p2) c1));simpl; rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;constructor;try setoid ring.
rewrite (Padd_sym (PX z p2 (C0 cops) ));rewrite (Padd_sym (PX y p2 (C0 cops))).
rewrite <- IHx;rewrite Padd_sym;apply Padd_ext_r.
simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl].

repeat rewrite (Padd_sym ( PX x p c)).
simpl Pol_add at 2;simpl Pol_add at 3;rewrite ZPminuspos;rewrite mkPX_PX_c.
generalize (ZPminus_spec p1 p);destruct (ZPminus p1 p);intro h1;rewrite h1.
simpl Pol_add at 1;rewrite ZPminus0.
simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.

simpl;rewrite ZPminus0;rewrite mkPX_PX_c;constructor;try setoid ring.

rewrite <- (Padd_sym x). rewrite IHz . apply Padd_ext_l;apply Padd_sym.
rewrite <- Pplus_assoc;simpl Pol_add at 1; repeat rewrite ZPminuspos.

simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.

rewrite <- (Padd_sym (PX z (p + p3) c1)) ;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c.
constructor;try setoid ring.
rewrite (Padd_sym (PX z p3 (C0 cops) )).
rewrite (Padd_sym(PX y (p3 + p2) (C0 cops))).

rewrite <- IHx.
rewrite Padd_sym;apply Padd_ext_r.

simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl].

rewrite Padd_sym; simpl Pol_add at 1;rewrite ZPminuspos.
generalize (ZPminus_spec p2 p3);destruct (ZPminus p2 p3);intro h2;rewrite h2.
simpl Pol_add at 4;rewrite ZPminus0;repeat rewrite mkPX_PX_c.

simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;constructor;[setoid ring|auto].

rewrite IHz; apply Padd_ext_l.

simpl;rewrite ZPminus0;rewrite mkPX_PX_c;constructor;[setoid ring|apply Padd_sym].

rewrite Pplus_assoc;simpl Pol_add at 4;rewrite ZPminuspos.
simpl  Pol_add at 4;repeat rewrite mkPX_PX_c.
simpl;

rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[setoid ring|auto].

rewrite IHz;apply Padd_ext_l.

rewrite Padd_sym;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl].
rewrite Pplus_assoc;rewrite (Padd_sym (PX y (p1 + p2) c0)); simpl Pol_add at 4;rewrite ZPminuspos.
repeat rewrite mkPX_PX_c;simpl Pol_add at 3; rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[setoid ring| auto].

rewrite  IHz; apply Padd_ext_l.

simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl].
rewrite (Padd_sym (PX y p0 c0));simpl Pol_add at 2;rewrite ZPminuspos;rewrite mkPX_PX_c.

generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h1;rewrite h1.
simpl Pol_add at 1;rewrite ZPminus0;rewrite mkPX_PX_c.
simpl Pol_add at 4;rewrite ZPminus0.

rewrite mkPX_PX_c;rewrite <- (Padd_sym (PX z (p0 + p2) c1));simpl;rewrite ZPminuspos.
rewrite mkPX_PX_c;constructor;[setoid ring|auto].
rewrite <- (Padd_sym y); rewrite IHy;rewrite <- (Padd_sym (x+y));apply PolEq_refl.

simpl Pol_add at 1;rewrite ZPminuspos;rewrite mkPX_PX_c.
simpl Pol_add at 4;rewrite ZPminuspos;rewrite mkPX_PX_c.

rewrite (Padd_sym (PX (Pol_add (PX x p3 (C0 cops)) y) p0 (Cadd cops c c0))).
simpl Pol_add at 3;rewrite ZPminuspos.
rewrite mkPX_PX_c;constructor;[setoid ring|auto].
 rewrite <- ( Padd_sym y);rewrite (Padd_sym (PX z p2 (C0 cops)) (PX x p3 (C0 cops) + y)).
rename c0 into c2.

rewrite IHy;apply PolEq_refl.
rewrite Padd_sym;simpl Pol_add at 1; rewrite ZPminuspos;rewrite mkPX_PX_c.
rewrite (Padd_sym ( PX x p c ));simpl Pol_add at 4;rewrite ZPminuspos;rewrite mkPX_PX_c.
rename c0 into c2.
rewrite (Padd_sym (PX (PX y p3 c0 + x) p (c2 ++ c) )); simpl Pol_add at 3.
rewrite <- Pplus_assoc;rewrite ZPminuspos.

rewrite mkPX_PX_c;constructor;[setoid ring|auto].

rewrite <- (Padd_sym( PX y p3 c0 + x));rewrite (Padd_sym (PX y p3 c0 ) x).

rewrite <- IHx; rewrite <- (Padd_sym x);apply Padd_ext_r.
rewrite (Padd_sym (PX y p3 c0 )); simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;try setoid ring;apply PolEq_refl.

Qed.

 Lemma   Padd_assoc: forall x y z, x + (y + z) != (x + y) + z.
intros;apply Padd_assoc1.
Qed.


 Lemma  Pmul_1_l    : forall x, P1* x != x.

induction x;simpl;unfold Pol_mul_Rat ;
case_c0_test c. constructor; rewrite H0;setoid ring.
case_c0_test  (c -- c1); [assert (H2:c==c1);[ apply copp_eq;trivial|rewrite H2]|idtac].
apply PolEq_refl.
simpl;constructor;setoid ring.
rewrite mkPX_PX_c;rewrite Padd_0_r.
rewrite H0;rewrite IHx; apply PolEq_refl.
rewrite mkPX_PX_c;case_c0_test (c -- c1). assert (H2:c==c1). apply copp_eq;trivial.
simpl;rewrite IHx;rewrite H2;rewrite cadd_0_r;apply PolEq_refl.
simpl.
rewrite IHx;constructor;try setoid ring;apply PolEq_refl.

Qed.

Lemma Pmul_Rat_aux_c0 : forall P, Pol_mul_Rat_aux P c0 != P0.
induction P;simpl.

constructor;setoid ring.
rewrite mkPX_PX_c;constructor;[setoid ring| apply IHP].

Qed.

Lemma Pmul_Rat_aux_c1 : forall P, Pol_mul_Rat_aux P c1 != P.
induction P;simpl.

constructor;setoid ring.
rewrite mkPX_PX_c;constructor;[setoid ring| apply IHP].

Qed.

Lemma Pmul_Rat_aux_P0 : forall P c, P!=P0 -> Pol_mul_Rat_aux P c != P0.

induction P;intros;simpl;inversion H;rewrite H2;repeat rewrite mkPX_PX_c;
constructor;try setoid ring;auto.

Qed.

Lemma Pmul_Rat_aux_compc: forall P Q , P!=Q-> forall c, Pol_mul_Rat_aux P c != Pol_mul_Rat_aux Q c.

intros P Q H;induction H;intros;simpl;rewrite H;try apply PolEq_refl.
rewrite IHPol_Eq;rewrite Pmul_Rat_aux_P0; try apply PolEq_refl.
rewrite mkPX_PX_c;constructor;try setoid ring; try apply PolEq_refl.
rewrite IHPol_Eq;rewrite Pmul_Rat_aux_P0; try apply PolEq_refl.
rewrite mkPX_PX_c;constructor;try setoid ring; try apply PolEq_refl.
rewrite IHPol_Eq; try apply PolEq_refl.
repeat rewrite mkPX_PX_c;constructor;[setoid ring|auto].

rewrite IHPol_Eq;simpl.
rewrite mkPX_PX_c;constructor;[apply cmul_0_l|apply PolEq_refl].

repeat rewrite mkPX_PX_c;constructor;[setoid ring|auto].

rewrite IHPol_Eq;simpl.
rewrite mkPX_PX_c;constructor;[apply cmul_0_l|apply PolEq_refl].
Qed.

Lemma Pmul_Rat_aux_compP : forall P  c c', c==c' ->Pol_mul_Rat_aux P c != Pol_mul_Rat_aux P c'.
induction P;intros;simpl.
constructor;rewrite H;apply ceq_refl.
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|apply IHP;trivial].
Qed.

Lemma Pmul_Rat_aux_comp: forall P Q , P!=Q-> forall c c', c==c' ->Pol_mul_Rat_aux P c != Pol_mul_Rat_aux Q c'.
intros;apply PolEq_trans with (Pol_mul_Rat_aux P c').
apply Pmul_Rat_aux_compP;trivial.
apply Pmul_Rat_aux_compc;trivial.
Qed.

Add Morphism Pol_mul_Rat_aux with signature Pol_Eq ==> ceq ==>  Pol_Eq as Pmul_Rat_aux_Morphism.
  intros P Q H c c'.
  apply Pmul_Rat_aux_comp;assumption.
Qed.



Lemma Pmul_Rat_aux_assoc : forall P c c' , Pol_mul_Rat_aux (Pol_mul_Rat_aux P c) c' != Pol_mul_Rat_aux P (c**c').
induction P;intros;simpl.
constructor;rewrite cmul_assoc;apply ceq_refl.
 rewrite (@Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux P c0) p (c ** c0)) (PX(Pol_mul_Rat_aux P c0) p (c ** c0))).
apply  mkPX_PX_c.

simpl;repeat rewrite mkPX_PX_c;constructor;[setoid ring|auto].

Qed.

Lemma Pmul_Rat_aux_distr: forall P Q  c , Pol_mul_Rat_aux (P + Q) c != Pol_mul_Rat_aux P c + Pol_mul_Rat_aux Q c.
intros P Q; generalize P ;clear P;induction Q;intros;rename c0 into c2.
simpl.

induction P;simpl;rename c0 into c3.
constructor; setoid ring.
rewrite Pol_addC_mkPX;repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl].

generalize c p ;clear c p ; induction P;intros.

simpl;repeat rewrite mkPX_PX_c;simpl;constructor;[setoid ring|apply PolEq_refl].

generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intros h;rewrite h.
simpl;rewrite ZPminus0.
repeat rewrite mkPX_PX_c.

simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;constructor;try setoid ring;auto.
rename c0 into c3.
simpl;rewrite ZPminuspos.

repeat rewrite mkPX_PX_c.

simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;constructor;try setoid ring.

rewrite IHQ.
apply Padd_ext_l.

simpl;rewrite mkPX_PX_c;constructor;[setoid ring| apply PolEq_refl].
rewrite Padd_sym.

simpl;rewrite ZPminuspos.
rename c0 into c3; repeat rewrite mkPX_PX_c.
rewrite (Padd_sym (PX (Pol_mul_Rat_aux P c2) p (c ** c2) ));simpl;rewrite ZPminuspos.

repeat rewrite mkPX_PX_c; constructor;[setoid ring|auto].
rewrite Padd_sym;rewrite IHP;rewrite Padd_sym;apply Padd_ext_l;simpl;rewrite mkPX_PX_c;
constructor;[setoid ring|apply PolEq_refl].

Qed.


Lemma Pmul_Rat_distr: forall P Q  c , Pol_mul_Rat (P + Q) c != Pol_mul_Rat P c + Pol_mul_Rat Q c.
intros;unfold Pol_mul_Rat.
case_c0_test c.
rewrite Padd_0_l;apply PolEq_refl.
case_c0_test (c--c1). apply PolEq_refl.
apply Pmul_Rat_aux_distr.
Qed.

Lemma Pmul_Rat_compc: forall P Q , P!=Q-> forall c, Pol_mul_Rat P c != Pol_mul_Rat Q c.
intros P Q H;induction H;intros;unfold Pol_mul_Rat;case_c0_test c;try apply PolEq_refl;
case_c0_test (c--c1);(try constructor);trivial;
apply Pmul_Rat_aux_comp;try apply ceq_refl;try constructor;trivial.
Qed.

Lemma Pmul_Rat_compP: forall P c c', c==c'->Pol_mul_Rat P c != Pol_mul_Rat P c'.
induction P;intros.
 unfold Pol_mul_Rat;simpl;case_c0_test c0.
case_c0_test c'.
apply PolEq_refl.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
rename c0 into c2.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H1; rewrite <- H5;trivial].

rename c0 into c2;simpl;constructor;rewrite <- H;rewrite H1;setoid ring.
rename c0 into c2.

case_c0_test (c2--c1).  assert (c2==c1). apply copp_eq;trivial.
case_c0_test c'.
absurd (c0==c1). 
apply c0_diff_c1. rewrite <- H5; rewrite <- H;trivial.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
constructor;apply ceq_refl.

simpl;constructor;rewrite <- H;rewrite H3;setoid ring.

case_c0_test c'.

simpl;constructor;rewrite H;rewrite H3;setoid ring.

case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.

simpl;constructor; rewrite H;rewrite H5;setoid ring.
simpl;constructor;rewrite H;setoid ring.

rename c0 into c2.
unfold Pol_mul_Rat.
case_c0_test c2.
case_c0_test c'.
apply PolEq_refl.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H1; rewrite <- H5;trivial].

simpl;rewrite mkPX_PX_c;simpl;constructor;rewrite <- H;rewrite H1;try setoid ring.

apply Pmul_Rat_aux_c0.
case_c0_test (c2--c1).  assert (c2==c1). apply copp_eq;trivial.
case_c0_test c'.
absurd (c0==c1). apply c0_diff_c1. rewrite <- H5; rewrite <- H;trivial.
case_c0_test (c'--c1). 
apply PolEq_refl.

simpl;rewrite mkPX_PX_c; constructor;rewrite <- H;rewrite H3;try setoid ring.
apply  PolEq_sym;apply Pmul_Rat_aux_c1.

case_c0_test c'.

simpl;rewrite mkPX_PX_c;constructor;rewrite H;rewrite H3;try setoid ring.

apply Pmul_Rat_aux_c0.
case_c0_test (c'--c1). 
assert (c'==c1). apply copp_eq;trivial.
rewrite H;rewrite H5;apply Pmul_Rat_aux_c1.
rewrite H;apply PolEq_refl.
Qed.

Lemma Pmul_Rat_comp: forall P Q , P!=Q-> forall c c', c==c'->Pol_mul_Rat P c != Pol_mul_Rat Q c'.
intros ;apply PolEq_trans with (Pol_mul_Rat P c').
apply  Pmul_Rat_compP;trivial.
apply  Pmul_Rat_compc;trivial.
Qed.



Add Morphism Pol_mul_Rat with signature Pol_Eq ==> ceq ==>  Pol_Eq as Pmul_Rat_Morphism.
  intros P Q H c c'.
  apply Pmul_Rat_comp;assumption.
Qed.

Lemma Pmul_Rat_c0 : forall P, Pol_mul_Rat P c0 != P0.
intro P;unfold Pol_mul_Rat.
rewrite c0test_c0;apply PolEq_refl.
Qed.
Lemma Pmul_Rat_P0 : forall c, Pol_mul_Rat P0 c != P0.
intros;unfold Pol_mul_Rat;simpl.
case_c0_test c.
 apply PolEq_refl.
case_c0_test (c -- c1);try apply PolEq_refl.
constructor;setoid ring.
Qed.





Lemma Pmul_Rat_c1 : forall P, Pol_mul_Rat P c1 != P.
induction P;unfold Pol_mul_Rat;
case_c0_test (C1 cops). absurd (c0 == c1);[apply c0_diff_c1|apply ceq_sym;trivial].
case_c0_test (c1 -- c1);try apply PolEq_refl.
simpl;constructor;setoid ring.
absurd (c0 == c1);[apply c0_diff_c1|apply ceq_sym;trivial].
case_c0_test (c1 -- c1);try apply PolEq_refl.
simpl.
rewrite mkPX_PX_c; generalize IHP; unfold Pol_mul_Rat;
rewrite H; rewrite H0;intro H1;rewrite H1;constructor; try setoid ring ; apply PolEq_refl.
Qed.




Lemma  Pmul_ext_l    : forall P Q x, P!=Q -> P* x != Q*x.
intros P Q x ; generalize P Q; clear P Q;induction x;intros;simpl.
unfold Pol_mul_Rat;case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1);[apply copp_eq |idtac];auto.
rewrite H;apply PolEq_refl.
rewrite (IHx P Q);trivial;rewrite H;apply PolEq_refl.
Qed.

Lemma  Pmul_0_r  : forall x, x * P0!= P0.
destruct x;simpl;
unfold Pol_mul_Rat;
(assert (h: czero_test c0=true );[apply c0test_c0|rewrite h];apply PolEq_refl).
Qed.


Lemma  Pmul_P0_r  : forall x P , P!=P0 -> x * P!= P0.
intros x P;generalize x;clear x;induction P;intros;simpl;
unfold Pol_mul_Rat;inversion H.
case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1);[apply copp_eq |idtac];auto.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H2;trivial].
rewrite H2;apply Pmul_Rat_aux_c0.
rewrite mkPX_PX_c;case_c0_test c.

rewrite Padd_0_r.
constructor;[apply ceq_refl|auto].

case_c0_test (c -- c1). assert (c==c1);[apply copp_eq |idtac];auto.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H2;trivial].

rewrite IHP;trivial.
rewrite H2;rewrite Pmul_Rat_aux_c0.
apply  Padd_P0_l;constructor;try setoid ring;trivial.
constructor;try setoid ring.

Qed.

Lemma  Pmul_P0_l  : forall x P , P!=P0 -> P*x!= P0.
intros x P;generalize x;clear x;induction P;intros;simpl.
generalize c H;clear c H; induction x;intros c2 H.
simpl.
inversion H; rewrite H2.
unfold Pol_mul_Rat;subst;case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1);auto.

constructor;setoid ring.
simpl;constructor;setoid ring.

simpl.

rewrite IHx;trivial.
rewrite mkPX_PX_c;rewrite Padd_P0_l.
constructor;try setoid ring;try PolEq_refl.
constructor;try setoid ring.
unfold Pol_mul_Rat.

case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1);trivial.
simpl.

inversion H;rewrite H4;constructor;setoid ring.

generalize p c H;clear p c H;induction x;intros;simpl;unfold Pol_mul_Rat;case_c0_test c.
apply PolEq_refl.

rename c0 into c2;case_c0_test (c -- c1);trivial.
rewrite H;apply Pmul_Rat_aux_P0; try apply PolEq_refl.
rename c0 into c2;inversion H;rewrite mkPX_PX_c;rewrite Padd_0_r;rewrite IHx;
constructor;trivial; try apply PolEq_refl;try setoid ring.
rename c0 into c2;rewrite mkPX_PX_c;case_c0_test (c -- c1);trivial.

rewrite Padd_P0_r;trivial.
constructor;[apply ceq_refl|auto].
simpl.
rewrite Padd_P0_l.
constructor;[apply ceq_refl|auto].
rewrite mkPX_PX_c;constructor;[inversion H;subst|auto].
rewrite H4;apply cmul_0_l.
inversion H;apply Pmul_Rat_aux_P0;trivial.
Qed.

Lemma  Pmul_ext_r   : forall P Q x, P!=Q -> x*P != x*Q.
intros P Q x H;generalize x;clear x;induction H;intros;simpl.

rewrite H;apply PolEq_refl.
rewrite H;rewrite IHPol_Eq ;rewrite Padd_P0_l;try apply PolEq_refl.
rewrite mkPX_PX_c;rewrite Pmul_0_r;
constructor;try setoid ring;apply PolEq_refl.
rewrite H;rewrite IHPol_Eq ;rewrite Padd_P0_l;try apply PolEq_refl.
rewrite mkPX_PX_c;rewrite Pmul_0_r;
constructor;try setoid ring;apply PolEq_refl.
rewrite H;rewrite IHPol_Eq;apply PolEq_refl.
rewrite H;rewrite IHPol_Eq;apply Padd_ext;try apply PolEq_refl.
repeat rewrite mkPX_PX_c;constructor;try setoid ring.
simpl.
rewrite mkPX_PX_c;rewrite Pmul_Rat_c0.
apply Padd_0_r.
rewrite H;repeat rewrite mkPX_PX_c.
apply Padd_ext_l.
rewrite IHPol_Eq;constructor;try setoid ring.
simpl.
rewrite mkPX_PX_c; rewrite Pmul_Rat_c0; apply Padd_0_r.

Qed.

Lemma  Pmul_ext   : forall P Q  R S , P!=Q -> R!=S -> P* R!= Q*S.
intros;apply PolEq_trans with (P*S).
apply Pmul_ext_r;trivial.
apply Pmul_ext_l;trivial.
Qed.


Add Morphism Pol_mul with signature Pol_Eq ==> Pol_Eq ==>  Pol_Eq as Pmul_Morphism.
  intros P Q H P' Q'.
  apply Pmul_ext;assumption.
Qed.


Lemma Pmul_symPc : forall x c, x* (Pc c)!= (Pc c) *x.
induction x.
intros c2;simpl;unfold Pol_mul_Rat;case_c0_test c.
case_c0_test c2.
apply PolEq_refl.
case_c0_test(c2--c1).
rewrite H0;simpl;constructor;setoid ring.
rewrite H0;simpl;constructor;setoid ring.

case_c0_test c2.

case_c0_test(c--c1);rewrite H1.
constructor;setoid ring.
rewrite Pmul_Rat_aux_P0;try apply PolEq_refl.

case_c0_test(c2--c1). assert (c2==c1). apply copp_eq;trivial.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.

rewrite H6;rewrite H3;apply PolEq_refl.
simpl;rewrite H3;simpl;constructor;setoid ring.

case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.

rewrite H4;simpl;constructor;setoid ring.
simpl;constructor;setoid ring.
intros c2; simpl;unfold Pol_mul_Rat;case_c0_test c.

case_c0_test c2.

rewrite Padd_0_r;rewrite mkPX_PX_c;rewrite H2;constructor;
try setoid ring.

rewrite <-  IHx;simpl.
unfold Pol_mul_Rat; rewrite c0test_c0;apply PolEq_refl.
case_c0_test(c2--c1).

assert (H4:c2==c1);[apply copp_eq;trivial|rewrite H4].
rewrite Padd_0_r;rewrite mkPX_PX_c;rewrite H0;constructor;try setoid ring.
rewrite<- IHx;simpl;rewrite Pmul_Rat_c1;apply PolEq_refl.
rewrite Padd_0_r;simpl;repeat rewrite mkPX_PX_c;
rewrite H0; constructor;try setoid ring.
rewrite <- IHx;simpl. 

unfold Pol_mul_Rat;rewrite H1;rewrite H2;apply PolEq_refl.
case_c0_test c2.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.

rewrite H1;  rewrite Padd_0_r; rewrite mkPX_PX_c.
constructor;try setoid ring;try apply PolEq_refl.
rewrite <- IHx;simpl; apply Pmul_Rat_c0.
rewrite H1; rewrite Pmul_Rat_aux_P0; try apply PolEq_refl.
rewrite Padd_0_r; rewrite mkPX_PX_c. 
rewrite Pmul_P0_l; try apply PolEq_refl.
constructor;try setoid ring; apply PolEq_refl.

case_c0_test(c2--c1).
assert (c2==c1). apply copp_eq;trivial.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
simpl;rewrite Pol_addC_mkPX .
rewrite mkPX_PX_c;constructor;[rewrite H3;rewrite cadd_0_l; trivial|rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;rewrite H1;apply PolEq_refl].

simpl;rewrite Pol_addC_mkPX;rewrite mkPX_PX_c;rewrite H3;constructor;try setoid ring.
rewrite <- IHx;simpl;unfold Pol_mul_Rat.
    case_c0_test (C1 cops).
absurd (c0==c1). apply c0_diff_c1. 
apply ceq_sym;trivial.
case_c0_test(c1--c1); try apply PolEq_refl.
rewrite Pmul_Rat_aux_c1; apply PolEq_refl.

case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
simpl;rewrite Pol_addC_mkPX;repeat rewrite mkPX_PX_c.

rewrite H4; constructor;try setoid ring;
rewrite <- IHx;simpl; unfold Pol_mul_Rat; rewrite H0;rewrite H1;apply PolEq_refl.
simpl;rewrite Pol_addC_mkPX;repeat rewrite mkPX_PX_c;constructor; try setoid ring.
rewrite <- IHx;simpl; unfold Pol_mul_Rat; rewrite H0;rewrite H1;apply PolEq_refl.

Qed.

Lemma PX_pq_qp: forall P Q p q c c', c==c'->P != Q->PX (PX P p c0) q c != PX(PX Q q c0) p c'.

intros P Q p q c c' Heqc HeqP;rewrite Heqc ; rewrite HeqP.
generalize (ZPminus_spec q p);destruct (ZPminus q p);intro h;rewrite h;try apply PolEq_refl;
rewrite Pplus_comm;constructor;try setoid ring;
rewrite Pplus_comm;constructor;try setoid ring; apply PolEq_refl.

Qed.


Lemma PX_pq_pq: forall P p q c , PX (PX P p c0) q c != PX P (p +q) c.
intros;constructor;try setoid ring.
apply PolEq_refl.
Qed.



Lemma PX_Padd_r: forall P Q p c, PX (P+Q) p c != PX P p c +  PX Q p c0.
intros;simpl;rewrite ZPminus0;rewrite mkPX_PX_c; 
constructor;[setoid ring|apply PolEq_refl].
Qed.
Lemma PX_Padd_l: forall P Q p c, PX (P+Q) p c != PX P p c0 +  PX Q p c.
intros;simpl;rewrite ZPminus0;rewrite mkPX_PX_c; 
constructor;[setoid ring|apply PolEq_refl].
Qed.


Lemma Pmul_Xpc_Y: forall  x y :Pol, forall p c, (PX y p c) * x!= PX (y*x)p c0 + (Pol_mul_Rat x c).
induction x.

intros y p c2;simpl. unfold Pol_mul_Rat. case_c0_test c. case_c0_test c2.
rewrite Padd_0_r;constructor;try setoid ring; apply PolEq_refl.

case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial.

rewrite H0; rewrite Padd_0_r; constructor;try setoid ring; apply PolEq_refl.
rewrite H0; rewrite Pmul_Rat_aux_P0; try setoid ring; try apply PolEq_refl;
rewrite Padd_0_r; constructor;try setoid ring; apply PolEq_refl.

case_c0_test (c--c1). assert (c==c1). apply copp_eq;trivial. case_c0_test c2.
rewrite H4;rewrite Padd_0_r; apply PolEq_refl.
case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial. simpl.

rewrite H2;rewrite H6;constructor;[setoid ring|apply PolEq_refl].
rewrite H2;simpl;constructor;[setoid ring|apply PolEq_refl].
case_c0_test c2.  rewrite Padd_0_r;simpl;apply mkPX_PX;rewrite H2;apply cmul_0_l.
case_c0_test (c2--c1). assert (h:c2==c1);[ apply copp_eq;trivial|rewrite h];simpl.
rewrite mkPX_PX_c;constructor;try setoid ring ; apply PolEq_refl.
simpl; rewrite mkPX_PX_c;constructor;try setoid ring ; apply PolEq_refl.

(*cas general*)
intros;unfold Pol_mul_Rat; case_c0_test c. 
rename c0 into c2;case_c0_test c2. 
rewrite Padd_0_r;simpl;unfold Pol_mul_Rat;rewrite H;rewrite Padd_0_r;
repeat rewrite mkPX_PX_c.

rewrite Padd_0_r;rewrite IHx.
unfold Pol_mul_Rat;rewrite H1; rewrite Padd_0_r.
 rewrite(@PX_pq_qp (y * x) (y * x)  p0 p c0 c0);try setoid ring;try apply PolEq_refl.

case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial.
simpl Pol_mul;unfold Pol_mul_Rat; rewrite H;rewrite Padd_0_r.

repeat rewrite mkPX_PX_c; rewrite Padd_0_r.
rewrite IHx; rewrite H4;rewrite Pmul_Rat_c1.
rewrite H0; rewrite(@PX_pq_qp (y * x) (y * x)  p p0 c0 c0);try setoid ring;try apply PolEq_refl.
simpl; rewrite ZPminus0; rewrite mkPX_PX_c;
constructor;[setoid ring|apply PolEq_refl].
rewrite H0; simpl; repeat rewrite mkPX_PX_c.
repeat rewrite Pmul_Rat_c0; repeat rewrite Padd_0_r.
rewrite (@PX_pq_qp (y * x) (y * x) p p0 c0 c0); try setoid ring;try apply PolEq_refl.
simpl;rewrite ZPminus0;rewrite mkPX_PX_c.
constructor;[setoid ring|idtac].
generalize (IHx y p0 c2);unfold Pol_mul_Rat; rewrite H1; rewrite H2; auto.
rename c0 into c2.

case_c0_test c2. 
rewrite Padd_0_r;simpl; repeat rewrite mkPX_PX_c.
unfold Pol_mul_Rat;rewrite H.
case_c0_test (c --c1). assert (c==c1). apply copp_eq;trivial.

rewrite IHx; rewrite H1;rewrite Pmul_Rat_c0; rewrite Padd_0_r.
rewrite (@PX_pq_qp (y * x) (y * x) p0 p c0 c0) ;try setoid ring;try apply PolEq_refl.
simpl; rewrite ZPminus0; rewrite mkPX_PX_c.
constructor;[setoid ring|apply PolEq_refl].
simpl; rewrite H1; rewrite mkPX_PX_c.
rewrite cmul_0_l;rewrite IHx; rewrite Pmul_Rat_c0; rewrite Padd_0_r.
rewrite (@PX_pq_qp (y * x) (y * x) p0 p c0 c0) ;try setoid ring;try apply PolEq_refl.
simpl ;rewrite ZPminus0;rewrite mkPX_PX_c.
constructor;[setoid ring|apply PolEq_refl].

case_c0_test (c2 --c1). assert (c2==c1). apply copp_eq;trivial.
simpl Pol_mul; rewrite mkPX_PX_c; unfold Pol_mul_Rat; rewrite H.
case_c0_test (c --c1). assert (c==c1). apply copp_eq;trivial.

rewrite mkPX_PX_c; rewrite IHx.
unfold Pol_mul_Rat;rewrite H0 ;rewrite H1.
assert (h: PX (PX (y * x) p0 c0 + x) p c0 !=PX (PX (y * x) p0 c0 ) p c0 + PX x p c0 ).
simpl; rewrite ZPminus0;rewrite mkPX_PX_c; rewrite cadd_0_l; apply PolEq_refl.
rewrite h.
rewrite (@PX_pq_qp (y * x) (y * x) p0 p c0 c0) ;try setoid ring;try apply PolEq_refl.

rewrite <- Padd_assoc.

assert (h1: PX (PX (y * x) p c0 + y) p0 c0 !=PX (PX (y * x) p c0 ) p0 c0 + PX y p0 c0 ).
simpl; rewrite ZPminus0;rewrite mkPX_PX_c; rewrite cadd_0_l; apply PolEq_refl.
rewrite h1.
rewrite <- Padd_assoc; apply Padd_ext_r.
rewrite H3;rewrite H6;
rewrite Padd_sym; generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h2;rewrite h2;
simpl;[rewrite ZPminus0|rewrite ZPminuspos|rewrite ZPminusneg]; repeat rewrite mkPX_PX_c;
(constructor;[setoid ring|apply PolEq_refl]).
rewrite H3; rewrite mkPX_PX_c.
rewrite IHx; unfold Pol_mul_Rat.
case_c0_test (C1 cops).
absurd (c0==c1);[apply c0_diff_c1| apply ceq_sym;trivial].
case_c0_test(c1--c1).
repeat rewrite PX_Padd_r.
rewrite (@PX_pq_qp (y * x) (y * x) p0 p c0 c0) ;try setoid ring;try apply PolEq_refl.
repeat rewrite <- Padd_assoc.
apply Padd_ext_r.
simpl Pol_mul_Rat_aux; rewrite mkPX_PX_c.
rewrite Padd_sym.
simpl;generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;try rewrite h;
(repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl]).
rewrite Pmul_Rat_aux_c1.
simpl Pol_mul_Rat_aux; rewrite mkPX_PX_c.
repeat rewrite PX_Padd_r.
rewrite (@PX_pq_qp (y * x) (y * x) p0 p c0 c0) ;try setoid ring;try apply PolEq_refl.
repeat rewrite <- Padd_assoc;apply Padd_ext_r.
rewrite Padd_sym;simpl;generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;try rewrite h;
(repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl]).
simpl; repeat rewrite mkPX_PX_c.
rewrite IHx.
repeat rewrite PX_Padd_r.
rewrite (@PX_pq_qp (y * x) (y * x) p0 p c0 c0) ;try setoid ring;try apply PolEq_refl.
repeat rewrite <- Padd_assoc;apply Padd_ext_r.
unfold Pol_mul_Rat; rewrite H;rewrite H0;rewrite H1.

case_c0_test (c --c1). assert (c==c1). apply copp_eq;trivial.


rewrite H4; rewrite Padd_sym;simpl;generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;try rewrite h;
(repeat rewrite mkPX_PX_c;constructor;[setoid ring|apply PolEq_refl]).
simpl Pol_mul_Rat_aux;rewrite mkPX_PX_c.
rewrite Padd_sym;simpl;
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;try rewrite h;
(repeat rewrite mkPX_PX_c;
constructor;[setoid ring|apply PolEq_refl]).

Qed.

Lemma    Pmul_sym    : forall x y, x * y != y * x.
intros x y; generalize x;clear x;induction y.
intros;apply Pmul_symPc.
simpl.
intros;rewrite mkPX_PX_c;rewrite IHy.
rewrite Pmul_Xpc_Y; apply PolEq_refl.
Qed.

Lemma Pmul_Rat_aux_assocP: forall x y c , Pol_mul_Rat_aux (x * y) c != x * Pol_mul_Rat_aux y c.
induction y.
intros;simpl;induction x.
rename c0 into c2.
rename c1 into c3.
simpl;unfold Pol_mul_Rat; case_c0_test c. 
case_c0_test (c**c2). 
apply Pmul_Rat_aux_P0; apply PolEq_refl.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.

absurd (c0==c1);[apply c0_diff_c1|idtac].
rewrite H0 in H4; rewrite <- H4;setoid ring.
rewrite Pmul_Rat_aux_P0; try apply PolEq_refl.
rewrite H0; rewrite cmul_0_l;rewrite Pmul_Rat_aux_c0;apply PolEq_refl.

case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c**c2). 

assert (c2 ==c0). rewrite <- H4; rewrite H2;setoid ring.
rewrite H5;apply Pmul_Rat_aux_c0.

case_c0_test (c**c2--c1). assert (c**c2==c1). apply copp_eq;trivial.

assert(h:c2==c1);[rewrite <- H6; rewrite H2;setoid ring|rewrite h]; apply Pmul_Rat_aux_c1.
rewrite H2;rewrite cmul_1_l;apply PolEq_refl.
case_c0_test( (c ** c2)). simpl.
constructor;rewrite <- cmul_assoc;rewrite H2;setoid ring.

case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.

simpl; constructor;rewrite <- cmul_assoc;rewrite H4;setoid ring.
simpl; constructor;setoid ring.
rename c0 into c2.
rename c1 into c3.

unfold Pol_mul_Rat.
case_c0_test c.
case_c0_test (c**c2). 
apply Pmul_Rat_aux_P0; apply PolEq_refl.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1| generalize H4; rewrite H0;rewrite cmul_0_l;auto].

simpl;rewrite mkPX_PX_c; rewrite H0.
constructor;try setoid ring; rewrite cmul_0_l;apply Pmul_Rat_aux_c0.

case_c0_test (c--c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c ** c2).

simpl;rewrite mkPX_PX_c.  
assert (h:c2==c0);[generalize H4;rewrite H2 ;intro H5; rewrite <- H5;setoid ring|rewrite h].
rewrite Pmul_Rat_aux_c0; constructor; try setoid ring; apply PolEq_refl.

case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
simpl;rewrite mkPX_PX_c.

assert (h :c2==c1); [ rewrite H2 in H6; rewrite <- H6;setoid ring|rewrite h];
rewrite Pmul_Rat_aux_c1;constructor; try setoid ring; apply PolEq_refl.
rewrite H2; rewrite cmul_1_l;apply PolEq_refl.

case_c0_test (c**c2 ).

simpl; rewrite mkPX_PX_c. 
simpl; rewrite mkPX_PX_c; rewrite <- cmul_assoc;rewrite H2.
constructor;try setoid ring.
generalize IHx; unfold Pol_mul_Rat ; rewrite H; rewrite H0; rewrite H1;auto.

case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial. 

repeat (simpl; rewrite mkPX_PX_c).
constructor; try setoid ring.
rewrite <- cmul_assoc; rewrite H4; setoid ring.
generalize IHx; unfold Pol_mul_Rat ; rewrite H; rewrite H0; rewrite H1;rewrite H2;auto.
repeat (simpl; rewrite mkPX_PX_c).
constructor; try setoid ring.
generalize IHx; unfold Pol_mul_Rat ; rewrite H; rewrite H0; rewrite H1;rewrite H2;auto.
intros c2;simpl; repeat rewrite mkPX_PX_c.

rewrite Pmul_Rat_aux_distr.
repeat (simpl;  rewrite mkPX_PX_c).
rewrite IHy.
rewrite cmul_0_l.
apply Padd_ext_r.
unfold Pol_mul_Rat.
case_c0_test c.
case_c0_test (c**c2).
apply Pmul_Rat_aux_P0; apply PolEq_refl.
case_c0_test (c **c2-- c1). assert (c**c2==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1|generalize H4;rewrite H0;rewrite cmul_0_l;trivial].
rewrite H0; rewrite cmul_0_l; rewrite Pmul_Rat_aux_c0; apply Pmul_Rat_aux_P0; apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c**c2). 

assert (h : c2==c0);[rewrite <-H4; rewrite H2;setoid ring| rewrite h]; apply Pmul_Rat_aux_c0.

case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.

assert (h : c2==c1);[rewrite <-H6; rewrite H2;setoid ring| rewrite h]; apply Pmul_Rat_aux_c1.
rewrite H2; rewrite cmul_1_l;apply PolEq_refl.

case_c0_test (c**c2).
rewrite Pmul_Rat_aux_assoc.
rewrite H2; apply Pmul_Rat_aux_c0.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
rewrite Pmul_Rat_aux_assoc; rewrite H4; apply Pmul_Rat_aux_c1.
apply Pmul_Rat_aux_assoc.
Qed.


Lemma Pmul_Rat_Pmul : forall x y c, Pol_mul_Rat (x*y) c != x * Pol_mul_Rat y c.
intros;simpl.
unfold Pol_mul_Rat. case_c0_test c. rewrite Pmul_0_r;apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
apply PolEq_refl.
apply Pmul_Rat_aux_assocP.
Qed.

Lemma Pscal_Pmul_r : forall x c, Pol_mul_Rat x c != x * (Pc c).
intros;simpl; apply PolEq_refl.
Qed.
 Lemma Pscal_aux_Pmul_r : forall x c, Pol_mul_Rat_aux x c != x * (Pc c).
intros;simpl;unfold Pol_mul_Rat;case_c0_test c.
rewrite H0;apply Pmul_Rat_aux_c0.
case_c0_test ( c--c1). assert (c==c1). apply copp_eq;trivial.
rewrite H2;apply Pmul_Rat_aux_c1.
apply PolEq_refl.
Qed.



Lemma Pscal_Pmul_l: forall x c, Pol_mul_Rat x c != (Pc c) * x.
intros; rewrite Pmul_sym;simpl; apply PolEq_refl.
Qed.

Lemma Pmul_assoc_Pc : forall x y c, x * (y * Pc c)!= (x *y) * Pc c.
intros.
simpl.
unfold Pol_mul_Rat. case_c0_test c. apply Pmul_0_r.
case_c0_test ( c--c1). assert (c==c1). apply copp_eq;trivial.
apply PolEq_refl.
apply PolEq_sym;apply Pmul_Rat_aux_assocP.
Qed.

 Lemma   Pdistr_l    : forall x y z, (x + y) * z != (x * z) + (y * z).
intros x y z;generalize x y;clear x y ;induction z;intros.
simpl;apply Pmul_Rat_distr;simpl.
simpl;repeat rewrite mkPX_PX_c.
rewrite  IHz.
apply PolEq_trans with (PX (x * z ) p c0 + PX(y*z) p c0 + Pol_mul_Rat (x + y) c).
apply Padd_ext_l.

simpl;rewrite ZPminus0; rewrite mkPX_PX_c; constructor;[setoid ring|apply PolEq_refl].

rewrite <-( Padd_assoc (PX (x * z) p c0 ) (Pol_mul_Rat x c )).
rewrite(Padd_sym (Pol_mul_Rat x c )).
rewrite <- Padd_assoc.
rewrite  <-Padd_assoc.
repeat apply Padd_ext_r.
rewrite Pmul_Rat_distr.
apply Padd_sym.
Qed.

 Lemma   Pmul_assoc  : forall x y z, x * (y * z) != (x * y) * z.
intros; generalize x y;clear x y ;induction z;intros;simpl.
rewrite Pmul_Rat_Pmul; apply PolEq_refl.
repeat rewrite mkPX_PX_c.
rewrite Pmul_Rat_Pmul.
rewrite <- IHz.
rewrite Pmul_sym;rewrite Pdistr_l.
apply Padd_ext; try apply Pmul_sym.
rewrite Pmul_sym; simpl; rewrite mkPX_PX_c.
rewrite Pmul_Rat_c0; rewrite Padd_0_r; apply PolEq_refl.
Qed.


Lemma PsubX_PaddX : forall x y fsub fadd p, (forall P, fadd P != fsub P) -> Pol_subX fsub y p x!= Pol_addX fadd (-y) p x.
induction x;intros.
simpl;apply PolEq_refl.
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.

simpl;rewrite ZPminus0; repeat rewrite mkPX_PX_c; rewrite H; apply PolEq_refl.
simpl;rewrite ZPminusneg; repeat rewrite mkPX_PX_c.
constructor;try setoid ring; apply IHx; trivial.
simpl;rewrite ZPminuspos; repeat rewrite mkPX_PX_c; rewrite H; apply PolEq_refl.

Qed.

 Lemma   Psub_def    : forall x y, x - y != x + -y.
intros; generalize x;clear x;induction y.
intros;simpl.
generalize c;clear c;induction x;intros.
simpl.

constructor;setoid ring.
simpl; constructor; try setoid ring; apply PolEq_refl.

generalize p c;clear p c;induction x;intros.

rename c0 into c2.
simpl; repeat rewrite mkPX_PX_c.
simpl; constructor; [setoid ring|apply PolEq_refl].

generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intros h;rewrite h;
[simpl;rewrite ZPminus0|simpl;rewrite ZPminuspos|idtac].
repeat rewrite mkPX_PX_c.

simpl;rewrite ZPminus0;rewrite mkPX_PX_c;constructor;[setoid ring|apply IHy].
repeat rewrite mkPX_PX_c;
simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[setoid ring|apply IHy].
simpl. rewrite ZPminusneg.

repeat rewrite mkPX_PX_c.

simpl; rewrite ZPminusneg; rewrite mkPX_PX_c.
constructor;[setoid ring|apply PsubX_PaddX].

intros;apply PolEq_sym;apply IHy.
Qed.

  Lemma   Popp_def    : forall x, x + (- x) != P0.
induction x;simpl.
constructor;setoid ring.
rewrite mkPX_PX_c;simpl;rewrite ZPminus0;rewrite mkPX_PX_c.
constructor;try setoid ring.
intuition.
Qed.


Lemma Padd_comp : forall P Q  R S, P !=Q -> R!=S -> P+R != Q+S.
exact Padd_ext.
Qed.

Lemma Pmul_comp: forall P Q  R S, P !=Q -> R!=S -> P*R != Q*S.
exact Pmul_ext. 
Qed.


Lemma Popp_0: forall P, P!=P0 -> -P!= P0.
induction P.
intro;simpl.
inversion H. constructor; rewrite H2;apply copp_0.
intro H;inversion H;simpl.

rewrite mkPX_PX_c.
rewrite H2;constructor;[setoid ring|apply IHP;trivial].

Qed.

Lemma Popp_comp: forall P Q, P!=Q -> -P != -Q.
intros P Q H;induction H;simpl; repeat rewrite mkPX_PX_c;constructor;try rewrite H0;try rewrite H; try apply ceq_refl.
 apply Popp_0;trivial.
 apply Popp_0;trivial.
apply IHPol_Eq.
rewrite IHPol_Eq.
simpl; rewrite mkPX_PX_c.
constructor;[apply copp_0|apply PolEq_refl].
rewrite IHPol_Eq;simpl; rewrite mkPX_PX_c;
constructor;[apply copp_0|apply PolEq_refl].
Qed.


Add Morphism Pol_opp with signature Pol_Eq  ==>  Pol_Eq as Popp_Morphism.
  intros P Q.
  apply Popp_comp;assumption.
Qed.



Lemma Psub_comp : forall x1 x2 y1 y2, x1 != x2 -> y1 != y2 -> x1 - y1 != x2 - y2.
   Proof.
   intros x1 x2 y1 y2 H1 H2.
   repeat rewrite Psub_def.
   rewrite H1;rewrite H2.
   reflexivity.
   Qed.

Add Morphism Pol_sub with signature Pol_Eq ==> Pol_Eq ==> Pol_Eq as Pol_sub_Morphism.
Proof.
intros;apply Psub_comp;trivial.
Qed.



Definition PRth : @ring_theory Pol 
(@Pc Coef (@Coef_record.C0 Coef cops))
(@Pc Coef (@Coef_record.C1 Coef cops))
Pol_add Pol_mul Pol_sub Pol_opp Pol_Eq.
Proof with trivial.
constructor.
apply Padd_0_l...
apply Padd_sym...
apply Padd_assoc...
apply Pmul_1_l...
apply Pmul_sym...
apply Pmul_assoc...
apply Pdistr_l...
apply Psub_def...
apply Popp_def...
Qed.

(* si on ne met pas @... Pol ci dessus il demande Leibnitz...*)

Add New Ring PolRing : PRth Abstract.


(* maintenant on a un ring sur Pol :setoid ring. *)

(* on ajoute aussi le morphisempourla soustraction*)





Add Morphism Pol_subC with signature Pol_Eq  ==>  ceq ==> Pol_Eq as PsubC_Morphism.
  intros P Q.
intros.
unfold Pol_subC.
inversion H;rewrite H0;rewrite H1;constructor;try rewrite H2;try  reflexivity.
Qed.





Lemma P0test_P0 :Pol_zero_test P0 =true.
simpl.

apply c0test_c0.
Qed.


Lemma P0test_P: forall P, Pol_zero_test P = true-> (Pol_Eq P P0).
induction P;simpl.

intro; constructor.

apply c0test_c;trivial.
intro;discriminate.
Qed.

Lemma P0_diff_P1: ~(Pol_Eq P0 P1).
simpl.
red;simpl;intro.
inversion H.
apply c0_diff_c1;trivial.
Qed.

Lemma Ppow_Pplus1:  forall x n, Pol_pow' x (1+n) != x * Pol_pow' x n.

induction n;simpl;try setoid ring.
rewrite Pplus_one_succ_l;rewrite IHn; setoid ring.

Qed.

Lemma Ppow_Psucc:forall x n, Pol_pow' x (Psucc n)!= x * Pol_pow' x n.
intros ; rewrite Pplus_one_succ_l.
apply Ppow_Pplus1.
Qed.

Lemma Ppow'_plus: forall x i j, (Pol_Eq (Pol_pow' x (i+j)) (Pol_mul (Pol_pow' x i)(Pol_pow' x j))).
intros;pattern i.
elim i using Pind.
elim j using Pind.

simpl;setoid ring.
intro;assert (h:(Pol_Eq (Pol_pow' x 1) x)); [simpl|rewrite h]. setoid ring.
(* si on met ;try setoid ring , ca fait Anomaly: 
uncaught exception Failure "cannot find relation". Please report !!!*)
intro;apply  Ppow_Pplus1.
intros;rewrite Pplus_succ_permute_l.
repeat rewrite Ppow_Psucc.
rewrite H; setoid ring.

Qed.

Lemma Ppow_plus: forall x i j, (Pol_Eq (Pol_pow x (i+j)) (Pol_mul (Pol_pow x i)(Pol_pow x j))).
destruct i;destruct j;simpl;apply PolEq_sym;try apply Pmul_Rat_c1;try apply Pmul_1_l.
apply PolEq_sym;apply Ppow'_plus.
Qed.



(*ici*)
Add Morphism Pol_pow' with signature Pol_Eq ==> (@eq positive) ==> Pol_Eq as Ppow'_Morphism.
  intros P Q i j;simpl.
induction j;simpl; auto; try setoid ring.
repeat rewrite IHj.
apply Pmul_ext_r;rewrite i;setoid ring.
repeat rewrite IHj;setoid ring.

Qed.


Add Morphism Pol_pow with signature Pol_Eq ==> (@eq N) ==> Pol_Eq as Ppow_Morphism.
  intros P Q i j;simpl.
destruct j; simpl;setoid ring.
destruct p;simpl; repeat rewrite i;setoid ring;trivial.

Qed.



Fixpoint Pol_is_zero(P:Pol):bool:=
  match P with
    |Pc c => czero_test c
    |PX P i c => andb (Pol_is_zero P) (czero_test c)
  end.


(* teste si P' est egal a PX^k, aux est le test d'egalite a P*)
Fixpoint Pol_eqb_aux(aux:Pol ->  bool)(P P':Pol)(k:positive)
  {struct P'}:bool:=
  match P' with
    |Pc c' => andb (Pol_is_zero P) (czero_test c')
    |PX P' j c' => (* teste si PX^k == P'X^j +c'*)
      match (Pcompare j k Eq) with
	|Eq => andb (aux P') (czero_test c')
	|Lt => (* j<k :revient a c'=0 et PX^(k-j) = P', cas recursif*)
	  andb (Pol_eqb_aux aux P P' (k-j)) (czero_test c')
	|Gt => (* j>k: le cas de dec struct pour Pol_eqb, appel a aux *)
	  andb (aux (PX P'  (j-k) c0)) (czero_test c')
      end
  end.


Fixpoint Pol_eqb(P P':Pol){struct P}:bool:=
  match P, P' with
    |Pc c, Pc c' => ceqb c c'
    |PX P i c, Pc c' => andb (Pol_is_zero P) (ceqb c c')
    |Pc c, PX P' j c' => andb (ceqb c c') (Pol_is_zero P')
    |PX P i c, PX P' j c' =>
      match Pcompare i j Eq with
	|Eq =>  andb (Pol_eqb P P') (ceqb c c')
	|Lt => andb (Pol_eqb P (PX P'  (j-i)c0 )) (ceqb c c')
	|Gt => andb (Pol_eqb_aux (Pol_eqb P) P P' (i-j)%positive)(ceqb c c')
      end
  end.


Inductive Pol_eq1 : Pol-> Pol-> Prop:=
  |eqb_true : forall P P', (Pol_eqb P P' = true) -> Pol_eq1 P P'.




Lemma P0test_P0'' :Pol_is_zero P0 =true.
simpl.
apply c0test_c0.
Qed.
Parameter c0test_c_b : forall c , czero_test c = (ceqb c c0).

Lemma P0test_P_b'': forall P, Pol_is_zero P = Pol_eqb P P0.
induction P;simpl;auto;rewrite c0test_c_b;auto.
Qed.

Lemma Piszero_P: forall P, Pol_is_zero P = true -> P!= P0.
induction P;simpl.
constructor;apply c0test_c;trivial.
intros;constructor;auto.
apply c0test_c;auto.
unfold andb in H.
generalize H;case(Pol_is_zero P);simpl;intros;auto;discriminate.
apply IHP;generalize H;case(Pol_is_zero P);simpl;intros;auto;discriminate.
Qed.

(*
Lemma Piszero_P_b: forall P, Pol_is_zero P = true -> (Pol_eqb P P0)=true.
induction P;simpl.
rewrite c0test_c_b ;auto.
case (Pol_is_zero P );simpl;auto.
rewrite c0test_c_b ;auto.
Qed.
*)

Lemma Pmul_PpowXP: forall P j ,(Pol_pow' X j) *P != (PX P j c0).
induction j;simpl.
rewrite mkPX_PX_c;rewrite Pmul_Rat_c0;rewrite Padd_0_r.
assert (h: PX (Pol_mul_Rat (Pol_pow' X j * Pol_pow' X j) c1) 1 c0 !=
PX (Pol_pow' X j * Pol_pow' X j) 1 c0);[idtac|rewrite h].
constructor;[apply ceq_refl|apply Pmul_Rat_c1].
rewrite Pmul_sym;simpl.
rewrite mkPX_PX_c;rewrite Pmul_Rat_c0;rewrite Padd_0_r.
apply PolEq_trans with (PX ((Pol_pow' X j)* (PX P j c0) )1 c0).
constructor;[apply ceq_refl|rewrite Pmul_sym].
rewrite <- Pmul_assoc;rewrite IHj.
apply PolEq_refl.
simpl.
apply PolEq_trans with (PX (PX (Pol_pow' X j * P) j c0 ) 1 c0).
constructor;[apply ceq_refl|rewrite mkPX_PX_c;rewrite Pmul_Rat_c0;rewrite Padd_0_r].
apply PolEq_refl.
apply PolEq_trans with (PX  (PX (PX P j c0) j c0) 1 c0).
constructor;[apply ceq_refl|constructor].
apply ceq_refl.
rewrite IHj.
apply PolEq_refl.
assert (xI j =j+ j+1)%positive.
rewrite  xI_succ_xO .
rewrite  Pplus_one_succ_r.
assert ((xO j)= j+j)%positive.
rewrite Pplus_diag;auto.
rewrite H;auto.
rewrite H.
constructor;[apply ceq_refl|constructor;[apply ceq_refl|apply PolEq_refl]].

rewrite <- Pmul_assoc;rewrite IHj;simpl.
rewrite mkPX_PX_c;rewrite Pmul_Rat_c0;rewrite Padd_0_r.
apply PolEq_trans with (PX ( PX P j c0) j c0).
constructor;[apply ceq_refl|apply IHj].
assert ((xO j)= j+j)%positive.
rewrite Pplus_diag;auto.
rewrite H;constructor;[apply ceq_refl|apply PolEq_refl].

rewrite Pmul_sym;simpl.
rewrite mkPX_PX_c;rewrite Pmul_Rat_c0;rewrite Padd_0_r.
constructor;[apply ceq_refl|apply Pmul_Rat_c1].
Qed.



Parameter ceqb_refl: forall c,ceqb c c= true.
Parameter ceqb_sym: forall c c', ceqb c c' = ceqb c' c.


Lemma Peqb_PEq: forall P Q , (Pol_eqb P Q = true ) -> Pol_Eq P Q.
induction P.
simpl;
intro Q;generalize c;clear c;induction Q.
intros;constructor;apply ceq_prop.
rewrite H;simpl;auto.
intros c2 H;constructor.
unfold andb in H.
generalize H;caseEq (ceqb c2 c);simpl.
intros;apply ceq_prop;trivial.
rewrite H0;simpl;auto.
intros;discriminate.
apply Piszero_P;generalize H;unfold andb;case(ceqb c2 c);simpl;intros;auto;discriminate.

intro Q;generalize c  p ;clear p c;induction Q.
simpl;intros c2 p H;constructor.
apply ceq_prop.
generalize H;case (Pol_is_zero P );simpl;intros.
rewrite H0;simpl;auto.
discriminate.
generalize H;caseEq (Pol_is_zero P );simpl;intros;auto;try discriminate.
apply Piszero_P;trivial.

simpl;intros c2 p0;
caseEq((p0 ?=  p)%positive Eq).
intro;assert (h:p0=p);[apply Pcompare_Eq_eq;trivial|rewrite h].
intro H1;elim (andb_prop _ _ H1);intros.
constructor;[apply ceq_prop;rewrite H2;simpl;auto|apply IHP ;trivial].

intro;assert (h: p=(p0 + (p -p0)) %positive);[auto|rewrite h].
assert ((p?= p0)%positive Eq = Gt).
apply ZC2;trivial.
rewrite Pplus_minus;auto.
intro H1;elim (andb_prop _ _ H1);intros;rewrite Pplus_comm;constructor.
apply ceq_sym;apply ceq_prop;rewrite H2;simpl;auto.
apply IHP.
assert ((p0 + (p - p0) - p0 = p -p0) %positive). rewrite Pplus_minus;auto.
apply ZC2;trivial.
rewrite <- H3;trivial.

intro;assert ((p + (p0 -p)=p0 )%positive). apply Pplus_minus;trivial.
intro H1;elim (andb_prop _ _ H1);intros.
rewrite <- H0.
rewrite Pplus_comm;constructor.
apply ceq_prop;rewrite H3;simpl;auto.

apply PolEq_sym;apply IHQ.
destruct Q.
simpl in H2.
simpl.
elim(andb_prop _ _ H2);intros.
rewrite H4;simpl.
rewrite ceqb_sym;rewrite <- c0test_c_b ;trivial.

generalize H2;simpl.
caseEq((p0 - p ?= p1)%positive Eq) ;intro.
assert ( (p1 ?= p0 - p)%positive Eq = Eq).
rewrite ZC3;trivial.
rewrite H5.
intro H6;elim (andb_prop _ _ H6);intros.
rewrite H7;simpl.
rewrite ceqb_sym;rewrite <- c0test_c_b;trivial.
rewrite ZC2;trivial.
intro H6;elim (andb_prop _ _ H6);intros;rewrite H5;simpl.
rewrite ceqb_sym;rewrite <- c0test_c_b;trivial.
rewrite ZC1;trivial.
intro H6;elim (andb_prop _ _ H6);intros;rewrite H5;simpl.
rewrite ceqb_sym;rewrite <-  c0test_c_b ;trivial.
Qed.


Lemma Peqb_refl: forall P  , (Pol_eqb P P ) =true.
induction P.
simpl;apply ceqb_refl.
simpl.
rewrite Pcompare_refl.
rewrite IHP;simpl.
apply ceqb_refl.
Qed.


Lemma Peqb_sym: forall P Q, Pol_eqb P Q = Pol_eqb Q P.
induction P.
simpl.
induction Q.
simpl.
apply ceqb_sym.
simpl.
rewrite andb_comm.
unfold andb.
case (Pol_is_zero Q) ;simpl;auto.
apply ceqb_sym.
intro Q;generalize p c;clear p c; induction  Q;intros;rename c0 into c2.
simpl.
rewrite  ( andb_comm (ceqb c c2));unfold andb;
case (Pol_is_zero P) ;simpl;auto.
apply ceqb_sym.

caseEq((p ?= p0)%positive Eq );intro.
simpl;rewrite H.
rewrite ZC3;auto.
rewrite IHP;rewrite ceqb_sym;trivial.
simpl;rewrite H.
rewrite ZC2;trivial.
rewrite ceqb_sym;repeat rewrite <-  ( andb_comm (ceqb c c2)).
unfold andb;case (ceqb c c2);simpl;auto.


rewrite <- IHQ;simpl.
destruct Q;simpl;rename c0 into c3.
case (Pol_is_zero P);simpl;auto.
rewrite ceqb_sym;apply  c0test_c_b.

caseEq ((p1 ?= p0 - p)%positive Eq);intro.
rewrite ZC3;trivial.
case (Pol_eqb P Q) ;simpl;auto.
rewrite ceqb_sym;apply  c0test_c_b.
rewrite ZC2;auto.
case (Pol_eqb_aux (Pol_eqb P) P Q (p0 - p - p1));simpl;auto;rewrite ceqb_sym;apply  c0test_c_b.
rewrite ZC1;trivial.
case(Pol_eqb P (PX Q (p1 - (p0 - p)) c0));simpl;auto;rewrite ceqb_sym;apply  c0test_c_b.
simpl.
rewrite ZC1;trivial.
rewrite H.
rewrite IHP;simpl.

destruct P;simpl;rename c0 into c3.
case (Pol_is_zero Q );simpl;auto.
rewrite c0test_c_b;rewrite ceqb_sym.
rewrite (ceqb_sym c);auto.

caseEq ((p1 ?= p- p0)%positive Eq);intro.
rewrite ZC3;trivial.
case (Pol_eqb Q P) ;simpl;auto.
rewrite ceqb_sym;rewrite c0test_c_b.
rewrite (ceqb_sym c);auto.

rewrite ZC2;auto.
case (Pol_eqb_aux (Pol_eqb Q) Q P (p - p0 - p1) );simpl;auto;rewrite ceqb_sym.
rewrite  c0test_c_b;rewrite (ceqb_sym c);auto.
rewrite ZC1;trivial.
case(Pol_eqb Q (PX P (p1 - (p - p0)) c0));simpl;auto;rewrite ceqb_sym.
rewrite  c0test_c_b; rewrite (ceqb_sym c);auto.
Qed.

Lemma nP0test_P_b: forall P, Pol_is_zero P = Pol_eqb P0 P.
induction P.
simpl.
rewrite ceqb_sym;apply c0test_c_b.
simpl.
rewrite ceqb_sym;rewrite c0test_c_b;apply andb_comm.
Qed.


Lemma Pmul_PPpowX: forall P j , P* (Pol_pow' X j) != PX P j c0.
intros;rewrite Pmul_sym;apply Pmul_PpowXP.
Qed.


 Fixpoint Peqb (P P' : Pol) {struct P'} : bool := 
  match P, P' with
  | Pc c, Pc c' => (ceqb c c') 
  | PX P i c, PX P' i' c' =>
    match Pcompare i i' Eq with
    | Eq => if Peqb P P' then (ceqb c c') else false
    | _ => false
    end
  | _, _ => false
  end.

 Notation " P ?== P' " := 
  (Peqb P P') (at level 70, no associativity) : pol_scope.




Lemma Peq_ok : forall P P', 
    (Peqb P P') = true -> forall l, (ceq (Pol_eval P l) (Pol_eval P' l)).
induction P;destruct P';simpl;intros;try discriminate;trivial.
apply ceq_prop.
rewrite H;simpl.
auto.
generalize H;case (p ?= p0)%positive;intros;try discriminate.
generalize H0;caseEq (Peqb P P');intros;try discriminate.
apply cadd_ext.
apply cmul_ext.
auto.
 assert (h := Pcompare_Eq_eq p p0); destruct ((p ?= p0)%positive Eq);try discriminate.
rewrite h ; auto.
 apply ceq_refl.
apply ceq_prop;trivial.
rewrite H2;auto.
simpl;auto.
Qed.

 Lemma Pphi0 : forall l, (Pol_eval P0 l )== c0.
intros;simpl.
setoid ring.
Qed.
Lemma Pphi1 : forall l,  (Pol_eval P1 l) == c1.
intros;simpl.
setoid ring.
Qed.



Lemma  PolEq_prop: forall x y , Bool.Is_true (Peqb x y) -> (Pol_Eq x y).
induction x;induction y.
simpl;intros;constructor;apply ceq_prop;trivial.
simpl;intro H;elim H.
simpl Peqb.
simpl.
intro H;elim H.
caseEq(Pcompare p0 p Eq);intro.
assert (h:p0=p);[apply Pcompare_Eq_eq|rewrite h];trivial.
simpl.
caseEq((p ?= p)%positive Eq).
caseEq(Peqb x y);intros.
constructor;[apply ceq_prop ;trivial| apply IHx;trivial].
rewrite H0;auto.
simpl;auto.
simpl in H2;elim H2.
intros.
simpl in H1; elim H1.
intros H1 H2;simpl in H2;elim H2.
simpl.
assert (h: (p ?= p0)%positive Eq = Gt).
apply ZC2;trivial.
rewrite h.
simpl;intro H1;elim H1.
simpl.
assert (h: (p ?= p0)%positive Eq = Lt);[apply ZC1;trivial|rewrite h;simpl;intro H1;elim H1].
Qed.

Hypothesis c2_diff_c0: ~ (c1++c1 == c0).
Hypothesis cmul_integral: forall n m , n **m == c0  -> n == c0 \/ m ==c0.

Lemma P2_diff_P0: ~(P1+P1 != P0).
simpl.
red; intros.
inversion H.
absurd (c1 ++ c1 == c0); trivial; apply c2_diff_c0.
Qed.


Lemma Pmul_PXn_m_c0 : forall n m p c , c == c0 -> (PX n p c * m != PX m p c * n).
intros;rewrite Pmul_sym.
rewrite <- (Pmul_sym n).
simpl.
repeat rewrite mkPX_PX_c; rewrite H; repeat rewrite Pmul_Rat_c0.
setoid ring.
rewrite Pmul_sym;setoid ring.
Qed.

Lemma PX_mn_c0 : forall n m p c, c==c0 -> (PX (n*m) p c ) != n* (PX m p c).
intros;simpl.
rewrite H; rewrite Pmul_Rat_c0;rewrite mkPX_PX_c; try setoid ring.
Qed.


Lemma Pmul_integral: forall n m , n *m != P0  -> n != P0 \/ m !=P0.
induction n.
induction  m.
simpl; intros;rename c0 into c2.
elim (cmul_integral c c2);intros;[left|right|idtac].
 constructor;trivial.
 constructor;trivial.

generalize H; unfold Pol_mul_Rat.
case_c0_test c2.
intro;rewrite H1;setoid ring.
case_c0_test (c2--c1).
intro H3;inversion H3.
rewrite H6;setoid ring.

simpl.
intro H2;inversion H2;trivial.
simpl; intros;rename c0 into c2.
generalize H; rewrite mkPX_PX_c;unfold Pol_mul_Rat;simpl.
case_c0_test c2.
rewrite Padd_0_r.
rewrite H1.
intro H2;inversion H2.
elim IHm; trivial;intros.
left;trivial.

right; constructor;trivial;setoid ring.
case_c0_test (c2--c1).
simpl.

intro H3;inversion H3; left; constructor.
rewrite <- H6;setoid ring.
simpl.
intro H2;inversion H2;trivial.
elim IHm; trivial;intros.
left;trivial.

elim (cmul_integral c c2).
intro;left;constructor; trivial.
intro;right;constructor; trivial.
rewrite <- H5;setoid ring.

intro m; generalize p c; clear p c ; induction m.
rename c into c2;intros p c.
simpl.

unfold Pol_mul_Rat;simpl.
case_c0_test c2.
intro;right;constructor; trivial.
case_c0_test (c2--c1).
intro;left;trivial.
rewrite mkPX_PX_c;simpl.

intros.
inversion H1.
elim (cmul_integral c c2); trivial; intro.
elim (IHn (Pc c2));intros.
left;constructor;trivial.
right ; trivial.
simpl; unfold Pol_mul_Rat; rewrite H;rewrite H0;trivial.
right;constructor;trivial.
rename c into c2; intros p0 c.
simpl.

rewrite mkPX_PX_c; unfold  Pol_mul_Rat;simpl.
case_c0_test c2.
rewrite Padd_0_r;intro H1;inversion H1.
elim (IHm p0 c);intros; trivial.
left;trivial.
right;constructor;trivial.

generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.
case_c0_test (c2--c1);simpl.
rewrite ZPminus0.
rewrite mkPX_PX_c;rewrite cadd_0_l;intro H2;inversion H2.
generalize H8; rewrite Pmul_PXn_m_c0;trivial.
elim (IHn (PX m p0 c + (Pc c1)));intros.
left; constructor;trivial.
simpl in H9.
inversion H9.

absurd (c0== c1). apply c0_diff_c1.
rewrite <- H13; rewrite H5;setoid ring.
rewrite Pmul_sym;rewrite Pdistr_l.
rewrite <-H8; rewrite Pmul_PXn_m_c0; trivial; (*fold P1;*)setoid ring.
rewrite mkPX_PX_c;simpl;rewrite ZPminus0;rewrite mkPX_PX_c.
rewrite cadd_0_l;intro H1;inversion H1.
elim (cmul_integral c c2); trivial; intros.
generalize H7; rewrite Pmul_PXn_m_c0;trivial.
elim (IHn (PX m p0 c + (Pc c2)));intros.
left; constructor;trivial.
simpl in H9.
inversion H9.

right; constructor; trivial.
rewrite <- H13; rewrite H8;setoid ring.
rewrite <- H7; rewrite Pscal_aux_Pmul_r; setoid ring.
rewrite Pmul_PXn_m_c0; trivial;setoid ring.
elim (IHm p0 c);intros.
left;trivial.
right; constructor;trivial.
rewrite <- H7;rewrite H8;rewrite Pmul_Rat_aux_c0;setoid ring.
case_c0_test (c2--c1).
simpl;rewrite ZPminuspos.
rewrite cadd_0_l;rewrite mkPX_PX_c; intro H2;inversion H2.
elim (IHn (PX (PX m p0 c ) p1 c0 + P1));intros.
left; constructor; trivial.
simpl in H9; inversion H9;absurd (c0 == c1).
apply c0_diff_c1.
rewrite <- H12;setoid ring.
rewrite Pmul_sym;rewrite Pdistr_l; simpl.
rewrite (Pmul_sym (Pc c1) n); simpl;rewrite Pmul_Rat_c1.
rewrite Pmul_PXn_m_c0; try apply ceq_refl.
simpl.

rewrite mkPX_PX_c;simpl.
rewrite H5;rewrite Pmul_Rat_c0; rewrite Padd_0_r.
rewrite <- H8;apply Padd_ext_l.
generalize (ZPminus_spec p0 p1); destruct (ZPminus p0 p1); intro h2;rewrite h2.
rewrite H5;setoid ring.
rewrite H5;rewrite Pplus_comm;constructor; try apply   ceq_refl;setoid ring.
rewrite Pmul_sym;simpl.
rewrite Pmul_Rat_c0;rewrite Padd_0_r;rewrite mkPX_PX_c;rewrite Pplus_comm;
constructor;[setoid ring | setoid ring].
rewrite Pmul_sym;simpl.
rewrite Pmul_Rat_c0;rewrite Padd_0_r;rewrite mkPX_PX_c;constructor;[setoid ring|setoid ring].
rewrite Pplus_comm;constructor; try apply   ceq_refl;setoid ring.
rewrite Pmul_sym;simpl;rewrite Pmul_Rat_c0;rewrite Padd_0_r;rewrite mkPX_PX_c;
rewrite Pplus_comm;constructor; [setoid ring | setoid ring].
rewrite Pmul_sym;simpl;rewrite mkPX_PX_c.
rewrite H5; rewrite Pmul_Rat_c0;setoid ring.
rewrite mkPX_PX_c;simpl; rewrite ZPminuspos; rewrite mkPX_PX_c.
rewrite cadd_0_l;intro H1; inversion  H1.
elim (cmul_integral c c2); trivial; intros.
elim (IHn (PX m p  c + (Pc c2)));intros.
left; constructor;trivial.
simpl in H9;inversion H9.

right; constructor; trivial.
rewrite <- H12; rewrite H8;setoid ring.
rewrite <- H7; rewrite Pscal_aux_Pmul_r; setoid ring.
rewrite Padd_sym; apply Padd_ext_r.
rewrite H8;simpl; rewrite mkPX_PX_c; rewrite Pmul_Rat_c0;setoid ring.
rewrite h;constructor;[setoid ring|setoid ring].
rewrite Pmul_sym;simpl;rewrite mkPX_PX_c; rewrite Pmul_Rat_c0;setoid ring.
rewrite Pmul_sym;setoid ring.
generalize H7; rewrite H8; rewrite Pmul_Rat_aux_c0;rewrite Padd_0_r;clear H7;intro H7; inversion H7.
elim ( IHm p0 c); trivial;intros.
left; trivial.
right;  constructor;trivial;setoid ring.
case_c0_test (c2--c1).
rewrite Padd_sym.
simpl; rewrite ZPminuspos.
rewrite cadd_0_r;rewrite mkPX_PX_c; intro H2; inversion H2.
generalize H8; rewrite Pmul_sym;simpl.
rewrite mkPX_PX_c;simpl.
rewrite H5;rewrite Pmul_Rat_c0;rewrite Padd_0_r.
rewrite Padd_sym;simpl; rewrite Pplus_comm;rewrite ZPminuspos.
rewrite mkPX_PX_c; clear H8; intro H8; inversion H8.
elim (IHn (PX m p c1));intros.
left;constructor;[setoid ring|trivial].
inversion H15.
absurd (c0==c1); [apply c0_diff_c1|rewrite H18;setoid ring].
simpl.
rewrite mkPX_PX_c; rewrite Pmul_Rat_c1; rewrite <- H14;setoid ring.
rewrite Pmul_sym; rewrite Padd_sym;setoid ring.
rewrite mkPX_PX_c;rewrite Padd_sym;simpl; rewrite ZPminuspos.
rewrite mkPX_PX_c;rewrite cadd_0_r.
intro H1; inversion H1.
elim (cmul_integral c c2); trivial; intros.
rewrite H8.
generalize H7; rewrite H8; rewrite Pmul_sym;simpl.
rewrite mkPX_PX_c; rewrite Pmul_Rat_c0; rewrite Padd_0_r.
rewrite Padd_sym;simpl; rewrite Pplus_comm;rewrite ZPminuspos.
rewrite mkPX_PX_c; intro H9;inversion H9.
elim (IHn (PX m p c2));intros.
left; constructor;[setoid ring|trivial].
right;trivial.
simpl; rewrite mkPX_PX_c.
unfold Pol_mul_Rat; rewrite H; rewrite H0.
rewrite Pmul_sym;trivial.
generalize H7;rewrite H8; rewrite Pmul_Rat_aux_c0; rewrite Padd_P0_l.
 constructor;try apply ceq_refl.
 constructor; setoid ring.
subst.
elim ( IHm (p + p1)%positive c);trivial;intros.
left;trivial.
right;constructor;trivial; setoid ring.
rewrite <- H7;rewrite H8; rewrite Pmul_Rat_aux_c0;setoid ring.
setoid ring.
rewrite Padd_P0_r.
constructor;[setoid ring|apply PolEq_refl].
setoid ring.
Qed.




Lemma Pol_sub_c0 : forall P Q, P != Q ->  Pol_subC P c0 != Q. 
Proof.
intros P Q H.
unfold Pol_subC.
inversion H;constructor;try rewrite H0;trivial;
try setoid ring.
Qed.

Lemma Pol_sub_c0' : forall P,  Pol_subC P c0 != P. 
Proof.
intro P;apply Pol_sub_c0.
reflexivity.
Qed.


Lemma Pmul_c1 : forall P Q, P !=Q -> Pol_mul_Rat P c1 != Q.
Proof.
intros P Q H.
rewrite H.
apply Pmul_Rat_c1.
Qed.

Lemma Pmul_c1' : forall P, Pol_mul_Rat P c1 != P.
intros P;apply Pmul_c1.
reflexivity.
Qed.


Lemma Pc_Pol_opp : forall x, - (Pc x) != Pc (-- x).
Proof.
intro x.
simpl.
constructor;apply ceq_refl.
Qed.



Lemma Pmul_P0_c : forall c, c !* P0 !=P0.
Proof.
intros;unfold Pol_mul_Rat.
simpl.
case_c0_test c;simpl.
reflexivity.
case_c0_test (c --c1).
reflexivity.
constructor;setoid ring.
Qed.

Lemma Pmul_P1_c : forall c, c !* P1 != Pc c.
Proof.
intros;unfold Pol_mul_Rat;simpl.
case_c0_test c;simpl.
constructor.
rewrite H0;reflexivity.
case_c0_test (c --c1);constructor.
assert (H2:c == c1);apply copp_eq;trivial.
rewrite H2;setoid ring.
setoid ring.
Qed.


Lemma Pol_addC_spec : forall P p, Pol_addC P p != P + Pc p.
Proof.
destruct P;simpl;intros;reflexivity.
Qed.


Add Morphism Pol_addC with signature Pol_Eq ==> ceq ==>Pol_Eq as PaddC_comp.
Proof.
intros x1 x2 H x3 x4 G.
repeat rewrite Pol_addC_spec.
rewrite H.
rewrite G.
reflexivity.
Qed.

(* Une tactique de simplification des expressions avec des Pc et des operations par des des coef,
peut permettre d' utiliser setoid ring*)



Let fun_Psub_c0 := fun x y h=> (PolEq_sym _ _ (Pol_sub_c0 x y h)).
Let fun_Psub_c0' := fun x => (PolEq_sym _ _ (Pol_sub_c0' x)).

Let fun_Pmul_c1 := fun x y h => (PolEq_sym _ _ (Pmul_c1 x y h)).
Let fun_Pmul_c1' := fun x => (PolEq_sym _ _ (Pmul_c1' x)).

Let fun_Pmul_Rat_c0 := fun x  => (PolEq_sym _ _ (Pmul_Rat_c0 x)).

Let fun_Pmul_P0_c := fun x => (PolEq_sym _ _ (Pmul_P0_c x)).

Let fun_Pmul_P1_c := fun x => (PolEq_sym _ _ (Pmul_P1_c x)).

Hint Resolve Padd_comp Pmul_comp Psub_comp PsubC_Morphism Popp_comp
PaddC_comp mkPX_morph ceq_refl
PolEq_refl  Pc_Pol_opp Pmul_Rat_c0  Pmul_c1' Pmul_c1 Pmul_P0_c Pmul_P1_c
 Pol_sub_c0' fun_Psub_c0' Pol_sub_c0 fun_Psub_c0' fun_Pmul_c1' fun_Pmul_c1 fun_Pmul_Rat_c0
fun_Pmul_P0_c fun_Pmul_P1_c: compat.

(*un pas de transformation *)
Ltac one_step t := 
  match t with 
   | context ctx [Pc (copp ?X)] => 
      let new_val := context ctx[Pol_opp(Pc X)] in
          constr:new_val
  | context ctx [Pol_subC ?P c0] =>
    let new_val := context ctx[P] in
         constr:new_val
  | context ctx [Pol_mul_Rat ?P c0] =>
   let new_val := context ctx[P0] in
        constr:new_val
  |context ctx [Pol_mul_Rat ?P c1] =>
    let new_val := context ctx[P] in
     constr:new_val
  |context ctx [Pol_mul_Rat P0 ?c] =>
	let new_val := context ctx[P0] in
        constr:new_val
  |context ctx [Pol_mul_Rat P1 ?c] =>
	let new_val := context ctx[Pc c] in
        constr:new_val
  | _ => true
end.

(* calcule la forme normale*)
Ltac steps t := 
   match one_step t with
     true => t
   | ?t1 => steps t1
end.

(* prouve un but qui est une egalite dans Pol en prouvant par transitivite que chaque memebre est egal a
sa forme normale calculee par steps*)

Ltac Pcsimpl := match goal with
  |- Pol_Eq ?t1 ?t2  =>
      let t3 := steps t1 in
      let t4 := steps t2 in
      (apply PolEq_trans with t3; [idtac | apply PolEq_trans with t4];auto 25 with compat)
end.
