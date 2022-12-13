
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*   Assia.Mahboubi@inria.fr, Laurence.Rideau@inria.fr       *)
(*  Laurent.Thery@inria.fr  &all    2006                     *)
(*************************************************************)

(* Construit une structure de relation et declare de morphismes si on a
  dans l'environnement la signature suivante :

    c0 : Coef;
    c1 : Coef;
    cadd : Coef -> Coef -> Coef;
    cmul : Coef -> Coef -> Coef;
    copp : Coef -> Coef;
    csub : Coef -> Coef -> Coef;
    ceq: Coef -> Coef -> Prop; qu'on note == pour le commentaire 

    ceq_refl : forall x, x==x;
    ceq_sym : forall x y, x == y -> y == x;
    ceq_trans : forall x y z, x == y -> y == z -> x == z
  
    cadd_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2;
    cmul_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2;
    copp_ext : forall x1 x2, x1 == x2 -> -- x1 == -- x2

il faut aussi:
Require Import Setoid *)


Definition ceq_Eq_Relation_Class : Relation_Class.
 eapply (@SymmetricReflexive unit _ ceq).
 exact ceq_sym.
 exact ceq_refl.
Defined.


Add Relation Coef ceq
 reflexivity proved by ceq_refl
 symmetry proved by ceq_sym
 transitivity proved by ceq_trans
 as ceq_relation.


  (* Morphism declarations *)

Add Morphism cadd with signature ceq ==> ceq ==> ceq as cadd_Morphism.
  intros;apply cadd_ext;assumption.
Qed.

Add Morphism cmul with signature ceq ==> ceq ==> ceq as cmul_Morphism.
  intros;apply cmul_ext;assumption.
Qed.

Add Morphism copp with signature ceq ==> ceq as copp_Morphism.
  intros;apply copp_ext;assumption.
Qed.

Add Morphism czero_test with signature ceq ==> (@eq bool) as c0_test_Morphism.
  intros;apply c0_test_ext;assumption.
Qed.

Add Morphism cpow with signature ceq ==> (@eq N) ==> ceq as cpow_morphism.
intros x1 x2 Heq n; case n.
repeat setoid_rewrite cpow_0; apply ceq_refl.
intros p; induction p.

replace (Npos (xI p)) with (1+(Npos p+Npos p))%N;
repeat setoid_rewrite cpow_plus; repeat setoid_rewrite cpow_1.
setoid_rewrite IHp; setoid_rewrite Heq; apply ceq_refl.
simpl; rewrite Pplus_diag; auto.

replace (Npos (xO p)) with (Npos p+Npos p)%N.
repeat setoid_rewrite cpow_plus; setoid_rewrite IHp; apply ceq_refl.
simpl; rewrite Pplus_diag; auto.
repeat setoid_rewrite cpow_1; setoid_rewrite Heq; apply ceq_refl.
Qed.
