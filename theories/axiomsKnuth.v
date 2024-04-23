From mathcomp Require Import all_ssreflect ssralg matrix ssrnum vector reals order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type KnuthAxioms.
Section Dummy.

Variable R : realType.
Definition Plane : vectType _ := (R^o * R^o)%type.
Parameter OT : Plane -> Plane -> Plane -> bool.

(*Knuth's axioms are given by the following variables.  But axiom 4 is not used in Jarvis' algorithm and axiom 3 is a property of the data, not of the
  plane. *)
Axiom Axiom1 : forall p q r, OT p q r -> OT q r p.

Axiom Axiom2 : forall p q r, OT p q r -> ~ OT p r q.

Axiom Axiom4 : forall p q r t, OT t q r -> OT p t r -> OT p q t -> OT p q r.

Axiom Axiom5 :
 forall t s p q r, OT t s p -> OT t s q -> OT t s r ->
    OT t p q -> OT t q r -> OT t p r.

Local Open Scope order_scope.
Axiom Axiom5' : forall (pivot p q r : Plane),
  (pivot : R *l R) < p ->
  (pivot : R *l R) < q ->
  (pivot : R *l R) < r ->
  OT pivot p q ->
  OT pivot q r ->
  OT pivot p r.

End Dummy.
End KnuthAxioms.
