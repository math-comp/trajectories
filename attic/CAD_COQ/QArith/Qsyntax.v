
Unset Boxed Definitions.
Unset Boxed Values.




Require Export QArith_base.

(* nocvs Infix LEFTA 3 "*" Qmult : Q_scope.*)

Infix "*":= Qmult (at level 40,left associativity) : Q_scope.

Open Scope Q_scope.

(*nocvs Infix NONA 5 "<=" Qle : Q_scope.*)
Infix "<=":= Qmult  : Q_scope.

(* nocvs Infix LEFTA 4 "==" Qeq : Q_scope.*)
Infix "==":= Qeq : Q_scope.


(*Notation "x <= y <= z" := (Qle x y)/\(Qle y z)
(at level 50, y at level 40):Q_scope. *)


Notation "x <= y <= z" := ((Qle x y)/\(Qle y z)).


(*nocvs Infix LEFTA 4 "<" Qlt : Q_scope.*)
Infix "<":= Qlt  : Q_scope.


(*nocvs Infix LEFTA 4 "+" Qplus : Q_scope.*)
Infix "+":= Qplus  : Q_scope.

(*nocvsInfix LEFTA 4 "-" Qminus : Q_scope.*)
Infix "-":= Qminus: Q_scope.

(*nocvs Distfix 3 " - _" Qopp :Q_scope.*)
Notation "- x" := (Qopp x)  : Q_scope.
