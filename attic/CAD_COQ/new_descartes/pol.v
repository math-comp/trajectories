Require Import QArith List Omega ZArith.

Fixpoint eval_pol (l:list Q)(x:Q) {struct l} : Q :=
  match l with 
    nil => 0
  | a::tl => a + x * (eval_pol tl x)
  end.

