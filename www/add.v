Require Import List QArith Extraction.


Definition a_val := 1%Q :: nil.

Fixpoint sum_val_rec l :=
 match l with a :: l =>     Qred (a + sum_val_rec l)%Q | _ => 0%Q end.

Definition sum_val l := (sum_val_rec l) :: nil.

Compute sum_val ((1#2)%Q :: (1#2)%Q :: nil).

Extraction "Add.ml" a_val sum_val.

