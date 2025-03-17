From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith String OrderedType OrderedTypeEx FMapAVL.

Notation head := seq.head.
Notation seq := seq.seq.
Notation nth := seq.nth.
Notation sort := path.sort.

Import Order.POrderTheory Order.TotalTheory.

Section shortest_path.

Variable R : Type.
Variable R0 : R.
Variable R_ltb : R -> R -> bool.
Variable R_add : R -> R -> R.

Variable cell : Type.
Variable node : Type.
Variable node_eqb : node -> node -> bool.
Variable neighbors_of_node : node -> seq (node * R).
Variable source target : node.

Variable priority_queue : Type.
Variable empty : priority_queue.
Variable gfind : priority_queue -> node -> option (seq node * option R).
Variable update : priority_queue -> node -> seq node -> option R ->
      priority_queue.
Variable pop :  priority_queue ->
       option (node * seq node * option R * priority_queue).

Definition cmp_option (v v' : option R) :=
  if v is Some x then
    if v' is Some y then
       (R_ltb x y)%O
    else
      true
   else
     false.

Definition Dijkstra_step (d : node) (p : seq node) (dist : R)
  (q : priority_queue) : priority_queue :=
  let neighbors := neighbors_of_node d in
  foldr (fun '(d', dist') q =>
           match gfind q d' with
           | None => q
           | Some (p', o_dist) =>
             let new_dist_to_d' := Some (R_add dist dist') in
             if cmp_option new_dist_to_d' o_dist then
                update q d' (d :: p) new_dist_to_d'
             else q
           end) q neighbors.

Fixpoint Dijkstra (fuel : nat) (q : priority_queue) :=
  match fuel with
  | 0%nat => None
  |S fuel' =>
    match pop q with
    | Some (d, p, Some dist, q') =>
      if node_eqb d target then Some p else
        Dijkstra fuel' (Dijkstra_step d p dist q')
    | _ => None
    end
  end.

Definition shortest_path (s : seq node) :=
  Dijkstra (size s)
    (update (foldr [fun n q => update q n [::] None] empty s)
        source [::] (Some R0)).

End shortest_path.
