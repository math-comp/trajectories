From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith List String OrderedType OrderedTypeEx FMapAVL.

Notation head := seq.head.
Notation seq := seq.seq.
Notation sort := path.sort.

Section shortest_path.

Variable R : numFieldType.
Variable cell : Type.
Variable cells : seq cell.
Variable node : eqType.
Variable neighbors_of_node : node -> seq (node * R).
Variable source target : node.

Definition path := seq node.
Variable priority_queue : Type.
Variable empty : priority_queue.
Variable find : priority_queue -> node -> option (path * option R).
Variable update : priority_queue -> node -> path -> option R -> priority_queue.
Variable pop :  priority_queue -> option (node * path * option R * priority_queue).

Definition cmp_option (v v' : option R) :=
  if v is Some x then
    if v' is Some y then
       (x < y)%O
    else
      true
   else
     false.

Definition Dijkstra_step (d : node) (p : seq node) (dist : R)
  (q : priority_queue) : priority_queue :=
  let neighbors := neighbors_of_node d in
  foldr (fun '(d', dist') q => 
           match find q d' with
           | None => q
           | Some (p', o_dist) =>
             let new_dist_to_d' := Some (dist + dist')%R in
             if cmp_option new_dist_to_d' o_dist then
                update q d' (d :: p) new_dist_to_d'
             else q
           end) q neighbors.

Fixpoint Dijkstra (fuel : nat) (q : priority_queue) :=
  match fuel with
  | 0 => None
  |S fuel' =>
    match pop q with
    | Some (d, p, Some dist, q') =>
      if d == target then Some p else 
        Dijkstra fuel' (Dijkstra_step d p dist q')
    | _ => None
    end
  end.

Definition shortest_path (s : seq node) :=
  Dijkstra (size s)
    (foldr [fun n q => update q n [::] None] empty s).
  
Definition neighbors_of_node (d : node) :  seq (node * R) :=
  let (c1, c2) := node_to_cells d in
  let ds1 := cell_to_nodes c1 in
  let ds2 := cell_to_nodes c2 in
  let ds := undup [seq x | x <- ds1 ++ ds2 & x != d] in
  [seq (x, node_distance d x) | x <- ds].
