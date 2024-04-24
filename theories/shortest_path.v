From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith (* List *) String OrderedType OrderedTypeEx FMapAVL.
Require Import smooth_trajectories.

Notation head := seq.head.
Notation seq := seq.seq.
Notation nth := seq.nth.
Notation sort := path.sort.

Section shortest_path.

Variable R : Type.
Variable R0 : R.
Variable ltb : R -> R -> bool.
Variable add : R -> R -> R.
Variable cell : Type.
Variable node : Type.
Variable node_eqb : node -> node -> bool.
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
       (ltb x y)%O
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
             let new_dist_to_d' := Some (add dist dist')%R in
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

Import generic_trajectories.
Notation cell := (cell R edge).

Notation v_eqb := (vert_edge_eqb R QArith_base.Qeq_bool).
Notation cell_left_doors :=
   (cell_safe_exits_left R (QArith_base.inject_Z 1) edge).
Notation cell_right_doors :=
   (cell_safe_exits_right R (QArith_base.inject_Z 1) edge).

Notation dummy_cell := (dummy_cell R (QArith_base.inject_Z 1) edge Bedge).

Definition index_seq {T : Type} (s : list T) : list (nat * T) :=
  zip (iota 0 (size s)) s.

Definition cells_to_doors (s : list cell) :=
  let indexed_s := index_seq s in
  let vert_edges_and_right_cell :=
    flatten (map (fun '(i, c) => 
                   (map (fun v => (v, i))) (cell_left_doors c))
      indexed_s) in
  let vert_edges_and_both_cells :=
    flatten (map (fun '(v, i) => 
          (map (fun '(i', c') => (v, i, i'))
               (filter (fun '(i', c') =>
                   existsb (v_eqb v) (cell_right_doors c'))
                   indexed_s)))
           vert_edges_and_right_cell) in 
      vert_edges_and_both_cells.

Notation on_vert_edge :=
  (on_vert_edge R QArith_base.Qeq_bool QArith_base.Qle_bool).

Notation vert_edge_midpoint :=
  (vert_edge_midpoint R QArith_base.Qplus QArith_base.Qdiv  (QArith_base.inject_Z 1)).

Definition vert_edge_to_reference_point (s t : pt R) (v : vert_edge R) :=
  if on_vert_edge s v then s
  else if on_vert_edge t v then t
  else vert_edge_midpoint v.

Definition one_door_neighbors
  (indexed_doors : seq (nat * (vert_edge R * nat * nat)))
  (i_d : nat * (vert_edge R * nat * nat)) : list nat :=
  match i_d with
  | (j, (v0, i0, i'0)) =>
    map fst
      (filter (fun '(vi, (v, i, i')) => (Nat.eqb i i0  || Nat.eqb i i'0 ||
              Nat.eqb i' i0 || Nat.eqb i' i'0) && (negb (Nat.eqb j vi)))
          indexed_doors)
  end.

Notation strict_inside_closed :=
  (strict_inside_closed R QArith_base.Qeq_bool QArith_base.Qle_bool QArith_base.Qplus QArith_base.Qminus QArith_base.Qmult (QArith_base.inject_Z 1) edge left_pt
   right_pt).

Definition add_extremity_reference_point
  (indexed_cells : seq (nat * cell))
  (doors : seq (vert_edge R * nat * nat)) (p : pt R) :=
  if existsb (fun '(v, _, _) => on_vert_edge p v) doors then
    [::]
  else 
    let '(i, c) :=
      head (size indexed_cells, dummy_cell)
        (filter (fun '(i', c') => strict_inside_closed p c')  indexed_cells) in
      [:: ({|ve_x := p_x _ p; ve_top := p_y _ p; ve_bot := p_y _ p|}, i, i)].

Definition doors_and_extremities (indexed_cells : seq (nat * cell))
  (doors : seq (vert_edge R * nat * nat)) (s t : pt R) :=
  add_extremity_reference_point indexed_cells doors s ++
  add_extremity_reference_point indexed_cells doors t ++
  doors.

Definition door_adjacency_map (doors : seq (vert_edge R * nat * nat)) :
  seq (seq nat) :=
  let indexed_doors := index_seq doors in
  map (fun i_d => one_door_neighbors indexed_doors i_d) indexed_doors.

Notation dummy_vert_edge :=
 (dummy_vert_edge R QArith_base.Qminus (QArith_base.inject_Z 1)).

Definition dummy_door := (dummy_vert_edge, 0, 0).

Definition distance (doors : seq (vert_edge R * nat * nat)) (s t : pt R) 
  (i j : nat) :=
  let '(v1, _, _) := nth dummy_door doors i in
  let '(v2, _, _) := nth dummy_door doors j in
  let p1 := vert_edge_to_reference_point s t v1 in
  let p2 := vert_edge_to_reference_point s t v2 in
  pt_distance p1 p2.

Definition cells_to_doors_graph (cells : seq cell) (s t : pt R) :=
  let regular_doors := cells_to_doors cells in
  let indexed_cells := index_seq cells in
  let full_seq_of_doors :=
    doors_and_extremities indexed_cells regular_doors s t in
  let adj_map := door_adjacency_map full_seq_of_doors in
  let neighbors_and_distances :=
    [seq [seq (j, distance full_seq_of_doors s t i j) | j <- neighbors]
        | '(i, neighbors) <- index_seq adj_map] in
      (full_seq_of_doors, neighbors_and_distances).

(* TODO : beware of the case where s and t are on the same door, they can't
   both be the reference point! *)

Import generic_trajectories.

Definition node := nat.

Definition empty := @nil (node * path node * option R).

Notation priority_queue := (list (node * path node * option R)).

Definition node_eqb := Nat.eqb.

Fixpoint find (q : priority_queue) n :=
  match q with
  | nil => None
  | (n', p, d) :: tl => if node_eqb n' n then Some (p, d) else find tl n
  end.

Fixpoint remove (q : priority_queue) n :=
  match q with
  | nil => nil
  | (n', p', d') :: tl =>
    if node_eqb n' n then
      tl
    else
      (n', p', d') :: remove tl n
  end.

Fixpoint insert (q : priority_queue) n p d :=
  match q with
  | nil => (n, p, d) :: nil
  | (n', p', d') :: tl =>
    if cmp_option R QArith_base.Qle_bool d d' then
      (n, p, d) :: q
    else
      (n', p', d') :: insert tl n p d
  end.

Definition update q n p d :=
  insert (remove q n) n p d.

Definition pop  (q : priority_queue) :
   option (node * path node * option R * priority_queue) :=
  match q with
  | nil => None
  | v :: tl => Some (v, tl)
  end.

Section example.

Import QArith.
Check Qedges_to_cells.
Definition bottom := Bedge (Bpt _ 0 0) (Bpt _ 4 0).
Definition top := Bedge (Bpt _ 0 4) (Bpt _ 4 4).
Definition edges := [:: Bedge (Bpt _ 1 2) (Bpt _ 3 2)].
Definition start := Bpt _ 1.2 3.
Definition target := Bpt _ 1.2 1.
Notation Bpt := (smooth_trajectories.Bpt _).

Definition adj := cells_to_doors_graph (Qedges_to_cells bottom top edges)
                      start target.
Compute adj.                      
Compute shortest_path R 0 Qlt_bool Qplus nat Nat.eqb
    (nth nil adj.2) 0%N 1%N _ empty find update pop (iota 0 (size adj.2)).

End example.
