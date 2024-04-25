From mathcomp Require Import all_ssreflect.
Require Import ZArith (* List *) String OrderedType OrderedTypeEx FMapAVL.

Notation head := seq.head.
Notation sort := path.sort.

(* I did not have the courage to understand how to use CoqEAL
  this first version uses only vanilla Coq data structures.  It could still
  use more mathcomp functions, like "has" instead of "existsb" *)

(* FIRST PART: Vertical cell decomposition. *)
(********************************************)
(* The first data structures and algorithms are taken from
   github.com/ybertot/VerticalCells, which was initially a master internship
   by Thomas Portet. *)
(* The main function is edges_to_cells.  The input should respect
  data invariants:
  - all edge extremities are inside the box defined by the bottom and
    top edge
  - all edges should have a left_pt that has a lower x coordinate than the
    right_pt
  - no two edges should cross.
  At the time of writing these lines, the proof of correctness is not
  complete, due to the complexity of the function "step".  Three important
  properties need to be satisfied:
  - edges given in the input never collide with the interior of cells,
  - points in the left_pts and right_pts sequences are vertically aligned
    and are the only potentially colliding points in these segments
  - the elements of left_pts have an x coordinate that is strictly smaller than
    the elements of right_pts *)

Notation seq := list.

Module natmap := FMapAVL.Make Nat_as_OT.

Section generic_implementation.

(* In the original development R has type numFieldType and the various
    operations are taken from that structure. *)
Variable R : Type.

Variables R_eqb R_leb :  R -> R -> bool.

Variables R_add R_sub R_mul R_div : R -> R -> R.

Definition R_ltb : R -> R -> bool :=
  fun x y => andb (negb (R_eqb x y)) (R_leb x y).

Notation "x * y" := (R_mul x y).

Notation "x - y" := (R_sub x y).

Notation "x + y" := (R_add x y).

Variable pt_distance : R -> R -> R -> R -> R.

Variable R1 : R.

Let R0 := R_sub R1 R1.

Let R2 := R_add R1 R1.

Record pt := Bpt {p_x : R; p_y : R}.
(* In the original development, edge have the data invariant that
  the left point has a first coordinate strictly less than the right point. *)

Variable edge : Type.
Variable Bedge : pt -> pt -> edge.
Variables left_pt right_pt : edge -> pt.

Definition same_x (p : pt) (v : R) :=
  R_eqb (p_x p) v.

Record event :=
  Bevent {point : pt; outgoing : seq edge}.

Record cell := Bcell  {left_pts : list pt; right_pts : list pt;
                        low : edge; high : edge}.

Definition dummy_pt := ({| p_x := R1; p_y := R1|}).

Definition dummy_edge := Bedge dummy_pt dummy_pt.

Definition dummy_cell := 
  {| left_pts := nil; right_pts := nil; low := dummy_edge; high := dummy_edge|}.

Definition dummy_event :=
  {| point := dummy_pt; outgoing := nil|}.

(* In the original development pt, edge, and cell are eq_types *)
Definition pt_eqb (a b : pt) : bool :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (R_eqb a_x b_x) && (R_eqb a_y b_y).

Definition edge_eqb (g1 g2 : edge) : bool :=
  pt_eqb (left_pt g1) (left_pt g2) && pt_eqb (right_pt g1) (right_pt g2).

(* The boolean value inc stands for incoming, meaning that we are looking   *)
(* at the right extremity of an edge.                                       *)
Fixpoint add_event (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if inc then (Bevent p nil :: nil)
           else (Bevent p (e :: nil) :: nil)
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if pt_eqb p p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if R_ltb (p_x p) (p_x p1) then
      if inc then
        Bevent p nil :: evs else
        Bevent p (e :: nil) :: evs
    else if R_eqb (p_x p) (p_x p1) && R_ltb (p_y p) (p_y p1) then
       if inc then
         Bevent p nil :: evs else
         Bevent p (e :: nil) :: evs else
    ev1 :: add_event p e inc evs'
  end.

Fixpoint edges_to_events (s : seq edge) : seq event :=
  match s with
  | nil => nil
  | e :: s' =>
    add_event (left_pt e) e false
      (add_event (right_pt e) e true (edges_to_events s'))
  end.

(* this function removes consecutives duplicates, meaning the seq needs
 to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq_aux [A : Type] (eqb : A -> A -> bool) (s : seq A) : (seq A) :=
  match s with
  | nil => nil
  | a::q =>
    match q with
    | nil => s
    | b::r =>
      if eqb a b then no_dup_seq_aux eqb q else a::(no_dup_seq_aux eqb q)
    end
  end.

Notation no_dup_seq := (no_dup_seq_aux pt_eqb).

Definition valid_edge e p := (R_leb (p_x (left_pt e)) (p_x p)) &&
(R_leb (p_x p) (p_x (right_pt e))).

(* TODO: check again the mathematical formula after replacing the infix     *)
(* operations by prefix function calls. *)
Definition vertical_intersection_point (p : pt) (e : edge) : option pt :=
  if valid_edge e p then 
    Some(Bpt (p_x p) (R_add
       (R_mul (R_sub (p_x p) (p_x (left_pt e)))
      (R_div (R_sub (p_y (right_pt e)) (p_y (left_pt e)))
    (R_sub (p_x (right_pt e)) (p_x (left_pt e))))) 
     (p_y (left_pt e))))
    else None.

Section area3_def.

Local Notation "x + y" := (R_add x y).
Local Notation "x - y" := (R_sub x y).
Local Notation "x * y" := (R_mul x y).

Definition area3' (a : pt) (b : pt) (c : pt) : R :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
  let: Bpt c_x c_y := c in
    (((c_x * a_y - a_x * c_y) -
                  (b_x * a_y - a_x * b_y)) +
           b_x * c_y) - c_x * b_y.

Definition area3 (a : pt) (b : pt) (c : pt) : R :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
  let: Bpt c_x c_y := c in
    b_x * c_y + a_x * b_y + c_x * a_y -
    b_x * a_y - a_x * c_y - c_x * b_y.

End area3_def.

Definition point_under_edge (p : pt) (e : edge) : bool :=
  R_leb (area3 p (left_pt e) (right_pt e)) R0.

Notation "p >>> g" := (negb (point_under_edge p g))
  (at level 70, no associativity).

Definition point_strictly_under_edge (p : pt) (e : edge) : bool :=
  R_ltb (area3 p (left_pt e) (right_pt e)) R0.

Notation "p <<< g" := (point_strictly_under_edge p g)
  (at level 70, no associativity).

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
(point_under_edge (left_pt e1) e2 && 
 point_under_edge (right_pt e1) e2)
|| (negb (point_strictly_under_edge (left_pt e2) e1) && 
   negb (point_strictly_under_edge (right_pt e2) e1)).

Definition contains_point (p : pt) (c : cell)  : bool :=
   negb (point_strictly_under_edge p (low c)) && point_under_edge p (high c).

Definition close_cell (p : pt) (c : cell) :=
  match vertical_intersection_point p (low c),
        vertical_intersection_point p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 => 
    Bcell (left_pts c) (no_dup_seq (p1 :: p :: p2 :: nil)) (low c) (high c)
  end.

Definition closing_cells (p : pt) (contact_cells: seq cell) : seq cell :=
  List.map (fun c => close_cell p c) contact_cells.

Definition pvert_y (p : pt) (e : edge) :=
  match vertical_intersection_point p e with
    Some p' => p_y p'
  | None => R0
  end.

Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e high_e : edge) 
  : seq cell * cell :=
  match out with
  | [::] =>
    let op0 := vertical_intersection_point p low_e in
    let op1 := vertical_intersection_point p high_e in
    match (op0,op1) with
    | (None,_) | (_,None) => ([::], dummy_cell)
    | (Some p0,Some p1) =>
      ([::] , Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e)
    end
  | c::q =>
    let op0 := vertical_intersection_point p low_e in
    let (s, nc) := opening_cells_aux p q c high_e in
    match op0 with
    | None => ([::], dummy_cell)
    | Some p0 =>
      (Bcell  (no_dup_seq [:: p; p0]) [::] low_e c :: s, nc)
    end
  end.

Fixpoint open_cells_decomposition_contact open_cells pt :
   option (seq cell * seq cell * cell) :=
if open_cells is c :: q then
  if contains_point pt c then
    if open_cells_decomposition_contact q pt is Some(cc, lc, c') then
      Some(c :: cc, lc, c')
    else
      Some([::], q, c)
  else
    None
else
  None.

Fixpoint open_cells_decomposition_rec open_cells pt : 
  seq cell * seq cell * cell * seq cell :=
if open_cells is c :: q then
  if contains_point pt c then
    if open_cells_decomposition_contact q pt is Some(cc, lc, c') then
      ([::], c :: cc, c', lc)
    else
      ([::], [::], c, q)
  else
    let '(fc, cc, c', lc) := open_cells_decomposition_rec q pt in
    (c :: fc, cc, c', lc)
else
  ([::], [::], dummy_cell, [::]).

Definition open_cells_decomposition (open_cells : seq cell) (p : pt) :
   seq cell * seq cell * cell * seq cell * edge * edge :=
let '(fc, cc, c', lc) := open_cells_decomposition_rec open_cells p in
(fc, cc, c', lc, low (head c' cc), high c').

Record scan_state :=
  Bscan {sc_open1 : seq cell;
         lst_open : cell;
         sc_open2 : seq cell;
         sc_closed : seq cell;
         lst_closed : cell;
         lst_high : edge;
         lst_x : R}.

Definition update_closed_cell (c : cell) (p : pt) : cell :=
  let ptseq := right_pts c in
  let newptseq :=
    (belast (head dummy_pt ptseq) (behead ptseq)) ++
    [:: p; seq.last dummy_pt ptseq] in
  Bcell (left_pts c) newptseq (low c) (high c).

Definition set_left_pts (c : cell) (l : seq pt) :=
  {| left_pts := l; right_pts := right_pts c; low := low c; high := high c |}.

Definition set_pts (c : cell) (l1 l2 : seq pt) :=
  {| left_pts := l1; right_pts := l2; low := low c; high := high c |}.

(* This function is to be called only when the event is in the middle
  of the last opened cell.  The point e needs to be added to the left
  points of one of the newly created open cells, but the one that receives
  the first segment of the last opening cells should keep its existing
  left points.*)
Definition update_open_cell (c : cell) (e : event) : seq cell * cell :=
  let ps := left_pts c in
  if outgoing e is [::] then
    ([::], set_left_pts c [:: head dummy_pt ps, point e & behead ps])
  else
    match
    opening_cells_aux (point e) (sort edge_below (outgoing e))
        (low c) (high c) with
    | ([::], c') => (* this is an absurd case. *)
      ([::], c)
    | (c'::tlc', lc') =>
      (set_left_pts c' (point e :: behead ps) :: tlc', lc')
    end.

Definition update_open_cell_top (c : cell) (new_high : edge) (e : event) :=
  if outgoing e is [::] then
    let newptseq :=
(* when function is called, (point e) should alread be in the left points. *)
      [:: Bpt (p_x (point e)) (pvert_y (point e) new_high) &
          left_pts c] in
      ([::], Bcell newptseq (right_pts c) (low c) new_high)
  else
    match opening_cells_aux (point e) (sort edge_below (outgoing e))
        (low c) new_high with
    | ([::], lc) => (* this is not supposed to happen *) ([::], lc)
    | (f :: q, lc) =>
      (set_left_pts f (point e :: behead (left_pts c)) :: q, lc)
    end.

Definition simple_step (fc cc lc : seq cell) (lcc : cell) (le he : edge)
   (closed_cells : seq cell) (last_closed : cell) ev :=
  let new_closed := closing_cells (point ev) cc in
  let last_new_closed := close_cell (point ev) lcc in
  let closed_cells' := closed_cells ++ last_closed :: new_closed in
  let (nos, lno) :=
    opening_cells_aux (point ev) (sort edge_below (outgoing ev)) le he in
    Bscan (fc ++ nos) lno lc closed_cells' last_new_closed he (p_x (point ev)).

Definition step (st : scan_state) (e : event) : scan_state :=
   let p := point e in
   let '(Bscan op1 lsto op2 cls cl lhigh lx) := st in
   if negb (same_x p lx) then
     let '(first_cells, contact_cells, last_contact, last_cells, 
           lower_edge, higher_edge) :=
       open_cells_decomposition (op1 ++ lsto :: op2) p in
     simple_step first_cells contact_cells last_cells last_contact
       lower_edge higher_edge cls cl e
   else if p >>> lhigh then
     let '(fc', contact_cells, last_contact, last_cells,
           low_edge, higher_edge) :=
       open_cells_decomposition op2 p in
     let first_cells := op1 ++ lsto :: fc' in
     simple_step first_cells contact_cells last_cells last_contact
       low_edge higher_edge cls cl e
   else if p <<< lhigh then 
     let new_closed := update_closed_cell cl (point e) in
     let (new_opens, new_lopen) := update_open_cell lsto e in
     Bscan (op1 ++ new_opens) new_lopen op2 cls new_closed lhigh lx
   else (* here p === lhigh *)
     let '(fc', contact_cells, last_contact, last_cells, lower_edge,
                higher_edge) :=
       open_cells_decomposition (lsto :: op2) p in
       (* we know lsto was just open, so that its left limit is lx
         and its right limit is bounded by p_x (right_pt lhigh), which
         is necessarily p_x (point e). lsto is necessarily the
         first cell of contact_cells.  So the first element of
         contact_cells should not be closed. It can just be
         disregarded. *)
     let closed := closing_cells p (seq.behead contact_cells) in
     let last_closed := close_cell p last_contact in
     let (new_opens, new_lopen) := update_open_cell_top lsto higher_edge e in
     Bscan (op1 ++ fc' ++ new_opens) new_lopen last_cells
          (closed ++ cl :: cls) last_closed higher_edge lx.

Definition leftmost_points (bottom top : edge) :=
  if R_ltb (p_x (left_pt bottom)) (p_x (left_pt top)) then
    if vertical_intersection_point (left_pt top) bottom is Some pt then
       [:: left_pt top; pt]
    else
        [::]
  else
     if vertical_intersection_point (left_pt bottom) top is Some pt then
        no_dup_seq [:: pt; left_pt bottom]
     else
        [::].

Definition rightmost_points (bottom top : edge) :=
  if R_ltb (p_x (right_pt bottom)) (p_x (right_pt top)) then
    if vertical_intersection_point (right_pt bottom) top is Some pt then
       [:: right_pt bottom; pt]
    else
        [::]
  else
     if vertical_intersection_point (right_pt top) bottom is Some pt then
        no_dup_seq [:: pt; right_pt top]
     else
        [::].

Definition complete_last_open (bottom top : edge) (c : cell) :=
  match c with
  | Bcell lpts rpts le he =>
      Bcell lpts (rightmost_points bottom top) le he
  end.

Definition start_open_cell (bottom top : edge) :=
  Bcell (leftmost_points bottom top) [::] bottom top.

Definition start (first_event : event) (bottom : edge) (top : edge) :
  scan_state :=
  let (newcells, lastopen) :=
  opening_cells_aux (point first_event)
      (path.sort edge_below (outgoing first_event)) bottom top in
      (Bscan newcells lastopen [::] [::]
         (close_cell (point first_event) (start_open_cell bottom top))
         top (p_x (point first_event))).

Definition complete_process (events : seq event) (bottom top : edge) : seq cell :=
  match events with
  | [::] => [:: complete_last_open bottom top (start_open_cell bottom top)]
  | ev0 :: events =>
    let start_scan := start ev0 bottom top in
    let final_scan := foldl step start_scan events in
      map (complete_last_open bottom top)
      (sc_open1 final_scan ++ lst_open final_scan :: sc_open2 final_scan) ++
      lst_closed final_scan :: sc_closed final_scan
  end.

(* This is the main function of vertical cell decomposition. *)
Definition edges_to_cells bottom top edges :=
  complete_process (edges_to_events edges) bottom top.

(* SECOND PART : computing a path in the cell graph *)
(* To compute a path that has reasonable optimzation, we compute a shortest *)
(* path between reference points chosen inside doors. *)

Section shortest_path.

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
       (R_ltb x y)%O
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


(* defining the connection relation between adjacent cells.  Two cells
  are adjacent when it is possible to move from one cell directly to the
  other without colliding an obstacle edge.  In the data structure, it means
  that they share a vertical edge. *)
Record vert_edge :=
 { ve_x : R; ve_top : R; ve_bot : R}.

Definition vert_edge_eqb (v1 v2 : vert_edge) :=
  let: Build_vert_edge v1x v1t v1b := v1 in
  let: Build_vert_edge v2x v2t v2b := v2 in
  R_eqb v1x v2x && R_eqb v1t v2t && R_eqb v1b v2b.

Fixpoint seq_to_intervals_aux [A : Type] (a : A) (s : seq A) :=
match s with
| nil => nil
| b :: tl => (a, b) :: seq_to_intervals_aux b tl
end.

Definition seq_to_intervals [A : Type] (s : seq A) :=
match s with
  nil => nil
| a :: tl => seq_to_intervals_aux a tl
end.

(* Vertical edges are collected from the left_pts and right_pts sequences. *)
Definition cell_safe_exits_left (c : cell) : seq vert_edge :=
  let lx := p_x (head dummy_pt (left_pts c)) in
  map (fun p => Build_vert_edge lx (p_y (fst p)) (p_y (snd p))) 
   (seq_to_intervals (left_pts c)).

Definition cell_safe_exits_right (c : cell) : seq vert_edge :=
  let lx := p_x (head dummy_pt (right_pts c)) in
  map (fun p => Build_vert_edge lx (p_y (fst p)) (p_y (snd p))) 
   (seq_to_intervals (rev (right_pts c))).

Definition index_seq {T : Type} (s : list T) : list (nat * T) :=
  zip (iota 0 (size s)) s.

Definition cells_to_doors (s : list cell) :=
  let indexed_s := index_seq s in
  let vert_edges_and_right_cell :=
    flatten (map (fun '(i, c) => 
                   (map (fun v => (v, i))) (cell_safe_exits_left c))
      indexed_s) in
  let vert_edges_and_both_cells :=
    flatten (map (fun '(v, i) => 
          (map (fun '(i', c') => (v, i, i'))
               (filter (fun '(i', c') =>
                   existsb (vert_edge_eqb v) (cell_safe_exits_right c'))
                   indexed_s)))
           vert_edges_and_right_cell) in 
      vert_edges_and_both_cells.

Definition on_vert_edge (p : pt) (v : vert_edge) : bool :=
  R_eqb (p_x p) (ve_x v) && R_ltb (ve_bot v) (p_y p) &&
  R_ltb (p_y p) (ve_top v).

Definition vert_edge_midpoint (ve : vert_edge) : pt :=
  {|p_x := ve_x ve; p_y := R_div ((R_add (ve_top ve) (ve_bot ve))) R2|}.
 
Definition vert_edge_to_reference_point (s t : pt) (v : vert_edge) :=
  if on_vert_edge s v then s
  else if on_vert_edge t v then t
  else vert_edge_midpoint v.

Definition one_door_neighbors
  (indexed_doors : seq (nat * (vert_edge * nat * nat)))
  (i_d : nat * (vert_edge * nat * nat)) : list nat :=
  match i_d with
  | (j, (v0, i0, i'0)) =>
    map fst
      (filter (fun '(vi, (v, i, i')) => (Nat.eqb i i0  || Nat.eqb i i'0 ||
              Nat.eqb i' i0 || Nat.eqb i' i'0) && (negb (Nat.eqb j vi)))
          indexed_doors)
  end.

Definition left_limit (c : cell) := p_x (seq.last dummy_pt (left_pts c)).

Definition right_limit c := p_x (seq.last dummy_pt (right_pts c)).

Definition strict_inside_closed p c :=
  negb (point_under_edge p (low c)) &&
  point_strictly_under_edge p (high c) &&
 (R_ltb (left_limit c) (p_x p) &&
 (R_ltb (p_x p) (right_limit c))).

Definition add_extremity_reference_point
  (indexed_cells : seq (nat * cell))
  (doors : seq (vert_edge * nat * nat)) (p : pt) :=
  if existsb (fun '(v, _, _) => on_vert_edge p v) doors then
    [::]
  else 
    let '(i, c) :=
      head (size indexed_cells, dummy_cell)
        (filter (fun '(i', c') => strict_inside_closed p c')  indexed_cells) in
      [:: ({|ve_x := p_x p; ve_top := p_y p; ve_bot := p_y p|}, i, i)].

Definition doors_and_extremities (indexed_cells : seq (nat * cell))
  (doors : seq (vert_edge * nat * nat)) (s t : pt) :=
  add_extremity_reference_point indexed_cells doors s ++
  add_extremity_reference_point indexed_cells doors t ++
  doors.

Definition door_adjacency_map (doors : seq (vert_edge * nat * nat)) :
  seq (seq nat) :=
  let indexed_doors := index_seq doors in
  map (fun i_d => one_door_neighbors indexed_doors i_d) indexed_doors.

Definition dummy_vert_edge :=
  {| ve_x := R0; ve_top := R0; ve_bot := R0|}.

Definition dummy_door := (dummy_vert_edge, 0, 0).

Definition distance (doors : seq (vert_edge * nat * nat)) (s t : pt) 
  (i j : nat) :=
  let '(v1, _, _) := seq.nth dummy_door doors i in
  let '(v2, _, _) := seq.nth dummy_door doors j in
  let p1 := vert_edge_to_reference_point s t v1 in
  let p2 := vert_edge_to_reference_point s t v2 in
  pt_distance (p_x p1) (p_y p1) (p_x p2) (p_y p2).

Definition cells_to_doors_graph (cells : seq cell) (s t : pt) :=
  let regular_doors := cells_to_doors cells in
  let indexed_cells := index_seq cells in
  let full_seq_of_doors :=
    doors_and_extremities indexed_cells regular_doors s t in
  let adj_map := door_adjacency_map full_seq_of_doors in
  let neighbors_and_distances :=
    [seq [seq (j, distance full_seq_of_doors s t i j) | j <- neighbors]
        | '(i, neighbors) <- index_seq adj_map] in
      (full_seq_of_doors, neighbors_and_distances).

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
    if cmp_option d d' then
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

Definition c_shortest_path cells s t :=
  let adj := cells_to_doors_graph cells s t in
  (adj, shortest_path node node_eqb (seq.nth [::] adj.2) 0%N 1%N _ empty
   find update pop (iota 0 (size adj.2))).

Definition midpoint (p1 p2 : pt) : pt :=
 {| p_x := R_div (R_add (p_x p1) (p_x p2)) R2;
    p_y := R_div (R_add (p_y p1) (p_y p2)) R2|}.

Definition cell_center (c : cell) :=
  midpoint
    (midpoint (seq.last dummy_pt (left_pts c)) 
              (head dummy_pt (right_pts c)))
    (midpoint (head dummy_pt (left_pts c))
              (seq.last dummy_pt (right_pts c))).

Record annotated_point :=
  Apt { apt_val : pt; door_index : option nat; cell_indices : seq nat}.

Definition safe_intermediate_point_in_cell (p1 p2 : pt) (c : cell)
   (ci : nat) :=
  let new_x := p_x (cell_center c) in
  let new_y := R_div (R_add (p_y p1) (p_y p2)) R2 in
  let new_pt := {|p_x := new_x; p_y := new_y|} in
    if strict_inside_closed new_pt c then
      Apt new_pt None (ci :: nil)
    else
      Apt (cell_center c) None (ci :: nil).

Definition intersection (s1 s2 : seq nat) :=
  [seq x | x <- s1 & existsb (fun y => Nat.eqb x y) s2].

Definition common_index (s1 s2 : seq nat) :=
  let intersect := intersection s1 s2 in
  seq.head 0 intersect.

Definition door_to_annotated_point s t (d : vert_edge * nat * nat) 
  (door_index : nat) :=
  let p' := vert_edge_to_reference_point s t d.1.1 in
  let annot :=
    if Nat.eqb d.1.2 d.2 then [:: d.2] else [:: d.1.2 ; d.2] in
  Apt p' (Some door_index) annot.

Fixpoint a_shortest_path (cells : seq cell)
  (doors : seq (vert_edge * nat * nat) * seq (seq (nat * R)))
  s t (p : annotated_point) (path : seq node) :=
  match path with
  | nil => [:: p]
  | p'i :: tlpath =>
    let d' := seq.nth dummy_door doors.1 p'i in
    let a_p' := door_to_annotated_point s t d' p'i in
    if R_eqb (p_x (apt_val p)) (p_x (apt_val a_p')) then
       let ci := common_index (cell_indices p) (cell_indices a_p') in
       let p_extra : annotated_point := 
         safe_intermediate_point_in_cell (apt_val p) (apt_val a_p')
           (seq.nth dummy_cell cells ci) ci in
       p :: p_extra :: a_shortest_path cells doors s t a_p' tlpath
    else
       p :: a_shortest_path cells doors s t a_p' tlpath
  end.

Fixpoint path_to_segments (p : annotated_point)
   (path : seq annotated_point) : seq (annotated_point * annotated_point) :=
  match path with
  | nil => nil
  | p' :: tl => (p, p') :: path_to_segments p' tl
  end.

Definition path_reverse (s : seq (annotated_point * annotated_point)) :=
  List.map (fun p => (snd p, fst p)) (List.rev_append s nil).

Definition source_to_target
 (cells : seq cell) (source target : pt) :
  option (seq (vert_edge * nat * nat) *
          seq (annotated_point * annotated_point)) :=
  let main := c_shortest_path cells source target in
  let doors := main.1 in
  let opath := main.2 in
  let last_point := 
     door_to_annotated_point source target
         (seq.nth dummy_door doors.1 1) 1 in
  if opath is Some path then
    match a_shortest_path cells doors source target
              last_point path with
    | nil => None
    | a :: tl => Some(doors.1, path_reverse (path_to_segments a tl))
    end
  else
    None.

(* THIRD PART: Producing a smooth trajectory. *)
(* We produce a smooth trajectory by replacing every angle by a Bezier curve.
   We first add anchor points in the middle of each straight line segment.
   These anchor points only have the constraints to be in a single cell and
   the curve will pass through these anchor points no matter what
   transformation will happen later.  Then broken line paths between
   anchor points are replaced by Bezier curves, thus keeping the invariant
   that the new smooth path connects the anchor points correctly.  *)

(* The point of this function is to add anchor points in the middle
  of each segment.  The annotation for these anchor points is the
  cell in which they appear, but this information is not going to play
  a significant role in the current version of the program. *)
Fixpoint break_segments (s : seq (annotated_point * annotated_point)) :
  seq (annotated_point * annotated_point) :=
  match s with
  | (Apt p1 door_index1 a1, Apt p2 door_index2 a2) :: tl =>
    (Apt p1 door_index1 a1, Apt (midpoint p1 p2) None (intersection a1 a2)) ::
    (Apt (midpoint p1 p2) None (intersection a1 a2), Apt p2 door_index2 a2) ::
        break_segments tl
  | nil => nil
  end. 

(* The connection at anchor points is straight (because it comes
   from a straight line segment.  The connection between two anchor points
   is a broken line (an angle).  The idea is to replace this broken line
   by a bezier curve, which by construction will be tangent with the
   initial segment.  However, there may be cases where this Bezier curve does
   not pass through the authorized door. *)
Variant curve_element :=
 straight (x y : annotated_point) | bezier (x y z : annotated_point).

(* This function assumes that every other straight line segment goes into
  an angle, and the other go into a straight connection.  The angles
  (represented by adjacent pairs) are then replace by Bezier curves. 
  the last element is left as is. *)
(* The input of this function is guaranteed to have b = b' in the second
  pattern matching rule below. *)
Fixpoint smoothen_aux (s : seq (annotated_point * annotated_point)) :
   seq curve_element :=
match s with
| nil => nil
| (a, b) :: nil => straight a b :: nil
(* Here we know the anonymous variable to have the same value as b *)
| (a, b) :: (_ , c) :: tl => bezier a b c :: smoothen_aux tl
end.

(* Here we move from a sequence of straight line segments given by pairs
  of points with anchor points to a sequence of curve elements.
  Actually only the first one and the last one are straight, all the rest
  are Bezier curve elements. *)
Definition smoothen (s : seq (annotated_point * annotated_point)) :
   seq curve_element :=
match s with
| (a, b)  :: tl => straight a b :: smoothen_aux tl
| nil => nil
end.

(* The curve produced by smoothen only guarantees to be a continuous
   path from the initial point to the last point going through the anchor
   points, but now we have lost the guarantee that this path goes through
   the doors. The next functions detect collisions and repair the curve. *)

(* We now have two functions to check whether a Bezier curve does pass
  through the door.  They implement specialized code and require fuel to
  operate. the result is an optional boolean.  When the boolean is given
  and true, we are sure the curve passes through the door, when the
  boolean is given and false, we are sure the curve hits an obstacle,
  when the boolean is not given (answer is None), we don't know, but
  for this algorithm, this is interpreted as a failure to pass through the
  door.  In practice, the fuel does not need to be big, because curve size
  is divided by 2 at each iteration.

  This function is to be used when p_x a < p_x b < p_x c and
  a b c is ccw (counter clockwise). It assumes that there is no need to
 check the bottom point. *)
Fixpoint check_bezier_ccw (fuel : nat) (v : vert_edge)
  (a b c : pt) : 
  option bool :=
match fuel with
| O => None
| S p =>
  let top_edge := Bpt (ve_x v)  (ve_top v) in
  if negb (point_under_edge top_edge (Bedge a c)) then
    Some true
  else if
     point_under_edge top_edge (Bedge a b) ||
     point_under_edge top_edge (Bedge b c)
  then 
    Some false
  else
    let b' := midpoint a b in
    let b2 := midpoint b c in
    let c' := midpoint b' b2 in
    if R_ltb (p_x c') (ve_x v) then
      check_bezier_ccw p v c' b2 c
    else if R_ltb (ve_x v) (p_x c') then
      check_bezier_ccw p v a b' c'
    else
      if R_ltb (p_y c') (ve_top v) then
         Some true
      else
         Some false
end.

(* This function is to be used when p_x a < p_x b < p_x c and
  a b c is cw (clockwise).
  It assumes that there is no need to check the top point. *)
Fixpoint check_bezier_cw (fuel : nat) (v : vert_edge)
  (a b c : pt) : 
  option bool :=
match fuel with
| O => None
| S p =>
  let bot_edge := Bpt (ve_x v)  (ve_bot v) in
  if point_strictly_under_edge bot_edge (Bedge a c) then
    Some true
  else if
     negb (point_strictly_under_edge bot_edge (Bedge a b)) ||
     negb (point_strictly_under_edge bot_edge (Bedge b c))
  then 
    Some false
  else
    let b' := midpoint a b in
    let b2 := midpoint b c in
    let c' := midpoint b' b2 in
    if R_ltb (p_x c') (ve_x v) then
      check_bezier_cw p v c' b2 c
    else if R_ltb (ve_x v) (p_x c') then
      check_bezier_cw p v a b' c'
    else
      if R_ltb (ve_bot v) (p_y c') then
         Some true
      else
         Some false
end.

(* This function verifies that the Bezier curve does pass through the
  door that was initially given has a constraint for the broken line.  This
  is done by performing a dichotomy on the Bezier curve until we either 
  see explicitely that the condition is met or that the condition is
  violated.  When the condition is violated, a new Bezier curve is proposed
  and by creating two new anchor points half way between the previous
  anchor points and the chosen point (normally the middle of the door) and
  verification starts again with the new Bezier curve, which is closer to
  the broken line trajectory.
  This function should normally be based on well-founded recursion, but
  for executability we rely on a fuel, which does not need to be enormous
  because the size of the bezier curve element is divided by 2 at each
  iteration.
  This function may replace a faulty curve element with a sequence of
  three new elements, so all results have to be concatened later. *)
Definition fuel_constant := 20.

Fixpoint check_curve_element_and_repair
  (fuel : nat) doors (e : curve_element) :
   seq curve_element :=
match e with
| straight p1 p2 => straight p1 p2 :: nil
| bezier p1 p2 p3 =>
  if door_index p2 is Some n then
    let vedge :=
       (seq.nth dummy_door doors n).1.1 in
    let e' :=
      (if R_ltb (p_x (apt_val p1)) (p_x (apt_val p2)) then
        bezier p1 p2 p3
      else
        bezier p3 p2 p1) in
    match e' with
    |straight _ _ => e' :: nil
    | bezier p1' p2' p3' =>
      let check_function :=
      if R_ltb R0 
          (area3 (apt_val p1') (apt_val p2') (apt_val p3')) then
          check_bezier_ccw
      else
          check_bezier_cw in
        match check_function fuel_constant vedge
                  (apt_val p1')(apt_val p2')(apt_val p3') with
        | Some true => bezier p1 p2 p3 :: nil
        | _ => 
          match fuel with
          | S p =>
            straight p1 
               (Apt (midpoint (apt_val p1) (apt_val p2)) 
                    None (cell_indices p1))
              ::
              check_curve_element_and_repair p doors
                (bezier (Apt (midpoint (apt_val p1) (apt_val p2)) None
                       (cell_indices p1))
                 p2
                 (Apt (midpoint (apt_val p2) (apt_val p3)) None (cell_indices p3)))
              ++
              straight (Apt (midpoint (apt_val p2) (apt_val p3))
                    None (cell_indices p3)) p3 :: nil
          | _ =>
            straight p1 p2 :: straight p2 p3 :: nil
          end
        end
    end
  else
    (bezier p1 p2 p3 :: nil)
end.

Definition smooth_from_cells (cells : seq cell)
  (initial final : pt) : seq curve_element :=
  match source_to_target cells initial final with
  | Some (doors, s) => List.concat
       (List.map (check_curve_element_and_repair fuel_constant doors)
                              (smoothen (break_segments s)))
  | None => nil
  end.

(* This function wraps up all operations:
  - constructing the cells
  - constructing the broken line
  - constructing the smooth line
  - repairing the faulty bezier elements. *)
Definition smooth_point_to_point (bottom top : edge) (obstacles : seq edge)
  (initial final : pt) : seq curve_element :=
  let cells := edges_to_cells bottom top obstacles in
  smooth_from_cells cells initial final.

End generic_implementation.
