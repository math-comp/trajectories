From mathcomp Require Import all_ssreflect.
Require Import ZArith QArith List String OrderedType OrderedTypeEx FMapAVL.
Require Import generic_trajectories.

Definition Qlt_bool x y := andb (negb (Qeq_bool x y)) (Qle_bool x y).

Record edge := Bedge {left_pt : pt Q; right_pt : pt Q}.

Notation R := Q.
Notation pt := (pt Q).
Notation Bpt := (Bpt Q).
Notation dummy_pt := (dummy_pt Q 1).
Notation p_x := (p_x Q).
Notation p_y := (p_y Q).
Notation cell := (cell Q edge).
Notation left_pts := (left_pts Q edge).
Notation right_pts := (right_pts Q edge).
Notation dummy_cell := (dummy_cell Q 0 edge Bedge).
Notation low := (low Q edge).
Notation high := (high Q edge).
Notation event := (event Q edge).
Notation point := (point Q edge).
Notation outgoing := (outgoing Q edge).

Definition scan :=
  complete_process Q Qeq_bool Qle_bool 
    Qplus Qminus Qmult Qdiv 0 edge Bedge left_pt right_pt.

Definition edges_to_events :=
  edges_to_events Q Qeq_bool Qle_bool edge left_pt right_pt.

(* This is the main function of vertical cell decomposition. *)
Definition edges_to_cells bottom top edges :=
  scan (edges_to_events edges) bottom top.

(* SECOND PART : computing a path in the cell graph *)
(* This code is taken from github.com/ybertot/breadth_first_search.
   the proof of this code is probably complete in that repository. *)

Section bfs.

Variable (state move : Type).
Variable (state_fmap : Type).
Variable find : state_fmap -> state -> option move.
Variable add : state_fmap -> state -> move -> state_fmap.
Variable (step : state -> list (state * move)).
Variable (state_eq_dec : forall s1 s2 : state, {s1 = s2}+{s1 <> s2}).

Variable map_order : state_fmap -> state_fmap -> Prop.
Hypothesis map_order_wf : well_founded map_order.
Hypothesis add_order : forall map s v,
  find map s = None -> map_order (add map s v) map.
Hypothesis map_order_trans : forall map2 map1 map3,
  map_order map1 map2 -> map_order map2 map3 -> map_order map1 map3.

Fixpoint bfs_aux (w w2 : list (state * move))
  (sufficient : state)
  (settled : state_fmap) : (list (state * move) * state_fmap) :=
match w with
| (s, m) :: w' =>
  match find settled s with
  | Some _ => bfs_aux w' w2 sufficient settled
  | None =>
    if state_eq_dec s sufficient then
      (nil, add settled s m)
    else
    bfs_aux w' (step s ++ w2) sufficient (add settled s m)
  end
| nil => (w2, settled)
end.

Fixpoint bfs (fuel : nat) (w : list (state * move)) (settled : state_fmap) 
  (sufficient : state)
  (round : nat) :
  (state_fmap * nat) + (list (state * move) * state_fmap) :=
  match fuel with
  | O => inr (w, settled)
  | S p =>
    match bfs_aux w nil sufficient settled with
    | (nil, s) => inl (s, round)
    | (w, s) => bfs p w s sufficient (round + 1)
    end
  end.

  (* We then explain how we build a path using the database. *)
Fixpoint make_path (db : state_fmap)
(targetb : state -> bool) (play : state -> move -> option state)
(x : state) (fuel : nat) :=
match fuel with
| O => None
| S p =>
if targetb x then
  Some nil
else
  match find db x with
  | None => None
  | Some m =>
    match play x m with
    | Some y =>
      match make_path db targetb play y p with
      | None => None
      | Some l => Some (m :: l)
      end
   | None => None
   end
  end
end.

End bfs.

(* defining the connection relation between adjacent cells.  Two cells
  are adjacent when it is possible to move from one cell directly to the
  other with colliding an obstacle edge.  In the data structure, it means
  that they share a vertical edge. *)
Record vert_edge :=
 { ve_x : Q; ve_top : Q; ve_bot : Q}.

Definition vert_edge_eqb (v1 v2 : vert_edge) :=
  let: Build_vert_edge v1x v1t v1b := v1 in
  let: Build_vert_edge v2x v2t v2b := v2 in
  Qeq_bool v1x v2x && Qeq_bool v1t v2t && 
  Qeq_bool v1b v2b.

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

Definition all_doors (cells : seq cell) : seq (vert_edge * nat) :=
  List.concat
    (List.map (fun i => List.map (fun v => (v, i))
                  (cell_safe_exits_right (nth i cells dummy_cell)))
         (seq.iota 0 (List.length cells))).

Definition door_right_cell (cells : seq cell) (v : vert_edge) :=
  find (fun i => existsb (fun v' => vert_edge_eqb v v')
           (cell_safe_exits_left (nth i cells dummy_cell)))
     (seq.iota 0 (List.length cells)).

Definition vert_edge_midpoint (ve : vert_edge) : pt :=
  Bpt (ve_x ve) ((ve_top ve + ve_bot ve) / 2).


(* connection from left to right is obtained by computing an intersection. *)
Definition lr_connected (c1 c2 : cell) : bool :=
  existsb (fun v => existsb (fun v' => vert_edge_eqb v v')
                       (cell_safe_exits_left c2))
       (cell_safe_exits_right c1).

Definition bi_connected c1 c2 :=
  lr_connected c1 c2 || lr_connected c2 c1.

Definition dummy_vert_edge :=
  {| ve_x := 0; ve_top := 0; ve_bot := 0|}.

Module natmap := FMapAVL.Make Nat_as_OT.

Definition bfs_find : natmap.t nat -> nat -> option nat :=
  (fun m k => natmap.find k m).

Definition bfs_add : natmap.t nat -> nat -> nat -> natmap.t nat :=
  (fun m k v => natmap.add k v m).

Definition reverse_step cells cell_i : seq (nat * nat) :=
  map (fun i => (i, cell_i))
    (filter (fun c_i => bi_connected (nth c_i cells dummy_cell)
                       (nth cell_i cells dummy_cell))
     (seq.iota 0 (List.length cells))).

(* To compute a path between two cells we use as input the list of cells
   and indices of two cells in this list (source and target).  This builds
   a table.  This table construction is interrupted as soon as a path
   from source_i to target_i is found, and this path is guaranteed to be
   of minimal length in terms of numbers of cells encountered. The result
   is in a sum type, where only the right variant would mean that no path
   has been found before exhaustion of some fuel.  But here, it is assumed
   that the fuel (length of cells) is going to be enough to find all cells
   connected to target_i. *)
Definition cell_connection_table (cells : seq cell) (source_i target_i : nat) :=
    bfs _ _ _ bfs_find bfs_add (reverse_step cells) eq_nat_dec
    (List.length cells) ((target_i, target_i) :: nil) (natmap.empty nat)
    source_i 0.

Definition cell_path (cells : seq cell) (source_i target_i : nat) :
  option (seq nat) :=
  match cell_connection_table cells source_i target_i with
  | inr _ => None
  | inl (table, _) =>
    make_path _ _ _ bfs_find table (fun c_i => Nat.eqb c_i target_i)
      (fun n1 n2 => Some n2) source_i (List.length cells)
  end.

(* Given two cells, we define the door from one cell to the other to
  be the common edge between these cells.  In example known so far, there
  is only one such door, but this may change in the future.  For now, we
  take arbitrarily the first one we find (the top one or the bottom one
  depending on the exits are ordered).  If the two cells are not adjacent,
  dummy_vert_edge is returned.  Maybe this should be made safer by returning
  an option type. *)
Definition lr_door (c1 c2 : cell) : vert_edge :=
  head dummy_vert_edge
     (filter (fun x => existsb (fun x' => vert_edge_eqb x x')
                  (cell_safe_exits_left c2)) (cell_safe_exits_right c1)).

Definition left_limit (c : cell) := p_x (seq.last dummy_pt (left_pts c)).

Definition right_limit c := p_x (seq.last dummy_pt (right_pts c)).

(* This function is like lr_door, but it is more precise, as it
  can be applied when the doors are connected but not lr_connected as it
  returns None in case the two given cells are not adjacent. *)
Definition common_vert_edge (c1 c2 : cell) : option vert_edge:=
  if Qeq_bool (right_limit c1) (left_limit c2) then
    find (fun v => existsb (fun v' => vert_edge_eqb v v')
                      (cell_safe_exits_left c2))
      (cell_safe_exits_right c1)
  else
    find (fun v => existsb (fun v' => vert_edge_eqb v v')
                      (cell_safe_exits_left c1))
      (cell_safe_exits_right c2).

Definition midpoint (p1 p2 : pt) : pt :=
 Bpt ((p_x p1 + p_x p2) / 2) ((p_y p1 + p_y p2) / 2).

Definition cell_center (c : cell) :=
  midpoint
    (midpoint (seq.last dummy_pt (left_pts c)) 
              (head dummy_pt (right_pts c)))
    (midpoint (head dummy_pt (left_pts c))
              (seq.last dummy_pt (right_pts c))).

Record annotated_point :=
  Apt { apt_val : pt; cell_indices : seq nat}.

Definition on_vert_edge (p : pt) (v : vert_edge) : bool :=
  Qeq_bool (p_x p) (ve_x v) && Qlt_bool (ve_bot v) (p_y p) &&
  Qlt_bool (p_y p) (ve_top v).

(* This function assumes a straight line to the door is safe.  For annotations
  it supposes the first cell index corresponds to the cell containing p.
  It returns nil if there is no door, and nil or a faulty edge if
  the other conditions are not met. *)
Definition point_to_door (cells : seq cell) (p : annotated_point) (c1i c2i : nat) :
   seq (annotated_point * annotated_point) :=
let c1 := nth c1i cells dummy_cell in
let c2 := nth c2i cells dummy_cell in
match common_vert_edge c1 c2 with
  Some v =>
    if (Qeq_bool (p_x (apt_val p)) (ve_x v)) && negb (on_vert_edge (apt_val p) v) then
      (p, Apt (cell_center c1) (c1i::nil)) ::
      (Apt (cell_center c1) (c1i :: nil), Apt (vert_edge_midpoint v) (c1i :: c2i :: nil)) :: nil
    else
      (p, Apt (vert_edge_midpoint v) (c1i :: c2i :: nil)) :: nil
| None => nil
end.

Definition path_reverse (s : seq (annotated_point * annotated_point)) :=
  List.map (fun p => (snd p, fst p)) (List.rev_append s nil).

(* This function creates a safe path from the door between
  c1 and c2 and the door between c2 and c3.  When op1 and op2
  are not provided, midpoints are used as path anchors,
  when p1 and p2 are provided they are used instead.
  This function assumes that p1 and p2 are members of the
  respective doors (c1-c2) and (c2-c3) *)
Definition to_next_door (op1 op2 : option pt)
  (cells : seq cell)
  (c1i c2i c3i : nat) : seq (annotated_point * annotated_point) :=
let c2 := nth c2i cells dummy_cell in
let p1 := match op1 with
          | Some p1 => p1
          | None =>
            match common_vert_edge (nth c1i cells dummy_cell) c2 with
            | Some v => vert_edge_midpoint v
            | None => dummy_pt
            end
          end in
let p2 := match op2 with
          | Some p2 => p2
          | None =>
            match common_vert_edge c2 (nth c3i cells dummy_cell) with
            | Some v => vert_edge_midpoint v
            | None => dummy_pt
            end
          end in
if Qeq_bool (p_x p1) (p_x p2) then
  let intermediate_point :=
    Apt (cell_center c2) (c2i :: nil) in
  (Apt p1 (c1i :: c2i :: nil), intermediate_point) ::
  (intermediate_point, Apt p2 (c2i :: c3i :: nil)) :: nil
else
  (Apt p1 (c1i :: c2i :: nil), Apt p2 (c2i :: c3i :: nil)) :: nil.

(* Given a sequence of cells c_i, and a sequence of indices i1, i2, ... 
   (where the ... are refered to as tl), we want to create a list of
   points, making it possible to move from door to door so that the all
   all list of points is describes a broken line moving from the door
   between i1 and i2 to the door between the last two elements of
   (i1, i2, & tl).  Adding paths to the first and last doors will make it
   easy to have a path from any point in cell i1 to any point in the last
   cell of (i1, i2, & tl). when optional points are provided, they
   are points in the first and last door. *)
Fixpoint door_to_door (cells : seq cell)
  (i1 i2 : nat) (opt_source opt_target : option pt)(tl : seq nat) :
  seq (annotated_point * annotated_point) :=
  match tl with
  | nil => nil
  | i3 :: nil =>
    to_next_door opt_source opt_target cells i1 i2 i3
  | i3 :: tl' =>
    let tail_path := door_to_door cells i2 i3 None opt_target tl' in
    to_next_door opt_source None cells i1 i2 i3 ++ tail_path
  end.

(* This function computes a path (broken line) between a point
  in a cell and a point in another cell, going through the midpoint of
  the door between the two cells.  the points are annotated with the
  constraint they have to satisfied: the cells of which they have to
  be members of. This annotation is important because smoothing will
  replace these points with other points that have to satisfy the same
  constraint. *)
Definition path_adjacent_cells (cells : seq cell) (source target : pt)
  (source_i target_i : nat) : option (seq (annotated_point * annotated_point)) :=
  let source_cell := nth source_i cells dummy_cell in
  let target_cell := nth target_i cells dummy_cell in
  match common_vert_edge source_cell target_cell with
  | Some v => 
    Some ((Apt source (source_i :: nil), 
           Apt (vert_edge_midpoint v) (source_i :: target_i :: nil)) ::
              (Apt (vert_edge_midpoint v) (source_i :: target_i :: nil),
               Apt target (target_i :: nil)) :: nil)
  | None => None
  end.

Definition point_under_edge :=
  point_under_edge Q Qle_bool Qplus Qminus Qmult 0 edge left_pt right_pt.

Definition point_strictly_under_edge :=
  point_strictly_under_edge  Q Qeq_bool Qle_bool Qplus Qminus Qmult 0 edge
  left_pt right_pt.

Definition strict_inside_closed p c :=
  negb (point_under_edge p (low c)) &&
  point_strictly_under_edge p (high c) &&
 (Qlt_bool (left_limit c) (p_x p) &&
 (Qlt_bool (p_x p) (right_limit c))).

(* find_origin_cells returns a list of cell indices. *)
(* If the list is empty, it should mean that the point is not in the
  safe part of the work space (it is either outside the box or on
  one of the obstacle edges).  If the list has only one element,
  the point is inside the indexed cell.  If the list has two
  elements, this means that the point is in the door between the
  two indexed cells. *)
Definition find_origin_cells (cells : seq cell) (p : pt) : seq nat :=
  match find (fun i => strict_inside_closed p (nth i cells dummy_cell))
         (seq.iota 0 (List.length cells)) with
  | Some n => n :: nil
  | None =>
    head nil
    (List.map (fun av => snd av ::
                match door_right_cell cells (fst av) with
                | Some rc => rc :: nil
                | None => nil
                end)
      (filter (fun av => on_vert_edge p (fst av)) (all_doors cells)))
  end.

Definition intersection (s1 s2 : seq nat) :=
  filter (fun e => existsb (fun e' => Nat.eqb e e')
                      s2) s1.

Definition point_to_point
 (cells : seq cell) (source target : pt) :
  option (seq (annotated_point * annotated_point)) :=
let source_is := find_origin_cells cells source in
let target_is := find_origin_cells cells target in
if Nat.ltb 0 (List.length source_is) && Nat.ltb 0 (List.length target_is) then
  if Nat.ltb 0 (List.length (intersection source_is target_is)) then
    Some ((Apt source source_is, Apt target target_is) :: nil)
  else
    let ocp := cell_path cells (head 0%nat source_is) (head 0%nat target_is) in
    match ocp with
    Some cp =>
      (* The first element of the path is (head 0 source_is), *)
      if 2 <=? List.length cp then
      (* looking
         at a length larger than 2 actually means the path has at least 3 fenceposts
         and at least 2 intervals:
         head source_is (nth 0 cp 0)  (nth 1 cp 0)
         so there are (at least) 2 doors. *)
        if existsb (Nat.eqb (nth 0 cp 0%nat)) source_is then
        (* It can only be the case that the source is on a door, and
         that the two cells concerned with the first hop are the
         two cells of this door.  In this case, there is no need
         to draw a first path element from from the source point to the
         vertical edge midpoint, since the first point is already
         on the door, and that the target is not in the second cell
         of the path, so the length of cp is strictly larger than 2 *)
           if existsb (Nat.eqb (nth (List.length cp - 2) cp 0%nat)) target_is then
             (* Here target_is is in the penultimate cell of the path *)
             Some (door_to_door cells (head 0%nat source_is) (nth 0 cp 0%nat)
                 (Some source) (Some target) (seq.behead cp (* (seq.behead cp) *)))
           else
             Some (door_to_door cells (head 0%nat source_is) (nth 0 cp 0%nat) (Some source) None
                 (seq.behead cp) ++
                 path_reverse (point_to_door cells (Apt target target_is)
                    (nth (List.length cp - 1) cp 0%nat)
                    (nth (List.length cp - 2) cp 0%nat)))
        else
          if existsb (Nat.eqb (nth ((List.length cp) - 2) cp 0%nat)) target_is then
             Some ((point_to_door cells (Apt source source_is) (head 0%nat source_is)
                        (nth 0 cp 0%nat)) ++
             door_to_door cells (head 0%nat source_is) (nth 0 cp 0%nat) None (Some target)
                 (seq.behead cp))
          else
             Some (point_to_door cells (Apt source source_is) (head 0%nat source_is) (nth 0 cp 0%nat) ++
             door_to_door cells (head 0%nat source_is) (nth 0 cp 0%nat) None None
                 (seq.behead cp) ++
                 path_reverse (point_to_door cells (Apt target target_is)
                    (nth (List.length cp - 1) cp 0%nat)
                    (nth (List.length cp - 2) cp 0%nat)))
      else
      (* if cp has length 1, then there is only one door. if one of the
         point is on the door, it can be connected to the other, *)
         match common_vert_edge (nth (head 0%nat source_is) cells dummy_cell)
                                (nth (head 0%nat target_is) cells dummy_cell) with
         | Some v =>
           if on_vert_edge source v || on_vert_edge target v then
              Some ((Apt source source_is, Apt target target_is) :: nil)
           else
              Some (point_to_door cells (Apt source source_is) (head 0%nat source_is)
                 (head 0%nat target_is) ++
                   path_reverse (point_to_door cells (Apt target target_is)
                        (head 0%nat source_is) (head 0%nat target_is)))
         | None => None
         end
  | None => None
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
  | (Apt p1 a1, Apt p2 a2) :: tl =>
    (Apt p1 a1, Apt (midpoint p1 p2) (intersection a1 a2)) ::
    (Apt (midpoint p1 p2) (intersection a1 a2), Apt p2 a2) ::
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
    if Qlt_bool (p_x c') (ve_x v) then
      check_bezier_ccw p v c' b2 c
    else if Qlt_bool (ve_x v) (p_x c') then
      check_bezier_ccw p v a b' c'
    else
      if Qlt_bool (p_y c') (ve_top v) then
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
    if Qlt_bool (p_x c') (ve_x v) then
      check_bezier_cw p v c' b2 c
    else if Qlt_bool (ve_x v) (p_x c') then
      check_bezier_cw p v a b' c'
    else
      if Qlt_bool (ve_bot v) (p_y c') then
         Some true
      else
         Some false
end.

Definition area3 := area3 Q Qplus Qminus Qmult.

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
Fixpoint check_curve_element_and_repair
  (fuel : nat) (cells : seq cell) (e : curve_element) :
   seq curve_element :=
match e with
| straight p1 p2 => straight p1 p2 :: nil
| bezier p1 p2 p3 =>
  if Nat.eqb (List.length (cell_indices p2)) 2 then
    let i1 := nth 0 (cell_indices p2) 0%nat in
    let i2 := nth 1 (cell_indices p2) 0%nat in
    let vedge := match common_vert_edge 
         (nth i1 cells dummy_cell) (nth i2 cells dummy_cell) with
      Some v => v
      | None => dummy_vert_edge
      end in
    let e' :=
      (if Qlt_bool (p_x (apt_val p1)) (p_x (apt_val p2)) then
        bezier p1 p2 p3
      else
        bezier p3 p2 p1) in
    match e' with
    |straight _ _ => e' :: nil
    | bezier p1' p2' p3' =>
      let check_function :=
      if Qlt_bool 0 
          (area3 (apt_val p1') (apt_val p2') (apt_val p3')) then
          check_bezier_ccw
      else
          check_bezier_cw in
        match check_function 20%nat vedge
                  (apt_val p1')(apt_val p2')(apt_val p3') with
        | Some true => bezier p1 p2 p3 :: nil
        | _ => 
          match fuel with
          | S p =>
            straight p1 
               (Apt (midpoint (apt_val p1) (apt_val p2)) (cell_indices p1))
              ::
              check_curve_element_and_repair p cells
                (bezier (Apt (midpoint (apt_val p1) (apt_val p2))
                       (cell_indices p1))
                 p2
                 (Apt (midpoint (apt_val p2) (apt_val p3)) (cell_indices p3)))
              ++
              straight (Apt (midpoint (apt_val p2) (apt_val p3))
                    (cell_indices p3)) p3 :: nil
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
  match point_to_point cells initial final with
  | Some s => List.concat (List.map (check_curve_element_and_repair 20 cells)
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

(* FOURTH PART: Displaying results. *)
(* TODO : this should probably be moved elsewhere. *)
(* This part is about producing postscript text to display examples. *)

Fixpoint positive_Z_to_decimal_string (fuel : nat) (z : Z) :=
  match fuel with
  | O => ""%string
  | S p =>
    if (z =? 0)%Z then
       ""%string
    else
    let (q, r) := Z.div_eucl z 10 in
    append (positive_Z_to_decimal_string p q) 
    match r with
    | 0%Z => "0"%string
    | 1%Z => "1"%string
    | 2%Z => "2"%string
    | 3%Z => "3"%string
    | 4%Z => "4"%string
    | 5%Z => "5"%string
    | 6%Z => "6"%string
    | 7%Z => "7"%string
    | 8%Z => "8"%string
    | _%Z => "9"%string
    end
  end.

Definition Z_to_string (z : Z) :=
  if (z =? 0)%Z then
    "0"%string
  else if (z <? 0)%Z then
    append "-" 
       (positive_Z_to_decimal_string (S (Z.abs_nat (Z.log2_up (- z)))) (- z))
  else 
    (positive_Z_to_decimal_string (S (Z.abs_nat (Z.log2_up z))) z).

Definition positive_rational_to_approx_decimal_string (x : Q) : string :=
    let frac_part := 
        (((1000 * Qnum x) / Zpos (Qden x)) mod 1000)%Z in
    let frac_part_string := 
      if (frac_part =? 0)%Z then
         "000"%string
      else if (frac_part <? 10)%Z then
        append "00" (Z_to_string frac_part)
      else if (frac_part <? 100)%Z then
        append "0" (Z_to_string frac_part)
      else 
        (Z_to_string frac_part) in
     append (Z_to_string (Qnum x / Z.pos (Qden x))) 
         (append "." frac_part_string).

Definition Q_to_approx_decimal_string (x : Q) :=
  if Qeq_bool x 0 then
    "0.000"%string
  else if Qle_bool 0 x then
    positive_rational_to_approx_decimal_string x
  else
    append "-" (positive_rational_to_approx_decimal_string (-x)).

Definition display_point (tr_x tr_y scale : Q) (p : pt) :=
  let process_coord tr scale v :=
    Q_to_approx_decimal_string (tr + scale * v) in
    append (process_coord tr_x scale (p_x p))
       (append " " (process_coord tr_y scale (p_y p))).

Definition display_edge (tr_x tr_y scale : Q) (e : edge) :=
  append (display_point tr_x tr_y scale (left_pt e))
    (append " moveto
" (append (display_point tr_x tr_y scale (right_pt e)) " lineto
")).

Definition display_segment (tr_x tr_y scale : Q) (s : pt * pt) :=
  display_edge tr_x tr_y scale (Bedge (fst s) (snd s)).

Definition weighted_sum (p1 p2 : pt) (weight1 : Q) :=
  Bpt (p_x p1 * weight1 + p_x p2 * (1 - weight1))
    (p_y p1 * weight1 + p_y p2 * (1 - weight1)).

(* The Bezer elements are quadratic elements, but postscript implements
  cubic Bezier curves, so some extra computation needs to be done.
  The mathematical elements were found on stackoverflow. *)

Definition display_curve_element (tr_x tr_y scale : Q) (e : curve_element) :=
match e with
| straight p1 p2 => display_segment tr_x tr_y scale (apt_val p1, apt_val p2)
| bezier p1 p2 p3 =>
  append (display_point tr_x tr_y scale (apt_val p1))
    (append " moveto "
      (append (display_point tr_x tr_y scale 
           (weighted_sum (apt_val p1) (apt_val p2) (1/3)))
         (append " "
           (append (display_point tr_x tr_y scale
                     (weighted_sum (apt_val p3) (apt_val p2) (1/3)))
             (append " "
                (append (display_point tr_x tr_y scale (apt_val p3))
             (append " curveto % "
               (append
                 (Z_to_string (Z.of_nat (head 0%nat (cell_indices p2))))
"
"))))))))
end.

Definition display_cell (tr_x tr_y scale : Q) (c : cell) :=
  display_edge tr_x tr_y scale
      {| left_pt := head dummy_pt (left_pts c);
                  right_pt := seq.last dummy_pt (left_pts c) |}.

Definition display_cell_centers (tr_x tr_y scale : Q) (s : seq cell) :=
  let indices := seq.iota 0 (List.length s) in
  map (fun i =>
         append "newpath "
         (append (display_point tr_x tr_y scale 
                      (cell_center (nth i s dummy_cell)))
          (append " moveto ("
            (append (Z_to_string (Z.of_nat i))
               ") show")))) indices.

Definition postscript_header :=
("" ::
"START"  ::
"%!PS" ::
"/Times-Roman findfont" ::
"12 scalefont" ::
"setfont" :: nil)%string.

Definition postscript_end_of_file := "END"%string :: nil.

Definition display_obstacles_and_cells (tr_x tr_y scale : Q)
  (bottom top : edge)
  (obstacles : seq edge) (cells : seq cell) : seq string :=
(List.map (display_edge tr_x tr_y scale)
  (bottom :: top :: obstacles) ++
"stroke"%string ::
display_cell_centers tr_x tr_y scale cells ++
"stroke gsave [1 3] 0 setdash"%string ::
List.map
  (fun c : cell => display_cell 300 400 70 c)
  cells ++
"
stroke grestore
"%string :: nil).

Definition display_smooth_trajectory (tr_x tr_y scale : Q)
   (s : seq curve_element) :=
(List.map (display_curve_element tr_x tr_y scale) s ++
"stroke"%string :: nil).

Definition display_full_example tr_x tr_y scale
  bottom top obstacles source target extra :=
let cells := edges_to_cells bottom top obstacles in
  String.concat "
"
(postscript_header ++
 display_obstacles_and_cells tr_x tr_y scale bottom top obstacles cells ++
 display_smooth_trajectory tr_x tr_y scale
   (smooth_from_cells cells source target) ++
extra ++
postscript_end_of_file).

(* FIFTH PART : testing preconditions *)
(* As explained in the introduction, edges have to satisfy some properties,
   part of which are easy to check in linear time.  We provide a few
   functions for these checks. *)

Definition edge_cond (edges : seq edge) :=
  forallb (fun e => Qlt_bool (p_x (left_pt e)) (p_x (right_pt e))) edges.

Definition inside_box (p : pt) (bottom top : edge) :=
  negb (point_under_edge p bottom) &&
  point_strictly_under_edge p top &&
  (Qlt_bool (p_x (left_pt bottom)) (p_x p) &&
     Qlt_bool (p_x p) (p_x (right_pt bottom))) &&
  (Qlt_bool (p_x (left_pt top)) (p_x p) &&
     Qlt_bool (p_x p) (p_x (right_pt top))).

(*******  starting work on an example ******************)

(*
Definition example_edge_list : seq edge :=
  Bedge (Bpt (-1) 0) (Bpt 0 (-1)) ::
  Bedge (Bpt 0 1) (Bpt 1 1) :: nil.
*)

Definition example_edge_sets : seq (seq edge) :=
  (Bedge (Bpt (-3) 0) (Bpt (-2) 1) ::
  Bedge (Bpt (-3) 0) (Bpt 0 (-3)) ::
  Bedge (Bpt 0 (-3)) (Bpt 3 0) ::
  Bedge (Bpt (-2) 1) (Bpt 0 1) ::
  Bedge (Bpt 0 1) (Bpt 1 0) ::
  Bedge (Bpt (-1) 0) (Bpt 0 (-1)) ::
  Bedge (Bpt 0 (-1)) (Bpt 1 0) :: nil) ::
(****)
  (Bedge (Bpt (-2) (-2)) (Bpt 2 0) ::
  Bedge (Bpt 0.8 (-1.2)) (Bpt 2 0) ::
  Bedge (Bpt 0.8 (-1.2)) (Bpt (17 # 5) (-3)) ::
  Bedge (Bpt (-2) (-2)) (Bpt (17 # 5) (-3)) :: nil) ::
(****)
  (Bedge (Bpt (-1) 0) (Bpt 0 (-1)) ::
  Bedge (Bpt 0 1) (Bpt 1 0) :: nil) :: nil.

Definition example_point_spread_sets : seq (seq (pt * pt)) :=
  ((Bpt 0.5 0.3, Bpt (-3) 1.9) ::
   (Bpt (-3) 1.9, Bpt (-1) 0.66) ::
   (Bpt (-1.9) 0.9, Bpt 1.5 (-1)) :: nil) ::
(*******)
  ((Bpt 0 0.3, Bpt (-3) 1.9) ::
   (Bpt (-3) 1.9, Bpt 1.5 (-1)) ::
   (Bpt (-1.9) (-2.1), Bpt 1.5 (-1)) :: nil) ::
(*******)
  ((Bpt (-0.5) 0, Bpt 0.5 0) ::
   (Bpt (-1.1) 0, Bpt 0.5 0) ::
   (Bpt 0 0 , Bpt 1 1) :: nil) ::
nil.

(* This lemma is testing that the datasets we produced
  do satisfy the pre-condition.  This lemma is not testing
  the code, but the dataset. *)
Lemma example_edge_cond :
  forallb (fun edge_list =>
               edge_cond edge_list) example_edge_sets = true.
Proof. easy. Qed.

Notation BOTTOM := (Bedge (Bpt (-4) (-4)) (Bpt 4 (-4))).

Notation TOP := (Bedge (Bpt (-4) 2) (Bpt 4 2)).

Definition example_bottom : edge := BOTTOM.

Definition example_top : edge := TOP.

(*  This lemma also tests the dataset, this time verifying
  that all edge exremities are inside the box. *)
Lemma example_inside_box :
  forallb (fun edge_list =>
     forallb (fun e => inside_box (point e) example_bottom example_top)
       (edges_to_events edge_list)) example_edge_sets = true.
Proof. easy. Qed.

Definition leftmost_points :=
  leftmost_points Q Qeq_bool Qle_bool Qplus Qminus Qmult Qdiv edge
  left_pt right_pt.

(* This lemma is testing the code.  It checks that all cells
   that have a vertical left edge have a neighbor on their left
   that has the same vertical edge on the right. *)
Lemma all_cells_have_left_neighbor :
  forallb (fun edge_list =>
  let cells := edges_to_cells example_bottom example_top edge_list in
  forallb (fun c =>
            (implb (andb (negb (Qeq_bool (left_limit c)
                (p_x (head dummy_pt (leftmost_points example_bottom example_top)))))
                (Nat.ltb 1 (List.length (left_pts c))))
            (existsb (fun c' => lr_connected c' c) cells))) cells)
        example_edge_sets = true.
Proof. easy. Qed.

Definition reference_line edge_list p1 p2 :=
   ("[4 4] 0 setdash 3 setlinewidth"%string ::
   (List.map (fun sg => display_segment 300 400 70 (apt_val (fst sg), apt_val (snd sg)))
   match point_to_point (edges_to_cells example_bottom example_top edge_list) p1 p2 with
   Some l => l
   | None => nil
   end ++ "stroke %debug"%string :: nil)).

Definition example_test edge_list (p1 p2 : pt) (extra : seq string) :=
  display_full_example 300 400 70 example_bottom example_top
    edge_list p1 p2 extra.

Definition example_by_index edge_list_index point_pair_index (with_dotted_line : bool) :=
  let edge_list := nth edge_list_index example_edge_sets nil in
  let point_pairs := nth edge_list_index example_point_spread_sets nil in
  let pp := nth point_pair_index point_pairs (Bpt 0 0, Bpt 1 1) in
  example_test edge_list (fst pp) (snd pp)
  (if with_dotted_line then
     reference_line edge_list (fst pp) (snd pp)
   else
     nil).

(* To display a more elaborate example that shows in a curved dash line
  the result of smoothening the trajectory without repaing, you can
  execute the following text.
Compute
  let p1 := Bpt (-19/10) (-3/2) in
  let p2 := Bpt (3/2) (0) in
  let cells := edges_to_cells example_bottom example_top example_edge_list in
  match point_to_point example_bottom example_top cells
          p1 p2 with
    Some s =>
      let bad_smooth := smoothen (break_segments s) in
      example_test p1 p2
         ("[2 4] 0 setdash"%string ::
List.map (display_curve_element 300 400 70) bad_smooth ++
          "stroke"%string :: nil)
    | None => ""%string
    end.
*)

(* To display the result of smoothening with repair, you can run the following
  command. *)

(*
Definition example_edge_list := nth 0 example_edge_sets nil.
Definition example_cells := edges_to_cells example_bottom example_top
     example_edge_list.

Definition o2l [A : Type] (x : option (seq A)) :=
  match x with Some v => v | None => nil end.

Compute (point_to_point example_cells (Bpt 2 1) (Bpt (-2) (1/3)),
         point_to_point example_cells (Bpt 2 1) (Bpt (-2.1) (1/3))).

Compute let p1 := (* Bpt (-19/10) (-3/2) *) Bpt (-1) (2/3) in
  let p2 := Bpt (-3.1) 1.9 in
  let target_is := find_origin_cells example_cells p2 in
  let cp := o2l (cell_path example_cells 0 3) in
  existsb (Nat.eqb (nth ((List.length cp) - 2) cp 0%nat)) target_is.

Compute let p2 := (* Bpt (-19/10) (-3/2) *) Bpt (-3.5) 1.9 in
  let p1 := Bpt 0.5 0 in
  example_test p1 p2
   ("[4 4] 0 setdash 3 setlinewidth"%string ::
   (List.map (fun sg => display_segment 300 400 70 (apt_val (fst sg), apt_val (snd sg)))
   match point_to_point example_cells p1 p2 with
   Some l => l
   | None => nil
   end ++ "stroke %debug"%string :: nil)).
(*   (door_to_door example_cells 3 5 None None
   match (cell_path example_cells 3 0) with
        Some l => (seq.behead l)
   | _ => nil end) ++ "stroke %debug"%string :: nil)). *)

Compute find_origin_cells example_cells (Bpt (-1) (1/3)).
Compute point_to_door example_cells (Apt (Bpt (-1) (1/3)) (5%nat :: 8%nat :: nil)) 5 7.
Compute match common_vert_edge (nth 5 example_cells dummy_cell) (nth 7 example_cells dummy_cell) with
          Some v => Some v
        | None => None
        end.

Compute match common_vert_edge (nth 5 example_cells dummy_cell) (nth 7 example_cells dummy_cell) with
          Some v => Some (on_vert_edge (Bpt (-1) (1/3)) v)
        | None => None
        end.

Compute
  let p2 := Bpt (-0.5) 0 in
  let p1 := Bpt 0.5 0 in
  example_test p1 p2 nil.

Compute nth 5 example_cells dummy_cell.

Compute nth 7 example_cells dummy_cell.

Compute edges_to_events example_edge_list.
*)

(* Compute example_by_index 0 0 false. *)
