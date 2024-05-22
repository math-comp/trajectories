Require Import Arith QArith List generic_trajectories smooth_trajectories.
Require Import Reals.

Open Scope R_scope.

(* x1 is the first coordinate of the vector corresponding to an edge.  It is
 reasonable to assume it is non-zero in the context of vertical cell
 decomposition, because edges are not vertical.  If intersection with
 vertical lines is needed, then we can use vertical_intersection. *)
Lemma find_segment_intersection t1 t2 x1 y1 xl1 yl1 x2 y2 xl2 yl2 :
  x1 <> 0 ->
  x2 * y1 - x1 * y2 <> 0 ->
  t1 * x1 + xl1 = t2 * x2 + xl2 ->
  t1 * y1 + yl1 = t2 * y2 + yl2 ->
  (* If the two lines cross and the first line has a non vertical
     direction, then this is the first coordinate of the intersection
     point. *)
  t1 * x1 + xl1 =
    (yl2 * x1 * x2 - yl1 * x1 * x2 - x1 * xl2 * y2 + xl1 * y1 * x2) /
    (y1 * x2 - x1 * y2).
Proof.
intros x1n0 dn0 eq1 eq2.
assert (valt1 : t1 = (t2 * x2 + (xl2 - xl1)) / x1).
  enough (tmp : t1 = (t2 * x2 + xl2 - xl1) / x1) by now rewrite tmp; field.
  apply (Rmult_eq_reg_l x1); auto; apply (Rplus_eq_reg_r xl1).
  now rewrite (Rmult_comm x1 t1), eq1; field.
revert eq2; rewrite valt1, Rdiv_plus_distr, Rmult_plus_distr_r.
replace (t2 * x2 / x1 * y1 + (xl2 -xl1) / x1 * y1 + yl1)
  with ((t2 * x2 * y1 + (xl2 - xl1) * y1 + yl1 * x1) / x1) by now field.
replace (t2 * y2 + yl2) with ((t2 * x1 * y2 + yl2 * x1) / x1) by now field.
intros eq2; apply (Rmult_eq_reg_r (/x1)) in eq2;[|now apply Rinv_neq_0_compat].
apply (Rplus_eq_compat_r (- (t2 * x1 * y2))) in eq2.
replace (t2 * x1 * y2 + yl2 * x1 + - (t2 * x1 * y2)) with (yl2 * x1) in eq2
   by ring.
replace (t2 * x2 * y1 + (xl2 - xl1) * y1 + yl1 * x1 + - (t2 * x1 * y2)) with
    (t2 * (x2 * y1 - x1 * y2) + (xl2 - xl1) * y1 + yl1 * x1) in eq2 by ring.
apply (Rplus_eq_compat_r (- ((xl2 - xl1) * y1 + yl1 * x1))) in eq2.
replace (t2 * (x2 * y1 - x1 * y2) +
   (xl2 - xl1) * y1 + yl1 * x1 + - ((xl2 - xl1) * y1 + yl1 * x1))
  with (t2 * (x2 * y1 - x1 * y2)) in eq2 by ring.
replace (yl2 * x1 + - ((xl2 - xl1) * y1 + yl1 * x1)) with
  ((yl2 - yl1) * x1 - (xl2 - xl1) * y1) in eq2 by ring.
apply (Rmult_eq_compat_r (/ (x2 * y1 - x1 * y2))) in eq2.
replace (t2 * (x2 * y1 - x1 * y2) * / (x2 * y1 - x1 * y2)) with t2 in eq2
  by now field.
rewrite eq2.
field; split; auto; intros abs; case dn0; rewrite <- abs; ring.
Qed.

Close Scope R_scope.
  
(* this function assumes the two edge directions cross and the first edge *)
Definition cross_first_coordinate (e1 e2 : edge) :=
  let yl2 := p_y (left_pt e2) in
  let xl2 := p_x (left_pt e2) in
  let yl1 := p_y (left_pt e1) in
  let xl1 := p_x (left_pt e1) in
  let yr2 := p_y (right_pt e2) in
  let xr2 := p_x (right_pt e2) in
  let yr1 := p_y (right_pt e1) in
  let xr1 := p_x (right_pt e1) in
  let x1 := xr1 - xl1 in
  let x2 := xr2 - xl2 in
  let y1 := yr1 - yl1 in
  let y2 := yr2 - yl2 in
  Qred (
  (yl2 * x1 * x2 - yl1 * x1 * x2 - x1 * xl2 * y2 + xl1 * y1 * x2) /
    (y1 * x2 - x1 * y2)).

(* this function assumes the two edge directions cross and the
   first edge is not vertical. *)
Definition pre_cross_second_coordinate (e1 : edge) (cross_coordinate : Q) :=
  Qred (p_y (left_pt e1) +
 (p_y (right_pt e1) - p_y (left_pt e1)) /
  (p_x (right_pt e1) - p_x (left_pt e1)) *
 (cross_coordinate - p_x (left_pt e1))).

Definition cross_second_coordinate (e1 e2 : edge) :=
  if Qeq_bool (p_x (left_pt e1)) (p_x (right_pt e1)) then
     pre_cross_second_coordinate e2 (cross_first_coordinate e1 e2)
  else
     pre_cross_second_coordinate e1 (cross_first_coordinate e1 e2).

Definition edge_determinant (e1 e2 : edge) : Q :=
  let y1 := p_y (right_pt e1) - p_y (left_pt e1) in
  let x1 := p_x (right_pt e1) - p_x (left_pt e1) in
  let y2 := p_y (right_pt e2) - p_y (left_pt e2) in
  let x2 := p_x (right_pt e2) - p_x (left_pt e2) in
  x1 * y2 - x2 * y1.

(* We don't consider edges to cross if they touch at their extremeties. *)
Definition have_crossing (e1 e2 : edge) : bool :=
  let x1 := p_x (right_pt e1) - p_x (left_pt e1) in
  let d2 := edge_determinant e1 e2 in
  if Qeq_bool x1 0 then
     Qlt_bool (p_x (left_pt e2)) (p_x (left_pt e1)) &&
     Qlt_bool (p_x (left_pt e1)) (p_x (right_pt e2))
  else
  if negb (Qeq_bool d2 0) then
     (Qlt_bool (p_x (left_pt e2)) (cross_first_coordinate e1 e2) &&
      Qlt_bool (cross_first_coordinate e1 e2) (p_x (right_pt e2))) ||
     (Qlt_bool (p_x (left_pt e1)) (cross_first_coordinate e1 e2) &&
      Qlt_bool (cross_first_coordinate e1 e2) (p_x (right_pt e1)))
  else
   (* The two edges are parallel.  They may still touch. *)
   if negb (Qeq_bool 
             (area3 _ Qplus Qminus Qmult (left_pt e1) (left_pt e2) (right_pt e2)) 0) then
     true
   else
     (Qlt_bool (p_x (left_pt e2)) (p_x (left_pt e1)) &&
      Qlt_bool (p_x (left_pt e1)) (p_x (right_pt e2))) ||
     (Qlt_bool (p_x (left_pt e2)) (p_x (right_pt e1)) &&
      Qlt_bool (p_x (right_pt e1)) (p_x (right_pt e2))) ||
     (Qlt_bool (p_x (left_pt e1)) (p_x (left_pt e2)) &&
      Qlt_bool (p_x (left_pt e2)) (p_x (right_pt e1))) ||
     (Qlt_bool (p_x (left_pt e1)) (p_x (right_pt e2)) &&
      Qlt_bool (p_x (right_pt e2)) (p_x (right_pt e1))).

(* This function assumes the two edges are non-vertical. *)
Definition break_edges_at_crossing (e1 e2 : edge) :
  option (edge * edge) * option (edge * edge) :=
let intersection_x := Qred (cross_first_coordinate e1 e2) in
  let new1 :=
    if Qlt_bool (p_x (left_pt e1)) intersection_x &&
       Qlt_bool intersection_x (p_x (right_pt e1)) then
      let intersection_y := Qred (cross_second_coordinate e1 e2) in
      Some (Bedge (left_pt e1) (Bpt intersection_x intersection_y),
       Bedge (Bpt intersection_x intersection_y) (right_pt e1))
    else
      None in
  let new2 :=
    if Qlt_bool (p_x (left_pt e2)) intersection_x &&
       Qlt_bool intersection_x (p_x (right_pt e2)) then
      let intersection_y := Qred (cross_second_coordinate e1 e2) in
      Some (Bedge (left_pt e2) (Bpt intersection_x intersection_y),
       Bedge (Bpt intersection_x intersection_y) (right_pt e2))
    else
      None in
   (new1, new2).

(* returns the first coordinates of all points where edge e intersects
  an existing edge from the sequence of events. *)
Fixpoint find_all_crossing_points (e : edge) (evs : list event) : list Q :=
  match evs with
  | nil => nil
  | Bevent p outg :: evs' =>
    map (fun g => Qred (cross_first_coordinate e g))
        (filter (have_crossing e) outg) ++
    find_all_crossing_points e evs'
  end.

Fixpoint make_broken_edges (e : edge) (break_points : seq Q) :=
  match break_points with
  | nil => e :: nil
  | bp :: bps =>
    let intermediate_point := (Bpt bp (pre_cross_second_coordinate e bp)) in
    Bedge (left_pt e) intermediate_point :: 
    make_broken_edges (Bedge intermediate_point (right_pt e)) bps
  end.

Notation Bevent := (@Bevent _ _).
Notation add_event := (@add_event Q Qeq_bool Qle_bool edge).

Fixpoint repair_hit_edge (g : edge) (evs : seq event) : seq event :=
match evs with
| nil => nil
| Bevent p gs :: evs' =>
  match partition (fun g' => have_crossing g g') gs with
  | (nil, cg) =>
    Bevent p gs :: repair_hit_edge g evs'
  | (bg :: _, cg) =>
    (* If there is a hit edge, we assume there can only be one,
       This invariant is not guaranteed by the datatype, but
       it is guaranteed in the use case of vertical cell decomposition. *)
    match break_edges_at_crossing bg g with
    | (Some (e1, e2), _) =>
      Bevent p (e1 :: cg) :: add_event (left_pt e2) e2 false evs'
    | (None, _) => nil (* This is dead code *)
    end
  end
end.

Definition add_edge_avoid_cross (evs : seq event) (e : edge) :=
  seq.foldl (fun evs' e' =>
               add_event (left_pt e') e' false 
                  (add_event (right_pt e') e' true
                        (repair_hit_edge e' evs')))
     evs
     (make_broken_edges e 
          (no_dup_seq_aux Qeq_bool
              (path.sort Qlt_bool (find_all_crossing_points e evs)))).

Definition add_edge_avoid_cross_debug (evs : seq event) (e : edge) :=
  seq.foldl (fun evs' e' =>
               add_event (left_pt e') e' false
                  (add_event (right_pt e') e' true
                        (repair_hit_edge e' evs')))
     evs
     (make_broken_edges e (find_all_crossing_points e evs)).

Definition edges_to_events_nc (es : seq edge) : seq event :=
  seq.foldl add_edge_avoid_cross nil es.

Definition e1 := (Bedge (Bpt 0 (-2)) (Bpt 2 (-1))).
Definition e2 := (Bedge (Bpt 0 0) (Bpt 2 (-2))).
Definition e3 := (Bedge (Bpt 0 (-3)) (Bpt 2 1)).
Definition e4 := Bedge (Bpt 0 0) (Bpt 2 0).

Compute (make_broken_edges e2 
           (find_all_crossing_points e2 (edges_to_events_nc (e1 :: nil)))). 

Notation dummy_edge := (dummy_edge Q 0 edge Bedge).

Definition evs14 := edges_to_events_nc (e1 :: e2 :: e3 :: e4 :: nil).
Definition evs13 := edges_to_events_nc (e1 :: e2 :: e3 :: nil).
Definition evs12 := edges_to_events_nc (e1 :: e2 :: nil).
Definition evs1 := edges_to_events_nc (e1 :: nil).
Definition e2_1 := nth 0 (make_broken_edges e2 (find_all_crossing_points e2 evs1)) dummy_edge.
Definition e3_1 := nth 0 (make_broken_edges e3 (find_all_crossing_points e3 evs12)) dummy_edge.

Compute e3_1.
Compute e2_1.
Compute have_crossing e1 e2.
Compute break_edges_at_crossing e1 e2.
Compute repair_hit_edge e2_1 evs1.
Compute evs14.
Compute List.length (List.concat (List.map (fun ev => outgoing ev) evs14)).

Definition display_break_points (e : edge) (bps : seq Q) :=
   List.concat (
   List.map (fun e => 
          (display_edge 300 400 70 
            (Bedge (Bpt (p_x (right_pt e) - 0.5) (p_y (right_pt e)))
                   (Bpt (p_x (right_pt e) + 0.5) (p_y (right_pt e)))) ::
            display_edge 300 400 70
            (Bedge (Bpt (p_x (right_pt e)) (p_y (right_pt e) - 0.5))
                   (Bpt (p_x (right_pt e)) (p_y (right_pt e) + 0.5))) :: nil))
         (make_broken_edges e bps)).

Compute no_dup_seq_aux Qeq_bool (path.sort Qlt_bool
                (find_all_crossing_points e3 evs12)).
Compute pre_cross_second_coordinate e3 (1/2).
Compute e3_1.
Compute make_broken_edges e3 (find_all_crossing_points e3 evs12).
Compute add_edge_avoid_cross evs12 e3_1.
Compute repair_hit_edge e3 evs12.

Notation edge_eqb := (@edge_eqb Q Qeq_bool edge left_pt right_pt).
Lemma noc14 :
  let l := List.concat (List.map outgoing evs14) in 
  forallb (fun g => forallb (fun g' => edge_eqb g g' || negb (have_crossing g g')) l) l = true.
Proof. easy. Qed.

Lemma cnt14 :
  List.length (List.concat (List.map outgoing evs14)) = 12%nat.
Proof. easy. Qed.

Import String.
(*
Compute example_test (List.concat (List.map outgoing evs14))
             (Bpt 1.2 (-0.8)) (Bpt (-1) (0.4)) nil.
*)
Compute (concat "
" (postscript_header ++
   display_edge 300 400 70 example_bottom ::
   display_edge 300 400 70 example_top ::
   List.map (display_edge 300 400 70)
         (List.concat (List.map (fun ev => outgoing ev) 
                evs14
(*  ((* add_event (left_pt e3_1) e3_1 false *)
                   ((* add_edge_avoid_cross_debug *) 
add_edge_avoid_cross e3 evs12)) *))) ++
        "stroke"%string :: ""%string ::
        postscript_end_of_file)).

Compute cross_first_coordinate e2 e3.
Compute find_all_crossing_points e3 (edges_to_events_nc (e1 :: nil)).
Compute evs12.
Compute find_all_crossing_points e3 evs12.
(*
Compute (concat "
" (postscript_header ++
        (display_edge 300 400 70 e1) ::
        (display_edge 300 400 70 e2) ::
        (display_edge 300 400 70 e3) ::
        (display_edge 300 400 70 e4) ::
        List.map (display_edge 300 400 70) 
            (make_broken_edges e3 (find_all_crossing_points e3 ev12)) ++
        "stroke"%string ::
        "[2 8] 0 setdash"%string ::
        (display_edge 300 400 70 
            (Bedge (Bpt (cross_first_coordinate e1 e2) (-2))
                             (Bpt (cross_first_coordinate e1 e2) 2))) ::
        (display_edge 300 400 70
            (Bedge (Bpt 0 (cross_second_coordinate e1 e2))
               (Bpt 2 (cross_second_coordinate e1 e2)))) ::
        display_break_points e3 
            (find_all_crossing_points e3 ev12) ++
        "stroke"%string :: ""%string ::
        postscript_end_of_file)).
*)




