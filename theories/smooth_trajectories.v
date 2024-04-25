From mathcomp Require Import all_ssreflect.
Require Import ZArith QArith List String OrderedType OrderedTypeEx FMapAVL.
Require Import generic_trajectories.
Require Import Qabs.

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

Definition manhattan_distance (p1x p1y p2x p2y : R) :=
  Qabs (p2x - p1x) + Qabs (p2y - p1y).

Definition pt_distance := manhattan_distance.

Definition Qsmooth_point_to_point :=
 smooth_point_to_point Q Qeq_bool Qle_bool Qplus Qminus Qmult Qdiv
   pt_distance 1 edge Bedge left_pt right_pt.

Definition Qedges_to_cells :=
   edges_to_cells Q Qeq_bool Qle_bool Qplus Qminus Qmult Qdiv 1
   edge Bedge left_pt right_pt.

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

Definition apt_val := apt_val Q.

Definition cell_indices := cell_indices Q.

Definition display_curve_element (tr_x tr_y scale : Q) (e : curve_element Q) :=
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

Definition cell_center :=
  cell_center Q Qplus Qdiv 1 edge.

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
   (s : seq (curve_element Q)) :=
(List.map (display_curve_element tr_x tr_y scale) s ++
"stroke"%string :: nil).

Definition Qsmooth_from_cells :=
  smooth_from_cells Q Qeq_bool Qle_bool Qplus Qminus Qmult Qdiv pt_distance 1 edge
  Bedge left_pt right_pt.

Definition display_full_example tr_x tr_y scale
  bottom top obstacles source target extra :=
let cells := Qedges_to_cells bottom top obstacles in
  String.concat "
"
(postscript_header ++
 display_obstacles_and_cells tr_x tr_y scale bottom top obstacles cells ++
 display_smooth_trajectory tr_x tr_y scale
   (Qsmooth_from_cells cells source target) ++
extra ++
postscript_end_of_file).

(* FIFTH PART : testing preconditions *)
(* As explained in the introduction, edges have to satisfy some properties,
   part of which are easy to check in linear time.  We provide a few
   functions for these checks. *)

Definition edge_cond (edges : seq edge) :=
  forallb (fun e => Qlt_bool (p_x (left_pt e)) (p_x (right_pt e))) edges.

Definition inside_box (p : pt) (bottom top : edge) :=
  negb (point_under_edge Q Qle_bool Qplus Qminus Qmult 1 edge left_pt right_pt
        p bottom) &&
  point_strictly_under_edge Q Qeq_bool Qle_bool Qplus Qminus Qmult 1 edge
       left_pt right_pt p top &&
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
       (edges_to_events Q Qeq_bool Qle_bool edge left_pt right_pt edge_list)) example_edge_sets = true.
Proof. easy. Qed.

Definition leftmost_points :=
  leftmost_points Q Qeq_bool Qle_bool Qplus Qminus Qmult Qdiv edge
  left_pt right_pt.

(* This lemma is testing the code.  It checks that all cells
   that have a vertical left edge have a neighbor on their left
   that has the same vertical edge on the right. *)

(*
Lemma all_cells_have_left_neighbor :
  forallb (fun edge_list =>
  let cells := Qedges_to_cells example_bottom example_top edge_list in
  forallb (fun c =>
            (implb (andb (negb (Qeq_bool (left_limit Q 1 edge c)
                (p_x (head dummy_pt (leftmost_points example_bottom example_top)))))
                (Nat.ltb 1 (List.length (left_pts c))))
            (existsb (fun c' => lr_connected Q Qeq_bool 1 edge c' c) cells))) cells)
        example_edge_sets = true.
Proof. easy. Qed.
*)
(*
Definition reference_line edge_list p1 p2 :=
   ("[4 4] 0 setdash 3 setlinewidth"%string ::
   (List.map (fun sg => display_segment 300 400 70 (apt_val (fst sg), apt_val (snd sg)))
   match point_to_point Q Qeq_bool Qle_bool Qplus Qminus Qmult Qdiv 1
        edge Bedge left_pt right_pt
     (Qedges_to_cells example_bottom example_top edge_list) p1 p2 with
   Some l => l
   | None => nil
   end ++ "stroke %debug"%string :: nil)).
*)
(*
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
*)
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

(* Definition approx_sqrt  *)

(*
Definition euclidean_distance (p1 p2 : pt) :=
   (p_x p2 - p_x p1) ^ 2 + (p_y p2 - p_y p1) ^ 2.

*)

