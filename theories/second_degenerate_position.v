From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg simple_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

(* Notation prefix, dupplicated from cells_alg.v *)
Notation pt := (pt (RealField.sort R)).
Notation p_x := (p_x (RealField.sort R)).
Notation p_y := (p_y (RealField.sort R)).
Notation Bpt := (Bpt (RealField.sort R)).
Notation edge := (edge R).
Notation left_pt := (@left_pt R).
Notation right_pt := (@right_pt R).
Notation event := (event (RealField.sort R) edge).
Notation outgoing := (outgoing (RealField.sort R) edge).
Notation point := (point (RealField.sort R) edge).
Notation cell := (cell (RealField.sort R) edge).

Notation dummy_pt := (dummy_pt (RealField.sort R) 1).
Notation dummy_edge := (dummy_edge (RealField.sort R) 1 edge (@unsafe_Bedge _)).
Notation dummy_cell :=
  (dummy_cell (RealField.sort R) 1 edge (@unsafe_Bedge _)).
Notation dummy_event := (dummy_event (RealField.sort R) 1 edge).
Notation edge_below :=
  (generic_trajectories.edge_below (RealField.sort R) eq_op <=%R +%R
    (fun x y => x - y) *%R 1 edge left_pt right_pt).
Notation "x <| y" := (edge_below x y).
Notation valid_edge :=
  (generic_trajectories.valid_edge (RealField.sort R)
   le edge left_pt right_pt).
Notation vertical_intersection_point :=
  (vertical_intersection_point (RealField.sort R)
  le +%R (fun x y => x - y) *%R
  (fun x y => x / y) edge left_pt right_pt).
Notation point_under_edge :=
  (point_under_edge (RealField.sort R) le +%R (fun x y => x - y) *%R 1
  edge left_pt right_pt).
Notation "p <<= g" := (point_under_edge p g).
Notation "p >>> g" := (~~ (point_under_edge p g)).
Notation point_strictly_under_edge :=
  (point_strictly_under_edge  (RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R 1 edge left_pt right_pt).
Notation "p <<< g" := (point_strictly_under_edge p g).
Notation "p >>= g" := (~~ (point_strictly_under_edge p g)).

Notation contains_point :=
  (contains_point (RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R 1
    edge left_pt right_pt).

Notation open_cells_decomposition_contact :=
  (open_cells_decomposition_contact (RealField.sort R) eq_op le +%R
  (fun x y => x - y) *%R 1 edge left_pt right_pt).
Notation open_cells_decomposition_rec :=
  (open_cells_decomposition_rec (RealField.sort R) eq_op le +%R
  (fun x y => x - y) *%R 1 edge (@unsafe_Bedge R) left_pt
  right_pt).
Notation open_cells_decomposition :=
  (open_cells_decomposition (RealField.sort R) eq_op le +%R
  (fun x y => x - y) *%R 1 edge (@unsafe_Bedge R) left_pt
  right_pt).

Notation scan_state := (scan_state (RealField.sort R) edge).
Notation sc_open1 := (sc_open1 (RealField.sort R) edge).
Notation lst_open := (lst_open (RealField.sort R) edge).
Notation sc_open2 := (sc_open2 (RealField.sort R) edge).
Notation sc_closed := (sc_closed (RealField.sort R) edge).
Notation lst_closed := (lst_closed (RealField.sort R) edge).

Notation update_closed_cell :=
  (update_closed_cell (RealField.sort R) 1 edge).

Notation set_left_pts :=
  (set_left_pts (RealField.sort R) edge).

Notation low := (low (RealField.sort R) edge).
Notation high := (high (RealField.sort R) edge).
Notation left_pts := (left_pts (RealField.sort R) edge).
Notation right_pts := (right_pts (RealField.sort R) edge).
Notation Bcell := (Bcell (RealField.sort R) edge).
Notation cell_center :=
  (cell_center (RealField.sort R) +%R (fun x y => x / y) 1%:R edge).

Notation closing_cells :=
  (generic_trajectories.closing_cells (RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
    *%R (fun x y => x / y) edge left_pt right_pt).
Notation close_cell :=
  (generic_trajectories.close_cell (RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
    *%R (fun x y => x / y) edge left_pt right_pt).

Notation set_pts := (set_pts (RealField.sort R) edge).

(* This function is to be called only when the event is in the middle
  of the last opening cell.  The point e needs to be added to the left
  points of one of the newly created open cells, but the one that receives
  the first segment of the last opening cells should keep its existing
  left points.*)
Notation update_open_cell :=
  (update_open_cell (RealField.sort R) eq_op le +%R (fun x y => x - y)
  *%R (fun x y => x / y) 1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation update_open_cell_top :=
  (update_open_cell_top (RealField.sort R) eq_op le +%R (fun x y => x - y)
  *%R (fun x y => x / y) 1
  edge (@unsafe_Bedge R) left_pt right_pt).

Notation Bscan := (Bscan (RealField.sort R) edge).

Notation opening_cells_aux :=
  (opening_cells_aux (RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
  *%R (fun x y => x / y) 1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation simple_step :=
  (generic_trajectories.simple_step (RealField.sort R) eq_op le +%R
  (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation step :=
  (step (RealField.sort R) eq_op le +%R (fun x y => x - y) *%R
  (fun x y => x / y) 1 edge (@unsafe_Bedge R) left_pt right_pt).
(*
Definition scan events st : seq cell * seq cell :=
  let final_state := foldl step st events in
  (sc_open1 final_state ++ lst_open final_state :: sc_open2 final_state,
   lst_closed final_state :: sc_closed final_state). *)

Notation start_open_cell :=
  (start_open_cell (RealField.sort R) eq_op le +%R (fun x y => x - y)
  *%R (fun x y => x / y) edge left_pt right_pt).

Notation open_cell_side_limit_ok :=
  (@open_cell_side_limit_ok R).

 (* End of notation prefix. *)

Definition last_case fop lsto fc' cc lcc lc cls lstc he ev :=
  let (nos, lno) := update_open_cell_top lsto he ev in
  Bscan (fop ++ fc' ++ nos) lno lc
    (closing_cells (point ev) (behead cc) ++ lstc ::cls)
    (close_cell (point ev) lcc) he (p_x (point ev)).

Lemma last_case_common_invariant
  bottom top s fop lsto lop cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  point ev <<= lsthe ->
  point ev >>= lsthe ->
  common_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  common_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
Proof.
move=> boxwf nocs' inbox_es at_lstx pu pa comng.
have comi := ngcomm comng.
rewrite /step /= /same_x at_lstx eqxx pu (negbTE pa) /=.
case oca_eq : open_cells_decomposition => [[[[[fc' cc] lcc] lc] le] he].
have oute : out_left_event ev.
  by apply: (out_events comi); rewrite inE eqxx.
have := inv1 comi; rewrite /state_open_seq/=.
move=> -[] clae [] [// | sval] [] adj [] cbtom rfo.
have pal : (point ev) >>> low lsto.
  by exact: (same_x_point_above_low_lsto at_lstx comng).
have noc : {in all_edges (fop ++ lsto :: lop) (ev :: evs) &,
           no_crossing R}.
  apply: inter_at_ext_no_crossing.
  by apply: (sub_in2 (edges_sub comi) nocs').
set st := last_case fop lsto fc' cc lcc lc cls lstc he ev.
have inv1' : inv1_seq bottom top evs
  (state_open_seq (last_case fop lsto fc' cc lcc lc cls lstc he ev)).
  have := (step_keeps_invariant1 cls lstc (inbox_events (ngcomm comng))
    oute rfo cbtom adj sval (closed_events comi) clae 
    (esym (high_lsto_eq comi)) (fun x : p_x (point ev) = lstx => pal) noc
    (lex_events comi)).
  rewrite /invariant1 /step /same_x at_lstx eqxx pu (negbTE pa) /=.
  by rewrite oca_eq.
have lstx_eq' : lst_x _ _ st = left_limit (lst_open st).
  rewrite /st/last_case.
  admit.
have high_lsto_eq' : high (lst_open st) = lst_high _ _ st.
  admit.
have edges_sub' : {subset all_edges (state_open_seq st) evs <=
  [:: bottom, top & s]}.
  admit.
have closed_events' : close_edges_from_events evs.
  by have := closed_events comi => /= /andP[].
have out_events' : {in evs, forall e, out_left_event e}.
  by move=> e ein; apply: (out_events comi); rewrite inE ein orbT.
have uniq_ec' : {in evs, forall e, uniq (outgoing e)}.
  by move=> e ein; apply: (uniq_ec comi); rewrite inE ein orbT.
have inbox_events' : all (inside_box bottom top)
           [seq point x | x <- evs].
  by have := inbox_events comi=> /= /andP[].
have no_dup_edge' : {in [seq high c | c <- state_open_seq st] & evs,
     forall g e, g \notin (outgoing e)}.
  admit.
have lex_events' : sorted (@lexPtEv _) evs.
  have := lex_events comi; rewrite /= (path_sortedE (@lexPtEv_trans _)).
  by move=> /andP[]. 
have sides_ok' : all open_cell_side_limit_ok (state_open_seq st).
  admit.
have above_low_lsto' :
     {in evs, forall e,
        lexPt (last dummy_pt (left_pts (lst_open st)))
              (point e)}.
  admit.
have stradle' : 
     evs = [::] \/ {in [seq high c | c <- state_open_seq st], forall g,
     lexPt (left_pt g) (point (head dummy_event evs)) &&
     lexePt (point (head dummy_event evs)) (right_pt g)}.
  admit.
by constructor.
Admitted.