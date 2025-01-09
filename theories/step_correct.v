From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg initial_cell simple_step
 first_degenerate_position second_degenerate_position.

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

Lemma edges_inside_from_events_inside (bottom top : edge) evs:
    all (inside_box bottom top) ([seq point e | e <- evs] : seq pt) ->
    {in evs, forall ev, out_left_event ev} ->
    close_edges_from_events evs ->
   {in events_to_edges evs,
         forall g : edge,
         inside_box bottom top (left_pt g) &&
         inside_box bottom top (right_pt g)}.
Proof.
elim: evs => [ | e evs Ih] /=; first by [].
move=> /andP[] inbox_e inbox_es out_es0.
have out_e : out_left_event e by apply: out_es0; rewrite mem_head.
have out_es : {in evs, forall e, out_left_event e}.
   by move=> e' e'in; apply: out_es0; rewrite inE e'in orbT.
move=> /andP[] close_e close_es.
move=> g; rewrite events_to_edges_cons mem_cat=> /orP[] gin; last first.
  by apply: (Ih   inbox_es out_es close_es).
apply/andP; split; first by rewrite (eqP (out_e g gin)).
move: close_e=> /allP /(_ g gin).
move/hasP=> [e2 e2in /eqP ->].
by apply: (@allP pt _ _ inbox_es); rewrite map_f.
Qed.

Lemma initial_safe_side bottom top events:
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: events_to_edges events &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} ->
  close_edges_from_events events ->
  {in events_to_edges events & events, forall g e, non_inner g (point e)} ->
  events != [::] ->
  safe_side_non_gp_invariant bottom top (events_to_edges events)
    [:: head dummy_event events]
    (initial_state bottom top events) (behead events).
Proof.
move=> boxwf start_open_cell_ok nocs' evin lexev out_evs uniqout 
  cle n_inner evsn0.
have := initial_safe_side_non_gp_invariant boxwf start_open_cell_ok
  nocs' evin lexev out_evs uniqout cle evsn0 n_inner.
by case: (events) evsn0=> [ | ? [ | ? ?]] //=.
Qed.


(* This lemma only provides a partial correctness statement in the case
  where the events are never aligned vertically.  This condition is
  expressed by the very first hypothesis.  TODO: it relies on the assumption
  that the first open cell is well formed.  This basically means that the
  two edges have a vertical overlap.  This statement should be probably
  be made clearer in a different way.

  TODO: one should probably also prove that the final sequence of open
  cells, here named "open", should be reduced to only one element. *)

Lemma step_safe_side_invariant bottom top past st s ev events :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- ev :: events] ->
  {in s,  forall g, inside_box bottom top (left_pt g) &&
        inside_box bottom top (right_pt g)} ->
  sorted (@lexPtEv _) (ev :: events) ->
  {in ev :: events, forall ev, out_left_event ev} ->
  {in ev :: events, forall ev, uniq (outgoing ev)} ->
  close_edges_from_events (ev :: events) ->
  {in s & (ev :: events), forall g e, non_inner g (point e)} ->
  {subset events_to_edges (ev :: events) <= s} ->
  safe_side_non_gp_invariant bottom top s past st (ev :: events) ->
  safe_side_non_gp_invariant bottom top s (rcons past ev)
   (step st ev) events.
Proof.
move=> boxwf nocs' inbox_es inbox_edges lexev out_events uniqout cle n_in 
  sub_evs.
case: st => [fop lsto lop cls lstc lsthe lstx] ss_inv.
have ec_inv := covered_ss ss_inv.
have d_inv := disjoint_ss ss_inv.
have comng := common_non_gp_inv_dis d_inv.
have comi := ngcomm comng.
have [clae [[ //| sval] [adj [cbtom rfo]]]] := inv1 comi.
have inbox_e : inside_box bottom top (point ev).
  by apply: (allP inbox_es); rewrite map_f // inE eqxx.
have exc : exists2 c, c \in fop ++ lsto :: lop & contains_point' (point ev) c.
  by have := exists_cell cbtom adj (inside_box_between inbox_e).
rewrite /step/same_x.
case: ifP=> [difx | ]; last (move=> /negbT; rewrite negbK=> /eqP at_lstx).
  case oe : open_cells_decomposition => [[[[[fc cc] lcc] lc] le] he].
  have simple_cond : lstx <> p_x (point ev) \/
    lstx = p_x (point ev) /\ point ev >>> lsthe.
      by left; apply/eqP; rewrite eq_sym.
    
  by have := simple_step_safe_side_non_gp_invariant boxwf nocs' inbox_edges
    inbox_es lexev sub_evs out_events cle n_in uniqout oe simple_cond
    ss_inv.
case: ifP=> [pah | puh'].
  have simple_cond : lstx <> p_x (point ev) \/
    lstx = p_x (point ev) /\ point ev >>> lsthe.
    by right; split;[apply/esym | ].
  case oe' : open_cells_decomposition => [[[[[fc' cc] lcc] lc] le] he].
  have exc2 : exists2 c, c \in lop & contains_point' (point ev) c.
    by have := exi' inbox_es rfo cbtom adj sval (esym (high_lsto_eq comi))
     pah.
  have vll : valid_edge (low (head dummy_cell lop)) (point ev).
    have [cctn cin _ ] := exc2.
    have inlop : head dummy_cell lop \in lop.
      by case: (lop) cin=> [ | ? ?] // _; rewrite mem_head.
    have /(allP sval) : head dummy_cell lop \in fop ++ lsto :: lop.
      by rewrite mem_cat inE inlop !orbT.
    by move=> /andP[].
  have pal : point ev >>> low (head dummy_cell lop).
    have [cctn cin _] := exc2.
    have := adj; rewrite /state_open_seq /= => /adjacent_catW[] _.
    case: (lop) cin => [ | ? ?] //= _ /andP[] /eqP <- _.
    by rewrite (high_lsto_eq comi) pah.
  move: adj rfo sval; rewrite /state_open_seq/= -cat_rcons=> adj rfo sval.
  have := open_cells_decomposition_cat adj rfo sval exc2 pal.
  rewrite /= oe' -[(fop ++ (lsto :: fc')%SEQ)%list]/(fop ++ (lsto :: fc')).
  rewrite cat_rcons=> oe.
  have := simple_step_safe_side_non_gp_invariant boxwf nocs' inbox_edges
    inbox_es lexev sub_evs out_events cle n_in uniqout oe simple_cond
    ss_inv.
  by rewrite cat_rcons.
case: ifP=> [pah | ponh'].
  have := update_open_cell_safe_side_non_gp_invariant boxwf nocs' 
    inbox_edges (esym at_lstx) pah ss_inv.
  by rewrite /step/same_x at_lstx puh' pah eqxx /=.
have puh : point ev <<= lsthe.
  by rewrite -(negbK (_ <<= _)) puh'.
have pah : point ev >>= lsthe.
  by rewrite ponh'.

have := last_case_safe_side_invariant nocs' (esym at_lstx) puh pah ss_inv.
by rewrite /step/same_x at_lstx eqxx puh' ponh' /=.
Qed.

Lemma start_safe_sides bottom top s closed open evs :
  bottom <| top ->
  (* TODO: rephrase this statement in one that is easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {subset events_to_edges evs <= s} ->
  {in evs, forall ev, out_left_event ev} ->
  close_edges_from_events evs ->
  {in s & evs, forall g e, non_inner g (point e)} ->
  {in evs, forall e, uniq (outgoing e)} ->
  main_process bottom top evs = (open, closed) ->
 {in closed, forall c,
     low c <| high c /\
     low c != high c /\
     left_limit c < right_limit c /\
     closed_cell_side_limit_ok c /\
    forall p : pt,
     in_safe_side_left p c || in_safe_side_right p c ->
     {in events_to_edges evs, forall g, ~ p === g} /\
     {in evs, forall ev, p != point ev}} /\
  {subset (cell_edges closed) <= [:: bottom, top & s]} /\
  all (@closed_cell_side_limit_ok R) closed /\
  size open = 1%N /\ low (head_cell open) = bottom /\
    high (head_cell open) = top /\
    {in open & closed, disjoint_open_closed_cells R} /\
    (evs != [::] ->
      left_limit (head_cell open) < min (p_x (right_pt bottom))
      (p_x (right_pt top))).
Proof.
move=> boxwf startok nocs' inbox_s evin lexev evsub out_evs cle
  n_inner uniq_edges.
(* Look in file safe_cells for a plan of the proof. *)
Admitted.

End working_environment.