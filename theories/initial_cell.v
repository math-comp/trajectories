From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg.

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

Lemma initial_intermediate bottom top s events :
(*   sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events -> *)
  bottom <| top ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  close_edges_from_events events ->
  events != [::] ->
  let op0 := (* close_cell (point (head (dummy_event _) events))  *)
               (start_open_cell bottom top) in
  all open_cell_side_limit_ok [:: op0] /\
  cells_bottom_top bottom top [:: op0] /\
  adjacent_cells [:: op0] /\
  seq_valid [:: op0] (point (head dummy_event events)) /\
  s_right_form [:: op0] /\
  all (inside_box bottom top) [seq point e | e <- behead events] /\
  close_edges_from_events (behead events) /\
  {in behead events, forall e, out_left_event e} /\
  close_alive_edges bottom top [:: op0] events  /\
  valid_edge bottom (point (head dummy_event events)) /\
  valid_edge top (point (head dummy_event events)) /\
  open_cells_decomposition ([::] ++ [:: op0])
        (point (head dummy_event events)) =
       ([::], [::], op0, [::], low op0, high op0) /\
  {in bottom :: top :: s &, no_crossing R} /\
  {in all_edges [:: op0] events &, no_crossing R} /\
  pairwise edge_below (bottom :: [seq high c | c <- [:: op0]]) /\
  sorted (@lexPtEv _) (behead events).
Proof.
move=> boxwf startok nocs' evin lexev evsub out_evs cle.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
case evsq : events => [ | ev future_events]; [by [] | move=> _ /=].
set op0 := (start_open_cell bottom top).
have op0sok : all open_cell_side_limit_ok ([::] ++ [::op0]).
  by rewrite /= /op0 startok.
have cbtom0 : cells_bottom_top bottom top [:: op0].
  by rewrite /op0 /cells_bottom_top/cells_low_e_top/= !eqxx.
have adj0: adjacent_cells [:: op0] by [].
have sval0 : seq_valid [:: op0] (point ev).
  move: evin; rewrite evsq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /= /valid_edge/generic_trajectories.valid_edge /= !betW.
have rf0: s_right_form [:: op0] by rewrite /= boxwf.
have inbox0 : all (inside_box bottom top) [seq point e | e <- future_events].
  by move: evin; rewrite evsq map_cons /= => /andP[].
have cle0 : close_edges_from_events future_events.
  by move: cle; rewrite evsq /= => /andP[].
have oute0 : {in future_events, forall e, out_left_event e}.
  by move=> e ein; apply: out_evs; rewrite evsq inE ein orbT.
have clae0 : close_alive_edges bottom top [:: op0] (ev :: future_events).
  by rewrite /=/end_edge_ext !inE !eqxx !orbT.
have noc0 : {in all_edges [:: op0] (ev :: future_events) &, no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite -evsq !inE.
  move=> /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by move=> /evsub ->; rewrite !orbT.
have [vb vt] : valid_edge bottom (point ev) /\ valid_edge top (point ev).
  have /(allP sval0) : start_open_cell bottom top \in [:: op0].
    by rewrite inE eqxx.
  by rewrite /= => /andP[].
have /andP[/andP[pal puh] _] : inside_box bottom top (point ev).
   by apply: (@allP pt _ _ evin); rewrite evsq map_f// inE eqxx.
have : open_cells_decomposition [:: op0] (point ev) =
  ([::], [::], op0, [::], bottom, top).
  apply: (open_cells_decomposition_single
           (isT : adjacent_cells ([::] ++ [:: op0])) rf0 sval0 pal puh).
have pw0 : pairwise edge_below (bottom :: [seq high c | c <- [::op0]]).
  by rewrite /= !andbT /=.
have lexev0 : sorted (@lexPtEv _) future_events.
  by move: lexev; rewrite evsq=> /path_sorted.
do 15 (split; first by []).
by [].
Qed.

Lemma initial_common_invariant bottom top s events:
  bottom <| top ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} ->
  close_edges_from_events events ->
  events != [::] ->
  common_invariant bottom top s
    (initial_state bottom top events) (behead events).
Proof.
move=> boxwf startok nocs' evin lexev evsub out_evs uniqout cle evsn0.
have :=
  initial_intermediate boxwf startok nocs' evin lexev evsub out_evs cle evsn0.
case evsq : events evsn0 => [ | ev future_events]; [by [] | move=> _].
move=> [op0sok [cbtom0 [adj0 /=
           [sval0 [rf0 [inbox0 [cle0 [oute0 [clae0 [vb
             [vt [oe [nocs [noc0 [pw0 lexev0]]]]]]]]]]]]]]].
have evins : ev \in events by rewrite evsq inE eqxx.
set op0 := start_open_cell bottom top.
case oca_eq:  (opening_cells_aux _ _ _ _) => [nos lno].
set w := Bscan _ _ _ _ _ _ _.
have [state1 ] : exists state1, state1 = w by exists w.
rewrite /w => {w} st1q.
set cl0 := lst_closed state1.
set ops0 := [::] ++ [:: op0].
have evsin0 : all (inside_box bottom top) [seq point ev | ev <- events].
  exact: evin.
have oute : out_left_event ev by apply: out_evs.
have oute' : {in sort edge_below (outgoing ev), forall g,
                  left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
have edges_sub1 : {subset all_edges (rcons nos lno)
        future_events <= [:: bottom, top & s]}.
  move=> g; rewrite mem_cat=> /orP[ | gfut ]; last first.
    have /evsub {}gfut : g \in events_to_edges events.
      by rewrite evsq events_to_edges_cons mem_cat gfut orbT.
    by rewrite !inE gfut; rewrite !orbT.
  have := opening_cells_subset vb vt oute.
  rewrite /opening_cells oca_eq=> main.
  rewrite mem_cat=> /orP[] /mapP [c /main + ->] => /andP[]; rewrite !inE.
    move=> /orP[-> | +] _; first by rewrite ?orbT.
    move=> {}main; apply/orP; right; apply/orP; right.
    by apply/evsub/flattenP; exists (outgoing ev); rewrite // map_f.
  move=> _ /orP[-> |]; first by rewrite ?orbT.
  move=> {}main; apply/orP; right; apply/orP; right.
  by apply/evsub/flattenP; exists (outgoing ev); rewrite // map_f.
have pin : inside_box bottom top (point ev).
  by apply: (@allP pt _ _ evin); rewrite evsq /= inE eqxx.
have inbox_all_events0 :
  all (inside_box bottom top) [seq point x | x <- (ev :: future_events)].
  by move: evin; rewrite evsq.
have evlexfut : path (@lexPtEv _) ev future_events.
  by move: lexev; rewrite evsq.
have rf0' : s_right_form ([::] ++ [:: start_open_cell bottom top]) by [].
have cle0' : close_edges_from_events (ev :: future_events) by rewrite -evsq.
have := invariant1_default_case
          inbox_all_events0 oute rf0' cbtom0 adj0 sval0 cle0' clae0 noc0
          evlexfut.
rewrite oe oca_eq /=.
move=> /[dup] inv1 -[] clae1 [] sval' [] adj1 [] cbtom1 rf1.
have rl0 : {in [::], forall c : cell, right_limit c <= p_x (point ev)} by [].
have cl0q : cl0 = close_cell (point ev) op0 by rewrite /cl0 st1q.
rewrite -cats1 in edges_sub1 sval'.
have lstx1op : lst_x _ _ state1 = left_limit (lst_open state1).
  have := opening_cells_left oute vb vt; rewrite /opening_cells.
  by rewrite oca_eq st1q => -> //=; rewrite mem_rcons inE eqxx.
have he1q' : high (lst_open state1) = lst_high _ _ state1.
  rewrite st1q /=.
  by have := opening_cells_aux_high_last vb vt oute'; rewrite oca_eq.
move: lstx1op he1q'; rewrite st1q=> lstx1op he1q'.
have oks1 : all open_cell_side_limit_ok (nos ++ [:: lno]).
  have := pin => /andP[] /andP[] /underWC pal puh _.
  have := opening_cells_side_limit vb vt pal puh oute.
  by rewrite /opening_cells oca_eq cats1.
have lexfutev : {in future_events, forall e,
     lexPt (last dummy_pt (left_pts lno)) (point e)}.
  move=> e ein.
  have := allP evin (point ev) (map_f _ evins).
  move=> /andP[] /andP[] pal puh _.
  have noce : {in bottom:: rcons (sort edge_below (outgoing ev)) top &,
           no_crossing R}.
    move=> g1 g2 g1in g2in; apply noc0.
      move: g1in; rewrite inE mem_rcons inE mem_sort orbA=> /orP[]g1in.
        by rewrite 2!mem_cat /start_open_cell /= !mem_seq1 g1in.
      by rewrite mem_cat orbC /events_to_edges /= mem_cat g1in.
    move: g2in; rewrite inE mem_rcons inE mem_sort orbA=> /orP[]g2in.
      by rewrite 2!mem_cat /start_open_cell /= !mem_seq1 g2in.
    by rewrite mem_cat orbC /events_to_edges /= mem_cat g2in.
  have lnoin : lno \in opening_cells (point ev) (outgoing ev) bottom top.
    by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
  have :=
    opening_cells_last_lexePt oute (underWC pal) puh vb vt noce boxwf lnoin.
  move=> /lexePt_lexPt_trans; apply.
  move: (lexev).
  rewrite evsq sorted_lexPtEv_lexPt /= (path_sortedE (@lexPt_trans _)).
  by move=> /andP[] /allP /(_ _ (map_f _ ein)).
have uniqout' : {in future_events, forall e, uniq (outgoing e)}.
  by move=> e ein; apply: uniqout; rewrite evsq inE ein orbT.
have no_dup : {in [seq high c | c <- nos ++ [:: lno]] & future_events,
   forall g e, g \notin outgoing e}.
  move=> g e /mapP [c' c'in gc'] ein.
  have := opening_cells_subset vb vt oute; rewrite /opening_cells.
  rewrite oca_eq -cats1 => /(_ c' c'in) /andP[] _ gin.
  apply/negP=> abs.
  have ein' : e \in events by rewrite evsq inE ein orbT.
  have out_e : out_left_event e by apply: out_evs.
  have lefte : left_pt g = point e.
     by apply/eqP/out_e.
  move: gin; rewrite inE => /orP[/eqP gtop | gev].
    have := allP evin (point e) (map_f _ ein').
    rewrite /inside_box strict_nonAunder // -gtop; last first.
      by rewrite -gc' -lefte valid_edge_left.
    have := out_e g abs => /eqP <-.
    by rewrite -gc' left_on_edge !andbF.
  move : evlexfut; rewrite (path_sortedE (@lexPtEv_trans _))=> /andP[] + _.
  move=> /allP /(_ e ein); rewrite /lexPtEv -lefte.
  by rewrite gc' (eqP (oute _  gev)) lexPt_irrefl.
by constructor.
Qed.

Lemma initial_common_non_gp_invariant bottom top s events:
  bottom <| top ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} ->
  close_edges_from_events events ->
  events != [::] ->
  common_non_gp_invariant bottom top s
    (initial_state bottom top events) (behead events).
Proof.
move=> boxwf startok nocs' evin lexev evsub out_evs uniqout cle evsn0.
have ici := initial_common_invariant boxwf startok nocs' evin lexev evsub
            out_evs uniqout cle evsn0.
have [ev1 [evs evsq]] : exists ev1 evs, events = ev1 :: evs.
  by case evsq :  events evsn0 => [ | ev1 evs] //= _; exists ev1, evs.
case oca_eq:
    (opening_cells_aux (point ev1) (sort edge_below (outgoing ev1))
      bottom top) => [nos lno].
have oute1 : out_left_event ev1.
  by apply: out_evs; rewrite evsq inE eqxx.
have oute1' : {in sort edge_below (outgoing ev1), forall g,
                  left_pt g == point ev1}.
  by move=> g; rewrite mem_sort; apply: oute1.
have [samex srt]: all (fun p => p_x p == left_limit lno) (left_pts lno) /\
     sorted >%R [seq p_y p | p <- left_pts lno].
  have := sides_ok ici.
  rewrite /initial_state evsq oca_eq /state_open_seq/= all_cat /= andbT.
  move=> /andP[] _; rewrite /open_cell_side_limit_ok.
  by move=> /andP[] _ /andP[] samex /andP[] srt _.
have ev1in : inside_box bottom top (point ev1).
  by apply: (allP evin); rewrite evsq map_f // inE eqxx.
have [vb vt] : valid_edge bottom (point ev1) /\ valid_edge top (point ev1).
  by rewrite !(inside_box_valid_bottom_top ev1in) // !inE eqxx ?orbT.
move: (ev1in); rewrite /inside_box=> /andP[] /andP[] /underWC ev1a ev1u _.
have [slptso nthq] := opening_cells_aux_event vb vt ev1a ev1u oute1' oca_eq.
have [slpts path_right] :
  (1 < size (left_pts (lst_open (initial_state bottom top events))))%N /\
  path (@lexPt _)
    (nth dummy_pt (left_pts (lst_open (initial_state bottom top events))) 1)
    [seq point e | e <- behead events].
  rewrite /initial_state evsq oca_eq /state_open_seq/=.
  split; first by [].
  by rewrite nthq path_map; move: lexev; rewrite evsq.
(* To be kept until one proves disjoint_non_gp_invariant for initial_state
*)
by constructor.
Qed.

Lemma initial_disjoint_non_gp_invariant bottom top s events:
  bottom <| top ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} ->
  close_edges_from_events events ->
  events != [::] ->
  disjoint_non_gp_invariant bottom top s
    (initial_state bottom top events) (behead events).
Proof.
move=> boxwf startok nocs' evin lexev evsub out_evs uniqout cle evsn0.
have ici := initial_common_invariant boxwf startok nocs' evin lexev evsub
            out_evs uniqout cle evsn0.
have icomng := initial_common_non_gp_invariant boxwf startok nocs' evin lexev
    evsub out_evs uniqout cle evsn0.
have [ev1 [evs evsq]] : exists ev1 evs, events = ev1 :: evs.
  by case evsq :  events evsn0 => [ | ev1 evs] //= _; exists ev1, evs.
case oca_eq:
    (opening_cells_aux (point ev1) (sort edge_below (outgoing ev1))
      bottom top) => [nos lno].
have oute1 : out_left_event ev1.
  by apply: out_evs; rewrite evsq inE eqxx.
have oute1' : {in sort edge_below (outgoing ev1), forall g,
                  left_pt g == point ev1}.
  by move=> g; rewrite mem_sort; apply: oute1.
have ev1in : inside_box bottom top (point ev1).
  by apply: (allP evin); rewrite evsq map_f // inE eqxx.
have [vb vt] : valid_edge bottom (point ev1) /\ valid_edge top (point ev1).
  by rewrite !(inside_box_valid_bottom_top ev1in) // !inE eqxx ?orbT.
have noc' : {in rcons (bottom :: sort edge_below (outgoing ev1)) top &,
  no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: sub_in2 nocs'=> g; rewrite mem_rcons !(inE, mem_cat) orbCA mem_sort.
  do 2 (move=> /orP [/eqP -> | ]; rewrite ?eqxx ?orbT //).
  move => gout1; do 2 (apply/orP; right).
  by apply evsub; rewrite evsq /= mem_cat gout1.
move: (ev1in); rewrite /inside_box=> /andP[] /andP[] /underWC ev1a ev1u _.
have [slptso nthq] := opening_cells_aux_event vb vt ev1a ev1u oute1' oca_eq.
have lex_left : {in state_open_seq (initial_state bottom top events),
   forall c, lexePt (bottom_left_corner c)
     (nth dummy_pt (left_pts (lst_open (initial_state bottom top events))) 1)}.
  rewrite /initial_state evsq oca_eq /state_open_seq/=.
  move=> c cin.
  have := opening_cells_last_lexePt oute1 ev1a ev1u vb vt noc' boxwf.
  by rewrite nthq /opening_cells oca_eq -cats1 => /(_ c cin).
have oc_dis : {in nos ++ [:: lno] & [:: close_cell (point ev1)
    (start_open_cell bottom top)], disjoint_open_closed_cells R}.
  admit.
have cl_dis : {in [:: close_cell (point ev1) (start_open_cell bottom top)] &,
                disjoint_closed_cells R}.
  admit.
rewrite /initial_state evsq oca_eq /state_open_seq/=.
move : icomng; rewrite /initial_state evsq oca_eq=> icomng.
have ipw : pairwise edge_below (bottom :: [seq high c | c <- nos ++ [::lno]]).
  Search "openin" "pairwise".
  have := opening_cells_pairwise oute1 _ _ ev1u.

End working_environment.