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
  (point_strictly_under_edge (RealField.sort R) eq_op <=%R +%R
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
move: (ev1in); rewrite /inside_box=> /andP[] /andP[] ev1a ev1u _.
have [slptso nthq] := 
  opening_cells_aux_event vb vt (underWC ev1a) ev1u oute1' oca_eq.
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

(* Lemma start_cover (bottom top : edge) (s : seq edge) closed open :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, no_crossing R} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  start (edges_to_events s) bottom top = (closed, open) ->
  forall p, inside_box bottom top p ->
  has (inside_closed' p) closed || has (inside_open' p) open.
Proof.
move=> boxwf boxwf2 nocs leftin rightin; rewrite /start.
set evs := edges_to_events s.
have/perm_mem := edges_to_events_no_loss s.
  rewrite -/evs/events_to_edges/= => stoevs.
set op0 := [:: Bcell (leftmost_points bottom top) [::] bottom top].
set cl0 := (X in scan _ _ X).
have : sorted (@lexPt R) [seq point x | x <- evs].
  by apply: sorted_edges_to_events.
have : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have : adjacent_cells op0 by [].
have : s_right_form op0 by rewrite /= boxwf.
have : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have : {in cell_edges op0 ++ flatten [seq outgoing i | i <- evs] &,
         no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by rewrite -stoevs => ->; rewrite ?orbT.
have : {in evs, forall ev, out_left_event ev}.
  by apply: out_left_edges_to_events.
have : close_edges_from_events bottom top evs.
  by apply: edges_to_events_wf.
have evsin0 : all (inside_box bottom top)
    [seq point ev | ev <- evs].
  apply/allP.
  have : {subset [seq right_pt g | g <- s] <= inside_box bottom top}.
    by apply/allP: rightin.
  have : {subset [seq left_pt g | g <- s] <= inside_box bottom top}.
    by apply/allP: leftin.
  by apply: edges_to_events_subset.
have btm_left0 : {in [seq point e | e <- evs],
         forall e,  bottom_left_cells_lex op0 e}.
  move=> ev /[dup] /(allP evsin0) /andP[_ /andP[valb valt]] evin c.
  rewrite /op0 inE /lexPt /bottom_left_corner=> /eqP -> /=.
  by apply/orP; left; apply/inside_box_left_ptsP/(allP evsin0).
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have cov0 : forall p, all (lexePt p) [seq point ev | ev <- evs] ->
         cover_left_of bottom top p op0 cl0.
  move=> p limrp q inbox_q qp; apply/orP; left; apply/hasP.
  exists (Bcell (leftmost_points bottom top) nil bottom top).
    by rewrite /op0 inE eqxx.
  rewrite inside_open'E.
  apply/andP; split;[ | apply/andP; split].
  - by apply: underW; move: inbox_q=> /andP[] /andP[].
  - by move: inbox_q=> /andP[] /andP[].
  - rewrite /open_limit /=.
    case: (ltrP  (p_x (right_pt bottom)) (p_x (right_pt top))) => _.
    rewrite inside_box_left_ptsP //.
    by move: inbox_q => /andP[] _ /andP[] /andP[] _ /ltW ->.
  rewrite inside_box_left_ptsP //.
  by move: inbox_q => /andP[] _ /andP[] _ /andP[] _ /ltW ->.
have leftlim0 : {in op0, forall c p, inside_box bottom top p ->
         left_limit c = p_x p ->
         contains_point' p c -> has (inside_closed' p) cl0}.
  move=> c + p; rewrite inE -[Bcell _ _ _ _]/(start_open_cell bottom top).
  move=> /eqP -> {c}.
  move/inside_box_left_ptsP/[swap].
  by rewrite (leftmost_points_max boxwf2)=> ->; rewrite lt_irreflexive.
move: cov0 evsin0 sval0 btm_left0 leftlim0; move=> {stoevs}.
elim: evs op0 cl0 => [ | ev evs' Ih]
   op cl main evsin sval btm_left llim clev oute noc clae rfo adj cbtom sortev.
  rewrite /= => [][] <- <- p inbox_p.
  have lexpp : lexePt p p by rewrite lexePt_eqVlt eqxx.
  by rewrite orbC; apply: (main p isT p inbox_p lexpp).
rewrite /=.
case stepeq : (step ev op cl) => [op' cl'].
move=> scaneq.
have inbox_e : inside_box bottom top (point ev).
  by apply: (allP evsin); rewrite map_f // inE eqxx.
have := sval isT; rewrite /= => sval'.
have oute' : out_left_event ev by apply: oute; rewrite inE eqxx.
have btm_left' : bottom_left_cells_lex op (point ev).
  by apply: btm_left; rewrite inE eqxx.
have cov : cover_left_of bottom top (point ev) op cl.
  apply: main=> /=; rewrite lexePt_eqVlt eqxx /=.
  move: sortev; rewrite /sorted /=.
  rewrite  (path_sortedE (@lexPt_trans R)) // => /andP[+ _].
  by apply: sub_all; exact: lexPtW.
have cov' : forall p : pt,
    all (lexePt p) [seq point ev0 | ev0 <- evs'] ->
    cover_left_of bottom top p op' cl'.
  have := step_keeps_cover sortev cbtom adj inbox_e sval' oute' rfo clae clev
           noc btm_left' llim stepeq cov.
  move=> it p; apply: it.
have evle : forall ev', ev' \in evs' -> lexPt (point ev) (point ev').
  move=> ev' ev'in.
  move: sortev=> /=; rewrite (path_sortedE (@lexPt_trans R))=> /andP[]/allP.
  by move=> /(_ (point ev')) + _; apply; apply map_f.
have svalr : evs' != [::] ->
       seq_valid op' (head dummy_pt [seq point ev0 | ev0 <- evs']).
  case evs'eq : evs' => [// | a q] /= _.
  have inbox_a : inside_box bottom top (point a).
    by apply: (allP evsin); rewrite evs'eq !inE eqxx orbT.
  have eva : lexPt (point ev) (point a).
    by apply: evle; rewrite evs'eq inE eqxx.
  have limra : forall e', e' \in evs' -> lexePt (point a) (point e').
    rewrite evs'eq => e'; rewrite inE => /orP[/eqP -> | e'q ].
      by rewrite lexePt_eqVlt eqxx.
    move: sortev=> /=; rewrite evs'eq=> /path_sorted/=; rewrite path_sortedE.
      by move=>/andP[]/allP/(_ (point e') (map_f (@point _) e'q))/lexPtW.
    exact: lexPt_trans.
  have := step_keeps_valid inbox_a inbox_e eva oute' rfo cbtom adj sval' clae
            clev limra stepeq.
  by [].
have btm_leftr:
   {in [seq point e | e <- evs'], forall e, bottom_left_cells_lex op' e}.
  have btm_left2 :=
    step_keeps_left_pts_inf inbox_e oute' rfo sval' adj cbtom clae clev
           noc btm_left' stepeq.
  by move=> evp /mapP [ev' ev'in ->]; apply/btm_left2/evle.
have evsinr : all (inside_box bottom top) [seq point ev' | ev' <- evs'].
  by move: evsin; rewrite /= => /andP[].
have clevr : close_edges_from_events bottom top evs'.
  by move: clev; rewrite /= => /andP[].
have outer :{in evs', forall ev0 : event, out_left_event ev0}.
  by move: oute; apply: sub_in1=> x xin; rewrite inE xin orbT.
have nocr : {in cell_edges op' ++ flatten [seq outgoing i | i <- evs'] &,
     no_crossing R}.
  move: noc; apply: sub_in2=> x.
  rewrite mem_cat=> /orP[].
    move/(step_sub_open_edges cbtom adj sval' oute' inbox_e stepeq)=> it.
    by rewrite /= /cell_edges catA -(catA _ _ (outgoing ev)) mem_cat it.
  by move=> xinf; rewrite /= !mem_cat xinf !orbT.
have claer : close_alive_edges bottom top op' evs'.
  by have := step_keeps_closeness inbox_e oute' rfo cbtom adj sval' clev
      clae stepeq.
have rfor : s_right_form op'.
  have noc1: {in  cell_edges op ++ outgoing ev &, no_crossing R}.
    move: noc; apply sub_in2=> x.
    rewrite mem_cat=> /orP[it| xino].
      by rewrite /= /cell_edges catA 2!mem_cat it.
    by rewrite /= !mem_cat xino !orbT.
  by apply: (step_keeps_right_form cbtom adj inbox_e sval' noc1 _ _ stepeq).
have adjr : adjacent_cells op'.
  by have := step_keeps_adjacent inbox_e oute' sval' cbtom stepeq adj.
have cbtomr : cells_bottom_top bottom top op'.
  by apply: (step_keeps_bottom_top inbox_e sval' adj cbtom oute' stepeq).
have sortev' : sorted (@lexPt R) [seq point x | x <- evs'].
  by move: sortev; rewrite /= => /path_sorted.
have llim' : {in op', forall c p, inside_box bottom top p ->
                  left_limit c = p_x p ->
                  contains_point' p c -> has (inside_closed' p) cl'}.
  by apply: (step_keeps_cover_left_border cbtom
         adj inbox_e sval' oute' rfo clae
       clev noc btm_left' stepeq llim).
by have := Ih _ _ cov' evsinr svalr btm_leftr llim' clevr outer nocr claer
  rfor adjr cbtomr sortev' scaneq.
Qed. *)

Lemma start_comm (bottom top : edge) (s : seq edge) events :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  (* {in bottom :: top :: s &, forall g1 g2, inter_at_ext g1 g2} -> *)
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  (* {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} -> 
  close_edges_from_events events ->*)
  events != [::] ->
  inv1_seq bottom top events [:: start_open_cell bottom top].
Proof.
move=> boxwf startok (*nocs'*) evin lexev evsub (*out_evs uniqout cle*)  evn0.
have [ev1 [evs evsq]] : exists ev1 evs, events = ev1 :: evs.
  by move : evn0; case: (events) => [ | ev1 evs] // _; exists ev1, evs.
have clae : close_alive_edges bottom top [:: start_open_cell bottom top] events.
  by rewrite /=/end_edge/end_edge_ext !inE !eqxx ?orbT.
split; first by [].
have sval' : events = [::] \/ seq_valid [:: start_open_cell bottom top]
               (point (head dummy_event events)).
  right.
  have inbox_e : inside_box bottom top (point ev1).
  by apply: (allP evin); rewrite map_f // evsq inE eqxx.
  have := inside_box_valid_bottom_top inbox_e => it.
  by rewrite evsq /= !it // !inE ?eqxx ?orbT.
split; first by [].
have adj0 : adjacent_cells [:: start_open_cell bottom top] by [].
split; first by [].
have cbtom0 : cells_bottom_top bottom top [:: start_open_cell bottom top].
  by rewrite /cells_bottom_top  /cells_low_e_top /= !eqxx.
split; first by [].
have rfo0 : s_right_form [:: start_open_cell bottom top].
  by rewrite /= boxwf.
by [].
Qed.

Lemma non_degenerate_box bottom top (p : pt) :
  inside_box bottom top p -> bottom != top.
Proof.
move=> /[dup] inboxp /andP[] /andP[] pa pu Extra; apply/eqP => abs.
have := inside_box_valid_bottom_top inboxp=> vbt.
move: pa; rewrite under_onVstrict; last by apply: vbt; rewrite inE eqxx.
by rewrite abs pu orbT.
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
have vsop : valid_cell (start_open_cell bottom top) (point ev1).
  by exact: (conj vb vt).
have noc0 : {in all_edges [::start_open_cell bottom top] (ev1 :: evs) &,
     no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: sub_in2 nocs'; rewrite -evsq=> g; rewrite mem_cat=> /orP[]; last first.
    by move=> /evsub; rewrite !inE orbA orbC=> ->.
  by rewrite /= !inE => /orP[] /eqP ->; rewrite eqxx ?orbT.
have noc' : {in rcons (bottom :: sort edge_below (outgoing ev1)) top &,
  no_crossing R}.
  apply: inter_at_ext_no_crossing.
  apply: sub_in2 nocs'=> g; rewrite mem_rcons !(inE, mem_cat) orbCA mem_sort.
  do 2 (move=> /orP [/eqP -> | ]; rewrite ?eqxx ?orbT //).
  move => gout1; do 2 (apply/orP; right).
  by apply evsub; rewrite evsq /= mem_cat gout1.
move: (ev1in); rewrite /inside_box=> /andP[] /andP[] ev1a ev1u _.
have [slptso nthq] :=
  opening_cells_aux_event vb vt (underWC ev1a) ev1u oute1' oca_eq.
have rlclq : right_limit (close_cell (point ev1) (start_open_cell bottom top))
  = p_x (point ev1).
  by apply: close_cell_right_limit.
have lex_left : {in state_open_seq (initial_state bottom top events),
   forall c, lexePt (bottom_left_corner c)
     (nth dummy_pt (left_pts (lst_open (initial_state bottom top events))) 1)}.
  rewrite /initial_state evsq oca_eq /state_open_seq/=.
  move=> c cin.
  have := opening_cells_last_lexePt oute1 (underWC ev1a) ev1u vb vt noc' boxwf.
  by rewrite nthq /opening_cells oca_eq -cats1 => /(_ c cin).
have oc_dis : {in nos ++ [:: lno] & [:: close_cell (point ev1)
    (start_open_cell bottom top)], disjoint_open_closed_cells R}.
  have closed_side : forall p, inside_closed' p
    (close_cell (point ev1) (start_open_cell bottom top)) ->
    p_x p <= p_x (point ev1).
  by move=> p /andP[] /andP[] _ /andP[] _ + _; rewrite rlclq.
  have open_side : forall c : cell, c \in nos ++ [:: lno] ->
    forall p, inside_open' p c -> p_x (point ev1) < p_x p.
    move=> c; rewrite cats1 => cin p pin.
    have := opening_cells_left oute1 vb vt; rewrite /opening_cells oca_eq.
    move=> /(_ _ cin)=> llc.
    by move: pin => /andP[] _ /andP[] _; rewrite llc.
  move=> c1 c2 c1in c2in p; apply/negP=> /andP[] pino pinc.
  have := open_side _ c1in  _ pino; rewrite ltNge.
  move: c2in; rewrite inE => /eqP c2q; rewrite c2q in pinc.
  by rewrite (closed_side _ pinc).
have cl_dis : {in [:: close_cell (point ev1) (start_open_cell bottom top)] &,
                disjoint_closed_cells R}.
  by move=> e1 e2; rewrite !inE=> /eqP -> /eqP ->; left.
have ipw : pairwise edge_below (bottom :: [seq high c | c <- nos ++ [::lno]]).
  have noc0' : {in all_edges ([::] ++ start_open_cell bottom top :: [::])
    (ev1 :: evs) &, no_crossing R} by [].
  have := opening_cells_pairwise oute1 noc0' ev1a ev1u _ _ vb vt.
    rewrite !mem_cat !inE !eqxx !orbT => /(_ isT isT).
    rewrite /opening_cells oca_eq cats1 => pwo.
    rewrite /= pwo andbT; apply/allP=> g /mapP [c cin gc].
    have := opening_cells_subset vb vt oute1=> /(_ c).
    rewrite /opening_cells oca_eq -gc=> /(_ cin)=> /andP[] _ gin.
    have babg : below_alt bottom g.
      apply: noc0; rewrite ?mem_cat ?inE ?eqxx //.
      move: gin; rewrite inE=> /orP[/eqP -> | ->]; first by rewrite eqxx ?orbT.
      by rewrite ?orbT.
    move: gin; rewrite inE => /orP[/eqP -> | gin]; first by [].
    move: babg; rewrite below_altC=> bagb.
    have := edge_below_from_point_under bagb _ vb.
    have vlg : valid_edge g (left_pt g) by rewrite valid_edge_left.
    move: ev1a.
    rewrite -(eqP (oute1 _ gin)) vlg (under_onVstrict vlg) left_on_edge.
    by move=> + /(_ isT isT)=> /[swap]/[apply].
have rl_cl_evs : {in [:: close_cell (point ev1) (start_open_cell bottom top)] &
     evs, forall c e, right_limit c <= p_x (point e)}.
  move=> /= c e + ein; rewrite inE => /eqP ->; rewrite rlclq.
  move: lexev; rewrite evsq /= (path_sortedE (@lexPtEv_trans _)).
  move => /andP[] /allP /(_ _ ein) + _ => /orP[].
    by rewrite le_eqVlt orbC => ->.
  by rewrite le_eqVlt=> /andP[] -> .
have srcl0 : (2 < size (right_pts 
                (close_cell (point ev1)
                  (start_open_cell bottom top))))%N.
  rewrite /start_open_cell /close_cell /= (pvertE vb) (pvertE vt).
  case: ifP => [abs1 | A].
    move: ev1u; rewrite (strict_under_pvert_y vt). 
    by rewrite -[X in p_y X](eqP abs1) /= lt_irreflexive.
  case: ifP => [abs2 | B].
    move: ev1a; rewrite (under_pvert_y vb).
    by rewrite [X in p_y X](eqP abs2) /= le_refl.
  by [].
have srcl0W : (1 < size (right_pts 
                (close_cell (point ev1)
                  (start_open_cell bottom top))))%N.
  by rewrite ltnW.
have lr_cl : {in [:: close_cell (point ev1) (start_open_cell bottom top)],
  forall c, left_limit c < right_limit c}.
  move=> c; rewrite inE => /eqP -> {c}; rewrite rlclq.
  have -> : left_limit (close_cell (point ev1) (start_open_cell bottom top)) =
        left_limit (start_open_cell bottom top).
    rewrite /left_limit.
    by have [_ _ ->] := close_cell_preserve_3sides (point ev1)
        (start_open_cell bottom top).
  by have := inside_box_left_ptsP startok ev1in.
have cl0ok : 
  {in [:: close_cell (point ev1) (start_open_cell bottom top)],
    forall c: cell, closed_cell_side_limit_ok c}.
  move=> c; rewrite inE => /eqP ->.
  have cnt_start : contains_point (point ev1) (start_open_cell bottom top).
    by rewrite contains_pointE underWC ?ev1a ?underW ?ev1u.
  by have := close_cell_ok cnt_start
     (vb : valid_edge (low (start_open_cell bottom top)) (point ev1))
     vt startok.
have hclq : high (close_cell (point ev1) (start_open_cell bottom top)) = top.
  by have [_ -> _] :=
    close_cell_preserve_3sides (point ev1) (start_open_cell bottom top).
have pmidcl0evs : 
  path (@lexPt R) (nth dummy_pt (right_pts (close_cell (point ev1)
                         (start_open_cell bottom top))) 1)
    [seq point x | x <- evs].
  move: srcl0; rewrite /close_cell /= (pvertE vb) (pvertE vt).
  case: ifP=> abs; case: ifP=> B //= _.
  rewrite -[path _ _ _]/(sorted (@lexPt _) 
       [seq point e | e <- (ev1 :: evs)]).
  by rewrite -sorted_lexPtEv_lexPt -evsq.
have btm_left_snd_lsto : {in nos ++ [:: lno], forall c,
  lexePt (bottom_left_corner c) (nth dummy_pt (left_pts lno) 1)}.
  by move: lex_left; rewrite /state_open_seq/=/initial_state evsq oca_eq /=.
have btmo_lex : {in nos ++ [:: lno] & evs,
   forall (c : cell) (e :event), lexPt (bottom_left_corner c) (point e)}.
  move=> c e cin ein.
  have : lexPt (point ev1) (point e).
    move: lexev; rewrite sorted_lexPtEv_lexPt evsq /=.
    rewrite (path_sortedE (@lexPt_trans _)) => /andP[] /allP + _.
    by move=> /(_ (point e)); rewrite map_f ?ein//; apply.
  by apply: lexePt_lexPt_trans; rewrite -nthq; apply: btm_left_snd_lsto.
have llx : {in nos ++ [:: lno], forall c, left_limit c <= p_x (point ev1)}.
  move=> c cin.
  have := opening_cells_left oute1 vb vt; rewrite /opening_cells oca_eq.
  by rewrite -cats1=> /(_ _ cin)=> ->.
have cl0_center : {in [:: close_cell (point ev1) (start_open_cell bottom top)],
   forall c, inside_closed' (cell_center c) c}.
  have ibt : inter_at_ext (low (start_open_cell bottom top)) 
        (high (start_open_cell bottom top)).
     by apply: nocs'; rewrite !inE eqxx ?orbT.
  have lltx := inside_box_left_ptsP startok ev1in.
  have ndb := non_degenerate_box ev1in.
  move=> c; rewrite inE=> /eqP ->.
  exact: (cell_center_close_cell_inside ibt ndb boxwf startok vb vt lltx).
have uniq0 : (bottom \notin [seq high c | c <- nos ++ [:: lno]]) &&
  uniq [seq high c | c <- nos ++ [:: lno]].
  have := opening_cells_high vb vt oute1; rewrite /opening_cells oca_eq.
  rewrite -cats1=> ->.
  rewrite mem_rcons inE mem_sort negb_or (non_degenerate_box ev1in).
  have -> : bottom \notin outgoing ev1.
    apply/negP=> abs; have := oute1 bottom abs => /eqP {}abs.
    move: ev1in=>/andP[] /andP[] + _ _.
    by rewrite -abs under_onVstrict ?left_on_edge // valid_edge_left.
  rewrite rcons_uniq mem_sort.
  have -> : top \notin outgoing ev1.
    apply/negP=> abs; have := oute1 top abs=> /eqP {} abs.
    move: ev1in=> /andP[] /andP[] _ + _.
    by rewrite -abs strict_nonAunder ?left_on_edge // valid_edge_left.
  by rewrite sort_uniq; apply: uniqout; rewrite evsq inE eqxx.

rewrite /initial_state evsq oca_eq /state_open_seq/=.
move : icomng; rewrite /initial_state evsq oca_eq=> icomng.
by constructor.
Qed.

End working_environment.