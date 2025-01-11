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

Lemma left_bottom_not_in bottom top :
  ~~ inside_box bottom top (left_pt bottom).
Proof.
apply/negP=> /andP[].
have := left_on_edge bottom.
move=> /[dup] bon /andP[] _ vlb.
by rewrite (under_onVstrict vlb) bon.
Qed.

Lemma left_top_not_in bottom top :
  ~~ inside_box bottom top (left_pt top).
Proof.
apply/negP=> /andP[].
have := left_on_edge top.
move=> /[dup] ton /andP[] _ vlt.
by rewrite (strict_nonAunder vlt) ton !andbF.
Qed.

(* This lemma is the main result of safety for the whole processing.
  TODO: it relies on the assumption
  that the first open cell is well formed.  This basically means that the
  two edges have a vertical overlap.  This statement should be probably
  be made clearer in a different way.

  TODO: one should probably also prove that the final sequence of open
  cells, here named "open", should be reduced to only one element. *)

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
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /main_process/scan/=.
case evsq : evs => [ | ev future_events]; first by  move=> [] <- <-.
have evsn0 : evs != [::] by rewrite evsq.
case oca_eq : opening_cells_aux => [nos lno].
set istate := Bscan _ _ _ _ _ _ _.
have : safe_side_non_gp_invariant bottom top s [:: ev]
  istate future_events.
  have := initial_safe_side_non_gp_invariant boxwf startok nocs' evsub
    evin lexev out_evs uniq_edges cle evsn0 n_inner.
  have -> : take 1 evs = [:: ev] by rewrite evsq; case: (future_events).
  by rewrite /initial_state /istate evsq oca_eq.
move=> invss req.
suff main: forall events op cl st processed_set,
  safe_side_non_gp_invariant bottom top s processed_set st events ->
  scan events st = (op, cl) ->
  {in cl, forall c,
    low c <| high c /\
    low c != high c /\
    left_limit c < right_limit c /\
    closed_cell_side_limit_ok c /\
    forall p : pt, in_safe_side_left p c || in_safe_side_right p c ->
    {in events_to_edges (processed_set ++ events), forall g, ~ p === g} /\
         {in processed_set ++ events, forall e', p != point e'}} /\
  {in op, forall (c : cell) (p : pt), in_safe_side_left p c ->
         {in events_to_edges (processed_set ++ events), forall g, ~ p === g} /\
         {in processed_set ++ events, forall e', p != point e'}} /\
  {subset (cell_edges cl) <= [:: bottom, top & s]} /\
  size op = 1%N /\
  low (head_cell op) = bottom /\
  high (head_cell op) = top /\
  {in op & cl, disjoint_open_closed_cells R} /\
  (left_limit (head_cell op) < min (p_x (right_pt bottom))
      (p_x (right_pt top))).
  have [A [B [C [E [F [G [H I]]]]]]] := main _ _ _ _ _ invss req.
  split; last by [].
  move=> c cin; move: (A c cin) => [] crf [] difc [] lltr [] clok A'.
  do 4 (split; first by []).
  by move=> p pside; have := A' _ pside.
elim=> [ | {evsq oca_eq istate invss}ev {req}future_events Ih] op cl st p_set.
  case stq : st => [fop lsto lop cls lstc lsthe lstx].
  move=> ss_inv.
  have d_inv := disjoint_ss ss_inv.
  have e_inv := covered_ss ss_inv.
  have ol_lt_fut := left_proc ss_inv.
  have subc := sub_closed ss_inv.
  have b'_e := cl_low_high d_inv subc nocs'.
  have b_e : {in rcons cls lstc, forall c, low c <| high c}.
    by move=> c /b'_e /andP[].
  have d_e : {in (fop ++ lsto :: lop) ++ rcons cls lstc,
    forall c, low c!= high c}.
    move=> c; rewrite mem_cat=> /orP[]; last first.
      by move=> /b'_e/andP[].
    by move=> /(low_diff_high_open d_inv).
    rewrite /= => -[] <- <-; rewrite !cats0.
  split.
    move=> c cin.
    split; first by apply: b_e; rewrite mem_rcons.
    split; first by apply: d_e; rewrite mem_cat mem_rcons cin orbT.
    split; first by apply: (cl_large d_inv); rewrite mem_rcons.
    split; first by apply: (cl_side d_inv); rewrite mem_rcons.
    move=> p pin; split.
      move=> g gin; apply: (safe_side_closed_edges ss_inv gin _ pin).
      by rewrite // mem_rcons.
    move=> e ein.
     apply: (safe_side_closed_points ss_inv ein _ pin).
     by rewrite // mem_rcons.
  split; last first.
    split; last first.
      have comi := ngcomm (common_non_gp_inv_dis d_inv).
      have := inv1 comi.
      rewrite /state_open_seq/= /close_alive_edges.
      move=> [] clae [] _ [] adj [] cbtom rfo.
      have htop : {in fop ++ lsto :: lop, forall c, high c = top}.
        move=> c cin.
        have := allP clae _ cin; rewrite /end_edge_ext ?orbF => /andP[] lP.
        rewrite !inE => /orP[] /eqP hcq; rewrite hcq //.
        have := d_e c; rewrite mem_cat cin hcq=> /(_ isT).
        move: lP; rewrite !inE => /orP[] /eqP lcq; rewrite lcq ?eqxx //.
        move: evin; rewrite evsq /= => /andP[] + _.
        move=> /[dup]/inside_box_valid_bottom_top vbt.
        have vb : valid_edge bottom (point ev) by apply: vbt; rewrite inE eqxx.
        have vt : valid_edge top (point ev).
          by apply: vbt; rewrite !inE eqxx orbT.
        move=> /andP[] /andP[] pab put _ tnb.
        have abs : top <| bottom by rewrite -lcq -hcq; apply: (allP rfo).
        have := order_edges_strict_viz_point' vt vb abs put.
        by move: pab; rewrite under_onVstrict // orbC => /[swap] ->.
      have := inj_high e_inv; rewrite /state_open_seq/= => ijh.
      have f0 : fop = [::].
        elim/last_ind: (fop) adj ijh htop => [ // | fs f1 _] + ijh htop.
        rewrite -cats1 -catA /= => /adjacent_catW[] _ /= /andP[] /eqP f1l _.
        move: (d_e lsto); rewrite !mem_cat inE eqxx ?orbT => /(_ isT).
        rewrite -f1l (htop f1); last by rewrite !(mem_rcons, mem_cat, inE) eqxx.
        by rewrite (htop lsto) ?eqxx // mem_cat inE eqxx ?orbT.
      have l0 : lop = [::].
        case lopq: (lop) adj ijh htop => [ // | l1 ls] + ijh htop.
        move=> /adjacent_catW[] _ /= /andP[] /eqP hl _.
        move: (d_e l1); rewrite lopq !(mem_cat, inE) eqxx ?orbT => /(_ isT).
        rewrite -hl (htop l1); last by rewrite !(mem_cat, inE) eqxx !orbT.
        by rewrite (htop lsto) ?eqxx // mem_cat inE eqxx ?orbT.
      rewrite f0 l0 /=.
      move: cbtom; rewrite f0 l0 /= /cells_bottom_top /cells_low_e_top /=.
      move=> /andP[] /eqP lq /eqP hq.
      do 3 (split; first by []).
      split.
        move=> c1 c2 c1in c2in; apply: (op_cl_dis_non_gp d_inv);
        by rewrite /state_open_seq/state_closed_seq  f0 l0 ?mem_rcons.
      by have := lst_side_lt d_inv.
(* End of lemma *)
    move=> g; rewrite -[lstc :: cls]/([:: lstc] ++ cls) cell_edges_catC cats1.
    by apply: subc.
  move=> c cin p pin.
  split.
    by move=> g gin; have := (safe_side_open_edges ss_inv gin cin pin).
  by move=> e ein; have := (safe_side_open_points ss_inv ein cin pin).
move=> ss_inv {cle lexev evsn0 evsub out_evs evin uniq_edges n_inner}.
have d_inv := disjoint_ss ss_inv.
have e_inv := covered_ss ss_inv.
have ol_lt_fut := left_proc ss_inv.
have subc := sub_closed ss_inv.
have b'_e := cl_low_high d_inv subc nocs'.
have rf_cl : {in state_closed_seq st, forall c, low c <| high c}.
  by move=> c /b'_e /andP[].
have d_e : {in state_open_seq st ++ state_closed_seq st,
  forall c, low c!= high c}.
  move=> c; rewrite mem_cat=> /orP[]; last first.
    by move=> /b'_e/andP[].
  by move=> /(low_diff_high_open d_inv).
have c_inv := common_non_gp_inv_dis d_inv.
have comi := ngcomm (common_non_gp_inv_dis d_inv).
have inbox_es := inbox_events comi.
have lexev := lex_events comi.
have out_evs := out_events comi.
have uniq_evs := uniq_ec comi.
have cle := closed_events comi.
have n_in := non_in_ec e_inv.
have sub_edges := edges_sub comi.
have sub_edges_evs : {subset events_to_edges (ev :: future_events) <= s}.
  move=> g gin.
  have /sub_edges : g \in all_edges (state_open_seq st) (ev :: future_events).
    by rewrite mem_cat gin orbT.
  rewrite !inE orbA=> /orP[gbot | ]; last by [].
  move: gin => /flatten_mapP [e ein gin].
  move: (left_bottom_not_in bottom top) (left_top_not_in bottom top).
  have := allP (inbox_events comi) (point e) (map_f _ ein).
  have : left_pt g = point e.
    by apply/eqP/(out_evs); rewrite ?inE ?eqxx.
  by move: gbot=> /orP[] /eqP -> <- ->.
have ss_inv' : safe_side_non_gp_invariant bottom top s (rcons p_set ev)
  (step st ev) future_events.
  by apply: step_safe_side_invariant.
rewrite -[scan _ _]/(scan future_events (step st ev)) => execq.
rewrite -cat_rcons.
have := (Ih _ _ _ _ ss_inv' execq) => -[A B].
by [].
Qed.

End working_environment.