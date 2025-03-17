From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg initial_cell simple_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

(* Notation prefix, duplicated from cells_alg.v *)
Notation pt := (pt (Num.RealField.sort R)).
Notation p_x := (p_x (Num.RealField.sort R)).
Notation p_y := (p_y (Num.RealField.sort R)).
Notation Bpt := (Bpt (Num.RealField.sort R)).
Notation edge := (edge R).
Notation left_pt := (@left_pt R).
Notation right_pt := (@right_pt R).
Notation event := (event (Num.RealField.sort R) edge).
Notation outgoing := (outgoing (Num.RealField.sort R) edge).
Notation point := (point (Num.RealField.sort R) edge).
Notation cell := (cell (Num.RealField.sort R) edge).

Notation dummy_pt := (dummy_pt (Num.RealField.sort R) 1).
Notation dummy_edge := (dummy_edge (Num.RealField.sort R) 1 edge (@unsafe_Bedge _)).
Notation dummy_cell :=
  (dummy_cell (Num.RealField.sort R) 1 edge (@unsafe_Bedge _)).
Notation dummy_event := (dummy_event (Num.RealField.sort R) 1 edge).
Notation edge_below :=
  (generic_trajectories.edge_below (Num.RealField.sort R) eq_op <=%R +%R
    (fun x y => x - y) *%R 1 edge left_pt right_pt).
Notation "x <| y" := (edge_below x y).
Notation valid_edge :=
  (generic_trajectories.valid_edge (Num.RealField.sort R)
   <=%R edge left_pt right_pt).
Notation vertical_projection :=
  (vertical_projection (Num.RealField.sort R)
  <=%R +%R (fun x y => x - y) *%R
  (fun x y => x / y) edge left_pt right_pt).
Notation point_under_edge :=
  (point_under_edge (Num.RealField.sort R) <=%R +%R (fun x y => x - y) *%R 1
  edge left_pt right_pt).
Notation "p <<= g" := (point_under_edge p g).
Notation "p >>> g" := (~~ (point_under_edge p g)).
Notation point_strictly_under_edge :=
  (point_strictly_under_edge  (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R 1 edge left_pt right_pt).
Notation "p <<< g" := (point_strictly_under_edge p g).
Notation "p >>= g" := (~~ (point_strictly_under_edge p g)).

Notation contains_point :=
  (contains_point (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R 1
    edge left_pt right_pt).

Notation open_cells_decomposition_contact :=
  (open_cells_decomposition_contact (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R 1 edge left_pt right_pt).
Notation open_cells_decomposition_rec :=
  (open_cells_decomposition_rec (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R 1 edge (@unsafe_Bedge R) left_pt
  right_pt).
Notation open_cells_decomposition :=
  (open_cells_decomposition (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R 1 edge (@unsafe_Bedge R) left_pt
  right_pt).

Notation scan_state := (scan_state (Num.RealField.sort R) edge).
Notation sc_open1 := (sc_open1 (Num.RealField.sort R) edge).
Notation lst_open := (lst_open (Num.RealField.sort R) edge).
Notation sc_open2 := (sc_open2 (Num.RealField.sort R) edge).
Notation sc_closed := (sc_closed (Num.RealField.sort R) edge).
Notation lst_closed := (lst_closed (Num.RealField.sort R) edge).

Notation update_closed_cell :=
  (update_closed_cell (Num.RealField.sort R) 1 edge).

Notation set_left_pts :=
  (set_left_pts (Num.RealField.sort R) edge).

Notation low := (low (Num.RealField.sort R) edge).
Notation high := (high (Num.RealField.sort R) edge).
Notation left_pts := (left_pts (Num.RealField.sort R) edge).
Notation right_pts := (right_pts (Num.RealField.sort R) edge).
Notation Bcell := (Bcell (Num.RealField.sort R) edge).
Notation cell_center :=
  (cell_center (Num.RealField.sort R) +%R (fun x y => x / y) 1%:R edge).
Notation left_limit := (left_limit (Num.RealField.sort R) 1 edge).
Notation right_limit := (right_limit (Num.RealField.sort R) 1 edge).
  
Notation closing_cells :=
  (generic_trajectories.closing_cells (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
    *%R (fun x y => x / y) edge left_pt right_pt).
Notation close_cell :=
  (generic_trajectories.close_cell (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
    *%R (fun x y => x / y) edge left_pt right_pt).

Notation set_pts := (set_pts (Num.RealField.sort R) edge).

(* This function is to be called only when the event is in the middle
  of the last opening cell.  The point e needs to be added to the left
  points of one of the newly created open cells, but the one that receives
  the first segment of the last opening cells should keep its existing
  left points.*)
Notation update_open_cell :=
  (update_open_cell (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
  *%R (fun x y => x / y) 1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation update_open_cell_top :=
  (update_open_cell_top (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
  *%R (fun x y => x / y) 1
  edge (@unsafe_Bedge R) left_pt right_pt).

Notation Bscan := (Bscan (Num.RealField.sort R) edge).

Notation opening_cells_aux :=
  (opening_cells_aux (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
  *%R (fun x y => x / y) 1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation simple_step :=
  (generic_trajectories.simple_step (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation step :=
  (step (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R
  (fun x y => x / y) 1 edge (@unsafe_Bedge R) left_pt right_pt).
(*
Definition scan events st : seq cell * seq cell :=
  let final_state := foldl step st events in
  (sc_open1 final_state ++ lst_open final_state :: sc_open2 final_state,
   lst_closed final_state :: sc_closed final_state). *)

Notation start_open_cell :=
  (start_open_cell (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
  *%R (fun x y => x / y) edge left_pt right_pt).

Notation open_cell_side_limit_ok :=
  (@open_cell_side_limit_ok R).

 (* End of notation prefix. *)

(* This lemma only provides a partial correctness statement in the case
  where the events are never aligned vertically.  This condition is
  expressed by the very first hypothesis.  TODO: it relies on the assumption
  that the first open cell is well formed.  This basically means that the
  two edges have a vertical overlap.  This statement should be probably
  be made clearer in a different way.

  TODO: one should probably also prove that the final sequence of open
  cells, here named "open", should be reduced to only one element. *)

Record common_general_position_invariant bottom top edge_set s
  (all_events processed_events events : seq event) :=
  { gcomm : common_invariant bottom top edge_set s all_events processed_events
    events;
   general_pos :
     all (fun ev => lst_x _ _ s < p_x (point ev)) events &&
     sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) events;
}.

Record disjoint_general_position_invariant (bottom top : edge)
 (edge_set : seq edge)
 (s : scan_state) (all_events processed_events events : seq event) :=
 { op_cl_dis :
     {in state_open_seq s & state_closed_seq s,
       disjoint_open_closed_cells R};
   cl_dis : {in state_closed_seq s &, disjoint_closed_cells R};
   common_inv_dis : common_general_position_invariant bottom top
        edge_set s all_events processed_events events;
   pairwise_open : pairwise edge_below
       (bottom :: [seq high c | c <- state_open_seq s]);
   closed_at_left :
       {in state_closed_seq s & events,
          forall c e, right_limit c <= p_x (point e)}}.

Lemma initial_common_general_position_invariant bottom top s 
  events:
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events ->
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
  common_general_position_invariant bottom top s
    (initial_state bottom top events)
    events (take 1 events) (behead events).
Proof.
move=> ltev boxwf startok nocs' evin lexev evsub out_evs uniqout cle evsn0.
have ici := initial_common_invariant boxwf startok nocs' evin lexev evsub
            out_evs uniqout cle evsn0.
constructor; first by exact: ici.
case evsq :  events => [ | ev1 evs] //.
move: ltev; rewrite evsq /=.
rewrite path_sortedE; last by  move=> x y z; apply: lt_trans.
move=> /andP[] + ->; rewrite andbT.
rewrite /initial_state /=.
by case oca_eq:  (opening_cells_aux _ _ _ _).
Qed.

Lemma initial_disjoint_general_position_invariant
    bottom top s events:
   sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events ->
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
  disjoint_general_position_invariant bottom top s
   (initial_state bottom top events) events (take 1 events) (behead events).
Proof.
move=> ltev boxwf startok nocs' evin lexev evsub out_evs uniqout cle evsn0.
have := initial_common_general_position_invariant ltev boxwf startok
  nocs' evin lexev evsub out_evs uniqout cle evsn0.
have := initial_intermediate boxwf startok nocs' evin lexev evsub
   out_evs cle evsn0.
move: evsn0; case evsq : events => [ | ev evs];[by [] | move=> _].
lazy zeta; rewrite [head _ _]/= [behead _]/=.
move=> -[] op0sok [cbtom0 [adj0 [sval0 [rf0 [inbox0
[cle0 [oute0 [clae0 [vb [vt [oe [nocs [noc0 [pw0 lexev0]]]]]]]]]]]]]].
have evins : ev \in events by rewrite evsq inE eqxx.
rewrite /initial_state /state_open_seq/state_closed_seq/= => Cinv.
case oca_eq:  (opening_cells_aux _ _ _ _) Cinv => [nos lno] Cinv.
move: (Cinv)=> -[] []; rewrite /state_open_seq/state_closed_seq/=.
move=> inv1 pxe hlno edges_sub1 cle1 oute1 inbox1 lexevs sok1 gen_pos.
set op0 := start_open_cell bottom top.
have op0_cl0_dis : {in [:: op0] & [::], disjoint_open_closed_cells R} by [].
have inbox0' : all (inside_box bottom top) [seq point e | e <- ev :: evs].
  by rewrite -evsq.
have cl0_dis : {in [::] &, disjoint_closed_cells R} by [].
have rl0 : {in [::], forall c : cell, right_limit c <= p_x (point ev)} by [].
have := @step_keeps_disjoint_default _ bottom top ev [::]
            op0 [::] evs inbox0' (out_evs _ evins) rf0 cbtom0 adj0
            sval0 pw0 op0sok [::] op0_cl0_dis cl0_dis rl0.
  rewrite oe oca_eq /= => -[] cl_dis1 op_cl_dis1.
have pw1 : pairwise edge_below
     (bottom:: [seq high c | c <- (nos ++ [:: lno ])]).
  have rf0' : s_right_form ([::] ++ [:: op0]) by [].
  have := step_keeps_pw_default inbox0' (out_evs _ evins) rf0' cbtom0 adj0
    sval0 noc0 pw0.
  by rewrite oe oca_eq.
have rl_closed1 : {in [:: close_cell (point ev) op0] & evs,
  forall c e, right_limit c <= p_x (point e)}.
  have vho : valid_edge (high op0) (point ev) by [].
  have vlo : valid_edge (low op0) (point ev) by [].
  have := right_limit_close_cell vlo vho=> rlcl0 c e.
  rewrite inE=> /eqP ->.
  move: lexev; rewrite evsq /= path_sortedE; last by apply: lexPtEv_trans.
  move=> /andP[] + _=> /allP /[apply].
  rewrite rlcl0=> /orP[]; first by move/ltW.
  by move=> /andP[] /eqP -> _; apply: le_refl.
by constructor.
Qed.

Lemma simple_step_common_general_position_invariant
  bottom top s fop lsto lop fc cc lcc lc le he cls lstc ev
  lsthe lstx all_events processed_events evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  common_general_position_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx) all_events processed_events
     (ev :: evs) ->
  common_general_position_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev) all_events
     (rcons processed_events ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s oe.
move=> [] comi /andP[] lstxlt ltev'.
have comi' := (simple_step_common_invariant boxwf nocs' inbox_s oe comi).
have ltev1 : all (fun e =>
            lst_x _ _ (simple_step fc cc lc lcc le he cls lstc ev) <
               p_x (point e)) evs &&
         sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) evs.
  rewrite (lstx_eq comi').
  have oute : out_left_event ev by apply: (out_events comi); rewrite inE eqxx.
  have [_ [sval' [adj [cbtom rfo]]]] := inv1 comi.
  have /= /andP[inbox_e inbox_es] := inbox_events comi.
  have sval : seq_valid
          (state_open_seq (Bscan fop lsto lop cls lstc lsthe lstx))
          (point ev).
    by case sval'; first done.
  have [{}pal {}puh vl vp nc]:=
    decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
  have := opening_cells_left oute vl vp.
  rewrite /opening_cells/simple_step/generic_trajectories.simple_step.
  rewrite -/(opening_cells_aux (point ev) (sort edge_below (outgoing ev))
               le he).
  case oca_eq : opening_cells_aux => [nos lno] /=.
  have lnoin : lno \in rcons nos lno by rewrite mem_rcons inE eqxx.
  move => /(_ _ lnoin) ->.
  move: ltev'; rewrite /= path_sortedE //.
  by move=> x y z; apply: lt_trans.
by constructor.
Qed.

Lemma simple_step_disjoint_general_position_invariant
  bottom top s fop lsto lop fc cc lcc lc le he cls lstc ev
  lsthe lstx all_events processed_events evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  disjoint_general_position_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx) all_events processed_events
     (ev :: evs) ->
  disjoint_general_position_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev) all_events
     (rcons processed_events ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s oe.
move=> []; rewrite /state_open_seq/state_closed_seq/=.
move=> oc_dis c_dis Cinv pw rl.
have := Cinv=> -[] []; rewrite /state_open_seq/state_closed_seq/=.
move=> inv1 lstxq lstheq sub_edges events_dec cle out_es uniqout inbox_es.
move=> no_dup lexev oks _ _ _.
have := inv1 => -[] clae [] []; first by [].
move=> sval []adj []cbtom rfo.
rewrite /simple_step.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have Cinv' : common_general_position_invariant bottom top s
         (Bscan (fc ++ nos) lno lc
            (cls ++ lstc :: closing_cells (point ev) cc)
            (close_cell (point ev) lcc) he (p_x (point ev)))
            all_events (rcons processed_events ev) evs.
  have := simple_step_common_general_position_invariant boxwf nocs' inbox_s oe.
  rewrite /simple_step.
  by rewrite oca_eq=> /(_ _ _ lsthe lstx); apply.
have cl_at_left' : {in rcons cls lstc,
        forall c, right_limit c <= p_x (point ev)}.
  by move=> c cin; apply: rl; rewrite // inE eqxx.
have oute : out_left_event ev by apply: out_es; rewrite inE eqxx.
have disjointness := step_keeps_disjoint_default inbox_es oute rfo
         cbtom adj sval pw oks oc_dis c_dis cl_at_left'.
rewrite oe oca_eq /= !cat_rcons -!cats1 /= in disjointness.
have op_cl_dis':
  {in (fc ++ nos) ++ lno :: lc & rcons (cls ++ lstc ::
           closing_cells (point ev) cc) (close_cell (point ev) lcc),
         disjoint_open_closed_cells _}.
   move=> c1 c2; rewrite -!(cats1, catA)=> c1in c2in.
   by apply: (proj2 (disjointness)).
have cl_dis : {in  rcons (cls ++ lstc :: closing_cells (point ev) cc)
                 (close_cell (point ev) lcc) &, disjoint_closed_cells R}.
  by rewrite -!(cats1, catA); apply: (proj1 disjointness).
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
have noc : {in all_edges (fop ++ lsto :: lop) (ev :: evs) &,
                 no_crossing R}.
  by move=> g1 gt2 g1in g2in; apply: nocs; apply: sub_edges.
have pwo' : pairwise edge_below
           (bottom :: [seq high c | c <- (fc ++ nos) ++ lno :: lc]).
  have := step_keeps_pw_default inbox_es oute rfo cbtom adj sval noc pw.
  by rewrite oe oca_eq -catA.
have right_limit_closed' :
  {in  rcons(cls ++
          lstc :: closing_cells (point ev) cc) (close_cell (point ev) lcc) &
     evs, forall c e, right_limit c <= p_x (point e)}.
  have:= step_keeps_right_limit_closed_default inbox_es cbtom adj
    sval lexev cl_at_left'.
  by rewrite oe oca_eq /=.
have all_events_break' : all_events = rcons processed_events ev ++ evs.
  by rewrite cat_rcons.
by constructor.
Qed.

Lemma complete_disjoint_general_position bottom top s closed open evs :
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) evs ->
  bottom <| top ->
  (* TODO: rephrase this statement in one that is easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {subset flatten [seq outgoing e | e <- evs] <= s} ->
  {in evs, forall ev, out_left_event ev} ->
  {in evs, forall ev, uniq (outgoing ev)} ->
  close_edges_from_events evs ->
  main_process bottom top evs = (open, closed) ->
  {in closed &, disjoint_closed_cells R} /\
  {in open & closed, disjoint_open_closed_cells R}.
Proof.
move=> ltev boxwf startok nocs' inbox_s evin lexev evsub out_evs uniq_evs cle.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /main_process/scan.
case evsq : evs => [ | ev future_events].
  move=> [] <- <-; split; last by [].
  by move=> c1 c2; rewrite in_nil.
have evsn0 : evs != [::] by rewrite evsq.
have := initial_disjoint_general_position_invariant ltev boxwf startok nocs'
  evin lexev evsub out_evs uniq_evs cle evsn0.
rewrite /initial_state evsq.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos1 lno1] /=.
have : ev :: future_events = (ev :: take 0 future_events) ++ future_events.
  by case: (future_events).
move: (ev :: future_events) (ev :: take 0 future_events).
elim: (future_events) {oca_eq evsq} (Bscan _ _ _ _ _ _ _)=> [ | ev' fut' Ih] + ae pe.
  move=> state_f /=; case: state_f=> [] f m l cls lstc lsthe lstx.
  move=> aeq /[swap] -[] <- <-; case; rewrite /state_open_seq /state_closed_seq /=.
  move=> dis_op_cl dis_cl *; split; move=> c1 c2 c1in c2in.
    by apply: dis_cl; rewrite // mem_rcons.
  by apply: dis_op_cl; rewrite // mem_rcons.
move=> {evs ltev evin lexev evsub out_evs uniq_evs cle evsn0}.
move=> [fop lsto lop cls lstc lsthe lstx] aeq.
case; set ops' := (state_open_seq _); set (cls' := state_closed_seq _).
rewrite /=.
move=> dis_open_closed dis_cl /[dup] Cinv [] [] inv1 lstxq lstheq sub_edges.
move=> all_events_dec /[dup] cle /andP[cl_e_fut' cle'] out_fut'.
move=> uniq_evs'.
move=> /= /[dup]  inbox_all_events' /andP[inbox_e inbox_all_events].
move=> no_dup lexevs oks.
move=> bottom_left_corner_cond strd.
move=> /andP[] /andP[] lstxlte lstx_fut' ltfut' edges_pairwise cl_at_left.
move: (inv1)=> [] clae [] pre_sval [] adj [] cbtom rfo.
have sval : seq_valid (fop ++ lsto :: lop) (point ev') by case: pre_sval.

rewrite /=; case: ifP=> [_ | ]; last first.
  move=> /negbFE; rewrite /same_x eq_sym=> /eqP abs; suff: False by [].
  by move : lstxlte; rewrite abs lt_irreflexive.
rewrite -/(open_cells_decomposition _ _).
rewrite /generic_trajectories.simple_step.
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
apply: (Ih _ ae (rcons pe ev')).
  by rewrite aeq cat_rcons.
have :=
  simple_step_disjoint_general_position_invariant boxwf nocs' inbox_s oe.
  rewrite /simple_step.
  rewrite oca_eq=> /(_ _ _ lsthe lstx).
by apply.
Qed.

Record edge_covered_general_position_invariant (bottom top : edge)
 (edge_set : seq edge) (all_events processed_set : seq event)
 (s : scan_state) (events : seq event) :=
 { edge_covered_ec : {in processed_set, forall e,
       {in outgoing e, forall g,
       edge_covered g (state_open_seq s) (state_closed_seq s)}};
   processed_covered : {in processed_set, forall e,
       exists2 c, c \in (state_closed_seq s) &
           point e \in (right_pts c : seq pt) /\ point e >>> low c}  ;
   common_inv_ec : common_general_position_invariant bottom top edge_set
     s all_events processed_set events;
   non_in_ec :
      {in edge_set & events, forall g e, non_inner g (point e)};
   inj_high : {in state_open_seq s &, injective high};
   bot_left_cells :
       {in state_open_seq s & events,
          forall c e, lexPt (bottom_left_corner c) (point e)};
   }.


Lemma initial_edge_covering_general_position
  bottom top s events:
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events ->
  sorted (@lexPtEv _) events ->
   bottom <| top ->
  close_edges_from_events events ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall g1 g2, inter_at_ext g1 g2} ->
  {in s & events, forall g e, non_inner g (point e)} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} ->
  events != [::] ->
  edge_covered_general_position_invariant bottom top s
   events [:: (head dummy_event events)]
   (initial_state bottom top events) (behead events).
Proof.
move=> gen_pos lexev wf cle startok nocs' n_inner inbox_es sub_es out_es
  uniq_out_es evsn0.
rewrite /initial_state.
have := initial_intermediate wf startok nocs' inbox_es lexev sub_es
  out_es cle evsn0.
have := initial_common_general_position_invariant gen_pos wf startok nocs'
  inbox_es lexev sub_es out_es uniq_out_es cle evsn0.
case evsq : events evsn0 => [ // | e evs] _.
case oca_eq: (opening_cells_aux _ _ _ _) => [nos lno].
lazy zeta; rewrite [head _ _]/= [behead _]/=.
have oute : out_left_event e by apply: out_es; rewrite evsq inE eqxx.
move=> Cinv [] ok0 []cbtom0 []adj0 []sval0 []rf0 []inbox_es0 []cle1
         []out_es1 []clae0 []vb []vt []oe0 []nocs []noc0 []pw0 lexevs.
have inbox_e : inside_box bottom top (point e).
  by apply/(@allP pt _ _ inbox_es)/map_f; rewrite evsq inE eqxx.
have /andP[eab ebt] : (point e >>> bottom) && (point e <<< top).
  by move: inbox_e=> /andP[].
have cle0 : close_edges_from_events (e :: evs) by rewrite -evsq.
move: inbox_es; rewrite evsq=> inbox_es.
move: Cinv; rewrite/initial_state oca_eq/state_open_seq/state_closed_seq/=.
move=> /[dup] Cinv; rewrite /state_open_seq/state_closed_seq /=.
move=> -[] []; rewrite /state_open_seq/state_closed_seq /=.
move=> inv1 px1 lstheq1 sub1 _ _ _ _ oks1 lexpt1.
have [clae1 [pre_sval [adj1 [cbtom1 rf1]]]] := inv1.
set op0 := start_open_cell bottom top.
have inj_high0 : {in [:: start_open_cell bottom top] &, injective high}.
  by move=> g1 g2; rewrite !inE=> /eqP -> /eqP ->.
have uniq1 : {in evs, forall e, uniq (outgoing e)}.
  by move=> ev evin; apply: uniq_out_es; rewrite evsq inE evin orbT.
have rf0' : s_right_form ([::] ++ [:: op0]) by [].
have  btm_left_lex0 :
  bottom_left_cells_lex [:: start_open_cell bottom top] (point e).
  by apply: bottom_left_start inbox_e startok.
have inj_high1 : {in nos ++ [:: lno] &, injective high}.
  have uniq_e : uniq (outgoing e) by apply: uniq_out_es; rewrite evsq inE eqxx.
  have := step_keeps_injective_high_default inbox_es oute rf0' cbtom0
    adj0 sval0 ok0 uniq_e inj_high0 btm_left_lex0.
  by rewrite oe0 oca_eq.
have n_inner0 : {in [:: start_open_cell bottom top],
           forall c, non_inner (high c) (point e)}.
  move=> c; rewrite inE /non_inner=> /eqP -> /onAbove.
  by move: inbox_e=> /andP[] /andP[] _ ->.
have n_inner1 : {in s & evs, forall g e, non_inner g (point e)}.
  by move=> g ev gin evin; apply: n_inner; rewrite // evsq inE evin orbT.
have cov1 : {in [:: e], forall e',
    {in outgoing e', forall g, (edge_covered g (nos ++ [:: lno])
            [:: close_cell (point e) op0])}}.
  move=> e'; rewrite inE => /eqP -> {e'}.
  have := step_keeps_edge_covering_default inbox_es oute rf0' cbtom0 adj0 sval0
           ok0 inj_high0 btm_left_lex0 n_inner0 oe0 oca_eq=> /=.
  move=> main g gin.
  by apply: (main [::]); right.
have btm_left_lex1 : {in nos ++ [:: lno] & evs,
          forall c e0, lexPt (bottom_left_corner c) (point e0)}.
  move=> c ev cin evin.
  have eev : lexPtEv e ev.
    move: lexev; rewrite evsq /= path_sortedE; last by apply: lexPtEv_trans.
    by move=> /andP [] /allP + _; apply.
  have := step_keeps_btom_left_corners_default inbox_es oute rf0' cbtom0
    adj0 sval0 btm_left_lex0; rewrite oe0 oca_eq=> /(_ _ eev).
  by apply.
rewrite /state_open_seq/state_closed_seq/=.
have cov_p1 : {in [:: e], forall e',
  exists2 c, c \in [:: close_cell (point e) op0] &
  point e' \in (right_pts c : seq pt)/\ point e' >>> low c}.
  move=> e'; rewrite inE => /eqP -> {e'}.
  exists (close_cell (point e) op0); first by rewrite mem_head.
  split.
    by exact: (@close_cell_in _ _ op0 (conj vb vt)).
  by have [-> _ _] := close_cell_preserve_3sides (point e) op0.
by constructor.
Qed.

Lemma simple_step_edge_covered_general_position
  bottom top s all_events cov_set fop lsto lop fc cc lcc lc le he cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  edge_covered_general_position_invariant bottom top s
   all_events cov_set (Bscan fop lsto lop cls lstc lsthe lstx)
   (ev :: evs) ->
  edge_covered_general_position_invariant bottom top s
    all_events (rcons cov_set ev) (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
set st := Bscan _ _ _ _ _ _ _.
move=> oe.
move=> [] covered p_covered /[dup] Cinv [] [] /[dup] inv_s [] clae.
move=> - [] []; first by [].
rewrite /state_open_seq/state_closed_seq /= => sval [] adj [] cbtom rfo.
move=> lstxq lstheq sub_edges events_dec cle out_es uniq_evs.
move=> /[dup] inbox0 /andP[] inbox_e inbox_es no_dup lexev oks.
move=> bottom_left_corner_cond strd.
move=> /andP[] lstxlt pathlt n_inner inj_high btm_left_lex.
have out_e : out_left_event ev by apply: out_es; rewrite inE eqxx.
have noc : {in all_edges (state_open_seq st) (ev :: evs) &, no_crossing R}.
  by move=> g1 g2 g1in g2in; apply: nocs; apply: sub_edges.
(* TODO: this should not be needed, if we had enough theorems about
  simple_step. *)
have lstxneq :  p_x (point ev) != lstx.
  by move: lstxlt; rewrite lt_neqAle eq_sym=> /andP[] /andP[].
case oca_eq :
  (opening_cells_aux (point ev) (sort edge_below (outgoing ev)) le he) =>
      [nos lno].
have Cinv' :=
  simple_step_common_general_position_invariant boxwf nocs' inbox_s oe Cinv.
have btm_left_lex_e : {in (state_open_seq st), forall c,
                         lexPt (bottom_left_corner c) (point ev)}.
  by move=> c cin; apply: btm_left_lex; rewrite // inE eqxx.
have n_inner2 : {in state_open_seq st,
         forall c, non_inner (high c) (point ev)}.
  move=> c cin.
  have /sub_edges : high c \in all_edges (state_open_seq st) (ev :: evs).
    by rewrite 2!mem_cat map_f ?orbT.
  have /inside_box_non_inner [nib nit] : inside_box bottom top (point ev).
    by move: inbox0 => /andP[].
  rewrite !inE => /orP[/eqP -> | /orP [/eqP -> | hcin ]] //.
  by apply: n_inner; rewrite // inE eqxx.
have cov' : {in rcons cov_set ev,forall e',
  {in outgoing e', forall g, edge_covered g (state_open_seq
                              (simple_step fc cc lc lcc le he cls lstc ev))
                  (state_closed_seq
                     (simple_step fc cc lc lcc le he cls lstc ev))}}.
  have main:= step_keeps_edge_covering_default
    inbox0 out_e rfo cbtom adj sval oks inj_high btm_left_lex_e n_inner2
         oe oca_eq.
  have := main (state_closed_seq st) => {}main.
  move=> e' e'in g gin.
  have /main : edge_covered g (fop ++ lsto :: lop) (state_closed_seq st) \/
         g \in outgoing ev.
    move: e'in; rewrite -cats1 mem_cat=> /orP[/covered|]; last first.
      by move: gin=> /[swap]; rewrite inE=> /eqP ->; right.
    by move=> /(_ _ gin); left.
  rewrite /state_open_seq /state_closed_seq /=.
  apply: edge_covered_sub.
    rewrite /simple_step/generic_trajectories.simple_step.
    rewrite -/(opening_cells_aux _ _ _ _).
    by rewrite oca_eq /= -catA.
  rewrite /simple_step/generic_trajectories.simple_step.
  rewrite -/(opening_cells_aux _ _ _ _).
  by rewrite oca_eq /= !cat_rcons -!cats1 -!catA.
have n_inner' : {in s & evs, forall g e, non_inner g (point e)}.
  by move=> g e gin ein; apply: n_inner; rewrite // inE ein orbT.
have uniq' : {in evs, forall e, uniq (outgoing e)}.
  by move=> g gin; apply: uniq_evs; rewrite inE gin orbT.
have uniq_ev : uniq (outgoing ev) by apply: uniq_evs; rewrite inE eqxx.
have inj_high' :
  {in state_open_seq (simple_step fc cc lc lcc le he cls lstc ev) &,
     injective high}.
  have := step_keeps_injective_high_default inbox0 out_e rfo cbtom adj sval
     oks uniq_ev inj_high btm_left_lex_e.
  rewrite /simple_step/generic_trajectories.simple_step.
  rewrite -/(open_cells_decomposition _ _).
  rewrite -/(opening_cells_aux _ _ _ _).
  by rewrite oe oca_eq /state_open_seq /= -catA.
have btm_left_lex' :
  {in state_open_seq (simple_step fc cc lc lcc le he cls lstc ev) & evs,
     forall c e, lexPt (bottom_left_corner c) (point e)}.
  have := step_keeps_btom_left_corners_default inbox0 out_e rfo cbtom adj
     sval btm_left_lex_e.
  rewrite /simple_step/= /= oe oca_eq /= /state_open_seq /=.
  rewrite catA=> main.
  move=> c e cin ein; apply: main=> //=.
  move: lexev; rewrite path_sortedE; last by apply: lexPtEv_trans.
  by move=> /andP[] /allP /(_ e ein).
have p_cov' : {in rcons cov_set ev, forall e, exists2 c,
   c \in state_closed_seq (simple_step fc cc lc lcc le he cls lstc ev) &
   point e \in (right_pts c : seq pt) /\ point e >>> low c}.
  have exi := exists_cell cbtom adj (inside_box_between inbox_e).
  have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  have [{}pal {}puh vle vhe nc]:=
    decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
  move=> e; rewrite mem_rcons inE=> /orP[]; last first.
    move=> /p_covered [] c cin pin.
    rewrite /state_closed_seq/simple_step/generic_trajectories.simple_step.
    rewrite -/(opening_cells_aux _ _ _ _).
    rewrite oca_eq /=.
    exists c; last by [].
    by rewrite -cats1 /= appE -(cat_rcons lstc) !mem_cat cin.
  move=> /eqP -> {e}.
  exists (close_cell (point ev) (head lcc cc)).
    rewrite /state_closed_seq /simple_step/generic_trajectories.simple_step.
    rewrite -/(opening_cells_aux _ _ _ _).
    rewrite oca_eq /= -cats1 -catA /=.
    rewrite -cat_rcons mem_cat; apply/orP; right.
    by case: (cc) => [ | ? ?]; rewrite /= mem_head.
  have hdin : head lcc cc \in fop ++ lsto :: lop.
    rewrite ocd mem_cat; apply/orP; right.
    by case: (cc)=> [ | ? ?]; rewrite /= mem_head.
  split.
    by apply/close_cell_in/andP/(allP sval).
  have [-> _ _] := close_cell_preserve_3sides (point ev) (head lcc cc).
  by rewrite -leq.
by constructor.
Qed.

Lemma start_edge_covered_general_position bottom top s closed open evs :
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) evs ->
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
  {in events_to_edges evs, forall g, edge_covered g open closed} /\
  {in evs, forall e, exists2 c, c \in closed &
      point e \in (right_pts c : seq pt) /\ point e >>> low c}.
Proof.
move=> ltev boxwf startok nocs' inbox_s evin lexev evsub out_evs cle
  n_inner uniq_edges.
(*
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
*)
rewrite /start.
case evsq : evs => [ | ev future_events]; first by split; move=> r_eq ?.
have evsn0 : evs != [::] by rewrite evsq.
have := initial_edge_covering_general_position ltev lexev boxwf cle
  startok nocs' n_inner evin evsub out_evs uniq_edges evsn0.
rewrite /initial_state evsq /=.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
set istate := Bscan _ _ _ _ _ _ _.
move=> istateP req.
suff main : forall events all_events op cl st cov_set,
  edge_covered_general_position_invariant bottom top s all_events cov_set st events ->
  scan events st = (op, cl) ->
  ({in events_to_edges (cov_set ++ events), forall g, edge_covered g op cl} /\
  {in cov_set ++ events, forall e, exists2 c, c \in cl &
    point e \in (right_pts c : seq pt) /\ point e >>> low c}).
  by move: req; apply: (main _ (ev :: future_events) _ _ _ [:: ev]).
move=> {req istateP istate oca_eq lno nos evsn0 evsq future_events ev}.
move=> {uniq_edges n_inner out_evs evsub lexev evin startok ltev}.
move=> {cle closed open evs}.
elim=> [ | ev evs Ih] all_events op cl st cov_set.
  case: st => fop lsto lop cls lstc lsthe lstx /=.
  move=> []; rewrite /state_open_seq/state_closed_seq /= => + p_main.
  move=> main _ _ _ _ [] <- <-; rewrite cats0; split.
    move=> g=> /flatten_mapP[e' /main /[apply]].
    apply: edge_covered_sub; first by [].
    by move=> c; rewrite mem_rcons.
  move=> e=> /p_main [c2 c2in pin2]; exists c2=> //.
  by move: c2in; rewrite mem_rcons.
move=> inv0; rewrite -cat_rcons.
apply: (Ih all_events).
case stq : st => [fop lsto lop cls lstc lsthe lstx].
rewrite /step/generic_trajectories.step.
have /andP[/andP[+ _] _] := general_pos (common_inv_ec inv0).
rewrite lt_neqAle eq_sym => /andP[] lstxneq _.
rewrite stq /= in lstxneq; rewrite lstxneq.
rewrite -/(open_cells_decomposition _ _).
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
move: (inv0); rewrite stq=> inv1.
by have := simple_step_edge_covered_general_position boxwf nocs'
    inbox_s oe inv1.
Qed.

Record safe_side_general_position_invariant (bottom top : edge)
 (edge_set : seq edge) (all_events processed_set : seq event)
 (s : scan_state) (events : seq event) :=
 { disjoint_ss :
     disjoint_general_position_invariant bottom top edge_set s 
     all_events processed_set events;
   covered_ss :
     edge_covered_general_position_invariant bottom top edge_set
       all_events processed_set s events;
    left_proc : {in processed_set & events, forall e1 e2,
                     p_x (point e1) < p_x (point e2)};
    rf_closed : {in state_closed_seq s, forall c, low c <| high c};
    diff_edges :
       {in state_open_seq s ++ state_closed_seq s, forall c, low c != high c};
    sub_closed :
      {subset cell_edges (state_closed_seq s) <= bottom :: top :: edge_set};
   (* TODO : move this to the common invariant. *)
   left_o_lt :
        {in state_open_seq s & events,
          forall c e, left_limit c < p_x (point e)};
   left_o_b :
        {in state_open_seq s, forall c, left_limit c <
              Num.min (p_x (right_pt bottom)) (p_x (right_pt top))};
   closed_lt :
        {in state_closed_seq s, forall c, left_limit c < right_limit c};
   closed_ok :
        all (@closed_cell_side_limit_ok R) (state_closed_seq s);
   (* TODO : move this to the disjoint invariant. *)
   cl_at_left_ss :
     {in state_closed_seq s & events,
        forall c e, right_limit c < p_x (point e)};
   safe_side_closed_edges :
     {in events_to_edges processed_set & state_closed_seq s, forall g c p,
         in_safe_side_left p c || in_safe_side_right p c -> ~ p === g};
   safe_side_open_edges :
     {in events_to_edges processed_set & state_open_seq s, forall g c p,
         in_safe_side_left p c -> ~p === g};
   safe_side_closed_points :
     {in processed_set & state_closed_seq s, forall e c p,
         in_safe_side_left p c || in_safe_side_right p c ->
         p != point e :> pt};
   safe_side_open_points :
     {in processed_set & state_open_seq s, forall e c p,
         in_safe_side_left p c ->
         p != point e :> pt};
}.

Lemma initial_safe_side_general_position bottom top s events:
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events ->
  sorted (@lexPtEv _) events ->
   bottom <| top ->
  close_edges_from_events events ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall g1 g2, inter_at_ext g1 g2} ->
  {in s & events, forall g e, non_inner g (point e)} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  {in events, forall ev, uniq (outgoing ev)} ->
  events != [::] ->
  safe_side_general_position_invariant bottom top s
    events [::(head dummy_event events)]
   (initial_state bottom top events) (behead events).
Proof.
move=> gen_pos lexev wf cle startok nocs' n_inner inbox_es sub_es out_es
  uniq_out_es evsn0.
have := initial_intermediate wf startok nocs' inbox_es lexev sub_es
  out_es cle evsn0.
have := initial_disjoint_general_position_invariant gen_pos wf startok
  nocs' inbox_es lexev sub_es out_es uniq_out_es cle evsn0.
have := initial_edge_covering_general_position gen_pos lexev wf cle
  startok nocs' n_inner inbox_es sub_es out_es uniq_out_es evsn0.
case evsq: events evsn0=> [ | ev evs]; [by [] | move=> evsn0].
rewrite /initial_state.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move=> e_inv d_inv.
move=> []; set op0 := start_open_cell bottom top.
rewrite [head _ _]/= [behead _]/=.
move=> ok0 [] btom0 [] adj0 [] sval0 [] rf0 [] inbox_es0 [] cle0 [] oute0.
move=> [] clae0 [] vb0 [] vt0 [] oe0 [] noc0 [] noc'0 [] pw0 lexevs.
have u0 : uniq (outgoing ev) by apply: uniq_out_es; rewrite evsq mem_head.
have oute : out_left_event ev by apply: out_es; rewrite evsq mem_head.
have inbox_e : inside_box bottom top (point ev).
  by have := inbox_es; rewrite evsq => /andP[].
have /andP [pab put] : (point ev >>> bottom) && (point ev <<< top).
  by move: inbox_e=> /andP[].
have rf_closed1 : {in [:: close_cell (point ev) op0], forall c,
      low c <| high c}.
  rewrite /close_cell (pvertE vb0) (pvertE vt0) /= => c.
  by rewrite inE=> /eqP -> /=.
have dif1 : {in (nos ++ [:: lno]) ++
                 [:: close_cell (point ev) op0], forall c, low c != high c}.
  move=> c; rewrite mem_cat=> /orP[].
    rewrite cats1.
    have := opening_cells_low_diff_high oute u0 vb0 vt0 pab put.
    by rewrite /opening_cells oca_eq; apply.
  rewrite inE /close_cell (pvertE vb0) (pvertE vt0) => /eqP -> /=.
  by apply/negP=> /eqP abs; move: pab; rewrite abs (underW put).
have subc1 : {subset cell_edges [:: close_cell (point ev) op0] <=
    bottom :: top :: s}.
  move=> c; rewrite !mem_cat !inE=> /orP[] /eqP ->.
    have [-> _ _] := close_cell_preserve_3sides (point ev) op0.
    by rewrite eqxx.
  have [_ -> _] := close_cell_preserve_3sides (point ev) op0.
  by rewrite eqxx orbT.
have lte : {in evs, forall e, p_x (point ev) < p_x (point e)}.
  move: gen_pos; rewrite evsq /=.
  rewrite path_sortedE; last by move=> ? ? ?; apply: lt_trans.
  by move=> /andP[] /allP.
have llt: {in nos ++ [:: lno] & evs, forall c e, left_limit c < p_x (point e)}.
  move=> c e cin ein.
  have lte' : p_x (point ev) < p_x (point e) by apply: lte.
  have := opening_cells_left oute vb0 vt0.
  by rewrite /opening_cells oca_eq -cats1=> /(_ _ cin) => ->.
have llop0ltev : left_limit op0 < p_x (point ev).
  rewrite (leftmost_points_max startok).
  have := inbox_e=> /andP[] _ /andP[] /andP[] + _ /andP[] + _.
  by case: (lerP (p_x (left_pt bottom)) (p_x (left_pt top))).
have lltr : {in [:: close_cell (point ev) op0],
  forall c, left_limit c < right_limit c}.
  move=> c; rewrite inE=> /eqP ->.
  rewrite (@right_limit_close_cell _ (point ev) op0 vb0 vt0).
  by rewrite left_limit_close_cell.
have clok: all (@closed_cell_side_limit_ok _) [:: close_cell (point ev) op0].
  rewrite /= andbT.
  by apply: close_cell_ok; rewrite // contains_pointE underWC // underW.
have rllt : {in [:: close_cell (point ev) op0] & evs,
               forall c e, right_limit c < p_x (point e)}.
  move=> c e; rewrite inE => /eqP -> ein.
  by rewrite right_limit_close_cell //; apply: lte.
(* Main points. *)
have safe_cl : {in events_to_edges [:: ev] & [:: close_cell (point ev) op0],
         forall g c p, in_safe_side_left p c || in_safe_side_right p c ->
         ~ p === g}.
  move=> g c gin.
  have lgq : left_pt g = point ev.
    apply/eqP/oute.
    by move: gin; rewrite /events_to_edges /= cats0.
  rewrite inE => /eqP -> p /orP[] pin.
    move=> /andP[] _ /andP[] + _.
    rewrite leNgt=> /negP; apply.
    move: pin=> /andP[] /eqP -> _.
    by rewrite left_limit_close_cell lgq.
  move=> pong.
  move: pin=> /andP[] + /andP[] _ /andP[] _ .
  rewrite right_limit_close_cell // => /eqP samex.
  move/negP;apply.
  suff -> : p = point ev by rewrite close_cell_in.
  apply/eqP; rewrite pt_eqE samex eqxx/=; apply/eqP.
  apply: (on_edge_same_point pong) => //.
  by rewrite -lgq left_on_edge.
have safe_op : {in events_to_edges [:: ev] & nos ++ [:: lno],
          forall g c p, in_safe_side_left p c -> ~ p === g}.
  move=> g c gin cin p pin pong.
  move: cin; rewrite cats1=> cin.
  have lgq : left_pt g = point ev.
    apply/eqP/oute.
    by move: gin; rewrite /events_to_edges /= cats0.
  have eong : point ev === g by rewrite -lgq left_on_edge.
  move: pin=> /andP[] + /andP[] _ /andP[] _.
  have := opening_cells_left oute vb0 vt0.
  have := opening_cells_in vb0 vt0 oute.
  rewrite /opening_cells oca_eq=> /(_ _ cin) evin /(_ _ cin) -> /eqP samex.
  move/negP; apply.
  suff -> : p = point ev.
    by apply: (opening_cells_in vb0 vt0 oute); rewrite /opening_cells oca_eq.
  apply/eqP; rewrite pt_eqE samex eqxx/=; apply/eqP.
  apply: (on_edge_same_point pong eong samex) => //.
have cl_no_event : {in [:: ev] & [:: close_cell (point ev) op0],
  forall e c (p : pt), in_safe_side_left p c || in_safe_side_right p c ->
       p != point e}.
  move=> e c; rewrite !inE => /eqP -> /eqP -> p /orP[].
    move=> /andP[] xlop0 _.
    apply/eqP=> pev.
    move: llop0ltev; rewrite -pev (eqP xlop0).
    by rewrite left_limit_close_cell lt_irreflexive.
  move=> /andP[] _ /andP[] _ /andP[] _ /negP it; apply/eqP=> pev.
  case: it; rewrite pev.
  by apply: close_cell_in.
have op_no_event : {in [:: ev] & nos ++ [:: lno],
         forall e c (p : pt), in_safe_side_left p c -> p != point e}.
  move=> e c; rewrite !inE=> /eqP ->; rewrite cats1=> cin p pin.
  apply/negP=> /eqP pev.
  move: pin=> /andP[] _ /andP[] _ /andP[] _ /negP[] .
  have := opening_cells_in vb0 vt0 oute; rewrite /opening_cells oca_eq pev.
  by apply.
have lt_p_ev :
  {in [:: ev] & evs, forall e1 e2 : event, p_x (point e1) < p_x (point e2)}.
  by move=> e1 e2; rewrite inE => /eqP ->; apply: lte.
have ll_o_b :
  {in nos ++ [:: lno], forall c,
       left_limit c < Num.min (p_x (right_pt bottom)) (p_x (right_pt top))}.
  move=> c cin.
  have := opening_cells_left oute vb0 vt0; rewrite /opening_cells oca_eq.
  rewrite -cats1 => /(_ _ cin) ->.
  by apply: inside_box_lt_min_right.
rewrite [take 1 _](_ : _ = [:: ev]) in d_inv; last first.
  by case: (evs).
by constructor.
Qed.

Lemma start_safe_sides bottom top s closed open evs :
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) evs ->
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
      left_limit (head_cell open) < Num.min (p_x (right_pt bottom))
      (p_x (right_pt top))).
Proof.
move=> ltev boxwf startok nocs' inbox_s evin lexev evsub out_evs cle
  n_inner uniq_edges.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /main_process/scan/=.
case evsq : evs => [ | ev future_events]; first by  move=> [] <- <-.
have evsn0 : evs != [::] by rewrite evsq.
case oca_eq : opening_cells_aux => [nos lno].
set istate := Bscan _ _ _ _ _ _ _.
have : safe_side_general_position_invariant bottom top s evs [:: ev]
  istate future_events.
  have := initial_safe_side_general_position ltev lexev boxwf cle startok
    nocs' n_inner evin evsub out_evs uniq_edges evsn0.
  by rewrite evsq /= oca_eq.
move=> invss req.
suff main: forall events op cl st all_events processed_set,
  safe_side_general_position_invariant bottom top s all_events
    processed_set st events ->
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
  all (@closed_cell_side_limit_ok _) cl /\
  size op = 1%N /\
  low (head_cell op) = bottom /\
  high (head_cell op) = top /\
  {in op & cl, disjoint_open_closed_cells R} /\
  (left_limit (head_cell op) < Num.min (p_x (right_pt bottom))
      (p_x (right_pt top))).
  have [A [B [C [D [E [F [G [H I]]]]]]]] := main _ _ _ _ _ _ invss req.
  split; last by [].
  move=> c cin; move: (A c cin) => [] crf [] difc [] lltr [] clok A'.
  do 4 (split; first by []).
  by move=> p pside; have := A' _ pside.
elim=> [ | {evsq oca_eq istate invss}ev {req}future_events Ih] op cl st all_events p_set.
  case stq : st => [fop lsto lop cls lstc lsthe lstx] [].
  move=> d_inv e_inv.
  set c_inv := common_inv_dis d_inv.
  rewrite /state_open_seq/state_closed_seq/= => old_lt_fut b_e d_e subc
     lolt lo_lb rllt clok rl A B C D.
  rewrite /= => -[] <- <-; rewrite !cats0.
  split.
    move=> c cin.
    split; first by apply: b_e; rewrite mem_rcons.
    split; first by apply: d_e; rewrite mem_cat mem_rcons cin orbT.
    split; first by apply: rllt; rewrite mem_rcons.
    split; first by apply: (allP clok); rewrite mem_rcons.
    move=> p pin; split.
      by move=> g gin; apply: (A g c gin); rewrite // mem_rcons.
    by move=> e ein; apply: (C e c ein); rewrite // mem_rcons.
  split; last first.
    split; last first.
      split.
        rewrite (eq_all_r (_ : lstc :: cls =i rcons cls lstc)) //.
        by move=> c; rewrite mem_rcons.
      (* TODO : find a place for this as a lemma. *)
      have [[] [] + + _ _ _ _ _ _ _ + _] := c_inv; rewrite /state_open_seq/=.
      rewrite /state_open_seq/= /close_alive_edges => clae.
      move=> [] _ [] adj [] cbtom rfo _.
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
        have := order_edges_strict_viz_point vt vb abs put.
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
        move=> c1 c2 c1in c2in; apply: (op_cl_dis d_inv);
        by rewrite /state_open_seq/state_closed_seq  f0 l0 ?mem_rcons.
      by apply: lo_lb; rewrite mem_cat inE eqxx orbT.
(* End of lemma *)
    move=> g; rewrite -[lstc :: cls]/([:: lstc] ++ cls) cell_edges_catC cats1.
    by apply: subc.
  move=> c cin p pin.
  split.
    by move=> g gin; apply: (B g c gin).
  by move=> g gin; apply: (D g c gin).
rewrite /scan/=.
move=> [] d_inv e_inv old_lt_fut rf_cl d_e subc lolt lo_lb rllt clok rl A B C D.
set c_inv := common_inv_dis d_inv.
rewrite /step/generic_trajectories.step/=.
case stq : st => [fop lsto lop cls lstc lsthe lstx].
have /andP[/andP[+ _] _] := general_pos c_inv.
rewrite lt_neqAle=> /andP[] + _.
rewrite stq eq_sym /= => ->.
rewrite -/(open_cells_decomposition _ _).
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
rewrite /simple_step/generic_trajectories.simple_step/=.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [{}nos {}lno].
rewrite -(cat_rcons ev).
apply: (Ih _ _ _ all_events).
have [clae [pre_sval [adj [cbtom rfo]]]] := inv1 (gcomm c_inv).
move: pre_sval=> [| sval]; first by[].
have inbox_es := inbox_events (gcomm c_inv).
have inbox_e : inside_box bottom top (point ev) by move: inbox_es=>/andP[].
move: (oe); rewrite (_ : fop ++ lsto :: lop = state_open_seq st); last first.
  by rewrite stq.
move=> oe'.
have exi' := exists_cell cbtom adj (inside_box_between inbox_e).
move: (exi'); rewrite stq => exi.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi'.
have [{}pal {}puh vl vp nc]:=
  decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe'.
have oute : out_left_event ev.
  by apply: (out_events (gcomm c_inv)); rewrite inE eqxx.
have oute' :
  {in (sort edge_below (outgoing ev)), forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
set rstate := Bscan (fc ++ nos) _ _ _ _ _ _.
have d_inv':
  disjoint_general_position_invariant bottom top s rstate all_events
    (rcons p_set ev) future_events.
  move: (d_inv); rewrite stq=> d_inv'.
  have := simple_step_disjoint_general_position_invariant boxwf nocs'
      inbox_s oe d_inv'.
  rewrite /simple_step/generic_trajectories.simple_step/=.
  by rewrite -/(opening_cells_aux _ _ _ _) oca_eq.
have e_inv' :edge_covered_general_position_invariant bottom top s
    all_events (rcons p_set ev) rstate future_events.
  move: e_inv; rewrite stq=> e_inv.
  have := simple_step_edge_covered_general_position boxwf nocs'
      inbox_s oe e_inv.
  rewrite /simple_step/generic_trajectories.simple_step/=.
  by rewrite -/(opening_cells_aux _ _ _ _) oca_eq.
(* Proving that low and high edges of every cell are distinct. *)
have low_diff_high' :
  {in state_open_seq rstate ++
      state_closed_seq rstate, forall c : cell, low c != high c}.
  move=> c; rewrite mem_cat=> /orP[].
    rewrite /state_open_seq /= -catA -cat_rcons !mem_cat orbCA.
    move=> /orP[ | cold]; last first.
      by apply: d_e; rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
    have uo : uniq (outgoing ev).
     by apply: (uniq_ec (gcomm c_inv)) (mem_head _ _).
    have := opening_cells_low_diff_high oute uo vl vp pal puh.
    by rewrite /opening_cells oca_eq; apply.
  rewrite /state_closed_seq /= -cats1 -!catA /= -cat_rcons.
  rewrite mem_cat => /orP[cold | ].
    by apply: d_e; rewrite mem_cat stq /state_closed_seq/= cold orbT.
  rewrite cats1 -map_rcons=> /mapP[c' c'in ->].
  have [-> -> _] := close_cell_preserve_3sides (point ev) c'.
  by apply: d_e; rewrite mem_cat ocd -cat_rcons !mem_cat c'in !orbT.
(* Provint that closed cells used edges only from the initial set. *)
have subc' :
  {subset cell_edges (state_closed_seq rstate) <= [:: bottom, top & s]}.
  move=> g; rewrite /state_closed_seq/= -cats1 -catA /= -cat_rcons.
  rewrite cell_edges_cat mem_cat=> /orP[gold | ].
    by apply: subc; rewrite stq.
  have subo := edges_sub (gcomm c_inv).
  rewrite cats1 -map_rcons mem_cat=> /orP[] /mapP[c'] /mapP[c2 c2in ->] ->.
    have [-> _ _] := close_cell_preserve_3sides (point ev) c2.
    apply: subo; rewrite !mem_cat; apply/orP; left; apply/orP; left.
    by rewrite map_f // ocd -cat_rcons !mem_cat c2in orbT.
  have [_ -> _] := close_cell_preserve_3sides (point ev) c2.
  apply: subo; rewrite !mem_cat; apply/orP; left; apply/orP; right.
  by rewrite map_f // ocd -cat_rcons !mem_cat c2in orbT.
(* Proving that open cells have a left side that is smaller than any
   event first coordinate. *)
have loplte : {in state_open_seq rstate & future_events,
    forall (c : cell) (e : event), left_limit c < p_x (point e)}.
  move=> c e; rewrite /state_open_seq/= -catA -cat_rcons => cin ein.
  move: cin; rewrite !mem_cat orbCA => /orP[ | cold ]; last first.
    apply: lolt; first by rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
    by rewrite inE ein orbT.
  have := opening_cells_left oute vl vp; rewrite /opening_cells oca_eq=> main.
  move=> /main=> ->.
  move: (proj2 (andP (general_pos c_inv))).
  rewrite /= path_sortedE; last by move=> x y z; apply: lt_trans.
  by move=> /andP[] /allP /(_ _ ein).
(* Proving that cells have distinct left and right sides. *)
have lltr :
 {in state_closed_seq rstate, forall c : cell, left_limit c < right_limit c}.
  rewrite /state_closed_seq/= -cats1 -catA /= -cat_rcons.
  move=> c; rewrite mem_cat=> /orP[cold | ].
    by apply: rllt; rewrite stq.
  rewrite cats1 -map_rcons=> /mapP [c' c'in ->].
  have [vlc' vhc'] : valid_edge (low c') (point ev) /\
                         valid_edge (high c')(point ev).
     apply/andP; have := allP sval; rewrite ocd -cat_rcons=> /(_ c'); apply.
     by rewrite !mem_cat c'in orbT.
  have := right_limit_close_cell vlc' vhc'=> ->.
  rewrite left_limit_close_cell lolt //; last by rewrite inE eqxx.
  by rewrite ocd -cat_rcons !mem_cat c'in orbT.
(* proving a closed_cell ok invariant. *)
have clok' : all (@closed_cell_side_limit_ok _) (state_closed_seq rstate).
  apply/allP; rewrite /state_closed_seq/= -cats1 -catA /= -cat_rcons.
    move=> c; rewrite mem_cat=> /orP[cin | cin].
    by apply: (allP clok); rewrite stq.
  move: cin; rewrite /closing_cells cats1 -map_rcons=> /mapP[c' c'in ->].
  have ccont : contains_point (point ev) c'.
    by move: c'in; rewrite mem_rcons inE => /orP[/eqP -> | /allct].
  have c'in' : c' \in state_open_seq st.
    by rewrite ocd -cat_rcons !mem_cat c'in orbT.
  have /(allP sval) /= /andP[vlc' vhc'] := c'in'.
  have c'ok : open_cell_side_limit_ok c'.
    by apply: (allP (sides_ok (gcomm c_inv))).
  by apply close_cell_ok.
(* proving a right_limit stronger invariant. *)
have rllte :   {in state_closed_seq rstate & future_events,
    forall (c : cell) (e : event), right_limit c < p_x (point e)}.
  rewrite /state_closed_seq/=.
  move=> c e cin ein.
  move: cin; rewrite -cats1 -catA /= -cat_rcons mem_cat=> /orP[cold | cnew].
    by apply: rl; rewrite ?stq // inE ein orbT.
  have in_es := inbox_events (gcomm c_inv).
  have := closing_cells_to_the_left in_es rfo cbtom adj sval.
  rewrite stq=> /(_ _ _ _ _ _ _ oe)=> -[] main1 main2.
  have eve : p_x (point ev) < p_x (point e).
    have:= general_pos c_inv=> /andP[] _ /=.
    rewrite path_sortedE; last by move=> x y z; apply: lt_trans.
    by move=> /andP[] /allP /(_ e ein).
  apply: le_lt_trans eve.
  move: cnew; rewrite mem_cat=> /orP[cin | ]; last first.
    by rewrite inE=> /eqP ->.
  by apply: (main1 _ cin).

have safe_side_bound : {in rcons cls lstc, forall c p,
       in_safe_side_left p c || in_safe_side_right p c ->
       p_x p <= right_limit c}.
  move=> c p cin /orP[] /andP[] /eqP -> _; last by rewrite le_refl.
  by apply/ltW/rllt; rewrite /state_closed_seq stq.
have not_safe_event : {in rcons (closing_cells (point ev) cc)
                                 (close_cell (point ev) lcc), forall c,
   ~~ (in_safe_side_left  (point ev) c || in_safe_side_right (point ev) c)}.
  move=> c cin; apply/negP.
  move: cin; rewrite -map_rcons=> /mapP[c' c'in cq].
  have c'in' : c' \in state_open_seq st.
    by rewrite ocd -cat_rcons !mem_cat c'in orbT.
  move=> /orP[ /andP[] + _ | /andP[] _ /andP[] _ /andP[] _ ].
    rewrite cq left_limit_close_cell=> /eqP abs.
    have := lolt c' _ c'in' (mem_head _ _).
    by rewrite  abs lt_irreflexive.
  by rewrite cq close_cell_in //; apply/andP/(allP sval).
have in_safe_side_left_close_cell :
  {in rcons cc lcc, forall c p, in_safe_side_left p (close_cell (point ev) c) =
        in_safe_side_left p c}.
  move=> c cin p; rewrite /in_safe_side_left.
  have [-> -> ->] := close_cell_preserve_3sides (point ev) c.
  by rewrite left_limit_close_cell.
(* Now comes the real important property. *)
have cl_safe_edge :
  {in events_to_edges (rcons p_set ev) & state_closed_seq rstate,
    forall (g : edge) (c : cell) (p : pt),
    in_safe_side_left p c || in_safe_side_right p c -> ~ p === g}.
  rewrite events_to_edges_rcons /state_closed_seq/=.
  move=> g c gin cin p pin.
  move: cin; rewrite -cats1 -catA /= -cat_rcons mem_cat=> /orP[cold | cnew].
    move: gin; rewrite mem_cat=> /orP[gold | gnew].
      (* the edge and the cell are old *)
      by apply: (A g c); rewrite // stq /state_closed_seq/=.
  (* the edge is new, the cell is old, I need to prove the events would
     need to be vertically aligned here. *)
    have cin' : c \in state_closed_seq st by rewrite stq.
    have abs := rl _ _ cin' (mem_head _ _).
    move=> /andP[] _ /andP[] + _.
    have := out_events (gcomm c_inv) (mem_head _ _) gnew=> /eqP ->.
  (* TODO : have the same condition, but for the right side of closed cells. *)
    suff prl : p_x p <= right_limit c.
      rewrite leNgt=> /negP; apply.
      by apply: le_lt_trans abs.
    have cold' : c \in state_closed_seq st by rewrite stq.
    move: pin => /orP[]; last first.
      by rewrite /in_safe_side_right => /andP[] /eqP -> _.
    rewrite /in_safe_side_left=> /andP[] /eqP -> _.
    by apply/ltW/rllt.
  (* now the cells are newly closed. *)
  move: cnew pin; rewrite cats1 /closing_cells -map_rcons.
  move=> /mapP[c' c'in ->].
  have c'in' : c' \in state_open_seq st.
    by rewrite ocd -cat_rcons !mem_cat c'in orbT.
  move=> /orP[pin | pin].
    have pin': in_safe_side_left p c'.
      by move: pin; rewrite in_safe_side_left_close_cell.
    move: pin=> /andP[]; rewrite left_limit_close_cell => pl _.
    move: gin; rewrite mem_cat=> /orP[gin | ].
      by apply: B pin'.
    move=> /oute /eqP lgq /andP[] _ /andP[]; rewrite lgq leNgt=> /negP[].
    by rewrite (eqP pl); apply: lolt; rewrite // inE eqxx.
  have vc' : valid_cell c' (point ev) by apply/andP/(allP sval).
  have /eqP samex : p_x p == p_x (point ev).
    by move: pin=> /andP[] + _; rewrite close_cell_right_limit.
  move: gin; rewrite mem_cat=> /orP[gin | /oute/eqP lgq ]; last first.
    have peg : point ev === g by rewrite -lgq left_on_edge.
    move=> pong.
    have /eqP samey := on_edge_same_point pong peg samex.
    have pev : p = point ev by apply/eqP; rewrite pt_eqE samex samey eqxx.
    have := not_safe_event (close_cell (point ev) c').
    rewrite -[e in in_safe_side_right e _]pev pin orbT.
    by rewrite /closing_cells -map_rcons map_f // => /(_ isT).
  move: gin=> /flatten_mapP[e' e'in gin].
  have := edge_covered_ec e_inv e'in gin=> -[]; last first.
    move=> [[ | pcc0 pcc] []]; first by [].
    move=> _ /= [pccsub [pcchigh [_ [_ rlpcc]]]] /andP[] _ /andP[] _.
    rewrite leNgt=> /negP; apply.
    rewrite samex -rlpcc; apply:rl; last by rewrite inE eqxx.
    by apply/pccsub; rewrite /last_cell /= mem_last.
  move=> [] opc [] pcc [] _ [] opch [] _ [] opco _ abs.
  have [vlc'p vhc'p] : valid_edge (low c') p /\ valid_edge (high c') p.
    by move: vc'; rewrite /valid_cell !(same_x_valid _ samex).
  have pinc' : contains_point' p c'.
    rewrite /contains_point'.
    have [<- <- _] := close_cell_preserve_3sides (point ev) c'.
    by have /andP[_ /andP[] /underW -> /andP[] ->] := pin.
  have {}opch : high opc = g by apply: opch; rewrite mem_rcons inE eqxx.
  have [vplc vphc] : valid_edge (low opc) p /\ valid_edge (high opc) p.
    by rewrite !(same_x_valid _ samex); apply/andP/(allP sval).
  have rfc : low opc <| high opc by apply: (allP rfo).
  have cnt : contains_point p opc.
    rewrite contains_pointE; apply/andP; rewrite under_onVstrict; last first.
      by have := (allP sval _ opco) => /andP[].
    rewrite opch abs; split; last by [].
    apply/negP=> pun.
    have := order_edges_strict_viz_point vplc vphc rfc pun.
    by apply/negP/onAbove; rewrite opch.
  have pw : pairwise edge_below [seq high c | c <- state_open_seq st].
    by move: (pairwise_open d_inv)=> /= /andP[].
  have [puhc' palc'] : p <<< high c' /\ p >>> low c'.
    apply/andP;  move: pin=> /andP[] _ /andP[] + /andP[] + _.
    by have [-> -> _] := close_cell_preserve_3sides (point ev) c' => ->.
  have : p >>= low opc by move: cnt=> /andP[].
  rewrite strict_nonAunder // negb_and negbK=> /orP[ | stricter]; last first.
    have := disoc adj pw (sides_ok (gcomm c_inv)).
    move=> /(_ opc c' opco c'in') [ab' | ].
      by move: puhc'; rewrite strict_nonAunder // -ab' opch abs.
    move=> /(_ p) + ; move=>/negP.
    rewrite inside_open'E stricter valid_open_limit //.
    move: cnt; rewrite contains_pointE=> /andP[] _ ->.
    rewrite samex lolt //=; last by rewrite inE eqxx.
    rewrite inside_open'E (underW puhc') palc' valid_open_limit //.
    by rewrite samex lolt // inE eqxx.
  move=> ponl.
  have vbp : valid_edge bottom p.
    by rewrite (same_x_valid _ samex) (inside_box_valid_bottom inbox_e).
  have vtp : valid_edge top p.
    rewrite (same_x_valid _ samex) /valid_edge/generic_trajectories.valid_edge.
    by move: inbox_e=> /andP[] _ /andP[] _ /andP[] /ltW -> /ltW ->.
  have bottom_b_c' : bottom <| low c'.
    have [-> | ] := eqVneq bottom (low c'); first by apply: edge_below_refl.
    have  [s1 [s2]] := mem_seq_split c'in'.
    elim/last_ind: s1 => [ | s1 op' _] /= => odec.
      by move: cbtom => /andP[]; rewrite odec /= => /eqP ->; rewrite eqxx.
    have := adj.
    rewrite odec cat_rcons=> /adjacent_catW /= [] _ /andP[] /eqP <- _ _.
    have := pairwise_open d_inv=> /= /andP[] /allP /(_ (high op')) + _.
    apply; apply/mapP; exists op'=> //.
    by rewrite // odec !mem_cat mem_rcons inE eqxx.
  have pab : p >>> bottom.
    apply/negP=> pub.
    have:= order_edges_viz_point vbp vlc'p bottom_b_c' pub.
    by move: palc'=> /[swap] => ->.
  have ldifh : low opc != high opc by apply: d_e; rewrite mem_cat opco.
  have low_opc_s : low opc \in [:: bottom, top & s].
    by apply: (edges_sub (gcomm c_inv)); rewrite !mem_cat map_f.
  have high_opc_s : high opc \in [:: bottom, top & s].
    by apply: (edges_sub (gcomm c_inv)); rewrite !mem_cat map_f ?orbT.
  have := nocs' (low opc) (high opc) low_opc_s high_opc_s.
  move=> [Q | ]; first by rewrite Q eqxx in ldifh.
  have ponh : p === high opc by rewrite opch.
  have opcok : open_cell_side_limit_ok opc.
    by apply: (allP (sides_ok (gcomm c_inv))).
  move=> /(_ _ ponl ponh); rewrite !inE=> /orP[/eqP pleft | /eqP].
    have : left_limit opc < p_x p.
      by rewrite samex; apply: lolt; rewrite // inE eqxx.
    have := left_limit_max opcok.
    have [_ | ] := lerP (p_x (left_pt (high opc)))(p_x (left_pt (low opc))).
      by move=> /le_lt_trans /[apply]; rewrite pleft lt_irreflexive.
    move=> /lt_le_trans /[apply]=> /lt_trans /[apply].
    by rewrite pleft lt_irreflexive.
(* Here p is vertically aligned with p_x, but it must be an event,
   because it is the end of an edge. *)
  move=> prl.
  have put : p <<< top.
    apply: (order_edges_strict_viz_point vhc'p vtp _ puhc').
    move: cbtom=> /andP[] _.
    have := pw.
    have [s1 [s2 s1q]] := mem_seq_split c'in'.
    rewrite s1q last_cat /= map_cat pairwise_cat /=.
    move=> /andP[] _ /andP[] _ /andP[] allabovec' _ /eqP highlast.
    case s2q : s2 => [ | c2 s3].
      by rewrite -highlast s2q edge_below_refl.
    have /(allP allabovec') : (high (last c' s2)) \in [seq high c | c <- s2].
      by rewrite map_f // s2q /= mem_last.
    by rewrite highlast.
  have := (allP clae _ opco)=> /andP[] + _ => /orP[].
    rewrite !inE => /orP[] /eqP=> ab'.
      by move: pab; rewrite under_onVstrict // -ab' ponl.
    by move: put; rewrite strict_nonAunder // -ab' ponl.
  move=> /hasP[e2 + /eqP pe2]; rewrite inE=> /orP[/eqP e2ev | e2in].
  (* if e' cannot be ev, because p cannot be ev because of pin *)
    have := pin=> /andP[].
    by rewrite prl pe2 e2ev close_cell_in // ?andbF.
(* if e' is in future_events, then e' and p cannot have the same p_x,
  because e' and ev don't, but p and e' are at the same point *)
    have /andP[_ /=]:= general_pos c_inv.
  rewrite path_sortedE; last by move=> ? ? ?; apply: lt_trans.
  move=> /andP[] /allP /(_ e2 e2in).
  by rewrite -pe2 -prl samex ltxx.
have op_safe_edge :
  {in events_to_edges (rcons p_set ev) & state_open_seq rstate,
    forall g c p, in_safe_side_left p c -> ~ p === g}.
(* We should re-use the proof that was just done. *)
  move=> g c gin; rewrite /rstate/state_open_seq/=.
  rewrite -catA -cat_rcons !mem_cat orbCA=> /orP[cnew | cold]; last first.
    have cin : c \in state_open_seq st.
      by rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
    move: gin; rewrite events_to_edges_rcons mem_cat=> /orP[gold | gnew].
      by apply: (B _ _ gold cin).
    move=> p pin /andP[] _ /andP[] pong _.
    have := lolt _ _ cin (mem_head _ _).
    move: (pin)=> /andP[] /eqP <- _.
    rewrite ltNge=> /negP; apply.
    by move: pong; rewrite (eqP (oute _ gnew)).
  move=> p pin.
  have : has (in_safe_side_left p)
           (opening_cells (point ev) (outgoing ev) le he).
    by apply/hasP; exists c; rewrite // /opening_cells oca_eq.
  have := sides_equiv inbox_es oute rfo cbtom adj sval; rewrite stq /=.
  move=> /(_ _ _ _ _ _ _ oe p) /eqP <- => /hasP[] c' c'in pin'.
  have := cl_safe_edge _ c' gin; apply.
    by rewrite /rstate /state_closed_seq/= rcons_cat /= mem_cat inE c'in ?orbT.
  by rewrite pin' orbT.
have cl_safe_event :
  {in rcons p_set ev & state_closed_seq rstate, forall e c (p : pt),
     in_safe_side_left p c || in_safe_side_right p c -> p != point e}.
  move=> e c; rewrite mem_rcons inE=> /orP[/eqP -> | ein].
    move=> cin p pin; apply/negP=> /eqP pev.
    move: cin.
    rewrite /rstate/state_closed_seq/= -cats1 -catA /= -cat_rcons mem_cat.
    move=> /orP[]; last by rewrite cats1=> /not_safe_event; rewrite -pev pin.
    move=> cin; have cin' : c \in state_closed_seq st by rewrite stq.
    move: (cin)=> /safe_side_bound/(_ _ pin); rewrite pev leNgt=> /negP; apply.
    by apply: (rl _ _ cin' (mem_head _ _)).
  rewrite /rstate/state_closed_seq/= -cats1 -catA /= -cat_rcons mem_cat.
  move=> /orP[cin | ].
    have cin' : c \in state_closed_seq st by rewrite stq.
    by apply: (C _ _ ein cin').
  rewrite cats1 -map_rcons=> /mapP[c' c'in /[dup] cq ->].
  have c'in' : c' \in state_open_seq st.
    by rewrite ocd -cat_rcons !mem_cat c'in orbT.
  move=> p /orP[] pin.
    apply: (D e c' ein c'in').
    by move: pin; rewrite in_safe_side_left_close_cell.
  have /andP[vlc' vhc'] : valid_edge (low c') (point ev) &&
                                   valid_edge (high c') (point ev).
    by apply: (allP sval).
  move: (pin) => /andP[] + _.
  rewrite right_limit_close_cell // => /eqP pxq.
  apply/eqP=> abs.
  have := old_lt_fut _ _ ein (mem_head _ _).
  by rewrite -abs pxq lt_irreflexive.
have op_safe_event :
{in rcons p_set ev & state_open_seq rstate,
    forall (e : event) (c : cell) (p : pt),
    in_safe_side_left p c -> p != point e}.
  move=> e c ein; rewrite /rstate/state_open_seq/=.
  rewrite -catA -cat_rcons !mem_cat orbCA=> /orP[cnew | cold]; last first.
    have cin : c \in state_open_seq st.
      by rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
    move: ein; rewrite mem_rcons inE=> /orP[/eqP -> | eold]; last first.
      by apply: (D _ _ eold cin).
    (* use lolt *)
    have := lolt _ _ cin (mem_head _ _)=> llt p /andP[] /eqP pll _.
    apply/eqP=> pev.
    by move: llt; rewrite -pll pev lt_irreflexive.
  move=> p pin.
  have : has (in_safe_side_left p)
           (opening_cells (point ev) (outgoing ev) le he).
    by apply/hasP; exists c; rewrite // /opening_cells oca_eq.
  have := sides_equiv inbox_es oute rfo cbtom adj sval; rewrite stq /=.
  move=> /(_ _ _ _ _ _ _ oe p) /eqP <- => /hasP[] c' c'in pin'.
  have := cl_safe_event _ c' ein; apply.
    by rewrite /rstate /state_closed_seq/= rcons_cat /= mem_cat inE c'in ?orbT.
  by rewrite pin' orbT.
have old_lt_fut' :
  {in rcons p_set ev & future_events,
     forall e1 e2, p_x (point e1) < p_x (point e2)}.
  move=> e1 e2; rewrite mem_rcons inE=>/orP[/eqP -> | e1old] e2fut; last first.
    by apply: old_lt_fut; rewrite // inE e2fut orbT.
  have := general_pos c_inv=> /andP[] _ /=.
  rewrite path_sortedE; last by move=> ? ? ?; apply: lt_trans.
  by move=> /andP[] /allP + _; apply.
have rf_closed1 : {in state_closed_seq rstate, forall c, low c <| high c}.
  move=> c; rewrite /rstate/state_closed_seq/=.
  rewrite appE -cat_rcons -cats1 -catA.
  rewrite mem_cat=> /orP[cin | ].
    by apply: rf_cl; rewrite /state_closed_seq stq/=.
  rewrite cats1 -map_rcons=> /mapP[c' c'in ->].
  have [-> -> _] := close_cell_preserve_3sides (point ev) c'.
  have := inv1 (gcomm c_inv).
  move=> [] _ [] _ [] _ [] _ /allP; apply.
  by rewrite ocd -cat_rcons !mem_cat c'in orbT.
have lo_lb' : {in state_open_seq rstate, forall c,
               left_limit c < Num.min (p_x (right_pt bottom)) (p_x (right_pt top))}.
  move=>c; rewrite /state_open_seq/= -catA -cat_rcons !mem_cat orbCA.
  move=> /orP[cnew | cold]; last first.
    by apply: lo_lb; rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
  have := opening_cells_left oute vl vp ; rewrite /opening_cells oca_eq.
  move=> /(_ _ cnew) ->.
  by apply: inside_box_lt_min_right.
by constructor.
Qed.

End working_environment.
