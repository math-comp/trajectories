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
Notation pt := (pt (Num.RealField.sort R)).
Notation p_x := (p_x (Num.RealField.sort R)).
Notation p_y := (p_y (Num.RealField.sort R)).
Notation Bpt := (Bpt (Num.RealField.sort R)).
Notation edge := (edge R).
Notation left_pt := (@left_pt R).
Notation right_pt := (@right_pt R).
Notation left_limit := (left_limit (Num.RealField.sort R) 1 edge).
Notation right_limit := (right_limit (Num.RealField.sort R) 1 edge).
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
  (cell_center (Num.RealField.sort R) +%R (fun x y => x / y) 1 edge).

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

(* TODO: understand why it did not cause any problem until now. *)
Lemma pvert_y_eq p g :
  pvert_y p g = generic_trajectories.pvert_y R
    <=%R +%R (fun x y : R => x - y) *%R (fun x y => x / y) 1 edge
    left_pt right_pt p g.
Proof.
by rewrite /pvert_y /generic_trajectories.pvert_y subrr.
Qed.

Definition last_case fop lsto fc' cc lcc lc cls lstc he ev :=
  let (nos, lno) := update_open_cell_top lsto he ev in
  Bscan (fop ++ fc' ++ nos) lno lc
    (closing_cells (point ev) (behead cc) ++ lstc ::cls)
    (close_cell (point ev) lcc) he (p_x (point ev)).

Lemma last_case_above_low lsto ev :
  valid_edge (low lsto) (point ev) ->
  open_cell_side_limit_ok lsto ->
  p_x (point ev) = left_limit lsto ->
  (1 < size (left_pts lsto))%N ->
  lexPt (nth dummy_pt (left_pts lsto) 1) (point ev) ->
  point ev >>> low lsto.
Proof.
move=> vlo lstok at_ll has1 lex1.
rewrite (under_pvert_y vlo) -ltNge.
move: has1 lstok lex1; rewrite /open_cell_side_limit_ok.
case: left_pts => [ | a [ | b tl]] //= _ /andP[] /andP[] _ /andP[] x1 AA.
move=> /andP[] /andP[] _ srt /andP[] _ lon.
rewrite /lexPt (eqP x1) at_ll ltxx eqxx /=; apply:le_lt_trans.
have x1' : p_x b = p_x (point ev) by rewrite (eqP x1) at_ll.
case tq : tl srt lon => [ | c tl'].
  move=> /= _ /on_pvert.
  by rewrite -(same_pvert_y vlo (esym x1')) le_eqVlt => /eqP ->.
rewrite (path_sortedE (rev_trans lt_trans)) => /andP[] /allP + _.
have lstin : (last b (c :: tl')) \in (c :: tl') by rewrite /= mem_last.
move=> /(_ _ (map_f _ lstin)) lstlt.
have xl : p_x (last b (c :: tl')) = p_x (point ev).
  rewrite at_ll.
  by apply/eqP/(allP AA); rewrite tq /= mem_last.
move=> /on_pvert; rewrite -(same_pvert_y vlo (esym xl))=> ->.
by apply/ltW.
Qed.

Lemma update_open_cell_top_properties lsto he ev nos lno:
  valid_edge (low lsto) (point ev) ->
  valid_edge (high lsto) (point ev) ->
  out_left_event ev ->
  valid_edge he (point ev) ->
  open_cell_side_limit_ok lsto ->
  p_x (point ev) = left_limit lsto ->
  point ev <<= high lsto ->
  point ev >>= high lsto ->
  (1 < size (left_pts lsto))%N ->
  lexPt (nth dummy_pt (left_pts lsto) 1) (point ev) ->
  point ev <<< he ->
  update_open_cell_top lsto he ev = (nos, lno) ->
  {in rcons nos lno, forall c,
    [/\ open_cell_side_limit_ok c,
    left_limit c = p_x (point ev) &
    lexePt (bottom_left_corner c) (point ev)]} /\
  point ev = head dummy_pt (left_pts lsto) /\
  (1 < size (left_pts lno))%N /\
  (nth dummy_pt (left_pts lno) 1 = point ev) /\
  high lno = he /\
  {subset cell_edges (rcons nos lno) <= [:: low lsto, he & outgoing ev]}.
Proof.
move=> vlo vho oute vhe lstok at_ll pu pa has1 lex1 puh.
have pal : point ev >>> low lsto.
  by apply: last_case_above_low.
have oute' :
  {in sort edge_below (outgoing ev), forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
rewrite /update_open_cell_top -pvert_y_eq.
move: (lstok) => /andP[] lptsn0 /andP[] allx /andP[] srt /andP[] hon lon.
have ponh : point ev === high lsto.
  rewrite /point_on_edge vho andbT; apply/eqP/le_anti.
  move: pu; rewrite /point_under_edge subrr=> -> /=; rewrite leNgt.
  by move: pa; rewrite /point_strictly_under_edge/R_ltb subrr -lt_neqAle.
have ph : point ev = head dummy_pt (left_pts lsto).
  have xs : p_x (point ev) = p_x (head dummy_pt (left_pts lsto)).
    by case: left_pts lptsn0 allx => [ | a tl] //= _ /andP[] /eqP -> _.
  have ys : p_y (point ev) = p_y (head dummy_pt (left_pts lsto)).
    exact: (on_edge_same_point ponh hon xs).
  by apply/eqP; rewrite pt_eqE xs ys !eqxx.
have puh' : p_y (point ev) < pvert_y (point ev) he.
  by rewrite -(strict_under_pvert_y vhe).
have btm_lsto : lexPt (bottom_left_corner lsto) (point ev).
  rewrite /bottom_left_corner.
  apply: lexePt_lexPt_trans lex1.
  (* TODO: check for duplication *)
  move: allx; rewrite -(open_cell_side_limit_ok_last lstok) => allx.
  case: left_pts has1 allx srt => [ | a [ | b [ | c tl]]] //= _.
      by rewrite lexePt_refl.
    rewrite /lexePt.
    move=> /andP[] _ /andP[] /eqP -> _; rewrite ltxx eqxx /=.
    move=> /andP[] _.
    rewrite -[_ && _]/(path >%R (p_y b) [seq p_y p | p <- c :: tl]).
    rewrite (path_sortedE (rev_trans lt_trans))=> /andP[] + _.
    by move=> /allP /(_ _ (map_f _ (mem_last _ _))) /ltW.

case ogq : outgoing => [ | fog ogs].
  move=> -[] <- <- /=.
  set lno1 := (Bcell (Bpt (p_x (point ev))
                            (pvert_y (point ev) he) :: left_pts lsto)
                (right_pts lsto) (low lsto) he).
  have lln : left_limit lno1 = left_limit lsto.
     exact at_ll.
  have btm_lno_eq : lexePt (bottom_left_corner lno1) (point ev).
    apply/lexPtW; move: btm_lsto.
    rewrite /bottom_left_corner /lno1 /=.
    by case: left_pts has1 => [ | a tl].
  split.
    move=> g; rewrite inE => /eqP ->; split.
        rewrite /open_cell_side_limit_ok /= lln at_ll eqxx allx.
        case: left_pts lptsn0 ph srt lon => [ | a tl] //= _ <- -> ->.
        by rewrite puh' !andbT /= -at_ll pvert_on.
      by  move: lln; rewrite at_ll.
    by [].
  split.
    by [].
  split.
    by case: left_pts lptsn0.
  split.
    by rewrite nth0 ph.
  by split.
case oca_eq : opening_cells_aux => [l lc].
have oca_eq' : opening_cells_aux (point ev)
          (sort edge_below (outgoing ev)) (low lsto) he = (l, lc).
  by rewrite ogq.
have ogn0 : outgoing ev != [::] by rewrite ogq.
have := opening_cells_aux_absurd_case vlo vhe ogn0 oute; rewrite ogq oca_eq.
case lq : l => [ | fc oc] // _ -[] <- <-; split; last first.
  have := opening_cells_aux_high_last vlo vhe oute'.
  have := opening_cells_last_left_pts vlo vhe oute ogn0 puh.
  rewrite oca_eq' /= => -> ->.
  do 4 (split; first by []).
  have := opening_cells_aux_subset vlo vhe oute' oca_eq'=> subo.
  rewrite /cell_edges.
  apply: subset_catl=> g /=.
    rewrite -[X in g \in X -> _]/([seq low i | i <- rcons (fc :: oc) lc]).
    rewrite -lq=> /mapP [c cin gc].
    move: (subo _ cin)=> /andP[] + _; rewrite inE mem_sort -ogq !inE gc.
    by move=> /orP[] ->; rewrite ?orbT.
  rewrite -[X in g \in X -> _]/([seq high i | i <- rcons (fc :: oc) lc]).
  rewrite -lq=> /mapP [c cin gc].
  move: (subo _ cin) => /andP[] _; rewrite inE mem_sort -ogq !inE gc.
  by move=> ->; rewrite orbT.
move=> c /=; rewrite inE=> /orP[/eqP -> | cin].
  have lptsq : point ev :: behead (left_pts lsto) = left_pts lsto.
    by case: left_pts lptsn0 ph => [ | a tl] //= _ ->.
  rewrite lptsq /left_limit left_pts_set at_ll; split;[ | by [] | ].
    rewrite /open_cell_side_limit_ok /= lptsn0 /left_limit.
    rewrite left_pts_set allx srt.
    have hfcin : high fc \in outgoing ev.
      have := opening_cells_high vlo vhe oute; rewrite /opening_cells oca_eq'.
      rewrite lq.
      have : (0 < size (sort edge_below (outgoing ev)))%N.
        by rewrite ogq size_sort.
      case sq: sort => [ | a tl] //= _ -[] hfca _.
      have : high fc \in a :: tl by rewrite hfca inE eqxx.
      by rewrite -sq mem_sort.
    rewrite -ph -(eqP (oute (high fc) hfcin)) left_on_edge.
    have := opening_cells_seq_edge_shift oute' vlo vhe oca_eq'.
    by rewrite lq /= => -[] <-.
  rewrite /bottom_left_corner left_pts_set; exact: (lexPtW btm_lsto).
split.
    have := opening_cells_aux_side_limit vlo vhe
      (underWC pal) puh oute' oca_eq'.
    move=> /allP; apply.
    by rewrite lq /= inE cin orbT.
  have := opening_cells_left oute vlo vhe; rewrite /opening_cells oca_eq'.
  by apply; rewrite lq /= inE cin orbT.
have cin' : c \in opening_cells (point ev) (outgoing ev) (low lsto) he.
  by rewrite /opening_cells oca_eq' lq /= inE cin !orbT.
by have := opening_cells_last_lexePt oute (underWC pal) puh vlo vhe cin'.
Qed.

Section proof_environment.

Variables (bottom top : edge) (s : seq edge) (fop : seq cell) (lsto : cell)
  (lop cls : seq cell) (lstc : cell) (ev : event) (lsthe : edge) (lstx : R)
  (all_e evs past : seq event).

Let evin : ev \in ev :: evs.
Proof. by rewrite inE eqxx. Qed.

Hypotheses
  (boxwf : bottom <| top)
  (nocs' : {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2})
  (inbox_es : {in s, forall g, inside_box bottom top (left_pt g) &&
                                inside_box bottom top (right_pt g)})
  (at_lstx : lstx = p_x (point ev))
  (pu : point ev <<= lsthe)
  (pa : point ev >>= lsthe)
  (ss_inv : safe_side_non_gp_invariant bottom top s all_e past
    (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs)).

Let d_inv : disjoint_non_gp_invariant bottom top s
    (Bscan fop lsto lop cls lstc lsthe lstx) all_e past (ev :: evs).
Proof.
apply: (disjoint_ss ss_inv).
Qed.

Let ec_inv : edge_covered_non_gp_invariant bottom top s
    all_e past (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs).
Proof. apply: (covered_ss ss_inv). Qed.

Let comng := common_non_gp_inv_dis d_inv.

Let comi : common_invariant bottom top s
  (Bscan fop lsto lop cls lstc lsthe lstx) all_e past (ev :: evs).
Proof. by exact: (ngcomm comng). Qed.

Let tmp_inv : inv1_seq bottom top (ev :: evs) (fop ++ lsto :: lop).
Proof. by exact: (inv1 comi). Qed.

Let oute : out_left_event ev.
Proof.
by apply: (out_events comi).
Qed.

Let oute' :
  {in sort edge_below (outgoing ev), forall g, left_pt g == point ev}.
Proof.
move=> g; rewrite mem_sort; apply: oute.
Qed.

Let pal : (point ev) >>> low lsto.
Proof.
by exact: (same_x_point_above_low_lsto at_lstx comng).
Qed.

Let clae : close_alive_edges bottom top (fop ++ lsto :: lop) (ev :: evs).
Proof.
by case: tmp_inv.
Qed.

Let sval : seq_valid (fop ++ lsto :: lop) (point ev).
Proof.
by move: tmp_inv => -[] ? [] [// | ?] [] ? [] ? ?.
Qed.

Let adj : adjacent_cells (fop ++ lsto :: lop).
Proof.
by move: tmp_inv => -[] ? [] [// | ?] [] ? [] ? ?.
Qed.

Let cbtom : cells_bottom_top bottom top (fop ++ lsto :: lop).
Proof.
by move: tmp_inv => -[] ? [] [// | ?] [] ? [] ? ?.
Qed.

Let rfo : s_right_form (fop ++ lsto :: lop).
Proof.
by move: tmp_inv => -[] ? [] [// | ?] [] ? [] ? ?.
Qed.

Let noc : {in all_edges (fop ++ lsto :: lop) (ev :: evs) &,
           no_crossing R}.
Proof.
apply: inter_at_ext_no_crossing.
by apply: (sub_in2 (edges_sub comi) nocs').
Qed.

Variables (fc' cc :seq cell) (lcc : cell) (lc :seq cell) (le he : edge).

Hypothesis oe :
  open_cells_decomposition (lsto :: lop) (point ev) =
    (fc', cc, lcc, lc, le, he).

Let inbox_e : inside_box bottom top (point ev).
Proof.
by have := inbox_events comi => /andP[].
Qed.


Let n_in : {in [:: bottom, top & s] & ev :: evs,
     forall g e, non_inner g (point e)}.
Proof.
move=> g e gin ein.
move: gin; rewrite !inE orbA=> /orP [gbt | gin]; last first.
  by apply : (non_in_ec ec_inv); rewrite // inE eqxx.
have in_e : inside_box bottom top (point e).
  by apply: (allP (inbox_events comi)); rewrite map_f.
have := inside_box_not_on in_e.
rewrite /non_inner negb_or=> /andP[] /negbTE + /negbTE +.
by move: gbt=> /orP[] /eqP ->; try (move=> -> //); move=> _ ->.
Qed.

Let lstoin : lsto \in fop ++ lsto :: lop.
Proof.
by rewrite mem_cat inE eqxx orbT.
Qed.

Let lstok : open_cell_side_limit_ok lsto.
Proof.
by apply/(allP (sides_ok comi))/lstoin.
Qed.
Let tmp_vls : valid_edge (low lsto) (point ev) /\
  valid_edge (high lsto) (point ev).
Proof.
by apply/andP/(allP sval); rewrite mem_cat inE eqxx orbT.
Qed.

Let vlo := proj1 tmp_vls.
Let vho := proj2 tmp_vls.

Let nth1in : (nth dummy_pt (left_pts lsto) 1) \in left_pts lsto.
Proof.
by apply/mem_nth/(has_snd_lst comng).
Qed.

Let x1 : p_x (nth dummy_pt (left_pts lsto) 1) = p_x (point ev).
Proof.
move: lstok=> /andP[] _ /andP[] /allP /(_ _ nth1in) /eqP -> _.
by rewrite -at_lstx -(lstx_eq comi).
Qed.

Variables (nos : seq cell) (lno : cell).

Hypothesis uoct_eq : update_open_cell_top lsto he ev = (nos, lno).

Let exi0 : exists2 w, w \in lsto :: lop & contains_point' (point ev) w.
Proof.
rewrite /contains_point'.
exists lsto; first by rewrite inE eqxx.
rewrite (high_lsto_eq comi) pu andbT; apply: last_case_above_low=> //.
    by rewrite -at_lstx -(lstx_eq comi).
  by apply: (has_snd_lst comng).
by have := (lst_side_lex comng) => /= /andP[] +.
Qed.

Let oe' : open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
  (fop ++ fc', cc, lcc, lc, le, he).
Proof.
have := open_cells_decomposition_cat adj rfo sval exi0 pal.
by rewrite oe /=.
Qed.

Let exi1 : exists2 w, w \in fop ++ lsto :: lop &
  contains_point' (point ev) w.
Proof.
move: exi0=> [w win wP]; exists w; last by exact wP.
by rewrite mem_cat win orbT.
Qed.

Let tmp_decomposition_main_properties :=
  decomposition_main_properties oe' exi1.

Let ocd : fop ++ lsto :: lop = (fop ++ fc') ++ cc ++ lcc :: lc.
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let ctn : contains_point (point ev) lcc.
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let all_ctn : {in cc, forall c, contains_point (point ev) c}.
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let nct : {in fop ++ fc', forall c, ~~ contains_point (point ev) c}.
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let nct2 : lc != [::] -> ~~ contains_point (point ev) (head lcc lc).
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let heq : he = high lcc.
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let leq : le = low (head lcc cc).
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let lein : le \in cell_edges (fop ++ lsto :: lop).
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let hein : he \in cell_edges (fop ++ lsto :: lop).
Proof.
by move: tmp_decomposition_main_properties=>
  [? [? [? [? [? [? [? [? ?]]]]]]]].
Qed.

Let tmp_connect_properties := connect_properties cbtom adj rfo sval
  (inside_box_between inbox_e) ocd nct all_ctn ctn nct2.

Let puh : point ev <<< he.
Proof.
by move: tmp_connect_properties; rewrite /= -heq => -[].
Qed.

Let vhe : valid_edge he (point ev).
Proof.
by move: tmp_connect_properties; rewrite /= -heq => -[].
Qed.

Let nct3 : forall c, (c \in fop ++ fc') || (c \in lc) ->
  ~~ contains_point (point ev) c.
Proof.
by move: tmp_connect_properties; rewrite /= -heq => -[].
Qed.

Let at_ll : p_x (point ev) = left_limit lsto.
Proof.
by rewrite -at_lstx -(lstx_eq comi).
Qed.

Let pu' : point ev <<= high lsto.
Proof.
by move: (high_lsto_eq comi) pu => /= <-.
Qed.

Let pa' : point ev >>= high lsto.
Proof.
by move: (high_lsto_eq comi) pa => /= <-.
Qed.

Let tmp_uoct_properties := update_open_cell_top_properties vlo vho oute vhe
  lstok at_ll pu' pa'
  (has_snd_lst comng) (proj1 (andP (lst_side_lex comng))) puh uoct_eq.

Let oks : {in rcons nos lno, forall c, [/\ open_cell_side_limit_ok c,
             left_limit c = p_x (point ev) &
             lexePt (bottom_left_corner c) (point ev)]}.
Proof.
by move: tmp_uoct_properties => [? [? [? [? ?]]]].
Qed.

Let has1' : (1 < size (left_pts lno))%N.
Proof.
by move: tmp_uoct_properties => [? [? [? [? ?]]]].
Qed.

Let nth1q : nth dummy_pt (left_pts lno) 1 = point ev.
Proof.
by move: tmp_uoct_properties => [? [? [? [? ?]]]].
Qed.

Let hiq : high lno = he.
Proof.
by move: tmp_uoct_properties => [? [? [? [? [? ?]]]]].
Qed.

Let p_topleft_lsto : point ev = head dummy_pt (left_pts lsto).
Proof.
by move: tmp_uoct_properties => [? [? [? [? [? ?]]]]].
Qed.

Let ponho : point ev === high lsto.
Proof.
by rewrite p_topleft_lsto; move: lstok=> /andP[] _ /andP[] _ /andP[] _ /andP[].
Qed.

Let sub' : {subset cell_edges (rcons nos lno) <=
     [:: low lsto, he & outgoing ev]}.
Proof.
by move: tmp_uoct_properties => [? [? [? [? [? ?]]]]].
Qed.

Let ctno : contains_point (point ev) lsto.
Proof.
by rewrite /contains_point (underWC pal) pu'.
Qed.


Let lstoh : lsto = head lcc cc.
Proof.
have : lsto \in rcons cc lcc.
  have : lsto \in fop ++ lsto :: lop by rewrite mem_cat inE eqxx orbT.
  rewrite ocd -cat_rcons mem_cat (mem_cat _ (rcons _ _)) => /orP[ | /orP[]] //.
    by move=> /nct; rewrite ctno.
  move=> lstol; move:(@nct3 lsto); rewrite lstol=> /(_ (orbT _)).
  by rewrite ctno.
move=> /mem_seq_split  [s1 [s2 sq]].
elim/last_ind: {2} (s1) (erefl s1) => [ | s1' ls1 _] s1q.
  by move: sq; rewrite s1q /=; case: (cc) => [ | a tl] //= [].
have hls1 : high ls1 = low lsto.
  move : adj; rewrite /state_open_seq /= ocd -cat_rcons sq s1q cat_rcons.
  move=> /adjacent_catW [] _ /adjacent_catW [] + _ => /adjacent_catW [] _.
  by move=> /= /andP[] /eqP ->.
have : contains_point (point ev) ls1.
  have : {in rcons cc lcc, forall c, contains_point (point ev) c}.
    by move=> c; rewrite mem_rcons inE => /orP[/eqP ->| /all_ctn].
  suff /[swap] /[apply] : ls1 \in rcons cc lcc by [].
  by rewrite sq s1q mem_cat mem_rcons inE eqxx.
by rewrite /contains_point hls1 (negbTE pal) andbF.
Qed.

Let lsto_side_under : all ((@lexPt _)^~ (point ev)) (behead (left_pts lsto)).
Proof.
apply/allP=> p pin.
have := (lst_side_lex comng) => /= /andP[] + _.
apply: lexePt_lexPt_trans.
rewrite /lexePt; move: lstok=>/andP[] _ /andP[] + /andP[] + _.
case: left_pts (has_snd_lst comng) pin=> [ | a [ | b tl]] //= _.
rewrite inE => /orP[/eqP -> | ].
  by rewrite eqxx le_refl orbT.
move=> pin /andP[] _ /andP[] /eqP -> allx /andP[] _.
have /eqP -> := allP allx _ pin.
rewrite (path_sortedE (rev_trans lt_trans)).
move => /andP[] /allP /(_ _ (map_f _ pin)) /ltW -> _.
by rewrite eqxx orbT.
Qed.

#[local]
Definition str := last_case fop lsto fc' cc lcc lc cls lstc he ev.

Let inv1' : inv1_seq bottom top evs (state_open_seq str).
Proof.
have := (step_keeps_invariant1 cls lstc (inbox_events (ngcomm comng))
  oute rfo cbtom adj sval (closed_events comi) clae
  (esym (high_lsto_eq comi)) (fun x : p_x (point ev) = lstx => pal) noc
  (lex_events comi)).
rewrite /invariant1 /step /same_x at_lstx eqxx pu (negbTE pa) /=.
by rewrite oe.
Qed.

Let lstx_eq' : lst_x _ _ str = left_limit (lst_open str).
Proof.
rewrite /str/last_case uoct_eq /=.
by have /oks[_ ->] : lno \in rcons nos lno by rewrite mem_rcons inE eqxx.
Qed.

Let high_lsto_eq' : high (lst_open str) = lst_high _ _ str.
Proof.
by rewrite /str/last_case uoct_eq /=.
Qed.

Let edges_sub' : {subset all_edges (state_open_seq str) evs <=
  [:: bottom, top & s]}.
Proof.
move=> g gin; apply: (edges_sub comi); move: gin.
rewrite mem_cat=> /orP[ | gin]; last first.
  by rewrite mem_cat events_to_edges_cons orbC mem_cat gin orbT.
rewrite /str/last_case uoct_eq /state_open_seq/=.
rewrite -!catA -cat_rcons catA cell_edges_cat mem_cat => /orP[gold | ].
  by rewrite mem_cat ocd cell_edges_cat mem_cat gold.
rewrite cell_edges_cat mem_cat => /orP[ | gold]; last first.
  rewrite mem_cat ocd -cat_rcons cell_edges_cat mem_cat.
  rewrite (cell_edges_cat (rcons _ _)) (mem_cat  _ (cell_edges _)).
  by rewrite gold !orbT.
move=> /sub'; rewrite !inE => /orP[/eqP -> | ].
  by rewrite mem_cat cell_edges_cat mem_cat cell_edges_cons inE eqxx !orbT.
move=> /orP[/eqP -> | gnew].
  by rewrite mem_cat hein.
by rewrite mem_cat orbC events_to_edges_cons mem_cat gnew.
Qed.

Let closed_events' : close_edges_from_events evs.
Proof.
by have := closed_events comi => /= /andP[].
Qed.

Let out_events' : {in evs, forall e, out_left_event e}.
Proof.
by move=> e ein; apply: (out_events comi); rewrite inE ein orbT.
Qed.

Let uniq_ec' : {in evs, forall e, uniq (outgoing e)}.
Proof.
by move=> e ein; apply: (uniq_ec comi); rewrite inE ein orbT.
Qed.

Let inbox_events' : all (inside_box bottom top)
           [seq point x | x <- evs].
Proof.
by have := inbox_events comi=> /= /andP[].
Qed.

Let no_dup_edge' : {in [seq high c | c <- state_open_seq str] & evs,
     forall g e, g \notin (outgoing e)}.
Proof.
move=> g e + ein.
rewrite /str /last_case uoct_eq /state_open_seq /= -!catA -cat_rcons.
rewrite !map_cat !mem_cat orbA orbCA=> /orP[gnew | gold]; last first.
  apply: (no_dup_edge comi); rewrite ?inE ?ein ?orbT //.
  rewrite /state_open_seq /= ocd !map_cat !(mem_cat, inE).
  by move: gold=> /orP[ /orP[] | ] ->; rewrite ?orbT.
have /sub' : g \in cell_edges (rcons nos lno).
  by rewrite mem_cat gnew orbT.
rewrite inE => /orP[/eqP -> | ]; last first.
  rewrite inE => /orP[/eqP -> |].
    apply: (no_dup_edge comi); rewrite ?inE ?ein ?orbT //.
    rewrite /state_open_seq /= ocd !map_cat !(mem_cat, inE).
    by rewrite heq eqxx !orbT.
  move=> gev; apply/negP=> ge.
  have abs : point ev = point e.
    have oute1 : out_left_event e.
      by apply: (out_events comi); rewrite inE ein orbT.
    by rewrite -(eqP (oute gev)) -(eqP (oute1 _ ge)).
  have := lex_events comi=> /=.
  rewrite (path_sortedE (@lexPtEv_trans _)) => /andP[] /allP /(_ _ ein) + _.
  by rewrite /lexPtEv abs lexPt_irrefl.
rewrite lstoh.
elim/last_ind: {2} (fop ++ fc') (erefl (fop ++ fc')); last first.
  move=> f' lf' _ f'q.
  apply: (no_dup_edge comi); rewrite ?inE ?ein ?orbT //.
  move: adj; rewrite /state_open_seq/= ocd f'q cat_rcons !map_cat /= mem_cat.
  rewrite inE.
  move=> /adjacent_catW[] _  /=.
  by case (cc) => [ | a tl] /= /andP[] /eqP <- _; rewrite eqxx ?orbT.
move=> f'q.
suff -> : low (head lcc cc) = bottom.
  apply/negP=> abs.
  have ponb : point e === bottom.
    by rewrite -(eqP (out_events' ein abs)) left_on_edge.
  have := allP (inbox_events comi) (point e) (map_f _ _).
  rewrite inE ein => /(_ (orbT _))=> /andP[] /andP[] + _ _.
  by rewrite (under_onVstrict (proj2 (andP ponb))) ponb.
move: cbtom=> /andP[] /andP[] _ + _; rewrite ocd f'q=> /eqP <-.
by case: (cc).
Qed.

Let lex_events' : sorted (@lexPtEv _) evs.
Proof.
have := lex_events comi; rewrite /= (path_sortedE (@lexPtEv_trans _)).
by move=> /andP[].
Qed.

Let sides_ok' : all open_cell_side_limit_ok (state_open_seq str).
Proof.
have := step_keeps_open_side_limit cls lstc (inbox_events comi) oute
  rfo cbtom adj sval (esym (high_lsto_eq comi))
  (lstx_eq comi) (fun _ => pal) (sides_ok comi) lsto_side_under.
rewrite /state_open_seq/step/same_x at_lstx eqxx pu /= (negbTE pa) /=.
by rewrite /str/last_case oe.
Qed.

Let above_low_lsto' :
     {in evs, forall e,
        lexPt (last dummy_pt (left_pts (lst_open str)))
              (point e)}.
Proof.
move=> e ein.
have := (lex_events comi)=> /=; rewrite (path_sortedE (@lexPtEv_trans _)).
move=> /andP[] /allP /(_ _ ein) + _.
apply: lexePt_lexPt_trans.
rewrite /str/last_case uoct_eq /=.
by have /oks [] : lno \in rcons nos lno by rewrite mem_rcons inE eqxx.
Qed.

Let stradle' :
     evs = [::] \/ {in [seq high c | c <- state_open_seq str], forall g,
     lexPt (left_pt g) (point (head dummy_event evs)) &&
     lexePt (point (head dummy_event evs)) (right_pt g)}.
Proof.
case evsq : (evs) => [ | e' evs'] /=; first by left.
right.
have := stradle comi=> -[ | stradle]; first by [].
have := step_keeps_lex_edge (inbox_events comi) oute rfo cbtom adj sval
  (closed_events comi) clae (esym (high_lsto_eq comi)) (fun _ => pal)
  stradle.
move=> /(_ cls lstc lstx).
rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe.
have inbox_e' : inside_box bottom top (point e').
  by apply: (allP inbox_events'); rewrite evsq inE eqxx.
have eve' : lexPtEv ev e'.
  by move: (lex_events comi); rewrite evsq=> /= /andP[].
have e'e : forall e2, e2 \in evs -> lexePtEv e' e2.
  move=> e2; rewrite evsq inE=> /orP[/eqP -> | e2in].
    by apply: lexePt_refl.
  apply: lexPtW.
  move: lex_events'; rewrite evsq=> /=.
  by rewrite (path_sortedE (@lexPtEv_trans _))=> /andP[] /allP /(_ _ e2in).
move=> /(_ _ inbox_e' eve' e'e).
by rewrite /str/last_case uoct_eq.
Qed.

Let strq : str = Bscan (fop ++ fc' ++ nos) lno lc
  (closing_cells (point ev) (behead cc) ++ lstc :: cls)
  (close_cell (point ev) lcc) he (p_x (point ev)).
Proof.
by rewrite /str/last_case uoct_eq.
Qed.

Let all_events_break' : all_e = rcons past ev ++ evs.
Proof.
by rewrite cat_rcons (all_events_break comi).
Qed.

Lemma last_case_common_invariant_pre :
  common_non_gp_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    all_e (rcons past ev) evs.
Proof.
rewrite /step /= /same_x at_lstx eqxx pu (negbTE pa) /=.
rewrite oe uoct_eq.
move: inv1' lstx_eq' high_lsto_eq' edges_sub' no_dup_edge'
  sides_ok' above_low_lsto' stradle'.
rewrite strq => ? ? ? ? ? ? ? ?.
have ngcomm' : common_invariant bottom top s str all_e (rcons past ev) evs.
  by rewrite /str/last_case uoct_eq; constructor.
have lst_side_lex' : path (@lexPt _)
  (nth dummy_pt (left_pts (lst_open str)) 1) [seq point e | e <- evs].
  rewrite /str/last_case uoct_eq /= nth1q.
  by have := (lex_events comi); rewrite sorted_lexPtEv_lexPt.
rewrite strq in lst_side_lex'.
by constructor.
Qed.

Let common_non_gp_inv_dis' : common_non_gp_invariant bottom top s str 
  all_e (rcons past ev) evs.
Proof.
have := last_case_common_invariant_pre.
by rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq strq.
Qed.

Let dis_main : {in rcons (closing_cells (point ev) (behead cc) ++ lstc :: cls)
  (close_cell (point ev) lcc) &,
  disjoint_closed_cells R} /\
  {in (fop ++ fc' ++ nos) ++ lno :: lc &
    rcons (closing_cells (point ev) (behead cc) ++ lstc :: cls)
  (close_cell (point ev) lcc), disjoint_open_closed_cells R}.
Proof.
have at_left : {in rcons cls lstc, forall c, right_limit c <= p_x (point ev)}.
  by rewrite -at_lstx; apply: (closed_at_left_non_gp d_inv).
have uniq_cl : uniq (rcons cls lstc).
by apply/(@map_uniq _ _ cell_center)/(uniq_cc d_inv).
have := step_keeps_disjoint (inbox_events comi) oute rfo cbtom adj sval
 (esym (high_lsto_eq comi)) (lstx_eq comi) (fun _ => pal)
 (pairwise_open_non_gp d_inv) (sides_ok comi)
 (op_cl_dis_non_gp d_inv) (cl_dis_non_gp d_inv) at_left uniq_cl
 (size_right_cls d_inv).
rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq /=.
by rewrite /state_closed_seq /state_open_seq.
Qed.

Let op_cl_dis_non_gp' :
    {in state_open_seq str & state_closed_seq str,
       disjoint_open_closed_cells R}.
Proof.
rewrite strq /state_open_seq /state_closed_seq /=.
by move: dis_main=> -[].
Qed.

Let cl_dis_non_gp' : {in state_closed_seq str &, disjoint_closed_cells R}.
Proof.
rewrite strq /state_open_seq /state_closed_seq /=.
by move: dis_main=> -[].
Qed.

Let pairwise_open_non_gp' : pairwise edge_below
     (bottom :: [seq high c | c <- state_open_seq str]).
Proof.
have := step_keeps_pw cls lstc (inbox_events (ngcomm comng))
  oute rfo cbtom adj sval (esym (high_lsto_eq comi))
  (fun x : p_x (point ev) = lstx => pal) noc (pairwise_open_non_gp d_inv).
rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq.
by rewrite strq.
Qed.

Let closed_at_left_non_gp' :
     {in state_closed_seq str,
       forall c, right_limit c <= lst_x _ _ str}.
Proof.
have cl_side' : all (@closed_cell_side_limit_ok _) (rcons cls lstc).
  apply/allP; exact: (cl_side d_inv).
have cl_at_left' :
  {in rcons cls lstc, forall c, right_limit c <= p_x (point ev)}.
  rewrite -at_lstx; exact: (closed_at_left_non_gp d_inv).
have := step_keeps_closed_to_the_left
 (inbox_events (ngcomm comng)) rfo
  cbtom adj sval (esym (high_lsto_eq comi))
  (fun x : p_x (point ev) = lstx => pal)
  cl_side' cl_at_left' (size_right_cls d_inv).
by rewrite strq /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq.
Qed.

Let vlcc : valid_edge (low lcc) (point ev) && valid_edge (high lcc) (point ev).
Proof.
by apply: (allP sval); rewrite ocd !mem_cat inE eqxx !orbT.
Qed.

Let vllcc := proj1 (andP vlcc).

Let vhlcc := proj2 (andP vlcc).

Let size_right_cls' : (1 < size (right_pts (lst_closed str)))%N.
Proof.
rewrite strq /= /close_cell.
rewrite (pvertE vllcc) (pvertE vhlcc) /no_dup_seq_aux.
rewrite -![pt_eqb _ _ _ _]/(_ == _).
case: ifP=> [/eqP ponhigh | _]; case: ifP=> _ //.
move: puh; rewrite heq (strict_nonAunder vhlcc).
by rewrite - ponhigh (pvert_on vhlcc).
Qed.


Let to_right_order :
  rcons (closing_cells (point ev) (behead cc) ++ lstc :: cls)
    (close_cell (point ev) lcc) =i
  rcons cls lstc ++ rcons (closing_cells (point ev) (behead cc))
    (close_cell (point ev) lcc).
Proof.
rewrite -!cats1 !catA=> g; rewrite !mem_cat !inE.
by repeat (set w := (X in (g \in X)); case: (g \in w);
  rewrite ?orbT ?orbF; clear w);
  repeat (set w := (X in (g == X)); case: (g == w); rewrite ?orbT ?orbF;
    clear w).
Qed.

Let rcbehead_sub : {subset rcons (behead cc) lcc <= rcons cc lcc}.
Proof.
by move=> c; case: (cc) => [ | ? ?] //=; rewrite inE orbC => ->.
Qed.

Let ccn0 : cc != [::].
Proof.
apply/negP=> /eqP abs; have := lstoh.
rewrite abs /= => lstoq.
by move: puh; rewrite heq -lstoq (high_lsto_eq comi) (negbTE pa).
Qed.

Let vle : valid_edge le (point ev).
Proof.
have hin : head lcc cc \in fop ++ lsto :: lop.
  rewrite ocd mem_cat; apply/orP; right.
  by case : (cc) => [ | ? ?] /=; rewrite inE eqxx.
by rewrite leq; have := (allP sval) _ hin => /andP[].
Qed.

Let cell_center_in' :
      {in state_closed_seq str,
      forall c, strict_inside_closed (cell_center c) c}.
Proof.
rewrite strq /state_closed_seq /=.
move=> c; rewrite to_right_order.
rewrite mem_cat -map_rcons => /orP[cold |/mapP[c' c'in cc']].
  apply: (cell_center_in d_inv).
  by rewrite /state_closed_seq /=.
have c'in2 : c' \in rcons cc lcc by apply: rcbehead_sub.
have c'in3 : c' \in fop ++ lsto :: lop.
  by rewrite ocd -cat_rcons mem_cat (mem_cat _ _ lc) c'in2 !orbT.
have /andP[vlc' vhc'] : valid_edge (low c') (point ev) &&
     valid_edge (high c') (point ev).
  by apply: (allP sval _ ).
have ldhc' : low c' != high c'.
  apply: (low_diff_high_open d_inv).
  rewrite /state_open_seq /= ocd -cat_rcons mem_cat (mem_cat _ _ lc).
  by rewrite c'in2 !orbT.
have c'ok : open_cell_side_limit_ok c'.
  by apply: (allP (sides_ok comi)).
have nocc' : inter_at_ext (low c') (high c').
  apply: nocs'; apply: (edges_sub comi); rewrite /state_open_seq /=.
    by rewrite mem_cat mem_cat map_f // c'in3.
  by rewrite mem_cat mem_cat map_f ?orbT // c'in3.
have lbhc' : low c' <| high c'.
  by apply: (allP rfo).

have llc'lt : left_limit c' < p_x (point ev).

  have adjcc : adjacent_cells (rcons cc lcc).
    have := adj; rewrite /state_open_seq /= ocd -cat_rcons.
    by move=> /adjacent_catW[] _ /adjacent_catW[].

  have [c2 c2in c'c2] : exists2 c2, c2 \in cc & low c' = high c2.
    move: (c'in); rewrite mem_rcons inE => /orP[/eqP -> | c'inb].
      exists (last dummy_cell cc).
        by move: ccn0; case: (cc)=> [ | ? ?]; rewrite //= mem_last.
      move: adjcc; rewrite -cats1; case: (cc) ccn0=> [ | a tl] //= _.
      by rewrite cat_path /= andbT => /andP[] _ /eqP/esym.
    have [[ | a s1] [s2 sq]] := mem_seq_split c'inb.
      exists (head dummy_cell cc).
        by move: ccn0; case: (cc) => [ | ? ?]; rewrite //= inE eqxx.
      by case: (cc) ccn0 sq adjcc => [ | ? ?] //= _ -> /= /andP[]/eqP/esym.
    exists (last a s1).
      case: (cc) ccn0 sq=> [ | b tl'] //= _ -> /=.
      by rewrite inE -[_ :: _ ++ _]/((_ :: _) ++ _) mem_cat mem_last !orbT.
    case: (cc) ccn0 sq adjcc=> [ | b tl'] //= _ -> /= /andP[] _.
    rewrite rcons_cat /=.
    by rewrite cat_path=> /andP[] /= _ /andP[] /eqP/esym.

  have : right_pt (high c2) = point ev.
    (* TODO: duplication,
      what follows is duplicated from the proof of right_pt_e inside
      step_keeps_edge_covering *)
    have := open_cells_decomposition_point_on cbtom adj
      (inside_box_between inbox_e) sval oe' c2in.
    rewrite -c'c2.
    have lc's : low c' \in [:: bottom, top & s].
      by apply: (edges_sub comi); rewrite mem_cat mem_cat map_f.
    have := n_in lc's evin; rewrite /non_inner=> /[apply].
    move=> [abs | ->]; last by [].
    have c2in2: c2 \in fop ++ lsto :: lop.
      by rewrite ocd !(mem_cat, inE) c2in !orbT.
    have := stradle comi; rewrite /state_open_seq /= => -[// | ].
    move=> /(_ _ (map_f _ c2in2)) /andP[] + _.
    by rewrite abs c'c2 lexPt_irrefl.
  rewrite -c'c2 => rlc'_ev.
  rewrite lt_neqAle.
  have := left_opens d_inv c'in3; rewrite /= at_lstx => ->; rewrite andbT.
  apply/eqP=> lc'x.
  have : bottom_left_corner c' = point ev.
    have evonc' : point ev === low c' by rewrite -rlc'_ev right_on_edge.
    have bonc' : bottom_left_corner c' === low c'.
      have := allP (sides_ok comi) _ c'in3.
      by move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _.
    rewrite -(open_cell_side_limit_ok_last c'ok) in lc'x.
    have same_y := on_edge_same_point bonc' evonc' lc'x.
    by apply/eqP; rewrite pt_eqE -lc'x -same_y !eqxx.
  have := bottom_left_opens d_inv c'in3 evin=> /[swap] ->.
  by rewrite lexPt_irrefl.
have := cell_center_close_cell_inside nocc' ldhc' lbhc' c'ok vlc' vhc' llc'lt.
by rewrite cc'.
Qed.

Let cl_side' : {in state_closed_seq str, forall c, closed_cell_side_limit_ok c}.
Proof.
rewrite strq /state_closed_seq /= => c; rewrite to_right_order.
rewrite -map_rcons mem_cat => /orP[cold | /mapP [c' c'in cc']]; last first.
  have c'in2 : c' \in rcons cc lcc by apply: rcbehead_sub.
  have c'in3 : c' \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons mem_cat (mem_cat _ _ lc) c'in2 !orbT.
  have ctc' : contains_point (point ev) c'.
    move: c'in2; rewrite mem_rcons inE=> /orP[/eqP -> | ] //.
    by apply: all_ctn.
  have /andP[vlc' vhc'] : valid_edge (low c') (point ev) &&
     valid_edge (high c') (point ev).
    by apply: (allP sval _ ).
  have c'ok : open_cell_side_limit_ok c'.
    by apply: (allP (sides_ok comi)).
  have := close_cell_ok ctc' vlc' vhc' c'ok.
  by rewrite cc'.
by apply: (cl_side d_inv); rewrite /state_closed_seq /=.
Qed.

(* TODO: important! the order of closed cells is not repsected here,
  but it makes the proof easier.*)
Let uniq_cc' : uniq [seq cell_center c | c <- state_closed_seq str].
Proof.
rewrite strq /state_closed_seq /= -cats1.
suff right_order :
  uniq [seq cell_center c | c <- cls ++ lstc ::
  closing_cells (point ev) (behead cc) ++ [:: close_cell (point ev) lcc]].
  rewrite -[lstc::cls]/([::lstc] ++ cls).
  rewrite !map_cat -!catA uniq_catC -!catA uniq_catCA catA uniq_catC.
  rewrite -!catA uniq_catCA catA uniq_catC -!catA.
  by move: right_order; rewrite -[lstc :: _]/([::lstc] ++ _) !map_cat.
rewrite -[lstc :: _] /([:: lstc] ++ _) catA map_cat cat_uniq !cats1.
have -> /= : uniq [seq cell_center c | c <- rcons cls lstc].
  by have := uniq_cc d_inv.
set new_cl := rcons _ (close_cell _ _).
have -> /= : ~~ has (in_mem^~ (mem [seq cell_center c | c <- rcons cls lstc]))
  [seq cell_center c | c <- new_cl].
(* TODO: duplication (from subproof ucc' in
  Lemma simple_step_disjoint_non_gp_invariant)*)
  rewrite /new_cl /closing_cells -map_rcons; apply/negP=> /hasP[p].
  move=> /mapP [c2 c2new pc2].
  move=> /mapP [c1 c1old pc1].
  move: c2new=> /mapP [c3 c3o_pre c2c3].
  have c3o : c3 \in rcons cc lcc by apply: rcbehead_sub.
  have c3o2 : c3 \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons !mem_cat c3o orbT.
  have noc3 : inter_at_ext (low c3) (high c3).
    by apply: nocs'; apply: (edges_sub comi); rewrite 2!mem_cat map_f ?orbT.
  have dif3 : low c3 != high c3.
    by apply: (low_diff_high_open d_inv).
  have wf3 : low c3 <| high c3 by apply (allP rfo).
  have ok3 : open_cell_side_limit_ok c3 by apply: (allP (sides_ok comi)).
  have vc3 : valid_cell c3 (point ev).
    by apply: (andP (allP sval c3 c3o2)).
  have [vlc3 vhc3] := vc3.
  have c2in : c2 \in rcons (cls ++ lstc :: closing_cells (point ev) cc)
                      (close_cell (point ev) lcc).
    rewrite -cats1 -catA mem_cat /= inE /closing_cells cats1 -map_rcons.
    by rewrite orbA orbC; apply/orP; left; apply/mapP; exists c3.
  have lc3ltp : left_limit c3 < p_x (point ev).
    have := cell_center_in'; rewrite strq /state_closed_seq /=.
    move=> /(_ (close_cell (point ev) c3)).
      rewrite to_right_order mem_cat orbC -map_rcons map_f //.
      move=> /(_ isT).
      move=> /andP[] _ /andP[] lt1.
      rewrite right_limit_close_cell //.
      apply: lt_trans.
      by move: lt1; rewrite left_limit_close_cell.
    (* rewrite c2c3 /left_limit.
    have [_ _ ->] := close_cell_preserve_3sides (point ev) c3.
    by rewrite right_limit_close_cell. *)
  have := cl_side'; rewrite strq /state_closed_seq /=.
  move=> /(_ c2); rewrite c2c3.
  rewrite to_right_order mem_cat orbC -map_rcons map_f //.
  move=> /(_ isT); rewrite -c2c3=> ok2.
  have :=
    cell_center_close_cell_inside noc3 dif3 wf3 ok3 vlc3 vhc3 lc3ltp.
  rewrite -[cells.close_cell _ _]/(close_cell _ _).
  rewrite -c2c3=> /strict_inside_closedW ccin.
  have := close'_subset_contact vc3; rewrite -c2c3 => /(_ _ ok2 ccin) ccin'.
  have := op_cl_dis_non_gp d_inv c3o2 c1old (cell_center c2)=> /negP.
  by rewrite ccin' -pc2 pc1 (strict_inside_closedW (cell_center_in d_inv _)).
suff : uniq [seq cell_center c | c <- new_cl] by [].
rewrite /new_cl.
case ccq : cc => [ | fcc cc'] /=; first by [].
apply/(uniqP dummy_pt).
  rewrite  /closing_cells !(size_map, size_rcons).
  set L := [seq cell_center c | c <- _].
  have main : forall i j, (i <= j < (size cc').+1)%N ->
    nth dummy_pt L i = nth dummy_pt L j -> i = j.
    move=> i j /[dup] ijs /andP[ij js] abs.
    have i_s : (i < (size cc').+1)%N by apply: leq_ltn_trans js.
    move: ij; rewrite leq_eqVlt=> /orP[/eqP -> | ij]; first by [].
    have jpred : j = j.-1.+1 by rewrite (ltn_predK ij).
    have i_sm : (i < (size cc'))%N.
      by apply: (leq_trans ij); rewrite -ltnS.
    have is' : (i < size [seq high c | c <- rcons cc' lcc])%N.
      by rewrite size_map size_rcons.
    have js' : (j < size [seq high c | c <- rcons cc' lcc])%N.
      by rewrite size_map size_rcons.
    have js2 : (j < size (rcons cc' lcc))%N by rewrite size_rcons.
    have jps : (j.-1 < (size cc').+1)%N.
      by apply : (ltn_trans _ js); rewrite -jpred leqnn.
    have jps2 : (j.-1 < size (rcons cc' lcc))%N by rewrite size_rcons.
    have jps3 : (j.-1 < size [seq high c | c <- rcons cc' lcc])%N.
      by rewrite size_map size_rcons.
    move: (pairwise_open_non_gp d_inv); rewrite /state_open_seq /=.
    rewrite ocd !map_cat pairwise_cat=> /andP[] _ /andP[] _.
    move=> /andP[] _.
    rewrite /= -cat_rcons pairwise_cat=> /andP[] _ /andP[] + _.
    rewrite -map_rcons.
    move=> big_pairwise.
    have : pairwise edge_below [seq high c | c <- rcons cc' lcc].
      by move: big_pairwise; rewrite ccq /= => /andP[].
    move=> /(pairwiseP dummy_edge)/(_ _ _ is' jps3) => ibelj.
    have nth_in k : (k < (size cc').+1)%N ->
      nth dummy_cell (rcons cc' lcc) k \in fop ++ lsto :: lop.
      move=> ks.
      rewrite ocd -cat_rcons !mem_cat; apply/orP; right; apply/orP; left.
      have -> : nth dummy_cell (rcons cc' lcc) k =
                nth dummy_cell (rcons cc lcc) k.+1.
        by rewrite ccq.
        have ks_cc : (k.+1 < (size cc).+1)%N by rewrite ccq ltnS.
      by rewrite mem_nth // size_rcons.
    have vlk k : (k < (size cc').+1)%N ->
      valid_edge (nth dummy_edge [seq high c | c <- rcons cc' lcc] k) (point ev).
      move=> ks.
      have ks' : (k < size (rcons cc' lcc))%N by rewrite size_rcons.
      set ck := nth dummy_cell (rcons cc lcc) k.
      rewrite (nth_map dummy_cell dummy_edge high) //.
      by have := allP sval _ (nth_in k ks)=> /andP[].
    have vllk k : (k < (size cc').+1)%N ->
      valid_edge (low (nth dummy_cell (rcons cc' lcc) k)) (point ev).
      move=> ks.
      have ks' : (k < size (rcons cc' lcc))%N by rewrite size_rcons.
      set ck := nth dummy_cell (rcons cc' lcc) k.
      by have := allP sval _ (nth_in k ks)=> /andP[].
    have vli := vlk i i_s.
    have incl k: (k < (size cc').+1)%N -> inside_closed' (nth dummy_pt L k)
            (nth dummy_cell
              [seq close_cell (point ev) c | c <- rcons cc' lcc] k).
      move=> ks.
      rewrite /L (nth_map dummy_cell); last first.
        by rewrite size_rcons size_map.
      rewrite -map_rcons.
      apply: (strict_inside_closedW (cell_center_in' _)).
      rewrite strq /state_closed_seq /=.
      rewrite to_right_order.
      rewrite mem_cat; apply/orP; right.
      rewrite ccq /=.
      by rewrite -map_rcons mem_nth // size_map size_rcons.
    have inclj := incl j js.
    have incli := incl i i_s.
    have lowjq : low (nth dummy_cell [seq close_cell (point ev) c |
                       c <- rcons cc' lcc] j)
      = high (nth dummy_cell [seq close_cell (point ev) c |
                                 c <- rcons cc' lcc] j.-1).
      have := (nth_map dummy_cell dummy_cell (close_cell (point ev))).
      move=> /(_ j (rcons cc' lcc) js2) => ->.
      have := (nth_map dummy_cell dummy_cell (close_cell (point ev))).
      move=> /(_ j.-1 (rcons cc' lcc) jps2) => ->.
      have [-> _ _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) j).
      have [ _ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) j.-1).
      have jint : (0 < j < size (rcons cc' lcc))%N.
        by rewrite (leq_ltn_trans (leq0n _) (ij)).
      have := adj; rewrite /adjacent_cells ocd -cat_rcons=>/adjacent_catW.
      move=>[] _ /adjacent_catW [] + _.
      rewrite ccq -[rcons (fcc :: cc') lcc]/([:: fcc] ++ rcons cc' lcc).
      move=>/adjacent_catW[] _.
      by move=> /adjacent_path_nth /(_ jint).
    move: inclj=> /andP[] /andP[] _ B /andP[] abovelow _.
    move: incli=> /andP[] /andP[] /andP[] _ belowhigh C _.
    have vni : valid_edge (high (nth dummy_cell
                   [seq close_cell (point ev) c | c <- rcons cc' lcc] i))
      (nth dummy_pt L i).
      apply/andP; split.
        apply: (le_trans _ (proj1 (andP C))).
        rewrite (nth_map dummy_cell); last by rewrite size_rcons.
        rewrite /left_limit.
        have [_ -> ->] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) i).
        have := allP (sides_ok comi) _ (nth_in _ i_s).
        by move=> /[dup] iok /andP[] lf_size /andP[] xs
        /andP[] _ /andP[] /andP[] _ /andP[] + _ _.
      apply: (le_trans (proj2 (andP C))).
      rewrite (nth_map dummy_cell); last by rewrite size_rcons.
      rewrite right_limit_close_cell //; last first.
          by move: vli; rewrite (nth_map dummy_cell) // size_rcons.
        by apply: vllk.
      have [_ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) i).
      have /andP[ _ ]:= vli.
      by rewrite (nth_map dummy_cell); last by rewrite size_rcons.
    have vnj : valid_edge
      (low (nth dummy_cell
        [seq close_cell (point ev) c | c <- rcons cc' lcc] j))
      (nth dummy_pt L i).
      rewrite abs {C belowhigh abovelow incl}.
      apply/andP; split.
      apply: (le_trans _ (proj1 (andP B))).
      rewrite (nth_map dummy_cell); last by rewrite size_rcons.
        rewrite /left_limit.
        have [-> _ ->] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) j).
        rewrite -/(left_limit (nth _ _ _)).
        have jok : open_cell_side_limit_ok (nth dummy_cell (rcons cc' lcc) j).
          by apply: allP (sides_ok comi) _ (nth_in _ js).
        rewrite -(open_cell_side_limit_ok_last jok).
        move: jok => /andP[] lf_size /andP[] xs
        /andP[] _ /andP[] hdon lston.
        by move: lston=> /andP[] _ /andP[].
      apply: (le_trans (proj2 (andP B))).
      rewrite (nth_map dummy_cell) {B}; last by rewrite size_rcons.
      rewrite right_limit_close_cell //; last first.
          by move: (vlk _ js); rewrite (nth_map dummy_cell) // size_rcons.
        by apply: vllk.
      have [-> _ _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) j).
      by have /andP[ _ ]:= vllk _ js.
    move: abovelow=> /negP; case.
    rewrite -abs.
    have := ij; rewrite jpred ltnS; rewrite leq_eqVlt=> /orP[/eqP ijq| ijp].
      by rewrite -jpred lowjq -ijq.
    have {}ibelj := (ibelj ijp).
    have ibelj' : high (nth dummy_cell
      [seq (close_cell (point ev)) c | c <- rcons cc' lcc] i) <|
        low (nth dummy_cell
          [seq (close_cell (point ev)) c | c <- rcons cc' lcc] j).
    move: ibelj; rewrite lowjq.
    repeat (rewrite (nth_map dummy_cell); last by rewrite size_rcons).
    have [_ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) j.-1).
    by have [_ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc' lcc) i).
    have := order_edges_viz_point vni vnj ibelj'.
    rewrite -jpred; apply.
    by apply: belowhigh.
  move=> i j; rewrite ?inE /= => i_s js eqcc.
  case: (ltnP i j) => [ij | ji].
    have ijint : (i <= j < (size cc').+1)%N by rewrite (ltnW ij) js.
    by apply: (main _ _ ijint).
  have jiint : (j <= i < (size cc').+1)%N by rewrite ji i_s.
  by apply/esym/(main _ _ jiint).
Qed.

Let high_lstc' : high (lst_closed str) = lst_high _ _ str.
Proof.
rewrite strq /= /close_cell.
by rewrite (pvertE vllcc) (pvertE vhlcc).
Qed.

Let nth1lstc' : nth dummy_pt (right_pts (lst_closed str)) 1 = point ev.
Proof.
rewrite strq /= /close_cell.
rewrite (pvertE vllcc) (pvertE vhlcc) /no_dup_seq_aux.
rewrite -![pt_eqb _ _ _ _]/(_ == _).
have main:
  Bpt (p_x (point ev)) (pvert_y (point ev) (high lcc)) = point ev -> False.
  move=> ponhigh.
  move : puh; rewrite heq (strict_nonAunder vhlcc).
  by rewrite -ponhigh (pvert_on vhlcc).
case: ifP=> [/eqP ponhigh | ]; case: ifP=> [/eqP ponlow | pdif] //;
  apply: (main ponhigh).
Qed.

Let nth1_eq' : nth dummy_pt (right_pts (lst_closed str)) 1 =
              nth dummy_pt (left_pts (lst_open str)) 1.
Proof.
by rewrite nth1lstc' strq /= nth1q.
Qed.

Let bottom_left_main :
  {in state_open_seq str, forall c,
    lexePt (bottom_left_corner c) (point ev)}.
Proof.
rewrite strq /state_open_seq /= -!catA -cat_rcons catA.
move=> c; rewrite mem_cat (mem_cat _ _ lc) orbCA.
move=> /orP[cnew | cold]; last first.
  apply: (lexPtW (bottom_left_opens d_inv _ _)); last by [].
  rewrite /state_open_seq /= ocd -cat_rcons mem_cat (mem_cat _ _ lc).
  by rewrite orbCA cold orbT.
by have [] := oks cnew.
Qed.

Let bottom_left_opens' :
       {in state_open_seq str & evs,
         forall c e, lexPt (bottom_left_corner c) (point e)}.
Proof.
move=> c e cin ein.
move: (lex_events comi)=> /=; rewrite (path_sortedE (@lexPtEv_trans _)).
move=> /andP[] /allP /(_ _ ein) + _.
apply: lexePt_lexPt_trans.
by apply: (bottom_left_main cin).
Qed.

Let btm_left_lex_snd_lst' :
      {in state_open_seq str, forall c, lexePt (bottom_left_corner c)
         (nth dummy_pt (left_pts (lst_open str)) 1)}.
Proof.
rewrite [nth _ _ _](_ : _ = (point ev)); last first.
  by rewrite strq /=.
exact: bottom_left_main.
Qed.

Let high_nos_q : [seq high c | c <- nos] = sort edge_below (outgoing ev).
Proof.
have := uoct_eq; rewrite /update_open_cell_top.
case ogq : outgoing => [|fog ogs]; first by move=> -[] <- _.
case oca_eq : opening_cells_aux => [ [ | fno nos'] lno'] -[] <- _.
  have ogn0 : (fog :: ogs) != [::] by [].
  have := opening_cells_aux_absurd_case vlo vhe ogn0.
  by rewrite -ogq => /(_ oute); rewrite ogq oca_eq /=.
have := opening_cells_high vlo vhe oute; rewrite /opening_cells ogq oca_eq.
rewrite map_rcons=> /rcons_inj [] + _.
by rewrite /=.
Qed.

Let uniq_high' : uniq (bottom :: [seq high c | c <- state_open_seq str]).
Proof.
rewrite /=; apply/andP; split.
  rewrite strq /state_open_seq /= catA 2!map_cat mem_cat.
  rewrite (mem_cat _ _ (map _ nos)).
  rewrite -orbA orbCA negb_or.
  have -> /= : bottom \notin [seq high c | c <- nos].
    rewrite high_nos_q mem_sort; apply/negP=> abs.
    have /inside_box_not_on := inbox_e.
    by rewrite -(eqP (oute abs)) left_on_edge.
  apply/negP=> bottomin.
  have := uniq_high d_inv; rewrite /state_open_seq /= ocd=> /andP[] + _.
  rewrite map_cat mem_cat.
  move: bottomin=> /orP[-> | bottomin]; first by [].
  rewrite negb_or => /andP[] _; rewrite map_cat mem_cat /=.
  rewrite negb_or => /andP[] _; rewrite inE.
  move: bottomin; rewrite inE => /orP [ | ->]; last by rewrite orbT.
  by rewrite -heq hiq => ->.
rewrite strq /state_open_seq /= catA 2!map_cat.
rewrite 2!cat_uniq.
have := uniq_high d_inv => /= /andP[] _.
rewrite /state_open_seq ocd map_cat !cat_uniq.
move=> /andP[] ->; rewrite -all_predC => /andP[] /allP /= not2part.
rewrite map_cat cat_uniq=> /andP[] _ /andP[] _ /=.
rewrite -heq -hiq=> /andP[] hlno_nlc ulc.
rewrite ulc andbT.
rewrite (mem_cat (high lno)) !negb_or.
have lccin : lcc \in cc ++ lcc :: lc by rewrite mem_cat inE eqxx orbT.
have := not2part (high lcc) (map_f _ lccin).
rewrite -heq -hiq=> -> /=.
have -> /= : ~~ has (in_mem^~ (mem [seq high c | c <- fop ++ fc']))
  [seq high c | c <- nos].
  rewrite -all_predC; apply/allP=> g gin /=; apply/negP=> gold.
  have := no_dup_edge comi _ evin; rewrite /state_open_seq /=.
  move=> /(_ g).
  rewrite ocd map_cat mem_cat gold=> /(_ isT).
  by move: gin; rewrite high_nos_q mem_sort=> ->.
have -> /= : uniq [seq high c | c <- nos].
  by rewrite high_nos_q sort_uniq; apply: (uniq_ec comi).
have new_diff_old : {in lno :: (fop ++ fc') ++ lc,
  forall c, high c \notin [seq high c | c <- nos]}.
  move=> c cin.
  rewrite high_nos_q mem_sort.
  have lex_left : lexPt (left_pt (high c)) (point ev).
    have [ | ]:= stradle comi; first by [].
    rewrite /state_open_seq/= ocd=> /(_ (high c)).
    have : high c \in [seq high i | i <- (fop ++ fc') ++ cc ++ lcc :: lc].
      move: cin; rewrite inE => /orP[/eqP->| cin].
        by rewrite hiq heq map_f // !mem_cat inE eqxx !orbT.
      rewrite map_f //.
      by move: cin; rewrite !(mem_cat, inE) => /orP[] ->; rewrite ?orbT.
    by move=> /[swap] /[apply] /andP[].
  apply/negP=> inout; move: lex_left; rewrite -(eqP (oute inout)).
  by rewrite lexPt_irrefl.
have -> /= : high lno \notin [seq high c | c <- nos].
  by apply: new_diff_old; rewrite inE eqxx.
rewrite hlno_nlc andbT.
rewrite -all_predC; apply/allP=> g gin /=.
rewrite mem_cat negb_or.
have -> /= : g \notin [seq high i | i <- fop ++ fc'].
  apply/negP=> gin_firsts.
  have /not2part : g \in [seq high i | i <- cc ++ lcc :: lc].
    by rewrite map_cat mem_cat /= inE gin !orbT.
  by rewrite gin_firsts.
move: gin=> /mapP [c cin ->].
suff /new_diff_old : c \in lno :: (fop ++ fc') ++ lc by move=> ->.
by rewrite inE mem_cat cin !orbT.
Qed.

Let lst_side_lt' : left_limit lno <
  Num.min (p_x (right_pt bottom)) (p_x (right_pt top)).
Proof.
have := nth1lstc'.
have := nth1_eq'.
have := (allP (sides_ok (ngcomm common_non_gp_inv_dis'))).
have lnoin : lno \in state_open_seq str.
  by rewrite strq /state_open_seq /= mem_cat inE /= eqxx !orbT.
move=> /(_ lno lnoin); rewrite /open_cell_side_limit_ok.
have := has_snd_lst common_non_gp_inv_dis'.
rewrite strq /state_open_seq /=.
case: (left_pts lno) => [ | a [ | b ?]] //= _.
move=> /andP[] /andP[] _ /andP[] /eqP + _ _.
move=> <- -> ->.
by apply: inside_box_lt_min_right.
Qed.

Lemma last_case_disjoint_invariant_pre :
  disjoint_non_gp_invariant bottom top s
    (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    all_e (rcons past ev) evs.
Proof.
rewrite /step /= /same_x at_lstx eqxx pu (negbTE pa) /=.
rewrite oe uoct_eq.
move: op_cl_dis_non_gp' cl_dis_non_gp'
  common_non_gp_inv_dis' pairwise_open_non_gp'
  closed_at_left_non_gp' size_right_cls'
  uniq_cc' cl_side' high_lstc' nth1_eq' bottom_left_opens'
  btm_left_lex_snd_lst' cell_center_in' uniq_high' lst_side_lt'.
rewrite strq.
constructor=> //.
Qed.

Let edge_covered_ec' : {in rcons past ev, forall e,
       {in outgoing e, forall g,
       edge_covered g (state_open_seq str) (state_closed_seq str)}}.
Proof.
rewrite strq /state_open_seq /state_closed_seq /=.
have cl_sideb : all (@closed_cell_side_limit_ok _) (rcons cls lstc).
  apply/allP; exact (cl_side d_inv).
have bll : bottom_left_cells_lex (fop ++ lsto :: lop) (point ev).
  move=> c cin.
  by apply: (bottom_left_opens d_inv).
have n_in_e : {in fop ++ lsto :: lop, forall c, non_inner (high c) (point ev)}.
  move=> c cin; apply/n_in=> //.
   apply: (edges_sub comi).
   by rewrite mem_cat mem_cat map_f ?orbT.
have [ | stradle_ev] := stradle comi; first by [].
move=> e; rewrite mem_rcons inE=> ein.
have := step_keeps_edge_covering (inbox_events comi) oute rfo cbtom
    adj sval (esym (high_lsto_eq comi)) (lstx_eq comi)
    (fun _ => pal) (sides_ok comi) cl_sideb (size_right_cls d_inv)
    (inj_high ec_inv) bll n_in_e stradle_ev.
rewrite /state_open_seq /state_closed_seq /=.
rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq /==> main.
move:ein=> /orP[/eqP -> | eold].
  by move=> g gin; apply: main; right.
move=> g gin.
have := edge_covered_ec ec_inv eold gin=> ec0.
apply: main; left; exact: ec0.
Qed.

Let top_lstc : point ev = head dummy_pt (right_pts lstc).
Proof.
have /(cl_side d_inv): lstc \in rcons cls lstc.
  by rewrite mem_rcons inE eqxx.
do 5 (move=> /andP[] _); move=> /andP[] + /andP[] + /andP[] _ /andP[] + _.
have := cl_at_lstx d_inv => -> /=.
rewrite at_lstx (high_lstc d_inv) -(high_lsto_eq comi) /=.
case : right_pts => [ | a tl] //= _ /andP[] /eqP ax _ aon.
have := on_edge_same_point aon ponho ax => ay.
by apply/eqP; rewrite pt_eqE ax ay !eqxx.
Qed.

Let processed_covered' : {in rcons past ev, forall e,
       exists2 c, c \in (state_closed_seq str) &
           point e \in (right_pts c : seq pt) /\ point e >>> low c}.
Proof.
move=> e; rewrite mem_rcons inE => /orP[ /eqP -> | eold]; last first.
  have [c cin cP] := (processed_covered ec_inv eold).
  exists c; last by [].
  move: cin; rewrite strq /state_closed_seq /= !mem_rcons !(mem_cat, inE).
  by move=> /orP[] ->; rewrite !orbT.
exists lstc.
  by rewrite strq /state_closed_seq /= !(mem_rcons, mem_cat, inE) eqxx ?orbT.
have lstcin : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
move: (cl_side d_inv lstcin); do 5 (move=> /andP[] _).
have sz : (1 < size (right_pts lstc))%N by apply: (size_right_cls d_inv).
move=> /andP[] _ /andP[] allx /andP[] srt /andP[] hon lon.
have pxh : p_x (head dummy_pt (right_pts lstc)) = right_limit lstc.
  by case: right_pts sz allx => [ | a tl] //= _ /andP[] /eqP -> _.
rewrite top_lstc; split.
  by case: right_pts sz => [ | ? ?] //= _; rewrite inE eqxx.
have lstc_ok := cl_side d_inv lstcin.
rewrite -(closed_cell_side_limit_ok_last lstc_ok) in pxh.
have -> := under_edge_lower_y pxh lon.
rewrite -ltNge.
case : right_pts sz srt => [ | a [ | b tl]] //= _.
rewrite -[_ && _]/(path >%R (p_y a) [seq p_y p | p <- (b :: tl)]).
rewrite (path_sortedE (rev_trans lt_trans))=> /andP[] /allP + _; apply.
by apply/map_f/mem_last.
Qed.

Let non_in_ec' :
      {in s & evs, forall g e, non_inner g (point e)}.
Proof.
move=> g e gin ein.
have ein' : e \in ev :: evs by rewrite inE ein orbT.
by apply: (non_in_ec ec_inv).
Qed.

Let inj_high' : {in state_open_seq str &, injective high}.
Proof.
rewrite strq /state_open_seq.
have bll : bottom_left_cells_lex (fop ++ lsto :: lop) (point ev).
  move=> c cin.
  by apply: (bottom_left_opens d_inv).
have uniq_ev : uniq (outgoing ev) by apply: (uniq_ec comi).
have := step_keeps_injective_high (inbox_events comi) oute rfo cbtom adj sval
  (esym (high_lsto_eq comi)) (fun _ => pal) (sides_ok comi) uniq_ev
  (inj_high ec_inv) bll (map_uniq (proj2 (andP (uniq_high d_inv)))).
move=> /(_ cls lstc lstx).
by rewrite /step/same_x at_lstx eqxx pu (negbTE pa) oe uoct_eq /=.
Qed.

Lemma last_case_edge_covered_invariant_pre :
  edge_covered_non_gp_invariant bottom top s
  all_e (rcons past ev)
  (step (Bscan fop lsto lop cls lstc lsthe lstx) ev) evs.
Proof.
move: last_case_disjoint_invariant_pre.
rewrite /step /same_x at_lstx eqxx pu (negbTE pa) /=.
rewrite oe uoct_eq.
move=> d_inv'.
move: edge_covered_ec' processed_covered' non_in_ec' inj_high'.
rewrite strq.
by constructor.
Qed.

Let left_proc' : {in (rcons past ev),
                   forall e1, lexePt (point e1)
                     (nth dummy_pt (left_pts (lst_open str)) 1)}.
Proof.
move=> e; rewrite mem_rcons inE => /orP[/eqP -> | eold].
  by rewrite strq /= nth1q lexePt_refl.
apply/lexPtW.
rewrite strq /= nth1q.
have := lst_side_lex comng=> /= /andP[] + _.
apply: lexePt_lexPt_trans.
apply: (left_proc ss_inv eold).
Qed.

Let sub_closed' :
      {subset cell_edges (state_closed_seq str) <= bottom :: top :: s}.
Proof.
rewrite strq /state_closed_seq /=.
move=> g; rewrite (cell_edges_eqi to_right_order) cell_edges_cat mem_cat.
move=> /orP[gold | ]; first by apply: (sub_closed ss_inv).
rewrite -cats1 cell_edges_cat mem_cat.
rewrite cell_edges_closing_cells cell_edges_close_cell -mem_cat.
rewrite -cell_edges_cat cats1=> gnew.
apply: (edges_sub comi); rewrite mem_cat /state_open_seq /=.
rewrite ocd -cat_rcons cell_edges_cat mem_cat.
apply/orP; left; apply/orP; right.
rewrite cell_edges_cat mem_cat; apply/orP; left.
move: gnew; apply: mono_cell_edges.
by case: (cc) => [ | a tl] //=; move=> c cin; rewrite inE cin orbT.
Qed.

Let cl_at_left_ss' :
     {in sc_closed str,
        forall c, lexePt (head dummy_pt (right_pts c))
          (nth dummy_pt (left_pts (lst_open str)) 1)}.
Proof.
move=> c.
rewrite strq /state_closed_seq /= nth1q.
rewrite mem_cat=> /orP[ cnew |]; last first.
  rewrite inE=> /orP[/eqP -> | ccls]; last first.
    apply/lexPtW.
    apply: (lexePt_lexPt_trans (cl_at_left_ss ss_inv _)); first by [].
    by have := (lst_side_lex comng) => /andP[] + _.
  rewrite top_lstc.
  by rewrite lexePt_refl.
have := cl_side'; rewrite strq /state_closed_seq /= => /(_ c).
  rewrite to_right_order mem_cat orbC mem_rcons inE cnew orbT => /(_ isT) cok.
suff -> : point ev = head dummy_pt (right_pts c) by apply: lexePt_refl.
move: (cnew)=> /mapP[c' c'in cc'].
have c'in2 : c' \in cc by case: (cc) c'in=> [ | ? ?]; rewrite // inE orbC=> ->.
have [vlc' vhc'] : valid_edge (low c') (point ev) /\
  valid_edge (high c') (point ev).
  by apply/andP/(allP sval); rewrite ocd !mem_cat c'in2 !orbT.
have := open_cells_decomposition_point_on cbtom adj
  (inside_box_between inbox_e) sval oe'.
move=> /(_ c' c'in2).
have [_ <- _]:= close_cell_preserve_3sides (point ev) c'.
rewrite -[X in high X]cc' => ponhc.
move: cok; do 5 (move=> /andP[] _).
move=> /andP[] sz /andP[] allx /andP[] _ /andP[] hon _.
have rlx : right_limit c = p_x (point ev) by rewrite cc' right_limit_close_cell.
have px : p_x (point ev) = p_x (head dummy_pt (right_pts c)).
  by case: right_pts sz allx => [ | ? ?] //= _ /andP[] /eqP -> _.
have := on_edge_same_point ponhc hon px => py.
by apply/eqP; rewrite pt_eqE px py !eqxx.
Qed.

Let lccok : open_cell_side_limit_ok lcc.
Proof.
apply: (allP (sides_ok comi)).
by rewrite /state_open_seq/=ocd !(mem_cat, inE) eqxx !orbT.
Qed.

Let old_edge_cases e g p :
  e \in past -> g \in outgoing e -> p === g ->
  (exists2 c, c \in rcons cls lstc & g = high c /\
  lexePt p (head dummy_pt (right_pts c))) \/
  exists2 c, c \in fop ++ lsto :: lop & g = high c /\
    left_limit c <= p_x p.
Proof.
move=> epast gin pong.
have common_fact c:
  closed_cell_side_limit_ok c ->
  p_x p < right_limit c ->
  lexPt p (head dummy_pt (right_pts c)).
  move=> + xlt.
  do 5 move=> /andP[] _; move=> /andP[].
  rewrite /lexPt.
  case: right_pts => [ | a tl] //= _ /andP[] /andP[] /eqP -> _ _.
  by rewrite xlt.

have := edge_covered_ec ec_inv epast gin => -[].
  move=> -[] oc [pcc [pcccl [hq [cl [oco llpcc]]]]].
  have [ inpcc | inoc ] := ltP (p_x p) (left_limit oc); last first.
    right; exists oc=> //.
    split; last by [].
    by apply/esym/hq; rewrite mem_rcons inE eqxx.
  left.
  have pccn0 : pcc != [::].
    apply/eqP=> pcc0.
    move: llpcc; rewrite pcc0 /= => llpcc.
    move: inpcc; rewrite llpcc ltNge.
    by move: pong=> /andP[] _ /andP[] ->.
  exists (last dummy_cell pcc); first by apply/pcccl/last_in_not_nil.
  split.
    by apply/esym/hq; rewrite mem_rcons inE last_in_not_nil// orbT.
  move: cl; rewrite -cats1.
  case pccq: pcc pccn0 => [ | a tl] //= _; rewrite cat_path=> /andP[] _ /=.
  move=> /andP[] /eqP llq _; rewrite -llq in inpcc.
  have lok : closed_cell_side_limit_ok (last a tl).
    by apply: (cl_side d_inv); apply: pcccl; rewrite pccq mem_last.
  by apply/lexPtW/common_fact.
move=> [pcc [pccn0 [pcccl [hq [cl [llpcc rlpcc]]]]]].
left; exists (last dummy_cell pcc).
  by apply: pcccl; apply: last_in_not_nil.
split.
  by apply/esym/hq/last_in_not_nil.
have : p_x p <= right_limit (last dummy_cell pcc).
  by rewrite rlpcc; move: pong=> /andP[] _ /andP[].
have lok : closed_cell_side_limit_ok (last dummy_cell pcc).
  by apply: (cl_side d_inv); apply: pcccl; rewrite last_in_not_nil.
rewrite le_eqVlt=> /orP[/eqP px | pr]; last first.
  by apply/lexPtW/common_fact.
move: lok; do 5 move=> /andP[] _; move=> /andP[].
case: right_pts => [ | a tl] //= _ /andP[] /andP[] /eqP ax _ /andP[] _ /andP[].
move=> + _.
rewrite /lexePt px ax ltxx eqxx hq /=; last by apply: last_in_not_nil.
move=> aon.
rewrite -px in ax.
by have -> := on_edge_same_point aon pong ax.
Qed.

Let lex_nth1_ev := proj1 (andP (lst_side_lex comng)).

Let pre_evong g : g \in outgoing ev -> point ev === g.
Proof. by move=> /oute /eqP <-; rewrite left_on_edge. Qed.

Let pre_pev p g : p_x p <= p_x (point ev) ->
  g \in outgoing ev -> p === g -> p = point ev.
Proof.
move=> pxle gin pong.
have pxq' : p_x p = p_x (point ev).
  have pxge' : p_x (point ev) <= p_x p.
    by move: pong=> /andP[] _ /andP[]; rewrite (eqP (oute gin)).
  by apply: le_anti; rewrite pxge' pxle.
  have evong : point ev === g by apply: pre_evong.
  apply/eqP; rewrite pt_eqE pxq' eqxx /=.
  by rewrite (on_edge_same_point pong evong pxq') eqxx.
Qed.

Let pnot_old_eq (c : cell):
  c \in state_open_seq str ->
  in_safe_side_left (point ev) c ->
   (c \in rcons nos lno) &&
  ~~ ((c \in (fop ++ fc')) || (c \in lc)).
Proof.
rewrite /state_open_seq/= strq /= -!catA -cat_rcons  catA mem_cat.
rewrite (mem_cat _ _ lc) orbCA.
case cold : ((c \in (fop ++ fc')) || (c \in lc)); last first.
  by rewrite orbF andbT.
have cino : c \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons mem_cat (mem_cat _ _ lc) orbCA cold orbT.
  have [vlc vhc] : valid_cell c (point ev).
    by apply/andP/(allP sval).
move=> _ pin.
 have notabove : ~~(c \in lc).
  apply/negP=> cl.
  have pac : point ev >>> low c.
    by move: pin=>  /andP[] _ /andP[] _ /andP[].
  have cahe : he <| low c.
  have [s1 [s2 sq]] := mem_seq_split cl.
  have lcq : low c = high (last lcc s1).
    move: adj; rewrite /state_open_seq/= ocd sq.
    rewrite -!catA 2!catA=> /adjacent_catW[] _ /=.
    by rewrite cat_path=> /andP[] _ /= /andP[] /eqP.
  rewrite lcq.
  have := pairwise_open_non_gp d_inv.
  rewrite /= /state_open_seq/= ocd => /andP[] _.
    rewrite -catA sq !catA.
    rewrite !map_cat pairwise_cat => /andP[] _ /andP[] _ /= /andP[] + _.
    case: (s1) => [ _ | a tl].
      by rewrite /= heq edge_below_refl.
    move=> /allP /(_ (high (last a tl)) (map_f _ _)).
    by rewrite mem_cat mem_last heq => /(_ isT).
  have /underW puc := order_edges_strict_viz_point vhe vlc cahe puh.
by rewrite puc in pac.
have notbelow : ~~(c \in fop ++ fc').
  apply/negP=> cf.
  have puc : point ev <<< high c.
    by move: pin => /andP[] _ /andP[].
  have cble : high c <| le.
    have [s1 [s2 sq]] := mem_seq_split cf.
    have leq' : le = high (last c s2).
      rewrite leq.
      have := adj; rewrite /state_open_seq/= ocd -cat_rcons.
      rewrite sq !catA=> /adjacent_catW[] + _.
      rewrite -!catA=> /adjacent_catW[] _ /= +.
      rewrite cat_path=> /andP[] _.
      by case: (cc)=> [ | a tl] /= /andP[] /eqP ->.
    rewrite leq'.
    have := pairwise_open_non_gp d_inv.
    rewrite /= /state_open_seq/= ocd => /andP[] _.
    rewrite -cat_rcons sq !catA.
    rewrite !map_cat pairwise_cat => /andP[] _.
    rewrite pairwise_cat=> /andP[] /andP[] _ /andP[] + _ _.
    rewrite pairwise_cat=> /andP[] _ /andP[] _ /= /andP[] + _.
    case: (s2) => [ | a tl]; first by rewrite edge_below_refl.
    by move=> /allP /(_ (high (last a tl)) (map_f _ (mem_last _ _))).
  have pul := order_edges_strict_viz_point vhc vle cble puc.
  have /all_ctn/andP[+ _]: head lcc cc \in cc.
    by case: (cc) ccn0 => [ | ? ?]; rewrite // inE eqxx.
by rewrite -leq pul.
by move: cold; rewrite (negbTE notabove) (negbTE notbelow).
Qed.

Let pnot_old p g (c : cell):
  g \in outgoing ev ->
  p === g ->
  c \in state_open_seq str ->
  in_safe_side_left p c ->
  (c \in rcons nos lno) &&
  ~~ ((c \in (fop ++ fc')) || (c \in lc)).
Proof.
move=> gin pong /[dup] startcin.
rewrite /state_open_seq/= strq /= -!catA -cat_rcons  catA mem_cat.
rewrite (mem_cat _ _ lc) orbCA.
case cold : ((c \in (fop ++ fc')) || (c \in lc)); last first.
  by rewrite orbF andbT.
move=> _ pin.
have cino : c \in fop ++ lsto :: lop.
  by rewrite ocd -cat_rcons mem_cat (mem_cat _ _ lc) orbCA cold orbT.
have [vlc vhc] : valid_cell c (point ev).
  by apply/andP/(allP sval).
have cok : open_cell_side_limit_ok c.
  by apply: (allP sides_ok').
have xle : p_x p <= p_x (point ev).
  have := bottom_left_opens d_inv cino evin.
  rewrite /lexPt -(bottom_left_x cok).
  by move: pin => /andP[] /eqP <- _ => /orP[/ltW | /andP[] /eqP -> _].
have pev : p = point ev.
  by apply: (pre_pev xle gin).
rewrite pev in pin.
by have := pnot_old_eq startcin pin; rewrite cold.
Qed.

Let safe_side_closed :
     {in rcons past ev & state_closed_seq str, forall e c p g,
      in_safe_side_left p c || in_safe_side_right p c ->
      (g \in outgoing e ->
          ~ p === g) /\ p != point e}.
Proof.
move=> e c ein cin p g pin.
 (* gin pong. *)
(* When the edge is new, the only way to be in a safe side and on this
  edge is to be the current event's point *)
have pev' : p === g -> g \in outgoing ev -> p = point ev.
  move=> pong gnew.
  have pxle' : p_x p <= p_x (point ev).
     have rcev : right_limit c <= p_x (point ev).
      by have := closed_at_left_non_gp'=> /(_ c cin); rewrite strq.
    move: pin=> /orP[] /andP[] /eqP -> _; last by rewrite rcev.
    have := cl_large last_case_disjoint_invariant_pre.
    rewrite /state_closed_seq /= /step/same_x at_lstx eqxx pu (negbTE pa) /=.
    rewrite oe /= => /(_ c cin)=> lcltrc.
    by apply/ltW/(lt_le_trans _ rcev).
  by apply: (pre_pev pxle' gnew pong).
have no_lstc1 w : w = lstc ->
  lexePt p (head dummy_pt (right_pts w)) -> ~ lexPt (point ev) p.
  by move=> ->; rewrite -top_lstc lexPtNge=> it; apply/negP;rewrite negbK.
have no_lstc : c = lstc -> p != point ev.
  move=> clstc.
  have lstcin : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
  move: pin; rewrite clstc=> pin.
  have := in_safe_side_top_right (cl_side d_inv lstcin)
      (cl_large d_inv lstcin) pin.
  rewrite -top_lstc=> p_ev.
  by apply/eqP=> it; rewrite it lexPt_irrefl in p_ev.
have no_cls_pre w : w \in cls ->
    lexePt (point ev) p -> ~ lexePt p (head dummy_pt (right_pts w)).
    move=> /(cl_at_left_ss ss_inv) P1 ev_p P2.
    have := lexePt_trans P2 P1 => /= P3.
    have := lexePt_lexPt_trans P3 (proj1 (andP (lst_side_lex comng)))=> P4.
    by have := lexPt_lexePt_trans P4 ev_p; rewrite lexPt_irrefl.
move: ein.
rewrite mem_rcons inE=> /orP [/eqP -> | epast]; last first.
  (* the edge is old. *)
  move: (cin); rewrite /state_closed_seq /= strq to_right_order mem_cat.
  move=> /orP[cold | ].
    (* the cell is also old. *)
    have gin' : g \in outgoing e -> g \in events_to_edges past.
      by move=> gin; apply/flatten_mapP; exists e.
    split; last first.
      by apply: (safe_side_closed_points ss_inv epast cold pin).
    move=> gin pong.
    by apply:(safe_side_closed_edges ss_inv (gin' gin) cold pin pong).
  (* the cell is new. *)
  rewrite -map_rcons=> /mapP[c' c'in cc'].
  have cok := cl_side' cin.
  have c'ino : c' \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons !mem_cat (rcbehead_sub c'in) !orbT.
  move: pin=> /orP[ | pin].
    rewrite cc' in_safe_side_left_close_cell => oldpin.
    split; last first.
      by apply: (safe_side_open_points ss_inv epast c'ino oldpin).
    move=> gin pong.
    have := safe_side_open_edges ss_inv _ c'ino oldpin pong; apply.
    by apply/flatten_mapP; exists e.
  move: c'in; rewrite mem_rcons inE => /orP[/eqP c'lcc | c'in]; last first.
    case ccq : cc ccn0 => [ | fcc cctl] //= _.
    have := middle_closing_side_char (inbox_events comi) rfo cbtom adj sval p.
    rewrite oe' ccq=> /(_ _ _ _ _ _ _ _ erefl) /negP; elim; apply/hasP.
    exists (close_cell (point ev) c'); last by rewrite -cc' pin.
    by rewrite map_f //; move: c'in; rewrite ccq.

  have /esym := last_closing_side_char (inbox_events comi) rfo cbtom adj
      sval p oe' ccn0 => facts.
  move: (facts); rewrite -c'lcc -cc' pin=> /andP[] px /andP[] py _.
  have px' := eqP px.
  have ev_p : lexPt (point ev) p by rewrite /lexPt eq_sym px py orbT.
  have no_cls_pre' w : w \in cls -> ~ lexePt p (head dummy_pt (right_pts w)).
    move=> wcls.
    have ev_p' : lexePt (point ev) p by apply/lexPtW.
    exact: (no_cls_pre _ wcls ev_p').
  split; last first.
    have := left_proc ss_inv epast; rewrite /= => e_nth1.
    have := lst_side_lex comng => /= /andP[] => nth1_ev _.
    apply/eqP=> pise.
    have := lexePt_lexPt_trans e_nth1 nth1_ev => e_ev.
    have := lexPt_trans e_ev ev_p.
    by rewrite pise lexPt_irrefl.
  move=> gin pong.
  have [[cl1 + [hcl1 p_tcl1]] | ]:= old_edge_cases epast gin pong.
    rewrite mem_rcons inE => /orP[/eqP cl1q| incls ].
      by have := no_lstc1 cl1 cl1q p_tcl1 ev_p.
    by have := no_cls_pre' _ incls p_tcl1.
  move=> [oc oco [hoc p_oc]].
  (* TODO: large duplication. *)
  have vc' : valid_cell c' (point ev) by apply/andP/(allP sval).
  have [vlc'p vhc'p] : valid_edge (low c') p /\ valid_edge (high c') p.
    by move: vc'; rewrite /valid_cell !(same_x_valid _ px').
  have {}opch : g = high oc by apply/esym.
  have [vplc vphc] : valid_edge (low oc) p /\ valid_edge (high oc) p.
    by rewrite !(same_x_valid _ px'); apply/andP/(allP sval).
  have pw : pairwise edge_below [seq high c | c <- fop ++ lsto :: lop].
    by move: (pairwise_open_non_gp d_inv)=> /= /andP[].
  have [puhc' palc'] : p <<< high c' /\ p >>> low c'.
    apply/andP;  move: pin=> /andP[] _ /andP[] + /andP[] + _.
    rewrite cc'.
    by have [-> -> _] := close_cell_preserve_3sides (point ev) c' => ->.
  have sb := edges_sub comi.
  have hc's : high c' \in [:: bottom, top & s].
    by apply: sb; rewrite !mem_cat map_f ?orbT.
  have hos : high oc \in [:: bottom, top & s].
    by apply: sb; rewrite !mem_cat map_f ?orbT.
  have balt : below_alt (high c') (high oc).
    by apply: (inter_at_ext_no_crossing nocs').
  have pabo : p >>= high oc by rewrite strict_nonAunder // -opch pong.
  have opcNab : ~~ (high c' <| high oc).
    apply/negP=> c'bo.
    have := order_edges_strict_viz_point vhc'p vphc c'bo puhc'.
    by rewrite strict_nonAunder // -opch pong.
  have hobhc' := edge_below_from_point_above balt vhc'p vphc.
  have [s1 [s2 sq]] := mem_seq_split c'ino.
  have opcs1 : oc \in s1.
    move: oco; rewrite sq mem_cat=> /orP[]; first by [].
    rewrite inE => /orP[/eqP opcc' | opcs2].
      by case/negP: pabo; rewrite opcc'.
    case/negP: opcNab.
    move: (pw); rewrite sq map_cat pairwise_cat => /andP[] _ /andP[] _.
    by move=> /andP[] /allP /(_ _ (map_f _ opcs2)).
  have opcbl : high oc <| low c'.
    have [s3 [s4 s1q]] := mem_seq_split opcs1.
    elim/last_ind : {-1}(s4) (erefl s4) => [ | s4' c2 _] s4q.
      move: adj; rewrite sq s1q s4q -catA /= => /adjacent_catW[] _ /=.
      by move=> /andP[] /eqP -> _; apply: edge_below_refl.
    have hc2 : high c2 = low c'.
      move: adj.
      rewrite sq s1q s4q /= -catA /= => /adjacent_catW[] _ /adjacent_cons.
      by rewrite cat_rcons => /adjacent_catW[] _ /= /andP[] /eqP.
    move: pw; rewrite sq s1q s4q /= -catA !map_cat /=.
    rewrite pairwise_cat /= => /andP[] _ /andP[] _ /andP[] + _.
    rewrite all_cat map_rcons all_rcons => /andP[] /andP[] + _ _.
    by rewrite hc2.
  case/negP: palc'.
  apply: (order_edges_viz_point vphc vlc'p opcbl).
  by rewrite under_onVstrict // -opch pong.

(* have pev : p === g -> g \in outgoing ev -> p = point ev.
  by move=> pong gnew; apply : (pev' pong gnew). *)
move: cin; rewrite /state_closed_seq/= strq to_right_order=> /[dup] oldcin.
rewrite mem_cat => /orP[cin| cnew].
  have cok := cl_side d_inv cin.
  have pnev : p != point ev.
    apply/eqP=> pev.
    move: (cin).
    rewrite mem_rcons inE => /orP [/eqP clstc | incls]; last first.
      have lexep : lexePt (point ev) p.
        by rewrite pev lexePt_refl.
      have := no_cls_pre _ incls lexep.
      by have /lexPtW -> := in_safe_side_top_right cok (cl_large d_inv cin) pin.
    by have := no_lstc clstc; rewrite pev eqxx.
  split; last by[].
  by move=> gnew pong; rewrite (pev' pong gnew) eqxx in pnev.

have := cl_large last_case_disjoint_invariant_pre.
rewrite /step /same_x at_lstx eqxx pu (negbTE pa) oe uoct_eq /=.
move/(_ c); rewrite /state_closed_seq/= to_right_order=> /(_ oldcin) lcltrc.
move: (cnew); rewrite -map_rcons=> /mapP[c' /[dup] c'in /rcbehead_sub c'in2].
move=> cc'.
have c'ino : c' \in fop ++ lsto :: lop.
  by rewrite ocd -cat_rcons !mem_cat c'in2 !orbT.
have vc' : valid_cell c' (point ev).
  by apply/andP/(allP sval).
have [vlc' vhc'] := vc'.
have rlc := close_cell_right_limit vc'.
rewrite -cc' in rlc.
move: (pin); rewrite cc'=> pin'.
move: lcltrc; rewrite cc'.
rewrite /left_limit.
have [_ _ ->] := close_cell_preserve_3sides (point ev) c'.
rewrite -/(left_limit c').
rewrite -cc' rlc=> lcltev.
have := in_safe_side_close_cell_diff vlc' vhc' lcltev pin'.
move=> pnev; split; last by [].
by move=> gnew pong; move: pnev; rewrite (pev' pong gnew) eqxx.
Qed.

Let safe_side_closed_edges' :
  {in events_to_edges (rcons past ev) &
    state_closed_seq str,
    forall g c p, in_safe_side_left p c || in_safe_side_right p c ->
    ~ p === g}.
Proof.
move=> g c /flatten_mapP [e ein gin] cin p pin.
have [main _]:= safe_side_closed ein cin g pin.
by apply: main.
Qed.

Let ponllcc : point ev === low lcc.
Proof.
have -> : low lcc = high (last dummy_cell cc).
  move: adj; rewrite ocd=> /adjacent_catW[] _.
  case: (cc) ccn0 => [ | a tl] //= _.
  by rewrite cat_path=> /andP[] _ /= /andP[] /eqP ->.
have lin : last dummy_cell cc \in cc by apply last_in_not_nil.
have := open_cells_decomposition_point_on cbtom adj
  (inside_box_between inbox_e) sval oe' lin.
by [].
Qed.

Let allo fno nos' lno' c':
  opening_cells_aux (point ev) (sort edge_below (outgoing ev)) (low lsto) he =
  (fno :: nos', lno')->
  c' \in fno :: nos' -> high c' \in outgoing ev.
Proof.
move=> oca_eq c'in.
rewrite -(mem_sort edge_below).
have := opening_cells_high vlo vhe oute; rewrite /opening_cells oca_eq.
rewrite map_rcons=> /rcons_inj[] <- _.
move: c'in; rewrite inE => /orP[/eqP -> | c'nos']; first by rewrite inE eqxx.
by rewrite inE map_f ?orbT.
Qed.

Let new_open_cells_pnev p (c : cell) :
  in_safe_side_left p c ->
  c \in rcons nos lno ->
  p != point ev.
Proof.
move=> pin cnew.
  apply/eqP=> pev.
  move: uoct_eq; rewrite /update_open_cell_top.
  have [og0 | ogn0] := eqVneq (outgoing ev) [::].
    rewrite og0 => -[] /esym nosq /esym lnoq.
    move: cnew; rewrite nosq lnoq /= inE => /eqP cnew.
    move: pin; rewrite pev p_topleft_lsto cnew.
    move=> /andP[] _ /andP[] _ /andP[] _ /=.
    move: lstok => /andP[] + _.
    by case: left_pts=> [ | a tl] //= _; rewrite !inE eqxx !orbT.
  case ogq : outgoing (ogn0) => [ | fog ogs] // _; rewrite -ogq.
  have := opening_cells_aux_absurd_case vlo vhe ogn0 oute.
  case oca_eq : opening_cells_aux => [[ | fno nos'] lno'] // _ -[] /esym nosq.
  move=> /esym lnoq.
  have := opening_cells_in vlo vhe oute; rewrite /opening_cells oca_eq.
  move=> evinpts.
  move: pin=> /andP[] _ /andP[] _ /andP[] _.
  move: cnew; rewrite mem_rcons inE => /orP[/eqP clno | ].
    by rewrite clno pev lnoq evinpts // mem_rcons inE eqxx.
  rewrite nosq inE => /orP[/eqP cfno| cnos'].
    by rewrite cfno left_pts_set inE pev eqxx.
  by rewrite pev evinpts // mem_rcons !inE cnos' !orbT.
Qed.

Let safe_side_open_edges' :
     {in events_to_edges (rcons past ev) & state_open_seq str, forall g c p,
         in_safe_side_left p c -> ~p === g}.
Proof.
move=> g c gin /[dup] startcin + p pin pong; rewrite strq /state_open_seq /=.
move=> /[dup] oldcin.
have cok : open_cell_side_limit_ok c.
  by apply: (allP sides_ok'); rewrite strq.
rewrite catA -catA -cat_rcons mem_cat (mem_cat _ _ lc) orbCA orbC.
move=> /orP [cold | cnew].
  move: gin; rewrite /events_to_edges => /flattenP[ogs].
  move=> /mapP[e + ->].
  rewrite mem_rcons inE=> /orP [/eqP -> gin | ]; last first.
    move=> epast gin; apply: (safe_side_open_edges ss_inv _ _ pin pong)=> //.
      by apply/flatten_mapP; exists e.
    rewrite /state_open_seq/= ocd -cat_rcons mem_cat (mem_cat _ _ lc) orbCA.
    by rewrite cold orbT.
  have cino : c \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons mem_cat (mem_cat _ _ lc) orbCA cold orbT.
  have [vlc vhc] : valid_cell c (point ev).
    by apply/andP/(allP sval).
  have xle : p_x p <= p_x (point ev).
    have := bottom_left_opens d_inv cino evin.
    rewrite /lexPt -(bottom_left_x cok).
    by move: pin => /andP[] /eqP <- _ => /orP[/ltW | /andP[] /eqP -> _].
  have pev : p = point ev.
    by apply: (pre_pev xle gin).
  have := pnot_old gin pong startcin pin.
  by rewrite cold andbF.
have pnev : p != point ev.
  by have := new_open_cells_pnev pin cnew.
move: gin=> /[dup] oldgin /flatten_mapP[e /[dup] ein].
rewrite mem_rcons inE=>/orP[/eqP -> | epast] gin.
  have pev : p = point ev.
    have xle : p_x p <= p_x (point ev).
      move: pin=> /andP[] /eqP -> _.
      by have [ _ -> _] := oks cnew.
    by apply:(pre_pev xle gin pong).
  by rewrite pev eqxx in pnev.
move: (uoct_eq); rewrite /update_open_cell_top.
case ogq : outgoing => [ | fog ogs].
  move=> -[] /esym nosq /esym lnoq.
  move: cnew; rewrite nosq lnoq /= inE => /eqP cq.
  move: pin; rewrite cq /in_safe_side_left /=.
  move=> /andP[] /eqP px /andP[] puhe /andP[] palsto.
  have px' : p_x p = p_x (point ev).
    rewrite px at_ll /left_limit /=.
    by case: left_pts (has_snd_lst comng) => [ | a tl].
  rewrite /= inE negb_or=> /andP[] pnoth pnllsto.
  have gin' : g \in events_to_edges past.
    by apply/flatten_mapP; exists e.
  have [above | below] := ltP (p_y (point ev)) (p_y p).
    have sfnewlstc : in_safe_side_right p (close_cell (point ev) lcc).
      apply/andP; split.
        by rewrite right_limit_close_cell // px'.
      have [-> -> _] := close_cell_preserve_3sides (point ev) lcc.
      rewrite -heq puhe.
      rewrite (under_edge_lower_y px' ponllcc).
      rewrite -ltNge above /=.
      rewrite /close_cell (pvertE vllcc) (pvertE vhlcc).
      rewrite -no_dup_seq_aux_eq mem_no_dup_seq.
      rewrite -heq !inE; apply/negP=> /orP[/eqP | /orP[] /eqP] pon.
          have vphe : valid_edge he p by rewrite (same_x_valid he px').
          have := pvert_on vphe; rewrite px' (same_pvert_y vphe px') => abs.
          by have := puhe; rewrite (strict_nonAunder vphe) pon abs.
        by move: above; rewrite pon ltxx.
      by rewrite (on_pvert ponllcc) in pon; rewrite pon ltxx in above.
    have cllccin : close_cell (point ev) lcc \in state_closed_seq str.
      by rewrite strq to_right_order mem_cat !mem_rcons !inE eqxx !orbT.
    have := safe_side_closed_edges' oldgin cllccin _ pong.
    by rewrite sfnewlstc orbT => /(_ isT).
  have {}below : p_y p < p_y (point ev).
    move: below; rewrite le_eqVlt=> /orP[/eqP py|]; last by [].
    case/negP: pnev.
    by rewrite pt_eqE px' py !eqxx.
  have pbhlsto : p <<< high lsto.
    by rewrite (strict_under_edge_lower_y px' ponho).
  have psafelsto : in_safe_side_left p lsto.
    by rewrite /in_safe_side_left px' at_ll eqxx pbhlsto palsto pnllsto.
  by have := (safe_side_open_edges ss_inv gin' lstoin psafelsto pong).
have ogn0 : outgoing ev != [::] by rewrite ogq.
rewrite -ogq.
have := opening_cells_aux_absurd_case vlo vhe ogn0 oute.
case oca_eq: opening_cells_aux => [ [ |fno nos'] lno'] // _ [].
move=> /esym nosq /esym lnoq.
have px' : p_x p = p_x (point ev).
  move: cnew; rewrite mem_rcons inE=> /orP[/eqP clno | cnos].
    move: pin; rewrite clno lnoq /in_safe_side_left.
    have := opening_cells_left oute vlo vhe=> ->; last first.
      by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
    by move=> /andP[] /eqP ->.
  move: pin=> /andP[] /eqP -> _.
  move: cnos; rewrite nosq inE => /orP[/eqP cfno | cnos'].
    rewrite cfno at_ll /left_limit left_pts_set.
    exact: at_ll.
  have := opening_cells_left oute vlo vhe=> -> //.
  by rewrite /opening_cells oca_eq mem_rcons !inE cnos' !orbT.
move: cnew; rewrite mem_rcons inE => /orP[/eqP clno |].
  move: (pin); rewrite clno /in_safe_side_left /=.
  move=> /andP[] /eqP px /andP[] puhe /andP[] palsto pnotinlno.
  have sfnewlstc : in_safe_side_right p (close_cell (point ev) lcc).
    apply/andP; split.
      by rewrite right_limit_close_cell // px'.
    have [-> -> _] := close_cell_preserve_3sides (point ev) lcc.
    rewrite -heq -hiq puhe.
    have pygtev : p_y (point ev) < p_y p.
      have lowlnoin : low lno \in outgoing ev.
        have := opening_cells_high vlo vhe oute; rewrite /opening_cells oca_eq.
        have := opening_cells_seq_edge_shift oute' vlo vhe; rewrite oca_eq.
        move=> /(_ _ _ erefl) /= [] _ -> => /rcons_inj[] main.
        have : low lno' \in [seq low i | i <- rcons nos' lno'].
          by apply:map_f; rewrite mem_rcons inE eqxx.
        by rewrite main mem_sort lnoq.
      have evonllno : point ev === low lno.
        by rewrite -(eqP (oute lowlnoin)) left_on_edge.
      move: palsto.
      have -> := (under_edge_lower_y px' evonllno).
      by rewrite -ltNge.
    have -> := (under_edge_lower_y px' ponllcc); rewrite -ltNge pygtev.
    rewrite /close_cell (pvertE vllcc) (pvertE vhlcc) -no_dup_seq_aux_eq.
    rewrite mem_no_dup_seq !inE (negbTE pnev) /=.
    apply/negP=>/orP[] /eqP pon.
      have vphe : valid_edge he p by rewrite (same_x_valid he px').
      have := pvert_on vphe; rewrite px' (same_pvert_y vphe px') => abs.
      have := puhe; rewrite hiq.
      by rewrite (strict_nonAunder vphe) pon -heq abs.
    rewrite (on_pvert ponllcc) in pon.
    by rewrite pon pt_eqE /= !eqxx in pnev.
  have ginnew : g \in events_to_edges (rcons past ev).
    by apply/flatten_mapP; exists e; rewrite // mem_rcons inE epast orbT.
  have cinnew : close_cell (point ev) lcc \in state_closed_seq str.
    rewrite /state_closed_seq strq to_right_order mem_cat !mem_rcons !inE eqxx.
    by rewrite !orbT.
  have := safe_side_closed_edges' ginnew cinnew _ pong.
  by rewrite sfnewlstc orbT; apply.
rewrite nosq inE=> /orP[/eqP cfno | cnos'].
  have plsto : in_safe_side_left p lsto.
    rewrite /in_safe_side_left.
    rewrite px' at_ll eqxx /=.
    have -> /= : p <<< high lsto.
      have evonf : point ev === high fno.
        have fnoo := allo oca_eq (mem_head fno nos').
        by rewrite -(eqP (oute fnoo)) left_on_edge.
      have := pin=> /andP[] _ /andP[] + _.
      have := strict_under_edge_lower_y px' evonf; rewrite cfno /= => -> yplt.
      by rewrite (strict_under_edge_lower_y px' ponho).
    have -> /= : p >>> low lsto.
      have /= := opening_cells_seq_edge_shift oute' vlo vhe oca_eq.
      move=> -[] -> _.
      by move: pin=> /andP[] _ /andP[] _ /andP[]; rewrite cfno.
    have -> /= : p \notin left_pts lsto.
      move: pin=> /andP[] _ /andP[] _ /andP[] _; rewrite cfno /=.
      move: lstok=> /andP[] + _.
      by rewrite p_topleft_lsto; case: left_pts => [ | ? ?].
    by [].
  rewrite p_topleft_lsto in cfno.
  have ginold : g \in events_to_edges past.
    by apply/flatten_mapP; exists e.
  by have := safe_side_open_edges ss_inv ginold lstoin plsto pong.
suff : ~ in_safe_side_left p c by rewrite pin.
have cnos : c \in fno :: nos' by rewrite inE cnos' orbT.
have hco : high c \in outgoing ev.
  by move: (allo oca_eq cnos).
have lco : low c \in outgoing ev.
  have [s1 [s2 sq]] := mem_seq_split cnos'.
  have : adjacent_cells (rcons nos lno).
  have := inv1'; rewrite /state_open_seq/= strq /= => -[] _ [] _ [] + _.
  by rewrite -!catA -cat_rcons catA => /adjacent_catW[] _ /adjacent_catW[].
  rewrite -cats1=> /adjacent_catW[] + _.
  rewrite nosq /= sq cat_path=> /andP[] _ /= /andP[] /eqP <- _.
  case s1q : s1 => [ | fs1 s1'] /=.
    by apply: (allo oca_eq); rewrite inE eqxx.
  by apply: (allo oca_eq); rewrite sq s1q inE mem_cat mem_last !orbT.
have ponl : point ev === low c.
  by rewrite -(eqP (oute lco)) left_on_edge.
have ponh : point ev === high c.
  by rewrite -(eqP (oute hco)) left_on_edge.
move=> /andP[] _ /andP[] puhc /andP[] palc _.
rewrite (under_edge_lower_y px' ponl) in palc.
rewrite (strict_under_edge_lower_y px' ponh) in puhc.
by rewrite (ltW puhc) in palc.
Qed.

Let safe_side_closed_points' :
     {in (rcons past ev) & state_closed_seq str, forall e c p,
         in_safe_side_left p c || in_safe_side_right p c ->
         p != point e :> pt}.
Proof.
move=> e c ein cin p pin.
by have [_ main]:= safe_side_closed ein cin dummy_edge pin.
Qed.

Let safe_side_open_points' :
     {in (rcons past ev) & state_open_seq str, forall e c p,
         in_safe_side_left p c ->
         p != point e :> pt}.
Proof.
move=> e c /[dup] ein ein' /[dup] startcin; rewrite strq /state_open_seq /=.
rewrite catA -catA -cat_rcons mem_cat (mem_cat _ _ lc) orbCA orbC.
move=> /orP [cold | cnew].
  move: ein'; rewrite mem_rcons inE=> /orP [/eqP -> | ]; last first.
    move=> epast; apply: (safe_side_open_points ss_inv) => //.
    rewrite /state_open_seq ocd -cat_rcons mem_cat (mem_cat _ _ lc) orbCA orbC.
    by rewrite cold.
  move=> p pin; apply/eqP=> pev.
  rewrite pev in pin.
  by have := pnot_old_eq startcin pin; rewrite cold andbF.
move=> p pin; apply/eqP=> pise {startcin}.
have pnev : p != point ev.
  by have := new_open_cells_pnev pin cnew.
move: ein'; rewrite mem_rcons inE => /orP[/eqP eev | epast].
  by rewrite pise eev eqxx in pnev.
move: (uoct_eq); rewrite /update_open_cell_top.
case ogq : outgoing => [ | fog ogs].
  move=> -[] /esym nosq /esym lnoq.
  move: cnew; rewrite nosq lnoq /= inE => /eqP cq.
  move: pin; rewrite cq /in_safe_side_left /=.
  move=> /andP[] /eqP px /andP[] puhe /andP[] palsto.
  have px' : p_x p = p_x (point ev).
    rewrite px at_ll /left_limit /=.
    by case: left_pts (has_snd_lst comng) => [ | a tl].
  rewrite /= inE negb_or=> /andP[] pnoth pnllsto.
  have [above | below] := ltP (p_y (point ev)) (p_y p).
    have sfnewlstc : in_safe_side_right p (close_cell (point ev) lcc).
      apply/andP; split.
        by rewrite right_limit_close_cell // px'.
      have [-> -> _] := close_cell_preserve_3sides (point ev) lcc.
      rewrite -heq puhe.
      rewrite (under_edge_lower_y px' ponllcc).
      rewrite -ltNge above /=.
      rewrite /close_cell (pvertE vllcc) (pvertE vhlcc).
      rewrite -no_dup_seq_aux_eq mem_no_dup_seq.
      rewrite -heq !inE; apply/negP=> /orP[/eqP | /orP[] /eqP] pon.
          have vphe : valid_edge he p by rewrite (same_x_valid he px').
          have := pvert_on vphe; rewrite px' (same_pvert_y vphe px') => abs.
          by have := puhe; rewrite (strict_nonAunder vphe) pon abs.
        by move: above; rewrite pon ltxx.
      by rewrite (on_pvert ponllcc) in pon; rewrite pon ltxx in above.
    have cllccin : close_cell (point ev) lcc \in state_closed_seq str.
      by rewrite strq to_right_order mem_cat !mem_rcons !inE eqxx !orbT.
    (* have ein : e \in rcons past ev by rewrite mem_rcons inE epast orbT.  *)
    have := safe_side_closed_points' ein cllccin=> /(_ p).
    by rewrite sfnewlstc orbT pise eqxx => /(_ isT).
  have {}below : p_y p < p_y (point ev).
    move: below; rewrite le_eqVlt=> /orP[/eqP py|]; last by [].
    case/negP: pnev.
    by rewrite pt_eqE px' py !eqxx.
  have pbhlsto : p <<< high lsto.
    by rewrite (strict_under_edge_lower_y px' ponho).
  have psafelsto : in_safe_side_left p lsto.
    by rewrite /in_safe_side_left px' at_ll eqxx pbhlsto palsto pnllsto.
  have := (safe_side_open_points ss_inv epast lstoin psafelsto).
  by rewrite pise eqxx.
have ogn0 : outgoing ev != [::] by rewrite ogq.
rewrite -ogq.
have := opening_cells_aux_absurd_case vlo vhe ogn0 oute.
case oca_eq: opening_cells_aux => [ [ |fno nos'] lno'] // _ [].
move=> /esym nosq /esym lnoq.
have px' : p_x p = p_x (point ev).
  move: cnew; rewrite mem_rcons inE=> /orP[/eqP clno | cnos].
    move: pin; rewrite clno lnoq /in_safe_side_left.
    have := opening_cells_left oute vlo vhe=> ->; last first.
      by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
    by move=> /andP[] /eqP ->.
  move: pin=> /andP[] /eqP -> _.
  move: cnos; rewrite nosq inE => /orP[/eqP cfno | cnos'].
    rewrite cfno at_ll /left_limit left_pts_set.
    exact: at_ll.
  have := opening_cells_left oute vlo vhe=> -> //.
  by rewrite /opening_cells oca_eq mem_rcons !inE cnos' !orbT.
move: cnew; rewrite mem_rcons inE => /orP[/eqP clno |].
  move: (pin); rewrite clno /in_safe_side_left /=.
  move=> /andP[] /eqP px /andP[] puhe /andP[] palsto pnotinlno.
  have sfnewlstc : in_safe_side_right p (close_cell (point ev) lcc).
    apply/andP; split.
      by rewrite right_limit_close_cell // px'.
    have [-> -> _] := close_cell_preserve_3sides (point ev) lcc.
    rewrite -heq -hiq puhe.
    have pygtev : p_y (point ev) < p_y p.
      have lowlnoin : low lno \in outgoing ev.
        have := opening_cells_high vlo vhe oute; rewrite /opening_cells oca_eq.
        have := opening_cells_seq_edge_shift oute' vlo vhe; rewrite oca_eq.
        move=> /(_ _ _ erefl) /= [] _ -> => /rcons_inj[] main.
        have : low lno' \in [seq low i | i <- rcons nos' lno'].
          by apply:map_f; rewrite mem_rcons inE eqxx.
        by rewrite main mem_sort lnoq.
      have evonllno : point ev === low lno.
        by rewrite -(eqP (oute lowlnoin)) left_on_edge.
      move: palsto.
      have -> := (under_edge_lower_y px' evonllno).
      by rewrite -ltNge.
    have -> := (under_edge_lower_y px' ponllcc); rewrite -ltNge pygtev.
    rewrite /close_cell (pvertE vllcc) (pvertE vhlcc) -no_dup_seq_aux_eq.
    rewrite mem_no_dup_seq !inE (negbTE pnev) /=.
    apply/negP=>/orP[] /eqP pon.
      have vphe : valid_edge he p by rewrite (same_x_valid he px').
      have := pvert_on vphe; rewrite px' (same_pvert_y vphe px') => abs.
      have := puhe; rewrite hiq.
      by rewrite (strict_nonAunder vphe) pon -heq abs.
    rewrite (on_pvert ponllcc) in pon.
    by rewrite pon pt_eqE /= !eqxx in pnev.

  have cinnew : close_cell (point ev) lcc \in state_closed_seq str.
    rewrite /state_closed_seq strq to_right_order mem_cat !mem_rcons !inE eqxx.
    by rewrite !orbT.
  have := safe_side_closed_points' ein cinnew=> /(_ p).
  by rewrite sfnewlstc orbT pise eqxx => /(_ isT).
rewrite nosq inE=> /orP[/eqP cfno | cnos'].
  have plsto : in_safe_side_left p lsto.
    rewrite /in_safe_side_left.
    rewrite px' at_ll eqxx /=.
    have -> /= : p <<< high lsto.
      have evonf : point ev === high fno.
        have fnoo := allo oca_eq (mem_head fno nos').
        by rewrite -(eqP (oute fnoo)) left_on_edge.
      have := pin=> /andP[] _ /andP[] + _.
      have := strict_under_edge_lower_y px' evonf; rewrite cfno /= => -> yplt.
      by rewrite (strict_under_edge_lower_y px' ponho).
    have -> /= : p >>> low lsto.
      have /= := opening_cells_seq_edge_shift oute' vlo vhe oca_eq.
      move=> -[] -> _.
      by move: pin=> /andP[] _ /andP[] _ /andP[]; rewrite cfno.
    have -> /= : p \notin left_pts lsto.
      move: pin=> /andP[] _ /andP[] _ /andP[] _; rewrite cfno /=.
      move: lstok=> /andP[] + _.
      by rewrite p_topleft_lsto; case: left_pts => [ | ? ?].
    by [].
  rewrite p_topleft_lsto in cfno.
  have := safe_side_open_points ss_inv epast lstoin plsto.
  by rewrite pise eqxx.
suff : ~ in_safe_side_left p c by rewrite pin.
have cnos : c \in fno :: nos' by rewrite inE cnos' orbT.
have hco : high c \in outgoing ev.
  by move: (allo oca_eq cnos).
have lco : low c \in outgoing ev.
  have [s1 [s2 sq]] := mem_seq_split cnos'.
  have : adjacent_cells (rcons nos lno).
  have := inv1'; rewrite /state_open_seq/= strq /= => -[] _ [] _ [] + _.
  by rewrite -!catA -cat_rcons catA => /adjacent_catW[] _ /adjacent_catW[].
  rewrite -cats1=> /adjacent_catW[] + _.
  rewrite nosq /= sq cat_path=> /andP[] _ /= /andP[] /eqP <- _.
  case s1q : s1 => [ | fs1 s1'] /=.
    by apply: (allo oca_eq); rewrite inE eqxx.
  by apply: (allo oca_eq); rewrite sq s1q inE mem_cat mem_last !orbT.
have ponl : point ev === low c.
  by rewrite -(eqP (oute lco)) left_on_edge.
have ponh : point ev === high c.
  by rewrite -(eqP (oute hco)) left_on_edge.
move=> /andP[] _ /andP[] puhc /andP[] palc _.
rewrite (under_edge_lower_y px' ponl) in palc.
rewrite (strict_under_edge_lower_y px' ponh) in puhc.
by rewrite (ltW puhc) in palc.
Qed.

Lemma last_case_safe_side_invariant_pre :
  safe_side_non_gp_invariant bottom top s all_e (rcons past ev)
    (step (Bscan fop lsto lop cls lstc lsthe lstx) ev) evs.
Proof.
move: last_case_disjoint_invariant_pre last_case_edge_covered_invariant_pre.
rewrite /step /same_x at_lstx eqxx pu (negbTE pa) /=.
rewrite oe uoct_eq.
move=> d_inv' ec_inv'.
move: left_proc' sub_closed' cl_at_left_ss'
  safe_side_closed_edges' safe_side_open_edges' safe_side_closed_points'
  safe_side_open_points'.
rewrite strq.
by constructor.
Qed.

End proof_environment.

Lemma last_case_safe_side_invariant bottom top s fop lsto lop cls lstc past ev
  lsthe lstx all_e evs :
  {in [:: bottom, top & s] &, forall e1 e2, inter_at_ext e1 e2} ->
  lstx = p_x (point ev) ->
  point ev <<= lsthe ->
  point ev >>= lsthe ->
  safe_side_non_gp_invariant bottom top s all_e past
    (Bscan fop lsto lop cls lstc lsthe lstx)
    (ev :: evs) ->
  safe_side_non_gp_invariant bottom top s all_e (rcons past ev)
    (step (Bscan fop lsto lop cls lstc lsthe lstx) ev) evs.
Proof.
move=> nocs at_lstx pu pa s_inv.
rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /=.
case oe : open_cells_decomposition => [[[[[fc' cc] lcc] lc] le] he].
case uoct_eq : update_open_cell_top => [nos lno].
have := last_case_safe_side_invariant_pre nocs at_lstx pu pa s_inv
oe uoct_eq.
by rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq.
Qed.

End working_environment.
