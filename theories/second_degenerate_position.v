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
  (cell_center (RealField.sort R) +%R (fun x y => x / y) 1 edge).

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
  move: allx; rewrite /left_limit=> allx.
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
    rewrite /left_limit /lno1.
    by case: left_pts lptsn0 allx=> [ | a tl].
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
  (evs past : seq event).

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
  (ss_inv : safe_side_non_gp_invariant bottom top s past
    (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs)).

Let d_inv : disjoint_non_gp_invariant bottom top s
    (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs).
Proof.
apply: (disjoint_ss ss_inv).
Qed.

Let ec_inv : edge_covered_non_gp_invariant bottom top s
    past (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs).
Proof. apply: (covered_ss ss_inv). Qed.

Let comng := common_non_gp_inv_dis d_inv.

Let comi : common_invariant bottom top s
  (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs).
Proof. by exact: (ngcomm comng). Qed.

Let tmp_inv : inv1_seq bottom top (ev :: evs) (fop ++ lsto :: lop).
Proof. by exact: (inv1 comi). Qed.

Let oute : out_left_event ev.
Proof.
by apply: (out_events comi).
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

Lemma last_case_common_invariant_pre :
  common_non_gp_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
Proof.
rewrite /step /= /same_x at_lstx eqxx pu (negbTE pa) /=.
rewrite oe uoct_eq.
move: inv1' lstx_eq' high_lsto_eq' edges_sub' no_dup_edge'
  sides_ok' above_low_lsto' stradle'.
rewrite strq => ? ? ? ? ? ? ? ?.
have ngcomm' : common_invariant bottom top s str evs.
  by rewrite /str/last_case uoct_eq; constructor.
have lst_side_lex' : path (@lexPt _)
  (nth dummy_pt (left_pts (lst_open str)) 1) [seq point e | e <- evs].
  rewrite /str/last_case uoct_eq /= nth1q.
  by have := (lex_events comi); rewrite sorted_lexPtEv_lexPt.
rewrite strq in lst_side_lex'.
by constructor.
Qed.

Let common_non_gp_inv_dis' : common_non_gp_invariant bottom top s str evs.
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

Let cell_center_in' :
      {in state_closed_seq str, forall c, inside_closed' (cell_center c) c}.
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
      rewrite inside_closed'E=> /andP[] _ /andP[] _ /andP[] lt1.
      rewrite right_limit_close_cell //.
      apply: lt_le_trans.
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
  rewrite -c2c3=> ccin.
  have := close'_subset_contact vc3; rewrite -c2c3 => /(_ _ ok2 ccin) ccin'.
  have := op_cl_dis_non_gp d_inv c3o2 c1old (cell_center c2)=> /negP.
  by rewrite ccin' -pc2 pc1 (cell_center_in d_inv).
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
      apply: cell_center_in'.
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
        move=> /andP[] lf_size /andP[] xs
        /andP[] _ /andP[] hdon _.
        case: left_pts lf_size xs hdon => [ | a tl] // _ xs hdon.
        have ain : a \in (a :: tl) by rewrite inE eqxx.
        have lstin : last a tl \in (a :: tl) by rewrite mem_last.
        have /eqP ax := allP xs _ ain.
        have /eqP lx := allP xs _ lstin.
        rewrite /= lx -ax.
        by move: hdon; rewrite /= => /andP[] _ /andP[] it _.
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
        have := allP (sides_ok comi) _ (nth_in _ js).
        move=> /andP[] lf_size /andP[] xs
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
    have := order_edges_viz_point' vni vnj ibelj'.
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

Lemma last_case_disjoint_invariant_pre :
  disjoint_non_gp_invariant bottom top s
    (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
Proof.
rewrite /step /= /same_x at_lstx eqxx pu (negbTE pa) /=.
rewrite oe uoct_eq.
move: op_cl_dis_non_gp' cl_dis_non_gp'
  common_non_gp_inv_dis' pairwise_open_non_gp'
  closed_at_left_non_gp' size_right_cls'
  uniq_cc' cl_side' high_lstc' nth1_eq' bottom_left_opens'
  btm_left_lex_snd_lst' cell_center_in' uniq_high'.
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
have pevq : point ev = head dummy_pt (right_pts lstc).
  have px : p_x (point ev) = p_x (head dummy_pt (right_pts lstc)).
    by have := cl_at_lstx d_inv; rewrite /= at_lstx pxh.
  have pon : point ev === high lstc.
    by rewrite (high_lstc d_inv) -(high_lsto_eq comi).
  have py := on_edge_same_point pon hon px.
  by apply/eqP; rewrite pt_eqE px py !eqxx.
rewrite pevq; split.
  by case: right_pts sz => [ | ? ?] //= _; rewrite inE eqxx.
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
  (rcons past ev)
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
  have -> : point ev = head dummy_pt (right_pts lstc).
    have /(cl_side d_inv): lstc \in rcons cls lstc.
      by rewrite mem_rcons inE eqxx.
    do 5 (move=> /andP[] _); move=> /andP[] + /andP[] + /andP[] _ /andP[] + _.
    have := cl_at_lstx d_inv => -> /=.
    rewrite at_lstx (high_lstc d_inv) -(high_lsto_eq comi) /=.
    case : right_pts => [ | a tl] //= _ /andP[] /eqP ax _ aon.
    have := on_edge_same_point aon ponho ax => ay.
    by apply/eqP; rewrite pt_eqE ax ay !eqxx.
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

Let old_edge_cases e g p :
  e \in past -> g \in outgoing e -> p === g ->
  (exists2 c, c \in rcons cls lstc & g = high c /\ 
  lexePt p (head dummy_pt (right_pts c))) \/
  exists2 c, c \in fop ++ lsto :: lop & g = high c /\
    left_limit c <= p_x p.
Proof.
move=> epast gin pong.
have := edge_covered_ec ec_inv epast gin => -[].
  move=> -[] oc [pcc [pcccl [hq [cl [oco llpcc]]]]].
  have : left_limit (head_cell (rcons pcc oc)) <= p_x p.
    by rewrite llpcc; move: pong=> /andP[] _ /andP[].
  elim: pcc cl pcccl hq {llpcc}=> [ | c1 pcc Ih] /= cl pcccl hq llpcc.
    right; exists oc=> //.
    split; last by [].
    by apply/esym/hq; rewrite inE eqxx.
  have [pltrc1 | rc1lep ]:= ltrP (p_x p) (right_limit c1).
    left; exists c1; first by apply: pcccl; rewrite inE eqxx.
    split; first by apply/esym/hq; rewrite inE eqxx.
    apply/lexPtW; rewrite /lexPt.
    have -> : (p_x (head dummy_pt (right_pts c1))) = (right_limit c1).
      have : closed_cell_side_limit_ok c1.
        by apply/(cl_side d_inv)/pcccl; rewrite inE eqxx.
      do 5 move=> /andP[] _.
      by case: right_pts => [ | a tl] // /andP[] _ /andP[] /andP[] /eqP + _ _.
    by rewrite pltrc1.
  have cl' : connect_limits (rcons pcc oc) by apply: (path_sorted cl).
  have pcccl' : {subset pcc <= rcons cls lstc}.
    by move=> c cin; apply: pcccl; rewrite inE cin orbT.
  have hq' : {in rcons pcc oc, forall c, high c = g}.
    by move=> c cin; apply: hq; rewrite inE cin orbT.
  have llpcc' : left_limit (head_cell (rcons pcc oc)) <= p_x p.
    by case: (pcc) cl => [ | a tl] /= /andP[] /eqP <-.
  by apply: Ih.
move=> tmp; left; move: tmp.
move=> [pcc [pccn0 [pcccl [hq [cl [llpcc rlpcc]]]]]].
have : p_x p <= right_limit (last dummy_cell pcc).
  by rewrite rlpcc; move: pong=> /andP[] _ /andP[].
have : left_limit (head_cell pcc) <= p_x p.
  by rewrite llpcc; move: pong=> /andP[] _ /andP[].
elim : pcc pccn0 pcccl hq cl {llpcc rlpcc}=>
  [ | c1 pcc Ih] //= _ pcccl hq cl lp pr.
  have [hx lon] : (p_x (head dummy_pt (right_pts c1))) = right_limit c1 /\
            (head dummy_pt (right_pts c1) === g).
    have : closed_cell_side_limit_ok c1.
      by apply/(cl_side d_inv)/pcccl; rewrite inE eqxx.
    do 5 move=> /andP[] _; move=> /andP[].
    case: right_pts => [ | a tl] //= _ /andP[] /andP[] /eqP -> _ /andP[].
    move=> _ /andP[] + _.
    by rewrite hq // inE eqxx.
  have [pcc0 | pccn0] := eqVneq pcc [::].
    exists c1; first by apply: pcccl; rewrite inE eqxx.
    split; first by apply/esym; apply: hq; rewrite inE eqxx.
    move: pr; rewrite le_eqVlt=> /orP[/eqP | ] pr.
      have hx' : (p_x (head dummy_pt (right_pts c1))) = p_x p.
        by rewrite pr pcc0.
      rewrite /lexePt hx' eqxx ltxx /=.
      by rewrite (on_edge_same_point lon pong hx').
    rewrite pcc0 in pr.
    by apply/lexPtW; rewrite /lexPt hx pr.
  have [ pin | pout ] := ltP (p_x p) (right_limit c1).
    exists c1; first by apply: pcccl; rewrite inE eqxx.
    split; first by apply/esym; apply: hq; rewrite inE eqxx.
  by apply/lexPtW; rewrite /lexPt hx pin.
have pcccl' : {subset pcc <= rcons cls lstc}.
  by move=> c cin; apply: pcccl; rewrite inE cin orbT.
have cl' : connect_limits pcc by apply: (path_sorted cl).
have hq' : {in pcc, forall c, high c = g}.
  by move=> c cin; apply: hq; rewrite inE cin orbT.
have pout' : left_limit (head_cell pcc) <= p_x p.
  by case: (pcc) pccn0 cl => [ | a tl] //= _ /andP[] /eqP <- _.
have pr' : p_x p <= right_limit (last dummy_cell pcc).
  by case: (pcc) pccn0 pr.
by apply: Ih.
Qed.

Let safe_side_closed_edges' :
     {in events_to_edges (rcons past ev) & state_closed_seq str, forall g c p,
         in_safe_side_left p c || in_safe_side_right p c -> ~ p === g}.
Proof.
move=> g c gin cin p pin pong.
(* When the edge is new, the only way to be in a safe side and on this
  edge is to be the current event's point *)
have pev' : g \in outgoing ev -> p = point ev.
  move=> gnew.
  have pxge' : p_x (point ev) <= p_x p.
    by move: pong=> /andP[] _ /andP[]; rewrite (eqP (oute gnew)).
  have pxq' : p_x p = p_x (point ev).
    apply: le_anti; rewrite pxge'.
    have rcev : right_limit c <= p_x (point ev).
      by have := closed_at_left_non_gp'=> /(_ c cin); rewrite strq.
    move: pin=> /orP[] /andP[] /eqP -> _; last by rewrite rcev.
    have := cl_large last_case_disjoint_invariant_pre.
    rewrite /state_closed_seq /= /step/same_x at_lstx eqxx pu (negbTE pa) /=.
    rewrite oe /= => /(_ c cin)=> lcltrc.
    by rewrite andbT; apply: ltW; apply: lt_le_trans rcev.
  have evong : point ev === g.
    by rewrite -(eqP (oute gnew)) left_on_edge.
  apply/eqP; rewrite pt_eqE pxq' eqxx /=.
  by rewrite (on_edge_same_point pong evong pxq') eqxx.
move: gin=> /flatten_mapP[e].
rewrite mem_rcons inE=> /orP [/eqP -> gnew | epast gin]; last first.
  (* the edge is old. *)
  move: (cin); rewrite /state_closed_seq /= strq to_right_order mem_cat.
  move=> /orP[cold | ].
    (* the cell is also old. *)
    have gin' : g \in events_to_edges past.
      by apply/flatten_mapP; exists e.
    by apply:(safe_side_closed_edges ss_inv gin' cold pin pong).
  (* the cell is new. *)
  rewrite -map_rcons=> /mapP[c' c'in cc'].
  have cok := cl_side' cin.
  have c'ino : c' \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons !mem_cat (rcbehead_sub c'in) !orbT.
  move: pin=> /orP[ | pin].
    rewrite cc' in_safe_side_left_close_cell => oldpin.
    have := safe_side_open_edges ss_inv _ c'ino oldpin pong; apply.
    by apply/flatten_mapP; exists e.
  move: c'in; rewrite mem_rcons inE => /orP[/eqP c'lcc | c'in].
    have /esym := last_closing_side_char (inbox_events comi) rfo cbtom adj
      sval p oe' ccn0.
    rewrite -c'lcc -cc' pin=> /andP[] px /andP[] py _.
    have : lexPt (point ev) p by rewrite /lexPt eq_sym px py orbT.
    rewrite (pev' gin) lexPt_irref.
    have p_top : lexPt p (head dummy_pt (right_pts c)).
      by have := in_safe_side_right_top_right cok pin.
    have top_ev : lexePt (head dummy_pt (right_pts c)) (point ev).
      have := @cl_at_left_ss' c; rewrite strq /= mem_cat.
      rewrite cc' map_f ; last first.


  case : (cc) ccn0=> [ | fcc cctl] // .
    have := middle_closing_side_char (inbox_events comi) rfo cbtom adj sval p.
    rewrite oe' ccq=> /(_ _ _ _ _ _ _ _ erefl) /negP; apply; apply/hasP.
    exists (close_cell (point ev) c'); last by rewrite -cc' pin.
    rewrite map_f //.
    oe'.
    oe'.
    Search in_safe_side_right.
  have := edge_covered_ec ec_inv epast gin => -[]; last first.
    move=> cl_cov.
    have [c2 c2in tor]:= on_edge_covered_closed_right_limit cl_cov pong.
    
  rewrite /edge_covered.
  admit.
have pev : p = point ev := pev' gnew.
have plh : lexPt p (head dummy_pt c)
move=> g c gin; rewrite strq /state_closed_seq to_right_order mem_cat.
move=> cin p pin pong.
set st := Bscan fop lsto lop cls lstc lsthe lstx.
have pxge' : g \in outgoing ev -> p_x (point ev) <= p_x p.
  by move=> gnew; move: pong=> /andP[] _ /andP[]; rewrite (eqP (oute gnew)).
have pxq' : g \in outgoing ev -> p_x p = p_x (point ev).
  move=> gnew; apply: le_anti; rewrite (pxge' gnew).
  move: pin=> /orP[] /andP[] /eqP -> _.
      by move=> gnew; apply: le_anti; rewrite (pxge' gnew) eqlx rll.

  move: gin; rewrite /events_to_edges => /flattenP[ogs].
  move=> /mapP[e + ->]; rewrite mem_rcons inE=> /orP [/eqP -> | ]; last first.
    move=> epast gin; apply: (safe_side_closed_edges ss_inv)=> //.
    by apply/flattenP; exists (outgoing e); rewrite // map_f.
  have cok : closed_cell_side_limit_ok c.
    apply: cl_side'; rewrite strq /state_closed_seq to_right_order.
    by rewrite mem_cat cold.
  move=> /[dup] gnew gin p pin. (* TODO: remove code duplication. *)

  move=> pong.
    have pxge : p_x (point ev) <= p_x p.
      by move: pong=> /andP[] _ /andP[]; rewrite (eqP (oute gnew)).
    have cin' : c \in state_closed_seq st by [].
    have := (closed_at_left_non_gp_compat d_inv cin')=> /(_ ev).
    rewrite inE eqxx=> /(_ isT) rll.
    move: pin=> /orP[] /[dup] pin /andP[] /eqP eqlx Extra.
      have ltlr := (cl_large d_inv cin').
      move: pxge; rewrite eqlx leNgt=> /negP; apply.
      by apply: lt_le_trans ltlr rll.
    have pxq : p_x p = p_x (point ev).
      by apply: le_anti; rewrite pxge eqlx rll.
    have pev : p = point ev.
      apply/eqP; rewrite pt_eqE pxq eqxx /=; apply/eqP.
      apply: (on_edge_same_point pong _ pxq).
      by rewrite -(eqP (oute gin)) left_on_edge.
    move: cold; rewrite mem_rcons inE => /orP[/eqP clstc | cold]; last first.
      have := in_safe_side_right_top_right cok pin => p_top.
      have := cl_at_left_ss ss_inv cold => /= top_nth1.
      have := lst_side_lex comng=> /andP[] /= nth1_p _.
      have := lexPt_trans p_top (lexePt_lexPt_trans top_nth1 nth1_p).
      by rewrite pev lexPt_irrefl.
    move: Extra; rewrite clstc (high_lstc d_inv) /=.
    have := (high_lsto_eq comi); rewrite /= => <-.
    by rewrite pev (strict_nonAunder vho) ponho.
  move=> p.
  move: cnew; rewrite -map_rcons => /mapP[ c' c'in ->].
  
admit.
Admitted.

Let safe_side_open_edges' :
     {in events_to_edges (rcons past ev) & state_open_seq str, forall g c p,
         in_safe_side_left p c -> ~p === g}.
Proof.
move=> g c gin; rewrite strq /state_open_seq /=.
rewrite catA -catA -cat_rcons mem_cat (mem_cat _ _ lc) orbCA orbC.
move=> /orP [cold | cnew].
  move: gin; rewrite /events_to_edges => /flattenP[ogs].
  move=> /mapP[e + ->]; rewrite mem_rcons inE=> /orP [/eqP -> | ]; last first.
    move=> epast gin; apply: (safe_side_open_edges ss_inv)=> //.
    by apply/flattenP; exists (outgoing e); rewrite // map_f.
  admit.
admit.
Admitted.

Let safe_side_closed_points' :
     {in (rcons past ev) & state_closed_seq str, forall e c p,
         in_safe_side_left p c || in_safe_side_right p c ->
         p != point e :> pt}.
Proof.
move=> e c ein; rewrite strq /state_closed_seq to_right_order mem_cat.
move=> /orP [cold | cnew].
  move: ein; rewrite mem_rcons inE=> /orP [/eqP -> | ]; last first.
    by move=> epast; apply: (safe_side_closed_points ss_inv).
  admit.
admit.
Admitted.

Let safe_side_open_points' :
     {in (rcons past ev) & state_open_seq str, forall e c p,
         in_safe_side_left p c ->
         p != point e :> pt}.
Proof.
move=> e c ein; rewrite strq /state_open_seq /=.
rewrite catA -catA -cat_rcons mem_cat (mem_cat _ _ lc) orbCA orbC.
move=> /orP [cold | cnew].
  move: ein; rewrite mem_rcons inE=> /orP [/eqP -> | ]; last first.
    move=> epast; apply: (safe_side_open_points ss_inv) => //.
    rewrite /state_open_seq ocd -cat_rcons mem_cat (mem_cat _ _ lc) orbCA orbC.
    by rewrite cold.
  admit.
admit.
Admitted.

Lemma last_case_safe_side_invariant_pre :
  safe_side_non_gp_invariant bottom top s (rcons past ev)
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

Lemma last_case_common_invariant bottom top s fop lsto lop cls lstc ev
  lsthe lstx evs :
  {in [:: bottom, top & s] &, forall e1 e2, inter_at_ext e1 e2} ->
  lstx = p_x (point ev) ->
  point ev <<= lsthe ->
  point ev >>= lsthe ->
  common_non_gp_invariant bottom top s (Bscan fop lsto lop cls lstc lsthe lstx)
    (ev :: evs) ->
  common_non_gp_invariant bottom top s
    (step (Bscan fop lsto lop cls lstc lsthe lstx) ev) evs.
Proof.
move=> nocs at_lstx pu pa comng.
rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /=.
case oe : open_cells_decomposition => [[[[[fc' cc] lcc] lc] le] he].
case uoct_eq : update_open_cell_top => [nos lno].
have := last_case_common_invariant_pre nocs at_lstx pu pa comng oe uoct_eq.
by rewrite /step/same_x at_lstx eqxx pu (negbTE pa) /= oe uoct_eq.
Qed.

End working_environment.