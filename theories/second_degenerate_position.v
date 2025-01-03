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
    open_cell_side_limit_ok c /\
    left_limit c = p_x (point ev)} /\
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

case ogq : outgoing => [ | fog ogs].
  move=> -[] <- <- /=.
  have lln : left_limit
                (Bcell (Bpt (p_x (point ev))
                            (pvert_y (point ev) he) :: left_pts lsto)
                (right_pts lsto) (low lsto) he) = left_limit lsto.
    rewrite /left_limit.
    by case: left_pts lptsn0 allx=> [ | a tl].
  split.
    move=> g; rewrite inE => /eqP ->; split; last first.
      by  move: lln; rewrite at_ll.
    rewrite /open_cell_side_limit_ok /= lln at_ll eqxx allx.
    case: left_pts lptsn0 ph srt lon => [ | a tl] //= _ <- -> ->.
    by rewrite puh' !andbT /= -at_ll pvert_on.
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
  do 3 (split; first by []).
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
  rewrite lptsq /left_limit left_pts_set at_ll; split; last by [].
  rewrite /open_cell_side_limit_ok /= lptsn0 /left_limit left_pts_set allx srt.
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
split; last first.
  have := opening_cells_left oute vlo vhe; rewrite /opening_cells oca_eq'.
  by apply; rewrite lq /= inE cin orbT.
have := opening_cells_aux_side_limit vlo vhe (underWC pal) puh oute' oca_eq'.
move=> /allP; apply.
by rewrite lq /= inE cin orbT.
Qed.

Section proof_environment.

Variables (bottom top : edge) (s : seq edge) (fop : seq cell) (lsto : cell)
  (lop cls : seq cell) (lstc : cell) (ev : event) (lsthe : edge) (lstx : R)
  (evs : seq event).

Hypotheses
  (boxwf : bottom <| top)
  (nocs' : {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2})
  (inbox_es : {in s, forall g, inside_box bottom top (left_pt g) &&
                                inside_box bottom top (right_pt g)})
  (at_lstx : lstx = p_x (point ev))
  (pu : point ev <<= lsthe)
  (pa : point ev >>= lsthe)
  (comng : common_non_gp_invariant bottom top s
    (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs)).

Let comi : common_invariant bottom top s
  (Bscan fop lsto lop cls lstc lsthe lstx) (ev :: evs).
Proof. by exact: (ngcomm comng). Qed.

Let tmp_inv : inv1_seq bottom top (ev :: evs) (fop ++ lsto :: lop).
Proof. by exact: (inv1 comi). Qed.

Let oute : out_left_event ev.
Proof.
by apply: (out_events comi); rewrite inE eqxx.
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

Let oks : {in rcons nos lno, forall c, open_cell_side_limit_ok c /\
             left_limit c = p_x (point ev)}.
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
by move: tmp_uoct_properties => [? [? [? [? ?]]]].
Qed.

Let sub' : {subset cell_edges (rcons nos lno) <=
     [:: low lsto, he & outgoing ev]}.
Proof.
by move: tmp_uoct_properties => [? [? [? [? ?]]]].
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
have [] : open_cell_side_limit_ok lno /\
  p_x (last dummy_pt (left_pts lno)) = p_x (point ev).
  by apply: oks; rewrite mem_rcons inE eqxx.
rewrite /open_cell_side_limit_ok.
case: left_pts has1' nth1q=> [ | a [ | b [ | c tl]]] //= _ ->.
  by rewrite lexePt_refl.
move=> /andP[] _ /andP[] /andP[] _ srt _ xs.
have : path >%R (p_y (point ev)) [seq p_y p | p <- c :: tl] by exact srt.
rewrite (path_sortedE (rev_trans lt_trans))=> /andP[] /allP + _.
move=> /(_ (p_y (last c tl)) (map_f _ (mem_last _ _))) /ltW ys.
by rewrite /lexePt xs eqxx ys orbT.
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
rewrite oe.
rewrite uoct_eq.
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