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
  (cell_center (Num.RealField.sort R) +%R (fun x y => x / y) 1%:R edge).

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

Lemma update_open_cell_common_invariant
  bottom top s fop lsto lop cls lstc ev
  lsthe lstx all_e p_e evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  common_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     all_e p_e (ev :: evs) ->
  common_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    all_e (rcons p_e ev) evs.
Proof.
move=> bxwf nocs' inbox_s at_lstx under_lsthe comng.
have comi := ngcomm comng.
rewrite /step/generic_trajectories.step.
rewrite /same_x at_lstx eqxx /=.
rewrite -/(point_under_edge _ _) underW /=; last by [].
rewrite -/(point ev <<< lsthe) under_lsthe.
have oute : out_left_event ev.
  by apply: (out_events comi); rewrite inE eqxx.
have oute' : {in sort edge_below (outgoing ev),
                  forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
have [clae [sval' [adj [cbtom rfo]]]] := inv1 comi.
have sval : seq_valid (state_open_seq (Bscan fop lsto lop cls lstc lsthe lstx))
              (point ev).
  by case: sval'.
have lstx_ll : lstx = left_limit lsto.
  rewrite -[lstx]/(lst_x _ _ (Bscan fop lsto lop cls lstc lsthe lstx)).
  by rewrite (lstx_eq comi).
have pal : (point ev) >>> low lsto.
  by exact: (same_x_point_above_low_lsto at_lstx comng).
have abovelow : p_x (point ev) = lstx -> (point ev) >>> low lsto by [].
have noc : {in all_edges (fop ++ lsto :: lop) (ev :: evs) &,
           no_crossing R}.
  apply: inter_at_ext_no_crossing.
  by apply: (sub_in2 (edges_sub comi) nocs').
have lstoin : lsto \in (fop ++ lsto :: lop).
  by rewrite mem_cat inE eqxx orbT.
have sok : open_cell_side_limit_ok lsto.
  by apply: (allP (sides_ok comi)); exact: lstoin.
have xev_llo : p_x (point ev) = left_limit lsto.
  by rewrite -at_lstx -(lstx_eq comi).
have puho : point ev <<< high lsto.
  move: under_lsthe.
  rewrite -[lsthe]/(lst_high _ _ (Bscan fop lsto lop cls lstc lsthe lstx)).
  by rewrite -(high_lsto_eq comi).
have [vl vh] := (andP (allP sval lsto lstoin)).
have sll : (1 < size (left_pts lsto))%N.
  by apply: (size_left_lsto sval lstx_ll (sides_ok comi) (esym at_lstx) pal
             (underW puho)).
have ogsub : {subset (outgoing ev) <= [:: bottom, top & s]}.
  move=> g gin; apply: (edges_sub comi); rewrite /all_edges mem_cat.
  by apply/orP; right; rewrite events_to_edges_cons mem_cat gin.
- have xev_ll : p_x (point ev) = left_limit lsto.
    by rewrite -at_lstx lstx_ll.
case uocq : update_open_cell => [nos lno].
have inv1' : inv1_seq bottom top evs
  ((fop ++ nos) ++ lno :: lop).
  have := step_keeps_invariant1 cls lstc (inbox_events comi) oute rfo cbtom adj
          sval
          (closed_events comi) clae (esym (high_lsto_eq comi)) abovelow noc
          (lex_events comi).
  rewrite /step /generic_trajectories.step/same_x -at_lstx eqxx /=.
  rewrite -/(point_under_edge _ _) underW /=; last by [].
  rewrite uocq.
  by rewrite -/(point ev <<< lsthe) under_lsthe.
have lstxq' : p_x (point ev) = left_limit lno.
  have [case1 | case2]:= update_open_cellE2 oute vl vh sok xev_llo sll pal puho.
    apply/esym.
    have := opening_cells_left oute vl vh.
    rewrite /opening_cells; move: case1; case: opening_cells_aux=> [nos' lno'].
    rewrite uocq /= => <- /(_ lno).
    by apply; rewrite mem_rcons inE eqxx.
  move: case2; rewrite uocq /= => ->.
  by rewrite (add_point_left_limit _ sll).
have hlsto' : high lno = lsthe.
  have [case1 | case2]:= update_open_cellE2 oute vl vh sok xev_llo sll pal puho.
    rewrite uocq /= in case1; rewrite case1.
    have := opening_cells_aux_high_last vl vh oute'.
    case: opening_cells_aux => [lno' nos'] /= => ->.
    by apply: (high_lsto_eq comi).
  rewrite uocq /= in case2; rewrite case2.
  rewrite high_set_left_pts.
  by apply: (high_lsto_eq comi).
have llin : low lsto \in [:: bottom, top & s].
  apply: (edges_sub comi); rewrite /all_edges mem_cat /state_open_seq /=.
  by rewrite cell_edges_cat mem_cat cell_edges_cons inE eqxx !orbT.
have hlin : high lsto \in [:: bottom, top & s].
  apply: (edges_sub comi); rewrite /all_edges mem_cat /state_open_seq /=.
  by rewrite cell_edges_cat mem_cat cell_edges_cons !inE eqxx !orbT.
have sub_edges' : {subset all_edges ((fop ++ nos) ++ lno :: lop) evs <=
  [:: bottom, top & s]}.
  rewrite /all_edges /state_open_seq /=.
  apply: subset_catl; last first.
    move=> g gin; apply: (edges_sub comi); rewrite /all_edges.
    by rewrite mem_cat orbC events_to_edges_cons mem_cat gin orbT.
  move=> g; rewrite cell_edges_cat mem_cat cell_edges_cons 2!inE.
  rewrite cell_edges_cat mem_cat -!orbA=> /orP[gin | ] .
    apply: (edges_sub comi); rewrite /state_open_seq /= /all_edges mem_cat.
    by rewrite cell_edges_cat mem_cat gin.
  move=> /orP[gin | ].
    have [c cin gq] : exists2 c, c \in nos & g = high c \/ g = low c.
      move: gin; rewrite mem_cat=> /orP[] /mapP[c cin gq]; exists c=> //.
        by right.
      by left.
    have := update_open_cellE1 oute vl vh sok xev_llo sll pal puho.
    rewrite uocq /= => /(_ _ cin) [c' c'in Pc].
    have /andP [lc'in hc'in] : (low c' \in [:: bottom, top & s]) &&
            (high c' \in [:: bottom, top & s]).
      have := opening_cells_subset' llin hlin ogsub vl vh oute.
      rewrite /opening_cells.
      move: c'in; case : opening_cells_aux => [nos' lno'] /= c'in main.
      by rewrite !main // mem_cat map_f ?orbT // mem_rcons inE c'in ?orbT.
    move: Pc gq=> [-> | [l lv [_ ->]]].
      by move=> [] ->.
    rewrite high_set_left_pts low_set_left_pts.
    by move=> [] ->.
  rewrite orbA=> /orP[ | gin]; last first.
    apply: (edges_sub comi); rewrite /all_edges mem_cat /state_open_seq /=.
    by rewrite cell_edges_cat mem_cat cell_edges_cons !inE gin !orbT.
  have := update_open_cellE2 oute vl vh sok xev_llo sll pal puho.
  rewrite uocq /=.
  have := opening_cells_subset' llin hlin ogsub vl vh oute.
  rewrite /opening_cells.
  move: opening_cells_aux => [nos' lno'] /= main.
  move=> [] -> /orP gin.
    apply: main; rewrite mem_cat; move: gin.
    by move=> [] /eqP ->; rewrite map_f ?orbT //; rewrite mem_rcons inE eqxx.
  move: gin; rewrite low_set_left_pts high_set_left_pts=> gin.
  apply: (edges_sub comi); rewrite /all_edges/state_open_seq /=.
  rewrite mem_cat cell_edges_cat mem_cat cell_edges_cons !inE.
  by move: gin=> [] ->; rewrite ?orbT.
have cle' : close_edges_from_events evs.
  by move: (closed_events comi)=> /andP[].
have out_es' : {in evs, forall e, out_left_event e}.
  by move=> e1 e1in; apply: (out_events comi); rewrite inE e1in orbT.
have uniqout' : {in evs, forall e, uniq (outgoing e)}.
  by move=> e1 e1in; apply: (uniq_ec comi); rewrite inE e1in orbT.
have inbox_es' : all (inside_box bottom top) [seq point x | x <- evs].
  by move: (inbox_events comi)=> /andP[].
(* have no_dup' : {in [seq high c | c <- (fop ++ nos) ++ lno :: lop] & evs,
  forall g e, g \notin outgoing e}. *)
have sevs' : sorted (@lexPtEv _) evs.
  move: (lex_events comi)=> /=.
  rewrite path_sortedE; last by apply:lexPtEv_trans.
  by move=> /andP[].
have no_dup' : {in [seq high c | c <- (fop ++ nos) ++ lno :: lop] &
  evs, forall g e, g \notin outgoing e}.
  move=> g e + ein.
  have ein2 : e \in (ev :: evs) by rewrite inE ein orbT.
  rewrite -catA -cat_rcons !map_cat !mem_cat orbCA orbC=>/orP[cold | ].
    apply: (no_dup_edge comi); rewrite /state_open_seq//=.
    by rewrite !map_cat /= mem_cat inE orbCA cold orbT.
  rewrite map_rcons mem_rcons inE=> /orP[/eqP -> |].
    have := update_open_cellE2 oute vl vh sok xev_ll sll pal puho.
    have ndho : high lsto \notin outgoing e.
      apply: (no_dup_edge comi) => //.
      by rewrite /state_open_seq/= map_f // mem_cat inE eqxx orbT.
    rewrite uocq /= => -[] ->; last by [].
    by rewrite opening_cells_aux_high_last.
  move=> /mapP [c cno gc].
  have := update_open_cellE1 oute vl vh sok xev_ll sll pal puho.
  rewrite uocq /= => /(_ c cno)=> -[c2 c2op].
  have highsq := opening_cells_aux_high vl vh oute'.
  have: high c2 \in sort edge_below (outgoing ev).
    by rewrite -highsq map_f.
  rewrite mem_sort => highc2.
  have highc2n : high c2 \notin outgoing e.
    apply/negP=> highc2'.
    have oute2 : out_left_event e by apply: (out_events comi).
    move: (lex_events comi)=> /=; rewrite (path_sortedE (@lexPtEv_trans _)).
    move=>/andP[] /allP /(_ e ein) + _; rewrite /lexPtEv.
    rewrite -(eqP (oute (high c2) highc2)) (eqP(oute2 (high c2) highc2')).
    by rewrite lexPt_irrefl.
  rewrite gc; move=> -[-> | [l lprop [_ ->]]]; first by [].
  by rewrite high_set_left_pts.
have all_ok' : all open_cell_side_limit_ok ((fop ++ nos) ++ lno :: lop).
  rewrite -catA -cat_rcons 2!all_cat andbCA.
  move: (sides_ok comi).
  rewrite !all_cat /= andbCA => /andP[] lstook ->; rewrite andbT.
  have sz_lptso := size_left_lsto sval lstx_ll
    (sides_ok comi) (esym at_lstx) pal (underW puho) => /=.
  have lxlftpts : all (fun x => lexPt x (point ev)) (behead (left_pts lsto)).
    have := lst_side_lex comng  => /=.
    case lptsq : (left_pts lsto) => [ | p1 [ | p2 ps]] //= /andP[] p2lex _.
    rewrite p2lex /=.
    apply/allP => px pxin.
    apply: (lexPt_trans _ p2lex).
    move: (sides_ok comi)=> /allP /(_ _ lstoin) /andP[] _.
    rewrite lptsq /= => /andP[] /andP[] _ /andP[] p2ll /allP psll.
    move=> /andP[] /andP[] _ + _.
    rewrite (path_sortedE (rev_trans (lt_trans)))=> /andP[] /allP cmpy _.
    rewrite /lexPt (eqP p2ll) (esym (eqP (psll _ pxin))) eqxx.
    by rewrite (cmpy (p_y px)) ?orbT // map_f.
  apply: (update_open_cell_side_limit_ok oute sval
    (sides_ok comi) lxlftpts uocq xev_ll puho pal).
have events_right' :
   {in evs,  forall e, lexPt (last dummy_pt (left_pts lno)) (point e)}.
  move=> e ein.
  have := update_open_cellE2 oute vl vh sok xev_ll sll pal puho.
  rewrite uocq /= => -[case1 | case2].
    have lnoin : lno \in opening_cells (point ev) (outgoing ev)
        (low lsto) (high lsto).
    move: case1; rewrite /opening_cells.
     case: opening_cells_aux => /= hd it ->.
    by rewrite mem_rcons inE eqxx.
    have noco : {in rcons (low lsto :: sort edge_below (outgoing ev))
       (high lsto) &, no_crossing R}.
      move=> g1 g2.
      rewrite !(inE, mem_rcons, mem_sort) !orbA=> /orP g1in /orP g2in.
      apply noc; rewrite mem_cat /events_to_edges /= (mem_cat _ (outgoing ev)).
        move: g1in=> [g1in | ] ; [ | by move=> ->; rewrite orbT].
        rewrite cell_edges_cat mem_cat cell_edges_cons !inE.
        by move: g1in=> /orP[] ->; rewrite ?orbT.
      move: g2in=> [g2in | ] ; [ | by move=> ->; rewrite orbT].
      rewrite cell_edges_cat mem_cat cell_edges_cons !inE.
      by move: g2in=> /orP[] ->; rewrite ?orbT.
    have lobhi : low lsto <| high lsto by move: rfo=> /allP /(_ lsto lstoin).
    have :=
      opening_cells_last_lexePt oute (underWC pal) puho vl vh lnoin.
    move=> /lexePt_lexPt_trans; apply.
    have := lex_events comi; rewrite sorted_lexPtEv_lexPt /=.
    rewrite (path_sortedE (@lexPt_trans _)).
    by move=> /andP[] /allP /(_ _ (map_f _ ein)).
  have ein' : e \in (ev :: evs) by rewrite inE ein orbT.
  have := above_low_lsto comi => /= /(_ _ ein').
  rewrite case2 left_pts_set.
  by case: (left_pts lsto) sll => [ | ? [ | ? ?]].
have stradle' : evs = [::] \/
  {in [seq high c | c <- (fop ++ nos) ++ lno :: lop], forall g,
    lexPt (left_pt g) (point (head dummy_event evs)) &&
    lexePt (point (head dummy_event evs)) (right_pt g)}.
  case evsq2 : evs => [ | ev1 evs']; first by left.
  right.
  have strd : {in [seq high c | c <- fop ++ lsto :: lop],
    forall g, lexPt (left_pt g) (point ev) && lexePt (point ev) (right_pt g)}.
    by move=> g gin; have [ //|  it]:= stradle comi; apply: it.
  move=> g gin.
  have := step_keeps_lex_edge (inbox_events comi) oute rfo cbtom adj sval
  (closed_events comi) clae erefl abovelow.
  rewrite /step/same_x at_lstx eqxx (underW puho) /= puho uocq.
  rewrite /state_open_seq /= => /(_ [::] dummy_cell strd) => main.
  apply: main.
        by apply: (allP inbox_es'); rewrite evsq2 inE eqxx.
      by have := lex_events comi; rewrite evsq2 /= => /andP[].
    move=> e2; rewrite evsq2 inE => /orP[/eqP -> | e2in].
      by apply lexePt_refl.
    have := sevs'; rewrite evsq2 /= (path_sortedE (@lexPtEv_trans _)).
    by move=> /andP[] /allP /(_ _ e2in) /lexPtW.
  by [].
have all_events_break' : all_e = rcons p_e ev ++ evs.
  by rewrite cat_rcons (all_events_break comi).
by constructor.
Qed.

Lemma update_open_cell_common_non_gp_invariant
  bottom top s fop lsto lop cls lstc ev
  lsthe lstx all_e p_e evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  common_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     all_e p_e (ev :: evs) ->
  common_non_gp_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    all_e (rcons p_e ev) evs.
Proof.
move=> bxwf nocs' inbox_s at_lstx under_lsthe comng.
have comi := ngcomm comng.
set st := Bscan _ _ _ _ _ _ _.
have oute : out_left_event ev.
  by apply: (out_events comi); rewrite inE eqxx.
have ci : common_invariant bottom top s (step st ev) all_e (rcons p_e ev) evs.
    by apply: update_open_cell_common_invariant.
have [clae [sval' [adj [cbtom rfo]]]] := inv1 comi.
have sval : seq_valid (state_open_seq (Bscan fop lsto lop cls lstc lsthe lstx))
              (point ev).
  by case: sval'.
have lstoin : lsto \in (fop ++ lsto :: lop).
  by rewrite mem_cat inE eqxx orbT.
have [vl vh] := (andP (allP sval lsto lstoin)).
have sok : open_cell_side_limit_ok lsto.
  by apply: (allP (sides_ok comi)); exact: lstoin.
have xev_llo : p_x (point ev) = left_limit lsto.
  by rewrite -at_lstx -(lstx_eq comi).
have puho : point ev <<< high lsto.
  move: under_lsthe.
  rewrite -[lsthe]/(lst_high _ _ (Bscan fop lsto lop cls lstc lsthe lstx)).
  by rewrite -(high_lsto_eq comi).
have pal : (point ev) >>> low lsto.
  by exact: (same_x_point_above_low_lsto at_lstx comng).
have lstx_ll : lstx = left_limit lsto.
  rewrite -[lstx]/(lst_x _ _ (Bscan fop lsto lop cls lstc lsthe lstx)).
  by rewrite (lstx_eq comi).
have sll : (1 < size (left_pts lsto))%N.
  by apply: (size_left_lsto sval lstx_ll (sides_ok comi) (esym at_lstx) pal
             (underW puho)).
have /andP[] : (1 < size (left_pts (lst_open (step st ev))))%N &&
               path (@lexPt _)
                  (nth dummy_pt (left_pts (lst_open (step st ev))) 1)
                  [seq point e | e <- evs].
  rewrite /step /st.
  rewrite /same_x at_lstx eqxx /= underW /=; last by [].
  rewrite under_lsthe.
  case uocq : update_open_cell => [nos lno] /=.
  have [og0 | ognn] := eqVneq (outgoing ev) [::].
    have := update_open_cell_outgoing_empty vl vh sok xev_llo sll pal puho og0.
    rewrite uocq=> -[] _ ->.
    rewrite left_pts_set /=.
    rewrite (@path_map _ _ (@point) (@lexPt R) ev evs).
    exact: (lex_events comi).
  have [_ ]:= update_open_cell_tail oute vl vh sok xev_llo sll pal puho ognn.
  rewrite uocq.
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos1 lno1] /=.
  move=> ->.
  have  [sz prf]:= last_opening_cells_left_pts_prefix vl vh puho oute oca_eq.
  rewrite sz /=.
  set thenth := nth _ _ _.
  suff -> : thenth = point ev.
    rewrite (@path_map _ _ (@point) (@lexPt R) ev evs).
    exact: (lex_events comi).
  have := take_nth dummy_pt sz; rewrite prf /thenth.
  case lpts1 : (left_pts lno1) sz => [ | a [ | b tl]] //= _.
  by move=> [] _ /esym.
(* To be kept until one proves btm_left_lex_snd_lst in for update_open_cell
have btm_lex : {in state_open_seq (step st ev), forall c,
  lexePt (bottom_left_corner c)
     (nth dummy_pt (left_pts (lst_open (step st ev))) 1)}.
  rewrite /step/st.
  rewrite /same_x at_lstx eqxx /= underW /=; last by [].
  rewrite under_lsthe.
  case uocq : update_open_cell => [nos lno] /=.
  have [og0 | ognn] := eqVneq (outgoing ev) [::].
    have := update_open_cell_outgoing_empty vl vh sok xev_llo sll pal puho og0.
    rewrite uocq=> -[] -> ->.
    rewrite cats0 left_pts_set /state_open_seq /=.
    move=> c; rewrite !(mem_cat, inE) orbCA orbC=> /orP[cold | cnew].
      have cold' : c \in state_open_seq st.
        rewrite /st /state_open_seq /=.
        by rewrite !(mem_cat, inE) orbCA cold orbT.
      have := (btm_left_lex_snd_lst dis cold')=> /=. *)
constructor=> //.
Qed.

Lemma update_open_cell_disjoint_non_gp_invariant
  bottom top s fop lsto lop cls lstc ev
  lsthe lstx all_e p_e evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  disjoint_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     all_e p_e (ev :: evs) ->
  disjoint_non_gp_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    all_e (rcons p_e ev) evs.
Proof.
move=> bxwf nocs' inbox_s at_lstx under_lsthe disng.
have comng := common_non_gp_inv_dis disng.
have comi := ngcomm comng.
rewrite /step/=/same_x eq_sym at_lstx eqxx /=.
rewrite underW ?under_lsthe //=.
have oute : out_left_event ev.
  by apply: (out_events comi); rewrite inE eqxx.
move: (inv1 comi) => [] clae [] sval' [] adj [] cbtom rfo.
move: sval' => [ //| sval].
have at_ll : p_x (point ev) = left_limit lsto.
  by rewrite -(lstx_eq comi) at_lstx.
have hlo_eq := high_lsto_eq comi.
have lstoin : lsto \in state_open_seq (Bscan fop lsto lop cls lstc lsthe lstx).
  by rewrite /state_open_seq/= mem_cat inE eqxx orbT.
have sok := sides_ok comi.
have evin : ev \in ev :: evs by rewrite inE eqxx.
have lstok : open_cell_side_limit_ok lsto by apply: (allP sok _ lstoin).
have /andP[vlo vho] := allP sval lsto lstoin.
have evabove : point ev >>> low lsto.
  have := above_low_lsto comi evin.
  move: lstok => /andP[] lln0 /andP[] sx /andP[] _ /andP[] _ onlow.
  rewrite -at_ll in sx.
  have lstin : last dummy_pt (left_pts lsto) \in left_pts lsto.
    by case: (left_pts lsto) lln0 => //= ? ?; rewrite mem_last.
  move: (allP sx _ lstin)=> /= samex'.
  rewrite /lexPt lt_neqAle samex' /= => ab.
  have vev : valid_edge (low lsto) (point ev).
    have <- := same_x_valid (low lsto) (eqP samex').
    by move: onlow=> /andP[].
  rewrite under_pvert_y // -ltNge.
  have := on_pvert onlow.
  by have := same_pvert_y vev (esym (eqP samex')) => -> ->.
have puho : point ev <<< high lsto by rewrite hlo_eq /=.
have sll : (1 < size (left_pts lsto))%N.
  by apply: (size_left_lsto sval erefl (sides_ok comi) at_ll evabove
      (underW puho)).
have pw := pairwise_open_non_gp disng.
have disoc := op_cl_dis_non_gp disng.
have discl := cl_dis_non_gp disng.
have clleft : {in rcons cls lstc, forall c, right_limit c <= p_x (point ev)}.
  move=> c cin.
  by have := closed_at_left_non_gp disng cin; rewrite /= at_lstx.
have uniq_cl : uniq (rcons cls lstc).
  by apply/(@map_uniq _ _ cell_center)/(uniq_cc disng).
have := step_keeps_disjoint (inbox_events comi) oute rfo cbtom adj sval
  (esym (high_lsto_eq comi)) (lstx_eq comi) (fun _ => evabove) pw sok disoc
  discl clleft uniq_cl (size_right_cls disng).
rewrite /step/same_x [lst_x _ _ _]/= at_lstx eqxx /= underW under_lsthe //=.
case uocq : update_open_cell=> [nos lno].
rewrite /state_closed_seq /= => -[] cc_disj oc_disj.
have srlstc : right_pts (update_closed_cell lstc (point ev)) != [::].
  by [].
have cl_rl : right_limit (update_closed_cell lstc (point ev)) =
             right_limit lstc.
  rewrite update_closed_cell_keeps_right_limit //.
    by apply: (size_right_cls disng).
  by apply: (cl_side disng); rewrite /= mem_rcons inE eqxx.
have nocs : {in all_edges (fop ++ lsto :: lop) (ev :: evs) &,
     no_crossing R}.
    apply: inter_at_ext_no_crossing.
    by apply: (sub_in2 (edges_sub comi)).
have ev_nth1 : point ev = nth dummy_pt (left_pts lno) 1.
   have := update_open_cellE2 oute vlo vho lstok at_ll sll evabove puho.
    rewrite uocq /= => -[ | lno_update]; last first.
      by rewrite lno_update left_pts_set.
    case oca_eq : opening_cells_aux => [nos1 lno1] /= lnoq.
    have  []:= last_opening_cells_left_pts_prefix vlo vho puho oute oca_eq.
    rewrite lnoq.
    by case: (left_pts lno1) => [ | a [ | b tl]] //= _ [].
constructor.
- rewrite /state_open_seq/state_closed_seq/=.
  move=> c1 c2 c1in c2in; exact: (oc_disj _ _ c1in c2in).
  move=> c1 c2 c1in c2in; exact: (cc_disj _ _ c1in c2in).
- have := update_open_cell_common_non_gp_invariant bxwf nocs' inbox_s at_lstx
   under_lsthe comng.
  by rewrite /step/same_x at_lstx eqxx /= underW under_lsthe //= uocq.
- have := step_keeps_pw cls lstc (inbox_events comi) oute rfo cbtom adj sval
    (esym hlo_eq) (fun (_ : _ = lstx) => evabove) nocs
    (pairwise_open_non_gp disng) => /=.
  rewrite /same_x  at_lstx eqxx /= underW under_lsthe //=.
  by rewrite uocq /state_open_seq.
- rewrite /state_closed_seq /=.
  move=> c; rewrite mem_rcons inE orbC=> /orP[cin | /eqP ->].
    have := (closed_at_left_non_gp disng); rewrite /= at_lstx; apply.
    by rewrite /state_closed_seq /= mem_rcons inE cin orbT.
  rewrite update_closed_cell_keeps_right_limit.
      have := (closed_at_left_non_gp disng); rewrite /= at_lstx; apply.
        by rewrite /state_closed_seq/= mem_rcons inE eqxx.
    apply: (size_right_cls disng).
  by apply (cl_side disng); rewrite /state_closed_seq /= mem_rcons inE eqxx.
- by [].
- have -> :
   [seq cell_center c | c <- rcons cls (update_closed_cell lstc (point ev))] =
   [seq cell_center c | c <- rcons cls lstc].
    rewrite -!cats1 !map_cat /=.
    rewrite cell_center_update_closed_cell //.
    exact: (size_right_cls disng).
  exact: (uniq_cc disng).
(* - rewrite /state_closed_seq/= => c.
  rewrite mem_rcons inE orbC => /orP[cin | /eqP ->].
    by apply: (cl_large disng); rewrite /= mem_rcons inE cin orbT.
  rewrite update_closed_cell_keep_left_limit.
  rewrite update_closed_cell_keeps_right_limit; last first.
      by apply: (cl_side disng); rewrite /= mem_rcons inE eqxx.
    exact: (size_right_cls disng).
  by apply: (cl_large disng); rewrite /= mem_rcons inE eqxx. *)
- rewrite /state_closed_seq/= => c.
  rewrite mem_rcons inE orbC=> /orP[ cin |/eqP ->].
    by apply: (cl_side disng); rewrite /= mem_rcons inE cin orbT.
  rewrite /closed_cell_side_limit_ok/left_limit.
  have -> : left_pts (update_closed_cell lstc (point ev)) = left_pts lstc.
    by [].
  have lstcin : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
  have /andP[ -> ] := (cl_side disng lstcin).
  move=> /andP[] -> /andP[] -> /andP[] -> /andP[] -> /andP[] rptsn0.
  move=> /andP[] alx /andP[] decry /andP[] onh onl /=.
  have lstc_at : right_limit lstc = lstx by apply: (cl_at_lstx disng).
  have hin : head dummy_pt (right_pts lstc) \in right_pts lstc.
    by apply: head_in_not_nil.
  apply/andP; split.
    have := (allP alx (head dummy_pt (right_pts lstc)) hin)=> /eqP ->.
    rewrite update_closed_cell_keeps_right_limit; last first.
        by apply: (cl_side disng); rewrite /= mem_rcons inE eqxx.
      by apply: (size_right_cls disng).
    rewrite eqxx /=.
    rewrite lstc_at at_lstx eqxx /=.
    apply/allP=> p pin.
    have pin' : p \in (right_pts lstc) by rewrite mem_behead.
    by rewrite (eqP (allP alx _ pin')) lstc_at at_lstx eqxx.
  apply/andP; split.
    have  [vl vh] := andP (allP sval lsto lstoin).
    move: hlo_eq; rewrite /= => hlo_eq.
    have := under_lsthe; rewrite -hlo_eq.
    rewrite (strict_under_pvert_y vh) /=.
    have xh : p_x (point ev) = p_x (head dummy_pt (right_pts lstc)).
      by rewrite (eqP (allP alx (head dummy_pt (right_pts lstc)) hin)) lstc_at.
    have := same_pvert_y vh xh => /= ->.
    have := (on_pvert onh); rewrite (high_lstc disng) /= hlo_eq => -> -> /=.
    move: (size_right_cls disng) (lexev_right_cls disng) decry alx xh=> /=.
    case: (right_pts lstc) => [| a [| b tl]] //= _ /andP[] + _ /andP[] _ ->.
    move=> lexevb /andP[] /eqP -> /andP[] /eqP bx _ evx.
    by move: lexevb; rewrite /lexPt lt_neqAle bx evx eqxx /= => ->.
  rewrite onh /=.
  move: (size_right_cls disng) onl.
  by case: (right_pts lstc) => [ | a [ | b ?]].
- by rewrite /=; apply: (high_lstc disng).
- by [].
- rewrite /state_open_seq /= -catA -cat_rcons.
  move=> c e + ein; rewrite !mem_cat orbCA orbC=> /orP[cold | cnew].
    apply: (bottom_left_opens disng); rewrite /state_open_seq/=.
      by rewrite !(mem_cat, inE) orbCA cold orbT.
    by rewrite inE ein orbT.
  have lexeve : lexPt (point ev) (point e).
    have := lex_events comi.
    rewrite /= (path_sortedE (@lexPtEv_trans _)) => /andP[] + _.
    by move=> /allP /(_ e ein).
  have btm_left_ev: {in fop ++ lsto :: lop, forall c,
        lexPt (bottom_left_corner c) (point ev)}.
      move=> c' c'in; apply: (bottom_left_opens disng).
        by rewrite // inE eqxx.
      by rewrite inE eqxx.
  have := step_keeps_btom_left_corners_default (inbox_events comi)
        oute rfo cbtom adj sval btm_left_ev lexeve.
  have -> /= := open_cells_decomposition_single adj rfo sval evabove puho.
  move=> main.
 move: cnew; rewrite mem_rcons inE => /orP[/eqP -> | cprefix].
    have := update_open_cellE2 oute vlo vho lstok at_ll sll evabove puho.
    rewrite uocq /= => -[] ->.
      move: main.
      case: opening_cells_aux => [a b]; apply.
      by rewrite /= !(mem_cat, inE) eqxx !orbT.
    apply: (lexPt_trans _ lexeve).
    move: (btm_left_ev lsto lstoin); rewrite /bottom_left_corner.
    by move: sll; case: (left_pts lsto) => [ | a [ | b l]].
  have := update_open_cellE1 oute vlo vho lstok at_ll sll evabove puho.
  rewrite uocq /= => /(_ c cprefix) [] c' c'in.
  move => [ -> | [l lprop [lq ->]]].
    move: c'in main; case: opening_cells_aux=> [a b] /= c'in; apply.
    by rewrite !(mem_cat, inE) c'in orbT.
  move: c'in main; case: opening_cells_aux => [a b] /= c'in main.
  have : lexPt (bottom_left_corner c') (point e).
    by apply: main; rewrite !mem_cat c'in orbT.
  by rewrite /bottom_left_corner left_pts_set lq.
- rewrite/state_open_seq /=.
  set pte := nth _ _ 1.
  have pteq : pte = point ev by [].
  move=> c; rewrite -catA -cat_rcons !mem_cat orbCA orbC=> /orP[cold | cnew].
    rewrite pteq; apply lexPtW.
    apply: (bottom_left_opens disng _ evin); rewrite /state_open_seq /=.
    by rewrite !(mem_cat, inE) orbCA cold orbT.
  have noc1 : {in rcons (low lsto :: sort edge_below (outgoing ev))
    (high lsto) &, no_crossing R}.
    have llstoin : low lsto \in cell_edges (fop ++ lsto :: lop).
      by rewrite mem_cat map_f.
    have hlstoin : high lsto \in cell_edges (fop ++ lsto :: lop).
      by rewrite mem_cat map_f ?orbT.
    by apply: (no_crossing_event nocs' (edges_sub comi) llstoin hlstoin evin).
  have lstorf : low lsto <| high lsto.
    by apply: (allP rfo); rewrite /state_open_seq /= mem_cat inE eqxx orbT.
  have := opening_cells_last_lexePt oute (underWC evabove) puho vlo vho.
  move=> mainop.
  have main_lno: lexePt (bottom_left_corner lno) (point ev).
    have := update_open_cellE2 oute vlo vho lstok at_ll sll evabove puho.
    rewrite uocq=> -[] /= ->.
      have pin : (opening_cells_aux (point ev) (sort edge_below (outgoing ev))
      (low lsto) (high lsto)).2 \in
      (opening_cells (point ev) (outgoing ev) (low lsto) (high lsto)).
        rewrite /opening_cells.
        by case: opening_cells_aux => [a b]; rewrite mem_rcons inE eqxx.
      by move: mainop=> /(_ _ pin).
    apply: lexPtW.
    have := (bottom_left_opens disng lstoin evin).
    rewrite /bottom_left_corner left_pts_set.
    by move: sll; case: (left_pts lsto) => [ | ? []].
  have main_nos: c \in nos -> lexePt (bottom_left_corner c) (point ev).
    move=> cin.
    have cin' : c \in (update_open_cell lsto ev).1 by rewrite uocq.
    have := update_open_cellE1 oute vlo vho lstok at_ll sll evabove puho cin'.
    have c'in2 a (ain : a \in (opening_cells_aux (point ev)
            (sort edge_below (outgoing ev)) (low lsto) (high lsto)).1):
        a \in opening_cells (point ev) (outgoing ev) (low lsto) (high lsto).
      rewrite /opening_cells; move: ain.
      by case: opening_cells_aux => [? ?] /= it; rewrite mem_rcons inE it orbT.
    move=> /=[c' c'in [cc' | [l lprop [lq cc']]]].
      by have := mainop c' (c'in2 _ c'in); rewrite -cc'.
    rewrite cc' /bottom_left_corner left_pts_set lq.
    by have := mainop c' (c'in2 _ c'in).
  rewrite pteq.
  by move: cnew; rewrite mem_rcons inE => /orP[/eqP -> | /main_nos].
- rewrite /state_closed_seq/=.
  move=> c; rewrite mem_rcons inE => /orP[/eqP -> | cold].
    have szc : (1 < size (right_pts lstc))%N.
      by apply: (size_right_cls disng).
    rewrite -strict_inside_closed_update // update_closed_cell_center //.
    apply: (cell_center_in disng).
    by rewrite /state_closed_seq/= mem_rcons inE eqxx.
  apply: (cell_center_in disng).
  by rewrite /state_closed_seq/= mem_rcons inE cold orbT.
rewrite /state_open_seq/= -catA -cat_rcons !map_cat.
have := update_open_cell_edges vlo vho oute.
rewrite uocq => /(_ _ _ erefl) ->.
have u0 : uniq (bottom :: [seq high c | c <- fop] ++ [seq high c | c <- [::]] ++
  high lsto :: [seq high c | c <- lop]).
  by have := (uniq_high disng); rewrite /state_open_seq /= !map_cat.
apply: (uniq_insert_edges _ u0); first by apply: (uniq_ec comi).
move=> g; rewrite inE=> /orP[/eqP gb | gin]; last first.
  apply: (no_dup_edge comi) => //.
  by rewrite /state_open_seq /= !map_cat.
(* TODO : make this a lemma in events.v *)
- apply/negP=> gout.
have lfg : left_pt g = point ev by apply/eqP/oute.
have : inside_box bottom top (left_pt g).
  rewrite lfg; apply: (allP (inbox_events comi)).
  by rewrite map_f // inE eqxx.
move=> /andP[] /andP[] + _ _.
have vb : valid_edge bottom (left_pt g).
  by rewrite gb; have := left_on_edge bottom=> /andP[].
rewrite under_onVstrict //.
by rewrite gb left_on_edge.
- suff lst_side_lt' :
  left_limit lno < Num.min (p_x (right_pt bottom)) (p_x (right_pt top)) by [].
  have comng' :=
   update_open_cell_common_non_gp_invariant bxwf nocs' inbox_s at_lstx
   under_lsthe comng.
  have comi' := ngcomm comng'.
  have := sides_ok comi'.
  have := has_snd_lst comng'.
  rewrite /step/same_x at_lstx eqxx /= underW under_lsthe //= uocq /=.
  rewrite /state_open_seq/= all_cat /= => + /andP[] _ /andP[] + _.
  move: ev_nth1; rewrite /open_cell_side_limit_ok.
  case: left_pts => [ | a [ | b ?]] //= + _ /andP[] /andP[] _ /andP[] + _ _.
  move=> <- /eqP <-.
  apply: inside_box_lt_min_right.
  apply: (allP (inbox_events comi)).
  by rewrite map_f // inE eqxx.
Qed.

Lemma update_open_cell_edge_covered_non_gp_invariant
  bottom top s fop lsto lop cls lstc past ev
  lsthe lstx all_e evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  edge_covered_non_gp_invariant bottom top s all_e past
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  edge_covered_non_gp_invariant bottom top s all_e (rcons past ev)
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
Proof.
move=> bxwf nocs' inbox_s at_lstx under_lsthe ec_inv.
have disng := dis_inv_ec ec_inv.
have comng := common_non_gp_inv_dis disng.
have comi := ngcomm comng.
rewrite /step/=/same_x eq_sym at_lstx eqxx /=.
rewrite underW ?under_lsthe //=.
have oute : out_left_event ev.
  by apply: (out_events comi); rewrite inE eqxx.
move: (inv1 comi) => [] clae [] sval' [] adj [] cbtom rfo.
move: sval' => [ //| sval].
have at_ll : p_x (point ev) = left_limit lsto.
  by rewrite -(lstx_eq comi) at_lstx.
have hlo_eq := high_lsto_eq comi.
have lstoin : lsto \in state_open_seq (Bscan fop lsto lop cls lstc lsthe lstx).
  by rewrite /state_open_seq/= mem_cat inE eqxx orbT.
have sok := sides_ok comi.
have evin : ev \in ev :: evs by rewrite inE eqxx.
have lstok : open_cell_side_limit_ok lsto by apply: (allP sok _ lstoin).
have /andP[vlo vho] := allP sval lsto lstoin.
have evabove : point ev >>> low lsto.
  have := above_low_lsto comi evin.
  move: lstok => /andP[] lln0 /andP[] sx /andP[] _ /andP[] _ onlow.
  rewrite -at_ll in sx.
  have lstin : last dummy_pt (left_pts lsto) \in left_pts lsto.
    by case: (left_pts lsto) lln0 => //= ? ?; rewrite mem_last.
  move: (allP sx _ lstin)=> /= samex'.
  rewrite /lexPt lt_neqAle samex' /= => ab.
  have vev : valid_edge (low lsto) (point ev).
    have <- := same_x_valid (low lsto) (eqP samex').
    by move: onlow=> /andP[].
  rewrite under_pvert_y // -ltNge.
  have := on_pvert onlow.
  by have := same_pvert_y vev (esym (eqP samex')) => -> ->.
have puho : point ev <<< high lsto by rewrite hlo_eq /=.
case uoc_eq : update_open_cell => [nos lno].
rewrite /state_open_seq /state_closed_seq /=.
have n_inner2 : {in fop ++ lsto :: lop,
         forall c, non_inner (high c) (point ev)}.
  move=> c cin.
  have := edges_sub comi; rewrite /state_open_seq /= => edges_sub.
  have /edges_sub : high c \in all_edges (fop ++ lsto :: lop) (ev :: evs).
    by rewrite 2!mem_cat map_f ?orbT.
  have /inside_box_non_inner [nib nit] : inside_box bottom top (point ev).
    by have := allP (inbox_events comi) _ (map_f _ evin).
  rewrite !inE => /orP[/eqP -> | /orP [/eqP -> | hcin ]] //.
  by apply: (non_in_ec ec_inv).
have ec_cov' : {in rcons past ev, forall e, {in outgoing e, forall g,
  edge_covered g ((fop ++ nos) ++ lno :: lop)
    (rcons cls (update_closed_cell lstc (point ev)))}}.
  have cl_side' : all (@closed_cell_side_limit_ok _) (rcons cls lstc).
    by apply/allP=> c cin; apply: (cl_side disng).
  have stradle' : {in [seq high c | c <- fop ++ lsto :: lop], forall g,
    lexPt (left_pt g) (point ev) && lexePt (point ev) (right_pt g)}.
    have := step_keeps_lex_edge
      (inbox_events comi) oute rfo cbtom adj
    sval (closed_events comi) clae erefl (fun _ => evabove).
    by have [// | ]:= stradle comi.
  move=> e ein g gin.
  have ec1 : edge_covered g (fop ++ lsto :: lop) (rcons cls lstc) \/
    g \in outgoing ev.
    move: ein; rewrite mem_rcons inE => /orP[/eqP <-| eold]; first by right.
    by left; have := edge_covered_ec ec_inv eold gin.
  have := step_keeps_edge_covering (inbox_events comi) oute rfo cbtom adj
    sval erefl (lstx_eq comi) (fun _ => evabove) (sides_ok comi)
    cl_side' (size_right_cls disng) (inj_high ec_inv)
    (fun c cin => bottom_left_opens disng cin evin) n_inner2 stradle' ec1.
  rewrite /step/same_x at_lstx eqxx /=.
  by rewrite (high_lsto_eq comi) underW /= under_lsthe // uoc_eq.
have processed_covered' :
 {in rcons past ev, forall e,
   exists2 c, c \in rcons cls (update_closed_cell lstc (point ev)) &
   point e \in right_pts c /\ point e >>> low c}.
  move=> e; rewrite mem_rcons inE => /orP[/eqP -> {e}| ein].
    exists (update_closed_cell lstc (point ev)).
      by rewrite mem_rcons inE eqxx.
    split; first by apply: update_closed_cell_add.
    have : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
    move=> /(cl_side disng); do 6 (move=> /andP[] _).
    have := size_right_cls disng=> /=.
    have := lst_side_lex (common_non_gp_inv_dis disng) => /= /andP[] + _.
    have := nth1_eq disng=> /= <-.
    have : p_x (point ev) = right_limit lstc.
      by have := cl_at_lstx disng => /= ->; apply/esym.
    rewrite /right_limit.
    case: (right_pts lstc) => [ | a [ | b tl]] //= <- + _.
    move=> blexe /andP[] /andP[] _ /andP[] /eqP bx alx /andP[] /andP[] _ srt.
    have bxl : p_x b = p_x (last b tl).
      case tlq : tl => [ | c tl']; first by [].
      move: alx => /allP /(_ (last b tl)); rewrite bx.
      by rewrite tlq /= => /(_ (mem_last _ _)) /eqP <-.
    move=> /andP[] _ lon.
    have bge : p_y (last b tl) <= p_y b.
      case tlq : tl => [ | c tl'].
        by [].
      move: srt; rewrite path_sortedE; last by apply/rev_trans/lt_trans.
      move=> /andP[] /allP /(_ (p_y (last b tl))) it _.
      have : last b tl \in tl by rewrite tlq /= mem_last.
      by rewrite -tlq=> /(map_f p_y)/it/ltW.
    move: blexe; rewrite /lexPt bx eqxx ltxx /= => ygt.
    apply/negP=> abs.
    have xevl : p_x (point ev) = p_x (last b tl) by rewrite -bx.
    have vev : valid_edge (low lstc) (point ev).
      have := same_x_valid (low lstc) xevl => ->.
      by move: lon => /andP[].
    have := same_x_under_edge_lt_y_trans vev xevl (le_lt_trans bge ygt) abs.
    by rewrite (strict_nonAunder (proj2 (andP lon))) lon.
  have := processed_covered ec_inv ein.
  rewrite /state_closed_seq /= => -[c cin [pin pa]].
  move: cin; rewrite mem_rcons inE => /orP[/eqP xlstc | cin]; last first.
    exists c; last by split.
    by rewrite mem_rcons inE cin orbT.
  rewrite xlstc in pin pa.
  exists (update_closed_cell lstc (point ev)).
    by rewrite mem_rcons inE eqxx.
  split; last by move: pa; case (lstc).
  move: pin; rewrite /update_closed_cell /=.
  case : right_pts => [ | a tl] //=.
  by rewrite !inE => /orP[] ->; rewrite ?orbT.
have d_inv' :
  disjoint_non_gp_invariant bottom top s
    (Bscan (fop ++ nos) lno lop cls
      (update_closed_cell lstc (point ev)) lsthe (p_x (point ev))) 
    all_e (rcons past ev) evs.
  have := update_open_cell_disjoint_non_gp_invariant bxwf nocs' inbox_s
    at_lstx under_lsthe disng.
    rewrite /step /same_x at_lstx eqxx /=.
    by rewrite underW ?under_lsthe //= uoc_eq.
have non_in' : {in s & evs, forall g e, non_inner g (point e)}.
  by move=> g e gin ein; apply: (non_in_ec ec_inv); rewrite // inE ein orbT.
have inj_high' : {in (fop ++ nos) ++ lno :: lop &, injective high}.
  have := step_keeps_injective_high (inbox_events comi) oute rfo
   cbtom adj sval erefl (fun _ => evabove)
   (sides_ok comi) (uniq_ec comi evin) (inj_high ec_inv)
   (fun c cin => bottom_left_opens disng cin evin)
   (map_uniq (proj2 (andP (uniq_high disng)))) => /(_ cls lstc lstx).
  rewrite /step/same_x at_lstx eqxx (underW puho) puho /=.
  by rewrite uoc_eq.
by constructor.
Qed.

Lemma update_open_cell_left_Limit fop lsto lop ev nos lno:
  out_left_event ev ->
  seq_valid (fop ++ lsto :: lop) (point ev) ->
  all open_cell_side_limit_ok (fop ++ lsto :: lop) ->
  (1 < size (left_pts lsto))%N ->
  update_open_cell lsto ev = (nos, lno) ->
  p_x (point ev) = left_limit lsto ->
  point ev <<< high lsto ->
  point ev >>> low lsto ->
  lexPt (nth dummy_pt (left_pts lsto) 1) (point ev) ->
  {in rcons nos lno, forall c, left_limit c = p_x (point ev)}.
Proof.
move=> oute sval oks sl uoc_eq at_ll puh ev_above lex1.
have oute' : {in sort edge_below (outgoing ev),
   forall g, left_pt g == (point ev)}.
  by move=> g; rewrite mem_sort; apply: oute.
have lstoin : lsto \in fop ++ lsto :: lop by rewrite mem_cat inE eqxx orbT.
have lstok : open_cell_side_limit_ok lsto by apply: (allP oks).
have : all ((@lexPt _)^~ (point ev)) (behead (left_pts lsto)).
  move: lstok sl lex1=> /andP[] _ /andP[] + /andP[] + _.
  case lq : left_pts => [ | a [ | b tl]] //= /andP[] /eqP xa /andP[] /eqP xb.
  move=> xs /andP[] blta stl _ /[dup] lexb -> /=.
  apply/allP=> p pin; apply/orP; right.
  rewrite at_ll (allP xs _ pin) /=.
  move: lexb; rewrite /lexPt at_ll xb ltxx eqxx /=; apply/lt_trans.
  move: stl; rewrite (path_sortedE (rev_trans lt_trans))=> /andP[] + _.
  by move=> /allP /(_ _ (map_f _ pin)).
move=> lextl.
have oks' := update_open_cell_side_limit_ok oute sval oks lextl
 uoc_eq at_ll puh ev_above.
have [vl vh] : valid_edge (low lsto) (point ev) /\
                valid_edge (high lsto) (point ev).
  exact: (andP (allP sval _ lstoin)).
move=> c; rewrite mem_rcons inE orbC.
have := opening_cells_left oute vl vh; rewrite /opening_cells.
move=> /[swap].
move=> /orP[cin | /eqP ->].
  have := update_open_cellE1 oute vl vh lstok at_ll sl ev_above puh.
  rewrite uoc_eq /= => /(_ c cin) [c' + cc'].
  case oca_eq : opening_cells_aux => [nos' lno'] /= c'in.
  have c'in2 : c' \in rcons nos' lno' by rewrite mem_rcons inE c'in orbT.
  move=> /(_ _ c'in2).
  case: cc' => [ <- // | [l lstl [lq cc']]].
  by rewrite /left_limit cc' left_pts_set lstl.
have := update_open_cellE2 oute vl vh lstok at_ll sl ev_above puh.
rewrite uoc_eq /=.
case oca_eq : opening_cells_aux => [nos' lno'] /= [] ->.
  by apply; rewrite mem_rcons inE eqxx.
move=> _; move: sl at_ll; rewrite /left_limit.
by case : left_pts => [ | a [ | b tl]].
Qed.

Lemma on_edge_vertical p g : p === g ->
  vertical_projection p g = Some p.
Proof.
move=> /[dup] pong /andP[] _ vp.
rewrite (pvertE vp) (on_pvert pong).
congr (Some _).
by apply/eqP; rewrite pt_eqE /= !eqxx.
Qed.

Lemma update_closed_cell_safe_side_right lstc pev p :
  (1 < size (right_pts lstc))%N ->
  in_safe_side_right p (update_closed_cell lstc pev) ->
  in_safe_side_right p lstc && (p != pev).
Proof.
rewrite /in_safe_side_right/right_limit/=.
case rpq : right_pts => [ | a [ | b tl]] //= _.
move=> /andP[] -> /andP[] -> /andP[] -> /=.
by rewrite !inE !negb_or=> /andP[] -> /andP[] -> /andP[] -> ->.
Qed.

Lemma update_open_cell_safe_side lsto nos lno p ev c:
  out_left_event ev ->
  valid_edge (low lsto) (point ev) ->
  valid_edge (high lsto) (point ev) ->
  point ev <<< high lsto ->
  point ev >>> low lsto ->
  p_x (point ev) = left_limit lsto ->
  (1 < size (left_pts lsto))%N ->
  lexPt (nth dummy_pt (left_pts lsto) 1) (point ev) ->
  open_cell_side_limit_ok lsto ->
  update_open_cell lsto ev = (nos, lno) ->
  c \in rcons nos lno ->
  in_safe_side_left p c ->
  in_safe_side_left p lsto && (p != point ev).
Proof.
move=> oute vl vh puho palo at_ll sl lex1 lstok.
have oute' :
  {in sort edge_below (outgoing ev), forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
rewrite /update_open_cell.
case ogq : outgoing => [ | fog ogs].
  move=> -[] <- <- /=.
  move: (sl).
  case lq : left_pts => [ | a [ | b tl]] //= _.
  move=> cin; rewrite /in_safe_side_left/left_limit lq /=.
  move: cin; rewrite inE => /eqP ->.
  rewrite left_pts_set /= => /andP[] -> /andP[] -> /andP[] -> /=.
  by rewrite !inE !negb_or => /andP[] -> /andP[] -> /andP[] -> ->.
have sz : (0 < size (sort edge_below (outgoing ev)))%N.
  by rewrite size_sort ogq.
rewrite ogq in sz.
move: oute'; rewrite ogq.
case: (sort edge_below (fog :: ogs)) sz => //= f l _ oute'.
rewrite pvertE //.
case oca_eq: opening_cells_aux => [nos' lno'] [] <- <-.
rewrite /= inE=> /orP[/eqP -> /[dup] W| ].
(*  have xlst : p_x (last (point ev) (behead (left_pts lsto))) =
              p_x (last dummy_pt (left_pts lsto)). 
    by case: left_pts sl => [ | a [ | b tl]]. *)
  rewrite -/(_ == _).
  rewrite /in_safe_side_left /=.
  rewrite /left_limit !inE !negb_or.
  rewrite left_pts_set /=.
  move=> /andP[] /[dup] /eqP xp _ /andP[] puf /andP[] -> /andP[] ->.
  rewrite /= andbT.
  have xs : p_x p = p_x (point ev).
    by rewrite xp at_ll.
  have vpf : valid_edge f p.
    rewrite (same_x_valid f xs) -(eqP (oute' f _)) ?inE ?eqxx //.
    by rewrite valid_edge_left.
  have evf : point ev === f.
    by rewrite -(eqP (oute' f _)) ?inE ?eqxx // left_on_edge.
  have ylowev: p_y p < p_y (point ev).
      by rewrite -(strict_under_edge_lower_y _ evf).
  have vph : valid_edge (high lsto) p.
    by rewrite (same_x_valid (high lsto) xs).
  have puh : p <<< high lsto.
    have /esym := strict_under_pvert_y vh.
    rewrite puho => yevuh.
    have := lt_trans ylowev yevuh.
    have  -> := same_pvert_y vh (esym xs).
    by rewrite -strict_under_pvert_y.
  rewrite puh /=.
  have := lstok => /andP[] _ /andP[] allx /andP[] srt /andP[] hon _.
  have pnh : p != head dummy_pt (left_pts lsto).
    apply/eqP=> abs.
    by move: puh; rewrite abs (strict_nonAunder (proj2 (andP hon))) hon.
  rewrite xs at_ll eqxx /=.
  case: left_pts sl pnh => [ | a tl] //= _.
  by rewrite inE negb_or => -> ->.
elim: l f oute' nos' lno' oca_eq c => [ | s l Ih] f oute' nos' lno' oca_eq c
  cin spc.
  move: oca_eq; rewrite /=.
  have -> : vertical_projection (point ev) f = Some (point ev).
    apply: on_edge_vertical.
    rewrite -(eqP (oute' f _)); last by rewrite inE eqxx.
    by apply: left_on_edge.
  rewrite (pvertE vh) => -[] /esym nos'q /esym lno'q.
  rewrite nos'q lno'q /= inE in cin.
  move: cin=> /eqP.
  case: ifP => [c1 | c2].
    have abs : point ev === high lsto.
      have := pvert_on vh; move: c1; case: (point ev) => px py /= /andP[] _.
      by move=> /eqP ->.
    rewrite -/(point ev == point ev) eqxx.
    by move: puho; rewrite (strict_nonAunder vh) abs.
  rewrite -/(_ == _) eqxx => cq.
  move: spc; rewrite cq.
  move=> /andP[]; rewrite /left_limit /= => /eqP xs /andP[] pu /andP[] pa.
  rewrite !inE !negb_or => /andP[] pd ->.
  rewrite /in_safe_side_left xs at_ll eqxx pu /= andbT.
  have evf : point ev === f.
    by rewrite -(eqP (oute' f _)) ?inE ?eqxx // left_on_edge.
  have vpl : valid_edge (low lsto) p.
    by rewrite (same_x_valid (low lsto) xs).
  have vpf : valid_edge f p.
    rewrite (same_x_valid f xs) -(eqP (oute' f _)) ?inE ?eqxx //.
    by rewrite valid_edge_left.
  have phighev : p_y (point ev) < p_y p.
    rewrite -(on_pvert evf) -(same_pvert_y vpf xs).
    rewrite ltNge -(under_pvert_y) ?pa //.
  apply/andP; split.
    rewrite under_pvert_y // -ltNge (lt_trans _ phighev) // ltNge.
    by rewrite (same_pvert_y vpl xs) -under_pvert_y.
  have := lstok => /andP[] _ /andP[] allx /andP[] srt /andP[] hon _.
  have hx : p_x (head dummy_pt (left_pts lsto)) = p_x (point ev).
    rewrite at_ll; apply/eqP/(allP allx).
    by move: sl; case: left_pts => [ | ? ?]; rewrite // inE eqxx.
  have hq : head dummy_pt (left_pts lsto) =
      Bpt (p_x (point ev)) (pvert_y (point ev) (high lsto)).
    rewrite (same_pvert_y vh (esym hx)) -hx (on_pvert hon).
    by apply/eqP; rewrite pt_eqE /= !eqxx.
  case lq : left_pts sl => [ | a [ | b tl]] //= _.
  rewrite !inE !negb_or.
  move: pd; rewrite -hq lq /= => -> /=.
  move: allx; rewrite lq /= => /andP[] _ /andP[] /eqP xb allx.
  move: lex1; rewrite lq /= /lexPt at_ll xb ltxx eqxx /= => yb.
  have := lt_trans yb phighev; rewrite lt_neqAle => /andP[] bp _.
  rewrite pt_eqE (eq_sym (p_y _)) negb_and bp orbT /=.
  apply/negP=> pintl.
  move: srt; rewrite lq /= => /andP[] _.
  rewrite (path_sortedE (rev_trans lt_trans))=> /andP[] + _.
  move=> /allP/(_ (p_y p) (map_f _ pintl)) /lt_trans /(_ yb).
  by move=> /lt_trans /(_ phighev); rewrite ltxx.
move: oca_eq; rewrite /=.
case oca_eq : opening_cells_aux => [nos2 lno2].
rewrite on_edge_vertical; last first.
  by rewrite -(eqP (oute' f _)) ?left_on_edge ?inE ?eqxx.
move=> -[] /esym nos2q /esym lno2q.
move: cin; rewrite nos2q lno2q /= inE.
rewrite -/(_ == _) eqxx => /orP[ /eqP cq| cin].
  move: spc; rewrite cq=> /andP[].
  rewrite /left_limit /= => /eqP xs /andP[] pus /andP[] puf.
  have evons : point ev === s.
    by rewrite -(eqP (oute' s _)) ?left_on_edge ?inE ?eqxx ?orbT.
  have evonf : point ev === f.
    by rewrite -(eqP (oute' f _)) ?left_on_edge ?inE ?eqxx.
  have ypltev : p_y p < p_y (point ev).
    have /esym := strict_under_edge_lower_y xs evons.
    by rewrite pus.
  have ypgtev : p_y (point ev) < p_y p.
    rewrite ltNge.
    have <- := under_edge_lower_y xs evonf.
    by rewrite puf.
  by have := lt_trans ypltev ypgtev; rewrite ltxx.
have oute2 : {in s :: l, forall g, left_pt g == point ev}.
  by move=> g gin; apply: oute'; rewrite inE gin orbT.
by have := Ih s oute2 nos2 lno2 oca_eq c cin spc.
Qed.

Lemma update_open_cell_safe_side_non_gp_invariant
  bottom top s fop lsto lop cls lstc all_e past ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  safe_side_non_gp_invariant bottom top s all_e past
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  safe_side_non_gp_invariant bottom top s all_e (rcons past ev)
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s at_lstx under_lsthe s_inv.
set st := Bscan fop lsto lop cls lstc lsthe lstx.
have ec_inv := covered_ss s_inv.
have d_inv := disjoint_ss s_inv.

(* TODO : unpleasant duplication *)
have comi := (ngcomm (common_non_gp_inv_dis d_inv)).
move: (inv1 comi).
move=> [] clae [] sval' [] adj [] cbtom rfo.
move: sval' => [ //| sval].
have at_ll : p_x (point ev) = left_limit lsto.
  by rewrite -(lstx_eq comi) at_lstx.
have hlo_eq := high_lsto_eq comi.
have lstoin : lsto \in state_open_seq (Bscan fop lsto lop cls lstc lsthe lstx).
  by rewrite /state_open_seq/= mem_cat inE eqxx orbT.
have sok := sides_ok comi.
have evin : ev \in ev :: evs by rewrite inE eqxx.
have lstok : open_cell_side_limit_ok lsto by apply: (allP sok _ lstoin).
have /andP[vlo vho] := allP sval lsto lstoin.
have evabove : point ev >>> low lsto.
  have := above_low_lsto comi evin.
  move: lstok => /andP[] lln0 /andP[] sx /andP[] _ /andP[] _ onlow.
  rewrite -at_ll in sx.
  have lstin : last dummy_pt (left_pts lsto) \in left_pts lsto.
    by case: (left_pts lsto) lln0 => //= ? ?; rewrite mem_last.
  move: (allP sx _ lstin)=> /= samex'.
  rewrite /lexPt lt_neqAle samex' /= => ab.
  have vev : valid_edge (low lsto) (point ev).
    have <- := same_x_valid (low lsto) (eqP samex').
    by move: onlow=> /andP[].
  rewrite under_pvert_y // -ltNge.
  have := on_pvert onlow.
  by have := same_pvert_y vev (esym (eqP samex')) => -> ->.
have puho : point ev <<< high lsto by rewrite hlo_eq /=.
have sll : (1 < size (left_pts lsto))%N.
  by apply: (size_left_lsto sval erefl (sides_ok comi) at_ll evabove
      (underW puho)).

have oute : out_left_event ev.
  by apply: (out_events (ngcomm (common_non_gp_inv_dis d_inv))).

have d_inv' : disjoint_non_gp_invariant bottom top s
  (step st ev) all_e (rcons past ev) evs.
  by apply: update_open_cell_disjoint_non_gp_invariant.
have ec_inv' : edge_covered_non_gp_invariant bottom top s 
  all_e (rcons past ev)
  (step st ev) evs.
  by apply: update_open_cell_edge_covered_non_gp_invariant.

have nth1eq : nth dummy_pt (left_pts (lst_open (step st ev))) 1 = point ev.
  rewrite /step /same_x /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
  have [] := update_open_cellE2 oute vlo vho lstok at_ll sll evabove puho.
    case uoc_eq : update_open_cell => [nos lno] /= ->.
    have := last_opening_cells_left_pts_prefix vlo vho puho oute.
    case oca_eq : opening_cells_aux => [nos' lno']=> /(_ _ _ erefl) [] /=.
    by case: (left_pts lno') => [ | a [ | b tl]] //= _ [] _.
  by case uoc_eq : update_open_cell => [nos lno] /= ->.

have left_Proc': {in rcons past ev,
  forall e, lexePt (point e)
    (nth dummy_pt (left_pts (lst_open (step st ev))) 1)}.
  rewrite nth1eq.
  move=> e; rewrite mem_rcons inE orbC=> /orP[eold | /eqP ->]; last first.
    by apply: lexePt_refl.
  have := lst_side_lex (common_non_gp_inv_dis d_inv) => /= /andP[] + _.
  apply: (fun h h1 => lexPtW (lexePt_lexPt_trans h h1)).
  by apply: (left_proc s_inv).
have sub_closed' :
  {subset cell_edges (state_closed_seq (step st ev)) <= [:: bottom, top & s]}.
  rewrite /step /same_x /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
  rewrite /state_closed_seq /=.
  case uoc_eq : update_open_cell => [lno nos] /=.
  move=> g; rewrite -cats1 cell_edges_cat mem_cat cell_edges_cons.
  have [-> ->]:= update_closed_cell_edges lstc (point ev) => gin.
  apply: (sub_closed s_inv).
  by rewrite /state_closed_seq /= -cats1 cell_edges_cat mem_cat cell_edges_cons.
have cl_at_left' : {in sc_closed (step st ev),
     forall c, lexePt (head dummy_pt (right_pts c))
      (nth dummy_pt (left_pts (lst_open (step st ev))) 1)}.
  move: nth1eq.
  rewrite /step /same_x /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
  case uoc_eq : update_open_cell => [lno nos] /= nth1eq.
  move=> c cin.
  have := (cl_at_left_ss s_inv cin) => /= /lexePt_trans; apply.
  rewrite nth1eq.
  by have := lst_side_lex (common_non_gp_inv_dis d_inv) => /= /andP[] /lexPtW.
have lstcok : closed_cell_side_limit_ok lstc.
  by apply: (cl_side d_inv); rewrite mem_rcons inE eqxx.
have srltsc : (1 < size (right_pts lstc))%N.
  by apply: (size_right_cls d_inv).

have closed_safe_viz_past_edges :
 {in events_to_edges (rcons past ev) & state_closed_seq (step st ev),
 forall (g : edge) (c : cell) (p : pt),
   in_safe_side_left p c || in_safe_side_right p c -> ~ p === g}.
  move=> g c gin cin p pin pong.
  move: gin; rewrite events_to_edges_rcons mem_cat=> /orP[gin | gnew].
    move: cin.
    rewrite /step/same_x /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
    case uoc_eq : update_open_cell => [nos lno].
    rewrite /state_closed_seq /= mem_rcons inE => /orP[/eqP cup | ccls].
      have lstcin : lstc \in state_closed_seq st.
        by rewrite /state_closed_seq/st/= mem_rcons inE eqxx.
      have pin' : in_safe_side_left p lstc || in_safe_side_right p lstc.
        move: pin=> /orP[pin | pin]; apply/orP;[left | right].
          by move: pin; rewrite cup; case: (lstc).
        move: pin; rewrite /in_safe_side_right cup.
        have [-> ->] := update_closed_cell_edges lstc (point ev).
        rewrite update_closed_cell_keeps_right_limit //.
        move=> /andP[] -> /andP[] -> /andP[] ->.
        rewrite /update_closed_cell /=.
        case: (right_pts lstc)=> //= a b; rewrite !inE orbCA negb_or.
        by move=> /andP[] _ ->.
      by have := safe_side_closed_edges s_inv gin lstcin pin' pong.
    have cin' : c \in rcons cls lstc by rewrite mem_rcons inE ccls orbT.
    by have := safe_side_closed_edges s_inv gin cin' pin pong.
  have valc : (c \in cls) \/ (c = update_closed_cell lstc (point ev)).
    move: cin.
    rewrite /step/same_x /st /= at_lstx eqxx.
    rewrite (underW under_lsthe) under_lsthe /=.
    case uoc_eq : update_open_cell => [nos lno].
    rewrite /state_closed_seq /= mem_rcons inE => /orP[/eqP -> | cin].
      by right.
    by left.
  have lift_cls : {subset cls <= rcons cls lstc}.
    by move=> c' cin'; rewrite mem_rcons inE cin' orbT.
  have lift_lstc : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
  have rle : right_limit c <= p_x (point ev).
    case: valc => [/lift_cls cin' | valc].
      by have := closed_at_left_non_gp d_inv cin'; rewrite /= at_lstx.
    have := closed_at_left_non_gp d_inv lift_lstc; rewrite /= at_lstx.
    by rewrite valc update_closed_cell_keeps_right_limit.
  move: pin => /orP[] pin.
    have pgtev : p_x p < p_x (point ev).
      have plt_right : p_x p < right_limit c.
        move: pin=> /andP[] /eqP -> _.
        move: valc=> [/lift_cls c'in | ->].
          by have := cl_large d_inv c'in.
        rewrite update_closed_cell_keep_left_limit.
        rewrite update_closed_cell_keeps_right_limit //.
        by apply: (cl_large d_inv lift_lstc).
      by apply: (lt_le_trans plt_right rle).
    move: pong => /andP[] _ /andP[] + _.
    by rewrite (eqP (oute _ gnew)) leNgt pgtev.
  have lg : left_pt g = point ev by apply/eqP/oute.
  have samex : p_x p = p_x (left_pt g).
    apply: le_anti.
    rewrite (eqP (proj1 (andP pin))) lg rle.
      case: valc rle pin=> [/lift_cls c'in rle | -> _] pin.
      rewrite -(eqP (proj1 (andP pin))) -lg.
      by move: pong=> /andP[] _ /andP[].
    move: pin=> /andP[] + _.
    rewrite update_closed_cell_keeps_right_limit // -lg => /eqP <- /=.
    by move: pong => /andP[] _ /andP[].
  have samey := on_edge_same_point pong (left_on_edge _) samex.
  have pev : p = point ev by apply/eqP; rewrite pt_eqE samex samey lg !eqxx.
  move: valc (pin)=> -[valc  | -> ]; last first.
    rewrite pev /in_safe_side_right/update_closed_cell.
    by move=> /andP[] _ /andP[] _ /andP[] _; rewrite !inE eqxx !orbT.
  rewrite pev=> {} pin.
  have ph :=
    in_safe_side_right_top_right (cl_side d_inv (lift_cls _ valc)) pin.
  have hm : lexePt (head dummy_pt (right_pts c))
              (nth dummy_pt (left_pts lsto) 1).
    by have := cl_at_left_ss s_inv valc=> /=.
  have mp : lexPt (nth dummy_pt (left_pts lsto) 1) (point ev).
    by have := lst_side_lex (common_non_gp_inv_dis d_inv)=> /andP[].
  by have := lexPt_trans (lexPt_lexePt_trans ph hm) mp; rewrite lexPt_irrefl.

have nth1oev : lexPt (nth dummy_pt (left_pts lsto) 1) (point ev).
  by have := lst_side_lex (common_non_gp_inv_dis d_inv) => /= /andP[].

have lstcin : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.

have open_safe_viz_past_edges :
  {in events_to_edges (rcons past ev) & state_open_seq (step st ev),
    forall g c p, in_safe_side_left p c -> ~ p === g}.
  rewrite /step/same_x  /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
  case uoc_eq : update_open_cell => [nos lno].
  rewrite /state_open_seq/=.
  move=> g c; rewrite events_to_edges_rcons mem_cat => /orP[gold | gnew].
    rewrite -catA -cat_rcons !mem_cat orbCA orbC => /orP[cold | cnew].
      apply: (safe_side_open_edges s_inv); first by [].
      by rewrite /state_open_seq /= mem_cat inE orbCA orbC cold.
    move=> p pin pong.
    have := update_open_cell_safe_side oute vlo vho puho evabove at_ll
      sll nth1oev lstok uoc_eq cnew pin.
    move=> /andP[] spl pnev.
    by have := safe_side_open_edges s_inv gold lstoin spl pong.
  rewrite -catA -cat_rcons !mem_cat orbCA orbC=> /orP[cold | cnew].
    move=> p pin pong.
    have xp : p_x p = p_x (point ev).
      have xpl : p_x p <= p_x (point ev).
        move: pin=> /andP[] /eqP -> _.
        have := bottom_left_opens d_inv; rewrite /state_open_seq/=.
        move=> /(_ c ev).
        rewrite !mem_cat orbCA orbC cold inE eqxx=> /(_ isT isT).
        have cok : open_cell_side_limit_ok c.
           apply: (allP (sides_ok comi)); rewrite /state_open_seq /=.
           by rewrite mem_cat inE orbCA cold orbT.
        rewrite /lexPt -bottom_left_x //.
        rewrite -(open_cell_side_limit_ok_last cok).
        by move=> /orP[/ltW // | /andP[] /eqP -> _].
      apply/le_anti; rewrite xpl /= -(eqP (oute g gnew)).
      by move: pong=> /andP[] _ /andP[].
    have evon : point ev === g.
      by rewrite -(eqP (oute g gnew)) left_on_edge.
    have pev : p = point ev.
      have yp := on_edge_same_point pong evon xp.
      by apply/eqP; rewrite pt_eqE xp yp !eqxx.
    (* TODO: probably needs a duplication here. MARKER *)
    have [vevhc vevlc] : valid_edge (high c) (point ev) /\
      valid_edge (low c) (point ev).
      have := (allP sval c); rewrite /state_open_seq/= mem_cat inE orbCA.
      by rewrite cold orbT=> /(_ isT) /andP[]; split.
    move: cold=> /orP[clow | chigh].
      have puc : p <<< high c.
        by move: pin=> /andP[] _ /andP[].
      have hcb : high c <| low lsto.
        have [s1 [ s2 s1q]] := mem_seq_split clow.
          elim/last_ind : {2} s2 (erefl s2) => [ | s2' ls2 _] s2q.
          move: adj; rewrite /state_open_seq/= s1q s2q /= -catA /=.
          move=> /adjacent_catW[] _ /= /andP[] /eqP -> _.
          by apply: edge_below_refl.
        move: adj; rewrite /state_open_seq/= s1q s2q /= -catA /= cat_rcons.
        rewrite -cat_rcons=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
        move=> /andP[] /eqP <- _.
        have := pairwise_open_non_gp d_inv.
        rewrite /state_open_seq/= s1q s2q /=.
        move=> /andP[] _.
        rewrite map_cat pairwise_cat=> /andP[] _ /andP[] + _.
        rewrite map_cat pairwise_cat=> /andP[] _ /andP[] _.
        rewrite /= => /andP[] /allP /(_ (high ls2)) + _.
        by apply;  apply/map_f; rewrite mem_rcons inE eqxx.
      have pul : p <<= low lsto.
        by apply: (order_edges_viz_point _ _ hcb (underW puc)); rewrite pev.
      by rewrite pev in pul; rewrite pul in evabove.
    have pac : p >>> low c.
      by move: pin=> /andP[] _ /andP[] _ /andP[].
    have hlb : high lsto <| low c.
      have [s1 [ s2 sq]] := mem_seq_split chigh.
        elim/last_ind : {2} s1 (erefl s1) => [ | s1' ls1 Ih] s1q.
        move: adj; rewrite /state_open_seq/= sq s1q /=.
        move=> /adjacent_catW[] _ /= /andP[] /eqP -> _.
        by rewrite edge_below_refl.
      move: adj; rewrite /state_open_seq/= sq s1q /= cat_rcons -cat_rcons.
      move=> /adjacent_catW[] _ /adjacent_catW[] _ /= /andP[] /eqP <- _.
      have := pairwise_open_non_gp d_inv.
      rewrite /state_open_seq/= sq s1q /=.
      move=> /andP[] _.
      rewrite map_cat pairwise_cat=> /andP[] _ /andP[] _ /= /andP[] + _.
      move=> /allP /(_ (high ls1) (map_f _ _)); apply.
      by rewrite mem_cat mem_rcons inE eqxx.
    case/negP: pac.
    rewrite pev.
    by apply: (order_edges_viz_point vho vevlc hlb (underW puho)).
  move=> p pin pong.
  have xp : p_x p = p_x (point ev).
    have := update_open_cell_left_Limit oute sval sok sll uoc_eq at_ll puho
      evabove nth1oev cnew.
    by move: pin=> /andP[] /eqP -> _.
  have evon : point ev === g.
    by rewrite -(eqP (oute g gnew)) left_on_edge.
  have pev : p = point ev.
    have yp := on_edge_same_point pong evon xp.
    by apply/eqP; rewrite pt_eqE xp yp !eqxx.
  have := update_open_cell_safe_side oute vlo vho puho evabove at_ll
    sll nth1oev lstok uoc_eq cnew pin.
  by rewrite pev eqxx; move=> /andP[] spl.
have closed_safe_viz_past_events :
  {in rcons past ev & state_closed_seq (step st ev), forall e c p,
  in_safe_side_left p c || in_safe_side_right p c -> p != point e}.
  rewrite /step/same_x /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
  case uoc_eq : update_open_cell => [nos lno].
  rewrite /state_closed_seq /=.
  move=> e c; rewrite mem_rcons inE orbC=> /orP[eold | enew].
    rewrite mem_rcons inE orbC=> /orP[cold | /eqP ->].
      apply: (safe_side_closed_points s_inv)=> //.
      by rewrite /state_closed_seq /= mem_rcons inE cold orbT.
    move=> p /orP[pleft | pright].
      have psl : in_safe_side_left p lstc by exact: pleft.
      apply: (safe_side_closed_points s_inv eold lstcin).
      by rewrite psl.
    have := update_closed_cell_safe_side_right srltsc pright.
    move=> /andP[] psr pnev.
    apply: (safe_side_closed_points s_inv eold lstcin).
    by rewrite psr orbT.
  rewrite (eqP enew).
  rewrite mem_rcons inE => /orP[/eqP -> | cold].
    move=> p /orP[pleft | pright].
      suff xpltev : p_x p < p_x (point ev).
        by apply/eqP=> abs; rewrite abs ltxx in xpltev.
      have -> : p_x p = left_limit lstc.
        move: pleft.
        by rewrite /in_safe_side_left/left_limit /= => /andP[] /eqP.
      have := cl_large d_inv lstcin => /lt_le_trans; apply.
      by have := closed_at_left_non_gp d_inv lstcin; rewrite at_lstx.
    by have := update_closed_cell_safe_side_right srltsc pright=> /andP[].
  move=> p psafe.
  have cin : c \in rcons cls lstc by rewrite mem_rcons inE cold orbT.
  have cok : closed_cell_side_limit_ok c by apply: (cl_side d_inv).
  have  ptrc := in_safe_side_top_right cok (cl_large d_inv cin) psafe.
  have /= trcnth1 := cl_at_left_ss s_inv cold.
  have /= /andP[nth1ev _]:= lst_side_lex (common_non_gp_inv_dis d_inv).
  apply/eqP=> abs.
  have := lexPt_trans ptrc (lexePt_lexPt_trans trcnth1 nth1ev).
  by rewrite abs lexPt_irrefl.
have open_safe_viz_past_events :
  {in rcons past ev & state_open_seq (step st ev),
   forall e c p, in_safe_side_left p c -> p != point e}.
  rewrite /step/same_x /= at_lstx eqxx (underW under_lsthe) under_lsthe /=.
  case uoc_eq : update_open_cell => [nos lno].
  rewrite /state_open_seq /= -catA -cat_rcons.
  move=> e c; rewrite mem_rcons inE orbC=> /orP[eold | enew].
    rewrite !mem_cat orbCA orbC=> /orP[cold | cnew].
      apply: (safe_side_open_points s_inv) => //.
      by rewrite /state_open_seq /= mem_cat inE orbCA cold orbT.
    move=> p pin.
    have := update_open_cell_safe_side oute vlo vho puho evabove at_ll sll
      nth1oev lstok uoc_eq cnew pin.
    move=> /andP[] psl pnev.
    by have := safe_side_open_points s_inv eold lstoin psl.
  rewrite (eqP enew).
  rewrite !mem_cat orbCA orbC => /orP[cold | cnew] p pin.
  apply/eqP=> pev.
  (* TODO: duplication MARKER *)
  have [vevhc vevlc] : valid_edge (high c) (point ev) /\
      valid_edge (low c) (point ev).
      have := (allP sval c); rewrite /state_open_seq/= mem_cat inE orbCA.
      by rewrite cold orbT=> /(_ isT) /andP[]; split.
    move: cold=> /orP[clow | chigh].
      have puc : p <<< high c.
        by move: pin=> /andP[] _ /andP[].
      have hcb : high c <| low lsto.
        have [s1 [ s2 s1q]] := mem_seq_split clow.
          elim/last_ind : {2} s2 (erefl s2) => [ | s2' ls2 _] s2q.
          move: adj; rewrite /state_open_seq/= s1q s2q /= -catA /=.
          move=> /adjacent_catW[] _ /= /andP[] /eqP -> _.
          by apply: edge_below_refl.
        move: adj; rewrite /state_open_seq/= s1q s2q /= -catA /= cat_rcons.
        rewrite -cat_rcons=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
        move=> /andP[] /eqP <- _.
        have := pairwise_open_non_gp d_inv.
        rewrite /state_open_seq/= s1q s2q /=.
        move=> /andP[] _.
        rewrite map_cat pairwise_cat=> /andP[] _ /andP[] + _.
        rewrite map_cat pairwise_cat=> /andP[] _ /andP[] _.
        rewrite /= => /andP[] /allP /(_ (high ls2)) + _.
        by apply;  apply/map_f; rewrite mem_rcons inE eqxx.
      have pul : p <<= low lsto.
        by apply: (order_edges_viz_point _ _ hcb (underW puc)); rewrite pev.
      by rewrite pev in pul; rewrite pul in evabove.
    have pac : p >>> low c.
      by move: pin=> /andP[] _ /andP[] _ /andP[].
    have hlb : high lsto <| low c.
      have [s1 [ s2 sq]] := mem_seq_split chigh.
        elim/last_ind : {2} s1 (erefl s1) => [ | s1' ls1 Ih] s1q.
        move: adj; rewrite /state_open_seq/= sq s1q /=.
        move=> /adjacent_catW[] _ /= /andP[] /eqP -> _.
        by rewrite edge_below_refl.
      move: adj; rewrite /state_open_seq/= sq s1q /= cat_rcons -cat_rcons.
      move=> /adjacent_catW[] _ /adjacent_catW[] _ /= /andP[] /eqP <- _.
      have := pairwise_open_non_gp d_inv.
      rewrite /state_open_seq/= sq s1q /=.
      move=> /andP[] _.
      rewrite map_cat pairwise_cat=> /andP[] _ /andP[] _ /= /andP[] + _.
      move=> /allP /(_ (high ls1) (map_f _ _)); apply.
      by rewrite mem_cat mem_rcons inE eqxx.
    case/negP: pac.
    rewrite pev.
    by apply: (order_edges_viz_point vho vevlc hlb (underW puho)).
  have := update_open_cell_safe_side oute vlo vho puho evabove at_ll sll
      nth1oev lstok uoc_eq cnew pin.
  by move=> /andP[].
by constructor.
Qed.

End working_environment.
