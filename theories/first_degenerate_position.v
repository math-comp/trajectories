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

Lemma update_open_cell_common_invariant
  bottom top s fop lsto lop cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  common_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  common_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
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
    move: Pc gq=> [-> | [l lv ->]].
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
  rewrite gc; move=> -[-> | [l lprop ->]]; first by [].
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
by constructor.
Qed.

Lemma update_open_cell_common_non_gp_invariant
  bottom top s fop lsto lop cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  common_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  common_non_gp_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
Proof.
move=> bxwf nocs' inbox_s at_lstx under_lsthe comng.
have comi := ngcomm comng.
set st := Bscan _ _ _ _ _ _ _.
have oute : out_left_event ev.
  by apply: (out_events comi); rewrite inE eqxx.
have ci : common_invariant bottom top s (step st ev) evs.
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
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  lstx = p_x (point ev) ->
  (point ev) <<< lsthe ->
  disjoint_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  disjoint_non_gp_invariant bottom top s
     (step (Bscan fop lsto lop cls lstc lsthe lstx) ev)
    evs.
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
  move => [ -> | [l lprop ->]].
    move: c'in main; case: opening_cells_aux=> [a b] /= c'in; apply.
    by rewrite !(mem_cat, inE) c'in orbT.
  move: c'in main; case: opening_cells_aux => [a b] /= c'in main.
  have : lexPt (bottom_left_corner c') (point e).
    by apply: main; rewrite !mem_cat c'in orbT.
  by rewrite /bottom_left_corner left_pts_set lprop.
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
    move=> /=[c' c'in [cc' | [l lprop cc']]].
      by have := mainop c' (c'in2 _ c'in); rewrite -cc'.
    rewrite cc' /bottom_left_corner left_pts_set lprop.
    by have := mainop c' (c'in2 _ c'in).
  rewrite pteq.
  by move: cnew; rewrite mem_rcons inE => /orP[/eqP -> | /main_nos].
- rewrite /state_closed_seq/=.
  move=> c; rewrite mem_rcons inE => /orP[/eqP -> | cold].
    have szc : (1 < size (right_pts lstc))%N.
      by apply: (size_right_cls disng).
    rewrite -inside_closed'_update // update_closed_cell_center //.
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
apply/negP=> gout.
have lfg : left_pt g = point ev by apply/eqP/oute.
have : inside_box bottom top (left_pt g).
  rewrite lfg; apply: (allP (inbox_events comi)).
  by rewrite map_f // inE eqxx.
move=> /andP[] /andP[] + _ _.
have vb : valid_edge bottom (left_pt g).
  by rewrite gb; have := left_on_edge bottom=> /andP[].
rewrite under_onVstrict //.
by rewrite gb left_on_edge.
Qed.

End working_environment.