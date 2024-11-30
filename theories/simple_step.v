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
 
Lemma simple_step_common_invariant
  bottom top s fop lsto lop fc cc lcc lc le he cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  common_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  common_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s oe.
move=> []; rewrite /state_open_seq/state_closed_seq/=.
move=> inv lstxq lstheq sub_edges cle out_es uniqout /[dup] inbox0.
move=> /andP[] inbox_e inbox_es.
move=> no_dup lexev oks lexpt1.
move: (inv)=> [] clae [] []; first by [].
move=> sval [] adj [] cbtom rfo.
have oute : out_left_event ev.
  by apply: out_es; rewrite inE eqxx.
have oute' : {in sort edge_below (outgoing ev),
                   forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
have noco : {in all_edges (fop ++ lsto :: lop) (ev :: evs) &,
                 no_crossing R}.
 by  move=> g1 gt2 g1in g2in; apply: nocs; apply: sub_edges.
rewrite /simple_step/generic_trajectories.simple_step.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have inv' : inv1_seq bottom top evs ((fc ++ nos) ++ lno :: lc).
  have := invariant1_default_case inbox0 oute rfo cbtom adj sval cle clae
            noco lexev.
  by rewrite oe oca_eq.
have := inv' =>  -[] clae' [] sval' [] adj' []cbtom' rfo'.
have exi := exists_cell cbtom adj (inside_box_between inbox_e).
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe exi.
have [{}pal {}puh vl vp nc]:=
  decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
have /esym left_last : left_limit lno = p_x (point ev).
  apply: (opening_cells_left oute vl vp).
  by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
have heqo : high lno = he.
  by have := opening_cells_aux_high_last vl vp oute'; rewrite oca_eq.
have sub_edges' : {subset all_edges ((fc ++ nos) ++ lno :: lc) evs <=
                     [:: bottom, top & s]}.
  have := step_keeps_subset_default inbox0 oute rfo cbtom adj sval.
  rewrite oe oca_eq !catA /= /all_edges => main g.
  rewrite mem_cat=> /orP[ | gin]; last first.
    apply: sub_edges; rewrite mem_cat; apply/orP; right.
    by rewrite events_to_edges_cons mem_cat gin orbT.
  rewrite (cell_edges_sub_high cbtom' adj') inE=> /orP[/eqP -> | /main].
    by rewrite inE eqxx.
  rewrite mem_cat=> /orP[] gin; apply: sub_edges; last first.
    by rewrite mem_cat events_to_edges_cons orbC mem_cat gin.
  by rewrite mem_cat mem_cat gin orbT.
have cle' : close_edges_from_events evs by move: cle=> /andP[].
have out_es' : {in evs, forall e, out_left_event e}.
  by move=> e ein; apply: out_es; rewrite inE ein orbT.
have lexev' : sorted (@lexPtEv _) evs by move: lexev=> /path_sorted.
have oks' : all open_cell_side_limit_ok ((fc ++ nos) ++ lno :: lc).
  have := step_keeps_open_side_limit_default inbox0 oute rfo
    cbtom adj sval oks; rewrite oe oca_eq.
  by [].
have lexfutev : {in evs, forall e,
     lexPt (last dummy_pt (left_pts lno)) (point e)}.
  move=> e ein.
  have noce : {in le :: rcons (sort edge_below (outgoing ev)) he &,
           no_crossing R}.
    move=> g1 g2 g1in g2in; apply noco.
      move: g1in; rewrite inE mem_rcons inE mem_sort orbA=> /orP[]g1in.
        by move: g1in=> /orP[] /eqP ->; rewrite mem_cat ?lein ?hein.
      by rewrite mem_cat orbC /events_to_edges /= mem_cat g1in.
    move: g2in; rewrite inE mem_rcons inE mem_sort orbA=> /orP[]g2in.
      by move: g2in=> /orP[] /eqP ->; rewrite mem_cat ?lein ?hein.
    by rewrite mem_cat orbC /events_to_edges /= mem_cat g2in.
  have lebhe : le <| he.
    apply: (edge_below_from_point_above _ vl vp (underWC pal) puh).
    by apply: noce; rewrite !(inE, mem_rcons) eqxx ?orbT.
  have lnoin: lno \in opening_cells (point ev) (outgoing ev) le he.
    by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
  have :=
    opening_cells_last_lexePt oute (underWC pal) puh vl vp noce lebhe lnoin.
  move=> /lexePt_lexPt_trans; apply.
  move: (lexev).
  rewrite -/(sorted _ (ev :: evs)) sorted_lexPtEv_lexPt /=.
  rewrite (path_sortedE (@lexPt_trans _)).
  by move=> /andP[] /allP /(_ _ (map_f _ ein)).
have uniqout' : {in evs, forall e, uniq (outgoing e)}.
  by move=> e ein; apply: uniqout; rewrite inE ein orbT.
have no_dup' : {in [seq high c | c <- (fc ++ nos) ++ lno :: lc] & evs,
  forall g e, g \notin outgoing e}.
  move=> /= g e + ein; rewrite -catA -cat_rcons !map_cat !mem_cat orbCA.
  move=> /orP[cnew | cold]; last first.
    apply: no_dup; last by rewrite inE ein orbT.
    rewrite ocd !map_cat /= !mem_cat inE.
    by move: cold=> /orP[] ->; rewrite ?orbT.
  have := opening_cells_aux_high vl vp oute'; rewrite oca_eq /=.
  have := opening_cells_aux_high_last vl vp oute'; rewrite oca_eq /=.
  move=> lnoq nosq.
  apply/negP=> gout.
  have lefte : left_pt g = point e.
    exact: (eqP (out_es' _ ein _ gout)).
  have ein2 : e \in (ev :: evs) by rewrite inE ein orbT.
  move: cnew; rewrite map_rcons mem_rcons inE=> /orP[/eqP ghe | gnos].
    have := no_dup g e _ ein2.
    rewrite ocd !map_cat /= gout ghe lnoq heq !mem_cat inE eqxx !orbT.
    by move=> /(_ isT).
  rewrite nosq mem_sort in gnos.
  move: lexev; rewrite (path_sortedE (@lexPtEv_trans _))=> /andP[] + _.
  move=> /allP /(_ _ ein).
  by rewrite /lexPtEv -lefte (eqP (oute g gnos)) lexPt_irrefl.
by constructor.
Qed.

Lemma simple_step_common_non_gp_invariant
  bottom top s fop lsto lop cls lstc ev lsthe lstx evs
  fc cc lcc lc le he:
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  (lstx <> p_x (point ev) \/ (lstx = p_x (point ev) /\ point ev >>> lsthe)) ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  common_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  common_non_gp_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs inbox_s simple_cond oe comng.
have comi := ngcomm comng.
have inv := inv1 comi.
move: (inv)=> [] clae [] []; first by [].
move=> sval [] adj [] cbtom rfo.
have inbox_es := inbox_events comi.
have evin : ev \in ev :: evs by rewrite inE eqxx.
have inbox_e : inside_box bottom top (point ev).
  by apply: (allP inbox_es); rewrite map_f.
have exi := exists_cell cbtom adj (inside_box_between inbox_e).
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe exi.
have out_es := out_events comi.
have oute : out_left_event ev by apply: out_es; rewrite inE eqxx.
case oca_eq : (opening_cells_aux (point ev) (sort edge_below (outgoing ev))
  le he) => [nos lno].
have [{}pal {}puh vl vp nc]:=
  decomposition_connect_properties rfo sval adj cbtom
  (inside_box_between inbox_e) oe.
have := last_opening_cells_left_pts_prefix vl vp puh oute.
  rewrite oca_eq /= => /(_ _ _ erefl) [] sll' snd_cond.
have comi' : common_invariant bottom top s
  (simple_step fc cc lc lcc le he cls lstc ev) evs.
  by apply: (simple_step_common_invariant boxwf nocs inbox_s oe comi).
(* have sll :
  (1 < size (left_pts (lst_open
      (simple_step fc cc lc lcc le he cls lstc ev))))%N.
  have := last_opening_cells_left_pts_prefix vl vp puh oute.
  by rewrite /simple_step oca_eq /= => /(_ _ _ erefl) []. *)
have lst_side_lex' : path (@lexPt _) (nth dummy_pt (left_pts lno) 1)
  [seq point e | e <- evs].
  move: snd_cond; case: (left_pts lno) sll' => [ | a [ | b tl]] //= _.
  move=> -[] _ -> _.
  suff :(sorted (@lexPt _) [seq point e | e <- ev :: evs]) by [].
  by rewrite -sorted_lexPtEv_lexPt; apply: (lex_events comi).
move:comi'; rewrite /simple_step/= oca_eq=> comi'.
by constructor.
Qed.

Lemma simple_step_disjoint_non_gp_invariant
  bottom top s fop lsto lop cls lstc ev lsthe lstx evs
  fc cc lcc lc le he:
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  (lstx <> p_x (point ev) \/ (lstx = p_x (point ev) /\ point ev >>> lsthe)) ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  disjoint_non_gp_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  disjoint_non_gp_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s simple_cond oe.
move=> []; rewrite /state_open_seq/state_closed_seq/=.
move=> oc_dis c_dis comng pw rl sr ucc wcl.
have := comng=> -[] /= comi lft_cond1 lft_cond2.
have := comi=> -[]; rewrite /state_open_seq/state_closed_seq/=.
move=> inv1 lstxq lstheq sub_edges cle out_es uniqout inbox_es
  no_dup lexev oks.
move=> bottom_left_cond cl_ok rllstc hlstcq midptlstc btm_leftops leftops.
move=> btm_left_lex_snd center_in uniq_high.
move: (inv1) => [] clae [] sval' [] adj [] cbtom rfo.
move: sval' => [ //| sval].
have inbox_e : inside_box bottom top (point ev).
  by have  := inbox_events comi=> /= /andP[].
have exi := exists_cell cbtom adj (inside_box_between inbox_e).
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have bet_e : between_edges bottom top (point ev).
  by apply: inside_box_between.
have [/= pal puh vle vhe ncont] :=
  connect_properties  cbtom adj rfo sval bet_e ocd allnct allct
  lcc_ctn flcnct.
rewrite /simple_step.
case oca_eq: opening_cells_aux => [nos lno].
have evin : ev \in ev :: evs by rewrite inE eqxx.
have lstxle: lstx <= p_x (point ev).
  have := bottom_left_cond _ evin.
  rewrite lstxq /left_limit=> /orP[].
    by rewrite le_eqVlt orbC => ->.
  by move => /andP[] /eqP -> _; apply: le_refl.
have cl_at_left' : {in rcons cls lstc,
        forall c, right_limit c <= p_x (point ev)}.
  by move=> c cin; apply: rl; rewrite // inE eqxx.
have oute : out_left_event ev by apply: out_es; rewrite inE eqxx.
have oute' : {in sort edge_below (outgoing ev),
  forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
have := step_keeps_disjoint_default inbox_es oute rfo
         cbtom adj sval pw oks oc_dis c_dis cl_at_left'.
have lstoin : lsto \in fop ++ lsto :: lop.
  by rewrite !(mem_cat, inE) eqxx !orbT.
have vho : valid_edge (high lsto) (point ev).
  by move: (allP sval lsto lstoin)=> /andP[].
rewrite oe oca_eq /= !cat_rcons -!cats1 /= => disjointness.
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
have /andP [vllcc vhlcc] : valid_edge (low lcc) (point ev) &&
  valid_edge (high lcc) (point ev).
  by apply: (allP sval); rewrite ocd !(mem_cat, inE) eqxx !orbT.
have pwo' : pairwise edge_below
           (bottom :: [seq high c | c <- (fc ++ nos) ++ lno :: lc]).
have := step_keeps_pw_default inbox_es oute rfo cbtom adj sval
      noc pw.
  by rewrite oe oca_eq -catA.
have right_limit_closed' :
  {in  rcons(cls ++
          lstc :: closing_cells (point ev) cc) (close_cell (point ev) lcc) &
     evs, forall c e, right_limit c <= p_x (point e)}.
  have:= step_keeps_right_limit_closed_default inbox_es cbtom adj
    sval lexev cl_at_left'.
  by rewrite oe oca_eq /=.
have cngi : common_non_gp_invariant bottom top s
              (Bscan (fc ++ nos) lno lc
                (cls ++ (lstc :: closing_cells (point ev) cc))
                (close_cell (point ev) lcc) he (p_x (point ev))) evs.
  have := simple_step_common_non_gp_invariant boxwf nocs' inbox_s
    simple_cond oe comng.
  by rewrite /simple_step oca_eq.
have midrlstc : (1 < size (right_pts (close_cell (point ev) lcc)))%N.
  have evnin:
    point ev != Bpt (p_x (point ev)) (pvert_y (point ev) (high lcc)).
    apply/eqP=> abs.
    have := pvert_on vhlcc; rewrite -abs => {}abs.
    by have := puh; rewrite strict_nonAunder // abs.
  rewrite /close_cell.
  rewrite !pvertE //.
  cbn [no_dup_seq_aux].
  case: ifP=> [/eqP /esym/eqP| diff]; first by rewrite (negbTE evnin).
  by case: ifP.
have wcl' : {in rcons (cls ++ (lstc :: closing_cells (point ev) cc))
                                (close_cell (point ev) lcc),
          forall c, left_limit c < right_limit c}.
  move=> c; rewrite -cats1 !(mem_cat, inE) -!orbA orbA => /orP[cold | cnew].
    by apply: wcl; rewrite -cats1 !(mem_cat, inE).
  have [c' c'in cc'] : exists2 c', c' \in rcons cc lcc &
        c = close_cell (point ev) c'.
    move: cnew=> /orP[/mapP [c' c'in ->] | /eqP ->].
      by exists c'; rewrite // mem_rcons inE c'in orbT.
    by exists lcc; rewrite // mem_rcons inE eqxx.
  rewrite cc' {c cc' cnew}.
  have c'in2 : c' \in fop ++ lsto :: lop.
      by rewrite ocd -cat_rcons !mem_cat c'in !orbT.
  have /andP/= [vlc' vhc'] := allP sval _ c'in2.
  rewrite (right_limit_close_cell vlc' vhc') /=.
  have llt : left_limit c' <= lstx.
    by apply: leftops; rewrite ocd -cat_rcons !mem_cat c'in ?orbT.
  rewrite /left_limit.
  have [_ _ ->]:= close_cell_preserve_3sides (point ev) c'.
  move: simple_cond=> -[/eqP simple_cond | [atlstx abovelsthe]].
     by apply: (le_lt_trans llt); rewrite lt_neqAle simple_cond.
  have c'high : c' \in lop.
    have cont : contains_point (point ev) c'.
      move: c'in; rewrite mem_rcons inE=> /orP[/eqP -> //| ].
      apply allct.
    move: c'in2; rewrite !(mem_cat, inE) orbA=> /orP[abs | ]; last by [].
    case/negP: abovelsthe; rewrite -lstheq.
    move: abs=> /orP[ c'fop | /eqP <-]; last first.
      by move: cont=> /andP[].
    have /andP[_] := pw.
    have lstoin2 : lsto \in lsto :: lop by rewrite inE eqxx.
    rewrite map_cat /= pairwise_cat=> /andP[] + _.
    move=> /allrelP /(_ _ _ (map_f _ c'fop) (map_f _ lstoin2)) hc'blsto.
    apply: (order_edges_viz_point' vhc' vho hc'blsto).
    by move/andP: cont=>[].
  move: llt; rewrite /left_limit atlstx le_eqVlt=> /orP[/eqP abs|]; last by [].
  have nth1in : nth dummy_pt (left_pts lsto) 1 \in (left_pts lsto).
     by apply: mem_nth.
  have xnth1 : p_x (nth dummy_pt (left_pts lsto) 1) = p_x (point ev).
    have := allP oks lsto lstoin=> /andP[] _ /andP[] + _.
    by move=> /allP /(_ _ nth1in) /eqP ->; rewrite -lstxq.
  have : lexePt (bottom_left_corner c') (nth dummy_pt (left_pts lsto) 1).
    by apply: (btm_left_lex_snd c' c'in2).
  rewrite /lexePt /bottom_left_corner lt_neqAle abs xnth1 eqxx /= leNgt.
  case/negP.
  have nth1b: p_y (nth dummy_pt (left_pts lsto) 1) <
         pvert_y (nth dummy_pt (left_pts lsto) 1) lsthe.
    have := allP oks lsto lstoin=> /andP[] _ /andP[] Q /andP[] S /andP[] hdon _.
    have xh : p_x (head dummy_pt (left_pts lsto)) =
      p_x (nth dummy_pt (left_pts lsto) 1).
      move: lft_cond1 Q; case: (left_pts lsto)=> [ | a [ | b tl]] //= _.
      by move=> /andP[] /eqP -> /andP[] /eqP <-.
    have := on_pvert hdon.
    have := same_pvert_y (proj2 (andP hdon)) xh => ->.
    rewrite lstheq => ->.
    move: lft_cond1 S.
    by case: (left_pts lsto) => [ | a [ | b tl]] //= _ /andP[].
  apply: (lt_le_trans nth1b).
  have [c'2 c'2in c'2q] : exists2 c'2, c'2 \in lsto::lop & high c'2 = low c'.
    have /mem_seq_split [s1 [s2 s1s2q]] := c'high.
    exists (last lsto s1).
      rewrite s1s2q -[_ :: _]/((lsto :: s1) ++ (c' :: s2)).
      by rewrite mem_cat mem_last.
    move: adj; rewrite s1s2q=> /adjacent_catW /= => -[] _.
    by rewrite cat_path /= => /andP[] _ /andP[] /eqP + _.
  have lstoin2 : lsto \in rcons fop lsto by rewrite mem_rcons inE eqxx.
  have lstobc' : high lsto <| low c'.
    rewrite -c'2q.
    move: c'2in; rewrite inE=> /orP[/eqP -> | c'2in].
      by apply: edge_below_refl.
    move:pw=> /andP[] _.
    rewrite -cat_rcons map_cat pairwise_cat => /andP[] + _.
    by move=>/allrelP /(_ _ _ (map_f _ lstoin2) (map_f _ c'2in)).
  have vhob: valid_edge (high lsto) (last dummy_pt (left_pts c')).
    by have := same_x_valid (high lsto) (esym abs); rewrite vho => <-.
    have vlc'b : valid_edge (low c') (nth dummy_pt (left_pts lsto) 1).
    by have := same_x_valid (low c') (esym xnth1) => <-.
  have lq1 : p_x (last dummy_pt (left_pts c')) =
      p_x (nth dummy_pt (left_pts lsto) 1).
    by rewrite xnth1 abs.
  have := (same_pvert_y vhob lq1); rewrite lstheq => <-.
  rewrite leNgt.
  have vlc'l : valid_edge (low c') (last dummy_pt (left_pts c')).
    by rewrite -(same_x_valid (low c') (esym abs)).
  have lon : last dummy_pt (left_pts c') === low c'.
    by have := allP oks c' c'in2 => /andP[] _ /andP[] _ /andP[] _ /andP[] _ ->.
  have : last dummy_pt (left_pts c') >>= high lsto.
    apply/negP=> HH.
    have := (order_edges_strict_viz_point' vhob vlc'l lstobc' HH).
    rewrite strict_nonAunder; last by [].
    by rewrite lon.
  have := strict_under_pvert_y vhob; rewrite lstheq.
  by move=> ->.
have ldifmain c : c \in fop ++ lsto :: lop -> low c != high c.
    move=> cin2.
    have [s1 [s2 sq]]:= mem_seq_split cin2.
    elim/last_ind: {-1} (s1) (erefl s1) => [ | s1' c2 _] s1q.
      apply/eqP=> abs.
      have := cbtom; rewrite /cells_bottom_top/cells_low_e_top.
      move=> /andP[] /andP[] _ + _; rewrite sq s1q /= => /eqP lb.
      have lcin : low c \in [:: bottom, top & s].
        by apply: sub_edges; rewrite !mem_cat map_f.
      by have := uniq_high => /andP[] + _; rewrite -lb abs map_f.
    have lq : low c = high c2.
      move: adj; rewrite sq s1q cat_rcons.
      by move=> /adjacent_catW /= => -[] _ /andP[] /eqP/esym + _.
    have := uniq_high => /andP[] _; rewrite sq s1q cat_rcons.
    rewrite map_cat cat_uniq=> /andP[] _ /andP[] _ /=  /andP[] + _.
    by rewrite inE negb_or -lq => /andP[] + _.
have center_in' :
  {in rcons (cls ++ lstc :: closing_cells (point ev) cc)
    (close_cell (point ev) lcc), forall c, inside_closed' (cell_center c) c}.
  move=> c; rewrite -cats1. rewrite -(cat_rcons lstc) -catA mem_cat.
  move=> /orP[cold | cnew]; first by apply: center_in.
  move: cnew.
  rewrite /closing_cells -(map_cat (close_cell (point ev)) cc [:: lcc]).
  move=> /[dup] cin /mapP [c' + /[dup] cc' ->]; rewrite cats1 => c'in.
  have c'in2 : c' \in fop ++ lsto :: lop.
    by rewrite ocd -cat_rcons !mem_cat c'in orbT.
  have inter_at_extc' : inter_at_ext (low c') (high c').
    by apply/nocs'; apply: sub_edges; rewrite mem_cat; apply/orP; left;
    rewrite mem_cat map_f ?orbT.
  have ldif : low c' != high c' by apply: ldifmain.
    (* have [s1 [s2 sq]]:= mem_seq_split c'in2.
    elim/last_ind: {-1} (s1) (erefl s1) => [ | s1' c2 _] s1q.
      apply/eqP=> abs.
      have := cbtom; rewrite /cells_bottom_top/cells_low_e_top.
      move=> /andP[] /andP[] _ + _; rewrite sq s1q /= => /eqP lb.
      move: inbox_es=> /andP[] /andP[] /andP[] + _ _ _ => /negP; apply.
      rewrite -lb abs.
      have /= incc := open_cells_decomposition_point_on cbtom adj bet_e sval oe.
      move: c'in; rewrite mem_rcons inE => /orP[/eqP c'lcc | /incc].
        by rewrite c'lcc underW.
      move=> /[dup] /andP[] _ vhc'.
      by rewrite under_onVstrict//  => ->.
    have := adj; rewrite sq s1q cat_rcons.
    move=> /adjacent_catW [] _ /= /andP[] /eqP <- _.
    have := uniq_high; rewrite sq s1q cat_rcons map_cat /=.
    rewrite cat_uniq => /andP[] _ /andP[] _ /= /andP[] + _.
    by rewrite inE negb_or => /andP[] + _. *)
  have rfc' : low c' <| high c'.
    by apply: (allP rfo).
  have c'ok : open_cell_side_limit_ok c'.
    by apply: (allP oks).
  have [vlc' vhc'] : valid_edge (low c') (point ev) /\
     valid_edge (high c') (point ev).
    by apply/andP; apply (allP sval).
  have leftc' : left_limit c' < p_x (point ev).
    have cin2 : c \in rcons (closing_cells (point ev) cc)
      (close_cell (point ev) lcc).
      by rewrite -cats1 -(map_cat (close_cell (point ev)) cc [:: lcc]).
    have:= wcl' c; rewrite -cats1 -catA /= cats1.
    rewrite !(mem_cat, inE) cin2 !orbT.
    rewrite cc' /left_limit.
    have [_ _ ->] := close_cell_preserve_3sides (point ev) c'.
    rewrite close_cell_right_limit; first by apply.
    by split.
  apply: (cell_center_close_cell_inside inter_at_extc' ldif rfc' c'ok
             vlc' vhc' leftc').
(* TODO avoid duplication #1 *)
have allcont : all (contains_point (point ev)) (rcons cc lcc).
  by rewrite -cats1 all_cat /= lcc_ctn !andbT; apply/allP.

have cl_ok' : {in rcons (cls ++ (lstc :: closing_cells (point ev) cc))
                                  (close_cell (point ev) lcc),
            forall c, closed_cell_side_limit_ok c}.
  have svalcc : seq_valid (rcons cc lcc) (point ev).
    apply/allP=> c cin; apply: (allP sval); rewrite ocd !mem_cat.
    move: cin; rewrite mem_rcons inE.
    by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT.
  have adjcc : adjacent_cells (rcons cc lcc).
    move: adj.
    by rewrite ocd -cat_rcons =>/adjacent_catW[] _ /adjacent_catW[].
  have rfocc : s_right_form (rcons cc lcc).
    apply/allP=> c cin; apply: (allP rfo); rewrite ocd !mem_cat.
    move: cin; rewrite mem_rcons inE.
    by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
  have closed_map : closing_cells (point ev) (rcons cc lcc) =
      rcons [seq close_cell (point ev) c | c <- cc]
          (close_cell (point ev) lcc).
    rewrite -closing_cellsE.
    by rewrite /cells.closing_cells map_rcons.
  have ccok : all open_cell_side_limit_ok (rcons cc lcc).
    apply/allP=> c cin; apply: (allP oks); rewrite ocd !mem_cat.
    move: cin; rewrite mem_rcons inE.
    by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
  have := closing_cells_side_limit' rfocc svalcc adjcc ccok allcont.
  rewrite head_rcons pal last_rcons puh=> /(_ isT isT).
  rewrite [X in all _ X]closed_map=> /allP cl_sok.
  move=> c; rewrite -cat_rcons -cats1 -catA mem_cat=> /orP[cold | cnew].
    by apply: cl_ok.
  apply: cl_sok.
  move: cnew; rewrite /closing_cells -[List.map]/@seq.map -cat_rcons cats0.
  by [].

have ucc' : uniq [seq cell_center c | c <-
                          rcons (cls ++ (lstc :: closing_cells (point ev) cc))
                                (close_cell (point ev) lcc)].
  set wcls := rcons _ _.
  have wclsq : wcls = rcons cls lstc ++ rcons (closing_cells (point ev) cc)
    (close_cell (point ev) lcc).
    by rewrite /wcls cat_rcons -!cats1 -!catA.
  rewrite wclsq => {wcls wclsq}.
  rewrite map_cat cat_uniq ucc /=.
  apply/andP; split.
    rewrite /closing_cells -map_rcons; apply/negP=> /hasP[p].
    move=> /mapP [c2 c2new pc2].
    move=> /mapP [c1 c1old pc1].
    move: c2new=> /mapP [c3 c3o c2c3].
    have c3o2 : c3 \in fop ++ lsto :: lop.
      by rewrite ocd -cat_rcons !mem_cat c3o orbT.
    have noc3 : inter_at_ext (low c3) (high c3).
      by apply: nocs'; apply: (sub_edges); rewrite 2!mem_cat map_f ?orbT.
    have dif3 : low c3 != high c3.
      have [[ | c0 s3][s4 sq]] := mem_seq_split c3o2.
        have c3b : low c3 = bottom.
          by move: cbtom=> /andP[] /andP[] _ /eqP + _; rewrite sq.
        move: uniq_high=> /= /andP[] + _; rewrite sq /= inE negb_or c3b.
        by move=> /andP[].
      have -> : low c3 = high (last c0 s3).
        by have := adj; rewrite sq /= cat_path => /andP[] _ /= /andP[] /eqP -> _.
      apply/eqP=> abs.
      have := uniq_high; rewrite sq => /andP[] _.
      rewrite map_cat cat_uniq => /andP[] _ /andP[] /negP + _; apply.
      apply/hasP; exists (high (last c0 s3)).
        by rewrite abs map_f // inE eqxx.
      by apply: map_f; rewrite mem_last.
    have wf3 : low c3 <| high c3 by apply (allP rfo).
    have ok3 : open_cell_side_limit_ok c3 by apply: (allP oks).
    have vc3 : valid_cell c3 (point ev).
      by apply: (andP (allP sval c3 c3o2)).
    have [vlc3 vhc3] := vc3.
    have c2in : c2 \in rcons (cls ++ lstc :: closing_cells (point ev) cc)
                       (close_cell (point ev) lcc).
      rewrite -cats1 -catA mem_cat /= inE /closing_cells cats1 -map_rcons.
      by rewrite orbA orbC; apply/orP; left; apply/mapP; exists c3.
    have lc3ltp : left_limit c3 < p_x (point ev).
      have := wcl' c2 c2in.
      rewrite c2c3 /left_limit.
      have [_ _ ->] := close_cell_preserve_3sides (point ev) c3.
      by rewrite right_limit_close_cell.
    have ok2 := cl_ok' c2 c2in.
    have :=
      cell_center_close_cell_inside noc3 dif3 wf3 ok3 vlc3 vhc3 lc3ltp.
    rewrite -[cells.close_cell _ _]/(close_cell _ _).
    rewrite -c2c3=> ccin.
    have := close'_subset_contact vc3; rewrite -c2c3 => /(_ _ ok2 ccin) ccin'.
    have := oc_dis c3 c1 c3o2 c1old (cell_center c2)=> /negP.
    by rewrite ccin' -pc2 pc1 center_in.
  apply/(uniqP dummy_pt).
  rewrite  /closing_cells !(size_map, size_rcons).
  set L := [seq cell_center c | c <- _].
  have main : forall i j, (i <= j < (size cc).+1)%N ->
    nth dummy_pt L i = nth dummy_pt L j -> i = j.
    move=> i j /[dup] ijs /andP[ij js] abs.
    have i_s : (i < (size cc).+1)%N by apply: leq_ltn_trans js.
    move: ij; rewrite leq_eqVlt=> /orP[/eqP -> | ij]; first by [].
    have jpred : j = j.-1.+1 by rewrite (ltn_predK ij).
    have i_sm : (i < size cc)%N.
      by apply: (leq_trans ij); rewrite -ltnS.
    have is' : (i < size [seq high c | c <- rcons cc lcc])%N.
      by rewrite size_map size_rcons.
    have js' : (j < size [seq high c | c <- rcons cc lcc])%N.
      by rewrite size_map size_rcons.
    have js2 : (j < size (rcons cc lcc))%N by rewrite size_rcons.
    have jps : (j.-1 < (size cc).+1)%N.
      by apply : (ltn_trans _ js); rewrite -jpred leqnn.
    have jps2 : (j.-1 < size (rcons cc lcc))%N by rewrite size_rcons.
    have jps3 : (j.-1 < size [seq high c | c <- rcons cc lcc])%N.
      by rewrite size_map size_rcons.
    move: pw; rewrite ocd !map_cat pairwise_cat=> /andP[] _ /andP[] _.
    move=> /andP[] _.
    rewrite /= -cat_rcons pairwise_cat=> /andP[] _ /andP[] + _.
    rewrite -map_rcons.
    move=> /(pairwiseP dummy_edge)/(_ _ _ is' jps3) => ibelj.
    have nth_in k : (k < (size cc).+1)%N ->
      nth dummy_cell (rcons cc lcc) k \in fop ++ lsto :: lop.
      move=> ks.
      rewrite ocd -cat_rcons !mem_cat; apply/orP; right; apply/orP; left.
      by rewrite mem_nth // size_rcons.
    have vlk k : (k < (size cc).+1)%N ->
      valid_edge (nth dummy_edge [seq high c | c <- rcons cc lcc] k) (point ev).
      move=> ks.
      have ks' : (k < size (rcons cc lcc))%N by rewrite size_rcons.
      set ck := nth dummy_cell (rcons cc lcc) k.
      rewrite (nth_map dummy_cell dummy_edge high) //.
      by have := allP sval _ (nth_in k ks)=> /andP[].
    have vllk k : (k < (size cc).+1)%N ->
      valid_edge (low (nth dummy_cell (rcons cc lcc) k)) (point ev).
      move=> ks.
      have ks' : (k < size (rcons cc lcc))%N by rewrite size_rcons.
      set ck := nth dummy_cell (rcons cc lcc) k.
      by have := allP sval _ (nth_in k ks)=> /andP[].
    have vli := vlk i i_s.
    have incl k: (k < (size cc).+1)%N -> inside_closed' (nth dummy_pt L k)
            (nth dummy_cell [seq close_cell (point ev) c | c <- rcons cc lcc] k).
      move=> ks.
      rewrite /L (nth_map dummy_cell); last first.
        by rewrite size_rcons size_map.
      rewrite -map_rcons.
      apply: center_in'.
      rewrite -(cats1 _ (close_cell _ _)) -catA /= cats1.
      rewrite mem_cat inE orbA; apply/orP; right.
      by rewrite /closing_cells -map_rcons mem_nth // size_map size_rcons.
    have inclj := incl j js.
    have incli := incl i i_s.
    have lowjq : low (nth dummy_cell [seq close_cell (point ev) c | c <- rcons cc lcc] j)
      = high (nth dummy_cell [seq close_cell (point ev) c | c <- rcons cc lcc] j.-1).
      have := (nth_map dummy_cell dummy_cell (close_cell (point ev))).
      move=> /(_ j (rcons cc lcc) js2) => ->.
      have := (nth_map dummy_cell dummy_cell (close_cell (point ev))).
      move=> /(_ j.-1 (rcons cc lcc) jps2) => ->.
      have [-> _ _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) j).
      have [ _ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) j.-1).
      have jint : (0 < j < size (rcons cc lcc))%N.
        by rewrite (leq_ltn_trans (leq0n _) (ij)).
      have := adj; rewrite /adjacent_cells ocd -cat_rcons=>/adjacent_catW.
      move=>[] _ /adjacent_catW [] + _.
      by move=> /adjacent_path_nth /(_ jint).
    move: inclj=> /andP[] /andP[] _ B /andP[] abovelow _.
    move: incli=> /andP[] /andP[] /andP[] _ belowhigh C _.
    have vni : valid_edge (high (nth dummy_cell [seq close_cell (point ev) c | c <- rcons cc lcc] i))
      (nth dummy_pt L i).
      apply/andP; split.
        apply: (le_trans _ (proj1 (andP C))).
        rewrite (nth_map dummy_cell); last by rewrite size_rcons.
        rewrite /left_limit.
        have [_ -> ->] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) i).
        have := allP oks _ (nth_in _ i_s) => /andP[] lf_size /andP[] xs
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
            (nth dummy_cell (rcons cc lcc) i).
      have /andP[ _ ]:= vli.
      by rewrite (nth_map dummy_cell); last by rewrite size_rcons.
    have vnj : valid_edge
      (low (nth dummy_cell [seq close_cell (point ev) c | c <- rcons cc lcc] j))
      (nth dummy_pt L i).
      rewrite abs {C belowhigh abovelow incl}.
      apply/andP; split.
      apply: (le_trans _ (proj1 (andP B))).
      rewrite (nth_map dummy_cell); last by rewrite size_rcons.
        rewrite /left_limit.
        have [-> _ ->] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) j).
        have := allP oks _ (nth_in _ js) => /andP[] lf_size /andP[] xs
        /andP[] _ /andP[] hdon lston.
        by move: lston=> /andP[] _ /andP[].
      apply: (le_trans (proj2 (andP B))).
      rewrite (nth_map dummy_cell) {B}; last by rewrite size_rcons.
      rewrite right_limit_close_cell //; last first.
          by move: (vlk _ js); rewrite (nth_map dummy_cell) // size_rcons.
        by apply: vllk.
      have [-> _ _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) j).
      by have /andP[ _ ]:= vllk _ js.
    move: abovelow=> /negP; case.
    rewrite -abs.
    have := ij; rewrite jpred ltnS; rewrite leq_eqVlt=> /orP[/eqP ijq| ijp].
      by rewrite -jpred lowjq -ijq.
    have {}ibelj := (ibelj ijp).
    have ibelj' : high (nth dummy_cell [seq (close_cell (point ev)) c | c <- rcons cc lcc] i) <|
        low (nth dummy_cell [seq (close_cell (point ev)) c | c <- rcons cc lcc] j).
    move: ibelj; rewrite lowjq.
    repeat (rewrite (nth_map dummy_cell); last by rewrite size_rcons).
    have [_ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) j.-1).
    by have [_ -> _] := close_cell_preserve_3sides (point ev)
            (nth dummy_cell (rcons cc lcc) i).
    have := order_edges_viz_point' vni vnj ibelj'.
    rewrite -jpred; apply.
    by apply: belowhigh.
  move=> i j; rewrite ?inE /= => i_s js eqcc.
  case: (ltnP i j) => [ij | ji].
    have ijint : (i <= j < (size cc).+1)%N by rewrite (ltnW ij) js.
    by apply: (main _ _ ijint).
  have jiint : (j <= i < (size cc).+1)%N by rewrite ji i_s.
  by apply/esym/(main _ _ jiint).

have rlstc' : right_limit (close_cell (point ev) lcc) = (p_x (point ev)).
  by apply: close_cell_right_limit.
have hlstcq' : high (close_cell (point ev) lcc) = he.
  have := close_cell_preserve_3sides (point ev) lcc.
  rewrite -[cells.close_cell _ _]/(close_cell _ _)=> -[] _ -> _.
  by rewrite heq.
have midptlstc' :
  path (@lexPt _) (nth dummy_pt (right_pts (close_cell (point ev) lcc)) 1)
  [seq point x | x <- evs].
  rewrite /close_cell (pvertE vllcc) (pvertE vhlcc) /=.
  rewrite -[X in if X then _ else _]
    /({|generic_trajectories.p_x := p_x (point ev);
   generic_trajectories.p_y := (pvert_y (point ev) (high lcc))|} ==
     (point ev)).
  rewrite pt_eqE /=.
  have := puh; rewrite /= (strict_under_pvert_y vhlcc) lt_neqAle eq_sym.
  move=> /andP[] /negbTE -> _; rewrite andbF.
  rewrite [nth _ _ _](_ : _ = point ev); last first.
    by case: ifP=> [/eqP abs | diff].
  move: lexev; rewrite -/(sorted (@lexPtEv _) (ev :: evs)).
  by rewrite sorted_lexPtEv_lexPt.
have btm_leftops' : {in (fc ++ nos) ++ lno :: lc & evs,
  forall c e, lexPt (bottom_left_corner c) (point e)}.
  move=> c e + ein; rewrite -catA=> cin.
  have lexeev : lexPt (point ev) (point e).
    have := lexev; rewrite (path_sortedE (@lexPtEv_trans _))=> /andP[] + _.
    by move=> /allP /(_ e ein).
  have btm_left_ev: {in fop ++ lsto :: lop, forall c,
    lexPt (bottom_left_corner c) (point ev)}.
    by move=> ? ?; apply: btm_leftops; rewrite // inE eqxx.
  have := step_keeps_btom_left_corners_default inbox_es oute rfo cbtom adj sval
    noc btm_left_ev.
  by rewrite oe oca_eq=> /(_ (point e) lexeev) => /(_ c cin).
have leftops' : {in ((fc ++ nos) ++ lno :: lc), forall c,
      left_limit c <= p_x (point ev)}.
  move=> c; rewrite -catA -cat_rcons !mem_cat orbCA orbC => /orP[cold | cnew].
    have : lstx <= p_x (point ev).
      rewrite lstxq /left_limit.
      have := bottom_left_cond ev evin=> /orP[ | /andP[/eqP -> _]].
        by rewrite lt_neqAle=> /andP[].
      by apply: le_refl.
    apply: le_trans.
    by apply: leftops; rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
  have := opening_cells_left oute vle vhe.
  rewrite /opening_cells -leq -heq oca_eq le_eqVlt.
  by move=> /(_ c cnew) /eqP => ->.
have lebhe : le <| he.
  rewrite leq heq.
  have ba : below_alt le he.
    by apply/nocs; apply/sub_edges; rewrite mem_cat; apply/orP; left.
  move: ba; rewrite leq heq=> ba.
  by apply: (edge_below_from_point_above ba vle vhe (underWC pal) puh).
have nth1q : nth dummy_pt (left_pts lno) 1 = point ev.
  have := last_opening_cells_left_pts_prefix vle vhe puh oute.
  rewrite -leq -heq oca_eq=> /(_ _ _ erefl) [].
  by case: (left_pts _) => [ | a [ | b tl]] //= _ -[].
have btm_left_lex1 : {in (fc++nos) ++ lno :: lc,
  forall c, lexePt (bottom_left_corner c) (nth dummy_pt (left_pts lno) 1)}.
  move=> c; rewrite -catA -cat_rcons !mem_cat orbCA orbC=> /orP[cold | cnew].
  rewrite nth1q; apply/lexPtW.
  apply: btm_leftops; last by rewrite inE eqxx.
  by rewrite ocd -cat_rcons !mem_cat orbCA orbC cold.
  have noc1 : {in rcons (le :: sort edge_below (outgoing ev)) he &,
                no_crossing R}.
    by apply: (no_crossing_event nocs' sub_edges lein hein evin).
  have := opening_cells_last_lexePt oute (underWC pal) puh vle vhe.
  rewrite -heq -leq /opening_cells oca_eq=> /(_ _ noc1 lebhe cnew).
  by rewrite nth1q.
have := opening_cells_aux_high vle vhe oute'.
  rewrite -leq -heq oca_eq /= => unos.
- have uniqhigh' : uniq (bottom :: [seq high c | c <- (fc ++ nos) ++ lno :: lc]).
  rewrite -catA.
  have newq : [seq high c | c <- rcons nos lno] =
    rcons (sort edge_below (outgoing ev)) (high lcc).
  have := opening_cells_aux_high_last vle vhe oute'.
  have := opening_cells_aux_high vle vhe oute'.
  rewrite -leq -heq oca_eq /= => <- <-.
  by rewrite map_rcons.
  have unew : uniq [seq high c | c <- rcons nos lno].
    rewrite newq rcons_uniq sort_uniq uniqout // andbT.
    rewrite mem_sort; apply/negP=> /oute /eqP abs.
    by move: puh; rewrite strict_nonAunder // -abs left_on_edge.
  rewrite -cat_rcons !map_cat newq.
  move: uniq_high; rewrite ocd !map_cat /= => uniq_high.
  apply: (uniq_insert_edges edge_below uniq_high).
      exact: (uniqout _ evin).
  move=> g; rewrite inE=> /orP[/eqP -> | gin]; last first.
    apply: no_dup=> //.
    by rewrite ocd !map_cat.
  apply/negP=>/oute /eqP abs.
  have vbt : valid_edge bottom (point ev).
    move : cbtom; rewrite /cells_bottom_top/cells_low_e_top.
    case sq : (fop ++ lsto :: lop) => [ | c0 tl] //= /andP[] /eqP lc0q _.
    rewrite <- lc0q.
    by apply: (proj1 (andP (allP sval c0 _))); rewrite sq inE eqxx.
  move: inbox_e=> /andP[] + _; rewrite under_onVstrict // -abs.
  by rewrite left_on_edge.
by constructor.
Qed.

End working_environment.