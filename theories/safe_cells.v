From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells cells_alg general_position.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section safety_property.

Variable R : realFieldType.

Notation pt := (@pt (Num.RealField.sort R)).
Notation p_x := (p_x R).
Notation p_y := (p_y R).
Notation Bpt := (Bpt R).
Notation edge := (@edge R).
Notation cell := (@cell (Num.RealField.sort R) edge).
Notation low := (low (Num.RealField.sort R) edge).
Notation high := (high (Num.RealField.sort R) edge).
Notation left_pts := (left_pts R edge).
Notation right_pts := (right_pts R edge).
Notation left_limit := (left_limit (Num.RealField.sort R) 1 edge).
Notation right_limit := (right_limit (Num.RealField.sort R) 1 edge).
Notation dummy_pt := (dummy_pt R 1).
Notation event := (@event R edge).
Notation point' := (@point R edge).
Notation outgoing := (@point R edge).
Notation point_under_edge :=
  (point_under_edge (Num.RealField.sort R) <=%R +%R (fun x y => x - y)
    *%R 1 edge (@left_pt R)(@right_pt R)).
Notation "p <<= e" := (point_under_edge p e).
Notation "p >>> e" := (negb (point_under_edge p e)).
Notation valid_edge :=
  (valid_edge (Num.RealField.sort R) <=%R edge (@left_pt R) (@right_pt R)).
Notation point_strictly_under_edge :=
  (point_strictly_under_edge (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
    *%R 1 edge (@left_pt R)(@right_pt R)).
Notation "p <<< e" := (point_strictly_under_edge p e).
Notation "p >>= e" := (negb (point_strictly_under_edge p e)).
Notation edge_below :=
  (generic_trajectories.edge_below (Num.RealField.sort R) eq_op <=%R +%R
    (fun x y => x - y) *%R 1 edge (@left_pt R) (@right_pt R)).
Notation "x <| y" := (edge_below x y).


Variables closed : seq cell.
(* The last open cell.  We need to prove that that its top edge is top.
   Then, coverage will be given for all obstacles by the fact that all
   edges in obstacles are different from top. *)
Variables bottom top : edge.
Variable obstacles : seq edge.
Variables points : seq pt.

Hypothesis obstacles_sub :
  {subset [seq low c | c <- closed] ++
     [seq high c | c <- closed] <= bottom :: top :: obstacles}.

Hypothesis obstacles_point_in :
  {subset [seq left_pt g | g <- obstacles] ++
    [seq right_pt g | g <- obstacles] <= points}.

Hypothesis disj_closed :  {in closed &, disjoint_closed_cells R}.
(*
Hypothesis disj_open :  {in [:: o_cell] & closed, disjoint_open_closed_cells R}*)

Hypothesis coverage : {in obstacles, forall g, edge_covered g [::] closed}.
Hypothesis covered_points :
   {in points, forall (p : pt), exists2 c,
       c \in closed & p \in (right_pts c : seq pt) /\
       (p >>> low c)}.

Hypothesis non_empty_closed : {in closed, forall c, left_limit c < right_limit c}.
Hypothesis closed_ok : {in closed, forall c, closed_cell_side_limit_ok c}.
Hypothesis noc : {in bottom :: top :: obstacles &,
  forall g1 g2, inter_at_ext g1 g2}.
Hypothesis low_high : {in closed, forall c, low c <| high c}.
Hypothesis low_dif_high : {in closed, forall c, low c != high c}.

Lemma right_valid :
  {in closed, forall c, {in (right_pts c : seq pt), forall p,
      valid_edge (low c) p /\ valid_edge (high c) p}}.
Proof.
move=> c cin p pin.
have cok := closed_ok cin.
have lltr : left_limit c < right_limit c.
  by apply: non_empty_closed cin.
split.
  apply/andP; split; rewrite (x_right_pts_right_limit cok pin).
    apply/(le_trans (left_limit_left_pt_low_cl cok)).
    by apply/ltW.
  by apply: right_limit_right_pt_low_cl.
apply/andP; split; rewrite (x_right_pts_right_limit cok pin).
  apply/(le_trans (left_limit_left_pt_high_cl cok)).
  by apply/ltW.
by apply: right_limit_right_pt_high_cl.
Qed.

(* I don't know yet if this is going to be used. *)
Lemma above_low :
  {in closed, forall c p, p === high c -> valid_edge (low c) p ->
     p >>= low c}.
Proof.
move=> c cin p /[dup] ponh /andP[] _ vh vl.
apply/negP=> pul.
have lbh : low c <| high c by apply: low_high.
have := order_edges_strict_viz_point vl vh lbh pul.
by rewrite strict_nonAunder // ponh.
Qed.

Lemma safe_cell_interior c p :
  c \in closed -> p <<< high c -> p >>> low c ->
  left_limit c < p_x p < right_limit c ->
  {in obstacles, forall g, ~~ (p === g)}.
Proof.
move=> ccl puh pal /andP[] pright pleft g gin; apply/negP=> pong.
have pinc : inside_closed' p c.
  by rewrite inside_closed'E (underW puh) pal pright (ltW pleft).
have [[opc [pccs [pccssub [highs [cpccs [opco lopcq]]]]]] | ] := coverage gin.
  by [].
move=> [[ | pc1 pcc] [pccn0 [pcccl [ highs [conn [lpcc rpcc]]]]]].
  by [].
have : left_limit pc1 <= p_x p.
  by move:(pong)=> /andP[] _ /andP[]; rewrite lpcc.
rewrite le_eqVlt=> /orP[ /eqP pxq | ].
  have plg : p = left_pt g.
    move: lpcc; rewrite /= pxq=> samex.
    have := on_edge_same_point pong (left_on_edge _).
    rewrite samex=> /(_ erefl) samey.
    by apply/(@eqP pt); rewrite pt_eqE samex samey !eqxx.
  have pin : p \in points.
    apply: obstacles_point_in; rewrite mem_cat; apply/orP; left.
    by rewrite plg map_f.
  have [c' ccl' [pc'r p'al]] := (covered_points pin).
  have := disj_closed ccl ccl'.
  move=> [cqc' | ].
    have := non_empty_closed ccl'.
    move: pleft; rewrite cqc'.
    by rewrite (x_right_pts_right_limit (closed_ok ccl')) // lt_irreflexive.
  move=> /(_ p); rewrite pinc=> /negP; apply.
  rewrite inside_closed'E p'al.
  have c'ok := closed_ok ccl'.
  have /andP[_ /andP[_ /andP[_ /andP[_ /andP[_ ]]] ]] := c'ok.
  move=> /andP[rn0 /andP[samex /andP[srt /andP[onhigh onlow]]]].
  have prlq : p_x p = right_limit c' by apply/eqP/(allP samex).
  rewrite (under_edge_lower_y _ onhigh) /=; last first.
    rewrite (eqP (allP samex _ pc'r)).
    by rewrite (eqP (allP samex _ (head_in_not_nil dummy_pt rn0))).
  have -> /= : p_y p <= p_y (head dummy_pt (right_pts c')).
    case psq : (right_pts c') => [ | p1 ps]; first by rewrite psq in rn0.
    move: pc'r; rewrite psq inE=> /orP[/eqP -> | pps]; first by [].
    apply: ltW.
    (* TODO : use rev_trans here. *)
    have gt_trans : transitive (>%R : rel R).
      by move=> x y z xy yz; apply: (lt_trans yz xy).
    move: (srt); rewrite psq /= (path_sortedE gt_trans)=> /andP[] + _.
    by move=> /allP /(_ _ (map_f _ pps)).
  by rewrite prlq le_refl andbT (non_empty_closed ccl').
elim: pcc pc1 pcccl highs conn rpcc {lpcc pccn0} =>
  [ | pc2 pcc Ih] pc1 pcccl highs conn rpcc pc1lp.
  have pc1cl : pc1 \in closed by apply: pcccl; rewrite inE eqxx.
  have hpc1 : high pc1 = g by apply: (highs _ (mem_head _ _)).
  move: rpcc; rewrite /last_cell/= => rpc1.
  have vgp : valid_edge g p by move: pong=> /andP[].
  have [pr | pnr ] := eqVneq (p : pt) (right_pt g).
    have [c' c'in [prc' pin']] : exists2 c', c' \in closed &
        p_x p = right_limit c' /\ inside_closed' p c'.
      have pp : p \in points.
        by apply/obstacles_point_in; rewrite pr mem_cat map_f // orbT.
      have [c' c'in [pr' pal']] := covered_points pp.
      exists c'; rewrite // inside_closed'E pal'.
      rewrite (x_right_pts_right_limit (closed_ok c'in)) // le_refl.
      rewrite (non_empty_closed c'in).
      have [vpl' vph'] := right_valid c'in pr'.
      by rewrite (right_side_under_high (closed_ok c'in)).
    have [cqc' | ] := disj_closed ccl c'in.
      by move: pleft; rewrite prc' cqc'; rewrite lt_irreflexive.
    by move=> /(_ p); rewrite pin' pinc.
  have noc1 : inter_at_ext (low pc1) (high pc1).
    by apply/noc; apply: obstacles_sub; rewrite mem_cat map_f //= ?orbT.
  have ponh : p === high pc1 by rewrite hpc1.
  have pin1 : inside_closed' p pc1.
    rewrite inside_closed'E under_onVstrict hpc1 // pong pc1lp /=.
    rewrite rpc1; move: vgp=> /andP[] _ ->; rewrite andbT.
    have := closed_cell_in_high_above_low (low_dif_high pc1cl) (low_high pc1cl)
    noc1 (closed_ok pc1cl) _ ponh; apply.
    rewrite pc1lp /= rpc1.
    move: (pong)=> /andP[] _ /andP[] _; rewrite le_eqVlt=> /orP[]; last by [].
    move=> /eqP abs.
    move: pnr=> /negP[]; rewrite pt_eqE abs /=.
    rewrite (on_edge_same_point pong (right_on_edge _)) -abs//.
    by rewrite !eqxx.
  have vph1 : valid_edge (high pc1) p by move: ponh=> /andP[].
  have [cqc' | ] := disj_closed ccl pc1cl.
    by move: puh; rewrite strict_nonAunder cqc' // ponh.
  by move=> /(_ p); rewrite pin1 pinc.
have pcccl' : {subset pc2 :: pcc <= closed}.
  by move=> c' c'in; apply: pcccl; rewrite inE c'in orbT.
have highs' : {in pc2 :: pcc, forall c, high c = g}.
  by move=> c' c'in; apply highs; rewrite inE c'in orbT.
have conn' : connect_limits (pc2 :: pcc).
  by move: conn; rewrite /= => /andP[].
have rpcc' : right_limit (last_cell (pc2 :: pcc)) = p_x (right_pt g).
  by exact: rpcc.
have [pleft2 | pright2 ] := lerP (p_x p) (left_limit pc2).
(* In this case, p is inside pc1, contradiction with pinc *)
  have v1 : valid_edge g p by move: pong=> /andP[].
  have pc1cl : pc1 \in closed by apply: pcccl; rewrite inE eqxx.
  suff pin1 : inside_closed' p pc1.
    have [cqpc1 | ] := disj_closed ccl pc1cl.
      move: puh; rewrite cqpc1 (highs _ (mem_head _ _)) strict_nonAunder //.
      by rewrite pong.
  by move=> /(_ p); rewrite pin1 pinc.
  rewrite inside_closed'E.
  have r1l2 : right_limit pc1 = left_limit pc2.
    by apply/eqP; move: conn=> /= /andP[].
  move: (conn)=> /= /andP[] /eqP -> _; rewrite pleft2 pc1lp !andbT.
  rewrite (highs _ (mem_head _ _)) under_onVstrict // pong /=.
  have ponh : p === high pc1 by rewrite (highs _ (mem_head _ _)).
  have noc1 : inter_at_ext (low pc1) (high pc1).
    by apply/noc; apply: obstacles_sub; rewrite mem_cat map_f //= ?orbT.
  move: (pleft2); rewrite le_eqVlt=> /orP[/eqP pat | pltstrict]; last first.
    have := closed_cell_in_high_above_low (low_dif_high pc1cl) (low_high pc1cl)
      noc1 (closed_ok pc1cl) _ ponh; apply.
    move: (conn)=> /= /andP[] /eqP -> _.
    by rewrite pltstrict pc1lp.
  have sl : p_x (left_pt g) < p_x p.
    have llh := left_limit_left_pt_high_cl (closed_ok pc1cl).
    by rewrite -(highs _ (mem_head _ _)); apply: (le_lt_trans llh).
  have pc2cl : pc2 \in closed by apply: pcccl'; rewrite mem_head.
  have sr : p_x p < p_x (right_pt g).
    rewrite pat.
    rewrite (lt_le_trans (non_empty_closed pc2cl)) //.
    have := right_limit_right_pt_high_cl (closed_ok pc2cl).
    by rewrite (highs' _ (mem_head _ _)).
  have [vl1 vh1] : valid_edge (low pc1) p /\ valid_edge (high pc1) p.
    have := in_bound_closed_valid (closed_ok pc1cl) (ltW pc1lp).
    by rewrite pat r1l2 le_refl=> /(_ isT).
  have := above_low pc1cl ponh vl1.
  rewrite strict_nonAunder // negb_and negbK=> /orP[] ponl; last by [].
  have lo : low pc1 \in bottom :: top :: obstacles.
    by apply: obstacles_sub; rewrite mem_cat map_f.
  have ho : high pc1 \in bottom :: top :: obstacles.
    by apply: obstacles_sub; rewrite mem_cat map_f ?orbT.
  have [lqh | ] := noc ho lo.
    by have := low_dif_high pc1cl; rewrite lqh eqxx.
  move=> /(_ p ponh ponl); rewrite !inE=> /orP[]/eqP pext.
    by move: sl; rewrite pext (highs _ (mem_head _ _)) lt_irreflexive.
  by move: sr; rewrite pext (highs _ (mem_head _ _)) lt_irreflexive.
(* In this case, we use the induction hypothesis *)
by have := Ih pc2 pcccl' highs' conn' rpcc' pright2.
Qed.

End safety_property.

Section main_statement.

Variable R : realFieldType.

Notation pt := (@pt (Num.RealField.sort R)).
Notation p_x := (p_x (Num.RealField.sort R)).
Notation p_y := (p_y (Num.RealField.sort R)).
Notation Bpt := (Bpt (Num.RealField.sort R)).
Notation edge := (@edge R).
Notation cell := (@cell (Num.RealField.sort R) edge).
Notation low := (low (Num.RealField.sort R) edge).
Notation high := (high (Num.RealField.sort R) edge).
Notation left_pts := (left_pts (Num.RealField.sort R) edge).
Notation right_pts := (right_pts (Num.RealField.sort R) edge).
Notation left_limit := (left_limit (Num.RealField.sort R) 1 edge).
Notation right_limit := (right_limit (Num.RealField.sort R) 1 edge).
Notation dummy_pt := (dummy_pt (Num.RealField.sort R) 1).
Notation event := (@event (Num.RealField.sort R) edge).
Notation point := (@point (Num.RealField.sort R) edge).
Notation outgoing := (@outgoing (Num.RealField.sort R) edge).
Notation point_under_edge :=
  (point_under_edge (Num.RealField.sort R) <=%R +%R (fun x y => x - y)
    *%R 1 edge (@left_pt R)(@right_pt R)).
Notation "p <<= e" := (point_under_edge p e).
Notation "p >>> e" := (negb (point_under_edge p e)).
Notation valid_edge :=
  (valid_edge (Num.RealField.sort R) <=%R edge (@left_pt R) (@right_pt R)).
Notation point_strictly_under_edge :=
  (point_strictly_under_edge (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
    *%R 1 edge (@left_pt R)(@right_pt R)).
Notation "p <<< e" := (point_strictly_under_edge p e).
Notation "p >>= e" := (negb (point_strictly_under_edge p e)).
Notation edge_below :=
  (generic_trajectories.edge_below (Num.RealField.sort R) eq_op <=%R +%R
    (fun x y => x - y) *%R 1 edge (@left_pt R) (@right_pt R)).
Notation "x <| y" := (edge_below x y).

Notation vertical_projection :=
  (vertical_projection (Num.RealField.sort R) <=%R +%R
  (fun x y => x - y) *%R
  (fun x y => x / y) edge (@left_pt R) (@right_pt R)).
Notation leftmost_points :=
 (leftmost_points (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R
  (fun x y => x / y) edge (@left_pt R) (@right_pt R)).
Notation start_open_cell :=
  (start_open_cell (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R
  (fun x y => x / y) edge (@left_pt R) (@right_pt R)).

Arguments pt_eqb : simpl never.

Lemma start_open_cell_ok (bottom top : edge) p :
  {in [:: bottom; top] &, forall g1 g2, inter_at_ext g1 g2} ->
  inside_box bottom top p ->
  open_cell_side_limit_ok (start_open_cell bottom top).
Proof.
move=> noc0 /andP[] /andP[] pab put /andP[] /andP[] lbp prb /andP[] ltp prt.
have noc : below_alt bottom top.
  by apply: (inter_at_ext_no_crossing noc0); rewrite !inE eqxx ?orbT.
have vb : valid_edge bottom p by rewrite /valid_edge/generic_trajectories.valid_edge !ltW.
have vt : valid_edge top p by rewrite /valid_edge/generic_trajectories.valid_edge !ltW.
rewrite /open_cell_side_limit_ok /=.
have ln0 : leftmost_points bottom top != [::] :> seq pt.
  rewrite /leftmost_points/generic_trajectories.leftmost_points.
  case: ifP=> [lbl | ltl]; rewrite pvertE //.
        by rewrite /no_dup_seq /=; case: ifP.
      rewrite R_ltb_lt in lbl.
      rewrite /valid_edge/generic_trajectories.valid_edge.
      by rewrite ltW // ?ltW // (lt_trans ltp).
    by rewrite /no_dup_seq /=; case: ifP=> _.
  move: ltl=> /negbT; rewrite R_ltb_lt -leNgt=> ltl.
  by rewrite /valid_edge/generic_trajectories.valid_edge ltl ltW // (lt_trans lbp).
rewrite ln0 /=.
have samex : all (fun p => p_x p == left_limit (start_open_cell bottom top))
               (leftmost_points bottom top).
  rewrite /left_limit.
  rewrite /left_pts /=.
  rewrite /leftmost_points.
  case: ifP=> [lbl | ltl].
    rewrite R_ltb_lt in lbl.
    rewrite pvertE; last first.
      by rewrite /valid_edge ltW // ltW // (lt_trans ltp).
    rewrite -no_dup_seq_aux_eq head_no_dup_seq.
    apply/allP=> q; rewrite mem_no_dup_seq /=.
    by rewrite !inE=> /orP[] /= /eqP -> /=.
  move: ltl=> /negbT; rewrite R_ltb_lt -leNgt=> ltl.
  rewrite pvertE; last first.
    by rewrite /valid_edge/generic_trajectories.valid_edge ltl ltW // (lt_trans lbp).
  set W := (X in no_dup_seq_aux _ X).
  have -> : no_dup_seq_aux (pt_eqb R eq_op) W = no_dup_seq (W : seq pt).
    by apply/esym/(@no_dup_seq_aux_eq pt).
  have := (@eq_all_r pt _ _ (@mem_no_dup_seq pt _)).
  move=> ->.
  rewrite head_no_dup_seq.
  by rewrite /W /= !eqxx.
rewrite samex /=.
have headin : head dummy_pt (leftmost_points bottom top) === top.
  rewrite /leftmost_points/generic_trajectories.leftmost_points.
  case: ifP => [lbl | ltl].
    rewrite R_ltb_lt in lbl.
    rewrite pvertE; last first.
      by rewrite /valid_edge ltW // ltW // (lt_trans ltp).
    rewrite -no_dup_seq_aux_eq head_no_dup_seq.
    by rewrite /= left_on_edge.
  move: ltl=> /negbT; rewrite R_ltb_lt -leNgt=> ltl.
  rewrite pvertE; last first.
    by rewrite /valid_edge/generic_trajectories.valid_edge ltl ltW // (lt_trans lbp).
  set W := (X in no_dup_seq_aux _ X).
  have -> : no_dup_seq_aux (pt_eqb R eq_op) W = no_dup_seq (W : seq pt).
    by apply/esym/(@no_dup_seq_aux_eq pt).
  rewrite (@head_no_dup_seq pt).
  rewrite /= pvert_on // /valid_edge/generic_trajectories.valid_edge.
  by rewrite ltl ltW // (lt_trans lbp).
have lastin : last dummy_pt (leftmost_points bottom top) === bottom.
  rewrite /leftmost_points/generic_trajectories.leftmost_points.
  case: ifP => [lbl | ltl].
    rewrite R_ltb_lt in lbl.
    rewrite pvertE; last first.
      by rewrite /valid_edge ltW // ltW // (lt_trans ltp).
    rewrite -no_dup_seq_aux_eq last_no_dup_seq.
    by rewrite /= pvert_on // /valid_edge ltW // ltW // (lt_trans ltp).
  move: ltl=> /negbT; rewrite R_ltb_lt -leNgt=> ltl.
  rewrite pvertE; last first.
    by rewrite /valid_edge ltl ltW // (lt_trans lbp).
  set W := (X in no_dup_seq_aux _ X).
  have -> : no_dup_seq_aux (pt_eqb R eq_op) W = no_dup_seq (W : seq pt).
    by apply/esym/(@no_dup_seq_aux_eq pt).
  rewrite (@last_no_dup_seq pt).
  by rewrite /= left_on_edge.
rewrite headin lastin !andbT.
have blt : bottom <| top.
  by have := edge_below_from_point_above noc vb vt (underWC pab) put.
rewrite /leftmost_points/generic_trajectories.leftmost_points.
case: ifP => [lbl | ltl].
  rewrite R_ltb_lt in lbl.
  have vtb : valid_edge bottom (left_pt top).
    by rewrite /valid_edge/generic_trajectories.valid_edge ltW // ltW // (lt_trans ltp).
  rewrite pvertE //=.
  rewrite -/(_ == _); case: ifP=> //= /negbT dif.
  have := order_below_viz_vertical vtb (valid_edge_left top).
  rewrite pvertE // => /(_ _ (left_pt top) erefl _ blt) /=.
  have -> : vertical_projection
    (left_pt top) top = Some (left_pt top).
   rewrite (pvertE (valid_edge_left _)); congr (Some _); apply/eqP.
   by rewrite pt_eqE /= (on_pvert (left_on_edge _)) !eqxx.
  move=> /(_ erefl); rewrite le_eqVlt=> /orP[/eqP abs | -> //].
  have := pvert_on vtb; rewrite abs => lton.
  have lteq : Bpt (p_x (left_pt top))(p_y (left_pt top)) =
        left_pt top.
    by apply/(@eqP pt); rewrite pt_eqE /= !eqxx.
  rewrite lteq in lton.
  have [bqt |]: inter_at_ext bottom top by apply: noc0; rewrite !inE eqxx ?orbT.
    by rewrite bqt lt_irreflexive in lbl.
  move=> /(_ _ lton (left_on_edge _)); rewrite !inE=> /orP[] /eqP same.
    by rewrite same lt_irreflexive in lbl.
  by have := lt_trans ltp prb; rewrite same lt_irreflexive.
move: ltl=> /negbT; rewrite R_ltb_lt -leNgt=> ltl.
have vbt : valid_edge top (left_pt bottom).
  by rewrite /valid_edge/generic_trajectories.valid_edge ltl ltW // (lt_trans lbp prt).
rewrite -/(vertical_projection _ _).
rewrite pvertE //=.
case: ifP=> [bont | bnont ].
  by [].
have := order_below_viz_vertical (valid_edge_left bottom) vbt.
have -> : vertical_projection (left_pt bottom) bottom =
               Some (left_pt bottom).
  rewrite (pvertE (valid_edge_left _)); congr (Some _); apply/eqP.
  by rewrite pt_eqE /= (on_pvert (left_on_edge _)) !eqxx.
rewrite pvertE // => /(_ (left_pt bottom) _ erefl erefl blt) /=.
rewrite le_eqVlt=> /orP[/eqP abs | -> //].
have := pvert_on vbt; rewrite abs => lton.
have lteq : Bpt (p_x (left_pt bottom))(p_y (left_pt bottom)) =
        left_pt bottom.
  by apply/(@eqP pt); rewrite pt_eqE /= !eqxx.
rewrite -abs lteq in lton.
have [bqt |]: inter_at_ext top bottom by apply: noc0; rewrite !inE eqxx ?orbT.
  by move: pab; rewrite -bqt under_onVstrict // put orbT.
  move=> /(_ _ lton (left_on_edge _)); rewrite !inE=> /orP[] /eqP same.
  move: bnont.
  rewrite same (on_pvert (left_on_edge top)).
  rewrite -[X in X = false]/(_ == _ :> pt).
  by rewrite pt_eqE !eqxx.
by have := lt_trans lbp prt; rewrite same lt_irreflexive.
Qed.

Lemma has_inside_box_bottom_below_top (bottom top : edge) p :
  {in [:: bottom; top] &, forall g1 g2, inter_at_ext g1 g2} ->
  inside_box bottom top p ->
  bottom <| top.
Proof.
move=> noc0.
have : below_alt bottom top.
  by apply: (inter_at_ext_no_crossing noc0); rewrite !inE eqxx ?orbT.
move=> [] // abs.
move=> /andP[] /andP[] pab put /andP[] /andP[] vb1 vb2 /andP[] vt1 vt2.
have vb : valid_edge bottom p.
  by rewrite /valid_edge/generic_trajectories.valid_edge !ltW.
have vt : valid_edge top p.
  by rewrite /valid_edge/generic_trajectories.valid_edge !ltW.
have pub := order_edges_strict_viz_point vt vb abs put.
by move: pab; rewrite under_onVstrict // pub orbT.
Qed.

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

Lemma start_yields_safe_cells evs bottom top (open closed : seq cell):
  sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) evs ->
  {in [:: bottom, top &
         events_to_edges evs] &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  {in evs, forall ev : event, out_left_event ev} ->
  {in evs, forall ev : event, uniq (outgoing ev)} ->
  close_edges_from_events evs ->
  {in events_to_edges evs & evs, forall g e, non_inner g (point e)} ->
  main_process bottom top evs = (open, closed) ->
  {in closed & events_to_edges evs, forall c g p,
    strict_inside_closed p c -> ~~(p === g)}.
Proof.
set p_x' := generic_trajectories.p_x R.
set point' := generic_trajectories.point R edge.
have [ev0 | evsn0] := eqVneq evs [::].
  rewrite /start /=; rewrite ev0 /=.
  by move=> _ _ _ _ _ _ _ [] _ <-.
move=> general_position no_crossing.
move=> all_points_in out_edges_correct outgoing_event_unique.
move=> edges_closed no_event_in_edge start_eq.
have [e0 e0in] : exists e, e \in evs.
  by case: (evs) evsn0 => [ | a ?] //; exists a; rewrite mem_head.
have inbox_e : inside_box bottom top (point e0).
  by apply: (@allP pt _ _ all_points_in); rewrite map_f.
have noc0 : {in [:: bottom; top] &, forall g1 g2, inter_at_ext g1 g2}.
  move=> g1 g2 g1in g2in.
  by apply: no_crossing; rewrite -[_ :: _]/([:: _; _] ++ _) mem_cat ?g1in ?g2in.
have startok : open_cell_side_limit_ok (start_open_cell bottom top).
   by have := start_open_cell_ok noc0 inbox_e.
have bottom_below_top : bottom <| top.
  by have := has_inside_box_bottom_below_top noc0 inbox_e.
have sorted_lex : sorted (@lexPtEv _) evs.
  move: general_position; apply: sub_sorted.
  by move=> e1 e2; rewrite /lexPtEv/lexPt=> ->.
have all_edges_in :   {in events_to_edges evs, forall g,
         inside_box bottom top (left_pt g) &&
         inside_box bottom top (right_pt g)}.
  by apply: edges_inside_from_events_inside.
have [closed_has_disjoint_cells no_intersection_closed_open]:=
   complete_disjoint_general_position general_position bottom_below_top
   startok no_crossing all_edges_in all_points_in sorted_lex (@subset_id _ _)
   out_edges_correct outgoing_event_unique edges_closed start_eq.
have [all_edges_covered all_points_covered]:=
   start_edge_covered_general_position general_position bottom_below_top
   startok no_crossing all_edges_in all_points_in sorted_lex (@subset_id _ _)
   out_edges_correct edges_closed no_event_in_edge outgoing_event_unique
   start_eq.
have [closed_main_properties [subcl [all_closed_ok last_open_props]]] :=
   start_safe_sides general_position bottom_below_top startok no_crossing
   all_edges_in all_points_in sorted_lex (@subset_id _ _) out_edges_correct
   edges_closed no_event_in_edge outgoing_event_unique start_eq.
move=> c g cin gin p pin.
set ref_points := [seq point e | e <- evs].
(* TODO : decide on moving this to a separate lemma. *)
have sub_ref : {subset [seq left_pt g | g <- events_to_edges evs] ++
                  [seq right_pt g | g <- events_to_edges evs] <=
                  (ref_points : seq pt)}.
  rewrite /ref_points.
  move: edges_closed out_edges_correct.
  elim: (evs) => [ | ev evs' Ih] //= => /andP [cl1 /Ih {}Ih].
  move=> out_evs.
  have oute : out_left_event ev by apply: out_evs; rewrite mem_head.
  have {}out_evs : {in evs', forall ev, out_left_event ev}.
   by move=> e ein; apply: out_evs; rewrite inE ein orbT.
  have {}Ih := Ih out_evs.
  rewrite events_to_edges_cons.
  move=> q; rewrite mem_cat=> /orP[] /mapP[e + ->].
    rewrite mem_cat => /orP[/oute/eqP -> | ein ]; first by rewrite mem_head.
    rewrite inE; apply/orP; right; apply: Ih.
    by rewrite mem_cat map_f.
  rewrite mem_cat=> /orP[/(allP cl1)/hasP[e' e'in /eqP ->] | e'in].
    by rewrite inE map_f ?orbT.
  rewrite inE; apply/orP; right; apply: Ih.
  by rewrite mem_cat map_f ?orbT.
have covered_closed :
  {in events_to_edges evs, forall g, edge_covered g [::] closed}.
  move: last_open_props=> [slo [lloq [hloq [ocdis last_open_props]]]].
  case oeq : open slo => [ | lsto [ | ? ?]] // _.
  move=> g' g'in.
  (* TODO : make a separate lemma. *)
  have g'ntop : g' != top.
    apply/negP=> /eqP abs.
    have := all_edges_in _ g'in => /andP[] /andP[] _ /andP[] _.
    by rewrite abs lt_irreflexive.
  have := all_edges_covered _ g'in; rewrite oeq.
  move=> [ | closed_covered]; last by right; exact: closed_covered.
  move=> [opc [pcc [_ [highs [ _ [ opcin _]]]]]].
  move: g'ntop.
  rewrite -(highs opc); last by rewrite mem_rcons mem_head.
  move: opcin; rewrite inE=> /eqP ->.
  by rewrite -hloq oeq /= eqxx.
have non_empty_closed :
 {in closed, forall c, left_limit c < right_limit c}.
 by move=> c' c'in; have [_ [_ []]]:= closed_main_properties _ c'in.
have rf_cl : {in closed, forall c, low c <| high c}.
  by move=> c' c'in; have [it _] := closed_main_properties _ c'in.
have dif_lh_cl : {in closed, forall c, low c != high c}.
  by move=> c' c'in; have [_ [it _]] := closed_main_properties _ c'in.
have points_covered' : {in [seq left_pt g0 | g0 <- events_to_edges evs] ++
       [seq right_pt g0 | g0 <- events_to_edges evs],
     forall p0 : pt,
     exists2 c0 : cell,
       c0 \in closed & p0 \in (right_pts c0 : seq pt) /\ p0 >>> low c0}.
  by move=> q /sub_ref/mapP[e ein ->]; apply: all_points_covered.
have puh : p <<< high c.
  by move: pin; rewrite /strict_inside_closed => /andP[] /andP[].
have pal : p >>> low c.
  by move: pin; rewrite /strict_inside_closed => /andP[] /andP[].
have p_between : left_limit c < p_x p < right_limit c.
  by move: pin; rewrite /strict_inside_closed=> /andP[].
by have := safe_cell_interior subcl (@subset_id _ _) closed_has_disjoint_cells
  covered_closed points_covered' non_empty_closed (allP all_closed_ok)
  no_crossing rf_cl dif_lh_cl cin puh pal p_between gin.
Qed.

End main_statement.
