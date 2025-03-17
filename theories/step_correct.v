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

Notation complete_process :=
  (complete_process (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation edges_to_cells :=
  (edges_to_cells (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) left_pt right_pt).

Notation rightmost_points :=
  (rightmost_points (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y) edge left_pt right_pt).

Notation check_bounding_box :=
  (check_bounding_box (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y) 1 edge left_pt right_pt).

Notation edges_to_events := 
  (generic_trajectories.edges_to_events (Num.RealField.sort R)
  eq_op <=%R edge left_pt right_pt).

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

Lemma step_safe_side_invariant bottom top all_e past st s ev events :
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
  safe_side_non_gp_invariant bottom top s all_e past st (ev :: events) ->
  safe_side_non_gp_invariant bottom top s all_e (rcons past ev)
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

Definition find_covering_cell s p g :
  s != [::] ->
  p === g ->
  p != left_pt g ->
  connect_limits s ->
  left_limit (head_cell s) = p_x (left_pt g) ->
  p_x p <= right_limit (last_cell s) ->
  {c | c \in s /\ left_limit c < p_x p <= right_limit c}.
Proof.
move=> + pong pnlg.
elim/last_ind : s => [ | /= s a Ih] // _ cs lb rb.
have [s0 | sn0] := eqVneq s [::].
  exists a.
  split; first by rewrite mem_rcons inE eqxx.
  move: rb; rewrite andbC /last_cell last_rcons=> -> /=.
  move: (proj1 (andP (proj2 (andP pong)))).
  rewrite -lb s0 /=.
  have llaq : left_limit a = p_x (left_pt g).
    by rewrite -lb s0.
  rewrite le_eqVlt => /orP[/eqP samex' | xllt]; last by [].
  have samex : p_x (left_pt g) = p_x p.
    by rewrite -llaq samex'.
  have samey : p_y (left_pt g) = p_y p.
    by apply: (on_edge_same_point (left_on_edge g) pong samex).
  by move:pnlg; rewrite eq_sym pt_eqE samex samey !eqxx.
have [b [s' sq]] : {b & { s' | s = b :: s'}}.
  by case sq : s (sn0) => [ | b s'] //= _; exists b, s'.
have cs' : connect_limits s.
  move: cs; rewrite /connect_limits.
  by rewrite sq /= rcons_path=> /andP[].
have lb' : left_limit (head_cell s) = p_x (left_pt g).
  by rewrite -lb sq.
have [ina | ins] := ltP (left_limit a) (p_x p); last first.
  have rb' : p_x p <= right_limit (last_cell s).
    move: cs; rewrite /connect_limits.
    rewrite sq /= rcons_path=> /andP[] _ /= /eqP.
    by rewrite /last_cell=> ->.
  have [c [cin pbetween]]:= Ih sn0 cs' lb' rb'.
  exists c; split; last exact: pbetween.
  by rewrite mem_rcons inE cin orbT.
exists a.
split; first by rewrite mem_rcons inE eqxx.
rewrite ina /=.
by move: rb; rewrite /last_cell last_rcons.
Defined.

Lemma edge_covered_closed_to_cell (s2 : seq cell) p g :
  {in cell_edges s2 &, forall g1 g2, inter_at_ext g1 g2} ->
  {in s2, forall c, (low c <| high c) && (low c != high c)} ->
  {in s2, forall c, closed_cell_side_limit_ok c} ->
  edge_covered_closed g s2 -> p === g -> 
  p \notin [:: left_pt g; right_pt g] ->
  exists2 c, c \in s2 & inside_closed' p c /\ ~ strict_inside_closed p c.
Proof.
move=> s2noc s2wf s2ok [pcc [pccn0 [pccsub [hpcc [cpcc [lb rb]]]]]] pong.
have : p_x p <= right_limit (last_cell pcc).
  by rewrite rb (proj2 (andP (proj2 (andP pong)))).
move: pcc pccn0 pccsub hpcc cpcc lb {rb}.
elim/last_ind => [ | pcc lc Ih] // _.
have [inright | inleft] := ltP (left_limit lc) (p_x p).
  move=> pccsub allhigh cpcc llh rb pnl.
  have lcin : lc \in rcons pcc lc by rewrite mem_rcons inE eqxx.
  have lcin2 : lc \in s2 by apply: pccsub.
  exists lc; first by [].
  have hlc : high lc = g by apply: (allhigh _ lcin).
  have lcok : closed_cell_side_limit_ok lc.
    by apply: (s2ok lc lcin2).
  have rb' : p_x p <= right_limit lc.
    by move: rb; rewrite /last_cell last_rcons.
  split.
    rewrite inside_closed'E.
    rewrite inright rb' !andbT.
    have [vllc vhlc]:= in_bound_closed_valid lcok (ltW inright) rb'.
    rewrite (under_onVstrict vhlc) hlc pong /=.
    have lbelow : (low lc <| g) && (low lc != g).
      by rewrite -hlc; have := s2wf lc lcin2.
    apply/negP; rewrite (under_onVstrict vllc).
    move=> /orP[ponlow | pstrictunderlow].
      have hlcin : high lc \in cell_edges s2.
        by rewrite mem_cat map_f // !orbT.
      have llcin : low lc \in cell_edges s2.
        by rewrite mem_cat map_f.
      have [ hql | ]:= s2noc _ _ hlcin llcin.
        by rewrite -hql hlc eqxx andbF in lbelow.
      rewrite hlc.
      by move=> /(_ p pong ponlow); rewrite (negbTE pnl).
    have := order_edges_strict_viz_point vllc (proj2 (andP pong))
      (proj1 (andP lbelow)) pstrictunderlow.
    by rewrite (strict_nonAunder (proj2 (andP pong))) pong.
  rewrite /strict_inside_closed hlc.
  by rewrite (strict_nonAunder (proj2 (andP pong))) pong.
move=> pccsub allhigh cpcc llpcc _ pnl.
have pccsub' : {subset pcc <= s2}.
  by move=> c cin; apply: pccsub; rewrite mem_rcons inE cin orbT.
have allhigh' : {in pcc, forall c, high c = g}.
  by move=> c cin; apply: allhigh; rewrite mem_rcons inE cin orbT.
have pccn0 : pcc != [::].
  apply/eqP=> pcc0; move: llpcc; rewrite pcc0 /= => atll.
  have xp : p_x p = p_x (left_pt g).
    by apply: le_anti; rewrite (proj1 (andP (proj2 (andP pong)))) -atll inleft.
  case/negP: pnl; rewrite inE pt_eqE xp eqxx.
  have := on_edge_same_point pong (left_on_edge _) xp => ->.
  by rewrite eqxx.
have /andP[ pcc' /eqP rl']: connect_limits pcc &&
  (right_limit (last dummy_cell pcc) == left_limit lc).
  by move : cpcc; rewrite connect_limits_rcons.
have llpcc' : left_limit (head_cell pcc) = p_x (left_pt g).
  by move: llpcc pccn0; case: (pcc) => [ | ? ?].
move: inleft; rewrite -rl'=> inleft.
apply: (Ih pccn0 pccsub' allhigh' pcc' llpcc' inleft pnl).
Qed.

Lemma edge_covered_to_cell (s1 s2 : seq cell) p g :
  {in cell_edges s2 &, forall g1 g2, inter_at_ext g1 g2} ->
  {in s2, forall c, closed_cell_side_limit_ok c} ->
  (exists2 c', c' \in s2 & inside_closed' (left_pt g) c' /\
        ~ strict_inside_closed (left_pt g) c') ->
  {in s2, forall c, (low c <| high c) && (low c != high c)} ->
  edge_covered g s1 s2 -> p === g -> p != right_pt g ->
  (exists2 c, c \in s1 & high c = g /\ left_limit c < p_x p) \/
  (exists2 c, c \in s2 & inside_closed' p c /\ ~ strict_inside_closed p c).
Proof.
move=> nocs' clok left_pt_covered cl_hl.
move=> [[oc [pcc A]] | [pcc A]] /[dup] pong /andP[] _ vpg pnright.
  move: A=> [pcc_sub [allhigh [cnct [ocin lb]]]].
  have [pinoc | pincc] := ltP (left_limit oc) (p_x p).
    left; exists oc.
      by [].
    split; last by [].
    by apply: allhigh; rewrite mem_rcons inE eqxx.
  have [pcc0 | pccn0] := eqVneq pcc [::].
    move: lb; rewrite pcc0 /= => lb.
    have same_x : p_x p = p_x (left_pt g).
      apply: le_anti.
      by rewrite (proj1 (andP (proj2 (andP pong)))) -lb pincc.
    have pl : p = left_pt g.
      have same_y := on_edge_same_point pong (left_on_edge _) same_x.
      by apply/eqP; rewrite pt_eqE same_x same_y !eqxx.
    by right; rewrite pl; apply: left_pt_covered.
  have [b [s' pccq]] : exists b s', pcc = b :: s'.
    by case: (pcc) (pccn0) => [ | b s'] // _; exists b, s'.
  have cpcc : connect_limits pcc.
    by move: cnct; rewrite pccq /= rcons_path => /andP[].
  have lb' : left_limit (head_cell pcc) = p_x (left_pt g).
    by move: lb; rewrite pccq.
  have rb' : p_x p <= right_limit (last_cell pcc).
    by move: cnct pincc; rewrite pccq /= rcons_path => /andP[] _ /eqP <-.
  have [pleft | pnleft] := eqVneq p (left_pt g).
    by right; rewrite pleft; apply: left_pt_covered.
  have [c [cin pcP]] := find_covering_cell pccn0 pong pnleft cpcc lb' rb'.
  have hcq : high c = g by apply: allhigh; rewrite mem_rcons inE cin orbT.
  have cok : closed_cell_side_limit_ok c by apply/clok/pcc_sub.
  right; exists c.
    by apply: pcc_sub.
  rewrite inside_closed'E.
  have vlh : valid_edge (high c) p by rewrite hcq; move: pong => /andP[].
  (* TODO: there should about lemma about inside_closed' and valid high and low
    edges of the cell. *)
  split; last first.
    rewrite /strict_inside_closed.
    by rewrite (strict_nonAunder vlh) hcq pong.
  have vll : valid_edge (low c) p.
    move: (cok)=> /andP[] slpt /andP[] allxl /andP[] _ /andP[] _ /andP[] lon.
    move=> /andP[] srpt /andP[] allxr /andP[] _ /andP[] _ lon'.
    have lplin : last dummy_pt (left_pts c) \in left_pts c.
      by case: left_pts slpt => [ | a tl] //= _; rewrite mem_last.
    have xql : p_x (last dummy_pt (left_pts c)) = left_limit c.
      by apply: (eqP (allP allxl _ lplin)).
    have left_cond : p_x (left_pt (low c)) <= p_x p.
      apply: le_trans (ltW (proj1 (andP pcP))).
      rewrite -xql.
      by move: lon=> /andP[] _ /andP[].
    have right_cond : p_x p <= p_x (right_pt (low c)).
      apply/(le_trans (proj2 (andP pcP))).
      rewrite -(closed_cell_side_limit_ok_last cok).
      by move: lon' => /andP[] _ /andP[].
    by rewrite /valid_edge left_cond right_cond.
  rewrite (under_onVstrict vlh) hcq pong /= pcP andbT.
  rewrite (under_onVstrict vll) negb_or.
  have pal : p >>= low c.
    apply/negP=> pbl.
    have := order_edges_strict_viz_point vll vlh
     (proj1 (andP (cl_hl _ (pcc_sub _ cin)))) pbl.
    by rewrite hcq (strict_nonAunder vpg) pong.
  rewrite pal andbT.
  have lce : low c \in cell_edges s2.
    by rewrite mem_cat map_f // (pcc_sub _ cin).
  have hce : high c \in cell_edges s2.
    by rewrite mem_cat map_f ?orbT // (pcc_sub _ cin).
  apply/negP=> ponl.
  have := nocs' _ _ hce lce; rewrite /inter_at_ext=> -[ lhq | ].
    by have := cl_hl _ (pcc_sub _ cin); rewrite lhq eqxx andbF.
  move=> /(_ p _ ponl); rewrite hcq !inE (negbTE pnleft) (negbTE pnright).
  by move=> /(_ pong).
move: A => [pccn0 [pcc_sub [allhigh [cpcc [lb rb]]]]].
have [pleft | pnleft] := eqVneq p (left_pt g).
    by right; rewrite pleft; apply: left_pt_covered.
have lpccin : last_cell pcc \in s2.
  case : (pcc) pccn0 pcc_sub => [ | a tl] // _; apply.
  by rewrite /last_cell /= mem_last.
have rb' : p_x p <= right_limit (last_cell pcc).
  by rewrite rb (proj2 (andP vpg)).
have [c [cin pcP]] := find_covering_cell pccn0 pong pnleft cpcc lb rb'.
right; exists c.
  by apply: pcc_sub.
have hcq : high c = g by apply: allhigh.
have cok : closed_cell_side_limit_ok c by apply/clok/pcc_sub.
have vlh : valid_edge (high c) p by rewrite hcq; move: pong => /andP[].
  (* TODO: there should about lemma about inside_closed' and valid high and low
    edges of the cell. *)
have vll : valid_edge (low c) p.
  move: (cok)=> /andP[] slpt /andP[] allxl /andP[] _ /andP[] _ /andP[] lon.
  move=> /andP[] srpt /andP[] allxr /andP[] _ /andP[] _ lon'.
  have lplin : last dummy_pt (left_pts c) \in left_pts c.
    by case: left_pts slpt => [ | a tl] //= _; rewrite mem_last.
  have xql : p_x (last dummy_pt (left_pts c)) = left_limit c.
    by apply: (eqP (allP allxl _ lplin)).
  have left_cond : p_x (left_pt (low c)) <= p_x p.
    apply: le_trans (ltW (proj1 (andP pcP))).
    rewrite -xql.
    by move: lon=> /andP[] _ /andP[].
  have right_cond : p_x p <= p_x (right_pt (low c)).
    apply/(le_trans (proj2 (andP pcP))).
    rewrite -(closed_cell_side_limit_ok_last cok).
    by move: lon' => /andP[] _ /andP[].
  by rewrite /valid_edge left_cond right_cond.
split; last first.
  by rewrite /strict_inside_closed (strict_nonAunder vlh) hcq pong.
rewrite inside_closed'E pcP andbT.
rewrite (under_onVstrict vlh) hcq pong /=.
have pal : p >>= low c.
  apply/negP=> pbl.
  have := order_edges_strict_viz_point vll vlh
    (proj1 (andP (cl_hl _ (pcc_sub _ cin)))) pbl.
  by rewrite hcq (strict_nonAunder vpg) pong.
rewrite (under_onVstrict vll) (negbTE pal) orbF.
have lce : low c \in cell_edges s2.
  by rewrite mem_cat map_f // (pcc_sub _ cin).
have hce : high c \in cell_edges s2.
  by rewrite mem_cat map_f ?orbT // (pcc_sub _ cin).
apply/negP=> ponl.
have := nocs' _ _ hce lce; rewrite /inter_at_ext=> -[ lhq | ].
  by have := cl_hl _ (pcc_sub _ cin); rewrite lhq eqxx andbF.
move=> /(_ p _ ponl); rewrite hcq !inE (negbTE pnleft) (negbTE pnright).
by move=> /(_ pong).
Qed.

Lemma out_not_box bottom top e g :
  inside_box bottom top (point e) ->
  out_left_event e ->
  g \in outgoing e -> (g != bottom) && (g != top).
Proof.
move=> inbox_e oute gin.
move: (inside_box_not_on inbox_e).
rewrite -(eqP (oute _ gin))=> main.
by apply /andP; split; apply/eqP=> gne; rewrite gne left_on_edge ?orbT in main.
Qed.

Lemma side_to_inside c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  p \in right_pts c ->
  p >>> low c ->
  inside_closed' p c  /\ ~ strict_inside_closed p c.
Proof.
move=> clarge.
do 5 (move=> /andP[] _); move=> /andP[] ptsn0 /andP[] allx /andP[] srt.
move=> /andP[] hon _ pin pal.
have xq : p_x p = right_limit c by apply/eqP/(allP allx).
split; last first.
  by rewrite /strict_inside_closed xq ltxx !andbF.
rewrite inside_closed'E pal /=.
rewrite xq clarge le_refl /= andbT.
have samex : p_x p = p_x (head dummy_pt (right_pts c)).
  by rewrite xq; case: right_pts ptsn0 allx => [ | ? ?] //= _ /andP[] /eqP ->.
rewrite (under_edge_lower_y samex hon).
move: srt; case: right_pts pin => [ | a tl] //=.
rewrite inE => /orP[/eqP /[dup] pa -> _ | pin] //.
rewrite (path_sortedE (rev_trans lt_trans))=> /andP[] + _.
by move=> /allP /(_ _ (map_f _ pin)) /ltW.
Qed.

(* This lemma is the main result of safety for the whole processing.
  TODO: it relies on the assumption
  that the first open cell is well formed.  This basically means that the
  two edges have a vertical overlap.  This statement should be probably
  be made clearer in a different way.

  TODO: one should probably also prove that the final sequence of open
  cells, here named "open", should be reduced to only one element. *)

Lemma closed_edges_from_eventsW s e g :
  close_edges_from_events s -> e \in s -> g \in outgoing e ->
  exists2 e', e' \in s & right_pt g = point e'.
Proof.
elim: s => [ | e0 s Ih] //= /andP[] clo0 cles.
rewrite inE => /orP[/eqP -> | ].
  move: clo0=> /allP main.
  move=> /main/hasP [e1 e1in /eqP ->].
  by exists e1; first (rewrite inE e1in orbT).
move=> ein gin; have [e1 e1in ->]:= Ih cles ein gin.
by exists e1; first (rewrite inE e1in orbT).
Qed.

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
  {in closed &, disjoint_closed_cells R} /\
  {in closed, forall c,
     strict_inside_closed (cell_center c) c /\
     low c <| high c /\
     low c != high c /\
     left_limit c < right_limit c /\
     closed_cell_side_limit_ok c /\
    (forall p,
      strict_inside_closed p c ->
      {in events_to_edges evs, forall g, ~ p === g} /\
      {in evs, forall ev, p != point ev}) /\
    forall p : pt,
     in_safe_side_left p c || in_safe_side_right p c ->
     {in events_to_edges evs, forall g, ~ p === g} /\
     {in evs, forall ev, p != point ev}} /\
  {subset (cell_edges closed) <= [:: bottom, top & s]} /\
  {in events_to_edges evs, forall g, edge_covered_closed g closed} /\
  {in evs, forall e, exists2 c, c \in closed & inside_closed' (point e) c} /\
  size open = 1%N /\ low (head_cell open) = bottom /\
  high (head_cell open) = top /\
  open_cell_side_limit_ok (head_cell open) /\
  {in open & closed, disjoint_open_closed_cells R} /\
  (forall p, in_safe_side_left p (head_cell open) ->
    {in events_to_edges evs, forall g, ~ p === g} /\
    {in evs, forall ev, p != point ev}) /\
  (evs != [::] ->
    left_limit (head_cell open) < Num.min (p_x (right_pt bottom))
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
have : safe_side_non_gp_invariant bottom top s (ev :: future_events) [:: ev]
  istate future_events.
  have := initial_safe_side_non_gp_invariant boxwf startok nocs' evsub
    evin lexev out_evs uniq_edges cle evsn0 n_inner.
  have -> : take 1 evs = [:: ev] by rewrite evsq; case: (future_events).
  by rewrite /initial_state /istate evsq oca_eq.
move=> invss req.
suff to_prove_inductively: forall events op cl st all_e processed_set,
  safe_side_non_gp_invariant bottom top s all_e processed_set st events ->
  close_edges_from_events all_e ->
  {in all_e, forall e, out_left_event e} ->
  all (inside_box bottom top) [seq point e | e <- all_e] ->
  all_e = processed_set ++ events ->
  scan events st = (op, cl) ->
  {in cl &, disjoint_closed_cells R} /\
  {in cl, forall c,
    strict_inside_closed (cell_center c) c /\
    low c <| high c /\
    low c != high c /\
    left_limit c < right_limit c /\
    closed_cell_side_limit_ok c /\
    (forall p,
      strict_inside_closed p c ->
      {in events_to_edges all_e, forall g, ~ p === g} /\
      {in all_e, forall ev, p != point ev}) /\
    forall p : pt, in_safe_side_left p c || in_safe_side_right p c ->
    {in events_to_edges (processed_set ++ events), forall g, ~ p === g} /\
         {in processed_set ++ events, forall e', p != point e'}} /\
  {in op, forall (c : cell) (p : pt), in_safe_side_left p c ->
         {in events_to_edges (processed_set ++ events), forall g, ~ p === g} /\
         {in processed_set ++ events, forall e', p != point e'}} /\
  {subset (cell_edges cl) <= [:: bottom, top & s]} /\
  {in events_to_edges all_e, forall g, edge_covered_closed g cl} /\
  {in all_e, forall e, exists2 c, c \in cl & inside_closed' (point e) c} /\
  size op = 1%N /\
  low (head_cell op) = bottom /\
  high (head_cell op) = top /\
  open_cell_side_limit_ok (head_cell op) /\
  {in op & cl, disjoint_open_closed_cells R} /\
  (forall p, in_safe_side_left p (head_cell op) ->
    {in events_to_edges all_e, forall g, ~ p === g} /\
    {in all_e, forall ev, p != point ev}) /\
  (left_limit (head_cell op) < Num.min (p_x (right_pt bottom))
      (p_x (right_pt top))).
  have := cle; rewrite [X in close_edges_from_events X] evsq=> cle'.
  have := out_evs; rewrite [in X in X -> _] evsq => out_evs'.
  have := evin; rewrite [in X in X -> _] evsq => inbox_evs'.
  by have [A [B [C [D [E [F [G [H [I [J [K [L]]]]]]]]]]]] :=
    (to_prove_inductively _ _ _ _ _ _ invss cle' out_evs' inbox_evs' erefl req).
elim=> [ | {evsq oca_eq istate invss} ev {req}future_events Ih] 
  op cl st all_e p_set.
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
  rewrite !cats0 /= => clea oute_a inbox_a all_e_q -[] <- <-.
  have [[fop0 lop0] main] :
    (fop = [::] /\ lop = [::]) /\
    size (fop ++ lsto :: lop) = 1 %N /\
    low (head_cell (fop ++ lsto :: lop)) = bottom /\
    high (head_cell (fop ++ lsto :: lop)) = top /\
    open_cell_side_limit_ok (head_cell (fop ++ lsto :: lop)) /\
    {in fop ++ lsto :: lop & lstc :: cls, disjoint_open_closed_cells R} /\
    (forall p, in_safe_side_left p (head_cell (fop ++ lsto :: lop)) ->
      {in events_to_edges all_e, forall g, ~ p === g} /\
      {in all_e, forall ev, p != point ev}) /\
    left_limit (head_cell (fop ++ lsto :: lop)) <
    Num.min (p_x (right_pt bottom)) (p_x (right_pt top)).
    have comi := ngcomm (common_non_gp_inv_dis d_inv).
    have := inv1 comi.
    rewrite /state_open_seq/= /close_alive_edges.
    move=> [] clae [] _ [] adj [] cbtom rfo.
    have hlsto : {in fop ++ lsto :: lop, forall c, high c = top}.
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
      elim/last_ind: (fop) adj ijh hlsto => [ // | fs f1 _] + ijh htop.
      rewrite -cats1 -catA /= => /adjacent_catW[] _ /= /andP[] /eqP f1l _.
      move: (d_e lsto); rewrite !mem_cat inE eqxx ?orbT => /(_ isT).
      rewrite -f1l (htop f1); last by rewrite !(mem_rcons, mem_cat, inE) eqxx.
      by rewrite (htop lsto) ?eqxx // mem_cat inE eqxx ?orbT.
    have l0 : lop = [::].
      case lopq: (lop) adj ijh hlsto => [ // | l1 ls] + ijh htop.
      move=> /adjacent_catW[] _ /= /andP[] /eqP hl _.
      move: (d_e l1); rewrite lopq !(mem_cat, inE) eqxx ?orbT => /(_ isT).
      rewrite -hl (htop l1); last by rewrite !(mem_cat, inE) eqxx !orbT.
      by rewrite (htop lsto) ?eqxx // mem_cat inE eqxx ?orbT.
    split; first by [].
    rewrite f0 l0 /=.
    move: cbtom; rewrite f0 l0 /= /cells_bottom_top /cells_low_e_top /=.
    move=> /andP[] /eqP lq /eqP hq.
    do 3 (split; first by []).
    split.
      have := sides_ok (ngcomm (common_non_gp_inv_dis d_inv)).
      by rewrite /state_open_seq /= all_cat /= => /andP[] _ /andP[].
    split.
      move=> c1 c2 c1in c2in; apply: (op_cl_dis_non_gp d_inv);
      by rewrite /state_open_seq/state_closed_seq  f0 l0 ?mem_rcons.
    have safe_left_op : 
    forall p, in_safe_side_left p lsto ->
    {in events_to_edges all_e, forall g, ~ p === g} /\
    {in all_e, forall e, p != point e}.
      split.
        rewrite all_e_q=> g /(safe_side_open_edges ss_inv).
        rewrite /state_open_seq f0 l0 /= => /(_ lsto); apply; last by [].
        by rewrite inE eqxx.
      rewrite all_e_q=> e /(safe_side_open_points ss_inv).
      rewrite /state_open_seq f0 l0 /= => /(_ lsto); apply; last by [].
      by rewrite inE eqxx.
    split.
       by [].
    by have := lst_side_lt d_inv.
  split.
    move=> c1 c2 c1in c2in.
    by apply: (cl_dis_non_gp d_inv); rewrite /state_closed_seq/= mem_rcons.
  split.
    move=> c cin.
    have cin2 : c \in rcons cls lstc by rewrite mem_rcons.
    split.
      by apply: (cell_center_in d_inv); rewrite mem_rcons.
    split; first by apply: b_e; rewrite mem_rcons.
    split; first by apply: d_e; rewrite mem_cat mem_rcons cin orbT.
    split; first by apply: (cl_large d_inv); rewrite mem_rcons.
    split; first by apply: (cl_side d_inv); rewrite mem_rcons.
    split.
      move=> p pin.
      have not_e : {in all_e, forall e, p != point e}.
        move=> e; rewrite all_e_q=> ein; apply/eqP => pe.
        have [c' c'in [er eab]]:= processed_covered e_inv ein.
        have : inside_closed' (point e) c' /\ 
         ~ strict_inside_closed (point e) c'.
          have c'ok : closed_cell_side_limit_ok c' by apply: (cl_side d_inv).
          have c'large : left_limit c' < right_limit c'.
            by apply: (cl_large d_inv).
          by apply: side_to_inside.
        have [cc' | /(_ p)] := cl_dis_non_gp d_inv cin2 c'in.
          by rewrite -cc' -pe pin=> -[].
        move=> + [inc' _] => /negP[].
        by rewrite (strict_inside_closedW pin) pe.
        split; last by [].
      move=> g /flatten_mapP/=[e ein gin] pong.
      have ein2 : e \in p_set by rewrite -all_e_q.
      have gcov := edge_covered_ec e_inv ein2 gin.
      have out_e : out_left_event e.
        by apply: oute_a.
      have [pright | pnright] := eqVneq p (right_pt g).
        have [e1 e1in rgq]:= closed_edges_from_eventsW clea ein gin.
        by have := not_e _ e1in; rewrite pright rgq eqxx.
      have [pleft | pnleft] := eqVneq p (left_pt g).
        rewrite (eqP (out_e _ gin)) in pleft.
         by have := not_e _ ein; rewrite pleft eqxx.
      have noc_cl : {in cell_edges (rcons cls lstc) &, 
        forall g1 g2, inter_at_ext g1 g2}.
        by apply: (sub_in2 _ nocs'); apply: (sub_closed ss_inv).
      have cl_lh := cl_low_high d_inv (sub_closed ss_inv) nocs'.
      have pnex : p \notin [:: left_pt g; right_pt g].
        by rewrite !inE negb_or pnleft pnright.
      have [ [a [pcc [_ [hq [_ [oco _]]]]]] |  cov_cl ] := gcov.
        have inbox_e : inside_box bottom top (point e).
          by apply: (allP inbox_a _ (map_f _ ein)).
      
        have := out_not_box inbox_e out_e gin.
        move: main=> -[] _ [] _ [] + _.
        move: oco; rewrite /state_open_seq /= fop0 lop0 /= inE => /eqP <-.
        rewrite (hq a); first by move=> ->; rewrite eqxx andbF.
        by rewrite mem_rcons inE eqxx.
      have incl := edge_covered_closed_to_cell noc_cl cl_lh (cl_side d_inv)
        cov_cl pong pnex.
      move: incl => [c1 c1in [inc1 ninc1]].
      have [cc1 | cnc1] := cl_dis_non_gp d_inv cin2 c1in.
      by case: ninc1; rewrite -cc1.
      by move: (cnc1 p); rewrite inc1 (strict_inside_closedW pin).
    move=> p pin; split.
      move=> g gin; apply: (safe_side_closed_edges ss_inv gin _ pin).
      by rewrite // mem_rcons.
    move=> e ein.
     apply: (safe_side_closed_points ss_inv ein _ pin).
     by rewrite // mem_rcons.
  have safe_op : {in fop ++ lsto :: lop,
    forall c p, in_safe_side_left p c ->
    {in events_to_edges p_set, forall g, ~ p === g} /\
    {in p_set, forall e', p != point e'}}.
    move=> c cin p pin; split.
      by move=> g gin; have := (safe_side_open_edges ss_inv gin cin pin).
    by move=> e ein; have := (safe_side_open_points ss_inv ein cin pin).
  have subc' : {subset cell_edges (lstc :: cls) <= [:: bottom, top & s]}.
    move=> g; rewrite -[_ :: _]/([:: lstc] ++ cls) cell_edges_catC cats1.
    by apply: subc.
  have cov_cl :
    {in events_to_edges all_e, forall g, edge_covered_closed g
       (lstc :: cls)}.
    move=> g /flatten_mapP [e ein gin].
    have ein2 : e \in p_set by rewrite -all_e_q.
    have [eco | [pcc [pccn0 [pccsub Others]]]]:=
      edge_covered_ec e_inv ein2 gin; last first.
      exists pcc; split; first by [].
      split; last by [].
      by move=> c /pccsub; rewrite /state_closed_seq /= mem_rcons.
    move: eco=> [oc [pcc [_ [highs [_ [ocin _]]]]]].
    have hocq : high oc = top.
      move: ocin; rewrite /state_open_seq /= fop0 lop0 inE => /eqP ocl.
      by move: main=> [_ [_ [+ _]]]; rewrite fop0 lop0 ocl.
    have gtop : g = top.
      by rewrite -hocq; apply/esym/highs; rewrite mem_rcons inE eqxx.
    have oute : out_left_event e by apply: oute_a.
    have inbox_e : inside_box bottom top (point e).
      by apply: (allP inbox_a); rewrite map_f.
    by have := out_not_box inbox_e oute gin; rewrite gtop eqxx andbF.
  have ev_cov : {in all_e, forall e, exists2 c, c \in lstc :: cls &
    inside_closed' (point e) c}.
    move=> e /[dup] ein; rewrite all_e_q => ein2.
    have [c1 /[dup] c1in + [eside eab]] := processed_covered e_inv ein2.
    rewrite /state_closed_seq /= mem_rcons => c1in2.
    have c1ok := cl_side d_inv c1in.
    have c1large := cl_large d_inv c1in.
    have [inc1 _] := side_to_inside c1large c1ok eside eab.
    by exists c1.
  by [].
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
have ss_inv' : safe_side_non_gp_invariant bottom top s all_e (rcons p_set ev)
  (step st ev) future_events.
  by apply: step_safe_side_invariant.
rewrite -[scan _ _]/(scan future_events (step st ev)) -cat_rcons.
move => clea out_eva all_e_q execq.
have := (Ih op cl _ all_e (rcons p_set ev) ss_inv' clea out_eva all_e_q execq).
by [].
Qed.


Notation complete_last_open :=
  (generic_trajectories.complete_last_open (Num.RealField.sort R) eq_op 
    <=%R +%R (fun x y => x - y) *%R
    (fun x y => x / y) edge left_pt right_pt).

Lemma no_dup_seq_cons_n0 {T : eqType} (a : T) tl :
  no_dup_seq (a :: tl) != [::].
Proof.
elim: tl a => [ | b tl Ih] a //=.
case: ifP=> [aqb | anb]; last by [].
case tlq : tl => [ | c tl'] //.
case: ifP => [bqc | bnc] //.
by have /= := Ih b; rewrite tlq bqc /=.
Qed.

Lemma all_no_dup_seq {T : eqType} (l : seq T) p :
  all p (no_dup_seq l) = all p l.
apply/idP/idP=> /allP it; apply/allP=> x xin.
  by apply: it; rewrite mem_no_dup_seq.
by rewrite mem_no_dup_seq in xin; apply: it.
Qed.

(* This lemma uses assumptions of minimal strength, but the amount of assumptions
 is quite verbose. *)
Lemma complete_safe (bottom top : edge) s 
  (closed : seq cell) (evs : seq event) :
  evs != [::] ->
  bottom <| top ->
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
  complete_process bottom top evs = closed ->
  {in closed, forall c,
    strict_inside_closed (cell_center c) c /\
    low c <| high c /\
    low c != high c /\
    left_limit c < right_limit c /\
    closed_cell_side_limit_ok c /\
    (forall p,
      strict_inside_closed p c ->
      {in events_to_edges evs, forall g, ~ p === g} /\
      {in evs, forall ev, p != point ev}) /\
    forall p : pt, in_safe_side_left p c || in_safe_side_right p c ->
    {in events_to_edges evs, forall g, ~ p === g} /\
         {in evs, forall e', p != point e'}}.
Proof.
move=> evsn0 boxwf startok nocs' inbox_s evin lexev evsub out_evs cle
  n_inner uniq_edges.
case evsq: evs evsn0 => [ | ev future_events] // _.
  rewrite complete_process_eq.
  rewrite -/(main_process bottom top (ev :: future_events)).
  have := start_safe_sides boxwf startok nocs' inbox_s evin lexev evsub out_evs
    cle n_inner uniq_edges.
  rewrite evsq.
  case: main_process => [op cl]=> /(_ _ _ erefl) Main.
  have ops : size op = 1%N.
    by move: Main=> -[] _ [] _ [] _ [] _ [] _ [] +.
  case opq : op ops => [ | a [ | ? ?]] //= _.
  set a' := cells_alg.complete_last_open a => /esym clq.
  case aeq: a => [lp rp b t].
  (* have a'eq : a' = Bcell lp (rightmost_points bottom top) b t. *)
  have a'eq : a' = Bcell lp (rightmost_points b t) b t.
    by rewrite /a' /cells_alg.complete_last_open /complete_last_open aeq /=.
  have ain : a \in op by rewrite opq inE eqxx.
  have tq : t = top.
    by move: Main; do 7 (move=> [] _); move=> []; rewrite opq aeq.
  have bq : b = bottom.
    by move: Main; do 6 (move=> [] _); move=> []; rewrite opq aeq.
  have bnt : bottom != top.
    have /non_degenerate_box // : inside_box bottom top (point ev).
    by apply: (allP evin _ (map_f _ _)); rewrite evsq inE eqxx.
  have aok : open_cell_side_limit_ok a.
    by move: Main; do 8 (move=> [] _); move=> []; rewrite opq aeq.
  have right_configs : ((p_x (right_pt bottom) < p_x (right_pt top)) &&
         (rightmost_points bottom top ==
          no_dup_seq
            [:: Bpt (p_x (right_pt bottom)) (pvert_y (right_pt bottom) top);
              right_pt bottom])) ||
          ((p_x (right_pt top) <= p_x (right_pt bottom)) &&
         (rightmost_points bottom top ==
            no_dup_seq [:: right_pt top;
              Bpt (p_x (right_pt top)) (pvert_y (right_pt top) bottom)])).
    rewrite /rightmost_points R_ltb_lt.
    case: ifP=> cmp.
      have vtrb : valid_edge top (right_pt bottom).
        have lla: p_x (left_pt top) <= left_limit a <= p_x (right_pt bottom).
          move: (aok); rewrite /open_cell_side_limit_ok.
          rewrite -(open_cell_side_limit_ok_last aok) /= aeq.
          move=> /andP[] + /andP[] + /andP[] _ /andP[] + +.
          case: (lp) => [ | x tl] // _ /= /andP[] /eqP xq _.
          move=> /andP[] _ /andP[] + _ /andP[] _ /andP[] _ +; rewrite xq tq bq.
          by move=> -> ->.
        apply/andP.
        move: lla => /andP[] ltlla llarb.
        by rewrite (le_trans ltlla llarb) (ltW cmp).
      rewrite (pvertE vtrb).
      rewrite /no_dup_seq; case: ifP=> cmp'; last by rewrite eqxx.
      have bont : right_pt bottom === top.
        by rewrite -(eqP cmp') (pvert_on vtrb).
      have : inter_at_ext top bottom by apply: nocs'; rewrite !inE eqxx ?orbT.
      move=> [/eqP | ]; first by rewrite eq_sym (negbTE bnt).
      move=> /(_ _ bont (right_on_edge _)).
      rewrite !inE.
      rewrite (_ : right_pt bottom == right_pt top = false) ?orbF; last first.
        apply/eqP=> bqt.
        by rewrite bqt ltxx in cmp.
      move=> /eqP rbqlt.
      have : inside_box bottom top (point ev).
        by apply: (allP evin _ (map_f _ _)); rewrite evsq inE eqxx.
      move=> /andP[] _ /andP[] /andP[] _ evlb /andP[] tlev _.
      by have := lt_trans tlev evlb; rewrite rbqlt ltxx.
    move: cmp=> /negbT; rewrite -leNgt => /[dup] cmp -> /=.
    have vbrt : valid_edge bottom (right_pt top).
      have lla : p_x (left_pt bottom) <= left_limit a <= p_x (right_pt top).
        move: (aok); rewrite /open_cell_side_limit_ok.
        rewrite -(open_cell_side_limit_ok_last aok) /= aeq.
        move=> /andP[] + /andP[] + /andP[] _ /andP[] + +.
        case: (lp) => [ | x tl] // _ /= /andP[] /eqP xq _.
        move=> /andP[] _ /andP[] _ + /andP[] _ /andP[] + _; rewrite xq tq bq.
        by move=> -> ->.
      apply/andP.
      move: lla => /andP[] lblla llart.
      by rewrite (le_trans lblla llart) cmp.
    by rewrite (pvertE vbrt) /=; case: ifP=> /=.
  have right_limit_a' : right_limit a' =
      Num.min (p_x (right_pt bottom)) (p_x (right_pt top)).
    rewrite /right_limit a'eq bq tq.
    by move: right_configs=> /orP[] /andP[] + /eqP ->;
      rewrite head_no_dup_seq /=; case: ltP.
  have disa' : {in cl, forall c, c_disjoint c a'}.
    move=> c cin p; have := Main; do 9 (move => [] _); move=> [] + _.
    move=> /(_ _ _ ain cin p).
    apply: contraNN=> /andP[] ->.
    rewrite inside_open'E.
    rewrite inside_closed'E a'eq /=.
    move=> /andP[] puh /andP[] pal /andP[] pgtl; rewrite -a'eq=> pler.
    rewrite aeq /= puh pal pgtl /= andbT.
    by rewrite /open_limit /= bq tq -right_limit_a'.
  move=> c; rewrite clq inE => /orP[ /eqP -> | cin]; last first.
    have [_ [Maincl _]] := Main.
    by have {}Maincl := Maincl c cin.
  have la'difh : low a' != high a'.
    rewrite a'eq bq tq /=.
    have /non_degenerate_box // : inside_box bottom top (point ev).
    by move: evin; rewrite evsq=> /andP[].
  have awf : low a' <| high a'.
    by rewrite a'eq bq tq.
  have a'ook : open_cell_side_limit_ok a'.
    move: Main; do 8 (move=> [] _); move=> [] + _.
    rewrite opq.
    by rewrite /head_cell /= aeq a'eq /open_cell_side_limit_ok /left_limit /=.
  set rx := Num.min (p_x (right_pt bottom)) (p_x (right_pt top)).
  have lllt : left_limit a' < rx.
    move: Main; do 10 (move=> [] _); move=> [] _ /(_ isT).
    by rewrite /left_limit opq  aeq /head_cell a'eq.
  have rx_low : rx <= p_x (right_pt (low a')).
    rewrite /rx a'eq bq /=.
    by case: (leP (p_x (right_pt bottom)) (p_x (right_pt top))) => // /ltW.
  have rx_high : rx <= p_x (right_pt (high a')).
    rewrite /rx a'eq tq /=.
    by case: (leP (p_x (right_pt bottom)) (p_x (right_pt top))) => // /ltW.
  have rxq : rx = right_limit a'.
    rewrite /right_limit a'eq /rx /=; move: right_configs.
    rewrite tq bq.
    move=> /orP[] /andP[] xcond /eqP ->; rewrite head_no_dup_seq /=.
      by case: ltP xcond.
    by case: leP xcond.
  have vbt' : p_x (right_pt bottom) < p_x (right_pt top) ->
    valid_edge top (right_pt bottom).
    move=> xcond.
    rewrite /valid_edge (ltW xcond).
      have := allP evin (point ev) (map_f _ _).
      have : ev \in evs by rewrite evsq inE eqxx.
      move=> /[swap] /[apply] /andP[] _ /andP[] /andP[] _ A /andP[] B _.
      by have /ltW -> := lt_trans B A.
  have vtb' : p_x (right_pt top) <= p_x (right_pt bottom) ->
    valid_edge bottom (right_pt top).
    move=> xcond.
    rewrite /valid_edge xcond.
    have := allP evin (point ev) (map_f _ _).
    have : ev \in evs by rewrite evsq inE eqxx.
    move=> /[swap] /[apply] /andP[] _ /andP[] /andP[] A _ /andP[] _ B.
    by have /ltW -> := lt_trans A B.
  have haon : head dummy_pt (right_pts a') === high a'.
    rewrite a'eq tq /=.
    move: right_configs.
    rewrite ?tq bq.
    move=> /orP[] /andP[] xcond /eqP ->; rewrite head_no_dup_seq /=.
      have vbt : valid_edge top (right_pt bottom) by apply: vbt'.
      by have := pvert_on vbt.
    by apply: right_on_edge.
  have laon : last dummy_pt (right_pts a') === low a'.
    rewrite a'eq bq /=.
    move: right_configs.
    rewrite tq ?bq.
    move=> /orP[] /andP[] xcond /eqP ->; rewrite last_no_dup_seq /=.
      by apply: right_on_edge.
    have vtb : valid_edge bottom (right_pt top) by apply: vtb'.
    by have := pvert_on vtb.
  have nocbt : inter_at_ext (low a') (high a').
    by rewrite a'eq tq bq /=; apply: nocs'; rewrite !inE eqxx ?orbT.
  have allrx : all (eq_op^~ rx) [seq p_x p | p <- right_pts a'].
    rewrite a'eq /=; move: right_configs.
    rewrite ?tq ?bq.
    move=> /orP[] /andP[] xcond /eqP ->; rewrite all_map all_no_dup_seq /=;
      rewrite /rx; move: xcond.
      by case: ltP; rewrite ?eqxx //.
    by case: lerP; rewrite ?eqxx //.
  have rpn0 : right_pts a' != [::].
    rewrite a'eq /=; move: right_configs.
    rewrite ?tq ?bq.
    by move=> /orP[] /andP[] _ /eqP ->; rewrite no_dup_seq_cons_n0.
  have ccain : strict_inside_closed (cell_center a') a'.
    by apply: (cell_center_inside_main nocbt la'difh awf a'ook lllt rx_low).
  have : left_limit a' < right_limit a'.
    by move: ccain=> /andP[] _ /andP[] A B; apply: (lt_trans A B).
  have sorted_righta : sorted >%R [seq p_y p | p <- right_pts a'].
    rewrite a'eq /=; move: right_configs.
    rewrite ?tq ?bq.
    move=> /orP[] /andP[] xcond /eqP -> /=.
      case: ifP=> // /negbT pcond /=; rewrite andbT.
      have vbt : valid_edge top (right_pt bottom) := vbt' xcond.
      rewrite -(strict_under_pvert_y vbt).
      rewrite (strict_nonAunder vbt).
      rewrite (order_edges_viz_point 
         (proj2 (andP (right_on_edge _))) vbt boxwf); last first.
        rewrite (under_onVstrict (proj2 (andP (right_on_edge _)))).
        by rewrite right_on_edge.
      rewrite andbT; apply/negP=> bont.
      case/negP: pcond.
      have := on_edge_same_point bont (pvert_on vbt) erefl => /= <-.
      by rewrite pt_eqE !eqxx.
    case: ifP=> // /negbT pcond /=; rewrite andbT.
    have vtb : valid_edge bottom (right_pt top) := vtb' xcond.
    rewrite ltNge -(under_pvert_y vtb).
    rewrite (under_onVstrict vtb) negb_or.
    have -> : right_pt top >>= bottom.
      apply/negP=> tbb.
    have := (order_edges_strict_viz_point vtb
        (proj2 (andP (right_on_edge _))) boxwf tbb).
      rewrite (strict_nonAunder (proj2 (andP (right_on_edge _)))).
      by rewrite right_on_edge.
    rewrite andbT; apply/negP=> tonb.
    case/negP: pcond.
    have := on_edge_same_point tonb (pvert_on vtb) erefl => /= <-.
    by rewrite pt_eqE !eqxx.
  have cla'ok : closed_cell_side_limit_ok a'.
    rewrite /closed_cell_side_limit_ok.
    move: a'ook=> /andP[] -> /andP[] -> /andP[] -> /andP[] -> -> /=.
    rewrite rpn0 haon laon -rxq sorted_righta !andbT.
   by  move: allrx; rewrite all_map.
  have inside_a_safe : forall p, strict_inside_closed p a' ->
    {in events_to_edges (ev :: future_events), forall g, ~ p === g} /\
    {in ev :: future_events, forall e, p != point e}.
    move=> p pin.  
    have pnevs : {in ev :: future_events, forall e, p != point e}.
      move=> e /[dup] ein2; rewrite -evsq => ein.
      apply/eqP=> pq.
      move: Main; do 4 (move=> -[] _); move=> -[] + _.
      move=> /(_ e ein2) [c1 c1_cl e1_inc1].
      have := disa' c1 c1_cl (point e).
      by rewrite e1_inc1 -pq (strict_inside_closedW pin).
    split; last by [].
    move => g /[dup] gin0 /flatten_mapP[e ein gin] pong.
    have ein2 : e \in evs by rewrite evsq.
    have [pex | pnex] := boolP (p \in [:: left_pt g; right_pt g]).
      have [e1 e1in pq] : exists2 e1, e1 \in evs & p = point e1.
        move: pex; rewrite !inE => /orP[/eqP plg | /eqP prg].
          rewrite plg; exists e; first by [].
          by apply /eqP/out_evs.
        have [e1 e1in rgq]:= closed_edges_from_eventsW cle ein2 gin.
        exists e1; first by [].
        by rewrite prg.
      by have := pnevs e1; rewrite -evsq pq eqxx => /(_ e1in).
    have ecl : edge_covered_closed g cl.
      by move: Main; do 3 (move=> [] _); move=> [] + _; apply.
    have clnoc : {in cell_edges cl &, forall g1 g2, inter_at_ext g1 g2}.
      apply: (sub_in2 _ nocs'); move: Main; do 7 (move=> [] _ //).
    have clwf : {in cl, forall c, (low c <| high c) && (low c != high c)}.
      by move=> c1 /(proj1 (proj2 Main))=> -[] _ [] -> [] ->.
    have clok : {in cl, forall c, closed_cell_side_limit_ok c}.
      by move=> c1 /(proj1 (proj2 Main))=> -[] _ [] _ [] _ [] _ [].
    have [c1 c1in [pinc1 pninc1]]:=
      edge_covered_closed_to_cell clnoc clwf clok ecl pong pnex.
    by have := disa' _ c1in p; rewrite pinc1 (strict_inside_closedW pin).
  have onside_a_safe :
    forall p, in_safe_side_left p a' || in_safe_side_right p a' ->
    {in events_to_edges (ev :: future_events), forall g, ~ p === g} /\
    {in ev :: future_events, forall e', p != point e'}.
    move=> p /orP[inlefta' | inrighta']; last first.
      have pfar : p_x p = Num.min (p_x (right_pt bottom)) (p_x (right_pt top)).
        by move: inrighta'=> /andP[] /eqP ->.
      have xev_lt : {in ev :: future_events, forall e, p_x (point e) < p_x p}.
        move=> e; rewrite -evsq pfar => ein.
        have /andP[_ /andP[/andP[_ +] /andP[_ +]]] :=
           (allP evin _ (map_f _ ein)).
        by case: (ltrP (p_x (right_pt bottom)) (p_x (right_pt top))).
      split; last first.
        move=> e /xev_lt; rewrite lt_neqAle eq_sym=> /andP[] + _.
        by apply: contraNN=> /eqP ->; rewrite eqxx.
      move=> g /flatten_mapP [e ein gin] pong.
      have ein2 : e \in evs by rewrite evsq.
      have := closed_edges_from_eventsW cle ein2 gin=> -[e1 e1in rgq].
      have e1in2 : e1 \in ev :: future_events by rewrite -evsq.
      have : p_x p <= p_x (point e1).
        by rewrite -rgq; apply: (proj2 (andP (proj2 (andP pong)))).
      by rewrite leNgt xev_lt.
    have inlefta : in_safe_side_left p a.
      by move: inlefta'; rewrite aeq a'eq.
    move: Main; do 10 (move=> -[] _); move=> -[] + _.
    by rewrite opq=> /(_ _ inlefta).
  do 6 (split; first by []).
  by [].
  Qed.

Definition well_formed_bounding_box (bottom top : edge) :=
    check_bounding_box bottom top.

Definition unsafe (evs : seq event) (p : pt) :=
  (exists2 e, e \in evs & p = point e) \/
    (exists2 g, g \in events_to_edges evs & p === g).

Definition cell_safe_part (c : cell) (p : pt) :=
  strict_inside_closed p c ||
  (in_safe_side_left p c || in_safe_side_right p c).

Lemma second_phase_safety (bottom top : edge)
  (evs : seq event) :
  well_formed_bounding_box bottom top ->
  {in bottom :: top ::
       events_to_edges evs &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- evs] ->
  sorted (@lexPtEv _) evs ->
  {in evs, forall ev, out_left_event ev} ->
  close_edges_from_events evs ->
  {in events_to_edges evs & evs, forall g e, non_inner g (point e)} ->
  {in evs, forall e, uniq (outgoing e)} ->
  {in complete_process bottom top evs, forall c,
    strict_inside_closed (cell_center c) c /\
    closed_cell_side_limit_ok c /\
    forall p, cell_safe_part c p -> ~ unsafe evs p}.
Proof.
rewrite /well_formed_bounding_box.
move=> wfbb noc' inbox_es lexev out_evs cle non_in uniq_out.
move: (wfbb); rewrite /check_bounding_box => /andP[] /andP[] box_wf boxok inc.
move: box_wf => /andP[] box_wf box_lr.
have btdif : bottom != top.
  apply/eqP=> bt.
  move: inc=> /andP[] /andP[] /underWC + + _.
  set p0 := cell_center _.
  by rewrite -[low _]/bottom -[high _]/top bt => /[swap] ->.
have [evs0 | evsn0] := eqVneq evs [::].
  rewrite evs0 /= wfbb=> c; rewrite inE=> /eqP -> {c}.
  set c := Bcell _ _ _ _.
  have cq : c = complete_last_open (start_open_cell bottom top) by [].
  move: (wfbb); rewrite /check_bounding_box => /andP[] /andP[] _.
  split; [ | split;[by apply: unbare_closed_cell_ok | ]].
    rewrite /strict_inside_closed.  
    rewrite /generic_trajectories.strict_inside_closed !R_ltb_lt in inc.
    by move: inc => /andP[] /andP[] -> -> /andP[] -> ->.
  by move=> p psafe [[e //] | [g /flatten_mapP[x //] ]].
remember (complete_process bottom top evs) as closed eqn:closedq.
move=> c cin.
have startok : open_cell_side_limit_ok (start_open_cell bottom top).
  move: boxok=> /unbare_closed_cell_ok; rewrite /open_cell_side_limit_ok.
  move=> /andP[] -> /andP[] + /andP[] + /andP[] + /andP[] + _.
  rewrite /left_limit /complete_last_open.
  by case: start_open_cell => l1 l2 le he /= -> -> -> ->.
have ext_inside : {in events_to_edges evs,
  forall g, inside_box bottom top (left_pt g) &&
    inside_box bottom top (right_pt g)}.
  move=> g /flatten_mapP [e ein gin].
  have /eqP -> := out_evs _ ein _ gin.
  rewrite (allP inbox_es _ (map_f _ ein)) /=.
  have [e' e'in rgq] := closed_edges_from_eventsW cle ein gin.
  by rewrite rgq; apply/(allP inbox_es)/map_f.
have := complete_safe evsn0 box_wf startok noc' ext_inside inbox_es lexev
  (@subset_id _ _) out_evs cle non_in uniq_out (esym closedq) cin.
move=> [ccin [cwf [lchcdif [clr [cok [insideP sideP]]]]]].
do 2 (split; first by []).
move=> p /orP[p_inside | p_safe_side].
  have [p_no_edge p_no_event] := insideP p p_inside.
  move=> [[/= e ein pone] | [/= g gin pong]].
    by have := p_no_event _ ein; rewrite pone eqxx.
  by have := p_no_edge g gin; rewrite pong.
have [p_no_edge p_no_event] := sideP _ p_safe_side.
move=> [[/= e ein pone] | [/= g gin pong]].
  by have := p_no_event _ ein; rewrite pone eqxx.
by have := p_no_edge g gin; rewrite pong.
Qed.

Lemma edges_to_events_uniq evs :
  uniq (events_to_edges evs) ->
  {in evs, forall e, uniq (outgoing e)}.
Proof.
elim: evs => [ | e evs Ih].
  by [].  
rewrite events_to_edges_cons.
move=> uniq_all.
have uniq1 : uniq (outgoing e).
  apply: subseq_uniq uniq_all.
  by apply: prefix_subseq.
move=> e1; rewrite inE => /orP[/eqP -> |]; first by [].
apply: Ih.
apply: subseq_uniq uniq_all.
by apply: suffix_subseq.
Qed.

Lemma two_phase_safety bottom top (edges : seq edge) :
  well_formed_bounding_box bottom top -> uniq edges ->
  {in bottom :: top :: edges &, forall e1 e2, inter_at_ext e1 e2} ->
  {in edges, forall g p, p === g -> inside_box bottom top p} ->
  {in edges_to_cells bottom top edges, forall c,
    strict_inside_closed (cell_center c) c /\
    closed_cell_side_limit_ok c /\
    forall p, cell_safe_part c p -> {in edges, forall g, ~ p === g}}.
Proof.
move=> wfbb ung noc inside c.
rewrite /edges_to_cells.
set evs := edges_to_events edges.
move=> cin.
have perm_evs : perm_eq (events_to_edges evs) edges.
  rewrite perm_sym.
  have := edges_to_events_no_loss edges.
  by rewrite edges_to_eventsE.
have noc' : {in [:: bottom, top & events_to_edges evs] &,
  forall e1 e2, inter_at_ext e1 e2}.
  move=> g1 g2; rewrite !inE.
  rewrite !(perm_mem perm_evs)=> g1in g2in.
  by apply: noc; rewrite !inE.
have leftin : {subset [seq left_pt g | g <- edges] <=
                 [seq left_pt g | g <- edges] ++ [seq right_pt g | g <- edges]}.
  by move=> p pin; rewrite mem_cat pin.
have rightin : {subset [seq right_pt g | g <- edges] <=
                 [seq left_pt g | g <- edges] ++ [seq right_pt g | g <- edges]}.
  by move=> p pin; rewrite mem_cat pin orbT.
have extremities_in := edges_to_events_subset leftin rightin.
have inbox_es : all (inside_box bottom top) [seq point e | e <- evs].
  move: extremities_in; rewrite edges_to_eventsE -/evs=> extremities_in.
  apply/allP=> e /extremities_in; rewrite mem_cat.
  move=> /orP[] /mapP[g gin eg]; apply: (inside _ gin); rewrite eg.
    by apply: left_on_edge.
  by apply: right_on_edge.
have lexev : sorted (@lexPtEv _) evs.
  rewrite sorted_lexPtEv_lexPt.
  rewrite /evs -edges_to_eventsE.
  by apply: sorted_edges_to_events.
have out_es : {in evs, forall ev, out_left_event ev}.
  rewrite /evs -edges_to_eventsE.
  by apply: out_left_edges_to_events.
have cle : close_edges_from_events evs.
  rewrite /evs -edges_to_eventsE.
  by apply: (edges_to_events_wf bottom top).
have nin : {in events_to_edges evs & evs, forall g e, non_inner g (point e)}.
  move=> g e.
  rewrite (perm_mem perm_evs)=> gin ein pong.
  have pinext : point e \in [seq left_pt g | g <- edges] ++
                            [seq right_pt g | g <- edges].
    by apply/extremities_in/map_f; rewrite edges_to_eventsE.
  have [g' g'in pextg'] : exists2 g', g' \in edges &
            point e = left_pt g' \/ point e = right_pt g'.
    move: pinext; rewrite mem_cat=> /orP[] /mapP[g' g'in pq]; exists g'=> //.
      by left.
    by right.
  have pong' : point e === g'.
    by move: pextg'=> [] ->; rewrite ?left_on_edge ?right_on_edge.
  have gin2 : g \in [:: bottom, top & edges].
    by rewrite !inE gin !orbT.
  have g'in2 : g' \in [:: bottom, top & edges].
    by rewrite !inE g'in !orbT.
  have [-> | /(_ _ pong pong')] := noc g g' gin2 g'in2; first by [].
  by rewrite !inE=> /orP[] /eqP; [left | right].
have uniq_out : {in evs, forall e, uniq (outgoing e)}.
  apply: edges_to_events_uniq.
  by rewrite (perm_uniq perm_evs).
have := second_phase_safety wfbb noc' inbox_es lexev out_es cle nin uniq_out cin.
move=> [ccin [cok csafe]].
split; first by [].
split; first by [].
move=> p psafe g gin pong.
move: (csafe p psafe)=> [].
right; exists g; last by [].
by rewrite (perm_mem perm_evs).
Qed.

End working_environment.
