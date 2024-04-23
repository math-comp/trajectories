From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import generic_trajectories.
Require Import math_comp_complements points_and_edges events cells.
Require Import opening_cells.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

Notation pt := (pt R).
Notation p_x := (p_x R).
Notation p_y := (p_y R).
Notation Bpt := (Bpt R).
Notation edge := (edge R).
Notation event := (event R edge).
Notation outgoing := (outgoing R edge).
Notation point := (point R edge).

Notation cell := (cell R edge).

Notation dummy_pt := (dummy_pt R 1).
Notation dummy_edge := (dummy_edge R 1 edge (@unsafe_Bedge R)).
Notation dummy_cell := (dummy_cell R 1 edge (@unsafe_Bedge _)).
Notation dummy_event := (dummy_event R 1 edge).

Definition open_cells_decomposition_contact :=
  open_cells_decomposition_contact R eq_op le +%R (fun x y => x - y) *%R 1
    edge (@left_pt R) (@right_pt R).

Definition open_cells_decomposition_rec :=
  open_cells_decomposition_rec R eq_op le +%R (fun x y => x - y) *%R 1
  edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Definition open_cells_decomposition :=
  open_cells_decomposition R eq_op le +%R (fun x y => x - y) *%R 1
  edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Notation scan_state := (scan_state R edge).
Notation sc_open1 := (sc_open1 R edge).
Notation lst_open := (lst_open R edge).
Notation sc_open2 := (sc_open2 R edge).
Notation sc_closed := (sc_closed R edge).
Notation lst_closed := (lst_closed R edge).


Definition update_closed_cell :=
  update_closed_cell R 1 edge.

Definition set_left_pts :=
  set_left_pts R.

Notation low := (low R edge).
Notation high := (high R edge).
Notation left_pts := (left_pts R edge).
Notation right_pts := (right_pts R edge).
Notation Bcell := (Bcell R edge).

Lemma high_set_left_pts (c : cell) l : high (set_left_pts c l) = high c.
Proof. by case: c. Qed.

Definition set_pts := set_pts R edge.

(* This function is to be called only when the event is in the middle
  of the last opening cell.  The point e needs to be added to the left
  points of one of the newly created open cells, but the one that receives
  the first segment of the last opening cells should keep its existing
  left points.*)
Definition update_open_cell := 
  update_open_cell R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y) 1
  edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Definition update_open_cell_top :=
  update_open_cell_top R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y) 1
  edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Notation Bscan := (Bscan _ _).

Definition simple_step :=
  simple_step R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Definition step :=
  step R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Definition scan events st : seq cell * seq cell :=
  let final_state := foldl step st events in
  (sc_open1 final_state ++ lst_open final_state :: sc_open2 final_state,
   lst_closed final_state :: sc_closed final_state).

Definition start_open_cell :=
  start_open_cell R eq_op le +%R (fun x y => x - y)
  *%R (fun x y => x / y) edge (@left_pt R) (@right_pt R).

(*
Definition start (events : seq event) (bottom : edge) (top : edge) :
  seq cell * seq cell :=
  match events with
  | nil => ([:: start_open_cell bottom top], nil)
  | ev0 :: events =>
    let (newcells, lastopen) :=
      opening_cells_aux (point ev0) (sort (@edge_below _) (outgoing ev0))
            bottom top in
      scan events (Bscan newcells lastopen nil nil
         (close_cell (point ev0) (start_open_cell bottom top))
         top (p_x (point ev0)))
  end.

*)

Lemma cell_edges_sub_high bottom top (s : seq cell) :
  cells_bottom_top bottom top s ->
  adjacent_cells s -> cell_edges s =i bottom::[seq high c | c <- s].
Proof.
case: s bottom => [ | c0 s] /= bottom; first by [].
rewrite /cells_bottom_top /cells_low_e_top=> /= /andP[] /eqP lc0 A lowhigh.
rewrite /cell_edges=> g; rewrite mem_cat.
have main : [seq high c | c <- c0 :: s] = 
            rcons [seq low c | c <- s] (high (last c0 s)).
  elim: s c0 lowhigh {lc0 A} => [ | c1 s Ih] c0 lowhigh; first by [].
  rewrite /=.
  move: lowhigh=> /= /andP[/eqP -> lowhigh]; congr (_ :: _).
  by apply: Ih.
rewrite main mem_rcons inE orbC map_cons inE -!orbA.
rewrite !(orbCA _ (g == low _)) orbb.
rewrite inE lc0; congr (_ || _).
by rewrite -map_cons main mem_rcons inE.
Qed.

Lemma not_bottom_or_top bottom top (ev : event) :
  inside_box bottom top (point ev) ->
  out_left_event ev ->
  {in outgoing ev, forall g, g \notin [:: bottom; top]}.
Proof.
move=> inbox oute g gin; apply/negP=> abs.
have lgq : left_pt g = point ev by apply/eqP/oute.
move: inbox=> /andP[]; rewrite -lgq; move: abs; rewrite !inE=> /orP[] /eqP ->.
  by rewrite left_pt_below.
by rewrite (negbTE (left_pt_above _)) !andbF.
Qed.

Section proof_environment.
Variables bottom top : edge.

Notation extra_bot := (extra_bot bottom).
Notation close_alive_edges := (close_alive_edges bottom top).
Notation cells_bottom_top := (cells_bottom_top bottom top).
Notation inside_box := (inside_box bottom top).
Notation open_cell_side_limit_ok := (@open_cell_side_limit_ok R).
Notation seq_low_high_shift := (@seq_low_high_shift R).
Notation cover_left_of := (@cover_left_of _ bottom top).

Section open_cells_decomposition.

Lemma open_cells_decomposition_contact_none open_cells p :
  open_cells_decomposition_contact open_cells p = None ->
  open_cells != [::] -> ~~contains_point p (head dummy_cell open_cells).
Proof.
rewrite /contains_point.
case: open_cells => [// | /= c0 q].
by case : ifP=> ? //;
  case: (open_cells_decomposition_contact q p)=> // [] [] [].
Qed.

Lemma open_cells_decomposition_contact_main_properties open_cells p cc c' lc:
  open_cells_decomposition_contact open_cells p = Some (cc, lc, c') ->
  cc ++ c' :: lc = open_cells /\
  contains_point p c' /\
  {in cc, forall c, contains_point p c} /\
  (lc != [::] -> ~~ contains_point p (head c' lc)).
Proof.
elim: open_cells cc c' lc => [ // | c q Ih] cc c' lc.
rewrite /=; case: ifP => [ctpcc | nctpcc] //.
case occ_eq : (open_cells_decomposition_contact _ _)
       (@open_cells_decomposition_contact_none q p)
    => [[[cc1 lc1] c1] | ] nonecase [] <- <- <-; last first.
  split;[ by [] | split; [by [] | split; [by [] | ] ]].
  by case: (q) nonecase => [// | c2 q2] ; apply.
have [eqls [ctc1 [allct nctlc1]]] := Ih _ _  _ occ_eq.
split; first by rewrite /=; congr (_ :: _).
split; first by [].
split; last by [].
by move=> w; rewrite inE => /orP[/eqP -> // | ]; apply: allct.
Qed.

Lemma decomposition_main_properties open_cells p fc cc lcc lc le he:
  open_cells_decomposition open_cells p = (fc, cc, lcc, lc, le, he) ->
  (exists2 w, w \in open_cells & contains_point' p w) ->
  open_cells = fc ++ cc ++ lcc :: lc /\
  contains_point p lcc /\
  {in cc, forall c, contains_point p c} /\
  {in fc, forall c, ~~contains_point p c} /\
  (lc != [::] -> ~~ contains_point p (head lcc lc)) /\
  he = high lcc /\
  le = low (head lcc cc) /\
  le \in cell_edges open_cells /\
  he \in cell_edges open_cells.
Proof.
rewrite /open_cells_decomposition/generic_trajectories.open_cells_decomposition.
elim : open_cells fc cc lcc lc le he => [ | c q Ih] fc cc lcc lc le he.
  by rewrite /= => _ [] w.
rewrite /=; case: ifP=> ctc.
  rewrite -[generic_trajectories.open_cells_decomposition_contact _ _ _ _ _
              _ _ _ _ _ _ _]/(open_cells_decomposition_contact q p).
  case ocdc_eq : (open_cells_decomposition_contact q p) => [[[cc0 lc0] c0]|].
    move=> [] <- <- <- <- <- <- _.
    have [qeq [ctc0 [allct nct]] ]:=
     open_cells_decomposition_contact_main_properties ocdc_eq.
    split; first by rewrite /= qeq.
    split; first by [].
    split; first by move=> c1 /orP[/eqP -> | ] //; apply: allct.
    repeat (split; first by []).
    by rewrite -qeq !mem_cat !map_f ?orbT // !(mem_cat, inE) eqxx ?orbT.
  move=> [] <- <- <- <- <- <- _.
  repeat (split; first by []).
  split.
    by move: (open_cells_decomposition_contact_none ocdc_eq); case: (q).
  split; first by [].
  split; first by [].
  by rewrite !mem_cat !map_f ?orbT // inE eqxx.
rewrite -[generic_trajectories.open_cells_decomposition_rec _ _ _ _ _
              _ _ _ _ _ _ _ _]/(open_cells_decomposition_rec q p).
case ocdr_eq : (open_cells_decomposition_rec q p) => [[[fc1 cc1] lcc1] lc1].
move=> [] <- <- <- <- <- <- [] w win ctw.
have ex2 :exists2 w, w \in q & contains_point' p w.
  exists w; last by [].
  move: win ctw; rewrite inE => /orP[/eqP -> | //].
  by move=> /contains_point'W; rewrite /contains_point ctc.
have := Ih fc1 cc1 lcc1 lc1 (low (head lcc1 cc1)) (high lcc1).
rewrite /open_cells_decomposition_rec in ocdr_eq.
rewrite ocdr_eq => /(_ erefl ex2).
move=> [qeq [ctplcc1 [allct [allnct [nctlc [leeq heq]]]]]].
split; first by rewrite /= qeq.
split; first by [].
split; first by [].
split.
  move=> c0; rewrite inE=> /orP[/eqP -> // | c0in]; last first.
    by rewrite ?allnct.
  by rewrite /contains_point ctc.
repeat (split; first by []).
by rewrite qeq !mem_cat !map_f ?orbT //; case:(cc1) => [| a b] /=; subset_tac.
Qed.

Lemma decomposition_connect_properties open_cells p 
  first_cells contact last_contact last_cells low_f high_f:
s_right_form open_cells ->
seq_valid open_cells p ->
adjacent_cells open_cells ->
cells_bottom_top open_cells ->
between_edges bottom top p ->
open_cells_decomposition open_cells p  =
  (first_cells, contact, last_contact, last_cells, low_f, high_f) ->
[/\ p >>> low_f, p <<< high_f, valid_edge low_f p, valid_edge high_f p &
forall c, (c \in first_cells) || (c \in last_cells) -> ~ contains_point p c].
Proof.
move=> rfo sval adj cbtom inbox_p oe.
have [w win ctw'] := exists_cell cbtom adj inbox_p.
have [ocd [ctpl [allct [allnct [nctlc [-> [-> _]]]]]]]:=
   decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
have [A B C D E] := 
  connect_properties cbtom adj rfo sval inbox_p ocd allnct allct ctpl nctlc.
by split => // c cin; apply/negP/E.
Qed.

Lemma decomposition_not_end open_cells e :
forall first_cells contact last_contact last_cells low_f high_f,
s_right_form open_cells ->
seq_valid open_cells (point e) ->
adjacent_cells open_cells ->
cells_bottom_top open_cells ->
between_edges bottom top (point e) ->
open_cells_decomposition open_cells (point e) =
 (first_cells, contact, last_contact, last_cells, low_f, high_f) ->
forall c, (c \in first_cells) || (c \in last_cells) ->
 ( ~ event_close_edge (low c) e) /\ ( ~ event_close_edge (high c) e).
Proof.
move=> fc cc lcc lc low_f high_f rfo sval adj cbtom inbox_p oe c cold.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq leq]]]]]]:=
   decomposition_main_properties oe (exists_cell cbtom adj inbox_p).
by apply: (fclc_not_end_aux cbtom adj _ sval inbox_p ocd _ lcc_ctn flcnct).
Qed.

Lemma open_cells_decomposition_point_on open p fc cc lcc lc le he c:
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  seq_valid open p ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  c \in cc -> p === high c.
Proof.

move=> cbtom adj inbox_p sval oe ccc.
have [ocd [lcc_ctn [allctn _]]]:= decomposition_main_properties oe
           (exists_cell cbtom adj inbox_p).
by have := in_cc_on_high adj sval ocd allctn lcc_ctn ccc.
Qed.

Lemma last_first_cells_high open p fc cc lcc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  last bottom [seq high i | i <- fc] = le.
Proof.
move=> cbtom adj inbox_p oe.
have exi := exists_cell cbtom adj inbox_p.
have [ocd [_ [_ [_ [_ [heq [leq _]]]]]]] :=
   decomposition_main_properties oe exi.
suff -> : last bottom [seq high i | i <- fc] = low (head lcc cc).
  by rewrite leq.
move: cbtom=> /andP[] /andP[] _ /eqP + _.
move : adj; rewrite ocd.
  elim/last_ind: {-1}(fc) (erefl fc) => [//= | fc' c1 _].
    by case: (cc) => [ | c2 cc'].
rewrite -cats1 -catA=> fceq /adjacent_catW /= [] _ + _.
rewrite cats1 map_rcons last_rcons.
by case: (cc) => [ | c2 cc'] /andP[] + _; rewrite /adj_rel /= => /eqP.
Qed.

Lemma head_last_cells_low open p fc cc lcc lc le he :
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  head top [seq low i | i <- lc] = he.
Proof.
move=> cbtom adj inbox_p oe.
have exi := exists_cell cbtom adj inbox_p.
have [ocd [_ [_ [_ [_ [-> _]]]]]] :=
   decomposition_main_properties oe exi.
move: cbtom=> /andP[] _ /eqP.
move: adj; rewrite ocd => /adjacent_catW [] _ /adjacent_catW [] _ /=.
  rewrite !last_cat /=.
case : (lc) => [ | c2 lc'] //=.
by move=> /andP[] /eqP ->.
Qed.

(* Temporary trial, but this lemma might be better placed in
  points_and_edges. *)
Lemma decomposition_above_high_fc p open fc cc lcc lc le he c1:
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  s_right_form open ->
  seq_valid open p ->
  c1 \in fc -> p >>> high c1.
Proof.
move=> oe cbtom adj inbox_e rfo sval c1in.
have exi := exists_cell cbtom adj inbox_e.
have [ocd [_ [_ [_ [_ [heq leq]]]]]] := decomposition_main_properties oe exi.
have [pal puh vl vp _]:=
  decomposition_connect_properties rfo sval adj cbtom inbox_e oe.
rewrite under_pvert_y; last first.
  apply: (seq_valid_high sval).
  by rewrite map_f //; rewrite ocd; subset_tac.
rewrite -ltNge.
have : pvert_y p le < p_y p.
  by move: pal; rewrite under_pvert_y // -ltNge.
apply: le_lt_trans.
move: c1in.
have [fceq |[fc' [lfc fceq]]]: fc = nil \/ exists fc' lfc, fc = rcons fc' lfc.
    by elim/last_ind : (fc) => [ | fc' lfc _];[left | right; exists fc', lfc].
  by rewrite fceq.
have := last_first_cells_high cbtom adj inbox_e oe.
rewrite fceq map_rcons last_rcons => <-.
rewrite mem_rcons inE => /orP[/eqP c1lfc | c1o]; first  by rewrite c1lfc.
have [a [b pab]] := mem_seq_split c1o.
move: fceq; rewrite pab -cats1 -catA /= => fceq.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (valid_edge (R := _) ^~ p)
    [seq high i | i <- c1 :: b ++ [:: lfc]].
  apply/allP; apply: (sub_in1 _ (seq_valid_high sval)); apply: sub_map.
  by rewrite ocd fceq; subset_tac.
have req2 : path (@edge_below R) (high c1) [seq high i | i <- b ++ [:: lfc]].
  have := seq_edge_below' adj rfo.
  rewrite ocd (_ : fc = rcons a c1 ++ rcons b lfc); last first.
     by move: fceq; rewrite -!cats1 !catA /= -!catA /=.
  rewrite -!catA [X in path _ _ X]map_cat cat_path=> /andP[] _.
  rewrite !map_rcons last_rcons map_cat cat_path => /andP[] + _.
  by rewrite -cats1.
have : path (<=%R) (pvert_y p (high c1))
  [seq pvert_y p (high i) | i <- b ++ [:: lfc]].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y p (high lfc))); apply.
by rewrite (map_f (fun c => pvert_y p (high c))) //; subset_tac.
Qed.

Lemma decomposition_under_low_lc p open fc cc lcc lc le he c1:
  open_cells_decomposition open p = (fc, cc, lcc, lc, le, he) ->
  cells_bottom_top open ->
  adjacent_cells open ->
  between_edges bottom top p ->
  s_right_form open ->
  seq_valid open p ->
  c1 \in lc -> p <<< low c1.
Proof.
move=> oe cbtom adj inbox_e rfo sval c1in.
have exi := exists_cell cbtom adj inbox_e.
have [ocd _] := decomposition_main_properties oe exi.
rewrite strict_under_pvert_y; last first.
  by apply/(seq_valid_low sval)/map_f; rewrite ocd; subset_tac.
have [pal puh vl vp _]:=
  decomposition_connect_properties rfo sval adj cbtom inbox_e oe.
have puhe : p_y p < pvert_y p he.
  by move: puh; rewrite strict_under_pvert_y.
apply: (lt_le_trans puhe).
move: c1in; case lceq : lc => [ // | flc lc'] c1in.
have := head_last_cells_low cbtom adj inbox_e oe.
rewrite lceq /= => <-.
move: c1in; rewrite inE => /orP[/eqP c1flc | c1o]; first by rewrite c1flc.
have [a [b Pab]] := mem_seq_split c1o.
(* requirement for path_edge_below_pvert_y *)
have req1 : all (@valid_edge R ^~ p)
  [seq low i | i <- flc :: a ++ c1 :: b].
  apply/allP; apply: (sub_in1 _ (seq_valid_low sval)); apply: sub_map.
  by rewrite ocd lceq Pab; subset_tac.
have req2 : path (@edge_below R) (low flc) [seq low i | i <- a ++ c1 :: b].
  have := seq_edge_below' adj rfo.
  have [on0 headq] : open != [::] /\ low (head dummy_cell open) = bottom.
    by move: cbtom=> /andP[] /andP[] + /eqP + _.
  have headq' : head dummy_edge [seq low i | i <- open] = bottom.
      by move: on0 headq; case: (open)=> [ // | ? ?] /=.
  rewrite headq' => pathoh.
  have : path (@edge_below R) bottom (bottom :: [seq high i | i <- open]).
      by rewrite /= edge_below_refl.
  have  := seq_low_high_shift on0 adj; rewrite headq => <-.
  rewrite -cats1 cat_path => /andP[] + _.
  rewrite ocd lceq Pab.
  by rewrite 2!map_cat 2!cat_path /= => /andP[] _ /andP[] _ /andP[] _ /andP[].
have : path (<=%R) (pvert_y p (low flc))
  [seq pvert_y p (low i) | i <- a ++ c1 :: b].
  by have := path_edge_below_pvert_y req1 req2; rewrite -map_comp.
rewrite le_path_sortedE => /andP[] /allP + _.
move=> /(_ (pvert_y p (low c1))); apply.
by rewrite (map_f (fun c => pvert_y p (low c))); subset_tac.
Qed.

End open_cells_decomposition.

Lemma open_cells_decomposition_cat f l p :
   adjacent_cells (f ++ l) ->
   s_right_form (f ++ l) ->
   seq_valid (f ++ l) p ->
   (exists2 c, c \in l & contains_point' p c) ->
   p >>> low (head dummy_cell l) ->
   let '(fc', cc, lcc, lc, le, he) :=
     open_cells_decomposition l p in
   open_cells_decomposition (f ++ l) p =
     (f ++ fc', cc, lcc, lc, le, he).
Proof.
move=> + + + exi pal.
elim: f => [ | c0 f Ih].
  move=> adj rfo sval.
 by case: (open_cells_decomposition l p) => [[[[[fc cc] lcc] lc] le] he].
rewrite /= => adj /andP[] lbh0 rfo /andP[] /andP[] vlc0 vhc0 sval.
case ocal_eq : (open_cells_decomposition l p) =>
  [[[[[fc' cc'] lcc'] lc'] le'] he'].
case oca_eq : (open_cells_decomposition _ _) =>
  [[[[[fc1 cc1] lcc1] lc1] le1] he1].
have exi0 : exists2 c, c \in c0 :: f ++ l & contains_point' p c.
  by case: exi => c cin A; exists c=> //; subset_tac.
have := decomposition_main_properties oca_eq exi0 =>
  -[ocd [lcc_ctn [allct [allnct [flnct [heq [leq [lein hein]]]]]]]].
have := decomposition_main_properties ocal_eq exi =>
  -[ocd' [lcc_ctn' [allct' [allnct' [flnct' [heq' [leq' [lein' hein']]]]]]]].
have svalf : seq_valid f p.
  by apply/allP=> x xin; apply: (allP sval); subset_tac.
have rfof : s_right_form f.
  by apply/allP=> x xin; apply: (allP rfo); subset_tac.
have adjf : adjacent_cells f.
  by move: adj; rewrite cat_path=> /andP[] /path_sorted.
have hfq : high (last c0 f) = low (head dummy_cell l).
  case: (l) adj exi => [ | c1 l']; first by move => _ [].
  by rewrite cat_path /==> /andP[] _ /andP[] /eqP.
move: oca_eq; rewrite /open_cells_decomposition/generic_trajectories.open_cells_decomposition /=.
case: ifP=> [c0ctn | c0nctn].
  move: c0ctn; rewrite /generic_trajectories.contains_point -[X in _ && X]negbK.
  have [/eqP f0 | fn0] := boolP (f == nil).
    by move: hfq; rewrite f0 /= => ->; rewrite pal andbF.
  have := above_all_cells svalf adjf rfof.
  have -> : high (last dummy_cell f) = high (last c0 f).
    by case: (f) fn0.
  rewrite hfq pal=> /(_ isT) [] palf _.
  have -> : high c0 = low (head dummy_cell f).
    by move: adj fn0; case: (f) => [// | ? ?] /= /andP[] /eqP.
  by rewrite palf andbF.
move: ocal_eq; rewrite /open_cells_decomposition/generic_trajectories.open_cells_decomposition.
rewrite -/(open_cells_decomposition_rec _ _).
case ocal_eq: (open_cells_decomposition_rec _ _) =>
  [[[fc2 cc2] lcc2] lc2] [] <- <- <- <- <- <-.
have adj' : adjacent_cells (f ++ l).
  by move: adj=> /path_sorted.
have := Ih adj' rfo sval; rewrite /open_cells_decomposition.
rewrite /generic_trajectories.open_cells_decomposition.
rewrite /open_cells_decomposition_rec in ocal_eq. rewrite ocal_eq.
rewrite -/(open_cells_decomposition_rec _ _).
case: (open_cells_decomposition_rec (f ++ l) p) => [[[fc4 cc4] lcc4] lc4].
by move=> -[] -> -> -> -> _ _ [] <- <- <- <- <- <-.
Qed.

Lemma open_cells_decomposition_cat' f l p :
  adjacent_cells (f ++ l) ->
  s_right_form (f ++ l) ->
  seq_valid (f ++ l) p ->
  (exists2 c, c \in (f ++ l) & contains_point' p c) ->
  f != nil ->
  p >>> high (last dummy_cell f) ->
   let '(fc', cc, lcc, lc, le, he) :=
     open_cells_decomposition l p in
   open_cells_decomposition (f ++ l) p =
     (f ++ fc', cc, lcc, lc, le, he).
Proof.
move=> adj rfo sval [w win wctn] fnnil paf.
have adjf : adjacent_cells f by move: adj=> /adjacent_catW[].
have rfof : s_right_form f.
  by apply/allP=> x xin; apply: (allP rfo); subset_tac.
have svalf : seq_valid f p.
  by apply/allP=> x xin; apply: (allP sval); subset_tac.
have winl : w \in l.
  have [_ abaf] := above_all_cells svalf adjf rfof paf.
  have wnf : w \notin f.
    apply/negP=> abs.
    by move: wctn; rewrite /contains_point' -[X in _ && X]negbK abaf ?andbF //.
  by move: win; rewrite mem_cat (negbTE wnf).
have exi' : exists2 c, c \in l & contains_point' p c by exists w.
have hfq : high (last dummy_cell f) = low (head dummy_cell l).
  move: adj fnnil.
  case:(f) => [ // | c0 f']; rewrite /= cat_path=> /andP[] _ + _.
  by move: winl; case: (l) => [ // | c1 l'] _ /= /andP[] /eqP.
by apply: open_cells_decomposition_cat; rewrite // -hfq.
Qed.

Lemma open_cells_decomposition_single f l c p :
  adjacent_cells (f ++ c :: l) ->
  s_right_form (f ++ c :: l) ->
  seq_valid (f ++ c :: l) p ->
  p >>> low c ->
  p <<< high c ->
  open_cells_decomposition (f ++ c :: l) p =
    (f, nil, c, l, low c, high c).
Proof.
move=> adj srf sv pal puh.
have exi : exists2 c', c' \in (c :: l) & contains_point' p c'.
  by exists c;[ rewrite inE eqxx // | rewrite /contains_point' pal underW].
have := open_cells_decomposition_cat adj srf sv exi pal.
case ocl : (open_cells_decomposition (c :: l) p) =>
        [[[[[fc cc] lcc] lc] le] he].
move: ocl; rewrite /open_cells_decomposition /=.
rewrite /generic_trajectories.open_cells_decomposition /=.
rewrite -/(contains_point _ _).
have -> : contains_point p c.
  by rewrite contains_pointE underWC // underW.
case lq : l => [ | c1 l'] /=.
  by move=> [] <- <- <- <- <- <-; rewrite cats0.
rewrite -/(contains_point _ _).
suff -> : contains_point p c1 = false.
  by move=> [] <- <- <- <- <- <-; rewrite cats0.
move: adj=> /adjacent_catW[] _; rewrite lq /= => /andP[] /eqP lc1q  _.
by rewrite contains_pointE -lc1q puh.
Qed.

Section step.


Variable e : event.
Variable fop : seq cell.
Variable lsto : cell.
Variable lop : seq cell.
Variable cls : seq cell.
Variable lstc :  cell.
Variable lsthe : edge.
Variable lstx : R.
Variable future_events : seq event.
Variable p : pt.

Let open := (fop ++ lsto :: lop).

(* lsto is only guaranteed to be the highest of the last created cells. *)
(* It might be the case that the next event is in the left side of this *)
(* cell *)
#[clearbody]
Let lstoin : lsto \in open.
Proof.  by rewrite /open; subset_tac. Defined.


Hypothesis inbox_all_edges :
  all (fun g => (g \in [:: bottom; top]) ||
        (inside_box (left_pt g) && inside_box (right_pt g)))
      (cell_edges open).
Hypothesis inbox_all_events :
  all inside_box [seq point x | x <- (e :: future_events)].

#[clearbody]
Let inbox_e : inside_box (point e).
Proof. by have /andP[] := inbox_all_events. Defined.

#[clearbody]
Let inbox_es : all inside_box [seq point x | x <- future_events].
Proof. by have /andP[] := inbox_all_events. Defined.

Hypothesis oute : out_left_event e.
Hypothesis rfo : s_right_form open.
Hypothesis cbtom : cells_bottom_top open.
Hypothesis adj : adjacent_cells open.
Hypothesis sval : seq_valid open (point e).
Hypothesis cle : close_edges_from_events (e :: future_events).
Hypothesis clae : close_alive_edges open (e :: future_events).
Hypothesis lstheq : lsthe = high lsto.
Hypothesis lstheqc : lsthe = high lstc.
Hypothesis lstxq : lstx = left_limit lsto.
Hypothesis abovelstle :
  p_x (point e) = lstx -> (point e) >>> low lsto.
Hypothesis elexp : lexePt (point e) p.
Hypothesis plexfut : {in future_events, forall e', lexePt p (point e')}.
Hypothesis inbox_p : inside_box p.
Hypothesis noc : {in all_edges open (e :: future_events) &, no_crossing R}.
Hypothesis sort_evs : path (@lexPtEv _) e future_events.
Hypothesis pwo : pairwise (@edge_below _) (bottom :: [seq high c | c <- open]).
Hypothesis btom_left_corners :
  {in open, forall c, lexPt (bottom_left_corner c) (point e)}.
Hypothesis open_side_limit : all open_cell_side_limit_ok open.
Hypothesis close_side_limit : all (@closed_cell_side_limit_ok _)
   (rcons cls lstc).
Hypothesis lex_left_limit :
  all (fun x => lexPt x (point e)) (behead (left_pts lsto)).
Hypothesis disjoint_open_closed :
  {in open & rcons cls lstc, disjoint_open_closed_cells R}.
Hypothesis disjoint_closed : {in rcons cls lstc &, disjoint_closed_cells R}.
Hypothesis closed_right_limit :
 {in rcons cls lstc, forall c, right_limit c <= p_x (point e)}.
Hypothesis uniq_closed : uniq (rcons cls lstc).
Hypothesis non_empty_closed :
  {in rcons cls lstc, forall c, exists p, inside_closed' p c}.
Hypothesis non_empty_right : right_pts lstc != [::] :> seq pt.
Hypothesis uniq_out : uniq (outgoing e).
Hypothesis high_inj : {in open &, injective high}.
Hypothesis btm_left : bottom_left_cells_lex open (point e).
Hypothesis uniq_open : uniq open.
Hypothesis open_non_inner :
    {in open, forall c, non_inner (high c) (point e)}.
Hypothesis lex_open_edges :
   {in [seq high c | c <- open], forall g, lexPt (left_pt g) (point e) &&
          lexePt (point e) (right_pt g)}.
Hypothesis left_limit_has_right_limit :
  {in open, forall c p, inside_box p -> left_limit c = p_x p ->
    contains_point' p c -> has (inside_closed' p) (rcons cls lstc)}.
Hypothesis cover_left_of_e : cover_left_of (point e) open (rcons cls lstc).

(* Thanks to the disoc lemma, we only need to prove that the high edges
  of all open cells satisfy the pairwise property for edge_below to
  obtain disjointness of cells. *)

Lemma disoc_i i j s : (i < j < size s)%N ->
  adjacent_cells s ->
  pairwise (@edge_below _) [seq high c | c <- s] ->
  all open_cell_side_limit_ok s ->
  o_disjoint_e (nth dummy_cell s i) (nth dummy_cell s j).
Proof.
move=> + adjs pws open_side_limit_s.
move=> /andP[] iltj jlts.
have ilts : (i < size s)%N by apply: ltn_trans jlts.
set x := nth dummy_cell s i.
set y := nth dummy_cell s j.
have iin : x \in s by apply: mem_nth.
have jin : y \in s by apply: mem_nth.
have xok : open_cell_side_limit_ok x by apply: (allP open_side_limit_s).
have yok : open_cell_side_limit_ok y by apply: (allP open_side_limit_s).
right=> q; apply/negP=> /andP[].
move=> /andP[] /[dup] inx /(inside_open_cell_valid xok) /andP[] _ vhx _.
move=> /andP[] /[dup] iny /(inside_open_cell_valid yok) /andP[] vly _.
move=> /andP[] qay _.
move: inx=> /andP[] /andP[] _ quhx _.
case/negP:qay.
move: iltj; rewrite leq_eqVlt=> /orP[/eqP/esym jq | ].
  move: adjs.
  rewrite -(cat_take_drop j.+1 s)=> /adjacent_catW[] + _.
  rewrite (take_nth dummy_cell jlts) -/y jq (take_nth dummy_cell ilts) -/x.
  rewrite -2!cats1 -catA /= =>/adjacent_catW[] _ /=.
  by rewrite andbT=> /eqP <-.
move=> i1ltj.
set j' := j.-1.
have jj : j = j'.+1 by rewrite (ltn_predK i1ltj).
have j'lts : (j' < size s)%N.
  by apply: ltn_trans jlts; rewrite jj.
have iltj' : (i < j')%N by rewrite -ltnS -jj.
move: adjs.
rewrite -(cat_take_drop j.+1 s)=> /adjacent_catW[] + _.
rewrite (take_nth dummy_cell jlts) -/y jj (take_nth dummy_cell j'lts).
rewrite -2!cats1 -catA /= =>/adjacent_catW[] _ /= /andP[] /eqP lyq _.
apply: (order_edges_viz_point' vhx) => //.
rewrite -lyq.
move: pws => /(pairwiseP dummy_edge) /(_ i j') /=; rewrite size_map 2!inE.
move=> /(_ ilts j'lts iltj').
by rewrite -[dummy_edge]/(high dummy_cell) !(nth_map dummy_cell).
Qed.

Lemma disoc s:
  adjacent_cells s ->
  pairwise (@edge_below _) [seq high c | c <- s] ->
  all open_cell_side_limit_ok s ->
 {in s &, disjoint_open_cells R}.
Proof.
move=> adjs pws sok.
move=> x y xin yin.
set i := find (pred1 x) s.
set j := find (pred1 y) s.
case : (leqP i j) => [ | jlti]; last first.
  have ilts : (i < size s)%N by rewrite -has_find has_pred1.
  have jint : (j < i < size s)%N by rewrite jlti ilts.
  move: xin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
  move: yin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
  by apply/o_disjoint_eC/disoc_i.
rewrite leq_eqVlt=> /orP[/eqP ij | iltj].
  move: xin; rewrite -has_pred1=> /(nth_find dummy_cell) /= /eqP.
  rewrite -/i ij /j.
  move: yin; rewrite -has_pred1=> /(nth_find dummy_cell) /= /eqP -> ->.
  by left.
have jlto : (j < size s)%N by rewrite -has_find has_pred1.
have jint : (i < j < size s)%N by rewrite iltj jlto.
move: xin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
move: yin; rewrite -has_pred1=> /(nth_find dummy_cell) => /eqP <-.
by apply/disoc_i.
Qed.

#[clearbody]
Let bet_e : between_edges bottom top (point e).
Proof. by apply inside_box_between. Defined.

#[clearbody]
Let exi : exists2 c, c \in open & contains_point' (point e) c.
Proof. by apply: (exists_cell cbtom adj bet_e). Defined.

Lemma close_cell_ok c :
  contains_point (point e) c ->
  valid_edge (low c) (point e) -> valid_edge (high c) (point e) ->
  open_cell_side_limit_ok c ->
  closed_cell_side_limit_ok (close_cell (point e) c).
Proof.
move=> ctp vl vh.
rewrite /open_cell_side_limit_ok/closed_cell_side_limit_ok.
rewrite /close_cell /=; have /exists_point_valid [p1 /[dup] vip1 ->] := vl.
have /exists_point_valid [p2 /[dup] vip2 -> /=] := vh.
move=> /andP[] -> /andP[]-> /andP[]-> /andP[] -> -> /=.
have [o1 /esym/eqP x1]:=intersection_on_edge vip1.
have [o2 /eqP x2]:=intersection_on_edge vip2.
rewrite -?(eq_sym (point e)).
(* TODO : this line performs a lot of complicated things, but they mostly
   failed at porting time. *)
case:ifP (o1) (o2) =>[/eqP q1 |enp1];case:ifP=>[/eqP q2 |enp2];
  rewrite ?q1 ?q2;
  rewrite -?q1 -?q2 /= ?eqxx ?x2 ?x1 /= => -> -> //; rewrite /= ?andbT.
- move: x1 x2 ctp=> /eqP/esym x1 /eqP x2 /andP[] _ eh.
  have := (under_edge_strict_lower_y x2 (negbT enp2) eh o2).
  rewrite q1=> ->; rewrite andbT.
  by rewrite /right_limit /= x2 eqxx.
- move: x1 x2 ctp=> /eqP/esym x1 /eqP x2 /andP[] el _.
  have := (above_edge_strict_higher_y x1 _ el).
  by rewrite eq_sym (negbT enp1)=> /(_ isT); apply.
move: x1 x2 ctp=> /eqP/esym x1 /eqP x2 /andP[] el eh.
rewrite (above_edge_strict_higher_y x1 _ el) //; last first.
  by rewrite eq_sym enp1.
rewrite  (under_edge_strict_lower_y x2 (negbT enp2) eh) //.
by rewrite -x1 x2 eqxx.
Qed.

Lemma closing_cells_side_limit' cc :
  s_right_form cc ->
  seq_valid cc (point e) ->
  adjacent_cells cc ->
  all open_cell_side_limit_ok cc ->
  all (contains_point (point e)) cc ->
  point e >>> low (head dummy_cell cc) ->
  point e <<< high (last dummy_cell cc) ->
  all (@closed_cell_side_limit_ok _) (closing_cells (point e) cc).
Proof.
move=> rfc valc adjc oks ctps abovelow belowhigh.
rewrite /closing_cells.
rewrite all_map.
apply/allP=> //= c cin.
have vlc: valid_edge (low c) (point e) by have:= (allP valc c cin) => /andP[].
have vhc : valid_edge (high c) (point e)
   by have := (allP valc c cin) => /andP[].
apply: close_cell_ok=> //.
  by apply: (allP ctps).
by apply: (allP oks).
Qed.

Lemma close'_subset_contact q c :
  valid_cell c (point e) ->
  closed_cell_side_limit_ok (close_cell (point e) c) ->
  inside_closed' q (close_cell (point e) c) -> inside_open' q c.
Proof.
move=>[] vl vh.
move=>/closed_right_imp_open.
rewrite inside_open'E // inside_closed'E /close_cell.
have [p1 vip1] := exists_point_valid vl.
have [p2 vip2] := exists_point_valid vh.
rewrite vip1 vip2 /= => cok /andP[] -> /andP[] -> /andP[] -> rlim /=.
by apply: (le_trans rlim cok).
Qed.

Lemma close_cell_right_limit c :
  valid_cell c (point e) ->
  right_limit (close_cell (point e) c) = p_x (point e).
Proof.
move=> [vl vh].
rewrite /close_cell; rewrite !pvertE // /right_limit /=.
by case: ifP=> cnd1 //; case: ifP=> cnd2.
Qed.

Definition state_open_seq (s : scan_state) :=
  sc_open1 s ++ lst_open s :: sc_open2 s.

Definition inv1_seq (s : seq cell) :=
  close_alive_edges s future_events /\
  (future_events = [::] \/
    seq_valid s (point (head dummy_event future_events))) /\
  adjacent_cells s /\ cells_bottom_top s /\ s_right_form s.

Definition invariant1 (s : scan_state) :=
  inv1_seq (state_open_seq s).

Let val_between g (h : valid_edge g (point e)) := 
  valid_between_events elexp plexfut h inbox_p.

#[clearbody]
Let subo : {subset outgoing e <= all_edges open (e :: future_events)}.
Proof. by rewrite /all_edges; subset_tac. Defined.

#[clearbody]
Let subo' : {subset sort (@edge_below _) (outgoing e)
                 <= all_edges open (e :: future_events)}.
Proof.
by move=> x; rewrite mem_sort=> xo; apply: subo.
Defined.

#[clearbody]
Let oute' : {in sort (@edge_below _) (outgoing e),
    forall g, left_pt g == (point e)}.
Proof. by move=> x; rewrite mem_sort; apply: oute. Defined.

(* This was a temporary movement section for objects
  transferred to the opening_cells section, but now it seems
  opening_cells_pairwise has to stay in this part of the world. *)

Lemma opening_cells_pairwise le he :
   point e >>> le ->
   point e <<< he ->
   le \in all_edges open (e :: future_events) ->
   he \in all_edges open (e :: future_events) ->
   valid_edge le (point e) ->
   valid_edge he (point e) ->
   pairwise (@edge_below _)
         [seq high x | x <- (opening_cells (point e) (outgoing e) le he)].
Proof.
move=> pal puh lein hein vle vhe.
apply: opening_cells_pairwise'=> //.
have sub : {subset [:: le, he & outgoing e] <=
               all_edges open (e :: future_events)}.
  move=> g1; rewrite !inE=> /orP[/eqP -> | /orP[/eqP -> | gin]] //.
  by rewrite mem_cat events_to_edges_cons !mem_cat gin !orbT.
by move=> g1 g2 /sub g1in /sub g2in; apply: noc.
Qed.

(* end of temporary moving area. *)
Lemma invariant1_default_case :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  inv1_seq ((fc ++ nos) ++ lno :: lc).
Proof.
case oe : (open_cells_decomposition open (point e)) =>
 [[[[[fc cc] lcc] lc] le] he].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe ncont] :=
    decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq:(opening_cells_aux _ _ _ _) => [nos nlsto].
rewrite /invariant1 /state_open_seq /=.
have dec_not_end :=
    decomposition_not_end rfo sval adj cbtom bet_e oe.
have close_fc : close_alive_edges fc future_events.
  suff/head_not_end : close_alive_edges fc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin.
  by apply/allP=> c0 cin; apply: (allP clae); rewrite ocd; subset_tac.
have close_lc : close_alive_edges lc future_events.
  suff/head_not_end : close_alive_edges lc (e :: future_events).
    by apply=> c0 cin; apply: dec_not_end; rewrite cin orbT.
  by apply/allP=> c0 cin; apply: (allP clae); rewrite ocd; subset_tac.
have endle : end_edge_ext bottom top le future_events.
  suff  : end_edge_ext bottom top le (e :: future_events).
    rewrite /end_edge_ext; move=> /orP[-> // | ] /= /orP[ | ->]; last first.
      by rewrite orbT.
    by move: pal=> /[swap] /eqP <-; rewrite right_pt_below.
  have := (proj1 (andP (allP clae (head lcc cc) _))); rewrite leq; apply.
  by rewrite ocd; subset_tac.
have endhe : end_edge_ext bottom top he future_events.
  suff  : end_edge_ext bottom top he (e :: future_events).
    rewrite /end_edge_ext; move=> /orP[-> // | ] /= /orP[ | ->]; last first.
      by rewrite orbT.
    move: puh=> /[swap] /eqP <-; rewrite strict_nonAunder; last first.
      by apply: valid_edge_right.
    by rewrite right_on_edge.
  have := (proj2 (andP (allP clae lcc _))); rewrite ?heq; apply.
  by rewrite ocd; subset_tac.
move: cle => /= /andP[] cloe _.
have clan := opening_cells_close vle vhe oute endle endhe cloe.
have main := (insert_opening_closeness close_fc clan close_lc).
split.
  by move: main; rewrite /opening_cells oca_eq -cats1 -!catA.
have subfc : {subset fc <= open} by rewrite ocd; subset_tac.
have sublc : {subset lc <= open} by rewrite ocd; subset_tac.
(* TODO : redo this as it is overkill for what follows. *)
have svaln :
  forall q, inside_box q -> lexePt (point e) q ->
   {in future_events, forall e', lexePt q (point e')} ->
   seq_valid ((fc ++ nos) ++ nlsto :: lc) q.
  move=> q inbox_q elexq qlexfut.
  apply/allP=> x; rewrite !(mem_cat, inE) -orbA => /orP[xf | ].
    have /andP [vlx vhx] := allP sval x (subfc _ xf).
    have := (allP main x); rewrite mem_cat xf => /(_ isT) /andP claex.
    by rewrite (valid_between_events elexq qlexfut vlx inbox_q)
     ?(valid_between_events elexq qlexfut vhx inbox_q); case: claex.
  rewrite orbA=> /orP[ | xl]; last first.
    have /andP [vlx vhx] := allP sval x (sublc _ xl).
    move: (elexq);rewrite lexePt_eqVlt => /orP[/eqP <- | elexp'].
      by rewrite vlx vhx.
    have := (allP main x).
    rewrite 2!mem_cat xl !orbT => /(_ isT) /andP claex.
    by rewrite (valid_between_events elexq qlexfut vlx inbox_q)
    ?(valid_between_events elexq qlexfut vhx inbox_q); case: claex.
  move=> xin; have xin' : x \in opening_cells (point e) (outgoing e) le he.
    by rewrite /opening_cells oca_eq mem_rcons inE orbC.
  have [vlx vhx] := andP (allP (opening_valid oute vle vhe) _ xin').
  have [eelx eehx] := andP (allP clan _ xin').
  by rewrite (valid_between_events elexq qlexfut vlx inbox_q)
    ?(valid_between_events elexq qlexfut vhx inbox_q).
split.
  case futq : future_events => [ | ev2 fut']; first by left.
  right; rewrite /=.
  apply: svaln.
      by apply: (@allP [eqType of pt] _ _ inbox_es); rewrite map_f // futq inE eqxx.
    apply: lexPtW.
    by move: sort_evs; rewrite futq /= => /andP[].
  move=> e'; rewrite futq inE => /orP[/eqP -> | ].
    by apply: lexePt_refl.
  move=> e'in; apply/lexPtW.
  move: sort_evs; rewrite futq /= => /andP[] _.
  rewrite path_sortedE; last by move=> x y z; apply: lexPt_trans.
  by move=> /andP[] /allP /(_ e' e'in).
have [adjnew lownew] := adjacent_opening_aux vle vhe oute' oca_eq.
have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq heq /=.
move=> hnlsto.
split.
  suff : adjacent_cells ((fc ++ nos) ++ nlsto :: lc) by [].
  rewrite -catA.
  have oldnnil : rcons cc lcc != nil.
    by apply/eqP/rcons_neq0.
  rewrite -cat_rcons; apply: (replacing_seq_adjacent oldnnil).
  - by apply/eqP/rcons_neq0.
  - by rewrite lownew; move: leq; case: (cc) => [ | ? ?].
  - by rewrite !last_rcons.
  - by move: adj; rewrite ocd cat_rcons.
  by apply: adjnew.
have nn0 : rcons nos nlsto != nil by apply/eqP/rcons_neq0.
have on0 : rcons cc lcc != nil by apply/eqP/rcons_neq0.
move: cbtom; rewrite ocd -cat_rcons => cbtom'.
have hds: low (head dummy_cell (rcons cc lcc)) =
  low (head dummy_cell (rcons nos nlsto)).
  by rewrite head_rcons -leq -lownew head_rcons.
have tls : high (last dummy_cell (rcons cc lcc)) =
          high (last dummy_cell (rcons nos nlsto)).
  by rewrite !last_rcons.
split.
  move: cbtom'; 
  rewrite (replacing_seq_cells_bottom_top _ _ _ _ on0 nn0) //.
  by rewrite -catA cat_rcons.
rewrite -catA -cat_rcons.
have lein' : le \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have hein' : he \in all_edges open (e :: future_events).
  by rewrite /all_edges; subset_tac.
have lebhe : le <| he.
  by apply: (edge_below_from_point_above (noc _ _) vle vhe (underWC _)).
have noc2 : {in [:: le, he & outgoing e] &, no_crossing R}.
  by apply: (sub_in2 _ noc); rewrite /all_edges; subset_tac.
have subso : {subset sort (@edge_below _) (outgoing e)
                <= all_edges open (e :: future_events)}.
  by move=> x; rewrite mem_sort; apply: subo.
apply/allP=> x; rewrite 2!mem_cat orbCA => /orP[xin | xold]; last first.
  by apply: (allP rfo); rewrite ocd; move: xold => /orP[] ?; subset_tac.
have srt : path (@edge_below _) le (sort (@edge_below _) (outgoing e)).
  by have := sorted_outgoing vle vhe pal puh oute noc2.
have := (opening_cells_aux_right_form (underWC pal) puh vle vhe
               lein' hein' lebhe oute' noc subso srt oca_eq).
by move=> /allP /(_ x xin).
Qed.

#[clearbody]
Let exi' : point e >>> lsthe ->
  exists2 c, c \in lop & contains_point' (point e) c.
Proof.
rewrite lstheq; move=> pa.
suff abf : {in fop, forall c, point e >>> high c}.
have [wc wcin wcct] := exi; exists wc => //.
  move: wcin; rewrite /open !(mem_cat, inE) => /orP[wf | /orP[/eqP wl | //]].
    by move: wcct; rewrite /contains_point' (negbTE (abf _ wf)) andbF.
  by move: wcct; rewrite /contains_point' wl (negbTE pa) andbF.
have vfop1 : seq_valid (rcons fop lsto) (point e).
  apply/allP=> x; rewrite mem_rcons=> xin; apply: (allP sval).
  by move: x xin; rewrite /open; change {subset lsto::fop <= open}; subset_tac.
have vfop : {in rcons fop lsto, forall c, valid_edge (high c) (point e)}.
  move=> c cin.
  have cin' : high c \in [seq high i | i <- open].
    by apply: map_f; rewrite /open -cat_rcons; subset_tac.
  by apply: (seq_valid_high sval cin').
have rfop : s_right_form (rcons fop lsto).
  by apply: all_sub rfo; rewrite /open -cat_rcons; subset_tac.
have afop : adjacent_cells (rcons fop lsto).
  by move: adj; rewrite /open -cat_rcons => /adjacent_catW [].
have vh : valid_edge (low (head lsto fop)) (point e).
  by move: sval; rewrite /open; case: (fop) => [ | ? ?] /= /andP[] /andP[].
suff [] : point e >>> low (head lsto fop) /\
       {in fop, forall c, point e >>> high c} by [].
have := above_all_cells vfop1 afop rfop; rewrite last_rcons=> /(_ pa).
have hq : head dummy_cell (rcons fop lsto) = head lsto fop.
  by case: (fop) => [ | ? ?].
rewrite hq => -[-> others]; split=> // x xin.
by apply: others; rewrite mem_rcons inE xin orbT.
Defined.

Lemma inv1_seq_set_pts s1 s2 c1 lpts1 lpts2 :
  inv1_seq (s1 ++ set_pts c1 lpts1 lpts2 :: s2) <->
  inv1_seq (s1 ++ c1 :: s2).
Proof.
rewrite /inv1_seq.
have -> : close_alive_edges (s1 ++ set_pts c1 lpts1 lpts2 :: s2)
 future_events =
  close_alive_edges (s1 ++ c1 :: s2) future_events.
  by rewrite /close_alive_edges !all_cat /=.
have -> : adjacent_cells (s1 ++ set_pts c1 lpts1 lpts2 :: s2) =
  adjacent_cells (s1 ++ c1 :: s2).
  elim/last_ind : s1 => [ | [ | c0 s1] c0' _]; case: s2 => [ | c2 s2] //=;
  by rewrite /adjacent_cells ?cat_rcons ?cat_path //.
have -> : cells_bottom_top (s1 ++ set_pts c1 lpts1 lpts2 :: s2) =
  cells_bottom_top (s1 ++ c1 :: s2).
  rewrite /cells_bottom_top /cells_low_e_top.
  by case: s1 => [ | c0 s1]; elim/last_ind: s2 => [ | s2 c2 _];
   rewrite /= -?cat_rcons ?(last_rcons, cats0, last_cat).
have -> : s_right_form (s1 ++ set_pts c1 lpts1 lpts2 :: s2) =
  s_right_form (s1 ++ c1 :: s2).
  by rewrite /s_right_form !all_cat /=.
split; move=> [-> [B [-> [-> -> ]]]]; split=> //; split=> //.
  case: B; first by left.
  by rewrite /seq_valid !all_cat /=; right.
case: B; first by left.
by rewrite /seq_valid !all_cat /=; right.
Qed.

Lemma inv1_seq_set_left_pts s1 s2 c1 lpts :
  inv1_seq (s1 ++ set_left_pts c1 lpts :: s2) <->
  inv1_seq (s1 ++ c1 :: s2).
Proof. exact (inv1_seq_set_pts s1 s2 c1 lpts (right_pts c1)). Qed.

#[clearbody]
Let vlo : valid_edge (low lsto) (point e).
Proof. by apply: (proj1 (andP (allP sval lsto lstoin))). Defined.

#[clearbody]
Let vho : valid_edge (high lsto) (point e).
Proof. by apply: (proj2 (andP (allP sval lsto lstoin))). Defined.

Lemma last_step_situation fc' cc lcc lc le he:
  open_cells_decomposition (lsto :: lop) (point e) =
    (fc', cc, lcc, lc, le, he) ->
  p_x (point e) = lstx ->
  ~~ (point e <<< lsthe) ->
  point e <<= lsthe ->
  fc' = [::] /\ le = low lsto /\ exists cc', cc = lsto :: cc'.
Proof.
move=> oe pxhere eabove ebelow.
have lsto_ctn : contains_point' (point e) lsto.
  by rewrite /contains_point' -lstheq ebelow abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := decomposition_main_properties oe exi2.
have fc'0 : fc' = [::].
  case fc'q : fc' => [// | fc'i fc2].
  move: ocd; rewrite fc'q /= => - [] lstoisfc'i _.
  move: (all_nct lsto).
  by rewrite (contains_point'W lsto_ctn) fc'q lstoisfc'i inE eqxx =>/(_ isT).
split; first by [].
case ccq: cc => [ | cc0 cc'].
  move: ocd; rewrite fc'0 ccq /= => -[] lstoq.
  move: heq; rewrite -lstoq.
  have := open_cells_decomposition_cat adj rfo sval exi2 (abovelstle pxhere).
  rewrite oe => oe'.
  have [ocd' [lcc_ctn' [all_ct' [all_nct' [flcnct' [heq' [leq' [_ _]]]]]]]]
    := decomposition_main_properties oe exi2.
  have [pal puh vle vhe]:=
    decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  by move: puh; rewrite heq' -lstoq -lstheq (negbTE eabove).
have [ fopq | [fop' [lfop fopq]]] :
  fop = nil \/ exists fop' lfop, fop = rcons fop' lfop.
    elim/last_ind: (fop) => [| fop' lfop]; first by left.
    by right; exists fop', lfop.
  move: ocd; rewrite -cat_rcons fc'0 /= => lstohead.
  split.
    suff : lsto = head lcc cc by move=> ->.
    by rewrite -[LHS]/(head lsto (lsto :: lop)) lstohead; case: (cc).
  by exists cc'; move: lstohead; rewrite ccq /= => -[] ->.
move: adj; rewrite /open ocd fopq fc'0 cat_rcons /=.
move=> /adjacent_catW[] _ it.
move: (ocd); rewrite fc'0 /=; move: it=> /[swap] <- /andP[] /eqP <- _.
split.
  apply/esym; rewrite leq.
  move: adj; rewrite /open ocd fc'0 /= fopq cat_rcons=>/adjacent_catW[] _.
  by rewrite ccq /= => /andP[] /eqP ->.
by exists cc'; move: ocd; rewrite fc'0 ccq /= => -[] ->.
Qed.

#[clearbody]
Let loin : low lsto \in all_edges open (e :: future_events).
Proof. by rewrite 2!mem_cat map_f. Defined.

#[clearbody]
Let hoin : high lsto \in all_edges open (e :: future_events).
Proof. by rewrite 2!mem_cat map_f // orbT. Defined.

Arguments pt_eqb : simpl never.

Lemma step_keeps_invariant1 :
  invariant1 (step (Bscan fop lsto lop cls lstc lsthe lstx) e).
Proof.
case step_eq : (step _ _) => [fop' lsto' lop' cls' lstc' lsthe' lstx']. 
rewrite /state_open_seq /=; move: step_eq.
rewrite /step/generic_trajectories.step -/open.
have val_bet := valid_between_events elexp plexfut _ inbox_p.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  move: invariant1_default_case.
  rewrite -/(open_cells_decomposition _ _).
  case oe: (open_cells_decomposition _ _) => [[[[[fc cc ] lcc] lc] le] he].
  rewrite /generic_trajectories.simple_step.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno] def_case.
  rewrite /inv1_seq /= in def_case.
  move=> [] <- <- <- _ _ _ _.
  by apply: def_case.
have infop : {subset fop <= open} by rewrite /open; subset_tac.
have sval1 : seq_valid fop (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: infop.
have rfo1 : s_right_form fop.
  by apply/allP=> x xin; apply: (allP rfo); apply: infop.
have adj1 : adjacent_cells fop.
  by move: adj; rewrite /open => /adjacent_catW[].
have allnct1 : {in fop, forall c, ~contains_point (point e) c}.
  case fop_eq : fop => [// | c1 fop1].
  have := above_all_cells sval1 adj1 rfo1.
  have hfopq : high (last dummy_cell fop) = low lsto.
    move: adj.
    by rewrite /open fop_eq /= cat_path => /andP[] _ /= /andP[] /eqP.
  move: palstol; rewrite hfopq=> -> /(_ isT) [] _ M.
  by rewrite -fop_eq=> x xin; rewrite contains_pointE (negbTE (M x xin)) andbF.
have inlop : {subset lop <= open} by rewrite /open; subset_tac.
have lopclae : close_alive_edges lop (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae x); apply inlop.
have fop_note x : x \in fop ->
  ~ event_close_edge (low x) e /\ ~ event_close_edge (high x) e.
  move=> xin; apply: contrapositive_close_imp_cont.
  - by apply: (allP rfo); rewrite /open; subset_tac.
  - by apply/andP; apply: (allP sval); rewrite /open; subset_tac.
  by apply: allnct1.
have fopclae : close_alive_edges fop (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); rewrite /open; subset_tac.
move: (cle) => /= /andP[] cloe _.
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite /generic_trajectories.simple_step.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  move=> [] <- <- <- _ _ _ _.
  have := invariant1_default_case.
  by rewrite oe' oca_eq  /= cat_rcons.
have /andP [vllsto vhlsto] : valid_edge (low lsto) (point e) &&
                       valid_edge (high lsto) (point e).
  by move: sval=> /allP/(_ lsto); rewrite /open; apply; subset_tac.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite -/(update_open_cell lsto e).
  case uoceq : (update_open_cell lsto e) => [ nos lno] <-.
  rewrite /invariant1 /= /state_open_seq /= -catA -cat_rcons.
  move: uoceq; rewrite /update_open_cell/generic_trajectories.update_open_cell.
  case ogq : (outgoing e) => [ | fog ogs] /=.
    move=> -[] <- <- /=; rewrite inv1_seq_set_left_pts.
    have := invariant1_default_case.
    rewrite open_cells_decomposition_single=> //; last by rewrite -lstheq.
    rewrite ogq /=.
    do 2 rewrite -/(vertical_intersection_point _ _).
    rewrite pvertE // pvertE //=; rewrite cats0.
    rewrite -[pt_eqb _ _ (point e) _]/((point e) == _:> pt).
    rewrite -[pt_eqb _ _ _ (point e)]/(_ == (point e):> pt).
    have /negbTE -> :
         (Bpt (p_x (point e)) (pvert_y (point e) (high lsto)))
           != point e :> pt.
      rewrite pt_eqE /= eqxx /=.
      move: ebelow_st; rewrite -/(_ <<< _).
      rewrite strict_under_pvert_y lstheq // lt_neqAle eq_sym.
      by move=> /andP[].
    have /negbTE -> :
     point e != Bpt (p_x (point e)) (pvert_y (point e) (low lsto)) :> pt.
      rewrite pt_eqE /= eqxx /=.
      by move: palstol; rewrite under_pvert_y // le_eqVlt negb_or=> /andP[].
    set w := [:: _ ; _; _].
    by rewrite (inv1_seq_set_pts fop lop lsto w nil).
  have := invariant1_default_case.
  rewrite open_cells_decomposition_single=> //; last by rewrite -lstheq.
  rewrite -/(opening_cells_aux _ _ _ _).
  rewrite ogq; case oca_eq: opening_cells_aux => [[| no0 nos'] lno'].
    have ognn : (outgoing e) != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vho ognn oute.
    by rewrite ogq oca_eq.
  by move => + [] <- <- /=; rewrite inv1_seq_set_left_pts cat_rcons -!catA /=.
have lsto_ctn : contains_point'(point e) lsto.
  rewrite /contains_point'.
  by rewrite -lstheq /point_under_edge (negbFE ebelow) abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe => oe'.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi.
have [ocd' _] := decomposition_main_properties oe exi2.
have [fc'0 [lelsto [cc' ccq]]] : fc' = [::] /\ le = low lsto /\
          exists cc', cc = lsto :: cc'.
  by have := last_step_situation oe pxhere (negbT eonlsthe) (negbFE ebelow).
rewrite /generic_trajectories.update_open_cell_top.
rewrite -/(open_cells_decomposition _ _).
rewrite oe.
case o_eq : (outgoing e) => [ | g l]; rewrite -?o_eq; last first.
  rewrite -!/(open_cells_decomposition _ _).
  have := invariant1_default_case; rewrite oe'.
  rewrite -lelsto.
  rewrite -!/(opening_cells_aux _ _ _ _).
  case: (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    move=> + <-; rewrite /invariant1 /state_open_seq /=.
    by rewrite !cats0 -!catA.
  move=> + <-; rewrite /invariant1 /state_open_seq /=.
  rewrite -!catA /= => it.
  by rewrite (catA fop) inv1_seq_set_left_pts -catA.
move=> [] <- <- <- _ _ _ _ /=.
have subf : {subset (fop ++ fc') <= open} by rewrite /open ocd; subset_tac.
have adjf : adjacent_cells (fop ++ fc').
  by move: adj; rewrite /open ocd=> /adjacent_catW[].
have claef : close_alive_edges (fop ++ fc') (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); apply: subf.
have rfof : s_right_form (fop ++ fc').
  by apply/allP=> x xin; apply: (allP rfo); apply: subf.
have svalf : seq_valid (fop ++ fc') (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: subf.
have subl : {subset (lsto :: lop) <= open}.
  by rewrite /open; subset_tac.
have adjl : adjacent_cells (lsto :: lop).
  by move: adj=> /adjacent_catW[].
have rfol : s_right_form (lsto :: lop).
  by apply/allP=> x xin; apply: (allP rfo); apply: subl.
have svall : seq_valid (lsto :: lop) (point e).
  by apply/allP=> x xin; apply: (allP sval); apply: subl.
have cbtom' : cells.cells_bottom_top (low lsto) top (lsto :: lop).
  move: cbtom; rewrite /open /cells.cells_bottom_top /cells_low_e_top eqxx //=.
  by move=> /andP[] _; rewrite last_cat /=.
have [pal puh vl vh not_ct] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
have claef' : close_alive_edges (fop ++ fc') future_events.
  elim/last_ind: {-1}(fop ++ fc') (erefl (fop ++ fc')) => [// | fc2 c2 _] f_eq.
  have hc2q : high c2 = low (head lcc cc).
    move: adj; rewrite /open ocd catA f_eq -cats1 -!catA=> /adjacent_catW[] _.
    by rewrite ccq /= => /andP[] /eqP.
  have palst : point e >>> high (last dummy_cell (fop ++ fc')).
    by rewrite f_eq last_rcons hc2q -leq.
  have [above_l above_h] := above_all_cells svalf adjf rfof palst.
  have {}allabove_l : {in fop ++ fc', forall c, point e >>> low c}.
    move=> c /mem_seq_split [s1 [s2 s_q]].
      elim/last_ind: {-1} (s1) (erefl s1) => [ | s1' c1 _] s1q.
        by move: above_l; rewrite s_q s1q /=.
      have : point e >>> high c1.
        by rewrite above_h // s_q s1q cat_rcons; subset_tac.
      have /eqP -> // : high c1 == low c.
      move: adjf; rewrite s_q s1q -cats1 -catA /= => /adjacent_catW[] _.
      by rewrite /= => /andP[].
  have f_not_end : forall c, c \in fop ++ fc' ->
  ~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
    move=> c cin; apply: contrapositive_close_imp_cont.
    - by apply: (allP rfof).
    - by apply/andP; apply: (allP svalf).
    by apply/negP; rewrite contains_pointE (negbTE (above_h _ cin)) andbF.
  apply/allP=> x; rewrite -f_eq => xin.
  by apply: (allP (head_not_end claef f_not_end)).  
have clael : close_alive_edges lc (e :: future_events).
  by apply/allP=> x xin; apply: (allP clae); rewrite /open ocd; subset_tac.
have clael' : close_alive_edges lc future_events.
  case lc_eq : (lc) => [ // | c2 lc2]; rewrite -lc_eq.
  have [puhlcc adj2] : point e <<< low (head dummy_cell lc) /\
                        adjacent_cells lc.
    move: adj; rewrite /open ocd lc_eq.
    move=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
    by move=> /andP[] /eqP <- ->; rewrite -heq.
  have sub2 : {subset lc <= open} by rewrite /open ocd; subset_tac.
  have sval2 : seq_valid lc (point e).
    by apply/allP=> x xin; apply: (allP sval); apply: sub2.
  have rfo2 : s_right_form lc.
    by apply/allP=> x xin; apply: (allP rfo); apply: sub2.
  have below_h : {in lc, forall c, point e <<< high c}.
    exact: (below_all_cells sval2 adj2 rfo2 puhlcc).
  have below_l : {in lc, forall c, point e <<< low c}.
    move=> c /mem_seq_split [s1 [s2 s_q]].
    elim/last_ind: {2}(s1) (erefl s1) => [ | s1' c1 _] s1_q.
      by move: puhlcc; rewrite s_q s1_q /=.
    move: adj2; rewrite s_q s1_q -cats1 -catA=> /adjacent_catW [] _ /=.
    move=> /andP[]/eqP <- _; apply: below_h.
    rewrite s_q s1_q cat_rcons; subset_tac.
  have l_not_end : forall c, c \in lc ->
  ~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
    move=> c cin; apply: contrapositive_close_imp_cont.
    - by apply: (allP rfo2).
    - by apply/andP; apply: (allP sval2).
    by apply/negP; rewrite contains_pointE negb_and negbK (below_l _ cin).
  apply/allP=> x xin.
  by apply: (allP (head_not_end clael l_not_end)).
rewrite cats0 /invariant1 /state_open_seq /=; set open' := (X in inv1_seq X).
have clae_part : close_alive_edges open' future_events.
  rewrite /close_alive_edges all_cat [all _ (fop ++ fc')]claef' /=.
  rewrite [all _ lc]clael' andbT.
  have le_end : end_edge_ext bottom top le future_events.
    elim/last_ind: {-1} (fop ++ fc') (erefl (fop ++ fc')) => [ | fs c1 _] f_eq.
      move: f_eq; case fop_eq: (fop) => [ | //].
      move: cbtom; rewrite /open fop_eq /= => /andP[] /andP[] _ /= /eqP + _.
      by rewrite /end_edge_ext lelsto !inE => -> _; rewrite eqxx.
    have <- : high c1 = le.
      rewrite fc'0 cats0 in f_eq.
      move: adj; rewrite /open f_eq -cats1 -catA=>/adjacent_catW[] _ /=.
      by rewrite lelsto; move=> /andP[] /eqP.
    apply: (proj2 (andP (allP claef' c1 _))).
    by rewrite f_eq mem_rcons inE eqxx.
  have he_end : end_edge_ext bottom top he future_events.
    case lc_eq : lc => [ | c1 lc'].
      have hetop : he = top.
        move: cbtom=> /andP[] /andP[] _ _.
        by rewrite /open ocd lc_eq !last_cat -heq /= => /eqP.
      by rewrite /end_edge_ext hetop !inE eqxx ?orbT.
    have hlccq : high lcc = low c1.
      move: adj; rewrite /open ocd lc_eq.
      by move=> /adjacent_catW[] _ /adjacent_catW[] _ /andP[] /eqP.
    have c1in : c1 \in lc by rewrite lc_eq inE eqxx.
    by have := (allP clael' _ c1in) => /andP[] + _; rewrite -hlccq -heq.
  by rewrite -lelsto le_end he_end.
split=> //.
have vhe : valid_edge he (point e).
 by have []:= decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
split.
  case futq : future_events => [ | e2 fut]; first by left.
  have elexe2 : lexePt (point e) (point e2).
    by apply/lexPtW; move: sort_evs; rewrite futq /= => /andP[].
  rewrite /seq_valid all_cat /= all_cat andbCA.
  have e2lexfut : {in future_events, forall e, lexePtEv e2 e}.
    move=> e'; rewrite futq inE=> /orP[/eqP ->|]; first by apply: lexePt_refl.
    move=> e'in; apply/lexPtW; move: sort_evs; rewrite futq=> /= /andP[] _.
    rewrite path_sortedE; last by move=> x y z; apply: lexPt_trans.
    by move=> /andP[] /allP /(_ e') + _; apply.
  have inbox_e2 : inside_box (point e2).
    by apply: (@allP [eqType of pt] _ _ inbox_es); rewrite futq /= inE eqxx.
  right.
  apply/andP; split; last first.
    rewrite -!all_cat fc'0 cats0; apply/allP=> x xin.
    have /andP[vlx vhx] :
    valid_edge (low x) (point e) && valid_edge (high x) (point e).
      apply: (allP sval); rewrite /open ocd.
      by move: xin; rewrite mem_cat=> /orP[] ?; subset_tac.
    have /andP[eelx eehx] :
     end_edge_ext bottom top (low x) future_events &&
     end_edge_ext bottom top (high x) future_events.
      apply: (allP clae_part). 
      by rewrite /open'; move: xin; rewrite mem_cat=>/orP[] ?; subset_tac.
    by rewrite !(valid_between_events elexe2 e2lexfut _ inbox_e2).
  have eelo : end_edge_ext bottom top (low lsto) future_events.
    have : end_edge_ext bottom top (low lsto) (e :: future_events).
      by apply: (proj1 (andP (allP clae lsto _))).
    rewrite /end_edge_ext /= => /orP[-> // | /orP[abs | ->]]; last first.
      by rewrite !orbT.
    by move: palstol; rewrite -(eqP abs) right_pt_below.
  have eehe : end_edge_ext bottom top he future_events.
    have : end_edge_ext bottom top (high lcc) (e :: future_events).
      apply: (proj2 (andP (allP clae lcc _))).
      by rewrite /open ocd; subset_tac.
    rewrite /end_edge_ext heq /= => /orP[-> // | /orP[abs | ->]]; last first.
      by rewrite orbT.
    by move: puh; rewrite heq -(eqP abs) -[_ <<< _]negbK right_pt_above.
  by rewrite !(valid_between_events elexe2 e2lexfut _ inbox_e2).
split.
  case feq : fop => [ | c0 f].
    rewrite /open' feq fc'0 /=.
    move: adj; rewrite /open ocd => /adjacent_catW[] _ /adjacent_catW[] _ /=.
    by case: (lc)=> [ // | c2 lc'] /=; rewrite heq.
  rewrite /open' -adjacent_cut /=; last by rewrite feq.
  apply/andP; split.
    apply/andP; split; last by move: adj; rewrite /open ocd=> /adjacent_catW.
    rewrite fc'0 cats0; move: adj; rewrite /open feq /= cat_path /=.
    by move=> /andP[] _ /andP[].
  move: adj; rewrite /open ocd=> /adjacent_catW[] _ /adjacent_catW[] _ /=.
  by case: (lc) => [// | c2 l'] /=; rewrite heq.
have on0 : rcons cc lcc != nil by apply/eqP/rcons_neq0.
rewrite /open'.
set nc := Bcell _ _ _ _.
have nn0 : [:: nc] != nil by [].
split.
  rewrite -(replacing_seq_cells_bottom_top _ _ _ _ on0 nn0).
  - by rewrite cat_rcons -ocd.
  - rewrite /nc /= head_rcons.
    by rewrite -leq.
  by rewrite /nc/= last_rcons.
rewrite /s_right_form all_cat /=; apply/andP; split.
  by apply/allP=> x xin; apply: (allP rfo); rewrite /open ocd; subset_tac.
apply/andP; split; last first.
  by apply/allP=> x xin; apply: (allP rfo); rewrite /open ocd; subset_tac.
have noclstohe : below_alt he (low lsto).
  by apply: noc; rewrite /all_edges; subset_tac.
have := edge_below_from_point_under noclstohe vhe vlo (underW puh) palstol.
by [].
Qed.

Lemma pairwise_subst {T : Type} [leT : rel T] (os ns s1 s2 : seq T) :
  pairwise leT (s1 ++ os ++ s2) ->
  pairwise leT ns ->
  allrel leT s1 ns ->
  allrel leT ns s2 ->
  pairwise leT (s1 ++ ns ++ s2).
Proof.
rewrite !pairwise_cat !allrel_catr => /andP[] /andP[] _ -> /andP[] ->.
by move=>/andP[] _ /andP[] _ -> -> -> ->.
Qed.

Lemma pairwise_subst1 {T : eqType} [leT : rel T] (oc nc : T)(s1 s2 : seq T) :
  leT nc =1 leT oc -> leT^~ nc =1 leT^~ oc ->
  pairwise leT (s1 ++ oc :: s2) = pairwise leT (s1 ++ nc :: s2).
Proof.
move=> l r.
by rewrite !(pairwise_cat, pairwise_cons, allrel_consr) (eq_all l) (eq_all r).
Qed.

Lemma new_edges_above_first_old fc cc lcc lc le:
  open = fc ++ cc ++ lcc :: lc ->
  all (fun x => valid_edge x(point e))
        [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  pairwise (@edge_below _) [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  all ((@edge_below _)^~ le) [seq high x | x <- fc] ->
  point e >>> le ->
  point e <<< high lcc ->
  valid_edge le (point e) ->
  allrel (@edge_below _) 
    [seq high c | c <- fc]
    [seq high c | c <- 
      opening_cells (point e) (outgoing e) le (high lcc)].
Proof.
move=> ocd.
rewrite !map_cat !all_cat => /andP[] vfc /andP[] _ /= /andP[] vhe _.
move=> + fcbl pal puh vle.
rewrite !pairwise_cat=> /andP[] fcbcc /andP[] _ /andP[] /=.
rewrite allrel_consr=> /andP[] pw' _ /andP[] pw _.
rewrite /opening_cells.
case oca_eq : opening_cells_aux => [s c].
have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => highsq.
have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => highcq.
rewrite -cats1 map_cat allrel_catr allrel_consr /=.
have -> : all ((@edge_below _)^~ (high c)) [seq high x | x <- fc].
  rewrite highcq; move: fcbcc; rewrite allrel_catr allrel_consr.
  by move=> /andP[] _ /andP[].
rewrite allrel0r.
have -> //: allrel (@edge_below _) [seq high x | x <- fc][seq high y | y <- s].
rewrite highsq.
apply/allrelP=> x y xin yin.
have vx : valid_edge x (point e) by apply: (allP vfc).
have vy : valid_edge y (point e).
  by apply: valid_edge_extremities; rewrite oute'.
have puy : point e <<= y.
  by rewrite -(eqP (oute' yin)); apply: left_pt_below.
have xble : x <| le by apply: (allP fcbl).
have pax : point e >>> x.
  apply/negP=> pux; case/negP: pal.
  by apply: (order_edges_viz_point' vx vle xble pux).
have nocyx : below_alt y x.
  apply: noc; rewrite ocd /all_edges/events_to_edges; last first.
    by rewrite !(cell_edges_cat, mem_cat) ?xin ?orbT //.
  rewrite /= mem_cat [X in (_ || X)]mem_cat.
  by rewrite mem_sort in yin; rewrite yin !orbT.
by have := edge_below_from_point_under nocyx vy vx puy pax.
Qed.

Lemma new_edges_below_last_old fc cc lcc lc le:
  open = fc ++ cc ++ lcc :: lc ->
  all (fun x => valid_edge x(point e))
        [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  pairwise (@edge_below _) [seq high x | x <- fc ++ cc ++ lcc :: lc] ->
  point e >>= le ->
  point e <<< high lcc ->
  valid_edge le (point e) ->
  allrel (@edge_below _) 
    [seq high c | c <- 
      opening_cells (point e) (outgoing e) le (high lcc)]
        [seq high c | c <- lc].
Proof.
move=> ocd.
rewrite !map_cat !all_cat => /andP[] _ /andP[] _ /= /andP[] vhe vlc.
move=> + pal puh vle.
rewrite !pairwise_cat=> /andP[] _ /andP[] _ /andP[] _ /andP[] _.
rewrite /= => /andP[] heblc _.
rewrite /opening_cells.
case oca_eq : opening_cells_aux => [s c].
have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => highsq.
have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => highcq.
rewrite -cats1 allrel_mapl allrel_catl /= allrel_consl allrel0l ?andbT.
rewrite highcq heblc andbT.
rewrite -allrel_mapl highsq; apply/allrelP=> x y /[dup] xin xin' yin.
rewrite mem_sort in xin'.
have vx: valid_edge x (point e) by apply valid_edge_extremities; rewrite oute'.
have vy: valid_edge y (point e) by apply: (allP vlc).
have highlccley : high lcc <| y by apply: (allP heblc).
have puy : point e <<< y.
  by have := order_edges_strict_viz_point' vhe vy highlccley puh.
have pax : point e >>= x.
  rewrite -(eqP (oute' xin)); apply left_pt_above.
have nocxy : below_alt x y.
  apply: noc; rewrite /all_edges/events_to_edges/= ocd !mem_cat ?xin' ?orbT //.
  by rewrite !map_cat /= !mem_cat !inE yin !orbT.
by have := edge_below_from_point_above nocxy vx vy pax puy.
Qed.

Lemma step_keeps_pw_default :
  let '(fc, cc, lcc, lc, le, he) :=
  open_cells_decomposition open (point e) in
  let '(nos, lno) := 
    opening_cells_aux (point e)
        (sort (@edge_below _) (outgoing e)) le he in
    pairwise (@edge_below _) 
       (bottom :: [seq high x | x <- fc ++ nos ++ lno :: lc]).
Proof.
case oe: (open_cells_decomposition open (point e)) =>
  [[[[[fc cc] lcc] lc] le] he].
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := decomposition_main_properties oe exi.
have [pal puh vle vhe allnct] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have oc_eq : opening_cells (point e) (outgoing e) le he = rcons nos lno.
  by rewrite /opening_cells oca_eq.
rewrite /=; apply/andP; split.
  rewrite map_cat all_cat; apply/andP; split.
    by move: pwo; rewrite ocd /= map_cat all_cat=> /andP[] /andP[] ->.
  rewrite -cat_rcons map_cat all_cat; apply/andP; split; last first.
    move: pwo; rewrite ocd /= !map_cat !all_cat /=.
    by move=> /andP[] + _; do 3 move=> /andP[] _.
  rewrite map_rcons all_rcons.
  have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => ->.
  have -> /= : bottom <| he.
    have lcco : lcc \in open by rewrite ocd !mem_cat inE eqxx !orbT. 
    rewrite heq.
    move: pwo=> /= /andP[] /allP /(_ (high lcc)) + _; rewrite map_f //.
    by apply.
  have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => ->.
  apply/allP=> g; rewrite mem_sort=> gin.
  have lgq : left_pt g = point e by apply/eqP/oute.
  have vlg : valid_edge bottom (left_pt g).
    by rewrite lgq; apply: (inside_box_valid_bottom inbox_e).
(* TODO : this should be made a top level lemma *)
  have /no_crossingE : below_alt g bottom.
    apply: noc.
      by rewrite mem_cat /events_to_edges /= !mem_cat gin !orbT.
    rewrite 2!mem_cat -orbA; apply/orP; left.
    move: cbtom=> /andP[]; case: (open) => [ // | o1 op'] /= /eqP -> _.
    by rewrite inE eqxx.
  move=> /(_ vlg) [] _; apply.
  by move: inbox_e=> /andP[] /andP[] + _ _; rewrite lgq.
rewrite -cat_rcons.
rewrite pairwise_map.
move: pwo; rewrite pairwise_cons ocd -cat_rcons pairwise_map=> /andP[] _ pwo'.
have vhocd : all ((@valid_edge _)^~ (point e))
     [seq high x | x <- fc ++ cc ++ lcc :: lc].
  by rewrite -ocd; apply/allP; apply: seq_valid_high.
move: (pwo'); rewrite cat_rcons -pairwise_map=> pwo2.
have puh' : point e <<< high lcc by rewrite -heq.
apply: (pairwise_subst pwo'); rewrite -?pairwise_map.
- rewrite -oc_eq.
  have lein' : le \in all_edges open (e :: future_events).
    by rewrite mem_cat lein.
  have hein' : he \in all_edges open (e :: future_events).
    by rewrite mem_cat hein.
  by apply: opening_cells_pairwise.
- have : allrel (@edge_below _) [seq high x | x <- fc]
          [seq high x | x <- rcons nos lno].
    have fcle : all ((@edge_below _)^~ le) [seq high x | x <- fc].
      apply/allP=> x /mapP[xc xcin xq].
      elim/last_ind : {-1} (fc) (erefl fc) => [ | fc' lfc _] fcq.
        by move: xcin; rewrite fcq.
      have := last_first_cells_high cbtom adj bet_e oe => <-.
      rewrite fcq map_rcons last_rcons xq.
      move: xcin; rewrite fcq mem_rcons inE=> /orP[/eqP -> | xcin ].
        by apply: edge_below_refl.
      move: pwo'; rewrite pairwise_cat fcq pairwise_rcons=> /andP[] _ /andP[].
      by move=> /andP[] + _ _ => /allP /(_ xc xcin) /=.
    have := new_edges_above_first_old ocd vhocd pwo2 fcle pal puh' vle.
    by rewrite -oc_eq heq.
  by rewrite allrel_mapr allrel_mapl.
have : allrel (@edge_below _) [seq high x | x <- rcons nos lno]
            [seq high x | x <- lc].
   have := new_edges_below_last_old ocd vhocd pwo2 (underWC pal) puh' vle.
   by rewrite -heq oc_eq.
by rewrite allrel_mapl allrel_mapr.
Qed.

#[clearbody]
Let open_edge_valid x :
   x \in cell_edges open -> valid_edge x (point e).
Proof.
by rewrite /cell_edges mem_cat => /orP[] /mapP [c /(allP sval) /andP[]+ + ->].
Defined.

Lemma step_keeps_pw :
  pairwise (@edge_below _)
     (bottom ::
       [seq high x | x <- state_open_seq (step (Bscan fop lsto lop cls lstc
           lsthe lstx) e)]).
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere/abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition (fop ++ lsto :: lop) (point e))=>
    [[[[[fc cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  move: step_keeps_pw_default; rewrite /open.
  by rewrite oe oca_eq /state_open_seq /= catA.
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have := step_keeps_pw_default; rewrite oe' oca_eq.
  rewrite [state_open_seq _]
           (_ : _ = (rcons fop lsto ++ fc') ++ nos ++ lno :: lc); last first.
    by rewrite /state_open_seq /= cat_rcons !catA.
  by apply.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite /state_open_seq /=.
  rewrite /generic_trajectories.update_open_cell.
  case oq : (outgoing e) => [ | fog ogs] /=.
    rewrite cats0 map_cat /=; apply/andP; split.
      move: pwo; rewrite pairwise_cons /open => /andP[] + _.
      by rewrite map_cat.
    move: pwo; rewrite pairwise_cons /open=> /andP[] _.
    by rewrite map_cat /=.
  have ocd : open_cells_decomposition open (point e) =
          (fop, [::], lsto, lop, low lsto, high lsto).
    by rewrite open_cells_decomposition_single; rewrite // -lstheq.
  have same_left cg lpts : (fun c' => (edge_below (high cg) (high c'))) =1
      (fun c' => (edge_below (high (set_left_pts cg lpts))(high c'))).
    by move=> c'; rewrite /set_left_pts /=.
  have same_right cg lpts : (fun c' => edge_below (high c') (high cg)) =1
      (fun c' => edge_below (high c') (high (set_left_pts cg lpts))).
    by move=> c'; rewrite /set_left_pts /=.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | f s] c] /=.
    rewrite cats0 -cat_rcons.
    have:= step_keeps_pw_default.
    rewrite ocd oq oca_eq /= cat_rcons !pairwise_map => pw.
    have onn : outgoing e != [::] by rewrite oq.
    have := opening_cells_aux_absurd_case vlo vho onn oute.
    by rewrite oq oca_eq.
  have := step_keeps_pw_default.
  rewrite ocd oq oca_eq /= !pairwise_map => pw.
  rewrite -catA /=.
  apply/andP; split.
    by move: pw=> /andP[] + _; rewrite !map_cat !all_cat /=.
  have := @pairwise_subst1 _
                 (fun c1 c2 => edge_below (high c1) (high c2)) f
      (set_left_pts f [:: point e & behead (left_pts lsto)]
) fop (s ++ c :: lop)
      (same_left f (point e :: behead (left_pts lsto)))
      (same_right f (point e :: behead (left_pts lsto))) => <-.
  by move: pw=> /andP[] _.
(* Now the point is on lsthe *)
(* Next12 lines duplicated from the end of step_keeps_invariant1 *)
have lsto_ctn : contains_point'(point e) lsto.
  rewrite /contains_point'.
  by rewrite -lstheq /point_under_edge (negbFE ebelow) abovelstle.
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  by exists lsto; rewrite // inE eqxx.
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
  rewrite oe => oe'.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi.
have [ocd' _] := decomposition_main_properties oe exi2.
have [fc'0  [lelsto [cc' ccq]]] : fc' = [::] /\ le = low lsto /\
  exists cc', cc = lsto :: cc'.
  by have := last_step_situation oe pxhere (negbT eonlsthe) (negbFE ebelow).
rewrite /generic_trajectories.update_open_cell_top.
case o_eq : (outgoing e) => [ | g l]; rewrite -?o_eq; last first.
(* If there are outgoing edges, this cell is treated as in the default case. *)
  have := step_keeps_pw_default.
  rewrite -/(open_cells_decomposition _ _) oe' -lelsto.
  rewrite oe.
  rewrite -/(opening_cells_aux _ _ _ _).
  case: (opening_cells_aux _ _ _ _) => [nos lno].
  case nosq : nos => [ | fno nos'] /=.
    by rewrite /state_open_seq /= !cats0.
  rewrite /state_open_seq /= catA -(catA (_ ++ _)) /= map_cat /= => it.
  by rewrite map_cat /=.
rewrite -/(open_cells_decomposition _ _) oe /=.
have := step_keeps_pw_default; rewrite oe' -lelsto o_eq /=.
have vle : valid_edge le (point e) by apply: open_edge_valid.
have vhe : valid_edge he (point e) by apply: open_edge_valid.
do 2 rewrite -/(vertical_intersection_point _ _).
by rewrite pvertE // pvertE // !map_cat /= cats0.
Qed.

Lemma update_open_cell_side_limit_ok new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  p_x (point e) = left_limit lsto ->
  point e <<< high lsto ->
  point e >>> low lsto ->
  all open_cell_side_limit_ok (rcons new_op new_lsto).
Proof.
rewrite /update_open_cell/generic_trajectories.update_open_cell.
move=> + pxq puh pal /=.
have := (allP open_side_limit lsto lstoin).
rewrite /open_cell_side_limit_ok /= => /andP[] lptsno /andP[] alllpts.
move=> /andP[] slpts /andP[] athigh atlow.
case lptsq : (left_pts lsto) lptsno => [ // | p1 [ | p2 lpts']] _ /=.
  rewrite lptsq /= in athigh atlow.
  (* contradiction with puh pal *)
  have pxe1 : p_x (point e) = p_x p1 by rewrite pxq /left_limit lptsq.
  have := strict_under_edge_lower_y pxe1 athigh; rewrite puh=> /esym.
  have := under_edge_lower_y pxe1 atlow; rewrite (negbTE pal)=>/esym.
  move/negbT; rewrite -ltNge=> /lt_trans /[apply].
  by rewrite lt_irreflexive.
have pxe2 : p_x (point e) = p_x p2.
  rewrite (eqP (allP alllpts p2 _)); last by rewrite lptsq !inE eqxx orbT.
  exact pxq.
have p2lte : p_y p2 < p_y (point e).
  have := lex_left_limit; rewrite lptsq /= => /andP[] + _.
  by rewrite /lexPt pxe2 lt_irreflexive eqxx.
case ogq : (outgoing e) => [ | fog ogs].
  move=> [] <- <-; rewrite /= andbT /open_cell_side_limit_ok /=.
  have pxel : p_x (point e) = p_x (last p2 lpts').
    by rewrite pxq /left_limit lptsq.
  move: (alllpts); rewrite /left_limit.
  rewrite lptsq /= => /andP[] -> /andP[] /[dup]/eqP p2x -> ->.
  rewrite lptsq /= in athigh.
  have pxe1 : p_x (point e) = p_x p1.
    by have := alllpts; rewrite lptsq /= => /andP[] /eqP ->.
  have := strict_under_edge_lower_y pxe1 athigh; rewrite puh=> /esym ye1.
  move: (pxel) => /eqP ->; rewrite ye1.
  move: slpts; rewrite lptsq /= => /andP[] _ ->.
  by rewrite athigh; move: atlow; rewrite lptsq /= => ->; rewrite p2lte !andbT.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq: (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  have onn : outgoing e != [::] by rewrite ogq.
  have := opening_cells_aux_absurd_case vlo vho onn oute.
  by rewrite ogq oca_eq.
move=> -[] <- <- /=.
have ognn : outgoing e != [::] by rewrite ogq.
have := opening_cells_last_left_pts vlo vho oute ognn puh; rewrite /=.
rewrite ogq oca_eq /= => llnoq /=.
move: (alllpts); rewrite /left_limit.
rewrite lptsq /= => /andP[] _ /andP[] -> ->.
move: pxq; rewrite /left_limit lptsq /= => ->; rewrite eqxx /=.
rewrite p2lte /=.
have := allP open_side_limit lsto lstoin => /andP[] _ /andP[] _.
rewrite lptsq /= => /andP[] /andP[] _ -> /andP[] _ llo.
have := opening_cells_seq_edge_shift _ vlo vho oca_eq.
rewrite -ogq => /(_ oute') /= -[] <- _; rewrite llo andbT.
have := opening_cells_aux_high vlo vho oute'; rewrite ogq oca_eq /= => highout.
apply/andP; split.
  have /oute'/eqP <- : high fno \in sort (@edge_below _) (outgoing e).
    by rewrite ogq -highout inE eqxx.
  by apply left_on_edge.
have := opening_cells_aux_side_limit vlo vho (underWC pal) puh oute'.
rewrite ogq oca_eq => /(_ _ _ erefl) allok.
by apply/allP=> x xin; apply: (allP allok x); rewrite /= inE xin orbT.
Qed.

Lemma size_left_lsto :
  p_x (point e) = lstx ->
  point e >>> low lsto ->
  point e <<= high lsto ->
  (1 < size (left_pts lsto))%N.
Proof.
move=> pxhere pal puh.
have lstok : open_cell_side_limit_ok lsto by apply: (allP open_side_limit).
case lptsq : (left_pts lsto) => [ | p1 [ | p2 lpts]] //.
  by move: lstok; rewrite /open_cell_side_limit_ok lptsq.
have /andP[p1onh p1onl] : (p1 === high lsto) && (p1 === low lsto).
  by move: lstok; rewrite /open_cell_side_limit_ok /left_limit lptsq /= eqxx /=.
have /eqP samex : p_x (point e) = p_x p1.
  by have := pxhere; rewrite lstxq /left_limit lptsq /=.
suff : p_y (point e) < p_y (point e) by rewrite lt_irreflexive.
have := same_pvert_y vho samex. 
rewrite (on_pvert p1onh). 
have := under_pvert_y vho; move: (puh)=> /[swap] -> /[swap] ->.
move=> /le_lt_trans; apply.
have := under_pvert_y vlo; move: (pal) => /[swap] ->.  
rewrite (same_pvert_y vlo samex).
by rewrite -ltNge (on_pvert p1onl).
Qed.

Lemma step_keeps_open_side_limit_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) := opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  all open_cell_side_limit_ok ((fc ++ nos) ++ lno :: lc).
Proof.
case oe: (open_cells_decomposition open (point e)) =>
  [[[[[fc cc] lcc] lc] le] he].
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]]
  := decomposition_main_properties oe exi.
have [pal puh vle vhe allnct] :=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have oc_eq : opening_cells (point e) (outgoing e) le he = rcons nos lno.
  by rewrite /opening_cells oca_eq.
have := opening_cells_side_limit vle vhe (underWC pal) puh oute.
rewrite /opening_cells oca_eq => oknew.
rewrite -catA -cat_rcons !all_cat andbCA; apply/andP; split; first by [].
have := open_side_limit; rewrite ocd -cat_rcons all_cat=> /andP[] -> /=.
by rewrite all_cat /= => /andP[].
Qed.

Lemma step_keeps_open_side_limit :
  all open_cell_side_limit_ok
    (state_open_seq (step (Bscan fop lsto lop cls lstc lsthe lstx) e)).
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP=> [pxaway | /negbFE/eqP/[dup] pxhere/abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition (fop ++ lsto :: lop) (point e))=>
    [[[[[fc cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  by move: step_keeps_open_side_limit_default; rewrite /open oe oca_eq.
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe: (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  move: step_keeps_open_side_limit_default; rewrite /open oe' oca_eq.
  by rewrite /state_open_seq /= cat_rcons.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite /state_open_seq /=.
  rewrite -/(update_open_cell _ _).
  case uoc_eq : (update_open_cell lsto e) => [nos lno] /=.
  have pxhere' : p_x (point e) = left_limit lsto by rewrite pxhere.
  have puh : point e <<< high lsto by rewrite -lstheq.
  have nosok := update_open_cell_side_limit_ok uoc_eq pxhere' puh palstol.
  rewrite -catA -cat_rcons !all_cat nosok /= -all_cat.
  by apply: (all_sub _ open_side_limit); rewrite /open; subset_tac.
move/negbFE:ebelow => ebelow.
move/negbT: eonlsthe=> eonlsthe.
rewrite -/(open_cells_decomposition _ _).
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  by exists lsto; [subset_tac | rewrite /contains_point' palstol -lstheq].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
have [fc'0 [lelsto _]] :=
   last_step_situation oe pxhere eonlsthe ebelow.
rewrite oe fc'0 lelsto cats0=> oe'.
rewrite /generic_trajectories.update_open_cell_top.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
have lstok : open_cell_side_limit_ok lsto by apply: (allP open_side_limit).
have slpts : (1 < size (left_pts lsto))%N.
  by apply: size_left_lsto=> //; rewrite -lstheq.
have [pal puh vle vhe ncont] :=
    decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
case ogq : (outgoing e) => [ | fog ogs]; rewrite -?ogq; last first.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  have ognn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vhe ognn oute.
    by rewrite oca_eq.
  have := step_keeps_open_side_limit_default; rewrite /open oe' oca_eq.
  rewrite /state_open_seq -!catA /= !all_cat /= !all_cat=> /andP[] ->.
  move=> /andP[] _ -> /=; rewrite andbT.
  rewrite /open_cell_side_limit_ok /set_left_pts /=.
  move: lstok=> /andP[].
  rewrite pxhere lstxq /left_limit.
  case lptsq: (left_pts lsto) slpts=> [// | p1 [ // | p2 ps]] _ _ /=.
  move=> /andP[] /andP[] _ /[dup] /andP[] x2q _ ->.
  move=> /andP[] /andP[] + -> /andP[] _.
  have := opening_cells_seq_edge_shift oute' vlo vhe oca_eq.
  rewrite eqxx /= => -[] <- _.
  move=> _ ->.
  have := lex_left_limit; rewrite lptsq /= => /andP[] + _.
  rewrite /lexPt lt_neqAle pxhere lstxq /left_limit lptsq /= x2q /= => ->.
  have /oute/eqP <- : high fno \in outgoing e.
    have := opening_cells_aux_high vlo vhe oute'; rewrite oca_eq /=.
    by rewrite -(mem_sort (@edge_below _))=> <-; rewrite inE eqxx.
  by rewrite !andbT /=; apply: left_on_edge.
(* Finished the case where there are some elements in outgoing e *)
rewrite /state_open_seq/= !cats0.
rewrite all_cat /=.
move: (open_side_limit); rewrite /open ocd !all_cat /=.
move=> /andP[] -> /andP[] _ /andP[] _ ->; rewrite /= ?andbT.
case lptsq : (left_pts lsto) slpts => [ | p1 [ | p2 lpts]] // _.
rewrite /open_cell_side_limit_ok /=.
have pxe : p_x (point e) = p_x (last p2 lpts).
  by rewrite pxhere lstxq /left_limit lptsq /=.
rewrite pxe eqxx /=.
move: (lstok); rewrite /open_cell_side_limit_ok /left_limit lptsq /=.
move=> /andP[] /andP[] /[dup] /eqP p1x -> /andP[] -> ->.
move=> /andP[] /andP[] -> -> /andP[] p1on ->.
rewrite /= !andbT.
have p1e : p1 = (point e).
  have /eqP samex : p_x (point e) = p_x p1.
    by have := pxhere; rewrite lstxq /left_limit lptsq /= p1x.
  have /eqP samey : p_y (point e) = p_y p1.
    have eonlsthe' : point e === high lsto.
      by apply: under_above_on=> //; rewrite -lstheq // ?underW.
    by have /eqP := on_edge_same_point eonlsthe' p1on samex.
  by apply/esym/(@eqP [eqType of pt]); rewrite pt_eqE samex samey.
rewrite p1e /generic_trajectories.pvert_y subrr -strict_under_pvert_y //.
by rewrite puh -pxe pvert_on.
Qed.

Lemma disjoint_open : {in open &, disjoint_open_cells R}.
Proof.
by apply: disoc=> //; have := pwo; rewrite /= => /andP[].
Qed.

Lemma step_keeps_open_disjoint :
  {in state_open_seq (step (Bscan fop lsto lop cls lstc lsthe lstx) e) &,
     disjoint_open_cells R}.
Proof.
have := step_keeps_invariant1; rewrite /invariant1/inv1_seq. 
set s' := (state_open_seq _) => -[clae' [sval' [adj' [cbtom' srf']]]].
have := step_keeps_pw; rewrite -/s' => /= /andP[] _ pw'.
have := step_keeps_open_side_limit; rewrite -/s'=> ok'.
apply: disoc=>//.
Qed.

Section arbitrary_closed.

Variable old_closed : seq cell.

Hypothesis disjoint_open_old_closed :
  {in open & old_closed, disjoint_open_closed_cells R}.

Hypothesis disjoint_old_closed : {in old_closed &, disjoint_closed_cells R}.
Hypothesis old_closed_right_limit :
  {in old_closed, forall c, right_limit c <= p_x (point e)}.

Lemma step_keeps_disjoint_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
    let closed := closing_cells (point e) cc in
     let last_closed := close_cell (point e) lcc in
     let closed_cells := old_closed ++ rcons closed last_closed in
  {in closed_cells &, disjoint_closed_cells R} /\
  {in fc ++ nos ++ lno :: lc & closed_cells,
    disjoint_open_closed_cells R}.
Proof.
case oe : (open_cells_decomposition open (point e)) =>
   [[[[[fc  cc] lcc] lc] le] he].
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct
     [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe ncont]
 := connect_properties cbtom adj rfo sval bet_e ocd all_nct all_ct
  lcc_ctn flcnct.
have allcont : all (contains_point (point e)) (rcons cc lcc).
  by rewrite -cats1 all_cat /= lcc_ctn !andbT; apply/allP.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move=> closed last_closed closed_cells.
have svalcc : seq_valid (rcons cc lcc) (point e).
   apply/allP=> c cin; apply: (allP sval); rewrite ocd !mem_cat.
   move: cin; rewrite mem_rcons inE.
   by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
have adjcc : adjacent_cells (rcons cc lcc).
  by move: adj; rewrite ocd -cat_rcons =>/adjacent_catW[] _ /adjacent_catW[].
have rfocc : s_right_form (rcons cc lcc).
   apply/allP=> c cin; apply: (allP rfo); rewrite ocd !mem_cat.
   move: cin; rewrite mem_rcons inE.
   by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
have closed_map : closing_cells (point e) (rcons cc lcc) =
       rcons [seq close_cell (point e) c | c <- cc]
          (close_cell (point e) lcc).
  by rewrite /closing_cells map_rcons.
have ccok : all open_cell_side_limit_ok (rcons cc lcc).
    apply/allP=> c cin; apply: (allP open_side_limit); rewrite ocd !mem_cat.
  move: cin; rewrite mem_rcons inE.
   by move=> /orP[/eqP |] ->; rewrite ?inE ?eqxx ?orbT //.
have := closing_cells_side_limit' rfocc svalcc adjcc ccok allcont.
rewrite head_rcons pal last_rcons puh=> /(_ isT isT).
rewrite [X in all _ X]closed_map=> /allP cl_sok.
have oldcl_newcl :
  {in old_closed & closing_cells (point e) (rcons cc lcc),
     disjoint_closed_cells R}.
  move=> c1 c2 c1in; rewrite closed_map -map_rcons=> /mapP[c2' c2'in c2eq].
  have c2'open : c2' \in open.
    by rewrite ocd -cat_rcons !mem_cat c2'in !orbT.
    have vc2 : valid_cell c2' (point e) by apply/andP/(allP sval).
  right; rewrite /c_disjoint=> q; apply/negP=> /andP[inc1 inc2].
  rewrite c2eq in inc2.
   case/negP:(disjoint_open_old_closed c2'open c1in q).
   rewrite inc1 andbT.
  apply:(close'_subset_contact vc2 _ inc2).
  by move: (cl_sok c2); rewrite c2eq; apply; rewrite -map_rcons; apply: map_f.
split.
  move=> c1 c2; rewrite !mem_cat.
  move=> /orP[c1old | c1new] /orP[c2old | c2new].
         by apply: disjoint_old_closed.
      by apply: oldcl_newcl; rewrite // closed_map.
    apply: c_disjoint_eC; apply: oldcl_newcl; first by [].
    by rewrite closed_map.
  rewrite -map_rcons in c1new c2new.
  move: c1new c2new => /mapP[c1' c1'in c1eq] /mapP[c2' c2'in c2eq].
  have c1'open : c1' \in open by rewrite ocd -cat_rcons !mem_cat c1'in orbT.
  have c2'open : c2' \in open by rewrite ocd -cat_rcons !mem_cat c2'in orbT.
  have vc1 : valid_cell c1' (point e) by apply/andP/(allP sval).
  have vc2 : valid_cell c2' (point e) by apply/andP/(allP sval).
  have [/eqP c1c2 | c1nc2] := boolP(c1' == c2').
    by left; rewrite c1eq c2eq c1c2.
  right=> q; apply/negP=> /andP[inc1 inc2].
  case: (disjoint_open c1'open c2'open)=> [/eqP | /(_ q)]. 
    by rewrite (negbTE c1nc2).
  move=> /negP[].
  rewrite c1eq in inc1; rewrite c2eq in inc2.
  rewrite (close'_subset_contact vc1 _ inc1); last first.
    by apply: cl_sok; rewrite -map_rcons; apply: map_f.
  rewrite (close'_subset_contact vc2 _ inc2) //.
  by apply: cl_sok; rewrite -map_rcons; apply: map_f.
rewrite -leq in vle; rewrite -heq in vhe.
move=> c1 c2; rewrite -cat_rcons 2!mem_cat orbCA=> /orP[c1newo |c1old] c2in.
  have rlc2 : right_limit c2 <= p_x (point e).
    move: c2in; rewrite /closed_cells mem_cat.
    move=> /orP[/old_closed_right_limit // |].
    rewrite -map_rcons=> /mapP[c2' c2'in ->].
    by rewrite close_cell_right_limit //; apply/andP/(allP svalcc).
  move=> q; rewrite inside_open'E inside_closed'E; apply/negP.
  move=> /andP[] /andP[] _ /andP[] _ /andP[] + _
     /andP[] _ /andP[] _ /andP[] _ +.
  have := opening_cells_left oute vle vhe.
  rewrite /opening_cells oca_eq=> /(_ _ c1newo) => -> peq qrlc2.
  by move: rlc2; rewrite leNgt=>/negP[]; apply: (lt_le_trans peq).
have c1open : c1 \in open by rewrite ocd -cat_rcons !mem_cat orbCA c1old orbT.
move: c2in; rewrite /closed_cells mem_cat=>/orP[c2old |].
  by apply: disjoint_open_old_closed.
rewrite -map_rcons=> /mapP[c2' c2'in c2eq] q; apply/negP=> /andP[] inc1 inc2.
have c2'open : c2' \in open by rewrite ocd -cat_rcons !mem_cat c2'in !orbT.
have [c1eqc2 | disjc1c2] := disjoint_open c1open c2'open.
  case (negP (ncont _ c1old)).
  rewrite c1eqc2.
  by move: c2'in; rewrite mem_rcons inE=> /orP[/eqP -> | /all_ct].
move: (disjc1c2 q); rewrite inc1 //=.
have vc2 : valid_cell c2' (point e) by apply/andP/(allP sval).
rewrite c2eq in inc2.
rewrite (close'_subset_contact vc2 _ inc2) //.
by apply: cl_sok; rewrite -map_rcons; apply: map_f.
Qed.

End arbitrary_closed.

Lemma bottom_edge_below : {in cell_edges open, forall g, bottom <| g}.
Proof.
move: pwo=> /= /andP[] /allP pwo' _ g.
rewrite (cell_edges_sub_high cbtom adj) inE=> /orP[/eqP -> | /pwo' //].
by apply: edge_below_refl.
Qed.

Definition state_closed_seq (s : scan_state) := 
  rcons (sc_closed s) (lst_closed s).

Lemma adjacent_update_open_cell new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  low lsto = low (head dummy_cell (rcons new_op new_lsto)) /\
  high lsto = high (last dummy_cell (rcons new_op new_lsto)) /\
  adjacent_cells (rcons new_op new_lsto).
Proof.
rewrite /update_open_cell/generic_trajectories.update_open_cell.
case o_eq : (outgoing e) => [ | g os].
  by move=> [] <- <- /=.
rewrite -o_eq.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [[ // | fno nos] lno] [] <- <-.
  have onn : outgoing e != [::] by rewrite o_eq.
  by have := opening_cells_aux_absurd_case vlo vho onn oute; rewrite oca_eq.
rewrite /= last_rcons.
have [/= A ->] := adjacent_opening_aux vlo vho oute' oca_eq.
split;[ | split]=> //=.
  have := opening_cells_aux_high_last vlo vho oute'.
  by rewrite oca_eq /=.
by move: A; case : (nos).
Qed.

Lemma low_all_edges c evs: c \in open -> low c \in all_edges open evs.
Proof. by move=> cin; rewrite !mem_cat map_f ?orbT. Qed.

Lemma high_all_edges c evs: c \in open -> high c \in all_edges open evs.
Proof. by move=> cin; rewrite !mem_cat map_f ?orbT. Qed.

Lemma update_open_cell_right_form  new_op new_lsto:
  update_open_cell lsto e = (new_op, new_lsto) ->
  point e <<< high lsto ->
  point e >>> low lsto ->
  s_right_form (rcons new_op new_lsto).
Proof.
move=> + puho palo.
have noco : below_alt (low lsto) (high lsto).
  apply: noc; first by apply: low_all_edges; rewrite /open; subset_tac.
  by apply: high_all_edges; rewrite /open; subset_tac.
have rflsto : low lsto <| high lsto.
  by apply: (edge_below_from_point_above noco vlo vho (underWC _)).
rewrite /update_open_cell/generic_trajectories.update_open_cell.
have srt : path (@edge_below _) (low lsto) (sort (@edge_below _) (outgoing e)).
  apply: (sorted_outgoing vlo vho palo puho oute).
  apply: sub_in2 noc=> x; rewrite 2!inE => /orP[/eqP ->|/orP[/eqP ->|]] //.
  by apply: subo.
case ogeq : (outgoing e) => [ | g os].
  move=> [] <- <- /=; rewrite andbT.
  by apply: (edge_below_from_point_above noco vlo vho (underWC _)).
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  move=> [] <- <- /=; rewrite andbT.
  rewrite -ogeq /= in oca_eq.
  have /= := opening_cells_aux_right_form (underWC palo)
  puho vlo vho loin hoin rflsto oute' noc subo' srt oca_eq.
  by rewrite andbT.
move=> [] <- <- /=.
rewrite -ogeq /= in oca_eq.
by have /= := opening_cells_aux_right_form (underWC palo)
puho vlo vho loin hoin rflsto oute' noc subo' srt oca_eq.
Qed.

Lemma update_open_cell_end_edge new_op new_lsto :
  end_edge_ext bottom top (low lsto) future_events ->
  end_edge_ext bottom top (high lsto) future_events ->
  valid_edge (low lsto) (point e) ->
  valid_edge (high lsto) (point e) ->
  update_open_cell lsto e = (new_op, new_lsto) ->
  {in rcons new_op new_lsto, forall x,
    end_edge_ext bottom top (low x) future_events &&
    end_edge_ext bottom top (high x) future_events}.
Proof.
move=> endl endh vl vh.
rewrite /update_open_cell/generic_trajectories.update_open_cell.
case ogeq : (outgoing e) => [ | fog ogs].
  move=> [] <- <- /= x; rewrite inE=> /eqP -> /=.
  by rewrite endl endh.
move: cle; rewrite /= => /andP[] cloe _.
have cllsto := opening_cells_close vl vh oute endl endh cloe => {cloe}.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
  have onn : outgoing e != [::] by rewrite ogeq.
  have := opening_cells_aux_absurd_case vlo vho onn oute.
  by rewrite ogeq oca_eq.
move=> -[] <- <- /= x; rewrite inE=> /orP[/eqP -> | xin].
  by rewrite /=; apply: (allP cllsto); rewrite /opening_cells ogeq oca_eq /=;
   subset_tac.
by apply: (allP cllsto); rewrite /opening_cells ogeq oca_eq /= inE xin orbT.
Qed.

Lemma update_open_cell_end_edge' c nos lno :
  valid_edge (low c) (point e) ->
  valid_edge (high c) (point e) ->
  update_open_cell c e = (nos, lno) ->
  close_alive_edges (rcons nos lno) future_events =
  close_alive_edges (opening_cells (point e) (outgoing e)
      (low c) (high c)) future_events.
Proof.
move=> vlc vhc; rewrite /update_open_cell/generic_trajectories.update_open_cell.
case ogeq : (outgoing e) => [ | fog ogs].
  move=> -[] <- <- /=.
  rewrite /opening_cells /=.
  rewrite -/(vertical_intersection_point _ _) /= pvertE //.
  by rewrite -/(vertical_intersection_point _ _) pvertE.
rewrite /opening_cells /=.
have onn : outgoing e != [::] by rewrite ogeq.
have := opening_cells_aux_absurd_case vlc vhc onn oute; rewrite ogeq.
rewrite -/(opening_cells_aux _ _ _ _).
by case oca_eq : (opening_cells_aux _ _ _ _) => [[ | ? ?] ?] + [] <- <- /=.
Qed.

Lemma update_open_cell_valid c nos lno :
  valid_edge (low c) (point e) ->
  valid_edge (high c) (point e) ->
  update_open_cell c e = (nos, lno) ->
  seq_valid (rcons nos lno) p = 
  seq_valid (opening_cells (point e) (outgoing e) (low c) (high c)) p.
Proof.
move=> vlc vhc; rewrite /update_open_cell/generic_trajectories.update_open_cell.
case ogeq : (outgoing e) => [ | fog ogs].
  move=> -[] <- <- /=.
  rewrite /opening_cells /= -/(vertical_intersection_point _ _) pvertE //.
  by rewrite -/(vertical_intersection_point _ _) pvertE.
rewrite /opening_cells /=.
have onn : outgoing e != [::] by rewrite ogeq.
have := opening_cells_aux_absurd_case vlc vhc onn oute; rewrite ogeq.
rewrite -/(opening_cells_aux _ _ _ _).
by case oca_eq : (opening_cells_aux _ _ _ _) => [[ | ? ?] ?] + [] <- <- /=.
Qed.

Lemma lex_left_pts_inf' :
  let '(fc, _, _, lc, le, he) :=
    open_cells_decomposition open (point e) in
  let '(nos, lno) :=
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he in
    {in fc ++ nos ++ lno :: lc,
      forall c, lexePt  (bottom_left_corner c) (point e)}.
Proof.
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have [ocd [_ [_ [_ [_ [leq [heq [lein hein]]]]]]]]:=
  decomposition_main_properties oe exi.
have [pal puh vle vhe A']:= decomposition_connect_properties rfo sval adj cbtom
  bet_e oe.
have sublehe : {subset rcons (le :: sort (@edge_below _) (outgoing e)) he <=
                  all_edges open (e :: future_events)}.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> | ].
    by rewrite /all_edges; subset_tac.
  rewrite inE=> /orP[/eqP -> | ].
    by rewrite /all_edges; subset_tac.
  by apply: subo'.
have noc2:
   {in rcons (le :: sort (@edge_below _) (outgoing e)) he &, no_crossing R}.
  by move=> x y xin yin; apply: noc; apply: sublehe.
move=> x; rewrite !(mem_cat, inE) => /orP[xfc | ].
  by apply: lexPtW; apply: btom_left_corners; rewrite ocd; subset_tac.
rewrite orbA=> /orP[xin | xlc]; last first.
  apply: lexPtW.
  apply: btom_left_corners; rewrite ocd; subset_tac.
have noclh : below_alt le he.
  by apply: noc2; rewrite ?(mem_rcons, inE) eqxx ?orbT.
have lebhe : le <| he.
  apply: (edge_below_from_point_above noclh vle vhe (underWC pal) puh).
have := opening_cells_last_lexePt oute (underWC pal) puh vle vhe noc2 lebhe.
rewrite /opening_cells oca_eq; apply.
by rewrite mem_rcons inE orbC.
Qed.

Lemma step_keeps_btom_left_corners_default q :
  lexPt (point e) q ->
  let '(fc, _, _, lc, le, he) :=
    open_cells_decomposition open (point e) in
  let '(nos, lno) :=
    opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he in
    {in fc ++ nos ++ lno :: lc, forall c, lexPt  (bottom_left_corner c) q}.
Proof.
move=> lexq.  
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
case oca_eq: (opening_cells_aux _ _ _ _) => [nos lno].
have := lex_left_pts_inf'; rewrite oe oca_eq => main.
by move=> x xin; apply: lexePt_lexPt_trans lexq; apply: main.
Qed.

Lemma leftmost_points_max :
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  left_limit (start_open_cell bottom top) =
  max (p_x (left_pt bottom)) (p_x (left_pt top)).
Proof.
rewrite /start_open_cell/generic_trajectories.start_open_cell /leftmost_points => /andP[] /=.
rewrite R_ltb_lt.
case: ltrP => cmpl.
  rewrite -/(vertical_intersection_point _ _).
  case peq: (vertical_intersection_point (left_pt top) bottom) => [p' | //].
  move=> _ /andP[] samex _ /=.
  move: peq.
  rewrite /vertical_intersection_point/generic_trajectories.vertical_intersection_point.
  by case: ifP=> // ve [] <-.
rewrite -/(vertical_intersection_point _ _).
case peq: (vertical_intersection_point (left_pt bottom) top)=> [p' | //] _.
by case: ifP=> [/eqP A | B]; move=> /andP[].
Qed.

Lemma trial1 c1 c2 :
  below_alt (high c1) (low c2) ->
  open_cell_side_limit_ok c1 ->
  open_cell_side_limit_ok c2 ->
  valid_edge (high c1) (point e) ->
  valid_edge (low c2) (point e) ->
  pvert_y (point e) (high c1) < pvert_y (point e) (low c2) ->
  o_disjoint c1 c2.
Proof.
move=> noc12 ok1 ok2 vhc1 vlc2 cmpc1c2 q; apply/andP=>-[].
move=> /andP[]inc1 _ /andP[] inc2 /andP[] str2 _.
have /andP[_ vhc1q] := inside_open_cell_valid ok1 inc1.
have /andP[vlc2q _] := inside_open_cell_valid ok2 inc2.
move: (inc1)=> /andP[] /andP[] _ qh1 _.
have := transport_above_edge noc12 vhc1 vlc2 vhc1q vlc2q cmpc1c2 str2.
rewrite /point_under_edge.
by rewrite qh1.
Qed.

Lemma trial2 c1 c2 :
  high c1 <| low c2 ->
  open_cell_side_limit_ok c1 ->
  open_cell_side_limit_ok c2 ->
  valid_edge (high c1) (point e) ->
  valid_edge (low c2) (point e) ->
  o_disjoint c1 c2.
Proof.
move=> c1bc2 ok1 ok2 v1 v2 q; apply/negP=> /andP[].
move=>/andP[] /andP[] /andP[] _ qbh1 /andP[] _ inx /andP[] _ stricterx.
have inx' : left_limit c1 < p_x q <= open_limit c1.
  by rewrite stricterx inx.
move: inx' {inx stricterx} => /(valid_high_limits ok1) vqhc1.
move=>/andP[] /andP[] _ /andP[] _ inx /andP[] qalc2 stricterx.
have inx' : left_limit c2 < p_x q <= open_limit c2.
  by rewrite stricterx inx.
move: inx' {inx stricterx} => /(valid_low_limits ok2) vqlc2.
rewrite (under_pvert_y vqlc2) -ltNge in qalc2.
rewrite -/(point_under_edge _ _) in qbh1.
rewrite (under_pvert_y vqhc1) in qbh1.
have /pvert_y_edge_below : pvert_y q (low c2) < pvert_y q (high c1).
  by apply: (lt_le_trans qalc2 qbh1).
by move=> /(_ vqlc2 vqhc1) /negP; apply.
Qed.

Lemma lexPt_left_pt_strict_under_edge_to_p_x (pt : pt) g:
  valid_edge g pt -> lexPt (left_pt g) pt -> pt <<< g ->
  p_x (left_pt g) < p_x pt.
Proof.
move=> vg.
rewrite /lexPt eq_sym=> /orP[ | /andP[] samex]; first by [].
have := same_pvert_y vg samex.
rewrite (on_pvert (left_on_edge g))=> <-.
rewrite ltNge le_eqVlt negb_or andbC.
by move=> /[swap]; rewrite strict_under_pvert_y // => ->.
Qed.

Lemma pvert_y_right_pt (g : edge) : pvert_y (right_pt g) g = p_y (right_pt g).
Proof. apply/on_pvert/right_on_edge. Qed.

Lemma inside_box_sorted_le :
  sorted <=%R [seq pvert_y (point e) (high c) | c <- extra_bot :: open].
Proof.
have adj' : adjacent_cells (extra_bot :: open).
  rewrite /=; move: cbtom=> /andP[] /andP[]; case: (open) adj => // o1 os + _.
  by move=> /= -> /eqP ->; rewrite eqxx.
apply adjacent_right_form_sorted_le_y => //=.
  rewrite andbb; apply/andP; split=> //.
  by apply: (inside_box_valid_bottom_top inbox_e)=> //; rewrite inE eqxx.
by rewrite edge_below_refl.
Qed.

Lemma head_cat [T : eqType] (s1 s2 : seq T) (a : T):
   s1 != nil -> head a (s1 ++ s2) = head a s1.
Proof. by case : s1 => [ | b s1]. Qed.

(* This is not used, just now. *)
Lemma left_limit_closing_cells (cc : seq cell) (p1 : pt) :
  adjacent_cells cc -> seq_valid cc p1 ->
  p1 >>> low (head_cell cc) -> p1 <<< high (last_cell cc) ->
  all (contains_point p1) cc ->
  [seq left_limit i | i <- closing_cells p1 cc] = [seq left_limit i | i <- cc].
Proof.
move=> adjcc svalcc pale puhe allcont.
rewrite /closing_cells.
rewrite -map_comp; rewrite -eq_in_map /close_cell => -[] ls rs lo hi cin /=.
move: (allP svalcc _ cin) => /= /andP[] vloc vhic.
by rewrite (pvertE vloc) (pvertE vhic).
Qed.

Definition set_right_pts (c : cell) (l : seq pt) :=
  Bcell (left_pts c) l (low c) (high c).

Lemma inside_closed_set_right_pts (c : cell) l q:
  last dummy_pt (right_pts c) = last dummy_pt l ->
  inside_closed' q c = inside_closed' q (set_right_pts c l).
Proof.
rewrite /inside_closed' /set_right_pts /inside_closed_cell /contains_point /=.
by rewrite /right_limit /= => ->.
Qed.

Lemma inside_closed'_update q1 q:
  inside_closed' q lstc = inside_closed' q (update_closed_cell lstc q1).
Proof.
have samer : last dummy_pt (right_pts lstc) =
             last dummy_pt (belast (head dummy_pt (right_pts lstc))
                             (behead (right_pts lstc)) ++
                           [:: q1; last dummy_pt (right_pts lstc)]).
  move: non_empty_right.
  elim/last_ind : (right_pts lstc) => [ // | rpts lr _] _ /=.
  by rewrite !last_cat /=.
rewrite /update_closed_cell.
have := inside_closed_set_right_pts q samer.
rewrite /set_right_pts /=.
by rewrite /set_right_pts /= => <- //.
Qed.

Lemma update_open_cellE1 c c1 :
 valid_edge (low c) (point e) ->
 valid_edge (high c) (point e) ->
 open_cell_side_limit_ok c ->
 p_x (point e) = left_limit c ->
 (1 < size (left_pts c))%N ->
 point e >>> low c ->
 point e <<< high c ->
 c1 \in (update_open_cell c e).1 ->
 exists2 c', c' \in (opening_cells_aux (point e) 
                        (sort (@edge_below _) (outgoing e)) (low c)
    (high c)).1 &
     c1 = c' \/
     exists2 l, last dummy_pt l = last dummy_pt (left_pts c') &
     c1 = set_left_pts c' l.
Proof.
move=> vle vhe cok xcond sl pal puh.
rewrite /update_open_cell/generic_trajectories.update_open_cell.
case ogq : (outgoing e) => [ | fog ogs] //=.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [ [// | fno nos] lno] /=.
rewrite inE => /orP[/eqP -> | ].
  exists fno; first by rewrite inE eqxx.
  right; exists (point e :: behead (left_pts c)).
    case lptsq : (left_pts c) sl => [ // | p1 [ // | p2 lpts]] _ /=.
    move: cok; rewrite /open_cell_side_limit_ok=> /andP[] _ /andP[] allx.
    move=> /andP[] _ /andP[] _; rewrite lptsq /=.
    have oute2 : {in (fog :: ogs),
        forall g, left_pt g == point e}.
      by rewrite -ogq; exact oute.
    have oute3 : {in sort (@edge_below _) (fog :: ogs),
        forall g, left_pt g == point e}.
      by move=> g; rewrite mem_sort; apply: oute2.
    have := opening_cells_side_limit vle vhe (underWC pal) puh oute2.
    rewrite /opening_cells oca_eq=> /allP /(_ fno).
    rewrite inE eqxx=> /(_ isT)=> /andP[] _ /andP[] _ /andP[] _ /andP[] _.
    have := opening_cells_first_left_pts (high c) vle _ pal.
    rewrite ogq oca_eq => /(_ isT) /= -> /=.
    have [_ /= ] := adjacent_opening_aux vle vhe oute3 oca_eq => ->.
    rewrite /=.
    move=> /on_edge_same_point /[apply] /=.
    rewrite xcond /left_limit lptsq /= eqxx => /(_ isT) /eqP ->.
    by apply/(@eqP [eqType of pt]); rewrite pt_eqE /= !eqxx.
  by [].
move=> c1in; exists c1; first by rewrite inE c1in orbT.
by left.
Qed.

Lemma update_open_cellE2 c :
 valid_edge (low c) (point e) ->
 valid_edge (high c) (point e) ->
 open_cell_side_limit_ok c ->
 p_x (point e) = left_limit c ->
 (1 < size (left_pts c))%N ->
 point e >>> low c ->
 point e <<< high c ->
 (update_open_cell c e).2 =
 (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) (low c)
    (high c)).2 \/
  (update_open_cell c e).2 =
  (set_left_pts c (head dummy_pt
       (left_pts c) :: point e :: behead (left_pts c))).
Proof.
move=> vle vhe cok xcond sl pal puh.
rewrite /update_open_cell/generic_trajectories.update_open_cell.
case ogq : (outgoing e)=> [ | fog ogs]; first by right.
left; rewrite -ogq.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos] lno] //=.
have ognn : outgoing e != [::] by rewrite ogq.
have := opening_cells_aux_absurd_case vle vhe ognn oute.
by rewrite oca_eq.
Qed.

Lemma inside_open'_set_pts (c : cell) l1 l2 q :
   last dummy_pt l1 = last dummy_pt (left_pts c) ->
   inside_open' q c = inside_open' q (set_pts c l1 l2).
Proof.
move=> same_lim.
rewrite /inside_open' /inside_open_cell /contains_point /left_limit /=.
by rewrite same_lim.
Qed.

Lemma oc_disjoint_set_left_pts c1 c2 l :
  last dummy_pt l = last dummy_pt (left_pts c1) ->
  oc_disjoint c1 c2 ->
  oc_disjoint (set_left_pts c1 l) c2.
Proof.
move=> eql ref q.
rewrite -inside_open'_set_pts; last by apply/esym.
exact: (ref q).
Qed.

Let step_keeps_disjoint_default' :=
  step_keeps_disjoint_default disjoint_open_closed disjoint_closed
  closed_right_limit.

Lemma appE {T : Type} (l1 l2 : seq T) : app l1 l2 = cat l1 l2.
Proof. by elim: l1 => [ | a l1 /= ->]. Qed.

Lemma step_keeps_disjoint :
  let s' := step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  {in state_closed_seq  s' &, disjoint_closed_cells R} /\
  {in state_open_seq s' & state_closed_seq s',
    disjoint_open_closed_cells R}.
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP=> [pxaway |/negbFE/eqP /[dup] pxhere /abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition open (point e)) =>
     [[[[[fc  cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_closed_seq /state_open_seq /=.
  rewrite -[X in rcons X _]cat_rcons rcons_cat /=.
  have := step_keeps_disjoint_default'; rewrite oe oca_eq /=.
  move=> [] A B; split;[apply: A | ].
  by rewrite -catA; apply: B.
case: ifP=> [eabove | ebelow].
rewrite -/(open_cells_decomposition _ _).
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  rewrite /state_open_seq /state_closed_seq /= rcons_cat.
  rewrite !appE.
  rewrite -(cat_rcons lsto) -catA -(cat_rcons lno).
  have := step_keeps_disjoint_default'.
  by rewrite oe' oca_eq /= -(cat_rcons lno) -(cat_rcons lstc).
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite -/(open_cells_decomposition _ _).
  have oe : open_cells_decomposition open (point e) =
          (fop, [::], lsto, lop, low lsto, high lsto).
    by rewrite open_cells_decomposition_single=> //; rewrite -lstheq.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  rewrite /state_open_seq /state_closed_seq /=.
  rewrite -/(update_open_cell _ _).
  case uoc_eq : (update_open_cell lsto e) => [nos lno] /=.
  split.
    have lstcn : lstc \notin cls.
      by move: uniq_closed; rewrite rcons_uniq=> /andP[].
    have lstcin : lstc \in rcons cls lstc by rewrite mem_rcons inE eqxx.
    have in' c : c \in cls -> c \in rcons cls lstc.
      by move=> cin; rewrite mem_rcons inE cin orbT.
    have main c1 q: 
         c_disjoint c1 lstc -> 
         c_disjoint c1 (update_closed_cell lstc q).
      by move=> /[swap] q1 /(_ q1); rewrite -inside_closed'_update.
    move=> c1 c2; rewrite !mem_rcons !inE !(orbC _ (_ \in cls)).
    move=>/orP[c1in | /eqP ->] /orP[c2in | /eqP ->]; last by left.
        by apply: disjoint_closed; rewrite mem_rcons inE ?c1in ?c2in orbT.
      right; apply: main; case: (disjoint_closed (in' _ c1in) lstcin)=> //.
      by move: lstcn=> /[swap] <-; rewrite c1in.
    apply: c_disjoint_eC; right; apply: main.
    case: (disjoint_closed (in' _ c2in) lstcin)=> //.
    by move: lstcn=> /[swap] <-; rewrite c2in.
  have main c : 
     oc_disjoint c lstc ->
     oc_disjoint c (update_closed_cell lstc (point e)).
    by rewrite /oc_disjoint=> /[swap] q /(_ q); rewrite -inside_closed'_update.
  have := step_keeps_disjoint_default'.
  have lstok : open_cell_side_limit_ok lsto.
    by apply: (allP open_side_limit); rewrite /open mem_cat /= inE eqxx orbT.
  have pxo : p_x (point e) = left_limit lsto by rewrite -lstxq.
  have slpts : (1 < size (left_pts lsto))%N.
    by apply: size_left_lsto=> //; rewrite -lstheq; apply: underW.
  have puh : point e <<< high lsto by rewrite -lstheq.
  have := update_open_cellE1 vlo vho lstok pxo slpts palstol puh.
  rewrite uoc_eq /=.
  have := update_open_cellE2 vlo vho lstok pxo slpts palstol puh.
  rewrite uoc_eq /=.
  rewrite oe.  
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos' lno'] /= helper2 helper1.
  move=> [] _ helper3.
  move=> c1 c2 c1in; rewrite mem_rcons inE => /orP[/eqP -> | ].
    apply: main.
    move: c1in; rewrite -!catA /= mem_cat=> /orP[c1f |].
      apply: disjoint_open_closed; last by rewrite mem_rcons inE eqxx.
      by rewrite /open mem_cat c1f.
    rewrite mem_cat=> /orP[].
      move=>/helper1 [c1' c1'in]=>- [-> | ].
        by apply: helper3; rewrite !mem_cat ?mem_rcons ?c1'in ?inE ?eqxx ?orbT.
      move=>[l lq ->] q.
      suff -> : inside_open' q (set_left_pts c1' l) = inside_open' q c1'.
        by apply: (helper3 c1' lstc _ _ q);
            rewrite !mem_cat ?mem_rcons ?c1'in ?inE ?eqxx ?orbT.
      by apply/esym/inside_open'_set_pts/esym.
    rewrite inE=> /orP[/eqP -> | ].
      case: helper2=> [ -> | -> ].
        by apply: helper3; rewrite !mem_cat ?mem_rcons !inE !eqxx ?orbT.
      set W := (set_left_pts _ _).    
      move=> q.
      suff -> : inside_open' q W = inside_open' q lsto.
        by apply: disjoint_open_closed;
         rewrite ?mem_rcons ?mem_cat /= ?inE ?eqxx ?orbT.
      apply/esym/inside_open'_set_pts.
      have := size_left_lsto pxhere palstol (underW puh).
      by case : (left_pts lsto) => [ | p1 [ | p2 lpts]].
    move=> c1f.
    by apply: disjoint_open_closed;
         rewrite ?mem_cat ?mem_rcons ?inE ?c1f ?eqxx ?orbT.
  move=> c2in.
  move: c1in; rewrite -catA !mem_cat /= => /orP[c1f |].
    by apply: disjoint_open_closed;
       rewrite ?mem_cat ?mem_rcons ?inE ?c1f ?eqxx ?c2in ?orbT.
  move=> /orP[/helper1 [c1' c1no'] |].
    move=> [-> | [l lq -> q] ].  
      by apply: helper3; rewrite !(mem_rcons, mem_cat, inE) ?c1no' ?c2in ?orbT.
    suff -> : inside_open' q (set_left_pts c1' l) = inside_open' q c1'.
      by apply: helper3;
           rewrite !(mem_cat, inE, mem_rcons) ?c1'in ?c2in ?c1no' ?orbT.
    by apply/esym/inside_open'_set_pts/esym.
  rewrite inE=> /orP[/eqP -> | ].
    move: helper2=> [-> | ->].
      by apply: helper3; rewrite !(mem_cat, mem_rcons, inE) ?eqxx ?c2in ?orbT.
    set W := (set_left_pts _ _).    
    move=> q.
    suff -> : inside_open' q W = inside_open' q lsto.
      by apply: disjoint_open_closed;
       rewrite ?mem_rcons ?mem_cat /= ?inE ?eqxx ?c2in ?orbT.
    apply/esym/inside_open'_set_pts.
    have := size_left_lsto pxhere palstol (underW puh).
    by case : (left_pts lsto) => [ | p1 [ | p2 lpts]].
  move=> c1f.
  by apply: disjoint_open_closed;
       rewrite ?mem_cat ?mem_rcons ?inE ?c1f ?c2in ?orbT.
rewrite /generic_trajectories.update_open_cell_top.
move : ebelow eonlsthe; rewrite lstheq=> /negbFE ebelow /negP/negP eonlsthe.
have ponlsthe : point e === lsthe.
  by rewrite lstheq; apply: under_above_on.
have exi2 : exists2 c, c \in (lsto :: lop) &
          contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  by rewrite /contains_point' palstol /point_under_edge ebelow.
case ogq : (outgoing e) => [ | fog og]; last first.
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
  rewrite oe=> oe'.
  have lelow : le = low lsto.
    move: oe; rewrite /open_cells_decomposition/generic_trajectories.open_cells_decomposition /=.
    rewrite -/(contains_point _ _).
    have -> : contains_point (point e) lsto.
      by rewrite contains_pointE /point_under_edge ebelow underWC.
    rewrite -/(open_cells_decomposition_contact _ _).
    case : (open_cells_decomposition_contact _ _) => [[[a b] c] |] /=;
      by move=> [] _ _ _ _ ->.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi2.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    have ognn : outgoing e != nil by rewrite ogq.
    have:= opening_cells_aux_absurd_case vlo vhe ognn oute.
    by rewrite ogq oca_eq /=.
  rewrite /state_open_seq /state_closed_seq /=.
  have := step_keeps_disjoint_default'; rewrite oe' ogq lelow oca_eq /=.
  move=> [] clsdisj ocdisj.
  split.           
    move=> x y xin yin; apply: clsdisj.
      move: xin; rewrite !(mem_rcons, inE, mem_cat).
      move=>/orP[-> | /orP[ | /orP[ ->| ->]]]; rewrite ?orbT //.
      by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
    move: yin; rewrite !(mem_rcons, inE, mem_cat).
    move=>/orP[-> | /orP[ | /orP[ ->| ->]]]; rewrite ?orbT //.
    by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
  move=> x y.
  rewrite !mem_cat !inE -!orbA !(orbCA _ (_ == set_left_pts _ _)).
  move=>/orP[]; last first.
    move=> xin yin; apply: ocdisj.
      rewrite !(mem_cat, inE).
      by move: xin=> /orP[-> | /orP[-> | ->]]; rewrite ?orbT //.
    move: yin; rewrite !(mem_rcons, mem_cat, inE).
    move=>/orP[-> | /orP[ | /orP[-> | ->] ]]; rewrite ?orbT //.
    by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
  move=> /eqP -> yin.
  apply: oc_disjoint_set_left_pts; last first.
    apply: ocdisj;[subset_tac | ].
    move: yin; rewrite !(mem_cat, inE, mem_rcons).
    move=> /orP[-> | /orP[ | /orP[-> | ->]]]; rewrite ?orbT //.
    by case: (cc) => /= [// | ? ?]; rewrite !inE /= => ->; rewrite ?orbT.
  have ognn : outgoing e != nil by rewrite ogq.
  have slsto := size_left_lsto pxhere palstol ebelow.
  have:= opening_cells_first_left_pts he vlo ognn palstol.
  rewrite ogq oca_eq /= => -> /=.
  move: slsto; case lptsq : (left_pts lsto) => [// | fp [// | sp lpts]] _ /=.
  have : open_cell_side_limit_ok lsto.
    by apply: (allP open_side_limit); rewrite /open mem_cat inE eqxx orbT.
  move=> /andP[] _ /andP[] A /andP[] _ /andP[] _ onlow.
  rewrite pxhere lstxq /left_limit lptsq /=.
  apply/(@eqP [eqType of pt]); rewrite pt_eqE /= eqxx /= eq_sym; apply/eqP.
  have -> : pvert_y (point e) (low lsto) = pvert_y (last sp lpts) (low lsto).
    apply: same_pvert_y=> //.
    by rewrite pxhere lstxq /left_limit lptsq.
  by apply: on_pvert; move: onlow; rewrite lptsq.
rewrite -/(open_cells_decomposition _ _).
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe /= => oe'.
rewrite /state_closed_seq /state_open_seq /=.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
  decomposition_main_properties oe' exi.
have [pal puh vle vhe _]:=
 decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
set nlsto := (X in (_ ++ X :: lc)).
have lelow : le = low lsto.
  move: oe; rewrite /open_cells_decomposition/generic_trajectories.open_cells_decomposition /=.
  rewrite -/(contains_point _ _).
  have -> : contains_point (point e) lsto.
    by rewrite contains_pointE /point_under_edge ebelow underWC.
  rewrite -/(open_cells_decomposition_contact _ _).
  case : (open_cells_decomposition_contact _ _) => [[[a b] c] |] /=;
    by move=> [] _ _ _ _ ->.
have := step_keeps_disjoint_default'; rewrite oe' ogq lelow /=.
rewrite -/(vertical_intersection_point _ _).
rewrite pvertE // -/(vertical_intersection_point _ _) pvertE //=.
have: Bpt (p_x (point e)) (pvert_y (point e) he) == point e :>pt = false.
  apply/negP=> abs.
  move: puh; rewrite strict_under_pvert_y // -[X in p_y X](eqP abs) /=.
  by rewrite lt_irreflexive.
have: point e == Bpt (p_x (point e)) (pvert_y (point e) (low lsto)) :> pt
   = false.
  apply/negP=> abs.
  move: pal; rewrite under_pvert_y // lelow [X in p_y X](eqP abs) /=.
  by rewrite le_eqVlt eqxx.
do 2 rewrite -[pt_eqb _ _ _ _]/(_ == _ :> pt).
move=> -> -> [] clcnd clopcnd.
split.
  move=> x y xin yin; apply: clcnd.
    move: xin; rewrite !(mem_rcons, mem_cat, inE) orbCA=> /orP[]; last first.
      by move=> /orP[->| /orP[] ->]; rewrite ?orbT.
    by case: (cc) => //= a l; rewrite inE=> ->; rewrite ?orbT.
  move: yin; rewrite !(mem_rcons, mem_cat, inE) orbCA=> /orP[]; last first.
    by move=> /orP[->| /orP[] ->]; rewrite ?orbT.
  by case: (cc) => //= a l; rewrite inE=> ->; rewrite ?orbT.
rewrite cats0.
move=> x y xin yin.
have yin' : y \in cls ++ lstc :: rcons (closing_cells (point e) cc)
                            (close_cell (point e) lcc).
  move: yin; rewrite !(mem_rcons, mem_cat, inE) orbCA=> /orP[]; last first.
    by move=> /orP[-> | /orP[] ->]; rewrite ?orbT.
  by case: (cc) => //= ? ?; rewrite inE=> ->; rewrite ?orbT.
move: xin; rewrite !(mem_cat, mem_rcons, inE)=> /orP[xin | ].
  apply: clopcnd; first by rewrite !(mem_cat, mem_rcons, inE) xin.
  by rewrite cat_rcons.  
move=>/orP[/eqP -> | xin]; last first.
  apply: clopcnd.
    by rewrite !(mem_cat, mem_rcons, inE) xin !orbT.
  by rewrite cat_rcons.
move=> q.
move: clopcnd; set w := (X in _ ++ X :: _).
have nlstoq : nlsto = set_pts w                      
   (Bpt (p_x (point e)) (pvert_y (point e) he) :: left_pts lsto)
   (right_pts lsto).
   by rewrite /nlsto /generic_trajectories.pvert_y subrr.
move=> clopcnd.
rewrite nlstoq -inside_open'_set_pts.
  apply: clopcnd.
    by rewrite !(mem_cat, mem_rcons, inE) eqxx ?orbT.
  by rewrite cat_rcons.
rewrite /w /=.
have /andP[] := allP open_side_limit lsto lstoin.
case plstq : (left_pts lsto) => [ // | a l] _ /= /andP[] A /andP[] _ /andP[] _.
move: lstxq; rewrite /left_limit plstq /= => sx one.
apply/(@eqP [eqType of pt]); rewrite pt_eqE /= pxhere sx eqxx /=.
rewrite -(on_pvert one).
apply/eqP; apply: same_pvert_y; first by case/andP: one.
by rewrite pxhere sx.
Qed.

Lemma step_keeps_injective_high_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) :=
      opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
    {in fc ++ nos ++ lno :: lc &, injective high}.
Proof.
  case oe : open_cells_decomposition => [[[[[fc cc] lcc] lc] le] he].
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct
     [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe ncont]
 := connect_properties cbtom adj rfo sval bet_e ocd all_nct all_ct
  lcc_ctn flcnct.
have dupcase c1 c2 : (c1 \in fc) || (c1 \in lc) ->
   c2 \in opening_cells (point e) (outgoing e) le he ->
   high c1 = high c2 -> c1 = c2.
  move=> c1in; rewrite leq heq => c2in hc1c2.
  have v1 : valid_edge (high c1) (point e).
    move: sval=>/allP/(_ c1); rewrite ocd -cat_rcons !mem_cat orbCA c1in orbT.
    by move=> /(_ isT) /andP[].
  have v2 : valid_edge (high c2) (point e).
    have /andP[ _ ] := opening_cells_subset vle vhe oute c2in.
    rewrite inE=> /orP[/eqP -> // | ].
    by have := opening_valid oute vle vhe => /allP /(_ _ c2in) /andP[].
  have : point e <<< high c1 \/ point e >>> high c1.
    move: c1in=> /orP[] c1in.
      right.
      by have := decomposition_above_high_fc oe cbtom adj bet_e rfo sval c1in.
    left.
    have [s1 [s2 lcq]] := mem_seq_split c1in.
    case s2q : s2 => [ | c1' s2'].
      move: inbox_e=> /andP[] /andP[] _ + _.
      suff -> : high c1 = top by [].
      move: cbtom=> /andP[] _ /eqP; rewrite ocd lcq s2q /=.
      by rewrite !(last_cat, last_cons) /=.
    have c1'in : c1' \in lc by rewrite lcq s2q mem_cat !inE eqxx !orbT.
    have := decomposition_under_low_lc oe cbtom adj bet_e rfo sval c1'in.
    suff -> : high c1 = low c1' by [].
    move: adj; rewrite /adjacent_cells ocd=> /sorted_catW /andP[] _.
    move=> /sorted_catW /andP[] _; rewrite lcq s2q.
    by rewrite /= -cat_rcons cat_path last_rcons /= => /andP[] _ /andP[] /eqP.
  have /andP[lows ] := opening_cells_subset vle vhe oute c2in.
  rewrite inE => /orP[/eqP hc1he | ]; last first.
    rewrite hc1c2 => /oute/eqP <-.
    move=> [ | ].
      rewrite strict_nonAunder; last first.
        by apply valid_edge_extremities; rewrite eqxx ?orbT.
      by rewrite left_on_edge.
    rewrite under_onVstrict ?left_on_edge //.
    by apply valid_edge_extremities; rewrite eqxx ?orbT.
  have c1hec : c1 = lcc.
    apply: high_inj.
        by rewrite ocd -cat_rcons!mem_cat orbCA c1in orbT.
      by rewrite ocd !(mem_cat, inE) eqxx !orbT.
    by rewrite hc1c2.
  have := ncont _ c1in.
  by rewrite c1hec lcc_ctn.
have henout : he \notin outgoing e.
  apply/negP=> /oute /eqP abs.
  have :=
    bottom_left_lex_to_high cbtom adj rfo open_side_limit inbox_e btm_left.
  move=> /(_ lcc); rewrite ocd !(mem_cat, inE) eqxx !orbT => /(_ isT).
  by rewrite -heq abs lexPt_irrefl.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
move=> c1 c2; rewrite -cat_rcons !mem_cat orbCA=> /orP[] c1in; last first.
  rewrite orbCA=> /orP[] c2in; last first.
    by apply: high_inj;
      rewrite ocd -cat_rcons !mem_cat orbCA ?c1in ?c2in ?orbT.
  by apply: (dupcase _ c2 c1in); rewrite /opening_cells oca_eq.
rewrite orbCA=> /orP[] c2in; last first.
  move/esym=> tmp; apply/esym; move: tmp.
  by apply: (dupcase _ c1 c2in); rewrite /opening_cells oca_eq.
have : uniq (rcons (sort (@edge_below _) (outgoing e)) he).
  by rewrite rcons_uniq mem_sort henout sort_uniq.
rewrite heq -(opening_cells_high vle vhe oute) => /uniq_map_injective; apply.
all: rewrite /opening_cells -heq -leq oca_eq; by [].
Qed.

(* TODO : propose for inclusion in math-comp *)
Lemma uniq_index (T : eqType) (x : T) l1 l2 :
   uniq (l1 ++ x :: l2) -> index x (l1 ++ x :: l2) = size l1.
Proof.
elim: l1 => [/= | a l1 Ih]; first by rewrite eqxx.
rewrite /= => /andP[].
case: ifP => [/eqP -> | _ _ /Ih -> //].
by rewrite mem_cat inE eqxx orbT.
Qed.
  
Lemma index_map_in (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) :
  {in s &, injective f} ->
  {in s, forall x, index (f x) [seq f i | i <- s] = index x s}.
Proof.
elim: s => [ // | a s Ih] inj x xin /=.
case: ifP => [/eqP/inj| fanfx].
  rewrite inE eqxx; move=> /(_ isT xin) => ->.
  by rewrite eqxx.
case: ifP=> [/eqP ax | xna ]; first by rewrite ax eqxx in fanfx.
congr (_.+1).
apply: Ih=> //.
  by move=> x1 x2 x1in x2in; apply: inj; rewrite !inE ?x1in ?x2in ?orbT.
by move: xin; rewrite inE eq_sym xna.
Qed.

Lemma update_cells_injective_high l1 l2 l2' l3:
  uniq (l1 ++ l2 ++ l3) ->
  [seq high c | c <- l2] = [seq high c | c <- l2'] ->
  {in l1 ++ l2 ++ l3 &, injective high} ->
  {in l1 ++ l2' ++ l3 &, injective high}.
Proof.
move=> u2 eqh inj0 x1 x2; rewrite !mem_cat orbCA=> x1in.
rewrite orbCA=> x2in hx1x2.
move: x1in=> /orP[x1l2' | x1in]; last first.
  move: x2in=> /orP[x2l2' | x2in]; last first.
    by move: hx1x2; apply: inj0; rewrite !mem_cat orbCA ?x1in ?x2in ?orbT.
  move: u2; rewrite uniq_catCA cat_uniq=> /andP[] _ /andP[] /negP abs _.
  have : high x2 \in [seq high c | c <- l2].
    by rewrite eqh; apply: map_f.
  move=> /mapP[x20 x20in hx20].
  rewrite -hx1x2 in hx20.
  have x1x20: x1 = x20.
    by apply: inj0; rewrite // ?mem_cat orbCA ?x20in ?x1in ?orbT.
  case: abs; apply/hasP; exists x20=> //.
  by rewrite -x1x20 mem_cat.
move: x2in=> /orP[x2l2'| x2in]; last first.
  move: u2; rewrite uniq_catCA cat_uniq=> /andP[] _ /andP[] /negP abs _.
  have : high x1 \in [seq high c | c <- l2].
    by rewrite eqh; apply: map_f.
  move=> /mapP[x10 x10in hx10].
  rewrite hx1x2 in hx10.
  have x2x10: x2 = x10.
    by apply: inj0; rewrite // !mem_cat orbCA ?x10in ?x2in ?orbT.
  case: abs; apply/hasP; exists x10=> //.
  by rewrite -x2x10 mem_cat.
remember (index x1 l2') as j1 eqn:j1def.
remember (index x2 l2') as j2 eqn:j2def.
have inj2 : {in l2 &, injective high}.
  by move=> u1 {}u2 uin1 uin2; apply: inj0; rewrite !mem_cat ?uin1 ?uin2 orbT.
have ul2 : uniq l2.
  by move: u2; rewrite !cat_uniq=> /andP[] _ /andP[] _ /andP[].
have uh : uniq [seq high c | c <- l2].
  by rewrite (map_inj_in_uniq inj2).
have := nth_index dummy_cell x1l2'; rewrite -j1def => j1q.
have := nth_index dummy_cell x2l2'; rewrite -j2def => j2q.
have j1lt : (j1 < size l2')%N by rewrite j1def index_mem.
have j2lt : (j2 < size l2')%N by rewrite j2def index_mem.
have : nth (high dummy_cell) [seq high c | c <- l2'] j1 = high x1.
  by rewrite (nth_map dummy_cell) // j1q.
have : nth (high dummy_cell) [seq high c | c <- l2'] j2 = high x1.
  by rewrite hx1x2 (nth_map dummy_cell) // j2q.
move=> <-; rewrite -eqh. 
move: uh=> /uniqP => /(_ dummy_edge); rewrite [X in size X]eqh size_map.
move=> /(_ j1 j2); rewrite !inE => /(_ j1lt j2lt) /[apply].
by rewrite -j1q -j2q => ->.
Qed.

Lemma step_keeps_uniq_default fc cc lcc lc le he nos lno:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  opening_cells_aux (point e) 
      (sort (@edge_below _) (outgoing e)) le he = (nos, lno) ->
  uniq (fc ++ nos ++ lno :: lc).
Proof.
move=> oe oca_eq.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe old_nctn]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
have := opening_cells_contains_point vle vhe pal puh oute.
rewrite /opening_cells oca_eq => /(_ _ erefl)=> new_ctn.
have uo : uniq (sort (@edge_below _) (outgoing e)) by rewrite sort_uniq.
have heno : he \notin (sort (@edge_below _) (outgoing e)).
  apply/negP=> /oute'/eqP; move: puh=> /[swap] <-.
  by rewrite (negbTE (left_pt_above he)).
have uniqnew := opening_cells_aux_uniq uo heno oute' vle vhe oca_eq.
rewrite -cat_rcons uniq_catCA cat_uniq uniqnew.
move: uniq_open; rewrite ocd -cat_rcons uniq_catCA cat_uniq=> /andP[] _.
move=>/andP[] _ ->; rewrite andbT /= -all_predC /=.
apply/allP=> x /=; rewrite mem_cat=> /old_nctn nctn.
by apply/negP=> /new_ctn/nctn.
Qed.

Lemma step_keeps_injective_high :
  let s' := step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  {in state_open_seq s' &, injective high}.
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP=> [pxaway |/negbFE/eqP /[dup] pxhere /abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition open (point e)) =>
     [[[[[fc  cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_closed_seq /state_open_seq /=.
  have := step_keeps_injective_high_default; rewrite oe oca_eq /=.
  by rewrite catA.
case: ifP=> [eabove | ebelow].
rewrite -/(open_cells_decomposition _ _).
case oe : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  have oe' :
    open_cells_decomposition open (point e) =
     (rcons fop lsto ++ fc', cc, lcc, lc, le, he).
    move: adj rfo sval; rewrite /open -cat_rcons=> adj' rfo' sval'.
    move: (open_cells_decomposition_cat adj' rfo' sval' (exi' eabove)).
    by rewrite oe; apply.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi.
  have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe'.
  rewrite /state_open_seq.
  rewrite appE.
  rewrite -(cat_rcons lsto) -catA -(cat_rcons lno).
  have := step_keeps_injective_high_default.
  by rewrite oe' oca_eq /= !catA -cat_rcons.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  have oe : open_cells_decomposition open (point e) =
          (fop, [::], lsto, lop, low lsto, high lsto).
    by rewrite open_cells_decomposition_single=> //; rewrite -lstheq.
  have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  rewrite /state_open_seq /=.
  rewrite -/(update_open_cell _ _).
  case uoc_eq : (update_open_cell _ _) => [nos lno] /=.
  rewrite -catA -cat_rcons.
  move: uoc_eq; rewrite /update_open_cell/generic_trajectories.update_open_cell.
  case ogq : (outgoing e) => [ | fog ogs].
    move=> [] <- <-; rewrite [rcons _ _]/=.
    have uniqlsto : uniq (fop ++ [:: lsto] ++ lop).
      by move: uniq_open; rewrite /open.
    set w := (X in fop ++ X ++ lop).
    have samehigh: [seq high c | c <- [:: lsto]] = [seq high c | c <- w] by [].
    by apply: (update_cells_injective_high uniqlsto samehigh).
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos'] lno'].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vho ogn oute.
    by rewrite ogq oca_eq.
  move=> [] <- <-.
  have := step_keeps_injective_high_default.
  rewrite oe ogq oca_eq -cat_rcons.
  apply: update_cells_injective_high.
    have := step_keeps_uniq_default oe; rewrite ogq=> /(_ _ _ oca_eq).
    by rewrite cat_rcons catA.
  by rewrite !map_rcons.
case oe': open_cells_decomposition => [[[[[fc' cc'] lcc'] lc'] le'] he'].
have lsto_ctn : contains_point' (point e) lsto.
  rewrite /contains_point' palstol -lstheq.
  by move: ebelow=> /negbT; rewrite negbK.
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  by exists lsto; [rewrite inE eqxx | ].
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe' exi2.
rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top.
rewrite -/(open_cells_decomposition _ _) oe'.
case ogq : (outgoing e) => [ | fog ogs] /=.
  rewrite /state_open_seq /= cats0 -cat1s.
  have : {in fop ++ fc' ++ [:: lcc'] ++ lc' &, injective high}.
    have subtmp : {subset fop ++ fc' ++ lcc' :: lc' <= open}.
      move=> x; rewrite /open ocd !(mem_cat, inE).
      repeat (move=> /orP[ -> | ]; rewrite ?orbT //).
      by move=> ->; rewrite ?orbT.
    by move=> x y xin yin; apply: high_inj; apply: subtmp.
  rewrite catA.
  apply: update_cells_injective_high.
    rewrite cat_uniq; move: uniq_open; rewrite /open ocd catA.
    rewrite [X in is_true X -> _]cat_uniq=> /andP[] -> /= /andP[].
    rewrite has_cat negb_or => /andP[] _ /= => ->.
    by rewrite [X in is_true X -> _]cat_uniq => /andP[] _ /andP[] _.
  by rewrite /= heq.
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe' => oe.
have [pal puh vle vhe _]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos] lno].
  have ogn : fog :: ogs != nil by [].
  have := opening_cells_aux_absurd_case vlo vhe ogn.
  by rewrite -[X in {in X, _}]ogq oca_eq => /(_ oute).
rewrite /state_open_seq /= !catA -(catA (_ ++ _)) -cat_rcons.
have := step_keeps_injective_high_default.
rewrite oe ogq.
have le'q : le' = low lsto.
  have := last_step_situation oe' pxhere.
  rewrite -/(point_strictly_under_edge _ _) in eonlsthe.
  rewrite eonlsthe=> /(_ isT).
  move: ebelow=> /negbT.
  rewrite -/(point_under_edge _ _).
  by rewrite negbK=> -> /(_ isT)[] + [].
rewrite le'q oca_eq -cat_rcons.
apply: update_cells_injective_high=> //.
have := step_keeps_uniq_default oe; rewrite ogq le'q=> /(_ _ _ oca_eq).
by rewrite cat_rcons !catA.
Qed.

(* TODO : understand why closing_cells_to_the_left seems to use too many
   hypotheses, once out of the section. *)
Lemma closing_cells_to_the_left fc cc lcc lc le he :
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  {in closing_cells (point e) cc, forall c, right_limit c <= p_x (point e)} /\
  right_limit (close_cell (point e) lcc) <= p_x (point e).
Proof.
move=> oe.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe _]:=
  decomposition_connect_properties rfo sval adj cbtom bet_e oe.
split; last first.
  have vlolcc : valid_edge (low lcc) (point e).
    apply: (proj1 (andP (allP sval lcc _))).
    by rewrite ocd !(mem_cat, inE) eqxx ?orbT.
  rewrite /close_cell (pvertE vlolcc).
  rewrite -heq (pvertE vhe) /right_limit /=.
  by case: ifP; case: ifP.
move=> c /mapP[c' c'in ->].
have c'in2 : c' \in open by rewrite ocd !mem_cat c'in ?orbT.
have /andP[vlc vhc] := allP sval c' c'in2.
rewrite /close_cell (pvertE vlc) (pvertE vhc) /=.
by case: ifP; case: ifP.
Qed.

Lemma update_closed_cell_keeps_right_limit c pt :
  closed_cell_side_limit_ok c ->
  right_limit (update_closed_cell c pt) =
  right_limit c.
Proof.
do 5 move=> /andP[_]; move=> /andP[ptsn0 /andP[/allP allx _]].
rewrite /update_closed_cell /right_limit /=.
elim/last_ind: {-1} (right_pts c) (erefl (right_pts c))
     ptsn0=> [ // | [ // | pt0 pts] ptf _] ptsq _ /=.
  by rewrite last_cat.
Qed.

Lemma step_keeps_closed_to_the_left :
  let s' := step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  {in state_closed_seq s', forall c, right_limit c <= p_x (point e)}.
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP => [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_closed_seq /=.
  have [ccP lccP] := closing_cells_to_the_left oe.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> // | ].
  by rewrite appE -cat_rcons mem_cat => /orP[/closed_right_limit | /ccP].
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  move: adj rfo sval; rewrite /open -cat_rcons => adj' rfo' sval'.
  have := open_cells_decomposition_cat adj' rfo' sval' (exi' eabove) eabove'.
  rewrite oe' cat_rcons => oe.
  have [ccP lccP] := closing_cells_to_the_left oe.
  rewrite /state_closed_seq /=.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> // | ].
  by rewrite appE -cat_rcons mem_cat => /orP[ /closed_right_limit | /ccP].
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite -/(update_open_cell _ _).
  case uoc_eq : (update_open_cell _ _) => [nos lno].
  rewrite /state_closed_seq /=.
  move=> x; rewrite mem_rcons inE => /orP[/eqP -> | ].
    rewrite /update_closed_cell /right_limit /=.
    have := non_empty_right; case pts_eq: (right_pts lstc) => [| p1 rpts] // _.
    rewrite /= last_cat /=.
    have /closed_right_limit: lstc \in rcons cls lstc.
      by rewrite mem_rcons inE eqxx.
    by rewrite /right_limit pts_eq.
  move=> xin.
  suff /closed_right_limit : x \in rcons cls lstc by [].
  by rewrite mem_rcons inE xin orbT.
rewrite -/(open_cells_decomposition _ _).
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
rewrite -/(update_open_cell_top lsto _ e).
case uoct_eq : (update_open_cell_top lsto _ _) => [nos lno].
have exi2 : exists2 c, c \in (lsto :: lop) &
          contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  by rewrite /contains_point' palstol -lstheq /point_under_edge (negbFE ebelow).
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite -/(open_cells_decomposition _ _).
rewrite oe' => oe.
rewrite /state_closed_seq /=.
have [ccP lccP] := closing_cells_to_the_left oe.
move=> x; rewrite mem_rcons inE => /orP[/eqP ->|]; first by [].
rewrite mem_cat=> /orP[xin | ].
  have /ccP // : x \in closing_cells (point e) cc.
  by move/mapP: xin=> [] x' x'in ->; apply/map_f/mem_behead.
by rewrite -mem_rcons; apply: closed_right_limit.
Qed.

Lemma contains_right (c : cell) :
  c \in open ->  right_pt (high c) = point e -> contains_point (point e) c.
Proof.
move=> cino rq.
have /andP[vlc vhc] := allP sval c cino.
apply/andP; split; last first.
 rewrite -/(point_under_edge _ _).
  by rewrite under_onVstrict // -rq right_on_edge.
apply/negP=> abs.
have bl := allP rfo c cino.
have := order_edges_strict_viz_point vlc vhc bl abs.
by rewrite (strict_nonAunder vhc) -rq right_on_edge.
Qed.

Lemma inbox_lexePt_right_bt g pt:
  inside_box pt ->
  g \in [:: bottom; top] -> lexePt pt (right_pt g).
Proof.
rewrite !inE /inside_box /lexePt.
by move=> /andP[] _ /andP[] /andP[] _ lb /andP[] _ lt /orP[] /eqP ->;
  rewrite ?lt ?lb.
Qed.

Lemma inside_box_lexPt_bottom pt :
  inside_box pt -> lexPt (left_pt bottom) pt && lexPt pt (right_pt bottom).
Proof.
by move=> /andP[] _ /andP[] /andP[] lp pr  _; rewrite /lexPt lp pr.
Qed.

Lemma inside_box_lexPt_top pt :
  inside_box pt -> lexPt (left_pt top) pt && lexPt pt (right_pt top).
Proof.
by move=> /andP[] _ /andP[]  _ /andP[] lp pr; rewrite /lexPt lp pr.
Qed.

Lemma step_keeps_lex_edge_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) := opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
   forall e', inside_box (point e') -> lexPtEv e e' ->
               (forall e2, e2 \in future_events -> lexePtEv e' e2) ->
   {in [seq high c | c <- fc ++ nos ++ lno :: lc], forall g,
       lexPt (left_pt g) (point e') && lexePt (point e') (right_pt g)}.
Proof.
case oe : (open_cells_decomposition _ _) =>
 [[[[[fc cc] lcc] lc] le] he].
case oca_eq:(opening_cells_aux _ _ _ _) => [nos nlsto].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vl vp nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
move=> e' inbox_e' ee' e'fut g.
rewrite !map_cat !mem_cat.
have old:  (g \in [seq high c | c <- fc]) || (g \in [seq high c | c <- lc]) ->
   lexPt (left_pt g) (point e') && lexePt (point e') (right_pt g).
  move=> gin; apply/andP; split.
    have /lexPt_trans : lexPt (left_pt g) (point e).
      have /lex_open_edges /andP[] // : g \in [seq high c | c <- open].
      rewrite ocd !map_cat !mem_cat map_cons inE.
      by move: gin => /orP[ | ] ->; rewrite ?orbT.
    by apply.
  have /mapP [c cin gq] : g \in [seq high c | c <- fc ++ lc].
    by rewrite map_cat mem_cat.
  have cino : c \in open.
    by move: cin; rewrite ocd !mem_cat /= inE=> /orP[] ->; rewrite ?orbT.
  move : (allP clae _ cino)=> /andP[] _; rewrite /end_edge.
  move=> /orP[ /(inbox_lexePt_right_bt inbox_e') | ]; first by rewrite gq.
  rewrite -gq; move=> /hasP [e2 e2in /eqP /[dup] e2P ->].
  apply: e'fut.
  move: e2in; rewrite inE => /orP[/eqP e2e | ]; last by [].
  move: (cin); rewrite mem_cat => /nc [].
  by apply: contains_right; rewrite // -e2e -gq.
move=> /orP[oldf |]; first by apply: old; rewrite oldf.
rewrite /= inE orbA=> /orP[| oldl]; last by apply: old; rewrite oldl orbT.
move=> /orP[go | ghe].
  have := opening_cells_aux_high vl vp oute'; rewrite oca_eq /=.
  move: go=> /[swap] -> /[dup] go /oute' /eqP /[dup] ge ->.
  rewrite mem_sort in go.
  apply/andP; split; first by exact ee'.
  have := cle; rewrite /= /close_out_from_event /end_edge => /andP[] + _.
  move=> /allP /(_ g go).
  by move=> /hasP[e3 e3in /eqP ->]; apply: e'fut.
have := opening_cells_aux_high_last vl vp oute'; rewrite oca_eq /= -(eqP ghe).
move=> {}ghe.
have lcco : lcc \in open by rewrite ocd !mem_cat inE eqxx !orbT.
have /lex_open_edges : g \in [seq high c | c <- open].
  by apply/mapP; exists lcc; rewrite // ghe.
move=> /andP[] left_e e_right.
rewrite (lexPt_trans left_e ee') /=.
have := (allP clae lcc lcco) => /andP[] _; rewrite /end_edge.
move=> /orP[].
  rewrite !inE -heq -ghe => /orP[] /eqP ->; move: inbox_e'.
    by move=> /inside_box_lexPt_bottom /andP[] _ /lexPtW.
  by move=> /inside_box_lexPt_top /andP[] _ /lexPtW.
move=> /hasP [e2 + /eqP ge2].
rewrite inE=> /orP[ /eqP abs | ].
  suff /onAbove : point e === he by rewrite puh.
  by rewrite -abs -ge2 heq right_on_edge.
by move=> /e'fut; rewrite /lexePtEv -ge2 -heq ghe.
Qed.

Lemma step_keeps_lex_edge :
  let s' := step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  forall e', inside_box (point e') -> lexPtEv e e' ->
               (forall e2, e2 \in future_events -> lexePtEv e' e2) ->
   {in [seq high c | c <- state_open_seq s'], forall g,
       lexPt (left_pt g) (point e') && lexePt (point e') (right_pt g)}.
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP => [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_open_seq /state_closed_seq /=.
  move=> e' in_e' ee' e'fut.
  by have := step_keeps_lex_edge_default; rewrite oe oca_eq catA; apply.
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  move: adj rfo sval; rewrite /open -cat_rcons => adj' rfo' sval'.
  have := open_cells_decomposition_cat adj' rfo' sval' (exi' eabove) eabove'.
  rewrite oe' cat_rcons => oe.
  rewrite /state_open_seq /state_closed_seq /=.
  have := step_keeps_lex_edge_default; rewrite oe oca_eq.
  move=> main e' in_e' ee' e'fut g /mapP[c cin gq].
  apply: (main e' in_e' ee' e'fut); apply/mapP; exists c; last by [].
  by move: cin; rewrite !(mem_rcons, mem_cat, inE) !orbA (orbC _ (c == lsto)).
have ebelow' : point e <<= lsthe by exact (negbFE ebelow).
case: ifP => [ebelow_st | enolsthe].
  rewrite /state_open_seq /update_open_cell/generic_trajectories.update_open_cell /=.
  have belowo : point e <<< high lsto by rewrite -lstheq.
  have := open_cells_decomposition_single adj rfo sval palstol belowo.
  move=> oe.
  have [ocd [lcc_ctn [_ [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  have [pal puh vl vp nc]:=
   decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
  case ogq: (outgoing e) => [ | fog ogs] /=.
    move=> e' in_e' ee' e'fut; rewrite cats0=> g /mapP [c + gq].
    rewrite mem_cat inE orbCA gq=> /orP[/eqP /[dup] cq -> /= | ].
      rewrite (fun h => lexPt_trans h ee')/=; last first.
        apply: (proj1 (andP (lex_open_edges (map_f _ _)))).
        by rewrite mem_cat inE eqxx orbT.
      have /andP[_ /orP[|] ] := (allP clae lsto lstoin).
        by move=>/(inbox_lexePt_right_bt in_e').
      move=> /hasP [e2].
      rewrite inE => /orP[/eqP -> | /e'fut +] /eqP rq.
        move: (strict_nonAunder vho); rewrite -lstheq /point_strictly_under_edge ebelow_st=>/esym.
        move: gq; rewrite cq high_set_left_pts=> gq.
        by rewrite lstheq -rq right_on_edge.
      by rewrite /lexePtEv -rq.
    move=> cold; apply/andP.
    have cino : c \in open.
      by rewrite mem_cat inE; move: cold=> /orP[] ->; rewrite ?orbT .
    split.
      apply: lexPt_trans ee'.
      by have /andP[] := lex_open_edges (map_f _ cino).
    have /andP[_] := (allP clae _ cino).
    move=> /orP[].
      by move=> /(inbox_lexePt_right_bt in_e').
    move=> /hasP[e2 + /eqP e2P]; rewrite inE => /orP[/eqP e2e | ].
      rewrite e2e in e2P.
      by move: (nc _ cold)=> []; apply: contains_right.
    by move=> /e'fut; rewrite /lexePtEv -e2P.
  rewrite -ogq.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vho ogn oute.
    by rewrite oca_eq.
  rewrite /= => e' in_e' ee' e'fut g /mapP[c cin gq].
  have := step_keeps_lex_edge_default.
  rewrite oe oca_eq=> /(_ e' in_e' ee' e'fut) main.
  move: cin; rewrite -!catA /= mem_cat => /orP[cin | ].
    by apply: main; apply/mapP; exists c; rewrite // mem_cat cin.
  rewrite inE=> /orP[/eqP cq | ].
    rewrite gq cq high_set_left_pts; apply: main.
    by apply/mapP; exists fno; rewrite // !(mem_cat, inE) eqxx ?orbT.
  move=> cin; apply: main.
  by apply/mapP; exists c; rewrite //= mem_cat inE cin !orbT.
move=> e' in_e' ee' e'fut.
rewrite -/(open_cells_decomposition _ _).
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
rewrite -/(update_open_cell_top _ _ _).
case uoctq: update_open_cell_top => [nos lno].
rewrite /state_open_seq /= -!catA.
move=> g /mapP [c cin gq]; rewrite gq {gq}.
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  by rewrite /contains_point' palstol -lstheq ebelow'.
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe'=> oe.
have [ocd [lcc_ctn [_ [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vl vp nc]:=
   decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
have := step_keeps_lex_edge_default; rewrite oe => main.
move: uoctq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top.
have := last_step_situation oe' pxhere (negbT enolsthe) ebelow'.
move=> [] fc'0 [] leo [cc' ccq].
case ogq : (outgoing e) => [ | fog ogs]; last first.
  rewrite -ogq.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos'] lno'].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vp ogn oute.
    by rewrite oca_eq.
  move=> -[] nosq lnoq.
  move: main; rewrite leo oca_eq => /(_ _ in_e' ee' e'fut) main.
  move: cin; rewrite mem_cat=> /orP[cin | ].
    by apply: main; apply/mapP; exists c; rewrite // !mem_cat cin.
  rewrite fc'0 /= mem_cat inE orbA=> /orP[|cin]; last first.
    by apply: main; apply/mapP; exists c; rewrite // !(mem_cat, inE) cin !orbT.
  move=> /orP[ | /eqP clno]; last first.
    apply: main; apply/mapP; exists c; rewrite // lnoq !(mem_cat, inE) clno.
    by rewrite eqxx !orbT.
  rewrite -nosq inE=> /orP[ | cin]; last first.
    by apply: main; apply/mapP; exists c; rewrite // !(mem_cat, inE) cin !orbT.
  move=> /eqP ->; rewrite high_set_left_pts.
  by apply: main; apply/mapP; exists fno; rewrite // !mem_cat inE eqxx !orbT.
move=> [] nosq lnoq.
have oca_eq : opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
   le he =
  ([::], (Bcell (@no_dup_seq [eqType of pt]
      [:: (Bpt (p_x (point e)) (pvert_y (point e) he));
          (point e);
          (Bpt (p_x (point e)) (pvert_y (point e) le))]) [::] le he)).
  rewrite ogq -[sort _ _]/[::].
  rewrite /opening_cells_aux/generic_trajectories.opening_cells_aux.
  by rewrite -/(vertical_intersection_point _ _) (pvertE vl)
       -/(vertical_intersection_point _ _)  (pvertE vp).
move: main; rewrite oca_eq => /(_ _ in_e' ee' e'fut)=> main.
move: cin; rewrite mem_cat=> /orP[cin |].
  by apply: main; apply/mapP; exists c; rewrite // !mem_cat cin.
rewrite fc'0 -nosq /= inE=> /orP[/eqP clno | cin]; last first.
  by apply: main; apply/mapP; exists c; rewrite // !(mem_cat, inE) cin !orbT.
apply: main.
rewrite map_cat /=.
suff ->: high c = he by rewrite !(mem_cat, inE) eqxx !orbT.
by rewrite clno -lnoq /=.
Qed.

Lemma opening_cells_aux_cover_outgoing le he nos lno:
  valid_edge le (point e) ->
  opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he =
  (nos, lno) ->
  {in (outgoing e), forall g, 
  exists c, c \in nos /\ high c = g /\ left_limit c = p_x (left_pt g)}.
Proof.
move=> + + g go.
have go' : g \in sort (@edge_below _) (outgoing e) by rewrite mem_sort.
elim: (sort _ _) go' oute' le nos lno {go} => [ // | g' og Ih].
rewrite inE=> /orP[/eqP -> | gin]; move=> + le nos lno vle.
  have /[swap] /[apply] /eqP lpg' : g' \in g' :: og by rewrite inE eqxx.
  rewrite /=.
  rewrite -/(opening_cells_aux _ _ _ _).
  case: (opening_cells_aux _ _ _ _) => s nc.
  rewrite -/(vertical_intersection_point _ _) (pvertE vle).
  set it := Bcell _ _ _ _; move=> [] sq ncq; exists it.
  rewrite -sq inE eqxx; split=> //; split=> //.
  rewrite /left_limit /=.
  rewrite -[pt_eqb _ _ _ _]/(_ == _ :> pt).
  by case: ifP => [/eqP -> /=| /= ]; rewrite lpg'.
move=> outg'.
have outg : {in og, forall g, left_pt g == point e}.
  by move=> x xin; apply: outg'; rewrite inE xin orbT.
rewrite /=.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [s nc].
rewrite -/(vertical_intersection_point _ _) (pvertE vle) => - [sq ncq].
have vg : valid_edge g' (point e).
  rewrite -(eqP (outg' g' _)); last by rewrite inE eqxx.
  by apply: valid_edge_left.
have [it [P1 P2]]:= Ih gin outg g' s nc vg oca_eq.
  exists it; split; last by [].
by rewrite -sq inE P1 orbT.
Qed.

Lemma step_keeps_edge_covering_default gen_closed fc cc lcc lc le he nos lno:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he =
     (nos, lno) ->
  forall g,
  edge_covered g open gen_closed \/ g \in outgoing e ->
  edge_covered g (fc ++ nos ++ lno :: lc)
    (gen_closed ++ rcons (closing_cells (point e) cc)
         (close_cell (point e) lcc)).
Proof.
move=> oe oca_eq.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe old_nctn]:=
   decomposition_connect_properties rfo sval adj cbtom bet_e oe.
move=> g [go | gn]; last first.
  have [c [cin [highc cleft]]]:=
      opening_cells_aux_cover_outgoing vle oca_eq gn.
  left; exists c, [::]; split=> /=; first by [].
  split; first by move=> c'; rewrite inE=> /eqP ->.
  split; first by [].
  split; last by [].
  by rewrite !mem_cat cin !orbT.
case: go => [[opc [pcc [pccsub opcP]]] | 
              [ pcc [pccn0 [pccsub pccP]]]]; last first.  
  right; exists pcc.
 split;[exact pccn0 | split; [ | exact pccP]].
  by move=> g1 /pccsub; rewrite mem_cat=> ->.
move: opcP => [highc [cnc [opco pccl]]].
have [ghe | gnhe] := eqVneq g he.
  have vllcc : valid_edge (low lcc) (point e).
    apply: (seq_valid_low sval); rewrite ocd !map_cat !mem_cat /= inE.
    by rewrite eqxx ?orbT.
  have lccq : lcc = opc.
    apply: high_inj=> //; first by rewrite ocd !(mem_cat, inE) eqxx !orbT.
    by rewrite (highc opc) ?ghe; last rewrite mem_rcons inE eqxx.
  left; exists lno, (rcons pcc (close_cell (point e) lcc)).
  split.
    move=> c; rewrite mem_rcons inE=> /orP[/eqP -> | /pccsub].
      by rewrite !(mem_rcons, mem_cat, inE) eqxx ?orbT.
    by rewrite mem_cat=> ->.
  split.
    move=> c; rewrite !(mem_rcons, inE).
    move=> /orP[/eqP |/orP[/eqP | inpcc]]; last 1 first.
        by apply: highc; rewrite !(mem_rcons, mem_cat, inE, inpcc, orbT).
      rewrite /close_cell.
      move=> ->; rewrite ghe.
      have := higher_edge_new_cells oute vle vhe.
      by rewrite /opening_cells oca_eq => /(_ _ erefl); rewrite last_rcons.
    rewrite /close_cell=> ->.
    by rewrite -heq (pvertE vhe) (pvertE vllcc) /= ghe.
  split.
    elim/last_ind : {-1} pcc (erefl pcc) => [pcceq | pcc1 lpcc _ pcceq].
      rewrite /= andbT.
      rewrite close_cell_right_limit; last first.
        by rewrite /valid_cell vllcc -heq vhe.
      have /(_ lno) -> // := opening_cells_left oute vle vhe.
      by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
    rewrite connect_limits_rcons; last by apply/eqP/rcons_neq0.
    apply/andP; split; last first.
      rewrite last_rcons right_limit_close_cell //.
        have /(_ lno) -> // := opening_cells_left oute vle vhe.
        by rewrite /opening_cells oca_eq mem_rcons inE eqxx.
      by rewrite -heq.
    rewrite connect_limits_rcons; last by apply/eqP/rcons_neq0.
    move: cnc.
    rewrite pcceq connect_limits_rcons; last by apply/eqP/rcons_neq0.
    move=> /andP[] -> /eqP ->.
    by rewrite left_limit_close_cell lccq eqxx.
  split; first by rewrite !(mem_cat, inE, eqxx, orbT).
  move: pccl; rewrite lccq; case: (pcc)=> /=; last by [].
  by rewrite left_limit_close_cell.
rewrite -cat_rcons.
move: opco; rewrite ocd -cat_rcons !mem_cat orbCA => /orP[]; last first.
  move=> opc_pres.
  left; exists opc, pcc.
  split; first by apply: subset_catrl.
  split; first by [].
  split; first by [].
  split; last by [].
  by rewrite !mem_cat orbCA opc_pres orbT.
move=> opcc.
right.
have [_ highopc leftopc] := close_cell_preserve_3sides (point e) opc.
exists (rcons pcc (close_cell (point e) opc)).
split.
  by apply/eqP/rcons_neq0.
split.
  move=> c; rewrite mem_rcons inE=> /orP[/eqP -> | ].
    rewrite mem_cat/closing_cells; apply/orP; right.
    by rewrite -map_rcons; apply/mapP; exists opc.
  by move=> /pccsub cin; rewrite mem_cat cin.
split.
  move=> c; rewrite mem_rcons inE => /orP[/eqP -> | inpcc]; last first.
    by apply highc; rewrite mem_rcons inE inpcc orbT.
  by rewrite highopc; apply highc; rewrite mem_rcons inE eqxx.
split.
  have [/eqP -> | pccn0] := boolP (pcc == [::]).
    by [].
  move: cnc; rewrite !connect_limits_rcons // => /andP[] -> /eqP -> /=.
  by rewrite /left_limit leftopc.
split.
  move: pccl; case pccq: pcc => [ | pcc0 pcc'] //=.
  by rewrite /left_limit leftopc.
have opco : opc \in open.
  by rewrite ocd -cat_rcons !mem_cat opcc orbT.
rewrite /last_cell last_rcons right_limit_close_cell; last first.
    by apply/(seq_valid_high sval)/map_f.
  by apply/(seq_valid_low sval)/map_f.
have hopc : high opc = g by apply: highc; rewrite mem_rcons inE eqxx.
have {}opcc : opc \in cc.
  move: opcc; rewrite mem_rcons inE=> /orP[] // /eqP abs.
  by case/eqP: gnhe; rewrite -hopc abs.
have e_on : point e === high opc.
  by apply: (open_cells_decomposition_point_on cbtom adj bet_e sval oe opcc).
have [ abs | -> ] := open_non_inner opco e_on; last by rewrite hopc.
have := bottom_left_lex_to_high cbtom adj rfo open_side_limit.
move=> /(_ _ inbox_e btm_left _ opco).
by rewrite abs lexPt_irrefl.
Qed.

Lemma edge_covered_set_left_pts g l1 c l2 l3 lpts :
  left_limit c = p_x (last dummy_pt lpts) ->
  edge_covered g (l1 ++ c :: l2) l3 ->
  edge_covered g (l1 ++ (set_left_pts c lpts) :: l2) l3.
Proof.
move=> left_cond [active | [pcc pccP]]; last by right; exists pcc; exact pccP.
move: active => [opc [pcc [pccP1 [pccP2 [pccP3 [pccP4 pccP5]]]]]].
have [copc | cnopc] := eqVneq c opc.
  left; exists (set_left_pts c lpts), pcc.
  split; first by [].
  split.
    move=> x; rewrite mem_rcons inE=> /orP[ /eqP -> | xin]; last first.
      by apply: pccP2; rewrite mem_rcons inE xin orbT.
    rewrite /set_left_pts /=.
    by apply: pccP2; rewrite mem_rcons inE copc eqxx.
  split.
    have [-> | pccn0] := eqVneq pcc [::]; first by [].
    move: pccP3; rewrite !connect_limits_rcons // => /andP[] -> /eqP -> /=.
    rewrite /set_left_pts /=.
    by rewrite -copc left_cond /left_limit.
  split; first by rewrite mem_cat inE eqxx orbT.
   move: pccP5; have [-> /= | pccn0] := eqVneq pcc [::].
     by rewrite -copc left_cond.
   by move: pccn0; case: (pcc).
left; exists opc, pcc.
split; first by [].
split; first by [].
split; first by [].
split; last by [].
move: pccP4.
rewrite !mem_cat !inE=> /orP[ -> | /orP [ | -> ]]; rewrite ?orbT //.
by move: cnopc=> /[swap]; rewrite eq_sym=> ->.
Qed.

Lemma update_closed_cell_keep_left_limit c pt : 
  left_limit (update_closed_cell c pt) = left_limit c.
Proof. by move: c => [? ? ? ?]. Qed.

Lemma connect_limits_seq_subst (l : seq cell) c c' :
  left_limit c = left_limit c' -> right_limit c = right_limit c' ->
  connect_limits l -> connect_limits (seq_subst l c c').
Proof.
move=> ll rr; elim: l => [ | a [ | b l] Ih] /=; first by [].
  by case: ifP.
move=> /[dup] conn /andP[ab conn'].
have conn0 : path (fun c1 c2 => right_limit c1 == left_limit c2) a (b :: l).
   by exact: conn. 
have /Ih : sorted (fun c1 c2 => right_limit c1 == left_limit c2) (b :: l).
  by apply: (path_sorted conn0).
case: ifP=> [/eqP ac | anc].
  rewrite /=; case: ifP => [/eqP bc | bnc].
    by rewrite /= -rr -ll -ac (eqP ab) ac -bc eqxx.
  by rewrite /= -rr -ac ab.
rewrite /=; case: ifP=> [/eqP bc | bnc].
  by rewrite /= -ll -bc ab.
by rewrite /= ab.
Qed.

Lemma edge_covered_update_closed_cell g l1 l2 c pt :
  closed_cell_side_limit_ok c ->
  edge_covered g l1 (rcons l2 c) ->
  edge_covered g l1 (rcons l2 (update_closed_cell c pt)).
Proof.
move=> cok ecg.
have lq : left_limit (update_closed_cell c pt) = left_limit c.
  by case: (c).
have rq : right_limit (update_closed_cell c pt) = right_limit c.
  by rewrite update_closed_cell_keeps_right_limit.
case: ecg => [[oc [pcc [ocP1 [hP [cP [ocin conn]]]]]] | ].
  left; exists oc, (seq_subst pcc c (update_closed_cell c pt)).
  split.
    elim: (pcc) ocP1 => [ // | a l Ih].
    move=> subh x; rewrite /=.
    have /Ih {} Ih : {subset l <= rcons l2 c}.
      by move=> y yin; have /subh : y \in a:: l by rewrite inE yin orbT.
    case: ifP => [ac | anc]; rewrite !(inE, mem_rcons).
      by move=> /orP[-> // | /Ih]; rewrite mem_rcons inE.
    move=> /orP[xa | ].
      have /subh : x \in a :: l by rewrite inE xa.
      by rewrite mem_rcons inE (eqP xa) anc /= orbC => ->.
    by move/Ih; rewrite mem_rcons inE.
  split.
    move=> x; rewrite mem_rcons inE => /orP[xoc | ].
      by apply: hP; rewrite mem_rcons inE xoc.
    have : {in pcc, forall c, high c = g}.
      by move=> y yin; apply: hP; rewrite mem_rcons inE yin orbT.
    elim: (pcc) => [ // | a l Ih] {}hP.
    have /Ih {}Ih : {in l, forall c, high c = g}.
      by move=> y yin; apply: hP; rewrite inE yin orbT.
    rewrite /=; case: ifP=> [ac | anc].
      rewrite inE=> /orP[/eqP -> | ]; last by [].
      have: high c = g by apply: hP; rewrite inE eq_sym ac.
      by case: (c).    
    rewrite inE=> /orP[/eqP -> | ]; last by [].
    by apply: hP; rewrite inE eqxx.
  split.
    elim/last_ind: (pcc) cP => [// | pcc' lpcc _].
    rewrite connect_limits_rcons; last by apply/eqP/rcons_neq0.
    move=> /andP[] cP cc.
    rewrite connect_limits_rcons; last first.
      by case: (pcc')=> /= [ | ? ?]; case: ifP.
    apply/andP; split; last first.
      rewrite -cats1 seq_subst_cat /=.
      move: cc; rewrite last_rcons=> /eqP <-.
      case: ifP; rewrite cats1 last_rcons; last by [].
      by rewrite rq => /eqP ->.
    by apply: connect_limits_seq_subst.
  split; first by [].
  case: (pcc) conn => [ | fpcc pcc']/=; first by [].
  by case: ifP=> [ /eqP -> | ].
move=> [pcc [P0 [P1 [P2 [P3 [P4 P5]]]]]].
right.
exists (seq_subst pcc c (update_closed_cell c pt)).
split.
  by rewrite seq_subst_eq0.
split.
  elim : (pcc) P1 => [ | a l Ih] P1; first by [].
  have ain : a \in rcons l2 c by apply: P1; rewrite inE eqxx.
  have /Ih {} Ih : {subset l <= rcons l2 c}.
    by move=> y yin; apply: P1; rewrite inE yin orbT.
  rewrite /=; case: ifP=> [ ac | anc].
    move=> g'; rewrite !inE => /orP[/eqP -> | /Ih]; last by [].
    by rewrite mem_rcons inE eqxx.
  move=> g'; rewrite !inE=> /orP[/eqP -> | ].
    by move: ain; rewrite !mem_rcons !inE anc /= orbC => ->.
  by apply: Ih.
split.
  elim: (pcc) P2 => [ | a l Ih] P2; first by [].
  have /Ih {} Ih : {in l, forall c, high c = g}.
    by move=> x xin; apply: P2; rewrite inE xin orbT.
  rewrite /=; case: ifP => [ac | anc].
    move=> c'; rewrite inE => /orP[/eqP -> | ].
      move: (P2 c); rewrite inE eq_sym ac => /(_ isT).
      by case: (c).
    by apply: Ih.
  move=> c'; rewrite inE => /orP[/eqP -> | ].
    by apply: P2; rewrite inE eqxx.
  by apply: Ih.
split; first by apply: connect_limits_seq_subst.
split.
  move: P4; case: (pcc)=> [ | a l]; first by [].
  rewrite /=; case: ifP=> [/eqP ac | anc] /=; last by [].
  by rewrite lq ac.
move: P5; elim/last_ind : (pcc) => [ | l b _]; first by [].
rewrite -cats1 seq_subst_cat /=; case: ifP=> [/eqP bc | bnc].
  by rewrite /last_cell !last_cat /= rq bc.
by rewrite /last_cell !last_cat /=.
Qed.

Lemma lsthe_at_left : point e <<= lsthe ->
  p_x (left_pt lsthe) < p_x (point e).
Proof.
move=> puh.
have /lex_open_edges/andP[+ _] : lsthe \in [seq high c | c <- open].
  by apply/mapP; exists lsto.
rewrite /lexPt=> /orP[ | /andP[] /eqP samex lty]; first by [].
have vhe : valid_edge lsthe (point e).
  move: (allP sval lsto); rewrite /open mem_cat inE eqxx !orbT.
  by move=> /(_ isT)=> /andP[]; rewrite lstheq.
move: puh; rewrite under_pvert_y //.
move: (samex)=> /esym/eqP=> samex'.
rewrite (same_pvert_y vhe samex').
by rewrite (on_pvert (left_on_edge _)) leNgt lty.
Qed.

Lemma step_keeps_edge_covering:
  let s' :=  step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  forall g, edge_covered g open (rcons cls lstc) \/ g \in outgoing e ->
  edge_covered g (state_open_seq s') (state_closed_seq s').
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP => [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  rewrite /state_open_seq /state_closed_seq /=.
  move=> g gin.
  have := step_keeps_edge_covering_default oe oca_eq gin.
  by rewrite -!cats1 -?catA /=.
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  move: adj rfo sval; rewrite /open -cat_rcons => adj' rfo' sval'.
  have := open_cells_decomposition_cat adj' rfo' sval' (exi' eabove) eabove'.
  rewrite oe' cat_rcons => oe.
  rewrite /state_open_seq /state_closed_seq /=.
  move=> g gin.
  have := step_keeps_edge_covering_default oe oca_eq gin.
  by rewrite !cat_rcons -!cats1 -?catA /=.
have [p1 [p2 [pts ptsq]]]: exists p1 p2 pts, left_pts lsto = p1 :: p2 :: pts.
  have ebelow' : point e <<= high lsto.
    by move/negbFE :ebelow; rewrite lstheq.
  have := size_left_lsto pxhere palstol ebelow'.
  case: (left_pts lsto) => [// | pt1 [ // | pt2 pts]] _.
  by exists pt1, pt2, pts.
case: ifP => [ebelow_st {ebelow} | eonlsthe].
  rewrite /update_open_cell/generic_trajectories.update_open_cell.
  case ogq : (outgoing e) => [ /= | fog ogs].
    move=> g [ ecg | //].
    rewrite /state_open_seq /= cats0 /state_closed_seq /=.
    apply: edge_covered_set_left_pts.
      by rewrite /left_limit ptsq.
    apply: edge_covered_update_closed_cell.
      by apply: (allP close_side_limit); rewrite mem_rcons inE eqxx.
    by exact: ecg.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos] lno]  /=.
    have outn0 : fog :: ogs != nil by [].
    have oute2 : {in fog :: ogs, forall g, left_pt g == point e}.
      by rewrite -ogq.
    have := opening_cells_aux_absurd_case vlo vho outn0 oute2.
    by rewrite oca_eq.
  move=> g [ecg | gnew]; last first.
    left.
    have :=opening_cells_aux_cover_outgoing vlo.
    move=> /(_ (high lsto) (fno :: nos) lno); rewrite ogq=> /(_ oca_eq).
    move=> /(_ g gnew) [gc [P1 [P2 P3]]].
    exists (if gc == fno then
               set_left_pts fno (point e :: behead (left_pts lsto))
            else gc), [::].
    split; first by [].
    split.
      move=> x; rewrite /= inE => /eqP ->.
      case: ifP => [/eqP <- | ]; last by [].
      by case: (gc) P2.
    split; first by [].
    split.
      rewrite /state_open_seq /=.
      move: P1; case: ifP => [/eqP -> _ | ].
        by rewrite !mem_cat inE eqxx orbT.
      by rewrite inE=> -> /=; rewrite !mem_cat inE=> ->; rewrite ?orbT.
    rewrite /head_cell /=; case: ifP=> [/eqP <- | ]; last by [].
    move: lstxq; rewrite /left_limit.
    rewrite ptsq /left_limit /= => <-.
    by rewrite (eqP (@oute g _)) ?pxhere // ogq.
  move: ecg=> [[oc [pcc [P1 [P2 [P3 [P4 P5]]]]]] | ].
    move: P4; rewrite mem_cat inE orbCA=> /orP[/eqP oclsto | inold].
      rewrite /state_open_seq /state_closed_seq /=.
      rewrite /= -catA /=.
      apply: edge_covered_set_left_pts.
        rewrite (opening_cells_left oute vlo vho).
          by rewrite pxhere lstxq /left_limit ptsq.
        by rewrite /opening_cells ogq oca_eq mem_rcons !inE eqxx !orbT.
      apply: edge_covered_update_closed_cell.
        by apply: (allP close_side_limit); rewrite mem_rcons inE eqxx.
      left; exists lno, pcc.
      split; first by [].
      split.
        move=> x; rewrite mem_rcons inE=> /orP[/eqP -> | xin]; last first.
          by apply P2; rewrite mem_rcons inE xin orbT.
        have := opening_cells_aux_high_last vlo vho oute'.
        rewrite ogq oca_eq /= -oclsto=> ->; apply: P2.
        by rewrite mem_rcons inE eqxx.
      have left_lno : left_limit lno = lstx.
        have := opening_cells_left oute vlo vho.
          rewrite -pxhere /opening_cells ogq oca_eq; apply.
          by rewrite mem_rcons inE eqxx.
      split.
        elim/last_ind: {-1} pcc (erefl pcc)  => [ | pcc' pcl _] pccq;
          first by [].
        rewrite connect_limits_rcons; last by apply/eqP/rcons_neq0.
        move: P3; rewrite pccq connect_limits_rcons; last first.
          by apply/eqP/rcons_neq0.
        move=> /andP[] -> /eqP ->.
        by rewrite oclsto -lstxq left_lno eqxx.
      split; first by rewrite !(mem_cat, inE) eqxx !orbT.
      move: P5; case: (pcc) => //=.
      by rewrite left_lno oclsto lstxq.
    rewrite /state_closed_seq /state_open_seq /=.
    rewrite -!catA /=.
    have left_fno : left_limit fno = lstx.
      have := opening_cells_left oute vlo vho.
      rewrite -pxhere /opening_cells ogq oca_eq; apply.
      by rewrite mem_rcons !inE eqxx !orbT.
    apply: edge_covered_set_left_pts.
      by rewrite left_fno lstxq /left_limit ptsq.
    apply: edge_covered_update_closed_cell.
      by apply: (allP close_side_limit); rewrite mem_rcons inE eqxx.
    left; exists oc, pcc; repeat (split; first by []); split; last by [].
    by rewrite !(mem_cat, inE); move: inold=> /orP[] ->; rewrite ?orbT.
  move=> [pcc [P1 [P2 [P3 [P4 P5]]]]].
  rewrite /state_open_seq /state_closed_seq /=.
  apply: edge_covered_update_closed_cell.
    by apply: (allP close_side_limit); rewrite mem_rcons inE eqxx.
  by right; exists pcc; repeat (split; first by []); done.
rewrite -/(open_cells_decomposition _ _).
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
have exi2 : exists2 c, c \in (lsto :: lop) & contains_point' (point e) c.
  have : contains_point' (point e) lsto.
    by rewrite /contains_point' palstol -lstheq /point_under_edge (negbFE ebelow).
  by exists lsto;[rewrite inE eqxx | ].
have := open_cells_decomposition_cat adj rfo sval exi2.
rewrite /= oe' => /(_ palstol)=> oe.
have [ocd [lcc_ctn [all_ct [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe old_nctn]:=
 decomposition_connect_properties rfo sval adj cbtom bet_e oe.
rewrite -/(update_open_cell_top _ _ _).
case uoct_eq: (update_open_cell_top lsto he e) => [nos lno].
rewrite /state_closed_seq /state_open_seq /= -!catA /=.
move=> g [ | ]; last first.
  case ogq : (outgoing e) => [// | fog ogs]; rewrite -ogq => go.
  move: uoct_eq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top ogq.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos'] lno'].
    have ogn : fog :: ogs != [::] by [].
    have := opening_cells_aux_absurd_case vlo vhe ogn.
    by rewrite -[X in {in X, _}]ogq oca_eq=> /(_ oute).
  rewrite -ogq in oca_eq.
  move=> [] <- <-.
  have [oc [P1 [P2 P3]]] := opening_cells_aux_cover_outgoing vlo oca_eq go.
  left; exists (if oc == fno then 
                  set_left_pts fno (point e :: behead (left_pts lsto))
                else oc), [::].
  split;[by [] | split;[ | split; [by [] | ]]].
    case: ifP => [/eqP ocfno | ocnfno]; last first.
      by move=> x; rewrite mem_rcons !inE=> /orP[/eqP -> | ].
    move=> x; rewrite inE -ocfno=> /eqP ->.
    by case: (oc) P2.
  split.
    case: ifP => [/eqP ocfno | ocnfno].
      by rewrite !(mem_cat, inE) eqxx !orbT.
    by move: P1; rewrite inE ocnfno /= !(mem_cat, inE)=> ->; rewrite !orbT.
  rewrite /=; case: ifP => [ocfno | ocnfno]; last by [].
  move: lstxq; rewrite /left_limit ptsq -pxhere /= => <-.
  by apply/f_equal/esym/(@eqP [eqType of pt])/oute.
move=> [ | [pcc [P0 [P1 [P2 [P3 [P4 P5]]]]]]]; last first.
  move: uoct_eq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top.
  case ogq : (outgoing e) => [ | fog ogs].
    move=> [] <- <- /=.
    right; exists pcc; split; [by [] | split; last by []].
    move=> x /P1; rewrite !(mem_rcons, inE, mem_cat).
    by move=> /orP[] ->; rewrite ?orbT.
  rewrite -ogq.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) =>
       [[ | fno nos'] lno'].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vhe ogn oute.
    by rewrite oca_eq.
  move=> [] <- <-.
  right; exists pcc.
  split; first by [].
  split; last by [].
  move=> x /P1.
  by rewrite !(mem_cat, mem_rcons, inE)=> /orP[] ->; rewrite ?orbT.
move=> [oc [pcc [P1 [P2 [P3 [P4 P5]]]]]].
move: P4; rewrite /open ocd.
move=> ocin.
have olds : [|| oc \in fop, oc \in fc' | (oc \in lc)] ->
      edge_covered g (fop ++ fc' ++ nos ++ lno :: lc)
        (rcons (closing_cells (point e) (behead cc) ++ lstc :: cls)
           (close_cell (point e) lcc)).
  move=> ocin'; left; exists oc, pcc.
  split.
    move=> x /P1; rewrite !(mem_rcons, mem_cat, inE).
    by move=> /orP[] ->; rewrite ?orbT.
  do 2 (split; first by []).
  split; last by [].
  rewrite !(mem_cat, inE).
  by move: ocin'=> /orP[-> | /orP[] -> ]; rewrite ?orbT.
move: ocin; rewrite -!catA !(mem_cat, inE) => /orP[ocin |].
  by apply: olds; rewrite ocin ?orbT.
move=> /orP[ocin |]; first by apply: olds; rewrite ocin ?orbT.
rewrite orbA=> /orP[ | ocin];last by apply: olds; rewrite ocin ?orbT.
have ealsthe : point e >>= lsthe by rewrite /point_strictly_under_edge eonlsthe.
have ebelow' : point e <<= lsthe by rewrite /point_under_edge (negbFE ebelow).
have := last_step_situation oe' pxhere ealsthe ebelow'.
move=> [-> /= [leo [cc' ccq]] ].
have ll := lsthe_at_left ebelow'.
rewrite ccq inE -orbA => /orP[/eqP oclsto | ].
  have gq : g = lsthe.
    by rewrite lstheq -oclsto P2 // mem_rcons inE eqxx.
  have [pcc1 [pcc' pccq]] : exists pcc1 pcc', pcc = pcc1 :: pcc'.
    case pccq : pcc => [ | pcc1 pcc']; last by exists pcc1, pcc'.
    move: P5; rewrite pccq /= oclsto -lstxq -pxhere => abs.
    by rewrite abs gq lt_irreflexive in ll.
  right; exists pcc.
    split.
      by rewrite pccq.
    split.    
      move=> x /P1; rewrite !(mem_rcons, mem_cat, inE).
      by move=> /orP[] -> ; rewrite ?orbT.
    split.
      by move=> x xin; apply: P2; rewrite mem_rcons inE xin orbT.
    split.
      move: P3; rewrite connect_limits_rcons; last by rewrite pccq.
      by move=> /andP[].
    split; first by move: P5; rewrite pccq.
    move: P3; rewrite connect_limits_rcons; last by rewrite pccq.
    move=> /andP[] _ /eqP ->.
    have eon : point e === high lsto.
      rewrite -lstheq.
      by apply: under_above_on; first rewrite lstheq.
    move: (open_non_inner lstoin eon)=> []; last first.
      rewrite -lstheq gq oclsto => <-.
      by rewrite -lstxq pxhere.
    by move: ll=> /[swap] ->; rewrite -lstheq lt_irreflexive.
    move=> /orP[ | oclcc]; last first.
  have hlnoq : high lno = high lcc.
    move: uoct_eq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top.
    case ogq: (outgoing e) => [| fog ogs]; first by move=> [] _ <- /=.
    rewrite -ogq.
    rewrite -/(opening_cells_aux _ _ _ _).
    case oca_eq : (opening_cells_aux _ _ _ _) => [[ | fno nos'] lno'].
      have := opening_cells_aux_high_last vle vhe oute'; rewrite leo oca_eq /=.
      by move=> /[swap] - [] _ <- => ->.
    have := opening_cells_aux_high_last vle vhe oute'; rewrite leo oca_eq /=.
    by move=> /[swap] - [] _ <- => ->.
  have llno : left_limit lno = p_x (point e).
    move: uoct_eq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top.
    case ogq: (outgoing e) => [| fog ogs].
      have:= size_left_lsto pxhere palstol.
      rewrite -lstheq => /(_ ebelow').
      move: lstxq; rewrite /left_limit pxhere => -> + [] _ <- /=.
      by case: (left_pts lsto).
    rewrite -ogq.
    rewrite -/(opening_cells_aux _ _ _ _).
    case oca_eq: opening_cells_aux => [ [ | fno nos'] lno'] [] _ <-;
      have := opening_cells_left oute vlo vhe; 
      rewrite /opening_cells oca_eq=> /(_ lno');
      by rewrite mem_rcons inE eqxx=> /(_ isT).
  have vlcc : valid_cell lcc (point e).
    by apply/andP/(allP sval); rewrite /open ocd !(mem_cat, inE) eqxx ?orbT.
  left; exists lno, (rcons pcc (close_cell (point e) lcc)).
  split.
    move=> c; rewrite !(mem_rcons, mem_cat, inE)=> /orP[-> |]; first by [].
    by move=> /P1; rewrite mem_rcons inE => ->; rewrite !orbT.
  split.
    move=> c; rewrite mem_rcons inE => /orP[/eqP -> |].
      by rewrite hlnoq; apply: P2; rewrite (eqP oclcc) mem_rcons inE eqxx.
    rewrite mem_rcons inE => /orP[/eqP -> | ].
      have [_ -> _] := close_cell_preserve_3sides (point e) lcc.
        by rewrite -(eqP oclcc); apply: P2; rewrite mem_rcons inE eqxx.
      by move=> cin; apply: P2; rewrite mem_rcons inE cin orbT.
  split.
    rewrite connect_limits_rcons; last by apply/eqP/rcons_neq0.
    rewrite last_rcons close_cell_right_limit // llno eqxx andbT.
    case pccq : pcc => [ | pcc1 pcc']; first by [].
    rewrite connect_limits_rcons //.
    move: P3; rewrite pccq connect_limits_rcons // => /andP[] -> /=.
    move=> /eqP ->; rewrite /left_limit (eqP oclcc).
    by have [_ _ ->] := close_cell_preserve_3sides (point e) lcc.
  split; first by rewrite !mem_cat inE eqxx !orbT.    
  rewrite /head_cell !head_rcons.
  move: P5; rewrite (eqP oclcc) => <-.
  case: (pcc) => [ /= | ? ?]; last by [].
  by rewrite left_limit_close_cell.
move=> ocin.
have ocin' : oc \in cc by rewrite ccq inE ocin orbT.
have right_pt_e : right_pt (high oc) = point e.
  have := open_cells_decomposition_point_on cbtom adj bet_e sval oe ocin'.
      have ocop : oc \in open by rewrite /open ocd !mem_cat ocin' ?orbT.
      have := open_non_inner ocop; rewrite /non_inner => /[apply].
      move=> [ abs |->]; last by [].
      have : high oc \in [seq high c | c <- open] by apply: map_f.
      by move=> /lex_open_edges; rewrite abs lexPt_irrefl.
right; exists (rcons pcc (close_cell (point e) oc)).
split.
  by apply/eqP/rcons_neq0.
split.
  have clocin : close_cell (point e) oc \in closing_cells (point e) cc'.
    by apply: map_f.
  move=> c; rewrite !(mem_rcons, mem_cat, inE)=> /orP[ /eqP -> | /P1].
    by rewrite clocin ?orbT.
  by rewrite mem_rcons inE=> ->; rewrite !orbT.
split.
  move=> c; rewrite mem_rcons inE => /orP[/eqP -> | ].
    have [_ -> _] := close_cell_preserve_3sides (point e) oc.
    by apply: P2; rewrite mem_rcons inE eqxx.
  by move=> cin; apply: P2; rewrite mem_rcons inE cin orbT.
split.
  case pccq : pcc => [ | pcc1 pcc']; first by [].
  rewrite connect_limits_rcons /left_limit; last by [].
  have [_ _ ->] := close_cell_preserve_3sides (point e) oc.
  by move: P3; rewrite pccq connect_limits_rcons.
split.
  case pccq : pcc => [ | pcc1 pcc'] /=.
    move: P5; rewrite pccq /= /left_limit.
    by have [_ _ ->] := close_cell_preserve_3sides (point e) oc.
  by move: P5; rewrite pccq.
rewrite /last_cell last_rcons close_cell_right_limit; last first.
  by apply/andP/(allP sval); rewrite /open ocd !mem_cat ocin' !orbT.
rewrite P2 in right_pt_e; last by rewrite mem_rcons inE eqxx.
by rewrite right_pt_e.
Qed.

Lemma step_keeps_subset_default:
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) := opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  {subset [seq high c | c <- fc ++ nos ++ lno :: lc]
       <= [seq high c | c <- open] ++ outgoing e}.
Proof.
case oe : (open_cells_decomposition _ _) =>
 [[[[[fc cc] lcc] lc] le] he].
case oca_eq:(opening_cells_aux _ _ _ _) => [nos lno].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vl vp nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
move=> g; rewrite ocd -2!cat_rcons !map_cat /= !(mem_cat, inE).
rewrite orbCA=> /orP[ | gold]; last first.
  by apply/orP; left; rewrite orbCA gold orbT.
suff -> : [seq high c | c <- rcons nos lno] =i rcons (outgoing e) he.
  by rewrite map_rcons !mem_rcons !inE heq=> /orP[-> | ->]; rewrite !orbT.
have := opening_cells_aux_high vl vp oute'; rewrite oca_eq /=.
rewrite map_rcons=> -> g'; rewrite !mem_rcons !inE mem_sort; congr (_ || _).
by have := opening_cells_aux_high_last vl vp oute'; rewrite oca_eq /= => ->.
Qed.

Lemma step_keeps_subset : 
  let s' :=  step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  {subset [seq high c | c <- state_open_seq s'] <=
    [seq high c | c <- open] ++ outgoing e}.
Proof.
rewrite /step/=/generic_trajectories.simple_step.
case: ifP => [pxaway | /negbFE/eqP/[dup] pxhere /abovelstle palstol].
  rewrite -/(open_cells_decomposition _ _).
  case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
rewrite /state_open_seq /= -catA.
  by have := step_keeps_subset_default; rewrite oe oca_eq.
case: ifP=> [eabove | ebelow].
  rewrite -/(open_cells_decomposition _ _).
  case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
  have eabove' : point e >>> low (head dummy_cell lop).
    have llopq : low (head dummy_cell lop) = lsthe.
      apply: esym; rewrite lstheq.
      move: (exi' eabove)=> [w + _].
      move: adj=> /adjacent_catW[] _.
      by case: (lop) => [ // | ? ?] /andP[] /eqP.
    by rewrite llopq.
  move: adj rfo sval; rewrite /open -cat_rcons => adj' rfo' sval'.
  have := open_cells_decomposition_cat adj' rfo' sval' (exi' eabove) eabove'.
  rewrite oe' cat_rcons => oe.
  rewrite /state_open_seq /= -!catA /=.
  have := step_keeps_subset_default.
  by rewrite oe oca_eq; rewrite cat_rcons -!catA.
have ebelow' : point e <<= lsthe by exact (negbFE ebelow).
case: ifP => [ebelow_st | enolsthe].
  have belowo : point e <<< high lsto by rewrite -lstheq.
  have := open_cells_decomposition_single adj rfo sval palstol belowo.
  move=> oe.
  have [ocd [lcc_ctn [_ [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
  have [pal puh vl vp nc]:=
   decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
  rewrite /update_open_cell/generic_trajectories.update_open_cell /state_open_seq.
  case ogq: (outgoing e) => [ | fog ogs] /=.
    have := step_keeps_subset_default; rewrite oe ogq /=.
    rewrite !cats0.
    do 2 rewrite -/(vertical_intersection_point _ _).
    by rewrite (pvertE vl) (pvertE vp) /= !map_cat /=.
  have := step_keeps_subset_default; rewrite oe ogq /=.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos'] lno'] /=.
    have := opening_cells_aux_absurd_case vl vp => /(_ (fog :: ogs) isT).
    by rewrite -ogq => /(_ oute); rewrite ogq oca_eq.
  move=> main g gin; apply: main; move: gin.
  by repeat (rewrite !map_cat /=); rewrite -!catA.
rewrite -/(open_cells_decomposition _ _).
case oe' : (open_cells_decomposition _ _) => [[[[[fc' cc] lcc] lc] le] he].
rewrite -/(update_open_cell_top _ _ _).
case uoctq: update_open_cell_top => [nos lno].
rewrite /state_open_seq /= -!catA.
move=> g /mapP [c cin gq]; rewrite gq {gq}.
have exi2 : exists2 c, c \in lsto :: lop & contains_point' (point e) c.
  exists lsto; first by rewrite inE eqxx.
  by rewrite /contains_point' palstol -lstheq ebelow'.
have := open_cells_decomposition_cat adj rfo sval exi2 palstol.
rewrite oe'=> oe.
have [ocd [lcc_ctn [_ [all_nct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vl vp nc]:=
   decomposition_connect_properties rfo sval adj cbtom
    (inside_box_between inbox_e) oe.
have := last_step_situation oe' pxhere (negbT enolsthe) ebelow'.
move=> [fc'0 [leo [cc' ccq]]].
case ogq : (outgoing e) => [ | fog ogs]; last first.
  move: uoctq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top.
  rewrite -/(opening_cells_aux _ _ _ _).
  case oca_eq : (opening_cells_aux _ _ _ _) => [ [ | fno nos'] lno'].
    have ogn : outgoing e != [::] by rewrite ogq.
    have := opening_cells_aux_absurd_case vlo vp ogn oute.
    by rewrite oca_eq.
  rewrite ogq.
  have := step_keeps_subset_default; rewrite oe.
  rewrite leo oca_eq fc'0 cats0 /= -ogq.
  move=> main [] nosq lnoq; apply: main.
  move: cin; rewrite mem_cat map_cat=> /orP[cin |cin].
    by rewrite mem_cat map_f.
  rewrite 2!mem_cat inE fc'0 /= -nosq inE -orbA in cin.
  rewrite mem_cat /=; apply/orP; right.
  move: cin=> /orP[/eqP -> | cin].
    by rewrite high_set_left_pts inE eqxx.
  rewrite inE; apply/orP; right.
  by apply/map_f; rewrite mem_cat inE lnoq.
move: uoctq; rewrite /update_open_cell_top/generic_trajectories.update_open_cell_top ogq => -[] nosq lnoq.
move: cin; rewrite /open ocd fc'0 -nosq !cats0 /= mem_cat.
rewrite map_cat inE mem_cat.
move=> /orP[cin | cin].
  by rewrite map_f.
apply/orP; right.
rewrite map_cat mem_cat; apply/orP; right.
move: cin=> /orP[/eqP -> | cin].
  by rewrite -lnoq /= heq inE eqxx.
by rewrite /= inE map_f ?orbT.
Qed.

(* Keeping as a record that this statement should be proved.  However,
  since this statement is not used yet, we do not start a proof. *)
Definition TODO_step_keeps_left_pts_inf :=
  let s' := step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  {in state_open_seq s', forall c, lexPt (bottom_left_corner c) (point e)}.

Lemma step_keeps_left_limit_has_right_limit_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) := opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  {in fc ++ nos ++ lno :: lc, 
   forall c p, inside_box p -> left_limit c = p_x p ->
     contains_point' p c ->
     has (inside_closed' p) 
      (cls ++ lstc :: rcons (closing_cells (point e) cc)
         (close_cell (point e) lcc))}.
Proof.
case oe : (open_cells_decomposition _ _) =>
 [[[[[fc cc] lcc] lc] le] he].
case oca_eq:(opening_cells_aux _ _ _ _) => [nos lno].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vl vp nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
remember (fc ++ nos ++ lno :: lc) as open' eqn:openeq.
remember (cls ++ lstc :: rcons (closing_cells (point e) cc)
           (close_cell (point e) lcc)) as closed' eqn:closeeq.
have := invariant1_default_case.
  rewrite oe oca_eq => - [] clae' [] sval' [] adj' []cbtom' rfo'. 
move=> c cin pt' inboxp lbnd pin.
move: cin; rewrite openeq -cat_rcons !mem_cat orbCA orbC=> /orP[cold | cnew].
  rewrite closeeq -cat_rcons has_cat; apply/orP; left.
  apply: (left_limit_has_right_limit _ inboxp lbnd pin).
  by rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
have lcco : lcc \in open.
  by rewrite ocd !(mem_cat, inE) eqxx !orbT.
have ppe : p_x pt' = p_x (point e).
  have := (opening_cells_left oute vl vp); rewrite /opening_cells oca_eq.
  by rewrite -lbnd; apply.
have adjcc : adjacent_cells cc.
  by move: adj; rewrite ocd=> /adjacent_catW[] _ /adjacent_catW[].
have valcc : seq_valid cc (point e).
  by apply/allP=> x xin; apply: (allP sval); rewrite ocd !mem_cat xin ?orbT.
have lonew : low (head dummy_cell
                 (opening_cells (point e) (outgoing e) le he)) = le.
  have := adjacent_opening_aux vl vp oute'; rewrite /opening_cells oca_eq.
  by move=> /(_ _ _ erefl) [].
have lonew' : head dummy_edge
    [seq low c | c <- opening_cells (point e) (outgoing e) le he] = le.
  move: (opening_cells_not_nil (outgoing e) le he) lonew.
  by set w := opening_cells _ _ _ _; case: w=> [ | a tl].
have highnew : [seq high i | i <- opening_cells (point e)(outgoing e) le he]=
               rcons (sort (@edge_below _) (outgoing e)) he.
  by rewrite (opening_cells_high vl vp).
have allval : all (fun g => valid_edge g pt')
     (head dummy_edge [seq low i | i <- opening_cells (point e) 
              (outgoing e) le he] ::
     [seq high i | i <- opening_cells (point e) (outgoing e) le he]).
  apply/allP=> x; rewrite inE=> xin.
  suff : valid_edge x (point e) by rewrite /valid_edge/generic_trajectories.valid_edge ppe.
  move: xin=> /orP[/eqP xin | xin]; first by rewrite xin lonew'.
  rewrite (opening_cells_high vl vp) // ?mem_rcons inE mem_sort in xin.
  case/orP: xin=> [/eqP -> // | xin ].
  apply: valid_edge_extremities; apply/orP; left.
  by apply: oute.
set lec := head lcc cc.
have [cc' ccq] : exists cc', rcons cc lcc = lec :: cc'.
  rewrite /lec; case: (cc) => [ | a b]; first by exists [::].
  by exists (rcons b lcc).
have lecc : lec \in rcons cc lcc by rewrite ccq inE eqxx.
have lecin : lec \in open.
  by rewrite ocd -cat_rcons !mem_cat lecc ?orbT.
have vhlece : valid_edge (high lec) (point e).
  by have := seq_valid_high sval (map_f high lecin).
have vhlecp : valid_edge (high lec) pt'.
  by move: vhlece; rewrite /valid_edge/generic_trajectories.valid_edge ppe.
move: adj'; rewrite -catA -cat_rcons =>
  /adjacent_catW[] _ /adjacent_catW[] adjo _.
have adjo' : adjacent_cells (opening_cells (point e) (outgoing e) le he).
  by rewrite /opening_cells oca_eq.
have [yle | yabove] := lerP (p_y pt') (p_y (point e)).
  have pale : pt' >>> le.
    have /mem_seq_split [s1 [s2 s1s2q]] := cnew.
    case s1q : s1 => [ | c0 s1'].
      move: lonew; rewrite /opening_cells oca_eq s1s2q s1q /= => <-.
      by move: pin=> /andP[].
    have lco : low c \in outgoing e.
      have := seq_low_high_shift
                (opening_cells_not_nil (outgoing e) le he (point e))
                adjo'.
      rewrite /opening_cells oca_eq /= s1s2q s1q /= => - [].
      rewrite -[RHS]/[seq high i | i <- (c0 :: s1') ++ c :: s2] -s1q -s1s2q.
      move: (opening_cells_high vl vp oute); rewrite /opening_cells oca_eq.
      move=> ->=> /rcons_inj [] lows _.
      have : low c \in [seq low i | i <- s1' ++ c :: s2].
        by apply: map_f; rewrite mem_cat inE eqxx orbT.
      by rewrite lows mem_sort.
    have vlce : valid_edge (low c) (point e).
      by apply: valid_edge_extremities; rewrite (oute lco).
    move: pin => /andP[] + _; rewrite under_pvert_y; last first.
      by move: vlce; rewrite /valid_edge/generic_trajectories.valid_edge ppe.
    rewrite -(same_pvert_y vlce); last by apply/eqP.
    by rewrite on_pvert ?yle // -(eqP (oute lco)) // left_on_edge.
  have plec : contains_point' pt' lec.
    rewrite /contains_point' -leq pale.
    rewrite under_pvert_y //.
    apply: (le_trans yle).
    rewrite -(same_pvert_y vhlece); last by apply/eqP.
    rewrite -under_pvert_y //.
    case ccq': cc => [ | cc0 ccs].
      by move: ccq; rewrite ccq' /= => -[] <- _; rewrite -heq; apply/underW.
    suff/allct/andP[] : lec \in cc by [].
    by move: ccq; rewrite ccq' /= => -[] -> _; rewrite inE eqxx.
  have [/eqP lbnd' | safe] := boolP(left_limit lec == p_x pt').
    rewrite closeeq has_cat.
    have := (left_limit_has_right_limit lecin inboxp lbnd' plec).
    move=> /hasP[x]; rewrite mem_rcons inE => /orP[] xin xP.
      by apply/orP; right; apply/hasP; exists x=> //; rewrite inE xin.
    by apply/orP; left; apply/hasP; exists x.
  have lbnd2 : left_limit lec < p_x pt'.
    rewrite lt_neqAle safe /=.
    rewrite ppe; apply/lexePt_xW/lexPtW.
    by apply: (btm_left lecin).
  rewrite closeeq has_cat; apply/orP; right.
  apply/hasP; exists (close_cell (point e) lec).
    rewrite inE; apply/orP; right; rewrite /closing_cells -map_rcons.
    by apply:map_f; rewrite ccq inE eqxx.
  have vlec : valid_cell lec (point e).
    by apply/andP/(allP sval).
  rewrite inside_closed'E /left_limit.
  have [-> -> ->]:= close_cell_preserve_3sides (point e) lec.
  move: plec=> /andP[] -> ->.
  by rewrite (close_cell_right_limit) // lbnd2 ppe lexx.
have plcc : contains_point' pt' lcc.
  have puhe : pt' <<= he.
    have /mem_seq_split [s1 [s2 s1s2q]] := cnew.
    elim /last_ind: {2} (s2) (erefl s2) => [ | s2' c2 _] s2q.
      move: highnew; rewrite /opening_cells oca_eq s1s2q s2q cats1 map_rcons.
      move=>/rcons_inj[] _ <-.
      by move: pin => /andP[].
    have hco : high c \in outgoing e.
      have := opening_cells_high vl vp oute.
      rewrite /opening_cells oca_eq s1s2q s2q.
      rewrite (_ : [seq high i | i <- s1 ++ c :: rcons s2' c2] =
             rcons [seq high i | i <- s1 ++ c :: s2'] (high c2)); last first.
        by rewrite !map_cat /= map_rcons -!cats1 /= -!catA /=.
      move=> /rcons_inj[] his _.
      have : high c \in [seq high i | i <- s1 ++ c :: s2'].
        by apply: map_f; rewrite mem_cat inE eqxx orbT.
      by rewrite his mem_sort.
    have vhce : valid_edge (high c) (point e).
      by apply: valid_edge_extremities; rewrite (oute hco).
    move: (pin) => /andP[] _; rewrite under_pvert_y; last first.
      by move: vhce; rewrite /valid_edge/generic_trajectories.valid_edge ppe.
    rewrite -(same_pvert_y vhce); last by apply/eqP.
    rewrite on_pvert; last first.
      by rewrite -(eqP (oute hco)) // left_on_edge.
    move=> ple.
    have ppe': p_y pt' = p_y (point e).
      by apply: le_anti; rewrite ple (ltW yabove).
    have/eqP -> : pt' == point e :> pt by rewrite pt_eqE ppe ppe' !eqxx.
    by apply/underW.
  rewrite /contains_point'; rewrite -heq puhe andbT.
  have vllcce : valid_edge (low lcc) (point e).
    by apply: (seq_valid_low sval); apply/map_f.
  have vllccp : valid_edge (low lcc) pt'.
    by move: vllcce; rewrite /valid_edge/generic_trajectories.valid_edge ppe.
  rewrite under_pvert_y // -?ltNge.
  apply: le_lt_trans yabove.  
  rewrite -(same_pvert_y vllcce); last by apply/eqP.
  rewrite leNgt -strict_under_pvert_y //.
  by have /andP[] := lcc_ctn.
have [/eqP lbnd' | safe] := boolP(left_limit lcc == p_x pt').
  rewrite closeeq has_cat /= orbA.
  have := left_limit_has_right_limit lcco inboxp lbnd' plcc.
  move/hasP=> [x]; rewrite mem_rcons inE=> /orP[/eqP -> ->| xin xP].
    by rewrite orbT.
  by apply/orP; left; apply/orP; left; apply/hasP; exists x.
have lbnd2 : left_limit lcc < p_x pt'.
  rewrite lt_neqAle safe /=.
  rewrite ppe; apply/lexePt_xW/lexPtW.
  by apply: (btom_left_corners lcco).
rewrite closeeq has_cat; apply/orP; right.
apply/hasP; exists (close_cell (point e) lcc).
  by rewrite inE mem_rcons inE eqxx ?orbT.
have vlcc : valid_cell lcc (point e).
  by apply/andP/(allP sval).
rewrite inside_closed'E /left_limit.
have [-> -> ->]:= close_cell_preserve_3sides (point e) lcc.
move: plcc=> /andP[] -> ->.
by rewrite (close_cell_right_limit) // lbnd2 ppe lexx.
Qed.

(* This statement is the normal lifting of the previous statement from
 the default case to the complete step function.  However, this proof
 is not used for now, so we make it a definition just to keep in records what
 should be the lemma statement. *)
Definition TODO_step_keeps_cover_left_border :=
  let s' :=  step (Bscan fop lsto lop cls lstc lsthe lstx) e in
  {in state_open_seq s', forall c p, inside_box p -> left_limit c = p_x p ->
     contains_point' p c ->
     has (inside_closed' p) (state_closed_seq s')}.
(*
Proof.
have [ + [+ [+ []]]] := step_keeps_invariant1.
set open0 := state_open_seq _ => + + + + + step_res c cin pt.
have := step_keeps_left_pts_inf.
have noc' : {in cell_edges open ++ outgoing e &, no_crossing R}.
  by move=> g1 g2 g1in g2in; apply: noc; rewrite /= !mem_cat orbA
   -2!mem_cat ?g1in ?g2in.
*)

(* The following statement is not necessary for a safety statement, since a
  vertical cell decomposition that returns an empty list of cells would indeed
  return only cells whose interior is safe. *)

Lemma step_keeps_cover_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) := opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  cover_left_of p (fc ++ nos ++ lno :: lc)
    (cls ++ lstc :: rcons (closing_cells (point e) cc)
         (close_cell (point e) lcc)).
Proof.
case oe : (open_cells_decomposition _ _) =>
 [[[[[fc cc] lcc] lc] le] he].
case oca_eq:(opening_cells_aux _ _ _ _) => [nos lno].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have oc_eq : opening_cells (point e) (outgoing e) le he = rcons nos lno.
  by rewrite /opening_cells oca_eq.
have [pal puh vl vp nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
remember (fc ++ nos ++ lno :: lc) as open' eqn:openeq.
remember (cls ++ lstc :: rcons (closing_cells (point e) cc)
           (close_cell (point e) lcc)) as closed' eqn:closeeq.
have := invariant1_default_case.
rewrite oe oca_eq => - [] clae' [] sval' [] adj' []cbtom' rfo'. 
have := step_keeps_left_limit_has_right_limit_default.
have := step_keeps_btom_left_corners_default.
rewrite oe oca_eq -openeq.
move=> btm_left' left_border_in'.
move=> q inbox_q limrq.
have [qright | qleft] := boolP(lexPt (point e) q).
  rewrite /inside_box in inbox_q.
  move: (inbox_q) => /andP[] bet_q _.
  have [c cin ctn]:= exists_cell cbtom' adj' bet_q.
  move: cin.

  have subpq1 : subpred (lexePt p) (lexePt q).
    by move=> x px; apply/(lexePt_trans limrq).
  have limr : all (lexePt p) [seq point x | x <- future_events].
    by apply/allP=> x /mapP [ev evc ->]; apply: plexfut.
  have limrq1 := sub_all subpq1 limr.
  rewrite -catA -cat_rcons !mem_cat orbCA -mem_cat=> /orP[] cin; last first.
    have [inc | ninc] := boolP(inside_open' q c).
      apply/orP; left;  rewrite openeq -cat_rcons !has_cat orbCA -has_cat.
      by apply/orP; right; apply/hasP; exists c.
    have cin0 : c \in open.
     by rewrite ocd -cat_rcons !mem_cat orbCA -mem_cat cin ?orbT.
    have cin1 : c \in open'.
      by rewrite openeq -cat_rcons !mem_cat orbCA -mem_cat cin orbT.
    apply/orP; right.
    rewrite closeeq -cat_rcons has_cat; apply/orP; left.
    move: ninc; rewrite inside_open'E; rewrite lt_neqAle.
    move: (ctn)=> /andP[] -> -> /=.
    have -> : left_limit c <= p_x q.
      have : p_x (point e) <= p_x q by apply/lexePt_xW/lexPtW.
      apply: le_trans.
      rewrite /left_limit -[X in X <= _]/(p_x (bottom_left_corner c)).
      by apply/lexePt_xW/lexPtW; apply: btm_left.
   have -> : p_x q <= open_limit c.
      rewrite /open_limit le_min.
      have extg :
         forall g, g \in [:: bottom; top] -> p_x q <= p_x (right_pt g).
        move: inbox_q=> /andP[] _ /andP[] /andP[] _ /ltW + /andP[] _ /ltW.
        by move=> A B g; rewrite !inE=> /orP[] /eqP ->.
      have intg g : has (event_close_edge g) future_events ->
           p_x q <= p_x (right_pt g).
        move=>/hasP[] ev' ev'in /eqP ->.
        by apply/lexePt_xW/(lexePt_trans limrq)/(allP limr)/map_f.
      move: clae'; rewrite -catA -openeq=> /allP /(_ _ cin1) /andP[].
      by move=> /orP[/extg | /intg] -> /orP[/extg | /intg] ->.
    rewrite !andbT negbK => /eqP atll.
    by apply: (left_limit_has_right_limit _ inbox_q atll ctn).

  have limrq' : forall e, e \in future_events -> lexePt q (point e).
    by move/(sub_all subpq1): (limr); rewrite all_map=>/allP.
  have [vertp | rightofp] : left_limit c = p_x q \/ left_limit c < p_x q.
      have cin' :  c \in opening_cells (point e) (outgoing e) le he.
        by rewrite oc_eq.
      rewrite (opening_cells_left oute vl vp cin').
      move: qright=> /lexPtW/lexePt_xW; rewrite le_eqVlt=> /orP[/eqP -> | ->].
        by left.
      by right.
    rewrite closeeq (left_border_in' _ _ _ _ vertp ctn) ?orbT //.
    by rewrite openeq -cat_rcons !mem_cat cin ?orbT.
  apply/orP; left; rewrite openeq -cat_rcons; rewrite !has_cat.
  apply/orP; right; apply/orP; left.
  apply/hasP; exists c=> //.
  rewrite inside_open'E rightofp /open_limit le_min.
  have [/andP[_ ->] /andP[_ ->]] : valid_cell c q.
    have := opening_valid oute vl vp=> /allP; rewrite oc_eq=> /(_ c cin).
    move=> /andP[] vlce vhce.
    have := (allP clae' c); rewrite -catA -cat_rcons !mem_cat cin orbT.
    move=> /(_ isT).
    move=> /andP[] end_edge_lc end_edge_hc.
    have :=
      valid_between_events (lexPtW qright) limrq' vlce inbox_q end_edge_lc.
    have :=
      valid_between_events (lexPtW qright) limrq' vhce inbox_q end_edge_hc.
    move=> vhcq vlcq.
    by split.
  by move: ctn=> /andP[] -> ->.
have qe : p_x q <= p_x (point e).
  by apply: lexePt_xW; rewrite lexePtNgt.
have inclosing : forall c, c \in cc -> inside_open' q c ->
  (forall c, c \in cc -> valid_edge (low c) (point e) &&
     (valid_edge (high c) (point e))) ->
  exists2 c', c' \in closing_cells (point e) cc & inside_closed' q c'.
  move=> c cin ins allval.
  exists (close_cell (point e) c).
    by apply: map_f.
  move: ins; rewrite inside_open'E andbA=>/andP[] ctn /andP[liml _] /=.
  move: ctn=>/andP [qlc qhc].
  rewrite /contains_point/close_cell /=.
  have [p1 vip1] := exists_point_valid (proj1 (andP (allval _ cin))).
  have [p2 vip2] := exists_point_valid (proj2 (andP (allval _ cin))).
  have [onl x1] := intersection_on_edge vip1.
  have [onh x2] := intersection_on_edge vip2.
  by rewrite inside_closed'E vip1 vip2 qlc qhc; case: ifP=> [p1e | p1ne];
    case: ifP=> [p2e | p2ne]; rewrite liml /right_limit /= -?x2 -?x1.
(* TODO : inclosing and inclosel could probably be instances of a single
  statement. maybe replacing cc with rcons cc lcc in the statement of
  inclosing. *)
have inclosel : inside_open' q lcc ->
  inside_closed' q (close_cell (point e) lcc).
  rewrite inside_open'E andbA=> /andP[] /andP[qlc qhc] /andP[liml _] /=.
  have lccin : lcc \in open by rewrite ocd !mem_cat inE eqxx ?orbT.
  have [p1 vip1] := exists_point_valid (proj1 (andP (allP sval _ lccin))).
  have [p2 vip2] := exists_point_valid (proj2 (andP (allP sval _ lccin))).
  have [onl x1] := intersection_on_edge vip1.
  have [onh x2] := intersection_on_edge vip2.
  by rewrite inside_closed'E /close_cell vip1 vip2 qlc qhc /=;
    case: ifP=> [p1e | p1ne]; case: ifP=> [p2e | p2ne];
    rewrite liml /right_limit /= -?x2 -?x1.
move: qleft; rewrite -lexePtNgt lexePt_eqVlt.
have svalcc :
   forall c : cell,
     c \in cc -> valid_edge (low c) (point e) && valid_edge (high c) (point e).
   by move=> x xin; apply: (allP sval); rewrite ocd !mem_cat xin orbT.
move=> /orP[/eqP qe' | qlte ].
  rewrite qe'.
  apply/orP; right; apply/hasP.
  set opc := head lcc cc.
  have opcin' : opc \in open.
    rewrite ocd -cat_rcons !mem_cat orbCA; apply/orP; left.
    by rewrite /opc; case: (cc)=> [ | ? ?]; rewrite /= inE eqxx.
  have adjcc : adjacent_cells cc.
    by move: adj; rewrite ocd => /adjacent_catW[] _ /adjacent_catW[].
  have opc_ctn' : contains_point' (point e) opc.
    rewrite /contains_point' -leq pal /=.
    case ccq : cc => [ | c1 cc']; rewrite /opc ccq /=.
      by rewrite -heq; apply underW.
    by have /allct/andP[] : c1 \in cc by rewrite ccq inE eqxx.
  have [leftb | ] :=
    boolP(p_x (last dummy_pt (left_pts opc)) < p_x (point e)); last first.
    move=> nleftb.
    have := btom_left_corners opcin';rewrite /bottom_left_corner.
    rewrite /lexPt (negbTE nleftb) /= => /andP[/eqP sx yl].
    have /hasP[x xin xP] :=
      left_limit_has_right_limit opcin' inbox_e sx opc_ctn'.
    exists x=> //.
    by rewrite closeeq -cat_rcons mem_cat xin.
  have : inside_open' (point e) opc.
    have elt: all (lexePt (point e)) [seq point e0 | e0 <- e :: future_events].
      rewrite /=; rewrite lexePt_eqVlt eqxx /=.
      move: sort_evs; rewrite path_sortedE; last exact: lexPtEv_trans.
      move=> /andP[cmpE _]; apply/allP=> x /mapP[ev evin ->].
      by apply/lexPtW/(allP cmpE).
    by apply: (contains_to_inside_open' sval clae inbox_e leftb).
  move: (opc_ctn').
  rewrite -qe'=> einopc einop'.
  case ccq : cc => [ | cc1 cc'] /=.
    exists (close_cell (point e) lcc).
      by rewrite closeeq !(mem_cat, inE, mem_rcons) eqxx ?orbT.
    by apply: inclosel; move: einop'; rewrite /opc ccq.
  have opcincc : opc \in cc by rewrite /opc ccq /= inE eqxx.
  have [it itin itP]:= inclosing opc opcincc einop' svalcc.
  exists it; last by [].
  by rewrite closeeq mem_cat inE mem_rcons inE itin ?orbT.
have /orP[| already_closed]:=
    cover_left_of_e inbox_q (lexPtW qlte); last first.
  by rewrite closeeq -cat_rcons has_cat already_closed orbT.
rewrite openeq ocd -2!cat_rcons 2!has_cat orbCA.
move=> /orP[/hasP[opc opcin qinopc] | keptopen].
  move: opcin; rewrite mem_rcons inE=> /orP[opclcc | opcin]; last first.
    have [it it1 it2] := inclosing _ opcin qinopc svalcc.
    apply/orP; right; apply/hasP.
    by exists it=> //; rewrite closeeq !(inE, mem_cat, mem_rcons) it1 ?orbT.
  apply/orP; right; apply/hasP; exists (close_cell (point e) lcc).
    by rewrite closeeq !(mem_cat, inE, mem_rcons) eqxx ?orbT. 
  by apply: inclosel; rewrite -(eqP opclcc).
apply/orP; left; apply/hasP.
move: keptopen; rewrite -has_cat=>/hasP[it + it2].
by rewrite mem_cat=> infclc; exists it; rewrite // !mem_cat orbCA infclc orbT.
Qed.

Lemma step_keeps_right_limit_closed_default :
  let '(fc, cc, lcc, lc, le, he) :=
    open_cells_decomposition open (point e) in
    let '(nos, lno) := opening_cells_aux (point e)
       (sort (@edge_below _) (outgoing e)) le he in
  {in  rcons(cls ++ 
          lstc :: closing_cells (point e) cc) (close_cell (point e) lcc) &
     future_events, forall c e, right_limit c <= p_x (point e)}.
Proof.
case oe : (open_cells_decomposition _ _) =>
 [[[[[fc cc] lcc] lc] le] he].
case oca_eq:(opening_cells_aux _ _ _ _) => [nos lno].
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
move=> c ev; rewrite mem_rcons=> cin evin.
suff rl_ev' : right_limit c <= p_x (point e).
  apply: (le_trans rl_ev').
  move: sort_evs; rewrite /= path_sortedE; last by apply: lexPtEv_trans.
  move=> /andP[] /allP /(_ ev evin) /orP[/ltW // | /andP[] /eqP -> _] _.
  by apply: le_refl.
have := sval; rewrite ocd /seq_valid !all_cat=> /andP[] _ /andP[] svalcc /=.
move=> /andP[] /andP[] vllcc vhlcc _.
move: cin; rewrite inE => /orP[/eqP -> | ].
  by have := right_limit_close_cell vllcc vhlcc=> ->; apply: le_refl.
rewrite mem_cat=> /orP[cold | ].
  by apply: closed_right_limit; rewrite mem_rcons inE cold orbT.
rewrite inE=> /orP[cold | ].
  by apply: closed_right_limit; rewrite mem_rcons inE cold.
move=> /mapP [c' c'in ->].
have /andP[vlc' vhc'] := allP svalcc c' c'in.
by rewrite (right_limit_close_cell vlc' vhc') le_refl.
Qed.

(* TODO : move to other file *)
Lemma close_cell_in (p' : pt) c :
  valid_cell c p' ->
  p' \in (right_pts (close_cell p' c): seq pt).
Proof.
move=> [] vl vh.
rewrite /close_cell; rewrite (pvertE vl) (pvertE vh) /=.
by case: ifP=> [/eqP <- | ];
  case: ifP=> [/eqP <- // | _ ]; rewrite !inE eqxx ?orbT.
Qed.

Lemma last_closing_side_char pp fc cc lcc lc le he :
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  cc != [::] ->
  in_safe_side_right pp (close_cell (point e) lcc) =
   [&& p_x pp == p_x (point e), p_y (point e) < p_y pp & pp <<< he].
Proof.
move=> oe ccn0.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
have lccin : lcc \in open by rewrite ocd !(mem_cat, inE) eqxx !orbT.
have /andP [vlcc vhcc] : valid_edge (low lcc) (point e) &&
  valid_edge (high lcc) (point e) by apply: (allP sval).
have := right_limit_close_cell vlcc vhcc.
rewrite /in_safe_side_right.
move=> ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have [-> -> _] := close_cell_preserve_3sides (point e) lcc.
rewrite -heq.
have eonllcc : (point e) === low lcc.
  have := open_cells_decomposition_point_on cbtom adj 
            (inside_box_between inbox_e) sval oe.
  elim /last_ind: {-1} (cc) (erefl cc) ccn0 => [ | cc' cc2 _] ccq // _.
  have : cc2 \in rcons cc' cc2 by rewrite mem_rcons mem_head.
  move=> + /(_ cc2) =>/[swap] /[apply].
  move: adj; rewrite ocd ccq cat_rcons; do 2 move =>/adjacent_catW[] _. 
  by move=> /= /andP[] /eqP ->.
have vppl : valid_edge (low lcc) pp.
  by rewrite (same_x_valid _ samex).
have vpphe : valid_edge he pp.
  by rewrite (same_x_valid _ samex).
rewrite (under_pvert_y vppl) (same_pvert_y vppl samex) -ltNge.
rewrite (on_pvert eonllcc).
rewrite (andbC _ (pp <<< he)).
have [ppuh | ] := boolP (pp <<< he); last by [].
have [ppae | ] := boolP (p_y (point e) < p_y pp); last by [].
rewrite /right_pts/close_cell (pvertE vlcc) (pvertE vhcc) /=.
rewrite !pt_eqE !eqxx /=.
rewrite (on_pvert eonllcc) eqxx.
rewrite -heq; move: (puh).
rewrite (strict_under_pvert_y vhe) lt_neqAle eq_sym=>/andP[]/negbTE -> _.
have ppuhy : (p_y pp == pvert_y (point e) he) = false.
  apply/negbTE; move: (ppuh).
  rewrite (strict_under_pvert_y vpphe) lt_neqAle=> /andP[] + _.
  by rewrite (same_pvert_y vpphe samex).
rewrite !(@in_cons [eqType of pt]).
rewrite !pt_eqE ppuhy andbF orbF.
move: ppae; rewrite lt_neqAle eq_sym=>/andP[] /negbTE -> _.
by rewrite andbF.
Qed.

Lemma first_closing_side_char pp fc cc1 cc lcc lc le he :
  open_cells_decomposition open (point e) = (fc, cc1 :: cc, lcc, lc, le, he) ->
  in_safe_side_right pp (close_cell (point e) cc1) =
   [&& p_x pp == p_x (point e), p_y pp < p_y (point e) & pp >>> le].
Proof.
move=> oe.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [/= leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
have cc1in : cc1 \in open by rewrite ocd !(mem_cat, inE) eqxx !orbT.
have /andP [vlcc1 vhcc1] : valid_edge (low cc1) (point e) &&
  valid_edge (high cc1) (point e) by apply: (allP sval).
have := right_limit_close_cell vlcc1 vhcc1.
rewrite /in_safe_side_right.
move=> ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have [-> -> _] := close_cell_preserve_3sides (point e) cc1.
rewrite -leq.
have eonhcc1 : (point e) === high cc1.
  have := open_cells_decomposition_point_on cbtom adj 
            (inside_box_between inbox_e) sval oe.
  by move=> /(_ cc1 (mem_head _ _)).
have vpph : valid_edge (high cc1) pp.
  by rewrite (same_x_valid _ samex).
have vpple : valid_edge le pp.
  by rewrite (same_x_valid _ samex).
rewrite (strict_under_pvert_y vpph) (same_pvert_y vpph samex).
rewrite (on_pvert eonhcc1).
have [ppue /= | ] := boolP (p_y pp < p_y (point e)); last by [].
have [ppal/= | ] := boolP (pp >>> le); last by [].
rewrite /right_pts/close_cell (pvertE vlcc1) (pvertE vhcc1) /=.
rewrite !pt_eqE !eqxx /=.
rewrite (on_pvert eonhcc1) eqxx.
rewrite -leq; move: (pal).
rewrite (under_pvert_y vle) -ltNge lt_neqAle=> /andP[] /negbTE -> _.
have ppaly : (p_y pp == pvert_y (point e) le) = false.
  apply/negbTE; move: (ppal).
  rewrite (under_pvert_y vpple) -ltNge lt_neqAle eq_sym=> /andP[] + _.
  by rewrite (same_pvert_y vpple samex).
rewrite !(@in_cons [eqType of pt]) !pt_eqE ppaly andbF.
move: ppue; rewrite lt_neqAle eq_sym=>/andP[] /negbTE -> _.
by rewrite andbF.
Qed.

Lemma middle_closing_side_char pp fc cc1 cc lcc lc le he :
  open_cells_decomposition open (point e) = (fc, cc1 :: cc, lcc, lc, le, he) ->
  ~~ has (in_safe_side_right pp) [seq close_cell (point e) c | c <- cc].
Proof.
move=> oe.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
rewrite -all_predC; apply/allP=> c /mapP [c' cin cq] /=.
have /andP[vlc' vhc']: valid_edge (low c') (point e) &&
       valid_edge (high c') (point e).
  by apply: (allP sval); rewrite ocd !(mem_cat, inE) cin !orbT.
have := right_limit_close_cell vlc' vhc'.
have allon := open_cells_decomposition_point_on cbtom adj 
            (inside_box_between inbox_e) sval oe.
have /allon eonh : c' \in cc1 :: cc by rewrite inE cin orbT.
have eonl : point e === low c'.
  have [s1 [s2 ccq]] := mem_seq_split cin.
  have := adj; rewrite ocd ccq /= => /adjacent_catW[] _ /=.
  rewrite /= cat_path=> /andP[] + _.
  rewrite cat_path=> /andP[] _ /= /andP[] /eqP <- _.
  by apply: allon; rewrite ccq -cat_cons mem_cat mem_last.
rewrite /in_safe_side_right cq=> ->.
have [-> -> _] := close_cell_preserve_3sides (point e) c'.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have vpph : valid_edge (high c') pp.
  by rewrite (same_x_valid _ samex).
have vppl : valid_edge (low c') pp.
  by rewrite (same_x_valid _ samex).
rewrite (strict_under_pvert_y vpph) (same_pvert_y vpph samex).
rewrite (on_pvert eonh).
rewrite (under_pvert_y vppl) (same_pvert_y vppl samex).
rewrite (on_pvert eonl).
by case : ltP; rewrite // le_eqVlt=> ->; rewrite orbT andbF.
Qed.

Lemma mem_no_dup_seq {A: eqType} (s : seq A) : no_dup_seq s =i s.
Proof.
elim: s => [ | a [ | b s] Ih]; first by [].
  by [].
rewrite -[no_dup_seq _]/(if a == b then no_dup_seq (b :: s) else
                           a :: no_dup_seq (b :: s)).
have [ab | anb] := (eqVneq a b).
  by move=> c; rewrite Ih !inE ab; case: (c == b).
by move=> c; rewrite 2!inE Ih.
Qed.

Lemma single_closing_side_char fc lcc lc le he pp :
  open_cells_decomposition open (point e) = (fc, [::], lcc, lc, le, he) ->
  in_safe_side_right pp (close_cell (point e) lcc) =
  ([&& p_x pp == p_x (point e), pp >>> le & p_y pp < p_y (point e)] ||
   [&& p_x pp == p_x (point e), pp <<< he & p_y (point e) < p_y pp]).
Proof.
move=> oe.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [/= leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
have /andP[vllcc vhlcc] : valid_edge (low lcc) (point e) &&
   valid_edge (high lcc) (point e).
  by apply: (allP sval); rewrite ocd /= !(mem_cat, inE) eqxx !orbT.
have [ppe | ppne] := eqVneq (pp : pt) (point e).
  rewrite ppe !lt_irreflexive !andbF.
  apply /negbTE.
  have einr := close_cell_in (conj vllcc vhlcc).
  by rewrite /in_safe_side_right einr !andbF.
have := right_limit_close_cell vllcc vhlcc.
rewrite /in_safe_side_right.
move=> ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have [-> -> _] := close_cell_preserve_3sides (point e) lcc.
rewrite -heq -leq.
have puhy : p_y (point e) < pvert_y (point e) he.
  by rewrite -(strict_under_pvert_y vhe).
have paly :  pvert_y (point e) le < p_y (point e).
  by rewrite ltNge -(under_pvert_y vle).
rewrite /close_cell/right_pts -leq -heq (pvertE vle) (pvertE vhe).
rewrite (@mem_no_dup_seq [eqType of pt]) !(@in_cons [eqType of pt]) (negbTE ppne) /=.
have [vpple vpphe] : valid_edge le pp /\ valid_edge he pp.
  by rewrite !(same_x_valid _ samex).
have [pu | ] := ltrP (p_y pp) (p_y (point e)).
  rewrite !pt_eqE /= andbT samex /=.
  rewrite ltNge le_eqVlt pu orbT andbF orbF.
  have ppuhe : pp <<< he.
    rewrite strict_under_pvert_y // (same_pvert_y _ samex) //.
    apply: (lt_trans pu).
    by rewrite -strict_under_pvert_y.
  rewrite (andbCA _ (pp >>> le)).
  have [ppale /= | ] := boolP (pp >>> le); last by [].
  have ppaly : (p_y pp == pvert_y (point e) le) = false.
    apply/negbTE; move: (ppale).
    rewrite (under_pvert_y vpple) -ltNge lt_neqAle eq_sym=> /andP[] + _.
    by rewrite (same_pvert_y vpple samex).
  have ppuhy : (p_y pp == pvert_y (point e) he) = false.
    apply/negbTE; move: (ppuhe).
    rewrite (strict_under_pvert_y vpphe) lt_neqAle=> /andP[] + _.
    by rewrite (same_pvert_y vpphe samex).
  by rewrite ppaly ppuhy ppuhe.
rewrite le_eqVlt => /orP[samey | /[dup] pa ->].
   by case/negP: ppne; rewrite pt_eqE samex eq_sym samey.
rewrite andbF andbT /=.
have [ppuhe /= | ] := boolP (pp <<< he); last by [].

rewrite !pt_eqE /= samex /=.
have ppale : pp >>> le.
  rewrite under_pvert_y // (same_pvert_y _ samex) // -ltNge.
  apply: (lt_trans _ pa).
  by rewrite ltNge -under_pvert_y.
have ppaly : (p_y pp == pvert_y (point e) le) = false.
  apply/negbTE; move: (ppale).
  rewrite (under_pvert_y vpple) -ltNge lt_neqAle eq_sym=> /andP[] + _.
  by rewrite (same_pvert_y vpple samex).
have ppuhy : (p_y pp == pvert_y (point e) he) = false.
  apply/negbTE; move: (ppuhe).
  rewrite (strict_under_pvert_y vpphe) lt_neqAle=> /andP[] + _.
  by rewrite (same_pvert_y vpphe samex).
by rewrite ppale ppuhy ppaly.
Qed.

Lemma sides_equiv fc cc lcc lc le he:
  open_cells_decomposition open (point e) = (fc, cc, lcc, lc, le, he) ->
  forall p, has (in_safe_side_right p)
              (rcons (closing_cells (point e) cc)
                 (close_cell (point e) lcc)) ==
       has (in_safe_side_left p)
         (opening_cells (point e) (outgoing e) le he).
Proof.
move=> oe pp.
have [ocd [lcc_ctn [allct [allnct [flcnct [heq [leq [lein hein]]]]]]]] :=
    decomposition_main_properties oe exi.
have [pal puh vle vhe nc]:=
    decomposition_connect_properties rfo sval adj cbtom
      (inside_box_between inbox_e) oe.
have [ogq | ogq] := eqVneq (outgoing e) [::].
  rewrite (single_opening_cell_side_char pp vle vhe pal puh ogq).
  case ccq : cc => [ | cc1 cc'].  
    move: (oe); rewrite ccq=> oe'.
    by rewrite /= (single_closing_side_char pp oe') orbF.
  move: (oe); rewrite ccq=> oe'.
  rewrite /= has_rcons.
  rewrite (first_closing_side_char pp oe').
  rewrite (negbTE (middle_closing_side_char _ oe')) orbF.
  rewrite (last_closing_side_char pp oe'); last by []. 
  by rewrite (andbC (pp >>> le)) (andbC (pp <<< he)).
rewrite /opening_cells; case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have oeq : opening_cells (point e) (outgoing e) le he = rcons nos lno.
 by rewrite /opening_cells oca_eq.
have := opening_cells_aux_absurd_case vle vhe ogq oute; rewrite oca_eq /=.
case nosq : nos => [ | fno nos'] // _.
move: oeq; rewrite nosq=> oeq.
rewrite /=.
rewrite (first_opening_cells_side_char pp ogq vle vhe pal oute oeq).
rewrite [in X in _ == X]has_rcons.
rewrite (last_opening_cells_side_char pp ogq vle vhe puh oute oeq).
rewrite (negbTE (middle_opening_cells_side_char pp ogq vle vhe oute oeq)) orbF.
case ccq : cc => [ | cc1 cc'].  
    move: (oe); rewrite ccq=> oe'.
    rewrite /= (single_closing_side_char pp oe') orbF.
    by rewrite (andbC (_ >>> _)) (andbC (_ <<< _)).
move: (oe); rewrite ccq=> oe'.
rewrite /= has_rcons.  
rewrite (first_closing_side_char pp oe').
rewrite (negbTE (middle_closing_side_char _ oe')) orbF.
by rewrite (last_closing_side_char pp oe'); last by []. 
Qed.

End step.

End proof_environment.

Notation open_cell_side_limit_ok :=
  (@open_cell_side_limit_ok R).

Lemma inside_box_left_ptsP bottom top p :
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  inside_box bottom top p -> left_limit (start_open_cell bottom top)  < p_x p.
Proof.
move=> sok /andP[] _ /andP[] /andP[] valb _ /andP[] valt _.
rewrite leftmost_points_max //.
by case : (lerP (p_x (left_pt bottom)) (p_x (left_pt top))).
Qed.

Lemma cell_edges_start bottom top :
  cell_edges [::(start_open_cell bottom top)] = [:: bottom; top].
Proof. by []. Qed.

Record common_general_position_invariant bottom top edge_set s
  (events : seq event) :=
  { inv1 : inv1_seq bottom top events (state_open_seq s);
   lstx_eq : lst_x _ _ s = left_limit (lst_open s);
   high_lsto_eq : high (lst_open s) = lst_high _ _ s;
   edges_sub : {subset all_edges (state_open_seq s) events <=
                    bottom :: top :: edge_set};
   closed_events : close_edges_from_events events;
   out_events : {in events, forall e, out_left_event e};
   inbox_events : all (inside_box bottom top)
           [seq point x | x <- events];
   lex_events : sorted (@lexPtEv _) events;
   sides_ok : all open_cell_side_limit_ok (state_open_seq s);
   general_pos :
     all (fun ev => lst_x _ _ s < p_x (point ev)) events &&
     sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) events;
}.

(* This lemma only provides a partial correctness statement in the case
  where the events are never aligned vertically.  This condition is
  expressed by the very first hypothesis.  TODO: it relies on the assumption
  that the first open cell is well formed.  This basically means that the
  two edges have a vertical overlap.  This statement should be probably
  be made clearer in a different way.

  TODO: one should probably also prove that the final sequence of open
  cells, here named "open", should be reduced to only one element. *)
Record disjoint_general_position_invariant (bottom top : edge)
 (edge_set : seq edge)
 (s : scan_state) (events : seq event) :=
 { op_cl_dis :
     {in state_open_seq s & state_closed_seq s,
       disjoint_open_closed_cells R};
   cl_dis : {in state_closed_seq s &, disjoint_closed_cells R};
   common_inv_dis : common_general_position_invariant bottom top
        edge_set s events;
   pairwise_open : pairwise (@edge_below _)
       (bottom :: [seq high c | c <- state_open_seq s]);
   closed_at_left :
       {in state_closed_seq s & events,
          forall c e, right_limit c <= p_x (point e)};
   }.

Definition dummy_state :=
  Bscan [::] dummy_cell [::] [::] dummy_cell dummy_edge 0.

Definition initial_state bottom top (events : seq event) :=
  match events with
  | [::] => dummy_state
  | ev :: future_events =>
    let (nos, lno) :=
      opening_cells_aux (point ev) (sort (@edge_below _) (outgoing ev))
           bottom top in
      Bscan nos lno [::] [::]
         (close_cell (point ev) (start_open_cell bottom top))
         top (p_x (point ev))
  end.

Lemma initial_intermediate bottom top s events :
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events ->
  bottom <| top ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  close_edges_from_events events ->
  events != [::] ->
  let op0 := (* close_cell (point (head (dummy_event _) events))  *)
               (start_open_cell bottom top) in
  all open_cell_side_limit_ok [:: op0] /\
  cells_bottom_top bottom top [:: op0] /\
  adjacent_cells [:: op0] /\
  seq_valid [:: op0] (point (head dummy_event events)) /\
  s_right_form [:: op0] /\
  all (inside_box bottom top) [seq point e | e <- behead events] /\
  close_edges_from_events (behead events) /\
  {in behead events, forall e, out_left_event e} /\
  close_alive_edges bottom top [:: op0] events  /\
  valid_edge bottom (point (head dummy_event events)) /\
  valid_edge top (point (head dummy_event events)) /\
  open_cells_decomposition ([::] ++ [:: op0])
        (point (head dummy_event events)) =
       ([::], [::], op0, [::], low op0, high op0) /\
  {in bottom :: top :: s &, no_crossing R} /\
  {in all_edges [:: op0] events &, no_crossing R} /\
  pairwise (@edge_below _) (bottom :: [seq high c | c <- [:: op0]]) /\
  sorted (@lexPtEv _) (behead events).
Proof.
move=> ltev boxwf startok nocs' evin lexev evsub out_evs cle.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
case evsq : events => [ | ev future_events]; [by [] | move=> _ /=].
set op0 := (start_open_cell bottom top).
have op0sok : all open_cell_side_limit_ok ([::] ++ [::op0]).
  by rewrite /= /op0 startok.
have cbtom0 : cells_bottom_top bottom top [:: op0].
  by rewrite /op0 /cells_bottom_top/cells_low_e_top/= !eqxx.
have adj0: adjacent_cells [:: op0] by [].
have sval0 : seq_valid [:: op0] (point ev).
  move: evin; rewrite evsq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /= /valid_edge/generic_trajectories.valid_edge /= !betW.
have rf0: s_right_form [:: op0] by rewrite /= boxwf.
have inbox0 : all (inside_box bottom top) [seq point e | e <- future_events].
  by move: evin; rewrite evsq map_cons /= => /andP[].
have cle0 : close_edges_from_events future_events.
  by move: cle; rewrite evsq /= => /andP[].
have oute0 : {in future_events, forall e, out_left_event e}.
  by move=> e ein; apply: out_evs; rewrite evsq inE ein orbT.
have clae0 : close_alive_edges bottom top [:: op0] (ev :: future_events).
  by rewrite /=/end_edge_ext !inE !eqxx !orbT.
have noc0 : {in all_edges [:: op0] (ev :: future_events) &, no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite -evsq !inE.
  move=> /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by move=> /evsub ->; rewrite !orbT.
have [vb vt] : valid_edge bottom (point ev) /\ valid_edge top (point ev).
  have /(allP sval0) : start_open_cell bottom top \in [:: op0].
    by rewrite inE eqxx.
  by rewrite /= => /andP[].
have /andP[/andP[pal puh] _] : inside_box bottom top (point ev).
   by apply: (@allP [eqType of pt] _ _ evin); rewrite evsq map_f// inE eqxx.
have : open_cells_decomposition [:: op0] (point ev) =
  ([::], [::], op0, [::], bottom, top).
  apply: (open_cells_decomposition_single
           (isT : adjacent_cells ([::] ++ [:: op0])) rf0 sval0 pal puh).
have pw0 : pairwise (@edge_below _) (bottom :: [seq high c | c <- [::op0]]).
  by rewrite /= !andbT /=.
have lexev0 : sorted (@lexPtEv _) future_events.
  by move: lexev; rewrite evsq=> /path_sorted.
do 15 (split; first by []).
by [].
Qed.

Lemma initial_common_general_position_invariant bottom top s events:
  sorted (fun e1 e2=> p_x (point e1) < p_x (point e2)) events ->
  bottom <| top ->
  (* TODO: rephrase this statement in a statement that easier to understand. *)
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  all (inside_box bottom top) [seq point e | e <- events] ->
  sorted (@lexPtEv _) events ->
  {subset flatten [seq outgoing e | e <- events] <= s} ->
  {in events, forall ev, out_left_event ev} ->
  close_edges_from_events events ->
  events != [::] ->
  common_general_position_invariant bottom top s
    (initial_state bottom top events)
    (* (head (dummy_event _) events) *) (behead events).
Proof.
move=> ltev boxwf startok nocs' evin lexev evsub out_evs cle evsn0.
have :=
  initial_intermediate ltev boxwf startok nocs' evin lexev evsub out_evs cle
    evsn0.
case evsq : events evsn0 => [ | ev future_events]; [by [] | move=> _].
move=> [op0sok [cbtom0 [adj0 /=
           [sval0 [rf0 [inbox0 [cle0 [oute0 [clae0 [vb 
             [vt [oe [nocs [noc0 [pw0 lexev0]]]]]]]]]]]]]]].
have evins : ev \in events by rewrite evsq inE eqxx.
set op0 := start_open_cell bottom top.
case oca_eq:  (opening_cells_aux _ _ _ _) => [nos lno].
set w := Bscan _ _ _ _ _ _ _.
have [state1 ] : exists state1, state1 = w by exists w.
rewrite /w => {w} st1q.
set cl0 := lst_closed state1.
set ops0 := [::] ++ [:: op0].
have evsin0 : all (inside_box bottom top) [seq point ev | ev <- events].
  exact: evin.
have oute : out_left_event ev by apply: out_evs.
have oute' : {in sort (@edge_below _) (outgoing ev), forall g,
                  left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
have edges_sub1 : {subset all_edges (rcons nos lno) 
        future_events <= [:: bottom, top & s]}.
  move=> g; rewrite mem_cat=> /orP[ | gfut ]; last first.
    have /evsub {}gfut : g \in events_to_edges events.
      by rewrite evsq events_to_edges_cons mem_cat gfut orbT.
    by rewrite !inE gfut; rewrite !orbT.
  have := opening_cells_subset vb vt oute.
  rewrite /opening_cells oca_eq=> main.
  rewrite mem_cat=> /orP[] /mapP [c /main + ->] => /andP[]; rewrite !inE.
    move=> /orP[-> | +] _; first by rewrite ?orbT.
    move=> {}main; apply/orP; right; apply/orP; right.
    by apply/evsub/flattenP; exists (outgoing ev); rewrite // map_f.
  move=> _ /orP[-> |]; first by rewrite ?orbT.
  move=> {}main; apply/orP; right; apply/orP; right.
  by apply/evsub/flattenP; exists (outgoing ev); rewrite // map_f.
have pin : inside_box bottom top (point ev).
  by apply: (@allP [eqType of pt] _ _ evin); rewrite evsq /= inE eqxx.
have inbox_all_events0 :
  all (inside_box bottom top) [seq point x | x <- (ev :: future_events)].
  by move: evin; rewrite evsq.
have evlexfut : path (@lexPtEv _) ev future_events.
  by move: lexev; rewrite evsq.
have rf0' : s_right_form ([::] ++ [:: start_open_cell bottom top]) by [].
have cle0' : close_edges_from_events (ev :: future_events) by rewrite -evsq.
have := invariant1_default_case
          inbox_all_events0 oute rf0' cbtom0 adj0 sval0 cle0' clae0 noc0
          evlexfut.
rewrite oe oca_eq /=.
move=> /[dup] inv1 -[] clae1 [] sval' [] adj1 [] cbtom1 rf1.
have rl0 : {in [::], forall c : cell, right_limit c <= p_x (point ev)} by [].
have cl0q : cl0 = close_cell (point ev) op0 by rewrite /cl0 st1q.
rewrite -cats1 in edges_sub1 sval'.
have lstx1op : lst_x _ _ state1 = left_limit (lst_open state1).
  have := opening_cells_left oute vb vt; rewrite /opening_cells.
  by rewrite oca_eq st1q => -> //=; rewrite mem_rcons inE eqxx.
have sh1 : all (fun ev => lst_x _ _ state1 < p_x (point ev)) future_events &&
          sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) future_events.
  move: ltev; rewrite evsq /= path_sortedE /=; last first.
    by move=> x y z; apply: lt_trans. 
  by rewrite st1q.
have he1q' : high (lst_open state1) = lst_high _ _ state1.
  rewrite st1q /=.
  by have := opening_cells_aux_high_last vb vt oute'; rewrite oca_eq.
move: lstx1op he1q' sh1; rewrite st1q=> lstx1op he1q' sh1.
have oks1 : all open_cell_side_limit_ok (nos ++ [:: lno]).
  have := pin => /andP[] /andP[] /underWC pal puh _.
  have := opening_cells_side_limit vb vt pal puh oute.
  by rewrite /opening_cells oca_eq cats1.
by constructor.
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
  close_edges_from_events events ->
  events != [::] ->
  disjoint_general_position_invariant bottom top s
   (initial_state bottom top events)
   (* (head (dummy_event _) events) *) (behead events).
Proof.
move=> ltev boxwf startok nocs' evin lexev evsub out_evs cle evsn0.
have := initial_common_general_position_invariant ltev boxwf startok
  nocs' evin lexev evsub out_evs cle evsn0.
have := initial_intermediate ltev boxwf startok nocs' evin lexev evsub
   out_evs cle evsn0.
move: evsn0; case evsq : events => [ | ev evs];[by [] | move=> _].
lazy zeta; rewrite [head _ _]/= [behead _]/=.
move=> -[] op0sok [cbtom0 [adj0 [sval0 [rf0 [inbox0 
[cle0 [oute0 [clae0 [vb [vt [oe [nocs [noc0 [pw0 lexev0]]]]]]]]]]]]]].
have evins : ev \in events by rewrite evsq inE eqxx.
rewrite /initial_state /state_open_seq/state_closed_seq/= => Cinv.
case oca_eq:  (opening_cells_aux _ _ _ _) Cinv => [nos lno] Cinv.
move: (Cinv)=> -[]; rewrite /state_open_seq/state_closed_seq/=.
move=> inv1 pxe hlno edges_sub1 cle1 oute1 inbox1 lexevs sok1 gen_pos.
set op0 := start_open_cell bottom top.
have op0_cl0_dis : {in [:: op0] & [::], disjoint_open_closed_cells R} by [].
have inbox0' : all (inside_box bottom top) [seq point e | e <- ev :: evs].
  by rewrite -evsq.
have cl0_dis : {in [::] &, disjoint_closed_cells R} by [].
have rl0 : {in [::], forall c : cell, right_limit c <= p_x (point ev)} by [].
have := @step_keeps_disjoint_default bottom top ev [::]
            op0 [::] evs inbox0' (out_evs _ evins) rf0 cbtom0 adj0
            sval0 pw0 op0sok [::] op0_cl0_dis cl0_dis rl0.
  rewrite oe oca_eq /= => -[] cl_dis1 op_cl_dis1.
have pw1 : pairwise (@edge_below _)
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
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  common_general_position_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  common_general_position_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s oe.
move=> []; rewrite /state_open_seq/state_closed_seq/=.
move=> inv lstxq lstheq sub_edges cle  out_es /[dup] inbox0.
move=> /andP[] inbox_e inbox_es.
move=> lexev oks /andP[] lstxlt ltev'.
move: (inv)=> [] clae [] []; first by [].
move=> sval [] adj [] cbtom rfo.
have oute : out_left_event ev.
  by apply: out_es; rewrite inE eqxx.
have oute' : {in sort (@edge_below _) (outgoing ev),
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
have ltev1 : all (fun e => p_x (point ev) < p_x (point e)) evs &&
         sorted (fun e1 e2 => p_x (point e1) < p_x (point e2)) evs.
  move: ltev'; rewrite path_sortedE //.
  by move=> x y z; apply: lt_trans.
by constructor.
Qed.

Lemma simple_step_disjoint_general_position_invariant
  bottom top s fop lsto lop fc cc lcc lc le he cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  disjoint_general_position_invariant bottom top s
     (Bscan fop lsto lop cls lstc lsthe lstx)
     (ev :: evs) ->
  disjoint_general_position_invariant bottom top s
     (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s oe.
move=> []; rewrite /state_open_seq/state_closed_seq/=.
move=> oc_dis c_dis Cinv pw rl.
have := Cinv=> -[]; rewrite /state_open_seq/state_closed_seq/=.
move=> inv1 lstxq lstheq sub_edges cle out_es inbox_es lexev oks gen_pos.
have := inv1 => -[] clae [] []; first by [].
move=> sval []adj []cbtom rfo.
rewrite /simple_step/generic_trajectories.simple_step.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
have Cinv' : common_general_position_invariant bottom top s
         (Bscan (fc ++ nos) lno lc
            (cls ++ lstc :: closing_cells (point ev) cc)
            (close_cell (point ev) lcc) he (p_x (point ev))) evs.
  have := simple_step_common_general_position_invariant boxwf nocs' inbox_s oe.
  rewrite /simple_step/generic_trajectories.simple_step.
  rewrite -/(opening_cells_aux _ _ _ _).
  by rewrite oca_eq=> /(_ _ _ lsthe lstx); apply.
have cl_at_left' : {in rcons cls lstc,
        forall c, right_limit c <= p_x (point ev)}.
  by move=> c cin; apply: rl; rewrite // inE eqxx.
have oute : out_left_event ev by apply: out_es; rewrite inE eqxx.
have := step_keeps_disjoint_default inbox_es oute rfo
         cbtom adj sval pw oks oc_dis c_dis cl_at_left'.
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
have pwo' : pairwise (@edge_below _)
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
by constructor.
Qed.

Definition start :=
  start R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y) 1 edge
  (@unsafe_Bedge _) (@left_pt _) (@right_pt _).

Lemma start_eq_initial (bottom top : edge) (ev : event) :
  start ev bottom top = initial_state bottom top [:: ev].
Proof. by []. Qed.

Definition complete_last_open : edge -> edge -> cell -> cell :=
  complete_last_open
    R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y) edge
    (@left_pt _) (@right_pt _).

Lemma map_eq [A B : Type] (f : A -> B)  l :
   List.map f l = [seq f x | x <- l].
Proof. by []. Qed.

Definition main_process bottom top evs :=
  match evs with
  | ev :: evs => scan evs (initial_state bottom top (ev :: evs))
  | [::] => ([:: start_open_cell bottom top], [::])
  end.

Lemma complete_process_eq bottom top ev evs :
  complete_process  R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y) 1 edge
  (@unsafe_Bedge _) (@left_pt _) (@right_pt _) (ev :: evs) bottom top =
  match scan evs (initial_state bottom top (ev :: evs)) with
   (a, b) => [seq complete_last_open bottom top c | c <- a] ++ b
  end.
Proof.  by []. Qed.


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
  close_edges_from_events evs ->
  main_process bottom top evs = (open, closed) ->
  {in closed &, disjoint_closed_cells R} /\
  {in open & closed, disjoint_open_closed_cells R}.
Proof.
move=> ltev boxwf startok nocs' inbox_s evin lexev evsub out_evs cle.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /main_process/scan.
case evsq : evs => [ | ev future_events].
  move=> [] <- <-; split; last by [].
  by move=> c1 c2; rewrite in_nil.
have evsn0 : evs != [::] by rewrite evsq.
have := initial_disjoint_general_position_invariant ltev boxwf startok nocs'
  evin lexev evsub out_evs cle evsn0.
rewrite /initial_state evsq.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos1 lno1] /=.
elim: (future_events) {oca_eq evsq} (Bscan _ _ _ _ _ _ _)=> [ | ev' fut' Ih].
  move=> state_f /=; case: state_f=> [] f m l cls lstc lsthe lstx.
  move=> /[swap] -[] <- <-; case; rewrite /state_open_seq /state_closed_seq /=.
  move=> dis_op_cl dis_cl *; split; move=> c1 c2 c1in c2in.
    by apply: dis_cl; rewrite // mem_rcons.
  by apply: dis_op_cl; rewrite // mem_rcons.
move=> {evs ltev evin lexev evsub out_evs cle evsn0}.
move=> [fop lsto lop cls lstc lsthe lstx].
case; set ops' := (state_open_seq _); set (cls' := state_closed_seq _).
rewrite /=.
move=> dis_open_closed dis_cl /[dup] Cinv [] inv1 lstxq lstheq sub_edges.
move=> /[dup] cle /andP[cl_e_fut' cle'] out_fut'.
move=> /[dup]  inbox_all_events' /andP[inbox_e inbox_all_events] lexevs oks.
move=> /andP[] /andP[] lstxlte lstx_fut' ltfut' edges_pairwise cl_at_left.
move: (inv1)=> [] clae [] pre_sval [] adj [] cbtom rfo.
have sval : seq_valid (fop ++ lsto :: lop) (point ev') by case: pre_sval.

rewrite /=/simple_step; case: ifP=> [_ | ]; last first.
  move=> /negbFE; rewrite /same_x eq_sym=> /eqP abs; suff: False by [].
  by move : lstxlte; rewrite abs lt_irreflexive.
rewrite -/(open_cells_decomposition _ _).
rewrite /generic_trajectories.simple_step.
case oe : (open_cells_decomposition _ _) => [[[[[fc cc] lcc] lc] le] he].
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
apply: Ih.
have :=
  simple_step_disjoint_general_position_invariant boxwf nocs' inbox_s oe.
  rewrite /simple_step/generic_trajectories.simple_step.
  rewrite -/(opening_cells_aux _ _ _ _).
  rewrite oca_eq=> /(_ _ _ lsthe lstx).
by apply.
Qed.

Record edge_covered_general_position_invariant (bottom top : edge)
 (edge_set : seq edge) (processed_set : seq event)
 (s : scan_state) (events : seq event) :=
 { edge_covered_ec : {in processed_set, forall e,
       {in outgoing e, forall g,
       edge_covered g (state_open_seq s) (state_closed_seq s)}};
   processed_covered : {in processed_set, forall e,
       exists2 c, c \in (state_closed_seq s) &
           point e \in (right_pts c : seq pt) /\ point e >>> low c}  ;
   common_inv_ec : common_general_position_invariant bottom top edge_set
     s events;
   non_in_ec : 
      {in edge_set & events, forall g e, non_inner g (point e)};
   uniq_ec : {in events, forall e, uniq (outgoing e)};
   inj_high : {in state_open_seq s &, injective high};
   bot_left_cells : 
       {in state_open_seq s & events, 
          forall c e, lexPt (bottom_left_corner c) (point e)};
   }.

Lemma in_cell_edges_has_cell (s : seq cell) (g : edge) :
   (g \in cell_edges s) = has (fun c => (g == low c) || (g == high c)) s.
Proof.
by elim: s => [ | c0 s Ih] //=; rewrite cell_edges_cons !inE !orbA Ih.
Qed.

Lemma bottom_left_start bottom top p : 
  inside_box bottom top p ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  bottom_left_cells_lex [:: start_open_cell bottom top] p.
Proof.
move=> inbox_p startok c; rewrite inE => /eqP ->.
have := leftmost_points_max startok => llq.
move: (startok); rewrite /open_cell_side_limit_ok=> /andP[] ln0.
move=> /andP[] samex _.
rewrite /bottom_left_corner.
have /eqP := (allP samex (last dummy_pt (left_pts (start_open_cell bottom top)))
            (last_in_not_nil _ ln0)).
rewrite llq.
rewrite /lexPt=> ->.
move: inbox_p=> /andP[] _ /andP[] /andP[] + _ /andP[] + _.
case: (lerP (p_x (left_pt bottom)) (p_x (left_pt top))).
  by move=> _ _ ->.
by move=> _ ->.
Qed.

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
   [:: (head dummy_event events)]
   (initial_state bottom top events) (behead events).
Proof.
move=> gen_pos lexev wf cle startok nocs' n_inner inbox_es sub_es out_es 
  uniq_out_es evsn0.
rewrite /initial_state.
have := initial_intermediate gen_pos wf startok nocs' inbox_es lexev sub_es
  out_es cle evsn0.
have := initial_common_general_position_invariant gen_pos wf startok nocs'
  inbox_es lexev sub_es out_es cle evsn0.
case evsq : events evsn0 => [ // | e evs] _.
case oca_eq: (opening_cells_aux _ _ _ _) => [nos lno].
lazy zeta; rewrite [head _ _]/= [behead _]/=.
have oute : out_left_event e by apply: out_es; rewrite evsq inE eqxx.
move=> Cinv [] ok0 []cbtom0 []adj0 []sval0 []rf0 []inbox_es0 []cle1
         []out_es1 []clae0 []vb []vt []oe0 []nocs []noc0 []pw0 lexevs.
have inbox_e : inside_box bottom top (point e).
  by apply/(@allP [eqType of pt] _ _ inbox_es)/map_f; rewrite evsq inE eqxx.
have /andP[eab ebt] : (point e >>> bottom) && (point e <<< top).
  by move: inbox_e=> /andP[].
have cle0 : close_edges_from_events (e :: evs) by rewrite -evsq.
move: inbox_es; rewrite evsq=> inbox_es.
move: Cinv; rewrite/initial_state oca_eq/state_open_seq/state_closed_seq/=.
move=> /[dup] Cinv; rewrite /state_open_seq/state_closed_seq /=.
move=> -[]; rewrite /state_open_seq/state_closed_seq /=.
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
    adj0 sval0 noc0 btm_left_lex0; rewrite oe0 oca_eq=> /(_ _ eev).
  by apply.
rewrite /state_open_seq/state_closed_seq/=.
have cov_p1 : {in [:: e], forall e',
  exists2 c, c \in [:: close_cell (point e) op0] &
  point e' \in (right_pts c : seq pt)/\ point e' >>> low c}.
  move=> e'; rewrite inE => /eqP -> {e'}.
  exists (close_cell (point e) op0); first by rewrite mem_head.
  split.
    by exact: (@close_cell_in _ op0 (conj vb vt)).
  by have [-> _ _] := close_cell_preserve_3sides (point e) op0.
by constructor.
Qed.

Lemma edge_covered_sub (g : edge) op1 op2 cl1 cl2 :
  op1 =i op2 -> cl1 =i cl2 ->
  edge_covered g op1 cl1 -> edge_covered g op2 cl2.
Proof.
move=> eqop eqcl [[opc [cls [P1 [P2 [P3 [P4 P5]]]]]] | ].
  left; exists opc, cls.
  split;[ |split;[by [] | split;[by [] | split;[ | by []]]]] .
    by move=> c; rewrite -eqcl; apply: P1.
  by rewrite -eqop.
move=> [pcc [P1 [P2 [P3 [P4 [P5 P6]]]]]].
right; exists pcc; split;[by [] | split;[ | by []]].
by move=> c; rewrite -eqcl; apply: P2.
Qed.

Lemma inside_box_non_inner bottom top (p : pt) :
  inside_box bottom top p -> non_inner bottom p /\ non_inner top p.
Proof.
move=> /andP[] /andP[] absbot abstop _; split.
  move=> /[dup] /andP[] _ vb; move: absbot; rewrite under_onVstrict // negb_or.
  by move=> /[swap] ->.
move=> /[dup] /andP[] _ vt; move: abstop; rewrite strict_nonAunder //.
by move=> /[swap] ->.
Qed.

Lemma simple_step_edge_covered_general_position
  bottom top s cov_set fop lsto lop fc cc lcc lc le he cls lstc ev
  lsthe lstx evs :
  bottom <| top ->
  {in bottom :: top :: s &, forall e1 e2, inter_at_ext e1 e2} ->
  {in s, forall g, inside_box bottom top (left_pt g) &&
                   inside_box bottom top (right_pt g)} ->
  open_cells_decomposition (fop ++ lsto :: lop) (point ev) =
    (fc, cc, lcc, lc, le, he) ->
  edge_covered_general_position_invariant bottom top s
   cov_set (Bscan fop lsto lop cls lstc lsthe lstx)
   (ev :: evs) ->
  edge_covered_general_position_invariant bottom top s
    (rcons cov_set ev) (simple_step fc cc lc lcc le he cls lstc ev)
    evs.
Proof.
move=> boxwf nocs' inbox_s.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
set st := Bscan _ _ _ _ _ _ _.
move=> oe.
move=> [] covered p_covered /[dup] Cinv [] /[dup] inv_s [] clae.
move=> - [] []; first by [].
rewrite /state_open_seq/state_closed_seq /= => sval [] adj [] cbtom rfo.
move=> lstxq lstheq sub_edges cle out_es.
move=> /[dup] inbox0 /andP[] inbox_e inbox_es lexev.
move=> oks /andP[] lstxlt pathlt n_inner uniq_evs inj_high btm_left_lex.
have out_e : out_left_event ev by apply: out_es; rewrite inE eqxx.
have noc : {in all_edges (state_open_seq st) (ev :: evs) &, no_crossing R}.
  by move=> g1 g2 g1in g2in; apply: nocs; apply: sub_edges.
(* TODO: this should not be needed, if we had enough theorems about
  simple_step. *)
have lstxneq :  p_x (point ev) != lstx.
  by move: lstxlt; rewrite lt_neqAle eq_sym=> /andP[] /andP[].
case oca_eq : 
  (opening_cells_aux (point ev) (sort (@edge_below _) (outgoing ev)) le he) =>
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
     sval noc btm_left_lex_e.
  rewrite /simple_step/= /= oe oca_eq /= /state_open_seq /=.
  rewrite catA=> main.
  move=> c e cin ein; apply: main=> //=.
    move: lexev; rewrite path_sortedE; last by apply: lexPtEv_trans.  
    by move=> /andP[] /allP /(_ e ein).
  move: cin; rewrite /generic_trajectories.simple_step.
  by rewrite -/(opening_cells_aux _ _ _ _) oca_eq.
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
suff main : forall events op cl st cov_set, 
  edge_covered_general_position_invariant bottom top s cov_set st events ->
  scan events st = (op, cl) ->
  ({in events_to_edges (cov_set ++ events), forall g, edge_covered g op cl} /\
  {in cov_set ++ events, forall e, exists2 c, c \in cl &
    point e \in (right_pts c : seq pt) /\ point e >>> low c}).
  by move: req; apply: (main _ _ _ _ [:: ev]).
  move=> {req istateP istate oca_eq lno nos evsn0 evsq future_events ev}.
  move=> {uniq_edges n_inner out_evs evsub lexev evin startok ltev}.
  move=> {cle closed open evs}.
  elim=> [ | ev evs Ih] op cl st cov_set.
  case: st => fop lsto lop cls lstc lsthe lstx /=.
  move=> []; rewrite /state_open_seq/state_closed_seq /= => + p_main.
  move=> main _ _ _ _ _ [] <- <-; rewrite cats0; split.
    move=> g=> /flatten_mapP[e' /main /[apply]].
    apply: edge_covered_sub; first by [].
    by move=> c; rewrite mem_rcons.
  move=> e=> /p_main [c2 c2in pin2]; exists c2=> //.
  by move: c2in; rewrite mem_rcons.
move=> inv0; rewrite -cat_rcons.
apply: Ih.
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
 (edge_set : seq edge) (processed_set : seq event)
 (s : scan_state) (events : seq event) :=
 { disjoint_ss :
     disjoint_general_position_invariant bottom top edge_set s events;
   covered_ss :
     edge_covered_general_position_invariant bottom top edge_set
       processed_set s events;
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
              min (p_x (right_pt bottom)) (p_x (right_pt top))};
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

Lemma events_to_edges_rcons evs (e : event) :
  events_to_edges (rcons evs e) = events_to_edges evs ++ outgoing e.
Proof. by rewrite /events_to_edges /= map_rcons flatten_rcons. Qed.

Lemma valid_open_limit (c : cell) p  :
  valid_edge (low c) p -> valid_edge (high c) p -> p_x p <= open_limit c.
Proof.
move=> /andP[] _ lp /andP[] _ hp; rewrite /open_limit.
by have [A | B] := lerP (p_x (right_pt (low c))) (p_x (right_pt (high c))).
Qed.

Lemma on_edge_inside_box (bottom top g : edge) p :
  inside_box bottom top (left_pt g) ->
  inside_box bottom top (right_pt g) ->
  p === g ->
  inside_box bottom top p.
Proof.
move=> inl inr pon.
rewrite /inside_box.
have -> : p >>> bottom.
  have la : left_pt g >>> bottom by move: inl=>/andP[] /andP[].
  have ra : right_pt g >>> bottom by move: inr=>/andP[] /andP[].
  by have := point_on_edge_above_strict pon la ra.
have -> : p <<< top.
  have lu : left_pt g <<< top by move: inl=>/andP[] /andP[].
  have ru : right_pt g <<< top by move: inr=>/andP[] /andP[].
  by have := point_on_edge_under_strict pon lu ru.
move: pon => /andP[] _ /andP[] lp pr.
move: inl => /andP[] _ /andP[] /andP[] bl _ /andP[] tl _.
move: inr => /andP[] _ /andP[] /andP[] _ rb /andP[] _ rt.
rewrite (lt_le_trans bl lp) (lt_le_trans tl lp).
by rewrite (le_lt_trans pr rb) (le_lt_trans pr rt).
Qed.

Lemma inside_box_lt_min_right (p : pt) bottom top :
  inside_box bottom top p ->
  p_x p < min (p_x (right_pt bottom)) (p_x (right_pt top)).
Proof.
move=> /andP[] _ /andP[] /andP[] _ + /andP[] _.
by case : (ltrP (p_x (right_pt bottom)) (p_x (right_pt top))).
Qed.

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
    [::(head dummy_event events)]
   (initial_state bottom top events) (behead events).
Proof.
move=> gen_pos lexev wf cle startok nocs' n_inner inbox_es sub_es out_es 
  uniq_out_es evsn0.
have := initial_intermediate gen_pos wf startok nocs' inbox_es lexev sub_es
  out_es cle evsn0.
have := initial_disjoint_general_position_invariant gen_pos wf startok
  nocs' inbox_es lexev sub_es out_es cle evsn0.
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
  apply /(@eqP [eqType of pt]); rewrite pt_eqE samex eqxx.
  apply: (on_edge_same_point pong).
    by rewrite -lgq left_on_edge.
  by apply/eqP.
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
  rewrite /opening_cells oca_eq=> /(_ _ cin) evin /(_ _ cin) -> samex.
  move/negP; apply.
  suff -> : p = point ev.
    by apply: (opening_cells_in vb0 vt0 oute); rewrite /opening_cells oca_eq.
  apply/(@eqP [eqType of pt]); rewrite pt_eqE samex /=.
  by apply: (on_edge_same_point pong eong samex).
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
       left_limit c < min (p_x (right_pt bottom)) (p_x (right_pt top))}.
  move=> c cin.
  have := opening_cells_left oute vb0 vt0; rewrite /opening_cells oca_eq.
  rewrite -cats1 => /(_ _ cin) ->.
  by apply: inside_box_lt_min_right.
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
      left_limit (head_cell open) < min (p_x (right_pt bottom))
      (p_x (right_pt top))).
Proof.
move=> ltev boxwf startok nocs' inbox_s evin lexev evsub out_evs cle
  n_inner uniq_edges.
have nocs : {in bottom :: top :: s &, no_crossing R}.
  by apply: inter_at_ext_no_crossing.
rewrite /main_process/scan/=.
case evsq : evs => [ | ev future_events]; first by  move=> [] <- <-.
have evsn0 : evs != [::] by rewrite evsq.
rewrite -/(opening_cells_aux _ _ _ _).
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
set istate := Bscan _ _ _ _ _ _ _.
have : safe_side_general_position_invariant bottom top s [:: ev]
  istate future_events.
  have := initial_safe_side_general_position ltev lexev boxwf cle startok
    nocs' n_inner evin evsub out_evs uniq_edges evsn0.
  by rewrite evsq /= oca_eq.
move=> invss req.
suff main: forall events op cl st processed_set, 
  safe_side_general_position_invariant bottom top s processed_set st events ->
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
  (left_limit (head_cell op) < min (p_x (right_pt bottom))
      (p_x (right_pt top))).
  have [A [B [C [D [E [F [G [H I]]]]]]]] := main _ _ _ _ _ invss req.
  split; last by [].
  move=> c cin; move: (A c cin) => [] crf [] difc [] lltr [] clok A'.
  do 4 (split; first by []).
  by move=> p pside; have := A' _ pside.
elim=> [ | {evsq oca_eq istate invss}ev {req}future_events Ih] op cl st p_set.
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
      have [[] + + _ _ _ _ _ _ _ + _] := c_inv; rewrite /state_open_seq/=.
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
apply: Ih.
have [clae [pre_sval [adj [cbtom rfo]]]] := inv1 c_inv.
move: pre_sval=> [| sval]; first by[].
have inbox_es := inbox_events c_inv.
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
  by apply: (out_events c_inv); rewrite inE eqxx.
have oute' :
  {in (sort (@edge_below _) (outgoing ev)), forall g, left_pt g == point ev}.
  by move=> g; rewrite mem_sort; apply: oute.
set rstate := Bscan _ _ _ _ _ _ _.
have d_inv': 
  disjoint_general_position_invariant bottom top s rstate future_events.
  move: (d_inv); rewrite stq=> d_inv'.
  have := simple_step_disjoint_general_position_invariant boxwf nocs'
      inbox_s oe d_inv'.
  rewrite /simple_step/generic_trajectories.simple_step/=.
  by rewrite -/(opening_cells_aux _ _ _ _) oca_eq.
have e_inv' :edge_covered_general_position_invariant bottom top s
    (rcons p_set ev) rstate future_events.
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
    have uo : uniq (outgoing ev) by apply: (uniq_ec e_inv) (mem_head _ _).
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
  have subo := edges_sub c_inv.
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
    by apply: (allP (sides_ok c_inv)).
  by apply close_cell_ok.
(* proving a right_limit stronger invariant. *)
have rllte :   {in state_closed_seq rstate & future_events,
    forall (c : cell) (e : event), right_limit c < p_x (point e)}.
  rewrite /state_closed_seq/=.
  move=> c e cin ein.
  move: cin; rewrite -cats1 -catA /= -cat_rcons mem_cat=> /orP[cold | cnew].
    by apply: rl; rewrite ?stq // inE ein orbT.
  have in_es := inbox_events c_inv.
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
    have := out_events c_inv (mem_head _ _) gnew=> /eqP ->.
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
  have samex : p_x p == p_x (point ev).
    by move: pin=> /andP[] + _; rewrite close_cell_right_limit.
  move: gin; rewrite mem_cat=> /orP[gin | /oute/eqP lgq ]; last first.
    have peg : point ev === g by rewrite -lgq left_on_edge.
    move=> pong.
    have samey := on_edge_same_point pong peg samex.
    have pev : p = point ev by apply/eqP; rewrite pt_eqE samex samey.
    have := not_safe_event (close_cell (point ev) c').
    rewrite -[e in in_safe_side_right e _]pev pin orbT.
    by rewrite /closing_cells -map_rcons map_f // => /(_ isT).
  move: gin=> /flatten_mapP[e' e'in gin].
  have := edge_covered_ec e_inv e'in gin=> -[]; last first.
    move=> [[ | pcc0 pcc] []]; first by []. 
    move=> _ /= [pccsub [pcchigh [_ [_ rlpcc]]]] /andP[] _ /andP[] _.
    rewrite leNgt=> /negP; apply.
    rewrite (eqP samex).
    rewrite -rlpcc; apply:rl; last by rewrite inE eqxx.
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
    have := order_edges_strict_viz_point' vplc vphc rfc pun.
    by apply/negP/onAbove; rewrite opch.
  have pw : pairwise (@edge_below _) [seq high c | c <- state_open_seq st].
    by move: (pairwise_open d_inv)=> /= /andP[].
  have [puhc' palc'] : p <<< high c' /\ p >>> low c'.
    apply/andP;  move: pin=> /andP[] _ /andP[] + /andP[] + _.
    by have [-> -> _] := close_cell_preserve_3sides (point ev) c' => ->.
  have : p >>= low opc by move: cnt=> /andP[].
  rewrite strict_nonAunder // negb_and negbK=> /orP[ | stricter]; last first.
    have := disoc adj pw (sides_ok c_inv)=> /(_ opc c' opco c'in') [ab' | ].
      by move: puhc'; rewrite strict_nonAunder // -ab' opch abs.
    move=> /(_ p) + ; move=>/negP.
    rewrite inside_open'E stricter valid_open_limit //.
    move: cnt; rewrite contains_pointE=> /andP[] _ ->.
    rewrite (eqP samex) lolt //=; last by rewrite inE eqxx.
    rewrite inside_open'E (underW puhc') palc' valid_open_limit //.
    by rewrite (eqP samex) lolt // inE eqxx.
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
    have:= order_edges_viz_point' vbp vlc'p bottom_b_c' pub.
    by move: palc'=> /[swap] => ->.
  have ldifh : low opc != high opc by apply: d_e; rewrite mem_cat opco.
  have low_opc_s : low opc \in [:: bottom, top & s].
    by apply: (edges_sub c_inv); rewrite !mem_cat map_f.
  have high_opc_s : high opc \in [:: bottom, top & s].
    by apply: (edges_sub c_inv); rewrite !mem_cat map_f ?orbT.
  have := nocs' (low opc) (high opc) low_opc_s high_opc_s.
  move=> [Q | ]; first by rewrite Q eqxx in ldifh.
  have ponh : p === high opc by rewrite opch.
  have opcok : open_cell_side_limit_ok opc by apply: (allP (sides_ok c_inv)).
  move=> /(_ _ ponl ponh); rewrite !inE=> /orP[/eqP pleft | /eqP].
    have : left_limit opc < p_x p.
      by rewrite (eqP samex); apply: lolt; rewrite // inE eqxx.
    have := left_limit_max opcok.
    have [_ | ] := lerP (p_x (left_pt (high opc)))(p_x (left_pt (low opc))).
      by move=> /le_lt_trans /[apply]; rewrite pleft lt_irreflexive.
    move=> /lt_le_trans /[apply]=> /lt_trans /[apply].
    by rewrite pleft lt_irreflexive.
(* Here p is vertically aligned with p_x, but it must be an event,
   because it is the end of an edge. *)
  move=> prl.
  have put : p <<< top.
    apply: (order_edges_strict_viz_point' vhc'p vtp _ puhc').
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
  by rewrite -pe2 -prl (eqP samex) lt_irreflexive.
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
  have [+ _ _ _ _ _ _ _ _ _] := c_inv.
  move=> [] _ [] _ [] _ [] _ /allP; apply.
  by rewrite ocd -cat_rcons !mem_cat c'in orbT.
have lo_lb' : {in state_open_seq rstate, forall c,
               left_limit c < min (p_x (right_pt bottom)) (p_x (right_pt top))}.
  move=>c; rewrite /state_open_seq/= -catA -cat_rcons !mem_cat orbCA.
  move=> /orP[cnew | cold]; last first.
    by apply: lo_lb; rewrite ocd -cat_rcons !mem_cat orbCA cold orbT.
  have := opening_cells_left oute vl vp ; rewrite /opening_cells oca_eq.
  move=> /(_ _ cnew) ->.
  by apply: inside_box_lt_min_right.
by constructor.
Qed.
  
(*  

Lemma start_cover (bottom top : edge) (s : seq edge) closed open :
  bottom <| top ->
  open_cell_side_limit_ok (start_open_cell bottom top) ->
  {in bottom :: top :: s &, no_crossing R} ->
  all (inside_box bottom top) [seq left_pt x | x <- s] ->
  all (inside_box bottom top) [seq right_pt x | x <- s] ->
  start (edges_to_events s) bottom top = (closed, open) ->
  forall p, inside_box bottom top p ->
  has (inside_closed' p) closed || has (inside_open' p) open.
Proof.
move=> boxwf boxwf2 nocs leftin rightin; rewrite /start.
set evs := edges_to_events s.
have/perm_mem := edges_to_events_no_loss s.
  rewrite -/evs/events_to_edges/= => stoevs.
set op0 := [:: Bcell (leftmost_points bottom top) [::] bottom top].
set cl0 := (X in scan _ _ X).
have : sorted (@lexPt R) [seq point x | x <- evs].
  by apply: sorted_edges_to_events.
have : cells_bottom_top bottom top op0.
  by rewrite /op0/cells_bottom_top/cells_low_e_top/= !eqxx.
have : adjacent_cells op0 by [].
have : s_right_form op0 by rewrite /= boxwf.
have : close_alive_edges bottom top op0 evs.
  by rewrite /=/end_edge !inE !eqxx !orbT.
have : {in cell_edges op0 ++ flatten [seq outgoing i | i <- evs] &,
         no_crossing R}.
  rewrite /=; move: nocs; apply sub_in2.
  move=> x; rewrite !inE => /orP[ -> // | /orP[-> // | ]]; rewrite ?orbT //.
  by rewrite -stoevs => ->; rewrite ?orbT.
have : {in evs, forall ev, out_left_event ev}.
  by apply: out_left_edges_to_events.
have : close_edges_from_events bottom top evs.
  by apply: edges_to_events_wf.
have evsin0 : all (inside_box bottom top)
    [seq point ev | ev <- evs].
  apply/allP.
  have : {subset [seq right_pt g | g <- s] <= inside_box bottom top}.
    by apply/allP: rightin.
  have : {subset [seq left_pt g | g <- s] <= inside_box bottom top}.
    by apply/allP: leftin.
  by apply: edges_to_events_subset.
have btm_left0 : {in [seq point e | e <- evs], 
         forall e,  bottom_left_cells_lex op0 e}.
  move=> ev /[dup] /(allP evsin0) /andP[_ /andP[valb valt]] evin c.
  rewrite /op0 inE /lexPt /bottom_left_corner=> /eqP -> /=.
  by apply/orP; left; apply/inside_box_left_ptsP/(allP evsin0).
have sval0 :
  evs != nil -> seq_valid op0 (head dummy_pt [seq point ev | ev <- evs]).
  case evseq : evs => [// | ev evs'] _ /=; rewrite andbT.
  move: evsin0; rewrite evseq /= => /andP[] /andP[] _ /andP[] ebot etop _.
  have betW : forall a b c : R, a < b < c -> a <= b <= c.
    by move=> a b c /andP[] h1 h2; rewrite !ltW.
  by rewrite /valid_edge !betW.
have cov0 : forall p, all (lexePt p) [seq point ev | ev <- evs] ->
         cover_left_of bottom top p op0 cl0.
  move=> p limrp q inbox_q qp; apply/orP; left; apply/hasP.
  exists (Bcell (leftmost_points bottom top) nil bottom top).
    by rewrite /op0 inE eqxx.
  rewrite inside_open'E.
  apply/andP; split;[ | apply/andP; split].
  - by apply: underW; move: inbox_q=> /andP[] /andP[].
  - by move: inbox_q=> /andP[] /andP[].
  - rewrite /open_limit /=.
    case: (ltrP  (p_x (right_pt bottom)) (p_x (right_pt top))) => _.
    rewrite inside_box_left_ptsP //.
    by move: inbox_q => /andP[] _ /andP[] /andP[] _ /ltW ->.
  rewrite inside_box_left_ptsP //.
  by move: inbox_q => /andP[] _ /andP[] _ /andP[] _ /ltW ->.
have leftlim0 : {in op0, forall c p, inside_box bottom top p ->
         left_limit c = p_x p ->
         contains_point' p c -> has (inside_closed' p) cl0}.
  move=> c + p; rewrite inE -[Bcell _ _ _ _]/(start_open_cell bottom top).
  move=> /eqP -> {c}.
  move/inside_box_left_ptsP/[swap].
  by rewrite (leftmost_points_max boxwf2)=> ->; rewrite lt_irreflexive.
move: cov0 evsin0 sval0 btm_left0 leftlim0; move=> {stoevs}.
elim: evs op0 cl0 => [ | ev evs' Ih]
   op cl main evsin sval btm_left llim clev oute noc clae rfo adj cbtom sortev.
  rewrite /= => [][] <- <- p inbox_p.
  have lexpp : lexePt p p by rewrite lexePt_eqVlt eqxx.
  by rewrite orbC; apply: (main p isT p inbox_p lexpp).
rewrite /=.
case stepeq : (step ev op cl) => [op' cl'].
move=> scaneq.
have inbox_e : inside_box bottom top (point ev).
  by apply: (allP evsin); rewrite map_f // inE eqxx.
have := sval isT; rewrite /= => sval'.
have oute' : out_left_event ev by apply: oute; rewrite inE eqxx.
have btm_left' : bottom_left_cells_lex op (point ev).
  by apply: btm_left; rewrite inE eqxx.
have cov : cover_left_of bottom top (point ev) op cl.
  apply: main=> /=; rewrite lexePt_eqVlt eqxx /=.
  move: sortev; rewrite /sorted /=.
  rewrite  (path_sortedE (@lexPt_trans R)) // => /andP[+ _].
  by apply: sub_all; exact: lexPtW.
have cov' : forall p : pt,
    all (lexePt p) [seq point ev0 | ev0 <- evs'] ->
    cover_left_of bottom top p op' cl'.
  have := step_keeps_cover sortev cbtom adj inbox_e sval' oute' rfo clae clev
           noc btm_left' llim stepeq cov.
  move=> it p; apply: it.
have evle : forall ev', ev' \in evs' -> lexPt (point ev) (point ev').
  move=> ev' ev'in.
  move: sortev=> /=; rewrite (path_sortedE (@lexPt_trans R))=> /andP[]/allP.
  by move=> /(_ (point ev')) + _; apply; apply map_f.
have svalr : evs' != [::] ->
       seq_valid op' (head dummy_pt [seq point ev0 | ev0 <- evs']).
  case evs'eq : evs' => [// | a q] /= _.
  have inbox_a : inside_box bottom top (point a).
    by apply: (allP evsin); rewrite evs'eq !inE eqxx orbT.
  have eva : lexPt (point ev) (point a).
    by apply: evle; rewrite evs'eq inE eqxx.
  have limra : forall e', e' \in evs' -> lexePt (point a) (point e').
    rewrite evs'eq => e'; rewrite inE => /orP[/eqP -> | e'q ].
      by rewrite lexePt_eqVlt eqxx.
    move: sortev=> /=; rewrite evs'eq=> /path_sorted/=; rewrite path_sortedE.
      by move=>/andP[]/allP/(_ (point e') (map_f (@point _) e'q))/lexPtW.
    exact: lexPt_trans.
  have := step_keeps_valid inbox_a inbox_e eva oute' rfo cbtom adj sval' clae
            clev limra stepeq.
  by [].
have btm_leftr:
   {in [seq point e | e <- evs'], forall e, bottom_left_cells_lex op' e}.
  have btm_left2 :=
    step_keeps_left_pts_inf inbox_e oute' rfo sval' adj cbtom clae clev
           noc btm_left' stepeq.
  by move=> evp /mapP [ev' ev'in ->]; apply/btm_left2/evle.
have evsinr : all (inside_box bottom top) [seq point ev' | ev' <- evs'].
  by move: evsin; rewrite /= => /andP[].
have clevr : close_edges_from_events bottom top evs'.
  by move: clev; rewrite /= => /andP[].
have outer :{in evs', forall ev0 : event, out_left_event ev0}.
  by move: oute; apply: sub_in1=> x xin; rewrite inE xin orbT.
have nocr : {in cell_edges op' ++ flatten [seq outgoing i | i <- evs'] &,
     no_crossing R}.
  move: noc; apply: sub_in2=> x.
  rewrite mem_cat=> /orP[].
    move/(step_sub_open_edges cbtom adj sval' oute' inbox_e stepeq)=> it.
    by rewrite /= /cell_edges catA -(catA _ _ (outgoing ev)) mem_cat it.
  by move=> xinf; rewrite /= !mem_cat xinf !orbT.
have claer : close_alive_edges bottom top op' evs'.
  by have := step_keeps_closeness inbox_e oute' rfo cbtom adj sval' clev
      clae stepeq.
have rfor : s_right_form op'.
  have noc1: {in  cell_edges op ++ outgoing ev &, no_crossing R}.
    move: noc; apply sub_in2=> x.
    rewrite mem_cat=> /orP[it| xino].
      by rewrite /= /cell_edges catA 2!mem_cat it.
    by rewrite /= !mem_cat xino !orbT.
  by apply: (step_keeps_right_form cbtom adj inbox_e sval' noc1 _ _ stepeq).
have adjr : adjacent_cells op'.
  by have := step_keeps_adjacent inbox_e oute' sval' cbtom stepeq adj.
have cbtomr : cells_bottom_top bottom top op'.
  by apply: (step_keeps_bottom_top inbox_e sval' adj cbtom oute' stepeq).
have sortev' : sorted (@lexPt R) [seq point x | x <- evs'].
  by move: sortev; rewrite /= => /path_sorted.
have llim' : {in op', forall c p, inside_box bottom top p ->
                  left_limit c = p_x p -> 
                  contains_point' p c -> has (inside_closed' p) cl'}.
  by apply: (step_keeps_cover_left_border cbtom
         adj inbox_e sval' oute' rfo clae
       clev noc btm_left' stepeq llim).
by have := Ih _ _ cov' evsinr svalr btm_leftr llim' clevr outer nocr claer
  rfor adjr cbtomr sortev' scaneq.
Qed.

Lemma middle_disj_last fc cc lcc lc nos lno:
 open = fc ++ cc ++ lcc :: lc ->
  adjacent_cells (fc ++ nos ++ lno :: lc) ->
  s_right_form  (fc ++ nos ++ lno :: lc)->
  low (head lno nos) =low (head lcc cc) ->
  high lno = high lcc ->
  {in [seq high c | c <- nos], forall g, left_pt g == (point e)} ->
  {in rcons nos lno &, disjoint_open_cells R} ->
   {in fc ++ nos ++ lno :: lc &, disjoint_open_cells R}.
Proof.
move=> ocd adjn rfon lecnct hecnct lefts ndisj.
move: pwo=> /= /andP[] _ pwo'.
have:= disoc adj pwo'.
Qed.



Lemma disjoint_open_parts fc cc lcc lc nos lno :
   open = fc ++ cc ++ lcc :: lc ->
  close_alive_edges (fc ++ nos ++ lno :: lc) future_events ->
  low (head lcc cc) <| high lcc ->
   low (head lcc cc) = low (head lno nos) ->
   high lcc = high lno ->
  {in rcons nos lno &, disjoint_open_cells R} ->
  {in fc ++ nos ++ lno :: lc &, disjoint_open_cells R}.
Proof.
move=> ocd clae_new low_high.
have lfcbot : fc != [::] -> low (head dummy_cell fc) = bottom.
  move: cbtom; rewrite ocd.
  by case: (fc) => [// | /= ca ?] /andP[] /andP[] _ /=/eqP.
have higfc : fc != nil -> high (last dummy_cell fc) = low (head lcc cc).
  elim/last_ind : (fc) ocd => [// |s c' _] /= ocd.
  move: adj; rewrite ocd cat_rcons last_rcons =>/adjacent_catW[] _ /=.
  by case: (cc) => [ | cc0 cc'] /= /andP[] /eqP ->.
move=> le_cnct.
move=> he_cnct.
have adjnew : adjacent_cells (fc ++ nos ++ lno :: lc).
  rewrite (_ : fc ++ nos ++ lno :: lc = 
                fc ++ (rcons nos lno) ++ lc);last first.
    by rewrite -cats1 -!catA.
  a d m i t.
have rfnew : s_right_form (fc ++ nos ++ lno :: lc).
  a d m i t.
apply: (@middle_disj_last _ cc lcc)=> //.

*)
End working_environment.
