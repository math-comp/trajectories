From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements generic_trajectories points_and_edges
  events.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

Notation pt := (pt (Num.RealField.sort R)).
Notation Bpt := (Bpt (Num.RealField.sort R)).
Notation p_x := (p_x (Num.RealField.sort R)).
Notation p_y := (p_y (Num.RealField.sort R)).
Notation edge := (edge R).
Notation left_pt := (@left_pt R).
Notation right_pt := (@right_pt R).
Notation valid_edge := (valid_edge (Num.RealField.sort R) <=%R edge left_pt right_pt).
Notation point_under_edge :=
  (point_under_edge (Num.RealField.sort R) <=%R +%R (fun x y => x - y) *%R 1 edge left_pt
    right_pt).

Notation "p <<= g" := (point_under_edge p g).
Notation "p >>> g" := (~~ (point_under_edge p g)).
Notation point_strictly_under_edge :=
  (point_strictly_under_edge  (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R 1
    edge left_pt right_pt).
Notation "p <<< g" := (point_strictly_under_edge p g).
Notation "p >>= g" := (~~ (point_strictly_under_edge p g)).
Notation edge_below :=
  (edge_below (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R 1
   edge left_pt right_pt).
Notation "e1 '<|' e2" := (edge_below e1 e2)( at level 70, no associativity).
Notation event := (event (Num.RealField.sort R) edge).
Notation point := (point (Num.RealField.sort R) edge).
Notation outgoing := (outgoing (Num.RealField.sort R) edge).

Notation cell := (cell (Num.RealField.sort R) edge).
Notation Bcell := (Bcell (Num.RealField.sort R) edge).
Notation low := (low (Num.RealField.sort R) edge).
Notation high := (high (Num.RealField.sort R) edge).
Notation left_pts := (left_pts (Num.RealField.sort R) edge).
Notation right_pts := (right_pts (Num.RealField.sort R) edge).
Notation set_left_pts := (set_left_pts (Num.RealField.sort R) edge).
Notation cell_center := (cell_center (Num.RealField.sort R) +%R
             (fun x y => x / y) 1 edge).
Notation update_closed_cell :=
  (update_closed_cell (Num.RealField.sort R) 1 edge).
Notation left_limit := (left_limit (Num.RealField.sort R) 1 edge).
Notation right_limit := (right_limit (Num.RealField.sort R) 1 edge).
Notation check_bounding_box :=
  (check_bounding_box (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y) 1 edge left_pt right_pt).

Notation start_open_cell :=
  (start_open_cell (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y)
  *%R (fun x y => x / y) edge left_pt right_pt).

Notation complete_last_open :=
  (generic_trajectories.complete_last_open (Num.RealField.sort R) eq_op
    <=%R +%R (fun x y => x - y) *%R
    (fun x y => x / y) edge left_pt right_pt).

Definition cell_eqb (ca cb : cell) : bool :=
  let: generic_trajectories.Bcell lptsa rptsa lowa higha := ca in
  let: generic_trajectories.Bcell lptsb rptsb lowb highb:= cb in
  (lptsa == lptsb :> seq pt) && (rptsa == rptsb :> seq pt) &&
  (lowa == lowb) && (higha == highb).

Lemma cell_eqP : Equality.axiom cell_eqb.
Proof.
rewrite /Equality.axiom.
move => [lptsa rptsa lowa higha] [lptsb rptsb lowb highb] /=.
have [/eqP <-|/eqP anb] := boolP(lptsa == lptsb :> seq pt).
  have [/eqP <-|/eqP anb] := boolP(rptsa == rptsb :> seq pt).
    have [/eqP <-|/eqP anb] := boolP(lowa == lowb).
      have [/eqP <-|/eqP anb] := boolP(higha == highb).
        by apply:ReflectT.
      by apply : ReflectF => [][].
    by apply : ReflectF => [][].
  by apply: ReflectF=> [][].
by apply: ReflectF=> [][].
Qed.

HB.instance Definition _ := hasDecEq.Build _ cell_eqP.

Lemma high_set_left_pts (c : cell) l : high (set_left_pts c l) = high c.
Proof. by case: c. Qed.

Lemma low_set_left_pts (c : cell) l : low (set_left_pts c l) = low c.
Proof. by case: c. Qed.

Definition valid_cell c x := valid_edge (low c) x /\ valid_edge (high c) x.

Lemma cell_order_edges_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<= (low c) -> p <<= (high c).
Proof. apply : order_edges_viz_point. Qed.

Lemma cell_order_edges_strict_viz_point c p :
valid_edge (low c) p -> valid_edge (high c) p ->
(low c) <| (high c) ->
p <<< (low c) ->  p <<< (high c).
Proof. apply: order_edges_strict_viz_point. Qed.

Definition unsafe_Bedge (a b : pt) :=
  if (ltrP (p_x a) (p_x b)) is LtrNotGe h then Bedge h else
    Bedge (ltr01 : p_x (Bpt 0 0) < p_x (Bpt 1 0)).

Notation dummy_pt := (generic_trajectories.dummy_pt (Num.RealField.sort R) 1).
Notation dummy_event := (generic_trajectories.dummy_event (Num.RealField.sort R) 1 edge).
Notation dummy_edge := (generic_trajectories.dummy_edge (Num.RealField.sort R) 1 edge unsafe_Bedge).
Notation dummy_cell := (dummy_cell (Num.RealField.sort R) 1 edge unsafe_Bedge).
Notation vertical_projection :=
  (vertical_projection (Num.RealField.sort R) <=%R +%R (fun x y => x - y) *%R
    (fun x y => x / y) edge left_pt right_pt).

Definition head_cell (s : seq cell) := head dummy_cell s.
Definition last_cell (s : seq cell) := last dummy_cell s.

Lemma left_pts_set c l: left_pts (set_left_pts c l) = l.
Proof. by move: c => []. Qed.

Notation  contains_point :=
  (contains_point (Num.RealField.sort R) eq_op <=%R +%R (fun x y => x - y) *%R 1 edge
  left_pt right_pt).
Notation midpoint :=
  (midpoint (Num.RealField.sort R) +%R (fun x y => x / y) 1).

Lemma contains_pointE p c :
  contains_point p c = (p >>= low c) && (p <<= high c).
Proof. by []. Qed.

Definition contains_point' (p : pt) (c : cell)  : bool :=
   (p >>> low c) && (p <<= (high c)).

Lemma contains_point'W p c :
  contains_point' p c -> contains_point p c.
by move=> /andP[] /underWC A B; rewrite contains_pointE A B.
Qed.

Definition open_limit c :=
  Num.min (p_x (right_pt (low c))) (p_x (right_pt (high c))).

Definition bottom_left_corner (c : cell) := last dummy_pt (left_pts c).

Definition bottom_left_cells_lex (open : seq cell) p :=
  {in open, forall c, lexPt (bottom_left_corner c) p}.

Lemma add_point_left_limit (c : cell) (p : pt) :
  (1 < size (left_pts c))%N ->
  left_limit (set_left_pts c
    (head dummy_pt (left_pts c) :: p :: behead (left_pts c))) =
  left_limit c.
Proof.
rewrite /left_limit.
by case lptsq : (left_pts c) => [ | p1 [ | p2 ps]].
Qed.

Definition inside_open_cell p c :=
  [&& contains_point p c & left_limit c <= p_x p <= open_limit c].

Definition inside_open' p c :=
  [&& inside_open_cell p c,  p >>> low c & left_limit c < p_x p] .

Lemma inside_open'E p c :
  inside_open' p c =
  [&& p <<= high c, p >>> low c, left_limit c < p_x p &
   p_x p <= open_limit c].
Proof.
rewrite /inside_open' /inside_open_cell contains_pointE.
rewrite strictE -leNgt !le_eqVlt.
rewrite [in _ >>> low c]/point_under_edge -ltNge subrr.
by case: (0 < _); case: (_ < p_x p); rewrite ?andbF ?orbT ?andbT.
Qed.

Definition inside_closed_cell p c :=
  contains_point p c && (left_limit c <= p_x p <= right_limit c).

Definition inside_closed' p c :=
  [&& inside_closed_cell p c, p >>> low c & left_limit c < p_x p].

Lemma inside_closed'E p c :
  inside_closed' p c =
  [&& p <<= high c, p >>> low c, left_limit c < p_x p &
     p_x p <= right_limit c].
Proof.
rewrite /inside_closed' /inside_closed_cell contains_pointE.
rewrite strictE -leNgt !le_eqVlt.
rewrite [in _ >>> low c]/point_under_edge -ltNge subrr.
by case: (0 < _); case: (_ < p_x p); rewrite ?andbF ?orbT ?andbT.
Qed.

Definition in_safe_side_left p c :=
  [&& p_x p == left_limit c, p <<< high c, p >>> low c &
      p \notin (left_pts c : seq pt)].

Definition in_safe_side_right p c :=
  [&& p_x p == right_limit c, p <<< high c, p >>> low c &
      p \notin (right_pts c : seq pt)].

Section proof_environment.
Variable bottom top : edge.

Definition between_edges (l h : edge) (p : pt) :=
  (p >>> l) && (p <<< h).

Definition inside_box p :=
(~~ (p <<= bottom)  && (p <<< top) ) &&
  ((p_x (left_pt bottom) < p_x p < p_x (right_pt bottom)) &&
  (p_x (left_pt top) < p_x p < p_x (right_pt top))).

Lemma inside_box_not_on p:
  inside_box p -> ~~ ((p === bottom) || (p === top)).
Proof.
move=> /andP[] /andP[] pab plt /andP[] /andP[] /ltW a /ltW b
  /andP[] /ltW c /ltW d.
have vb : valid_edge bottom p by rewrite /valid_edge a b.
have vt : valid_edge top p by rewrite /valid_edge c d.
move: pab; rewrite (under_onVstrict vb) !negb_or => /andP[] -> _ /=.
by move: plt; rewrite (strict_nonAunder vt)=> /andP[] ->.
Qed.

(* this function removes consecutives duplicates, meaning the seq needs
 to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq (A : eqType) (s : seq A) : (seq A) :=
  match s with
  | [::] => [::]
  | a::q => match q with
            | [::] => s
            | b::r => if a == b then no_dup_seq q else a::(no_dup_seq q)
            end
    end.

Lemma no_dup_seq_aux_eq {A : eqType} (s : seq A) :
  no_dup_seq s = no_dup_seq_aux eq_op s.
Proof. by elim: s => [ | a s /= ->]. Qed.

Lemma last_no_dup_seq {T : eqType} (s : seq T) d:
  last d (no_dup_seq s) = last d s.
Proof.
elim: s d => [ | a [ | b s'] Ih] //.
rewrite /=; case: ifP=> [/eqP ab | anb].
  by apply: Ih.
move=> d /=; apply: Ih.
Qed.

Lemma head_no_dup_seq {T : eqType} (s : seq T) d:
  head d (no_dup_seq s) = head d s.
Proof.
elim: s d => [ | a [ | b s'] Ih] //.
rewrite /=; case: ifP=> [/eqP ab | anb].
  by move=> d; rewrite Ih ab.
by [].
Qed.

(* TODO : remove duplication with generic_trajectories *)
Definition close_cell (p : pt) (c : cell) :=
  match vertical_projection p (low c),
        vertical_projection p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 =>
    Bcell (left_pts c) (no_dup_seq [:: p2; p; p1]) (low c) (high c)
  end.

Definition closing_cells (p : pt) (contact_cells: seq cell) : seq cell :=
  [seq close_cell p c | c <- contact_cells].

Lemma closing_cellsE p cs :
  closing_cells p cs =
  generic_trajectories.closing_cells (Num.RealField.sort R) eq_op <=%R +%R
  (fun x y => x - y) *%R (fun x y => x / y) edge left_pt right_pt
   p cs.
Proof. by []. Qed.

Lemma close_cell_in (p' : pt) c :
  valid_cell c p' ->
  p' \in (right_pts (close_cell p' c): seq pt).
Proof.
move=> [] vl vh.
rewrite /close_cell; rewrite (pvertE vl) (pvertE vh) /=.
by case: ifP=> [/eqP <- | ];
  case: ifP=> [/eqP <- // | _ ]; rewrite !inE eqxx ?orbT.
Qed.

Lemma close_cell_preserve_3sides p c :
  [/\ low (close_cell p c) = low c,
      high (close_cell p c) = high c &
      left_pts (close_cell p c) = left_pts c].
Proof.
rewrite /close_cell.
case: (vertical_projection p (low c))=> [p1 | ] //.
by case: (vertical_projection p (high c))=> [p2 | ].
Qed.

Lemma right_limit_close_cell p1 c :
  valid_edge (low c) p1 -> valid_edge (high c) p1 ->
  right_limit (close_cell p1 c) = p_x p1.
Proof.
move=> vlc vhc; rewrite /close_cell /right_limit.
rewrite !pvertE //=.
by case: ifP; case: ifP.
Qed.

Lemma left_limit_close_cell p1 c :
   left_limit (close_cell p1 c) = left_limit c.
Proof.
rewrite /close_cell.
by do 2 (case: (vertical_projection _ _) => //).
Qed.

Lemma top_right_close_cell p1 c :
  p1 === high c ->
  valid_edge (low c) p1 ->
  head dummy_pt (right_pts (close_cell p1 c)) = p1.
Proof.
move=> /[dup] p1on /andP[] _ vh vl.
rewrite /close_cell.
rewrite (pvertE vl) (pvertE vh) /=.
rewrite pt_eqE eqxx.
rewrite (on_pvert p1on) eqxx /=.
by case: ifP=> // /eqP <-.
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

Lemma inside_box_between p : inside_box p -> between_edges bottom top p.
Proof.  by move=> /andP[]. Qed.

Lemma inside_box_valid_bottom_top p g :
  inside_box p ->
  g \in [:: bottom; top] -> valid_edge g p.
Proof.
move=>/andP[] _ /andP[] /andP[] /ltW a /ltW b /andP[] /ltW c /ltW d.
rewrite /valid_edge/generic_trajectories.valid_edge.
by rewrite !inE=> /orP[] /eqP ->; rewrite ?(a, b, c, d).
Qed.

Definition end_edge_ext (g : edge) (evs : seq event) :=
  (g \in [:: bottom; top]) || end_edge g evs.

Lemma end_edgeW g evs : end_edge g evs -> end_edge_ext g evs.
Proof. by rewrite /end_edge_ext=> ->; rewrite orbT. Qed.

Definition close_alive_edges open future_events : bool :=
all (fun c => (end_edge_ext (low c) future_events) &&
    (end_edge_ext (high c) future_events)) open.

Lemma insert_opening_all (first_cells  new_open_cells last_cells : seq cell) p :
all p first_cells  -> all p new_open_cells  ->
  all p last_cells  -> all p (first_cells++new_open_cells++ last_cells).
Proof.
move => C_first C_new C_last.
 rewrite  all_cat all_cat.
apply /andP.
split.
  by [].
apply /andP.
split.
  by [].
by [].
Qed.

Lemma insert_opening_closeness first_cells new_open_cells last_cells events :
  close_alive_edges first_cells events -> close_alive_edges new_open_cells events ->
  close_alive_edges last_cells events -> close_alive_edges (first_cells++new_open_cells++ last_cells) events.
Proof.
apply insert_opening_all.
Qed.

Definition adj_rel := [rel x y : cell | high x == low y].

Definition adjacent_cells := sorted adj_rel.

Lemma adjacent_catW s1 s2 :
  adjacent_cells (s1 ++ s2) -> adjacent_cells s1 /\ adjacent_cells s2.
Proof.
case: s1 => [ // | cs1  s1 /=]; rewrite /adjacent_cells.
rewrite cat_path => /andP[] -> ps2; split=> //.
by move/path_sorted: ps2.
Qed.

Lemma adjacent_cut l2 a lc :
l2 != nil ->
((high (last dummy_cell l2) == low a) &&
adjacent_cells l2 &&
adjacent_cells (a::lc) ) =
adjacent_cells (l2 ++ a::lc).
Proof.
case : l2 => [//= | c2 q2 _].
elim : q2 c2 => [ | c3 q3 IH]  c2 //=.
by rewrite andbT.
have /= IH' := IH c3.
rewrite andbCA.
rewrite -IH'.
by rewrite !andbA.
Qed.

Definition bottom_edge_seq_above (s : seq cell) (p : pt) :=
  if s is c :: _ then (p) <<= (low c) else true.

Definition bottom_edge_seq_below (s : seq cell) (p : pt) :=
  if s is c :: _ then ~~ (p <<< low c) else true.

Lemma strict_under_cell (c : cell) (p : pt) :
  valid_cell c p ->
  low c <| high c -> p <<= (low c) -> ~~ contains_point p c ->
  p <<< (low c).
Proof.
move=> valcp rfc.
move: (valcp)=> [vallp valhp].
rewrite (under_onVstrict vallp) => /orP [] //.
move=> ponl; rewrite /contains_point negb_and negbK=> /orP[] //.
case/negP.
apply: (cell_order_edges_viz_point vallp) => //.
by rewrite under_onVstrict // ponl.
Qed.

Definition s_right_form (s : seq cell)  : bool :=
  all (fun c => low c <| high c ) s.

Definition seq_valid (s : seq cell) (p : pt) : bool :=
    all (fun c => (valid_edge (low c) p) && (valid_edge (high c) p)) s.

Lemma seq_valid_high (s : seq cell) (p : pt) :
  seq_valid s p -> {in [seq high i | i <- s], forall g, valid_edge g p}.
Proof.
by move=> sval g /mapP [c cin ->]; move: (allP sval c cin)=> /andP[].
Qed.

Lemma seq_valid_low (s : seq cell) (p : pt) :
  seq_valid s p -> {in [seq low i | i <- s], forall g, valid_edge g p}.
Proof.
by move=> sval g /mapP [c cin ->]; move: (allP sval c cin)=> /andP[].
Qed.

Lemma insert_opening_valid fc nc lc p :
  [&& seq_valid fc p, seq_valid nc p & seq_valid lc p] =
  seq_valid (fc ++ nc ++ lc) p.
Proof.
by rewrite /seq_valid !all_cat.
Qed.

Lemma strict_under_seq p c q :
  adjacent_cells (c :: q) ->
  seq_valid (c :: q) p ->
  s_right_form (c :: q) ->
  p <<< (low c) ->
  forall c1, c1 \in q -> p <<< (low c1).
Proof.
elim: q c => [// | c' q Ih] c adj vals rfs plow c1 c1in.
move: adj; rewrite /adjacent_cells /= => /andP[/eqP eq_edges adj'].
move: vals; rewrite /seq_valid /= => /andP[/andP[vallc valhc] valc'q].
move: rfs; rewrite /s_right_form /= => /andP[lowhigh rfc'q].
have pc' : p <<< (low c').
  by rewrite -eq_edges; apply: (cell_order_edges_strict_viz_point vallc).
have [/eqP c1c' | c1nc'] := boolP (c1 == c').
  by rewrite c1c'.
apply: (Ih c')=> //.
  by move: c1in; rewrite !inE (negbTE c1nc').
Qed.

Lemma strict_under_seq' p c q :
  adjacent_cells (c :: q) ->
  seq_valid (c :: q) p ->
  s_right_form (c :: q) ->
  p <<< (low c) ->
  forall c1, c1 \in (c :: q) -> p <<< (low c1).
Proof.
move=> adj sv rf pl c1; rewrite inE=> /orP[/eqP -> // | ].
by apply: (strict_under_seq adj sv rf pl).
Qed.

Lemma close_imp_cont c e :
low c <| high c ->
valid_edge (low c) (point e) /\ valid_edge (high c) (point e) ->
event_close_edge (low c) e \/  event_close_edge (high c) e ->
contains_point (point e) c.
Proof.
rewrite contains_pointE /event_close_edge .
move =>  rf val [/eqP rlc | /eqP rhc].
move : rf val.
  rewrite !strictE -rlc {rlc e}.
  have := area3_two_points (right_pt (low c)) (left_pt (low c)) => [][] _ [] -> _.
  rewrite ltxx /= /edge_below.
  move => /orP [] /andP [] //= => pablhlow pabrhlow [] _ validrlhigh.
  apply: not_strictly_above pablhlow pabrhlow validrlhigh.
  move : rf val.
rewrite underE -rhc {rhc}.
have := area3_two_points (right_pt (high c)) (left_pt (high c)) => [] [] _ [] -> _ /=.
rewrite le_refl /edge_below /= andbT=> /orP [] /andP [] //= => pablhlow pabrhlow [] valrhlow _ .
apply : not_strictly_under pablhlow pabrhlow valrhlow.
Qed.

Lemma contrapositive_close_imp_cont c e :
low c <| high c->
valid_edge (low c) (point e) /\ valid_edge (high c) (point e) ->
~ contains_point (point e) c ->
~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e.
Proof.
  move => rf val ev.
have aimpb := (close_imp_cont rf val).
have  := (@contra_not  ( contains_point (point e) c) (event_close_edge (low c) e \/ event_close_edge (high c) e) aimpb ev) .
move => /orP /= .
rewrite negb_or.
by move => /andP [] /negP a /negP.
Qed.

Lemma adjacent_cons a q : adjacent_cells (a :: q) -> adjacent_cells q.
Proof.
by rewrite /=; case: q => [// | b q]; rewrite /= => /andP[].
Qed.


(* this lemma below is not true, see the counter example below.
Lemma lowest_above_all_above (s : seq cell) p :
s != [::] ->
adjacent_cells s ->
s_right_form s ->
 p <<< (low (head dummy_cell s)) ->
forall c, (c \in s) ->   p<<< (low c) /\  p <<< (high c) .
Proof.
case: s => [// | c q].
*)

Lemma lowest_above_all_above_counterexample :
  ~(forall (s : seq cell) p,
       s != [::] -> adjacent_cells s ->
       s_right_form s -> p <<< (low (head dummy_cell s)) ->
      forall c, (c \in s) ->   p<<< (low c) /\  p <<< (high c)).
Proof.
move=> abs.
set e1 := @Bedge R (Bpt 0 1) (Bpt 1 1) ltr01.
set e2 := @Bedge R (Bpt 0 2) (Bpt 1 1) ltr01.
set p := (Bpt 3%:R 0).
set c := Bcell [::] [::] e1 e2.
have exrf : s_right_form [:: c].
  rewrite /= andbT /e1 /e2 /edge_below /=.
  rewrite !underE /=.
  rewrite !strictE /=.
  rewrite !(mul0r, subrr, mul1r, subr0, add0r, addr0, oppr0, opprK, addrK).
  rewrite le_refl lt_irreflexive /= !andbT.
  rewrite -[X in X - 2%:R]/(1%:R) -opprB -natrB //  -[(2-1)%N]/1%N.
  by rewrite lerN10.
have plow : p <<< low (head dummy_cell [:: c]).
  rewrite strictE /=.
  by rewrite !(mul0r, subrr, mul1r, subr0, add0r, addr0, oppr0, opprK) ltrN10.
have := abs [::c] p isT isT exrf  plow c.
rewrite inE=> /(_ (eqxx _))=> [][] _.
rewrite strictE /=.
rewrite
  !(mul0r, subrr, mul1r, subr0, add0r, addr0, oppr0, opprK, mulr1, addrK).
rewrite -natrM -!natrB // -[X in X%:R]/(1%N).
by rewrite ltNge ler0n.
Qed.

Definition cells_low_e_top cells low_e : bool :=
  (cells != nil) && (low (head dummy_cell cells) == low_e) && (high (last dummy_cell cells) == top).

Definition cells_bottom_top cells : bool :=
  cells_low_e_top cells bottom.

Lemma bottom_imp_seq_below s p :
cells_bottom_top s -> inside_box p -> bottom_edge_seq_below s p.
Proof.
case s=> [// | c q].
rewrite /cells_bottom_top /cells_low_e_top => /andP []/andP [] _ /eqP /= loweq _.
rewrite /bottom_edge_seq_below  /inside_box loweq => /andP [] /andP []  /negP nsab _ _ /=.
by apply /underWC/negP.
Qed.

Lemma exists_cell_aux low_e p open :
cells_low_e_top open low_e -> adjacent_cells open ->
p >>> low_e ->  p <<< top ->
exists2 c : cell, c \in open & contains_point' p c.
Proof.
elim : open low_e => [//= | c0 q IH ].
case cont : (contains_point' p c0).
  by exists c0; rewrite ?cont ?inE ?eqxx.
have := (IH (high c0)).
move => IH' low_e {IH}.
rewrite /cells_low_e_top => /andP[] /andP [] _ /= /eqP <- hightop.
move=> adj lowunder topabove.
  have : cells_low_e_top q (high c0).
  rewrite /cells_low_e_top /=.
  have qnnil: q!= nil.
    move : hightop lowunder topabove  cont {IH'} adj.
    case : q => //=.
    rewrite  /contains_point' /=.
    by move=> /eqP -> -> /underW ->.
  rewrite qnnil /=.
  move : hightop qnnil adj IH'.
  case : q => [ // | a q /=].
  move => hightop.
  by rewrite hightop eq_sym => _ /andP [] ->.
move => lowtop /=.
rewrite /contains_point' in cont.
move : lowunder cont  => -> /= /negbT phc.
have := (IH' lowtop (path_sorted adj) phc topabove) .
move => [] x xinq cpx.
by exists x; rewrite ?in_cons ?xinq /= ?orbT ?cpx.
Qed.

Lemma exists_cell  p open :
cells_bottom_top open -> adjacent_cells open  ->
between_edges bottom top p ->
exists2 c : cell, c \in open & contains_point' p c.
Proof.
move=> cbtom adj /[dup] inbox_e /andP[] pa pu.
by apply:  (exists_cell_aux cbtom adj).
Qed.

Definition cell_edges cells := map low cells ++ map high cells.

Lemma head_not_end q e future_events :
close_alive_edges q (e :: future_events) ->
(forall c, (c \in q) ->
~ event_close_edge (low c) e /\ ~ event_close_edge (high c) e) ->
close_alive_edges q (future_events).
Proof.
elim q => [//| c' q' IH cae].
have cae': close_alive_edges q' (e :: future_events).
  move : cae.
  by rewrite /close_alive_edges /all => /andP [] /andP [] _ _.
move=> condition.
rewrite /=.
apply/andP; split; last first.
  apply: IH=> //.
  by move=> c cin; apply condition; rewrite inE cin orbT.
move: cae; rewrite /= /end_edge_ext /= => /andP[] /andP[] /orP[].
  move=> -> +; rewrite orTb=> /orP[].
    by move=> ->.
  move=> /orP [abs | ].
  case: (condition c').
    by rewrite inE eqxx.
  by rewrite abs.
  by move=> ->; rewrite orbT.
  move=> /orP [abs | ].
  case: (condition c').
    by rewrite inE eqxx.
  by rewrite abs.
move=> ->; rewrite orbT.
move=> /orP[] .
    by move=> ->.
  move=> /orP [abs | ].
  case: (condition c').
    by rewrite inE eqxx.
  by rewrite abs.
by move=> ->; rewrite orbT.
Qed.

Lemma valid_between_events g e p future :
lexePt e p ->
(forall e', e' \in future -> lexePt p (point e')) ->
valid_edge g e -> inside_box p -> end_edge_ext g future ->
valid_edge g p.
Proof.
move => einfp pinffut vale.
rewrite /inside_box => /andP [] _ /andP [] botv topv.
rewrite /end_edge => /orP [].
  rewrite !inE /valid_edge/generic_trajectories.valid_edge.
  by move=> /orP [] /eqP ->; rewrite !ltW;
    move: botv topv=> /andP[] a b /andP[] c d; rewrite ?(a,b,c,d).
move => /hasP [] e' e'in e'c.
have pinfe' := pinffut e' e'in.
rewrite /valid_edge; apply /andP; split.
  move : vale.
  rewrite /valid_edge => /andP [] ginfe _.
  move : einfp.
  rewrite /lexPt => /orP [esinfp | /andP [] /eqP <- //].
  by rewrite ltW // (le_lt_trans ginfe esinfp).
move : e'c.
rewrite /event_close_edge => /eqP ->.
move : pinfe'.
rewrite /lexPt => /orP [ | /andP [] /eqP -> //].
apply ltW .
Qed.

Lemma replacing_seq_adjacent l1 l2 fc lc :
l1 != nil -> l2 != nil ->
low (head dummy_cell l1) = low (head dummy_cell l2) ->
high (last dummy_cell l1) = high (last dummy_cell l2) ->
adjacent_cells (fc ++ l1 ++ lc) ->
adjacent_cells l2 ->
adjacent_cells (fc ++ l2 ++ lc).
Proof.
rewrite /adjacent_cells; case: fc => [ | a0 fc] /=; case: l1 => //=;
   case: l2 => //=; move=> a2 l2 a1 l1 _ _ a1a2 l1l2.
  rewrite cat_path => /andP[] pl1 plc pl2; rewrite cat_path pl2.
  by move: plc; case: lc => [// | a3 l3 /=]; rewrite -l1l2.
rewrite cat_path /= cat_path => /andP[] pfc /andP[] jfca1 /andP[] pl1 plc pl2.
rewrite cat_path /= cat_path; rewrite pfc -a1a2 jfca1 pl2.
by move: plc; case: lc => [// | a3 l3 /=]; rewrite -l1l2.
Qed.

Lemma replacing_seq_cells_bottom_top l1 l2 fc lc :
  l1 != nil -> l2 != nil ->
  low (head dummy_cell l1) = low (head dummy_cell l2) ->
  high (last dummy_cell l1) = high (last dummy_cell l2) ->
  cells_bottom_top (fc ++ l1 ++ lc) = cells_bottom_top (fc ++ l2 ++ lc).
Proof.
move=> l1n0 l2n0 hds tls.
case: fc => [ | c1 fc]; case: lc => [ | c2 lc];
   rewrite /cells_bottom_top /cells_low_e_top /= ?cats0.
-  by rewrite l1n0 l2n0 hds tls.
-  case : l1 l1n0 hds tls => [ // | c1 l1] _; case: l2 l2n0 => [ | c3 l2] //= _.
   by move=> -> lts; rewrite !last_cat /=.
- case: l1 l1n0 tls {hds} => [ | c1' l1] //= _; case: l2 l2n0 => [ | c2' l2] //.
  by move=> _ /=; rewrite !last_cat /= => ->.
by rewrite !last_cat /=.
Qed.

Definition all_edges cells events :=
  cell_edges cells ++ events_to_edges events.

Lemma mono_cell_edges s1 s2 : {subset s1 <= s2} ->
  {subset cell_edges s1 <= cell_edges s2}.
Proof.
by move=> Sub g; rewrite mem_cat => /orP[] /mapP[c cin geq];
  rewrite /cell_edges geq mem_cat map_f ?orbT // Sub.
Qed.

Lemma cell_edges_eqi s1 s2 : s1 =i s2 ->
 cell_edges s1 =i cell_edges s2.
Proof.
move=> eqi.
have sub1 : {subset s1 <= s2} by move=> g; rewrite eqi.
have sub2 : {subset s2 <= s1} by move=> g; rewrite eqi.
move=> g; apply/idP/idP.
  by move/(mono_cell_edges sub1).
by move/(mono_cell_edges sub2).
Qed.

Lemma cell_edges_catC s1 s2 :
  cell_edges (s1 ++ s2) =i cell_edges (s2 ++ s1).
Proof.
move=> g.
by apply/idP/idP; apply: mono_cell_edges => {}g; rewrite !mem_cat orbC.
Qed.

Lemma cell_edges_cat (s1 s2 : seq cell) :
  cell_edges (s1 ++ s2) =i cell_edges s1 ++ cell_edges s2.
Proof.
move=> g; rewrite /cell_edges !(mem_cat, map_cat) !orbA; congr (_ || _).
by rewrite -!orbA; congr (_ || _); rewrite orbC.
Qed.

Lemma cell_edges_cons c s : cell_edges (c :: s) =i
    (low c :: high c :: cell_edges s).
Proof. by move=> g; rewrite -[c :: s]/([:: c] ++ s) cell_edges_cat. Qed.

Lemma cell_edges_catCA s1 s2 s3 :
  cell_edges (s1 ++ s2 ++ s3) =i cell_edges (s2 ++ s1 ++ s3).
Proof.
move=> g; rewrite 2!catA [in LHS]cell_edges_cat [in RHS]cell_edges_cat.
rewrite [in LHS]mem_cat [in RHS]mem_cat; congr (_ || _).
by rewrite cell_edges_catC.
Qed.

Lemma cell_edges_close_cell p c :
  cell_edges [:: close_cell p c] = cell_edges [:: c].
Proof.
rewrite /cell_edges /=.
by have [-> -> _] := close_cell_preserve_3sides p c.
Qed.

Lemma cell_edges_closing_cells p cs :
  cell_edges (closing_cells p cs) =i cell_edges cs.
Proof.
move=> g.
elim: cs => [ | c1 cs Ih]; first by [].
rewrite /= -[_ :: _]/([:: _] ++ _) cell_edges_cat mem_cat Ih.
rewrite cell_edges_close_cell.
rewrite -[c1 :: cs]/([:: c1] ++ cs) cell_edges_cat.
by rewrite (mem_cat _ _ (cell_edges _)).
Qed.

Definition cover_left_of p s1 s2 :=
  forall q, inside_box q -> lexePt q p ->
  has (inside_open' q) s1 || has (inside_closed' q) s2.

Lemma contains_to_inside_open' open evs c p :
  seq_valid open p -> close_alive_edges open evs ->
  inside_box p ->
  p_x (head dummy_pt (left_pts c)) < p_x p ->
  all (lexePt p) [seq point e | e <- evs] ->
  c \in open -> contains_point' p c -> inside_open' p c.
Proof.
rewrite inside_open'E /contains_point'.
move=> val clae inbox_p leftb rightb cin /andP[] -> ->.
rewrite leftb.
have cledge g : (g \in [:: bottom; top]) || end_edge g evs ->
        p_x p <= p_x (right_pt g).
  have [/ltW pbot /ltW ptop] : p_x p < p_x (right_pt bottom) /\
             p_x p < p_x (right_pt top).
    by apply/andP; move:inbox_p=> /andP[] _ /andP[] /andP[] _ -> /andP[] _ ->.
  move=>/orP[]; [by rewrite !inE => /orP[]/eqP -> | ].
  move/hasP=> [ev' ev'in /eqP ->].
  apply: lexePt_xW.
  by apply/(allP rightb)/map_f.
have /andP [cmp1 cmp2] : (p_x p <= p_x (right_pt (low c))) &&
                (p_x p <= p_x (right_pt (high c))).
  by apply/andP; split; apply/cledge; move/allP: clae=> /(_ _ cin)/andP[].
rewrite /open_limit.
by case: (ltrP (p_x (right_pt (low c))) (p_x (right_pt (high c))))=> //.
Qed.

Lemma contact_middle_at_point p cc s1 s2 c :
  adjacent_cells cc ->
  seq_valid cc p ->
  all (contains_point p) cc ->
  cc = s1 ++ c :: s2 ->
  (s1 != nil -> p === low c) /\ (s2 != nil -> p === high c).
Proof.
move=> adj sv ctps dec.
have cin : c \in cc by rewrite dec !(inE, mem_cat) eqxx ?orbT.
have [vlc vhc] : valid_cell c p by move: (allP sv _ cin) => /andP.
have /andP[plc phc] := (allP ctps _ cin).
split.
elim/last_ind: s1 dec => [// | s1 a _] dec _.
  have /eqP ac : high a == low c.
    case: s1 dec adj => [ | b s1] -> /=; first by move => /andP[] ->.
    by rewrite cat_path last_rcons /= => /andP[] _ /andP[].
  have ain : a \in cc by rewrite dec -cats1 !(mem_cat, inE) eqxx ?orbT.
  apply: (under_above_on vlc _ plc).
  by rewrite -ac; move: (allP ctps _ ain)=> /andP[].
case: s2 dec => [// | a s2] + _.
rewrite -[ c :: _]/([:: c] ++ _) catA => dec.
have /eqP ca : high c == low a.
  case: s1 dec adj => [ | b s1] -> /=; first by move=> /andP[] ->.
  by rewrite cats1 cat_path last_rcons /= => /andP[] _/andP[].
have ain : a \in cc by rewrite dec !(mem_cat, inE) eqxx ?orbT.
apply: (under_above_on vhc phc).
by rewrite ca; move: (allP ctps _ ain)=> /andP[].
Qed.

Definition strict_inside_open (p : pt) (c : cell) :=
  (p <<< high c) && (~~(p <<= low c)) &&
  (left_limit c < p_x p < open_limit c).

Definition strict_inside_closed (p : pt) (c : cell) :=
  (p <<< high c) && (~~(p <<= low c)) &&
  (left_limit c < p_x p < right_limit c).

Definition o_disjoint (c1 c2 : cell) :=
  forall p, ~~(inside_open' p c1 && inside_open' p c2).

Definition o_disjoint_e (c1 c2 : cell) :=
  c1 = c2 \/ o_disjoint c1 c2.

Lemma o_disjointC c1 c2 : o_disjoint c1 c2 -> o_disjoint c2 c1.
Proof. by move=> c1c2 p; rewrite andbC; apply: c1c2. Qed.

Definition disjoint_open_cells :=
  forall c1 c2 : cell, o_disjoint_e c1 c2.


Lemma seq_edge_below s c :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  path edge_below (head dummy_edge [seq low i | i <- rcons s c])
     [seq high i | i <- rcons s c].
Proof.
elim: s => [ | c0 s Ih] // /[dup]/= /adjacent_cons adj' adj /andP[] rfc rfo.
apply/andP;split;[exact: rfc | ].
have -> : high c0 = head dummy_edge [seq low i | i <- rcons s c].
  by move: adj; case: (s) => [ | c1 q]; rewrite //= => /andP[] /eqP -> _.
by apply: Ih.
Qed.

Lemma seq_edge_below' s :
  adjacent_cells s -> s_right_form s ->
  path edge_below (head dummy_edge [seq low i | i <- s])
     [seq high i | i <- s].
Proof.
elim: s => [ | c0 s Ih] // /[dup]/= /adjacent_cons adj' adj /andP[] rfc rfo.
apply/andP;split;[exact: rfc | ].
case sq : s => [// | c1 s'].
have -> : high c0 = head dummy_edge [seq low i | i <- c1 :: s'].
  by move: adj; rewrite sq /= => /andP[] /eqP.
by rewrite -sq; apply: Ih.
Qed.

Lemma below_seq_higher_edge_aux s g e p  :
  {in rcons s g & &, transitive edge_below} ->
  all (fun g' => valid_edge g' p) (rcons s g) ->
  sorted edge_below (rcons s g) ->
  all (fun g' => valid_edge g' e) (rcons s g) ->
  {in rcons s g &, no_crossing R} ->
  {in rcons s g, forall g', p <<< g' -> p <<< g}.
Proof.
elim: s => [ | g0 s Ih].
  rewrite /=?andbT => /= _ _ _ sval noc g1.
  by rewrite inE=> /eqP ->.
rewrite -[rcons _ _]/(g0 :: rcons s g)=> e_trans svp.
move/[dup]/path_sorted=> adj' adj /= sval noc.
move=> g1 g1in puc1.
have v0p : valid_edge g0 p by apply: (allP svp); rewrite inE eqxx.
have vedge g2 : g2 \in rcons s g -> valid_edge g2 p.
  by move=> g2in; apply: (allP svp); rewrite inE g2in orbT.
have vgp : valid_edge g p by apply: vedge; rewrite mem_rcons inE eqxx.
have g0below : g0 <| g.
  move: adj; rewrite /= (path_sorted_inE e_trans); last by apply/allP.
  by move=> /andP[]/allP + _; apply; rewrite mem_rcons inE eqxx.
move:g1in; rewrite /= inE => /orP[/eqP g1g0 | intail].
  by apply: (order_edges_strict_viz_point v0p vgp g0below); rewrite -g1g0.
have tr' : {in rcons s g & &, transitive edge_below}.
  move=> g1' g2' g3' g1in g2in g3in.
  by apply: e_trans; rewrite inE ?g1in ?g2in ?g3in orbT.
have svp' : all (fun x => valid_edge x p) (rcons s g) by case/andP: svp.
have sval' : all (fun x => valid_edge x e) (rcons s g) by case/andP: sval.
have noc' : {in rcons s g &, no_crossing R}.
  by move=> g1' g2' g1in g2in; apply: noc; rewrite !inE ?g1in ?g2in orbT.
by apply: (Ih tr' svp' adj' sval' noc' g1 intail puc1).
Qed.

Definition open_cell_side_limit_ok c :=
  [&& left_pts c != [::] :> seq pt,
   all (fun (p : pt) => p_x p == left_limit c) (left_pts c),
  sorted >%R [seq p_y p | p <- left_pts c],
  (head dummy_pt (left_pts c) === high c) &
  (last dummy_pt (left_pts c) === low c)].

Lemma open_cell_side_limit_ok_left_pt_limit c :
  open_cell_side_limit_ok c ->
  {in left_pts c, forall p, p_x p = left_limit c}.
Proof.
by move=> /andP[] _ /andP[] /allP + _=> /[swap] x /[apply] /eqP.
Qed.

Lemma open_cell_side_limit_ok_left_pt_above c j:
  open_cell_side_limit_ok c ->
  (j < size (left_pts c))%N ->
  nth dummy_pt (left_pts c) j >>= low c.
Proof.
move=> + js.
move=> /andP[] _ /andP[] /allP samex /andP[] srt /andP[] _ onl.
have vl : valid_edge (low c) (last dummy_pt (left_pts c)).
  by move: onl=> /andP[].
have nth_in := mem_nth dummy_pt js.
have xlast : p_x (last dummy_pt (left_pts c)) =
  p_x (nth dummy_pt (left_pts c) j).
  have /(last_in_not_nil dummy_pt): (left_pts c) != [::].
    by move: js; case: left_pts.
  move=> /samex /eqP ->; by rewrite (eqP (samex _ nth_in)).
move: srt.
have gt_trans : transitive (>%R : rel R) by apply/rev_trans/lt_trans.
move: (map_f p_y nth_in) => /(sorted_last (p_y dummy_pt) gt_trans).
move=> /[apply] main.
apply/negP=> abs.
have vj : valid_edge (low c) (nth dummy_pt (left_pts c) j).
  by rewrite -(same_x_valid (low c) xlast).
suff : (last dummy_pt (left_pts c)) <<< low c.
  by rewrite strict_nonAunder // onl.
apply: (same_x_strict_under_edge_le_y_trans vj (esym xlast) _ abs).
move: main; rewrite last_map eq_sym=> /orP[ | /ltW]; last by [].
by rewrite le_eqVlt => ->.
Qed.

Lemma open_cell_side_limit_ok_left_pt_strict_under c j:
  open_cell_side_limit_ok c ->
  (j.+1 < size (left_pts c))%N ->
  nth dummy_pt (left_pts c) j.+1 <<< high c.
Proof.
move=> + js.
move=> /andP[] _ /andP[] /allP samex /andP[] srt /andP[] onh _.
have vh: valid_edge (high c) (head dummy_pt (left_pts c)).
  by move: onh=> /andP[].
have nth_in := mem_nth dummy_pt js.
have xhead : p_x (head dummy_pt (left_pts c)) =
  p_x (nth dummy_pt (left_pts c) j.+1).
  have /(head_in_not_nil dummy_pt): (left_pts c) != [::].
    by move: js; case: left_pts.
  move=> /samex /eqP ->; by rewrite (eqP (samex _ nth_in)).
move: srt.
have gt_trans : transitive (>%R : rel R) by apply/rev_trans/lt_trans.
have nthq : nth dummy_pt (left_pts c) j.+1 =
  nth dummy_pt (behead (left_pts c)) j.
  by move: js; case: (left_pts c).
have : nth dummy_pt (left_pts c) j.+1 \in behead (left_pts c).
  move: (js); case: (left_pts c) => [ | a tl] //=; rewrite ltnS.
  by apply: mem_nth.
case lptsq: (left_pts c) (js) => [ | a tl] //= _ nth_intl.
rewrite (path_sortedE gt_trans)=> /andP[] /allP /(_ _ (map_f _ nth_intl)) /= .
move=> main _.
have vj : valid_edge (high c) (nth dummy_pt (left_pts c) j.+1).
  by rewrite -(same_x_valid (high c) xhead).
apply: (same_x_under_edge_lt_y_trans vh).
    by rewrite xhead lptsq.
  by rewrite lptsq.
by rewrite under_onVstrict // onh.
Qed.

Lemma open_cell_side_limit_ok_left_limit_valid c p :
  open_cell_side_limit_ok c ->
  p_x p = left_limit c ->
  valid_edge (low c) p && valid_edge (high c) p.
Proof.
move=> + sx.
move=> /andP[] ls /andP[] /allP al /andP[] _ /andP[] /andP[] _ hh /andP[] _ ll.
move: (al) => /(_ _ (last_in_not_nil dummy_pt ls)) => /eqP lll.
move: (al) => /(_ _ (head_in_not_nil dummy_pt ls)) => /eqP hll.
have := same_x_valid (low c) (eq_trans lll (esym sx)) => <-.
have := same_x_valid (high c) (eq_trans hll (esym sx)) => <-.
by rewrite hh ll.
Qed.

Lemma open_cell_side_limit_ok_last c :
  open_cell_side_limit_ok c ->
  p_x (last dummy_pt (left_pts c)) = left_limit c.
Proof.
rewrite /open_cell_side_limit_ok/left_limit=> /andP[] + /andP[] + _.
case: (left_pts c)=> [ // | a tl] _ /allP /(_ (last a tl) (mem_last _ _)) .
by move=> /eqP.
Qed.

Lemma strict_inside_open_valid c (p : pt) :
  open_cell_side_limit_ok c ->
  strict_inside_open p  c ->
  valid_edge (low c) p && valid_edge (high c) p.
Proof.
move=> /[dup] + /open_cell_side_limit_ok_last.
move=> /andP[]; rewrite /strict_inside_open /left_limit /open_limit.
case: (left_pts c) => [// | w tl _] /andP[] allxl /andP[] _ /andP[].
rewrite /=; move=> /andP[] _ /andP[] lh _ /andP[] _ /andP[] ll _ lastq.
rewrite lastq in ll.
move=> /andP[] _ /andP[] ls rs.
rewrite /valid_edge/generic_trajectories.valid_edge ltW; last first.
  by apply: (le_lt_trans ll).
rewrite ltW; last first.
  apply: (lt_le_trans rs).
  by case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c)))) => // /ltW.
rewrite ltW; last first.
  apply: (le_lt_trans lh).
  by rewrite (eqP (allP allxl w _)) //= inE eqxx.
apply: ltW.
apply: (lt_le_trans rs).
by case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c)))) => // /ltW.
Qed.

Lemma valid_high_limits c p :
  open_cell_side_limit_ok c ->
  left_limit c < p_x p <= open_limit c -> valid_edge (high c) p.
Proof.
move=>/andP[] wn0 /andP[] /allP allx /andP[] _ /andP[] /andP[] _ /andP[] + _ _.
rewrite (eqP (allx _ (head_in_not_nil _ wn0))) // => onh.
rewrite /left_limit=> /andP[] /ltW llim.
rewrite /valid_edge/generic_trajectories.valid_edge (le_trans onh llim) /=.
rewrite /open_limit.
case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c))))=> // /[swap].
by apply: le_trans.
Qed.

Lemma valid_low_limits c p :
  open_cell_side_limit_ok c ->
  left_limit c < p_x p <= open_limit c -> valid_edge (low c) p.
Proof.
move=> /[dup] + /open_cell_side_limit_ok_last.
move=>/andP[] wn0 /andP[] /allP ax /andP[] _ /andP[] _ /andP[] _ /andP[] onl _.
rewrite /left_limit=> lastq /andP[] /ltW llim.
rewrite lastq in onl.
rewrite /valid_edge/generic_trajectories.valid_edge (le_trans onl llim) /=.
rewrite /open_limit.
case: (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c))))=> // /[swap].
by move=> ph hl; apply/ltW/(le_lt_trans ph hl).
Qed.

Lemma inside_openP p c :
  open_cell_side_limit_ok c ->
  strict_inside_open p c =
  [&& inside_open' p c, p_x p < open_limit c & p <<< high c].
Proof.
move=> cok.
rewrite /strict_inside_open/inside_open'/inside_open_cell contains_pointE.
have [pin | ] := boolP (left_limit c < p_x p <= open_limit c); last first.
  rewrite (lt_neqAle _ (open_limit _)).
  by rewrite negb_and => /orP[] /negbTE /[dup] A ->; rewrite !andbF.
have vh : valid_edge (high c) p.
  by move: (pin) => /(valid_high_limits cok).
have vl : valid_edge (low c) p.
  by move: (pin) => /(valid_low_limits cok).
rewrite [in RHS](under_onVstrict) // [in RHS] strict_nonAunder // negb_and.
rewrite !le_eqVlt !negbK.
by have [uh //= | nuh] := boolP(p <<< high c);
  have [al //= | nal] := boolP(p >>> low c);
  have [lfp | nlfp] := boolP (left_limit c < p_x p);
  have [rhp | nrhp] := boolP (p_x p < open_limit c);
      rewrite ?orbT ?andbT ?orbF ?andbF.
Qed.

Lemma below_seq_higher_edge s c e p :
  {in [seq high i | i <- rcons s c] & & ,transitive edge_below} ->
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  seq_valid (rcons s c) e ->
  {in [seq high i | i <- rcons s c] &, no_crossing R} ->
  {in rcons s c, forall g, open_cell_side_limit_ok g} ->
  {in rcons s c, forall c1, strict_inside_open p c1 ->
                 valid_edge (high c) p-> p <<< high c}.
Proof.
move=> e_trans adj rf sval noc csok c1 c1in /[dup]/andP[] /andP[] puc1 _ pp2.
move=> inpc1.
set g := high c => vgp.
set sg := [seq high i | i <- s & valid_edge (high i) p].
have subp : {subset rcons sg g <= [seq high i | i <- rcons s c]}.
  move=> g1; rewrite map_rcons 2!mem_rcons 2!inE=>/orP[-> //| ].
  rewrite /sg=> /mapP[c1' + c1'eq]; rewrite mem_filter=>/andP[] _ c1'in.
  by apply/orP; right; apply/mapP; exists c1'.
have e_trans' : {in rcons sg g & &, transitive edge_below}.
  move=> g1 g2 g3 g1in g2in g3in.
  by apply: e_trans; apply: subp.
have svp : all (fun g' => valid_edge g' p) (rcons sg g).
  apply/allP=> g'; rewrite -map_rcons => /mapP [c' + ->].
  by rewrite mem_rcons inE mem_filter => /orP[/eqP -> |  /andP[] + _].
have adj' : sorted edge_below (rcons sg g).
  have sggq : rcons sg g =
             [seq i  <- [seq high j | j <- rcons s c] | valid_edge i p].
     by rewrite (@filter_map _ _ high) filter_rcons /= vgp map_rcons.
  rewrite sggq.
  apply: (sorted_filter_in e_trans).
    apply/allP=> g1 /mapP[c' + g'eq].
    rewrite topredE !mem_rcons !inE.
    rewrite /g=>/orP[/eqP <- | c'in].
      by rewrite map_rcons mem_rcons inE g'eq eqxx.
    by rewrite map_rcons mem_rcons inE; apply/orP/or_intror/mapP; exists c'.
  have := seq_edge_below' adj rf.
  by case s_eq : s => [ // | a s' /=] /andP[] _.
have noc' : {in rcons sg g &, no_crossing R}.
  by move=> g1 g2 /subp g1in /subp g2in;  apply: noc.
apply: (below_seq_higher_edge_aux e_trans' svp adj' svp noc' _ puc1).
rewrite -map_rcons; apply/mapP; exists c1 => //.
move: c1in; rewrite !mem_rcons !inE=>/orP[-> // | c1in].
rewrite mem_filter c1in andbT; apply/orP/or_intror.
apply: (proj2 (andP (strict_inside_open_valid _ inpc1))).
by apply: csok; rewrite mem_rcons inE c1in orbT.
Qed.

Lemma left_side_below_seq_higher_edge s c e p :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  seq_valid (rcons s c) e ->
  {in [seq high i | i <- rcons s c], forall g, p_x (left_pt g) < p_x e} ->
  {in [seq high i | i <- rcons s c] &, no_crossing R} ->
  {in rcons s c, forall c1, open_cell_side_limit_ok c1} ->
  {in rcons s c, forall c1, strict_inside_open p c1 ->
        valid_edge (high c) p -> p <<< high c}.
Proof.
move => adj rfs svals llim noc csok.
apply: (below_seq_higher_edge _ adj rfs svals) => //.
have vale' : {in [seq high i | i <- rcons s c], forall g, valid_edge g e}.
  by apply: seq_valid_high.
apply: (edge_below_trans _ vale' noc); right; exact: llim.
Qed.

Lemma right_side_below_seq_higher_edge s c e p :
  adjacent_cells (rcons s c) -> s_right_form (rcons s c) ->
  seq_valid (rcons s c) e ->
  {in [seq high i | i <- rcons s c], forall g, p_x e < p_x (right_pt g)} ->
  {in [seq high i | i <- rcons s c] &, no_crossing R} ->
  {in rcons s c, forall c1, open_cell_side_limit_ok c1} ->
  {in rcons s c, forall c1, strict_inside_open p c1 ->
      valid_edge (high c) p -> p <<< high c}.
Proof.
move => adj rfs svals rlim noc csok.
apply: (below_seq_higher_edge _  adj rfs svals) => //.
have vale' : {in [seq high i | i <- rcons s c], forall g, valid_edge g e}.
  by apply: seq_valid_high.
apply: (edge_below_trans _ vale' noc); left; exact: rlim.
Qed.

Lemma o_disjoint_eC (c1 c2 : cell) :
  o_disjoint_e c1 c2 -> o_disjoint_e c2 c1.
Proof.
move=> [-> // |]; first by left.
by move=> disj; right=> p; rewrite andbC; apply: disj.
Qed.

Definition closed_cell_side_limit_ok c :=
 [&& left_pts c != [::] :> seq pt,
   all (fun p : pt => p_x p == left_limit c) (left_pts c),
   sorted >%R [seq p_y p | p <- left_pts c],
   head dummy_pt (left_pts c) === high c,
   last dummy_pt (left_pts c) === low c,
    right_pts c != [::] :> seq pt,
   all (fun p : pt => p_x p == right_limit c) (right_pts c),
   sorted >%R [seq p_y p | p <- right_pts c],
   head dummy_pt (right_pts c) === high c &
   last dummy_pt (right_pts c) === low c].

Lemma x_left_pts_left_limit (c : cell) (p : pt) :
  closed_cell_side_limit_ok c ->
  p \in (left_pts c : seq pt) -> p_x p = left_limit c.
Proof.
move=> + pin; move=> /andP[] ln0 /andP[] lsx _.
by rewrite (eqP (allP lsx _ _)).
Qed.

Lemma mem_head_right_pts (c : cell):
  closed_cell_side_limit_ok c ->
  head dummy_pt (right_pts c) \in right_pts c.
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
by case (right_pts c) => [ | ? ?] //=; rewrite inE eqxx.
Qed.

Lemma x_right_pts_right_limit (c : cell) (p : pt) :
  closed_cell_side_limit_ok c ->
  p \in (right_pts c : seq pt) -> p_x p = right_limit c.
Proof.
move=> + pin; move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] rn0 /andP[] rsx _.
by rewrite (eqP (allP rsx _ _)).
Qed.

Lemma left_limit_left_pt_high_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  p_x (left_pt (high c)) <= left_limit c.
Proof.
move=> /andP[] ln0 /andP[] lsx /andP[] _ /andP[] /andP[] _ /andP[] + _ _.
by rewrite (eqP (allP lsx _ (head_in_not_nil _ ln0))).
Qed.

Lemma right_limit_right_pt_high_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  right_limit c <= p_x (right_pt (high c)).
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] rn0 /andP[] rsx /andP[] _ /andP[] /andP[] _ /andP[] _ + _.
by rewrite (eqP (allP rsx _ (head_in_not_nil _ rn0))).
Qed.

Lemma left_limit_left_pt_low_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  p_x (left_pt (low c)) <= left_limit c.
Proof.
move=> /andP[] ln0 /andP[] lsx /andP[] _ /andP[] _ /andP[].
move=> /andP[] _ /andP[] + _ _.
by rewrite (eqP (allP lsx _ (last_in_not_nil _ ln0))).
Qed.

Lemma right_limit_right_pt_low_cl (c : cell) :
  closed_cell_side_limit_ok c ->
  right_limit c <= p_x (right_pt (low c)).
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] rn0 /andP[] rsx /andP[] _ /andP[] _ /andP[] _ /andP[] _ +.
by rewrite (eqP (allP rsx _ (last_in_not_nil _ rn0))).
Qed.

Lemma closed_cell_in_high_above_low p (c : cell) :
  low c != high c ->
  low c <| high c ->
  inter_at_ext (low c) (high c) ->
  closed_cell_side_limit_ok c ->
  left_limit c < p_x p < right_limit c ->
  p === high c -> p >>> low c.
Proof.
move=> dif bel noclh cok /andP[] midl midr on.
have [vlp vhp] : valid_edge (low c) p /\ valid_edge (high c) p.
  move: cok=> /andP[] ln0 /andP[] lsx /andP[].
  move=> _ /andP[] /andP[] _ /andP[] lh _ /andP[] /andP[] _ /andP[] ll _.
  move=> /andP[] rn0 /andP[] rsx /andP[].
  move=> _ /andP[] /andP[] _ /andP[] _ rl /andP[] _ /andP[] _ rh.
  rewrite (eqP (allP lsx _ (@last_in_not_nil pt dummy_pt _ ln0))) in ll.
  rewrite (eqP (allP rsx _ (@head_in_not_nil pt dummy_pt _ rn0))) in rl.
  rewrite (eqP (allP lsx _ (@head_in_not_nil pt dummy_pt _ ln0))) in lh.
  rewrite (eqP (allP rsx _ (@last_in_not_nil pt dummy_pt _ rn0))) in rh.
  split; rewrite /valid_edge/generic_trajectories.valid_edge.
    by rewrite (ltW (le_lt_trans ll midl)) (ltW (lt_le_trans midr rh)).
  by rewrite (ltW (le_lt_trans lh midl)) (ltW (lt_le_trans midr rl)).
rewrite under_onVstrict // negb_or.
move: noclh=> [abs | noclh]; first by rewrite abs eqxx in dif.
apply/andP; split; last first.
  apply/negP=> abs.
  have := order_edges_strict_viz_point vlp vhp bel abs.
  by rewrite strict_nonAunder // on.
apply/negP=> abs.
have := noclh _ abs on; rewrite !inE=> /orP[] /eqP {}abs.
  move: midl; apply/negP; rewrite -leNgt abs.
  by apply: left_limit_left_pt_low_cl.
(* TODO: at this place, the typechecking loops, this warrants a bug report. *)
(*(  have := left_limit_max cok. *)
move: midr; apply/negP; rewrite -leNgt abs.
by apply: right_limit_right_pt_low_cl.
Qed.

Lemma left_side_under_high (c : cell) p :
  closed_cell_side_limit_ok c ->
  valid_edge (high c) p ->
  p \in (left_pts c : seq pt) ->
  p <<= high c.
Proof.
move=> cok vph pin.
set p' := Bpt (p_x p) (pvert_y p (high c)).
have sx: p_x p = p_x p' by rewrite /p'.
have p'on : p' === high c by apply: pvert_on vph.
rewrite (under_edge_lower_y sx) //.
have := cok.
move=> /andP[] ln0 /andP[] lsx /andP[] srt /andP[] hon _.
have p'q : p' = head dummy_pt (left_pts c).
  have := on_edge_same_point p'on hon.
  rewrite (eqP (allP lsx _ pin)).
  rewrite (x_left_pts_left_limit cok (head_in_not_nil _ ln0)).
  move=> /(_ erefl) samey.
  apply/(@eqP pt); rewrite pt_eqE samey eqxx andbT.
  rewrite (eqP (allP lsx _ pin)) eq_sym.
  by rewrite (allP lsx _ (head_in_not_nil _ ln0)).
move: ln0 p'q pin srt.
case: (left_pts c)=> [| p2 lpts] // _ p'q pin srt.
move: pin; rewrite (@in_cons pt) => /orP[/eqP -> | pin].
  by rewrite p'q.
apply: ltW; rewrite p'q.
move: srt=> /=; rewrite (path_sortedE); last first.
  by move=> x y z xy yz; apply: (lt_trans yz xy).
move=> /andP[] /allP/(_ (p_y p)) + _; apply.
by rewrite (@map_f pt).
Qed.

Lemma right_side_under_high (c : cell) (p : pt) :
  closed_cell_side_limit_ok c ->
  valid_edge (high c) p ->
  p \in (right_pts c : seq pt) ->
  p <<= high c.
Proof.
move=> cok vph pin.
set p' := Bpt (p_x p) (pvert_y p (high c)).
have sx: p_x p = p_x p' by rewrite /p'.
have p'on : p' === high c by apply: pvert_on vph.
rewrite (under_edge_lower_y sx) //.
have := cok.
do 5 move=> /andP[] _.
move=> /andP[] rn0 /andP[] rsx /andP[] srt /andP[] lon _.
have p'q : p' = head dummy_pt (right_pts c).
  have := on_edge_same_point p'on lon.
  have /eqP -> := allP rsx _ (head_in_not_nil dummy_pt rn0).
  have /eqP -> := allP rsx _ pin=> /(_ erefl) samey.
  apply/(@eqP pt).
  rewrite pt_eqE samey eqxx andbT.
  rewrite (eqP (allP rsx _ pin))/=.
  by rewrite (eqP (allP rsx _ (head_in_not_nil dummy_pt rn0))).
move: rn0 p'q pin srt.
elim: (right_pts c) => [| p2 rpts Ih] // rn0 p'1 pin srt.
move: pin; rewrite inE => /orP[/eqP -> | pin].
  by rewrite p'1.
rewrite /= in srt.
(* TODO : use rev_trans here. *)
have gt_trans : transitive (>%R : rel R).
  by move=> x y z xy yz ; apply: (lt_trans yz xy).
move: (srt); rewrite (path_sortedE gt_trans)=> /andP[] srt' _.
apply: ltW; rewrite p'1.
by apply: (allP srt'); rewrite map_f.
Qed.

Lemma in_bound_closed_valid (c : cell) p :
  closed_cell_side_limit_ok c ->
  left_limit c <= p_x p -> p_x p <= right_limit c ->
  valid_edge (low c) p /\ valid_edge (high c) p.
Proof.
move=> cok lp pr.
have llh := left_limit_left_pt_high_cl cok.
have lll := left_limit_left_pt_low_cl cok.
have rrh := right_limit_right_pt_high_cl cok.
have rrl := right_limit_right_pt_low_cl cok.
split; rewrite /valid_edge/generic_trajectories.valid_edge.
  by rewrite (le_trans lll lp) (le_trans pr rrl).
by rewrite (le_trans llh lp) (le_trans pr rrh).
Qed.

Lemma closed_cell_side_limit_ok_last c :
  closed_cell_side_limit_ok c ->
  p_x (last dummy_pt (right_pts c)) = right_limit c.
Proof.
do 5 (move=> /andP[] _); move=> /andP[] + /andP[] + _.
rewrite /right_limit.
by case: (right_pts c) => [ // | a tl] _ /allP /(_ _ (mem_last _ _)) /eqP.
Qed.

Lemma closed_right_imp_open c:
  closed_cell_side_limit_ok c -> right_limit c <= open_limit c.
Proof.
move=> /[dup] + /closed_cell_side_limit_ok_last lastq.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] ln0 /andP[] eqs /andP[] _ /andP[] /andP[] _ /andP[] _ /[swap].
move=> /andP[] _ /andP[] _.
rewrite lastq.
rewrite (eqP (allP eqs (head dummy_pt (right_pts c)) (head_in_not_nil _ ln0))).
rewrite /right_limit /open_limit.
by case : (lerP (p_x (right_pt (low c))) (p_x (right_pt (high c)))).
Qed.

Definition any_edge (b : bool) (c : cell) : edge :=
  if b then low c else high c.

(* This is not used (yet?) *)
Lemma fc_lc_right_pt s ev events :
  close_alive_edges s events ->
  inside_box (point ev) ->
  all (fun x => lexPtEv  ev x) events ->
  {in s, forall c b, lexPt (point ev) (right_pt (any_edge b c))}.
Proof.
move=> /allP clae inbox_e /allP lexev c cin b.
have : ((any_edge b c) \in [:: bottom; top]) || end_edge (any_edge b c) events.
  by have := clae _ cin; rewrite /end_edge /any_edge; case: b=> /= /andP[].
move=> /orP[ | ].
  move: inbox_e => /andP[] _ /andP[]/andP[] _ botP /andP[] _ topP.
  by rewrite !inE => /orP[]/eqP ->; rewrite /lexPt ?botP ?topP.
by move=>/hasP[ev' ev'in /eqP ->]; apply: lexev.
Qed.

Lemma seq_low_high_shift s :
  s != nil ->  adjacent_cells s ->
  rcons [seq low i | i <- s] (high (last dummy_cell s)) =
  (low (head dummy_cell s) :: [seq high i | i <- s]).
Proof.
elim: s => [ // | c s +] _ /=.
  case: s => [// | c' s].
rewrite /=; move=> /(_ isT) Ih => /andP[] /eqP -> adj; congr (_ :: _).
by apply: Ih.
Qed.

Lemma cell_edges_high s :
  s != [::] -> adjacent_cells s ->
  cell_edges s =i low (head dummy_cell s) :: [seq high i | i <- s].
Proof.
move=> sn0 adj g; rewrite mem_cat; apply/idP/idP.
  move=>/orP[].
    by rewrite -(seq_low_high_shift sn0 adj) mem_rcons inE orbC => ->.
  by rewrite inE orbC => ->.
rewrite inE => /orP[/eqP -> | ].
  by rewrite map_f // head_in_not_nil.
by move=> ->; rewrite orbT.
Qed.

Lemma pvert_y_bottom p : inside_box p -> pvert_y p bottom < p_y p.
Proof.
have tmp : bottom \in [:: bottom; top] by rewrite inE eqxx.
move=> /[dup]/inside_box_valid_bottom_top=> /(_ _ tmp) val.
move=> /andP[] /andP[] + _ _.
by rewrite (under_pvert_y val) -ltNge.
Qed.

Lemma adjacent_right_form_sorted_le_y s p :
    seq_valid s p ->
    adjacent_cells s ->
    s_right_form s ->
    sorted <=%R [seq pvert_y p (high c) | c <- s].
Proof.
elim: s => [ // | a s Ih] /=.
move=> /andP[] _ vs /[dup]/adjacent_cons adj + /andP[] _ rfs.
case s_eq : s => [ // | b s'] /= /andP[]/eqP hl _.
rewrite hl.
have bin : b \in s by rewrite s_eq inE eqxx.
have rfb := (allP rfs b bin).
have := (allP vs b bin)=> /andP[] vl vh.
have := order_below_viz_vertical vl vh.
rewrite (pvertE vl) (pvertE vh) => /(_ _ _ erefl erefl rfb) /= => -> /=.
by move: Ih; rewrite s_eq; apply; rewrite -s_eq.
Qed.

Definition edge_side_prop (ev : event) (g : edge) :=
        if valid_edge g (point ev) then
          if pvert_y (point ev) g < p_y (point ev) then
             p_x (point ev) < p_x (right_pt g)
          else
             if p_y (point ev) < pvert_y (point ev) g then
             p_x (left_pt g) < p_x (point ev)
             else
           true
        else
          true.

Definition edge_side (evs : seq event) (open : seq cell) :=
  if evs is ev :: _ then
    all (edge_side_prop ev) [seq high c | c <- open]
  else true.

Definition extra_bot := Bcell nil nil bottom bottom.

Definition oc_disjoint (c1 c2 : cell) :=
  forall p, ~~ (inside_open' p c1 && inside_closed' p c2).

Definition disjoint_open_closed_cells :=
  forall c1 c2, oc_disjoint c1 c2.

Definition c_disjoint (c1 c2 : cell) :=
  forall p, ~~ (inside_closed' p c1 && inside_closed' p c2).

Lemma c_disjointC (c1 c2 : cell) :
  c_disjoint c1 c2 -> c_disjoint c2 c1.
Proof. by move=> cnd p; rewrite andbC; apply: cnd. Qed.

Definition c_disjoint_e (c1 c2 : cell) :=
  c1 = c2 \/ c_disjoint c1 c2.

Lemma c_disjoint_eC (c1 c2 : cell) :
  c_disjoint_e c1 c2 -> c_disjoint_e c2 c1.
Proof.
move=> cnd; have [/eqP -> | c1nc2] := boolP(c1 == c2).
  by left.
case: cnd => [/eqP | cnd ]; first by rewrite (negbTE c1nc2).
by right; apply: c_disjointC.
Qed.

Definition disjoint_closed_cells :=
  forall c1 c2, c_disjoint_e c1 c2.

Definition pt_at_end (p : pt) (e : edge) :=
  p === e -> p \in [:: left_pt e; right_pt e].

Definition connect_limits (s : seq cell) :=
  sorted [rel c1 c2 | right_limit c1 == left_limit c2] s.

Definition edge_covered_closed  (e : edge) (cs : seq cell) :=
  (exists pcc, pcc != [::] /\
    {subset pcc <= cs} /\
    {in pcc, forall c, high c = e} /\
    connect_limits pcc /\
    left_limit (head_cell pcc) = p_x (left_pt e) /\
    right_limit (last_cell pcc) = p_x (right_pt e)).

Definition edge_covered_open (e : edge) (os : seq cell) (cs : seq cell) :=
  (exists (opc : cell) (pcc : seq cell), {subset pcc <= cs} /\
    {in rcons pcc opc, forall c, high c = e} /\
    connect_limits (rcons pcc opc) /\
    opc \in os /\
    left_limit (head_cell (rcons pcc opc)) = p_x (left_pt e)) .

Definition edge_covered (e : edge) (os : seq cell) (cs : seq cell) :=
    edge_covered_open e os cs \/ edge_covered_closed e cs.

Lemma on_edge_covered_closed_right_limit p g cs :
  edge_covered_closed g cs ->
  p === g ->
  exists2 c, c \in cs & p_x p <= right_limit c.
Proof.
move=> [][| pcc0 pcc] [] // _ [] sub [] _ [] _ [] _ rl /andP[] _ /andP[] _ pl.
exists (last pcc0 pcc); first by apply/sub/mem_last.
by rewrite rl.
Qed.

Lemma connect_limits_rcons (s : seq cell) (lc : cell) :
  s != nil -> connect_limits (rcons s lc) =
   connect_limits s && (right_limit (last dummy_cell s) == left_limit lc).
Proof.
elim: s => [// | c0 s Ih] _ /=.
by rewrite rcons_path.
Qed.

Lemma left_limit_max c:
  open_cell_side_limit_ok c ->
  Num.max (p_x (left_pt (high c))) (p_x (left_pt (low c))) <= left_limit c.
Proof.
move=>/[dup] cok.
move=>/andP[] + /andP[] + /andP[] _ /andP[] /andP[] _ + /andP[] _ +.
rewrite -(open_cell_side_limit_ok_last cok) ge_max.
case: (left_pts c) => [ // | p tl] /=.
by move => _ /andP[] /eqP +  _ /andP[] + _ /andP[] + _ => <- -> ->.
Qed.

Lemma bottom_left_x c :
  open_cell_side_limit_ok c ->
  left_limit c = p_x (bottom_left_corner c).
Proof. by move=> cok; rewrite -(open_cell_side_limit_ok_last cok). Qed.

Lemma bottom_left_lex_to_high s p:
cells_bottom_top s ->
adjacent_cells s ->
s_right_form s ->
all open_cell_side_limit_ok s ->
inside_box p ->
bottom_left_cells_lex s p ->
{in s, forall c, lexPt (left_pt (high c)) p}.
Proof.
move=> cbtom adj rfo sok inboxp btm_left c cin.
have /mem_seq_split [s1 [s2 s12q]] := cin.
case s2q : s2 => [ | c' s2'].
   move: cbtom=> /andP[] /andP[] _ _; rewrite s12q s2q last_cat /=.
   move=> /eqP ctop.
   move: inboxp=> /andP[] _ /andP[] _ /andP[] + _.
   by rewrite /lexPt ctop=> ->.
have c'in : c' \in s.
  by rewrite s12q s2q !mem_cat !inE eqxx ?orbT.
move: adj; rewrite s12q s2q=> /adjacent_catW[] _ /= /andP[] /eqP cc' _.
have c'ok : open_cell_side_limit_ok c'.
  by apply: (allP sok c').
have lexbtme := btm_left c' c'in.
have btmon : bottom_left_corner c' === low c'.
  by move: c'ok=> /andP[] _ /andP[] _ /andP[] _ /andP[] _.
have := lexePt_lexPt_trans (on_edge_lexePt_left_pt btmon) lexbtme.
by rewrite cc'.
Qed.

Lemma inside_box_valid_bottom x : inside_box x -> valid_edge bottom x.
Proof.
move=> /andP[] _ /andP[] /andP[] /ltW + /ltW + _.
rewrite /valid_edge/generic_trajectories.valid_edge.
by move=> -> ->.
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

Lemma on_edge_inside_box (g : edge) p :
  inside_box (left_pt g) ->
  inside_box (right_pt g) ->
  p === g ->
  inside_box p.
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

Lemma inside_box_lt_min_right (p : pt) :
  inside_box p ->
  p_x p < Num.min (p_x (right_pt bottom)) (p_x (right_pt top)).
Proof.
move=> /andP[] _ /andP[] /andP[] _ + /andP[] _.
by case : (ltrP (p_x (right_pt bottom)) (p_x (right_pt top))).
Qed.

Lemma valid_open_limit (c : cell) p  :
  valid_edge (low c) p -> valid_edge (high c) p -> p_x p <= open_limit c.
Proof.
move=> /andP[] _ lp /andP[] _ hp; rewrite /open_limit.
by have [A | B] := lerP (p_x (right_pt (low c))) (p_x (right_pt (high c))).
Qed.

Lemma inside_box_non_inner (p : pt) :
  inside_box p -> non_inner bottom p /\ non_inner top p.
Proof.
move=> /andP[] /andP[] absbot abstop _; split.
  move=> /[dup] /andP[] _ vb; move: absbot; rewrite under_onVstrict // negb_or.
  by move=> /[swap] ->.
move=> /[dup] /andP[] _ vt; move: abstop; rewrite strict_nonAunder //.
by move=> /[swap] ->.
Qed.

Section open_cells_decomposition.

Variables open fc cc : seq cell.
Variable lcc : cell.
Variable lc : seq cell.
Variable p : pt.

Hypothesis cbtom : cells_bottom_top open.
Hypothesis adj : adjacent_cells open.
Hypothesis rfo : s_right_form open.
Hypothesis sval : seq_valid open p.
Hypothesis inbox_p : between_edges bottom top p.

Hypothesis ocd : open = fc ++ cc ++ lcc :: lc.
Hypothesis allnct : {in fc, forall c, ~~ contains_point p c}.
Hypothesis allct : {in cc, forall c, contains_point p c}.
Hypothesis lcc_ctn : contains_point p lcc.
Hypothesis head_nct : lc != [::] -> ~~ contains_point p (head lcc lc).
Hypothesis noc : {in cell_edges open &, no_crossing R}.

Let le := low (head lcc cc).
Let he := high lcc.

#[clearbody]
Let headin : head lcc cc \in open.
Proof.
by rewrite ocd; case: cc => [ | a cc'] /=; rewrite !(mem_cat, inE) eqxx ?orbT.
Defined.

#[clearbody]
Let vle : valid_edge le p.
Proof. by have /andP[] := (allP sval _ headin). Defined.

#[clearbody]
Let lccin : lcc \in open.
Proof. by rewrite ocd !(mem_cat, inE) eqxx !orbT. Defined.

#[clearbody]
Let lein : le \in cell_edges open.
Proof. by rewrite mem_cat /le map_f // headin. Defined.

#[clearbody]
Let hein : he \in cell_edges open.
Proof. by rewrite mem_cat /he map_f ?orbT // lccin. Defined.

#[clearbody]
Let vhe : valid_edge he p.
Proof. by have /andP[] := (allP sval _ lccin). Defined.

#[clearbody]
Let pal : p >>> le.
Proof.
elim/last_ind : {-1}(fc) (erefl fc) => [ | fc' c1 _] fc_eq.
  suff -> : le = bottom.
    by move: inbox_p=> /andP[].
  move: cbtom=> /andP[] /andP[] _ /eqP <- _; rewrite ocd fc_eq /le.
  by case: (cc).
have c1in : c1 \in open.
  by rewrite ocd fc_eq !(mem_cat, mem_rcons, inE) eqxx.
have /andP[vlc1 vhc1] : valid_edge (low c1) p && valid_edge (high c1) p.
  by apply: (allP sval).
have /order_edges_strict_viz_point : low c1 <| high c1 by apply: (allP rfo).
move=> /(_ _ vlc1 vhc1) oc1.
have ctfc : contains_point p (head lcc cc).
  case cc_eq : (cc) => [ // | c2 cc'].
  by apply: allct; rewrite /= cc_eq inE eqxx.
have hc1q : high c1 = low (head lcc cc).
  move: adj; rewrite ocd fc_eq -cats1 -!catA=> /adjacent_catW[] _ /=.
  by case: (cc) => [ | ? ?] /= /andP[] /eqP.
have palc1 : p >>= low c1.
  apply/negP=> /oc1 abs.
  by move: ctfc; rewrite contains_pointE -hc1q abs.
have nctc1 : ~~ contains_point p c1.
  by apply: allnct; rewrite fc_eq mem_rcons inE eqxx.
by move: nctc1; rewrite contains_pointE palc1 /= hc1q.
Defined.

#[clearbody]
Let puh : p <<< he.
Proof.
case lc_eq : lc => [ | c1 lc'].
  move: inbox_p => /andP[] _ +.
  by case/andP : cbtom=> _; rewrite ocd lc_eq !last_cat /= /he => /eqP ->.
have c1in : c1 \in open.
  by rewrite ocd lc_eq /= !(mem_cat, inE) eqxx !orbT.
have /andP[vlc1 vhc1] : valid_edge (low c1) p && valid_edge (high c1) p.
  by apply: (allP sval).
have /order_edges_viz_point := allP rfo _ c1in => /(_ _ vlc1 vhc1) oc1.
have hlcclc1 : high lcc = low c1.
  move: adj; rewrite ocd lc_eq=> /adjacent_catW[] _ /adjacent_catW[] _.
  by move=> /andP[] /eqP.
have pulc1 : p <<= low c1.
  by rewrite -hlcclc1; move: lcc_ctn => /andP[].
move: head_nct; rewrite lc_eq /= contains_pointE negb_and.
rewrite (oc1 pulc1) orbF negbK -hlcclc1.
by apply.
Defined.

Lemma fclc_not_contain c : (c \in fc) || (c \in lc) ->
  ~~ contains_point p c.
Proof.
move=> /orP[ | cl]; first by apply: allnct.
case lc_eq : lc => [ | c2 lc']; first by move: cl; rewrite lc_eq.
have adjlc : adjacent_cells (lcc :: lc).
  by move: adj; rewrite ocd => /adjacent_catW[] _ /adjacent_catW[].
have adjlc' : adjacent_cells (c2 :: lc').
  by move: adjlc; rewrite lc_eq=> /andP[] _.
have sval' : seq_valid (c2 :: lc') p.
  apply/allP=> x xin; apply: (allP sval); rewrite ocd !(mem_cat, inE).
  by rewrite lc_eq xin !orbT.
have lc2_eq : low c2 = he.
  by move: adjlc; rewrite lc_eq /= /he => /andP[] /eqP ->.
have rfolc : s_right_form (c2 :: lc').
  apply/allP=> x xin; apply: (allP rfo).
  by  rewrite ocd !mem_cat inE lc_eq xin ?orbT.
have pulc2 : p <<< low c2 by rewrite lc2_eq.
move: cl; rewrite lc_eq inE => /orP[/eqP -> | cinlc' ].
  by apply/negP; rewrite contains_pointE pulc2.
have pulc : p <<< low c.
  by apply: (strict_under_seq adjlc' sval' rfolc pulc2 cinlc').
by apply/negP; rewrite contains_pointE pulc.
Qed.

Lemma above_all_cells (s : seq cell) :
  seq_valid s p ->
  adjacent_cells s ->
  s_right_form s ->
  p >>> high (last dummy_cell s) ->
  p >>> low (head dummy_cell s) /\ {in s, forall c, p >>> high c}.
Proof.
elim: s => [ | c0 s Ih]; first by move=> _ _ _ ->.
move=> /= /andP[] /andP[] vl0 vh0 svals adjs /andP[] lbh rfos pah.
have pal0 : p >>> high c0 -> p >>> low c0.
  move=> {}pah.
  rewrite under_pvert_y // -ltNge.
  apply: (le_lt_trans (edge_below_pvert_y vl0 vh0 lbh)).
  by rewrite ltNge -under_pvert_y.
elim/last_ind : {-1}s (erefl s) svals adjs rfos pah => [ | s' c1 _]
  /= s_eq svals adjs rfos pah.
  split; last by move=> x; rewrite inE => /eqP ->.
  by apply: pal0.
have adjs1 : adjacent_cells (rcons s' c1) by apply: (path_sorted adjs).
rewrite last_rcons in pah.
rewrite s_eq last_rcons in Ih; have := Ih svals adjs1 rfos pah.
move=> [] palh {}Ih.
have hc0q : high c0 = low (head dummy_cell (rcons s' c1)).
  by move: adjs; case: (s') => [ | ? ?] /= /andP[] /eqP.
split; first by apply pal0; rewrite hc0q.
move=> x; rewrite inE=> /orP[ /eqP -> |]; last by apply: Ih.
by rewrite hc0q.
Qed.

Lemma below_all_cells (s : seq cell) :
  seq_valid s p ->
  adjacent_cells s ->
  s_right_form s ->
  p <<< low (head dummy_cell s) -> {in s, forall c, p <<< high c}.
Proof.
elim: s => [ | c0 s Ih]; first by [].
move=> /= /andP[] /andP[] vl0 vh0 svals adjs /andP[] lbh rfos pah.
have puh0 : p <<< low c0 -> p <<< high c0.
  move=> {}pul.
  rewrite strict_under_pvert_y //.
  apply: (lt_le_trans _ (edge_below_pvert_y vl0 vh0 lbh)).
  by rewrite -strict_under_pvert_y.
have adjs1 : adjacent_cells s by apply: (path_sorted adjs).
move=> x; rewrite inE => /orP[/eqP -> | ]; first by apply: puh0.
case s_eq: s => [ // | c1 s'].
have h0lc1 : high c0 = low c1 by move: adjs; rewrite s_eq /= => /andP[] /eqP.
by rewrite -s_eq; apply: (Ih) => //; rewrite s_eq /= -h0lc1 (puh0 pah).
Qed.

Lemma connect_properties :
  [/\ p >>> le, p <<< he, valid_edge le p, valid_edge he p &
    forall c, (c \in fc) || (c \in lc) -> ~~contains_point p c].
Proof. by split; last exact fclc_not_contain. Qed.

Lemma fclc_not_end_aux c e :
  point e = p ->
  (c \in fc) || (c \in lc) ->
  (~ event_close_edge (low c) e) /\ (~ event_close_edge (high c) e).
Proof.
move=> pq /[dup] cin /fclc_not_contain/negP.
have cino : c \in open.
  by rewrite ocd !(mem_cat, inE); move:cin=> /orP[] ->; rewrite ?orbT.
rewrite -pq=>/contrapositive_close_imp_cont; apply.
  by apply: (allP rfo).
by rewrite pq; apply/andP/(allP sval).
Qed.

Lemma low_under_high : le <| he.
Proof.
have [// | abs_he_under_le] := noc lein hein; case/negP: pal.
by have /underW := (order_edges_strict_viz_point vhe vle abs_he_under_le puh).
Qed.

Lemma in_cc_on_high c : c \in cc -> p === high c.
Proof.
move=> cin.
have cino : c \in open by rewrite ocd !mem_cat cin !orbT.
have vhc : valid_edge (high c) p by apply/(seq_valid_high sval)/map_f.
apply: under_above_on => //; first by apply: (proj2 (andP (allct cin))).
have [s1 [[ | c2 s2] cceq]] := mem_seq_split cin.
  move: adj; rewrite ocd cceq -catA /= => /adjacent_catW[] _ /adjacent_catW[].
  move=> _ /= /andP[] /eqP -> _.
  by move: lcc_ctn=> /andP[].
have c2in : c2 \in cc by rewrite cceq !(mem_cat, inE) eqxx !orbT.
move: adj; rewrite ocd cceq -!catA; do 2 move => /adjacent_catW[] _.
rewrite /= => /andP[] /eqP -> _.
by apply: (proj1 (andP (allct c2in))).
Qed.

End open_cells_decomposition.

Lemma inside_open_cell_valid c p1 :
  open_cell_side_limit_ok c ->
  inside_open_cell p1 c ->
  valid_edge (low c) p1 && valid_edge (high c) p1.
Proof.
move=> /[dup] + /open_cell_side_limit_ok_last lastq.
move=> /andP[] ne /andP[] sxl /andP[] _ /andP[] /andP[] _ onh /andP[] _ onl.
move=> /andP[] _; rewrite /left_limit /open_limit=> /andP[] ge lemin.
apply/andP; split.
  apply/andP; split.
    apply: le_trans ge.
    by move: onl=> /andP[]; rewrite lastq.
  apply: (le_trans lemin).
  by rewrite ge_min lexx.
apply/andP; split.
 apply: le_trans ge; move: onh=> /andP[].
 rewrite (eqP (allP sxl (head dummy_pt (left_pts c))_)) //.
 by apply: head_in_not_nil.
by rewrite le_min in lemin; move: lemin=>/andP[].
Qed.

Lemma midpoint_swap a b c d :
  midpoint (midpoint a b) (midpoint c d) =
  midpoint (midpoint a d) (midpoint c b).
Proof.
rewrite /midpoint.
apply/eqP; rewrite pt_eqE /= !mulrDl !addrA.
rewrite !(addrAC _ (p_x d / (1 + 1) / (1 + 1))).
rewrite !(addrAC _ (p_x b / (1 + 1) / (1 + 1))).
rewrite !(addrAC _ (p_y d / (1 + 1) / (1 + 1))).
rewrite !(addrAC _ (p_y b / (1 + 1) / (1 + 1))).
by rewrite !eqxx.
Qed.

Lemma two_halves (x : R) : (x + x) / 2 = x.
Proof.
have twon0 : 2 != 0 :> R by rewrite pnatr_eq0.
by apply: (mulIf twon0); rewrite mulfVK // mulrDr mulr1.
Qed.

Lemma cell_center_inside_main c rl :
  inter_at_ext (low c) (high c) -> low c != high c -> low c <| high c ->
  open_cell_side_limit_ok c ->
  left_limit c < rl ->
  rl <= p_x (right_pt (low c)) ->
  rl <= p_x (right_pt (high c)) ->
  right_pts c != [::] ->
  all (fun y => y == rl) [seq p_x p | p <- right_pts c] ->
  head dummy_pt (right_pts c) === high c ->
  last dummy_pt (right_pts c) === low c ->
  strict_inside_closed (cell_center c) c.
move=> noc dif cwf cok llrl rll rlh rsn0 rsok hon lon.
rewrite /strict_inside_closed.
have twogt0: (0 : R) < 1 + 1 by apply: Num.Theory.addr_gt0.
have [xrh xrl] : p_x (head dummy_pt (right_pts c)) = rl /\
          p_x (last dummy_pt (right_pts c)) = rl.
  case: right_pts rsn0 rsok => [ | a tl] // _ /[dup] allx /andP[] /eqP -> _.
  by move: (allP allx _ (map_f _ (mem_last _ _))) => /eqP ->.
have [xlh xll] :
    p_x (head dummy_pt (left_pts c)) = left_limit c/\
          p_x (last dummy_pt (left_pts c)) = left_limit c.
  move: cok=> /andP[] + /andP[] + _.
  case: (left_pts c) => [ | a [ | b tl]] //= _ /andP[] /eqP /[dup] eqa -> //.
  rewrite -[_ && _]/(all (fun p => p_x p == left_limit c) (b :: tl)).
  move=> /allP /(_ (last b tl) _) /eqP -> //.
  by rewrite mem_last.
have xcond :
  left_limit c < p_x (cell_center c) < right_limit c.
  rewrite /cell_center/midpoint.
  rewrite xrl xrh xll xlh /=.
  (* rewrite -[left_limit c](open_cell_side_limit_ok_last cok).
  rewrite -[p_x (last _ _)]/(left_limit _). *)
  rewrite -mulrDr.
  set one := (X in _ < _ * X / _ < _).
  have one1 : one = 1.
    rewrite /one -(mulr1 (_ ^-1)) -mulrDr mulVf //.
    by move: twogt0; rewrite lt0r=> /andP[].
  rewrite one1 mulr1.
  rewrite /right_limit xrh.
  by apply: half_between_lt.
rewrite xcond andbT.
have [ab bel] : cell_center c >>> low c /\
          cell_center c <<< high c.
  rewrite /cell_center midpoint_swap.
  have midl : midpoint (last dummy_pt (left_pts c))
               (last dummy_pt (right_pts c)) === low c.
    apply: midpoint_on_edge; last by [].
    by move: cok=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ ->.
  have midh : midpoint (head dummy_pt (left_pts c))
               (head dummy_pt (right_pts c)) === high c.
    apply: midpoint_on_edge; last by [].
    by move: cok=> /andP[] _ /andP[] _ /andP[] _ /andP[] ->.
  set ml := (X in midpoint X _).
  set mh := (X in midpoint _ X).
  have [_ vh] := andP midh.
  have [_ vl] := andP midl.
  have same_x : p_x ml = p_x mh.
    by rewrite /ml /mh /midpoint /= xrh xrl xlh xll.
  have vlh : valid_edge (high c) ml.
    by have := same_x_valid (high c) same_x => ->.
  have mlab : ml >>= low c by rewrite strict_nonAunder // negb_and negbK midl.
  have mll : ml <<= low c.
    by rewrite under_onVstrict // midl.
  have mldifl :  left_limit c < p_x ml < rl.
    rewrite /ml/midpoint/= xrl xll.
    by apply: (half_between_lt llrl).
  have nl : p_x (left_pt (low c)) < p_x ml.
    apply: (le_lt_trans  _ (proj1 (andP mldifl))).
    apply: (le_trans _ (left_limit_max cok)).
    by rewrite le_max le_refl orbT.
  have nr : p_x ml < p_x (right_pt (low c)).
    by apply: (lt_le_trans (proj2 (andP mldifl))).
  have mlu : ml <<< high c.
    rewrite strict_nonAunder //; last first.
    have := order_edges_viz_point vl vlh cwf mll => ->; rewrite andbT.
    apply/negP=> mlh.
    move: noc; rewrite /inter_at_ext=> -[abs | ].
      by rewrite abs eqxx in dif.
    move=> /(_ ml midl mlh); rewrite !inE=> /orP[] /eqP abs.
      by rewrite abs lt_irreflexive in nl.
    by rewrite abs lt_irreflexive in nr.
  have := (half_between_edges vl vlh mlab mlu); rewrite -/ml.
  rewrite /midpoint same_x two_halves.
  have := on_pvert midl; rewrite -/ml => ->.
  have := same_pvert_y vh (esym same_x); rewrite -/mh => <-.
  by have := on_pvert midh; rewrite -/mh => ->.
by rewrite ab bel.
Qed.

Lemma close_cell_ok c p :
  contains_point p c ->
  valid_edge (low c) p -> valid_edge (high c) p ->
  open_cell_side_limit_ok c ->
  closed_cell_side_limit_ok (close_cell p c).
Proof.
move=> ctp vl vh.
rewrite /open_cell_side_limit_ok/closed_cell_side_limit_ok.
rewrite /close_cell /=; have /exists_point_valid [p1 /[dup] vip1 ->] := vl.
have /exists_point_valid [p2 /[dup] vip2 -> /=] := vh.
move=> /andP[] -> /andP[]-> /andP[]-> /andP[] -> -> /=.
have [o1 /esym/eqP x1]:=intersection_on_edge vip1.
have [o2 /eqP x2]:=intersection_on_edge vip2.
rewrite -?(eq_sym p).
(* TODO : this line performs a lot of complicated things, but they mostly
   failed at porting time. *)
case:ifP (o1) (o2) =>[/eqP q1 |enp1];case:ifP=>[/eqP q2 |enp2];
  rewrite ?q1 ?q2;
  rewrite -?q1 -?q2 /= ?eqxx ?x2 ?x1 /= => -> -> //=; rewrite ?andbT.
- move: x1 x2 ctp=> /eqP/esym x1 /eqP x2 /andP[] el _.
  have := (above_edge_strict_higher_y x1 (negbT enp2) el).
  by apply.
- move: x1 x2 ctp=> /eqP/esym x1 /eqP x2 /andP[] _ eh.
  have := (under_edge_strict_lower_y x2 (negbT enp1) eh o2).
  by [].
move: x1 x2 ctp=> /eqP/esym x1 /eqP x2 /andP[] el eh.
rewrite (above_edge_strict_higher_y x1 _ el) //; last first.
  exact: negbT.
rewrite  (under_edge_strict_lower_y x2 (negbT enp1) eh) //.
by rewrite !andbT /right_limit /= -x1 -x2 eqxx.
Qed.

Lemma cell_center_close_cell_inside c p :
  inter_at_ext (low c) (high c) -> low c != high c -> low c <| high c ->
  open_cell_side_limit_ok c ->
  valid_edge (low c) p -> valid_edge (high c) p ->
  left_limit c < p_x p ->
  strict_inside_closed (cell_center (close_cell p c)) (close_cell p c).
Proof.
move=> noc dif cwf cok vlc vhc xdif.
have lccq : low (close_cell p c) = low c.
  by have [] := close_cell_preserve_3sides p c.
have hccq : high (close_cell p c) = high c.
  by have [] := close_cell_preserve_3sides p c.
have llccq : left_pts (close_cell p c) = left_pts c.
  by have [] := close_cell_preserve_3sides p c.
have ccok : open_cell_side_limit_ok (close_cell p c).
  move: cok; rewrite /open_cell_side_limit_ok /left_limit !(lccq, hccq, llccq).
  by [].
have llltrl : left_limit (close_cell p c) < p_x (right_pt (low c)).
  move: xdif; rewrite /left_limit llccq=> xdif'.
  by apply: (lt_le_trans xdif' (proj2 (andP vlc))).
have llltx : left_limit (close_cell p c) < p_x p.
  by move: xdif; rewrite /left_limit llccq.
have plerl : p_x p <= p_x (right_pt (low c)).
  by apply: (proj2 (andP vlc)).
have plerh : p_x p <= p_x (right_pt (high c)).
  by apply: (proj2 (andP vhc)).
have rpn0 : right_pts (close_cell p c) != [::].
  rewrite /close_cell (pvertE vlc) (pvertE vhc) /=.
  by do 2 (case: ifP => _).
have allx : all (fun y => y == (p_x p))
    [seq p_x w | w <- right_pts (close_cell p c)].
  rewrite /close_cell (pvertE vlc) (pvertE vhc) /=.
  by case: ifP => cmp1; case: ifP=> cmp2 /=; rewrite ?eqxx.
have hon : head dummy_pt (right_pts (close_cell p c)) === high c.
  rewrite /close_cell (pvertE vlc) (pvertE vhc) /=.
  have := pvert_on vhc.
  by case: ifP => [/eqP <- | pnh]; case: ifP=> [/eqP <- | pnl].
have lon : last dummy_pt (right_pts (close_cell p c)) === low c.
  rewrite /close_cell (pvertE vlc) (pvertE vhc) /=.
  have := pvert_on vlc.
  by case: ifP => [/eqP pish | pnh]; case: ifP => [/eqP pisl | pnl].
apply: (cell_center_inside_main _ _ _ _ llltx);
  (rewrite ?(lccq, hccq, llccq)); move=> //.
Qed.

Lemma strict_inside_closedW c p :
 strict_inside_closed p c -> inside_closed' p c.
Proof.
move=> /andP[] /andP[] cu ca /andP[] lb rb.
by rewrite inside_closed'E (underW cu) ca lb (ltW rb).
Qed.

Lemma update_closed_cell_center c p :
  (1 < size (right_pts c))%N ->
  cell_center (update_closed_cell c p) = cell_center c.
Proof.
rewrite /cell_center/update_closed_cell.
by case: right_pts => [ | a [ | b tl]].
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

Lemma update_closed_cell_add c p :
  p \in right_pts (update_closed_cell c p).
Proof. by rewrite /update_closed_cell /= !inE eqxx orbT. Qed.

Lemma update_closed_cell_edges c p :
  low (update_closed_cell c p) = low c /\
  high (update_closed_cell c p) = high c.
Proof. by case: c. Qed.

Lemma update_closed_cell_sides c p :
  closed_cell_side_limit_ok c -> (1 < size (right_pts c))%N ->
  left_limit (update_closed_cell c p) = left_limit c /\
  right_limit (update_closed_cell c p) = right_limit c.
Proof.
move=> /andP[] sl; do 4 (move=> /andP[] _); move=> _; move: sl.
rewrite/left_limit/right_limit/update_closed_cell.
by case: left_pts => [ | a tl] //; case: right_pts => [ | b [ | d tl']] //=.
Qed.

(* Thanks to the disoc lemma, we only need to prove that the high edges
  of all open cells satisfy the pairwise property for edge_below to
  obtain disjointness of cells. *)

Lemma disoc_i i j s : (i < j < size s)%N ->
  adjacent_cells s ->
  pairwise edge_below [seq high c | c <- s] ->
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
apply: (order_edges_viz_point vhx) => //.
rewrite -lyq.
move: pws => /(pairwiseP dummy_edge) /(_ i j') /=; rewrite size_map 2!inE.
move=> /(_ ilts j'lts iltj').
by rewrite -[dummy_edge]/(high dummy_cell) !(nth_map dummy_cell).
Qed.

Lemma disoc s:
  adjacent_cells s ->
  pairwise edge_below [seq high c | c <- s] ->
  all open_cell_side_limit_ok s ->
 {in s &, disjoint_open_cells}.
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

Lemma in_safe_side_right_top_right c p:
  closed_cell_side_limit_ok c ->
  in_safe_side_right p c -> lexPt p (head dummy_pt (right_pts c)).
Proof.
move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] _.
move=> /andP[] sr /andP[] /allP sx /andP[] _ /andP[] hdon _.
move=> /andP[] /eqP px /andP[] puh _.
have xhd : p_x (head dummy_pt (right_pts c)) = right_limit c.
  apply/eqP/sx.
  by move: sr; case: (right_pts c) => [ | ? ?] //=; rewrite inE eqxx.
rewrite /lexPt xhd px eqxx ltxx /=.
have vh : valid_edge (high c) (head dummy_pt (right_pts c)).
  by move: hdon=> /andP[].
have vp : valid_edge (high c) p.
  by rewrite -(same_x_valid (high c) (eq_trans xhd (esym px))).
by have := strict_under_edge_lower_y (eq_trans px (esym xhd)) hdon => <-.
Qed.

Lemma in_safe_side_top_right c p :
  closed_cell_side_limit_ok c ->
  left_limit c < right_limit c ->
  in_safe_side_left p c || in_safe_side_right p c ->
  lexPt p (head dummy_pt (right_pts c)).
Proof.
move=> cok clarge /orP[pleft | pright]; last first.
  by apply: in_safe_side_right_top_right.
rewrite /lexPt.
move: pleft=> /andP[] /eqP -> _.
move: cok; do 5 (move=> /andP[] _); move=> /andP[] + /andP[] + _.
case: right_pts => [ | a tl] //= _ /andP[] /eqP -> _.
by rewrite clarge.
Qed.

Lemma in_safe_side_close_cell_diff q c p :
  valid_edge (low c) q ->
  valid_edge (high c) q ->
  left_limit c < p_x q ->
  in_safe_side_left p
    (close_cell q c) ||
  in_safe_side_right p (close_cell q c) ->
  p != q.
Proof.
move=> vl vh ltx.
move=> /orP[/andP[] /eqP pxq _ | ].
  rewrite pt_eqE pxq negb_and /left_limit.
  have [_ _ ->] := close_cell_preserve_3sides q c.
  by move: ltx; rewrite /left_limit lt_neqAle=> /andP[] -> _.
move=> /andP[] _ /andP[] _ /andP[] _.
rewrite /close_cell /=.
rewrite (pvertE vl) (pvertE vh).
by case: ifP=> [ /eqP A| _]; case: ifP => [/eqP/esym B| _]; rewrite ?A; rewrite ?B;
  rewrite !inE ?negb_or // => /andP[] // _ /andP[].
Qed.

Lemma  in_safe_side_left_close_cell p q c:
  in_safe_side_left p (close_cell q c) =
        in_safe_side_left p c.
  rewrite /in_safe_side_left.
  have [-> -> ->] := close_cell_preserve_3sides q c.
  by rewrite left_limit_close_cell.
Qed.

Lemma in_safe_side_left_contains c p :
  in_safe_side_left p c -> contains_point p c.
Proof.
by rewrite /contains_point=> /andP[] _ /andP[] /underW -> /andP[] /underWC ->.
Qed.


Notation bare_closed_cell_side_limit_ok :=
 (bare_closed_cell_side_limit_ok (Num.RealField.sort R) eq_op <=%R +%R
   (fun x y => x - y) *%R 1 edge left_pt right_pt).

Lemma unbare_closed_cell_ok c :
  bare_closed_cell_side_limit_ok c ->
  closed_cell_side_limit_ok c.
Proof.
move=> bc.
have lcn0 : left_pts c != [::].
  by move:bc=> /andP[]; rewrite size_eq0.
have rcn0 : right_pts c != [::].
  by move: bc; do 5 (move=> /andP[] _); move=> /andP[]; rewrite size_eq0.
have lxs : all (fun p => p_x p == left_limit c) (left_pts c).
  by move: bc=> /andP[] _ /andP[].
have rxs : all (fun p => p_x p == right_limit c) (right_pts c).
  by move: bc; do 5 (move => /andP[] _); move=> /andP[] _ /andP[].
have same_rel : (fun x y => R_ltb R eq_op <=%R y x) =2 (>%R : R -> R -> bool).
  by move=> x y; rewrite R_ltb_lt.
have sl : sorted >%R [seq p_y p | p <- left_pts c].
  move: bc=> /andP[] _ /andP[] _ /andP[] + _.
  by rewrite (eq_sorted same_rel).
have sr : sorted >%R [seq p_y p | p <- right_pts c].
    move: bc; do 5 (move=> /andP[] _); move=> /andP[] _ /andP[] _ /andP[] + _.
    by rewrite (eq_sorted same_rel).
have blon : last dummy_pt (left_pts c) === low c.
  move: bc=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ /andP[] it _.
  by rewrite addrN in it.
have bron : last dummy_pt (right_pts c) === low c.
  move: bc; do 5 (move=> /andP[] _). 
  move=> /andP[] _ /andP[] _ /andP[] _ /andP[] _ it.
  by rewrite addrN in it.
have hlon : head dummy_pt (left_pts c) === high c.
  move: bc=> /andP[] _ /andP[] _ /andP[] _ /andP[] it _.
  by rewrite addrN in it.
have hron : head dummy_pt (right_pts c) === high c.
  move: bc; do 5 (move=> /andP[] _). 
  move=> /andP[] _ /andP[] _ /andP[] _ /andP[] it _.
  by rewrite addrN in it.
rewrite /closed_cell_side_limit_ok.
by rewrite lcn0 rcn0 lxs rxs sl sr blon hlon bron hron.
Qed.

Lemma check_bounding_box_to_closed_cell :
  let cc := (complete_last_open (start_open_cell bottom top)) in
  check_bounding_box bottom top ->
  (bottom <| top) &&
  (left_limit cc < right_limit cc) &&
  closed_cell_side_limit_ok cc.
Proof.
move=> cc /andP[] /andP[] /andP[] boxwf.
rewrite R_ltb_lt => lr.
move=> /unbare_closed_cell_ok cok extra.
by rewrite boxwf lr cok.
Qed.

End proof_environment.


End working_environment.
