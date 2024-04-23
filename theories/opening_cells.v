From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements
  generic_trajectories points_and_edges events cells.

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
Notation point := (point R edge).
Notation outgoing := (outgoing R edge).

Notation cell := (cell R edge).
Notation low := (low R edge).
Notation high := (high R edge).
Notation left_pts := (left_pts R edge).
Notation right_pts := (right_pts R edge).

Notation dummy_pt := (dummy_pt R 1).
Notation dummy_edge := (dummy_edge R).
Notation dummy_cell := (dummy_cell R 1 edge (@unsafe_Bedge R)).

(*
Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e high_e : edge) 
  : seq cell * cell :=
  match out with
  | [::] =>
      let op0 := vertical_intersection_point p low_e in
      let op1 := vertical_intersection_point p high_e in
      match (op0,op1) with
      |(None,_) |(_,None)=> ([::], dummy_cell)
      |(Some(p0),Some(p1)) =>
        ([::] , Bcell  (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e)
      end
  | c::q =>
    let op0 := vertical_intersection_point p low_e in
    let (s, nc) := opening_cells_aux p q c high_e in
    match op0 with
    | None => ([::], dummy_cell)
    | Some(p0) =>
      (Bcell  (no_dup_seq([:: p; p0])) [::] low_e c :: s, nc)
  end
end.
*)

Definition opening_cells_aux :=
  opening_cells_aux R eq_op le +%R (fun x y => x - y) *%R (fun x y => x / y)
  1 edge (@unsafe_Bedge R) (@left_pt R) (@right_pt R).

Lemma opening_cells_aux_eqn p out low_e high_e :
  opening_cells_aux p out low_e high_e =
  match out with
  | [::] =>
      let op0 := vertical_intersection_point p low_e in
      let op1 := vertical_intersection_point p high_e in
      match (op0,op1) with
      |(None,_) |(_,None)=> ([::], dummy_cell)
      |(Some(p0),Some(p1)) =>
        ([::] , Bcell _ _ (no_dup_seq ([:: p1; p; p0])) [::] low_e high_e)
      end
  | c::q =>
    let op0 := vertical_intersection_point p low_e in
    let (s, nc) := opening_cells_aux p q c high_e in
    match op0 with
    | None => ([::], dummy_cell)
    | Some(p0) =>
      (Bcell _ _ (no_dup_seq([:: p; p0] : seq pt)) [::] low_e c :: s, nc)
  end
end.
Proof.  by case: out. Qed.

Definition opening_cells (p : pt) (out : seq edge) (l h : edge) : seq cell :=
   let (s, c) := opening_cells_aux p (sort (@edge_below R) out) l h in
   rcons s c.

Section proof_environment.
Variables bottom top : edge.

Notation extra_bot := (extra_bot bottom).
Notation close_alive_edges := (close_alive_edges bottom top).
Notation cells_bottom_top := (cells_bottom_top bottom top).
Notation inside_box := (inside_box bottom top).
Notation open_cell_side_limit_ok := (@open_cell_side_limit_ok R).
Notation seq_low_high_shift := (@seq_low_high_shift R).
Notation cover_left_of := (@cover_left_of _ bottom top).

Section opening_cells.

Lemma opening_cells_left p out le he :
  {in out, forall g, left_pt g == p} ->
  valid_edge le p ->
  valid_edge he p ->
  {in opening_cells p out le he, forall c, left_limit c = p_x p}.
Proof.
move=> outl vle vhe; rewrite /opening_cells.
rewrite /opening_cells_aux.
have : forall g, g \in sort (@edge_below _) out -> left_pt g == p.
  by move=> g; rewrite mem_sort; apply: outl.
elim: (sort _ _) le vle => [ | g1 gs Ih] le vle {}outl c /=.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite /= pvertE // pvertE //=.
  by case: ifP=> _; case: ifP=> _; rewrite inE /left_limit => /eqP ->.
have outl' : forall g, g \in gs -> left_pt g == p.
  by move=> g gin; apply outl; rewrite inE gin orbT.
rewrite /=.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (outl g1 _)) ?valid_edge_left // inE eqxx.
move: Ih; case oca_eq : (generic_trajectories.opening_cells_aux _ _ _ _) => [s c'] /(_ _ vg1 outl').
rewrite oca_eq => Ih.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE //=.
rewrite inE => /orP[/eqP -> | ]; first by rewrite /left_limit; case : ifP.
by apply: Ih.
Qed.

Lemma opening_cells_low_diff_high p out le he :
  {in out, forall g, left_pt g == p} ->
  uniq out ->
  valid_edge le p ->
  valid_edge he p ->
  p >>> le ->
  p <<< he ->
  {in opening_cells p out le he, forall g, low g != high g}.
Proof.
move=> outl u vle vhe pal puh; rewrite /opening_cells.
have {outl} : {in sort (@edge_below _) out, forall g, left_pt g == p}.
  by move=> g; rewrite mem_sort; apply: outl.
have {u} : uniq (sort (@edge_below _) out) by rewrite sort_uniq.
move=> u outl.
have : le != head he (sort (@edge_below _) out).
  case: (sort _ _) outl => [ | g1 gs] /=.  
    move=> _; apply/eqP=> abs; move: puh; rewrite -abs strict_nonAunder// andbC.
    by rewrite (negbTE pal).
  move=> /(_ g1 (mem_head _ _)) /eqP lg1q; apply/eqP=> abs.
  by move: pal; rewrite abs under_onVstrict -lg1q ?valid_edge_left ?left_on_edge.
elim: (sort _ _) le vle {pal} u outl => [ | g1 gs Ih] le /= vle + + ledif.
  rewrite /= => _ _.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite (pvertE vle) (pvertE vhe).
  by case: ifP=> _; case: ifP=> _ /= g; rewrite inE=> /eqP -> /=.
move=> /andP[] gnin u outl.
have /eqP lg1q : left_pt g1 == p by apply: outl; rewrite inE eqxx.
have {}outl : {in gs, forall g, left_pt g == p}.
  by move=> g gin; apply: outl; rewrite inE gin ?orbT.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite (pvertE vle).
have vg1 : valid_edge g1 p by rewrite -lg1q valid_edge_left.
have g1nhe : g1 != he.
  apply/eqP=> abs.
  by move: puh; rewrite -abs strict_nonAunder // -lg1q ?left_on_edge.
have g1dif : g1 != head he gs.
  apply/eqP=> abs; move: gnin.
  have : head he gs \in he :: gs.
    by case: (gs) => [ | ? ?]; rewrite /= !inE !eqxx ?orbT.
  rewrite -abs inE=> /orP[/eqP {}abs _ | ->]; last by [].
  by rewrite abs eqxx in g1nhe.
have := Ih g1 vg1 u outl g1dif; rewrite oca_eq=> {}Ih.
move=> g; rewrite /= inE=> /orP [/eqP -> /= | ]; first by [].
apply: Ih.
Qed.

Lemma opening_cells_seq_edge_shift p s c oe le he :
  {in oe, forall g, left_pt g == p} ->
  valid_edge le p -> valid_edge he p ->
  opening_cells_aux p oe le he = (s, c) ->
  le :: [seq high i | i <- rcons s c] =
  rcons [seq low i | i <- rcons s c] he.
Proof.
move=> + + vh.
elim: oe le s c => [ | g1 oe Ih] le s c leftg vl /=.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE // => -[] <- <- /=.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (leftg g1 _)) ?valid_edge_left // inE eqxx.
have leftg' : {in oe, forall g, left_pt g == p}.
  by move=> g gin; apply: leftg; rewrite inE gin orbT.
have := Ih _ _ _ leftg' vg1; case: (opening_cells_aux _ _ _ _)=> [s' c'].
move=> /(_ s' c' erefl) {}Ih.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
by rewrite pvertE // => -  [] <- <- /=; congr (_ :: _).
Qed.

Lemma opening_cells_aux_subset c' s' c p s le he:
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he = (s', c') ->
  c \in rcons s' c' ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> + vhe.
elim: s c' s' le => [ | g1 s Ih] c' s' le /= vle lsp.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite pvertE // pvertE // => - [] <- <-.
  by do 2 (case: ifP=> _); rewrite /= inE=> /eqP -> /=; rewrite !inE !eqxx.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; rewrite lsp // inE gin orbT.
have := Ih _ _ _ vg1 lsp'; case: (opening_cells_aux _ _ _ _)=> [s1 c1].
move=> /(_ _ _ erefl) {} Ih.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE // => - [] <- <- /=; rewrite inE=> /orP[/eqP -> /= | ].
  by rewrite !inE ?eqxx ?orbT.
rewrite inE; move=>/Ih/andP[] ->; rewrite orbT andTb.
by rewrite !inE orbCA => ->; rewrite orbT.
Qed.


(*TODO : check all uses of opening_cells_aux_subset for potential uses
  of this simpler lemma. *)
Lemma opening_cells_subset c p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  c \in opening_cells p s le he ->
  (low c \in le :: s) && (high c \in he :: s).
Proof.
move=> vle vhe lsp.
rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co] cin.
have lsp' : {in sort (@edge_below _) s, forall g, left_pt g == p}.
  by move=> g; rewrite mem_sort; apply: lsp.
have := opening_cells_aux_subset vle vhe lsp' oca_eq cin.
by rewrite !inE !mem_sort.
Qed.

(*
Lemma opening_cells_aux_nnil p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he != nil.
Proof.
by move=> + vhe; case: s => [ | g1 s] vle lsp; rewrite /= pvertE // ?pvertE.
Qed.
*)

Lemma opening_cells_aux_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- (opening_cells_aux p s le he).1] = s.
Proof.
move=> vle vhe lsp.
elim: s le vle lsp => [ | g1 s Ih] le vle lsp.
  rewrite /= -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite /= pvertE // pvertE.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; apply: lsp; rewrite inE gin orbT.
rewrite /= -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE //.
by have := Ih _ vg1 lsp'; case: (opening_cells_aux _ _ _ _) => [s' c'] /= ->.
Qed.

Lemma opening_cells_aux_high_last p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  high (opening_cells_aux p s le he ).2 = he.
Proof.
move=> + vhe; elim: s le => [ /= | g1 s Ih] le vle lsp.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (lsp g1 _)) ?valid_edge_left // inE eqxx.
have lsp' : {in s, forall g, left_pt g == p}.
  by move=> g gin; apply: lsp; rewrite inE gin orbT.
have := Ih _ vg1 lsp'.
rewrite /= -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE //.
by case : (opening_cells_aux _ _ _ _) => [s' c'].
Qed.

Lemma opening_cells_high p s le he :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  [seq high i | i <- opening_cells p s le he] =
  rcons (sort (@edge_below R) s) he.
Proof.
move=> vle vhe lsp; rewrite /opening_cells.
have lsp' :
   {in sort (@edge_below _) s, forall g, left_pt g == p}.
  move=> g; rewrite mem_sort; apply: lsp.
move: (lsp') => /opening_cells_aux_high => /(_ _ _ vle vhe).
move: lsp' => /opening_cells_aux_high_last => /(_ _ _ vle vhe).
case: (opening_cells_aux _ _ _ _) => [s' c'] /=.
by rewrite map_rcons => -> ->.
Qed.

Lemma opening_cells_aux_right_form (ctxt s : seq edge) (p : pt) le he
 s' c' :
p >>= le -> p <<< he -> valid_edge le p -> valid_edge he p ->
le \in ctxt -> he \in ctxt ->
le <| he -> {in s, forall g, left_pt g == p} ->
{in ctxt &, (@no_crossing R)} ->
{subset s <= ctxt} ->
path (@edge_below R) le s  ->
opening_cells_aux p s le he = (s', c') ->
s_right_form (rcons s' c').
Proof.
move=> + ph + vh + hin + + noc + +.
elim: s le s' c' => [ | g1 edges IH] le s' c'
  pabove vle lin lowhigh outs allin sorted_e /=.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE // => -[] <- <- /=; rewrite andbT.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE //.
have outs' : {in edges, forall g, left_pt g == p}.
  by move=> g gin; apply outs; rewrite inE gin orbT.
have allin' : {subset edges <= ctxt}.
  by move=> g gin; rewrite allin // inE gin orbT.
have sorted_e' : path (@edge_below R) g1 edges.
   by apply: (path_sorted sorted_e).
have /eqP gl : left_pt g1 == p by rewrite outs // inE eqxx.
have g1belowhigh : g1 <| he.
  have gin' : g1 \in ctxt by rewrite allin // inE eqxx.
  have/no_crossingE := noc g1 he gin' hin.
  by rewrite gl=>/(_ vh)=> -[]/(_ ph).
have pong : p === g1 by rewrite -gl left_on_edge.
have paboveg1 : p >>= g1
   by rewrite strict_nonAunder ?pong //; case/andP: pong.
move: (sorted_e) => /=/andP[] leg1 _.
have g1in : g1 \in ctxt by rewrite allin // inE eqxx.
have vg1 : valid_edge g1 p.
  by rewrite -(eqP (outs g1 _)) ?valid_edge_left // inE eqxx.
have := IH g1 _ _ paboveg1 vg1 g1in g1belowhigh outs' allin' sorted_e'.
case: (opening_cells_aux _ _ _ _) => [s1 c1] - /(_ _ _ erefl) {} IH /=.
by move=> [] <- <- /=; rewrite leg1.
Qed.

Lemma opening_cells_right_form p s low_e high_e :
valid_edge low_e p ->
valid_edge high_e p ->
p >>= low_e -> p <<< high_e ->
low_e <| high_e ->
{in s, forall g, left_pt g == p} ->
{in s, forall g, low_e <| g} ->
{in s, forall g, g <| high_e} ->
{in s &, (@no_crossing R)} ->
s_right_form (opening_cells p s low_e high_e).
Proof.
move=> vl vh pabove punder lowhigh outs alla allb noc; apply/allP.
have noc' : {in low_e :: high_e :: s &, (@no_crossing R)}.
  move=> e1 e2; rewrite !inE !orbA =>/orP[e1lh |e1in ]/orP[e2lh |e2in].
    by apply/orP;move:e1lh e2lh=> /orP[]/eqP -> /orP[]/eqP ->;
      rewrite ?edge_below_refl ?lowhigh ?orbT.
    - by move: e1lh=> /orP[]/eqP ->;apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    - by move: e2lh=> /orP[]/eqP ->; apply/orP;
         rewrite/below_alt ?alla ?allb ?orbT.
    by apply: noc.
have sorted_e : sorted (@edge_below R) (sort (@edge_below R) s).
  by apply: sort_edge_below_sorted.
have /sub_in1/= trsf : {subset sort (@edge_below R) s <= s}.
  by move=> x; rewrite mem_sort.
move/trsf:outs => {}outs.
have [lin hin] : (low_e \in [:: low_e, high_e & s]) /\
   (high_e \in [:: low_e, high_e & s]).
  by split; rewrite !inE eqxx ?orbT.
have slho : {subset (sort (@edge_below _) s) <=
               [:: low_e, high_e & s]}.
  by move=> x; rewrite mem_sort => xin; rewrite !inE xin ?orbT.
move=> x xin.
have srt : sorted (@edge_below R) (low_e :: sort (@edge_below R) s).
  case sq : (sort (@edge_below R) s) => [// | a tl].
    rewrite -[sorted _ _]/((low_e <| a) && sorted (@edge_below R) (a :: tl)).
    rewrite -sq sorted_e andbT alla //.
    by rewrite -(mem_sort (@edge_below _)) sq inE eqxx.
have := (opening_cells_aux_right_form _ _ _ _ lin hin lowhigh outs).
move: xin; rewrite /opening_cells.
case: (opening_cells_aux _ _ _ _) => [s1 c1] xin - /(_ s1 c1).
move=> /(_ _ _ _ _ _ _ _ erefl) => it.
by apply: (allP (it _ _ _ _ _ _ _) x xin).
Qed.

Lemma lower_edge_new_cells e low_e high_e:
forall new_open_cells,
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
opening_cells (point e) (outgoing e) low_e high_e = new_open_cells ->
low (head dummy_cell new_open_cells) = low_e.
Proof.
move=> vle vhe.
rewrite /opening_cells.
case : (sort (@edge_below R) (outgoing e)) => [/= |/= c q] newop.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE //= => <- /=.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE //.
by case: (opening_cells_aux _ _ _ _) => [s1 c1] /= => <- /=.
Qed.

Lemma opening_cells_not_nil out le he p :
  opening_cells p out le he != [::].
Proof.
rewrite /opening_cells; case: (opening_cells_aux _ _ _ _) => [s1 c1].
apply/eqP/rcons_neq0.
Qed.

Lemma higher_edge_new_cells e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) -> valid_edge high_e (point e) ->
forall new_open_cells,
opening_cells (point e) (outgoing e) low_e high_e =
   new_open_cells ->
high (last dummy_cell new_open_cells) = high_e.
Proof.
rewrite /opening_cells.
move=> /outleft_event_sort outl vle vhe.
have := opening_cells_aux_high_last vle vhe outl.
case : (opening_cells_aux _ _ _ _) => [s1 c1] <- ? <-.
by rewrite last_rcons.
Qed.

Lemma opening_cells_close event low_e high_e future :
valid_edge low_e (point event) ->
valid_edge high_e (point event) ->
out_left_event event ->
end_edge_ext bottom top low_e future ->
end_edge_ext bottom top high_e future ->
close_out_from_event event future ->
close_alive_edges (opening_cells (point event) (outgoing event) low_e high_e)
   future.
Proof.
rewrite /opening_cells.
move=> vle vhe oute A B /close_out_from_event_sort; move: A B.
have : {in sort (@edge_below _) (outgoing event),
          forall g, left_pt g == (point event)}.
  by move=> g; rewrite mem_sort; apply: oute.
move : low_e vle.
elim : (sort (@edge_below R) (outgoing event)) => [| g1 q Ih] /= 
            le vle oute' endl endh.
  move=> _.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE //= endl endh.
move => /andP[] endg1 allend.
have oute1 : {in q, forall g, left_pt g == point event}.
  by move=> g gin; apply oute'; rewrite inE gin orbT.
have vg1 : valid_edge g1 (point event).
  by rewrite -(eqP (oute' g1 _)) ?valid_edge_left // inE eqxx.
have:= Ih g1 vg1 oute1 (end_edgeW _ _ endg1) endh allend.
case : (opening_cells_aux _ _ _ _) => [s1 c1] => {}Ih.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
by rewrite pvertE //= endl (end_edgeW _ _ endg1) Ih.
Qed.

Lemma opening_valid e low_e high_e:
out_left_event e ->
valid_edge low_e (point e) ->
valid_edge high_e (point e) ->
seq_valid (opening_cells (point e) (outgoing e) low_e high_e) (point e).
Proof.
move=> + + vhe.
rewrite /opening_cells.
move/outleft_event_sort.
move : low_e.
elim : (sort (@edge_below R) (outgoing e)) => [/= | c q IH] low_e outl vle.
  rewrite /=.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE //= vle vhe.
rewrite /=.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
rewrite pvertE //.
have vc : valid_edge c (point e).
  by rewrite -(eqP (outl c _)) ?valid_edge_left // inE eqxx.
have outl1 : forall g, g \in q -> left_pt g == point e.
  by move=> g gin; rewrite outl // inE gin orbT.
have := IH c outl1 vc.
case: (opening_cells_aux _ _ _ _) => [s1 c1] {} Ih /=.
by rewrite vle vc Ih.
Qed.

Lemma adjacent_opening_aux p s le he news newc :
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  opening_cells_aux p s le he = (news, newc) -> 
  adjacent_cells (rcons news newc) /\
   (low (head dummy_cell (rcons news newc)) = le).
Proof.
move=> + vhe.
elim: s le news newc => [ | g s Ih] le news newc /= vle oute.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  by rewrite pvertE // pvertE // => - [] <- <- /=.
have vg : valid_edge g p.
  by rewrite -(eqP (oute g _)) ?valid_edge_left // inE eqxx.
have oute' : {in s, forall g, left_pt g == p}.
  by move=> g' gin; rewrite oute // inE gin orbT.
case oca_eq: (opening_cells_aux _ _ _ _) => [s1 c1].
have := Ih g s1 c1 vg oute' oca_eq => -[] Ih1 Ih2 {Ih}.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite pvertE // => - [] <- <- /=; split;[ | done].
case: (s1) Ih1 Ih2 => [ | a s'] /=.
  by move=> _ ->; rewrite eqxx.
by move=> -> ->; rewrite eqxx.
Qed.

Lemma adjacent_opening p s le he:
  valid_edge le p -> valid_edge he p ->
  {in s, forall g, left_pt g == p} ->
  adjacent_cells (opening_cells p s le he).
Proof.
move=> vle vhe lefts.
have lefts' : {in sort (@edge_below _) s, forall g, left_pt g == p}.
  by move=> g; rewrite mem_sort; apply: lefts.
rewrite /opening_cells; case oca_eq: (opening_cells_aux _ _ _ _) => [so co].
by have [] := adjacent_opening_aux vle vhe  lefts' oca_eq.
Qed.

Lemma opening_cells_last_lexePt e low_e high_e c :
out_left_event e ->
~~(point e <<< low_e) -> point e <<< high_e ->
valid_edge low_e (point e)-> valid_edge high_e (point e) ->
{in  (rcons (low_e::(sort (@edge_below R) (outgoing e))) high_e) &, no_crossing R} ->
low_e <| high_e ->
 c \in (opening_cells (point e) (outgoing e) low_e high_e) ->
 lexePt (last dummy_pt (left_pts c)) (point e).
Proof.
rewrite /opening_cells.
move => /outleft_event_sort outlefte eabl eunh lowv highv.
elim : (sort (@edge_below R) (outgoing e)) low_e eabl lowv outlefte => [/= | c' q IH] low_e eabl lowv outlefte nc linfh.
  have := pvertE highv; set high_p := Bpt _ _ => hp.
  have := pvertE lowv; set low_p := Bpt _ _ => lp.
  have := intersection_on_edge lp=> [][] poel lx_eq.
  have := intersection_on_edge hp=> [][] poeh hx_eq.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite lp hp.
  rewrite lx_eq in hx_eq.
  have y_ineq := order_below_viz_vertical lowv highv lp hp linfh.
  rewrite  inE => /eqP ->.
  case: ifP.
    rewrite -[pt_eqb R eq_op high_p (point e)]/(high_p == (point e) :> pt).
    move=> /eqP <-.
    rewrite -[pt_eqb R eq_op high_p low_p]/(high_p == low_p :> pt).
    case : ifP => [/eqP <-/=|/= _].
      by rewrite /lexePt eqxx le_refl orbT .
    by rewrite /lexePt hx_eq eqxx y_ineq /= orbT.
  rewrite /lexePt.
  rewrite -[pt_eqb _ _ _ _]/(high_p == point e :> pt).
  rewrite -[pt_eqb _ _ _ _]/(point e == low_p :> pt).
  case : ifP => [/eqP <-/=|/=_ ].
    by rewrite eqxx le_refl /= orbT.
  rewrite lx_eq eqxx.
  have -> : p_y low_p <= p_y (point e).
    by rewrite leNgt -(strict_under_edge_lower_y lx_eq poel).
  by rewrite orbT.
rewrite /= .
have cin : c' \in c' :: q.
  by rewrite  inE eqxx.
have c'v: (valid_edge c' (point e)).
  apply valid_edge_extremities.
  by rewrite outlefte // cin.
have einfc' : ~~ (point e <<< c').
  apply : onAbove.
  have := outlefte c' cin => /eqP <-.
  apply :  left_on_edge.
have outq: (forall e0 : edge_eqType R, e0 \in q -> left_pt e0 == point e).
  move => e0 ein.
  apply outlefte.
  by rewrite inE ein orbT.
have c'infh : c' <| high_e.
  have := nc high_e c'.
  rewrite /= !inE  !mem_rcons !inE  !eqxx !orbT /= => /(_ isT isT).
  move=> /below_altC/no_crossingE.
  have := outlefte c' cin => /eqP ->.
  rewrite highv eunh => [] /(_ isT) [a _].
  by apply: a.
have nc' : {in  (rcons (c'::q) high_e) &, no_crossing R}.
  move => e1 e2 e1in e2in.
  apply nc.
    by rewrite inE e1in orbT.
  by rewrite inE e2in orbT.
rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
have := pvertE lowv; set low_p := Bpt _ _ => lp.
rewrite lp.
have := intersection_on_edge lp=> [][] poel lx_eq.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co].
rewrite -[pt_eqb _ _ (point e) low_p]/(point e == low_p :> pt).
case : ifP=> [/eqP <-/=|/= _].
  rewrite inE => /orP  [/eqP -> /=|].
    by rewrite lexePt_refl.
  have := IH c' einfc' c'v outq nc' c'infh.
  by rewrite oca_eq.
rewrite inE => /orP  [/eqP -> /=|].
  have : p_y low_p <= p_y (point e).
    by rewrite leNgt -(strict_under_edge_lower_y lx_eq poel).
  rewrite /lexePt lx_eq eqxx=> ->.
  by rewrite orbT.
have := IH c' einfc' c'v outq nc' c'infh.
by rewrite oca_eq.
Qed.

Arguments pt_eqb : simpl never.

Lemma opening_cells_aux_side_limit e s le he s' c':
  valid_edge le e -> valid_edge he e ->
  e >>= le -> e <<< he ->
  {in s, forall g, left_pt g == e} ->
  opening_cells_aux e s le he = (s', c') ->
  all open_cell_side_limit_ok (rcons s' c').
Proof.
move=> + vh.
elim : s le s' c'=> [ | g s Ih] le s' c' /= vl above under lg.
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  rewrite -[generic_trajectories.vertical_intersection_point
             _ _ _ _ _ _ _ _ _ _ _]/(vertical_intersection_point _ _).
  have := pvertE vl; set p1 := Bpt _ _ => /[dup] vip1 ->.
  have := pvertE vh; set p2 := Bpt _ _ => /[dup] vip2 ->.
  rewrite /open_cell_side_limit_ok => -[] <- <- /=.
  have [v1 on1 x1] : [/\ valid_edge le p1, p1 === le & p_x e = p_x p1].
    by have [on1 xp] := intersection_on_edge vip1.
  have [v2 on2 x2] : [/\ valid_edge he p2, p2 === he & p_x e = p_x p2].
    by have [on2 xp] := intersection_on_edge vip2.
  have p2ne : p2 != e :> pt.
    apply/eqP=> A; have := strict_under_edge_lower_y x2 on2.
    by rewrite under => /esym; rewrite ltNge A lexx.
  rewrite -[pt_eqb _ _ p2 e]/(p2 == e :> pt).
  rewrite -[pt_eqb _ _ e p1]/(e == p1 :> pt).
  rewrite (negbTE p2ne); case: ifP => [p1ise | p1ne] /=;
    move: on1 on2; rewrite ?(eqP p2ise) -?(eqP p1ise) => on1 on2;
    rewrite ?eqxx ?on1 ?on2 ?(eqP p2ise) -?(eqP p1ise) -?x1 -?x2
        ?eqxx ?andbT //=.
    have euh : e <<= he by apply: underW.
    rewrite lt_neqAle.
    have tmp:= (under_edge_lower_y x2 on2).
    rewrite (eqP p1ise) /p1 /p2 /= in tmp; rewrite -tmp {tmp}.
    rewrite -/p1 -(eqP p1ise) euh andbT.
    apply/negP=> A; case/negP: p2ne; rewrite pt_eqE (eqP p1ise) /=.
    by rewrite (eqP A) !eqxx.
  rewrite -(strict_under_edge_lower_y x2 on2) under /=.
  rewrite ltNge le_eqVlt negb_or.
  rewrite -(strict_under_edge_lower_y x1 on1) above andbT.
  by apply/negP=> A;case/negbT/negP:p1ne; rewrite pt_eqE -?x1 (eqP A) !eqxx.
have /eqP lgg : left_pt g == e by apply: lg; rewrite inE eqxx.
rewrite 
 -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
have := pvertE vl; set p1 := Bpt _ _ => /[dup] vip1 ->.
have [v1 on1 x1] : [/\ valid_edge le p1, p1 === le & p_x e = p_x p1].
  by have [on1 xp] := intersection_on_edge vip1.
have eong : e === g by rewrite -(eqP (lg g _)) ?inE ?eqxx // left_on_edge.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co] [] <- <-.
rewrite /=; apply/andP; split.
  rewrite /open_cell_side_limit_ok.
  rewrite -[pt_eqb _ _ e p1]/(e == p1 :> pt).
  case: ifP=> [eisp1 | enp1] /=;
    rewrite -?x1 !eqxx on1 -?(eqP eisp1) ?eong ?andbT //=.
  rewrite ltNge le_eqVlt negb_or.
  rewrite -(strict_under_edge_lower_y x1 on1) above andbT.
  by apply/negP=> A; case/negP: enp1; rewrite pt_eqE (eqP A) x1 ?eqxx.
apply/allP=> c cintl.
suff/allP/(_ c cintl) : all open_cell_side_limit_ok (rcons so co) by [].
apply: (Ih g) => //.
- by apply: valid_edge_extremities; rewrite lg ?inE ?eqxx.
- by apply: onAbove.
by move: lg; apply: sub_in1 => g' gin; rewrite inE gin orbT.
Qed.

Lemma opening_cells_side_limit e s le he :
  valid_edge le e -> valid_edge he e ->
  e >>= le -> e <<< he ->
  {in s, forall g, left_pt g == e} ->
  all open_cell_side_limit_ok (opening_cells e s le he).
Proof.
move=> vle vhe ea eu lefts.
have lefts' : {in sort (@edge_below _) s, forall g, left_pt g == e}.
  by move=> g; rewrite mem_sort; apply: lefts.
have := opening_cells_aux_side_limit vle vhe ea eu lefts'.
rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _) => [so co].
by apply.
Qed.

Lemma fan_edge_below_trans (s : seq edge) p :
  {in s, forall g, left_pt g == p} ->
  {in s & &, transitive (@edge_below R)}.
Proof.
move=> lcnd g1 g2 g3 g1in g2in g3in.
by apply: trans_edge_below_out (eqP (lcnd _ _))(eqP (lcnd _ _))(eqP (lcnd _ _)).
Qed.

Lemma opening_cells_pairwise' e le he :
   point e >>> le ->
   point e <<< he ->
   out_left_event e ->
   {in le :: he :: outgoing e &, no_crossing R} ->
   valid_edge le (point e) ->
   valid_edge he (point e) ->
   pairwise (@edge_below _)
         [seq high x | x <- (opening_cells (point e) (outgoing e) le he)].
Proof.
move=> pal puh oute noc vle vhe; rewrite /opening_cells.
have oute' := outleft_event_sort oute.
have lein : le \in le :: he :: sort (@edge_below _) (outgoing e) by subset_tac.
have hein : he \in le :: he :: sort (@edge_below _) (outgoing e) by subset_tac.
have subo' : {subset sort (@edge_below _) (outgoing e) <=
   le :: he :: sort (@edge_below _) (outgoing e)} by subset_tac.
have sub' : (le :: he :: sort (@edge_below _) (outgoing e)) =i (le :: he :: (outgoing e)).
  by move=> g; rewrite !inE mem_sort.
have noc' : {in le :: he :: sort (@edge_below _) (outgoing e) &, no_crossing R}.
  by move=> g1 g2; rewrite !sub'; apply: noc.
case oca_eq : opening_cells_aux => [s' c].
rewrite pairwise_map pairwise_rcons -pairwise_map /=.
have [_ it _]:= outgoing_conditions pal puh lein hein vle vhe subo' noc' oute'.
have := opening_cells_aux_high vle vhe oute'; rewrite oca_eq /= => highsq.
 apply/andP; split.
  rewrite [X in is_true X]
     (_ : _ = all (fun x => x <| high c) [seq high x | x <- s']); last first.
    by rewrite all_map.
  have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq /= => ->.
  by rewrite highsq; apply/allP.
rewrite highsq.
have loc_trans : {in sort (@edge_below _) (outgoing e) & &,
 transitive (@edge_below _)}.
  by apply: (@fan_edge_below_trans _ (point e)).
have /sort_edge_below_sorted : {in outgoing e &, no_crossing _}.
  by move=> x y xin yin; apply: noc; subset_tac.
by rewrite (sorted_pairwise_in loc_trans (allss _)).
Qed.

Lemma opening_cells_contains_point e le he nos:
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  out_left_event e ->
  opening_cells (point e) (outgoing e) le he = nos ->
  {in nos, forall c, contains_point (point e) c}.
Proof.
move=> vle vhe pal puh oute oceq.
have oute' := outleft_event_sort oute.
have := opening_cells_aux_subset vle vhe oute'.
move: oceq; rewrite /opening_cells.
case oca_eq : (opening_cells_aux _ _ _ _)=> [nos' lno'] <- /(_ _ _ _ erefl).
move=> main x xin; rewrite contains_pointE.
move: (main x xin); rewrite !inE=> /andP[] lows highs.
apply/andP; split.
  move: lows=> /orP[/eqP -> | /oute'/eqP <-]; first by rewrite underWC.
  by rewrite left_pt_above.
move: highs=> /orP[/eqP -> | /oute'/eqP <-]; first by rewrite underW.
by rewrite left_pt_below.
Qed.

Lemma opening_cells_last_left_pts e le he :
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  out_left_event e ->
  outgoing e != nil ->
  point e <<< he ->
  left_pts (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
     le he).2
 = Bpt (p_x (point e)) (pvert_y (point e) he) :: point e :: nil.
Proof.
move=> vle vhe oute onn puh.
have oute' := outleft_event_sort oute.
have puh' : p_y (point e) < pvert_y (point e) he.
  by rewrite -strict_under_pvert_y.
have pdif : Bpt (p_x (point e)) (pvert_y (point e) he) != point e :> pt.
  rewrite pt_eqE negb_and /=; apply/orP; right; rewrite eq_sym.
  by move: puh'; rewrite lt_neqAle => /andP[] ->.
case ogeq : (sort _ (outgoing e)) (mem_sort (@edge_below _) (outgoing e)) =>
  [ | fog ogs] // .
  move=> abs; case ogeq' : (outgoing e) onn => [ | f q] //=.
  by suff : f \in [::];[rewrite in_nil | rewrite abs ogeq' inE eqxx].
move=> elems.
have lf : left_pt fog = point e.
  by move: oute'; rewrite ogeq=> oute2; apply/eqP/oute2; rewrite inE eqxx.
have vf : valid_edge fog (point e) by rewrite valid_edge_extremities // lf eqxx.
rewrite opening_cells_aux_eqn.
rewrite /= pvertE //.
have : {subset ogs <= outgoing e} by move=> x xin; rewrite -elems inE xin orbT.
move: (fog) lf vf {ogeq elems}.
elim : (ogs) le {vle} => [ | f q Ih] //= => le fog1 lfog1 vf1 qsubo.
  rewrite 
   -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
  rewrite 
    -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
  rewrite pvertE // pvertE //=. 
  rewrite -[pt_eqb _ _ _ (point e)]/(_ == point e :> pt).
  rewrite (negbTE pdif).
  have -> : pvert_y (point e) fog1 = p_y (point e).
     by apply on_pvert; rewrite -lfog1 left_on_edge.
  rewrite -[pt_eqb _ _ (point e) _]/(point e == _ :> pt).
  rewrite pt_eqE /= !eqxx /=; congr (_ :: _ :: _); apply/(@eqP [eqType of pt]).
  by rewrite pt_eqE /= !eqxx.
case oca_eq: (opening_cells_aux _ _ _ _) => [s c].
rewrite 
 -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
rewrite pvertE //=.
have lfq : left_pt f = point e.
  by apply/eqP/oute'; rewrite mem_sort qsubo // inE eqxx.
have vf : valid_edge f (point e).
  by apply: valid_edge_extremities; rewrite lfq eqxx.
have qsub : {subset q <= outgoing e}.
  by move=> x xin; apply: qsubo; rewrite inE xin orbT.
by have := Ih le f lfq vf qsub; rewrite oca_eq /=.
Qed.

Lemma opening_cells_aux_absurd_case e le he (s : seq edge) :
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  s != [::] ->
  {in s, forall g, left_pt g == point e} ->
   (opening_cells_aux (point e) (sort (@edge_below _) s) le he).1 != [::].
Proof.
move=> vle vhe + outs; case sq : s => [ // | a s'] _.
case ssq : (sort (@edge_below _) s) => [ | b s2].
  by suff : a \in [::];[ | rewrite -ssq mem_sort sq inE eqxx].
rewrite opening_cells_aux_eqn.
rewrite -sq ssq /= pvertE //.
by case oca_eq : (opening_cells_aux _ _ _ _).
Qed.

(* TODO : complain that there is no sort_eq0 lemma with statement
   (sort r l == [::]) = (l == [::]) *)

Lemma opening_cells_1 e le he:
  outgoing e != [::] ->
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  out_left_event e ->
  exists fno nos lno, opening_cells (point e) (outgoing e) le he =
       fno :: rcons nos lno.
Proof.
move=> ogn vle vhe oute.
rewrite /opening_cells.
have := opening_cells_aux_absurd_case vle vhe ogn oute.
set x := (opening_cells_aux _ _ _ _).
case x => [ [ | fno nos] lno] // _.
by exists fno, nos, lno.
Qed.

Lemma opening_cells_in p' s le he :
  valid_edge le p' -> valid_edge he p' ->
  {in s, forall g, left_pt g == p'} ->
  {in opening_cells p' s le he, forall c, p' \in (left_pts c : seq pt)}.
Proof.
move=> + vhe outp.
rewrite /opening_cells.
have {outp} : {in sort (@edge_below _) s, forall g, left_pt g == p'}.
  by move=> g; rewrite mem_sort; apply: outp.
elim: (sort _ _) le => [ | g gs Ih] le.
  move=> _ /= vle g.
  rewrite 
   -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
  rewrite 
   -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
  rewrite (pvertE vle) (pvertE vhe) !inE => /eqP ->.
  do 2 rewrite -[pt_eqb _ _ _ _]/(_ == _ :> pt).
  case: ifP=> []; case: ifP=> [] /=.
        move=> /eqP -> // /eqP <-.
        by rewrite (@mem_head [eqType of pt]).
      by rewrite (@mem_head [eqType of pt]).
    move=> /eqP <-; rewrite (@in_cons [eqType of pt]).
    by rewrite (@mem_head [eqType of pt]) orbT.
    (* was by move=> /eqP <-; rewrite !inE eqxx orbT. *)
  by rewrite (@in_cons [eqType of pt]) (@mem_head [eqType of pt]) orbT.
move=> outp vl.
have lgq : left_pt g = p' by apply/eqP; apply: (outp _ (mem_head _ _)).
have vg : valid_edge g p' by rewrite -lgq valid_edge_left.
have {}outp : {in gs, forall g, left_pt g == p'}.
  by move=> g' gin; apply: outp; rewrite inE gin orbT.
have {}Ih := Ih g outp vg.
rewrite /=.
rewrite 
 -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
rewrite /= (pvertE vl); case oca_eq : (opening_cells_aux _ _ _ _)=> [nos lno].
move: Ih; rewrite oca_eq /= => Ih.
move=> c; rewrite inE=> /orP[/eqP -> /= |]; last by apply: Ih.
case: ifP; last by rewrite (@mem_head [eqType of pt]).
rewrite -[pt_eqb _ _ _ _]/(_ == _ :> pt).
by move=> /eqP <-; rewrite (@mem_head [eqType of pt]).
Qed.

Lemma last_opening_cells_side_char e le he pp nos lno :
  outgoing e != [::] ->
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e <<< he ->
  out_left_event e ->
  opening_cells (point e) (outgoing e) le he = rcons nos lno ->
  in_safe_side_left pp lno =
   [&& p_x pp == p_x (point e), p_y (point e) < p_y pp & pp <<< he].
Proof.
move=> ogn0 vle vhe puh oute oeq.
have oute' := outleft_event_sort oute.
have oca_eq:
  (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he) =
 (nos, lno).
  move: oeq; rewrite /opening_cells; case: (opening_cells_aux _ _ _ _)=> [a b].
  by move/eqP; rewrite eqseq_rcons=> /andP[] /eqP -> /eqP ->.
have lnoin : lno \in opening_cells (point e) (outgoing e) le he.
  by rewrite oeq mem_rcons mem_head.
rewrite /in_safe_side_left.
have := opening_cells_left oute vle vhe lnoin=> ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have highlno : high lno = he.
  by have := opening_cells_aux_high_last vle vhe oute'; rewrite oca_eq.
rewrite highlno [in RHS]andbC.
have := opening_cells_1 ogn0 vle vhe oute => -[fno [nos' [lno' oeq']]].
have [nosq lnoq] : nos = fno :: nos' /\ lno = lno'.
  move: oeq'; rewrite oeq -[fno :: rcons _ _]/(rcons (fno :: _) _) => /eqP.
  by rewrite eqseq_rcons => /andP[] /eqP -> /eqP ->.
have llnoq : low lno = high (last fno nos').
  have := adjacent_opening vle vhe oute; rewrite oeq'.
  rewrite /= -cats1 cat_path=> /andP[] _ /=.
  by rewrite andbT lnoq eq_sym=> /eqP.
have /oute lfnoq : high (last fno nos') \in outgoing e.
  have := opening_cells_high vle vhe oute; rewrite oeq'.
  have := size_sort (@edge_below _) (outgoing e).
(* TODO : should use some lemma here *)
  rewrite -(mem_sort (@edge_below _)); case: (sort _ _) => [ | w w'] //=.
    by move=>/eqP; rewrite eq_sym size_eq0 (negbTE ogn0).
  move=> _ [] <-; rewrite map_rcons=> /eqP.
  rewrite eqseq_rcons => /andP[] /eqP <- _.
  by elim/last_ind: (nos') => [ | ? ? _];
rewrite ?mem_head // last_rcons inE map_rcons mem_rcons mem_head orbT.
have eonl : point e === low lno by rewrite llnoq -(eqP lfnoq) left_on_edge.
have ppal : (pp >>> low lno) = (p_y (point e) < p_y pp).
  have := under_edge_lower_y (eqP samex) eonl => ->.
  by rewrite -ltNge.
rewrite ppal.
have := opening_cells_last_left_pts vle vhe oute ogn0 puh.
rewrite oca_eq /= => ->.
have [ppuh /= | ] := boolP (pp <<< he); last by [].
have [ppae /= | ] := boolP (p_y (point e) < p_y pp); last by [].
rewrite !(@in_cons [eqType of pt]) !pt_eqE /=.
have vpphe : valid_edge he pp by rewrite (same_x_valid _ samex).
rewrite -(same_pvert_y vpphe samex).
move: ppuh; rewrite (strict_under_pvert_y vpphe) lt_neqAle=> /andP[].
move=> /negbTE -> _.
move: ppae; rewrite lt_neqAle eq_sym=> /andP[] /negbTE -> _.
by rewrite !andbF.
Qed.

Lemma opening_cells_first_left_pts e le he :
  valid_edge le (point e) ->
  outgoing e != nil ->
  point e >>> le ->
  left_pts 
     (head dummy_cell
     (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e))
     le he).1)
 = point e :: Bpt (p_x (point e)) (pvert_y (point e) le) :: nil.
Proof.
move=> vle onn pal.
set W := sort _ _.
have sgt0 : (0 < size W)%N by rewrite /W size_sort; case : (outgoing e) onn.
case Wq : W sgt0 => [ // | g1 gs'] _ /=.
case oca_eq : (opening_cells_aux _ _ _ _) => [nos lno].
rewrite 
 -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
rewrite pvertE //=.
rewrite -[pt_eqb _ _ _ _]/(_ == _ :> pt).
case: ifP=> // samept.
have := pvert_on vle; rewrite -(eqP samept) => onle.
have /andP[/eqP pf _] := onle.
by move: pal; rewrite /point_under_edge underE pf le_eqVlt eqxx.
Qed.

Lemma first_opening_cells_side_char e le he pp fno nos lno :
  outgoing e != [::] ->
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  out_left_event e ->
  opening_cells (point e) (outgoing e) le he = rcons (fno :: nos) lno ->
  in_safe_side_left pp fno =
   [&& p_x pp == p_x (point e), p_y pp  < p_y (point e) & pp >>> le].
Proof.
move=> ogn0 vle vhe pal oute oeq.
have oute' := outleft_event_sort oute.
have oca_eq:
  (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he) =
 ((fno :: nos), lno).
  move: oeq; rewrite /opening_cells; case: (opening_cells_aux _ _ _ _)=> [a b].
  by move/eqP; rewrite eqseq_rcons=> /andP[] /eqP -> /eqP ->.
have fnoin : fno \in opening_cells (point e) (outgoing e) le he.
  by rewrite oeq mem_rcons !inE eqxx orbT.
rewrite /in_safe_side_left.
have := opening_cells_left oute vle vhe fnoin=> ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have lowfno : low fno = le.
  by rewrite (lower_edge_new_cells vle vhe oeq).
rewrite lowfno.
have /oute hfnoq : high fno \in outgoing e.
  have := opening_cells_high vle vhe oute; rewrite oeq /=.
  have := size_sort (@edge_below _) (outgoing e).
(* TODO : should use some lemma here *)
  rewrite -(mem_sort (@edge_below _)); case: (sort _ _) => [ | w w'] //=.
    by move=>/eqP; rewrite eq_sym size_eq0 (negbTE ogn0).
  move=> _ [] <-; rewrite map_rcons=> /eqP.
  rewrite eqseq_rcons => /andP[] /eqP <- _.
  by rewrite mem_head.
have eonh : point e === high fno by rewrite -(eqP hfnoq) left_on_edge.
have ppue : (pp <<< high fno) = (p_y pp < p_y (point e)).
  by have := strict_under_edge_lower_y (eqP samex) eonh.
rewrite ppue.
have := opening_cells_first_left_pts he vle ogn0 pal.
rewrite oca_eq /= => ->.
have [{}ppue /= | ] := boolP (p_y pp < p_y (point e)); last by [].
have [ppal /= | ] := boolP (pp >>> le); last by [].
rewrite !(@in_cons [eqType of pt]) !pt_eqE.
have vpple : valid_edge le pp by rewrite (same_x_valid _ samex).
rewrite -(same_pvert_y vpple samex).
move: ppal; rewrite (under_pvert_y vpple) le_eqVlt negb_or=> /andP[].
move=> /negbTE -> _.
move: ppue; rewrite lt_neqAle=> /andP[] /negbTE -> _.
by rewrite !andbF.
Qed.

Lemma middle_opening_cells_side_char e le he pp fno nos lno :
  outgoing e != [::] ->
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  out_left_event e ->
  opening_cells (point e) (outgoing e) le he = rcons (fno :: nos) lno ->
  ~~ has (in_safe_side_left pp) nos.
Proof.
move=> ogn0 vle vhe oute oeq.
have oute' := outleft_event_sort oute.
have oca_eq:
  (opening_cells_aux (point e) (sort (@edge_below _) (outgoing e)) le he) =
 ((fno :: nos), lno).
  move: oeq; rewrite /opening_cells; case: (opening_cells_aux _ _ _ _)=> [a b].
  by move/eqP; rewrite eqseq_rcons=> /andP[] /eqP -> /eqP ->.
rewrite -all_predC; apply/allP=> c cino /=.
have cin : c \in opening_cells (point e) (outgoing e) le he.
  by rewrite oeq mem_rcons !(inE, mem_cat) cino !orbT.
rewrite /in_safe_side_left.
have := opening_cells_left oute vle vhe cin=> ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
have /oute hc : high c \in outgoing e.
  have := opening_cells_high vle vhe oute; rewrite oeq /=.
  have := size_sort (@edge_below _) (outgoing e).
(* TODO : should use some lemma here *)
  rewrite -(mem_sort (@edge_below _)); case: (sort _ _) => [ | w w'] //=.
    by move=>/eqP; rewrite eq_sym size_eq0 (negbTE ogn0).
  move=> _ [] <-; rewrite map_rcons=> /eqP.
  rewrite eqseq_rcons => /andP[] /eqP <- _.
  by rewrite inE map_f ?orbT.
have /oute lc : low c \in outgoing e.
  have := opening_cells_high vle vhe oute; rewrite oeq /=.
  have /= := opening_cells_seq_edge_shift oute' vle vhe oca_eq.
  move=> [] _ -> /eqP; rewrite eqseq_rcons=> /andP[] /eqP + _.
  rewrite -(mem_sort (@edge_below _)) => <-.
  by rewrite map_f // mem_rcons inE cino orbT.
have eonh : point e === high c by rewrite -(eqP hc) left_on_edge.
have eonl : point e === low c by rewrite -(eqP lc) left_on_edge.
have := strict_under_edge_lower_y (eqP samex) eonh=> ->.
have := under_edge_lower_y (eqP samex) eonl=> ->.
by rewrite le_eqVlt negb_or -!andbA andbCA; case: (_ < _); rewrite !andbF.
Qed.

Lemma single_opening_cell_side_char e le he pp :
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  outgoing e = [::] ->
  has (in_safe_side_left pp) (opening_cells (point e) (outgoing e) le he) =
  ([&& p_x pp == p_x (point e), pp >>> le & p_y pp < p_y (point e)] ||
   [&& p_x pp == p_x (point e), pp <<< he & p_y (point e) < p_y pp]).
Proof.
move=> vle vhe pal puh og0.
have oute : out_left_event e by move=> g; rewrite og0 in_nil.
have [ppe | ppne] := eqVneq (pp : pt) (point e).
  rewrite ppe !lt_irreflexive !andbF.
  apply /negbTE; rewrite -all_predC; apply/allP=> c cin /=.
  have einl := opening_cells_in vle vhe oute cin.
  by rewrite /in_safe_side_left einl !andbF.
have := opening_cells_left oute vle vhe.
rewrite og0 /opening_cells /=.
do 2 rewrite 
 -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
rewrite (pvertE vle) (pvertE vhe) /= orbF.
set c := Bcell _ _ _ _.
move=> /(_ _ (mem_head _ _)).
rewrite /in_safe_side_left /= => ->.
have [samex /= | ] := boolP (p_x pp == p_x (point e)); last by [].
rewrite andbCA.
have puhy : p_y (point e) < pvert_y (point e) he.
  by rewrite -(strict_under_pvert_y vhe).
have paly :  pvert_y (point e) le < p_y (point e).
  by rewrite ltNge -(under_pvert_y vle).
do 2 rewrite -[pt_eqb _ _ _ _]/(_ == _ :> pt).
rewrite !pt_eqE /= eqxx /=.
move: (puhy); rewrite lt_neqAle eq_sym=> /andP[] /negbTE -> _.
move: (paly); rewrite lt_neqAle eq_sym=> /andP[] /negbTE -> _.
have vpple : valid_edge le pp by rewrite (same_x_valid _ samex).
have vpphe : valid_edge he pp by rewrite (same_x_valid _ samex).

have [ | pa] := lerP (p_y pp) (p_y (point e)); rewrite ?(andbF, orbF).
  rewrite le_eqVlt => /orP[samey | /[dup] pu ->].
    by case/negP: ppne; rewrite pt_eqE samex samey.
  have [ppale | _] := boolP (pp >>> le); last by [].
  have -> : pp <<< he.
    rewrite (strict_under_pvert_y vpphe).
    rewrite (same_pvert_y vpphe samex).
    by apply: (lt_trans pu); rewrite -(strict_under_pvert_y vhe).
  rewrite /=.
  have ppaly :  pvert_y (point e) le < p_y pp.
    rewrite -(same_pvert_y vpple samex).
    by rewrite ltNge -(under_pvert_y vpple).
  rewrite !(@in_cons [eqType of pt]).
  rewrite (negbTE ppne) !pt_eqE /=.
  move: ppaly; rewrite lt_neqAle eq_sym=> /andP[] /negbTE -> _.
  have ppuhy : p_y pp < pvert_y (point e) he.
    by apply: (lt_trans pu).
  move: ppuhy; rewrite lt_neqAle => /andP[] /negbTE -> _.
  by rewrite !andbF.
move=> {c}.
rewrite ltNge le_eqVlt pa orbT andbF andbT /=.
have [ppuhe | _] := boolP (pp <<< he); last by rewrite andbF.
have ppale : pp >>> le.
  rewrite (under_pvert_y vpple).
  rewrite (same_pvert_y vpple samex) -ltNge.
  by apply: (lt_trans _ pa); rewrite ltNge -(under_pvert_y vle).
rewrite /=.
have ppaly :  pvert_y (point e) le < p_y pp.
  rewrite -(same_pvert_y vpple samex).
  by rewrite ltNge -(under_pvert_y vpple).
rewrite !(@in_cons [eqType of pt]) (negbTE ppne) !pt_eqE /=.
move: ppaly; rewrite lt_neqAle eq_sym=> /andP[] /negbTE -> _.
have ppuhy : p_y pp < pvert_y (point e) he.
  rewrite -(same_pvert_y vpphe samex).
  by rewrite -(strict_under_pvert_y vpphe).
 move: ppuhy; rewrite lt_neqAle => /andP[] /negbTE -> _.
by rewrite ppale !andbF.
Qed.

Lemma opening_cells_aux_uniq (q : pt) l g1 g2 r1 r2:
  uniq l ->
  g2 \notin l ->
  {in l, forall g, left_pt g == q} ->
  valid_edge g1 q ->
  valid_edge g2 q ->
  opening_cells_aux q l g1 g2 = (r1, r2) ->
  uniq (rcons r1 r2).
Proof.
move=> ul g2nin ol v1 v2 oca_eq.
have lg2 := opening_cells_aux_high_last v1 v2 ol.
have lg1 := opening_cells_aux_high v1 v2 ol.
apply: (@map_uniq _ _ high).
rewrite map_rcons rcons_uniq.
rewrite oca_eq /= in lg2 lg1.
by rewrite lg2 lg1 g2nin ul.
Qed.

(* TODO : move to points_and_edges. *)
Lemma half_point_valid (g : edge) (p1 p2 : pt) :
  valid_edge g p1 -> valid_edge g p2 ->
  valid_edge g (Bpt ((p_x p1 + p_x p2) / 2) ((p_y p1 + p_y p2) / 2)).
Proof.
rewrite /valid_edge; move=> /andP[] vp1l vp1r /andP[] vp2l vp2r /=.
have cst2gt0 : (0 < 2 :> R) by apply: addr_gt0.
apply/andP; split.
  rewrite -(ler_pM2r cst2gt0) -mulrA mulVf ?mulr1; last by apply: lt0r_neq0.
  by rewrite mulrDr !mulr1 lerD.
rewrite -(ler_pM2r cst2gt0) -mulrA mulVf ?mulr1; last by apply: lt0r_neq0.
by rewrite mulrDr !mulr1 lerD.
Qed.

Lemma half_between (x y : R) : x < y -> x < (x + y) / 2 < y.
Proof.
move=> xy.
have cst2gt0 : (0 < 2 :> R) by apply: addr_gt0.
apply/andP; split.
  rewrite -(ltr_pM2r cst2gt0) -mulrA mulVf ?mulr1; last by apply: lt0r_neq0.
  by rewrite mulrDr !mulr1 ler_ltD.
rewrite -(ltr_pM2r cst2gt0) -mulrA mulVf ?mulr1; last by apply: lt0r_neq0.
by rewrite mulrDr !mulr1 ltr_leD.
Qed.

Lemma half_between_edges (g1 g2 : edge) p :
  valid_edge g1 p -> valid_edge g2 p -> p >>= g1 -> p <<< g2 ->
  (Bpt (p_x p) ((pvert_y p g1 + pvert_y p g2) / 2)) >>> g1 /\
  (Bpt (p_x p) ((pvert_y p g1 + pvert_y p g2) / 2)) <<< g2.
Proof.
move=> vg1 vg2 pal puh; set p1 := Bpt _ _.
have samex : p_x p1 == p_x p by rewrite eqxx.
have v1g1 : valid_edge g1 p1 by rewrite (same_x_valid _ samex).
have v1g2 : valid_edge g2 p1 by rewrite (same_x_valid _ samex).
rewrite (under_pvert_y v1g1) (strict_under_pvert_y v1g2) -ltNge; apply/andP.
apply: half_between.
have := puh; rewrite (strict_under_pvert_y vg2); apply: le_lt_trans.
by rewrite leNgt -(strict_under_pvert_y vg1).
Qed.

Lemma opening_cells_non_empty e le he:
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  out_left_event e ->
  uniq (outgoing e) ->
  {in [:: le, he & outgoing e] &, forall e1 e2, inter_at_ext e1 e2} ->
  {in opening_cells (point e) (outgoing e) le he, forall c p,
     valid_edge (low c) p -> valid_edge (high c) p ->
     p_x (point e) < p_x p ->
     exists q, [&& q >>> low (close_cell p c), q <<< high (close_cell p c)&
                 left_limit (close_cell p c) < p_x q < 
                 right_limit (close_cell p c)]}.
Proof.
move=> vle vhe pal puh oute une noc.
rewrite /opening_cells.
have : {subset le :: sort (@edge_below _) (outgoing e) <=
               [:: le, he & outgoing e]}.
  move=> g; rewrite inE mem_sort=> /orP[/eqP -> | ]; first by subset_tac.
  by move=> gin; rewrite !inE gin !orbT.
have := outleft_event_sort oute.
have : sorted (@edge_below _) (le :: (sort (@edge_below _) (outgoing e))).
  by apply: (sorted_outgoing vle vhe _ _ _ (inter_at_ext_no_crossing noc)).
have : uniq (le :: sort (@edge_below _) (outgoing e)).
  rewrite /= sort_uniq une andbT.
  rewrite mem_sort; apply/negP=> /oute /eqP abs.
  by move: pal; rewrite under_onVstrict // -abs left_on_edge.
elim: (sort _ _) {-6} (le) vle (underWC pal)=> [ | g1 gs Ih] le' vle' pale'.
  move=> _ _ _ sub0.
rewrite opening_cells_aux_eqn.
  rewrite /= (pvertE vle') (pvertE vhe) /=.
  set c0 := (X in [:: X])=> ?; rewrite inE => /eqP -> p vlp vhp pxgt.
  (* point p0 has no guarantee concerning the vertical position. *)
  set p0 := Bpt ((p_x (point e) + p_x p) / 2) ((p_x (point e) + p_x p) / 2).
  have vlp0 : valid_edge le' p0 by apply: half_point_valid.
  set p1 := Bpt (p_x p0)(pvert_y p0 le').
  have vlp1 : valid_edge le' p1 by apply: half_point_valid.
  have vhp1 : valid_edge he p1 by apply: half_point_valid.
  have p1onle' : p1 === le' by apply: (pvert_on vlp0).
  have hein : he \in [:: le, he & outgoing e] by subset_tac.
  have le'in : le' \in [:: le, he & outgoing e] by apply: sub0; subset_tac.
  have ba' : inter_at_ext le' he by apply: noc.
  have ba : below_alt le' he by apply: (inter_at_ext_no_crossing noc).
  have le'bhe : le' <| he.
    by apply: (edge_below_from_point_above ba vle' vhe).
  have p1uh : p1 <<< he.
    have p1ule' : p1 <<= le' by rewrite (under_onVstrict vlp1) p1onle'.
    have : p1 <<= he by apply: (order_edges_viz_point' vlp1).
    rewrite (under_onVstrict vhp1)=> /orP[p1onhe |]; last by [].
    case: ba'=> [lqh | ]; first by move: pale'; rewrite lqh puh.
    move=> /(_ _ p1onle' p1onhe).
    rewrite !inE=> /orP[] /eqP abs.
      move: vle'; rewrite /valid_edge=> /andP[] + _; rewrite -abs.
      rewrite leNgt=> /negP[].
      by have := half_between pxgt=> /andP[] + _; apply.
    move: vlp; rewrite /valid_edge=> /andP[] _; rewrite -abs.
    rewrite leNgt=> /negP[].
    by have := half_between pxgt=> /andP[] _ +.
  have p1ale' : p1 >>= le' by rewrite (strict_nonAunder vlp1) p1onle'.
  have := half_between_edges vlp1 vhp1 p1ale' p1uh.
  set q := Bpt (p_x p1) ((pvert_y p1 le' + pvert_y p1 he) / 2).
  move=> []qal quh.  
  exists q.
  have [-> -> _] := close_cell_preserve_3sides p c0.
  rewrite right_limit_close_cell // left_limit_close_cell qal quh.
  have := half_between pxgt=> /andP[] keepit ->; rewrite andbT /=.
  rewrite /c0/=.
  by case: ifP=>[] _; case: ifP=> [] _ /=; rewrite /left_limit /= keepit.
move=> uns srt out sub /=.
case oca_eq: opening_cells_aux => [s c].
rewrite 
 -[generic_trajectories.vertical_intersection_point _ _ _ _ _ _ _ _ _ _ _]
   /(vertical_intersection_point _ _).
rewrite (pvertE vle') /=.
set c0 := Bcell _ _ _ _ _ _.
move=> c1; rewrite inE=> /orP[/eqP -> | c1in] p /= vlp vhc pxgt; last first.
  have lg1 : left_pt g1 = (point e).
    by have := out _ (mem_head _ _) => /eqP <-.
  have vg1 : valid_edge g1 (point e) by rewrite -lg1 valid_edge_left.
  have ag1 : point e >>= g1 by rewrite -lg1 left_pt_above.
  have out' : forall ed, ed \in gs -> left_pt ed == point e.
    by move=> ed edin; apply: out; rewrite inE edin orbT.
  have sub' : {subset g1 :: gs <= [:: le, he & outgoing e]}.
    by move=> g gin; apply: sub; rewrite inE gin orbT.
  have c1in' : c1 \in (let (s0, c2) := opening_cells_aux (point e) gs g1 he in
       rcons s0 c2).
    by rewrite oca_eq.
  have srt' : sorted (@edge_below _) (g1 :: gs) by move: srt=> /= /andP[] _.
  have un' : uniq (g1 :: gs) by move: uns=> /= /andP[].
  by apply: (Ih g1 vg1 ag1 un' srt' out' sub' _ c1in').
have [-> -> _] := close_cell_preserve_3sides p c0.
rewrite right_limit_close_cell // left_limit_close_cell.
set p0 := Bpt ((p_x (point e) + p_x p) / 2) ((p_x (point e) + p_x p) / 2).
have vlp0 : valid_edge le' p0 by apply: half_point_valid.
set p1 := Bpt (p_x p0) (pvert_y p0 le').
have vlp1 : valid_edge le' p1 by apply: half_point_valid.
have lg1 : left_pt g1 = point e by apply/eqP/out/mem_head.
have vg1 : valid_edge g1 (point e) by rewrite -lg1 valid_edge_left.
have vhp1 : valid_edge g1 p1 by apply: half_point_valid.
have p1onle' : p1 === le' by apply: (pvert_on vlp0).
have g1in : g1 \in [:: le, he & outgoing e] by apply: sub; subset_tac.
have le'in : le' \in [:: le, he & outgoing e] by apply: sub; subset_tac.
have ba' : inter_at_ext le' g1 by apply: noc.
have ba : below_alt le' g1 by apply: (inter_at_ext_no_crossing noc).
have le'bhe : le' <| g1 by move: srt=> /= /andP[].
have p1ug1 : p1 <<< g1.
  have p1ule' : p1 <<= le' by rewrite (under_onVstrict vlp1) p1onle'.
  have : p1 <<= g1.
    by apply: (order_edges_viz_point' vlp1).
  rewrite (under_onVstrict vhp1)=> /orP[p1ong1 |]; last by [].
  case: ba'=> [lqg1 | ]; first by move: uns; rewrite lqg1 /= inE eqxx.
  move=> /(_ _ p1onle' p1ong1).
  rewrite !inE=> /orP[] /eqP abs.
    move: vle'; rewrite /valid_edge=> /andP[] + _; rewrite -abs.
    rewrite leNgt=> /negP[].
    by have := half_between pxgt=> /andP[] + _; apply.
  move: vlp; rewrite /valid_edge=> /andP[] _; rewrite -abs.
  rewrite leNgt=> /negP[].
  by have := half_between pxgt=> /andP[] _ +.
have p1ale' : p1 >>= le' by rewrite (strict_nonAunder vlp1) p1onle'.
have := half_between_edges vlp1 vhp1 p1ale' p1ug1.
set q := Bpt (p_x p1) ((pvert_y p1 le' + pvert_y p1 g1) / 2).
move=> []qal qug1.
exists q.
have := half_between pxgt=> /andP[] keepit ->; rewrite andbT /=.
rewrite /c0/= qal qug1 /=.
by case: ifP=> [] _ /=; rewrite /left_limit /= keepit.
Qed.

End opening_cells.

End proof_environment.

End working_environment.

