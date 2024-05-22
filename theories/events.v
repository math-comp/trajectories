From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.
Require Import math_comp_complements.
Require Import generic_trajectories points_and_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Section working_environment.

Variable R : realFieldType.

Notation pt := (pt R).
Notation edge := (edge R).
Notation p_x := (p_x R).
Notation p_y := (p_y R).

Notation event := (event R edge).
Notation point := (point R edge).
Notation outgoing := (outgoing R edge).

Definition event_eqb (ea eb : event) : bool :=
  (point ea == point eb :> pt) && (outgoing ea == outgoing eb).

Lemma event_eqP : Equality.axiom event_eqb.
Proof.
rewrite /Equality.axiom.
move => [pta outa] [ptb outb] /=.
rewrite /event_eqb/=.
have [/eqP <- | /eqP anb] := boolP (pta == ptb :> pt).
  have [/eqP <- | /eqP anb] := boolP (outa == outb).
    by apply: ReflectT.
  by apply : ReflectF => [][].
by apply: ReflectF=> [][].
Qed.

HB.instance Definition _ := hasDecEq.Build _ event_eqP.

Notation Bevent := (Bevent _ _).
(* As in insertion sort, the add_event function assumes that event are
  sorted in evs (lexicographically, first coordinate, then second coordinate
  of the point.  On the other hand, no effort is made to sort the various
  edges in each list.  *)
Fixpoint add_event (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if inc then [:: Bevent p [::]]
           else [:: Bevent p [:: e]]
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if p == p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if p_x p < p_x p1 then
      if inc then
        Bevent p [::] :: evs else
        Bevent p [:: e] :: evs
    else if (p_x p == p_x p1) && (p_y p < p_y p1) then
       if inc then
         Bevent p [::] :: evs else
         Bevent p [:: e] :: evs else
    ev1 :: add_event p e inc evs'
  end.

Lemma add_event_step (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  add_event p e inc evs =
  match evs with
  | nil => if inc then [:: Bevent p [::]]
           else [:: Bevent p [:: e]]
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if p == p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if p_x p < p_x p1 then
      if inc then
        Bevent p [::] :: evs else
        Bevent p [:: e] :: evs
    else if (p_x p == p_x p1) && (p_y p < p_y p1) then
       if inc then
         Bevent p [::] :: evs else
         Bevent p [:: e] :: evs else
    ev1 :: add_event p e inc evs'
  end.
Proof. by case: evs. Qed.

(* We should be able to prove that the sequence of events produced by
  edges to events is sorted lexicographically on the coordinates of
  the points. *)
Fixpoint edges_to_events (s : seq edge) : seq event :=
  match s with
  | nil => nil
  | e :: s' =>
    add_event (left_pt e) e false
      (add_event (right_pt e) e true (edges_to_events s'))
  end.

Section proof_environment.
Variable bottom top : edge.

Definition lexPtEv (e1 e2 : event) : bool :=
  lexPt (point e1) (point e2).

Definition lexePtEv (e1 e2 : event) : bool :=
  lexePt (point e1) (point e2).

Definition event_close_edge ed ev : bool :=
right_pt ed == point ev.

Definition end_edge edge events : bool :=
  has (event_close_edge edge) events.

Definition close_out_from_event ev future : bool :=
  all (fun edge => end_edge edge future) (outgoing ev).

Fixpoint close_edges_from_events events : bool :=
  match events with
  | [::] => true
  | ev :: future_events => close_out_from_event ev future_events && close_edges_from_events future_events
  end.

Lemma close_edges_from_events_step events :
  close_edges_from_events events = match events with
  | [::] => true
  | ev :: future_events => close_out_from_event ev future_events && close_edges_from_events future_events
  end.
Proof. by case: events. Qed.

Lemma lexPtEv_trans : transitive lexPtEv.
Proof. by move=> e2 e1 e3; rewrite /lexPtEv; apply: lexPt_trans. Qed.

Lemma lexePtEv_trans : transitive lexePtEv.
Proof. by move=> e1 e2 e3; rewrite /lexePtEv; apply: lexePt_trans. Qed.

Lemma event_close_edge_on g e:
  event_close_edge g e -> (point e) === g.
Proof.  by move=> /eqP <-; apply: right_on_edge. Qed.

Definition out_left_event ev :=
  {in outgoing ev, forall e, left_pt e == point(ev)}.

Lemma outleft_event_sort e :
  out_left_event e ->
  forall ed, ed \in sort (@edge_below R) (outgoing e) -> left_pt ed == point e.
Proof.
move=> outleft ed edin; apply: outleft.
by have <- := perm_mem (permEl (perm_sort (@edge_below _) (outgoing e))).
Qed.

Lemma close_out_from_event_sort event future :
  close_out_from_event event future ->
  all (end_edge^~ future) (sort (@edge_below R) (outgoing event)).
Proof.
move/allP=> outP; apply/allP=> x xin; apply outP.
by have <- := perm_mem (permEl (perm_sort (@edge_below R) (outgoing event))).
Qed.

Definition events_to_edges := flatten \o (map outgoing).

Lemma events_to_edges_cons e evs :
  events_to_edges (e :: evs) = outgoing e ++ events_to_edges evs.
Proof. by []. Qed.

Lemma out_left_event_on e :
  out_left_event e -> {in outgoing e, forall g, point e === g}.
Proof.
move=> outs g gin; rewrite -(eqP (outs _ gin)); apply: left_on_edge.
Qed.

Lemma sort_edge_below_sorted s :
  {in s &, @no_crossing _} ->
  sorted (@edge_below R) (sort (@edge_below R) s).
Proof.
move=> noc.
have /sort_sorted_in : {in s &, total (@edge_below _)}.
  by move=> x1 x2 x1in x2in; apply/orP/noc.
by apply; apply: allss.
Qed.

Lemma sorted_outgoing le he e : 
  valid_edge le (point e) ->
  valid_edge he (point e) ->
  point e >>> le ->
  point e <<< he ->
  out_left_event e ->
  {in le :: he :: outgoing e &, no_crossing R} ->
  sorted (@edge_below R) (le :: sort (@edge_below R) (outgoing e)).
Proof.
 set ctxt := (le :: he :: _); move=> vl hl above under outs noc.
have lein : le \in ctxt by rewrite /ctxt inE eqxx.
have hein : he \in ctxt by rewrite /ctxt !inE eqxx ?orbT.
have osub : {subset outgoing e <= ctxt}.
  by move=> g gin; rewrite /ctxt !inE gin ?orbT.
have [ls us noc''] :=
   outgoing_conditions above under lein hein vl hl osub noc outs.
have /sort_sorted_in tmp : {in le :: outgoing e &, total (@edge_below R)}.
  move=> e1 e2; rewrite !inE =>/orP[/eqP -> |e1in ]/orP[/eqP -> |e2in].
  - by rewrite edge_below_refl.
  - by rewrite ls.
  - by rewrite ls ?orbT.
  by apply/orP/noc''.
rewrite /=; case oeq : (sort (@edge_below R) (outgoing e)) => [// | g1 gs] /=.
rewrite ls; last first.
  have <- := perm_mem (permEl (perm_sort (@edge_below R) (outgoing e))).
  by rewrite oeq inE eqxx.
rewrite -[X in is_true X]/(sorted _ (g1 :: gs)) -oeq tmp //.
by apply/allP=> x xin /=; apply/orP; right; exact: xin.
Qed.

Definition events_non_inner (evs : seq event) :=
  {in evs &,
    forall ev1 ev2,
    {in outgoing ev1, forall g, non_inner g (point ev2)}}.

Lemma add_event_preserve_first p e inc ev evs :
  (0 < size (add_event p e inc (ev :: evs)))%N /\
  (point (head ev (add_event p e inc (ev :: evs))) = p \/
   point (head ev (add_event p e inc (ev :: evs))) = point ev).
Proof.
rewrite /=.
case: ev => [p1 o1].
have [/eqP -> | /eqP pnp1] := boolP(p == p1).
  by split; case: inc => //=; left.
have [pltp1 /= | pnltp1] := boolP(p_x p < p_x p1).
  split.
    by case: inc.
  by case:inc; left.
have [/eqP pxqpx1 /= | pxnpx1 /=] := boolP (p_x p == p_x p1).
  have [/eqP pyltpy1 /= | pynltpy1 /=] := boolP (p_y p < p_y p1).
    by case:inc; (split;[ | left]).
  by split;[ | right].
by split;[ | right].
Qed.

Lemma add_event_sort p e inc evs : sorted lexPtEv evs ->
  sorted lexPtEv (add_event p e inc evs).
Proof.
elim: evs => [ | ev1 evs Ih /=].
  by case: inc.
move=> path_evs.
have [/eqP pp1 | /eqP pnp1] := boolP(p == point ev1).
  case: inc Ih.
    by case: evs path_evs => [ | ev2 evs'].
  by case: evs path_evs => [ | ev2 evs'].
move/path_sorted/Ih: (path_evs) {Ih} => Ih.
have [ pltp1 | pnltp1] /= := boolP(p_x p < p_x (point ev1)).
  by case: inc {Ih}=> /=; (apply/andP; split=> //); rewrite /lexPtEv /lexPt /= pltp1.
have [/eqP pp1 | pnp1'] /= := boolP (p_x p == p_x (point ev1)).
  have pyneq : p_y p != p_y (point ev1).
    apply/eqP=> pp1'; case pnp1.
    move: p (point ev1) {pnp1 Ih pnltp1} pp1 pp1'.
    by move=> [a b][c d] /= -> ->.
  have [ pltp1 | pnltp1'] /= := boolP(p_y p < p_y (point ev1)).
    by case: (inc); rewrite /= path_evs andbT /lexPtEv /lexPt /= pp1 eqxx pltp1 orbT.
  have p1ltp : p_y (point ev1) < p_y p.
    by rewrite ltNge le_eqVlt negb_or pyneq pnltp1'.
  case evseq : evs => [ | [p2 o2] evs2].
    by case: (inc)=> /=; rewrite /lexPtEv /lexPt /= pp1 eqxx p1ltp orbT.
  rewrite -evseq.
  case aeq : (add_event p e inc evs) => [ | e' evs3].
    have := add_event_preserve_first p e inc
           (Bevent p2 o2) evs2.
      by rewrite -evseq aeq => [[]].
  case: (add_event_preserve_first p e inc
          (Bevent p2 o2) evs2)=> _.
  rewrite -evseq aeq /= => [] [eqp | eqp2].
    apply/andP; split; last by move: Ih; rewrite aeq.
    by rewrite /lexPtEv /lexPt eqp pp1 eqxx p1ltp orbT.
  apply/andP; split; last by move: Ih; rewrite aeq.
  move: path_evs; rewrite evseq /= andbC => /andP[] _.
  by rewrite /lexPtEv /= eqp2.
have p1ltp : p_x (point ev1) < p_x p.
  by rewrite ltNge le_eqVlt negb_or pnp1' pnltp1.
case evseq : evs => [ | [p2 o2] evs2].
  by case: (inc)=> /=; rewrite /lexPtEv /lexPt /= p1ltp.
case aeq : (add_event p e inc evs) => [ | e' evs3].
  case: (add_event_preserve_first p e inc
       (Bevent p2 o2) evs2).
  by rewrite -evseq aeq.
case: (add_event_preserve_first p e inc
     (Bevent p2 o2) evs2) => _.
have path_e'evs3 : path lexPtEv e' evs3 by move: Ih; rewrite aeq.
rewrite -evseq aeq /= => [][e'p | e'p2]; rewrite path_e'evs3 andbT.
  by rewrite /lexPtEv /lexPt e'p p1ltp.
by move: path_evs; rewrite evseq /= andbC /lexPtEv e'p2=> /andP[].
Qed.

Lemma sorted_edges_to_events s :
   sorted (@lexPt R) [seq point x | x <- edges_to_events s].
Proof.
have /mono_sorted -> : {mono point : x y / lexPtEv x y >-> lexPt x y} by [].
by elim: s => [ | g s Ih] //=; do 2 apply: add_event_sort.
Qed.

End proof_environment.

Lemma add_event_preserve_ends p e inc evs ed :
  end_edge ed evs ->
  end_edge ed (add_event p e inc evs).
Proof.
rewrite /end_edge /=.
elim: evs => [// | ev evs Ih] /= /orP[|];
  repeat (case: ifP => _);
   rewrite /=/event_close_edge /=; try (move=> -> //); rewrite ?orbT //.
by move=> ?; rewrite Ih ?orbT.
Qed.

Lemma add_event_inc evs ed :
  end_edge ed (add_event (right_pt ed) ed true evs).
Proof.
elim: evs => [ | ev evs Ih] /=.
  by rewrite /end_edge /event_close_edge eqxx.
case: ifP=> [/eqP <- | ].
  by rewrite /end_edge /= /event_close_edge /= eqxx.
repeat (case: ifP=> _); rewrite /end_edge/=/event_close_edge ?eqxx //.
move=> _; move: Ih; rewrite /end_edge/=/event_close_edge => ->.
by rewrite !orbT.
Qed.

Lemma close_edges_from_events_inc evs p ed :
 close_edges_from_events evs ->
 close_edges_from_events (add_event p ed true evs).
Proof.
elim: evs => /= [ // | ev evs Ih /andP [clev clevs]].
move: Ih=> /(_ clevs) Ih.
case: ifP=> _ /=; first by rewrite clevs andbT; exact clev.
case: ifP=> _ /=; first by rewrite clevs andbT; exact clev.
case: ifP=> _ /=; first by rewrite clevs andbT; exact clev.
rewrite Ih andbT.
apply/allP=> ed' edin'.
move: (allP clev ed' edin').
by move=> it; rewrite add_event_preserve_ends // /end_edge it.
Qed.

Lemma add_edge_close_edges_from_events evs ed :
  close_edges_from_events evs ->
  close_edges_from_events
    (add_event (left_pt ed) ed false (add_event (right_pt ed) ed true evs)).
Proof.
have no_eq : left_pt ed == right_pt ed = false.
    by apply/negP=> /eqP abs_eq; have := edge_cond ed; rewrite abs_eq ltxx.
elim: evs => [/= _ | ev evs Ih].
  rewrite no_eq edge_cond /=.
  by rewrite /close_out_from_event /= /end_edge/=/event_close_edge eqxx.
move=> tmp; rewrite /= in tmp; case/andP: tmp=> [clev clevs].
move: Ih=> /(_ clevs) Ih.
have : end_edge ed (add_event (right_pt ed) ed true (ev :: evs)).
  by apply: add_event_inc.
rewrite [add_event (right_pt _) _ _ _]add_event_step.
lazy zeta.
case: ifP=> [/eqP <- /= | cnd1].
  rewrite no_eq edge_cond /=.
  rewrite /close_out_from_event /= /end_edge/=/event_close_edge.
  rewrite eqxx /= clevs andbT=> _; exact: clev.
case: ifP=> cnd2 /=.
  rewrite no_eq edge_cond /=.
  rewrite /close_out_from_event /= => -> /=; rewrite clevs andbT; exact: clev.
case: ifP=> cnd3 ended /=.
  rewrite no_eq edge_cond.
  rewrite close_edges_from_events_step.
  apply/andP; split; last by rewrite /= clev clevs.
  by move: ended; rewrite /= /close_out_from_event /= andbT.
case: ifP=> cnd4.
  rewrite close_edges_from_events_step /close_out_from_event/=.
  rewrite close_edges_from_events_inc ?andbT ?clevs //.
  apply/andP; split; last first.
    apply/allP=> x xin.
    move/allP: clev=> /(_ x xin) closed.
    by rewrite add_event_preserve_ends ?orbT.
  by rewrite add_event_inc.
case: ifP=> cnd5.
  rewrite close_edges_from_events_step; apply/andP; split.
    by move: ended; rewrite /= /close_out_from_event /= andbT.
  rewrite close_edges_from_events_step; apply/andP; split.
    apply/allP=> x xin; apply: add_event_preserve_ends.
    by move/allP: clev=> /(_ x xin).
  by apply: close_edges_from_events_inc.
case: ifP=> cnd6.
  rewrite close_edges_from_events_step; apply/andP; split.
    by move: ended; rewrite /close_out_from_event /= andbT.
  rewrite close_edges_from_events_step; apply/andP; split.
    apply/allP=> x xin; apply: add_event_preserve_ends.
    by move/allP: clev=> /(_ x xin).
  by apply: close_edges_from_events_inc.
rewrite close_edges_from_events_step; apply/andP; split.
  rewrite /close_out_from_event.
  apply/allP=> x xin.
  do 2 apply:add_event_preserve_ends.
  by move/allP: clev; apply.
by apply: Ih.
Qed.

Lemma edges_to_events_wf (bottom top : edge)(s : seq edge) :
  close_edges_from_events (edges_to_events s).
Proof.
elim : s => [ // | e s Ih /=].
by apply: add_edge_close_edges_from_events.
Qed.

Lemma edges_to_events_no_loss (s : seq edge) :
  perm_eq s (events_to_edges (edges_to_events s)).
Proof.
have add_inc evs p ed:
  perm_eq (events_to_edges evs)
    (events_to_edges (add_event p ed true evs)).
  elim: evs => [/= | ev evs Ih]; first by apply: perm_refl.
  rewrite /events_to_edges /=.
  by repeat (case: ifP=> _ //=); rewrite perm_cat2l Ih.
have add_out evs p ed:
  perm_eq (ed :: events_to_edges evs)
     (events_to_edges (add_event p ed false evs)).
  elim: evs => [/= | ev evs]; first by apply: perm_refl.
  rewrite /events_to_edges /= => Ih.
  repeat (case: ifP => //=); move => ? ? ?.
  rewrite -[ed :: outgoing ev ++ _]/([:: ed] ++ outgoing ev ++ _).
  by rewrite perm_catCA perm_cat2l Ih.
elim: s => /= [// | ed s Ih]; rewrite -(perm_cons ed) in Ih.
apply/(perm_trans Ih)/(perm_trans _ (add_out _ (left_pt ed) _)).
by rewrite perm_cons; apply: add_inc.
Qed.

Lemma edges_to_events_no_crossing s :
  {in s &, no_crossing R} ->
  {in events_to_edges (edges_to_events s) &, no_crossing R}.
Proof.
by apply: sub_in2=> x; rewrite (perm_mem (edges_to_events_no_loss s)).
Qed.

Lemma out_left_add_event p g b evs:
    p = (if b then right_pt g else left_pt g) ->
    {in evs, forall ev, out_left_event ev} ->
    {in add_event p g b evs, forall ev, out_left_event ev}.
Proof.
move=> ->.
elim: evs => [ | ev evs Ih] acc.
  move=> /= ev; case:b; rewrite inE => /eqP -> e //=.
  by rewrite inE => /eqP ->; rewrite eqxx.
rewrite /=; case: ifP=> [/eqP pev | ] ev'.
  case bval: (b); rewrite /= inE => /orP[/eqP ev'ev | ev'inevs].
  - have -> : ev' = ev by rewrite ev'ev; case: (ev).
    by apply: acc; rewrite inE eqxx.
  - by apply: acc; rewrite inE ev'inevs orbT.
  - move=> g2; rewrite ev'ev /= inE=> /orP[/eqP -> | ].
    * by rewrite -pev bval eqxx.
    by apply: acc; rewrite inE eqxx.
  by apply: acc; rewrite inE ev'inevs orbT.
case: ifP => [athead | later].
  case bval: (b) => ev2; rewrite inE => /orP[].
  - by move/eqP=> -> g2.
  - by apply: acc.
  - by move/eqP=> -> g2 /=; rewrite inE=> /eqP ->; rewrite eqxx.
  by apply: acc.
case: ifP => [athead' | later'].
  case bval: (b) => ev2; rewrite inE => /orP[].
  - by move/eqP=> -> g2.
  - by apply: acc.
  - by move/eqP=> -> g2 /=; rewrite inE=> /eqP ->; rewrite eqxx.
  by apply: acc.
move=> ev2; rewrite inE=> /orP[/eqP -> | ev2intl].
  by apply: acc; rewrite inE eqxx.
apply: Ih=> //.
by move=> ev3 ev3in; apply: acc; rewrite inE ev3in orbT.
Qed.

Lemma out_left_edges_to_events s:
  {in edges_to_events s, forall ev, out_left_event ev}.
Proof.
elim: s => [// | g s Ih] /=.
have Ih' := @out_left_add_event (right_pt g) g true _ erefl Ih.
by have Ih'' := @out_left_add_event (left_pt g) g false _ erefl Ih'.
Qed.

Lemma add_event_point_subset (s : mem_pred pt) p g b evs :
  {subset ([seq point ev | ev <- evs] : seq pt) <= s} ->
  p \in s ->
  {subset ([seq point ev | ev <- add_event p g b evs] : seq pt) <= s}.
Proof.
elim: evs => [ | ev evs Ih].
  by move=> _ pin /=; case: ifP => /= bval p'; rewrite inE=> /eqP ->.
move=> cnd pin.
  have cnd' : {subset ([seq point ev' | ev' <- evs] : seq pt) <= s}.
  by move=> p' p'in; apply: cnd; rewrite inE p'in orbT.
have Ih' := Ih cnd' pin; clear Ih.
have evin : point ev \in s by apply: cnd; rewrite !inE eqxx.
rewrite /=; (repeat (case: ifP=> _))=> p'; rewrite /= !inE;
  (repeat(move=>/orP[])); try solve[move=> /eqP -> // | by apply: cnd'].
apply: Ih'.
Qed.

Lemma edges_to_events_subset (s : mem_pred pt) (gs : seq edge) :
  {subset [seq left_pt g | g <- gs] <= s} ->
  {subset [seq right_pt g | g <- gs] <= s} ->
  {subset ([seq point ev | ev <- edges_to_events gs] : seq pt) <= s}.
Proof.
elim: gs => [// | g gs Ih].
rewrite /=.
move=> cndl cndr.
have cndl' : {subset [seq left_pt g | g <- gs] <= s}.
  by move=> x xin; apply: cndl; rewrite inE xin orbT.
have cndr' : {subset [seq right_pt g | g <- gs] <= s}.
  by move=> x xin; apply: cndr; rewrite inE xin orbT.
have cndleft : left_pt g \in s by apply: cndl; rewrite inE eqxx.
have cndright : right_pt g \in s by apply: cndr; rewrite inE eqxx.
have Ih' := Ih cndl' cndr'; clear Ih.
by apply: add_event_point_subset;[apply: add_event_point_subset | ].
Qed.

End working_environment.
