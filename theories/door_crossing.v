From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_real_closed reals.
From mathcomp.algebra_tactics Require Import ring lra.
Require Import casteljau convex counterclockwise intersection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory.
Import Num.Theory Num.Def.
Local Open Scope ring_scope.

Section sandbox.

Lemma poly_coord {R : rcfType} 
  (c : (R^o * R^o)%type)
  (p : {poly R}) (t : R) :
  p.[t] *: c = c.1 * p.[t] *: (1, 0) + c.2 * p.[t] *: (0, 1).
Proof.
congr (_, _); rewrite /= !scaler0 ?addr0 ?add0r mulrC /GRing.scale /=; ring.
Qed.

  
Variable R : reals.Real.type.

(* This version differs from the one in the hulls development to avoid
  using Program Fixpoint. Here the sequence of control point is given
  by a function and the degree is given as argument. *)
Fixpoint bezier (c : nat -> Plane R) (n : nat) (t : R) :=
  match n with
  | 0 => c 0%N
  | S p => (1 - t) *: (bezier c p t) +
           t *: (bezier (c \o S) p t)
  end.

Definition f3pt (a b c : Plane R) :=
  [fun n : nat => a with 1%nat |-> b, 2%nat |-> c].

Lemma bezier_step_conv c n t :
  bezier c (S n) t =
  bezier (c \o S) n t <| t |> bezier c n t.
Proof. by rewrite /= /conv addrC. Qed.

(* TODO: complain about the wrong error message for the following mistake. *)
(* Lemma bezier_bernstein2 c t :
  bezier c 2 t =  (bernp 0 1 2 0) *: c 0%N. *)

Lemma bezier_bernstein2 c t :
  bezier c 2 t = 
    \sum_(i < 3) (bernp 0 1 2 i).[t] *: c i.
Proof.
rewrite !big_ord_recr big_ord0 /= add0r.
rewrite /= scalerDr scalerA -!addrA; congr (_ *: _ + _).
  by rewrite /bernp !hornerE /= subr0 expr1n invr1; ring.
rewrite !(scalerA, scalerDr) addrA -scalerDl; congr (_ *:_ + _ *: _).
  by rewrite /bernp !hornerE /= subr0 expr1n invr1; ring.
by rewrite /bernp !hornerE /= subr0 expr1n invr1; ring.
Qed.

(* The proofs of these lemmas follow a general pattern explained in file
  casteljau.  However, here, we can brute force the proof because we are
  working with a known low degree. *)
Lemma bezier2_dichotomy_l (c : nat -> Plane R) (t u : R) :
  bezier c 2 (t * u) =
  bezier (f3pt (c 0%nat) (bezier c 1 u) (bezier c 2 u)) 2 t.
Proof.
rewrite /bezier /= !scalerDr !scalerA !addrA.
(* Make sure all instance of c 0 are grouped on the left and c 0 is
   factored out. *)
rewrite !(addrAC _ (_ *: c (S O)) (_ *: c O)) -!scalerDl.
rewrite -!addrA; congr (_ *: _ + _); first by ring.
(* Now factor out all instances of c 1. *)
rewrite !addrA -!scalerDl; congr (_ *: _ + _ *: _); ring.
Qed.

Lemma bezier2_dichotomy_r (c : nat -> Plane R) (t u : R) :
  bezier c 2 (u + t * (1 - u)) =
  bezier (f3pt (bezier c 2 u) (bezier (c \o S) 1 u) (c 2%nat)) 2 t.
Proof.
rewrite /bezier /= !scalerDr !scalerA !addrA.
(* There is only one instance of c 0 on the left, we can process it directly *)
rewrite -!addrA; congr (_ *: _ + _); first by ring.
rewrite !addrA -!scalerDl.
rewrite !(addrAC _ (_ *: c (S (S _))) (_ *: c (S O))) -!scalerDl.
rewrite -!addrA -!scalerDl.
congr (_ *: _ + _ *: _); ring.
Qed.

Record edge := Bedge 
  { left_pt : Plane R;
    right_pt : Plane R; 
    edge_cond : left_pt.1 < right_pt.1}.

Record cell :=
  { left_pts : seq (Plane R);
    right_pts : seq (Plane R);
    low : edge; high : edge}.

Definition valid_edge : edge -> Plane R -> bool :=
  fun g p => (left_pt g).1 <= p.1 <= (right_pt g).1.

Definition point_on_edge (p : Plane R) (g : edge) :=
  valid_edge g p && (det (left_pt g) (right_pt g) p == 0).

Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).

Definition dummy_pt : Plane R := (0, 0).

Definition closed_cell_side_limit_ok c :=
 [&& left_pts c != [::],
   all (fun p => p.1 == (last dummy_pt (left_pts c)).1) (left_pts c),
   sorted >%R [seq p.2 | p <- left_pts c],
   head dummy_pt (left_pts c) === high c,
   last dummy_pt (left_pts c) === low c,
    right_pts c != [::],
   all (fun p => p.1 == (head dummy_pt (right_pts c)).1) (right_pts c),
   sorted <%R [seq p.2 | p <- right_pts c],
   head dummy_pt (right_pts c) === low c &
   last dummy_pt (right_pts c) === high c].

Definition left_limit (c : cell) := (last dummy_pt (left_pts c)).1.

Definition right_limit c := (last dummy_pt (right_pts c)).1.

Definition point_under_edge (p : Plane R) (e : edge) : bool :=
  det p (left_pt e) (right_pt e) <= 0.

  (* returns true if p is strictly under e *)
Definition point_strictly_under_edge (p : Plane R) (e : edge) : bool :=
  det p (left_pt e) (right_pt e) < 0.

Notation "p '<<=' e" := (point_under_edge p e)( at level 70, no associativity).
Notation "p '<<<' e" := (point_strictly_under_edge p e)
       (at level 70, no associativity).

Definition strict_inside_closed (p : Plane R) (c : cell) :=
  (p <<< high c) && (~~(p <<= low c)) &&
  (left_limit c < p.1 < right_limit c).

Definition bottom_left_corner (c : cell) := last dummy_pt (left_pts c).

Record vert_edge := { ve_x : R; ve_top : R; ve_bot : R}.

Definition vert_edge_eqb (v1 v2 : vert_edge) :=
  let: Build_vert_edge v1x v1t v1b := v1 in
  let: Build_vert_edge v2x v2t v2b := v2 in
  (v1x == v2x) && (v1t == v2t) && (v1b == v2b).

Lemma vert_edge_eqP : Equality.axiom vert_edge_eqb.
Proof.
move=> [vxa vta vba] [vxb vtb vbb] /=.
have [/eqP <-|/eqP anb] := boolP(vxa == vxb).
  have [/eqP <-|/eqP anb] := boolP(vta == vtb).
    have [/eqP <-| /eqP anb] := boolP(vba == vbb).
      by apply:ReflectT.
    by apply: ReflectF=> [] [].
  by apply: ReflectF=> [] [].
by apply: ReflectF=> [] [].
Qed.

Fail Check (fun (x : vert_edge) (l : seq vert_edge) => x \in l).

HB.instance Definition _ := hasDecEq.Build _ vert_edge_eqP.

Fixpoint seq_to_intervals_aux [A : Type] (a : A) (s : seq A) :=
match s with
| nil => nil
| b :: tl => (a, b) :: seq_to_intervals_aux b tl
end.

Definition seq_to_intervals [A : Type] (s : seq A) :=
match s with
  nil => nil
| a :: tl => seq_to_intervals_aux a tl
end.

Definition cell_safe_exits_left (c : cell) : seq vert_edge :=
  let lx := (seq.head dummy_pt (left_pts c)).1 in
  map (fun p => Build_vert_edge lx (p.1).2 (p.2).2) 
   (seq_to_intervals (left_pts c)).

Definition cell_safe_exits_right (c : cell) : seq vert_edge :=
  let lx := (seq.head dummy_pt (right_pts c)).1 in
  map (fun p => Build_vert_edge lx (p.1).2 (p.2).2) 
   (seq_to_intervals (rev (right_pts c))).

Definition dummy_vert_edge :=
  {| ve_x := 0; ve_top := 0; ve_bot := 0|}.

Definition on_vert_edge (p : Plane R) (v : vert_edge) : bool :=
  (p.1 == ve_x v) && (ve_bot v < p.2 < ve_top v).

Check fun (v : vert_edge) (l : seq vert_edge) => v \in l.
Check fun (v : vert_edge)(c : cell) => 
   v \in cell_safe_exits_left c.

Lemma detDM2 (l p1 p2 q1 q2 r1 r2 : R) :
  l * det (p1, p2) (q1, q2) (r1, r2) =
  det (p1, p2) (p1 + l * (q1 - p1), p2 + l * (q2 - p2)) (r1, r2).
Proof. by rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma detDM1 (l p1 p2 q1 q2 r1 r2 : R) :
  l * det (p1, p2) (q1, q2) (r1, r2) =
  det (q1 + l * (p1 - q1), q2 + l * (p2 - q2)) (q1, q2) (r1, r2).
Proof. by rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma detDM3 (l p1 p2 q1 q2 r1 r2 : R) :
det (p1, p2) (q1, q2) (r1, r2) =
det (p1, p2) (q1, q2) (r1 + l * (q1 - p1), r2 + l * (q2 - p2)).
Proof. by rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma detVert (p1 p2 q1 q2 r2 : R) :
  det (p1, p2) (q1, q2) (q1, r2) =
   (r2 - q2) * (q1 - p1).
Proof. rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma bezier1_conv c t : bezier c 1 t = c 0%nat <| (1 - t) |> c 1%nat.
Proof.  rewrite /= /conv; congr (_ *: _ + _ *: _); ring. Qed.

Lemma left_vertical_edge_wrt_high c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_left c ->
  (ve_top v <= (head dummy_pt (left_pts c)).2) &&
  ((left_pt (high c)).1 <= ve_x v < (right_pt (high c)).1) &&
  (ve_x v == (head dummy_pt (left_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl.
move=> /andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have {}samexl :
   {in left_pts c, forall p, (head dummy_pt (left_pts c)).1 = p.1 }.
  move=> x xin; rewrite (eqP (samexl x xin)).
  rewrite -(eqP (samexl (head dummy_pt (left_pts c)) _)) //.
  by move: leftn0; case (left_pts c)=> //= s l _; rewrite inE eqxx.
have vxleft : ve_x v = left_limit c.
  move: vin.
  rewrite /left_limit /cell_safe_exits_left.
  elim: (left_pts c) leftn0 samexl => [ // | e1 [// | e2 tl] Ih] _ /= samexl.
  rewrite inE=> /orP[/eqP -> /= | vin].
    by apply: samexl; rewrite inE mem_last orbT.
  apply: (Ih isT)=> /=.
     move=> x xin. rewrite -(samexl e2); last by rewrite !inE eqxx orbT.
     by apply: samexl; rewrite inE xin orbT.
  by rewrite -(samexl e2) //; rewrite !inE eqxx orbT.
apply/andP; split; last first.
  rewrite vxleft /left_limit (samexl (last dummy_pt (left_pts c))) //.
  by case: (left_pts c) leftn0=> [// | ? ?]; rewrite /= mem_last.
move: llr.
rewrite vxleft /left_limit -(samexl (last dummy_pt (left_pts c))); last first.
   by case: (left_pts c) leftn0 => //= a tl _ ; rewrite mem_last.
move: lonh=> /andP[] /andP[] -> /= _ _ llr.
rewrite (lt_le_trans llr) ?andbT; last first.
  by rewrite /right_limit; move: ronh=> /andP[] /andP[] _ ->.
move: vin; rewrite /cell_safe_exits_left.
elim: (left_pts c) leftn0 sortl samexl
  => [// | e1 [ // | e2 tl] /(_ isT) Ih] _ /= /andP[] cmp s samexl.
rewrite inE=> /orP[/eqP -> // | vin ].
apply: (le_trans _ (ltW cmp)).
apply Ih=> //=.
  move=> x xin.
  by rewrite -(samexl e2) ?inE ?eqxx ?orbT // (samexl x) // inE xin orbT.
by rewrite -(samexl e2) // !inE eqxx orbT.
Qed.

Lemma seq_to_intervals_rcons [A : Type](e1 e2 : A) l :
  seq_to_intervals (rcons (rcons l e2) e1) =
  rcons (seq_to_intervals (rcons l e2)) (e2, e1).
Proof. by elim: l => [// | e3 [// | e4 l] /= Ih] //; rewrite Ih. Qed.

Lemma right_vertical_edge_wrt_high c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_right c ->
  (ve_top v <= (last dummy_pt (right_pts c)).2) &&
  ((left_pt (high c)).1 < ve_x v <= (right_pt (high c)).1) &&
  (ve_x v == (last dummy_pt (right_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl.
move=>/andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have vxright : ve_x v = right_limit c.
  move: vin.
  rewrite /right_limit /cell_safe_exits_right.
  elim/last_ind: (right_pts c) rightn0 samexr => [ // | lh e1 Ih] _ /=.
  elim/last_ind: lh Ih => [ // | lh e2 _] Ih samexr.
  rewrite last_rcons !rev_rcons/=.
  rewrite inE=> /orP[/eqP -> /= | vin]. 
    by rewrite (eqP (samexr e1 _)) // mem_rcons inE eqxx.
  rewrite (eqP (samexr e1 _)); last by rewrite mem_rcons inE eqxx.
  rewrite -(eqP (samexr e2 _)); last by rewrite !(mem_rcons, inE) eqxx ?orbT.
  rewrite [e2](_ : _ = last dummy_pt (rcons lh e2)); last by rewrite last_rcons.
  apply: Ih=> /=.
      by case lhq: lh.
     move=> x xin.
     rewrite (eqP (samexr x _)); last by rewrite mem_rcons inE xin orbT.
     by rewrite 3!headI /=.
  rewrite
   [head _ (rcons _ _)](_ : _ = head dummy_pt (rcons lh e2)) in vin; last first.
    by rewrite 3!headI /=.
  by rewrite rev_rcons; apply: vin.
apply/andP; split; last by rewrite vxright.
move: llr.
rewrite vxright /right_limit.
move: ronh=> /andP[] /andP[] _ -> /= _ llr.
rewrite (le_lt_trans _ llr) ?andbT; last first.
  rewrite /left_limit; move: lonh=> /andP[] /andP[] + _ _.
  rewrite (eqP (samexl (head dummy_pt (left_pts c)) _)) //.
  by case: (left_pts c) leftn0 => [// | a ?]; rewrite /= inE eqxx.
move: vin; rewrite /cell_safe_exits_right.
elim/last_ind: (right_pts c) rightn0 sortr samexr=> [// | + e1 ].
elim/last_ind=> [// | l e2 _] Ih _ sortr samexr.
rewrite 2!rev_rcons /= inE last_rcons=> /orP[/eqP -> | vin]; first by [].
have cmp : e2.2 < e1.2.
  move: sortr; rewrite -2!cats1 -catA /= map_cat=> /cat_sorted2[_ /=].
  by rewrite andbT.
have {}sortr : sorted <%R [seq p.2 | p <- rcons l e2].
  by move: sortr; rewrite -cats1 map_cat=> /cat_sorted2[].
apply: (le_trans _ (ltW cmp)).
rewrite [e2](_ : _ = last dummy_pt (rcons l e2)); last by rewrite last_rcons.
apply Ih=> //=.
   by case lq : l.
  move=> x xin.
  have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
    by case lq : l.
  by apply: samexr; rewrite mem_rcons inE xin orbT.
have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
  by case lq : l.
by rewrite rev_rcons.
Qed.

Lemma left_vertical_edge_wrt_low c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_left c ->
  ((last dummy_pt (left_pts c)).2 <= ve_bot v) &&
  ((left_pt (low c)).1 <= ve_x v < (right_pt (low c)).1) &&
  (ve_x v == (last dummy_pt (left_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl.
move=>/andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have {}samexl: {in left_pts c, forall p, (head dummy_pt (left_pts c)).1 = p.1 }.
  move=> x xin; rewrite (eqP (samexl x xin)).
  rewrite -(eqP (samexl (head dummy_pt (left_pts c)) _)) //.
  by move: leftn0; case (left_pts c)=> //= s l _; rewrite inE eqxx.
have vxleft : ve_x v = left_limit c.
  move: vin.
  rewrite /left_limit /cell_safe_exits_left.
  elim: (left_pts c) leftn0 samexl => [ // | e1 [// | e2 tl] Ih] _ /= samexl.
  rewrite inE=> /orP[/eqP -> /= | vin].
    by apply: samexl; rewrite inE mem_last orbT.
  apply: (Ih isT)=> /=.
     move=> x xin. rewrite -(samexl e2); last by rewrite !inE eqxx orbT.
     by apply: samexl; rewrite inE xin orbT.
  by rewrite -(samexl e2) //; rewrite !inE eqxx orbT.
apply/andP; split; last by rewrite vxleft.
move: llr.
rewrite vxleft /left_limit.
move: lonl=> /andP[] /andP[] -> /= _ _ llr.
rewrite (lt_le_trans llr) ?andbT; last first.
  rewrite /right_limit; move: ronl=> /andP[] /andP[] _ + _.
  rewrite -(eqP (samexr (last dummy_pt (right_pts c)) _)) //.
  by move: rightn0; case: (right_pts c)=> [// | ? ?]; rewrite /= mem_last.
move: vin; rewrite /cell_safe_exits_left.
elim: (left_pts c) leftn0 sortl samexl
  => [// | e1 [ // | e2 tl] /(_ isT) Ih] _ /= /andP[] cmp s samexl.
rewrite inE=> /orP[/eqP -> /= | vin ].
  have sgt : subrel >%R (>=%R : rel R) by move=> x y /ltW.
  have s' : path >=%R e2.2 [seq p.2 | p <- tl].
    by apply: (sub_path sgt).
  case tlq : tl => [// | e3 tl']; rewrite -tlq.
  move: s'; rewrite path_sortedE; last by apply/rev_trans/le_trans.
  move=> /andP[] /allP /(_ (last e2 tl).2) + _; apply.
  by apply/mapP; exists (last e2 tl); rewrite // tlq /= mem_last.
apply Ih=> //=.
  move=> x xin.
  by rewrite -(samexl e2) ?inE ?eqxx ?orbT // (samexl x) // inE xin orbT.
by rewrite -(samexl e2) // !inE eqxx orbT.
Qed.

Lemma right_vertical_edge_wrt_low c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_right c ->
  ((head dummy_pt (right_pts c)).2 <= ve_bot v) &&
  ((left_pt (low c)).1 < ve_x v <= (right_pt (low c)).1) &&
  (ve_x v == (head dummy_pt (right_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl.
move=>/andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have vxright : ve_x v = right_limit c.
  move: vin.
  rewrite /right_limit /cell_safe_exits_right.
  elim/last_ind: (right_pts c) rightn0 samexr => [ // | lh e1 Ih] _ /=.
  elim/last_ind: lh Ih => [ // | lh e2 _] Ih samexr.
  rewrite last_rcons !rev_rcons/=.
  rewrite inE=> /orP[/eqP -> /= | vin]. 
    by rewrite (eqP (samexr e1 _)) // mem_rcons inE eqxx.
  rewrite (eqP (samexr e1 _)); last by rewrite mem_rcons inE eqxx.
  rewrite -(eqP (samexr e2 _)); last by rewrite !(mem_rcons, inE) eqxx ?orbT.
  rewrite [e2](_ : _ = last dummy_pt (rcons lh e2)); last by rewrite last_rcons.
  apply: Ih=> /=.
      by case lhq: lh.
     move=> x xin.
     rewrite (eqP (samexr x _)); last by rewrite mem_rcons inE xin orbT.
     by rewrite 3!headI /=.
  rewrite [head _ (rcons _ _)]
    (_ : _ = head dummy_pt (rcons lh e2)) in vin; last first.
    by rewrite 3!headI /=.
  by rewrite rev_rcons; apply: vin.
apply/andP; split; last first.
  rewrite vxright /right_limit; apply: samexr.
  by case: (right_pts c) rightn0=> [// | ? ?]; rewrite /= mem_last.
move: llr.
rewrite vxright /right_limit.
move: ronl=> /andP[] /andP[] _ + _ /=.
rewrite -(eqP (samexr (last dummy_pt (right_pts c)) _)); last first.
  by case: (right_pts c) rightn0 => [// | ? ?]; rewrite /= mem_last.
move=> -> xcond; rewrite ?andbT.
rewrite (le_lt_trans _ xcond) ?andbT; last by move: lonl=> /andP[] /andP[].
move: vin; rewrite /cell_safe_exits_right.
elim/last_ind: (right_pts c) rightn0 sortr samexr=> [// | + e1 ].
elim/last_ind=> [// | l e2 _] Ih _ sortr samexr.
have cmp : e2.2 < e1.2.
  move: sortr; rewrite -2!cats1 -catA /= map_cat=> /cat_sorted2[_ /=].
  by rewrite andbT.
have {}sortr : sorted <%R [seq p.2 | p <- rcons l e2].
  by move: sortr; rewrite -cats1 map_cat=> /cat_sorted2[].
rewrite [head dummy_pt _](_ : _ = head e2 l); last by rewrite 2!headI /=.
rewrite 2!rev_rcons /= inE => /orP[/eqP -> /= | vin].
  case lq : l => [// | e3 l'] /=.
  move: sortr; rewrite lq /= => /(sub_path ltW).
  rewrite (path_sortedE le_trans)=> /andP[] /allP + _; apply.
  by apply/mapP; exists e2; rewrite // mem_rcons inE eqxx.
rewrite [X in X.2 <= _](_ : _ = head dummy_pt (rcons l e2)); last first.
  by case lq: l.
apply Ih=> //=.
   by case lq : l.
  move=> x xin.
  have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
    by case lq : l.
  by apply: samexr; rewrite mem_rcons inE xin orbT.
have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
  by case lq : l.
by rewrite rev_rcons 2!headI /=.
Qed.
  
Lemma vert_projr (p q r : Plane R) : 
  p.1 != q.1 -> (det p q r == 0) =
  (r.2 == q.2 + (r.1 - q.1) / (q.1 - p.1) * (q.2 - p.2)).
Proof.
case: p q r=> [p1 p2][q1 q2][r1 r2] /=; rewrite develop_det /= => e_cnd.
apply/idP/eqP; last first.
  move=> -> /=; rewrite !mulrDl -(opprB q1 p1) !mulrN (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  rewrite (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  apply/eqP; ring.
rewrite !(addrAC _ (- (r2 * (p1 - q1)))) subr_eq0 eq_sym => /eqP r2Mdf.
have dn0 : (p1 - q1) != 0 by rewrite subr_eq0.
apply: (mulIf dn0); rewrite r2Mdf mulrDl (mulrAC _ _ (p1 - q1)) -(opprB p1 q1).
rewrite invrN !(mulrN, mulNr).
rewrite mulfVK //; ring.
Qed.

Lemma vert_projl (p q r : Plane R) : 
  p.1 != q.1 -> (det p q r == 0) =
  (r.2 == p.2 + (r.1 - p.1) / (q.1 - p.1) * (q.2 - p.2)).
Proof.
case: p q r=> [p1 p2][q1 q2][r1 r2] /=; rewrite develop_det /= => e_cnd.
apply/idP/eqP; last first.
  move=> -> /=; rewrite !mulrDl -(opprB q1 p1) !mulrN (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  rewrite (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  apply/eqP; ring.
rewrite !(addrAC _ (- (r2 * (p1 - q1)))) subr_eq0 eq_sym => /eqP r2Mdf.
have dn0 : (p1 - q1) != 0 by rewrite subr_eq0.
apply: (mulIf dn0); rewrite r2Mdf mulrDl (mulrAC _ _ (p1 - q1)) -(opprB p1 q1).
rewrite invrN !(mulrN, mulNr).
rewrite mulfVK //; ring.
Qed.

Lemma on_vert_edge_under_high_left v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_left c ->
  p <<< high c.
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] :=
   left_vertical_edge_wrt_high llr cok vin.
move: (cok)=> /andP[] leftn0 /andP[] samexl /andP[] sortl /andP[] lonh _.
rewrite /point_strictly_under_edge.
set l := ((right_pt (high c)).1 - p.1) /
            ((right_pt (high c)).1 - (left_pt (high c)).1).
set q := ((right_pt (high c)).1 - l * 
             ((right_pt (high c)).1 - (left_pt (high c)).1),
        (right_pt (high c)).1 - l * 
           ((right_pt (high c)).2 - (left_pt (high c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (high c)) => [q1 q2].
case rq : (right_pt (high c)) => [r1 r2].
have lv : l = (r1 - p1) / (r1 - q1) by rewrite /l pq rq lq /=.
have p1ltr1 : p1 < r1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (high c)); rewrite lq rq.
rewrite det_cyclique.
rewrite -(pmulr_rlt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = r1 + l * (q1 - r1).
  rewrite lv -(opprB r1 q1) mulrN mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (high c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite nmulr_llt0; last by rewrite subr_lt0.
have proj2: (head dummy_pt (left_pts c)).2 =
               r2 + (r1 - p1) / (r1 - q1) * (q2 - r2).
  have ecnd : (left_pt (high c)).1 != (right_pt (high c)).1.
    by apply/eqP=> abs; have := edge_cond (high c); rewrite abs lt_irreflexive.
  have := vert_projr (head dummy_pt (left_pts c)) ecnd.
  move: lonh=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_gt0.
apply: lt_le_trans vtople.
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma on_vert_edge_above_low_left v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_left c ->
  ~~ (p <<= low c).
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] :=
  left_vertical_edge_wrt_low llr cok vin.
move: (cok)=> /andP[] leftn0 /andP[] samexl /andP[] sortl.
move=>/andP[] _ /andP[] lonl _.
rewrite /point_under_edge -ltNge.
set l := ((right_pt (low c)).1 - p.1) / ((right_pt (low c)).1 - (left_pt (low c)).1).
set q := ((right_pt (low c)).1 - l * ((right_pt (low c)).1 - (left_pt (low c)).1),
        (right_pt (low c)).1 - l * ((right_pt (low c)).2 - (left_pt (low c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (low c)) => [q1 q2].
case rq : (right_pt (low c)) => [r1 r2].
have lv : l = (r1 - p1) / (r1 - q1) by rewrite /l pq rq lq /=.
have p1ltr1 : p1 < r1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (low c)); rewrite lq rq.
rewrite det_cyclique.
rewrite -(pmulr_rgt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = r1 + l * (q1 - r1).
  rewrite lv -(opprB r1 q1) mulrN mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (low c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite nmulr_lgt0; last by rewrite subr_lt0.
have proj2: (last dummy_pt (left_pts c)).2 = r2 + (r1 - p1) / (r1 - q1) * (q2 - r2).
  have ecnd : (left_pt (low c)).1 != (right_pt (low c)).1.
    by apply/eqP=> abs; have := edge_cond (low c); rewrite abs lt_irreflexive.
  have := vert_projr (last dummy_pt (left_pts c)) ecnd.
  move: lonl=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_lt0.
apply: (le_lt_trans vtople).
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma on_vert_edge_under_high_right v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_right c ->
  p <<< high c.
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] := right_vertical_edge_wrt_high llr cok vin.
move: (cok); rewrite /closed_cell_side_limit_ok.
rewrite 4!andbA=> /andP[] _.
move=> /andP[] rightn0 /andP[] samexr /andP[] sortr /andP[] _ ronh.
rewrite /point_strictly_under_edge.
set l := (p.1 - (left_pt (high c)).1) / ((right_pt (high c)).1 - (left_pt (high c)).1).
set q := ((left_pt (high c)).1 + l * ((right_pt (high c)).1 - (left_pt (high c)).1),
        (left_pt (high c)).1 + l * ((right_pt (high c)).2 - (left_pt (high c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (high c)) => [q1 q2].
case rq : (right_pt (high c)) => [r1 r2].
have lv : l = (p1 - q1) / (r1 - q1) by rewrite /l pq rq lq /=.
have q1ltp1 : q1 < p1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (high c)); rewrite lq rq.
rewrite det_inverse det_cyclique oppr_lt0.
rewrite -(pmulr_rgt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = q1 + l * (r1 - q1).
  rewrite lv mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (high c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite pmulr_lgt0; last by rewrite subr_gt0.
have proj2: (last dummy_pt (right_pts c)).2 = q2 + (p1 - q1) / (r1 - q1) * (r2 - q2).
  have ecnd : (left_pt (high c)).1 != (right_pt (high c)).1.
    by apply/eqP=> abs; have := edge_cond (high c); rewrite abs lt_irreflexive.
  have := vert_projl (last dummy_pt (right_pts c)) ecnd.
  move: ronh=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_gt0.
apply: lt_le_trans vtople.
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma on_vert_edge_above_low_right v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_right c ->
  ~~ (p <<= low c).
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] := right_vertical_edge_wrt_low llr cok vin.
move: (cok); rewrite /closed_cell_side_limit_ok.
rewrite 4!andbA=> /andP[] _.
move=> /andP[] rightn0 /andP[] samexr /andP[] sortr /andP[] ronl _.
rewrite /point_under_edge -ltNge.
set l := (p.1 - (left_pt (low c)).1) / ((right_pt (low c)).1 - (left_pt (low c)).1).
set q := ((left_pt (low c)).1 + l * ((right_pt (low c)).1 - (left_pt (low c)).1),
        (left_pt (low c)).1 + l * ((right_pt (low c)).2 - (left_pt (low c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (low c)) => [q1 q2].
case rq : (right_pt (low c)) => [r1 r2].
have lv : l = (p1 - q1) / (r1 - q1) by rewrite /l pq rq lq /=.
have q1ltp1 : q1 < p1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (low c)); rewrite lq rq.
rewrite det_inverse det_cyclique oppr_gt0.
rewrite -(pmulr_rlt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = q1 + l * (r1 - q1).
  rewrite lv mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (low c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite pmulr_llt0; last by rewrite subr_gt0.
have proj2: (head dummy_pt (right_pts c)).2 = q2 + (p1 - q1) / (r1 - q1) * (r2 - q2).
  have ecnd : (left_pt (low c)).1 != (right_pt (low c)).1.
    by apply/eqP=> abs; have := edge_cond (low c); rewrite abs lt_irreflexive.
  have := vert_projl (head dummy_pt (right_pts c)) ecnd.
  move: ronl=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_lt0.
apply: (le_lt_trans vtople).
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma conv_num_sg s (a b t : R) :
   0 < t < 1 -> sgz a = s -> sgz b = s -> sgz ((a : R^o) <| t |> b) = s.
Proof.
move=> tint.
have [ -> <- | agt0 <- | alt0 <-] := sgzP a.
    have [ -> | // | // ] := sgzP b.
    by rewrite convmm sgz0.
  have [ // | bgt0 _ | // ] := sgzP b.
  rewrite /conv; apply/gtr0_sgz/addr_gt0; apply/mulr_gt0; lra.
have [ // | // | blt0 _] := sgzP b.
rewrite /conv; apply/ltr0_sgz; rewrite -oppr_gt0 opprD.
apply/addr_gt0; rewrite -mulrN; apply/mulr_gt0; lra.
Qed.

Lemma conv_num_gtl (a b t c : R) :
  0 < t < 1 -> c < a -> c <= b -> c < (a : R^o) <| t |> b.
Proof.
move=> tint clta cleb; rewrite /conv.
rewrite -[_ *: (a : R^o)]/(t * a).
rewrite -[_ *: (b : R^o)]/((1 - t) * b).
rewrite [X in _ < X]
  (_ : _ = c + ((t * (a - c)) + (1 - t) * (b - c))); last by ring.
have fact1 : 0 < t * (a - c) by apply: mulr_gt0; lra.
have fact2 : 0 <= (1 - t) * (b - c) by apply: mulr_ge0; lra.
lra.
Qed.

Lemma conv_num_ltr (a b t c : R) :
  0 < t < 1 -> a < c -> b <= c -> (a : R^o) <| t |> b < c.
Proof.
move=> tint clta cleb; rewrite /conv.
rewrite -[_ *: (a : R^o)]/(t * a).
rewrite -[_ *: (b : R^o)]/((1 - t) * b).
rewrite [X in X < _]
  (_ : _ = c - ((t * (c - a)) + (1 - t) * (c - b))); last by ring.
have fact1 : 0 < t * (c - a) by apply: mulr_gt0; lra.
have fact2 : 0 <= (1 - t) * (c - b) by apply: mulr_ge0; lra.
lra.
Qed.

Lemma conv_p1 (a b : Plane R) t : (a <| t |> b).1 =
   ((a.1 : R^o) <| t |> b.1).
Proof.  by []. Qed.

Lemma safe_bezier2 p1 p2 p3 c1 c2 vert_e u :
  closed_cell_side_limit_ok c1 ->
  closed_cell_side_limit_ok c2 ->
  strict_inside_closed p1 c1 ->
  strict_inside_closed p3 c2 ->
  vert_e \in cell_safe_exits_right c1 ->
  vert_e \in cell_safe_exits_left c2 ->
  on_vert_edge p2 vert_e ->
  0 < u < 1 ->
  on_vert_edge (bezier (f3pt p1 p2 p3) 2 u) vert_e ->
  forall t, 0 <= t <= 1 ->
    let bzt := bezier (f3pt p1 p2 p3) 2 t in
    (strict_inside_closed bzt c1) ||
    (strict_inside_closed bzt c2) ||
    on_vert_edge bzt vert_e.
Proof.
move=> ok1 ok2 p1in p3in v1 v2 p2in uin bzuin t tin.
have un0 : u != 0 by apply: lt0r_neq0; case/andP: uin.
set bzt := bezier _ 2 t; lazy zeta.
have [tu | nut] := eqVneq t u; first by rewrite /bzt tu bzuin !orbT.
have llr1 : left_limit c1 < right_limit c1.
  by move: p1in=> /andP[] _ /andP[]; apply: lt_trans.
have llr2 : left_limit c2 < right_limit c2.
  by move: p3in=> /andP[] _ /andP[]; apply: lt_trans.
have p2belh1 : p2 <<< high c1.
  by apply: (on_vert_edge_under_high_right _ ok1 p2in v1).
have p2belh2 : p2 <<< high c2.
  by apply: (on_vert_edge_under_high_left _ ok2 p2in v2).
have p2abol1 : ~~(p2 <<= low c1).
  by apply: (on_vert_edge_above_low_right _ ok1 p2in v1).
have p2abol2 : ~~(p2 <<= low c2).
  by apply: (on_vert_edge_above_low_left _ ok2 p2in v2).
have bzubelh1 : bezier (f3pt p1 p2 p3) 2 u <<< high c1.
  by apply: (on_vert_edge_under_high_right _ ok1 bzuin v1).
have bzuabol1 : ~~(bezier (f3pt p1 p2 p3) 2 u <<= low c1).
  by apply: (on_vert_edge_above_low_right _ ok1 bzuin v1).
have bzubelh2 : bezier (f3pt p1 p2 p3) 2 u <<< high c2.
  by apply: (on_vert_edge_under_high_left _ ok2 bzuin v2).
have bzuabol2 : ~~(bezier (f3pt p1 p2 p3) 2 u <<= low c2).
  by apply: (on_vert_edge_above_low_left _ ok2 bzuin v2).
have [P1 | P2] := ltrP t u.
  apply/orP; left; apply/orP; left.
  set t' := t / u.
  have t'int : 0 <= t' < 1.
    apply/andP; split.
      rewrite /t'; apply divr_ge0; lra.
    rewrite /t' ltr_pdivr_mulr; lra.
  have tt' : t = t' * u by rewrite /t' mulfVK.
  have := bezier2_dichotomy_l (f3pt p1 p2 p3) t' u; rewrite -tt' /bzt => ->.
  set p2' := p2 <| u |> p1.
  set p3' := bezier (f3pt p1 p2 p3) 2 u.
  rewrite [bezier _ _ _](_ : _ = (p3' <| t' |> p2') <| t' |>
                                 (p2' <| t' |> p1)); last first.
    by rewrite !bezier_step_conv /= -/p2'.
  have [-> | t'n0] := eqVneq t' 0; first by rewrite !conv0.
  have t'int' : 0 < t' < 1 by lra.
  rewrite /strict_inside_closed -andbA; apply/andP; split.
    rewrite /point_strictly_under_edge !det_conv.
    have sgp1 : sgz (det p1 (left_pt (high c1)) (right_pt (high c1))) = -1.
      by apply:ltr0_sgz; move: p1in=> /andP[] /andP[].
    have sgp2' : sgz
             ((det p2 (left_pt (high c1)) (right_pt (high c1)) : R ^o) <|u|> 
             det p1 (left_pt (high c1)) (right_pt (high c1))) = -1.
      apply: conv_num_sg=> //.
      apply: ltr0_sgz; exact p2belh1.
    rewrite -sgz_lt0; set (tmp := sgz _); suff -> : tmp = -1 by [].
    rewrite {}/tmp; apply: conv_num_sg => //.
      apply: conv_num_sg=> //.
      apply: ltr0_sgz; exact bzubelh1.
    by apply: conv_num_sg.
  apply/andP; split.
    rewrite /point_under_edge -ltNge.
    rewrite !det_conv.
    have sgp1 : sgz (det p1 (left_pt (low c1)) (right_pt (low c1))) = 1.
       by apply:gtr0_sgz; move: p1in=> /andP[] /andP[] _; rewrite -ltNge.
    have sgp2' : sgz
             ((det p2 (left_pt (low c1)) (right_pt (low c1)) : R ^o) <|u|> 
             det p1 (left_pt (low c1)) (right_pt (low c1))) = 1.
      apply: conv_num_sg=> //.
      apply: gtr0_sgz; rewrite ltNge; exact p2abol1.
    rewrite -sgz_gt0; set (tmp := sgz _); suff -> : tmp = 1 by [].
    rewrite {}/tmp; apply: conv_num_sg => //.
      apply: conv_num_sg=> //.
      apply: gtr0_sgz; rewrite ltNge; exact bzuabol1.
    by apply: conv_num_sg.
  have vx1 : ve_x vert_e = right_limit c1.
    by have /andP[_ /eqP ->] := right_vertical_edge_wrt_high llr1 ok1 v1.
  have lp2' : left_limit c1 < p2'.1.
    rewrite conv_p1; apply: conv_num_gtl => //.
      move: p2in=> /andP[] /eqP -> _.
      by rewrite vx1.
    by apply: ltW; move: p1in=> /andP[] _ /andP[].
  apply/andP; split.
    rewrite conv_p1.
    apply: conv_num_gtl=> //.
      rewrite conv_p1.
      apply: conv_num_gtl=> //; last by apply: ltW.
      by move: bzuin; rewrite -/p3'=> /andP[] /eqP -> _; rewrite vx1.
    rewrite conv_p1; apply/ltW/conv_num_gtl=> //; apply/ltW.
    by move: p1in=> /andP[] _ /andP[].
  have p2'r : p2'.1 < right_limit c1.
    rewrite conv_p1 convC.
    apply: conv_num_ltr; first by lra.
      by move: p1in=> /andP[] _ /andP[].
    by move: p2in=> /andP[] /eqP -> _; rewrite vx1.
  apply: conv_num_ltr;[ done | | apply: ltW].
    rewrite conv_p1 convC; apply: conv_num_ltr => //; first by lra.
    by move: bzuin=> /andP[] /eqP -> _; rewrite vx1.
  apply: conv_num_ltr=> //; apply: ltW.
  by move: p1in=> /andP[] _ /andP[].
apply/orP; left; apply/orP; right.
have {P2}tgtu : u < t by lra.
set t' := (t - u) / (1 - u).
have tt' : t = u + t' * (1 - u) by rewrite /t' mulfVK; [ring | lra].
have := bezier2_dichotomy_r (f3pt p1 p2 p3) t' u; rewrite -tt' /bzt => ->.
have [t1 | tn1] := eqVneq t 1.
  rewrite /t' /= t1 divff; last by lra.
 by rewrite subrr !(scale0r, add0r, addr0, scale1r).
have t'int : 0 < t' < 1.
  rewrite /t'; apply/andP; split.
    apply: divr_gt0; lra.
  by rewrite ltr_pdivr_mulr; lra.
set p1' := bezier (f3pt p1 p2 p3) 2 u.
set p2' := p3 <| u |> p2.
rewrite [bezier _ 2 _](_ : _ = (p3 <| t' |> p2') <| t' |> (p2' <| t' |> p1'));
  last first.
  by rewrite !bezier_step_conv.
rewrite /strict_inside_closed -andbA; apply/andP; split.
rewrite /point_strictly_under_edge !det_conv.
  have sgp3 : sgz (det p3 (left_pt (high c2)) (right_pt (high c2))) = -1.
    by apply:ltr0_sgz; move: p3in=> /andP[] /andP[].
  have sgp2' : sgz
           ((det p3 (left_pt (high c2)) (right_pt (high c2)) : R ^o) <|u|> 
             det p2 (left_pt (high c2)) (right_pt (high c2))) = -1.
    apply: conv_num_sg=> //.
    apply: ltr0_sgz; exact p2belh2.
  rewrite -sgz_lt0; set (tmp := sgz _); suff -> : tmp = -1 by [].
  rewrite {}/tmp; apply: conv_num_sg => //.
    by apply: conv_num_sg.
  apply: conv_num_sg=> //.
  apply: ltr0_sgz; exact bzubelh2.
apply/andP; split.
  rewrite /point_under_edge -ltNge.
  rewrite !det_conv.
  have sgp3 : sgz (det p3 (left_pt (low c2)) (right_pt (low c2))) = 1.
     by apply: gtr0_sgz; move: p3in=> /andP[] /andP[] _; rewrite -ltNge.
  have sgp2' : sgz
             ((det p3 (left_pt (low c2)) (right_pt (low c2)) : R ^o) <|u|> 
             det p2 (left_pt (low c2)) (right_pt (low c2))) = 1.
    apply: conv_num_sg=> //.
    by apply: gtr0_sgz; rewrite ltNge; exact p2abol2.
  rewrite -sgz_gt0; set (tmp := sgz _); suff -> : tmp = 1 by [].
  rewrite {}/tmp; apply: conv_num_sg => //.
    by apply: conv_num_sg.
  apply: conv_num_sg=> //.
  by apply: gtr0_sgz; rewrite ltNge; exact bzuabol2.
have vx2 : ve_x vert_e = left_limit c2.
  have /andP[_ /eqP ->] := left_vertical_edge_wrt_high llr2 ok2 v2.
  rewrite /left_limit; apply/eqP.
  move: ok2=> /andP[] lc2n0 /andP[].
  move=> /allP /(_ (head dummy_pt (left_pts c2))) + _; apply.
  by case : (left_pts c2) lc2n0 => [// | ? ?] _ /=; rewrite inE eqxx.
have p2'r : p2'.1 < right_limit c2.
  apply: conv_num_ltr=> //.
    by move: p3in=>/andP[] _ /andP[].
  move: p2in=> /andP[] /eqP -> _.
  by rewrite vx2; apply: ltW.
apply/andP; split.
  have p2'l : left_limit c2 < p2'.1.
    apply: conv_num_gtl=> //.
      by move: p3in=> /andP[] _ /andP[].
    by move: p2in=> /andP[] /eqP ->; rewrite vx2.
  apply: conv_num_gtl;[done | | apply: ltW].
    apply: conv_num_gtl=> //.
      by move: p3in=> /andP[] _ /andP[].
    by apply/ltW.
  apply: conv_num_gtl=> //.
  by move: bzuin=> /andP[] /eqP + _; rewrite -/p1' vx2 => ->.
apply: conv_num_ltr=> //.
  apply: conv_num_ltr=> //.
    by move: p3in=> /andP[] _ /andP[].
  by apply/ltW.
apply/ltW/conv_num_ltr=> //.
move: bzuin=> /andP[] + _; rewrite -/p1'=> /eqP ->.
by apply/ltW; rewrite vx2.
Qed.

Definition midpoint (a b : Plane R) := a <| 1/2 |> b.

Definition mkedge_aux (a b : Plane R) : {e : edge | 
     forall h : a.1 < b.1, e = Bedge h}.
case (boolP (a.1 < b.1)).
move=> h; exists (Bedge h)=> h0.
  by rewrite (bool_irrelevance h h0).
move=> not_edge.
exists (@Bedge (0, 0) (1, 0) (ltr01 : (0,0).1 < (1, 0).1)).
by move=> h; case: (negP not_edge).
Defined.

Definition mkedge (a b : Plane R) := sval (mkedge_aux a b).

Lemma mkedgeE (a b : Plane R) (h : a.1 < b.1) :
   mkedge a b = Bedge h.
Proof.
rewrite /mkedge; case: (mkedge_aux a b)=> v Pv /=; apply: Pv.
Qed.

Fixpoint check_bezier_ccw (fuel : nat) (v : vert_edge)
  (a b c : Plane R) : 
  option bool :=
match fuel with
| O => None
| S p =>
  let top_edge := (ve_x v, ve_top v) in
  if negb (point_under_edge top_edge (mkedge a c)) then
    Some true
  else if
     point_under_edge top_edge (mkedge a b) ||
     point_under_edge top_edge (mkedge b c)
  then 
    Some false
  else
    let b' := midpoint a b in
    let b2 := midpoint b c in
    let c' := midpoint b' b2 in
    if c'.1 < ve_x v then
      check_bezier_ccw p v c' b2 c
    else if ve_x v < c'.1 then
      check_bezier_ccw p v a b' c'
    else
      if c'.2 < ve_top v then
         Some true
      else
         Some false
end.

Lemma bezier_on_vertical_line (a b c : Plane R) (v : vert_edge) :
  a.1 < b.1 < c.1 ->
  {u | u \in `]0, 1[ & (bezier (f3pt a b c) 2 u).1 = b.1}.
Proof.
move=> abc.
set bezierx :=
  \sum_(i < 3) ((f3pt a b c) i).1 *: bernp 0 1 2 i - b.1%:P.
have bezierxq t :
  (bezier (f3pt a b c) 2 t).1 = (bezierx + b.1%:P).[t].
  rewrite bezier_bernstein2 /bezierx.
  rewrite addrNK !big_ord_recr /= !big_ord0 /= !add0r.
  have expandscale (x y : R) : x *: (y : R^o) = x * y by [].
  rewrite 3![in RHS] hornerE !hornerZ !expandscale.
  (* Problem with the failure of ring here. *)
  Fail ring.
  by rewrite (mulrC a.1) (mulrC b.1) (mulrC c.1).
have bz0 : bezier (f3pt a b c) 2 0 = a.
  by rewrite !bezier_step_conv /= !conv0.
have bz1 : bezier (f3pt a b c) 2 1 = c.
  by rewrite !bezier_step_conv /= !conv1.
have : bezierx.[0] < 0.
  move: (bezierxq 0); rewrite bz0 hornerE [X in _ + X]hornerE.
  move=> /eqP; rewrite -subr_eq=> /eqP <-.
  by rewrite subr_lt0; case/andP: abc.
have : 0 < bezierx.[1].
  move: (bezierxq 1); rewrite bz1 hornerE [X in _ + X]hornerE.
  move=> /eqP; rewrite -subr_eq=> /eqP <-.
  by rewrite subr_gt0; case/andP: abc.
move=> /gtr0_sg sg1 /ltr0_sg sg0.
have sgM : Num.sg bezierx.[0] * Num.sg bezierx.[1] = -1.
  by rewrite sg1 sg0 mulr1.
have [u uint /rootP ur] := ivt_sign ler01 sgM.
exists u=> //.
by rewrite bezierxq hornerE ur add0r hornerE.
Qed.

(*  In triangle p q r, the distance from r to its projection on
  line pq is det p q r / (q.1 - p.1) *)
Lemma diff_vert_y  (a b c c' : Plane R) :
  a.1 != b.1 ->
  c' = (c.1, a.2 + (c.1 - a.1) / (b.1 - a.1) * (b.2 - a.2)) ->
  (c.2 - c'.2 ) = det a b c / (b.1 - a.1).
Proof.
intros anb c'def.
have dn0 : b.1 - (a.1 : R^o) != 0.
  by rewrite subr_eq0 eq_sym.
rewrite c'def /= (mulrAC _ _ (b.2 - a.2)) opprD addrA.
apply: (mulIf dn0); rewrite mulrBl !mulfVK //.
rewrite det_scalar_productE /rotate /scalar_product /= mulrN.
by rewrite mulrC; congr (_ - _); rewrite mulrC.
Qed.

Lemma height_bezier2 (a b c p : Plane R) t: 
  a.1 < b.1 < c.1 ->
  (* p is the vertical projection of bezier ... t on the straight line ab *)
  det a b p = 0 ->
  p.1 = (bezier (f3pt a b c) 2 t).1 ->
  (bezier (f3pt a b c) 2 t).2 - p.2 =
  t ^ 2 * det a b c / (b.1 - a.1).
Proof.
move=> abcdq p1q palign.
(* c' is the vertical projection of c on the straight line ab. *)
set c' := (c.1, a.2 + (c.1 - a.1) / (b.1 - a.1) * (b.2 - a.2)).
have anb : a.1 != b.1 by lra.
rewrite -[RHS]mulrA -(diff_vert_y anb erefl).
move: p1q palign => /eqP.
rewrite vert_projr; last by lra.
move=> /eqP /[dup] palign -> projP.
rewrite (mulrAC _ _ (b.2 - a.2)).
have dba : b.1 - a.1 != 0 by lra.
apply: (mulIf dba).
rewrite mulrBl (mulrDl b.2) mulfVK // projP.
rewrite (mulrBr (t ^ 2)) (mulrBl (b.1 - a.1)).
have tmp1 : t ^ 2 * c'.2 * (b.1 - a.1) =
   t ^ 2 * (a.2 * ( b.1 - a.1) + (c.1 - a.1) * (b.2 - a.2)).
  rewrite -mulrA; congr (_ * _).
  by rewrite /= mulrDl (mulrAC _ _ (b.1 - a.1)) mulfVK.
rewrite !bezier_step_conv /=.
have tmp x (y : R^o) : x *: y = x * y by [].
rewrite !tmp tmp1 /=.
ring.
Qed.

Lemma safe_bezier_ccw_corner_side (a b c : Plane R) (v : vert_edge) 
  (u : R):
  ccw a b c ->
  a.1 < b.1 < c.1 ->
  a.1 < ve_x v < c.1 ->
  on_vert_edge b v ->
  u \in `]0, 1[ ->
  (bezier (f3pt a b c) 2 u).1 = ve_x v ->
  ve_bot v < (bezier (f3pt a b c) 2 u).2.
Proof.
move=> abc abc1 avc bon uin bzx.
move: (bon) => /andP[] /eqP bx /andP[]bl bh.
apply: (lt_trans bl).
rewrite -subr_gt0.
have abb : det a b b = 0.
  by rewrite det_cyclique det_alternate.
have bzxb : b.1 = (bezier (f3pt a b c) 2 u).1 by rewrite bzx.
rewrite (height_bezier2 abc1 abb bzxb).
apply: divr_gt0; last by lra.
apply: mulr_gt0; last by [].
rewrite in_itv /= in uin.
have tmp : 0 < u < 1 by exact uin.
apply: mulr_gt0; lra.
Qed.

Lemma under_proj e p :
   valid_edge e p -> (p <<= e) = (p.2 <= (left_pt e).2 +
        (p.1 - (left_pt e).1) * ((right_pt e).2 - (left_pt e).2) /
          ((right_pt e).1 - (left_pt e).1)).
Proof.
move=> vep.
rewrite /point_under_edge det_cyclique.
have ecnd := edge_cond e.
have ecnd' : (left_pt e).1 != (right_pt e).1 by lra.
set p' := (p.1, (left_pt e).2 + (p.1 - (left_pt e).1) /
                ((right_pt e).1 - (left_pt e).1) *
                    ((right_pt e).2 - (left_pt e).2)).
have := diff_vert_y ecnd'=> /(_ p p' erefl) /eqP.
rewrite subr_eq=> /eqP ->; rewrite /p' /=.
rewrite addrA (addrC _ (left_pt e).2) -!addrA.
rewrite ler_add2.
rewrite addrC -ler_subr_addl mulrAC addrN.
rewrite pmulr_lle0 // invr_gt0/=.
by rewrite subr_gt0.
Qed.

Lemma safe_bezier_ccw (a b c : Plane R) (v : vert_edge) (u : R) :
  ccw a b c ->
  a.1 < b.1 < c.1 ->
  a.1 < ve_x v < c.1 ->
  ~~((ve_x v, ve_top v) <<= mkedge a c) ->
  u \in `]0, 1[ ->
  (bezier (f3pt a b c) 2 u).1 = ve_x v ->
  ve_bot v < (bezier (f3pt a b c) 2 u).2 ->
  on_vert_edge (bezier (f3pt a b c) 2 u) v.
Proof.
move=> abc bint vint topP uin /[dup] bzx /eqP bzxb bzb.
rewrite /on_vert_edge bzxb bzb 2!andTb.
have ac_cond : a.1 < c.1 by lra.
have vav : valid_edge (mkedge a c) (ve_x v, ve_top v).
  rewrite/valid_edge mkedgeE [(left_pt _).1]/= [(right_pt _).1]/=.
  by rewrite ?ltW //; move: vint=> /andP[].
move: topP.
rewrite (under_proj vav) -ltNge; apply le_lt_trans.
rewrite (_ : (ve_x v, ve_top v).1 = (bezier (f3pt a b c) 2 u).1); last first.
  by rewrite bzx.
rewrite -under_proj; last by rewrite /valid_edge bzx; exact: vav.
rewrite /point_under_edge.
rewrite bezier_step_conv.
have vacp : valid_edge (mkedge a c) (bezier (f3pt a b c) 2 u).
  rewrite/valid_edge mkedgeE [(left_pt _).1]/= [(right_pt _).1]/= bzx.
  by rewrite ?ltW //; move: vint=> /andP[].
rewrite det_conv -sgz_le0.
have Cuin : 0 < 1 - u < 1 by rewrite in_itv /= in uin; lra.
set X := (X in X <= 0).
suff : X = -1.
  (* TODO : report
  Fail Timeout 2 lra. *)
  by move=> ->; apply: lerN10.
rewrite {}/X.
apply: conv_num_sg=> //.
  apply: ltr0_sgz.
  rewrite bezier_step_conv det_conv.
  rewrite convC.
  apply: conv_num_ltr=> //.
    rewrite /=; move: abc; rewrite /ccw mkedgeE /= => abc.
    by rewrite det_inverse oppr_lte0 -det_cyclique.
  by rewrite /= mkedgeE /= -det_cyclique det_alternate.
apply: ltr0_sgz.
rewrite bezier_step_conv det_conv.
apply: conv_num_ltr=> //.
  rewrite /=; move: abc; rewrite /ccw mkedgeE /= => abc.
  by rewrite det_inverse oppr_lte0 -det_cyclique.
by rewrite mkedgeE /= det_alternate.
Qed.

End sandbox.
