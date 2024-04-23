From mathcomp Require Import all_ssreflect all_algebra.
Require Export Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArithRing.
Import Order.TTheory GRing.Theory Num.Theory Num.ExtraDef Num.

Open Scope ring_scope.

Fixpoint seq_subst {A : eqType}(l : seq A) (b c : A) : seq A :=
  match l with
  | nil => nil
  | a :: tl =>
    if a == b then (c :: seq_subst tl b c) else (a :: seq_subst tl b c)
  end.

Lemma mem_seq_subst {A : eqType} (l : seq A) b c x :
  x \in (seq_subst l b c) -> (x \in l) || (x == c).
Proof.
elim: l => [// | a l Ih].  
rewrite /=.
by case: ifP => [] ?; rewrite !inE=> /orP[ | /Ih /orP[] ] ->; rewrite ?orbT.
Qed.
  
Lemma seq_subst_eq0  {A : eqType} (l : seq A) b c :
  (seq_subst l b c == [::]) = (l == [::]).
Proof. by case : l => [ | a l] //=; case: ifP. Qed.

Lemma seq_subst_cat {A : eqType} (l1 l2 : seq A) b c : 
  seq_subst (l1 ++ l2) b c = seq_subst l1 b c ++ seq_subst l2 b c.
Proof.
elim: l1 => [ // | a l1 Ih] /=.
by case: ifP=> [ab | anb]; rewrite Ih.
Qed.

Lemma last_in_not_nil (A : eqType) (e : A) (s : seq A) :
s != [::] -> last e s \in s.
Proof.
case : s  => [//= | c q  ]  /= _.
by rewrite mem_last.
Qed.

Lemma head_in_not_nil (A : eqType) (e : A) (s : seq A) :
s != [::] -> head e s \in s.
Proof.
case : s  => [//= | c q  ]  /= _.
by rewrite inE eqxx.
Qed.

Lemma middle_seq_not_nil  (A : eqType) (a b c : seq A) :
b != [::] ->
a ++ b ++ c != [::].
Proof.
rewrite -size_eq0 => /negP sizebneq0 /=.
apply  /negP.
rewrite -size_eq0 !size_cat /= !addn_eq0 .
apply  /negP /andP => [] /andP .
move => /andP [] _ /andP [] sizebeq0.
by rewrite sizebeq0 in sizebneq0.
Qed.

Lemma rcons_neq0 (A : Type) (z : A) (s : seq A) : (rcons s z) <> nil.
Proof.
by case : s.
Qed.

Lemma head_rcons (A : Type) (d l : A) (s : seq A) :
    head d (rcons s l) = head l s.
Proof. by case: s. Qed.

Lemma allcons [T : predArgType]
  (f : T -> bool) a q' : all f (a :: q') = f a && all f q'.
Proof.  by []. Qed.

Definition cutlast (T : Type) (s : seq T) :=
match s with | a :: s => belast a s | [::] => [::] end.

Lemma last_seq2 (T : Type) (def a : T) (s : seq T) :
   s <> nil -> last def (a :: s) = last def s.
Proof.
by case: s => [// | b s] _ /=.
Qed.

Lemma behead_cutlasteq (T : Type) a (s : seq T) :
  (1 < size s)%N -> s = head a s :: rcons (cutlast (behead s)) (last a s).
Proof.
by case: s => [ | b [ | c s]] //= _; congr (_ :: _); rewrite -lastI.
Qed.

Lemma cutlast_subset (T : eqType) (s : seq T) : {subset cutlast s <= s}.
Proof.
rewrite /cutlast; case: s => [// | a s].
elim: s a => [ // | b s Ih /=] a e; rewrite inE=> /orP[/eqP -> | ein].
  by rewrite inE eqxx.
by rewrite inE Ih ?orbT.
Qed.

Lemma behead_subset (T : eqType) (s : seq T) : {subset behead s <= s}.
Proof. by case: s => [ | a s] // e /=; rewrite inE orbC => ->. Qed.

Lemma sorted_catW (T : Type) (r : rel T) s s' :
 (sorted r (s ++ s')) -> sorted r s && sorted r s'.
Proof.
case: s => [// | a s] /=.
by rewrite cat_path => /andP[] ->; apply: path_sorted.
Qed.

Lemma sorted_rconsE (T : Type) (leT : rel T) s y:
  transitive leT -> sorted leT (rcons s y) -> all (leT^~ y) s.
Proof.
move=> tr; elim: s=> [ | init s Ih] //=.
by rewrite (path_sortedE tr) all_rcons => /andP[] /andP[] -> _.
Qed.

Lemma uniq_map_injective (T T' : eqType) (f : T -> T') (s : seq T) :
  uniq [seq f x | x <- s] -> {in s &, injective f}.
Proof.
elim: s => [ // | a s Ih] /= /andP[fan uns].
move=> e1 e2; rewrite !inE => /orP[/eqP -> | e1s ] /orP[/eqP -> | e2s] feq //.
    by move: fan; rewrite feq; case/negP; apply/mapP; exists e2.
  by move: fan; rewrite -feq; case/negP; apply/mapP; exists e1.
by apply: Ih.
Qed.

Lemma mem_seq_split (T : eqType) (x : T) (s : seq T) :
  x \in s -> exists s1 s2, s = s1 ++ x :: s2.
Proof.
by move=> /splitPr [s1 s2]; exists s1, s2.
Qed.

Section transitivity_proof.

Variables (T : eqType) (r : rel T) (s1 s2 : mem_pred T).

Hypothesis s1tr : {in s1 & &, transitive r}.
Hypothesis s2tr : {in s2 & &, transitive r}.
Hypothesis s1s2 : {in s1 & s2, forall x y, r x y && ~~ r y x}.

Lemma two_part_trans : {in predU s1 s2 & &, transitive r}.
Proof.
move=> x2 x1 x3 /orP[x2ins1 | x2ins2] /orP[x1ins1 | x1ins2]
      /orP[x3ins1 | x3ins2];
  try solve[move=> ?; apply:s1tr=> // |
            move=> ?; apply: s2tr => // |
            move=> ? ?; apply: (proj1 (andP (s1s2 _ _))) => //].
- by move=> r12 r23; move: (s1s2 x2ins1 x1ins2); rewrite r12 andbF.
- by move=> r12 r23; move: (s1s2 x2ins1 x1ins2); rewrite r12 andbF.
- by move=> r12 r23; move: (s1s2 x3ins1 x2ins2); rewrite r23 andbF.
- by move=> r12 r23; move: (s1s2 x3ins1 x2ins2); rewrite r23 andbF.
Qed.

End transitivity_proof.

Section abstract_subsets_and_partition.

Variable cell : eqType.
Variable sub : cell -> cell -> Prop.
Variable exclude : cell -> cell -> Prop.

Variable close : cell -> cell.

Hypothesis excludeC : forall c1 c2, exclude c1 c2 -> exclude c2 c1.
Hypothesis exclude_sub : 
  forall c1 c2 c3, exclude c1 c2 -> sub c3 c1 -> exclude c3 c2.

Lemma add_map (s1 : pred cell) (s2 : seq cell) :
    all (predC s1) s2 ->
    {in s2, forall c, sub (close c) c} ->
    {in predU s1 (mem s2) &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  {in predU s1 (mem [seq close c | c <- s2]) &,
    forall c1 c2, c1 = c2 \/ exclude c1 c2}.
Proof.
have symcase : forall (s : pred cell) (s' : seq cell),
  all (predC s) s' -> 
  {in s', forall c, sub (close c) c} ->
  {in predU s (mem s') &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  forall c1 c2, s c1 -> c2 \in s' -> exclude c1 (close c2).
  move=> s s' dif clsub exc c1 c2 sc1 c2s'.
  apply/excludeC/(exclude_sub _ (clsub _ _)); last by [].
  have := exc c2 c1; rewrite 2!inE c2s' orbT inE sc1 => /(_ isT isT).
  by move=> -[abs | //]; have := allP dif _ c2s'; rewrite inE abs sc1.
move=> s1nots2 clsub oldx g1 g2.
rewrite inE => /orP[g1old | /mapP[co1 co1in g1c]];
  rewrite inE =>  /orP[g2old |/mapP[co2 co2in g2c ]].
- by apply: oldx; rewrite inE ?g1old ?g2old.
- by right; rewrite g2c; apply: (symcase _ _ s1nots2 clsub oldx).
- by right; rewrite g1c; apply excludeC; apply: (symcase _ _ s1nots2 clsub oldx).
have [/eqP co1co2 | co1nco2] := boolP(co1 == co2).
  by left; rewrite g1c g2c co1co2.
right; rewrite g1c; apply/(exclude_sub _ (clsub _ _)); last by [].
rewrite g2c; apply/excludeC/(exclude_sub _ (clsub _ _)); last by [].
have := oldx co2 co1; rewrite !inE co2in co1in !orbT=> /(_ isT isT).
by case=> [abs | //]; case/negP: co1nco2; rewrite abs eqxx.
Qed.

Lemma add_new (s s2 : pred cell) :
  {in s &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  {in s & s2, forall c1 c2, exclude c1 c2} ->
  {in s2 &, forall c1 c2, c1 = c2 \/ exclude c1 c2} ->
  {in predU s s2 &, forall c1 c2, c1 = c2 \/ exclude c1 c2}.
Proof.
move=> oldx bipart newx c1 c2.
rewrite inE=> /orP[c1old | c1new] /orP[c2old | c2new].
- by apply: oldx.
- by right; apply: bipart.
- by right; apply/excludeC/bipart.
by apply: newx.
Qed.

End abstract_subsets_and_partition.

Section subset_tactic.

Lemma all_sub [T : eqType] [p : pred T] [s1 s2 : seq T] :
  {subset s1 <= s2} -> all p s2 -> all p s1.
Proof.  by move=> subs as2; apply/allP=> x xin; apply/(allP as2)/subs. Qed.

Lemma subset_consl [T : eqType] (x : T) (s s': seq T) :
  x \in s' -> {subset s <= s'} -> {subset (x :: s) <= s'}.
Proof.
by move=> xin ssub g; rewrite inE=> /orP[/eqP -> // | ]; apply: ssub.
Qed.

Lemma subset_catl [T : eqType] (s1 s2 s' : seq T) :
  {subset s1 <= s'} -> {subset s2 <= s'} -> {subset s1 ++ s2 <= s'}.
Proof.
move=> s1sub s2sub g; rewrite mem_cat=>/orP[];[apply: s1sub | apply s2sub].
Qed.

Lemma subset_catrl [T : eqType] [s s1 s2 : seq T] :
  {subset s <= s1} -> {subset s <= s1 ++ s2}.
Proof. by move=> ssub g gn; rewrite mem_cat ssub. Qed.

Lemma subset_catrr [T : eqType] [s s1 s2 : seq T] :
  {subset s <= s2} -> {subset s <= s1 ++ s2}.
Proof. by move=> ssub g gn; rewrite mem_cat ssub ?orbT. Qed.

Lemma subset_id [T : eqType] [s : seq T] : {subset s <= s}.
Proof. by move=> x. Qed.

Lemma subset_head [T : eqType] [s1 s2 : seq T] [x : T] :
  {subset (x :: s1) <= s2} -> head x s1 \in s2.
Proof. 
by move=> sub; apply: sub; case: s1=> [ | a ?] /=; rewrite !inE eqxx ?orbT.
Qed.

End subset_tactic.

Ltac subset_tac :=
  trivial; 
  match goal with
  | |- {subset ?x <= ?x} => apply: subset_id
  | |- {subset (_ :: _) <= _} => apply: subset_consl; subset_tac
  | |- {subset (_ ++ _) <= _} => apply: subset_catl; subset_tac
  | |- {subset _ <= _ ++ _} => 
     solve[(apply: subset_catrl; subset_tac)] || 
     (apply: subset_catrr; subset_tac)
  | |- {subset _ <= _} =>
    let g := fresh "g" in let gin := fresh "gin" in
    move=> g gin; rewrite !(mem_cat, inE, cat_rcons);
    rewrite ?eqxx ?gin ?orbT //; subset_tac
  | |- is_true (?x \in (?x :: _)) => rewrite inE eqxx; done
  | |- is_true (head _ (rcons _ _) \in _) => rewrite head_rcons; subset_tac
  | |- is_true (head _ _ \in _) => apply: subset_head; subset_tac
  | |- is_true (_ \in (_ :: _)) => rewrite inE; apply/orP; right; subset_tac
  | |- is_true (_ \in (_ ++ _)) => rewrite mem_cat; apply/orP;
    (solve [left; subset_tac] || (right; subset_tac))
  end.
