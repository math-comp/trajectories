From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith String OrderedType OrderedTypeEx FMapAVL.
Require Import shortest_path.

Notation head := seq.head.
Notation seq := seq.seq.
Notation nth := seq.nth.
Notation sort := path.sort.

Import Order.POrderTheory Order.TotalTheory.

Section shortest_path_proofs.

Variable R : realDomainType.

Variable node : eqType.

Variable neighbors : node -> seq (node * R).

Variable queue : Type.
Variable empty : queue.
Variable find : queue -> node -> option (seq node * option R).
Variable update : queue -> node -> seq node -> option R -> queue.
Variable pop :  queue -> option (node * seq node * option R * queue).

Hypothesis find_empty :
  forall n, find empty n = None.
Hypothesis find_update_eq : forall q n p d p' d',
  find q n = Some(p', d') -> cmp_option R <%R d d' ->
  find (update q n p d) n = Some(p, d).
Hypothesis find_update_None : forall q n p d,
  find q n = None -> find (update q n p d) n = Some(p, d).
Hypothesis find_update_diff : forall q n1 n2 p d,
  n1 != n2 ->
  find (update q n1 p d) n2 = find q n2.
Hypothesis pop_remove :
  forall q n p d q', pop q = Some (n, p, d, q') ->
  find q' n = None.
Hypothesis pop_find :
  forall q n p d q', pop q = Some (n, p, d, q') ->
  find q n = Some(p, d).
Hypothesis pop_diff :
  forall q n1 n2 p d q', pop q = Some(n1, p, d, q') ->
    n1 != n2 ->
    find q' n2 = find q n2.
Hypothesis pop_min : forall q n1 n2 p p' d d' q',
    pop q = Some(n1, p, d, q') ->
    find q n2 = Some(p', d') -> cmp_option _ <%R d d'.
Hypothesis update_discard :
  forall q n p d p' d',
    find q n = Some(p, d) ->
    ~~ cmp_option _ <%R d' d ->
    find (update q n p' d') n = find q n.

Lemma oltNgt (d1 d2 : option R) : cmp_option _ <%R d1 d2 ->
                      ~~ cmp_option _ <%R d2 d1.
Proof.
case: d1 => [d1 | ]; case: d2 => [d2 | ] //.
rewrite /cmp_option.
by rewrite -leNgt le_eqVlt orbC => ->.
Qed.


Lemma cmp_option_trans (r : rel R) : ssrbool.transitive r ->
  ssrbool.transitive (cmp_option _ r).
Proof.
move=> rtr [y |] [x |] [z|] //=.
by apply: rtr.
Qed.

Lemma cmp_option_le_lt_trans (y x z: option R) :
  ~~ cmp_option _ <%R y x -> cmp_option _ <%R y z ->
  cmp_option _ <%R x z.
Proof.
case: x => [x | ]; case: y => [y | ] // xley.
rewrite /= -leNgt le_eqVlt in xley.
case: (orP xley)=> [/eqP ->| xltkey ]; first by [].
apply: (cmp_option_trans <%R lt_trans).
exact: xltkey.
Qed.

Arguments cmp_option_trans [r] _ [_ _ _].

(* A sobering counter example: you cannot swap updates, because they
  may imply different choices between points at the same distance. *)
Lemma update_update_counterx  n p1 p2 d :
  p1 != p2 ->
  find (update (update empty n p1 d) n p2 d) n !=
  find (update (update empty n p2 d) n p1 d) n.
Proof.
move=> pdif.
have testfail : ~~ cmp_option R <%R d d.
  by case: d => [d | ] //=; rewrite lt_irreflexive.
have inup1 : find (update empty n p1 d) n = Some(p1, d).
  by rewrite find_update_None.
rewrite (update_discard _ _ _ _ _ _ inup1) //.
rewrite inup1.
have inup2 : find (update empty n p2 d) n = Some(p2, d).
  by rewrite find_update_None.
rewrite (update_discard _ _ _ _ _ _ inup2) //.
rewrite inup2.
by apply/eqP=> - [] /eqP; rewrite (negbTE pdif).
Qed.

End shortest_path_proofs.
