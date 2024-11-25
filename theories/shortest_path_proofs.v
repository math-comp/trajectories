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

Arguments cmp_option_trans [r] _ [_ _ _].

Lemma update_update q n1 n2 n3 p d p' d' :
    find (update (update q n1 p d) n2 p' d') n3 =
    find (update (update q n2 p' d') n1 p d) n3.
Proof.
have [n1n3 | n1nn3] := eqVneq n1 n3.
  rewrite -n1n3.
  have [n1n2 | n1nn2] := eqVneq n1 n2.
    rewrite -n1n2.
    case n1inq : (find q n1) => [ [p1  d1] | ].
      case cmp1 : (cmp_option _ <%R d d1).
        case cmp2 :(cmp_option _ <%R d' d).
          have int1 : find (update q n1 p d) n1 = Some(p, d).
            by apply: find_update_eq n1inq cmp1.
          rewrite (find_update_eq _ _ _ _ _ _ int1 cmp2).
          have [cmp3 | cmp3]:= boolP(cmp_option _ <%R d' d1).
            have int2 : find (update q n1 p' d') n1 = Some(p', d').
              by apply: find_update_eq n1inq cmp3.
            rewrite (update_discard _ _ _ _ _ _ int2); last by apply: oltNgt.
          by rewrite int2.
        have int3 : find (update q n1 p' d') n1 = Some (p1, d1).
          by rewrite (update_discard _ _ _ _ _ _ n1inq).
        case/negP: cmp3.
        by apply: (cmp_option_trans lt_trans cmp2).
Admitted.

End shortest_path_proofs.
