From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith String OrderedType OrderedTypeEx FMapAVL.

Notation head := seq.head.
Notation seq := seq.seq.
Notation nth := seq.nth.
Notation sort := path.sort.

Import Order.POrderTheory Order.TotalTheory.

Section shortest_path.

Variable R : Type.
Variable R0 : R.
Variable R_ltb : R -> R -> bool.
Variable R_add : R -> R -> R.

Variable cell : Type.
Variable node : Type.
Variable node_eqb : node -> node -> bool.
Variable neighbors_of_node : node -> seq (node * R).
Variable source target : node.

Variable priority_queue : Type.
Variable empty : priority_queue.
Variable gfind : priority_queue -> node -> option (seq node * option R).
Variable update : priority_queue -> node -> seq node -> option R ->
      priority_queue.
Variable pop :  priority_queue ->
       option (node * seq node * option R * priority_queue).

Definition cmp_option (v v' : option R) :=
  if v is Some x then
    if v' is Some y then
       (R_ltb x y)%O
    else
      true
   else
     false.

Definition Dijkstra_step (d : node) (p : seq node) (dist : R)
  (q : priority_queue) : priority_queue :=
  let neighbors := neighbors_of_node d in
  foldr (fun '(d', dist') q =>
           match gfind q d' with
           | None => q
           | Some (p', o_dist) =>
             let new_dist_to_d' := Some (R_add dist dist') in
             if cmp_option new_dist_to_d' o_dist then
                update q d' (d :: p) new_dist_to_d'
             else q
           end) q neighbors.

Fixpoint Dijkstra (fuel : nat) (q : priority_queue) :=
  match fuel with
  | 0%nat => None
  |S fuel' =>
    match pop q with
    | Some (d, p, Some dist, q') =>
      if node_eqb d target then Some p else
        Dijkstra fuel' (Dijkstra_step d p dist q')
    | _ => None
    end
  end.

Definition shortest_path (s : seq node) :=
  Dijkstra (size s)
    (update (foldr [fun n q => update q n [::] None] empty s)
        source [::] (Some R0)).

End shortest_path.

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
        have : ~~ cmp_option _ <%R d d1.
Admitted.

End shortest_path_proofs.
