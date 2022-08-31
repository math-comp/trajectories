From mathcomp Require Import all_ssreflect all_algebra vector reals classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Remove the module, it is only here to print the results at the end. *)
Module Convex.
Section C.

Variable R: realType.
Variable E: vectType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Definition segment (x y: E) := image `[0: R, 1] (fun t => (t *: x) + (1 - t) *: y).

Definition convex (C: set E) := forall x y, C x -> C y -> subset (segment x y) C.

Lemma segment_convex (x y: E): convex (segment x y).
Proof.
move=> x0 y0 [t0 /andP [t00 t01]] <- [t1 /andP [t10 t11]] <- z [t /andP [t0' t1']] <-.
do 2 rewrite GRing.scalerDr GRing.scalerA GRing.scalerA.
rewrite [_ *: _ + _]GRing.addrC GRing.addrA GRing.addrC -GRing.addrA -GRing.scalerDl GRing.addrA -GRing.scalerDl GRing.addrC.
have e: (1 - t) * (1 - t1) + t * (1 - t0) = 1 - (t * t0 + (1 - t) * t1).
   do 2 rewrite GRing.mulrBr GRing.mulr1.
   rewrite -GRing.addrA -GRing.addrA [- t+_]GRing.addrC [t+_]GRing.addrC GRing.addrA GRing.addrA GRing.addrA -GRing.addrA GRing.subrr GRing.addr0 -GRing.addrA.
   by f_equal; rewrite GRing.opprD GRing.addrC.
rewrite e; exists (t * t0 + (1 - t) * t1)=>//.
apply /andP; split; rewrite bnd_simp.
   apply Num.Theory.addr_ge0; apply Num.Theory.mulr_ge0=>//.
   by rewrite Num.Theory.subr_ge0.
rewrite -Num.Theory.subr_ge0 -e.
by apply Num.Theory.addr_ge0; apply Num.Theory.mulr_ge0=>//; rewrite Num.Theory.subr_ge0.
Qed.

Lemma convexI (C D: set E): convex C -> convex D -> convex (C `&` D).
Proof.
move=> Cc Dc x y [Cx Dx] [Cy Dy] z xzy.
by split; [ apply (Cc x y) | apply (Dc x y) ].
Qed.

Definition conv (A: set E): set E := (fun s: seq (R * E) => \sum_(i <- s) (let (t, a) := i in t *: a)) @` (mkset (fun s: seq (R*E) => \sum_(i <- s) (let (t, _) := i in t) = 1 /\ List.Forall (fun x: R*E => let (t, a) := x in 0 <= t /\ a \in A) s)).

Lemma conv_ext (A: set E): subset A (conv A).
Proof.
move=> x Ax.
exists [:: (1, x)].
   2: by rewrite big_seq1 GRing.scale1r.
split.
   by rewrite big_seq1.
apply List.Forall_cons.
   2: by apply List.Forall_nil.
split.
   exact Num.Theory.ler01.
by apply mem_set.
Qed.

Lemma conv_sub_convex (A C: set E): subset A C -> convex C -> subset (conv A) C.
Proof.
move=>AsC Cc x [s [s1 sA] <-]; clear x.
remember (size s) as n; symmetry in Heqn.
move: s Heqn s1 sA; induction n=> s sn s1 sA.
   move: sn s1 (GRing.oner_neq0 R)=>/size0nil ->.
   by rewrite big_nil=>-> /eqP.
destruct s=>//.
destruct p as [t a].
rewrite big_cons.
inversion sA; subst l x.
move: sA H1 H2=> _ [t0 aA] sA.
move: s1; rewrite big_cons=>s1.
case t1: (0 < 1-t).
   apply (Cc a ((GRing.inv (1-t)) *: (\sum_(j <- s) (let (t2, a0) := j in t2 *: a0)))).
      by apply AsC; apply set_mem.
      2:{
      move: t1; rewrite Num.Theory.lt0r=>/andP [tn0 tge0].
      exists t.
         apply /andP; split; rewrite bnd_simp=>//.
         by rewrite -Num.Theory.subr_ge0.
      by f_equal; rewrite GRing.scalerA GRing.divff // GRing.scale1r.
      }
   rewrite GRing.scaler_sumr.
   move:IHn=>/(_ [seq (let (t', a) := i: R*E in (t' / (1-t), a)) | i <- s]).
   rewrite size_map; inversion sn=>/(_ Logic.eq_refl).
   rewrite big_map (congr_big s (fun _ => true) (fun i => (1-t)^-1 * (let (t', a) := i in t'))) //.
      2: by move=> [t' b] _; apply GRing.mulrC.
   rewrite -GRing.mulr_sumr GRing.mulrC.
   move: s1=>/(f_equal (fun u => u-t)); rewrite GRing.addrC GRing.addrA [-t+_]GRing.addrC GRing.subrr GRing.add0r=> ->.
   move: (t1); rewrite Num.Theory.lt0r=>/andP [tn0 tge0]=> /(_ (GRing.divff tn0)).
   rewrite big_map (congr_big s (fun _ => true) (fun i => (1-t)^-1 *: (let (t', a') := i in t' *: a'))) //.
      2: by move=> [t' a'] _; rewrite GRing.mulrC; rewrite GRing.scalerA.
   apply; apply List.Forall_forall=> [[t' a']] /List.in_map_iff [[t'' a'']] [t'a' tin]; inversion t'a'; subst t' a'.
   move: sA=>/List.Forall_forall /(_ (t'', a'') tin) [t''ge0 a''A].
   split=>//.
   by apply Num.Theory.divr_ge0.
clear n sn IHn Cc t0; move: t1=>/negP/negP; rewrite -Num.Theory.real_leNgt //.
   2, 3: by apply Num.Theory.num_real.
move=> t1.
have se: s = [seq (let (t, a) := i: R*E in (0, a)) | i <- s].
   clear C AsC a aA; induction s=>//=.
   destruct a; inversion sA; clear sA; subst x l.
   suff: (s0 == 0).
      move=>/eqP s00; subst s0; f_equal; apply IHs=>//.
      by move: s1; rewrite big_cons GRing.add0r.
   move: s1=> /(f_equal (fun u => u-t)); rewrite GRing.addrC GRing.addrA [-t+t]GRing.addrC GRing.subrr GRing.add0r big_cons=>s1.
   move: s1 t1 H1=><- s0le [s0ge _]; apply /eqP; apply Order.POrderTheory.le_anti; apply /andP; split=>//.
   clear IHs s0ge.
   rewrite -[s0]GRing.addr0; refine (Order.POrderTheory.le_trans _ s0le); apply Num.Theory.ler_add=>//.
   clear s0le; induction s.
      by rewrite big_nil.
   inversion H2; subst x l; destruct a; rewrite big_cons.
   apply Num.Theory.addr_ge0.
      by move: H1=>[s10 _].
   by apply IHs.
rewrite se big_map (congr_big s (fun _ => true) (fun _ => 0)) //.
   2: by move=> [t' a'] _; apply GRing.scale0r.
rewrite mathcomp_extra.big_const_idem; rewrite GRing.addr0 //.
move: s1; rewrite se big_map (congr_big s (fun _ => true) (fun _ => 0)) //.
   2: by move=> [t' a'] _.
rewrite mathcomp_extra.big_const_idem; rewrite GRing.addr0 // =>->; rewrite GRing.scale1r.
by apply AsC; apply set_mem.
Qed.

Lemma conv_segment (x y: E): segment x y = conv [set x; y].
Proof.
rewrite eqEsubset; split.
   move=> z [t /andP [t0 t1]] <-.
   rewrite bnd_simp in t0; rewrite bnd_simp in t1.
   exists [:: (t, x); (1-t, y)].
      2: by rewrite big_cons big_seq1. 
   split.
      by rewrite big_cons big_seq1 [1-t]GRing.addrC GRing.addrA GRing.subrr GRing.add0r.
   apply List.Forall_cons.
      by split=>//; apply mem_set; left.
   apply List.Forall_cons=>//.
   by split; [ rewrite Num.Theory.subr_ge0 | apply mem_set; right ].
apply conv_sub_convex.
   2: by apply segment_convex.
move=>z; case=>->.
   exists 1.
      2: by rewrite GRing.scale1r GRing.subrr GRing.scale0r GRing.addr0.
   apply /andP; split; rewrite bnd_simp=>//.
   exact (@Num.Theory.ler01 R).
exists 0.
   2: by rewrite GRing.scale0r GRing.subr0 GRing.scale1r GRing.add0r.
apply /andP; split; rewrite bnd_simp=>//.
exact (@Num.Theory.ler01 R).
Qed.

Lemma conv_convex (A: set E): convex (conv A).
Proof.
move=> x y [sx [sx1 sxA] sxx] [sy [sy1 syA] syy] z [t /andP [t0 t1] <-].
rewrite bnd_simp in t0; rewrite bnd_simp in t1.
exists ([seq (let (u, a) := i: R*E in (t*u, a)) | i <- sx] ++ [seq (let (u, a) := i: R*E in ((1-t)*u, a)) | i <- sy]).
split.
   rewrite big_cat.
   rewrite big_map (congr_big sx (fun _ => true) (fun i => t * (let (u, a) := i in u))) //.
      2: by move=> [u a] _.
   rewrite -GRing.mulr_sumr sx1 big_map (congr_big sy (fun _ => true) (fun i => (1-t) * (let (u, a) := i in u))) //.
      2: by move=> [u a] _.
   rewrite -GRing.mulr_sumr sy1 GRing.mulr1 GRing.mulr1 GRing.addrC.
   have -> : GRing.add_monoid R t (- t + 1) = t + (-t+1) by lazy.
   by rewrite GRing.addrA GRing.subrr GRing.add0r.
   apply List.Forall_forall=> i iin.
   by move: (List.in_app_or _ _ _ iin); case; [ move: sxA | move: syA ] =>/List.Forall_forall sF /List.in_map_iff [[u a] [ie /sF [u0 ua]]]; subst i; split=>//; apply Num.Theory.mulr_ge0=>//; rewrite Num.Theory.subr_ge0.
rewrite big_cat.
rewrite big_map (congr_big sx (fun _ => true) (fun i => t *: (let (u, a) := i in u *: a))) //.
   2: by move=> [u a] _; rewrite GRing.scalerA.
rewrite -GRing.scaler_sumr sxx big_map (congr_big sy (fun _ => true) (fun i => (1-t) *: (let (u, a) := i in u *: a))) //.
   2: by move=> [u a] _; rewrite GRing.scalerA.
rewrite -GRing.scaler_sumr syy.
by lazy.
Qed.

Lemma convex_convE (C: set E): convex C <-> C = conv C.
Proof.
split=> Cc.
   by rewrite eqEsubset; split; [ apply conv_ext | apply conv_sub_convex ].
by rewrite Cc; apply conv_convex.
Qed.

Lemma conv_mono (A B: set E): subset A B -> subset (conv A) (conv B).
Proof.
move=>AB; apply conv_sub_convex.
   by apply (subset_trans AB), conv_ext.
by apply conv_convex.
Qed.

End C.
End Convex.

(* TODO: move in another file *)
Require Import Coq.Program.Wf.

Section Bezier.

Variable R: realType.
Variable E: vectType R.

Local Open Scope fun_scope.
Local Open Scope ring_scope.

Program Fixpoint bezier (x: E) (s: seq E) (t: R) {measure (size s)}: E :=
  match s with
  | nil => x
  | y :: s => (1-t) *: (bezier x (belast y s) t) + t *: (bezier y s t)
  end.
Next Obligation.
Proof. by rewrite size_belast. Defined.

Lemma bezier_cons x y s t: bezier x (y :: s) t = (1-t) *: (bezier x (belast y s) t) + t *: (bezier y s t).
Proof.
unfold bezier, bezier_func.
by rewrite WfExtensionality.fix_sub_eq_ext.
Qed.

Lemma bezier0 x s: bezier x s 0 = x.
Proof.
remember (size s) as n; symmetry in Heqn.
move: s Heqn.
induction n.
   by move=> s /size0nil ->.
move=> s sn.
destruct s=>//.
rewrite bezier_cons GRing.subr0 GRing.scale1r GRing.scale0r GRing.addr0.
by apply IHn; rewrite size_belast; inversion sn.
Qed.

Lemma bezier1 x s: bezier x s 1 = last x s.
Proof.
remember (size s) as n; symmetry in Heqn.
move: x s Heqn.
induction n.
   by move=> x s /size0nil ->.
move=> x s sn.
destruct s=>//.
rewrite bezier_cons GRing.subrr GRing.scale1r GRing.scale0r GRing.add0r /=.
by apply IHn; inversion sn.
Qed.

Lemma bezier_sub_conv x s: subset (bezier x s @` `[0, 1]) (Convex.conv (fun y => y \in (x :: s))).
Proof.
move=> y [t t01 <-].
remember (size s) as n; symmetry in Heqn.
move: s x Heqn; induction n.
   move=> s x /size0nil ->.
   apply Convex.conv_ext.
   by rewrite inE; apply /eqP.
move=> s x sn.
destruct s as [| a s ]=>//; rewrite bezier_cons.
inversion sn.
have /Convex.conv_mono lsub: subset (fun y : E => y \in x :: belast a s) (fun y : E => y \in x :: a :: s) by move=> z; (do 2 rewrite in_cons)=>/orP; case=> [ -> // | /mem_belast -> ]; rewrite orbT.
have /(IHn _ x) /lsub l: size (belast a s) = n by rewrite size_belast.
have /Convex.conv_mono rsub: subset (fun y : E => y \in a :: s) (fun y : E => y \in x :: a :: s) by move=> z; (do 3 rewrite in_cons)=>/orP; case=>[ -> // | -> ]; rewrite orbT // orbT.
move: H0=>/(IHn _ a) /rsub r.
move: (@Convex.conv_convex _ _ (fun y : E => y \in x :: a :: s) (bezier x (belast a s) t) (bezier a s t) l r); apply.
exists (1-t).
   2: by rewrite -{2}[1]GRing.add0r GRing.addrKA GRing.opprK GRing.add0r.
apply /andP; move: t01=>/andP.
(repeat rewrite bnd_simp)=>[[t0 t1]]; split.
   by rewrite Num.Theory.subr_ge0.
rewrite Num.Theory.ler_subl_addl -{1}[1]GRing.add0r.
by apply Num.Theory.ler_add.
Qed.

Print Convex.
