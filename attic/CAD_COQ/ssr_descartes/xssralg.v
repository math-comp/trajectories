Require Import ssreflect eqtype ssrbool ssrnat fintype seq ssrfun .
Require Import bigops groups choice .
Require Export ssralg .

Set   Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope .
Import GRing.Theory .

Open Local Scope ring_scope .

Structure orderb (M : Type) (R : M -> M -> bool) : Type := Orderb {
  reflb    : reflexive R;
  antisymb : antisymmetric R;
  transb   : transitive R
} .

Structure sorderb (M : Type) (R : M -> M -> bool) : Type := SOrderb {
  irreflsb : irreflexive R;
  transsb  : transitive R
} .

Reserved Notation "x <<= y" (at level 70, no associativity) .
Reserved Notation "x <<! y" (at level 70, no associativity) .

Section Compatible .
  Variable R : ringType .

(* assia : I don't like the "compatible" name, turned temp. to lcompat, added rcompat*)
  Definition lcompatible (r : R -> R -> bool) :=
    forall (x y₁ y₂ : R), r 0 x -> r y₁ y₂ -> r (x * y₁) (x * y₂) .

  Definition rcompatible (r : R -> R -> bool) :=
    forall (x y₁ y₂ : R), r 0 x -> r y₁ y₂ -> r (y₁* x) (y₂ * x) .


End Compatible .


(* -------------------------------------------------------------------- *)
Module GOrdered .
  (* ------------------------------------------------------------------ *)
  Module OComRing.

    Record mixin_of (G : GRing.Ring.type) : Type := Mixin {
      leb : G -> G -> bool;
      ltb : G -> G -> bool;
      _   : sorderb  ltb;
      _   : forall x y, leb x y -> forall z, leb (x+z) (y+z);
      _   : forall x y, leb x y = (ltb x y) || (x == y);
      _   : forall x y, (leb x y) || (leb y x);
      _   : lcompatible ltb
    } .

    Record class_of (R : Type) : Type := Class {
      base :> GRing.ComRing.class_of R;
      mixin  :> mixin_of (GRing.Ring.Pack base R)
    } .


    Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.

    Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
    Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
      let: Pack T c _ := cT return K _ (class cT) in k _ c.
    Definition repack cT : _ -> Type -> type :=
      let k T c p := p c in unpack k cT.

    Definition pack := let k T c m :=
      Pack (@Class T c m) T in GRing.ComRing.unpack k.

    Definition eqType          cT := Equality.Pack             (class cT) cT.
    Definition choiceType      cT := Choice.Pack               (class cT) cT.
    Definition zmodType        cT := GRing.Zmodule.Pack        (class cT) cT.
    Definition ringType        cT := GRing.Ring.Pack           (class cT) cT.
    Coercion comringType cT := GRing.ComRing.Pack (class cT) cT.

    Definition EtaMixin R leb ltb ltr_sorderb leb_addr leb_ltb_eq leb_total ltb_lcompatible :=
      let _ := @Mixin R leb ltb ltr_sorderb leb_addr leb_ltb_eq leb_total ltb_lcompatible in
        @Mixin (GRing.Ring.Pack (GRing.Ring.class R) R) leb ltb ltr_sorderb leb_addr leb_ltb_eq leb_total ltb_lcompatible.

  
  End OComRing .

  Canonical Structure OComRing.eqType.
  Canonical Structure OComRing.choiceType.
  Canonical Structure OComRing.zmodType.
  Canonical Structure OComRing.ringType.
  Canonical Structure OComRing.comringType.

  Bind Scope comring_scope with OComRing.sort .

  Definition ltbDef (R : OComRing.type) : R -> R -> bool := OComRing.ltb (OComRing.class R).
  Notation ltb := (@ltbDef _).

  Definition lebDef (R : OComRing.type) : R -> R -> bool := OComRing.leb (OComRing.class R).
  Notation leb := (@lebDef _).

(*  Definition leb R := OComRing.leb (OComRing.class R).*)
(*  Definition ltb R := OComRing.ltb (OComRing.class R).*)

  Local Notation "x <<= y" := (leb x y) .
  Local Notation "x <<! y" := (ltb x y) .

  Definition absrDef (R : OComRing.type) (x : R) := 
    if (ltb x 0) then -x else x .
  Notation absr := (@absrDef _).

  Definition signDef (R : OComRing.type) (x : R) : R := 
  if (0 <<! x) then 1 else (if (x <<! 0) then (-1) else 0) .

  Notation sign := (@signDef _).

(*Definition sign R x := 
  if (@ltb R 0 x) then 1 else (if (@ltb R x 0) then (-1) else (0 : R)) .
*)

  (* -------------------------------------------------------------------- *)
  Section OComringTheory .
    Variable G : OComRing.type .
    Implicit Types x y z : G .



(*
    Notation Local "x <<= y" := (@leb G x y) .
    Notation Local "x <<! y" := (@ltb G x y) .
*)
    (* ------------------------------------------------------------------ *)
    Lemma ltr_sorderb : sorderb (@ltbDef G) .
    Proof . by case G => [T [? []]] . Qed .

    Lemma ltr_irrefl : irreflexive (@ltbDef G).
    Proof . by case ltr_sorderb . Qed .
      
    Lemma ltr_trans : transitive (@ltbDef G) .
    Proof . by case ltr_sorderb . Qed .

    Lemma ltr_lcompat : lcompatible (@ltbDef G) .
    Proof . by case G => [T [? []]] . Qed .

    Lemma ltr_rcompat : rcompatible (@ltbDef G).
    Proof. by move=> x y z; rewrite mulrC [z * _]mulrC; exact: ltr_lcompat. Qed.

      
    (* ------------------------------------------------------------------ *)

    Lemma ler_ltreq : forall x y, (x <<= y) = (x <<! y) || (x == y) .
      Proof. by case: G => [T [? []]]. Qed.
(*    Proof .
      move=> x y; rewrite ltr_lerne /negb; case D: (x == y) .
      + by rewrite (eqP D) ler_refl .
      + by rewrite orbF andbT .
    Qed .
*)

    Lemma ler_refl : reflexive (@lebDef G) .
    Proof. by move=> x; rewrite ler_ltreq eqxx orbT. Qed.

    Lemma ler_antisym : forall (x y : G), x <<= y -> y <<= x -> x = y .
    Proof .
      case: ltr_sorderb => h3 h4 x y; rewrite !ler_ltreq.
      case/orP=> hxy; last by move/eqP: hxy.
      case/orP=> hyx; last by move/eqP: hyx.
      by move: (h4 _ _ _ hxy hyx); rewrite (h3 x).
    Qed .

    Lemma ler_trans : transitive (@lebDef G) .
    Proof .
      case: ltr_sorderb=> h1 h2.
      move=> x y z; rewrite !ler_ltreq; case/orP; last first.
        move/eqP->; case/orP; by [move-> | move/eqP->; rewrite eqxx orbT].
      move=> hyx; case/orP; last by move/eqP<-; rewrite hyx.
      by move=> hxz; rewrite (h2 _ _ _ hyx).
    Qed.

    Lemma ler_order : orderb (@lebDef G) .
    Proof . 
      constructor.
      - exact: ler_refl.
      - move=> x y; case/andP; exact: ler_antisym.
      - exact: ler_trans.
    Qed.

    Lemma ler_total : forall x y, (x <<= y) || (y <<= x) .
    Proof . by case G => [T [? []]] . Qed .

    Lemma ler_lcompat : lcompatible (@lebDef G) .
    Proof . 
      move=> x y z; rewrite !ler_ltreq => px.
      case/orP; last by move/eqP->; rewrite eqxx orbT.
      move=> hyz; case/orP: px => hx; first by rewrite ltr_lcompat.
      by rewrite -(eqP hx) !mul0r eqxx orbT.
    Qed.

    Lemma ler_rcompat : rcompatible (@lebDef G).
    Proof. by move=> x y z; rewrite mulrC [z * _]mulrC; exact: ler_lcompat. Qed.

    Lemma eq_ler : forall x y, (x == y) = (x <<= y) && (y <<= x) .
    Proof .
      move=> x y; apply/idP/idP .
      + by move/eqP => ->; rewrite ler_refl .
      + by case/andP=> Hxy Hyx; rewrite (ler_antisym Hxy Hyx) .
    Qed .

    (* ------------------------------------------------------------------ *)



    Lemma ltr_lerne : forall x y, (x <<! y) = (x <<= y) && (x != y) .
    Proof . 
      move=> x y; rewrite ler_ltreq; case e: (x <<! y); rewrite /= ?andbN //.
      by case exy: (x == y) e => //; rewrite (eqP exy) ltr_irrefl.
    Qed .

    Lemma ltr_ne : forall x y, (x <<! y) -> (x != y) .
    Proof. by move=> x y; rewrite ltr_lerne; case/andP. Qed.

    Lemma ltrW : forall x y, x <<! y -> x <<= y .
    Proof . by move=> x y H; rewrite ler_ltreq H . Qed .

    Lemma lerNgtr : forall x y, (x <<= y) = ~~ (y <<! x).
    Proof.
      move=> x y; rewrite ltr_lerne eq_ler; case e: (y <<= x); rewrite ?negbK //=.
      by move: (ler_total x y); rewrite e orbF.
    Qed.

    Lemma ltr_ler_trans :
      forall x y z, x <<! y -> y <<= z -> x <<! z .
    Proof .
      move=> x y z Hxy Hyz; rewrite ltr_lerne; apply/andP; split .
      + by apply ler_trans with y; first apply ltrW .
      + apply/eqP; move=> H; subst z .
        rewrite ltr_lerne in Hxy; case/andP: Hxy => Hxy .
        by rewrite eq_ler Hyz Hxy .
    Qed .


    Lemma ler_ltr_trans : forall x y z,
      x <<= y -> y <<! z -> x <<! z.
    Proof.
      move=> x y z Hxy Hyz; rewrite ltr_lerne; apply/andP; split .
      + by apply ler_trans with y; last apply ltrW .
      + apply/eqP; move=> H; subst z .
        rewrite ltr_lerne in Hyz; case/andP: Hyz => Hyz .
        by rewrite eq_ler Hyz Hxy .
      Qed.
    (* ------------------------------------------------------------------ *)

    Lemma ltrN : forall x y, x <<! y -> ~~ (y <<! x).
    Proof. 
      by move=> x y; case e: (y <<! x) => //; move/(ltr_trans e); rewrite ltr_irrefl.
    Qed.


    Lemma ltrNger : forall x y, (x <<! y) = ~~ (y <<= x).
    Proof .
      by move=> x y; rewrite lerNgtr negbK .
    Qed .

    (* ------------------------------------------------------------------ *)
    Lemma lerTl : forall x y, x <<= y -> forall z, x+z <<= y+z .
    Proof . by case G => T [? []] . Qed .

    Lemma lerTr : forall x y, x <<= y -> forall z, z+x <<= z+y .
    Proof .
      by move=> x y Hxy z; rewrite ![z+_]addrC; apply lerTl .
    Qed .

    Lemma lerTlb : forall z x y, (x+z <<= y+z) = (x <<= y) .
    Proof .
      move=> z x y; apply /idP/idP => H; last by apply lerTl .
      rewrite -[x](addr0) -(addrN z) -[y](addr0) -(addrN z) .
      by rewrite !addrA; apply lerTl .
    Qed .

    Lemma lerTrb : forall z x y, (z+x <<= z+y) = (x <<= y) .
    Proof . by move=> z x y; rewrite ![z+_]addrC; apply lerTlb . Qed .

    (* ------------------------------------------------------------------ *)
    Lemma ltrTl : forall x y, x <<! y -> forall z, x+z <<! y+z .
    Proof .
      move=> x y H z; rewrite ltr_lerne; apply/andP; split .
      + by apply lerTl; apply ltrW .
      + rewrite ltr_lerne in H; case/andP: H => _ H .
        by apply/eqP => Hz; rewrite (addIr Hz) eqxx in H .
    Qed .

    Lemma ltrTr : forall x y, x <<! y -> forall z, z+x <<! z+y .
    Proof .
      by move=> x y Hxy z; rewrite ![z+_]addrC; apply ltrTl .
    Qed .

    Lemma ltrTlb : forall z x y, (x+z <<! y+z) = (x <<! y) .
    Proof .
      move=> z x y; apply/idP/idP => H; last by apply ltrTl .
      rewrite -[x](addr0) -(addrN z) -[y](addr0) -(addrN z) .
      by rewrite !addrA; apply ltrTl .
    Qed .

    Lemma ltrTrb : forall z x y, (z+x <<! z+y) = (x <<! y) .
    Proof . by move=> z x y; rewrite ![z+_]addrC; apply ltrTlb . Qed .

    (* ------------------------------------------------------------------ *)
    Lemma lerT :
      forall (x₁ y₁ x₂ y₂ : G), x₁ <<= y₁ -> x₂ <<= y₂ -> x₁ + x₂ <<= y₁ + y₂ .
    Proof .
      move=> x₁ y₁ x₂ y₂ Hx Hy; apply ler_trans with (x₁+y₂) .
      by apply lerTr . by apply lerTl .
    Qed .

    Lemma lerT0 :
      forall (x y : G), 0 <<= x -> 0 <<= y -> 0 <<= x + y .
    Proof .
      by move=> x y Hx Hy; rewrite -[0]addr0; apply lerT .
    Qed .


    Lemma ler0T :
      forall (x y : G), x <<= 0 -> y <<= 0 -> x + y <<= 0.
    Proof .
      by move=> x y Hx Hy; rewrite -[0]add0r; apply lerT .
    Qed .
      
    Lemma ltrT :
      forall (x₁ y₁ x₂ y₂ : G), x₁ <<! y₁ -> x₂ <<! y₂ -> x₁ + x₂ <<! y₁ + y₂ .
    Proof .
      move=> x₁ y₁ x₂ y₂ H1 H2; apply ltr_ler_trans with (y₁ + x₂) .
      - by apply ltrTl .
      - by apply: lerT; rewrite ?ler_refl //; apply: ltrW.
    Qed .

    Lemma ltr_lerT :
      forall (x₁ y₁ x₂ y₂ : G), x₁ <<! y₁ -> x₂ <<= y₂ -> x₁ + x₂ <<! y₁ + y₂ .
    Proof .
      move=> x₁ y₁ x₂ y₂ H1 H2; apply ltr_ler_trans with (y₁ + x₂) .
      by apply ltrTl . by apply lerTr .
    Qed .

    Lemma ltrT0 :
      forall (x y : G), 0 <<! x -> 0 <<! y -> 0 <<! x + y .
    Proof .
      move=> x y Hx Hy; rewrite -[0]addr0; apply ltrT => //.
    Qed .

    Lemma ltr0T :
      forall (x y : G), x <<! 0 -> y <<! 0 -> x + y <<! 0.
    Proof .
      by move=> x y Hx Hy; rewrite -[0]add0r; apply ltrT .
    Qed .



    (* ------------------------------------------------------------------ *)
    Lemma ler_oppger : forall x y, (-x <<= -y) = (y <<= x) .
    Proof .
      move=> x y; rewrite -(lerTlb x) addNr -(lerTrb y) .
      by rewrite addrA addrN addr0 add0r .
    Qed .

    Lemma le0r_geNr0 : forall x, (0 <<= -x) = (x <<= 0) .
    Proof . by move => x; rewrite -{1}oppr0 ler_oppger . Qed .

      Lemma ger0_leNr0 : forall x, (0 <<= x) = (- x <<= 0).
      Proof. by move=> x; rewrite -{2}oppr0 ler_oppger. Qed.

    Lemma ltr_oppgtr : forall x y, (-x <<! -y) = (y <<! x) .
    Proof .
      move=> x y .
      rewrite !ltr_lerne ler_oppger; case (y <<= x) => //= .
      apply congr1; apply/eqP/eqP => [H|->//] .
      by rewrite -[y]opprK -[x]opprK H .
    Qed .

    Lemma lt0r_gtNr0 : forall x, (0 <<! -x) = (x <<! 0) .
    Proof . by move=> x; rewrite -{1}oppr0 ltr_oppgtr . Qed .

      Lemma gtr0_ltNr0 : forall x, (0 <<! x) = (- x <<! 0).
      Proof. by move=> x; rewrite -[x]opprK lt0r_gtNr0 opprK. Qed.

    Lemma opp_ler_ler0 : forall x, ( -x <<= x) = (0 <<= x).
      Proof.
        move=> x;rewrite -(lerTlb x) addNr. 
        case e : (0 <<= x); first by rewrite lerT0 //.
        by apply: negbTE; rewrite lerNgtr negbK ltr0T // ltrNger e.
      Qed.

    Lemma opp_lrr_lrr0 : forall x, ( -x <<! x) = (0 <<! x).
      Proof.
        move=> x;rewrite -(ltrTlb x) addNr. 
        case e : (0 <<! x); first by rewrite ltrT0 //.
        by apply: negbTE; rewrite ltrNger negbK ler0T // lerNgtr e.
      Qed.

    Lemma ler_opp_ler0 : forall x, ( x <<= -x) = (x <<= 0).
      Proof.
        move=> x;rewrite -(lerTlb x) addNr. 
        case e : (x <<= 0); first by rewrite ler0T //.
        by apply: negbTE; rewrite lerNgtr negbK ltrT0 // ltrNger e.
      Qed.

    Lemma lrr_opp_lrr0 : forall x, ( x <<! -x) = (x <<! 0).
      Proof.
        move=> x;rewrite -(ltrTlb x) addNr. 
        case e : (x <<! 0); first by rewrite ltr0T //.
        by apply: negbTE; rewrite ltrNger negbK lerT0 // lerNgtr e.
      Qed.



    (* ------------------------------------------------------------------ *)
    Lemma ler_0_lcompat : forall x y, 0 <<= x -> 0 <<= y -> 0 <<= x * y .
    Proof .
      by move=> x y Hx Hy; rewrite -[0](mulr0 x); apply ler_lcompat .
    Qed .

    Lemma ler_neg0_lcompat : forall x y, x <<= 0 -> y <<= 0 -> 0 <<= x * y .
    Proof .
      move=> x y Hx Hy .
      by rewrite -mulrNN; apply ler_0_lcompat; rewrite le0r_geNr0 .
    Qed .

    Lemma ltr_0_1 : 0 <<! (1 : G) .
    Proof .
      rewrite ltr_lerne /negb eq_sym oner_eq0 andbT .
      case/orP: (ler_total 0 1) => // H .
      by rewrite -[1](mulr1 1); apply ler_neg0_lcompat .
    Qed .


    (* ------------------------------------------------------------------ *)
    Lemma ler_add_0l : forall x y, 0 <<= x -> 0 <<= y -> x+y = 0 -> x = 0 .
    Proof .
      move=> x y Hx Hy; move/(congr1 (+%R^~ -y)) .
      rewrite -addrA addrN addr0 add0r; move=> H; subst x .
      rewrite -ler_oppger oppr0 in Hy .
      by apply/eqP; rewrite eq_ler Hx Hy .
    Qed .

    Lemma ler_add_0r : forall x y, 0 <<= x -> 0 <<= y -> x+y = 0 -> y = 0 .
    Proof .
      move=> x y Hx Hy Hxy; apply ler_add_0l with x => // .
      by rewrite addrC .
    Qed .

    (* ------------------------------------------------------------------ *)
    CoInductive ler_xor_gtr (x y : G) : bool -> bool -> Set :=
    | LerNotGtr of x <<= y : ler_xor_gtr x y true  false
    | GtrNotLer of y <<! x : ler_xor_gtr x y false true  .

    CoInductive ltr_xor_ger (x y : G) : bool -> bool -> Set :=
    | LtrNotGer of x <<! y : ltr_xor_ger x y true  false
    | GerNotLtr of y <<= x : ltr_xor_ger x y false true  .

    Lemma lerP : forall x y, ler_xor_gtr x y (x <<= y) (y <<! x) .
    Proof.
      move=> x y; rewrite ltrNger; case Hxy: (x <<= y); constructor=> // .
      by rewrite ltrNger Hxy .
    Qed.

    Lemma ltrP : forall x y, ltr_xor_ger x y (x <<! y) (y <<= x) .
    Proof .
      move=> x y; rewrite lerNgtr; case Hxy: (x <<! y); constructor=> // .
      by rewrite lerNgtr Hxy .
    Qed .

    CoInductive compare x y : bool -> bool -> bool -> Set :=
    | CompareLt of x <<! y : compare x y true  false false
    | CompareGt of y <<! x : compare x y false true  false
    | CompareEq of x =   y : compare x y false false true  .

    Lemma compareP : forall x y, compare x y (x <<! y) (y <<! x) (x == y) .
    Proof .
      move=> x y; rewrite ltrNger eq_ler andbC ltr_lerne .
      case: ltrP; [by constructor | rewrite ler_ltreq; case: lerP => //=] .
      + by move=> _; move/eqP => ->; rewrite eqxx; constructor .
      + by move=> Hxy _; rewrite (ltr_ne Hxy); constructor .
    Qed .

    Lemma ltrNgtr : forall x y, x <<! y -> ~~(y <<! x) .
    Proof . by move=> x y; case: compareP . Qed .

    (* ------------------------------------------------------------------ *)

    Lemma χ0_ltr : forall n, (0 : G) <<! 1 *+ (n.+1).
      have HnSn : forall n, (n%:R : G) <<! n.+1%:R .
      + by elim=> [|n IH]; [apply ltr_0_1 | rewrite 2!mulrS; apply ltrTr] .
      elim=> [|n IH]; [by apply ltr_0_1 | apply: ltr_trans] .
      by apply IH . by rewrite 2!mulrS; apply ltrTr; apply HnSn .
    Qed .

    Lemma χ0 : forall n, 1 *+ n.+1 != 0 :> G.
    Proof .
      move=> n; case D: (n.+1%:R == 0) => //= .
      by move/eqP: D => D; have H := χ0_ltr n; rewrite D ltr_irrefl in H .
    Qed .


    Lemma sign_posR : forall x, 0 <<! x -> sign x = 1 .
    Proof . by move=> x hx; rewrite /sign hx. Qed.


    Lemma sign_negR : forall x, x <<! 0 -> sign x = -1 .
    Proof . by move=> x hx; rewrite /sign hx (negbTE (ltrN hx)). Qed.

    Lemma sign0 : sign 0 = 0 :> G.
    Proof . by rewrite /sign !ltr_irrefl . Qed .

    Lemma sign0P : forall x, reflect (sign x = 0) (x == 0) .
    Proof .
      move=> x; rewrite /sign; case: (compareP 0 x)=> H; last first.
      + by rewrite -H eqxx; constructor.
      + rewrite (negbTE (ltr_ne H)); constructor.
        by  apply/eqP; rewrite oppr_eq0 nonzero1r.
      + rewrite eq_sym (negbTE (ltr_ne H)); constructor.
        by  apply/eqP; rewrite nonzero1r.
      Qed.


    Lemma sign_codomP :
      forall x, [\/ sign x = 1, sign x = -1 | sign x = 0] .
    Proof .
      move=> x; case: (compareP 0 x) => H; [apply Or31 | apply Or32 | apply Or33] .
      - by apply: sign_posR.
      - by apply: sign_negR. 
      - by rewrite -H sign0 .
    Qed .


    (* ------------------------------------------------------------------ *)
    Lemma absr_nneg : forall x, 0 <<= x -> absr x = x .
    Proof .
      move=> x Hx; rewrite /absr ltrNger .

      by case D: (0 <<= x) => //=; rewrite Hx in D .
    Qed .

    Lemma absr_npos : forall x, x <<= 0 -> absr x = -x .
    Proof .
      move=> x Hx; rewrite /absr ltrNger; case Hx': (0 <<= x) => //= .
      have Hx0: x = 0 by apply/eqP; rewrite eq_ler Hx Hx' .
      by rewrite Hx0 oppr0 .
    Qed .

    Lemma absr_neg : forall x, x <<! 0 -> absr x = -x .
    Proof . by move=> x Hx; apply absr_npos; apply ltrW . Qed .

    Lemma absr0 : absr 0 = 0 :> G .
    Proof . by rewrite /absr ltr_irrefl . Qed .

    Lemma absrpos : forall x, 0 <<= absr x .
    Proof .
      move=> x; case: (ltrP x 0) => H .
      + by rewrite absr_neg // le0r_geNr0; apply ltrW .
      + by rewrite absr_nneg.
    Qed .

    Lemma absrK : forall x, absr (absr x) = absr x .
    Proof . by move=> x; rewrite absr_nneg // absrpos . Qed .

    Lemma absr_oppr : forall x, absr(-x) = absr x.
    Proof.
      move=> x.
      case a : (0 <<! x).
        by rewrite (absr_nneg (ltrW a)) absr_npos ?opprK // 
             -oppr0 ler_oppger ltrW.
        move: (negbT a); rewrite -lerNgtr => a'; rewrite (absr_npos a').
        by rewrite absr_nneg // -ler_oppger opprK oppr0.
    Qed.

    Lemma absr_sign : forall x , (absr x) = (sign x) * x .
    Proof .
      move=> x; case: (compareP x 0) => h.
      + by rewrite /absr h; move/sign_negR: h=> ->; rewrite mulN1r.
      + by rewrite absr_nneg ?ltrW //; move/sign_posR: h=> ->; rewrite mul1r .
      + by rewrite h sign0 absr0 mul0r.
    Qed .



    Lemma absr_addr :
      forall x y, absr (x + y) <<= (absr x) + (absr y).
      move=> x y; rewrite !absr_sign.
      case: (compareP x 0) => hx.
      - rewrite (sign_negR hx) mulN1r; case: (compareP y 0) => hy.
        + rewrite (sign_negR hy) mulN1r mulr_addr.
          rewrite (_ : sign _ = -1) ?mulN1r ?ler_refl //; apply: sign_negR.
          by apply: ltr0T.
        + rewrite (sign_posR hy) mul1r ; case: (compareP (x + y) 0) => hxy.
          * by rewrite (sign_negR hxy) mulr_addr !mulN1r lerTrb opp_ler_ler0 ltrW.
          * by rewrite (sign_posR hxy) mul1r lerTlb ler_opp_ler0 ltrW.
          * by rewrite hxy sign0 mul0r lerT0 // ?le0r_geNr0 ltrW.
        + by rewrite hy mulr0 !addr0 (sign_negR hx) mulN1r ler_refl.
      - rewrite (sign_posR hx) mul1r;  case: (compareP y 0) => hy.
        + rewrite (sign_negR hy) mulN1r mulr_addr; case: (compareP (x + y) 0) => hxy.
          * by rewrite (sign_negR hxy) !mulN1r lerTlb opp_ler_ler0 ltrW.
          * by rewrite (sign_posR hxy) !mul1r lerTrb ler_opp_ler0 ltrW.
          * by rewrite hxy sign0 !mul0r addr0 lerT0 // ?le0r_geNr0 ltrW.
        + rewrite (sign_posR hy) mul1r (_ : sign _ = 1) ?mul1r ?ler_refl //.
          by apply: sign_posR; apply: ltrT0.
        + by rewrite hy mulr0 !addr0 (sign_posR hx) mul1r ler_refl.
      - by rewrite hx mulr0 !add0r ler_refl.
    Qed. 


Lemma absr_lt : forall x y, absr x <<! y -> x <<! y.
Proof.
move=> x y h. 
have py : 0 <<! y by apply: (ler_ltr_trans (absrpos x)).
case: (compareP x 0) => h2.
- by rewrite (ltr_trans h2).
- by rewrite -[x]absr_nneg // ltrW.
- by rewrite h2.
Qed.

Lemma absr_le : forall x y, absr x <<= y -> x <<= y.
Proof.
move=> x y h. 
have py : 0 <<= y by apply: (ler_trans (absrpos x)).
case: (compareP x 0) => h2.
- by rewrite ltrW // (ltr_ler_trans h2).
- by rewrite -[x]absr_nneg // ltrW.
- by rewrite h2.
Qed.

Lemma lt_absr : forall x y, absr x <<! y -> - y <<! x.
Proof.
move=> x y h.
have py : 0 <<! y by apply: (ler_ltr_trans (absrpos x)).
case: (compareP x 0) => h2.
- by rewrite -[x]opprK ltr_oppgtr -[- x]absr_npos // ltrW.
- by rewrite -[x]opprK -ltr_oppgtr !opprK; apply: ltr_trans py; rewrite -gtr0_ltNr0.
- by rewrite h2 -gtr0_ltNr0.
Qed.

Lemma le_absr : forall x y, absr x <<= y -> - y <<= x.
Proof.
move=> x y h.
have py : 0 <<= y by apply: (ler_trans (absrpos x)).
case: (compareP x 0) => h2.
- by rewrite -[x]opprK ler_oppger -[- x]absr_npos // ltrW.
- by rewrite -[x]opprK -ler_oppger !opprK; apply: ler_trans py; rewrite -ger0_leNr0 ltrW.
- by rewrite h2 -ger0_leNr0.
Qed.

(* ------------------------------------------------------------------ *)
Lemma ler_addl_abs :
  forall x₁ x₂, x₁ <<= x₂ ->
    forall y, (absr y) <<= (x₂ - x₁) ->
      x₁ <<= x₂ + y .
Proof.
move=> x1 x2 hx12 y; move/le_absr. rewrite -(@lerTlb x2) addrC oppr_add opprK.
by rewrite  addrA addrN add0r addrC.
Qed.


    Lemma ler0_addl_abs :
      forall x y, 0 <<= x -> (absr y) <<= x -> 0 <<= x + y .
    Proof .
      by move=> x y Hx Hy; apply ler_addl_abs; last rewrite oppr0 addr0 .
    Qed .
  End OComringTheory .

(*
  Module OField .

    Record class_of (R : Type) : Type := Class {
      base1 :> GRing.Field.class_of R;
      ext :> OComRing.mixin_of (GRing.Field.Pack base1 R)
    } .

(*    Coercion base2 R m := OComRing.Class (@ext R m).*)
    Coercion base2 R m := @OComRing.Class R _ (@ext R m).


    Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.

    Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
    Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
      let: Pack T c _ := cT return K _ (class cT) in k _ c.
    Definition repack cT : _ -> Type -> type :=
      let k T c p := p c in unpack k cT.

(* Mixin here ? *)
    Definition pack := 
      let k T c m := Pack (@Class T c m) T in GRing.Field.unpack k.

    Definition eqType          cT := Equality.Pack             (class cT) cT.
    Definition choiceType      cT := Choice.Pack               (class cT) cT.
    Definition zmodType        cT := GRing.Zmodule.Pack        (class cT) cT.
    Definition ringType        cT := GRing.Ring.Pack           (class cT) cT.
    Definition unitRingType    cT := GRing.UnitRing.Pack       (class cT) cT.
    Definition comRingType     cT := GRing.ComRing.Pack (class cT) cT.
    Definition comUnitRingType cT := GRing.ComUnitRing.Pack       (class cT) cT.
    Definition idomainType     cT := GRing.IntegralDomain.Pack (class cT) cT.
    Coercion   fieldType       cT := GRing.Field.Pack (class cT) cT.
    Coercion   oComRingType    cT := OComRing.Pack (class cT) cT.
    Definition oFieldType cT :=
      @OComRing.Pack (fieldType cT) (class cT) cT.

  End OField .

  Canonical Structure OField.eqType.
  Canonical Structure OField.choiceType.
  Canonical Structure OField.zmodType.
  Canonical Structure OField.ringType.
  Canonical Structure OField.comRingType.
  Canonical Structure OField.unitRingType.
  Canonical Structure OField.comUnitRingType.
  Canonical Structure OField.idomainType.
  Canonical Structure OField.fieldType.
  
  Bind Scope comring_scope with OField.sort .
*)
  Module OField .

    Record class_of (R : Type) : Type := Class {
      base1 :> GRing.Field.class_of R;
      ext :> OComRing.mixin_of (GRing.Field.Pack base1 R)
    } .

    Coercion base2 R m := @OComRing.Class R _ (@ext R m).

    Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.

    Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
    Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
      let: Pack T c _ := cT return K _ (class cT) in k _ c.
    Definition repack cT : _ -> Type -> type :=
      let k T c p := p c in unpack k cT.

(* Mixin here ? *)
    Definition pack := 
      let k T c m := Pack (@Class T c m) T in GRing.Field.unpack k.

    Definition eqType          cT := Equality.Pack             (class cT) cT.
    Definition choiceType      cT := Choice.Pack               (class cT) cT.
    Definition zmodType        cT := GRing.Zmodule.Pack        (class cT) cT.
    Definition ringType        cT := GRing.Ring.Pack           (class cT) cT.
    Definition unitRingType    cT := GRing.UnitRing.Pack       (class cT) cT.
    Definition comRingType     cT := GRing.ComRing.Pack (class cT) cT.
    Definition comUnitRingType cT := GRing.ComUnitRing.Pack       (class cT) cT.
    Definition idomainType     cT := GRing.IntegralDomain.Pack (class cT) cT.
    Coercion   fieldType       cT := GRing.Field.Pack (class cT) cT.
    Coercion   oComRingType    cT := OComRing.Pack (class cT) cT.
    Definition oFieldType cT :=
      @OComRing.Pack (fieldType cT) (class cT) cT.

  End OField .

  Canonical Structure OField.eqType.
  Canonical Structure OField.choiceType.
  Canonical Structure OField.zmodType.
  Canonical Structure OField.ringType.
  Canonical Structure OField.comRingType.
  Canonical Structure OField.unitRingType.
  Canonical Structure OField.comUnitRingType.
  Canonical Structure OField.idomainType.
  Canonical Structure OField.fieldType.
  Canonical Structure OField.oComRingType.

Bind Scope ring_scope with OField.sort.

Section OrderedFieldTheory.

    Variable G : OField.type .
    Implicit Types x y : G.

    Lemma ltr_0_lcompat : forall x y, 0 <<! x -> 0 <<! y -> 0 <<! x * y .
    Proof .
      move=> x y Hx Hy; rewrite ltr_lerne; apply/andP; split .
      + by apply ler_0_lcompat; apply ltrW .
      + rewrite eq_sym mulf_eq0 negb_or .
        by rewrite ![_ == 0]eq_sym (ltr_ne Hx) (ltr_ne Hy) .
    Qed .

    Lemma oppreq_0 : forall x, (x == -x) = (x == 0) .
    Proof .
      move=> x; apply/eqP/eqP => [|->]; last by rewrite oppr0 .
      move/(congr1 (+%R x)); rewrite addrN -{1 2}[x](mul1r) -mulr_addl .
      move/eqP; rewrite mulf_eq0; case/orP; last by move/eqP => -> .
      by rewrite (negbTE (χ0 G 1%nat)).
    Qed.

    Lemma sign_pos : forall x, reflect (sign x = 1) (0 <<! x) .
    Proof .
      move=> x; rewrite /sign; case: (compareP 0 x) => h; constructor => //.
      + by apply/eqP; rewrite eq_sym oppreq_0 nonzero1r.
      + by apply/eqP; rewrite eq_sym nonzero1r.
    Qed .

    Lemma sign_neg : forall x, reflect (sign x = -1) (x <<! 0) .
    Proof .
      move=> x; rewrite /sign; case: (compareP 0 x) => _; constructor=> // .
      + apply/eqP; rewrite oppreq_0; exact: nonzero1r .
      + move/(congr1 -%R); rewrite opprK oppr0; move/eqP .
        by rewrite eq_sym (negbTE (nonzero1r _)) .
    Qed .

    Lemma mulr_sign : forall x y, sign (x * y) = (sign x) * (sign y) .
    Proof .
      move=> x y; case: (compareP 0 x) .
      + case: (compareP 0 y) => Hy Hx .
        * by rewrite !sign_posR ?mul1r //; apply ltr_0_lcompat .
        * rewrite [sign x]sign_posR // !sign_negR ?mul1r // .
          rewrite -lt0r_gtNr0 -mulrN; apply ltr_0_lcompat => // .
          by rewrite lt0r_gtNr0 .
        * by rewrite -Hy mulr0 sign0 mulr0 .
      + case: (compareP 0 y) => Hy Hx .
        * rewrite [sign y]sign_posR // !sign_negR ?mulr1 // .
          rewrite -lt0r_gtNr0 -mulNr; apply ltr_0_lcompat => // .
          by rewrite lt0r_gtNr0 .
        * rewrite [sign x]sign_negR // [sign y]sign_negR // .
          rewrite sign_posR; first by rewrite ?mulrNN ?mulr1 .
          by rewrite -mulrNN; apply ltr_0_lcompat; rewrite lt0r_gtNr0 .
        * by rewrite -Hy mulr0 sign0 mulr0 .
      + by move=> <-; rewrite mul0r sign0 mul0r .
    Qed .

    (* ------------------------------------------------------------------ *)


    Lemma invr_ltr : forall x, (0 <<! x^-1) = (0 <<! x) .
    Proof .
      have Hsign : forall x, x != 0 -> sign (x^-1 * x) = 1 .
      + by move=> x Hx; rewrite mulVf // sign_posR // ltr_0_1 .

      have HP: forall x, 0 <<! x -> 0 <<! x^-1 .
      + move=> x Hx; apply/sign_pos; rewrite -(Hsign x) .
        * rewrite mulr_sign -{1}[sign x^-1]mulr1 .
          by congr (_ * _); symmetry; apply/sign_pos .
        * by rewrite eq_sym; apply (ltr_ne Hx) .

      move=> x; apply/idP/idP; last exact: HP .
      by move=> Hx; rewrite -(invrK x); apply HP .
    Qed .

    Lemma ler_Ilcompat_r :
      forall x y₁ y₂, 0 <<! x -> x * y₁ <<= x * y₂ -> y₁ <<= y₂ .
    Proof .
      move=> x y₁ y₂ Hx Hy .
      rewrite -[y₁](mul1r) -[y₂](mul1r) -[1](@mulVf _ x) 1?eq_sym ?(ltr_ne Hx) //.
      by rewrite -!mulrA; apply ler_lcompat => //; apply ltrW; rewrite invr_ltr .
    Qed .

    Lemma ler_Ilcompat_l :
      forall x y₁ y₂, 0 <<! x -> y₁ * x <<= y₂ * x -> y₁ <<= y₂ .
    Proof .
      move=> x y₁ y₂; rewrite mulrC [y₂ * _]mulrC; exact: ler_Ilcompat_r.
    Qed .

    Lemma ltr_Ilcompat_r :
      forall x y₁ y₂, 0 <<! x -> x * y₁ <<! x * y₂ -> y₁ <<! y₂ .
    Proof .
      move=> x y₁ y₂ Hx Hy .
      rewrite -[y₁](mul1r) -[y₂](mul1r) -[1](@mulVf _ x) 1?eq_sym ?(ltr_ne Hx) //.
      by rewrite -!mulrA; apply ltr_lcompat => //; rewrite invr_ltr .
    Qed .

    Lemma ltr_Ilcompat_l :
      forall x y₁ y₂, 0 <<! x -> y₁ * x <<! y₂ * x -> y₁ <<! y₂ .
    Proof .
      move=> x y₁ y₂; rewrite mulrC [y₂ * _]mulrC; exact: ltr_Ilcompat_r.
    Qed .


    Lemma invr1_ltr0_ltr1 : forall x, 0 <<! x -> (x <<! 1) = (1 <<! x^-1).
      Proof.
        move=> x hx; move:(hx); rewrite ltr_lerne eq_sym; case/andP=> hx1 hx2.
        rewrite -{1}(divff hx2) -{1}(mulr1 x); case e: (1 <<! x^-1).
          by rewrite ltr_lcompat.
        by rewrite ltrNger ler_lcompat // lerNgtr e.
      Qed.

    Lemma invr1_ltr0_1ltr : forall x, 0 <<! x -> (1 <<! x) = (x^-1 <<! 1).
      Proof.
        move=> x hx; apply/idP/idP => h1.
          apply: (ltr_Ilcompat_r hx); rewrite divff // ?mulr1 //.
          by move: hx; rewrite ltr_lerne eq_sym; case/andP.
        move:(hx); rewrite -invr_ltr=> hIx; apply: (ltr_Ilcompat_r hIx).
        by rewrite mulr1 mulVf //; move: hx; rewrite ltr_lerne eq_sym; case/andP.
      Qed.

    Lemma invr1_0ltr_ltr1I : forall x, x <<! 0 -> (x <<! -1) = (-1 <<! x^-1).
      Proof.
        move=> x; rewrite -(opprK x).
      rewrite invrN !ltr_oppgtr -lt0r_gtNr0 opprK; exact: invr1_ltr0_1ltr.
      Qed.

    Lemma invr1_0ltr_ltrI1 : forall x, x <<! 0 -> (-1 <<! x) = (x^-1 <<! -1).
      Proof.
        move=> x; rewrite -(opprK x).
      rewrite invrN !ltr_oppgtr -lt0r_gtNr0 opprK; exact: invr1_ltr0_ltr1.
      Qed.

      (* We cannot define a theory of floor since some ordered comring do not have...*)

    (* ------------------------------------------------------------------ *)
    Lemma Ndiscrete01 : exists x : G, (0 <<! x) && (x <<! 1) .
    Proof .
      have H : (0 : G) <<! 1/(1+1).
      + apply ltr_0_lcompat; first exact: ltr_0_1 .
        rewrite invr_ltr; apply: (χ0_ltr _ 1%nat) .
      exists (1/(1+1)); apply/andP; split=> // .
      rewrite -(ltrTlb (-1)) addrN .
      rewrite -{4}[1](@mulfV _ (1+1)); last exact: (χ0 _ 1) .
      rewrite -mulNr -mulr_addl -mulN1r mulr_addr mulN1r .
      by rewrite addrA addrN add0r mulNr -ltr_oppgtr oppr0 opprK .
    Qed .
 
    Lemma Ndiscrete : forall x z, x <<! z -> exists y, (x <<! y) && (y <<! z) .
    Proof .
      move=> x z Hxz; elim Ndiscrete01=> y; case/andP => Hylow Hyhi .
      exists (y * (z-x) + x); apply/andP; split .
      + rewrite -{1}[x]add0r ltrTlb; apply ltr_0_lcompat => // .
        by rewrite -[0](addrN x) ltrTlb .
      + rewrite -(ltrTlb (-x)) -addrA addrN addr0 .
        rewrite mulrC -{2}[z-x]mulr1; apply ltr_lcompat => // .
        by rewrite -[0](addrN x) ltrTlb .
    Qed .


    Lemma absr_mulr :
      forall x y, absr (x * y) = (absr x) * (absr y) .
    Proof .
      move=> x y; rewrite !absr_sign mulr_sign .
      by rewrite -[_ * x * _]mulrA -[x * (_ * _)]mulrCA !mulrA .
    Qed .



End OrderedFieldTheory.

End GOrdered .

Bind Scope comring_scope with GOrdered.OComRing.sort .

Canonical Structure GOrdered.OComRing.eqType.
Canonical Structure GOrdered.OComRing.choiceType.
Canonical Structure GOrdered.OComRing.zmodType.
Canonical Structure GOrdered.OComRing.ringType.
Canonical Structure GOrdered.OComRing.comringType.

Notation ocomringType  := (GOrdered.OComRing.type) .
Notation OcomringType  := (GOrdered.OComRing.pack) .
Notation OcomringMixin := (GOrdered.OComRing.Mixin) .

Canonical Structure GOrdered.OField.eqType.
Canonical Structure GOrdered.OField.choiceType.
Canonical Structure GOrdered.OField.zmodType.
Canonical Structure GOrdered.OField.ringType.
Canonical Structure GOrdered.OField.comRingType.
Canonical Structure GOrdered.OField.unitRingType.
Canonical Structure GOrdered.OField.comUnitRingType.
Canonical Structure GOrdered.OField.idomainType.
Canonical Structure GOrdered.OField.fieldType.
Canonical Structure GOrdered.OField.oComRingType.

Notation ofieldType  := (GOrdered.OField.type) .
Notation OfieldType  := (GOrdered.OField.pack) .


Notation "x <<= y" := (GOrdered.leb x y) .
Notation "x <<! y" := (GOrdered.ltb x y) .

(* -------------------------------------------------------------------- *)
Module Min .
  Section Defs .
    Variable R : ocomringType .
    Implicit Types x y : R .

    Definition minr x y := if x <<! y then x else y .

    Section MinB .
      Variable I : eqType .
      Variable P : pred I .
      Variable F : I -> R .

      Definition minB (x0 : R) (r : seq I) :=
        if   (filter P r) is x::xs
        then \big[minr/(F x)]_(i <- xs) (F i)
        else x0 .
    End MinB .
  End Defs .
End Min .

Notation minr := (@Min.minr _) .
Notation minB := (@Min.minB _ _) .

Section MinTheory .
  Variable R : ocomringType .

  Import GOrdered .

  Lemma minrC : commutative (@Min.minr R) .
  Proof . by move=> x y; rewrite /minr; case: (compareP x y) . Qed .

  Lemma minrA : associative (@Min.minr R) .
    move=> x y z; rewrite /minr .
    (case: (compareP y z); last (move=> <-));
    (case: (compareP x y); last (move=> <-));
      try solve
        [ by do! (move=> H; rewrite ?H ?(negbTE (ltrNgtr H)) => {H})
        | by rewrite ltr_irrefl ] .
    + by move=> Hxy Hyz; rewrite (ltr_trans Hxy Hyz) .
    + move=> Hyx Hzy; rewrite (negbTE (ltrNgtr Hzy)) .
      by rewrite (negbTE (ltrNgtr (ltr_trans Hzy Hyx))) .
  Qed .

  Lemma minrCA : left_commutative (@Min.minr R) .
  Proof .
    by move=> x y z; rewrite minrA [minr x y]minrC -minrA .
  Qed .

  Lemma minrAC : right_commutative (@Min.minr R) .
  Proof .
    by move=> x y z; rewrite -minrA [minr y z]minrC minrA .
  Qed .

  Lemma minrl : forall (x y : R), minr x y <<= x .
  Proof .
    by move=> x y; rewrite /minr; case: (ltrP x y); rewrite // ler_refl .
  Qed .

  Lemma minrr : forall (x y : R), minr x y <<= y .
  Proof .
    by move=> x y; rewrite minrC; apply minrl .
  Qed .

  Section minB .
    Variable I  : eqType .
    Variable P  : pred I .
    Variable F  : I -> R .
    Variable x0 : R .

    Lemma minB_nil : minB P F x0 [::] = x0 .
    Proof . by [] . Qed .

    Lemma minB_seq1 : forall x, P x -> minB P F x0 [:: x] = (F x) .
    Proof . by move=> x H; rewrite /minB /filter H big_nil . Qed .

    Lemma minB_cons :
      forall x xs, P x -> has P xs
        -> minB P F x0 (x::xs) = minr (F x) (minB P F x0 xs) .
    Proof .
      move=> x xs HPx HPxs; rewrite {1}/minB /= HPx .
      rewrite has_filter in HPxs; move/eqP: HPxs => HPxs .
      rewrite /minB; case D: (filter P xs) => [|z₁ zs] {D HPx} // .
      elim: zs x z₁ => [|z₂ zs IH] x z₁ .
      + by rewrite unlock /= minrC .
      + by rewrite big_cons !IH minrCA .
    Qed .

    Lemma minB_head :
      forall x xs, ~~ (has P xs) ->
        minB P F x0 (x::xs) = (if P x then F x else x0) .
    Proof .
      move=> x xs HPxs; rewrite /minB /= .
      rewrite has_filter negbK in HPxs; rewrite (eqP HPxs) .
      by case (P x); rewrite ?big_nil .
    Qed .

    Lemma minB_tail :
      forall x xs, ~~ (P x) -> minB P F x0 (x::xs) = minB P F x0 xs .
    Proof .
      by move=> x xs HPx; rewrite {1}/minB /= (negbTE HPx) .
    Qed .

    Lemma minB_empty :
      forall xs, ~~ (has P xs) ->  minB P F x0 xs = x0 .
    Proof .
      elim=> [|x xs IH] //= .
      rewrite negb_orb; case/andP=> HPx HPxs .
      by rewrite minB_tail // IH .
    Qed .

    Lemma minBE :
      forall (r : seq I),
        forall z, z \in r -> P z -> minB P F x0 r <<= F z .
    Proof .
      elim=> [|x xs IH] // z Hmem Hpz .
      rewrite in_cons in Hmem; case/orP: Hmem => [|Hz] .
      + move/eqP => <-; case D: (has P xs) .
        * by rewrite minB_cons // minrl .
        * by rewrite minB_head /negb ?D // Hpz ler_refl .
      + have Htail: has P xs by (apply/hasP; exists z) .
        case D: (P x) .
        * rewrite minB_cons //; apply: ler_trans .
          by apply minrr . by apply IH .
        * by rewrite minB_tail /negb ?D //; apply IH .
    Qed .

    Lemma minBP :
      forall d (r : seq I), has P r ->
        exists i,
          let x := nth d r i in
            [/\ (i < size r), P x & (minB P F x0 r = F x)] .
    Proof .
      move=> d; elim=> [|x xs IH] //= H .
      case Dhead: (P x); case Dtail: (has P xs) .
      + rewrite minB_cons // /minr; case: ltrP => _ .
        * by exists 0%N => // .
        * by elim (IH Dtail)=> i [Hsize HPi Hmini]; exists i.+1 .
      + exists 0%N; split=> // .
        by rewrite minB_head ?Dhead //=; apply negbT .
      + elim (IH Dtail)=> i [Hsize HPi Hmini]; exists i.+1 .
        by split=> //=; rewrite minB_tail //; apply negbT .
      + by rewrite Dhead Dtail in H .
    Qed .

    Lemma minBI :
      forall (r : seq I), has P r -> (minB P F x0 r) \in (map F r) .
    Proof .
      move=> r; move/hasP=> [d Hdr HPd]; elim (@minBP d r) .
      + move=> n [Hsize HP Heq]; apply/nthP; exists n .
        * by rewrite size_map .
        * by rewrite Heq -(nth_map d x0) //; reflexivity .
      + by apply/hasP; exists d .
    Qed .

    Lemma min_fall_lt :
      forall (r : seq I) x, has P r
        -> (forall z, z \in r -> P z -> x <<! F z)
        -> x <<! minB P F x0 r .
    Proof .
      elim=> [|x xs IH] // z Hpz H .
      case Dhead: (P x); case Dtail: (has P xs) .
      + rewrite minB_cons // /minr; case: (ltrP (F x)) => D .
        * by apply H => //; rewrite in_cons eqxx .
        * by apply IH => // w Hw HPw; apply H => //; rewrite in_cons Hw orbT .
      + rewrite minB_head /negb ?Dtail // Dhead .
        by apply H => //; rewrite in_cons eqxx .
      + rewrite minB_tail /negb ?Dhead //; apply IH => // .
        by move=> w Hw HPw; apply H => //; rewrite in_cons Hw orbT .
      + by rewrite /= Dhead Dtail in Hpz .
    Qed .

    Lemma min_fall_le :
      forall (r : seq I) x, has P r
        -> (forall z, z \in r -> P z -> x <<= F z)
        -> x <<= minB P F x0 r .
    Proof .
      elim=> [|x xs IH] // z Hpz H .
      case Dhead: (P x); case Dtail: (has P xs) .
      + rewrite minB_cons // /minr; case: (ltrP (F x)) => D .
        * by apply H => //; rewrite in_cons eqxx .
        * by apply IH => // w Hw HPw; apply H => //; rewrite in_cons Hw orbT .
      + rewrite minB_head /negb ?Dtail // Dhead .
        by apply H => //; rewrite in_cons eqxx .
      + rewrite minB_tail /negb ?Dhead //; apply IH => // .
        by move=> w Hw HPw; apply H => //; rewrite in_cons Hw orbT .
      + by rewrite /= Dhead Dtail in Hpz .
    Qed .
  End minB .
End MinTheory .

Notation "\minB_ ( i | P ) F" :=
  (minB (fun i => P%B) (fun i => F) 0 (index_enum _))
  (at level 36, F at level 36, i at level 50) .

Notation "\minB_ ( i \in I | P ) F"
  := (\minB_(i | (i \in I) && P) F)
  (at level 36, F at level 36, i, A at level 50) .
