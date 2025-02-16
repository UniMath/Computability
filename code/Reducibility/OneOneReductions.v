Require Import init.imports.
Require Import Decidability.DecidablePredicates.
Require Import Inductive.Predicates.
Require Import Reducibility.ManyOneReductions.

Section OneOneReducibility.

Definition oneonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) := ∑ (f : incl X Y), (ismanyonereduction p q f).

Lemma oneonefun {X Y : UU} (p : X → hProp) (q : Y → hProp) : oneonereduction p q → (X → Y).
intros [f isr]. exact f.
Qed.

Coercion oneonefun : oneonereduction >-> Funclass.

Definition make_oneonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : incl X Y) (isr : ismanyonereduction p q f) : (oneonereduction p q) := (f,, isr).

Definition isoneonereducible {X Y : UU} (p : X → hProp) (q : Y → hProp) := ∥oneonereduction p q∥.

Notation "p ⪯₁ q" := (isoneonereducible p q) (at level 500).

Lemma isapropisoneonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : incl X Y) : isaprop (ismanyonereduction p q f).
Proof.
  apply isapropismanyonereduction.
Qed.

Lemma isapropisoneonereducible {X Y : UU} (p : X → hProp) (q : Y → hProp) : isaprop (isoneonereducible p q).
Proof.
  apply propproperty.
Qed.

Definition oneoneequivalent {X Y : UU} (p : X → hProp) (q : Y → hProp) := (p ⪯₁ q) × (q ⪯₁ p).

Infix "p ≡₁ q" := (oneoneequivalent p q) (at level 50).

Example nooneredeq0 : ¬ (oneonereduction (λ x, ishinh (¬ (x = 0))) (λ x, ishinh (x = 0))).
Proof.
  intros [f isred].
  assert (∑ n : nat, f (S n) != 0).
  + induction (isdeceqnat (f 1) 0).
    * use tpair. exact 1. 
      {simpl. intros eq. destruct f as [f inclf]. simpl in *. apply (negpathssx0 0), invmaponpathsS, (invmaponpathsincl _ inclf). rewrite a, eq. apply idpath. }
    * exact (0,, b).
  + destruct X as [x ineq].
    destruct (isred (S x)) as [impl1 impl2].
    apply ineq.
    use squash_to_prop.
    * exact (f (S x) = 0).
    * apply impl1, hinhpr, negpathssx0.
    * apply isasetnat.
    * apply idfun.
Qed.

End OneOneReducibility.

Section ManyManyOneOneCharacterisation.
  
  Notation "p ⪯₁ q" := (isoneonereducible p q) (at level 500).

  Lemma predcylinder1 {X Z : UU} (p : X → hProp) (z : Z) : (p ⪯₁ (predcylinder p Z)).
  Proof.
    apply hinhpr.
    use make_oneonereduction.
    - use make_incl.
      + intros x. exact (x,, z).
      + admit.
    - simpl. intros x. split; intros ?.
      + exact (X0,, tt).
      + exact (dirprod_pr1 X0).
  Admitted.

  Lemma predcylinder2 {X Z : UU} (p : X → hProp) : ( ismanyonereducible (predcylinder p Z) p).
  Proof.
    apply hinhpr. use make_reduction.
    - intros [x z]. exact x.
    - simpl. intros [x z]. split.
      + simpl. exact (dirprod_pr1).
      + simpl. intros px. exact (px,, tt).
  Qed.     

  Lemma manyone_oneone1 {X Y : UU} (Z : UU) (p : X → hProp) (q : Y → hProp) (g : incl (Y) Z) : (ismanyonereducible q (predcylinder p Z)) → (q ⪯₁ (predcylinder p Z)).
  Proof.
    intros ismo.
    use squash_to_prop.
      exact (reduction q (predcylinder p Z)). exact ismo. apply propproperty. clear ismo. intros [f ismr]. apply hinhpr. 
    use make_oneonereduction.
    - use make_incl.
      + intros y.
        exact ((dirprod_pr1 (f y)),, g (y)).
      + admit.
    - simpl. intros y. destruct (ismr y) as [impl1 impl2].
      apply (impl1,, impl2).
  Admitted.
  
  Lemma isoneonereducible_ismanyonereducible {X Y : UU} (p : X → hProp) (q : Y → hProp) : isoneonereducible p q → ismanyonereducible p q.
  Proof.
    intros isr1. use (squash_to_prop isr1). apply propproperty. intros [? ?]. apply hinhpr. use make_reduction. exact pr1. exact pr2.
  Qed.

  Lemma manymany_oneone2 {X Y Z : UU} (z : Z) (f : incl (Y × Z) Z) (p : X → hProp) (q : Y → hProp) : (ismanyonereducible q p) <-> ((predcylinder q Z) ⪯₁ (predcylinder p Z)).
  Proof. 
    split.
    - intros impl1.
      apply manyone_oneone1. apply f.
      use (isreduciblecomp). exact Y. exact q. apply predcylinder2.
      use (isreduciblecomp). exact X. exact p. apply impl1.
      apply isoneonereducible_ismanyonereducible, predcylinder1, z. 
    - intros.
      use (isreduciblecomp). exact (Y × Z). exact (predcylinder q Z).
      apply isoneonereducible_ismanyonereducible, predcylinder1, z.
      use (isreduciblecomp). exact (X × Z). exact (predcylinder p Z).
      apply isoneonereducible_ismanyonereducible, X0.
      apply predcylinder2.
  Qed.
End ManyManyOneOneCharacterisation.