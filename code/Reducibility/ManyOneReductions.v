Require Import init.imports.
Require Import Decidability.DecidablePredicates.

  
Section ManyOneReducibility.

Definition ismanyonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) := ∏ (x : X), p x <-> q (f x).

Definition reduction {X Y : UU} (p : X → hProp) (q : Y → hProp) := ∑ (f : X → Y), ismanyonereduction p q f.

Definition make_reduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) (isrct : ismanyonereduction p q f) : (reduction p q) := (f,, isrct).

Definition ismanyonereducible {X Y : UU} (p : X → hProp) (q : Y → hProp) := ∥reduction p q∥.

Notation "p ≼ q" := (ismanyonereducible p q) (at level 500).

Lemma isapropismanyonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) : (isaprop (ismanyonereduction p q f)).
Proof.
  apply impred_isaprop; intros.
  apply isapropdirprod; apply isapropimpl; apply propproperty.
Qed.

Lemma reductiontodecidability {X Y : UU} (p : X → hProp) (q : Y → hProp) : (p ≼ q) → (deptypeddecider q) → (deptypeddecider p).
Proof.
  intros rct dep1.
  use squash_to_prop.
  - exact (reduction p q).
  - exact rct.
  - apply isapropdeptypeddecider.
  - intros [f isrct] x.
    destruct (isrct x) as [impl1 impl2].
    induction (dep1 (f x)).
    + left. exact (impl2 a).
    + right. intros px. apply b. exact (impl1 px).
Qed.

Lemma isreductionidfun {X : UU} (p : X → hProp) : (ismanyonereduction p p (idfun X)).
Proof.
  intros x; split; apply idfun.
Qed.

(* Many one reducibility is a preorder. *)

Lemma reductionrefl {X : UU} (p : X → hProp) : reduction p p.
Proof.
  use make_reduction.
  - exact (idfun X).
  - exact (isreductionidfun p).
Qed.

Lemma reductioncomp {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (reduction p q) → (reduction q r) → (reduction p r).
Proof.
  intros [f rf] [g rg].
  use make_reduction.
  - exact (λ x : X, (g (f x))).
  - intros x; destruct (rf x) as [rf1 rf2]; destruct (rg (f x)) as [rg1 rg2]; split; intros pp.
    + exact (rg1 (rf1 pp)).
    + exact (rf2 (rg2 pp)).
Qed.

Lemma isreduciblerefl {X : UU} (p : X → hProp) : (p ≼ p).
Proof.
  apply hinhpr.
  apply reductionrefl.
Qed.

Lemma isreduciblecomp {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (p ≼ q) → (q ≼ r) → (p ≼ r).
Proof.
  apply hinhfun2.
  apply reductioncomp.
Qed.

(* Many one reducibility forms an upper semi-lattice *)

Definition coprod_pred {X Y : UU} (p : X → hProp) (q : Y → hProp) : (X ⨿ Y) → hProp.
Proof.
  intros [a | b].
  - exact (p a).
  - exact (q b).
Defined.

Notation "p + q" := (coprod_pred p q).

Lemma isreduction_ii1 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (ismanyonereduction p (p + q) ii1).
Proof.
intros x.
split; apply idfun.
Defined.

Lemma isreduction_ii2 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (ismanyonereduction q (p + q) ii2).
Proof.
  intros x.
  split; apply idfun.
Defined.

Lemma reduction_coprod1 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (reduction p (p+q)).
Proof.
  use make_reduction.
  - apply ii1.
  - apply isreduction_ii1.
Defined.

Lemma reduction_coprod2 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (reduction q (p + q)).
Proof.
  use make_reduction.
  - apply ii2.
  - apply isreduction_ii2.
Defined.

Lemma isreducible_coprod1 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (p ≼ (p + q)).
Proof.
  apply hinhpr.
  apply reduction_coprod1.
Qed.

Lemma isreducible_coprod2 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (q ≼ (p + q)).
Proof.
  apply hinhpr.
  apply reduction_coprod2.
Qed.

Lemma isreduction_sumofmaps {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) (f : X → Z) (g : Y → Z) : (ismanyonereduction p r f) → (ismanyonereduction q r g) → (ismanyonereduction (p + q) r (sumofmaps f g)).
Proof.
  intros isf isg x.
  induction x.
  - exact (isf a).
  - exact (isg b).
Qed.

Lemma reduction_coprod {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (reduction p r) → (reduction q r) → (reduction (p + q) r).
Proof.
  intros [f irf] [g irg].
  use make_reduction.
  - exact (sumofmaps f g).
  - exact (isreduction_sumofmaps p q r f g irf irg).
Defined.

Lemma isreducible_coprod {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (p ≼ r) → (q≼ r) → ((p + q) ≼ r).
Proof.
  apply hinhfun2, reduction_coprod.
Qed.

Definition predcompl {X : UU} (p : X → hProp) : X → hProp := (λ x : X, (hneg (p x))).

(* If a predicate is reducible to a predicate q, then its complement is reducible to the complement of q *)

Lemma isreductioncompl {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) : (ismanyonereduction p q f) → (ismanyonereduction (predcompl p) (predcompl q) f).
Proof.
  intros isr x.
  destruct (isr x) as [isr1 isr2].
  split.
  - intros npx qfx.
    exact (npx (isr2 qfx)).
  - intros nqfx px.
    exact (nqfx (isr1 px)).
Defined.

Lemma reductioncompl {X Y : UU} (p : X → hProp) (q : Y → hProp) : (reduction p q) → (reduction (predcompl p) (predcompl q)).
Proof.
  intros rect.
  exact (make_reduction (predcompl p) (predcompl q) (pr1 rect) (isreductioncompl p q (pr1 rect) (pr2 rect))).
Defined.

Lemma isreduciblecompl {X Y : UU} (p : X → hProp) (q : Y → hProp) : (p ≼ q) → ((predcompl p) ≼ (predcompl q)).
Proof.
  intros rdct.
  use squash_to_prop.
  - exact (reduction p q).
  - exact rdct.
  - apply propproperty.
  - intros rect.
    apply hinhpr.
    apply reductioncompl.
    exact rect.
Qed.

Definition lem := ∏ (P : UU), (isaprop P) → P ⨿ ¬P.

Definition isstable {X : UU} (p : X → hProp) := ∏ (x : X), (hneg (hneg (p x))) → (p x).

Lemma isapropisstable {X : UU} (p : X → hProp) : (isaprop (isstable p)).
Proof.
  apply impred_isaprop.
  intros t; apply isapropimpl.
  apply propproperty.
Qed.

Lemma fundneg {X Y : UU} (f : X → Y) : (¬¬ X) → (¬¬ Y).
Proof.
  intros nnx ny.
  apply nnx.
  intros x.
  exact (ny (f x)).
Qed.

Lemma isreduciblestable {X Y : UU} (p : X → hProp) (q : Y → hProp) : (isstable q) → (p ≼ q) → (isstable p).
Proof.
  intros.
  use squash_to_prop.
  - exact (reduction p q).
  - exact X1.
  - apply isapropisstable.
  - intros [f isr] x; destruct (isr x) as [isr1 isr2].
    simpl.
    intros nnpx.
    set (nf := fundneg isr1).
    apply isr2, (X0 (f x)).
    exact (nf nnpx).
Qed.

End ManyOneReducibility.
