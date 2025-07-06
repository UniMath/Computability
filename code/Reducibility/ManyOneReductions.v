Require Import init.imports.
Require Import Decidability.DecidablePredicates.
Require Import Inductive.Predicates.

  
Section ManyOneReducibility.

Definition ismanyonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) := ∏ (x : X), p x <-> q (f x).

Definition reduction {X Y : UU} (p : X → hProp) (q : Y → hProp) := ∑ (f : X → Y), ismanyonereduction p q f.

Definition make_reduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) (isrct : ismanyonereduction p q f) : (reduction p q) := (f,, isrct).

Definition ismanyonereducible {X Y : UU} (p : X → hProp) (q : Y → hProp) := ∥reduction p q∥.

Notation "p ≼ₘ q" := (ismanyonereducible p q) (at level 500).

Lemma isapropismanyonereduction {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) : (isaprop (ismanyonereduction p q f)).
Proof.
  apply impred_isaprop; intros.
  apply isapropdirprod; apply isapropimpl; apply propproperty.
Qed.

Lemma reductiontodecidability {X Y : UU} (p : X → hProp) (q : Y → hProp) : (p ≼ₘ q) → (deptypeddecider q) → (deptypeddecider p).
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

Lemma isreduciblerefl {X : UU} (p : X → hProp) : (p ≼ₘ p).
Proof.
  apply hinhpr.
  apply reductionrefl.
Qed.

Lemma isreduciblecomp {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (p ≼ₘ q) → (q ≼ₘ r) → (p ≼ₘ r).
Proof.
  apply hinhfun2.
  apply reductioncomp.
Qed.

(* Many one reducibility forms an upper semi-lattice *)
Lemma isreduction_ii1 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (ismanyonereduction p (predcoprod p q) ii1).
Proof.
intros x.
split; apply idfun.
Defined.

Lemma isreduction_ii2 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (ismanyonereduction q (predcoprod p q) ii2).
Proof.
  intros x.
  split; apply idfun.
Defined.

Lemma reduction_coprod1 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (reduction p (predcoprod p q)).
Proof.
  use make_reduction.
  - apply ii1.
  - apply isreduction_ii1.
Defined.

Lemma reduction_coprod2 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (reduction q (predcoprod p q)).
Proof.
  use make_reduction.
  - apply ii2.
  - apply isreduction_ii2.
Defined.

Lemma isreducible_coprod1 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (p ≼ₘ (predcoprod p q)).
Proof.
  apply hinhpr.
  apply reduction_coprod1.
Qed.

Lemma isreducible_coprod2 {X Y : UU} (p : X → hProp) (q : Y → hProp) : (q ≼ₘ (predcoprod p q)).
Proof.
  apply hinhpr.
  apply reduction_coprod2.
Qed.

Lemma isreduction_sumofmaps {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) (f : X → Z) (g : Y → Z) : (ismanyonereduction p r f) → (ismanyonereduction q r g) → (ismanyonereduction (predcoprod p q) r (sumofmaps f g)).
Proof.
  intros isf isg x.
  induction x.
  - exact (isf a).
  - exact (isg b).
Qed.

Lemma reduction_coprod {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (reduction p r) → (reduction q r) → (reduction (predcoprod p q) r).
Proof.
  intros [f irf] [g irg].
  use make_reduction.
  - exact (sumofmaps f g).
  - exact (isreduction_sumofmaps p q r f g irf irg).
Defined.

Lemma isreducible_coprod {X Y Z : UU} (p : X → hProp) (q : Y → hProp) (r : Z → hProp) : (p ≼ₘ r) → (q≼ₘ r) → ((predcoprod p q) ≼ₘ r).
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

Lemma isreduciblecompl {X Y : UU} (p : X → hProp) (q : Y → hProp) : (p ≼ₘ q) → ((predcompl p) ≼ₘ (predcompl q)).
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

Lemma isreduciblestable {X Y : UU} (p : X → hProp) (q : Y → hProp) : (isstable q) → (p ≼ₘ q) → (isstable p).
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

Example eq0manyonered : ((λ x, ishinh (¬ (x = 0))) ≼ₘ (λ x, ishinh (x = 0))).
Proof.
  apply hinhpr.
  use make_reduction.
  - intros n. destruct n as [ | n' ]. exact 1. exact 0.
  - simpl. intros x.
    destruct x as [ | x'].
    + split; intros;
      use squash_to_prop.
        exact (0 != 0). exact X.
        apply propproperty. intros contra. apply fromempty, contra, idpath.
        exact (1 = 0). exact X. apply propproperty. intros contra. apply fromempty. apply (negpathssx0 0), contra.
    + split; intros; apply hinhpr.
      * apply idpath.
      * apply negpathssx0.
Qed.

Definition DNEG_ELIM := ∏ (P : UU) , isaprop P → (¬ (¬ P)) → P.
Definition DNEG_REDUCTION1 := ∏ (p : unit → hProp) , (p ≼ₘ (predcompl (predcompl p))).
Definition DNEG_REDUCTION2 := ∏ (p : unit → hProp) , ((predcompl (predcompl p)) ≼ₘ p).

Lemma dneg_reduction1_to_lem : DNEG_REDUCTION1 → DNEG_ELIM.
Proof.
  intros DNEG_REDUCTION.
  intros P isapropP dneg.
  set (hP := make_hProp P isapropP).
  set (p := λ t : unit , hP).
  set (red := (DNEG_REDUCTION p)).
  use squash_to_prop.
  - exact (reduction p (predcompl (predcompl p))).
  - exact red.
  - exact isapropP.
  - intros [f isr].
    set (r := isr tt). simpl in r. destruct r as [r1 r2].
    apply r2.
    exact dneg.
Qed.   

Lemma dneg_reduction2_to_lem : DNEG_REDUCTION2 → DNEG_ELIM.
Proof.
  intros DNEG_REDUCTION.
  intros P isapropP dneg.
  set (hP := make_hProp P isapropP).
  set (p := λ t : unit , hP).
  set (red := (DNEG_REDUCTION p)).
  use squash_to_prop.
  - exact (reduction (predcompl (predcompl p)) p).
  - exact red.
  - exact isapropP.
  - intros [f isr].
    set (r := isr tt). simpl in r. destruct r as [r1 r2].
    exact (r1 dneg).
Qed.


End ManyOneReducibility.