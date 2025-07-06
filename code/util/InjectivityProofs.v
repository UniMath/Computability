Require Import init.imports.

Lemma isinclidfun {X : UU} : isincl (idfun X).
Proof.
  exact (idisweq X).
Qed.

Definition examplefun (X Z : UU) (z : Z) (x : X) : X × Z := (x ,, z).

Search "dirprod_pr1".

Lemma pathpairtopairpath {X Y : UU} {x y : X × Y} : x = y → (dirprod_pr1 x) = (dirprod_pr1 y) × (dirprod_pr2 x) = (dirprod_pr2 y).
Proof.
  intros eq.
  destruct eq.
  split; reflexivity.
Defined.

Lemma pairpathtopathpair {X Y : UU} {x y : X × Y} : (dirprod_pr1 x) = (dirprod_pr1 y) × (dirprod_pr2 x) = (dirprod_pr2 y) → x = y.
Proof.
  intros [a b].
  induction x as [x1 x2].
  induction y as [y1 y2].
  simpl in a, b.
  induction a, b.
  reflexivity.
Defined.

Lemma weqpathpair {X Y : UU} {x y : X × Y} : x = y ≃ (dirprod_pr1 x) = (dirprod_pr1 y) × (dirprod_pr2 x) = (dirprod_pr2 y).
Proof.
  exists pathpairtopairpath.
  apply (isweq_iso pathpairtopairpath pairpathtopathpair).
  - intros eq.
    unfold pathpairtopairpath.
    destruct eq. simpl; reflexivity.
  - intros [eq1 eq2].
    unfold pairpathtopathpair.
    destruct x as [x1 x2]; destruct y as [y1 y2].
    simpl in eq1, eq2.
    destruct eq1; destruct eq2; reflexivity.
Qed.

Lemma weqprodunit (X : UU) : X ≃ X × unit.
Proof.
  exists (λ x , (x ,, tt)).
  use isweq_iso.
  - exact dirprod_pr1.
  - intros; reflexivity.
  - intros [yy x]; destruct x; reflexivity.
Qed.

Definition cylinder (X Z : UU) (z : Z) : X → (X × Z) := λ x , (make_dirprod x z).

Lemma weqpathcylinder {X Z : UU} {x x' : X} (isz : isaset Z) (z : Z) : x = x' ≃ cylinder X Z z x = cylinder X Z z x'.
Proof.
  use weqcomp.
  - exact ((x = x') × (z = z)).
  - exists (λ x , (x ,, idpath z)).
    use isweq_iso.
    + intros [e e']. exact e.
    + intros; apply idpath.
    + simpl. intros [a b].
      assert (b = idpath z).
      * apply isz.   
      * rewrite X0. apply idpath.
  - apply invweq. 
    set (weq := @weqpathpair X Z (x ,, z) (x' ,, z)). simpl in weq. exact weq.
Qed.

Lemma isInjectivecylinder {X Z : UU} (z : Z) (isz : isaset Z) : isInjective (cylinder X Z z).
Proof.
  intros x x'.
  use isweq_iso.
  - exact (maponpaths dirprod_pr1).
  - intros. induction x0. apply idpath.
  - intros. unfold cylinder, make_dirprod in y.
