Require Export UniMath.Foundations.All.
  
Section EqualityDeciders.

  Definition iseqdecider (X : UU) (f : X → X → bool) : UU := ∏ (x1 x2 : X), x1 = x2 <-> f x1 x2 = true.

  Definition eqdecider (X : UU) := ∑ (f : X → X → bool), (iseqdecider X f).

  Definition make_eqdecider {X : UU} {f : X → X → bool} : (iseqdecider X f) → eqdecider (X) := (λ is : (iseqdecider X f), (f,, is)).

  Lemma eqdecidertodeptypedeqdecider (X : UU) : (eqdecider X) → (isdeceq X).
  Proof.
    intros [f is] x y.
    destruct (is x y) as [impl1 impl2].
    induction (f x y).
    - left; apply impl2; apply idpath.
    - right. intros eq. apply nopathsfalsetotrue. exact (impl1 eq).
  Qed.

  Lemma deptypedeqdecidertoeqdecider (X : UU) : (isdeceq X) → (eqdecider X).
  Proof.
    intros is.
    use tpair.
    - intros x y.
      induction (is x y).
      + exact true.
      + exact false.
    - intros x y.
      induction (is x y); simpl; split.
      + exact (λ a : (x = y), (idpath true)).
      + exact (λ b : (true = true), a).
      + intros; apply fromempty; exact (b X0).
      + intros; apply fromempty; exact (nopathsfalsetotrue X0).
  Qed.

  Lemma eqdecidertoisapropeq (X : UU) (f : eqdecider X) : ∏ (x y : X) ,(isaprop (x = y)).
  Proof.
    intros x.
    apply isaproppathsfromisolated.
    intros y.
    set (dec := eqdecidertodeptypedeqdecider X f).
    apply (dec x).
  Qed.

  Lemma isapropiseqdecider (X : UU) (f : X → X → bool) : (isaprop (iseqdecider X f)).
  Proof.
    apply isofhlevelsn.
    intros is.
    repeat (apply impred_isaprop + intros).
    apply isapropdirprod; apply isapropimpl.
    - induction (f t).
      + apply isapropifcontr.
        use iscontrloopsifisaset.
        exact isasetbool.
      + apply isapropifnegtrue.
        exact nopathsfalsetotrue.
    - apply eqdecidertoisapropeq.
      use make_eqdecider.
      + exact f.
      + exact is.
  Qed.

  Lemma pathseqdeciders (X : UU) (f g : X → X → bool) (isf : iseqdecider X f) (isg : iseqdecider X g) : f = g.
  Proof.
    apply funextsec; intros x.
    apply funextsec; intros y.
    destruct (isf x y) as [implf1 implf2].
    destruct (isg x y) as [implg1 implg2].
    induction (g x y).
    - apply implf1; apply implg2.
      apply idpath.
    - induction (f x y).
      + apply fromempty, nopathsfalsetotrue, implg1, implf2.
        exact (idpath true).
      + exact (idpath false).
  Qed.

  Lemma isapropeqdecider (X : UU) : (isaprop (eqdecider X)).
  Proof.
    apply invproofirrelevance.
    intros [f isf] [g isg].
    induction (pathseqdeciders X f g isf isg).
    assert (eq : isf = isg).
    - apply proofirrelevance.
      apply isapropiseqdecider.
    - induction eq.
      apply idpath.
  Qed.

  Lemma weqisdeceqiseqdecider (X : UU) : (isdeceq X) ≃ (eqdecider X).
  Proof.
    use make_weq.
    - exact (deptypedeqdecidertoeqdecider X).
    - apply isweqimplimpl.
      + exact (eqdecidertodeptypedeqdecider X).
      + exact (isapropisdeceq X).
      + exact (isapropeqdecider X).
  Qed.
End EqualityDeciders.

Section ChoiceFunction.

End ChoiceFunction.
