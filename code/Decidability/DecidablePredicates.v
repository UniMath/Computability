Require Import init.imports.
Require Import Inductive.Predicates.

Section Definitions.

  Definition isdecider {X : UU} (p : X → hProp) (f : X → bool) : UU := ∏ (x : X), (p x) <-> (f x = true).

  Definition decider {X : UU} (p : X → hProp) : UU := ∑ (f : X → bool), (isdecider p f).

  Definition deptypeddecider {X : UU} (p : X → hProp) : UU := ∏ (x : X), decidable (p x).

  Definition decidable_pred {X : UU} : UU := ∑ (p : X → hProp), (deptypeddecider p).
End Definitions.

Section Properties.
  Lemma isapropisdecider {X : UU} (p : X → hProp) (f : X → bool) : isaprop (isdecider p f).
  Proof.
    apply impred_isaprop.
    intro t.
    apply isapropdirprod; apply isapropimpl.
    - induction (f t).
      + apply isapropifcontr.
        use iscontrloopsifisaset.
        exact isasetbool.
      + apply isapropifnegtrue.
        exact nopathsfalsetotrue.
    - apply propproperty.
  Qed.

  Lemma isapropdeptypeddecider {X : UU} (p : X → hProp) : isaprop (deptypeddecider p).
  Proof.
    apply impred_isaprop.
    intro t.
    apply isapropdec.
    apply propproperty.
  Qed.

  Lemma decidertodeptypeddecider {X : UU} (p : X → hProp) : (decider p) → (deptypeddecider p).
  Proof.
    intros [f isdec] x.
    destruct (isdec x) as [isdec1 isdec2].
    induction (f x).
    - left.
      apply isdec2, idpath.
    - right; intro px.
      apply nopathsfalsetotrue, isdec1.
      exact px.
  Qed.

  Lemma deptypeddecidertodecider {X : UU} (p : X → hProp) : (deptypeddecider p) → (decider p).
  Proof.
    intros dpd.
    use tpair.
    - intro x.
      induction (dpd x).
      + exact true.
      + exact false.
    - simpl.
      intro x.
      induction (dpd x); split.
      + intro px.
        apply idpath.
      + intro; exact a.
      + intro; contradiction.
      + intro.
        apply fromempty, nopathsfalsetotrue.
        exact X0.
  Qed.


  Lemma pathsbetweendeciders {X : UU} (p : X → hProp) (f g : X → bool) (isdecf : isdecider p f) (isdecg : isdecider p g) : f = g.
  Proof.
    apply funextsec.
    intro x.
    destruct (isdecf x) as [fa fb].
    destruct (isdecg x) as [ga gb].
    induction (g x).
    - set (px := gb (idpath true)).
      exact (fa px).
    - induction (f x).
      + apply fromempty, nopathsfalsetotrue, ga, fb.
        exact (idpath true).
      + exact (idpath false).
  Qed.

  Lemma isapropdecider {X : UU} (p : X → hProp) : isaprop (decider p).
  Proof.
    apply invproofirrelevance.
    intros [f isdecf] [g isdecg].
    induction (pathsbetweendeciders p f g isdecf isdecg).
    assert (eq : isdecf = isdecg).
    - apply proofirrelevance.
      exact (isapropisdecider p f).
    - induction eq.
      exact (idpath (f,, isdecf)).
  Qed.
  
  Lemma isweqdecidertodeptypeddecider {X : UU} (p : X → hProp) : (decider p) ≃ (deptypeddecider p).
  Proof.
    use make_weq.
    - exact (decidertodeptypeddecider p).
    - apply (isweqimplimpl).
      + exact (deptypeddecidertodecider p).
      + exact (isapropdecider p).
      + exact (isapropdeptypeddecider p).
  Qed.
  
End Properties.

Section ClosureProperties.

  Lemma decidabledisj {X : UU} (p q : X → hProp) : (deptypeddecider p) → (deptypeddecider q) → (deptypeddecider (preddisj p q)).
  Proof.
    intros decp decq x.
    induction (decp x).
    - left. apply hinhpr.
      left. exact a.
    - induction (decq x).
      + left. apply hinhpr.
        right. exact a.
      + right. intro.
        use squash_to_prop.
        * exact ((p x) ⨿ (q x)).
        * exact X0.
        * exact isapropempty.
        * exact (sumofmaps b b0).
  Qed.

  Lemma decidableconj {X : UU} (p q : X → hProp) : (deptypeddecider p) → (deptypeddecider q) → (deptypeddecider (predconj p q)).
  Proof.
    intros decp decq x.
    induction (decp x), (decq x).
    - left. exact (a,,h).
    - right. intros [pp qq]. exact (n qq).
    - right. intros [pp qq]. exact (b pp).
    - right. intros [pp qq]. exact (b pp).
  Qed.

  Lemma decidableneg {X : UU} (p : X → hProp) : (deptypeddecider p) → (deptypeddecider (predneg p)).
  Proof.
    intros decp x.
    induction (decp x).
    - right. intros f. exact (f a).
    - left. exact b.
  Qed.

End ClosureProperties.
