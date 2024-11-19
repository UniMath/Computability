Require Import init.imports. 

Section Option.

  Definition option {X : UU} : UU := X ⨿ unit.

  Definition some {X : UU} (x : X) : option := (ii1 x).
  Definition none {X : UU} : @option X := (ii2 tt).
  
End Option.

Section PathProperties.

  Lemma nopathssomenone {X : UU} (x : X) : ¬ ((some x) = none). 
  Proof.
    apply negpathsii1ii2.
  Qed.

  Lemma nopathsnonesome {X : UU} (x : X) : ¬ (none = (some x)).
  Proof.
    apply negpathsii2ii1.
  Qed.

  Lemma some_injectivity {X : UU} (x y : X) : (some x = some y) → x = y.
  Proof.
    apply ii1_injectivity.
  Qed.
  
  
End PathProperties.

