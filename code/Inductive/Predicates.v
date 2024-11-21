Require Import init.imports.

(*

This file contains definitions of the used operations on predicates and a number of useful 
properties. 

*)


Section Operations.

  Definition predconj {X : UU} (p q : X → hProp) : X → hProp := (λ x : X, (p x) ∧ (q x)).

  Infix "p ∧ q" := (predconj p q) (at level 25).
  
  Definition preddisj {X : UU} (p q : X → hProp) : X → hProp := (λ x : X, (p x) ∨ (q x)).

  Infix "p ∨ q" := (preddisj p q) (at level 25).
  
  Definition predneg {X : UU} (p : X → hProp) : X → hProp := (λ x : X, hneg (p x)).
  
  Notation "¬ p" := (predneg p) (at level 35).

  Definition preddirprod {X Y : UU} (p : X → hProp) (q : Y → hProp) : (X × Y) → hProp := (λ x : X × Y, (p (pr1 x)) ∧ (q (pr2 x))). 

  Infix "p × q" := (preddirprod p q) (at level 25).
  
  Definition predcoprod {X Y : UU} (p : X → hProp) (q : Y → hProp) : (X ⨿ Y) → hProp.
  Proof.
    intros x.
    induction x.
    - exact (p a).
    - exact (q b). 
  Defined.
  
End Operations.
