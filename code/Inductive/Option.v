(* Definition of an option as the coproduct of a type X with the unit type *)

Require Import init.imports. 

Section Option.

  Definition option {X : UU} : UU := X ⨿ unit.

  Definition some {X : UU} (x : X) : option := (ii1 x).
  Definition none {X : UU} : @option X := (ii2 tt).
  
End Option.
