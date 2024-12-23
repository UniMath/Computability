Require Import init.imports.

Definition rangeequiv {X : UU} {Y : UU} (f g : X → Y) := ∏ (y : Y), ∥hfiber f y∥ <-> ∥hfiber g y∥.

Notation "f ≡ᵣ g" := (rangeequiv f g) (at level 50). 
