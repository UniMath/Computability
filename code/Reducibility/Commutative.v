Require Import init.imports.
Require Import Reducibility.ManyOneReductions.
Require Import Inductive.Predicates.

Lemma weqmanyonereductions {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) (x : X) : ismanyonereduction p q f → (p x) ≃ (q (f x)).
Proof.
    intros isr.
    destruct (isr x) as [isr1 isr2].
    use (make_weq isr1).
    use (isweqimplimpl _ isr2); apply propproperty.
Qed.

Lemma pathmanyonereductions {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) (x : X) : ismanyonereduction p q f → p x = (q (f x)).
Proof. 
    intros isr.
    apply weqtopathshProp, weqmanyonereductions, isr.
Qed.

Lemma reduction_funeq  {X Y : UU} (p : X → hProp) (q : Y → hProp) (f : X → Y) : ismanyonereduction p q f → p = (λ x : X , q (f x)).
Proof.
    intros isr; apply funextsec; intros x. 
    apply pathmanyonereductions, isr.
Qed.