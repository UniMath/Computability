Require Import init.imports. 
Require Import Inductive.ListProperties. 
Require Import Reducibility.OneOneReductions.

Section CorrespondenceSequences.

    Hypothesis X Y : UU. 
    Hypothesis p : X → hProp.
    Hypothesis q : Y → hProp. 
    Hypothesis deceqX : isdeceq X.
    Hypothesis deceqY : isdeceq Y.

    Definition corr_prop1 (C : list (X × Y)) := ∏ (x : X) (y : Y), is_in (x,, y) C → p x <-> q y.

    Definition corr_prop2 (C : list (X × Y)) := ∏ (x : X) (y1 y2 : Y), is_in (x,, y1) C -> is_in (x,, y2) C -> y1 = y2.

    Definition corr_prop3 (C : list (X × Y)) := ∏ (x1 x2 : X) (y : Y), is_in (x1,, y) C -> is_in (x2,, y) C -> x1 = x2.

    Definition iscorrespondence (C : list (X × Y)) := corr_prop1 C × corr_prop2 C × corr_prop3 C.

    Lemma isapropiscorrespondence (C : list (X × Y)) : isaprop (iscorrespondence C).
    Proof.
        apply isapropdirprod.
        - apply impred_isaprop; intros x. apply impred_isaprop; intros y. apply isapropimpl. apply isapropdirprod; apply isapropimpl, propproperty.
        - apply isapropdirprod;
            apply impred_isaprop; intros x; apply impred_isaprop; intros y1; apply impred_isaprop; intros y2; repeat apply isapropimpl; apply isasetifdeceq. apply deceqY. apply deceqX.
    Qed.    

    Definition first_projection (C : list (X × Y)) := map dirprod_pr1 C.
    
    Definition second_projection (C : list (X × Y)) := map dirprod_pr2 C.
    
End CorrespondenceSequences.