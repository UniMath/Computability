Require Import init.imports.
Require Import Inductive.Option.
Require Import Decidability.DecidablePredicates.
Require Import Inductive.Predicates.
Require Import util.NaturalEmbedding. 

Definition rangeequiv {X : UU} {Y : UU} (f g : X → Y) := ∏ (y : Y), ∥hfiber f y∥ <-> ∥hfiber g y∥.

Notation "f ≡ᵣ g" := (rangeequiv f g) (at level 50).

Section EnumerablePredicates.
  
  Definition ispredenum {X : UU} (p : X → hProp) (f : nat → option) := ∏ (x : X), (p x) <-> ∥(hfiber f (some x))∥. 

  Definition predenum {X : UU} (p : X → hProp) := ∑ (f : nat → option), (ispredenum p f).

  Definition isenumerablepred {X : UU} (p : X → hProp) := ∥predenum p∥.
  
  Lemma isapropispredenum {X : UU} (p : X → hProp) (f : nat → option) : (isaprop (ispredenum p f)).
  Proof.
    apply impred_isaprop.
    intros t.
    apply isapropdirprod; apply isapropimpl, propproperty.
  Qed.

  Lemma rangeequivtohomot {X : UU} (p q : X → hProp) (e1 : (predenum p)) (e2 : (predenum q)) : ((pr1 e1) ≡ᵣ (pr1 e2)) → p ~ q.  
  Proof.
    intros req x.
    destruct e1 as [f ispf].
    destruct e2 as [g ispg].
    destruct (req (some x)) as [impl1 impl2].
    destruct (ispf x) as [if1 if2].
    destruct (ispg x) as [ig1 ig2].
    use hPropUnivalence. 
    - intros px.
      apply ig2, impl1, if1.
      exact px.
    - intros qx.
      apply if2, impl2, ig1.
      exact qx. 
  Qed.

  (* Closure properties *)
  Lemma enumconj {X : UU} (p q : X → hProp) (deceq : isdeceq X) : (predenum p) → (predenum q) → (predenum (λ x : X, p x ∧ q x)).
  Proof.
    intros [f enumf] [g enumg]. 
    use tpair.  
    - intros n.
      destruct (unembed n) as [m1 m2]. 
      induction (f m1), (g m2). 
      + induction (deceq a x).  
        * exact (some x). 
        * exact none. 
      + exact none.
      + exact none.
      + exact none.
    - simpl. intros x.         
      split. intros [px qx].
      destruct (enumf x) as [enumfx1 enumfx2].
      destruct (enumg x) as [enumgx1 enumgx2].
      use squash_to_prop. 
      + exact (hfiber f (some x)). 
      + exact (enumfx1 px).
      + apply propproperty.
      + intros [m1 m1eq].
        use squash_to_prop.
        * exact (hfiber g (some x)).
        * exact (enumgx1 qx).
        * apply propproperty.
        * intros [m2 m2eq].
          apply hinhpr.
          use make_hfiber.
          -- exact (embed (m1,, m2)).
          -- simpl.
             induction (pathsinv0 (unembedinv (m1,, m2))).
             induction (pathsinv0 (m1eq)), (pathsinv0 (m2eq)).
             simpl.
             induction (deceq x x).
             ++ induction a.
                apply idpath.
             ++ apply fromempty, b. exact (idpath x).
      + intros; split; use squash_to_prop. 
        * exact (hfiber
                   (λ n : nat,
                       coprod_rect (λ _ : X ⨿ unit, option)
                         (λ a : X,
                             match g (pr2 (unembed n)) with
                             | inl x =>
                                 coprod_rect (λ _ : (a = x) ⨿ (a != x), option) (λ _ : a = x, some x)
                                   (λ _ : a != x, none) (deceq a x)
                             | inr _ => none
                             end) (λ _ : unit, match g (pr2 (unembed n)) with
                                               | inl _ | _ => none
                                               end) (f (pr1 (unembed n)))) (some x)).
        * exact X0.
        * apply propproperty. 
        * intros [mm enumff].
          destruct (enumg x), (enumf x).
          apply pr3, hinhpr.
          destruct (unembed mm) as [m1 m2]. 
          use make_hfiber.
          -- exact m1.             
          -- assert (eq : m1 = Preamble.pr1 (m1,, m2)).
             ++ apply idpath.
             ++ induction eq.
                assert (eq : m2 = Preamble.pr2 (m1,, m2)). 
                apply idpath. induction eq.
                revert enumff. 
                induction (g m2).
                induction (f m1). simpl.
                induction (deceq a0 a). simpl.
                induction a1.
                apply idfun.
                simpl; intros. apply fromempty.
                exact (nopathsnonesome x enumff).
                simpl; intros. apply fromempty.
                exact (nopathsnonesome x enumff).
                induction (f m1). simpl. intros. apply fromempty. exact (nopathsnonesome x enumff).
                simpl. intros. apply fromempty. exact (nopathsnonesome x enumff).
        * exact (hfiber
                   (λ n : nat,
                       coprod_rect (λ _ : X ⨿ unit, option)
                         (λ a : X,
                             match g (pr2 (unembed n)) with
                             | inl x =>
                                 coprod_rect (λ _ : (a = x) ⨿ (a != x), option) (λ _ : a = x, some x)
                                   (λ _ : a != x, none) (deceq a x)
                             | inr _ => none
                             end) (λ _ : unit, match g (pr2 (unembed n)) with
                                               | inl _ | _ => none
                                               end) (f (pr1 (unembed n)))) (some x)).
        * exact X0.
        * apply propproperty. 
        * intros [mm enumgg].
          destruct (enumg x), (enumf x).
          apply pr2, hinhpr.
          destruct (unembed mm) as [m1 m2]. 
          use make_hfiber.
          -- exact m2.             
          -- assert (eq : m1 = Preamble.pr1 (m1,, m2)).
             ++ apply idpath.
             ++ induction eq.
                assert (eq : m2 = Preamble.pr2 (m1,, m2)). 
                apply idpath. induction eq.
                revert enumgg. 
                induction (g m2).
                induction (f m1). simpl.
                induction (deceq a0 a). simpl.
                induction a1.
                apply idfun.
                simpl; intros. apply fromempty.
                exact (nopathsnonesome x enumgg).
                simpl; intros. apply fromempty.
                exact (nopathsnonesome x enumgg).
                induction (f m1). simpl. intros. apply fromempty. exact (nopathsnonesome x enumgg).
                simpl. intros. apply fromempty. exact (nopathsnonesome x enumgg).
  Defined.            
                
  Lemma enumdisj {X : UU} (p q : X → hProp) : (predenum p) → (predenum q) → (predenum (λ x : X, p x ∨ q x)).
  Proof.
    intros [f enumff] [g enumgg].
    use tpair.
    - intros n.
      destruct (unembed n) as [m1 m2].
      induction m1.
      exact (f m2).
      exact (g m2).
    - simpl.
      intros x; split; intros.
      destruct (enumff x), (enumgg x); clear enumff enumgg.
      use squash_to_prop. exact (p x ⨿ q x). exact X0. apply propproperty. intros [px | qx]; clear X0.
      + use squash_to_prop. exact (hfiber f (some x)). exact (pr1 px). apply propproperty. intros [m2 feq].
        apply hinhpr. use make_hfiber.
        exact (embed (0,, m2)). simpl.
        rewrite -> (unembedinv (0,, m2)). simpl. exact feq.
      + use squash_to_prop. exact (hfiber g (some x)). exact (pr0 qx). apply propproperty. intros [m2 geq].
        apply hinhpr. use make_hfiber.
        exact (embed (1,, m2)). simpl.
        rewrite -> (unembedinv (1,, m2)). simpl. exact geq.
      + use squash_to_prop.
        * exact (hfiber
                 (λ n : nat,
                     nat_rect (λ _ : nat, option) (f (pr2 (unembed n)))
                       (λ (_ : nat) (_ : option), g (pr2 (unembed n))) (pr1 (unembed n))) 
                 (some x)).
        * exact X0.
        * apply propproperty.
        * clear X0. intros [n feq]. revert feq.
          destruct (unembed n) as [m1 m2].
          assert (eq1 : m1 = pr1 (m1,, m2)) by apply idpath.
          assert (eq2 : m2 = pr2 (m1,, m2)) by apply idpath. 
          induction eq1, eq2.
          induction m1; intros; apply hinhpr.
          -- left. 
             destruct (enumff x).
             apply pr2, hinhpr. exact (m2,, feq).
          -- right.
             destruct (enumgg x).
             apply pr2, hinhpr. exact (m2,, feq). 
  Defined.

  Lemma isenumerableconj {X : UU} (p q : X → hProp) : (isdeceq X) → (isenumerablepred p) → (isenumerablepred q) → (isenumerablepred (predconj p q)).
  Proof.
    intros.
    use squash_to_prop.
    exact (predenum p). exact X1. apply propproperty. intros.
    use squash_to_prop.
    exact (predenum q). exact X2. apply propproperty. intros.
    apply hinhpr. exact (enumconj p q X0 X3 X4). 
  Qed.

  Lemma isenumerabledisj {X : UU} (p q : X → hProp) : (isenumerablepred p) → (isenumerablepred q) → (isenumerablepred (preddisj p q)). 
  Proof.
    intros.
    use squash_to_prop.
    - exact (predenum p).
    - exact X0.
    - apply propproperty.
    - intros.
      use squash_to_prop.
      + exact (predenum q).
      + exact X1.
      + apply propproperty.
      + intros. apply hinhpr.
        exact (enumdisj p q X2 X3).
  Qed.
  
End EnumerablePredicates.


