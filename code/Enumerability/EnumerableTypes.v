Require Import init.imports.
Require Import Enumerability.EnumerablePredicates.
Require Import Decidability.DecidablePredicates.
Require Import Inductive.Option. 
Require Import Inductive.Predicates.
Require Import util.NaturalEmbedding.
Require Import Inductive.ListProperties.

Section Definitions.

  Definition isenumerator (X : UU) (f : nat → @option X) := ∏ (x : X), ∃ (n : nat), (f n) = some x.    
  Definition enumerator (X : UU) := ∑ (f : nat → @option X), (isenumerator X f). 
  Definition isenumerable (X : UU) := ∥enumerator X∥. 

  Lemma isapropisenumerator (X : UU) (f : nat → @option X) : isaprop (isenumerator X f).
  Proof. 
    apply impred_isaprop.
    intros t; apply propproperty.
  Qed.

  Lemma isapropisenumerable (X : UU) (f : nat → @option X) : isaprop (isenumerable X).
  Proof.
    apply propproperty. 
  Qed.
  
End Definitions. 

Section TypePredicateEnumerabilityEquivalence.
  Lemma typeenumtopredenum (X : UU) (f : nat → @option X) : (isenumerator X f) → (ispredenum (truepred X) f).
  Proof.
    intros isenumf x. 
    split; intros.  
    - exact (isenumf x). 
    - exact tt.
  Defined. 

  Lemma predenumtotypeenum (X : UU) (f : nat → @option X) : (ispredenum (truepred X) f) → (isenumerator X f).
  Proof.
    intros isenumpred x. 
    destruct (isenumpred x); clear isenumpred. 
    exact (pr1 tt). 
  Defined.

  Lemma isenumerabletypetoisenumerablepred (X : UU) : (isenumerable X) ≃ (isenumerablepred (truepred X)). 
    use weqiff. 
    - split.
      + intros isenumx; use (squash_to_prop isenumx (propproperty _)); intros [f isenum]; apply hinhpr. 
        exact (f,, (typeenumtopredenum X f isenum)).
      + intros isenumpred; use (squash_to_prop isenumpred (propproperty _)); intros [f predenum]; apply hinhpr.
        exact (f,, (predenumtotypeenum X f predenum)). 
    - apply propproperty. 
    - apply propproperty. 
  Qed.

  Lemma isdecenumerabletypetoenumerablepred (X : UU) (p : X → hProp) (d : decider p) (e : enumerator X) : (predenum p).
  Proof.
    destruct d as [f decf].
    destruct e as [g enumg].
    use tpair. 
    - intros n. 
      induction (g n). 
      + induction (f a).
        * exact (some a). 
        * exact none.
      + exact none.
    - intros x.
      destruct (decf x) as [dec1 dec2].
      split; intros. 
      + set (q := (enumg x)).
        use squash_to_prop.
        * exact (∑ (n : nat), (g n) = (some x)).
        * exact q.
        * apply propproperty.
        * intros [n neqx]. apply hinhpr.
          simpl.
          use make_hfiber.
          -- exact n.
          -- simpl. induction (pathsinv0 neqx).
             simpl. induction (pathsinv0 (dec1 X0)).
             apply idpath.
      + use squash_to_prop.
        * exact (hfiber
                   (λ n : nat,
                       let o := g n in
                       coprod_rect (λ _ : X ⨿ unit, option)
                         (λ a : X, let b := f a in bool_rect (λ _ : bool, option) (some a) none b)
                         (λ _ : unit, none) o) (some x)).
        * exact X0.
        * apply propproperty.
        * intros [a aa].
          revert aa. simpl.
          induction (g a); simpl.
          -- assert (q : (f a0) = true → x = a0 → (f x) = true).
             ++ intros. induction X2.
                exact X1.
             ++ induction (f a0).
                ** simpl.
                   intros.
                   set (bb := (some_injectivity a0 x aa)).
                   apply dec2, (q (idpath true) (pathsinv0 bb)). 
                ** simpl; intros. 
                   apply fromempty. exact (nopathsnonesome x aa).
          -- intros i. apply fromempty. exact (nopathsnonesome x i). 
  Defined.

  Lemma isdecidablepredenumerabletypetoenumneg (X : UU) (p : X → hProp) : (enumerator X) → (decider p) → (predenum (predneg p)). 
  Proof.
    intros f g.
    use isdecenumerabletypetoenumerablepred.
    - apply deptypeddecidertodecider. 
      use decidableneg.
      apply decidertodeptypeddecider.
      exact g.
    - exact f. 
  Qed.
  
End TypePredicateEnumerabilityEquivalence. 

Section ClosureProperties.
  
  Lemma enumeratornat : (isenumerator nat (λ (n : nat), (some n))).
  Proof.
    intros n.
    apply hinhpr.
    exact (n,, (idpath _)).
  Qed.

  Lemma enumeratorbool : (isenumerator bool (λ (n : nat), (nat_rect _ (some true) (λ (n : nat) _ , (some false)) n))). 
  Proof.
    intros b; apply hinhpr.
    induction b.
    - exact (0,, (idpath _)).
    - exact (1,, (idpath _)).
  Qed.

  Lemma enumeratorunit : (isenumerator unit (λ (n : nat), (some tt))). 
  Proof.
    intros x; apply hinhpr. 
    induction x.
    exact (0,, (idpath _)).
  Qed. 
  
  Lemma enumeratoroption (X : UU) (f : nat → @option X) : (isenumerator X f) → (isenumerator (@option X) (nat_rect (λ _, @option (@option X)) (some none) (λ (n : nat) _, some (f n)))).
  Proof.
    intros enumff x. 
    induction x. 
    - use squash_to_prop.   
      + exact (hfiber f (some a)).
      + exact (enumff a).
      + apply propproperty. 
      + clear enumff; intros [n hfib]. 
        apply hinhpr.
        use tpair. 
        * exact (S n).
        * simpl. apply maponpaths. exact hfib.
    - apply hinhpr. 
      use tpair.
      * exact 0.
      * simpl; induction b; apply idpath. 
  Qed.

  Definition enumeratorfunctiondirprod (X Y : UU) (f : nat → @option X) (g : nat → @option Y) : nat → @option (X × Y). 
  Proof.
    intros n. 
    destruct (unembed n) as [m1 m2]. 
    clear n. 
    induction (f m1), (g m2). 
    - exact (some (a,, y)).
    - exact none. 
    - exact none. 
    - exact none. 
  Defined.

  Lemma enumeratordirprod (X Y : UU) (f : nat → @option X) (g : nat → @option Y) :(isenumerator X f) → (isenumerator Y g) → isenumerator (X × Y) (enumeratorfunctiondirprod X Y f g).
  Proof.
    intros enumff enumgg [a b].
    use (squash_to_prop (enumff a)). apply propproperty. 
    - intros [n hfibf]. clear enumff. 
      use (squash_to_prop (enumgg b)). apply propproperty. 
      + intros [m hfibg]. clear enumgg.
        apply hinhpr; use make_hfiber.
        * exact (embed (n,, m)). 
        * unfold enumeratorfunctiondirprod.
          rewrite -> (unembedinv (n,, m)), hfibf, hfibg.
          simpl; apply idpath. 
  Qed.

  Definition enumeratorfunctioncoprod (X Y : UU) (f : nat → @option X) (g : nat → @option Y) : nat → (@option (X ⨿ Y)).
  Proof.
    intros n; destruct (unembed n) as [m1 m2]; clear n. 
    induction m1.
    - induction (f m2). 
      + exact (some (ii1 a)).
      + exact (none).
    - induction (g m2).
      + exact (some (ii2 a)).
      + exact none.
  Defined.

  Definition enumeratorcoprod (X Y : UU) (f : nat → @option X) (g : nat → @option Y) : (isenumerator X f) → (isenumerator Y g) → (isenumerator (X ⨿ Y) (enumeratorfunctioncoprod X Y f g)).
  Proof.
    intros enumff enumgg [x | y]. 
    - use (squash_to_prop (enumff x) (propproperty _)).
      intros [n hfibf]. apply hinhpr. 
      use make_hfiber. 
      + exact (embed (0,, n)).  
      + unfold enumeratorfunctioncoprod. 
        rewrite -> (unembedinv), hfibf. 
        simpl. apply idpath.
    - use (squash_to_prop (enumgg y) (propproperty _)).
      intros [n hfibg]. apply hinhpr.
      use make_hfiber.
      + exact (embed (1,, n)).
      + unfold enumeratorfunctioncoprod.
        rewrite -> (unembedinv), hfibg.
        simpl. apply idpath.
  Qed.  
  
  Lemma isenumerablenat : (isenumerable nat).
  Proof.
    apply hinhpr.
    exact ((λ (n : nat), (some n)),, enumeratornat).
  Qed.

  Lemma isenumerablebool : (isenumerable bool). 
  Proof.
    apply hinhpr.
    use tpair.
    exact (λ (n : nat), (nat_rect _ (some true) (λ (n : nat) _ , (some false))) n).
    exact (enumeratorbool).
  Qed.

  Lemma isenumerabledirprod (X Y : UU) : (isenumerable X) → (isenumerable Y) → (isenumerable (X × Y)). 
  Proof.
    intros isenumf isenumg. 
    use (squash_to_prop (isenumf) (propproperty _)). 
    intros [f enumf]; clear isenumf. 
    use (squash_to_prop (isenumg) (propproperty _)).
    intros [g enumg]; clear isenumg. 
    apply hinhpr. 
    use tpair. 
    - exact (enumeratorfunctiondirprod X Y f g). 
    - exact (enumeratordirprod X Y f g enumf enumg).
  Qed.
  
  Lemma isenumerablecoprod (X Y : UU) : (isenumerable X) → (isenumerable Y) → (isenumerable (X ⨿ Y)). 
  Proof.
    intros isenumf isenumg. 
    use (squash_to_prop (isenumf) (propproperty _)). 
    intros [f enumf]; clear isenumf. 
    use (squash_to_prop (isenumg) (propproperty _)).
    intros [g enumg]; clear isenumg. 
    apply hinhpr. 
    use tpair. 
    - exact (enumeratorfunctioncoprod X Y f g). 
    - exact (enumeratorcoprod X Y f g enumf enumg).
  Qed.
  
  Lemma isenumerableoption (X : UU) : (isenumerable X) → (isenumerable (@option X)). 
  Proof.
    intros isenumx.  
    use (squash_to_prop (isenumx) (propproperty _)); intros [f enumx]; apply hinhpr.
    use tpair. 
    - exact (nat_rect (λ _, @option (@option X)) (some none) (λ (n : nat) _, some (f n))).
    - exact (enumeratoroption X f enumx).
  Qed.
  
End ClosureProperties.

Section ListEnumerability. 
  Definition islistenumerator (X : UU) (L : nat → list X) := ∏ (x : X), ∃ (n : nat), (is_in x (L n)).

  Definition listenumerator (X : UU) := ∑ (L : nat → list X), (islistenumerator X L).

  Definition islistenumerable (X : UU) := ishinh (listenumerator X).

  Lemma enumeratortolistenumerator (X : UU) (E : enumerator X) : (listenumerator X).
  Proof.
    destruct E as [E isenum].
    use tpair. (**TODO: to replace with make_enumerator? **)
    - intros n.
      induction (E n).
      + exact (cons a nil).
      + exact nil.
    - intros x.
      use squash_to_prop.
      + exact (hfiber E (some x)).
      + exact (isenum x).
      + apply propproperty.
      + intros [n nfib]; clear isenum; apply hinhpr.
        use tpair.
        * exact n.
        * cbn beta. rewrite -> nfib. right; apply idpath.
  Defined.

  Lemma listenumeratortoenumerator (X : UU) (L : listenumerator X) : (enumerator X). 
  Proof. 
    destruct L as [L islstenum].
    use tpair.
    - intros n.
      destruct (unembed n) as [m1 m2]; clear n.
      exact (pos (L m1) m2).
    - intros x.
      use squash_to_prop.  
      + exact (∑ (n : nat), (is_in x (L n))).
      + exact (islstenum x).
      + apply propproperty.
      + intros [n inn]; apply hinhpr.
        use tpair.
        * exact (embed (n,, (elem_pos x (L n) inn))).    
        * cbn beta; rewrite -> unembedinv; simpl.   
          apply poselem_posinv.
  Defined.

  Lemma weqisenumerableislistenumerable (X : UU) : (isenumerable X) ≃ (islistenumerable X).
  Proof.
    use weqiff.
    - split; intros x; use (squash_to_prop x (propproperty _)); intros enum; apply hinhpr.
      + exact (enumeratortolistenumerator X enum).
      + exact (listenumeratortoenumerator X enum).
    - apply propproperty. 
    - apply propproperty.
  Qed.

  

End ListEnumerability. 