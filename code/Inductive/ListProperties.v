Require Import init.imports.
Require Import UniMath.Combinatorics.Lists.

Section Definitions.

  Definition is_in {X : UU} (x : X) : (list X) → UU.
  Proof.
     use list_ind.
     - exact empty.
     - intros.
       exact (X0 ⨿ (x = x0)). 
  Defined.

  Definition hin {X : UU} (x : X) : (list X) → hProp := (λ l : (list X), ∥is_in x l∥).

  Section Tests.

    Definition l : list nat := (cons 1 (cons 2 (cons 3 (nil)))).

    Lemma test1In : (is_in 1 l).
    Proof.
      right; apply idpath.
    Qed.

    Lemma negtest4In : ¬ (is_in 4 (cons 1 nil)).  
    Proof.
      intros [a | b].
      - exact a.
      - apply (negpathssx0 2).
        apply invmaponpathsS.
        exact b.
    Qed.    
  End Tests.
  
End Definitions.

Section Length.
  (*Lemmas related to the length of the list*)
  
  Lemma length_zero_nil {X : UU} (l : list X) (eq : 0 = length l) : l = nil.   
  Proof.
    revert l eq.
    use list_ind. 
    - exact (λ x, (idpath nil)).
    - intros x xs Ih eq.
      apply fromempty.
      apply (negpaths0sx (length xs) eq).
  Qed.

  Lemma length_cons {X : UU} (l : list X) (inq : 0 < length l) : ∑ (x0 : X) (l2 : list X), l = (cons x0 l2). 
    revert l inq.
    use list_ind.
    - intros inq.
      exact (fromempty (isirreflnatlth 0 inq)).
    - intros x xs Ih ineq.
      exact (x,, (xs,, (idpath (cons x xs)))).
  Qed.

  Lemma length_in {X : UU} (l : list X) (x : X) (inn : is_in x l) : 0 < length l.
  Proof.
    revert l inn.
    use list_ind.
    - intros inn. apply fromempty. exact inn.
    - cbv beta. intros.
      apply idpath.
  Qed.
  
End Length.


Section DistinctList.

  Definition distinctterms {X : UU} : (list X) → UU.
  Proof.
    use list_ind.
    - exact unit.
    - intros.
      exact (X0 × ¬(is_in x xs)).
  Defined.

  Definition hdistinct {X : UU} : (list X) → hProp := (λ l : (list X), ∥distinctterms l∥).
  
End DistinctList.

Section Filter.

  Definition filter_ex_fun {X : UU} (d : isdeceq X) (x : X) : X → list X → list X.
  Proof.
    intros x0 l1.
    induction (d x x0).
    - exact l1.
    - exact (cons x0 l1).
  Defined.
  
  Definition filter_ex {X : UU} (d : isdeceq X) (x : X) (l : list X) : list X :=
    (@foldr X (list X) (filter_ex_fun d x) nil l).

  Definition filter_ex_nil {X : UU} (d : isdeceq X) (x : X) (l : list X) : (filter_ex d x nil) = nil.
  Proof.
    apply idpath.
  Qed.
  
  
  Definition filter_ex_cons1 {X : UU} (d : isdeceq X) (x : X) (l : list X) : (filter_ex d x (cons x l)) = (filter_ex d x l).
  Proof.
    set (q:= foldr_cons (filter_ex_fun d x) nil x l).
    unfold filter_ex; induction (pathsinv0 q).
    unfold filter_ex_fun; induction (d x x).
    - apply idpath.
    - apply fromempty, b, idpath.
  Defined.

  Definition filter_ex_cons2 {X : UU} (d : isdeceq X) (x x0 : X) (l : list X) (nin : ¬ (x = x0)) : (filter_ex d x (cons x0 l)) = cons x0 (filter_ex d x l).
  Proof.
    set (q := foldr_cons (filter_ex_fun d x) nil x0 l).
    unfold filter_ex; induction (pathsinv0 q).
    unfold filter_ex_fun; induction (d x x0).
    - apply fromempty, nin, a.
    - apply idpath.
  Defined.

  Lemma xninfilter_ex {X : UU} (d : isdeceq X) (x : X) (l : list X) : ¬ is_in x (filter_ex d x l).
  Proof.
    revert l.
    use list_ind.
    - intros is_in.
      exact is_in.
    - cbv beta.
      intros x0 xs Ih.
      induction (d x x0).
      + induction a. induction (pathsinv0 (filter_ex_cons1 d x xs)). exact Ih.
      + induction (pathsinv0 (filter_ex_cons2 d x x0 xs b)). intros [lst | elm].
        * exact (Ih lst).
        * exact (b elm).
  Defined.
  
  Lemma filter_exltlist1 {X : UU} (d : isdeceq X) (x : X) (l : list X) : (length (filter_ex d x l)) ≤ (length l).
  Proof.
    revert l.
    use list_ind.
    - use isreflnatleh.
    - cbv beta. intros x0 xs Ih.
      induction (d x x0).
      + induction a.
        induction (pathsinv0 (filter_ex_cons1 d x xs)).
        apply natlehtolehs; exact Ih.
      + induction (pathsinv0 (filter_ex_cons2 d x x0 xs b)).
        exact Ih.
  Qed.

  Lemma istransnatlth {n m k : nat} : n < m → (m < k) → (n < k). 
  Proof.
    intros inq1 inq2.
    apply (istransnatgth k m n).
    - exact inq2.
    - exact inq1.
  Qed.
  
  Lemma natlthnsnmtonm {n m : nat} : (S n < m) → (n < m). 
  Proof.
    intros.
    exact (istransnatlth (natlthnsn n) X). 
  Qed.
  
  Lemma filter_exltlist2 {X : UU} (d : isdeceq X) (x : X) (l : list X) (inn : is_in x l) : (length (filter_ex d x l)) < (length l). 
  Proof.
    revert l inn.
    use list_ind; cbv beta.
    - intros. apply fromempty. exact inn.
    - intros x0 xs Ih inn.
      destruct inn as [in' | elm].
      + set (q := (Ih in')).
        induction (d x x0).
        * induction a. induction (pathsinv0 (filter_ex_cons1 d x xs)).
          apply natlthtolths. exact q.
        * induction (pathsinv0 (filter_ex_cons2 d x x0 xs b)).
          exact q.
      + induction (pathsinv0 elm).
        set (ineq := (filter_exltlist1 d x0 xs)).
        induction (pathsinv0 (filter_ex_cons1 d x0 xs)).
        apply natlehtolthsn.
        exact ineq.
  Qed.

  Lemma filter_ex_in {X : UU} (d : isdeceq X) (l : list X) (x x0 : X) (neq : ¬ (x = x0)) : (is_in x0 l) → (is_in x0 (filter_ex d x l)).
  Proof.
    revert l.
    use list_ind; cbv beta.
    - intros nn. apply fromempty. exact nn.
    - intros.
      induction (d x x1).
      + induction a. induction (pathsinv0 (filter_ex_cons1 d x xs)).
        destruct X1 as [a | b].
        * exact (X0 a).
        * apply fromempty, neq. exact (pathsinv0 b).
      + induction (pathsinv0 (filter_ex_cons2 d x x1 xs b)).
        destruct X1 as [a | c].
        * left.
          exact (X0 a).
        * induction (pathsinv0 c).
          right. apply idpath.
  Qed.
  
End Filter.



Section Properties.

  Lemma eqdecidertomembdecider {X : UU} (d : ∏ (x1 x2 : X), decidable(x1=x2)) : ∏ (x : X) (l : list X), decidable (is_in x l). 
  Proof.
    intros x.
    use list_ind.
    - right; intros inn. exact inn.
    - intros x0 xs dec.
      induction dec.
      + left; left. exact a.
      + induction (d x x0).
        * left; right. exact a.
        * right. intros [a | a'].
          -- apply b. exact a.
          -- apply b0. exact a'.
  Defined.

  (* An induction principle for lists with distinct terms. *)
  Lemma distinct_list_induction {X : UU} : ∏ (P : list X → UU),
  (P nil) → (∏ (x : X) (xs : (list X)) (d : (distinctterms xs)), (P xs) → ¬(is_in x xs) → (P (cons x xs))) → ∏ (xs : list X) (d : distinctterms xs), (P xs). 
  Proof.
    intros P Pnil Ih.
    use list_ind.
    - exact (λ d : _, Pnil).
    - intros x xs X0 d.
      destruct d as [d inn].
      apply Ih.
      + exact d.
      + exact (X0 d).
      + exact inn.
  Defined.        
  
  Lemma pigeonhole_sigma {X : UU} (l1 l2 : list X) (d : ∏ (x1 x2 : X), (decidable (x1=x2))) (dist : distinctterms l2) : (length l1) < (length l2) → (∑ (x : X), (is_in x l2) × (¬ (is_in x l1))). 
  Proof.
    revert l2 dist l1.
    use distinct_list_induction.
    - intros l1 ineq.
      apply fromempty.
      exact (negnatlthn0 (length l1) ineq).
    - cbn beta; intros x xs dt Ih nin.
      intros l1 ineq.
      induction (eqdecidertomembdecider d x l1).
      + set (l' := filter_ex d x l1).
        assert (length l' < length xs).
        * apply (natlthlehtrans (length l') (length l1) (length xs)).
          -- exact (filter_exltlist2 d x l1 a).
          -- apply natlthsntoleh. exact ineq.
        * set (pr := (Ih l' X0)).
          destruct pr as [x0 [ixs il']].
          use tpair.
          -- exact x0.
          -- split.
             left.
             ++ exact ixs.
             ++ intros il1.
                apply il', filter_ex_in.
                ** intros eq.
                   induction eq.
                   exact (nin ixs).
                ** exact il1.
      + use tpair.
        * exact x.
        * split.
          -- right. apply idpath.
          -- exact b.
  Qed.
  
                
             
End Properties.
