Require Import init.imports.
Require Import Inductive.Option.

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

Section Position. 
  Definition pos {X : UU} : (list X) → nat → @option X.
  Proof.
    use list_ind; cbn beta.
    - exact (λ _, none).
    - intros xs l f n.
      induction n.
      + exact (some xs).
      + exact (f n).
  Defined.

  Definition elem_pos {X : UU} (x : X) (l : list X) (inn : is_in x l) : nat.
  Proof.
    revert l inn.
    use list_ind.
    - intros inn. apply fromempty; exact inn.
    - intros x0 xs f inn.
      destruct inn as [l | r].
      + exact (S (f l)).
      + exact 0.
  Defined.

  Lemma bla {X : UU} (x : X) (l : list X) (inn : is_in x l) (n : nat) : (elem_pos x l inn) = n → (pos l n) = (some x).
  Proof.
    revert l n inn.
    use list_ind.
    - intros n inn. exact (fromempty inn).
    - cbn beta. intros x0 xs IHn n inn eq.
      destruct inn as [l | r].
      + induction n.
        * apply fromempty. exact (negpathssx0 _ eq).
        * assert (elem_pos x xs l = n) by exact (invmaponpathsS _ _ eq).
          assert (pos (cons x0 xs) (S n) = pos xs n) by apply idpath.
          rewrite X1. exact (IHn n l X0).
      + induction n.
        * assert (pos (cons x0 xs) 0 = some x0) by apply idpath; rewrite -> X0; apply maponpaths.
          exact (pathsinv0 r).
        * apply fromempty. exact (negpaths0sx _ eq).
  Defined.

  Lemma poselem_posinv {X : UU} (x : X) (l : list X) (inn : is_in x l) : pos l (elem_pos x l inn) = some x.
  Proof.
    apply (bla x l inn).
    apply idpath.
  Defined.

End Position. 

Section Append. 

  Definition append {X : UU} : (list X) → (list X) → (list X). 
  Proof. 
    use list_ind; cbn beta.
    - exact (idfun _).
    - intros. exact (cons x (X0 X1)).
  Defined.
  
  Section AppendTests.
    Definition l0 : list nat := (cons 0 (cons 1 (cons 2 nil))).
    Definition l1 : list nat := (cons 1 (cons 2 (cons 3 nil))).
    Definition l2 : list nat := (cons 0 (cons 1 (cons 2 (cons 1 (cons 2 (cons 3 nil)))))).

    Example testappend : (append l0 l1) = l2. Proof. apply idpath. Qed.

    Example testappendnilleft : (append nil l1) = l1. Proof. apply idpath. Qed.
    
    Example testappendnilright: (append l2 nil) = l2. Proof. apply idpath. Qed. 

  End AppendTests. 
  
  Local Infix "++" := concatenate.

  Lemma isin_concatenate1 {X : UU} (l1 l2 : list X) (x : X) : (is_in x l1) → (is_in x (l1 ++ l2)).
  Proof.
    revert l1.
    use list_ind; cbn beta; intros. 
    - apply fromempty; exact X0.
    - rewrite -> (concatenateStep x0 xs l2).
      destruct X1 as [l | r].
      + left; apply X0; exact l.
      + right; exact r.
  Defined.
  
  Lemma isin_concatenate2 {X : UU} (l1 l2 : list X) (x : X) : (is_in x l2) → (is_in x (l1 ++ l2)).
  Proof.
    revert l1.
    use list_ind; cbn beta; intros.
    - rewrite -> (nil_concatenate l2); exact X0.
    - rewrite -> (concatenateStep x0 xs l2). left. exact (X0 X1).
  Defined.
  
  Lemma isin_concatenate_choice {X : UU} (l1 l2 : list X) (x : X) : (is_in x (l1 ++ l2)) → (is_in x l1) ⨿ (is_in x l2).
  Proof.
    revert l1.
    use list_ind; cbn beta.
    - rewrite -> nil_concatenate. intros inn; right; exact inn.
    - intros x0 xs IHl. rewrite -> (concatenateStep x0 xs l2). intros [l | r].
      + induction (IHl l) as [a | a]. left; left; exact a. right; exact a.
      + left; right; exact r.
  Defined. 
End Append. 

Section ListProduct. 
Local Infix "++" := concatenate. 
  Definition list_prod {X Y : UU} (l1 : list X) (l2 : list Y) : (list (X × Y)).
  Proof. 
    revert l1.
    use list_ind; cbn beta.  
    - exact nil.
    - intros; exact ((map (λ (y : Y), (x,, y)) l2) ++ X0).
  Defined.
  
  Lemma inn_list_prod1 {X Y : UU} (l1 : list X) (l2 : list Y) (x : X) (y : Y) : (is_in x l1) → (is_in y l2) → (is_in (x,, y) (list_prod l1 l2)). 
  Proof. 
    revert l1.
    use list_ind; cbn beta.
    - exact fromempty.
    - intros x0 xs IHl inn1 inn2.
      destruct inn1 as [l | r]. 
      + apply isin_concatenate2. exact (IHl l inn2).
      + apply isin_concatenate1. rewrite <- r. clear IHl r x0.
        revert l2 inn2. use list_ind; cbn beta.
        * exact (fromempty).
        * intros y0 ys IHl [l | r]; rewrite -> (mapStep).
          -- left. exact (IHl l).
          -- right. rewrite -> r. apply idpath.
  Defined.           
End ListProduct. 

Section Map. 

  Lemma is_inmap {X Y : UU} (f : X → Y) (l : list X) (x : X) : (is_in x l) → (is_in (f x) (map f l)).
  Proof. 
    revert l. use list_ind; cbn beta.
    - exact fromempty.
    - intros x0 xs IHl [l | r].
      + left. exact (IHl l).
      + right. apply maponpaths. exact r.
  Defined.  
End Map. 

Section CumulativeFunctions.

  Local Infix "++" := concatenate. 
  Definition iscumulative {X : UU} (L : nat → list X) := ∏ (n : nat), ∑ (l : list X), (L (S n) = ((L n) ++ l)).

  Lemma cumulativenleqm {X : UU} (L : nat → list X) (iscum : (iscumulative L)) (m n : nat) : n ≤ m → ∑ (l : list X), L m = (L n) ++ l.
  Proof.
    intros nleqm.
    assert (eq : ∑ (k : nat), n + k = m).
    - use tpair. 
      + exact (m - n).
      + cbn beta. rewrite -> (natpluscomm n (m - n)). apply (minusplusnmm _ _ nleqm).
    - destruct eq as [k eq].
      induction eq; induction k.
      + rewrite (natpluscomm n 0). use (tpair _ nil). simpl. rewrite -> (concatenate_nil (L n)). apply idpath.
      + rewrite (natplusnsm n k); destruct (iscum (n + k)) as [l eq]; clear iscum.
        destruct (IHk (natlehnplusnm _ _)) as [l0 neq]; clear IHk.
        use (tpair _ (l0 ++ l)). simpl. rewrite -> eq, neq. apply assoc_concatenate.
  Qed.
         
  Definition cumul {X : UU} : (nat → list X) → (nat → list X). 
  Proof.
  intros L n.
  induction n.
  - exact (L 0).
  - exact (IHn ++ (L (S n))).
  Defined.
  
  Lemma iscumulativecumul {X : UU} (L : nat → list X) : (iscumulative (cumul L)).
  Proof.
    intros n; induction n. 
    - use (tpair _ (L 1) (idpath _)).
    - use (tpair _ (L (S (S n))) (idpath _)). 
  Defined.

  Lemma isinlisincumull {X : UU} (L : nat → list X) (x : X) (n : nat) : (is_in x (L n)) → (is_in x (cumul L n)).
  Proof.
    intros inn.
    induction n.
    - exact inn.
    - simpl. apply isin_concatenate2. exact inn.
  Defined.

  Lemma isincumulleh {X : UU} (L : nat → list X) (x : X) (iscum : iscumulative L) (n m: nat) : (n ≤ m) → (is_in x (L n)) → (is_in x (L m)).
  Proof. 
    intros leq inn.
    set (q := cumulativenleqm L iscum m n leq); destruct q as [l eq]; rewrite -> eq.
    apply isin_concatenate1. exact inn.
  Defined.   

  Lemma iscumulex {X : UU} (L : nat → list X) (x : X) : (∃ (n : nat), (is_in x (L n))) <-> (∃ (n : nat), (is_in x (cumul L n))).
  Proof.
  split; intros ex; use (squash_to_prop ex (propproperty _)); clear ex; intros [n inn]; apply hinhpr.
  - use (tpair _ n); cbn beta.        
    apply isinlisincumull. exact inn.
  - induction n.
    + use (tpair _ 0). exact inn.
    + induction (isin_concatenate_choice (cumul L n) (L (S n)) x inn).
      * exact (IHn a).
      * exact ((S n),, b).
  Defined.

End CumulativeFunctions. 

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
