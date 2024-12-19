Require Import init.imports. 
  
(*

This file contains the definition of embedding functions, which form a bijective mapping from nat × nat to nat, together with its inverse unembed. 

Together with the two definitions, there also are proofs that the functions are inverses of each other. 

The embedding is done using diagonalization. 

0/0 0/1 0/2 0/3 0/4 0/5
1/0 1/1 1/2 1/3 1/4 1/5
2/0 2/1 2/2 2/3 2/4 2/5
3/0 3/1 3/2 3/3 3/4 3/5
4/0 4/1 4/2 4/3 4/4 4/5
5/0 5/1 5/2 5/3 5/4 5/5
6/0 6/1 6/2 6/3 6/4 6/5
*)
  
Section EmbedNaturals.

  (* Bijective maps from pairs of natural numbers to natural numbers.*)

  Definition gauss_sum (n : nat) : nat := (nat_rec _ 0 (λ (m s : nat), (S m) + s) (n)).
  
  Definition embed (p : nat×nat) : nat := (pr2 p) + (gauss_sum ((pr2 p) + (pr1 p))).
  
  Definition unembed (n : nat) : nat × nat :=
    nat_rec _ (0,, 0) (λ _ a, match (pr1 a) with S x => (x,, S (pr2 a)) | _ => (S (pr2 a),, 0) end) n.

  Section Tests.
    Fact embed00 : (embed (0,, 0)) = 0. apply idpath. Defined.
    Fact embed01 : (embed (0,, 1)) = 2. apply idpath. Defined.
    Fact embed33 : (embed (3,, 3)) = 24. apply idpath. Defined. 

    Fact unembed0 : (unembed 0) = (0,, 0). apply idpath. Defined.
    Fact unembed2 : (unembed 2) = (0,, 1). apply idpath. Defined.
    Fact unembed24 : (unembed 24) = (3,, 3). apply idpath. Defined. 
  End Tests.
  
  (*Proofs that embed and unembed are inverses of each other. *)

  Lemma gauss_sum_sn (n : nat) : (gauss_sum (S n)) = ((S n) + gauss_sum n).
  Proof.
    apply idpath.
  Qed.

  Lemma natplusS (n m : nat) : n + S m = S (n + m). 
  Proof.
    induction (pathsinv0 (natpluscomm n (S m))). 
    induction (pathsinv0 (natpluscomm n m)).
    apply idpath.
  Qed.
  
    
  Lemma embedsn (m : nat) : (embed (0,, S m)) = ((S (S m)) + embed (0,, m)).
  Proof.
    induction m.
    - apply idpath.
    - unfold embed. simpl.
      induction (pathsinv0 (natplusr0 m)).
      induction (pathsinv0 (natplusS m (S (m + S (m + gauss_sum (m)))))). 
      apply idpath.
  Qed.
    
  Lemma embedmsn (n m : nat) : (embed (n,, S m)) = ((S (S (n + m)) + embed (n,, m))).
  Proof.
    unfold embed. 
    simpl.
    induction (pathsinv0 (natplusS m (m + n + gauss_sum (m + n)))). 
    repeat apply maponpaths.
    induction (pathsinv0 (natpluscomm n m)).
    induction ( (natplusassoc m (m + n) (gauss_sum (m + n)))).
    induction (natplusassoc m m n).
    induction (natplusassoc (m + n) m (gauss_sum (m + n))).
    apply (maponpaths (λ x, add x (gauss_sum (m + n)))). 
    induction (pathsinv0 (natplusassoc m m n)), (pathsinv0 (natplusassoc m n m)).
    apply (maponpaths (add m)).
    apply natpluscomm.
  Qed.

  Lemma natnmto0 (n m : nat) : n + m = 0 → n = 0. 
  Proof.
    intros eq.
    induction n. 
    - apply idpath.
    - apply fromempty.
      exact (negpathssx0 _ eq).
  Qed.
  
  Lemma embed0 (n : nat × nat) : (embed n) = 0 → n = (0,, 0). 
  Proof.
    induction n as [[|?] [|?]].
    - intros. apply idpath. 
    - unfold embed. simpl. intros. apply fromempty. exact (negpathssx0 _ X).  
    - unfold embed. simpl. intros. apply fromempty. exact (negpathssx0 _ X). 
    - unfold embed. simpl. intros. apply fromempty. exact (negpathssx0 _ X).
  Defined. 
        
  Lemma embedinv (n : nat) : (embed (unembed n)) = n.
  Proof.
    assert (eq : ∏ (m : nat × nat), unembed n = m → n = embed m).
    - admit.  
    - rewrite <- (eq (unembed n)); apply idpath; apply idpath.
  Admitted.
  
  Lemma unembedinv (n : nat × nat) : (unembed (embed n)) = n. 
  Proof.
    (* TODO *)
  Admitted.


  
End EmbedNaturals.

Lemma nat_ind_geq_n (n : nat) (P : nat → UU) : (P n) → (∏ (k : nat), (P (n + k) → (P (S (n + k))))) → (∏ (m : nat), (n ≤ m) → (P (m))).
Proof. 
  intros.
  assert (∑ (k : nat), n + k = m).
  - use tpair.
    + exact (m - n).
    + cbn beta. rewrite -> (natpluscomm n (m - n)). exact (minusplusnmm m n X1).
  - destruct X2 as [k eq].
    induction eq.
    induction k.
    + rewrite -> (natpluscomm n 0); simpl. exact X.
    + rewrite -> (natplusnsm n k); simpl. apply (X0 k), (IHk (natlehnplusnm _ _)).
  Defined.