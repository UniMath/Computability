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

  Lemma embedinv (n : nat) : (embed (unembed n)) = n.
  Proof.
    induction n as [|n IH]. reflexivity.
    simpl. revert IH. destruct (unembed n) as [x y]. 
    case x as [|x]; intro Hx; rewrite <- Hx; unfold embed; simpl.
    - rewrite natplusr0. apply idpath.
    - rewrite natpluscomm, (natpluscomm y (S x)).
      simpl. rewrite (natpluscomm y (S (x + y + gauss_sum (x + y)))). apply maponpaths. simpl. apply maponpaths. rewrite (natpluscomm x y). apply idpath.
  Qed.
  
  Lemma embed0x (x y : nat) : (embed (S x,, 0) = S (embed (0,, x))).
  Proof.
    unfold embed; simpl; rewrite natplusr0. apply idpath.
  Qed.

  Lemma embedsxy (x y : nat) : (embed (x,, S y) = S (embed (S x,, y))).
  Proof.
    unfold embed; simpl.
    rewrite natplusnsm, (natplusnsm y x); simpl.
    rewrite natplusnsm. apply idpath.
  Qed.    

  Lemma unembedinv (mn : nat × nat) : (unembed (embed mn)) = mn. 
  Proof.
    assert (∏ (n : nat), embed mn = n → unembed n = mn).
    - intro n. revert mn. induction n as [|n IH].
      + intros [[|?][|?]]; intro H; inversion H; apply idpath.
      + intros [x [|y]]; simpl.
        * case x as [| x]; simpl; intro H.
            inversion H.
          rewrite (IH (0,, x)); [reflexivity |].
          revert H. rewrite embed0x. intros H; apply invmaponpathsS. apply H. exact x.
        * intro H. rewrite (IH (S x,, y)); [reflexivity| ].
          apply invmaponpathsS. rewrite <- embedsxy. exact H.
    - apply X. apply idpath.
    Qed.
  
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