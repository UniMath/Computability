Require Import init.imports.
Require Import Inductive.Option.

Definition rangeequiv {X : UU} {Y : UU} (f g : X → Y) := ∏ (y : Y), ∥hfiber f y∥ <-> ∥hfiber g y∥.

Notation "f ≡ᵣ g" := (rangeequiv f g) (at level 50).

Section EmbedNaturals.

  (* Bijective maps from pairs of natural numbers to natural numbers.*)
  
  Definition embed (p : nat×nat) : nat :=
    (pr2 p) + (nat_rec _ 0 (λ i m,  (S i) + m) ((pr2 p) + (pr1 p))).

  Definition unembed (n : nat) : nat × nat :=
    nat_rec _ (0,, 0) (fun _ a => match (pr1 a) with S x => (x,, S (pr2 a)) | _ => (S (pr2 a),, 0) end) n.

  (*Proofs that embed and unembed are inverses of each other. *)

  Lemma embedinv (n : nat) : (embed (unembed n)) = n.
  Proof.
  (*TODO*)  
  Admitted.

  Lemma unembedinv (n : nat × nat) : (unembed (embed n)) = n. 
  Proof.
  (* TODO *)
  Admitted.  
End EmbedNaturals.

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
  Lemma enumconj {X : UU} (p q : X → hProp) : (predenum p) → (predenum q) → (predenum (λ x : X, p x ∧ q x)).
  Admitted.

  Lemma enumdisj {X : UU} (p q : X → hProp) : (predenum p) → (predenum q) → (predenum (λ x : X, p x ∨ q x)). 
  Admitted.

  Lemma enumdirprod {X Y : UU} (p : X → hProp) (q : Y → hProp) : (predenum p) → (predenum q) → (predenum (λ a, (p (pr1 a)) ∧ (q (pr2 a)))).
  Proof.
  Admitted.

  Lemma enumcoprod {X Y : UU} (p : X → hProp) (q : Y → hProp) : (predenum p) → (predenum q) → (predenum (λ a, (
  
  
End EnumerablePredicates.




