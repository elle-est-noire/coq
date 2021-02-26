Theorem id: forall A:Prop, A -> A.
Proof.
  exact (fun A:Prop => fun x:A => x).
Qed.

Theorem id2: forall A:Prop, A -> A.
Proof.
  intros.
  exact H.
Qed.

Theorem syllogism: forall A B:Prop,
  A->((A->B)->B).
Proof.
  intros.
  apply H0.
  apply H.
Qed.

Theorem cap: forall A B:Prop,
  (A/\B)->A.
Proof.
  intros.
  apply H.
Qed.

Section contraposition.

Hypothesis classical:forall A:Prop,
  ~~A->A.

Theorem contraposition1: forall A B:Prop,
  (A->B)->(~B->~A).
Proof.
  intros A B ab notb a.
  apply notb.
  apply ab.
  apply a.
Qed.

Theorem contraposition2: forall A B:Prop,
  (~B->~A)->(A->B).
Proof.
  intros A B nbna a.
  apply classical.
  intros nb.
  apply nbna.
  apply nb.
  apply a.
Qed.
  
End contraposition.

Section contraposition'.
Hypothesis classical':forall A:Prop,
  A\/~A.

Theorem contraposition2':forall A B:Prop,
  (~B->~A)->(A->B).
Proof.
  intros A B nbna a.
  destruct (classical' B) as [b|nb].
  -apply b.
  -elimtype False.
  apply nbna.
  apply nb.
  apply a.
Qed.

End contraposition'.

Theorem dnot: forall A:Prop,
  A->~~A.
Proof.
  intros A a na.
  apply na.
  apply a.
Qed.

Theorem final: forall A:Prop,
  ~~(A\/~A).
Proof.
  intros A naorna.
  apply naorna.
  right.
  intros a.
  apply naorna.
  left.
  apply a.
Qed.

Inductive mynat: Set:=
  Z:mynat
  | S:mynat -> mynat.

Fixpoint plus (m n:mynat){struct m}:mynat:=
  match m with
    Z=>n
    | S m' => S(plus m' n)
  end.
Compute plus (S Z) (S Z).

