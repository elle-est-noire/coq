
Variable Entity : Type.
Variables human mortal : Entity -> Prop.
Variable socrates : Entity.

Hypothesis hm : forall x, human x -> mortal x.
Hypothesis hs : human socrates.

From mathcomp Require Import all_ssreflect.
Theorem ms : mortal socrates.
Proof.
  apply hm.
  apply hs.
Qed.

Theorem ms2 : mortal socrates.
Proof.
  move: hm hs. move=> hm' hs'.
  apply hm' in hs'.
  by [].
Qed.


Print ms.

Definition ms' : mortal socrates :=
  hm socrates hs.
Print ms'.

Locate "/\".
Print and.
Locate and.
Definition n_adder n : nat -> nat := fun m => n + m.

Locate "*".
Print Nat.mul.
Print Nat.add.

Theorem a :forall (n m:nat), (2+n)=(2+m) -> n = m.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Print nat.
Compute 10000+1.
Print Init.Nat.add.


