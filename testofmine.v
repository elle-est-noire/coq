Require Import Arith.
Lemma plus1: forall x:nat,x+2=x+1+1.
Proof.
  intros.
  SearchRewrite((_ + _)).
  rewrite plus_assoc_reverse.
  simpl.
  reflexivity.
Qed.

Lemma ord: forall x:nat, x+1<x+1+1->x+1<x+2.
Proof.
  intros.
  SearchRewrite(_+_).
  rewrite BinInt.ZL0.
  rewrite Nat.add_assoc.
  apply H.
Qed.

Theorem plus2: (forall x:nat, x<x+1)->(forall x y z:nat, (x<y) -> (y<z)->x<z)->(forall x:nat, x<(x+1)+1).
Proof.
  intros.
  apply (H0 x (x+1) (x+1+1)).
  apply (H x).
  apply (H (x+1)).
Qed.

Theorem ordlaw: forall x y z:nat, x<y->y<z->x<y<z.
Proof.
  auto.
Qed.

Theorem plus2': (forall x:nat, x<x+1)->(forall x y z:nat, x<y<z->x<z)->(forall x:nat, x<(x+1)+1).
Proof.
  intros.
  apply plus2.
  apply H.
  intros.
  apply (H0 x0 y z).
  apply (ordlaw x0 y z).
  apply H1.
  apply H2.
Qed.






