Require Import study03.

Module study04.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof. 
  induction n. simpl. induction m. reflexivity.
  simpl. intros H. inversion H.
  simpl. induction m. simpl. intros H.
  inversion H. simpl. intros H.
  inversion H. apply IHn in H1.
  rewrite H1. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m. simpl. induction n.
  reflexivity. simpl. intros H.
  inversion H. simpl. induction n.
  simpl. intros H. inversion H.
  simpl. intros H. inversion H.
  apply IHm in H1. rewrite H1.
  reflexivity.
Qed.
Theorem plus_n_n_injective_take2 : forall n m,
     n + n = m + m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m. induction n.
  reflexivity. intros H. inversion H.
  simpl. induction n. intros H.
  inversion H. simpl. intros H.
  inversion H. rewrite plus_comm in H1.
  assert (m+S m=S m+m). apply plus_comm.
  rewrite H0 in H1. simpl in H1.
  inversion H1. apply IHm in H3.
  rewrite H3. reflexivity.
Qed.

Theorem index_after_last: forall (n : nat) (X : Type) (l : ImplicitTest.llist X),
ImplicitTest.llength' l = n -> ImplicitTest.lindex' (S n) l = ImplicitTest.lNone'.
Proof.
  intros n X l.
  generalize dependent n.
  induction l. reflexivity.
  simpl. induction n. intros H.
  inversion H. intros H.
  inversion H. rewrite H1.
  apply IHl. apply H1.
Qed.
Lemma lapp_lcons_lsnoc : forall (X:Type) (l:ImplicitTest.llist X) (v:X),
ImplicitTest.lapp' l (ImplicitTest.lcons' v ImplicitTest.lnil')
  =ImplicitTest.lsnoc' l v.
Proof.
  intros X l v. induction l. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed. 
Theorem length_snoc''' : forall (n : nat) (X : Type)
                              (v : X) (l : ImplicitTest.llist X),
     ImplicitTest.llength' l = n -> ImplicitTest.llength' (ImplicitTest.lsnoc' l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l. simpl.
  induction n. reflexivity.
  intros H. inversion H.
  simpl. induction n.
  intros H. inversion H.
  intros H. inversion H.
  rewrite H1. 
  apply ImplicitTest.study03'.eq_remove_S.
  rewrite lapp_lcons_lsnoc.
  apply IHl. apply H1.
Qed.
Notation "x :: y" := (ImplicitTest.lcons' x y) (at level 60, right associativity).
Notation "[ ]" := ImplicitTest.lnil'.
Notation "[ x , .. , y ]" := (ImplicitTest.lcons' x .. (ImplicitTest.lcons' y []) ..).
Notation "x ++ y" := (ImplicitTest.lapp' x y) (at level 60, right associativity).

Theorem app_length_cons : forall (X : Type) (l1 l2 : ImplicitTest.llist X)
                                  (x : X) (n : nat),
     ImplicitTest.llength' (l1 ++ (x :: l2)) = n ->
     S (ImplicitTest.llength' (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  generalize dependent l2.
  induction l1. intros l2 n H.
  rewrite <- H. reflexivity.
  simpl. induction n.
  intros H. inversion H.
  intros H. inversion H.
  apply ImplicitTest.study03'.eq_remove_S.
  rewrite H1. apply IHl1.
  apply H1.
Qed.
Theorem app_length_cons_inv : forall (X : Type) (l1 l2 : ImplicitTest.llist X)
                                  (x : X) (n : nat),
     S (ImplicitTest.llength' (l1 ++ l2)) = n -> 
     ImplicitTest.llength' (l1 ++ (x :: l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  generalize dependent l2.
  induction l1. intros l2 n H.
  rewrite <- H. reflexivity.
  simpl. induction n.
  intros H. inversion H.
  intros H. inversion H.
  apply ImplicitTest.study03'.eq_remove_S.
  rewrite H1. apply IHl1. apply H1.
Qed.
Theorem app_length_twice : forall (X:Type) (n:nat) (l:ImplicitTest.llist X),
  ImplicitTest.llength' l = n -> ImplicitTest.llength' (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n.
  induction l. simpl. intros n H.
  rewrite <- H. reflexivity.
  simpl. induction n.
  intros H. inversion H.
  simpl. intros H. inversion H.
  apply ImplicitTest.study03'.eq_remove_S.
  rewrite H1. rewrite plus_comm. simpl. 
  apply app_length_cons_inv.
  apply ImplicitTest.study03'.eq_remove_S.
  apply IHl. apply H1.
Qed.
  
End study04.
  
