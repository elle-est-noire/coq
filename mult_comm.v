Theorem plus_0_r : forall n:nat, n+0=n.
Proof. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem plus_assoc : forall n m l:nat, (m+n)+l=m+(n+l).
Proof. induction m. reflexivity. intros l. simpl. rewrite IHm. reflexivity. Qed.
Theorem plus_suc_r : forall m n:nat, m+S n=S(m+n).
Proof. induction m. reflexivity. simpl. intros n. rewrite IHm. reflexivity. Qed.
Theorem mult_1_r : forall n:nat, n*1=n.
Proof. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem plus_comm : forall n m:nat, n+m=m+n.
Proof. induction n. simpl. intros m. rewrite plus_0_r. reflexivity. simpl.
intros m. rewrite plus_suc_r. rewrite IHn. reflexivity. Qed.
Theorem mult_0_r : forall n:nat, n*0=0.
Proof. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem mult_suc_r : forall n m:nat, n*(S m)=n+n*m.
Proof. induction n. reflexivity. simpl. intros m. rewrite IHn.
rewrite <- plus_assoc. assert (H1:m+n=n+m). rewrite plus_comm. reflexivity.
rewrite H1. rewrite plus_assoc. reflexivity. Qed.
Theorem mult_comm : forall m n:nat, n*m=m*n.
Proof. induction n. simpl. rewrite mult_0_r. reflexivity.
rewrite mult_suc_r. simpl. rewrite IHn. reflexivity. Qed. 
