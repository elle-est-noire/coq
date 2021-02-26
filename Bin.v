
Theorem plus_assoc : forall n m p:nat, n+(m+p)=(n+m)+p.
Proof. intros n m p. induction n. reflexivity. simpl. rewrite -> IHn. reflexivity. Qed.
Theorem mult_0_r : forall n:nat, n*0=0.
Proof. intros n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem plus_0_r : forall n:nat, n+0=n.
Proof. intros n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem plus_comm : forall n m:nat, n+m=m+n.
Proof. intros n m. induction n. simpl. rewrite plus_0_r. reflexivity. simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity. Qed.
Theorem mult_suc_r : forall n m:nat, n*(S m)=n+n*m.
Proof. induction n. reflexivity. simpl. intros m. rewrite IHn.
rewrite plus_assoc. assert (H1:m+n=n+m). rewrite plus_comm. reflexivity.
rewrite H1. rewrite plus_assoc. reflexivity. Qed.
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof. induction p. rewrite mult_0_r. rewrite mult_0_r. rewrite mult_0_r. reflexivity.
rewrite mult_suc_r. rewrite mult_suc_r. rewrite mult_suc_r. rewrite IHp.
rewrite plus_assoc. rewrite plus_assoc. 
assert (H0:m+n*p=n*p+m). rewrite plus_comm. reflexivity.
assert (H1:n+m+n*p=n+n*p+m). rewrite <- plus_assoc. 
rewrite <- plus_assoc. rewrite H0. reflexivity.
rewrite H1. reflexivity. Qed.

Inductive bin : Type :=
 | O 
 | D (b : bin)
 | P (b : bin).

(*Inductive bin' : Type :=
  | stop
  | tick (foo : bin').*)

Fixpoint incr_bin (b:bin) : bin :=
  match b with
  | O => P O
  | D b' => P b'
  | P b' => D (incr_bin b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | O => 0
  | D b' => (bin_to_nat b') * 2
  | P b' => (bin_to_nat b') * 2 + 1
  end.

Compute bin_to_nat (P (D (P O))).

Theorem incr_comm : forall b:bin, bin_to_nat(incr_bin b)=(bin_to_nat b)+1.
Proof. induction b. reflexivity. reflexivity. simpl. rewrite IHb.
rewrite mult_plus_distr_r. assert (H1:1*2=1+1). reflexivity. rewrite H1.
rewrite plus_assoc. reflexivity. Qed.

Fixpoint evenb (n:nat): bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => evenb n'
  end.

Fixpoint halve_nat (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with 
    | 0 => 0
    | S n'' => S (halve_nat n'')
    end
  end.

Compute halve_nat 102.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | 0 => O
  | S n' => incr_bin(nat_to_bin n')
  end.

Compute nat_to_bin 16.

Theorem S_plus : forall n:nat, S n = n+1.
Proof. intros n. induction n. reflexivity. assert (H1:S(S n)=S(n+1)). rewrite IHn. reflexivity.
rewrite H1. simpl. reflexivity. Qed.
Theorem nat_bin_nat : forall n:nat, bin_to_nat (nat_to_bin n) = n.
Proof. induction n. reflexivity. simpl. rewrite incr_comm. rewrite IHn.
rewrite <- S_plus. reflexivity. Qed.

Compute nat_to_bin (bin_to_nat (P (P (D O)))).

Definition norm_bin (b:bin) : bin := nat_to_bin (bin_to_nat b).

 





