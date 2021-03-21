Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Arith Euclid Ring Omega.

Check modulo.
Compute modulo 5.

Locate "%|".
Locate dvdn.
Print dvdn.
Locate "%%".
Compute 100 %% 37.
Print modn.
Print modn_rec.

Definition mod' n m := modulo (S m) (lt_O_Sn m) n.

Compute proj1_sig (mod' 5 3).
Check proj1_sig.

Require Import Recdef.
Function gcd (m n : nat) {wf lt m} : nat :=
  match m with
  | 0    => n
  | S m' => gcd (proj1_sig (mod' n m')) m
  end.
  (*減少の証明*)
  intros. destruct (mod' n m'). simpl.
  destruct e as [q [Hn Hm]].
  apply Hm.
  (*清楚性の証明*)
  exact lt_wf.
Defined.

Compute gcd 18 24.

Inductive divides (m:nat) : nat -> Prop :=
  divi : forall a, divides m (a * m).

Lemma divide : forall a m n, n = a * m -> divides m n.
Proof.
  intros. rewrite H. constructor.
Qed.

Lemma divides_mult : forall m q n, divides m n -> divides m (q * n).
Proof.
  induction 1.
  replace (q*(a*m)) with (q*a*m).
  by apply divide with (a:=q*a).
  by rewrite mulnA.
Qed.

Theorem divides_plus : forall m n p, divides m n ->
  divides m p -> divides m (n + p).
Proof.
  intros. destruct H. destruct H0.
  replace (a*m+a0*m) with ((a+a0)*m).
  apply divi.
  by rewrite mulnDl.
Qed.

Theorem divides_1 : forall n, divides 1 n.
Proof.
  intros.
  replace n with (n*1).
  apply divi.
  apply muln1.
Qed.

Theorem divides_0 : forall n, divides n 0.
Proof.
  intros.
  replace 0 with (0*n).
  apply divi.
  apply mul0n.
Qed.

Theorem divides_n : forall n, divides n n.
Proof.
  intros.
  rewrite {2}(_ : n = 1 * n).
  apply divi.
  by rewrite mul1n.
Qed.

Hint Resolve divides_plus divides_mult divides_1 divides_0 divides_n.

Theorem gcd_divides : forall m n,
  divides (gcd m n) m /\ divides (gcd m n) n.
Proof.
  intros.
  functional induction (gcd m n).
  auto.
  destruct (mod' n m').
  simpl in *.
  destruct e as [q [Hn Hm]].
  destruct IHn0.
  split; auto.
  rewrite Hn.
  auto.
Qed.


Theorem plus_inj : forall m n p,
  m + n = m + p -> n = p.
Proof.
  intros.
  induction m.
  by rewrite 2!add0n in H.
  apply IHm.
  assert(H2:S(m+n)=S(m+p)).
  rewrite -add1n. rewrite (_ : (m+p).+1=(1+(m+p))).
  by rewrite addnA. apply add1n.
  by inversion H2.
Qed.

Require Import Omega.

Lemma divides_plus' : forall m n p,
  divides m n -> divides m (n+p) -> divides m p.
Proof.
  induction 1.
  intro.
  induction a. assumption.
  inversion H.
  destruct a0.
  destruct p.
  auto.
  elimtype False.
  destruct m. destruct a. try discriminate. 
  rewrite 2!muln0 in H1.
  inversion H1.
  rewrite mul0n in H1.
  inversion H1.
  apply IHa.
  rewrite -add1n in H1. rewrite (_:a.+1=(1+a)) in H1.
  rewrite 2!mulnDl in H1. rewrite (_:(1*m+a*m+p)=(1*m)+(a*m+p)) in H1.
  apply plus_inj in H1. rewrite -H1. constructor.
  by rewrite addnA. apply add1n.
Qed.

Theorem add_compat : forall m n, addn m n = Init.Nat.add m n.
Proof.
  intros. induction m.
  by [].
  by [].
Qed.

Theorem mul_compat : forall m n, muln m n = Init.Nat.mul m n.
Proof.
  by [].
Qed.

Theorem gcd_max : forall g m n,
  divides g m -> divides g n -> divides g (gcd m n).
Proof.
  intros.
  functional induction (gcd m n).
  assumption.
  destruct (mod' n m'). simpl in *.
  destruct e as [q [Hn Hm']].
  apply IHn0.
  apply divides_plus' with (n:=q*S m').
  induction H. rewrite (_ : (q*(a*g))=((q*a)*g)).
  apply divi. by rewrite mulnA.
  rewrite (_ : (q * m'.+1 + x)=(((q * m'.+1)%coq_nat+x)%coq_nat)).
  by rewrite -Hn. Locate addn.
  apply add_compat.
  apply H.
Qed.

