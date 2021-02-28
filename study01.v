Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).
Compute next_weekday friday.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true ) = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => false
  | true => (andb b2 b3)
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true).
Check negb.

Definition xorb (b1:bool) (b2:bool) : bool :=
  andb (negb (andb b1 b2)) (orb b1 b2).
Example test_xor1: (xorb true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_xor2: (xorb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_xor3: (xorb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_xor4: (xorb false false) = false.
Proof. simpl. reflexivity. Qed.

Module Playground1.

Inductive mynat: Type :=
  | O
  | S (n : mynat).

Definition mypred (n : mynat) : mynat :=
  match n with
  | O => O
  | S n' => n'
  end.

Inductive mynat' : Type :=
  | stop
  | tick (foo : mynat').

Definition minustwo (n : mynat) : mynat :=  
  match n with
  | O => O
  | S O => O
  | S (S (n')) => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo (S (S (S (S O))))).

Fixpoint evenb (n:mynat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:mynat) : bool := negb (evenb n).

Eval simpl in evenb (S (S (S (S (S O))))).
Eval simpl in oddb (S (S (S (S (S O))))).
Compute oddb (S (S (S (S (S O))))).
Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n:mynat) (m:mynat) : mynat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
Fixpoint mult (n m:mynat) : mynat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
Fixpoint minus (n m:mynat) : mynat :=
  match n, m with
  | O   , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
Fixpoint power (base index:mynat):mynat:=
  match index with
  | O => S O
  | S n' => mult base (power base n')
  end.

Eval simpl in plus (S (S (S O))) (S (S O)).
Eval simpl in mult (S (S (S O))) (S (S O)).
Eval simpl in minus (S (S (S O))) (S (S O)).
Eval simpl in power (S (S (S O))) (S (S O)).

Fixpoint factorial (n:mynat) : mynat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial (S (S (S O)))) = S (S (S (S (S (S O))))).
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial (S (S (S (S (S O)))))) 
= (mult (mult (S (S O)) (S (S (S (S (S O))))))  (mult (S (S (S O))) (S (S (S (S O)))))).
Proof. simpl. reflexivity. Qed.
Notation "x + y" := (plus x y) (at level 50, left associativity) : mynat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : mynat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : mynat_scope.

Fixpoint beq_nat (n m : mynat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
Fixpoint ble_nat (n m : mynat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
Definition blt_nat (n m : mynat) : bool :=
 andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat (S (S O)) (S (S O))) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat (S (S O)) (S (S (S (S O))))) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat (S (S (S (S O)))) (S (S O))) = false.
Proof. simpl. reflexivity. Qed.
End Playground1.

Definition minustwo_ex (n : Playground1.mynat) : Playground1.mynat :=  
  match n with
  | Playground1.O => Playground1.O
  | Playground1.S Playground1.O => Playground1.O
  | Playground1.S (Playground1.S (n')) => n'
  end.

Check (S (S (S (S 0)))).
(*Eval simpl in (minustwo 4).*)
Check S.
Check Playground1.S.

Theorem plus_0_n : forall n:nat, 0+n=n.
Proof. intros n. simpl. reflexivity. Qed.
Theorem plus_id_example : forall n m:nat,
  n=m->n+n=m+m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.
Theorem plus_id_exercise : forall n m o:nat,
  n=m->m=o->n+m=m+o.
Proof. intros n m o. intros H. intros I. rewrite <- I. rewrite<-H. reflexivity. Qed.
Theorem mult_0_plus : forall n m:nat,
  (0+n)*m=n*m.
Proof. intros n m. rewrite -> plus_0_n. reflexivity. Qed.
Theorem mult_1_plus : forall n m:nat,(1+n)*m=m+(n*m).
Proof. intros n m. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_0 : forall n:nat, beq_nat (n+1) 0 =false.
Proof. intros n. destruct n as [|n']. reflexivity. reflexivity. Qed.
Theorem negb_involutive : forall b:bool, negb(negb b) = b.
Proof. intros b. destruct b. reflexivity. reflexivity. Qed.
Theorem zero_nbeq_plus_1 : forall n:nat, beq_nat 0 (n+1) = false.
Proof. intros n. destruct n. reflexivity. reflexivity. Qed.

Theorem plus_0_r : forall n:nat, n+0=n.
Proof. intros n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem minus_diag : forall n, minus n n = 0.
Proof. intros n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem mult_0_r : forall n:nat, n*0=0.
Proof. intros n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem plus_n_Sm : forall n m:nat, S (n+m)=n+ (S m).
Proof. intros n m. induction n. rewrite plus_0_n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem plus_comm : forall n m:nat, n+m=m+n.
Proof. intros n m. induction n. simpl. rewrite plus_0_r. reflexivity. simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity. Qed.
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n:nat, double n=n+n.
Proof. intros n. induction n. reflexivity. simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity. Qed.

Theorem plus_assoc : forall n m p:nat, n+(m+p)=(n+m)+p.
Proof. intros n m p. induction n. reflexivity. simpl. rewrite -> IHn. reflexivity. Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem mult_0_plus' : forall n m:nat, (0+n)*m=n*m.
Proof. intros n m. assert (H: 0 + n=n). reflexivity. rewrite -> H. reflexivity. Qed.

Theorem plus_rearrange : forall n m p q:nat, (n+m)+(p+q)=(m+n)+(p+q).
Proof. intros n m p q. assert (H: n+m=m+n). rewrite plus_comm. reflexivity.
rewrite H. reflexivity. Qed.
Theorem plus_swap : forall n m p:nat, n+(m+p)=m+(n+p).
Proof. intros n m p. rewrite <- plus_comm. assert (H: p+n=n+p). rewrite plus_comm. reflexivity.
rewrite <- H. assert(H2: m+(p+n)=(m+p)+n). rewrite plus_assoc. reflexivity. rewrite H2. reflexivity. Qed.
Theorem S_plus : forall n:nat, S n = n+1.
Proof. intros n. induction n. reflexivity. assert (H1:S(S n)=S(n+1)). rewrite IHn. reflexivity.
rewrite H1. simpl. reflexivity. Qed.
Theorem mult_1 : forall n:nat, n*1=n.
Proof. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.
Theorem mult_suc_r : forall n m:nat, n*(S m)=n+n*m.
Proof. induction n. reflexivity. simpl. intros m. rewrite IHn.
rewrite plus_assoc. assert (H1:m+n=n+m). rewrite plus_comm. reflexivity.
rewrite H1. rewrite plus_assoc. reflexivity. Qed.
Theorem mult_comm : forall m n:nat, m*n=n*m.
Proof. induction m. intros n. rewrite mult_0_r. reflexivity.
simpl. intros n. rewrite IHm. simpl. rewrite mult_suc_r. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Theorem evenb_n__oddb_Sn : forall n:nat, evenb n=negb(evenb (S n)).
Proof. induction n. reflexivity. simpl. rewrite IHn. rewrite negb_involutive.
destruct n. reflexivity. reflexivity. Qed.


Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof. destruct b. reflexivity. reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof. induction p. simpl. intros H. rewrite H. reflexivity.
intros H2. simpl. rewrite IHp. reflexivity. rewrite H2. reflexivity. Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. simpl. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof. destruct b. destruct c. reflexivity. reflexivity. destruct c. reflexivity. reflexivity. Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof. induction p. rewrite mult_0_r. rewrite mult_0_r. rewrite mult_0_r. reflexivity.
rewrite mult_suc_r. rewrite mult_suc_r. rewrite mult_suc_r. rewrite IHp.
rewrite plus_assoc. rewrite plus_assoc. 
assert (H0:m+n*p=n*p+m). rewrite plus_comm. reflexivity.
assert (H1:n+m+n*p=n+n*p+m). rewrite <- plus_assoc. 
rewrite <- plus_assoc. rewrite H0. reflexivity.
rewrite H1. reflexivity. Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof. induction n. reflexivity. simpl. intros m p. rewrite IHn. 
rewrite mult_plus_distr_r. reflexivity. Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof. intros n m p. rewrite plus_assoc. rewrite plus_assoc. replace (n+m) with (m+n).
reflexivity. rewrite plus_comm. reflexivity. Qed.










