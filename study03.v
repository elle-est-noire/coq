Require Export study02.


Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
Check nil. Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length X t)
  end.
Example test_length1:length nat
 (cons nat 2 (cons nat 1 (nil nat)))=2.
Proof. reflexivity. Qed.
Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X:Type) (l1 l2:list X) : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app X t l2)
  end.
Definition snoc (X:Type) (l:list X) (v:X) : (list X) :=
  app X l (cons X v (nil X)).
Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil _ => nil X
  | cons _ h t => snoc X (rev X t) h
  end.
Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.
Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app' X t l2)
  end.
Check app. Check app'.
Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length' _ t)
  end.
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Inductive list' (A:Set) : Set :=(* listの型はSet -> Set *)
  | nil' : list' A
  | cons' : A -> list' A -> list' A.

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length'' t)
  end.

Check @nil.























