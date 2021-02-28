Require Export study02.

Module study03.

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

Definition id {A:Type} (x:A) : A := x.
Definition compose {A B C} (g:B->C)(f:A->B):=
  fun x => g (f x).
Goal forall A, compose id id = id (A := A).
Proof. auto. Qed.

Set Implicit Arguments.
Axiom eq0_le0 : forall (n:nat)(x:n=0),n<=0.
Print Implicit eq0_le0.
Axiom eq0_le0' : forall (n:nat){x:n=0},n<=0.
Print Implicit eq0_le0'.

End study03.
Module ImplicitTest.
Require Import Ascii String.

Inductive llist (X:Type) : Type :=
  | lnil : llist X
  | lcons : X -> llist X -> llist X.
Definition llist' {X:Type}:Type:= llist X.
Definition lnil' {X:Type}:llist X:= lnil X.
Definition lcons' {X:Type}:X->llist X->llist X:= lcons X.
Check (lcons' 2 (lcons' 1 (lnil' ))).
Check (lcons' "a" (lcons' "b" (lnil' ))).
(*Check (lcons 2 (lcons "c" (lnil ))).*)

Fixpoint lapp (X:Type) (l1 l2:llist X) : (llist X) :=
  match l1 with
  | lnil _ => l2
  | lcons _ h t => lcons X h (lapp X t l2)
  end.
Definition lapp' {X:Type} (l1 l2:llist X):(llist X):=lapp X l1 l2.
Fixpoint llength (X:Type) (l:llist X) : nat :=
  match l with
  | lnil _ => 0
  | lcons _ h t => S (llength X t)
  end.
Definition llength' {X:Type} (l:llist X):nat:=llength X l.
Definition lsnoc' {X:Type} (l:llist X) (v:X) : (llist X) :=
  lapp' l (lcons' v (lnil' )).
(*Definition lsnoc' {X:Type} (l:llist X)(v:X):(llist X):=lsnoc X l v.*)
Fixpoint lrev' {X:Type} (l:llist X) : llist X :=
  match l with
  | lnil _  => lnil'
  | lcons _ h t => lsnoc' (lrev' t) h
  end.
(*Definition lrev' {X:Type} (l:llist X) : llist X := lrev X l.*)
Definition list123'' := lcons' 1 (lcons' 2 (lcons' 3 lnil')).
Compute (llength' list123'').
Check lnil'. Check @lnil'.
Notation "x :: y" := (lcons' x y) (at level 60, right associativity).
Notation "[ ]" := lnil'.
Notation "[ x , .. , y ]" := (lcons' x .. (lcons' y []) ..).
Notation "x ++ y" := (lapp' x y) (at level 60, right associativity).

Definition list123''' := [1, 2, 3].
Check list123'''.

Fixpoint lrepeat (X:Type)(n:X)(count:nat):llist X:=
  match count with
  | 0 => lnil X
  | S count' => lcons X n (lrepeat X n count')
  end.
Definition lrepeat' {X:Type}(n:X)(count:nat):llist X:=
  lrepeat X n count.
Example test_lrepeat1:
  lrepeat' true 2 = lcons' true (lcons' true lnil').
Proof. reflexivity. Qed.

Theorem lnil_app : forall X:Type, forall l:llist X,
  lapp' [] l = l.
Proof. reflexivity. Qed.

Theorem lrev_lsnoc : forall X:Type, forall v:X, forall s:llist X,
  lrev' (lsnoc' s v) = v :: (lrev' s).
Proof. induction s. reflexivity. simpl. 
assert (H1:s++[v]=lsnoc' s v). reflexivity.
rewrite H1. rewrite IHs. reflexivity. Qed.

Theorem lapp_ass : forall X:Type, forall l1 l2 l3:llist X,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. induction l1. reflexivity. simpl. intros l2 l3. 
rewrite IHl1. reflexivity. Qed.
Theorem lsnoc_with_lapp : forall X:Type, forall l1 l2:llist X,
  forall v:X,  lsnoc' (l1++l2) v = l1 ++ (lsnoc' l2 v).
Proof. intros X l1 l2 v. unfold lsnoc'. rewrite lapp_ass.
reflexivity. Qed.

Inductive lprod (X Y:Type) : Type :=
  lpair : X -> Y -> lprod X Y. 
Definition lprod'{X Y:Type}:Type:=lprod X Y.
Definition lpair'{X Y:Type}:X -> Y -> lprod X Y:=lpair X Y.
Notation "( x , y )" := (lpair' x y).
Notation "X ^ Y" := (lprod X Y) : type_scope.
(*type_scope というアノテーションによって，型を解析する際に用いる省略形
であることを明示し，乗法の演算子との衝突を回避する．嘘*)
Locate "*". Locate "^".
Check nat ^ nat.
Check (2,3).
Definition lfst' {X Y:Type} (p:X ^ Y):X:=
  match p with (lpair _ _ x y) => x end.
Definition lsnd' {X Y:Type} (p:X ^ Y):Y:=
  match p with (lpair _ _ x y) => y end.
Compute lfst' (2,3).
Fixpoint lcombine' {X Y:Type}(lx:llist X)(ly:llist Y)
  : llist' :=
  match lx, ly with
  | lnil _ , _  => []
  | _, lnil _ => []
  | lcons _ x tx, lcons _ y ty => (x,y)::(lcombine' tx ty)
  end.
(*Fixpoint lcombine'' (lx:llist')(ly:llist')
  : llist' :=
  match lx, ly with
  | [] , _  => []
  | _, [] => []
  | x::tx, y::ty => (x,y)::(lcombine' tx ty)
  end.*)
Check @lcombine'.
Compute (lcombine' [1,2][false,false,true,true]).
Compute [(1,false),(2,false)].
Example test_lcombine:lcombine' 
  [1,2][false,false,true,true]=[(1,false),(2,false)].
Proof. reflexivity. Qed.
Fixpoint lsplit'{X Y:Type} (l:llist (X^Y)) : (llist X) ^ (llist Y) :=
  match l with
  | lnil _ => ([],[])
  | lcons _ (lpair _ _ x y) t => (x::lfst'(lsplit' t),y::lsnd'(lsplit' t))
  end.
Example test_lsplit:
  lsplit' [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity. Qed.

Inductive loption (X:Type) : Type :=
  | lSome : X -> loption X
  | lNone : loption X.
Definition loption' {X:Type} : Type := loption X.
Definition lSome' {X:Type} : X -> loption' := lSome X.
Definition lNone' {X:Type} : loption' := lNone X.
Fixpoint lindex' {X:Type} (n:nat) (l:llist X) : loption' :=
  match l with
  | lnil _ => lNone'
  | lcons _ a l' => if beq_nat n 0 then lSome' a else lindex' (pred n) l'
  end.
Example test_lindex1 : lindex' 0 [4,5,6,7] = lSome' 4.
Proof. reflexivity. Qed.
Example test_lindex2 : lindex' 1 [[1],[2]] = lSome' [2].
Proof. reflexivity. Qed.
Example test_lindex3 : lindex' 2 [true] = lNone'.
Proof. reflexivity. Qed.
Definition lhd_opt' {X:Type} (l:llist X) : loption' :=
  lindex' 0 l.
Check @lhd_opt'.
Example test_lhd_opt1 : lhd_opt' [1,2] = lSome' 1.
Proof. reflexivity. Qed.
Example test_lhd_opt2 : lhd_opt' [[1],[2]] = lSome' [1].
Proof. reflexivity. Qed.



Module study03'.

Definition doit3times {X:Type} (f:X->X)(n:X) : X :=
  f (f (f n)).
Check @doit3times.
Definition minustwo (n :nat) : nat :=  
  match n with
  | O => O
  | S O => O
  | S (S (n')) => n'
  end.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.
Check plus.
Definition plus3:= plus 3.
Check plus3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.
Definition prod_curry {X Y Z:Type}
  (f:X^Y->Z)(x:X)(y:Y):Z:=f (x,y).
Definition prod_uncurry {X Y Z:Type}
  (f:X->Y->Z)(p:X^Y):Z:=f (lfst' p) (lsnd' p).
Check @prod_curry.
Check @prod_uncurry.
(*Theorem uncurry_curry_mine:forall (X Y Z:Type) (f:X^Y->Z),
  prod_uncurry(prod_curry f)=f.
Proof. intros X Y Z f. unfold prod_curry. unfold prod_uncurry.*)
Theorem uncurry_curry : forall (X Y Z:Type) (f:X->Y->Z) (x:X) (y:Y),
  prod_curry(prod_uncurry f) x y = f x y.
Proof. intros X Y Z f x y. unfold prod_curry. unfold prod_uncurry.
reflexivity. Qed.
Theorem curry_uncurry : forall (X Y Z:Type) (f:(X^Y)->Z) (p:X^Y),
  prod_uncurry(prod_curry f) p = f p.
Proof. unfold prod_uncurry. unfold prod_curry. intros X Y Z f p.
destruct p. reflexivity. Qed.

Fixpoint filter {X:Type} (test:X->bool)(l:llist X) : llist' :=
  match l with
  | lnil _ => []
  | lcons _ h t => 
    if test h then h::(filter test t)
    else filter test t
  end.
Example test_filter1:filter evenb [1,2,3,4]=[2,4].
Proof. reflexivity. Qed.
Definition length_is_1 {X:Type} (l:llist X) : bool :=
  beq_nat (llength' l) 1.
Example test_filter2:
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.
Definition countoddmembers' (l:llist nat) : nat :=
  llength' (filter NatList.oddb l).
Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' lnil' = 0.
Proof. reflexivity. Qed.
Example test_anon_fun' : doit3times (fun n => n*n) 2 = 256.
Proof. reflexivity. Qed.
Example test_filter2':
    filter (fun l => beq_nat (llength' l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l:llist nat) : llist nat :=
  filter (fun n => andb (NatList.evenb n) (ble_nat 8 n)) l.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.
Definition partition {X:Type} (test:X->bool) (l:llist X)
  : (llist X) ^ (llist X) :=
  ((filter test l) , (filter (fun x => negb (test x)) l)).
Example test_partition1: partition NatList.oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X->Y) (l:llist X) : llist' :=
  match l with
  | lnil _ => []
  | lcons _ h t => (f h) :: (map f t)
  end.
Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.
Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.
Theorem lsnoc_app:forall (X:Type) (l:llist X) (x:X),
  lsnoc' l x = l ++ [x].
Proof. reflexivity. Qed.
Theorem map_app1:forall (X Y:Type) (f:X->Y) (l:llist X) (x:X),
  map f (l++[x]) = (map f l) ++ [f x].
Proof. induction l. reflexivity. intros x0. simpl.
rewrite IHl. reflexivity. Qed.
Theorem map_rev:forall (X Y:Type)(f:X->Y)(l:llist X),
  map f (lrev' l) = lrev' (map f l).
Proof. induction l. reflexivity. simpl.
rewrite <- IHl. rewrite lsnoc_app. rewrite lsnoc_app.
rewrite map_app1. reflexivity. Qed.
Fixpoint flat_map {X Y:Type} (f:X->llist Y)(l:llist X)
  :(llist Y):=
  match l with
  | lnil _ => []
  | lcons _ h t => 
    (f h) ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.
Definition loption_map {X Y:Type} (f:X->Y)
  (xo:loption X) : loption Y :=
  match xo with
  | lNone _ => lNone'
  | lSome _ x => lSome' (f x)
  end.

Fixpoint fold {X Y:Type} (f:X->Y->Y)(l:llist X)(b:Y):Y:=
  match l with
  | lnil _ => b
  | lcons _ h t => f h (fold f t b)
  end.
Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).
Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 : fold lapp' [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.
Definition override {X:Type}(f:nat->X)(k:nat)(x:X)
  : nat->X :=
  fun (k':nat)=>if beq_nat k k' then x else f k'.
Definition fmostlytrue:=override (override ftrue 1 false)
  3 false.
Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.
Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.
Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.
Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.
Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof. reflexivity. Qed.
Theorem unfold_example:forall m n,
  3+n=m->plus3 n+1=m+1.
Proof. intros m n H. simpl. rewrite <- H.
reflexivity. Qed.
Theorem override_eq:forall {X:Type} x k(f:nat->X),
  (override f k x) k = x.
Proof. intros X x k f. unfold override.
rewrite beq_refl. reflexivity. Qed.
Theorem override_neq : forall {X:Type}
  x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof. intros X x1 x2 k1 k2 f H1 H2.
unfold override. rewrite H2. rewrite H1.
reflexivity. Qed.

Theorem eq_add_S:forall (n m:nat), S n=S m->n=m.
Proof. intros n m eq. inversion eq. reflexivity.
Qed.
Theorem silly4:forall (n m:nat),[n]=[m]->n=m.
Proof. intros n m eq. inversion eq. reflexivity.
Qed.
Theorem silly5:forall (n m o:nat),
  [n,m]=[o,o]->[n]=[m].
Proof. intros n m o eq. inversion eq.
reflexivity. Qed.
Example sillyex1 : forall (X : Type) (x y z : X)
 (l j : llist X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof. intros X x y z l j H1 H2.
inversion H1. inversion H2.
rewrite H0. reflexivity. Qed.
Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof. intros n H. inversion H. Qed.
Theorem silly7 : forall (n m : nat),
     false = true -> [n] = [m].
Proof. intros n m H. inversion H. Qed.
Example sillyex2 : forall (X : Type) (x y z : X) (l j : llist X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof. intros X x y z l j H1 H2. inversion H1. Qed.

Lemma eq_remove_S:forall n m, n=m->S n=S m.
Proof. intros n m H. inversion H. reflexivity. Qed.
Theorem beq_nat_eq:forall n m,
  true=beq_nat n m->n=m.
Proof. induction n. induction m. reflexivity.
simpl. intros H1. inversion H1. induction m.
simpl. intros H2. inversion H2. simpl.
intros H3. apply eq_remove_S. apply IHn.
apply H3. Qed.
Theorem beq_nat_eq':forall m n,
  beq_nat n m = true -> n = m.
Proof. intros m. induction m. destruct n.
reflexivity. simpl. intros H. inversion H.
destruct n. simpl. intros H. inversion H.
simpl. intros H. apply eq_remove_S.
apply IHm. apply H. Qed.
Theorem length_snoc':forall (X:Type)(v:X)
  (l:llist X)(n:nat),
  llength' l = n -> llength' (lsnoc' l v) = S n.
Proof. induction l. simpl. intros n H. inversion H.
reflexivity. simpl. intros n' H. apply eq_remove_S.
induction n'. inversion H.
assert (H1:l++[v]=lsnoc' l v). reflexivity.
apply IHl. inversion H. reflexivity. Qed.
Theorem length_snoc'':forall (X:Type)(v:X)
  (l:llist X)(n:nat),
  llength' l = n -> llength' (lsnoc' l v) = S n.
Proof. intros X v l. induction l. intros n eq.
rewrite <- eq. reflexivity. intros n eq.
simpl. destruct n. inversion eq.
apply eq_remove_S. apply IHl. inversion eq.
reflexivity. Qed.
Theorem beq_nat_0_l:forall n,
  true=beq_nat 0 n -> 0 = n.
Proof. induction n. reflexivity.
simpl. intros H. inversion H. Qed.
Theorem beq_nat_0_r:forall n,
  true=beq_nat n 0  -> 0 = n.
Proof. induction n. reflexivity.
simpl. intros H. inversion H. Qed.
Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof. induction n. simpl. intros m H.
destruct m. reflexivity. inversion H.
destruct m. simpl. intros H. inversion H.
simpl. intros H. apply eq_remove_S. 
apply IHn. inversion H. reflexivity. Qed.

Theorem S_inj:forall (n m:nat) (b:bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof. intros n m b H. simpl in H.
apply H. Qed.
Theorem silly3' : forall (n:nat),
(beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof. intros n H1 H2. symmetry in H2. apply H1 in H2.
symmetry in H2. apply H2. Qed.
Theorem plus_n_n_injection : forall n m,
  n+n=m+m->n=m.
Proof. induction n. simpl. destruct m. reflexivity.
simpl. intros H. inversion H. induction m as [|m'].
simpl. intros H. inversion H. intros H.
apply eq_remove_S. simpl in H. inversion H. 
rewrite plus_comm in H1. symmetry in H1. 
 rewrite plus_comm in H1. simpl in H1.
inversion H1. symmetry in H2. apply IHn.
apply H2. Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.
Theorem sillyfun_false:forall (n:nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  reflexivity. destruct (beq_nat n 5).
  reflexivity. reflexivity. 
Qed.
Theorem override_shadow:forall {X:Type} x1 x2 k1 k2
  (f:nat->X),
  (override (override f k1 x2) k1 x1) k2
  = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  reflexivity. reflexivity.
Qed.
Check @lsplit'.
Theorem lcombine_lsplit:forall (X Y:Type)(p:llist (X^Y)),
  lcombine' (lfst' (lsplit' p)) (lsnd' (lsplit' p)) = p.
Proof.
  intros X Y p. induction p.
  reflexivity. destruct x. simpl.
  rewrite IHp. reflexivity.
Qed.
Definition beq_lnil' {X:Type} (l:llist X) : bool :=
  match l with
  | lnil _ => true
  | lcons _ _ _ => false
  end.
Theorem lsplit_lcombine:forall (X Y:Type)(x:llist X)(y:llist Y),
  llength' x = llength' y -> 
    lsplit' (lcombine' x y) = (x,y).
Proof.
  induction x. induction y. reflexivity.
  simpl. intros H. inversion H.
  induction y. simpl. intros H. inversion H.
  simpl. intros H. rewrite IHx. reflexivity.
  inversion H. reflexivity. 
Qed.

Definition sillyfun1 (n:nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.
Theorem sillyfun1_odd:forall (n:nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3. apply beq_nat_eq in Heqe3.
  rewrite Heqe3. reflexivity.
  remember (beq_nat n 5) as e5. destruct e5.
  apply beq_nat_eq in Heqe5.
  rewrite Heqe5. reflexivity.
  inversion eq. 
Qed.
Theorem override_same:forall {X:Type} x1 k1 k2
  (f:nat->X), f k1 = x1 -> (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq.
  remember (beq_nat k1 k2) as keq.
  destruct keq. apply beq_nat_eq in Heqkeq.
  rewrite Heqkeq. unfold override.
  rewrite beq_refl. rewrite <- Heqkeq.
  symmetry in eq. apply eq.
  unfold override. rewrite <- Heqkeq.
  reflexivity.
Qed.
Theorem filter_exercise:forall (X:Type)(test:X->bool)
  (x:X)(l lf:llist X),
  filter test l = x :: lf -> test x = true.
Proof.
  induction l. intros lf H. inversion H.
  remember (test x0) as x0test.
  destruct x0test. simpl.
  rewrite <- Heqx0test. intros lf H.
  inversion H. rewrite <- H1. rewrite Heqx0test.
  reflexivity. simpl. rewrite <- Heqx0test.
  apply IHl.
Qed. 

Theorem trans_eq:forall {X:Type} (n m o:X),
  n=m->m=o->n=o.
Proof.
  intros X n m o H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.
Example trans_eq_example:forall (a b c d e f:nat),
  [a,b]=[c,d]->[c,d]=[e,f]->[a,b]=[e,f].
Proof.
  intros a b c d e f H1 H2.
  apply trans_eq with (m:=[c,d]).
  apply H1. apply H2.
Qed.
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  apply eq2. apply eq1.
Qed.
Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_eq in eq1.
  apply beq_nat_eq in eq2.
  rewrite eq1. rewrite eq2.
  symmetry.
  apply beq_refl.
Qed.
Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f eq.
  unfold override.
  remember (beq_nat k1 k3) as k13.
  remember (beq_nat k2 k3) as k23.
  destruct k13. destruct k23.
  apply beq_nat_eq in Heqk23.
  apply beq_nat_eq in Heqk13.
  rewrite Heqk13 in eq.
  rewrite Heqk23 in eq.
  rewrite beq_refl in eq.
  inversion eq. reflexivity.
  reflexivity.
Qed.

Definition fold_length {X : Type} (l : llist X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.
Theorem fold_length_correct : forall X (l : llist X),
  fold_length l = llength' l.
Proof.
  induction l. reflexivity.
  simpl. rewrite <- IHl. reflexivity.
Qed.
Definition fold_map {X Y:Type} (f : X -> Y) (l : llist X) : llist Y :=
  fold (fun x yl => (f x)::yl) l [].
Theorem fold_map_correct : forall (X Y:Type) (f:X->Y) (l:llist X),
  fold_map f l = map f l.
Proof.
  induction l. reflexivity.
  simpl. rewrite <- IHl. reflexivity.
Qed.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Fixpoint forallb {X:Type} (f:X->bool) (l:llist X) : bool :=
  match l with
  | lnil _ => true
  | lcons _ t h => andb (f t) (forallb f h)
  end.
Example forallb_test1 : forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity. Qed.
Example forallb_test2 : forallb negb [false,false] = true.
Proof. reflexivity. Qed.
Example forallb_test3 : forallb evenb [0,2,4,5] = false.
Proof. reflexivity. Qed.
Example forallb_test4 : forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.
Fixpoint existsb {X:Type} (f:X->bool) (l:llist X) : bool :=
  match l with
  | lnil _ => false
  | lcons _ t h => orb (f t) (existsb f h)
  end.
Example existsb_test1 : existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.
Example existsb_test2 : existsb (andb true) [true,true,false] = true.
Proof. reflexivity. Qed.
Example existsb_test3 : existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity. Qed.
Example existsb_test4 : existsb evenb [] = false.
Proof. reflexivity. Qed.
Definition existsb' {X:Type} (f:X->bool) (l:llist X) : bool :=
  negb (forallb (fun x => negb (f x)) l).
Theorem existsb_correct : forall (X:Type) (f:X->bool) (l:llist X),
  existsb f l = existsb' f l.
Proof.
  induction l. reflexivity.
  simpl. rewrite IHl. unfold existsb'. simpl.
  remember (f x) as fx.
  destruct fx. reflexivity.
  reflexivity.
Qed.
End study03'.
End ImplicitTest.

















