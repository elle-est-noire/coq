Require Export study04.
Require Export study01. (*ないと何故かble_natを認識しない*)

Module st05.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.
Definition strange_prop : Prop :=
  (2+2=5)->(99+26=42).
Check ble_nat.
Definition strange_prop2 : Prop :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).
Definition even (n:nat) : Prop :=
  evenb n = true.
Check even.
Check even 2.
Check even 3.
Definition even_n__even_SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).
Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.
Definition teen : nat->Prop := between 13 19.
Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.
Definition true_for_n__true_for_Sn (P:nat->Prop) (n:nat) : Prop :=
  P n -> P (S n).
Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').
Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.
Definition our_nat_induction (P:nat->Prop) : Prop :=
     (true_for_zero P) ->
     (preserved_by_S P) ->
     (true_for_all_numbers P).

Inductive good_day : day -> Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.
Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.
Inductive day_before : day -> day -> Prop :=
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.
Inductive fine_day_for_singing : day -> Prop :=
  | fdfs_any : forall d:day, fine_day_for_singing d.
Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.
Check fdfs_wed.
Check fdfs_wed'.
Check fdfs_any.
Check fdfs_any wednesday.
Check fine_day_for_singing wednesday.
(* "OK"な日とは(1)良い日であるか(2)OKな日の前日である*)
Inductive ok_day : day -> Prop :=
  | okd_gd : forall d,
      good_day d ->
      ok_day d
  | okd_before : forall d1 d2,
      ok_day d2 ->
      day_before d2 d1 ->
      ok_day d1.
Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday
         (okd_gd saturday gd_sat)
         db_sat)
       db_fri)
    db_thu.
Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2:=thursday).
    apply okd_before with (d2:=friday).
      apply okd_before with (d2:=saturday).
          apply okd_gd. apply gd_sat.
          apply db_sat.
      apply db_fri.
  apply db_thu. 
Qed.
Print okdw'.

Definition okd_before2 := forall d1 d2 d3,
  ok_day d3 ->
  day_before d2 d1 ->
  day_before d3 d2 ->
  ok_day d1.
Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros d1 d2 d3 H1 H2 H3.
  apply okd_before with (d2:=d2).
  apply okd_before with (d2:=d3).
  apply H1. apply H3. apply H2.
Qed.
Print okd_before2_valid.

Check nat_ind.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

Check natlist1_ind.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check list_ind.

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

Check tree_ind.

Inductive mytype (X:Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y:Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

Check foo'_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.
Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind. reflexivity.
  unfold P_m0r. simpl. intros n' IHn'.
  apply IHn'.
Qed.

Inductive ev : nat -> Prop :=
  | ev_o : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev' : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_o.
Qed.
Print four_ev'.
Definition four_ev : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_o).

Theorem ev_plus4' : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. apply ev_SS. apply ev_SS.
  apply H.
Qed.
Print ev_plus4'.
Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) (H : ev n) => ev_SS (S (S n)) 
  (ev_SS n H).

Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n. simpl. apply ev_o.
  simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  simpl.
  apply ev_o.
  simpl. apply E'.
Qed.
(*Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct n.
  simpl. apply E.
  simpl. apply ev_SS.*)

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  unfold even. reflexivity.
  unfold even. unfold even in IHE'.
  simpl. apply IHE'.
Qed.

Theorem ev_sum : forall n m,
  ev n -> ev m -> ev (n+m).
Proof.
  intros n m En Em.
  induction En.
  apply Em.
  simpl. apply ev_SS.
  apply IHEn.
Qed.

Theorem SSev_evn : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E.
  apply H0.
Qed.
(* I が現在のコンテキストにおいて帰納的に宣言された仮定 P を
参照しているとします。 ここで、inversion I は、Pの
コンストラクタごとにサブゴールを生成します。 
各サブゴールにおいて、 コンストラクタが P を証明するのに
必要な条件によって I が置き換えられます。 サブゴールのうち
いくつかは矛盾が存在するので、 inversion はそれらを除外します。 
残っているのは、元のゴールが成り立つことを示すのに必要なサブゴールです。*)

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E.
  inversion H0.
  apply H2.
Qed.

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  inversion E.
  inversion H0.
  inversion H2.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E.
  simpl. rewrite <- H in E.
  apply E.
  simpl. apply H.
Qed.

Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Enm En.
  induction En.
  simpl in Enm. apply Enm.
  apply IHEn. simpl in Enm.
  inversion Enm. apply H0.
Qed.
(*Enm についての帰納法はダメ*)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E1 E2.
  assert (H1:ev((n+n)+(m+p))).
  replace ((n+n)+(m+p)) with ((n+m)+(n+p)).
  apply ev_sum with (n:=n+m) (m:=n+p).
  apply E1. apply E2.
  replace (n+m+(n+p)) with (n+(m+n)+p).
  replace (m+n) with (n+m).
  rewrite plus_assoc. rewrite plus_assoc. 
  reflexivity.
  rewrite plus_comm. reflexivity.
  rewrite plus_assoc. rewrite plus_assoc.
  reflexivity.
  apply ev_ev_even with (n:=n+n)(m:=m+p) in H1.
  apply H1.
  rewrite <- double_plus.
  apply double_even.
Qed.

Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp (4 + n)
  | MyProp3 : forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  apply MyProp2. apply MyProp2.
  apply MyProp1.
Qed.

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3. apply MyProp3. apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n
  -> MyProp (S (S n)).
Proof.
  intros n E. replace (S (S n)) with (2+n).
  apply MyProp3. apply MyProp2. apply E.
  reflexivity.
Qed.

Theorem MyProp_ev : forall n:nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E. apply MyProp_0.
  apply MyProp_plustwo. apply IHE.
Qed.

Theorem ev_MyProp : forall n:nat,
  MyProp n -> ev n.
Proof.
  intros n E.
  induction E.
  apply ev_SS. apply ev_SS. apply ev_o.
  apply ev_SS. apply ev_SS. apply IHE.
  apply ev_minus2 in IHE. simpl in IHE.
  apply IHE.
Qed.

About MyProp_ev.
Print MyProp_ev.
Locate plus_comm.








