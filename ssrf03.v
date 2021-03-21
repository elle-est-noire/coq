From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.

Lemma contrap : forall (A B:Prop),
  (A -> B) -> (~B -> ~A).
Proof.
  rewrite /not. (*定義を紐解く*)
  move=> A B AtoB notB.
  by move /AtoB.
Qed.

(*B に apply (A->B) をすると A になる*)
(*A->C に move /(A->B) をすると B->C になる*)

Variables A B C : Prop.

Lemma AndOrDistL : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
Proof.
  rewrite /iff.
  apply: conj.
  -case.
   +case=> AisTrue CisTrue. (*case. move=> _ _*)
    by apply: conj; [apply: or_introl |]. (*apply conj. apply or_introl. by []*)
    case=> BisTrue CisTrue.
    by apply: conj; [apply: or_intror |].
  -case=> AorBisTrue CisTrue.
  (*move: AorBisTrue. case. move=> AisTrue. apply or_introl. by [].
  move=> BisTrue. apply or_intror. by [].*)
   case: AorBisTrue => [AisTrue | BisTrue].
   +by apply: or_introl.
   +by apply: or_intror.
Qed.

Inductive ex' (A:Type) (P:A -> Prop) : Prop :=
  ex_intro' : forall x:A, (P x -> ex' (A:=A) P).
Check ex_intro'.

Lemma JDM (T:Type) (P:T->Prop):
  ~(exists (x:T), P x) <-> forall x, ~(P x).
Proof.
  apply: conj => Hyp. (*apply:conj. move=> Hyp.*)
  -move=> x0 HPx0.
  apply: Hyp.
  (*Print ex.*)
  by apply: (ex_intro P x0).
  by case.
Qed.

Hypothesis ExMidLaw : forall P : Prop, P \/ ~P.

Lemma notnotEq (P : Prop): ~~P -> P.
Proof.
  move=> HnotnotP.
  move: (ExMidLaw (~P)).
  case.
  move=> /HnotnotP.
  by [].
  move: (ExMidLaw P).
  case. move=> H1 H2. apply H1.
  move=> H1.
  apply HnotnotP in H1.
  inversion H1.
Qed.
  

Search (_ /\ _).
From mathcomp Require Import ssrnat.
Search _ (_ + _ = _).

Locate and_comm.
Locate conj.
Locate "+".
Locate "^".
Locate "/\".

Section AxiomTest.

Variables Q : Prop.
Axiom a_axiom : Q.
Hypothesis a_hypo : Q.

End AxiomTest.

Check a_axiom.
(*Check AxiomTest.a_hypo.*)
End Logic.

Record magma : Type := Magma {
  carrier : Type ;
  operator : carrier -> carrier -> carrier
}.

Check magma.
Check Magma.

Definition prop_and_magma := Magma and.
Print prop_and_magma.
Definition nat_plus_magma := Magma plus.
Print nat_plus_magma.

Check (operator).
Lemma PropMagmaFalse (x y:carrier prop_and_magma) : 
  (operator x False) -> y.

  Abort.

Record semigroup : Type := Semigroup {
  scarrier : magma ;
  assoc : forall a b c : carrier scarrier,
    operator a (operator b c)
    = operator (operator a b) c
}.

Check addnA. Check addn.
Locate "+".
Theorem plus_comm : forall (a b c : carrier nat_plus_magma),
  (operator a (operator b c))=operator (operator a b) c.
Proof.
  apply addnA.
Qed.

Canonical nat_plus_magma.
Definition nat_plus_semigroup := Semigroup
  addnA.

(* Definition nat_plus_semigroup := Semigroup
  plus_comm. *)

Notation "a ^ b" := (operator a b).
Canonical nat_plus_semigroup.
Lemma natPlusExample1 (x y z : carrier nat_plus_magma) : 
  x ^ (y ^ z) = (x ^ y) ^ z.
Proof. by rewrite assoc. Qed.

From mathcomp Require Import ssrbool.

Check addbb. Check ssrfun.self_inverse.
Print addbb.
Locate "==>".

From mathcomp Require Import eqtype.

Print eqType.
About eqType.
Locate ".+4".
Eval simpl in (muln 3 4).
Compute (muln 3 4).
Check ex_minn.
Check pred nat.




