Require Import Even.
From mathcomp Require Import eqtype ssrnat fintype div bigop prime binomial.
Require Import ssreflect ssrfun ssrbool.


Theorem t: forall n:nat,even(n*(1+n)).
Proof.
intros.
apply even_mult_aux.
elim n.
left.
SearchAbout(even _).
apply even_O.
intros.
elim H.
right.
SearchAbout(even _).
apply even_S, odd_S, H0.
left.
apply H0.
Qed.

Theorem tri:forall n:nat, even(n*(1+n)*(2+n)).
Proof.
intros.
apply even_mult_aux.
left.
apply t.
Qed.

Theorem sqn_even:forall n:nat, even (n ^ 2) -> even n.
Proof.
intros.
rewrite <-mulnn in H.
apply even_mult_aux in H.
destruct H.
apply H.
apply H.
Qed.