(* Proof of Euclid' theorem *)
(* Constructive proof by Euclid himself *)

From mathcomp Require Import all_ssreflect.

Fixpoint primorial n :=
  if n is S m then (if prime n then n else 1) * primorial m else 1.

Notation "n `#" := (primorial n) (at level 2).

Lemma primo_gtS n: 1 < n`# .+1.
Proof.
  rewrite ltnS; elim: n => // m IH. by rewrite muln_gt0; case:(prime m.+1).
Qed.  

Lemma dvdn_primo {m n}: m <= n -> prime m -> m %| n`#.
Proof.
  move=>mn pm; move:mn; elim n.
  - by rewrite leqn0=>/eqP E; move:E pm=>->; auto.
  - by move=> n' IH mn/=; move: leq_eqVlt mn pm => ->/orP[/eqP<-->|]; auto.
Qed. 

Theorem Euclid's_theorem: forall n, exists p, prime p /\ n < p.
Proof.
  move => n; pose m:= pdiv (n`# .+1).
  have pm: prime m by apply/pdiv_prime/primo_gtS.
  exists m; split; [done|rewrite leqNgt ltnS; apply/negP=>mn].
  move: {mn} (dvdn_primo mn pm) (pdiv_dvd (n`# .+1)); fold m => mnp.
  apply/negP; rewrite -(prime_coprime _ pm); apply/(coprime_dvdl mnp)/coprimenS.
Qed.