Require Import Arith Lia.

Fixpoint sumn (n : nat) :=
  match n with S n' => sumn n' + n' | 0 => 0 end.

Lemma sumn_eq (n : nat) : sumn n = (n * (n - 1)) / 2.
Proof.
induction n as [ | p Ih].
  compute.
  easy.
cbn [sumn].
rewrite Ih.
Fail ring.
destruct p as [ | p'].
  compute.
  easy.
replace (S p' - 1) with p' by lia.
replace (S (S p') - 1) with (S p') by lia.
Search (_ * _ = _ * _).
rewrite <- (Nat.mul_cancel_r _ _ 2); auto.
Search ((_ + _) * _).
rewrite Nat.mul_add_distr_r.
Search (_ * (_ / _)).
assert (even_prod : forall k, S k * k / 2 * 2 = S k * k).
  assert (aux : forall k, exists l, S k * k = l * 2).
    intros k; induction k as [ | k' Ihk].
      exists 0; easy.
    destruct Ihk as [l1 Pl1].
    exists (l1 + S k').
    replace (S (S k') * S k') with (S k' * k' + 2 * S k') by ring.
    rewrite Pl1; ring.
  intros k; destruct (aux k) as [l Pl].
  now rewrite Pl, Nat.div_mul; auto.
rewrite !even_prod.
ring.
Qed.
