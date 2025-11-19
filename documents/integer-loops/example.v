Require Import ZArith Arith Lia Zwf.

Open Scope Z_scope.

 Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

 Ltac strong := try (easy || ring || lia).

Definition sum_n (n : Z) :=
  Z.iter n (fun '(s, i) => (s + i, i + 1)) (0, 0).

Definition sum_n' (n : Z) := fst (sum_n n).
Lemma sum_n'_0 : sum_n' 0 = 0.
easy.
Qed.

Module missing_lemmas_for_Z_iter.

Lemma Z_0_le_ind :
  forall P : Z -> Prop,
  (forall n, (forall l, 0 <= l < n -> P l) -> P n) ->
  forall n, P n.
Proof. exact (well_founded_ind (Z.lt_wf 0)). Qed.

Lemma Z_iter_succ_l : forall (i : Z) (A : Type) (f : A -> A) (a : A),
  0 <= i -> Z.iter (i + 1) f a = f (Z.iter i f a).
Proof.
intros i A f a xge0.
rewrite iter_nat_of_Z; strong.
replace (Z.abs_nat (i + 1)) with (S (Z.abs_nat i)) by strong.
simpl; rewrite <- iter_nat_of_Z; strong.
Qed.

Lemma Z_iter_ind : forall {A : Type}, forall P : Z -> A -> Prop,
forall (a : A)(f : A -> A),
P 0 a ->
(forall i x, 0 <= i -> P i x -> P (i + 1) (f x)) ->
forall n, 0 <= n -> P n (Z.iter n f a).
Proof.
intros A P a f pstart pstep.
induction n as [n Ih] using Z_0_le_ind.
intros nge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  rewrite n0.
  exact pstart.
replace n with ((n - 1) + 1) by strong.
rewrite Z_iter_succ_l; strong.
apply pstep; strong.
apply Ih; strong.
Qed.

Lemma Z_iter_succ_r : forall (i : Z) (A : Type) (f : A -> A) (a : A),
  0 <= i -> Z.iter (i + 1) f a = Z.iter i f (f a).
Proof.
intros i A f.
induction i as [i Ih] using Z_0_le_ind.
intros a ige0.
assert (i = 0 \/ 0 < i) as [i0 | igt0] by strong.
  replace i with 0; strong.
rewrite Z_iter_succ_l; strong.
replace i with ((i - 1) + 1) by strong.
  rewrite Ih; strong.
  rewrite Z_iter_succ_l; strong.
Qed.

End missing_lemmas_for_Z_iter.

Import missing_lemmas_for_Z_iter.

Lemma sum_n'_formula n : 0 <= n ->  sum_n' n = (n * (n - 1)) / 2.
Proof.
intros nge0; unfold sum_n', sum_n.
set (P := fun i '(s, j) => i = j /\ s = (i * (i - 1) / 2)).
assert (main : P n (Z.iter n (fun '(s, i) => (s + i, i + 1)) (0, 0))).
  assert (pstart : P 0 (0, 0)).
    unfold P; strong.
  assert (pstep : forall k t, 0 <= k -> P k t ->
    P (k + 1) ((fun '(s, j) => (s + j, j + 1)) t)).
    intros k [s j] kge0 [kj sq].
    split.
      now rewrite kj.
    strong.
  apply Z_iter_ind; strong.
destruct Z.iter as [v1 v2]; unfold P, fst.
unfold P in main.
strong.
Qed.

Lemma sum_n2_formula n : 0 <= n ->
  Z.iter n (fun '(s, i) => (s + i ^ 2, i + 1)) (0, 0) = 
    (n * (2 * n - 1) * (n - 1) / 6, n).
Proof.
intros nge0; unfold sum_n', sum_n.
set (P := fun i '(s, j) => i = j /\ s = (i * (2 * i - 1)* (i - 1) / 6)).
assert (main : P n (Z.iter n (fun '(s, i) => (s + i ^ 2, i + 1)) (0, 0))).
  assert (pstart : P 0 (0, 0)).
    unfold P; strong.
  assert (pstep : forall k t, 0 <= k -> P k t ->
    P (k + 1) ((fun '(s, j) => (s + j ^ 2, j + 1)) t)).
    intros k [s j] kge0 [kj sq].
    split.
      now rewrite kj.
    strong.
  apply Z_iter_ind; strong.
destruct Z.iter as [v1 v2]; unfold P, fst.
unfold P in main.
destruct main as [main indexq]; rewrite <- main, indexq.
strong.
Qed.

(* A section on the fibonacci function. *)
Definition fib n :=
  fst (Z.iter n (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1)).

Lemma fib0 : fib 0 = 0.
Proof. easy. Qed.

Lemma fib1 : fib 1 = 1.
Proof. easy. Qed.

(* we wish to prove that the fibonacci function satisfies the well
  known recursive equation fib n = fib (n - 1) + fib (n - 2) *)
Lemma fib_pair n : 1 < n ->
  Z.iter n (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1) =
  (fst (Z.iter (n - 1) (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1))
   + fst (Z.iter (n - 2) (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1)),
   fst (Z.iter (n - 1) (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1))).
Proof.
intros ngt1.
induction n as [n Ih] using Z_0_le_ind.
assert (n = 2 \/ 2 < n) as [n2 | ngt2] by strong.
  rewrite n2.
  easy.
pattern n at 1.
replace n with (n - 1 + 1) by strong.
rewrite Z_iter_succ_l; strong.
rewrite Ih; strong.
replace (n - 1 - 1) with (n - 2) by strong.
replace (n - 1 - 2) with (n - 3) by strong.
strong.
Qed.

Lemma fib_rec n : 1 < n -> fib n = fib (n - 1) + fib (n - 2).
Proof.
intros ngt1.
assert (main := fib_pair n ngt1).
unfold fib at 1.
rewrite main; strong.
Qed.

Lemma every_fib :
 forall g, g 0 = 0 -> g 1 = 1 ->
  (forall i, 1 < i -> g i = g (i - 1) + g (i - 2)) ->
  forall n, 0 <= n -> g n = fib n.
Proof.
intros g g0 g1 ggt1 n.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros nge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  rewrite n0.
  apply g0.
assert (n = 1 \/ 1 < n) as [n1 | ngt1] by strong.
  rewrite n1.
  apply g1.
rewrite ggt1; strong.
rewrite fib_rec; strong.
rewrite Ih; strong.
rewrite Ih; strong.
Qed.

(* A section about the binomial function. *)
Definition bin (n : Z) :=
  Z.iter n (fun f m => f m + f (m - 1))
    (fun x => if x =? 0 then 1 else 0).

Lemma bin0 m : bin 0 m = if m =? 0 then 1 else 0.
Proof. strong. Qed.

Lemma bin_rec n m: 0 < n -> bin n m = bin (n - 1) m + bin (n - 1) (m - 1).
Proof.
intros ngt0.
replace n with (n - 1 + 1) at 1 by ring.
unfold bin; rewrite Z_iter_succ_l; strong.
Qed.

Lemma bin_outside n m : 0 <= n -> (m < 0 \/ n < m) ->
  bin n m = 0.
Proof.
revert m.
induction n as [n Ih] using Z_0_le_ind.
intros m nge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  intros mplaces.
  rewrite n0.
  simpl.
  (* A specific behavior inherited from lia that requires explanation. *)
  replace (m =? 0) with false by strong.
  strong.
rewrite bin_rec; strong.
intros mconds.
rewrite Ih; strong.
rewrite Ih; strong.
Qed.

(* Definition of the factorial function.  We are using a
  for i in (1 .. n) pattern, as already seen in sum_n' *)
Definition fact (n : Z) :=
  fst (Z.iter n (fun '(p, i) => (p * i, i + 1)) (1, 1)).

Lemma fact0 : fact 0 = 1.
Proof. strong. Qed.

Lemma fact_rec n :  0 < n -> fact n = fact (n - 1) * n.
Proof.
intros ngt0.
assert (main : forall m, 0 <= m -> 
  snd (Z.iter m (fun '(p, i) => (p * i, i + 1)) (1, 1)) = m + 1).
  set (P := fun i (t : Z * Z) => snd t = i + 1).
  assert (pstart : P 0 (1, 1)) by strong.
  assert (pstep : forall k t, 0 <= k -> P k t -> P (k + 1)
            ((fun '(p, i) => (p * i, i + 1)) t)).
    intros k [p i]; unfold P; simpl; intros kge0 Ih.
    strong.
  apply (Z_iter_ind P (1, 1) _ pstart pstep).
replace n with (n - 1 + 1) at 1 by strong.
unfold fact; rewrite Z_iter_succ_l; strong.
(* There should be a specific induction theorem for the
  for i in (1 .. n) pattern. *)
assert (ge0 : 0 <= n - 1) by strong.
assert (main':= main (n - 1) ge0).
(* The specific need for simpl is unpleasant here. *)
destruct (Z.iter (n - 1)) as [p i]; simpl in main' |- *.
strong.
Qed.

Lemma fact_gt0 : forall n, 0 <= n -> 0 < fact n.
Proof.
induction n as [n Ih] using Z_0_le_ind.
intros nge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  rewrite n0, fact0; strong.
rewrite fact_rec; strong.
assert (0 < fact (n - 1)).
  apply Ih; strong.
strong.
Qed.

Lemma bin_n_n n : 0 <= n -> bin n n = 1.
Proof.
induction n as [n Ih] using Z_0_le_ind.
intros nge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  rewrite n0; strong.
rewrite bin_rec; strong.
rewrite bin_outside; strong.
rewrite Ih; strong.
Qed.

Lemma bin_n_0 n : 0 <= n -> bin n 0 = 1.
Proof.
induction n as [n Ih] using Z_0_le_ind.
intros nge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  rewrite n0; strong.
rewrite bin_rec; strong.
rewrite (bin_outside _ (0 - 1)); strong.
rewrite Ih; strong.
Qed.

(* Here is the main lemma we are interested in. *)
Lemma bin_and_fact n m : 0 <= m <= n ->
  bin n m = fact n / (fact m * fact (n - m)).
Proof.
revert m.
(* reasoning about division is especially difficult, because
  (a + b) / c = a / c + b / c only when either a or b is divisible by c *)
enough (main : forall m, 0 <= m <= n -> fact m * fact (n - m) * bin n m = fact n).
  intros m mnge0.
  rewrite <- (main m); strong.
  Search ((_ * ?x) / ?x).
  replace (fact m * fact (n - m) * bin n m) with (bin n m * (fact m * fact (n - m)))
    by strong.
  rewrite Z.div_mul; strong.
  enough (0 < fact m /\ 0 < fact (n - m)) by strong.
  assert (0 < fact m) by (apply fact_gt0; strong).
  assert (0 < fact (n - m)) by (apply fact_gt0; strong).
  strong.
(* Reducing to a common denominator is a pain when considering integer
  division. *)
induction n as [n Ih] using Z_0_le_ind.
intros m mnge0.
assert (n = 0 \/ 0 < n) as [n0 | ngt0] by strong.
  rewrite n0.
  assert (m0 : m = 0) by strong.
  rewrite m0; strong.
assert (m = 0 \/ 0 < m) as [m0 | mgt0] by strong.
  rewrite m0, fact0.
  replace (n - 0) with n by strong.
  replace (1 * fact n) with (fact n) by strong.
  rewrite bin_n_0; strong.
assert (m = n \/ m < n) as [mn | mltn] by strong.
  rewrite mn.
  replace (n - n) with 0 by strong.
  rewrite fact0.
  replace (fact n * 1) with (fact n) by strong.
  rewrite bin_n_n; strong.
rewrite bin_rec; strong.
set (facts := fact m * (fact (n - m))).
replace (facts * (bin (n - 1) m + bin (n - 1) (m - 1))) with
  (facts * bin (n - 1) m + facts * bin (n - 1) (m - 1)) by strong.
assert (main1 : facts * bin (n - 1) m = (n - m) * fact (n - 1)).
  unfold facts.
  rewrite (fact_rec (n - m)); strong.
  replace (n - m - 1) with (n - 1 - m) by strong.
  replace (fact m * (fact (n - 1 - m) * (n - m)) * bin (n - 1) m)
    with ((n - m) * (fact m * fact (n - 1 - m) * bin (n - 1) m)) by strong.
  rewrite Ih; strong.
assert (main2 : facts * bin (n - 1) (m - 1) = m * fact (n - 1)).
  unfold facts.
  rewrite (fact_rec m); strong.
  replace (fact (m - 1) * m * fact (n - m) * bin (n - 1) (m - 1))
    with (m * (fact (m - 1) * fact (n - m) * bin (n - 1) (m - 1))) by strong.
  replace (n - m) with (n - 1 - (m - 1)) by strong.
  rewrite Ih; strong.
  rewrite main1, main2.
  replace ((n - m) * fact (n - 1) + m * (fact (n - 1))) with
    (n * fact (n - 1)) by strong.
  rewrite (fact_rec n); strong.
Qed.


