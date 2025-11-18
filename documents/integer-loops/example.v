Require Import ZArith Arith Lia Zwf.

Open Scope Z_scope.

 Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition sum_n (n : Z) :=
  Z.iter n (fun '(s, i) => (s + i, i + 1)) (0, 0).

Definition sum_n' (n : Z) := fst (sum_n n).
Lemma sum_n'_0 : sum_n' 0 = 0.
easy.
Qed.

Lemma Z_iter_succ_l : forall (i : Z) (A : Type) (f : A -> A) (a : A),
  0 <= i -> Z.iter (i + 1) f a = f (Z.iter i f a).
Proof.
intros i A f a xge0.
Search Z.iter.
rewrite iter_nat_of_Z;[ | lia].
replace (Z.abs_nat (i + 1)) with (S (Z.abs_nat i)) by lia.
simpl; rewrite <- iter_nat_of_Z;[ | lia].
easy.
Qed.

Lemma Z_iter_ind : forall {A : Type}, forall P : Z -> A -> Prop,
forall (a : A)(f : A -> A),
P 0 a ->
(forall i x, 0 <= i -> P i x -> P (i + 1) (f x)) ->
forall n, 0 <= n -> P n (Z.iter n f a).
Proof.
intros A P a f pstart pstep.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros nge0.
destruct (n =? 0) eqn:cmp0.
  replace n with 0 by lia.
  exact pstart.
replace n with ((n - 1) + 1) by ring.
rewrite Z_iter_succ_l; [ | lia].
apply pstep;[lia | ].
apply Ih; lia.
Qed.

Lemma Z_iter_succ_r : forall (i : Z) (A : Type) (f : A -> A) (a : A),
  0 <= i -> Z.iter (i + 1) f a = Z.iter i f (f a).
Proof.
intros i A f.
induction i as [i Ih] using (well_founded_ind (Z.lt_wf 0)).
intros a.
destruct (i =? 0) eqn:cmp0.
  intros ige0; replace i with 0 by lia.
  easy.
intros ige0.
rewrite Z_iter_succ_l;[ | lia].
replace i with ((i - 1) + 1) by ring.
  rewrite Ih, Z_iter_succ_l;[easy | ..]; lia.
Qed.

Lemma sum_n'_formula n : 0 <= n ->
  sum_n' n = (n * (n - 1)) / 2.
Proof.
intros nge0; unfold sum_n', sum_n.
set (P := fun i '(s, j) => i = j /\ s = (i * (i - 1) / 2)).
assert (pstart : P 0 (0, 0)).
  unfold P; lia.
assert (pstep : forall k t, 0 <= k -> P k t ->
  P (k + 1) ((fun '(s, j) => (s + j, j + 1)) t)).
  intros k [s j] kge0 [kj sq].
  split.
    now rewrite kj.
  lia.
generalize (Z_iter_ind P (0, 0) (fun '(s, j) => (s + j, j + 1)) pstart
             pstep n nge0).
destruct Z.iter as [v1 v2]; unfold P, fst.
tauto.
Qed.

Lemma sum_n2_formula n : 0 <= n ->
  Z.iter n (fun '(s, i) => (s + i ^ 2, i + 1)) (0, 0) = 
    (n * (2 * n - 1) * (n - 1) / 6, n).
Proof.
intros nge0.
set (P := fun i '(s, j) => i = j /\ s = i * (2 * i - 1) * (i - 1) / 6).
assert (pstart : P 0 (0, 0)) by easy.
assert(pstep :
  forall k t, 0 <= k -> P k t -> P (k + 1) ((fun '(s, i) =>
   (s + i ^ 2, i + 1)) t)).
  intros k [s j] kge0 [kj sq].
  split.
    now rewrite kj.
  rewrite kj.
  lia.
assert (Main := Z_iter_ind P _ _ pstart pstep _ nge0).
destruct Z.iter as [v v0].
destruct Main as [indexq sumq].
rewrite <- indexq.
rewrite <- sumq.
easy.
Qed.

Definition fib n :=
  fst (Z.iter n (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1)).

Lemma fib0 : fib 0 = 0.
Proof. easy. Qed.

Lemma fib1 : fib 1 = 1.
Proof. easy. Qed.

Lemma fib_pair n : 1 < n ->
  Z.iter n (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1) =
  (fst (Z.iter (n - 1) (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1))
   + fst (Z.iter (n - 2) (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1)),
   fst (Z.iter (n - 1) (fun '(fn, fnm1) => (fn + fnm1, fn)) (0, 1))).
Proof.
intros ngt1.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 1)).
destruct (n =? 2) eqn:cmp2.
  replace n with 2 by lia.
  easy.
pattern n at 1.
replace n with (n - 1 + 1) by ring.
rewrite Z_iter_succ_l;[ | lia].
rewrite Ih;[ | lia | lia].
replace (n - 1 - 1) with (n - 2) by ring.
replace (n - 1 - 2) with (n - 3) by ring.
easy.
Qed.

Lemma fib_rec n : 1 < n ->
  fib n = fib (n - 1) + fib (n - 2).
Proof.
intros ngt1.
assert (main := fib_pair n ngt1).
unfold fib at 1.
rewrite main.
easy.
Qed.

Lemma every_fib :
 forall g, g 0 = 0 -> g 1 = 1 ->
  (forall i, 1 < i -> g i = g (i - 1) + g (i - 2)) ->
  forall n, 0 <= n -> g n = fib n.
Proof.
intros g g0 g1 ggt1 n.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros nge0.
destruct (n =? 0) eqn:cmp0.
  replace n with 0 by lia.
  apply g0.
destruct (n =? 1) eqn:cmp1.
  replace n with 1 by lia.
  apply g1.
rewrite ggt1;[ | lia].
rewrite fib_rec;[ | lia].
rewrite Ih;[ | lia | lia].
rewrite Ih; [ | lia | lia].
easy.
Qed.

Definition bin (n : Z) :=
  Z.iter n (fun f m => f m + f (m - 1))
    (fun x => if x =? 0 then 1 else 0).

Lemma bin0 m : bin 0 m = if m =? 0 then 1 else 0.
Proof. easy. Qed.

Lemma bin_rec n m: 0 <= n -> bin (n + 1) m = bin n m + bin n (m - 1).
Proof.
intros nge0.
unfold bin; rewrite Z_iter_succ_l; easy.
Qed.

Lemma bin_outside n m : 0 <= n -> (m < 0 \/ n < m) ->
  bin n m = 0.
Proof.
revert m.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros m nge0.
destruct (n =? 0) eqn:cmp0.
  intros mplaces.
  replace n with 0 by lia.
  simpl.
  replace (m =? 0) with false by lia.
  easy.
replace n with (n - 1 + 1) by ring.
rewrite bin_rec;[ | lia].
intros mconds.
assert (mcond1 : m < 0 \/ n - 1 < m) by lia.
assert (mcond2 : m -1 < 0 \/ n - 1 < m - 1) by lia.
rewrite Ih;[ | lia | lia |easy ].
rewrite Ih;[ | lia | lia | easy].
ring.
Qed.

Definition fact (n : Z) :=
  fst (Z.iter n (fun '(p, i) => (p * i, i + 1)) (1, 1)).

Lemma fact0 : fact 0 = 1.
Proof. easy. Qed.

Lemma fact_rec n :  0 <= n -> fact (n + 1) = fact n * (n + 1).
Proof.
intros nge0.
assert (main : forall m, 0 <= m -> 
  snd (Z.iter m (fun '(p, i) => (p * i, i + 1)) (1, 1)) = m + 1).
  set (P := fun i (t : Z * Z) => snd t = i + 1).
  assert (pstart : P 0 (1, 1)) by easy.
  assert (pstep : forall k t, 0 <= k -> P k t -> P (k + 1)
            ((fun '(p, i) => (p * i, i + 1)) t)).
    intros k [p i]; unfold P; simpl; intros kge0 Ih.
    lia.
  apply (Z_iter_ind P (1, 1) _ pstart pstep).
unfold fact; rewrite Z_iter_succ_l;[ | lia].
assert (main':= main n nge0).
destruct (Z.iter n) as [p i]; simpl in main' |- *.
lia.
Qed.

Lemma fact_gt0 : forall n, 0 <= n -> 0 < fact n.
Proof.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros nge0.
destruct (n =? 0) eqn:cmp0.
  replace n with 0 by lia.
  rewrite fact0.
  lia.
replace n with (n - 1 + 1) by ring.
rewrite fact_rec;[ | lia].
assert (0 < fact (n - 1)).
  apply Ih; lia.
lia.
Qed.

Lemma bin_n_n n : 0 <= n -> bin n n = 1.
Proof.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros nge0.
destruct (n =? 0) eqn:cmpn0.
  replace n with 0 by lia.
  easy.
replace n with (n - 1 + 1) at 1 by ring.
rewrite bin_rec;[ | lia].
rewrite bin_outside;[ | lia | lia].
rewrite Ih;[ | lia | lia].
ring.
Qed.

Lemma bin_n_0 n : 0 <= n -> bin n 0 = 1.
Proof.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros nge0.
destruct (n =? 0) eqn:cmpn0.
  replace n with 0 by lia.
  easy.
replace n with (n - 1 + 1) by ring.
rewrite bin_rec;[ | lia].
  rewrite Ih;[ | lia | lia].
rewrite bin_outside; lia.
Qed.

Lemma bin_and_fact n m : 0 <= m <= n ->
  bin n m = fact n / (fact m * fact (n - m)).
Proof.
intros mnge0.
enough (no_div : (fact m * fact (n - m) * bin n m = fact n)).
  assert (0 < fact m) by (apply fact_gt0; lia).
  assert (0 < fact (n - m)) by (apply fact_gt0; lia).
  rewrite <- no_div.
  rewrite <- (Z.mul_comm (bin n m)).
  rewrite Z.div_mul.
    easy.
  lia.
revert m mnge0.
induction n as [n Ih] using (well_founded_ind (Z.lt_wf 0)).
intros m mnge0.
destruct (n =? 0) eqn:cmp0.
  replace n with 0 by lia.
  replace m with 0 by lia.
  replace (0 - 0) with 0 by ring.
  rewrite fact0.
  simpl; easy.
destruct (n =? m) eqn:cmpmn.
  replace n with m by lia.
  rewrite bin_n_n;[ | lia].
  replace (m - m) with 0 by ring.
  rewrite fact0.
  ring.
destruct (m =? 0) eqn:cmpm0.
  replace m with 0 by lia.
  replace (n - 0) with n by ring.
  rewrite bin_n_0;[ | lia].
  rewrite fact0.
  ring.
replace n with (n - 1 + 1) at 2 3 by ring.
rewrite bin_rec;[ | lia].
rewrite fact_rec;[ | lia].
replace (n - 1 + 1) with n by ring.
set (facts := fact m * fact (n - m)).
replace (facts * (bin (n - 1) m + bin (n - 1) (m - 1)))
  with (facts * bin (n - 1) m + facts * bin (n - 1) (m - 1)) by ring.
replace (facts * bin (n - 1) m) with
  ((n - m) * (fact m * fact (n - 1 - m) * bin (n - 1) m)); cycle 1.
  unfold facts.
  replace (n - m) with (n - 1 - m + 1) by ring.
  rewrite fact_rec;[ | lia].
  ring.
rewrite Ih;[ | lia | lia].
replace (facts * bin (n - 1) (m - 1)) with
  (m * (fact (m - 1) * fact (n - 1 - (m - 1)) * bin (n - 1) (m - 1)));
  cycle 1.
  unfold facts.
  replace (n - m) with (n - 1 - (m - 1)) by ring.
  replace (fact m) with (m * fact (m - 1)).
    ring.
  replace m with (m - 1 + 1) at 3 by ring.
  rewrite fact_rec;[ | lia].
  ring.
rewrite Ih;[ | lia | lia].
ring.
Qed.


