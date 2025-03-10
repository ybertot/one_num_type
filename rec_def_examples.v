Require Import List Reals Lra Lia.
Set Warnings "-notation-overridden".
Require Import R_subsets rec_def R_compute.
Set Warnings "notation-overridden".
From elpi Require Import elpi.
Open Scope R_scope.

Definition Zsqr (x : Z) := (x * x)%Z.

Lemma Zsqr_prf x : Rsqr (IZR x) = IZR (Zsqr x).
Proof. now unfold Zsqr; rewrite mult_IZR. Qed.

(* This command should only be used and seen by library developers *)
Elpi add_computation Rsqr Zsqr Zsqr_prf.

Recursive (def simple_example such that simple_example 0 = 0 /\
   forall n, Rnat (n - 1) -> simple_example n = simple_example (n - 1) + 1).

Lemma simple_example_Rnat n : Rnat n -> Rnat (simple_example n).
Proof.
rec_Rnat simple_example.
Qed.

Print simple_example.
(* This is the proof that is done automatically in rec_nat
intros nnat; unfold fib.
apply private.Rnat_rec_nat'; [ | | assumption ].
  intros [ | [ | [ | k]]]; cbn [nth]; typeclasses eauto.
intros m l lnat mnat [ | [ | [ | k]]]; typeclasses eauto.
Qed.
*)

Recursive (def fib such that
    fib 0 = 0 /\
    fib 1 = 1 /\
    forall n : R, Rnat (n - 2) ->
    fib n = fib (n - 2) + fib (n - 1)).

Elpi mirror_recursive_definition fib.
Check fib_Z_prf.
R_compute (fib 7 - fib 2).
Fail R_compute (fib (fib 2 - fib 7)).
R_compute (fib (fib 7 - fib 2)) fib_f7_f2_eqn.
Check fib_f7_f2_eqn.

R_compute (fib (7 + 3)) fib_subproof.
Check fib_subproof.

R_compute (fib 7) fib_7_eqn.

Recursive (def monster such that
  monster 0 = 1 /\
  forall n, Rnat (n - 1) -> monster n = fib (Rabs (monster (n - 1) + n))).

Elpi mirror_recursive_definition monster.

R_compute (monster 2) m2_eqn.

Lemma monster2 : monster 2 = 2.
Proof.
exact m2_eqn.
Qed.

(* An example of making the proofs step by step with the specifications. *)
Lemma monster3 : monster 3 = 5.
Proof.
elpi r_compute (monster 3).
reflexivity.
Qed.

(* monster grows very fast after that.  monster 4 = 34,
  monster 5 = 63245986 *)
R_compute (monster 5) m5_eqn.

R_compute (fib (Rabs (fib (Rabs 9) + 2))) ff9_eqn.

(* A proof that Rnat is stable for fib, using only tactics that can be
  shown to students.  There is a clever trick here, which is the technique
  of proving the required property for every pair of successive natural
  numbers.  Maybe a proof based on course of value induction would be more
  suitable. *)
Lemma student_fib_nat n : Rnat n -> Rnat (fib n).
Proof.
destruct fib_eqn as [fib0 [fib1 fib_suc]].
intros nnat.
enough (main : Rnat (fib n) /\ Rnat (fib (n + 1))).
  now destruct main.
induction nnat as [ | p pnat [Ih1 Ih2]].
  rewrite fib0.
  replace (0 + 1) with 1 by ring.
  rewrite fib1.
  split; typeclasses eauto.
split.
  assumption.
rewrite fib_suc.
  ring_simplify (p + 1 + 1 - 2).
  ring_simplify (p + 1 + 1 - 1).
  typeclasses eauto.
ring_simplify (p + 1 + 1 - 2).
assumption.
Qed.

Lemma cov_fib_nat n : Rnat n -> Rnat (fib n).
Proof.
destruct fib_eqn as [fib0 [fib1 fib_suc]].
intros nnat.
induction nnat as [ n nnat Ih] using course_of_value_induction.
assert (nge0 : 0 <= n) by now apply Rnat_ge0.
destruct (Rle_lt_or_eq _ _ nge0) as [ngt0 | neq0].
  assert (nge1 : 1 <= n).
    assert (tmp := Rnat_le_lt _ _ ngt0).
    lra.
  destruct (Rle_lt_or_eq _ _ nge1) as [ngt1 | neq1].
    assert (nge2 : 2 <= n).
      assert (tmp := Rnat_le_lt _ _ ngt1).
      lra.
    assert (nm2nat: Rnat (n - 2)).
      apply Rnat_sub.
          assumption. (* proving Rnat n *)
        now solve_Rnat. (* proving Rnat 2 *)
      lra. (* proving 2 <= n*)
    rewrite fib_suc;[ | assumption].
    apply Rnat_add.
      apply Ih;[assumption | lra].
    apply Ih;[ | lra].
    replace (n - 1) with ((n - 2) + 1) by ring.
    now solve_Rnat.
  rewrite <- neq1.
  rewrite fib1.
  now solve_Rnat.
rewrite <- neq0.
rewrite fib0.
now solve_Rnat.
Qed.

(* This is the automated proof. *)
Lemma fib_nat n : Rnat n -> Rnat (fib n).
Proof.
rec_Rnat fib.
Qed.

Existing Instance fib_nat.

Lemma monster_nat n : Rnat n -> Rnat (monster n).
Proof.
rec_Rnat monster.
Qed.

Existing Instance monster_nat.

(* this is one way to keep the result in a theorem, without using the
  fact that the computation has already been done.  However, this is
  not for the eyes of students, because it exposes type Z. *)
Derive f36 SuchThat (f36 = fib (fib 9 + 2)) As Ex_f_9.
Proof.
elpi r_compute (fib (fib 9 + 2)).
unfold f36.
reflexivity.
Qed.

(* Here is a different way to prove equalities, this time using
  only the recursive equation, and Ltac "Match goal" to repeat the common
  step.  Maybe the
  "match goal" construct is too hard, but instances can be
  written by hand.  Even with the automation, this does
  not scale well to f36, but it could be use to motivate *)

Lemma f9 : fib 9 = 34.
Proof.
destruct fib_eqn as [fib0 [fib1 fib_s]].
assert (fib2 : fib 2 = 1).
(* Here we would like to be able to say: compute using
  the ring laws the values of all subtractions that appear
  in the goals.  But ring_simplify does not have the right
  kind of input argument. *)
  match goal with |- fib ?v = _ =>
    rewrite fib_s; ring_simplify (v - 2) (v - 1);
    try typeclasses eauto; lra
  end.
assert (fib3 : fib 3 = 2);[ |
assert (fib4 : fib 4 = 3);[ |
assert (fib5 : fib 5 = 5);[ |
assert (fib6 : fib 6 = 8);[ |
assert (fib7 : fib 7 = 13);[ |
assert (fib8 : fib 8 = 21)]]]]].
all: match goal with |- fib ?v = _ =>
    rewrite fib_s; ring_simplify (v - 2) (v - 1);
    try typeclasses eauto; try lra
  end.
Qed.

(* This is another function that looks like fib, but adds the index argument
  in the sum. *)
Recursive (fun  test3 : R -> R => test3 0 = 0 /\ test3 1 = 1 /\
     forall n, Rnat (n - 2) ->
       test3 n = test3 (n - 2) + test3 (n - 1) + n).

Elpi mirror_recursive_definition test3.

R_compute (test3 10).

Recursive (def factorial such that factorial 0 = 1 /\
  forall n, Rnat (n - 1) -> factorial n = n * factorial (n - 1)).

Example rec_clause_factorial : forall n, Rnat (n - 1) ->
  factorial n = n * factorial (n - 1).
Proof.
(* prove_recursive_specification factorial 1%Z. *)
unfold factorial.
intros n nnat.
unfold Rnat_rec.
set (protect_base := IRN (n - 1)).
unfold protect_base.
rewrite (private.IRN_to_S_top n 1 refl_equal nnat).
simpl.
(* this works but the automatic tactic does not do that.
  rewrite (INR_IRN);[ring | assumption].
*)
enough (Last_eqn : INR (IRN (n- 1)) + 1 = n)
            by (rewrite Last_eqn; reflexivity).
rewrite INR_IRN;[ring | assumption].
Qed.

(* This is a proof that factorial maps natural numbers to natural numbers. *)
Lemma student_factorial_nat n : Rnat n -> Rnat (factorial n).
Proof.
destruct factorial_eqn as [factorial0 factorial_suc].
intros nnat; induction nnat as [ | p pnat Ih].
  rewrite factorial0.
  typeclasses eauto.
rewrite factorial_suc; ring_simplify (p + 1 - 1).
typeclasses eauto.
assumption.
Qed.

(* The proof can also be done automatically. *)
Lemma factorial_nat n : Rnat n -> Rnat (factorial n).
Proof.
rec_Rnat factorial.
Qed.

Existing Instance factorial_nat.

Elpi mirror_recursive_definition factorial.

R_compute (factorial 6).

(* This is a computation of factorial 6 by explicit uses of the recursive equation.
  lra is usable in the automatic step here because each multiplication instance is
  actually multiplciation by an integer constant. *)
Lemma fact_6 : factorial 6 = 720.
Proof.
destruct factorial_eqn as [factorial0 factorial_suc].
(* hand made proofs. *)
assert (factorial 1 = 1).
  rewrite factorial_suc; ring_simplify (1 - 1); solve_Rnat; try lra.
assert (factorial 2 = 2).
  rewrite factorial_suc; ring_simplify (2 - 1); solve_Rnat; try lra.
assert (factorial 3 = 6).
  rewrite factorial_suc; ring_simplify (3 - 1); solve_Rnat; try lra.
assert (factorial 4 = 24).
  rewrite factorial_suc; ring_simplify (4 - 1); solve_Rnat; try lra.
assert (factorial 5 = 120).
  rewrite factorial_suc; ring_simplify (5 - 1); solve_Rnat; try lra.
rewrite factorial_suc; ring_simplify (6 - 1); solve_Rnat; try lra.
(*  The following two lines take advantage of automation and goal pattern matching
  to perform all proofs steps in one go.
assert (factorial 1 = 1);[ | assert (factorial 2 = 2);[ | assert (factorial 3 = 6);
  [ | assert (factorial 4 = 24);[ | assert (factorial 5 = 120)]]]].
(* I am a bit nervous about showing this kind of code to users, but it saves *)
all : match goal with |- context [factorial ?v = _] =>
  rewrite factorial_suc; ring_simplify (v - 1); try typeclasses eauto; try lra
end.
*)
Qed.

(* We can now prove the value for the formula that was initially intended, *)
(* TODO: make the preliminary steps into tactic steps, withoug the need to *)
(* define theorems.                                                        *)
Derive huge_val SuchThat (huge_val = 42 + fib (factorial 5)) As huge_val_eq.
Proof.
elpi r_compute (42 + fib (factorial 5)).
unfold huge_val.
reflexivity.
Qed.

Definition k_among_n (k n : R) :=
  factorial n / ((factorial k) * factorial (n - k)).

Lemma fact0 : factorial 0 = 1.
Proof. destruct factorial_eqn as [f0 fs]; auto. Qed.

Lemma fact_suc : forall n, Rnat (n - 1) -> factorial n = n * factorial (n - 1).
Proof. destruct factorial_eqn as [f0 fs]; auto. Qed.

Lemma factorial_gt0 n : Rnat n -> 0 < factorial n.
Proof.
induction 1 as [ | n nnat Ih].
  rewrite fact0.
  lra.
rewrite fact_suc.
  apply Rmult_lt_0_compat.
    enough (0 <= n) by lra.
    apply Rnat_ge0.
    assumption.
  ring_simplify (n + 1 - 1).
  assumption.
ring_simplify (n + 1 - 1).
assumption.
Qed.

Lemma zero_among_n : forall n, Rnat n -> k_among_n 0 n = 1.
Proof.
intros n nnat.
destruct factorial_eqn as [fact0 fact_suc].
unfold k_among_n.
ring_simplify (n - 0).
rewrite fact0.
field.
enough (0 < factorial n) by lra.
apply factorial_gt0.
assumption.
Qed.

Lemma n_among_n : forall n, Rnat n -> k_among_n n n = 1.
Proof.
intros n nnat.
destruct factorial_eqn as [fact0 fact_suc].
unfold k_among_n.
ring_simplify (n - n).
rewrite fact0.
field.
enough (0 < factorial n) by lra.
apply factorial_gt0.
assumption.
Qed.

Lemma k_among_n_suc k n : Rnat k -> Rnat n -> k < n ->
   k_among_n (k + 1) (n + 1) = k_among_n k n + k_among_n (k + 1) n.
Proof.
intros knat nnat kint.
unfold k_among_n.
assert (nnat' : Rnat (n + 1 - 1)).
  ring_simplify (n + 1 - 1).
  assumption.
assert (knat' : Rnat (k + 1 - 1)).
  ring_simplify (k + 1 - 1).
  assumption.
rewrite (fact_suc (n + 1)); auto.
rewrite (fact_suc (k + 1)); auto.
ring_simplify (n + 1 - 1) (k + 1 - 1) (n + 1 - (k + 1)).
assert (nmknat: Rnat (n - (k + 1))).
  apply Rnat_sub; solve_Rnat.
  apply Rnat_le_lt; solve_Rnat.
  lra.
rewrite (fact_suc (n - k)).
  replace (n - k - 1) with (n - (k + 1)) by ring.
  field.
  split.
    enough (0 < factorial (n - (k + 1))) by lra.
    apply factorial_gt0.
    assumption.
  split.
    enough (0 < factorial k) by lra.
    apply factorial_gt0.
    assumption.
  assert (0 <= k).
    apply Rnat_ge0.
    assumption.
  lra.
replace (n - k - 1) with (n - (k + 1)) by ring.
assumption.
Qed.

Lemma k_among_n_nat k n : Rnat k -> Rnat n -> k <= n ->
  Rnat (k_among_n k n).
Proof.
intros knat nnat; revert k knat.
induction nnat as [ | n nnat Ih].
  intros k knat kle0.
  enough (it : k_among_n k 0 = 1) by (rewrite it; solve_Rnat).
  assert (0 <= k).
    apply Rnat_ge0 in knat.
    easy.
  replace k with 0 by lra.
  rewrite zero_among_n; solve_Rnat.
  easy.
intros k knat klenp1.
destruct (Req_dec k (n + 1)) as [ knp1 | knnp1].
  rewrite knp1, n_among_n.
    solve_Rnat.
  solve_Rnat.
destruct (Req_dec k 0) as [k0 |kn0].
  rewrite k0.
  now rewrite zero_among_n; solve_Rnat.
assert (kgt0 : 0 < k).
  enough (0 <= k) by lra.
  apply Rnat_ge0.
  assumption.
assert (1 <= k).
  replace 1 with (0 + 1) by ring.
  apply Rnat_le_lt; solve_Rnat.
  assumption.
assert (Rnat (k - 1)).
  apply Rnat_sub; solve_Rnat.
  assumption.
assert (k <= n).
  replace k with ((k - 1) + 1) by ring.
  apply Rnat_le_lt; solve_Rnat.
  lra.
replace k with ((k - 1) + 1) by ring.
rewrite k_among_n_suc; solve_Rnat.
  apply Rnat_add.
    apply Ih.
      assumption.
    lra.
  apply Ih.
    solve_Rnat.
  lra.
lra.
Qed.

(* experiments with big operators *)

Lemma sum_integers n : Rnat n ->
  \sum_(0 <= i < n) i = n * (n - 1) / 2.
Proof.
intros nnat.
induction nnat as [ | n nnat Ih].
  rewrite sum0.
  now field.
rewrite sum_recr.
    replace (n + 1 - 1) with n by ring.
    rewrite Ih.
    now field.
  replace (n + 1 - 0) with (n + 1) by ring.
  solve_Rnat.
assert (0 <= n) by now apply Rnat_ge0.
lra.
Qed.

Lemma sum_squares n : Rnat n ->
  \sum_(0 <= i < n) i ^ 2 = n * (n - 1) * (2 * n - 1) / 6.
Proof.
intros nnat.
induction nnat as [ | n nnat Ih].
  rewrite sum0.
  now field.
rewrite sum_recr.
    replace (n + 1 - 1) with n by ring.
    replace (n + 1 - 2) with (n - 1) by ring.
    rewrite Ih.
    now field.
  replace (n + 1 - 0) with (n + 1) by ring.
  solve_Rnat.
assert (0 <= n) by now apply Rnat_ge0.
lra.
Qed.

Lemma factorial_as_product n:
   Rnat n -> factorial n = \prod_(1 <= i < n + 1) i.
Proof.
intros nnat.
induction nnat as [ | n nnat Ih].
  rewrite fact0.
  replace (0 + 1) with 1 by ring.
  rewrite big0.
  easy.
rewrite fact_suc.
  all:replace (n + 1 - 1) with n by ring.
  rewrite prod_recr.
  all:replace (n + 1 + 1 - 1) with (n + 1) by ring; solve_Rnat.
  rewrite Ih.
  ring.
assert (0 <= n) by now apply Rnat_ge0.
lra.
Qed.

Lemma truncated_factorial n k: Rnat n -> Rnat k ->
  \prod_((n + 1) <= i < n + k + 1) i =
    factorial (n + k) / factorial n.
Proof.
intros nnat knat.
induction knat as [ | k knat Ih].
  replace (n + 0) with n by ring.
  rewrite big0.
  field.
  assert (0 < factorial n) by now apply factorial_gt0.
  lra.
rewrite (fact_suc (n + (k + 1))).
  replace (n + (k + 1) - 1) with (n + k) by ring.
  rewrite prod_recr.
    replace (n + (k + 1) + 1 - 1) with (n + k + 1) by ring.
    rewrite Ih.
    field.
    assert (0 < factorial n) by now apply factorial_gt0.
    lra.
  ring_simplify (n + (k + 1) + 1 - (n + 1)).
  solve_Rnat.
  assert (0 <= k) by now apply Rnat_ge0.
  lra.
replace (n + (k + 1) - 1) with (n + k) by ring.
solve_Rnat.
Qed.

Definition choose n k :=
  \prod_((n - k + 1) <= i < n + 1) i /
  factorial k.

Lemma choose_def1 n k : Rnat n -> Rnat k -> k <= n ->
  choose n k = factorial n / (factorial (n - k) * factorial k).
Proof.
intros nnat knat klen.
unfold choose.
replace (n + 1) with ((n - k) + k + 1) by ring.
assert (nmknat : Rnat (n - k)).
  now apply Rnat_sub; solve_Rnat.
rewrite truncated_factorial.
    replace (n - k + k) with n by ring.
    field.
    split.
      assert (0 < factorial k) by now apply factorial_gt0.
      lra.
    enough (0 < factorial (n - k)) by lra.
    apply factorial_gt0.
all: easy.
Qed.

Lemma choose_n_0 n : Rnat n -> choose n 0 = 1.
Proof.
intros nnat.
unfold choose.
ring_simplify (n - 0 + 1).
rewrite big0.
rewrite fact0.
field.
Qed.

Lemma choose_n_n n: Rnat n -> choose n n = 1.
Proof.
intros nnat.
rewrite choose_def1; solve_Rnat; try lra.
replace (n - n) with 0 by ring.
rewrite fact0.
field.
assert (0 < factorial n) by now apply (factorial_gt0).
lra.
Qed.

Lemma choose_suc k n : Rnat k -> Rnat n -> k < n ->
   choose (n + 1) (k + 1) = choose n k + choose n (k + 1).
Proof.
intros knat nnat kint.
assert (0 <= k) by now apply Rnat_ge0.
assert (k + 1 <= n) by now apply Rnat_le_lt.
rewrite !choose_def1; solve_Rnat; try lra.
assert (nnat' : Rnat (n + 1 - 1)).
  ring_simplify (n + 1 - 1).
  assumption.
assert (knat' : Rnat (k + 1 - 1)).
  ring_simplify (k + 1 - 1).
  assumption.
rewrite (fact_suc (n + 1)); auto.
rewrite (fact_suc (k + 1)); auto.
ring_simplify (n + 1 - 1) (k + 1 - 1) (n + 1 - (k + 1)).
assert (nmknat: Rnat (n - (k + 1))).
  apply Rnat_sub; solve_Rnat.
  apply Rnat_le_lt; solve_Rnat.
  lra.
rewrite (fact_suc (n - k)).
  replace (n - k - 1) with (n - (k + 1)) by ring.
  field.
  split.
    enough (0 < factorial k) by lra.
    apply factorial_gt0.
    assumption.
  split.
    lra.
  split.
    enough (0 < factorial (n - (k + 1))) by lra.
    apply factorial_gt0.
    assumption.
  lra.
replace (n - k - 1) with (n - (k + 1)) by ring.
assumption.
Qed.

Lemma choose_nat k n : Rnat k -> Rnat n -> k <= n ->
  Rnat (choose n k).
Proof.
intros knat nnat; revert k knat.
induction nnat as [ | n nnat Ih].
  intros k knat kle0.
  enough (it : choose 0 k = 1) by (rewrite it; solve_Rnat).
  assert (0 <= k).
    apply Rnat_ge0 in knat.
    easy.
  replace k with 0 by lra.
  rewrite choose_n_0; solve_Rnat.
  easy.
intros k knat klenp1.
destruct (Req_dec k (n + 1)) as [ knp1 | knnp1].
  rewrite knp1, choose_n_n.
    solve_Rnat.
  solve_Rnat.
destruct (Req_dec k 0) as [k0 |kn0].
  rewrite k0.
  now rewrite choose_n_0; solve_Rnat.
assert (kgt0 : 0 < k).
  enough (0 <= k) by lra.
  apply Rnat_ge0.
  assumption.
assert (1 <= k).
  replace 1 with (0 + 1) by ring.
  apply Rnat_le_lt; solve_Rnat.
  assumption.
assert (Rnat (k - 1)).
  apply Rnat_sub; solve_Rnat.
  assumption.
assert (k <= n).
  replace k with ((k - 1) + 1) by ring.
  apply Rnat_le_lt; solve_Rnat.
  lra.
replace k with ((k - 1) + 1) by ring.
rewrite choose_suc; solve_Rnat.
  apply Rnat_add.
    apply Ih.
      assumption.
    lra.
  apply Ih.
    solve_Rnat.
  lra.
lra.
Qed.

(* This lemma is made approximately in a way that could be shown to students. *)
(* Even for an expert, it is an exercise that requires more than an hour. *)
Lemma binomial_poly (x y n : R) : Rnat n -> (x + y) ^ n =
  \sum_(0 <= i < n + 1)
       (choose n i * x ^ i * y ^ (n - i)).
Proof.
(* TODO: figure out why the notations for sums and products are not used.  *)
induction 1 as [ | n nnat Ih].
  rewrite Rpow0.
  rewrite sum1.
  rewrite choose_n_n; solve_Rnat.
  (* TODO: figure out a way to use ring only once. *)
  replace (0 - 0) with 0 by ring.
  ring.
replace ((x + y) ^ (n + 1)) with (x * (x + y) ^ n + y * (x + y) ^ n); cycle 1.
  (* TODO: this should be a ring no-brainer. *)
  rewrite Rpow_succ; solve_Rnat; ring.
rewrite Ih.
rewrite !big_distr;[ |  rewrite Rminus_0_r | rewrite Rminus_0_r]; solve_Rnat.
(* TODO: understand why this set command changes the name of bound variables when i
  is not written explicitely, making names inappropriate. *)
set (w1 := \sum_(_ <= i < _) _).
set (w2 := \sum_(_ <= i < _) _).
set (w3 := \sum_(_ <= i < _) _).
set (w4 := \sum_(1 <= i < n + 1) (choose n i * x ^ i * y ^ (n + 1 - i))).
assert (eq2 : w2 = choose (n + 1) 0 * x ^ 0 * y ^ (n + 1) + w4).
  unfold w2.
  rewrite big_recl; cycle 1.  (* This step avoids having to mention choose n (-1) *)
      now replace (n + 1 - 0) with (n + 1) by ring; solve_Rnat.
  (* TODO: encapsulate lra in a preparing tactic that exploits all possible
     uses of Rnat_ge0. *)
    apply Rnat_ge0 in nnat; lra.
(* Now the bound variable has its name from theorem big_recl *)
  apply f_equal2.
    rewrite !choose_n_0, Rpow_add; solve_Rnat.
    replace (n - 0) with n by ring.
    ring.
  replace (0 + 1) with 1 by ring.
  (* Here we need to use an extensionality step, because we can't rewrite inside
    the big sum. *)
  apply big_ext_low_nat; solve_Rnat.
    replace (n + 1 - 1) with n by ring.
    solve_Rnat.
  intros i inat iint.
  replace (n + 1 - i) with ((n - i) + 1) by ring.
  rewrite Rpow_add; solve_Rnat.
    ring.
  apply Rnat_sub; solve_Rnat.
  enough (i + 1 <= n + 1) by lra.
  apply Rnat_le_lt; solve_Rnat.
  tauto.
set (w5 := \sum_(0 <= i < n) (choose n i * x ^ (i + 1) * y ^ (n - i))).
assert (eq1 : w1 = choose (n + 1) (n + 1) * x ^ (n + 1) * y ^ 0 + w5).
  unfold w1.
  rewrite big_recr; auto; cycle 1.
      replace (n + 1 - 0) with (n + 1) by ring.
      solve_Rnat.
    apply Rnat_ge0 in nnat; lra.
    replace (n + 1 - 1) with n by ring.
    replace (n - n) with 0 by ring.
  rewrite Rplus_comm.
  apply f_equal2.
    rewrite !choose_n_n; solve_Rnat.
    rewrite Rpow_add; solve_Rnat; ring.
  unfold w5.
  (* Here again, we need to rewrite inside the sum using a extensionality step. *)
  apply big_ext_low_nat; solve_Rnat.
    replace (n - 0) with n by ring.
    solve_Rnat.
  intros i inat iint.
  rewrite Rpow_add; solve_Rnat.
  ring.
rewrite eq1, eq2.
unfold w3.
rewrite big_recr; auto; cycle 1.
    replace (n + 1 + 1 - 0) with (n + 1 + 1) by ring.
    solve_Rnat.
  apply Rnat_ge0 in nnat; lra.
replace (n + 1 + 1 - 1) with (n + 1) by ring.
replace ((n + 1) - (n + 1)) with 0 by ring.
(* This should be a strike-proof-step---upto apply f_equal *)
rewrite (Rplus_comm _ (choose (n + 1) _ * _ * _)), !Rplus_assoc.
apply f_equal.
rewrite big_recl; replace (n + 1 - 0) with (n + 1) by ring;
  solve_Rnat; cycle 1.
  apply Rnat_ge0 in nnat; lra.
(* This should be a strike-proof-step---upto appl f_equal; clear w6 *)
set (w6 := choose (n + 1) 0 * _ * _).
rewrite <- Rplus_assoc, <- (Rplus_comm w6), Rplus_assoc.
apply f_equal; clear w6.
rewrite <- big_shift; cycle 1.
  replace (n - 0) with n by ring; solve_Rnat.
(* This should be a few rewrites under the sum, but there is the question
  of exploiting the fact that i in the 0.. (n-1) range. *)
set (w7 := Rbigop _ _ _ _ _).
assert (eq3 : w7 =
         \sum_(0 <= i < n)
           (choose n i * x ^ (i + 1) * y ^(n - i) +
           choose n (i + 1) * x ^ (i + 1) * y ^ ((n + 1) - (i + 1)))).
  apply big_ext_low_nat; solve_Rnat.
    replace (n - 0) with n by ring; solve_Rnat.
  intros i inat iint.
  replace (n + 1 - (i + 1)) with (n - i) by ring.
  rewrite choose_suc; solve_Rnat; cycle 1.
    lra.
  ring.
rewrite eq3, <- big_add; cycle 1.
  replace (n - 0) with n by ring; solve_Rnat.
apply f_equal.
rewrite big_shift with
  (f := fun j => choose n j * x ^ j * y ^ (n + 1 - j)); cycle 1.
    replace (n - 0) with n by ring; solve_Rnat.
replace (0 + 1) with 1 by ring.
easy.
Qed.

(* Todo : understand why Elpi r_compute (89 - 5) does not work in some places. *)
Lemma exercise_4_5_17 : exists n, choose n 5 = 17 * choose n 4.
Proof.
eexists ?[ex_n].
remember ?ex_n as n eqn:Heqn.
rewrite !choose_def1; solve_Rnat;[ | shelve | shelve | shelve | shelve].
replace (17 * (factorial n / (factorial (n - 4) * (factorial 4)))) with
  (factorial n / ((factorial (n - 5) * factorial 4)) * (17 / ( n - 4))).
replace (factorial n / ((factorial (n - 5) * factorial 5))) with
  (factorial n / ((factorial (n - 5) * factorial 4)) * (1/5)).
apply f_equal.
apply (Rmult_eq_reg_r (5 * (n - 4))).
field_simplify.
apply (Rplus_eq_reg_r 4).
ring_simplify.
rewrite Heqn.
reflexivity.
1,2: shelve.
rewrite (fact_suc 5); ring_simplify (5 - 1); solve_Rnat.
field.
shelve.
rewrite (fact_suc (n - 4)); ring_simplify (n - 4 -1).
field.
Unshelve.
all: ring_simplify [Heqn] (n - 5); rewrite ?Heqn.
all: assert (0 < factorial 4 /\ 0 < factorial 84) by
  (split; apply factorial_gt0; solve_Rnat).
all: solve_Rnat.
all: lra.
Qed.

(* An example of a function where the order of recursion is
  lower than the number of base cases.  *)
Recursive (def one_then_0 such that
   one_then_0 0 = 1 /\
   one_then_0 1 = 0 /\
   forall n, Rnat (n - 2) -> one_then_0 n = one_then_0 (n - 1)).
