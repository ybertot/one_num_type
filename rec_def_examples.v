Require Import List Reals Lra Lia.
Require Import R_subsets rec_def R_compute.
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