Require Import List Reals Lra Lia.
Require Import R_subsets rec_def R_compute.

Open Scope R_scope.

Definition Zsqr (x : Z) := (x * x)%Z.

(* This command should only be used and seen by library developers *)
Elpi add_computation Rsqr Zsqr.

Ltac rec_Rnat fun_name :=
(* This tactic is only meant to be used on statements of the form:
  Rnat x -> Rnat (fun_name x)
  where fun_name was defined using the Recursive command.  It succeeds
  if all operations that appear in the body of the definition are
  known to preserve membership in Rnat. *)
  let Nnat := fresh "nnat" in
  let M := fresh "m" in
  let L := fresh "l" in
  let Lnat := fresh "lnat" in
  let Mnat := fresh "mnat" in
  intros nnat;
  unfold fun_name;
  apply private.Rnat_rec_nat';[
    repeat ((intro; apply Rnat0)||(
             intros [ | k];[typeclasses eauto | revert k; cbn [nth]]
    )) |
    intros M L Lnat Mnat;
     repeat ((intro; apply Rnat0)||(
             intros [ | k];[typeclasses eauto | revert k; cbn [nth]]
    )) | assumption].

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

Recursive (def fib such that fib 0 = 0 /\ fib 1 = 1 /\
    forall n : R, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)).

Elpi mirror_recursive_definition fib.

Recursive (def monster such that monster 0 = 1 /\
  forall n, Rnat (n - 1) -> monster n = fib (Rabs (monster (n - 1) + n))).

Elpi mirror_recursive_definition monster.

Elpi R_compute (monster 2) m2_eqn.

Lemma monster2 : monster 2 = 2.
Proof.
exact m2_eqn.
Qed.

(* An example of making the proofs step by step with the specifications. *)
Lemma monster3 : monster 3 = 5.
Proof.
destruct monster_eqn as [monster0 monster_suc].
destruct fib_eqn as [fib0 [fib1 fib_suc]].
rewrite monster_suc; ring_simplify (3 - 1);[ | typeclasses eauto].
rewrite monster2.
rewrite Rabs_right;[ | lra].
rewrite fib_suc; ring_simplify (2 + 3 - 2);[ | typeclasses eauto].
ring_simplify (2 + 3 - 1).
rewrite (fib_suc 4); ring_simplify (4 - 2);[ | typeclasses eauto].
ring_simplify (4 - 1).
rewrite (fib_suc 3); ring_simplify (3 - 2);[ | typeclasses eauto].
ring_simplify (3 - 1).
rewrite (fib_suc 2); ring_simplify (2 - 2);[ | typeclasses eauto].
ring_simplify (2 - 1).
rewrite fib1, fib0.
ring.
Qed.

(* monster grows very fast after that.  monster 4 = 34,
  monster 5 = 63245986 *)
Elpi R_compute (monster 5) m5_eqn.

Elpi R_compute (fib (Rabs (fib (Rabs 9) + 2))) ff9_eqn.

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
apply (course_of_value_induction (fun n => Rnat (fib n)));[ | assumption].
clear n nnat.
intros n nnat Ih.
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
        typeclasses eauto. (* proving Rnat 2 *)
      lra. (* proving 2 <= n*)
    rewrite fib_suc;[ | assumption].
    apply Rnat_add.
      apply Ih;[assumption | lra].
    apply Ih;[ | lra].
    replace (n - 1) with ((n - 2) + 1) by ring.
    typeclasses eauto.
  rewrite <- neq1.
  rewrite fib1.
  typeclasses eauto.
rewrite <- neq0.
rewrite fib0.
typeclasses eauto.
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
  (*  It is difficult to make this succession of computation
    steps automatic, because they should rather be done inside
    out. *)

replace 9 with (Rabs 9);[ | rewrite Rabs_pos_eq; lra].
rewrite (fib_Z_prf 9 _ eq_refl).
rewrite <- plus_IZR.
match goal with |- context [IZR ?x] =>
  let v := eval compute in x in change x with v
end.
replace 36 with (Rabs 36);[ | rewrite Rabs_pos_eq; lra].
rewrite (fib_Z_prf _ _ eq_refl); try typeclasses eauto.
match goal with |- context [IZR ?x] =>
  let v := eval compute in x in change x with v
end.
unfold f36.
reflexivity.
Qed.

(* Here is a different way to prove equalities, this time using
  only commands that are available to the student.  Maybe the
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

Recursive (fun  test3 : R -> R => test3 0 = 0 /\ test3 1 = 1 /\
     forall n, Rnat (n - 2) ->
       test3 n = test3 (n - 2) + test3 (n - 1) + n).

Elpi mirror_recursive_definition test3.

Elpi R_compute (test3 (Rabs 10)).

Recursive (def factorial such that factorial 0 = 1 /\
  forall n, Rnat (n - 1) -> factorial n = n * factorial (n - 1)).

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

Lemma factorial_nat n : Rnat n -> Rnat (factorial n).
Proof.
rec_Rnat factorial.
Qed.

Existing Instance factorial_nat.

Elpi mirror_recursive_definition factorial.

Elpi R_compute (factorial 6).

(* lra is usable in the automatic step here because each multiplication instance is
  actually multiplciation by an integer constant. *)
Lemma fact_6 : factorial 6 = 720.
Proof.
destruct factorial_eqn as [factorial0 factorial_suc].
(* hand made proofs. *)
assert (factorial 1 = 1).
  rewrite factorial_suc; ring_simplify (1 - 1); try typeclasses eauto; try lra.
assert (factorial 2 = 2).
  rewrite factorial_suc; ring_simplify (2 - 1); try typeclasses eauto; try lra.
assert (factorial 3 = 6).
  rewrite factorial_suc; ring_simplify (3 - 1); try typeclasses eauto; try lra.
assert (factorial 4 = 24).
  rewrite factorial_suc; ring_simplify (4 - 1); try typeclasses eauto; try lra.
assert (factorial 5 = 120).
  rewrite factorial_suc; ring_simplify (5 - 1); try typeclasses eauto; try lra.
rewrite factorial_suc; ring_simplify (6 - 1); try typeclasses eauto; try lra.
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

Elpi R_compute (42 + fib (Rabs (factorial (Rabs 5)))).

Elpi R_compute (factorial 15) fact15_eqn.

(* The following two lines are preparatory lines for the next interactive  *)
(* proof.  We want to establish the value of 42 + fib (factorial 5) but    *)
(* the computation tool only accepts formulas where calls of recursive     *)
(* function on values that are guaranteed to be positive (using Rabs).     *)
(* So we call the computation tool on the patched formula, and we will     *)
(* to show that the absolute value instances are useless.                  *)
Elpi R_compute (42 + fib (Rabs (factorial 5))) huge_val_pre_eq.

(* This computation is for the subformula (in the absolute value)          *)
Elpi R_compute (factorial 5) huge_val_subproof.

(* We can now prove the value for the formula that was initially intended, *)
(* TODO: make the preliminary steps into tactic steps, withoug the need to *)
(* define theorems.                                                        *)
Derive huge_val SuchThat (huge_val = 42 + fib (factorial 5)) As huge_val_eq.
Proof.
generalize huge_val_pre_eq.
assert (0 <= factorial 5).
  rewrite huge_val_subproof.
  lra.
rewrite Rabs_pos_eq; auto.
intros ->.
unfold huge_val.
reflexivity.
Qed.

