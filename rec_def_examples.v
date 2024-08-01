Require Import List Reals Lra Lia.
Require Import R_subsets rec_def R_compute.

Open Scope R_scope.

Definition Zsqr (x : Z) := (x * x)%Z.

(* This command should only be used and seen by library developers *)
Elpi add_computation Rsqr Zsqr.

Recursive (def simple_example such that simple_example 0 = 0 /\
   forall n, Rnat (n - 1) -> simple_example n = simple_example (n - 1) + 1).

Recursive (def fib such that fib 0 = 0 /\ fib 1 = 1 /\
    forall n : R, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)).

(* fibz is not for the eyes of the student.  The library developer can simply
  use this function to make computation possible with the R_compute command.  *)
Definition fibz (n : Z) : Z :=
  nth 0 (nat_rect (fun _ => list Z) (0 :: 1 :: nil)%Z
    (fun k l => nth 1 l 0%Z :: (nth 0 l 0 + nth 1 l 0)%Z :: nil) (Z.abs_nat n)) 0%Z.

(* This is the proof that fibz is correct.  *)
Lemma fibz_IZR n : Rnat n -> fib n = IZR (fibz (IRZ n)).
Proof.
intros nnat.
unfold fib, Rnat_rec, fibz.
set (fr := nat_rect (fun _ : nat => list R) _ _ _).
set (fz := nat_rect (fun _ : nat => list Z) _ _ _).
enough (pr : fr = map IZR fz).
  destruct fr as [ | r0 tr].
    destruct fz as [ | z0 tz]; try discriminate.
    easy.
  destruct fz as [ | z0 tz]; try discriminate.
  simpl in pr; injection pr as r0q _.
  easy.
unfold fr, fz.
apply (private.nat_rect_list_IZR (0 :: 1 :: nil)%Z).
intros k lR lZ lq; simpl.
destruct lR as [ | r0 [ | r1 tr]].
    destruct lZ as [ | z0 tz]; try discriminate.
    now simpl; rewrite <- plus_IZR.
  destruct lZ as [ | z0 [ | z1 tz]]; try discriminate.
  simpl.
  now injection lq as r0q; rewrite r0q, <- plus_IZR.
destruct lZ as [ | z0 [ | z1 tz]]; try discriminate.
simpl; injection lq as r0q r1q tq; rewrite r0q, r1q, <- plus_IZR.
easy.
Qed.

(* A proof that Rnat is stable for fib, using only tactics that can be
  shown to students.  There is a clever trick here, which is the technique
  of proving the required property the every pair of successive natural
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

(* An attempt to develop a proof that is more automatable.  *)
Lemma fib_nat n : Rnat n -> Rnat (fib n).
Proof.
intros nnat.
enough (main : Forall Rnat (Rnat_rec (0 :: 1 :: nil)
  (fun _ l => nth 1 l 0 :: nth 0 l 0 + nth 1 l 0 :: nil) n)).
  inversion main as [v0 | x ys xnat ysnat vs].
    unfold fib; rewrite <- v0; simpl; typeclasses eauto.
  now unfold fib; rewrite <- vs; simpl.
apply private.Rnat_rec_nat.
    repeat constructor; typeclasses eauto.
  intros k l _ lnat.
  assert (Rnat (nth 0 l 0) /\ Rnat (nth 1 l 0)) as [nat_at_0 nat_at_1].
    inversion lnat as [v0 | x l' nx nl lq].
      now simpl; repeat constructor.
    inversion nl as [v1 | y l2 ny nl2 l'q].
      now simpl; repeat constructor.
    now simpl; repeat constructor.
  repeat constructor.
    easy.
  typeclasses eauto.
easy.
Qed.

(* This command should only be seen by library developers. *)
Elpi add_computation fib fibz.

Elpi R_compute (fib (fib 9 + 2)).
(* Thanks to this command, we know that the result is 14930352 *)

(* this is one way to keep the result in a theorem, without using the
  fact that the computation has already been done.  However, this is
  not for the eyes of students, because it exposes type Z. *)
Derive f36 SuchThat (f36 = fib (fib 9 + 2)) As Ex_f_9.
Proof.
  (*  It is difficult to make this succession of computation
    steps automatic, because they should rather be done inside
    out. *)
rewrite (fibz_IZR 9); try typeclasses eauto.
rewrite IRZ_IZR.
rewrite <- plus_IZR.
match goal with |- context [IZR ?x] =>
  let v := eval compute in x in change x with v
end.
rewrite fibz_IZR; try typeclasses eauto.
rewrite IRZ_IZR.
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

Recursive (def trib such that trib 0 = 0 /\ trib 1 = 1 /\ trib 2 = 2 /\
  forall n, Rnat (n - 3) -> trib n = trib (n - 3) + trib (n - 2)).

Recursive (fun  test3 : R -> R => test3 0 = 0 /\ test3 1 = 1 /\
     forall n, Rnat (n - 2) ->
       test3 n = test3 (n - 2) + test3 (n - 1) + n).

Recursive (def factorial such that factorial 0 = 1 /\
  forall n, Rnat (n - 1) -> factorial n = n * factorial (n - 1)).

Lemma factorial_nat n : Rnat n -> Rnat (factorial n).
Proof.
destruct factorial_eqn as [factorial0 factorial_suc].
intros nnat; induction nnat as [ | p pnat Ih].
  rewrite factorial0.
  typeclasses eauto.
rewrite factorial_suc; ring_simplify (p + 1 - 1).
typeclasses eauto.
assumption.
Qed.

Existing Instance factorial_nat.


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

Definition factorialz (n : Z) :=
  nth 0 (nat_rect (fun _ => list Z) (1 :: nil)%Z
    (fun n l => ((1 + Z.of_nat n) * nth 0 l 0)%Z :: nil) (Z.abs_nat n)) 0%Z.

Lemma factorial_factorialz n : Rnat n ->
  factorial n = IZR (factorialz (IRZ n)).
Proof.
intros nnat.
unfold factorial, Rnat_rec, factorialz.
set (fr := nat_rect (fun _ => list R) _ _ _).
set (fz := nat_rect (fun _ => list Z) _ _ _).
enough (main : fr = map IZR fz).
  destruct fr as [ | r0 tl].
    destruct fz as [ | z0 tl]; try discriminate.
    easy.
  destruct fz as [ | z0 tlz]; try discriminate.
  now injection main as r0q _; rewrite r0q.
unfold fr, fz.
apply (private.nat_rect_list_IZR (1 :: nil)%Z).
intros k lR lZ lq.
destruct lR as [ | r0 tr].
  destruct lZ as [ | z0 tz]; try discriminate.
  cbn [map].
  rewrite mult_IZR.
  rewrite plus_IZR.
  rewrite INR_IZR_INZ.
  easy.
destruct lZ as [ | z0 tz]; try discriminate.
injection lq as r0q _; rewrite r0q.
cbn [nth map].
rewrite mult_IZR, plus_IZR.
rewrite INR_IZR_INZ.
easy.
Qed.

Elpi add_computation factorial factorialz.

Elpi R_compute (42 + fib (factorial 5)).

Derive fct15 SuchThat (fct15 = factorial 15) As fct15_eq.
Proof.
rewrite factorial_factorialz; try typeclasses eauto.
rewrite IRZ_IZR.
match goal with
 |- context[IZR ?v0] =>
   let v := eval compute in v0 in
     change v0 with v
end.
unfold fct15.
reflexivity.
Qed.

Derive huge_val SuchThat (huge_val = 42 + fib (factorial 5)) As uge_val_eq.
Proof.
rewrite fibz_IZR;[ | typeclasses eauto].
rewrite <- plus_IZR.
rewrite factorial_factorialz;[ | typeclasses eauto].
rewrite !IRZ_IZR.
match goal with |- context [IZR ?v] =>
  let y := eval vm_compute in v in change v with y
end.
unfold huge_val.
reflexivity.
Qed.


(* This example puts the user interface under stress (if one uses an input
  higher that 14), as it returns
  a tree of additions, where all the leaves are either 1 or (0 + 1).
  with the parentheses, this data should take at least 10 k chars. *)
Lemma fib11 : fib 11 = 89.
Proof.
unfold fib.
unfold Rnat_rec.
unfold IRN.
rewrite IRZ_IZR.
(* If the simpl command is placed alone in a command and its result
  should be improved, this breaks the outputting machinery of
  VsCoq2's current version.  Otherwise, just executing the combined
  simpl; ring command leads to a command that takes 3 seconds to
  execute. *)
simpl.
ring_simplify.
reflexivity.
Qed.
