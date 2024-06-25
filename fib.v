Require Import List Reals.
Open Scope R_scope.

(* Experimenting with Rnat as a subset of R, equiped with a recursive
  function definition that has a rewrite rule for its behavior.  *)

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall n, Rnat n -> Rnat (n + 1).

Parameter Rnat_rec :
  forall {A : Type} (v0 : A) (step : R -> A -> A), R -> A.

Parameter Rnat_rec0 : forall {A : Type} (v0 : A) (step : R -> A -> A),
  Rnat_rec v0 step 0 = v0.

Parameter Rnat_rec_succ : forall {A : Type} (v0 : A) (step : R -> A -> A)
  n, Rnat n ->
  Rnat_rec v0 step (n + 1) = step n (Rnat_rec v0 step n).

Definition fib' :=
  fun x =>
  nth 0 (Rnat_rec (0 :: 1 :: nil)
          (fun n v => (nth 1 v 0 :: nth 0 v 0 + nth 1 v 0 :: nil))
          x)
    0.

Lemma RnatZ x: Rnat (IZR (Z.pos x)).
Proof.
change (Z.pos x) with (Z.abs (Z.pos x)).
rewrite <-Zabs2Nat.id_abs.
induction (Z.abs_nat (Z.pos x)).
  exact Rnat0.
rewrite Nat2Z.inj_succ, succ_IZR.
now apply Rnat_succ, IHn.
Qed.

(* With Rnat_rec that is free of membership condition, it is comfortable
  to compute with the rewrite rules, with the minor nuisance of checking
  whether the membership condition holds only when triggering the rewrite
  rule. *)
Lemma test_fib3 : fib' 3 = 2.
Proof.
unfold fib'.
replace 3 with (0 + 1 + 1 + 1) by ring.
 do 3 (try (rewrite Rnat_rec_succ; simpl)).
 rewrite Rnat_rec0; simpl.
 ring.
 all: repeat apply Rnat_succ; apply Rnat0.
Qed.
