Require Import Reals.

(* Experimenting with Rnat as a subset of R, equiped with a recursive
  function definition that has a rewrite rule for its behavior.  *)

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall n, Rnat n -> Rnat (n + 1).

Parameter Rnat_rec :
  forall {A : Type} (v0 : A) (step : R -> A -> A) (n : R)
    (h : Rnat n), A.

Parameter Rnat_rec0 : forall {A : Type} (v0 : A) (step : R -> A -> A),
  Rnat_rec v0 step 0 Rnat0 = v0.

Parameter Rnat_rec_succ : forall {A : Type} (v0 : A) (step : R -> A -> A)
  n (h : Rnat n) (h' : Rnat (n + 1)),
  Rnat_rec v0 step (n + 1) h' = step n (Rnat_rec v0 step n h).

Definition fib' :=
  fun x (h : Rnat x) =>
  nth 0 (Rnat_rec (0 :: 1 :: nil)
          (fun n v => (nth 1 v 0 :: nth 0 v 0 + nth 1 v 0 :: nil))
          x h)
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

(* This proof is reminder that functions with domain definition conditions
  are a pain to use.  The rewrite rules are just not helping. *)
Lemma test_fib3 : fib' 3 (RnatZ 3) = 2.
Proof.
unfold fib'.
generalize (RnatZ 3); replace 3 with (0 + 1 + 1 + 1) by ring.
intros r.
assert (r' : Rnat (0 + 1 + 1)) by now repeat apply Rnat_succ; apply Rnat0.
rewrite Rnat_rec_succ with (h := r'); simpl.
assert (r'' : Rnat (0 + 1)) by now repeat apply Rnat_succ; apply Rnat0.
rewrite Rnat_rec_succ with (h := r''); simpl.
rewrite Rnat_rec_succ with (h := Rnat0); simpl.
rewrite Rnat_rec0; simpl.
ring.
Qed.
