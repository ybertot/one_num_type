Require Import List Reals Lra Lia.
Require Import R_subsets rec_def.

Open Scope R_scope.


Recursive (def simple_example such that simple_example 0 = 0 /\
   forall n, Rnat (n - 1) -> simple_example n = simple_example (n - 1) + 1).

Recursive (def fib such that fib 0 = 0 /\ fib 1 = 1 /\
    forall n : R, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)).

Definition fibz (n : nat) : Z :=
  nth 0 (nat_rect (fun _ => list Z) (0 :: 1 :: nil)%Z
    (fun k l => nth 1 l 0%Z :: (nth 0 l 0 + nth 1 l 0)%Z :: nil) n) 0%Z.

Lemma fibz_IZR n : Rnat n -> fib n = IZR (fibz (IRN n)).
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

Existing Instance fib_nat.

Derive f36 SuchThat (fib (fib 9 + 2) = f36) As Ex_f_9.
Proof.
repeat (rewrite <- plus_IZR || (rewrite fibz_IZR; try typeclasses eauto)).
rewrite IRN_pos.
match goal with |- context [fibz (Pos.to_nat ?x)] =>
  let v := eval compute in (fibz (Pos.to_nat x)) in change
    (fibz (Pos.to_nat x)) with v
end.
match goal with |- context [(?x + ?y)%Z] =>
  let v := eval compute in (x + y)%Z in change (x + y)%Z with v
end.
rewrite IRN_pos.
match goal with |- context [fibz (Pos.to_nat ?x)] =>
  let v := eval compute in (fibz (Pos.to_nat x)) in change
    (fibz (Pos.to_nat x)) with v
end.
unfold f36.
reflexivity.
Qed.

Recursive (def trib such that trib 0 = 0 /\ trib 1 = 1 /\ trib 2 = 2 /\
  forall n, Rnat (n - 3) -> trib n = trib (n - 3) + trib (n - 2)).

Recursive (fun  test3 : R -> R => test3 0 = 0 /\ test3 1 = 1 /\
     forall n, Rnat (n - 2) ->
       test3 n = test3 (n - 2) + test3 (n - 1) + n).

Recursive (def fact3 such that fact3 0 = 1 /\
  forall n, Rnat (n - 1) -> fact3 n = n * fact3 (n - 1)).

Lemma fact_6 : fact3 6 = 720.
Proof.
unfold fact3.
unfold Rnat_rec.
unfold IRN.
rewrite IRZ_IZR.
simpl.
ring.
Qed.

(* This example puts the user interface under stress, as it returns
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
