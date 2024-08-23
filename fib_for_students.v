Require Import Reals List Lra R_subsets rec_def R_compute rec_def_examples.
(* TODO: remove this line when the file contains only stuff for the student's
eyes*)
Require Import Lia.
Open Scope R_scope.

(* You can type numeric formulas.  The result is a real number. *)

Check (3 + 5).

(* The command "Check" helps you test if you can write a formula that the
  proof assistant will be able to understand.  When it understand a formula,
  this command returns information about the type of the object that you
  gave it. *)

Definition add5 (x : R) := x + 5.

(* when you use the Check command, you can give a function name to it.  The
  command returns different information than for a number.  Here the information
  explains that the object is a function, that it expects an argument of type R,
  and that it will return a value of type R. *)

Check add5.

(* Because the function expects a number argument, you can apply it to something
  that is a number.  For instance, we already know that (3 + 5) is a real number,
  so we can write the following formula, which is well formed. *)

Check add5 (3 + 5).

(* On the other hand, we cannot apply the function to itself, because the function
  is not a number.  Here I use the prefix command "Fail" to warn the system that
  I know this is an error, and it should not get to upset. *)

Fail Check add5 (add5).

(* Similarly, a number is not a function so, it cannot be applied to another number. 
  This kind of consistency checking of formulas is one of the first benefits of
  using a proof assistant to write mathematics. *)

Fail Check 3 (3).

(* A notation habit of this proof tool is that parentheses are not necessarily
  written around the argument of functions.  Here is an example.  the function
  add is applied to 3, and then the result is multiplied by 5. *)

Check add5 3 * 5.

(* If on the other hand one wishes to write the formula where the function is
  applied to the result of the multiplication, one needs to add the parentheses
  explicitly. *)

Check add5 (3 * 5).

(*  Computing. *)
(* To compute formulas, one need to start a proof, where one describes explicitly
   the results that one expect. *)

Example exercise1 : add5 (3 * 5) = 20.
Proof.
(* The proof tool is candid: it knows very little.  In particular, it does not
  know what the function add5 does, so we need to explicitly instruct it to
  unfold the definition. *)
unfold add5.
(* On the other hand, once we have a formula that contains only operations
  it already knows, it can berform the computation for us.  The command
  to perform the computation of a subformula in the goal is called 
  ring_simplify. *)
ring_simplify (3 * 5 + 5).
(* After this step, it is easy to recognize that we want to prove an
  quality between a number and itself.   We can ask the system to do it
  with the "easy" proof command. *)
easy.
Qed.

Recursive (def dd such that dd 0 = 0 /\ forall n, Rnat (n - 1) -> dd n = 2 + dd (n - 1)).

Check dd_eqn.

Lemma dd2 : dd 2 = 4.
Proof.
destruct dd_eqn as [dd0 dd_suc].
rewrite dd_suc; ring_simplify (2 - 1);[ |  typeclasses eauto].
rewrite dd_suc; ring_simplify (1 - 1);[ |  typeclasses eauto].
rewrite dd0.
ring.
Qed.

Elpi mirror_recursive_definition dd.

Lemma nat_rect_suc_list (l : list R) (lz : list Z)
  (fsz : nat -> list Z -> list Z)
  (fs : nat -> list R -> list R) k :
  l = map IZR lz ->
  (forall n l', fs n (map IZR l') = map IZR (fsz n l')) ->
  nat_rect (fun _ => list R) l fs k =
  map IZR (nat_rect (fun _ => list Z) lz fsz k).
Proof.
intros lq fsq.
induction k as [ | k Ih].
  assumption.
simpl.
rewrite Ih.
apply fsq.
Qed.

Check private.nat_rect_list_IZR.

Lemma dd_mirror_proof (z : R) : Rnat z -> dd z = IZR (dd_Z_mirror (IRZ z)).
Proof.
intros znat.
destruct (Rnat_exists_nat z) as [k zq].
rewrite zq.
unfold dd, Rnat_rec, IRN, dd_Z_mirror.
rewrite IRZ_IZR, Zabs2Nat.id.
rewrite (nat_rect_suc_list _ (0%Z :: nil) 
   (fun (_ : nat) (v : list Z) => (2 + nth 0 v 0)%Z :: nil)).
    now rewrite map_nth.
  reflexivity.
intros _ l; cbn [map].
apply (f_equal (fun x => (x :: nil))).
now rewrite plus_IZR, map_nth.
Qed.

Lemma fib_mirror_proof (z : R) : Rnat z -> fib z = IZR (fib_Z_mirror (IRZ z)).
Proof.
intros znat.
destruct (Rnat_exists_nat z) as [k zq].
rewrite zq.
unfold fib, Rnat_rec, IRN, fib_Z_mirror.
rewrite IRZ_IZR, Zabs2Nat.id.
rewrite (nat_rect_suc_list _ (0 :: 1 :: nil)%Z
  (fun (_ : nat) (v : list Z) => 
    nth 1 v 0%Z :: (nth 0 v 0 + nth 1 v 0)%Z :: nil)).
    now rewrite map_nth.
  (* This part is usually reflexivity, because we see the same contants
    on both side.  It would be different if there was a computed value
    in the base case. *)
  reflexivity.
intros _ l; cbn [map].
(* The first elements of the sequence can all be treated in this manner. *)
apply f_equal2; [now rewrite map_nth | ].
(* For the last one, the computation requires a specific proof.  the tail
  of the sequence is easy because it is nil. *)
apply f_equal2; [ | easy].
rewrite plus_IZR.
(* In this case, teh only values come from recursive calls. *)
rewrite !map_nth.
easy.
Qed.


Elpi R_compute (dd 212).

Elpi R_compute (fib (fib 9)).

Fail Elpi R_compute (fib (add5 3)).

(* TODO: improve R_compute so that mirror functions for simple definitions
  like add5 are also generated automatically. *)

Definition add5Z (x : Z) := (x + 5)%Z.

Elpi add_computation add5 add5Z.

Elpi R_compute (add5 3).

Elpi R_compute (fib (add5 3)).

Definition Rpow (x y : R) := pow x (IRN y).

Lemma Rpow0 x : Rpow x 0 = 1.
Proof.  unfold Rpow; rewrite IRN0, pow_O; easy. Qed.

Lemma Rpow1 x : Rpow x 1 = x.
Proof.  unfold Rpow; rewrite IRN1, pow_1; easy. Qed.

Lemma Rpow_add x a b : 
  Rnat a -> Rnat b -> Rpow x (a + b) = Rpow x a * Rpow x b.
Proof.
intros anat bnat.
unfold Rpow; rewrite IRN_add, pow_add; easy.
Qed.

Lemma Fibonacci_and_golden_number n:
  let phi := (sqrt 5 + 1) / 2 in
  let phi' := (1 - sqrt 5) / 2 in
    Rnat n -> 
    fib n = (Rpow phi n - Rpow phi' n)/ sqrt 5.
Proof.
destruct fib_eqn as [fib0 [fib1 fib_suc]].
intros phi phi'.
assert (sqrt5gt0 : 0 < sqrt 5).
  apply sqrt_lt_R0.
  lra.
assert (phi_gt0 : 0 < phi).
  unfold phi.
  lra.
 assert (phi_root :  Rpow phi 2 = phi + 1).
  replace 2 with (1 + 1) by ring.
  rewrite Rpow_add, Rpow1; try typeclasses eauto.
  unfold phi.
  replace ((sqrt 5 + 1) / 2 * ((sqrt 5 + 1) / 2)) with
    ((sqrt 5 * sqrt 5 + 2 * sqrt 5 + 1)  / 4) by field.
  rewrite sqrt_sqrt;[ | lra].
  field.
assert (phi'_root : Rpow phi' 2 = phi' + 1).
  replace 2 with (1 + 1) by ring.
    rewrite Rpow_add, Rpow1; try typeclasses eauto.
  unfold phi'.
  replace ((1 - sqrt 5) / 2 * ((1 - sqrt 5) / 2)) with
    ((sqrt 5 * sqrt 5 - 2 * sqrt 5 + 1)  / 4) by field.
  rewrite sqrt_sqrt; [ | lra].
  field.
intros nnat.
enough (fib n = (Rpow phi n - Rpow phi' n) / sqrt 5 /\
        fib> (n + 1) = (Rpow phi (n + 1) - Rpow phi' (n + 1)) / sqrt 5).
  now tauto.
induction nnat as [ | p pnat Ih].
  split.
    rewrite 2!Rpow0.
    replace ((1 - 1) / sqrt 5)with 0; cycle 1.
      field.
      lra.
    assumption.
  ring_simplify (0 + 1).
  rewrite fib1.
  rewrite 2!Rpow1.
  unfold phi, phi'.
  field.
  lra.
destruct Ih as [Ih1 Ih2].
split;[ assumption | ].
rewrite fib_suc; ring_simplify (p + 1 + 1 - 2); ring_simplify (p + 1 + 1 - 1);
  try typeclasses eauto.
replace (Rpow phi (p + 1 + 1)) with (Rpow phi (p + 1) + Rpow phi p); cycle 1.
   rewrite Rpow_add, Rpow1; try typeclasses eauto.
   ring_simplify (p + 1 + 1).
   rewrite Rpow_add, phi_root; try typeclasses eauto.
   ring.
replace (Rpow phi' (p + 1 + 1)) with (Rpow phi' (p + 1) + Rpow phi' p); cycle 1.
   rewrite Rpow_add, Rpow1; try typeclasses eauto.
   ring_simplify (p + 1 + 1).
   rewrite Rpow_add, phi'_root; try typeclasses eauto.
   ring.
rewrite Ih1, Ih2.
field.
lra.
Qed.


