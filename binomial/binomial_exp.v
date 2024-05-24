Require Import Reals ClassicalEpsilon Lia Lra.

Open Scope R_scope.

(* The set of integers in the type of real numbers *)
(* ============ *)
(* Definitions.  The beginner users may not need to see that, but
  a full documentation of the provided concepts might be better. *)

(* For the experiment, we only give an inductive definition of the
  subset of R that contains the integers.  This only has two constructors,
  but this may be the result of hubris. *)
Inductive Rint : R -> Prop :=
  Rint1 : Rint 1
| Rint_sub : forall x y, Rint x -> Rint y -> Rint (x - y).

Hint Resolve Rint1 Rint_sub : rnat.

(* We then need to have all the stability statements for the ring
  operations (we already have subtraction. *)
Lemma Rint0 : Rint 0.
Proof. now replace 0 with (1 - 1) by ring; auto with rnat. Qed.

Hint Resolve Rint0 : rnat.

Lemma Rint_add x y : Rint x -> Rint y -> Rint (x + y).
Proof. now replace (x + y) with (x - (0 - y)) by ring; auto with rnat. Qed.

Lemma Rint_mul x y : Rint x -> Rint y -> Rint (x * y).
Proof.
induction 1 as [ | u v Ru Ihu Rv Ihv].
  now replace (1 * y) with y by ring; auto.
replace ((u - v) * y) with ((u * y) - (v * y)) by ring.
now auto with rnat.
Qed.

Hint Resolve Rint_add Rint_mul : rnat.

Lemma Rint_opp x : Rint x -> Rint (- x).
Proof. intros xint; replace (-x) with (0 - x) by ring; auto with rnat. Qed.

(* 2 will later be covered by a more general theorem, but we need a
  special lemma to prove that general theorem. *)
Lemma Rint2 : Rint 2.
Proof.  now replace 2 with (1 + 1); auto with rnat. Qed.

Hint Resolve Rint2 : rnat.

Lemma Rint_pos p : Rint (IZR (Z.pos p)).
Proof.
induction p as [ p' Ih | p' Ih | ].
    now rewrite Pos2Z.inj_xI, plus_IZR, mult_IZR; auto with rnat.
  now rewrite Pos2Z.inj_xO, mult_IZR; auto with rnat.
auto with rnat.
Qed.

Hint Resolve Rint_pos : rnat.

Lemma Rint_neg p : Rint (IZR (Z.neg p)).
Proof.
replace (IZR (Z.neg p)) with (IZR (Z.opp (Z.pos p))) by easy.
rewrite opp_IZR.
replace (- IZR (Z.pos p)) with (0 - IZR (Z.pos p)) by ring.
auto with rnat.
Qed.

Hint Resolve Rint_neg : rnat.

(* This is the general theorem that covers all numbers, even 0, 1, and 2
  which are already provided by more elementary proofs.
  The full general form of this theorem should not really be put in
  front of the eyes of beginners, but its specialization to ground
  constants like 1, 32, or 45 is useful (see the example below). *)

Lemma Rint_Z x : Rint (IZR x).
Proof.
now destruct x as [ | p | p]; auto with rnat.
Qed.

Hint Resolve Rint_Z : rnat.

Example Rint_big : Rint 1043.
Proof. now auto with rnat. Qed.

(* This lemma is not for the beginners, because it mentions the type
  Z explicitely. *)
Lemma Rint_exists_Z x : Rint x -> exists z, x = IZR z.
Proof.
induction 1 as [ | u v Ru Ihu Rv Ihv].
  exists 1%Z; easy.
destruct Ihu as [nu nuq]; destruct Ihv as [nv nvq].
exists (nu - nv)%Z; rewrite nuq, nvq.
now rewrite minus_IZR.
Qed.

(* order properties. *)
(* ============ *)
(* The order on integers is the same as the order on real numbers.
  However, there is a subtlety due to the discrete nature of the set of
  integers.  This is a transposition of an existing theorem on integers,
  actually covered by lia. *)
Lemma Rint_le_lt x y : Rint x -> Rint y -> x < y -> x + 1 <= y.
Proof.
intros xint yint.
destruct (Rint_exists_Z _ xint) as [z xz].
destruct (Rint_exists_Z _ yint) as [u yu].
rewrite xz, yu.
intros zu; apply lt_IZR in zu.
rewrite <- plus_IZR; apply IZR_le; lia.
Qed.

(* This ends the basic stability properties of Rint.  Proving that Rint
  is satisfied is a bit like type-checking.  In the current form, it
  is only provided for the basic ring operations.  *)

(* Mapping real numbers to Z, when they satisfy Rint. *)
(* ============ *)
(* This part is only useful to the developer of theories, when they want
  to re-use existing developments about integers. *)

(* Given a real number that is integer, we want to be able to talk about
  its value as an integer (beginner users are not supposed to know that
  the type Z exists. *)

(* Using classical logic (especially Hilbert's choice operator, we can
   now have a function from R to Z that returns the corresponding integer
   when it exists. *)
Definition IRZ x :=
  epsilon (inhabits 0%Z) (fun y => x = IZR y).

Lemma IRZ_IZR z : IRZ (IZR z) = z.
Proof.
unfold IRZ.
assert (exz : exists y, IZR z = IZR y).
  exists z; easy.
apply eq_sym, eq_IZR.
now apply epsilon_spec.
Qed.

(* Subsection: defining a factorial function on R. *)
(* ============ *)
(* We could use a direct definition by induction on positive, this could
   be useful for efficiency reason, but to make this experiment faster,
   we go all the way down to the naively defined factorial on natural
   numbers. *)
Definition Zfactorial x :=
  (if 0 <? x then Z.of_nat (fact (Z.to_nat x)) else 1)%Z.

(* The next two lemmas help recovering the "usual" recursive definition
  of factorial at the level of Z. *)
Lemma Zfactorial0 : Zfactorial 0 = 1%Z.
Proof. easy. Qed.

Lemma Zfactorial_succ x : (0 <= x)%Z -> 
  Zfactorial (x + 1) = (Zfactorial x * (x + 1))%Z.
Proof.
intros xge0.
unfold Zfactorial.
destruct (x =? 0)%Z eqn:x0.
assert (x0' : x = 0%Z) by lia.
rewrite x0'; easy.
assert (test1 : (0 <? x + 1)%Z = true) by lia.
rewrite test1.
replace (Z.to_nat (x + 1)) with (S (Z.to_nat x)) by lia.
rewrite fact_simpl.
assert (test2 : (0 <? x)%Z = true) by lia.
rewrite test2.
rewrite Nat2Z.inj_mul; lia.
Qed.

(* Thanks to the functions from R to Z and from Z to R, we can define
  a factorial function on real numbers. *)
Definition Rfactorial (x : R) :=
  IZR (Zfactorial (IRZ x)).

(* The Rfactorial function does not compute in the sense of type theory,
  but computation by proof is still quite feasible. *)
Lemma Rfactorial10 : Rfactorial 10 = 3628800.
Proof.
unfold Rfactorial.
(* This is the trick to leave the domain of numbers that do not compute
  (R) and enter the domain of numbers that compute (in the type theory
  sense) *)
rewrite IRZ_IZR.
(* easy would do it, but it goes through a natural number computation
  that takes a long time (more than 10 seconds) *)

(* Instead, we make the recursive scheme appear by writing successive
  additions, which are fortunately organized in the right shape, thanks
  to the default associativity of the addition notation. *)
replace 10%Z with (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)%Z by ring.
(* We do one step by hand, to show the conditions that are generated. *)
rewrite Zfactorial_succ.
(* the second goal is 0 <= 9, a condition needed to express that we
  actually dealing with a natural number. *)
2: lia.
repeat rewrite Zfactorial_succ; try lia.
(* In the end, this is just a product of 10 terms, each of them smaller
than 10. *)
easy.
Qed.

(* For the beginner user-experience, we only wish to provide the
  recursive behavior at the level of the R function. *)
Lemma Rfactorial0 : Rfactorial 0 = 1.
Proof.
unfold Rfactorial.
rewrite IRZ_IZR.
easy.
Qed.

Lemma Rfactorial_succ x : 0 <= x -> Rint x -> Rfactorial (x + 1) =
    Rfactorial x * (x + 1).
Proof.
intros xge0 xint.
destruct (Rint_exists_Z _ xint) as [z xz].
unfold Rfactorial.
rewrite xz.
rewrite <- plus_IZR, !IRZ_IZR, Zfactorial_succ, mult_IZR; auto.
now apply le_IZR; rewrite <- xz.
Qed.

Lemma Rfactorial_gt_0 n : Rint n -> 0 < Rfactorial n.
Proof.
intros nint.
destruct (Rint_exists_Z _ nint) as [z nz].
unfold Rfactorial; rewrite nz, IRZ_IZR.
unfold Zfactorial.
destruct (0 <? z)%Z eqn:z0; [ | lra].
apply IZR_lt.
replace 0%Z with (Z.of_nat 0) by easy.
apply inj_lt.
apply lt_O_fact.
Qed.

(* This is amazingly easy, maybe there should be a Rint precondition. *)
Lemma Rint_factorial n : Rint (Rfactorial n).
Proof. apply Rint_Z. Qed.

Hint Resolve Rint_factorial.
(* The binomial function. *)
(* ================== *)

(* There are several characteristic properties of the binomal function,
  we can use one of them to define the binomial function.  Notice that
  this definition is well-typed for any real number, even though we will
  need the factorial function to be well-behaved in several places to
  obtain a value we can reason about. *)
Definition binomial x y :=
  Rfactorial x / (Rfactorial y * Rfactorial (x - y)).

(* In a full presentation, one would need to show that the other approach
  to the binomial function, where it is defined recusively over any
  pair of number n and m, such that 0 <= m <= n, is also available.
  Here is one of the equalities. *)
Lemma binomial_rec n m : 0 <= n -> 0 <= m -> m < n ->
  Rint n -> Rint m -> 
  binomial (n + 1) (m + 1) = binomial n m + binomial n (m + 1).
Proof.
intros nge0 mge0 mlen nint mint.
unfold binomial.
rewrite Rfactorial_succ; auto.
replace (n + 1 - (m + 1)) with (n - m) by ring.
rewrite Rfactorial_succ; auto.
replace (n - m) with (n - (m + 1) + 1) by ring.
assert (mlen' : m + 1 <= n).
  apply Rint_le_lt; auto.
rewrite Rfactorial_succ; try lra; auto with rnat.
replace (n - (m + 1) + 1) with (n - m) by ring.
field.
assert (0 < Rfactorial (n - (m + 1))).
  apply Rfactorial_gt_0; auto with rnat.
assert (0 < Rfactorial m).
  apply Rfactorial_gt_0; auto with rnat.
lra.
Qed.

Lemma binomial_n_0 n : Rint n -> 0 <= n -> binomial n 0 = 1.
Proof.
intros nint nge0.
unfold binomial.
rewrite Rfactorial0, Rmult_1_l, Rminus_0_r.
rewrite Rdiv_diag; [easy | ].
apply not_eq_sym, Rlt_not_eq, Rfactorial_gt_0; auto with rnat.
Qed.

(* This is awkward, but given by the way binomial was defined.  It might
  be different if we chose the recursive definition instead. *)
Lemma binomial_complement n m : binomial n (n - m) = binomial n m.
Proof.
unfold binomial.
replace (n - (n - m)) with m by ring.
now rewrite Rmult_comm.
Qed.

Lemma binomial_n_n n : Rint n -> 0 <= n -> binomial n n = 1.
Proof.
intros nint nge0.
rewrite <- binomial_complement.
replace (n - n) with 0 by ring.
now rewrite binomial_n_0.
Qed.

(* This ends the section of tools that should be provided to students about
  binomial numbers. *)

(* Now we come to the exercise that triggered my curiosity. *)
Lemma exo : exists n, binomial n 5 = 17 * binomial n 4.
Proof.
(* One way to perform math is to prove the existence of a number by
  gathering constraints about this number.  Here we go, we assume
  the existance of the number. *)
eapply ex_intro with ?[ex_n].
remember ?ex_n as n.
unfold binomial.
rewrite Rdiv_def, Rinv_mult, (Rmult_comm (/ Rfactorial 5)), <- Rmult_assoc.
enough (Rint n).
enough (0 <= n - 5).

replace (Rfactorial n * / Rfactorial (n - 5)) with
  (n * (n - 1) * (n - 2) * (n - 3) * (n - 4)); cycle 1.
  apply eq_sym.
  replace n with ((n - 5) + 1 + 1 + 1 + 1 + 1) at 1 by ring.
  repeat (rewrite Rfactorial_succ; [ | lra | auto 10 with rnat]).
  field.
  apply not_eq_sym, Rlt_not_eq, Rfactorial_gt_0; auto with rnat.
replace (Rfactorial n / (Rfactorial 4 * Rfactorial (n - 4))) with
   (n * (n - 1) * (n - 2) * (n - 3) / Rfactorial 4); cycle 1.
  apply eq_sym.
  replace n with ((n - 4) + 1 + 1 + 1 + 1) at 1 by ring.
  repeat (rewrite Rfactorial_succ; [ | lra | auto 10 with rnat]).
  field.
  split; apply not_eq_sym, Rlt_not_eq, Rfactorial_gt_0; auto with rnat.
  replace (17 * (n * (n - 1) * (n - 2) * (n - 3) / Rfactorial 4))
    with ((n * (n - 1) * (n - 2) * (n - 3)) *
        (17 * (/Rfactorial 4)))
    by (rewrite Rdiv_def; ring).
  replace (n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * / Rfactorial 5) with
   ((n * (n - 1) * (n - 2) * (n - 3)) * ((n - 4) * / Rfactorial 5)) by ring.
  apply Rmult_eq_compat_l.
  replace 5 with (4 + 1) by ring.
  rewrite Rfactorial_succ;[ | lra | auto with rnat].
  rewrite Rinv_mult, (Rmult_comm (/ Rfactorial _)), <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  replace (4 + 1) with 5 by ring.
  apply (Rmult_eq_reg_r 5);[ | lra].
  rewrite Rmult_assoc, Rinv_l;[ | lra].
  rewrite Rmult_1_r; apply (Rplus_eq_reg_r 4).
  replace (n - 4 + 4) with n by ring.
  rewrite Heqn.
  (* We give the value here, but just reflexivity would make it possible
     to solve the problem without ever writing the value in the script. *)
  enough (?ex_n = 17 * 5 + 4) by assumption; reflexivity.
(* The value for n is then propagated to the equation Heqn and we can
   proved the delayed obligations about the value. *)
rewrite Heqn; lra.
rewrite Heqn; auto with rnat.
Qed.
