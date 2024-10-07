Require Import Reals.

Open Scope R_scope.

Example test0 : 3 + 2 = 5.
 Proof. ring_simplify (3 + 2). easy. Qed.

Example test0_1 (n : R) : n ^ 3 * n ^ 4 = n ^ 7.
Proof. ring_simplify. easy. Qed.

Example test0_2 (n : R) : n ^ (3 + 4) = n ^ 7.
Proof. 
Fail progress ring_simplify.
ring_simplify (3 + 4)%nat.
easy.
Qed.

(* This is a sub-part of the field declaration used for
  the real numbers.  It illustrates the need to declare
  morphisms using the morphisms modifier.   When
  no morphism are provided, all integer constants
  are expressed solely using the unit of the ring,
  addition, and multiplication, using a binary number
  structure.
  *)
Add Field RField2 : Rfield
 (completeness Zeq_bool_complete, constants [IZR_tac]).

(* Testing the simplification of ground expressions containing
  integers. This does not behave as before. *)
Example test1 : 2 + 3 = 5.
Proof.
ring_simplify (2 + 3).
(* The result is unsightly, but it has the right shape for a direct
syntactic equality with the expansion of IZR 5. *)
easy.
Qed.

(* As expected, ring_simplify does not produce anything.  Because
  the ring description used here has no knowldge of the power function. *)
Example test2 (n : R) : n ^ 3 = n * n * n.
Proof.
Fail progress ring_simplify.
simpl.
ring_simplify.
easy.
Qed.

(* The previous experiments highlights what happens when the
  IZR functio is expanded.  Unfortunately, if we want IZR to appear
  as part of the exponent argument in powers, it will be expanded.
  The following Module introduces a copy of the IZR function that
  will not be expanded, but is provably equal to the known IZR.  *)
Module Type MyIZR_type.

Parameter IZR : Z -> R.

Axiom eq : IZR = Rdefinitions.IZR.

End MyIZR_type.

Module MyIZR : MyIZR_type.

Definition IZR := Rdefinitions.IZR.

Lemma eq : IZR = Rdefinitions.IZR.
Proof. reflexivity. Qed.

End MyIZR.

(* The Ring tactic uses the type N to encode the exponents
  of powers, and if one uses a power function with a different
  type for the exponents, one must provide a function to translate
  the elements of type N to the used type.  In our case, we aim
  to use the function Rpow defined in R_subsets.v, where exponents
  are in type R.   We define a function mapping N to R. *)
Definition MyINR : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => IZR (Z.pos p)
  end.

Definition MyINR1 : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => MyIZR.IZR (Z.pos p)
  (* Alternatively: MyIZR.IZR instead of IZR*)
end.

(* For the experiments in this file, we do no load the file
  R_subset, but assume the existence of the relevant function,
  with two axioms describing the expected properties. *)
 Parameter Rpow : R -> R -> R.
 
Disable Notation "^" := pow.

#[local]
Set Warnings "-notation-overridden".

Notation "x ^ y" := (Rpow x y) : R_scope.

#[local]
Set Warnings "+notation-overridden".

 Axiom Rpow_convert0 : forall n, n ^ 0 = 1.

 Axiom Rpow_convertp : forall n p, n ^ (IZR (Z.pos p)) =
   pow n (Pos.to_nat p).

(* the following structure uses MyINR, where the IZR
   function is used, and we will see in experiments that
   the exponents produced by ring_simplify are uncomfortable. *)
Definition R_p_t : power_theory 1 Rmult (@eq R) MyINR Rpow.
constructor.
destruct n.
  simpl.
  now rewrite Rpow_convert0.
(* The option rewrite in the next line is to be robust to the
  fact that MyINR may call directly IZR or MyIZR.IZR instead. *)
unfold MyINR; rewrite ?MyIZR.eq.
simpl (RMicromega.INZ (N.pos p)).
rewrite Rpow_convertp.
change (Pos.to_nat p) with (N.to_nat (N.pos p)).
(* We use the fact that the correctness property is already proved
  in an existing structure. *)
now destruct R_power_theory as [ it]; apply it.
Qed.

(* The following structure use MyINR1, where the MyIZR function
  is used instead.  We will see that it makes the results of
  ring_simplify more readable, but still slightly uncomfortable. *)
Definition R_p_t1 : power_theory 1 Rmult (@eq R)
  MyINR1 Rpow.
constructor.
destruct n.
  simpl.
  now rewrite Rpow_convert0.
(* The option rewrite in the next line is to be robust to the
  fact that MyINR may call directly IZR or MyIZR.IZR instead. *)
unfold MyINR1; rewrite ?MyIZR.eq.
rewrite Rpow_convertp.
change (Pos.to_nat p) with (N.to_nat (N.pos p)).
(* We use the fact that the correctness property is already proved
  in an existing structure. *)
now destruct R_power_theory as [ it]; apply it.
Qed.

(* This Ltac function performs the inverse of MyINR,  mapping
  any real value that could have been the result of applying  MyINR
  to a constant of type N back to that constant. *)
Ltac Rpow_tac1 t :=
  match t with
  | IZR Z0 => N0
  | IZR (Z.pos ?p) =>
    match isPcst p with
    | true => constr:(N.pos p)
    | false => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

(* This field declaration is inspired from the sources of Coq in file
  theories/Reals/RIneq.v *)
Add Field RField3 : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac], 
    power_tac R_p_t [Rpow_tac1]).

(* Testing the simplification of ground expressions containing
  integers. We recover the correct handling of integers. *)
Example test2_1 : 3 + 2 = 5.
Proof. ring_simplify (3 + 2). easy. Qed.

(* As expected, the exponents produced in power expressins are not
  protected agains the computation of IZR, so that the formula we obtain
  in uncomfortable to read. *)
Example test2_2 (n : R) : n ^ 10 = n * n * n * n * n * n * n * n * n * n.
Proof.
(* ring succeeds in handling powers, but the exponent is unsightly,
  due to excessive simplification of the IZR function. *)
ring_simplify.
easy.
Qed.

Add Field RField4 : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac], 
    power_tac R_p_t1 [Rpow_tac1]).

(* Testing the simplification of ground expressions containing
  integers. We recover the correct handling of integers. *)
Example test3_1 : 3 + 2 = 5.
Proof. ring_simplify (3 + 2). easy. Qed.

(* As expected, ring_simplify does not produce *)
Example test3_2 (n : R) : n ^ 10 = n * n * n * n * n * n * n * n * n * n.
Proof.
(* ring succeeds in handling powers, but the exponent is relying on MyIZR,
  with blocked computation. This is readable, but final users will wonder what
  this MyIZR.MyIZR function is. *)
field_simplify.
rewrite MyIZR.eq.
easy.
Qed.

Lemma Rpow_IZR_to_myIZR x y : 
   x ^ (IZR y) = x ^ (MyIZR.IZR y).
Proof. now rewrite MyIZR.eq. Qed.

Ltac r_simplify_pre :=
  rewrite ?Rpow_IZR_to_myIZR.

Ltac r_simplify_post := 
  rewrite ?MyIZR.eq.

Add Field RField5 : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac], 
    power_tac R_p_t1 [Rpow_tac1], preprocess [r_simplify_pre],
    postprocess [r_simplify_post]).

Add Ring RRing5 : RTheory
  (morphism R_rm, constants [IZR_tac], power_tac R_p_t1 [Rpow_tac1],
  preprocess [r_simplify_pre], postprocess [r_simplify_post]).

(* Testing the simplification of ground expressions containing
  integers. We recover the correct handling of integers. *)
Example test4_1 : 3 - 2 + 4 = 5.
Proof. ring_simplify (3 - 2). ring_simplify (1 + 4). easy. Qed.

(* As expected, ring_simplify does not produce *)
Example test4_2 (n : R) : n ^ 10 = n * n * n * n * n * n * n * n * n * n.
Proof.
(* The results of ring_simplify are now comfortable for the final user,
  who does not need to see (and to know) that there is an IZR function
  (here used as hidden coercion) in the display of integer constants of
  type R. *)
ring_simplify.
easy.
Qed.

(* This example does not behave correctly if one does not include the
  preprocess modifier for the ring tactic. *)
Example test4_3 (n : R) : n ^ 2 - n - 1 + (1 + n) = n ^ 2 + 0.
Proof.
ring_simplify.
easy.
Qed.

Example test4_4 (n : R) : n <> 0 ->
  n ^ 2 * ( (- 1 / n) ^ 2 - (-1 / n) - 1) =
   - (n ^ 2 - n - 1).
Proof.
intros nn0.
Fail progress (field_simplify ((-1 / n) ^ 2 - (-1 / n) - 1);[ | auto]).