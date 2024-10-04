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
  the real numbers.  Normally, it should only remove the
  handling of powers.  This field declaration is inspired from
  the last lines in the sources of Coq in file
  theories/setoid_ring/RealField.v
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

(* As expected, ring_simplify does not produce anything. *)
Example test2 (n : R) : n ^ 3 = n * n * n.
Proof.
Fail progress ring_simplify.
simpl.
ring_simplify.
easy.
Qed.

Module Type MyIZR_type.

Parameter MyIZR : Z -> R.

Axiom MyIZR_eq : MyIZR = IZR.

End MyIZR_type.

Module MyIZR : MyIZR_type.

Definition MyIZR := IZR.

Lemma MyIZR_eq : MyIZR = IZR.
Proof. reflexivity. Qed.

End MyIZR.

Definition MyINR : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => IZR (Z.pos p)
  (* Alternatively: MyIZR.MyIZR instead of IZR*)
end.

Definition MyINR1 : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => MyIZR.MyIZR (Z.pos p)
  (* Alternatively: MyIZR.MyIZR instead of IZR*)
end.

 Parameter Rpow : R -> R -> R.

 Axiom Rpow_convert0 : forall n, Rpow n 0 = 1.

 Axiom Rpow_convertp : forall n p, Rpow n (IZR (Z.pos p)) =
   pow n (Pos.to_nat p).

Definition R_p_t : power_theory 1 Rmult (@eq R)
  MyINR Rpow.
constructor.
destruct n.
  simpl.
  now rewrite Rpow_convert0.
(* The option rewrite in the next line is to be robust to the
  fact that MyINR may call directly IZR or MyIZR.MyIZR instead. *)
unfold MyINR; rewrite ?MyIZR.MyIZR_eq.
simpl (RMicromega.INZ (N.pos p)).
rewrite Rpow_convertp.
change (Pos.to_nat p) with (N.to_nat (N.pos p)).
now destruct R_power_theory as [ it]; apply it.
Qed.

Definition R_p_t1 : power_theory 1 Rmult (@eq R)
  MyINR1 Rpow.
constructor.
destruct n.
  simpl.
  now rewrite Rpow_convert0.
(* The option rewrite in the next line is to be robust to the
  fact that MyINR may call directly IZR or MyIZR.MyIZR instead. *)
unfold MyINR1; rewrite ?MyIZR.MyIZR_eq.
simpl (RMicromega.INZ (N.pos p)).
rewrite Rpow_convertp.
change (Pos.to_nat p) with (N.to_nat (N.pos p)).
now destruct R_power_theory as [ it]; apply it.
Qed.

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

(* As expected, ring_simplify does not produce *)
Example test2_2 (n : R) : Rpow n 10 = n * n * n * n * n * n * n * n * n * n.
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
Example test3_2 (n : R) : Rpow n 3 = n * n * n.
Proof.
(* ring succeeds in handling powers, but the exponent is relying on MyIZR,
  with blocked computation. *)
ring_simplify.
rewrite MyIZR.MyIZR_eq.
easy.
Qed.

Ltac r_simplify_post := rewrite 1?MyIZR.MyIZR_eq.

Add Field RField5 : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac], 
    power_tac R_p_t1 [Rpow_tac1], postprocess [r_simplify_post]).


(* Testing the simplification of ground expressions containing
  integers. We recover the correct handling of integers. *)
Example test4_1 : 3 + 2 = 5.
Proof. ring_simplify (3 + 2). easy. Qed.

(* As expected, ring_simplify does not produce *)
Example test4_2 (n : R) : Rpow n 10 = n * n * n * n * n * n * n * n * n * n.
Proof.
(* I expected the results of r_simplify to contain no occurrence
  of MyIZR.MyIZR, since they should have been rewritten.  This
  feels like a bug.  Unfortunately, there is no use of the
  postprocess directive in the Coq sources. *)
ring_simplify.
(* The next line should be unnecessary. *)
rewrite MyIZR.MyIZR_eq.
easy.
Qed.











