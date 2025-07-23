From Stdlib Require Import Reals ZArith Lra.

Open Scope R_scope.

Ltac end_calculate :=
  repeat
   match goal with | id : _ = _ |- _ => (rewrite id || rewrite <- id); clear id end;
   (easy || ring || (field; (easy || lra))).

Ltac calc_LHS F  :=
  match goal with
  | |- ?L = _ =>
    let name := fresh "temp_for_calc_LHS" in
     assert (name: L = F);[ | apply (eq_trans name); clear name]
  end.

Ltac start_with F :=
  match goal with |- ?L = _ => change L with F end.

Ltac compute_sqrt :=
  match goal with
  | |- context[sqrt (IZR ?x)] =>
    let v := eval compute in (Z.sqrt x) in
    change (sqrt (IZR x)) with (sqrt (IZR (v * v)));
    rewrite mult_IZR, sqrt_square;[ | lra]
  end.

Section lemmas_that_should_exist.

Lemma square_pos x : x <> 0 -> 0 < x ^ 2.
Proof.
intros xn0.
assert (x < 0 \/ 0 < x) as [xneg | xpos] by lra.
  replace (x ^ 2) with ((- x) ^ 2) by ring.
  apply pow_lt; lra.
apply pow_lt; lra.
Qed.

(* We believe that in a mathematical class, we cannot assume sqrt to be defined
  for all real number, we should rather respect that the value is well defined
  only for positive real numbers. sqrt_pos should not be used in our context,
  but sqrt_pos' instead. *)
Lemma sqrt_pos' x : 0 <= x -> 0 <= sqrt x.
Proof. intros; apply sqrt_pos. Qed.

End lemmas_that_should_exist.

Module Type simple_trigo.

Parameter derivable : (R -> R) -> R -> Prop.

Parameter derive : (R -> R) -> R -> R.

Axiom MVT : forall f a b, a < b ->
  (forall x, a < x < b -> derivable f x) ->
  exists c, a < c < b /\ f b = f a + derive f c * (b - a).

Parameters cos sin : R -> R.

Axiom par_sin : forall x, sin (- x) = - (sin x).
Axiom par_cos : forall x, cos (- x) = cos x.

Axiom unit_circle : forall x, cos x ^ 2 + sin x ^ 2 = 1.

Axiom cos_add : forall x y, cos (x + y) = cos x * cos y - sin x * sin y.
Axiom sin_add : forall x y, sin (x + y) = cos x * sin y + cos y * sin x.

Axiom derivable_cos : forall x, derivable cos x.
Axiom derive_cos : forall x, derive cos x = -sin x.
Axiom derivable_sin : forall x, derivable sin x.
Axiom derive_sin : forall x, derive sin x = cos x.

Parameter Pi : R.

Axiom cos_Pi_half : cos (Pi / 2) = 0.

Axiom Pi_gt0 : 0 < Pi.

Axiom first_cos_root : forall x, 0 <= x < Pi / 2 -> 0 < cos x.

End simple_trigo.

Lemma trinom : forall a b c x, a <> 0 ->
  0 <= b ^ 2 - 4 * a * c ->
  a * x ^ 2 + b * x + c = 0 ->
    x = ((- b + sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) \/
    x = ((- b - sqrt (b ^ 2 - 4 * a * c)) / (2 * a)).
Proof.
enough (wlog : forall a b c x, 0 < a ->
  0 <= b ^ 2 - 4 * a * c ->
  a * x ^ 2 + b * x + c = 0 ->
  x = ((- b + sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) \/
  x = ((- b - sqrt (b ^ 2 - 4 * a * c)) / (2 * a))).
  intros a b c x an0 discr_ge_0 equa.
  assert (a < 0 \/ 0 < a) as [aneg | apos] by lra.
    assert (0 < - a) by lra.
    assert (fact: b ^ 2 - 4 * a * c = (- b) ^ 2 - 4 * (-a) * (- c)) by ring.
    assert (0 <= (-b) ^ 2 - 4 * (- a) * (- c)) by now rewrite <- fact.
    apply or_comm.
    replace (b ^ 2 - 4 * a * c) with ((- b) ^ 2 - 4 * (-a) * (- c)) by ring.
    replace ((- b - sqrt ((- b) ^ 2 - 4 * -a * - c)) / (2 * a)) with
      ((- (- b) + sqrt ((- b) ^ 2 - 4 * -a * - c)) / (2 * (- a))) by (field; easy).
    replace ((- b + sqrt ((- b) ^ 2 - 4 * -a * - c)) / (2 * a)) with
      ((- (- b) - sqrt ((- b) ^ 2 - 4 * -a * - c)) / (2 * (- a)))
      by (field; easy).
    apply wlog.
        easy.
      easy.
    lra.
  apply wlog; easy.
assert (solve_square :
  forall A B, 0 <= B -> A ^ 2 = B -> A = sqrt B \/ A = - sqrt B).
  intros A B Bpos Asq.
  assert (A < 0 \/ 0 <= A) as [Aneg | Apos] by lra.
    right.
    enough (- A = sqrt B) by lra.
    symmetry.
    assert (0 <= - A) by lra.
    assert (- A * - A = B).
      replace (- A * - A) with (A ^ 2) by ring.
      easy.
    apply sqrt_lem_1; easy.
  left.
  symmetry.
  assert (A * A = B).
    replace (A * A) with (A ^ 2) by ring.
    easy.
  apply sqrt_lem_1; try easy.
intros a b c x agt0 discr_pos equality.
assert (0 < 4 * a ^ 2).
  replace (4 * a ^ 2) with ((2 * a) ^ 2) by ring.
  apply pow_lt.
  lra.
assert ( a * x ^ 2 + b * x + c = a * ( x ^ 2 + b / a * x + c / a)).
  field.
  lra.
assert (x ^ 2 + b / a * x + c / a =
            (x + b / (2 * a)) ^ 2 + (c / a - b ^ 2 / (4 * a ^ 2))).
  field.
  lra.
assert (step : c / a - b ^ 2 / (4 * a ^ 2)= - ( b ^ 2 - 4 * a * c) / (4 * a ^ 2)).
  field.
  lra.
assert ((x + b / (2 * a)) ^ 2 =
        (b ^ 2 - 4 * a * c) / (4 * a ^ 2)).
  start_with ((x + b /  (2 * a)) ^ 2).
  calc_LHS ((x + b / (2 * a)) ^ 2 + (c / a - b ^ 2 / (4 * a ^ 2)) -
    (c / a - b ^ 2 / (4 * a ^ 2))).
    end_calculate.
    replace ((x + b / (2 * a)) ^ 2 + (c / a - b ^2 / (4 * a ^2))) with 0; cycle 1.
    symmetry.
    replace ((x + b / (2 * a)) ^ 2 + (c / a - b ^ 2 / (4 * a ^ 2))) with
      (1 / a * (a * ((x + b / (2 * a)) ^ 2 + (c / a - b ^ 2 / (4 * a ^ 2))))); cycle 1.
      field; lra.
    replace (a * ((x + b / (2 * a)) ^ 2 + (c / a - b ^ 2 / (4 * a ^ 2)))) with
      0; cycle 1.
      symmetry.
      end_calculate.
    ring.
  (* Hmmm.  There must be a problem with the order of established facts. *)
  rewrite step; field; lra.
assert (0 < / (4 * a ^ 2)).
  apply Rinv_0_lt_compat.
  easy.
assert (0 <= (b ^  2 - 4 * a * c) / (4 * a ^ 2)).
  apply Rmult_le_pos.
    easy.
  lra.
enough (x + b / (2 * a) = sqrt (b ^ 2 - 4 * a * c) / (2 * a) \/
        x + b / (2 * a) = - (sqrt (b ^ 2 - 4 * a * c) / (2 * a))) by lra.
replace (sqrt (b ^ 2 - 4 * a * c) / (2 * a)) with
    (sqrt ((b ^ 2 - 4 * a * c) / (4 * a ^ 2))); cycle 1.
  rewrite sqrt_div.
      replace (sqrt (4 * a ^ 2)) with (2 * a); cycle 1.
        symmetry; apply sqrt_lem_1.
            apply Rmult_le_pos.
              lra.
            enough (0 < a ^ 2) by lra.
            apply pow_lt.
            easy.
          lra.
        ring.
      easy.
    easy.
  easy.
apply solve_square.
  easy.
easy.
Qed.

Module trigo_facts (D : simple_trigo).

Import D.

Lemma cos_sub x y : cos (x - y) = cos x * cos y + sin x * sin y.
Proof.
start_with (cos (x - y)).
calc_LHS (cos (x + (- y))).
  now replace (x + (- y)) with (x - y) by ring.
calc_LHS (cos x * cos (- y) - sin x * sin (- y)).
  now rewrite cos_add.
calc_LHS (cos x * cos y - sin x * sin (- y)).
  now rewrite par_cos.
calc_LHS (cos x * cos y - sin x * (- sin y)).
  now rewrite par_sin.
ring.
Qed.

Lemma sin_sub x y : sin (x - y) = cos y * sin x - cos x * sin y.
Proof.
start_with (sin (x - y)).
calc_LHS (sin (x + (- y))).
  now replace (x + (- y)) with (x - y) by ring.
calc_LHS (cos x * sin (- y) + cos (- y) * sin x).
  now rewrite sin_add.
calc_LHS (cos x * - sin y + cos (- y) * sin x).
  now rewrite par_sin.
calc_LHS (cos x * - sin y + cos y * sin x).
  now rewrite par_cos.
ring.
Qed.

Lemma sin0 : sin 0 = 0.
Proof.
start_with (sin 0).
calc_LHS ((sin 0 + sin 0) / 2).
  now field.
calc_LHS ((sin (-0) + sin 0) / 2).
  now replace (-0) with 0 by ring.
calc_LHS ((- sin 0 + sin 0) / 2).
  now rewrite par_sin.
now field.
Qed.

Lemma cos0 : cos 0 = 1.
Proof.
(* This is not satisfactory, because sin 0 ^ 2 and sin 0 * sin 0
  maybe interchangeable in the user's mind, but they are not in
  the computer's ability to recognize formulas.  *)
assert (sin 0 ^ 2 = 0).
  rewrite sin0.
  ring.
start_with (cos 0).
calc_LHS (cos (0 + 0)).
  now replace (0 + 0) with 0 by ring.
calc_LHS (cos 0 * cos 0 - sin 0 * sin 0).
  now rewrite cos_add.
(* Transforming products into squares has to be done explicitly. *)
calc_LHS (cos 0 ^ 2 - sin 0 ^ 2).
  ring.
calc_LHS (cos 0 ^ 2 + sin 0 ^ 2).
  end_calculate.
apply unit_circle.
Qed.

Lemma cos_double x : cos (2 * x) = cos x ^ 2 - sin x ^ 2.
Proof.
start_with (cos (2 * x)).
calc_LHS (cos (x + x)).
  now replace (2 * x) with (x + x) by ring.
calc_LHS (cos x * cos x - sin x * sin x).
  now rewrite cos_add.
end_calculate.
Qed.

Lemma sin_double x : sin (2 * x) = 2 * sin x * cos x.
Proof.
start_with (sin (2 * x)).
calc_LHS (sin (x + x)).
  now replace (2 * x) with (x + x) by ring.
calc_LHS (cos x * sin x + cos x * sin x).
  now rewrite sin_add.
end_calculate.
Qed.

Lemma sin_Pi_half : sin (Pi / 2) = 1.
Proof.
assert (cos (Pi / 2) ^ 2 = 0).
  rewrite cos_Pi_half.
  ring.
assert (sin_sq : sin (Pi / 2) ^ 2 = 1).
  start_with (sin (Pi / 2) ^ 2).
  calc_LHS (cos (Pi / 2) ^ 2 + sin (Pi / 2) ^ 2).
    end_calculate.
  rewrite unit_circle.
  easy.
assert (1 * sin (Pi / 2) ^ 2 + 0 * sin (Pi / 2) + - 1 = 0).
  (* Again a problem, you cannot replace occurrences of 0 and 1 by the
    left-hand sides of equations established in the history, and hope it
    will work, so end_calculate fails here. *)
  rewrite sin_sq; ring.
assert (0 < 0 ^ 2 - 4 * 1 * (- 1)).
  lra.
assert (1 <> 0) by lra.
assert (sin (Pi / 2) = (- 0 + sqrt ((0 ^ 2) - 4 * 1 * (- 1))) / (2 * 1) \/
        sin (Pi / 2) = (- 0 - sqrt ((0 ^ 2) - 4 * 1 * (- 1))) / (2 * 1)) as
        [posval | negval].
  apply trinom.
        lra.
      lra.
    easy.
  rewrite posval.
  replace (0 ^ 2 - 4 * 1 * -1) with 4 by ring.
  replace (sqrt 4) with 2; cycle 1.
    compute_sqrt.
    easy.
  field.
assert (0 - sqrt (0 ^ 2 - 4 * 1 * -1) / (2 * 1) = -1).
  replace (0 ^ 2 - 4 * 1 * -1) with 4 by ring.
  compute_sqrt.
  field.
enough (0 <= sin(Pi / 2)) by lra.
assert (0 < Pi / 2).
  assert (tmp := Pi_gt0); lra.
assert (forall x, 0 < x < Pi / 2 -> derivable sin x).
  now intros; apply derivable_sin.
assert (exists c, 0 < c < Pi / 2 /\
  sin (Pi / 2) = sin 0 + derive sin c * (Pi / 2 - 0)) as [c [cint sin_c]].
  apply MVT.
    easy.
  easy.
assert (sin (Pi / 2) = cos c * (Pi / 2)).
  start_with (sin (Pi / 2)).
  calc_LHS (sin 0 + derive sin c * (Pi / 2 - 0)).
    now rewrite sin_c.
  calc_LHS (derive sin c * (Pi / 2)).
    now rewrite sin0; ring.
  now rewrite derive_sin.
assert (0 < cos c).
  apply first_cos_root.
  lra.
replace (sin (Pi / 2)) with (cos c * (Pi / 2)) by easy;
apply Rmult_le_pos; lra.
Qed.

Lemma sin_Pi : sin Pi = 0.
Proof.
start_with (sin Pi).
calc_LHS (sin (Pi / 2 + Pi / 2)).
  now replace (Pi / 2 + Pi / 2) with Pi by field.
calc_LHS (cos (Pi / 2) * sin (Pi / 2) + cos (Pi / 2) * sin (Pi / 2)).
  now rewrite sin_add.
calc_LHS (0 * sin (Pi / 2) + 0 * sin (Pi / 2)).
  now rewrite cos_Pi_half.
now ring.
Qed.

Lemma cos_Pi : cos Pi = -1.
Proof.
start_with (cos Pi).
calc_LHS (cos (Pi / 2 + Pi / 2)).
  now replace (Pi / 2 + Pi / 2) with Pi by field.
calc_LHS (cos (Pi / 2) * cos (Pi / 2) - sin (Pi / 2) * sin (Pi / 2)).
  now rewrite cos_add.
calc_LHS (0 - sin (Pi / 2) * sin (Pi / 2)).
  now rewrite cos_Pi_half; ring.
calc_LHS (0 - 1 * 1).
  now rewrite sin_Pi_half.
ring.
Qed.

Lemma sin_add_Pi_half x : sin (x + Pi / 2) = cos x.
Proof.
start_with (sin (x + Pi / 2)).
calc_LHS (cos x * sin (Pi / 2) + cos (Pi / 2) * sin x).
  now rewrite sin_add.
calc_LHS (cos x + cos(Pi / 2) * sin x).
  now rewrite sin_Pi_half; ring.
now rewrite cos_Pi_half; ring.
Qed.

Lemma cos_add_Pi_half x : cos (x + Pi /  2) = - sin x.
Proof.
start_with (cos (x + Pi / 2)).
calc_LHS (cos x * cos (Pi / 2) - sin x * sin (Pi / 2)).
  now rewrite cos_add.
now rewrite cos_Pi_half, sin_Pi_half; ring.
Qed.

Lemma sin_add_Pi x : sin (x + Pi) = - sin x.
Proof.
start_with (sin (x + Pi)).
(* Here it fails if one writes cos Pi * sin x + cos x * sin Pi and do not
   include ring as the last operation. *)
calc_LHS (cos x * sin Pi + cos Pi * sin x).
  now rewrite sin_add.
calc_LHS (cos x * 0 + cos Pi * sin x).
  now rewrite sin_Pi.
calc_LHS (cos x * 0 + (-1) * sin x).
  now rewrite cos_Pi.
ring.
Qed.

Lemma cos_add_Pi x : cos (x + Pi) = - cos x.
Proof.
start_with (cos (x + Pi)).
calc_LHS (cos x * cos Pi - sin x * sin Pi).
  now rewrite cos_add.
calc_LHS (cos x * (-1) - sin x * sin Pi).
  now rewrite cos_Pi.
calc_LHS (cos x * (-1) - sin x * 0).
  now rewrite sin_Pi.
ring.
Qed.

Lemma cos_sub_Pi x : cos (x - Pi) = - cos x.
Proof.
symmetry; start_with (- (cos x)).
calc_LHS (-(cos (x - Pi + Pi))).
  now replace (x - Pi + Pi) with x by ring.
calc_LHS (- (- (cos (x - Pi)))).
  now rewrite cos_add_Pi.
end_calculate.
Qed.

Lemma sin_sub_Pi x : sin (x - Pi) = - sin x.
Proof.
symmetry; start_with (- sin x).
calc_LHS (- sin (x - Pi + Pi)).
  now replace (x - Pi + Pi) with x by ring.
now rewrite sin_add_Pi; ring.
Qed.

Lemma sin_add_2Pi x : sin (x + 2 * Pi) = sin x.
Proof.
start_with (sin (x + 2 * Pi)).
calc_LHS (sin (x + Pi + Pi)).
  now replace (x + 2 * Pi) with (x + Pi + Pi) by ring.
calc_LHS (- (sin (x + Pi))).
  now rewrite sin_add_Pi.
now rewrite sin_add_Pi; ring.
Qed.

Lemma cos_add_2Pi x : cos (x + 2 * Pi) = cos x.
Proof.
start_with (cos (x + 2 * Pi)).
calc_LHS (cos (x + Pi + Pi)).
  now replace (x + Pi + Pi) with (x + 2 * Pi) by ring.
calc_LHS (- cos (x + Pi)).
  now rewrite cos_add_Pi.
now rewrite cos_add_Pi; ring.
Qed.

Lemma cos_sub_Pi_half x : cos (x - Pi / 2) = sin x.
Proof.
start_with (cos (x - Pi / 2)).
calc_LHS (cos x * cos (Pi / 2) + sin x * sin (Pi / 2)).
  now rewrite cos_sub.
calc_LHS (cos x * 0 + sin x * sin (Pi / 2)).
  now rewrite cos_Pi_half.
calc_LHS (cos x * 0 + sin x * 1).
  now rewrite sin_Pi_half.
ring.
Qed.

Lemma sin_sub_Pi_half x : sin (x - Pi / 2) = - cos x.
Proof.
start_with (sin (x - Pi / 2)).
calc_LHS (cos (Pi / 2) * sin x - cos x * sin (Pi / 2)).
  now rewrite sin_sub.
calc_LHS (0 * sin x - cos x * sin (Pi / 2)).
  now rewrite cos_Pi_half.
calc_LHS (0 * sin x - cos x * 1).
  now rewrite sin_Pi_half.
ring.
Qed.

Lemma sin_Pi_sub x : sin (Pi - x) = sin x.
Proof.
start_with (sin (Pi - x)).
calc_LHS (cos x * sin Pi - cos Pi * sin x).
  now rewrite sin_sub.
calc_LHS (cos x * 0 - (-1) * sin x).
  now rewrite cos_Pi, sin_Pi.
ring.
Qed.

Lemma cos_Pi_sub x : cos (Pi - x) = - cos x.
Proof.
start_with (cos (Pi - x)).
calc_LHS (cos Pi * cos x + sin Pi * sin x).
  now rewrite cos_sub.
now rewrite cos_Pi, sin_Pi; ring.
Qed.

Lemma cos_Pi_half_sub x : cos (Pi / 2 - x) = sin x.
Proof.
start_with (cos (Pi / 2 - x)).
calc_LHS (cos (Pi / 2) * cos x + sin (Pi / 2) * sin x).
  now rewrite cos_sub.
calc_LHS (0 * cos x + 1 * sin x).
  now rewrite cos_Pi_half, sin_Pi_half.
ring.
Qed.

Lemma sin_Pi_half_sub x : sin (Pi / 2 - x) = cos x.
Proof.
start_with (sin (Pi / 2 - x)).
calc_LHS (cos x * sin (Pi / 2) - cos (Pi / 2) * sin x).
  now rewrite sin_sub.
calc_LHS (cos x * 1 - cos (Pi / 2) * sin x).
  now rewrite sin_Pi_half.
calc_LHS (cos x * 1 - 0 * sin x).
  now rewrite cos_Pi_half.
ring.
Qed.

Lemma cos_double_1 x : cos (2 * x) = 2 * cos x ^ 2 - 1.
Proof.
assert (step : sin x ^ 2 = 1 - cos x ^ 2).
  start_with (sin x ^ 2).
  calc_LHS (cos x ^ 2 + sin x ^ 2 - cos x ^ 2).
    ring.
  now rewrite unit_circle.
start_with (cos (2 * x)).
calc_LHS (cos x ^ 2 - sin x ^ 2).
  now rewrite cos_double.
calc_LHS (cos x ^ 2 - (1 - cos x ^ 2)).
  now rewrite step.
ring.
Qed.

Lemma cos_Pi_third : cos (Pi / 3) = 1 / 2.
Proof.
assert (step1 : cos (Pi / 3) = - cos (Pi - Pi / 3)).
  rewrite cos_Pi_sub; ring.
assert (step2 : cos (Pi - Pi / 3) = 2 * cos (Pi / 3) ^ 2 - 1).
  start_with (cos (Pi - Pi / 3)).
  calc_LHS (cos (2 * (Pi / 3))).
    now replace (Pi - Pi / 3) with (2 * (Pi / 3)) by field.
  now rewrite cos_double_1.
assert (2 * cos (Pi / 3) ^ 2 + 1 * cos (Pi / 3) - 1 = 0).
  start_with (2 * cos (Pi / 3) ^ 2 + 1 * cos (Pi / 3) - 1).
  calc_LHS (2 * cos (Pi / 3) ^ 2 - 1 + cos (Pi / 3)).
    ring.
  calc_LHS (cos (Pi - Pi / 3) + cos (Pi / 3)).
    now rewrite step2.
  calc_LHS (- - (cos (Pi - Pi / 3)) + cos (Pi / 3)).
    ring.
  calc_LHS (- cos (Pi / 3) + cos (Pi / 3)).
    now rewrite step1.
  ring.
assert (0 <= 1 ^ 2 - 4 * 2 * (-1)).
  lra.
assert (vsqrt : sqrt (1 ^ 2 - 4 * 2 * (-1)) = 3).
  replace (1 ^ 2 - 4 * 2 * (-1)) with 9 by ring.
  now compute_sqrt.
assert (cos (Pi / 3) = ((- 1 + sqrt (1 ^ 2 - 4 * 2 * (-1))) / (2 * 2)) \/
        cos (Pi / 3) = ((- 1 - sqrt (1 ^ 2 - 4 * 2 * (-1)))/ (2 * 2)))
        as [higher | lower].
    apply trinom.
        lra.
      lra.
    easy.
  end_calculate.
assert (cos (Pi / 3) = -1).
  end_calculate.
assert (0 < cos (Pi / 3)).
  apply first_cos_root.
  assert (tmp := Pi_gt0); lra.
lra.
Qed.

Lemma sin_Pi_third : sin (Pi / 3) = sqrt 3 / 2.
Proof.
assert (1 * sin (Pi / 3) ^ 2 + 0 * sin (Pi / 3) + (- 3 / 4) = 0).
  start_with (1 * sin (Pi / 3) ^ 2 + 0 * sin (Pi / 3) + (- 3 / 4)).
  calc_LHS (sin (Pi / 3) ^ 2 - 1 + 1 / 4).
    field.
  calc_LHS (sin (Pi / 3) ^ 2 - (cos (Pi / 3) ^ 2 + sin (Pi / 3) ^ 2) + 1 /4).
    now rewrite unit_circle.
  calc_LHS (- (cos (Pi / 3) ^ 2) + 1 / 4).
    ring.
  calc_LHS (- (1 / 2) ^ 2 + 1 / 4).
    now rewrite cos_Pi_third.
  field.
assert (0 <= 0 ^ 2 - 4 * 1 * (-3 / 4)).
  lra.
assert (0 < sin (Pi / 3)).
  replace (sin (Pi / 3)) with (cos (Pi / 6)); cycle 1.
    symmetry; start_with (sin (Pi / 3)).
    calc_LHS (sin (Pi / 2 - Pi / 6)).
      now replace (Pi / 2 - Pi / 6) with (Pi / 3) by field.
    now rewrite sin_Pi_half_sub.
  apply first_cos_root.
  assert (tmp:= Pi_gt0); lra.
assert (sin (Pi / 3) = (- 0 + sqrt (0 ^ 2 - 4 * 1 * (-3 / 4))) / (2 * 1) \/
        sin (Pi / 3) = (- 0 - sqrt (0 ^ 2 - 4 * 1 * (-3 / 4))) / (2 * 1))
  as [higher | lower].
    apply trinom.
        lra.
      lra.
    easy.
  rewrite higher.
  replace (0 ^ 2 - 4 * 1 * (-3 / 4)) with 3 by field.
  field.
enough (0 <= sqrt (0 ^ 2 - 4 * 1 * (-3 / 4))) by lra.
now apply sqrt_pos'.
Qed.


Lemma cos_Pi_sixth : cos (Pi / 6) = sqrt 3 / 2.
Proof.
start_with (cos (Pi / 6)).
calc_LHS (cos (Pi / 2 - Pi / 3)).
  now replace (Pi / 2 - Pi / 3) with (Pi / 6) by field.
calc_LHS (sin (Pi / 3)).
  now rewrite cos_Pi_half_sub.
now rewrite sin_Pi_third.
Qed.

Lemma sin_Pi_sixth : sin (Pi / 6) = 1 / 2.
Proof.
start_with (sin (Pi / 6)).
calc_LHS (sin (Pi / 2 - Pi / 3)).
  now replace (Pi / 2 - Pi / 3) with (Pi / 6) by field.
calc_LHS (cos (Pi / 3)).
  now rewrite sin_Pi_half_sub.
now rewrite cos_Pi_third.
Qed.

Lemma common_sqrt_2 x : 0 < x -> 2 * x ^ 2 - 1 = 0 -> x = sqrt 2 / 2.
Proof.
intros xgt0 equa.
assert (2 * x ^ 2 + 0 * x + (-1) = 0) by lra.
(* It would be great to avoid an unreadable error message here. *)
Fail (assert (x = (- 0 - sqrt (0 ^ 2 - 4 * 2 * (-1))) / (2 * 2) \/
        x = (- 0 + sqrt (0 ^ 2 - 4 * 2 * (-1))) / (2 * 2)) as [higher | lower];
  [apply trinom | | ]).
assert (x = (- 0 + sqrt (0 ^ 2 - 4 * 2 * (-1))) / (2 * 2) \/
        x = (- 0 - sqrt (0 ^ 2 - 4 * 2 * (-1))) / (2 * 2)) as [higher | lower].
    apply trinom.
        lra.
      lra.
    easy.
  rewrite higher.
  start_with ((- 0 + sqrt (0 ^ 2 - 4 * 2 * (- 1))) / (2 * 2)).
  calc_LHS ((sqrt (0 ^ 2 - 4 * 2 * (- 1))) / 4).
    field.
  calc_LHS ((sqrt (2 * 4)) / 4).
    now replace (0 ^ 2 - 4 * 2 * -1) with (2 * 4) by ring.
  calc_LHS ((sqrt 2 * sqrt 4) / 4).
    now rewrite sqrt_mult; lra.
  calc_LHS (sqrt 2 * 2 / 4).
    now replace (sqrt 4) with 2 by now compute_sqrt.
  field.
assert (0 <= sqrt (0 ^ 2 - 4 * 2 * -1)) by now apply sqrt_pos'; lra.
lra.
Qed.

Lemma cos_Pi_fourth : cos (Pi / 4) = sqrt 2 / 2.
Proof.
assert (2 * cos (Pi / 4) ^ 2 - 1 = 0).
  start_with (2 * cos (Pi / 4) ^ 2 - 1).
  calc_LHS (cos (2 * (Pi / 4))).
    now rewrite <- cos_double_1.
  calc_LHS (cos (Pi / 2)).
    now replace (2 * (Pi / 4)) with (Pi / 2) by field.
  now rewrite cos_Pi_half.
assert (0 < cos (Pi / 4)).
  apply first_cos_root.
  assert (tmp := Pi_gt0); lra.
now apply common_sqrt_2.
Qed.

Lemma sin_Pi_fourth : sin (Pi / 4) = sqrt 2 / 2.
Proof.
start_with (sin (Pi / 4)).
calc_LHS (sin (Pi / 2 - Pi / 4)).
  now replace (Pi / 2 - Pi / 4) with (Pi / 4) by field.
calc_LHS (cos (Pi / 4)).
  now rewrite sin_Pi_half_sub.
now rewrite cos_Pi_fourth.
Qed.
