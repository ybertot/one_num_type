From Stdlib Require Import Reals ZArith Lra.
From OneNum Require Import R_subsets rec_def R_compute automation.
From elpi Require Import elpi.

Open Scope R_scope.

Ltac end_calculate :=
  repeat
   match goal with | id : _ = _ |- _ => (rewrite id || rewrite <- id); clear id end;
   (easy || ring || (field; (easy || lra))).

Ltac end_calculate' :=
  repeat
   match goal with | id : _ = _ |- _ => (rewrite id || rewrite <- id); clear id end;
   (easy || super_ring' || (super_field'; (easy || lra))).

Ltac calc_LHS F  :=
  match goal with
  | |- ?L = _ =>
    let name := fresh "temp_for_calc_LHS" in
     assert (name: L = F);[ | apply (eq_trans name); clear name]
  end.

Ltac calc_LHS' F :=
  match goal with
  | |- ?L = _ =>
    let name := fresh "temp_for_calc_LHS" in
     assert (name: L = F);[solve [easy |lra' | super_ring'|super_field' |lra'  ]| apply (eq_trans name); clear name]
  end.


Ltac start_with F :=
  match goal with |- ?L = _ => change L with F end.


Definition square_decompose m :=
  Z.iter (Z.sqrt m)
    (fun '(x, v) => 
      match v with Some _ => (x, v)%Z
      | None => if (m mod (x ^ 2) =? 0)%Z then 
                  (x, Some (m / (x ^ 2)))%Z
                else (x - 1, None)%Z
      end) (Z.sqrt m + 1, None)%Z.
      
Ltac compute_sqrt :=
  match goal with
  | |- context[sqrt (IZR ?x)] =>
    let v := eval compute in (Z.sqrt x) in
    change (sqrt (IZR x)) with (sqrt (IZR (v * v)));
    rewrite mult_IZR, sqrt_square;[ | lra]
  | |- context[sqrt (IZR ?x)] =>
    progress (let v := eval compute in (square_decompose x) in
    match v with
    (_, None) => idtac
    | (?z, Some ?y) => 
      change (sqrt (IZR x)) with (sqrt (IZR (z * z * y)));
      rewrite 2!mult_IZR;
      (rewrite sqrt_mult_alt;[ | lra]);
      rewrite sqrt_square;[ | lra]
    end)
  end.

Lemma compute_sqrt_test : sqrt 144 = 12 /\ sqrt 48 = 2 * sqrt 12.
Proof.
compute_sqrt.
compute_sqrt.
compute_sqrt.
split; ring.
Qed.

Section lemmas_that_should_exist.

Lemma div_cancel_r x y : y <> 0 -> x / y * y = x.
Proof.
intros yn0; unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
  ring.
easy.
Qed.

Lemma div_eq_transfer x y z : y <> 0 -> x / y = z -> z * y = x.
Proof.
intros yn0 divxy; apply (Rdiv_eq_reg_r y);[ | easy].
unfold Rdiv; rewrite Rmult_assoc, Rinv_r;[ | easy].
now fold (x / y); rewrite divxy; field.
Qed.

Lemma div_le_transfer x y z : 0 < y -> x / y <= z <-> x <= z * y.
Proof.
intros yn0; split; intros it.
apply (Rmult_le_reg_r (/ y));[now apply Rinv_0_lt_compat |].
  rewrite Rmult_assoc, Rinv_r; lra.
apply (Rmult_le_reg_r y);[easy |].
rewrite div_cancel_r; lra.
Qed.

Lemma div_le_1 x y : 0 < y -> x <= y -> x / y <= 1.
Proof.
intros ygt0 xlty.
apply (Rmult_le_reg_r y).
  easy.
rewrite div_cancel_r; lra.
Qed.

(* We believe that in a mathematical class, we cannot assume sqrt to be defined
  for all real number, we should rather respect that the value is well defined
  only for positive real numbers. sqrt_pos should not be used in our context,
  but sqrt_pos' instead. *)
Lemma sqrt_pos' x : 0 <= x -> 0 <= sqrt x.
Proof. intros; apply sqrt_pos. Qed.

Lemma sqrt_Rpow2 x : 0 <= x -> sqrt (x ^ 2) = x.
Proof.
now intros xge0; rewrite pow_2_expand; apply sqrt_square.
Qed.

Lemma Rpow2_sqrt x : 0 <= x -> sqrt x ^ 2 = x.
Proof.
now intros xge0; rewrite pow_2_expand; apply sqrt_sqrt.
Qed.

End lemmas_that_should_exist.

Module Type simple_trigo.

Parameter derivable : (R -> R) -> R -> Prop.

Parameter derive : (R -> R) -> R -> R.

Parameter continuous : (R -> R) -> R -> Prop.

Axiom continuous_opp : forall f x, continuous f x -> continuous (fun y => - f y) x.

Axiom derivable_continuous : forall f x, derivable f x -> continuous f x.

Axiom IVT_increasing : forall f a b, a < b ->
  (forall x, a <= x <= b -> continuous f x) ->
  forall v, f a <= v <= f b -> exists c, a <= c <= b /\ f c = v.

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

Axiom tan : R -> R.

Axiom tan_val : forall x, (forall n, Rint n -> x <> Pi / 2 + n * Pi) -> 
  tan x = sin x / cos x.

Axiom tan_derivable : forall x, (forall n, Rint n -> x <> Pi / 2 + n * Pi) ->
  derivable tan x.

Axiom tan_derive : forall x, (forall n, Rint n -> x <> Pi / 2 + n * Pi) ->
  derive tan x = 1 + tan x ^ 2.

End simple_trigo.

Lemma square_eq x y : x ^ 2 = y ^ 2 -> x = y \/ x = - y.
Proof.
intros sqeq.
assert (main : (x - y) * (x + y) = 0).
  start_with ((x - y) * (x + y)).
  calc_LHS' (x ^ 2 - y ^ 2).
  Timeout 1 calc_LHS' (x ^ 2 - x ^ 2).
  lra.
apply Rmult_integral in main.
destruct main as [it | it]; lra.
Qed.

Lemma sqrt_intro x y : 0 <= y -> x ^ 2 = y -> x = -sqrt y \/ x = sqrt y.
Proof.
intros yge0 x2q.
apply or_comm, square_eq.
rewrite Rpow2_sqrt; easy.
Qed.

Lemma trinom : forall a b c x, a <> 0 ->
  0 <= b * b - 4 * a * c ->
  a * x ^ 2 + b * x + c = 0 ->
    x = ((- b - sqrt (b * b - 4 * a * c)) / (2 * a)) \/
    x = ((- b + sqrt (b * b - 4 * a * c)) / (2 * a)).
Proof.
enough (wlog : forall a b c x, 0 < a ->
  0 <= b * b - 4 * a * c ->
  a * x ^ 2 + b * x + c = 0 ->
  x = ((- b - sqrt (b * b - 4 * a * c)) / (2 * a)) \/
  x = ((- b + sqrt (b * b - 4 * a * c)) / (2 * a))).
  intros a b c x an0 discr_ge_0 equa.
  assert (a < 0 \/ 0 < a) as [aneg | apos] by lra.
    assert (0 < - a) by lra.
    assert (fact: b * b - 4 * a * c = (- b) * (-b) - 4 * (-a) * (- c)) by ring.
    assert (0 <= (-b) * (-b) - 4 * (- a) * (- c)) by now rewrite <- fact.
    apply or_comm.
    replace (b * b - 4 * a * c) with ((- b) * (- b) - 4 * (-a) * (- c)) by ring.
    replace ((- b - sqrt ((- b) * (-b) - 4 * -a * - c)) / (2 * a)) with
      ((- (- b) + sqrt ((- b) * (- b) - 4 * -a * - c)) / (2 * (- a))) by (field; easy).
    replace ((- b + sqrt ((- b) * (- b) - 4 * -a * - c)) / (2 * a)) with
      ((- (- b) - sqrt ((- b) * (- b) - 4 * -a * - c)) / (2 * (- a)))
      by (field; easy).
    apply wlog.
        easy.
      easy.
    lra.
  apply wlog; easy.
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
        (b * b - 4 * a * c) / (4 * a ^ 2)).
  start_with ((x + b /  (2 * a)) ^ 2).
  Timeout 5 calc_LHS' ((x + b / (2 * a)) ^ 2 + (c / a - b ^ 2 / (4 * a ^ 2)) -
    (c / a - b ^ 2 / (4 * a ^ 2))).
    
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
assert (0 <= (b * b - 4 * a * c) / (4 * a ^ 2)).
  apply Rmult_le_pos.
    easy.
  lra.
enough (x + b / (2 * a) = - (sqrt (b * b - 4 * a * c) / (2 * a)) \/
        x + b / (2 * a) = sqrt (b * b - 4 * a * c) / (2 * a)) by lra.
replace (sqrt (b * b - 4 * a * c) / (2 * a)) with
    (sqrt ((b * b - 4 * a * c) / (4 * a ^ 2))); cycle 1.
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
apply sqrt_intro.
  easy.
easy.
Qed.


Ltac body A B C Thm First_Root Second_Root :=
try (match goal with
  | discr_ge0 : 0 <= ?d ,
    equa : ?p = 0 |- ?X = ?V1 \/ ?X = ?V2 =>
    let h_a := fresh "lead_coeff_eq" in
    let h_b := fresh "discr_eq" in
    let h_c := fresh "equa_eq" in
    let h_d := fresh "first_root" in
    let h_e := fresh "second_root"in
    let h_tmp := fresh "tmp" in
    assert (h_a : A <> 0 ) by (lra ||
      fail 2 "Working with equation" p "= 0"
        "You need to provide a proof that" A "is not 0");
    let D := constr:(B * B - 4 * A * C) in
    assert (h_b : d = B * B - 4 * A * C) by (field; (easy || lra));
    assert (h_c : p = A * X ^ 2 + B * X + C) by (field; (easy || lra));
    assert (h_d : V1 = First_Root)
      ;
      [(( (* if field_simplify produces side goals, 
            we want them to be solved by easy or lra*)
        field_simplify D;[ idtac | (easy || lra) ..]);
       try compute_sqrt; field; (easy || lra)) ||
       fail 3 "Working with equation" p "= 0"
       "this tactic failed to prove that" V1 "is equal to" "the smallest root"
       First_Root
       "Maybe you gave the roots in the wrong order"
       | ];
    assert (h_e : V2 = Second_Root);
       [(( (* if field_simplify produces side goals, 
            we want them to be solved by easy or lra*)
        field_simplify D;[ idtac | (easy || lra) ..]);
       try compute_sqrt; field; (easy || lra)) ||
       fail 3 "Working with equation" p "= 0"
       "this tactic failed to prove that" V2 "is equal to the largest root"
       Second_Root
       | ];
    enough (h_tmp: X = First_Root \/
            X = Second_Root);
        [try (rewrite <- 1?h_d, <- 1?h_e in h_tmp; easy) | ];
    apply Thm;[ easy| 
                   try rewrite <- h_b; easy| 
                   try rewrite <- h_c; easy]
  end).

Ltac trinom_with_coeff_and_hypotheses A B C Thm First_Root Second_Root :=
  idtac "entering trinom_with_c_a_h" A B C;
  match goal with | |- ?W => idtac W end;
  match goal with
  | discr_ge0 : 0 <= ?d ,
    equa : ?p = 0 |- ?X = ?V1 \/ ?X = ?V2 =>
    let h_a := fresh "lead_coeff_eq" in
    let h_b := fresh "discr_eq" in
    let h_c := fresh "equa_eq" in
    let h_d := fresh "first_root" in
    let h_e := fresh "second_root"in
    let h_tmp := fresh "tmp" in
    assert (h_a : A <> 0 ) by (lra ||
      fail 1 "Working with equation" p "= 0"
        "You need to provide a proof that" A "is not 0");
    let D := constr:(B * B - 4 * A * C) in
    assert (h_b : d = B * B - 4 * A * C) by (field; (easy || lra ||
      fail 2 "failed to check discriminant identity"));
    assert (h_c : p = A * X ^ 2 + B * X + C) by (field; (easy || lra
      || fail 2 "failed to check trinom equality"));
    assert (h_d : V1 = First_Root);
      [(( (* if field_simplify produces side goals, 
            we want them to be solved by easy or lra*)
        field_simplify D;[ idtac | (easy || lra) ..]);
       try compute_sqrt; field; (easy || lra)) ||
       fail 2 "Working with equation" p "= 0"
       "this tactic failed to prove that" V1 "is equal to" "the smallest root"
       First_Root
       "Maybe you gave the roots in the wrong order"
       | ];
    assert (h_e : V2 = Second_Root);
       [(( (* if field_simplify produces side goals, 
            we want them to be solved by easy or lra*)
        field_simplify D;[ idtac | (easy || lra) ..]);
       try compute_sqrt; field; (easy || lra)) ||
       fail 2 "Working with equation" p "= 0"
       "this tactic failed to prove that" V2 "is equal to the largest root"
       Second_Root
       | ];
    enough (h_tmp: X = First_Root \/
            X = Second_Root);
        [try (rewrite <- 1?h_d, <- 1?h_e in h_tmp; easy) | ];
    apply Thm;[ easy| 
                   try rewrite <- h_b; easy| 
                   try rewrite <- h_c; easy]
  end.

Ltac trinom_with_coeff A B C :=
  let D := constr:(B * B - 4 * A * C) in
  let First_Root := constr:((- B - sqrt D) / (2 * A)) in
  let Second_Root := constr:((- B + sqrt D) / (2 * A)) in
  let d_h := fresh "trinom_hyp_discr" in
  match goal with
  | discr_ge0 : 0 <= ?d |- _ =>
    assert (d_h : 0 <= D) by
     (replace D with d by field; assumption);
     idtac "recognized user given discriminant";
     clear discr_ge0
  | |- _ => (assert (d_h : 0 <= D) by (lra ||
              fail 2 "failed to prove that the discriminant" D "is non negative"))
  end
  ;
    (assert_succeeds (assert (0 < A) by lra);
    idtac "calling trinom_w_c_a_h with positive head coefficient";
  (trinom_with_coeff_and_hypotheses A B C trinom First_Root Second_Root)
    )
  ||
  (assert_succeeds (assert (A < 0) by lra); trinom_with_coeff_and_hypotheses A B C
    (fun a b c x an0 dge0 equa => proj1 (or_comm _ _) (trinom a b c x an0 dge0 equa))
    Second_Root First_Root)
    .
  
Ltac trinom_fast :=
(* To begin with, we expect that there is an equation of degree 2 in the
   context. *)
match goal with | equa : ?p = 0 |- _ =>
  field_simplify p in equa;
  (* After field_simplify, we expect the term to be a polynomial where all
    coefficients are integers, potentially divided by another integer. *)
  let q := match type of equa with | ?q / _ = 0 => q | ?q = 0 => q end in
  let X := match q with
    | _ * ?X ^ 2 + _ + _ => X
    | ?X ^ 2 + _ + _ => X
    | - ?X ^ 2 + _ + _ => X
    | _ * ?X ^ 2 - _ + _ => X
    | ?X ^ 2 - _ + _ => X
    | - ?X ^ 2 - _ + _ => X
    | _ * ?X ^ 2 + _ - _ => X
    | ?X ^ 2 + _ - _ => X
    | - ?X ^ 2 + _ - _ => X
    | _ * ?X ^ 2 - _ - _ => X
    | ?X ^ 2 - _ - _ => X
    | - ?X ^ 2 - _ - _ => X
    | _ * ?X ^ 2 + _ => X
    | ?X ^ 2 + _ => X
    | - ?X ^ 2 + _ => X
    | _ * ?X ^ 2 - _ => X
    | ?X ^ 2 - _ => X
    | -?X ^ 2 - _ => X
  end in
  let A := match q with
    | ?A * X ^ 2 + _ + _ => A
    | X ^ 2 + _ + _ => constr:(IZR 1)
    | - X ^ 2 + _ + _ => constr:(IZR (- 1))
    | ?A * X ^ 2 + _ => A
    | X ^ 2 + _ => constr:(IZR 1)
    | ?A * X ^ 2 - _ + _ => A
    | X ^ 2 - _ + _ => constr:(IZR 1)
    | - X ^ 2 - _ + _ => constr:(IZR (- 1))
    | ?A * X ^ 2 + _ - _ => A
    | X ^ 2 + _ - _ => constr:(IZR 1)
    | - X ^ 2 + _ - _ => constr:(IZR (- 1))
    | ?A * X ^ 2 - _ - _ => A
    | X ^ 2 - _ - _ => constr:(IZR 1)
    | - X ^ 2 - _ - _ => constr:(IZR (- 1))
    | ?A * X ^ 2 - _ => A
    | X ^ 2 - _ => constr:(IZR 1)
  
  end in
  let B := match q with
    | _ + ?B * X + _ => B
    | _ - ?B * X + _ => constr:(- B)
    | _ + ?B * X - _ => B
    | _ - ?B * X - _ => constr:(- B)
    | _ + ?X + _ => constr:(IZR 1)
    | _ - ?X + _ => constr:(IZR (- 1))
    | _ + ?X - _ => constr:(IZR 1)
    | _ - ?X - _ => constr:(IZR (- 1))
    | _ + ?B * X => B
    | _ - ?B * X => constr:(- B)
    | _ + X => constr:(IZR 1)
    | _ - X => constr:(IZR (- 1))
    | _ + ?C => constr:(IZR 0)
    | _ - ?C => constr:(IZR 0)
  end in
  let C := match q with
    | _ + ?B * X + ?C => C
    | _ - ?B * X + ?C => C
    | _ + ?B * X - ?C => constr:(- C)
    | _ - ?B * X - ?C => constr:(- C)
    | _ + ?X + ?C => C
    | _ - ?X + ?C => C
    | _ + ?X - ?C => constr:(- C)
    | _ - ?X - ?C => constr:(- C)
    | _ + ?B * X => constr:(IZR 0)
    | _ - ?B * X => constr:(IZR 0)
    | _ + X => constr:(IZR 0)
    | _ - X => constr:(IZR 0)
    | _ + ?C => C
    | _ - ?C => constr:(- C)
  end in
let new_lhs := constr:(A * X ^ 2  + B * X + C) in
assert (new_lhs = 0) by lra; clear equa;
trinom_with_coeff A B C
end.

Lemma toto x :  - x ^ 2 + 1 / 2 = 0 -> 0 < x -> x = sqrt 2 / 2.
Proof.
intros eqx xgt0.
Fail assert (two_roots : x = - sqrt 2 / 2 \/ x = - sqrt 2 / 2) by trinom_fast.
assert (two_roots : x = - sqrt 2 / 2 \/ x = sqrt 2 / 2) by trinom_fast.
body 2 0 (- (1)) trinom ((- 0 - sqrt (0 * 0 - 4 * 2 * -(1))) / (2 * 2))
  ((- 0 + sqrt (0 * 0 - 4 * 2 * -(1))) / (2 * 2)).
destruct two_roots as [lower| higher].
assert (x = -sqrt 2 / 2) by exact lower.
  assert (0 <= sqrt 2) by now apply sqrt_pos.
  lra.
easy.
Qed.

Lemma toto0 x : -2 * x ^ 2 + 1 = 0 -> 0 < x -> x = sqrt 2 / 2.
Proof.
intros eqx xgt0.
Fail assert (two_roots : x = - sqrt 2 / 2 \/ x = - sqrt 2 / 2) by trinom_fast.
assert (two_roots : x = - sqrt 2 / 2 \/ x = sqrt 2 / 2).
 trinom_fast.
now destruct two_roots; [assert (0 <= sqrt 2) by apply sqrt_pos; lra| easy].
Qed.

Lemma toto1 x : 0 <= 3 ->
  x ^ 2 - 3 / 4 = 0 -> x = -sqrt 3 / 2 \/ x = sqrt 3 / 2.
Proof.
intros.
trinom_fast.
Qed.

Lemma toto2 x :  2 * x ^ 2 + x - 1 = 0 ->
  x = - 1 \/ x = 1 / 2.
Proof.
intros.
trinom_fast.
Qed.

Module trigo_facts (D : simple_trigo).

Import D.

(* TODO: place this in a different context. *)
Lemma IVT_decreasing : forall f a b, a < b ->
  (forall x, a <= x <= b -> continuous f x) ->
  forall v, f b <= v <= f a -> exists c, a <= c <= b /\ f c = v.
Proof.
intros f a b altb cont v intv.
set (g := fun y => - f y).
assert (g a <= -v <= g b) by (unfold g; lra).
assert (gcont : forall x, a <= x <= b -> continuous g x).
  intros x intx.
  unfold g.
  apply continuous_opp.
  now apply cont.
assert (exists c, a <= c <= b /\ g c = -v) as [c [intc gc]].
  apply IVT_increasing.
      easy.
    easy.
  easy.
exists c.
split.
  easy.
symmetry.
start_with v.
calc_LHS' (- g (c)).
calc_LHS' (- - (f c)).
end_calculate'.
Qed.
  
Lemma cos_sub x y : cos (x - y) = cos x * cos y + sin x * sin y.
Proof.
start_with (cos (x - y)).
calc_LHS' (cos (x + (- y))).
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
calc_LHS' (sin (x + (- y))).
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
calc_LHS' ((sin (-0) + sin 0) / 2).
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
calc_LHS' (cos (0 + 0)).
calc_LHS (cos 0 * cos 0 - sin 0 * sin 0).
  now rewrite cos_add.
(* Transforming products into squares has to be done explicitly. *)
calc_LHS' (cos 0 ^ 2 - sin 0 ^ 2).
calc_LHS' (cos 0 ^ 2 + sin 0 ^ 2).
apply unit_circle.
Qed.

(* This proof is unsatisfactory because it adapts to the limited
  reasoning capability of lra, *)
Lemma cos_bounds x : -1 <= cos x <= 1.
Proof.
assert (main : ~ 1 < cos x ^ 2).
  intros abs.
  assert (tmp := unit_circle x).
  assert (0 <= sin x ^ 2) by apply square_ge0.
  lra.
assert (cos x < - 1 \/ -1 <= cos x) as [badbelow | above] by lra.
  destruct main.
  assert (cos x ^ 2 = 1 + 2 * (- 1 - cos x) + (- 1 - cos x) ^ 2)
      by ring.
  assert (0 < -1 - cos x) by lra.
  assert (0 <= (-1 - cos x) ^ 2) by apply square_ge0.
  lra.
assert (1 < cos x \/ cos x <= 1) as [below | badabove] by lra.
  destruct main.
  assert (cos x ^ 2 = 1 + 2 * (cos x - 1) + (cos x - 1) ^ 2) by ring.
  assert (0 <= (cos x - 1) ^ 2) by apply square_ge0.
  lra.
lra.
Qed.

Lemma sin_bounds x : -1 <= sin x <= 1.
Proof.
assert (main : ~ 1 < sin x ^ 2).
  intros abs.
  assert (tmp := unit_circle x).
  assert (0 <= cos x ^ 2) by apply square_ge0.
  lra.
assert (sin x < - 1 \/ -1 <= sin x) as [badbelow | above] by lra.
  destruct main.
  assert (sin x ^ 2 = 1 + 2 * (- 1 - sin x) + (- 1 - sin x) ^ 2)
      by ring.
  assert (0 < -1 - sin x) by lra.
  assert (0 <= (-1 - sin x) ^ 2) by apply square_ge0.
  lra.
assert (1 < sin x \/ sin x <= 1) as [below | badabove] by lra.
  destruct main.
  assert (sin x ^ 2 = 1 + 2 * (sin x - 1) + (sin x - 1) ^ 2) by ring.
  assert (0 <= (sin x - 1) ^ 2) by apply square_ge0.
  lra.
lra.
Qed.

Lemma cos_double x : cos (2 * x) = cos x ^ 2 - sin x ^ 2.
Proof.
start_with (cos (2 * x)).
calc_LHS' (cos (x + x)).
calc_LHS (cos x * cos x - sin x * sin x).
  now rewrite cos_add.
end_calculate.
Qed.

Lemma sin_double x : sin (2 * x) = 2 * sin x * cos x.
Proof.
start_with (sin (2 * x)).
calc_LHS' (sin (x + x)).
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
  calc_LHS' (cos (Pi / 2) ^ 2 + sin (Pi / 2) ^ 2).
  rewrite unit_circle.
  end_calculate.
assert (sin (Pi / 2) ^ 2 - 1 = 0).
  rewrite sin_sq; ring.
assert (sin (Pi / 2) = -1 \/ sin(Pi / 2) = 1) as [abs | it].
    trinom_with_coeff 1 0 (-1).
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
    calc_LHS' (sin 0 + derive sin c * (Pi / 2 - 0)).
    calc_LHS (derive sin c * (Pi / 2)).
      now rewrite sin0; ring.
    now rewrite derive_sin.
  assert (0 < cos c).
    apply first_cos_root.
    lra.
  replace (sin (Pi / 2)) with (cos c * (Pi / 2)) by easy;
  apply Rmult_le_pos; lra.
easy.
Qed.

Lemma sin_Pi : sin Pi = 0.
Proof.
start_with (sin Pi).
calc_LHS' (sin (Pi / 2 + Pi / 2)).
  (* do 2 super_field ; reflexivity. *)
calc_LHS (cos (Pi / 2) * sin (Pi / 2) + cos (Pi / 2) * sin (Pi / 2)).
  now rewrite sin_add.
calc_LHS (0 * sin (Pi / 2) + 0 * sin (Pi / 2)).
  now rewrite cos_Pi_half.
end_calculate.
Qed.

Lemma cos_Pi : cos Pi = -1.
Proof.
start_with (cos Pi).
calc_LHS' (cos (Pi / 2 + Pi / 2)).
  (* do 2 super_field ; reflexivity.  *)
calc_LHS (cos (Pi / 2) * cos (Pi / 2) - sin (Pi / 2) * sin (Pi / 2)).
  now rewrite cos_add.
calc_LHS (0 - sin (Pi / 2) * sin (Pi / 2)).
  now rewrite cos_Pi_half; ring.
calc_LHS (0 - 1 * 1).
  now rewrite sin_Pi_half.
end_calculate.
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
end_calculate.
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
end_calculate.
Qed.

Lemma cos_sub_Pi x : cos (x - Pi) = - cos x.
Proof.
symmetry; start_with (- (cos x)).
calc_LHS' (-(cos (x - Pi + Pi))).
calc_LHS (- (- (cos (x - Pi)))).
  now rewrite cos_add_Pi.
end_calculate.
Qed.

Lemma sin_sub_Pi x : sin (x - Pi) = - sin x.
Proof.
symmetry; start_with (- sin x).
calc_LHS' (- sin (x - Pi + Pi)).
rewrite sin_add_Pi.
end_calculate.
Qed.

Lemma sin_add_2Pi x : sin (x + 2 * Pi) = sin x.
Proof.
start_with (sin (x + 2 * Pi)).
calc_LHS' (sin (x + Pi + Pi)).
calc_LHS (- (sin (x + Pi))).
  now rewrite sin_add_Pi.
rewrite sin_add_Pi.
end_calculate.
Qed.

Lemma cos_add_2Pi x : cos (x + 2 * Pi) = cos x.
Proof.
start_with (cos (x + 2 * Pi)).
calc_LHS' (cos (x + Pi + Pi)).
calc_LHS (- cos (x + Pi)).
  now rewrite cos_add_Pi.
rewrite cos_add_Pi.
end_calculate.
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
end_calculate.
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
end_calculate.
Qed.

Lemma sin_Pi_sub x : sin (Pi - x) = sin x.
Proof.
start_with (sin (Pi - x)).
calc_LHS (cos x * sin Pi - cos Pi * sin x).
  now rewrite sin_sub.
calc_LHS (cos x * 0 - (-1) * sin x).
  now rewrite cos_Pi, sin_Pi.
end_calculate.
Qed.

Lemma cos_Pi_sub x : cos (Pi - x) = - cos x.
Proof.
start_with (cos (Pi - x)).
calc_LHS (cos Pi * cos x + sin Pi * sin x).
  now rewrite cos_sub.
rewrite cos_Pi, sin_Pi.
end_calculate.
Qed.

Lemma cos_Pi_half_sub x : cos (Pi / 2 - x) = sin x.
Proof.
start_with (cos (Pi / 2 - x)).
calc_LHS (cos (Pi / 2) * cos x + sin (Pi / 2) * sin x).
  now rewrite cos_sub.
calc_LHS (0 * cos x + 1 * sin x).
  now rewrite cos_Pi_half, sin_Pi_half.
end_calculate.
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
end_calculate.
Qed.

Lemma sin_pos x : 0 <= x <= Pi -> 0 <= sin x.
Proof.
intros xint.
assert (x = 0 \/ x <> 0) as [x0 | xn0] by lra.
  now rewrite x0, sin0.
assert (x = Pi \/ x <> Pi) as [xPi | xnPi] by lra.
  now rewrite xPi, sin_Pi.
assert (x < Pi / 2 \/ Pi / 2 <= x) as [xlow | xhigh] by lra.
  replace (sin x) with (cos (Pi / 2 - x)) by now rewrite cos_Pi_half_sub.
  enough (0 < cos (Pi / 2 - x)) by lra.
  apply first_cos_root; lra.
replace (sin x) with (cos (x - Pi / 2)) by now rewrite cos_sub_Pi_half.
enough (0 < cos (x - Pi / 2)) by lra.
apply first_cos_root; lra.
Qed.

Lemma linearisation_cos_cos x y : cos x * cos y = (cos (x + y) + cos (x - y)) / 2.
Proof.
symmetry.
start_with ((cos (x + y) + cos (x - y)) / 2).
calc_LHS ((cos x * cos y - sin x * sin y + cos (x - y)) / 2).
  now rewrite cos_add.
calc_LHS ((cos x * cos y - sin x * sin y + (cos x * cos y + sin x * sin y)) / 2).
  now rewrite cos_sub.
end_calculate.
Qed.

Lemma linearisation_cos_sin x y : cos x * sin y = (sin (x + y) - sin (x - y)) / 2.
Proof.
start_with (cos x * sin y).
calc_LHS' ((cos x * sin y + cos y * sin x - (cos y * sin x - cos x * sin y)) / 2).
calc_LHS ((sin (x + y) - (cos y * sin x - cos x * sin y)) / 2).
  now rewrite <- sin_add.
calc_LHS ((sin (x + y) - (sin (x - y)))/ 2).
  now rewrite <- sin_sub.
end_calculate.
Qed.

Lemma linearisation_sin_sin x y : sin x * sin y = (cos (x - y) - cos (x + y)) / 2.
Proof.
symmetry.
start_with ((cos (x - y) - cos (x + y)) / 2).
calc_LHS ((cos x * cos y + sin x * sin y - cos (x + y)) / 2).
  now rewrite cos_sub.
calc_LHS ((cos x * cos y + sin x * sin y - (cos x * cos y - sin x * sin y)) / 2).
  now rewrite cos_add.
end_calculate.
Qed.

Lemma cos_double_1 x : cos (2 * x) = 2 * cos x ^ 2 - 1.
Proof.
assert (step : sin x ^ 2 = 1 - cos x ^ 2).
  start_with (sin x ^ 2).
  calc_LHS' (cos x ^ 2 + sin x ^ 2 - cos x ^ 2).
  now rewrite unit_circle.
start_with (cos (2 * x)).
calc_LHS (cos x ^ 2 - sin x ^ 2).
  now rewrite cos_double.
calc_LHS (cos x ^ 2 - (1 - cos x ^ 2)).
  now rewrite step.
clear step.
end_calculate.
Qed.

Lemma cos_Pi_third : cos (Pi / 3) = 1 / 2.
Proof.
assert (step1 : cos (Pi / 3) = - cos (Pi - Pi / 3)).
  rewrite cos_Pi_sub; ring.
assert (step2 : cos (Pi - Pi / 3) = 2 * cos (Pi / 3) ^ 2 - 1).
  start_with (cos (Pi - Pi / 3)).
  calc_LHS' (cos (2 * (Pi / 3))).
  now rewrite cos_double_1.
assert (step3 : 2 * cos (Pi / 3) ^ 2 + cos (Pi / 3) - 1 = 0).
lra.

(* Solution using an obvious solution. *)
assert (main : (cos (Pi / 3) + 1) * (cos (Pi /3) - 1 / 2) = 0).
  start_with ((cos (Pi / 3) + 1) * (cos (Pi /3) - 1 / 2)).
  calc_LHS' ((2 * cos (Pi / 3) ^ 2 + cos (Pi / 3) - 1) / 2).
  end_calculate.
assert (cos (Pi / 3) = - 1 \/ cos (Pi / 3) = 1 / 2).
  assert (tmp := Rmult_integral _ _ main); lra.
assert (cos (Pi / 3) = -1 \/ cos (Pi / 3) = 1 / 2)
        as [lower | higher].
  trinom_fast.
  assert (0 < cos (Pi / 3)).
    apply first_cos_root.
    assert (tmp := Pi_gt0); lra.
  lra.
easy.
Qed.

Lemma cos_Pi_third_with_trinom : cos (Pi / 3) = 1 / 2.
Proof.
assert (step1 : cos (Pi / 3) = - cos (Pi - Pi / 3)).
  rewrite cos_Pi_sub; ring.
assert (step2 : cos (Pi - Pi / 3) = 2 * cos (Pi / 3) ^ 2 - 1).
  start_with (cos (Pi - Pi / 3)).
  calc_LHS' (cos (2 * (Pi / 3))).
  now rewrite cos_double_1.
assert (step3 : 2 * cos (Pi / 3) ^ 2 + cos (Pi / 3) - 1 = 0).
lra.
assert (cos (Pi / 3) = -1 \/ cos (Pi / 3) = 1 / 2)
        as [lower | higher].
  trinom_fast.
  assert (0 < cos (Pi / 3)).
    apply first_cos_root.
    assert (tmp := Pi_gt0); lra.
  lra.
easy.
Qed.

Lemma sin_Pi_third : sin (Pi / 3) = sqrt 3 / 2.
Proof.
assert (tmp: sin (Pi / 3) ^ 2 - 3 / 4 = 0).
  start_with (sin (Pi / 3) ^ 2 - 3 / 4).
  calc_LHS' (sin (Pi / 3) ^ 2 - 1 + 1 / 4).
  calc_LHS (sin (Pi / 3) ^ 2 - (cos (Pi / 3) ^ 2 + sin (Pi / 3) ^ 2) + 1 /4).
    now rewrite unit_circle.
  calc_LHS' (- (cos (Pi / 3) ^ 2) + 1 / 4).
  calc_LHS (- (1 / 2) ^ 2 + 1 / 4).
    now rewrite cos_Pi_third.
  end_calculate.
assert (sin (Pi / 3) = - sqrt 3 / 2 \/ sin (Pi / 3) = sqrt 3 / 2)
  as [lower | higher].
    trinom_fast.
  assert (0 < sin (Pi / 3)).
    assert (sin_to_cos : sin (Pi / 3) = cos (Pi / 6)).
      start_with (sin (Pi / 3)).
      calc_LHS (cos (Pi / 2 - Pi / 3)).
        now rewrite cos_Pi_half_sub.
      now replace (Pi / 2 - Pi / 3) with (Pi / 6) by field.
    rewrite sin_to_cos.
    apply first_cos_root.
    assert (p0 := Pi_gt0); lra.
  enough (0 <= sqrt 3) by lra.
  now apply sqrt_pos'; lra.
easy.
Qed.

Lemma cos_Pi_sixth : cos (Pi / 6) = sqrt 3 / 2.
Proof.
start_with (cos (Pi / 6)).
calc_LHS' (cos (Pi / 2 - Pi / 3)).
calc_LHS (sin (Pi / 3)).
  now rewrite cos_Pi_half_sub.
now rewrite sin_Pi_third.
Qed.

Lemma sin_Pi_sixth : sin (Pi / 6) = 1 / 2.
Proof.
start_with (sin (Pi / 6)).
calc_LHS' (sin (Pi / 2 - Pi / 3)).
calc_LHS (cos (Pi / 3)).
  now rewrite sin_Pi_half_sub.
now rewrite cos_Pi_third.
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
assert (two_roots : cos (Pi / 4) = - sqrt 2 / 2 \/ cos (Pi / 4) = sqrt 2 / 2).
  now trinom_fast.
destruct two_roots as [lower | higher].
  assert (0 <= sqrt 2) by now apply sqrt_pos'; lra.
  lra.
easy.
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

Lemma sin_periodic_1 x n : Rnat n ->
  sin (x + 2 * n * Pi) = sin x.
Proof.

 induction 1 as [ | m mnat Ih].
  start_with (sin (x + 2 * 0 * Pi)).
  calc_LHS' (sin x).
  end_calculate.
start_with (sin (x + 2 * (m + 1) * Pi)).
calc_LHS' (sin (x + 2 * m * Pi + 2 * Pi)).
calc_LHS (sin (x + 2 * m * Pi)).
  now rewrite sin_add_2Pi.
exact Ih.
Qed. 

Lemma sin_periodic x n : Rint n ->
  sin (x + 2 * n * Pi) = sin x.
Proof.
assert (0 <= n \/ n < 0) as [npos | nneg] by lra.
  intro nint.
  apply sin_periodic_1.
  now apply Rint_Rnat.
intros nint.
symmetry.
assert (0 <= -n) by lra.
assert (Rint (- n)).
  now apply Rint_opp.
assert (Rnat (- n)).
  now apply Rint_Rnat.
start_with (sin x).
calc_LHS' (sin (x + 2 * n  * Pi + 2 * (- n) * Pi)).
calc_LHS (sin (x + 2 * n * Pi)).
  now rewrite sin_periodic_1.
end_calculate.
Qed.

Lemma cos_periodic x n : Rint n ->
  cos (x + 2 * n * Pi) = cos x.
Proof.
intros nnat.
start_with (cos (x + 2 * n * Pi)).
calc_LHS (sin (Pi / 2 - (x + 2 * n * Pi))).
  now rewrite sin_Pi_half_sub.
calc_LHS' (sin (Pi / 2 - x + 2 * -n * Pi)).
assert (Rint (-n)) by now apply Rint_opp.
calc_LHS (sin (Pi / 2 - x)).
  now rewrite sin_periodic.
calc_LHS (cos x).
  now rewrite sin_Pi_half_sub.
end_calculate.
Qed.

Lemma modulus_bound_pos x y : 0 < x ->
  x / sqrt (x ^ 2 + y ^ 2) <= 1.
Proof.
intros x_gt0.
assert (0 < x ^ 2) by now apply square_pos; lra.
assert (0 <= y ^ 2) by apply square_ge0.
assert (0 < x ^ 2 + y ^ 2) by lra.
assert (0 < sqrt(x ^ 2 + y ^ 2)).
  apply sqrt_lt_R0.
  easy.
replace (x / sqrt (x ^ 2 + y ^ 2)) with (sqrt (x ^ 2 / (x ^ 2 + y ^ 2))); cycle 1.
  start_with (sqrt (x ^ 2 / (x ^ 2 + y ^ 2))).
  calc_LHS (sqrt (x ^ 2) / sqrt (x ^ 2 + y ^ 2)).
    rewrite sqrt_div; lra.
  now rewrite sqrt_Rpow2; lra.
replace 1 with (sqrt 1); cycle 1.
  now rewrite sqrt1.
apply sqrt_le_1.
    enough (0 < x ^  2 / (x ^ 2 + y ^ 2)) by lra.
    now apply Rdiv_lt_0_compat.
  lra.
apply div_le_1.
  easy.
lra.
Qed.


Lemma phase_and_amplitude a b : (a, b) <> (0, 0) ->
  exists rho phi, forall theta, 
    0 < rho /\ a * cos theta + b * sin theta = rho * cos (theta + phi).
Proof.
intros non_zero.
assert (a ^ 2 + b ^ 2 <> 0).
  assert (b_alt : b = 0 \/ b <> 0) by lra.
  assert (a_alt : a = 0 \/ a <> 0) by lra.
  destruct b_alt as [b0 | bn0].
    destruct a_alt as [a0 | an0].
      case non_zero; rewrite a0, b0.
      easy.
    assert (0 < a ^ 2) by now apply square_pos.
    assert (0 <= b ^ 2) by apply square_ge0.
    lra.
  assert (0 < b ^ 2) by now apply square_pos.
  assert (0 <= a ^ 2) by apply square_ge0.
  lra.
set (rho := sqrt (a ^ 2 + b ^ 2)).
exists rho.
assert (0 <= a ^ 2) by apply square_ge0.
assert (0 <= b ^ 2) by apply square_ge0.
assert (0 < rho).
  unfold rho; apply sqrt_lt_R0; lra.
assert (0 < 1 / rho).
  now apply Rdiv_lt_0_compat; lra.
assert (-1 <= a / rho <= 1).
  assert (a < 0 \/ 0 <= a) as [aneg | anneg] by lra.
    split.
      enough (- (a / rho) <= 1) by lra.
      replace (- (a / rho)) with ((-a) / sqrt ((- a) ^ 2 + b ^ 2)); cycle 1.
        start_with (- a / sqrt ((- a) ^ 2 + b ^ 2)).
        calc_LHS' (- a / sqrt (a ^ 2 + b ^ 2)).
        calc_LHS' (- (a / sqrt (a ^ 2 + b ^ 2))).
        end_calculate.
      apply modulus_bound_pos.
      lra.
    apply div_le_1.
      easy.
    lra.
  assert (a = 0 \/ 0 < a) as [a0 | agt0] by lra.
    rewrite a0.
    lra.
  split.
    transitivity 0.
      lra.
    enough (0 < a / rho) by lra.
    apply Rdiv_lt_0_compat.
      easy.
    easy.
  apply modulus_bound_pos.
  easy.
assert (exists c, 0 <= c <= Pi /\ cos c = a / rho) as [psi [intpsi cospsi]].
  apply IVT_decreasing.
      exact Pi_gt0.
    intros x intx; apply derivable_continuous.
    now apply derivable_cos.
  now rewrite cos0, cos_Pi.
assert (rho * cos psi = a).
  rewrite Rmult_comm.
  apply div_eq_transfer.
    lra.
  easy.
assert ((rho * sin psi) ^ 2 = b ^ 2).
  start_with ((rho * sin psi) ^ 2).
  calc_LHS' (rho ^ 2 * sin psi ^ 2).
  calc_LHS (rho ^ 2 * (1 - cos psi ^ 2)).
    now rewrite <- (unit_circle psi); ring.
  calc_LHS' (rho ^ 2 - (rho * cos psi) ^ 2).
  calc_LHS (rho ^ 2 - a ^ 2).
    now replace (rho * cos psi) with a.
  calc_LHS ((a ^ 2 + b ^ 2) - a ^ 2).
    now unfold rho; rewrite Rpow2_sqrt; lra.
  ring.
assert (sols : rho * sin psi = b \/ rho * sin psi = -b).
  now apply square_eq.
assert (0 <= sin psi).
  now apply sin_pos.
assert (0 <= rho * sin psi).
  apply Rmult_le_pos; lra.
assert (b < 0 \/ 0 <= b) as [blt0 | bge0] by lra.
  assert (rho * sin psi = - b) by lra.
  exists psi.
  intros theta.
  split.
    easy.
  symmetry.
  start_with (rho * cos (theta + psi)).
  calc_LHS (rho * (cos theta * cos psi - sin theta * sin psi)).
    now rewrite cos_add.
  calc_LHS (rho * cos psi * cos theta - rho * sin psi * sin theta).
    ring.
  replace (rho * sin psi) with (-b) by easy.
  replace (rho * cos psi) with a by easy.
  ring.
exists (- psi).
assert (rho * sin psi = b) by lra.
intros theta.
split.
  easy.
symmetry.
start_with (rho * cos (theta - psi)).
calc_LHS (rho * (cos theta * cos psi + sin theta * sin psi)).
  now rewrite cos_sub.
calc_LHS' (rho * cos psi * cos theta + rho * sin psi * sin theta).

calc_LHS (a * cos theta + rho * sin psi * sin theta).
  now replace (rho * cos psi) with a by easy.
calc_LHS (a * cos theta + b * sin theta).
  now replace (rho * sin psi) with b by easy.
easy.
Qed.

Lemma cos_non_0 x : (forall n, Rint n -> x <> Pi / 2 + n * Pi) ->
  cos x <> 0.
Proof.
intros defd.
assert (pi_gt0 := Pi_gt0).
set (m := floor (x / (2 * Pi))).
assert (nat_m : Rint m).
  now unfold m; apply floor_int.
set (y := x - m * (2 * Pi)).
assert (0 <= y < 2 * Pi).
  unfold y.
  enough (m * (2 * Pi) <= x < (m + 1) * (2 * Pi)) by lra.
  enough (m <= x / (2 * Pi) < (m + 1)).
    split;[rewrite mult_div_transfer_le | ].
        tauto.
      lra.
  rewrite <- mult_div_transfer_lt2.
    lra.
  lra.
apply floor_interval.
assert (xy : x = y + 2 * m * Pi).
  now unfold y; ring.
assert (cos_xy : cos x = cos y).
  rewrite xy.
  rewrite cos_periodic.
    easy.
  now apply floor_int.
rewrite cos_xy.
assert ((0 <= y /\ y <= Pi / 2) \/
        (Pi / 2 < y /\ y < 2 * Pi)) as [below_half_pi | above_half_pi] by lra.
  assert (y < Pi / 2 \/ y = Pi /2) as [below_strict | at_Pi_2] by lra.
    enough (0 < cos y) by lra.
    apply first_cos_root.
    lra.
  destruct (defd (2 * m)).
    solve_Rnat.
  rewrite xy, at_Pi_2; ring.
assert (Pi/2 < y <= 3 * Pi / 2 \/ 3 * Pi / 2 < y < 2 * Pi) as
  [below_3_half | above_3_half] by lra.
  assert (y < 3 * Pi / 2 \/ y = 3 * Pi / 2) as [below_strict | at_3Pi_2]
    by lra.
    enough (cos y < 0) by lra.
    replace (cos y) with (- (- (cos y))) by ring.
    rewrite <- cos_sub_Pi.
    enough (0 < cos (y - Pi)) by lra.
    assert (y <= Pi \/ Pi < y) as [below_Pi | above_Pi] by lra.
      rewrite <- par_cos.
      apply first_cos_root.
      lra.
    apply first_cos_root.
    lra.
  destruct (defd (2 * m + 1)).
    solve_Rnat.
  rewrite xy, at_3Pi_2; field.
enough (0 < cos y) by lra.
rewrite <- (cos_periodic y (-1));[ | solve_Rnat].
rewrite <- par_cos.
apply first_cos_root.
lra.
Qed.

Lemma tan_derive_2 x : (forall n, Rint n -> x <> Pi / 2 + n * Pi) -> 
  derive tan x = 1 / cos x ^ 2.
Proof.
intros xdefd.
start_with (derive tan x).
calc_LHS (1 + tan x ^ 2).
  now apply tan_derive.
calc_LHS (1 + (sin x / cos x) ^ 2).
  now rewrite tan_val.
calc_LHS ((cos x ^ 2 + sin x ^ 2) / cos x ^ 2).
  now field; apply cos_non_0.
calc_LHS (1 / cos x ^ 2).
  now rewrite unit_circle.
end_calculate.
Qed.

End trigo_facts.

Module Viete (D : simple_trigo).

Module T := trigo_facts D.
Import D.
Import T.

(* Starting here an exercise to prove Viete's formula
  Pi = 2 * 2 / sqrt 2 * 2 / sqrt (2 + sqrt 2) *
       2 / sqrt (2 + sqrt (2 + sqrt 2)) *)

(* First define a recursive function to describe the
  nested square root constructs. *)
Recursive (def Viete_aux such that
             Viete_aux 0 = sqrt 2 /\
             forall n, Rnat (n - 1) -> 
             Viete_aux n = sqrt (2 + Viete_aux (n - 1))).

(* Section 1: cos (Pi / 2 ^ (n + 2)) = Viete_aux n / 2 *)
Lemma cos_half_formula x : 0 <= x < Pi / 2 ->
  cos (x / 2) = sqrt (2 + 2 * cos x) / 2.
Proof.
intros xcond.
assert (tri : 2 * cos (x / 2) ^ 2 - (1 + cos x) = 0).
  assert (tmp := cos_double_1 (x / 2)).
  replace (2 * (x / 2)) with x in tmp by field.
  lra.

assert (tmp1 : -1 <= cos x <= 1) by apply cos_bounds.
assert (0 <= 0 * 0 - 4 * 2 * - (1 + cos x)).
  assert (tmp := cos_bounds x); lra.

(* TODO : trinom_Fast still needs improving to recognize equalities with sqrt
  involved. *)
assert (cos (x / 2) = - sqrt (0 * 0 - 4 * 2 * -(1 + cos x)) / 4 \/
   cos (x / 2) = sqrt (0 * 0 - 4 * 2 * -(1 + cos x)) / 4) as [wrong_value | good_value].
  trinom_with_coeff 2 0 (- (1 + cos x)).
  replace (0 * 0 -4 * 2 * - (1 + cos x)) with (8 * (1 + cos x)) in wrong_value by ring.
  assert (0 <= sqrt (8 * (1 +  cos x))) by apply sqrt_pos.
  assert (0 < cos (x / 2)) by (apply first_cos_root; lra).
  lra.
start_with (cos (x / 2)).
calc_LHS' (sqrt (0 * 0 - 4 * 2 * - (1 + cos x)) / 4).
calc_LHS' (sqrt (4 * (2 + 2 * cos x)) / 4).
calc_LHS (sqrt 4 * sqrt (2 + 2 * cos x) / 4).
  rewrite sqrt_mult_alt;[ | lra].
  easy.
calc_LHS (2 * sqrt (2 + 2 * cos x) / 4).
  compute_sqrt; easy.
end_calculate.
Qed.

Lemma cos_2_exp_n n : Rnat n -> cos (Pi / 2 ^ (n + 2)) =
  Viete_aux n / 2.
Proof.
induction 1.
  start_with (cos (Pi / 2 ^ (0 + 2))).
  calc_LHS' (cos (Pi /4)).
  rewrite cos_Pi_fourth.
  symmetry.

  start_with (Viete_aux 0 / 2).
  calc_LHS (sqrt 2 / 2).
    now rewrite (proj1 (Viete_aux_eqn)).
  end_calculate.
rename x into n.
rename H into nNat.
assert (0 < 2 ^ (n + 2)).
  apply Rpow_lt; lra.
start_with (cos (Pi / 2 ^ (n + 1 + 2))).
calc_LHS' (cos ((Pi / 2 ^ (n + 2 + 1)))).
calc_LHS (cos (Pi / (2 ^ (n + 2) * 2))).

  now rewrite Rpow_succ; [ | solve_Rnat].
calc_LHS' (cos ((Pi / (2 ^ (n + 2)) / 2))).
calc_LHS (sqrt (2 + 2 * cos (Pi / 2 ^ (n + 2))) / 2).
  rewrite cos_half_formula.
    easy.
  split.
    enough (0 < Pi / 2 ^ (n + 2)) by lra.
    apply Rdiv_lt_0_compat.
      exact Pi_gt0.
    easy.
  apply div_decr_r.
    exact Pi_gt0.
    split;[lra | ].
  replace 2 with (2 ^ 1) at 1 by ring.
  apply Rpow_incr_lt;[solve_Rnat | solve_Rnat | lra | ].
  lra'.
calc_LHS (sqrt (2 + 2 * (Viete_aux n / 2)) / 2).
  now rewrite IHRnat.
calc_LHS' (sqrt (2 + Viete_aux n) / 2).
  super_field'. 
calc_LHS (Viete_aux (n + 1) / 2).
rewrite (proj2 Viete_aux_eqn (n + 1)).
    super_ring'.
  solve_Rnat.
end_calculate.
Qed.
 
Lemma Rpow_incr_le x y z : Rnat y -> Rnat z ->
  1 <= x -> y <= z -> x ^ y <= x ^ z.
Proof.
intros ynat znat xge1 ylez.
assert (y = z \/ y < z) as [yz | yltz] by lra.
  now rewrite yz; lra.
assert (x = 1 \/ 1 < x) as [x1 | xgt1] by lra.
  rewrite x1, !Rpow1_l.
  lra.
enough (x ^ y < x ^ z) by lra.
apply Rpow_incr_lt; easy.
Qed.

Lemma pi_frac_bounds :
  forall m, Rnat m -> 0 < Pi / 2 ^ (m + 1) <= Pi / 2.
Proof.
intros m mnat.
split.
  apply Rdiv_lt_0_compat.
    apply Pi_gt0.
  apply Rpow_lt; lra.
apply div_decr_r_le.
  apply Pi_gt0.
split;[ lra' | ].
replace 2 with (2 ^ 1) at 1 by now rewrite Rpow1.
apply Rpow_incr_le;[solve_Rnat | solve_Rnat | lra | lra'].
Qed.

Lemma break_power_div a m : Rnat m ->
  a / 2 ^ (m + 1) = 2 * (a / 2 ^ (m + 2)).
Proof.
  intros mnat.

(* Field refuses to work, because of the need for the Rnat hypothesis*)
replace (m + 2) with ((m + 1) + 1) by ring.
replace (2 ^ ((m + 1) + 1)) with (2 * 2 ^ (m + 1)) by
  (rewrite (Rpow_succ _ (m + 1)); [ring | solve_Rnat]).
field.
enough (0 < 2 ^ (m + 1)) by lra.
apply Rpow_lt; lra.
Qed.

Lemma cos_Pi_frac_pow2_gt_0 n : Rnat n ->
  0 < cos (Pi / 2 ^ (n + 2)).
Proof.
intros nnat.
assert (0 < Pi / 2 ^ (n + 1) <= Pi / 2) by now apply pi_frac_bounds.
assert (Pi / 2 ^ (n + 1) = 2 * (Pi / 2 ^ (n + 2))).

  now apply break_power_div.
apply first_cos_root.
lra.
Qed.

Lemma prod_non_0 m n f : Rnat (n - m) -> Rnat m ->
  (forall i, Rnat i -> m <= i < n -> f i <> 0) ->
  \prod_(m <= i < n) f i <> 0.
Proof.
intros mnnat mnat.
replace n with (n - m + m) by ring.
revert mnnat.
(* generalize (n - m). *)
induction 1.
  intros _; replace (0 + m) with m by ring.
  rewrite prod0; lra.
intros fcond.
assert (fcond' : forall i, Rnat i -> m <= i < x + m -> f i <> 0).
  intros i inat iint.
  apply fcond.
    easy.
  lra.
rewrite prod_recr;[ | solve_Rnat | lra'].
apply Rmult_integral_contrapositive_currified.
  replace (x + 1 + m - 1) with (x + m) by ring.
  apply IHmnnat; easy.
apply fcond.
  solve_Rnat.
lra'.
Qed.

Lemma sin_Pi_over_2_pow_n n : Rnat n -> sin (Pi / 2 ^ (n + 1)) =
  1 / (\prod_(1 <= i < n + 1) cos (Pi / 2 ^ (i + 1)) * 2 ^ n).
Proof.
assert (pi_frac_bounds :
  forall m, Rnat m -> 0 < Pi / 2 ^ (m + 1) <= Pi / 2).
 intros m mnat.
 split.
    apply Rdiv_lt_0_compat.
      apply Pi_gt0.
    apply Rpow_lt; lra.
  apply div_decr_r_le.
    apply Pi_gt0.

  split;[ lra' | ].
  replace 2 with (2 ^ 1) at 1 by now rewrite Rpow1.
  apply Rpow_incr_le;[solve_Rnat | solve_Rnat | lra' | lra'].
assert (sin_not0 : forall m, Rnat m -> sin (Pi / 2 ^ (m + 1)) <> 0).
  intros m mnat.
  rewrite <- cos_Pi_half_sub.
  enough (0 < cos (Pi / 2 - (Pi / 2 ^ (m + 1)))) by lra.
  apply first_cos_root.
  enough (0 < Pi / 2 ^ (m + 1) <= Pi / 2) by lra.
  now apply pi_frac_bounds.
intros nnat.
(* assert (break : forall m, Rnat m ->
  Pi / 2 ^ (m + 1) = 2 * (Pi / 2 ^ (m + 2))).
  now apply break_power_div. *)
assert (main : forall m, Rnat m ->
  sin (Pi / 2 ^ (m + 2)) = sin (Pi / 2 ^ (m + 1)) /
    (2 * cos(Pi / 2 ^ (m + 2)))).
  intros m mnat.
  rewrite break_power_div; solve_Rnat.
  rewrite sin_double.
  field. 
  enough (0 < cos (Pi / 2 ^ (m + 2))) by lra.
  apply first_cos_root.
  assert (0 < Pi / 2 ^ (m + 1) <= Pi / 2) by now apply pi_frac_bounds.
  assert (Pi / 2 ^ (m + 1) = 2 * (Pi / 2 ^ (m + 2))) 
    by now apply break_power_div.
  lra.
induction nnat as [ | n nnat Ihn].
  start_with (sin (Pi / 2 ^ (0 + 1))).
  calc_LHS' (sin (Pi / 2)).
  (* super_ring'. *)
  calc_LHS 1.
    now rewrite sin_Pi_half.
  symmetry.
  start_with (1 / (\prod_( 1 <= i < (0 + 1)) cos (Pi / 2 ^ (i + 1)) * 2 ^ 0)).
  calc_LHS (1 / \prod_(1 <= i < (0 + 1)) cos (Pi / 2 ^ (i + 1))).
    field.
    replace (0 + 1) with 1 by ring.
    rewrite prod0; lra.
  calc_LHS' (1 / \prod_(1 <= i < 1) cos (Pi / 2 ^ (i + 1))).

  rewrite prod0; field.
replace (n + 1 + 1) with (n + 2) by ring.
assert (prod_step : \prod_(1 <= i < (n + 2)) cos (Pi / 2 ^ (i + 1)) =
   \prod_(1 <= i < (n + 1)) cos (Pi / 2 ^ (i + 1)) *
     cos (Pi / 2 ^ (n + 2))).
  assert (0 <= n) by now apply Rnat_ge0.
  rewrite prod_recr;[ | solve_Rnat | lra ].
  now super_ring'.
assert (2 < 2 ^ (n + 2)).
  replace 2 with (2 ^ 1) at 1 by ring. (* need a suitable theorem *)
  assert (0 <= n) by now apply Rnat_ge0.
  apply Rpow_incr_lt;[solve_Rnat | solve_Rnat | lra | lra ].
assert (0 <= Pi / 2 ^ (n + 2) < Pi / 2).
  assert (tmp := Pi_gt0).
  split.
    enough (0 < Pi / 2 ^ (n + 2)) by lra.
    apply Rdiv_lt_0_compat; lra.
  apply div_decr_r; lra.
assert (0 < cos (Pi / 2 ^ (n + 2))).
  now apply first_cos_root.
assert (0 < 2 ^ n).
  apply Rpow_lt; lra.
assert (0 <= n) by now apply Rnat_ge0.
start_with (sin (Pi / 2 ^ (n + 2))).
calc_LHS (sin (Pi / 2 ^ (n + 1)) / (2 * cos (Pi / 2 ^ (n + 2)))).
  now rewrite main.
calc_LHS (((1 / (\prod_(1 <= i < (n + 1)) cos (Pi / 2 ^ (i + 1)) * 2 ^ n))) /
            (2 * cos (Pi / 2 ^ (n + 2)))).
  now rewrite Ihn.
calc_LHS (1 / ((\prod_(1 <= i < (n + 1)) cos (Pi / 2 ^ (i + 1)) *
  cos (Pi / 2 ^ (n + 2))) * (2 ^ n * 2))).
  assert (\prod_(1 <= i < n + 1) cos (Pi / 2 ^ (i + 1)) <> 0).
    apply prod_non_0; solve_Rnat.
    intros i inat iint.
    enough (0 < cos (Pi / 2 ^ (i + 1))) by lra.
    replace (i + 1) with ((i - 1) + 2) by ring.
    apply cos_Pi_frac_pow2_gt_0.
    apply Rnat_sub; solve_Rnat; lra.
  field; lra.
calc_LHS (1 / (\prod_(1 <= i < (n + 2)) cos (Pi / 2 ^ (i + 1)) *
  (2 ^ n * 2))).
  rewrite (prod_recr _ _ (n + 2));[ | solve_Rnat | lra].
  replace (n + 2 - 1 + 1) with (n + 2) by ring.
  replace (n + 2 - 1) with (n + 1) by ring.
  easy.
now rewrite Rpow_succ.
Qed.

Parameter lim_nat_seq : (R -> R) -> R -> Prop.
Axiom equiv_seq_inv : forall f g, (forall n, Rnat n -> f n <> 0) ->
  (forall n, Rnat n -> g n <> 0) ->
  lim_nat_seq (fun x => f x / g x) 1 ->
  lim_nat_seq (fun x => g x / f x) 1.

Axiom equiv_seq_sin_x : forall u, lim_nat_seq u 0 ->
  lim_nat_seq (fun n => sin (u n) / u n) 1.

Axiom powers_to_zero : forall a b, 1 < b ->
  lim_nat_seq (fun n => a / b ^ n) 0.

Axiom lim_nat_seq_constant : forall a, lim_nat_seq (fun n => a) a.

Axiom equiv_to_lim : forall f g a, lim_nat_seq (fun n => f n / g n) 1->
  lim_nat_seq (fun n => g n) a -> lim_nat_seq (fun n => f n) a.

Axiom lim_nat_seq_ext_above : forall m f g l,
  (forall i, m <= i -> Rnat i -> g i = f i) ->
  lim_nat_seq f l -> lim_nat_seq g l.

Parameter lim_nat_inf : (R -> R) -> Prop.

Axiom lim_nat_inf_shift_x :
  forall x, lim_nat_inf (fun i => i + x).

Axiom lim_nat_inf_above : forall m f g ,
  (forall i, Rnat i -> m <= i -> f i <= g i) ->
    lim_nat_inf g -> lim_nat_inf f.

Axiom lim_nat_seq_subseq : forall f g a,
  (forall n, Rnat n -> Rnat (g n)) ->
  lim_nat_inf g ->
  lim_nat_seq f a -> lim_nat_seq (fun x => f (g x)) a.

Lemma lim_nat_seq_ext f g l:
  (forall i, Rnat i -> g i = f i) ->
  lim_nat_seq f l -> lim_nat_seq g l.
Proof.
intros fg; apply (lim_nat_seq_ext_above 0).
now intros i _; apply fg.
Qed.

Definition Viete n := 2 / Viete_aux n.

Lemma Rnat_gt0_ge1 n : Rnat n -> 0 < n -> 1 <= n.
Proof.
intros nnat ngt0.
enough (0 + 1 <= n) by lra.
apply Rnat_le_lt;[solve_Rnat | solve_Rnat | easy].
Qed.

Lemma Viete_aux_pos n : Rnat n -> 0 < Viete_aux n.
Proof.
induction 1 as [ | n nnat Ihn].
  rewrite (proj1 Viete_aux_eqn).
  apply sqrt_lt_R0; lra.
rewrite (proj2 Viete_aux_eqn);[ | solve_Rnat].
replace (n + 1 - 1) with n by ring.
apply sqrt_lt_R0; lra.
Qed.

Lemma Viete_formula :
  lim_nat_seq (fun n => 2 * \prod_(0 <= i < n) Viete i) Pi.
Proof.
assert (sin_formula : 
 forall n, Rnat n -> 2 * \prod_(0 <= i < n) Viete i =
   2 ^ (n + 1) * sin (Pi / 2 ^ (n + 1))).
  intros n nnat.
  assert (Viete_q : forall i, Rnat i -> 0<= i < n ->
    Viete i = 1 / cos (Pi / 2 ^ (i + 2))).
    intros i inat _.
    unfold Viete.
    rewrite cos_2_exp_n;[ | easy].
    field.
    enough (0 < Viete_aux i) by lra'.
    now apply Viete_aux_pos.
  assert (cos_n0 : forall i, Rnat i -> 0 <= i < n ->
            cos (Pi / 2 ^ (i + 2)) <> 0).
    intros i inat _.
    assert (0 < cos (Pi / 2 ^ (i + 2)))
      by now apply cos_Pi_frac_pow2_gt_0.
    lra'.
  assert (main1 : \prod_(0 <= i < n) Viete i =
          1 / \prod_(0 <= i < n) cos (Pi / (2 ^ (i + 2)))).
    add_ge0s.
    rewrite <- prod_inverse; solve_Rnat; auto.
    apply big_ext_low_nat; solve_Rnat; auto.
  rewrite main1.
  rewrite sin_Pi_over_2_pow_n; solve_Rnat.
  rewrite Rpow_succ; solve_Rnat.
  replace 1 with (0 + 1) at 5 by ring.
  rewrite <- big_shift; solve_Rnat.
  assert (triv : 
          \prod_(0 <= i < n) cos (Pi / 2 ^ (i + 1 + 1)) =
          \prod_(0 <= i < n) cos (Pi / 2 ^ (i + 2))).
    apply big_ext_low_nat; solve_Rnat.
    intros x _; replace (x + 1 + 1) with (x + 2) by ring.
    easy.
  rewrite triv.
  field.
  split.
    enough (0 < 2 ^ n) by lra.
    now apply Rpow_lt; lra.
  apply prod_non_0; solve_Rnat.
  intros i inat iint.
  enough (0 < cos (Pi / 2 ^ (i + 2))) by lra.
  apply cos_Pi_frac_pow2_gt_0; easy.
apply (lim_nat_seq_ext _ _ _ sin_formula).
apply (equiv_to_lim _ (fun _ => Pi));
 [ | apply lim_nat_seq_constant].
assert (ratio : forall n, Rnat n ->
           2 ^ (n + 1) * sin (Pi / 2 ^ (n + 1)) / Pi =
           sin (Pi / 2 ^ (n + 1)) / (Pi / 2 ^ (n + 1))).
  intros n nat.
  field.
  split.
    enough (0 < 2 ^ (n + 1)) by lra.
    now apply Rpow_lt; lra.
  enough (0 < Pi) by lra.
  now apply Pi_gt0.
apply (lim_nat_seq_ext _ _ _ ratio).
apply equiv_seq_sin_x.
apply (lim_nat_seq_subseq (fun i => Pi / 2 ^ i)).
  solve_Rnat.
apply lim_nat_inf_shift_x.
apply powers_to_zero.
lra.
Qed.

End Viete.
