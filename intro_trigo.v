From Stdlib Require Import Reals.

Open Scope R_scope.

Module Type simple_trigo.

Parameter derivable : (R -> R) -> R -> Prop.

Parameter derive : (R -> R) -> R -> R.

Axiom MVT : forall f a b, a < b ->
  (forall x, a < x < b -> derivable f x) ->
  exists c, a < c < b /\ f b = f a + derive f c * (b - a).

Parameters cos sin : R -> R.

Axiom par_sin : forall x, sin (- x) = - (sin x).
Axiom par_cons : forall x, cos (- x) = cos x.

Axiom derivable_cos : forall x, derivable cos x.
Axiom derive_cos : forall x, derive cos x = -sin x.
Axiom derivable_sin : forall x, derivable sin x.
Axiom derive_sin : forall x, derive sin x = cos x.

End simple_trigo.

Module trigo_facts (D : simple_trigo).

Import D.

Ltac end_calculate :=
  repeat 
   match goal with | id : _ = _ |- _ => rewrite id; clear id end;
   easy.

Ltac assert_LHS F  :=
  match goal with
  | |- ?L = _ =>
    let name := fresh "temp_for_assert_LHS" in
     assert (name: L = F);[ | rewrite name; clear name]
  end.

Lemma sin0 : sin 0 = 0.
Proof.
assert_LHS ((sin 0 + sin 0) / 2).
  now field.
assert_LHS ((sin (-0) + sin 0) / 2).
  now replace (-0) with 0 by ring.
assert_LHS ((- sin 0 + sin 0) / 2).
  now rewrite par_sin.
now field.
Qed.
