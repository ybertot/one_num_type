Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.

Open Scope R_scope.

Module Type MyIZR_type.

Parameter IZR : Z -> R.

Axiom eq : IZR = Rdefinitions.IZR.

End MyIZR_type.

Module MyIZR : MyIZR_type.

Definition IZR := Rdefinitions.IZR.

Lemma eq : IZR = Rdefinitions.IZR.
Proof. reflexivity. Qed.

End MyIZR.

Definition MyINR : N -> R :=
  fun n => match n with
  | N0 => 0
  | N.pos p => MyIZR.IZR (Z.pos p)
  end.
 
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

Existing Class Rint.

Existing Instance Rint1.
Existing Instance Rint_sub.
(* #[export]
Hint Resolve Rint1 Rint_sub : rnat. *)

(* We then need to have all the stability statements for the ring
  operations (we already have subtraction. *)
Instance Rint0 : Rint 0.
Proof. now replace 0 with (1 - 1) by ring; typeclasses eauto. Qed.

(* #[export]
Hint Resolve Rint0 : rnat. *)

Instance Rint_add x y  {xint : Rint x} {yint : Rint y} : Rint (x + y).
Proof. now replace (x + y) with (x - (0 - y)) by ring; typeclasses eauto. Qed.

Instance Rint_mul x y {xint : Rint x} {yint : Rint y} : Rint (x * y).
Proof.
induction xint as [ | u v Ru Ihu Rv Ihv].
  now replace (1 * y) with y by ring; auto.
replace ((u - v) * y) with ((u * y) - (v * y)) by ring.
now typeclasses eauto.
Qed.

(* #[export]
Hint Resolve Rint_add Rint_mul : rnat. *)

Instance Rint_opp x {xint : Rint x} : Rint (- x).
Proof. replace (-x) with (0 - x) by ring; typeclasses eauto. Qed.

(* 2 will later be covered by a more general theorem, but we need a
  special lemma to prove that general theorem. *)
Instance Rint2 : Rint 2.
Proof.  now replace 2 with (1 + 1) by ring; typeclasses eauto. Qed.

(* #[export]
Hint Resolve Rint2 : rnat. *)

Instance Rint_abs p {pint : Rint p} : Rint (Rabs p).
Proof.
destruct (Rle_or_gt 0 p).
  rewrite Rabs_right;[easy | lra].
rewrite Rabs_left;[typeclasses eauto | lra].
Qed.

Instance Rint_pos p : Rint (IZR (Z.pos p)).
Proof.
induction p as [ p' Ih | p' Ih | ].
    now rewrite Pos2Z.inj_xI, plus_IZR, mult_IZR; typeclasses eauto.
  now rewrite Pos2Z.inj_xO, mult_IZR; typeclasses eauto.
now typeclasses eauto.
Qed.

(* #[export]
Hint Resolve Rint_pos : rnat. *)

Lemma Rint_neg p : Rint (IZR (Z.neg p)).
Proof.
replace (IZR (Z.neg p)) with (IZR (Z.opp (Z.pos p))) by easy.
rewrite opp_IZR.
replace (- IZR (Z.pos p)) with (0 - IZR (Z.pos p)) by ring.
typeclasses eauto.
Qed.

(* #[export]
Hint Resolve Rint_neg : rnat. *)

(* This is the general theorem that covers all numbers, even 0, 1, and 2
  which are already provided by more elementary proofs.
  The full general form of this theorem should not really be put in
  front of the eyes of beginners, but its specialization to ground
  constants like 1, 32, or 45 is useful (see the example below). *)

Instance Rint_Z x : Rint (IZR x).
Proof.
now destruct x as [ | p | p]; typeclasses eauto.
Qed.

(* #[export]
Hint Resolve Rint_Z : rnat. *)

Example Rint_big : Rint 1043.
Proof. now typeclasses eauto. Qed.

(* This lemma is not for the beginners, because it mentions the type
  Z explicitely. *)
Lemma Rint_exists_Z x  {xint : Rint x} : exists z, x = IZR z.
Proof.
induction xint as [ | u v Ru Ihu Rv Ihv].
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
Lemma Rint_le_lt x y {xint : Rint x}{yint : Rint y} :  x < y -> x + 1 <= y.
Proof.
destruct (Rint_exists_Z x) as [z xz].
destruct (Rint_exists_Z y) as [u yu].
rewrite xz, yu.
intros zu; apply lt_IZR in zu.
rewrite <- plus_IZR; apply IZR_le; lia.
Qed.

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

Lemma IRZ_add n m {nint : Rint n} {mint : Rint m} :
   IRZ (n + m) = (IRZ n + IRZ m)%Z.
Proof.
destruct (Rint_exists_Z n) as [n' nn'].
destruct (Rint_exists_Z m) as [m' mm'].
now rewrite nn', mm', <- plus_IZR, !IRZ_IZR.
Qed.

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall x, Rnat x -> Rnat (x + 1).

Existing Class Rnat.

Lemma Rnat_Rint x {xint : Rnat x} : Rint x /\ 0 <= x.
Proof.
induction xint as [ | y ynat [yint yge0]].
  now split; try typeclasses eauto.
split; try typeclasses eauto; lra.
Qed.

Instance Rnat_Rintw x (xnat : Rnat x) : Rint x.
Proof. now destruct (Rnat_Rint x). Qed.

Lemma Rint_Rnat x {xint : Rint x} : 0 <= x -> Rnat x.
Proof.
intros xge0.
destruct (Rint_exists_Z x) as [x' px].
assert (x'ge0 : (0 <= x')%Z).
  now apply le_IZR; rewrite <- px.
assert (x'n : x' = Z.of_nat (Z.abs_nat x')).
  now rewrite Nat2Z.inj_abs_nat, Z.abs_eq.
rewrite px, x'n.
generalize (Z.abs_nat x'); intros n.
induction n.
  exact Rnat0.
replace (S n) with (n + 1)%nat by ring.
rewrite Nat2Z.inj_add.
rewrite plus_IZR.
now apply Rnat_succ.
Qed.

Lemma Rnat_ge0 x : Rnat x -> 0 <= x.
Proof.
induction 1; lra.
Qed.

Lemma Rnat_INR n : Rnat (INR n).
Proof. 
apply Rint_Rnat.
  now rewrite INR_IZR_INZ; apply Rint_Z.
now apply pos_INR.
Qed.

Instance Rnat_cst x : Rnat (IZR (Z.pos x)).
Proof. apply Rint_Rnat;[apply Rint_Z | apply IZR_le; lia]. Qed.

Existing Instances Rnat0 Rnat_succ Rnat_cst.

Instance Rnat_add x y {xnat : Rnat x} {ynat : Rnat y} : Rnat (x + y).
Proof.
induction xnat as [ | x xnat Ih].
  now rewrite Rplus_0_l.
replace (x + 1 + y) with (x + y + 1) by ring.
apply Rnat_succ.
now apply Ih.
Qed.

Instance Rnat_mul x y {xnat : Rnat x} {ynat : Rnat y} : Rnat (x * y).
Proof.
induction xnat as [ | x xnat Ih].
  now rewrite Rmult_0_l; intros; apply Rnat0.
replace ((x + 1) * y) with (x * y + y) by ring.
typeclasses eauto.
Qed.

Instance Rnat_abs x {xint: Rint x} : Rnat (Rabs x).
Proof.
apply Rint_Rnat;[ | apply Rabs_pos].
typeclasses eauto.
Qed.

Lemma Rnat_sub x y {xnat : Rnat x} {ynat : Rnat y} : y <= x -> Rnat (x - y).
Proof.
intros ylex.
destruct (Rnat_Rint x) as [xint xge0].
destruct (Rnat_Rint y) as [yint yge0].
apply Rint_Rnat; [ typeclasses eauto | lra].
Qed.

From elpi Require Import elpi.
Elpi Tactic solve_Rnat.
Elpi Accumulate lp:{{

:index (8) % ask davide
pred proof i:term, o:term.

proof {{ Rnat 0 }} {{ Rnat0 }}.
proof {{ Rnat (lp:N + 1) }} {{ @Rnat_succ lp:N lp:P }} :-
  proof {{ Rnat lp:N }} P.
proof {{ Rnat (IZR (Z.pos lp:X)) }} {{ @Rnat_cst lp:X }}.
proof {{ Rnat (INR lp:N) }} {{ @Rnat_INR lp:N }}.
proof {{ Rnat (lp:X + lp:Y) }} {{ @Rnat_add lp:X lp:Y lp:PX lp:PY }} :-
  proof {{ Rnat lp:X }} PX,
  proof {{ Rnat lp:Y }} PY.
proof {{ Rnat (lp:X * lp:Y) }} {{ @Rnat_mul lp:X lp:Y lp:PX lp:PY }} :-
  proof {{ Rnat lp:X }} PX,
  proof {{ Rnat lp:Y }} PY.
proof {{ Rnat (Rabs lp:X) }} {{ @Rnat_abs lp:X lp:PX }} :-
  proof {{ Rint lp:X }} PX.
proof {{ Rnat (lp:X - lp:Y) }} {{ @Rnat_sub lp:X lp:Y lp:PX lp:PY lp:PXY }} :-
  proof {{ Rnat lp:X }} PX,
  proof {{ Rnat lp:Y }} PY,
  proof {{ lp:Y <= lp:X }} PXY.

% this is a bit silly since the only entrypoint already knows X is Rnat
proof {{ 0 <= lp:X }} {{ @Rnat_ge0 lp:X lp:PX }} :- proof {{ Rnat lp:X }} PX.

proof {{ Rint 0 }} {{ Rint0 }}.
proof {{ Rint 1 }} {{ Rint1 }}.
proof {{ Rint 2 }} {{ Rint2 }}.
proof {{ Rint (lp:X - lp:Y) }} {{ @Rint_sub lp:X lp:Y lp:PX lp:PY }} :-
  proof {{ Rint lp:X }} PX,
  proof {{ Rint lp:Y }} PY.
proof {{ Rint (lp:X + lp:Y) }} {{ @Rint_add lp:X lp:Y lp:PX lp:PY }} :-
  proof {{ Rint lp:X }} PX,
  proof {{ Rint lp:Y }} PY.
proof {{ Rint (lp:X * lp:Y) }} {{ @Rint_mul lp:X lp:Y lp:PX lp:PY }} :-
  proof {{ Rint lp:X }} PX,
  proof {{ Rint lp:Y }} PY.
proof {{ Rint (IZR lp:X) }} {{ @Rint_Z lp:X }}.
proof {{ Rint (Rabs lp:X) }} {{ @Rint_abs lp:X lp:PX }} :-
  proof {{ Rint lp:X }} PX.
proof {{ Rint (- lp:X) }} {{ @Rint_opp lp:X lp:PX }} :-
  proof {{ Rint lp:X }} PX.
proof {{ Rint lp:X }} {{ Rnat_Rintw lp:X lp:PX }} :-
  proof {{ Rnat lp:X }} PX.

pred compile-ctx i:goal-ctx, o:list prop.
compile-ctx [] [].
compile-ctx [decl H _ P |L] [(proof P H :- !)|L'] :- compile-ctx L L'.
compile-ctx [def H _ P _|L] [(proof P H :- !)|L'] :- compile-ctx L L'.

pred find-proof i:goal-ctx, i:term, o:term.
find-proof C A P :-
  compile-ctx C Rules,
  Rules => proof A P, !.
find-proof _ A _ :-
  coq.ltac.fail _ {calc ("Cannot prove" ^ {coq.term->string A})}.

solve (goal Ctx _ ({{ Rnat _ }} as Ty) _ _ as G) GL :-
  find-proof Ctx Ty P,
  std.assert! (refine P G GL) "bad proof".
solve (goal _ _ Ty _ _) _ :-
  coq.ltac.fail _  {calc ("Goal outside tactic domain:" ^ {coq.term->string Ty})}.

}}.
Elpi Typecheck.

(*
Hint Resolve Rnat_add Rnat_mul : rnat. *)
(* Ltac solve_Rnat := try typeclasses eauto. *)
Ltac solve_Rnat := try elpi solve_Rnat.

(* Order properties for natural numbers. *)

Lemma Rnat_le_lt x y {xnat : Rnat x}{ynat : Rnat y} : x < y -> x + 1 <= y.
Proof.
intros xlty; apply Rint_le_lt; auto.
  now destruct (Rnat_Rint x).
now destruct (Rnat_Rint y).
Qed.

Lemma Rnat_gt_pred (x y : R) {xnat : Rnat x}{ynat : Rnat y} :
  x - 1 < y -> x <= y.
Proof.
intros xlty.
induction xnat as [ | x' x'nat _].
  now apply Rnat_ge0.
apply Rnat_le_lt; try typeclasses eauto.
lra.
Qed.

Lemma Rnat_exists_nat x {xnat : Rnat x} : exists n, x = IZR (Z.of_nat n).
Proof.
induction xnat as [ | x xnat [n xn]].
  exists 0%nat; easy.
exists (S n).
now rewrite Nat2Z.inj_succ, <- Z.add_1_r, plus_IZR, xn.
Qed.

(* The function IRN is only a tool for expert.  It should not be seen
  by students. *)
Definition IRN (x : R) := Z.abs_nat (IRZ x).

Lemma INR_IRN x {xnat : Rnat x} : INR (IRN x) = x.
Proof.
destruct (Rnat_exists_nat x) as [x' xx'].
rewrite xx'.
unfold IRN.
rewrite IRZ_IZR.
rewrite INR_IZR_INZ.
now rewrite Zabs2Nat.id.
Qed.

Lemma IRN0 : IRN 0 = 0%nat.
Proof.
now unfold IRN; rewrite IRZ_IZR.
Qed.

Lemma IRN1 : IRN 1 = 1%nat.
Proof.
now unfold IRN; rewrite IRZ_IZR.
Qed.

Lemma IRN2 : IRN 2 = 2%nat.
Proof.
now unfold IRN; rewrite IRZ_IZR.
Qed.

Lemma IRN_IZR z : IRN (IZR z) = Z.abs_nat z.
Proof. now unfold IRN; rewrite IRZ_IZR. Qed.

Lemma IRN_pos p : IRN (IZR (Z.pos p)) = Pos.to_nat p.
Proof. now rewrite IRN_IZR, Zabs2Nat.inj_pos. Qed.

Example IRN_42 : IRN 42 = 42%nat.
Proof. now rewrite IRN_pos. Qed.

Lemma IRN_add n m : 
Rnat n -> Rnat m -> IRN (n + m) = (IRN n + IRN m)%nat.
Proof.
intros nnat mnat.
destruct (Rnat_Rint n) as [nint nge0].
destruct (Rnat_Rint m) as [mint mge0].
unfold IRN; rewrite IRZ_add; auto.
rewrite Zabs2Nat.inj_add; auto; apply le_IZR.
  destruct (Rint_exists_Z n) as [n' nn'].
  now rewrite nn' in nge0 |- *; rewrite IRZ_IZR.
destruct (Rint_exists_Z m) as [m' mm'].
now rewrite mm' in mge0 |- *; rewrite IRZ_IZR.
Qed.

Definition Rpow (x y : R) := pow x (IRN y).

Lemma Rpow_pre_ring x y : Rpow x (IZR y) = Rpow x (MyIZR.IZR y).
Proof. rewrite MyIZR.eq; easy. Qed.

#[local]
Set Warnings "-notation-overridden".

Disable Notation "^" := pow.

Notation "x ^ y" := (Rpow x y) : R_scope.

#[local]
Set Warnings "+notation-overridden".

Lemma Rpow0 x : x ^ 0 = 1.
Proof.  unfold Rpow; rewrite IRN0, pow_O; easy. Qed.

Lemma Rpow1 x : x ^ 1 = x.
Proof.  unfold Rpow; rewrite IRN1, pow_1; easy. Qed.

Lemma Rpow_add x a b : 
  Rnat a -> Rnat b -> x ^ (a + b) = x ^ a * x ^ b.
Proof.
intros anat bnat.
unfold Rpow; rewrite IRN_add, pow_add; easy.
Qed.

Lemma Rpow_convert_Z n m :
  Rpow n (IZR m) = pow n (Z.abs_nat m).
Proof.
now unfold Rpow; rewrite IRN_IZR.
Qed.

Definition R_p_t : power_theory 1 Rmult (@eq R)
  MyINR Rpow.
constructor.
destruct n.
  simpl.
  now rewrite Rpow_convert_Z.
unfold MyINR; rewrite MyIZR.eq.
rewrite Rpow_convert_Z.
change (Z.abs_nat (Z.pos p)) with (N.to_nat (N.pos p)).
now destruct R_power_theory as [ it]; apply it.
Qed.

Ltac Rpow_tac1 t :=
  match t with
  | MyIZR.IZR Z0 => N0
  | MyIZR.IZR (Z.pos ?p) =>
    match isPcst p with
    | true => constr:(N.pos p)
    | false => constr:(InitialRing.NotConstant)
    end
  | _ => constr:(InitialRing.NotConstant)
  end.

Example test_ring n :  pow n 3 + 3 * pow n 2 + 3 * n + 1 =
  pow (n + 1) 3.
Proof. ring_simplify. easy. Qed.

(* The following example shows that Rpow is not handled by ring. *)
Example test_ring2 n : n ^ 3 + 3 * n ^ 2 + 3 * n + 1 =
  (n + 1) ^ 3.
Proof.
Fail ring.
rewrite !Rpow_convert_Z.
repeat (match goal with |- context[Z.abs_nat ?n] =>
          let v := eval compute in (Z.abs_nat n) in
            change (Z.abs_nat n) with v
end).
ring_simplify.
easy.
Qed.

Ltac to_pow :=
  repeat
    (match goal with |- context [Rpow ?x (IZR (Z.pos ?n))] =>
      let nN := constr:(Z.abs_nat (Z.pos n)) in
      let v := eval compute in nN in
        replace (Rpow x (IZR (Z.pos n))) with (pow x v);
         [ | rewrite (Rpow_convert_Z x (Z.pos n)); easy]
    end).

Ltac from_pow :=
  repeat
    (match goal with |- context [pow ?x ?n] =>
      let nZ := constr:(Z.of_nat n) in
      let v := eval compute in nZ in
        replace (pow x n) with (Rpow x (IZR v));
         [ | rewrite (Rpow_convert_Z x v); easy]
    end).

(* Adding preprocessing and post processing to leverage the knowledge
  of pow.*)
Add Field RField_w_Rpow : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac],
    preprocess [to_pow],
    postprocess [from_pow], power_tac R_power_theory [Rpow_tac]).

Add Ring RRing_w_Rpow : RTheory
  (morphism R_rm, constants [IZR_tac], preprocess [to_pow],
    postprocess [from_pow], power_tac R_power_theory [Rpow_tac]).

Example test_ring3 n : n ^ 3 + 3 * n ^ 2 + 3 * n + 1 = (n + 1) ^ 3.
Proof.
Fail progress field_simplify ((n + 1) ^ 3).
to_pow.
field_simplify.
easy.
Qed.

Lemma Rpow_nonzero n m : Rnat m ->
  n <> 0 -> Rpow n m <> 0.
Proof.
intros mnat nn0; unfold Rpow.
now apply pow_nonzero.
Qed.

(* I don't know if this is important. *)
Lemma IRN_succ n : Rnat n -> IRN (n + 1) = S (IRN n).
Proof.
now intros nnat; rewrite IRN_add, IRN1, Nat.add_1_r; try typeclasses eauto.
Qed.

Lemma IRN_INR (n : nat) : IRN (INR n) = n.
Proof.
unfold IRN.
now rewrite INR_IZR_INZ, IRZ_IZR, Zabs2Nat.id.
Qed.

Definition Rnat_rec {A : Type} (v0 : A) (stf : R -> A -> A) (x : R) : A :=
  nat_rect (fun _ => A) v0 (fun x => stf (INR x)) (IRN x).

Lemma Rnat_rec0 {A : Type} (v0 : A) stf : Rnat_rec v0 stf 0 = v0.
Proof.
now unfold Rnat_rec, IRN; rewrite IRZ_IZR.
Qed.

Lemma Rnat_rec_succ {A : Type} (v0 : A) stf (x : R) :
  Rnat x ->
  Rnat_rec v0 stf (x + 1) = stf x (Rnat_rec v0 stf x).
Proof.
intros xnat.
destruct (Rnat_exists_nat x) as [x' xx'].
unfold Rnat_rec.
replace (IRN (x + 1)) with (S (IRN x)).
  now simpl; rewrite INR_IRN.
rewrite xx'.
unfold IRN.
rewrite <- plus_IZR.
rewrite !IRZ_IZR.
replace 1%Z with (Z.of_nat 1) by (simpl; ring).
rewrite <- Nat2Z.inj_add.
rewrite !Zabs2Nat.id.
ring.
Qed.

Lemma Rnat_IZR_nneg n: Rnat n -> (0 <= IRZ n)%Z.
Proof.
intros nnat.
destruct (Rnat_exists_nat n) as [n' nq].
rewrite nq, IRZ_IZR.
now apply Nat2Z.is_nonneg.
Qed.

Lemma course_of_value_induction (P : R -> Prop) :
  (forall y, Rnat y -> (forall x, Rnat x -> (x < y) -> P x) -> P y) ->
  (forall n, Rnat n -> P n).
Proof.
intros Ih n nnat.
enough (main : forall m, (m <= n) -> Rnat m -> P m).
  now apply main; [apply Rle_refl | assumption].
induction nnat as [ | n nat Ihn].
intros m mle0 mnat.
assert (mge0 : 0 <= m) by now apply Rnat_ge0.
assert (m0 : m = 0) by lra.
rewrite m0.
  apply Ih.
    typeclasses eauto.
  intros x xnat xlt0.
  assert (xge0 : 0 <= x) by now apply Rnat_ge0.
  lra.
intros m mlen1 mnat.
destruct (Rle_lt_or_eq _ _ mlen1) as [mltn1 | meqn1]; cycle 1.
  apply Ih; [assumption | ].
  intros x xnat xltm.
  assert (tmp := Rnat_le_lt x m xltm).
  apply Ihn;[ | assumption].
  lra.
assert (tmp := Rnat_le_lt m (n + 1) mltn1).
apply Ihn;[ | assumption].
lra.
Qed.

(* Properties of the square root function. *)

Lemma sqrt0 : sqrt 0 = 0.
Proof. replace 0 with (0 * 0) by ring; rewrite sqrt_square; lra. Qed.

Lemma sqrt1 : sqrt 1 = 1.
Proof. replace 1 with (1 * 1) by ring; rewrite sqrt_square; lra. Qed.

Lemma pow_2_expand x : x ^ 2 = x * x.
Proof.
replace 2 with (1 + 1) by ring.
rewrite Rpow_add; solve_Rnat.
now rewrite Rpow1.
Qed.

Lemma pow_2_sqrt x : 0 <= x -> sqrt x ^ 2 = x.
Proof.
now intros xpos; rewrite pow_2_expand, sqrt_sqrt.
Qed.

Lemma sqrt_pow_2 x : 0 <= x -> sqrt (x ^ 2) = x.
Proof.
intros xpos.
replace (x ^ 2) with (x * x) by ring.
rewrite sqrt_square; lra.
Qed.

(* Upon inspection of the type, this lemma makes the positive number type
  visible.  So it may not be that good after all.  In particular, it
  it is unclear how this lemma should be documented. *)
Lemma sqrt_pos_Z x : 0 < sqrt (IZR (Z.pos x)).
Proof.
apply sqrt_lt_R0.
now apply IZR_lt.
Qed.
