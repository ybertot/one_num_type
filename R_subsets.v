Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.

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

Example test_Rnat_proof x : Rnat x -> Rnat ((x + 2) * x).
Proof. exact _. Qed.

(* TODO: this command is not very principled.  *)
Ltac solve_Rnat :=
  exact _ || (repeat match goal with
  |- Rnat ?x => ring_simplify x
  end;
  try exact _).

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

Lemma Rpow_succ x a : Rnat a -> x ^ (a + 1) = x ^ a * x.
Proof.
intros anat.
rewrite Rpow_add; auto; try exact _.
now rewrite Rpow1.
Qed.

Lemma Rpow_convert_Z n m :
  Rpow n (IZR m) = pow n (Z.abs_nat m).
Proof.
now unfold Rpow; rewrite IRN_IZR.
Qed.

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
    (match goal with 
      |- context [Rpow ?x (IZR (Z.pos ?n))] =>
      let nN := constr:(Z.abs_nat (Z.pos n)) in
      let v := eval compute in nN in
        replace (Rpow x (IZR (Z.pos n))) with (pow x v);
         [ | rewrite (Rpow_convert_Z x (Z.pos n)); easy]
    | |- context [Rpow ?x (IZR Z0)] =>
         replace (Rpow x (IZR Z0)) with 1;
         [ | rewrite Rpow0]
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

(* This is only needed as long as the correction to preprocessing
  bugs has not been incorporated into the released version of the
  system (up to coq 8.20).  The code here is duplicated from the
  code in the fix. *)
Add Ring RRing_w_Rpow : RTheory
  (morphism R_rm, constants [IZR_tac], preprocess [to_pow],
    postprocess [from_pow], power_tac R_power_theory [Rpow_tac]).

Ltac Field_simplify_gen f FLD lH rl :=
  let l := fresh "to_rewrite" in
  pose (l:= rl);
  generalize (eq_refl l);
  unfold l at 2;
  get_FldPre FLD ();
  let rl :=
    match goal with
    | [|- l = ?RL -> _ ] => RL
    | _ => fail 1 "ring_simplify anomaly: bad goal after pre"
    end in
  let Heq := fresh "Heq" in
  intros Heq;clear Heq l;
  Field_norm_gen f ring_subst_niter FLD lH rl;
  get_FldPost FLD ().

Ltac Field_simplify :=
  Field_simplify_gen ltac:(fun H => rewrite H).

Tactic Notation (at level 0) "field_simplify" constr_list(rl) :=
  let G := Get_goal in
  field_lookup (PackField Field_simplify) [] rl G.

(* End of fix code for field_simplify. *)

Example test_ring3 n : n ^ 3 + 3 * n ^ 2 + 3 * n + 1 = (n + 1) ^ 3.
Proof.
field_simplify ((n + 1) ^ 3).
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

(* sequences of natural numbers and big operators *)
(* It is sensible that students see the primitives used to program
  recursively on lists, so this definition may be part of the visible
  interface.  Otherwise, we could decide to only have big operations. *)
Fixpoint rlength {A : Type} (l : list A) : R :=
  match l with
  | nil => 0
  | a :: l => 1 + rlength l
  end.

(* Ideally all theorems about the length of lists and its interactions with
   map, filter, app, etc. should be made available to the students.  The
   following theorem is a tool for that, but it is not for the students' eyes. *)

Lemma rlength_nat {A : Type} (l : list A) : rlength l = INR (length l).
Proof.
induction l as [ | a l Ih]; auto.
cbn [rlength length]; rewrite S_INR; ring [Ih].
Qed.

Definition Rseq (n m : R) :=
  map (fun x => n + INR x) (seq 0 (IRN m)).

Lemma rlength_Rseq x y : Rnat y -> rlength (Rseq x y) = y.
Proof.
intros ynat.
rewrite rlength_nat; unfold Rseq.
now rewrite length_map, length_seq, INR_IRN.
Qed.

Lemma Rseq0 (n : R) : Rseq n 0 = nil.
Proof.
now unfold Rseq; rewrite IRN0.
Qed.

Lemma Rseq1 (n : R) : Rseq n 1 = n :: nil.
Proof.
unfold Rseq; rewrite IRN1; simpl; apply (f_equal (fun x => x :: nil)); ring.
Qed.

Lemma seq_shift_add (n l m : nat) : seq (n + l) m =
  map (fun x => Nat.add x l) (seq n m).
Proof.
revert n l; induction m as [ | m Ih].
  easy.
intros n l; simpl; apply f_equal.
replace (S (n + l))%nat with ((S n) + l)%nat by ring.
now apply Ih.
Qed.

(* This is a workhorse, making it possible to chip off elements at each
  extremity, or to cut a big sequence in the middle. *)
Lemma Rseq_add (n l m : R) :
  Rnat l -> Rnat m -> Rseq n (l + m) = Rseq n l ++ Rseq (n + l) m.
Proof.
intros lnat mnat.
unfold Rseq.
rewrite IRN_add; auto.
rewrite seq_app, map_app.
apply f_equal.
rewrite seq_shift_add, map_map.
apply map_ext.
intros a; rewrite plus_INR, INR_IRN; auto; ring.
Qed.

Lemma Rseq_S (n m : R) {mnat : Rnat m} :
  Rseq n (m + 1) = n :: (Rseq (n + 1) m).
Proof.
now rewrite Rplus_comm; rewrite Rseq_add, Rseq1; try typeclasses eauto.
Qed.

Lemma Rseq_S' (n m : R) {m'nat : Rnat (m - 1)} :
  Rseq n m = n :: Rseq (n + 1) (m - 1).
Proof.
replace m with (1 + (m - 1)) at 1 by ring.
rewrite Rseq_add; try typeclasses eauto.
now rewrite Rseq1.
Qed.

Notation "[ '0 <..> m ]"  := (Rseq 0 m).

Example seq03 : ['0 <..> 3] = 0 :: 1 :: 2 :: nil.
Proof.
unfold Rseq; rewrite IRN_pos; simpl.
replace (0 + 0) with 0 by ring.
replace (0 + 1) with 1 by ring.
replace (0 + (1 + 1)) with 2 by ring.
easy.
Qed.

Definition Rbigop [A : Type] (f : A -> A -> A) (idf : A)
  (a b : R) (E : R -> A) :=
  fold_right f idf (map E (Rseq a (b - a))).

Notation "\big[ f / idf ]_( a <= i < b ) E" :=
  (Rbigop f idf a b (fun i => E))
  (at level 35, a at level 30, b at level 30, E at level 36, f, idf
   at level 10, i at level 0, right associativity).

Notation "\sum_ ( a <= i < b ) E" :=
  (Rbigop Rplus (IZR 0) a b (fun i => E))
  (at level 35, a at level 30,  b at level 30, E at level 36,
  i at level 0, right associativity,
   format "'[' \sum_ ( a  <=  i  <  b ) '/  '  E ']'").

Notation "\prod _( a <= i < b ) E" :=
  (Rbigop Rmult 1 a b (fun i => E))
  (at level 35, a at level 30,  b at level 30, E at level 36,
  i at level 0, right associativity).


Lemma big0 {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a : R) :
  \big[f / idx]_(a <= i < a) E i = idx.
Proof.
now unfold Rbigop; rewrite Rminus_diag, Rseq0.
Qed.

Lemma big_recl {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a b : R)
  {hnat : Rnat (b - a)} : a < b ->
  \big[f / idx]_(a <= i < b) E i =
   f (E a) (\big[f / idx]_((a + 1) <= i < b) E i).
Proof.
intros altb.
unfold Rbigop.
rewrite Rseq_S'; [ | apply Rnat_sub; try typeclasses eauto]; simpl.
  replace (b - a - 1) with (b - (a + 1)) by ring.
  easy.
replace 1 with (0 + 1) by ring; apply Rnat_le_lt; try typeclasses eauto.
lra.
Qed.

Definition associative_monoid {A : Type} (f : A -> A -> A) (idx : A) :=
  (forall x y z, f x (f y z) = f (f x y) z) /\
   (forall x, f x idx = x) /\
   (forall x, f idx x = x).

Lemma big_recr {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a b : R) :
  associative_monoid f idx ->
  Rnat (b - a) -> a < b ->
  \big[f / idx]_(a <= i < b) E i =
   f (\big[f / idx]_(a <= i < (b - 1)) E i)
    (E (b - 1)).
Proof.
intros amf hnat altb.
unfold Rbigop.
assert (induct_arg : Rnat (b - a  - 1)).
  apply Rnat_sub; try typeclasses eauto;
      apply Rnat_gt_pred; try typeclasses eauto; lra.
enough (main : forall p, Rnat p ->
  forall a, fold_right f idx (map (fun i => E i) (Rseq a (p + 1))) =
   f (fold_right f idx (map (fun i => E i) (Rseq a p))) (E (a + p))).
  replace (b - a) with (b - a - 1 + 1) by ring.
  rewrite main; auto.
  replace (a + (b - a - 1)) with (b - 1) by ring.
  now replace (b - 1 - a) with (b - a - 1) by ring.
clear hnat altb induct_arg a.
intros p'; induction 1 as [ | p pnat Ih] using Rnat_ind.
  intros a; rewrite Rplus_0_l, Rplus_0_r, Rseq0, Rseq1; simpl.
  now destruct amf as [_ [P1 P2]]; rewrite P1, P2.
intros a; rewrite Rseq_S; try typeclasses eauto; simpl.
rewrite (Rseq_S a); auto; simpl.
destruct amf as [Pa [P1 P2]].
now rewrite Ih, Pa; replace (a + (p + 1)) with (a + 1 + p) by ring.
Qed.

Lemma big1 {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a : R)
  {mf : associative_monoid f idx} :
  \big[f / idx]_(a <= i < a + 1) E i = E a.
Proof.
rewrite big_recl, big0.
    now destruct mf as [_ [it _]]; rewrite it.
  now replace (a + 1 - a) with 1 by ring; exact _.
lra.
Qed.

Lemma associative_monoid_Rplus : associative_monoid Rplus 0.
Proof.
split;[exact (fun x y z => eq_sym (Rplus_assoc x y z))| ].
split;[exact Rplus_0_r | exact Rplus_0_l].
Qed.

#[export]
Hint Resolve associative_monoid_Rplus : core.

Lemma associative_mul : associative_monoid Rmult 1.
Proof.
split.
  exact (fun x y z => eq_sym (Rmult_assoc x y z)).
split.
  exact Rmult_1_r.
exact Rmult_1_l.
Qed.

#[export]
Hint Resolve associative_mul : core.

Existing Class associative_monoid.
Existing Instances associative_monoid_Rplus associative_mul.

Lemma sum0 (E : R -> R) (a : R) : \sum_(a <= i < a) E i = 0.
Proof. now apply big0. Qed.

Lemma sum1 (E : R -> R) (a : R) : \sum_(a <= i < a + 1) E i = E a.
Proof. now apply big1. Qed.

Lemma prod1 (E : R -> R) (a : R) : \prod_(a <= i < a + 1) E i = E a.
Proof. now apply big1. Qed.

Lemma sum_recr (E : R -> R) (a b : R) :
  Rnat (b - a) -> a < b ->
  \sum_(a <= i < b) E i =
   (\sum_(a <= i < (b - 1)) E i) + E (b - 1).
Proof.
apply big_recr; auto.
Qed.

Lemma prod_recr (E : R -> R) (a b : R) :
  Rnat (b - a) -> a < b ->
  \prod_(a <= i < b) E i =
   (\prod_(a <= i < (b - 1)) E i) * E (b - 1).
Proof.
apply big_recr; auto.
Qed.

Lemma big_add (f g : R -> R) (b n : R) : Rnat (n - b) ->
  \sum_(b <= i < n) f i +
  \sum_(b <= i < n) g i = 
  \sum_(b <= i < n) (f i + g i).
Proof.
unfold Rbigop.
generalize (n - b); intros k knat; revert b.
induction knat as [ | k knat Ih]; intros b.
  rewrite Rseq0; simpl; ring.
rewrite Rseq_S'; replace (k + 1 - 1) with k by ring; auto.
simpl.
rewrite <- Ih; ring.
Qed.

Lemma big_distr (f : R -> R) (b n a : R) : Rnat (n - b) ->
  a * \sum_(b <= i < n) f i =
  \sum_(b <= i < n) (a * f i).
Proof.
unfold Rbigop.
generalize (n - b); intros k knat; revert b.
induction knat as [ | k knat Ih]; intros b.
   rewrite Rseq0; simpl; ring.
rewrite Rseq_S'; replace (k + 1 - 1) with k by ring; auto.
simpl.
rewrite <- Ih; ring.
Qed.

Lemma big_shift {A : Type} (op : A -> A -> A) v
 (f : R -> A) (b k n : R) : Rnat (n - b) ->
  \big[op/v]_(b <= i < n) (f (i + k)) =
  \big[op/v]_((b + k) <= i < (n + k)) (f i).
Proof.
unfold Rbigop.
replace (n + k - (b + k)) with (n - b) by ring.
generalize (n - b); intros l lnat; revert b.
induction lnat as [ | l lnat Ih]; intros b.
  now rewrite !Rseq0.
rewrite !Rseq_S; auto.
simpl; rewrite Ih.
now replace (b + 1 + k) with (b + k + 1) by ring.
Qed.

Lemma big_ext {A : Type} (op : A -> A -> A) v (f g : R -> A)
  (b n : R) : Rnat (n - b) ->
  (forall x, Rnat x -> 0 <= x < n - b -> f (b + x) = g (b + x)) ->
  \big[op/v]_(b <= i < n) f i =
  \big[op/v]_(b <= i < n) g i.
Proof.
unfold Rbigop.
generalize (n - b); intros l lnat; revert b.
induction lnat as [ | l lnat Ih]; intros b eq_cnd.
  now rewrite Rseq0.
rewrite Rseq_S; auto; simpl.
replace b with (b + 0) at 1 3 by ring.
rewrite eq_cnd; cycle 1.
    try typeclasses eauto.
  apply Rnat_ge0 in lnat; lra.
apply f_equal, Ih.
intros x xnat xint.
replace (b + 1 + x) with (b + (1 + x)) by ring.
apply eq_cnd.
  try typeclasses eauto.
lra.
Qed.

Lemma big_ext_low_nat {A : Type} (op : A -> A -> A) v (f g : R -> A)
  (b n : R) : Rnat b -> Rnat (n - b) ->
  (forall x, Rnat x -> b <= x < n -> f x = g x) ->
  \big[op/v]_(b <= i < n) f i =
  \big[op/v]_(b <= i < n) g i.
Proof.
intros bnat dnat eq_ext.
apply big_ext; auto.
intros x xnat xint.
apply eq_ext; solve_Rnat.
apply Rnat_ge0 in xnat.
lra.
Qed.