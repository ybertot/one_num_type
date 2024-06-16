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

#[export]
Hint Resolve Rint1 Rint_sub : rnat.

(* We then need to have all the stability statements for the ring
  operations (we already have subtraction. *)
Lemma Rint0 : Rint 0.
Proof. now replace 0 with (1 - 1) by ring; auto with rnat. Qed.

#[export]
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

#[export]
Hint Resolve Rint_add Rint_mul : rnat.

Lemma Rint_opp x : Rint x -> Rint (- x).
Proof. intros xint; replace (-x) with (0 - x) by ring; auto with rnat. Qed.

(* 2 will later be covered by a more general theorem, but we need a
  special lemma to prove that general theorem. *)
Lemma Rint2 : Rint 2.
Proof.  now replace 2 with (1 + 1); auto with rnat. Qed.

#[export]
Hint Resolve Rint2 : rnat.

Lemma Rint_pos p : Rint (IZR (Z.pos p)).
Proof.
induction p as [ p' Ih | p' Ih | ].
    now rewrite Pos2Z.inj_xI, plus_IZR, mult_IZR; auto with rnat.
  now rewrite Pos2Z.inj_xO, mult_IZR; auto with rnat.
auto with rnat.
Qed.

#[export]
Hint Resolve Rint_pos : rnat.

Lemma Rint_neg p : Rint (IZR (Z.neg p)).
Proof.
replace (IZR (Z.neg p)) with (IZR (Z.opp (Z.pos p))) by easy.
rewrite opp_IZR.
replace (- IZR (Z.pos p)) with (0 - IZR (Z.pos p)) by ring.
auto with rnat.
Qed.

#[export]
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

#[export]
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

Module alternative_Rint.

Definition Rint (x : R) : Prop := exists z, x = IZR z.

Lemma Rint_Z (z : Z) : Rint (IZR z).
Proof. now exists z. Qed.

Lemma Rint0 : Rint 0.
Proof. now apply Rint_Z. Qed.

Lemma Rint1 : Rint 1. 
Proof. now apply Rint_Z. Qed.

Lemma Rint_sub x y : Rint x -> Rint y -> Rint (x - y).
Proof. 
now intros [x' xx'] [y' yy']; exists (x' - y')%Z; rewrite xx', yy', minus_IZR.
Qed.

Lemma Rint_ind (P : R -> Prop) (P1 : P 1)
  (Psub : forall x y, P x -> P y -> P (x - y)) :
  forall x, Rint x -> P x.
Proof.
assert (wf : well_founded (fun x y => (Z.abs_nat x < Z.abs_nat y)%nat)).
  apply wf_inverse_image.
  now apply lt_wf.
intros x [x' xx']; rewrite xx'; clear x xx'.
induction x' as [x' Ih] using (well_founded_ind wf).
destruct (Z_lt_le_dec 0 x').
  destruct (Z_lt_le_dec 1 x').
    replace x' with (1 - (1 - x'))%Z by ring.
    rewrite minus_IZR; apply Psub.
      exact P1.
    apply Ih.
    rewrite Zabs2Nat.abs_nat_spec.
    rewrite <- Z.abs_opp.
    replace (- (1 - x'))%Z with (x' - 1)%Z by ring.
    rewrite <- !Zabs2Nat.abs_nat_spec.
    apply Zabs_nat_lt.
    lia.
  replace x' with 1%Z by lia.
  now apply P1.
destruct (Z.eq_dec x' 0) as [x0 | xn0].
  replace x' with (1 - 1)%Z by (rewrite x0; ring).
  now rewrite minus_IZR; apply (Psub 1 1); auto.
replace x' with ((x' + 1) - 1)%Z by ring.
rewrite minus_IZR; apply Psub;[ | exact P1].
apply Ih.
rewrite !Zabs2Nat.abs_nat_spec.
rewrite <- Z.abs_opp, <- (Z.abs_opp x').
rewrite <- !Zabs2Nat.abs_nat_spec.
apply Zabs_nat_lt.
lia.
Qed.

End alternative_Rint.
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

Lemma IRZ_add n m : Rint n -> Rint m -> IRZ (n + m) = (IRZ n + IRZ m)%Z.
Proof.
intros nint mint.
destruct (Rint_exists_Z n nint) as [n' nn'].
destruct (Rint_exists_Z m mint) as [m' mm'].
now rewrite nn', mm', <- plus_IZR, !IRZ_IZR.
Qed.

(* We should also have an induction principle for natural numbers. *)
Lemma Rnat'_ind (P : R -> Prop) (v0 : P 0) 
  (step : forall n, Rint n -> 0 <= n -> P n -> P (n + 1)) :
  (forall n, Rint n -> 0 <= n -> P n). 
Proof.
intros n nint nge0.
destruct (Rint_exists_Z n nint) as [nz Pnz].
rewrite Pnz.
assert (nge0' : (0 <= nz)%Z).
  now apply le_IZR; rewrite <- Pnz.
assert (Pnz' : nz = Z.of_nat (Z.abs_nat nz)).
  now rewrite Nat2Z.inj_abs_nat, Z.abs_eq.
rewrite Pnz'.
generalize (Z.abs_nat nz); clear Pnz' nge0' Pnz nz.
intros n'; induction n'.
  exact v0.
replace (IZR (Z.of_nat (S n'))) with (IZR (Z.of_nat n') + 1); cycle 1.
  rewrite <- plus_IZR.
  replace 1%Z with (Z.of_nat 1) by easy.
  rewrite <- Nat2Z.inj_add.
  now rewrite Nat.add_1_r.
apply step; auto with rnat.
apply IZR_le.
apply Zle_0_nat.
Qed.

(* It turns out Rnat'_ind is cumbersome to use, so we attempt another
  inductive description of natural numbers. *)
Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall x, Rnat x -> Rnat (x + 1).

Lemma Rnat_Rint x : Rnat x -> Rint x /\ 0 <= x.
Proof.
induction 1 as [ | y ynat [yint yge0]].
  now split; auto with rnat.
split; auto with rnat; lra.
Qed.


Lemma Rint_Rnat x : Rint x -> 0 <= x -> Rnat x.
Proof.
intros xint xge0.
destruct (Rint_exists_Z x xint) as [x' px].
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

Module alternative_Rnat.

Definition Rnat x := exists n, x = INR n.

Lemma Rnat_add x y : Rnat x -> Rnat y -> Rnat (x + y).
Proof.
now intros [n xn] [m ym]; exists (n + m)%nat; rewrite xn, ym, plus_INR.
Qed.

End alternative_Rnat.

Lemma Rnat_cst x : Rnat (IZR (Z.pos x)).
Proof. apply Rint_Rnat;[apply Rint_Z | apply IZR_le; lia]. Qed.

Hint Resolve Rnat0 Rnat_succ Rnat_cst : rnat.

Lemma Rnat_add x y : Rnat x -> Rnat y -> Rnat (x + y).
Proof.
induction 1 as [ | x xnat Ih].
  now rewrite Rplus_0_l.
intros ynat.
replace (x + 1 + y) with (x + y + 1) by ring.
apply Rnat_succ.
apply Ih.
assumption.
Qed.

Lemma Rnat_mul x y : Rnat x -> Rnat y -> Rnat (x * y).
Proof.
induction 1 as [ | x xnat Ih].
  now rewrite Rmult_0_l; intros; apply Rnat0.
intros ynat; replace ((x + 1) * y) with (x * y + y) by ring.
apply Rnat_add.
  apply Ih.
  assumption.
assumption.
Qed.

Lemma Rnat_sub x y : Rnat x -> Rnat y -> y <= x -> Rnat (x - y).
Proof.
intros xnat ynat ylex.
destruct (Rnat_Rint _ xnat) as [xint xge0].
destruct (Rnat_Rint _ ynat) as [yint yge0].
apply Rint_Rnat; auto with rnat.
lra.
Qed.

Hint Resolve Rnat_add Rnat_mul : rnat.

(* Order properties for natural numbers. *)

Lemma Rnat_le_lt x y : Rnat x -> Rnat y -> x < y -> x + 1 <= y.
Proof.
intros xnat ynat xlty; apply Rint_le_lt; auto.
  now destruct (Rnat_Rint _ xnat).
now destruct (Rnat_Rint _ ynat).
Qed.

Lemma Rnat_gt_pred (x y : R) : Rnat x -> Rnat y ->
  x - 1 < y -> x <= y.
Proof.
intros xnat ynat xlty.
induction xnat as [ | x' x'nat _].
  now apply Rnat_ge0.
apply Rnat_le_lt; auto with rnat.
lra.
Qed.

Lemma Rnat_exists_nat x : Rnat x -> exists n, x = IZR (Z.of_nat n).
Proof.
induction 1 as [ | x xnat [n xn]].
  exists 0%nat; easy.
exists (S n).
now rewrite Nat2Z.inj_succ, <- Z.add_1_r, plus_IZR, xn.
Qed.

(* The function IRN is only a tool for expert.  It should not be seen
  by students. *)
Definition IRN (x : R) := Z.abs_nat (IRZ x).

Lemma INR_IRN x : Rnat x -> INR (IRN x) = x.
Proof.
intros xnat; destruct (Rnat_exists_nat _ xnat) as [x' xx'].
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

Lemma IRN_pos p : IRN (IZR (Z.pos p)) = Pos.to_nat p.
Proof. now unfold IRN; rewrite IRZ_IZR, Zabs2Nat.inj_pos. Qed.

Example IRN_42 : IRN 42 = 42%nat.
Proof. now rewrite IRN_pos. Qed.

Lemma IRN_add n m : 
Rnat n -> Rnat m -> IRN (n + m) = (IRN n + IRN m)%nat.
Proof.
intros nnat mnat.
destruct (Rnat_Rint _ nnat) as [nint nge0].
destruct (Rnat_Rint _ mnat) as [mint mge0].
unfold IRN; rewrite IRZ_add; auto.
rewrite Zabs2Nat.inj_add; auto; apply le_IZR.
  destruct (Rint_exists_Z _ nint) as [n' nn'].
  now rewrite nn' in nge0 |- *; rewrite IRZ_IZR.
destruct (Rint_exists_Z _ mint) as [m' mm'].
now rewrite mm' in mge0 |- *; rewrite IRZ_IZR.
Qed.

Lemma IRN_succ n : Rnat n -> IRN (n + 1) = S (IRN n).
Proof.
now intros nnat; rewrite IRN_add, IRN1, Nat.add_1_r; auto with rnat.
Qed.

(* Iteration: a first way to use natural numbers to compute. This function
  should be well understood by students, well documented, and well provided
  in theorems. *)

Definition Rnat_iter {A : Type} (n : R) (f : A -> A) (e : A) :=
  Nat.iter (IRN n) f e.

Lemma Rnat_iter0 {A : Type} (f : A -> A) (e : A) :
  Rnat_iter 0 f e = e.
Proof. now unfold Rnat_iter; rewrite IRN0. Qed.

Lemma Rnat_iter1 {A : Type} (f : A -> A) (e : A) :
  Rnat_iter 1 f e = f e.
Proof. now unfold Rnat_iter; rewrite IRN1. Qed.

Lemma Rnat_iter_add {A : Type} (f : A -> A) (e : A) n m :
  Rnat n -> Rnat m ->
  Rnat_iter (n + m) f e = Rnat_iter n f (Rnat_iter m f e).
Proof.
intros nnat mnat.
unfold Rnat_iter.
rewrite IRN_add; auto.
now rewrite Nat.iter_add.
Qed.

(* TODO : add theorems for successors of iteration, but iter_add and
  and iter1 are already powerful enough. *)

(* For instance, nth can be viewed as an instance of iteration. *)
Definition rnth {A : Type} (e : A) (l : list A) (n : R) :=
  hd e (Rnat_iter n (@tl A) l).

Lemma rnth0 {A : Type} (e : A) a l :
  rnth e (a :: l) 0 = a.
Proof.
now unfold rnth; rewrite Rnat_iter0.
Qed.

Lemma rnthS {A : Type} (e : A) a l n :
  Rnat n ->
  rnth e (a :: l) (n + 1) = rnth e l n.
Proof.
intros nnat.
unfold rnth.
rewrite Rnat_iter_add, Rnat_iter1; auto with rnat.
Qed.

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

(* Subsection: making big operations on sequence of natural numbers.
   Rseq n m is the sequence of length m of numbers n, n + 1, m + 2, ...
   iteraction could be used for that, but we decide here to rely on the
   existing function in Coq's standard library.
 *)

Definition Rseq (n m : R) :=
  map (fun x => n + INR x) (seq 0 (IRN m)).

Lemma rlength_Rseq x y : Rnat y -> rlength (Rseq x y) = y.
Proof.
intros ynat.
rewrite rlength_nat; unfold Rseq.
now rewrite map_length, seq_length, INR_IRN.
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

Lemma Rseq_S (n m : R) : Rnat m ->
  Rseq n (m + 1) = n :: (Rseq (n + 1) m).
Proof.
now intros mnat; rewrite Rplus_comm; rewrite Rseq_add, Rseq1; auto with rnat.
Qed.

Lemma Rseq_S' (n m : R) : Rnat (m - 1) ->
  Rseq n m = n :: Rseq (n + 1) (m - 1).
Proof.
intros mn; replace m with (1 + (m - 1)) at 1 by ring.
rewrite Rseq_add; auto with rnat.
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

(* Now providing a big operation, inspired by mathematical components. *)

Notation "'\big[' f / idf ]_( a <= i < b ) E" :=
  (fold_right f  idf (map (fun i => E) (Rseq a (b - a))))
  (at level 35, a at level 30,  b at level 30, E at level 36, f,
   idf at level 10, i at level 0, right associativity).

Lemma big0 {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a : R) :
  \big[f / idx]_(a <= i < a) E i = idx.
Proof.
now rewrite Rminus_eq_0, Rseq0.
Qed.

Lemma big_recl {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a b : R) :
  Rnat (b - a) -> a < b ->
  \big[f / idx]_(a <= i < b) E i =
   f (E a) (\big[f / idx]_((a + 1) <= i < b) E i).
Proof.
intros hnat altb.
rewrite Rseq_S'; [ | apply Rnat_sub; auto with rnat]; simpl.
  replace (b - a - 1) with (b - (a + 1)) by ring.
  easy.
replace 1 with (0 + 1) by ring; apply Rnat_le_lt; auto with rnat.
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
assert (induct_arg : Rnat (b - a  - 1)).
  apply Rnat_sub; auto with rnat; apply Rnat_gt_pred; auto with rnat; lra.
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
intros a; rewrite Rseq_S; auto with rnat; simpl.
rewrite (Rseq_S a); auto; simpl.
destruct amf as [Pa [P1 P2]].
now rewrite Ih, Pa; replace (a + (p + 1)) with (a + 1 + p) by ring.
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

Lemma Rfactorial_succ' x : 1 <= x -> Rint x -> Rfactorial x =
    Rfactorial (x - 1) * x.
Proof.
intros xge1 xint.
replace x with ((x - 1) + 1) at 1 by ring.
rewrite Rfactorial_succ; [ring | lra | auto with rnat].
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

#[export]
Hint Resolve Rint_factorial : rnat.

(* The factorial could also have been defined using a big operator. *)

Lemma Rfactorial_iterated_product n :
  Rnat n ->
  Rfactorial n = \big[Rmult/1]_(1 <= i < n + 1) i.
Proof.
induction 1 as [ | x xnat Ih].
  now rewrite Rfactorial0, Rplus_0_l, big0.
rewrite Rfactorial_succ; cycle 1.
    now apply Rnat_ge0.
  now destruct (Rnat_Rint _ xnat).
rewrite big_recr; auto; cycle 1.
    replace (x + 1 + 1 - 1) with (x + 1) by ring.
    now auto with rnat.
  apply Rnat_ge0 in xnat.
  lra.
replace (x + 1 + 1 - 1) with (x + 1) by ring.
now rewrite Ih.
Qed.

(* The binomial function. *)
(* ================== *)

(* There are several characteristic properties of the binomal function,
  we can use one of them to define the binomial function.  Notice that
  this definition is well-typed for any real number, even though we will
  need the factorial function to be well-behaved in several places to
  obtain a value we can reason about. *)
Definition binomial x y :=
  Rfactorial x / (Rfactorial y * Rfactorial (x - y)).

Lemma binomial_eq x y :
  binomial x y = Rfactorial x / (Rfactorial y * Rfactorial (x - y)).
Proof. reflexivity. Qed.

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

(* Up to now,  we described natural numbers as the conjunction of being an
  integer and being positive, hoping that the recursive statement Rnat'_ind
  would be enough for practical proofs.  The following proof shows how the
  Rnat'_ind theorem can be used.  *)
Lemma Rint_binomial n m : Rint n -> 0 <= n -> Rint m -> 0 <= m <= n ->
  Rint (binomial n m).
Proof.
intros nint nge0; revert nint nge0 m.
Fail elim n using Rnat'_ind.
assert (base : forall m, Rint m -> 0 <= m <= 0 -> Rint (binomial 0 m)).
  clear n.
  intros m mint m00.
  assert (m0 : m = 0) by lra.
  rewrite m0, binomial_n_0; auto with rnat.
  lra.
assert (step : forall n, Rint n -> 0 <= n ->
           (forall m, Rint m -> 0 <= m <= n -> Rint (binomial n m))
  ->
  (forall m, Rint m -> 0 <= m <= n + 1 -> Rint (binomial (n + 1) m))).
  clear n.
  intros n nint nge0 Ihn m.
  intros mint [mge0 mlenp1].
  assert (cases_on_m : m = 0 \/ exists m', Rint m' /\ 0 <= m' /\ m = m' + 1).
    destruct (Rle_lt_dec 1 m) as [ mge1| mlt1].
      right; exists (m - 1); split;[auto with rnat | split;[lra | ring]].
    assert (tmp:= Rint_le_lt m 1 mint Rint1 mlt1); lra.
  destruct cases_on_m as [m0 | [m' [m'int [m'ge0 msucc]]]].
    rewrite m0, binomial_n_0; auto with rnat; lra.
  rewrite msucc.
  destruct (Rle_lt_dec m n) as [mlen | mgtn].
    rewrite binomial_rec; auto with rnat; try lra.
    apply Rint_add.
      apply Ihn; auto with rnat; lra.
    apply Ihn; auto with rnat; lra.
  assert (n + 1 <= m) by now apply Rint_le_lt.
  replace (m' + 1) with (n + 1) by lra.
  rewrite binomial_n_n; auto with rnat; lra.
intros nint nge0.
revert nint nge0.
apply (Rnat'_ind _ base step).
Qed.

(* Transfering the binomial recursive properties to the natural number
  interface. *)
Lemma binomial_n_0_nat n : Rnat n -> binomial n 0 = 1.
Proof.
now intros nnat; destruct (Rnat_Rint _ nnat); apply binomial_n_0.
Qed.

Lemma binomial_n_n_nat n : Rnat n -> binomial n n = 1.
Proof.
now intros nnat; destruct (Rnat_Rint _ nnat); apply binomial_n_n.
Qed.

Lemma binomial_rec_nat n m : Rnat n -> Rnat m -> m < n ->
  binomial (n + 1) (m + 1) = binomial n m + binomial n (m + 1).
Proof.
intros nnat mnat mbound; apply binomial_rec; auto with rnat;
   try now apply Rnat_ge0.
all: now apply Rnat_Rint.
Qed.

(* Illustrating a proof by induction on natural numbers relying on
  the Rnat predicate.   This is made smoother by the fact that all the
  theorems natively use the Rnat interface. *)
Lemma Rnat_binomial n m : Rnat n -> Rnat m -> m <= n ->
  Rnat (binomial n m).
Proof.
intros nnat; revert nnat m; induction 1 as [ | n nnat Ih].
  intros m mnat mle0.
  assert (m0 : m = 0).
    assert (0 <= m) by now apply Rnat_ge0.
    lra.
  rewrite m0, binomial_n_0_nat.
    now auto with rnat.
  now auto with rnat.
intros m mnat mbound.
induction mnat as [ | m' m'nat _].  (*case analysis on m *)
  destruct (Rnat_Rint _ nnat) as [nint nge0].
  rewrite binomial_n_0_nat.
    now auto with rnat.
  now auto with rnat.
destruct (Rle_lt_dec n m') as [nlem' | m'ltn].
  assert (nm' : n = m') by lra.
  now rewrite <- nm', binomial_n_n_nat; auto with rnat.
rewrite binomial_rec_nat; try auto with rnat.
apply Rnat_add.
  apply Ih.
    now auto with rnat.
  lra.
apply Ih.
  now auto with rnat.
now apply Rnat_le_lt.
Qed.

(* This proof could be given as an exercise.  It shows how much of the
  "fake typing information" clutters the proof: each time we need to prove
  that arguments to Rfactorial is natural number! *)

Lemma binomial_succ n m : Rint n -> 0 <= n -> Rint m -> 0 <= m < n ->
  binomial (n + 1) (m + 1) = binomial n m + binomial n (m + 1).
Proof.
intros nint nge0 mint mbounds.
unfold binomial at 2 3.
replace (Rfactorial n / (Rfactorial m * Rfactorial (n - m))) with
  ((Rfactorial n * (m + 1)) / ((Rfactorial m * (m + 1)) * Rfactorial (n - m)));
  cycle 1.
  field; repeat split; try lra.
    assert (tmp1 : Rint (n - m)) by auto with rnat.
    assert (tmp2 : 0 < Rfactorial (n - m)) by now apply Rfactorial_gt_0.
    lra.
  assert (tmp3 : 0 < Rfactorial m) by now apply Rfactorial_gt_0.
  lra.
replace (n - m) with ((n + 1) - (m + 1)) by ring.
replace (Rfactorial n / (Rfactorial (m + 1) * Rfactorial (n - (m + 1)))) with
   (Rfactorial n * ((n + 1) - (m + 1)) /
    (Rfactorial (m + 1) * (Rfactorial (n - (m + 1)) * ((n + 1) - (m + 1)))));
  cycle 1.
  field.
  assert (tmp1 : Rint (n - (m + 1))) by auto with rnat.
  assert (tmp2 : Rint (m + 1)) by auto with rnat.
  assert (tmp3 : 0 < Rfactorial (n - (m + 1))) by now apply Rfactorial_gt_0.
  assert (tmp4 : 0 < Rfactorial (m + 1)) by now apply Rfactorial_gt_0.
  lra.
replace (Rfactorial m * (m + 1)) with (Rfactorial (m + 1)); cycle 1.
  apply Rfactorial_succ; auto with rnat; lra.
replace (Rfactorial (n - (m + 1)) * (n + 1 - (m + 1))) with
  (Rfactorial ((n + 1) - (m + 1))); cycle 1.
  rewrite (Rfactorial_succ' (n + 1 - (m + 1))); cycle 1.
    enough (m + 1 <= n) by lra.
    apply Rint_le_lt; auto; lra.
    now auto with rnat.
  now replace (n + 1 - (m + 1) - 1) with (n - (m + 1)) by ring.
assert (tech : forall a b c, c <> 0 -> a / c + b / c = (a + b) / c).
  now intros a b c cn0; field.
rewrite tech; cycle 1.
  apply Rmult_integral_contrapositive.
  assert (tmp1 : Rint (n + 1 - (m + 1))) by auto with rnat.
  assert (tmp2 : Rint (m + 1)) by auto with rnat.
  assert (tmp3 : 0 < Rfactorial (n + 1 - (m + 1))) by now apply Rfactorial_gt_0.
  assert (tmp4 : 0 < Rfactorial (m + 1)) by now apply Rfactorial_gt_0.
  lra.
replace (Rfactorial n * (m + 1) + Rfactorial n * (n + 1 - (m + 1))) with
  (Rfactorial n * (n + 1)) by ring.
replace (Rfactorial n * (n + 1)) with (Rfactorial (n + 1)); cycle 1.
  rewrite Rfactorial_succ; auto.
reflexivity.
Qed.

Definition Rnat_rect {A : Type} (v0 : A) (stf : R -> A -> A) (x : R) : A :=
  nat_rect (fun _ => A) v0 (fun x => stf (INR x)) (IRN x).

Lemma Rnat_rect0 {A : Type} (v0 : A) stf : Rnat_rect v0 stf 0 = v0.
Proof.
now unfold Rnat_rect, IRN; rewrite IRZ_IZR.
Qed.

Lemma Rnat_rect_succ {A : Type} (v0 : A) stf (x : R) :
  Rnat x ->
  Rnat_rect v0 stf (x + 1) = stf x (Rnat_rect v0 stf x).
Proof.
intros xnat.
destruct (Rnat_exists_nat _ xnat) as [x' xx'].
unfold Rnat_rect.
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

(* thanks to Rnat_rect, we can define recursive sequences of numbers. *)

Definition factr (x : R) :=
  Rnat_rect 1 (fun y fact_y => fact_y * (y + 1)) x.

(* We have enough material to show that this new definition of factorial
   is correct with respect to the other ones. *)
Lemma factr_correct x : Rnat x -> factr x = Rfactorial x.
Proof.
induction 1 as [ | x xnat Ih].
  now unfold factr; rewrite Rnat_rect0, Rfactorial0.
destruct (Rnat_Rint _ xnat) as [xint xge0].
unfold factr; rewrite Rnat_rect_succ; auto.
fold (factr x).
rewrite Rfactorial_succ; auto.
now rewrite Ih.
Qed.

Definition Rnat_rect_2 {A : Type} (v0 v1 : A) (stf : R -> A -> A -> A) :
  R -> A :=
  fun y : R => fst (Rnat_rect (v0, v1)
    (fun x p => (snd p, stf x (fst p) (snd p))) y).

Lemma Rnat_rect_2_0 {A : Type} (v0 v1 : A) stf :
  Rnat_rect_2 v0 v1 stf 0 = v0.
Proof. now unfold Rnat_rect_2; rewrite Rnat_rect0. Qed.

Lemma Rnat_rect_2_1 {A : Type} (v0 v1 : A) stf :
  Rnat_rect_2 v0 v1 stf 1 = v1.
Proof.
unfold Rnat_rect_2.
replace 1 with (0 + 1) by ring.
rewrite Rnat_rect_succ; auto with rnat.
now rewrite Rnat_rect0.
Qed.

Lemma Rnat_rect_2_succ {A : Type} (v0 v1 : A) stf x :
  Rnat x ->
  Rnat_rect_2 v0 v1 stf (x + 2) =
  stf x (Rnat_rect_2 v0 v1 stf x) (Rnat_rect_2 v0 v1 stf (x + 1)).
Proof.
intros xnat.
unfold Rnat_rect_2.
replace (x + 2) with (x + 1 + 1) by ring.
now rewrite !Rnat_rect_succ; auto with rnat.
Qed.

(* It may not be necessary to expose the definition of the fibonacci
  sequence to students, but the next three properties are the 
  real usable interface. *)
Definition fibr := Rnat_rect_2 0 1 (fun n fn fn' => fn + fn').

Lemma fibr0 : fibr 0 = 0.
Proof.  now unfold fibr; rewrite Rnat_rect_2_0. Qed.

Lemma fibr1 : fibr 1 = 1.
Proof.  now unfold fibr; rewrite Rnat_rect_2_1. Qed.

Lemma fibr_succ n : Rnat n -> fibr (n + 2) = fibr n + fibr (n + 1).
Proof.  now intros nnat; unfold fibr; rewrite Rnat_rect_2_succ. Qed.

Example fibr7 : fibr 7 = 13.
assert (fibr2 : fibr 2 = 1).
  replace 2 with (0 + 2) by ring.
  rewrite fibr_succ; auto with rnat; replace (0 + 1) with 1 by ring.
  now rewrite fibr0, fibr1; ring.
assert (fibr3 : fibr 3 = 2).
  replace 3 with (1 + 2) at 1 by ring.
  rewrite fibr_succ; auto with rnat; replace (1 + 1) with 2 by ring.
  now rewrite fibr1, fibr2.
assert (fibr4 : fibr 4 = 3).
  replace 4 with (2 + 2) by ring.
  rewrite fibr_succ; auto with rnat; replace (2 + 1) with 3 by ring.
  now rewrite fibr2, fibr3; ring.
assert (fibr5 : fibr 5 = 5).
  replace 5 with (3 + 2) by ring.
  rewrite fibr_succ; auto with rnat; replace (3 + 1) with 4 by ring.
  now rewrite fibr3, fibr4; ring.
assert (fibr6 : fibr 6 = 8).
  replace 6 with (4 + 2) by ring.
  rewrite fibr_succ; auto with rnat; replace (4 + 1) with 5 by ring.
  now rewrite fibr4, fibr5; ring.
replace 7 with (5 + 2) by ring.
rewrite fibr_succ; auto with rnat; replace (5 + 1) with 6 by ring.
rewrite fibr5, fibr6; ring.
Qed.

(* We can also define the binomial function recursively *)

Definition binomialr (n m : R) :=
  Rnat_rect (fun x : R => if Req_dec_T x 0 then 1 else 0)
     (fun n f m => f (m - 1) + f m) n m.

(* We can then show that this definition of binomial satisfies the
  expected properties. *)
Lemma binomialr_0_n (m : R) :
  binomialr 0 m = if Req_dec_T m 0 then 1 else 0.
Proof.
now unfold binomialr; rewrite Rnat_rect0.
Qed.

Lemma binomialr_succ (n m : R) : Rnat n ->
  binomialr (n + 1) m = binomialr n (m - 1) + binomialr n m.
Proof.
intros nnat.
unfold binomialr.
now rewrite Rnat_rect_succ; auto with rnat.
Qed.

(* This new definition of binomial is slightly different.  We check
  the equality within the Pascal triangle. *)

Lemma binomialr_right (n m : R) : Rnat n -> Rnat m -> n < m ->
  binomialr n m = 0.
Proof.
intros nnat; revert m; induction nnat as [ | x xnat Ih].
intros m mnat mbound; rewrite binomialr_0_n; auto with rnat.
  destruct (Req_dec_T m 0) as [m0 | mn0].
    lra.
  easy.
intros m mnat mgtx2.
rewrite binomialr_succ; auto with rnat.
rewrite Ih; cycle 1.
    apply Rnat_sub; auto with rnat.
    assert (0 <= x) by now apply Rnat_ge0.
    lra.
  lra.
rewrite Ih.
    ring.
  assumption.
lra.
Qed.

Lemma binomialr_n_n (n : R) : Rnat n -> binomialr n n = 1.
Proof.
induction 1 as [ | x xnat Ih].
  rewrite binomialr_0_n; auto with rnat.
  destruct (Req_dec_T 0 0) as [zz | abs]; [ | lra].
  easy.
rewrite binomialr_succ; auto with rnat.
replace (x + 1 - 1) with x by ring.
rewrite Ih.
rewrite binomialr_right; auto with rnat.
  ring.
lra.
Qed.

Lemma binomialr_left (n m : R) : Rnat n ->
  m < 0 -> binomialr n m = 0.
Proof.
intros nnat; revert m.
induction nnat as [ | x xnat Ih].
  intros m mlt0.
  rewrite binomialr_0_n.
  destruct (Req_dec_T m 0) as [m0 | mn0].
    lra.
  easy.
intros m mlt0.
rewrite binomialr_succ; auto.
rewrite Ih;[ | lra].
rewrite Ih.
  ring.
lra.
Qed.

Lemma binomialr_n_0 n : Rnat n -> binomialr n 0 = 1.
Proof.
induction 1 as [ | x xnat Ih].
  now rewrite binomialr_n_n; auto with rnat.
rewrite binomialr_succ; auto with rnat.
rewrite Ih.
rewrite binomialr_left.
    ring.
  auto with rnat.
lra.
Qed.

(* If we use Rnat_rect to define function, we need to evaluate how hard
  it is to reason about these functions, using Rnat_ind.  This is an
  example where we show that the the binomial function, defined recursively
  coincides when 0 <= m <= n with the binomial function defined with
  ratios of factorials. *)
Lemma binomialr_fact (n m : R) : Rnat n -> Rnat m -> m <= n ->
  binomialr n m = Rfactorial n / (Rfactorial (n - m) * Rfactorial m).
Proof.
intros nnat; revert m.
induction nnat as [ | x xnat Ih].
  intros m mnat mle0.
  assert (m0 : m = 0).
    assert (0 <= m) by now apply Rnat_ge0.
    lra.
  rewrite m0.
  replace (0 - 0) with 0 by ring.
  rewrite Rfactorial0.
  rewrite binomialr_n_n; auto with rnat.
  now field.
intros m mnat mlex1.
rewrite binomialr_succ; auto with rnat.
destruct (Req_dec_T m 0) as [m0 | mn0].
  rewrite m0.
  replace (0 - 1) with (-1) by ring.
  rewrite binomialr_left; auto with rnat; cycle 1.
    lra.
  rewrite binomialr_n_0; auto with rnat.
  replace (x + 1 - 0) with (x + 1) by ring.
  rewrite Rfactorial0, Rmult_1_r, Rdiv_diag; cycle 1.
    enough (0 <> Rfactorial (x + 1)) by lra.
    apply Rlt_not_eq.
    apply Rfactorial_gt_0.
    now apply Rnat_Rint; auto with rnat.
  ring.
rewrite Ih; cycle 1.
    apply Rnat_sub; auto with rnat.
    replace 1 with (0 + 1) by ring.
    apply Rnat_le_lt; auto with rnat.
    assert (0 <= m) by now apply Rnat_ge0.
    lra.
  lra.
destruct (Req_dec_T m (x + 1)) as [mx1 | mnx1].
  rewrite mx1.
  replace (x - (x + 1 - 1)) with 0 by ring.
  replace (x + 1 - 1) with x by ring.
  replace (x + 1 - (x + 1)) with 0 by ring.
  rewrite binomialr_right; auto with rnat; cycle 1.
    lra.
  rewrite Rplus_0_r.
  rewrite Rfactorial0, Rmult_1_l.
  assert (xint : Rint x) by now apply Rnat_Rint.
  rewrite Rdiv_diag; cycle 1.
    assert (tmp := Rfactorial_gt_0 _ xint).
    lra.
  rewrite Rmult_1_l.
  rewrite Rdiv_diag; cycle 1.
    assert (xint1 : Rint (x + 1)) by auto with rnat.
    assert (tmp := Rfactorial_gt_0 _ xint1).
    lra.
  ring.
rewrite Ih; auto with rnat; cycle 1.
  enough (m + 1 <= x + 1) by lra.
  assert (m < x + 1) by lra.
  now apply Rnat_le_lt; auto with rnat.
replace (Rfactorial (x + 1)) with (Rfactorial x * ((x + 1 - m) + m)); cycle 1.
  rewrite Rfactorial_succ; cycle 1.
      now apply Rnat_ge0.
    now apply Rnat_Rint.
  ring.
replace (x - (m - 1)) with (x + 1 - m) by ring.
replace (Rfactorial (x + 1 - m)) with 
   ((x + 1 - m) * Rfactorial (x - m)); cycle 1.
  replace (x + 1 - m) with (x - m + 1) by ring.
  rewrite Rfactorial_succ; cycle 1.
      enough (m + 1 <= x + 1) by lra.
      apply Rnat_le_lt; auto with rnat; lra.
    now apply Rint_sub; apply Rnat_Rint.
  ring.
replace (Rfactorial m) with (Rfactorial (m - 1) * m); cycle 1.
  assert (1 <= m).
    replace 1 with (0 + 1) by ring.
    apply Rnat_le_lt; auto with rnat.
    assert (0 <= m) by now apply Rnat_ge0.
    lra.
  rewrite (Rfactorial_succ' m); auto with rnat.
  now apply Rnat_Rint.
field.
assert (0 < Rfactorial (m - 1)).
  apply Rfactorial_gt_0; apply Rint_sub; auto with rnat.
  now apply Rnat_Rint.
assert (0 < Rfactorial (x - m)).
  now apply Rfactorial_gt_0; apply Rint_sub; apply Rnat_Rint.
assert (x + 1 - m <> 0) by lra.
repeat split; auto; lra.
Qed.

(* This ends the section of tools that should be provided to students about
  binomial numbers. *)

(* Small recreation: another definition of factorial, an efficient one,
   It can be used to find the value empirically. *)
Fixpoint p_fact (base : Z) (p : positive) :=
  match p with
  | xH => (base + 1)%Z
  | xI p' => (p_fact base p' * p_fact (base + Z.pos p') p' * (base + Z.pos p))%Z
  | xO p' => (p_fact base p' * p_fact (base + Z.pos p') p')%Z
  end.

Lemma p_fact_correct (base : Z) (p : positive) :
  (0 <= base)%Z -> (Z.of_nat (fact (Z.abs_nat base)) *
  p_fact base p = Z.of_nat (fact (Z.abs_nat  (base + Z.pos p))))%Z.
Proof.
revert base; induction p as [ p Ih | p Ih | ]; simpl.
- intros base basege0; simpl.
  rewrite !Z.mul_assoc.
  rewrite !Ih; [ | lia | assumption].
  set (w := (base + Z.pos p~1)%Z).
  replace w with (Z.of_nat (Z.abs_nat w)) at 1; cycle 1.
    rewrite Zabs2Nat.id_abs; apply Z.abs_eq; unfold w; lia.
  rewrite <- Nat2Z.inj_mul.
  replace (Z.abs_nat w) with (S (Z.abs_nat (base + Z.pos p + Z.pos p))); cycle 1.
    unfold w; lia.
  rewrite Nat.mul_comm; easy.
- intros base basege0; simpl.
  rewrite !Z.mul_assoc.
  rewrite !Ih; try lia.
  replace (base + Z.pos p + Z.pos p)%Z with (base + Z.pos p~0)%Z by lia.
  easy.
- intros base basege0.
  replace (base + 1)%Z with (Z.of_nat (S (Z.abs_nat base)))%Z at 1 by lia.
  rewrite Z.mul_comm.
  rewrite <- Nat2Z.inj_mul.
  replace (Z.abs_nat (base + 1)) with (S (Z.abs_nat base)) by lia.
  easy.
Qed.

Definition Zfact (x : Z) :=
  match x with Z.pos p => p_fact 0 p | _ => 1%Z end.

Lemma Zfact_correct (x : Z) : Zfact x = Zfactorial x.
Proof.
unfold Zfact, Zfactorial.
destruct x as [ | p | p]; simpl; auto.
assert (main := p_fact_correct 0 p (Z.le_refl 0)).
now rewrite Z.mul_1_l, Z.add_0_l in main.
Qed.

Definition nums_5_105 := (rev (Z.iter 100 (fun l =>
           match l with a :: tl => (a + 1)%Z :: l | nil => 1%Z :: nil end)
           (5%Z :: nil))).

Compute nums_5_105.
Compute last nums_5_105 0%Z.

(* This is an example computing many instances of binomial values, using
   the fact that we have an efficient way to compute factorials.   *)
Compute filter (fun p => (fst p =? 0)%Z) (map
          (fun x => ((Zfact x / (Zfact 5 * Zfact (x - 5)) -
                      (17 * (Zfact x / (Zfact 4 * Zfact (x - 4)))))%Z, x))
             (rev (Z.iter 100 (fun l =>
           match l with a :: tl => (a + 1)%Z :: l | nil => 1%Z :: nil end)
           (5%Z :: nil)))).
(* This says that the value expected at the next exercise could be 89, the
   computation of the division is approximated to 1/100, and we test values
   between 5 and 105. *)

(* This is a specific tactic to compute factorials, but we could have a
  more general tactics (based on a database of correspondence between
  real functions and integer functions), to provide computation on ground terms
  for real function. *)

Ltac compute_factorial :=
  match goal with |- context[Rfactorial (IZR (Z.pos ?p))] =>
    let vfp := eval compute in (Zfact (Z.pos p)) in
    replace (Rfactorial (IZR (Z.pos p))) with (IZR vfp);
      [ try reflexivity |
        now unfold Rfactorial; rewrite IRZ_IZR, <- Zfact_correct]
  end.

(* This would be unpractical if we had preserved the computation based on
  natural numbers. *)
Compute Zfact 100.
Lemma fact100 : Rfactorial 100 = 93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000.
Proof. compute_factorial. Qed.

(* End of recreation. *)

(* The binomial formula for polynomials. *)
Definition Rpow (x n : R) :=
  Rnat_iter n (Rmult x) 1.

Lemma Rpow0 (x : R) : Rpow x 0 = 1.
Proof. now unfold Rpow; rewrite Rnat_iter0. Qed.

Lemma Rpow1 (x : R) : Rpow x 1 = x.
Proof. now unfold Rpow; rewrite Rnat_iter1, Rmult_1_r. Qed.

Lemma Rpow_succ (x n : R) : Rnat n ->
  Rpow x (n + 1) = x * Rpow x n.
Proof.
intros nnat.
unfold Rpow; rewrite Rplus_comm, Rnat_iter_add; auto with rnat.
now rewrite Rnat_iter1.
Qed.

Lemma Rpow_succ' (x n : R) : Rnat (n - 1) ->
  Rpow x n = x * Rpow x (n - 1).
Proof.
intros nnat.
rewrite <- Rpow_succ; auto.
now replace (n - 1 + 1) with n by ring.
Qed.

Lemma Rpow_add_r (x n m : R) : Rnat n -> Rnat m ->
  Rpow x (n + m) = Rpow x n * Rpow x m.
Proof.
intros nnat mnat.
induction nnat as [ | n nnat Ih].
  now rewrite Rplus_0_l, Rpow0, Rmult_1_l.
rewrite Rpow_succ; auto with rnat.
replace (n + 1 + m) with (n + m + 1) by ring.
now rewrite Rpow_succ, Ih, Rmult_assoc; auto with rnat.
Qed.

(* TODO : generalize to an arbitrary associative-commutative monoid. *)
Lemma big_add (f g : R -> R) (b n : R) : Rnat (n - b) ->
  \big[Rplus/0]_(b <= i < n) f i +
  \big[Rplus/0]_(b <= i < n) g i = 
  \big[Rplus/0]_(b <= i < n) (f i + g i).
Proof.
set (w := fold_right).
generalize (n - b); intros k knat; revert b.
induction knat as [ | k knat Ih]; intros b.
  rewrite Rseq0; simpl; ring.
rewrite Rseq_S'; replace (k + 1 - 1) with k by ring; auto.
unfold w; simpl; fold w.
rewrite <- Ih; ring.
Qed.

Lemma big_distr (f : R -> R) (b n a : R) : Rnat (n - b) ->
  a * \big[Rplus/0]_(b <= i < n) f i =
  \big[Rplus/0]_(b <= i < n) (a * f i).
Proof.
set (w := fold_right).
generalize (n - b); intros k knat; revert b.
induction knat as [ | k knat Ih]; intros b.
   rewrite Rseq0; simpl; ring.
rewrite Rseq_S'; replace (k + 1 - 1) with k by ring; auto.
unfold w; simpl; fold w.
rewrite <- Ih; ring.
Qed.

Lemma big_shift {A : Type} (op : R -> A -> A) v
 (f : R -> R) (b k n : R) : Rnat (n - b) ->
  \big[op/v]_(b <= i < n) (f (i + k)) =
  \big[op/v]_((b + k) <= i < (n + k)) (f i).
Proof.
set (w := fold_right).
replace (n + k - (b + k)) with (n - b) by ring.
generalize (n - b); intros l lnat; revert b.
induction lnat as [ | l lnat Ih]; intros b.
  now rewrite !Rseq0.
rewrite !Rseq_S; auto.
simpl; rewrite Ih.
now replace (b + 1 + k) with (b + k + 1) by ring.
Qed.

Lemma big_ext {A : Type} (op : R -> A -> A) v (f g : R -> R)
  (b n : R) : Rnat (n - b) ->
  (forall x, Rnat x -> 0 <= x < n - b -> f (b + x) = g (b + x)) ->
  \big[op/v]_(b <= i < n) f i =
  \big[op/v]_(b <= i < n) g i.
Proof.
set (w := fold_right).
generalize (n - b); intros l lnat; revert b.
induction lnat as [ | l lnat Ih]; intros b eq_cnd.
  now rewrite Rseq0.
rewrite Rseq_S; auto; simpl.
replace b with (b + 0) at 1 3 by ring.
rewrite eq_cnd; cycle 1.
    auto with rnat.
  apply Rnat_ge0 in lnat; lra.
apply f_equal, Ih.
intros x xnat xint.
replace (b + 1 + x) with (b + (1 + x)) by ring.
apply eq_cnd.
  auto with rnat.
lra.
Qed.

(* This lemma is made approximately in a way that could be shown to students. *)
(* Even for an expert, it is an exercise that requires more than an hour. *)
Lemma binomial_poly (x y n : R) : Rnat n -> Rpow (x + y) n =
  \big[Rplus/0]_(0 <= i < n + 1) 
       (binomial n i * Rpow x i * Rpow y (n - i)).
Proof.
induction 1 as [ | n nnat Ih].
  rewrite Rpow0.
  rewrite big_recl; cycle 1.
      now replace (0 + 1 - 0) with 1 by ring; auto with rnat.
    lra.
  rewrite binomial_n_n; auto with rnat; cycle 1.
    lra.
  replace (0 - 0) with 0 by ring.
  rewrite !Rpow0; cycle 1.
  rewrite big0.
  ring.
rewrite Rpow_succ, Ih; auto with rnat.
rewrite Rmult_plus_distr_r.
rewrite !big_distr;[ |  rewrite Rminus_0_r | rewrite Rminus_0_r]; auto with rnat.
set (w1 := fold_right _ _ _).
set (w2 := fold_right _ _ _).
set (w3 := fold_right _ _ _).
unfold w2.
rewrite big_recl; auto; cycle 1.
    now replace (n + 1 - 0) with (n + 1) by ring; auto with rnat.
  apply Rnat_ge0 in nnat; lra.
rewrite <- big_shift; cycle 1.
  now replace (n - 0) with n by ring.
set (w4 := fold_right _ _ _).
replace (n - 0) with n by ring.
replace (binomial n 0) with (binomial (n + 1) 0); cycle 1.
  rewrite !binomial_n_0; destruct (Rnat_Rint _ nnat); auto with rnat; lra.
replace (y * (binomial (n + 1) 0 * Rpow x 0 * Rpow y n)) with
  (binomial (n + 1) 0 * Rpow x 0 * Rpow y (n + 1 - 0)); cycle 1.
  rewrite Rminus_0_r, Rpow_succ; auto with rnat; ring.
unfold w1.
rewrite big_recr; auto; cycle 1.
    now replace (n + 1 - 0) with (n + 1) by ring; auto with rnat.
  apply Rnat_ge0 in nnat; lra.
replace (n + 1 - 1) with n by ring.
set (w5 := fold_right _ _ _).
replace (x * (binomial n n * Rpow x n * Rpow y (n - n))) with
  (binomial (n + 1) (n + 1) * Rpow x (n + 1) * Rpow y ((n + 1) - (n + 1))); 
  cycle 1.
  replace (n - n) with 0 by ring; replace ((n + 1) - (n + 1)) with 0 by ring.
  rewrite Rpow_succ; auto.
  rewrite !binomial_n_n; destruct (Rnat_Rint _ nnat); auto with rnat.
    ring.
  lra.
set (tmn := _ * _ * _).
set (t0 := _ * _ * _).
replace (w5 + tmn + (t0 + w4)) with (t0 + (w5 + w4) + tmn) by ring.
replace (w5 + w4) with
 (\big[Rplus/0]_((0 + 1) <= i < (n + 1))
   (binomial (n + 1) i * Rpow x i * Rpow y ((n + 1) - i))).
  unfold t0.
  rewrite <-
    (big_recl (fun i => binomial (n + 1) i * Rpow x i * Rpow y ((n + 1) - i)));
  cycle 1.
      now rewrite Rminus_0_r; auto with rnat.
    apply Rnat_ge0 in nnat; lra.
  unfold tmn.
  replace (n + 1) with (n + 1 + 1 - 1) at 1 3 4 6 by ring.
  rewrite <-
   (big_recr (fun i => binomial (n + 1) i * Rpow x i * Rpow y ((n + 1) - i)));
    cycle 1.
        now auto.
      now rewrite Rminus_0_r; auto with rnat.
    apply Rnat_ge0 in nnat; lra.  
  easy.
unfold w5, w4.
rewrite big_add; cycle 1.
  now rewrite Rminus_0_r; auto with rnat.
rewrite <- big_shift; cycle 1.
  now rewrite Rminus_0_r; auto with rnat.
apply big_ext.
  now rewrite Rminus_0_r; auto with rnat.
intros i inat ibound.
replace (0 + i + 1) with (i + 1) by ring.
replace (0 + i) with i by ring.
replace (x * (binomial n i * Rpow x i * Rpow y (n - i))) with
  (binomial n i * Rpow x (i + 1) * Rpow y (n - i)); cycle 1.
  rewrite Rpow_succ; auto; ring.
replace (y * (binomial n (i + 1) * Rpow x (i + 1) * Rpow y (n - (i + 1)))) with
  (binomial n (i + 1) * Rpow x (i + 1) * Rpow y (n - i)); cycle 1.
  replace (n - i) with (n - (i + 1) + 1) by ring.
  rewrite (Rpow_succ y); cycle 1.
    apply Rnat_sub; auto with rnat.
  assert (iltn : i < n) by lra.
  now apply Rnat_le_lt; auto.
  ring.
rewrite binomial_rec; destruct (Rnat_Rint _ nnat);
  destruct (Rnat_Rint _ inat); auto with rnat; try lra.
replace (n + 1 - (i + 1)) with (n - i) by ring.
ring.
Qed.

(* The golden ratio *)
Definition phi := (1 + sqrt 5) / 2.

Definition psi := (1 - sqrt 5) / 2.

Lemma golden_fib n : Rnat n -> fibr n = 
  (Rpow phi n - Rpow psi n) / (phi - psi).
Proof.
assert (phi2q : Rpow phi 2 = phi + 1).
  replace (Rpow phi 2) with (phi * phi); cycle 1.
    rewrite Rpow_succ'; auto with rnat; cycle 1.
      now apply Rnat_sub; auto with rnat; lra.
    now replace (2 - 1) with 1 by ring; rewrite Rpow1.
  unfold phi.
  replace ((1 + sqrt 5) / 2 * ((1 + sqrt 5) / 2)) with
   ((1 + 2 * sqrt 5 + sqrt 5 * sqrt 5) / 4) by field.
  replace (sqrt 5 * sqrt 5) with 5; cycle 1.
    now rewrite sqrt_def; lra.
  now field.
assert (psi2q : Rpow psi 2 = psi + 1).
  replace (Rpow psi 2) with (psi * psi); cycle 1.
    rewrite Rpow_succ'; auto with rnat; cycle 1.
      now apply Rnat_sub; auto with rnat; lra.
    now replace (2 - 1) with 1 by ring; rewrite Rpow1.
  unfold psi.
  replace ((1 - sqrt 5) / 2 * ((1 - sqrt 5) / 2)) with
   ((1 - 2 * sqrt 5 + sqrt 5 * sqrt 5) / 4) by field.
  replace (sqrt 5 * sqrt 5) with 5; cycle 1.
    now rewrite sqrt_def; lra.
  now field.
assert (root_n_q : forall r x, Rnat x -> Rpow r 2 = r + 1 ->
          Rpow r (x + 2) = Rpow r (x + 1) + Rpow r x).
  intros r x xnat rrroot.
  replace (Rpow r x) with (Rpow r x * 1) by ring.
  rewrite !Rpow_add_r, Rpow1; auto with rnat.
  rewrite <- Rmult_plus_distr_l.
  now apply Rmult_eq_compat_l.
intros nnat.
assert (psidifphi : phi - psi <> 0).
  unfold phi, psi.
  enough (0 < sqrt 5) by lra.
  now apply sqrt_lt_R0; lra.
enough (main : fibr n = (Rpow phi n - Rpow psi n) / (phi - psi) /\
        fibr (n + 1) = (Rpow phi (n + 1) - Rpow psi (n + 1)) / (phi - psi)).
   now destruct main as [main _].  
induction nnat as [ | x xnat Ih].
  split.
    replace (0 + 1) with 1 by ring; replace (0 + 2) with 2 by ring.
    now rewrite !Rpow0, Rminus_diag, fibr0; field; auto.
  now rewrite Rplus_0_l, !Rpow1, fibr1; field.
destruct Ih as [Ih0 Ih1].
split.
  easy.
replace (x + 1 + 1) with (x + 2) by ring.
rewrite fibr_succ; auto with rnat.
rewrite Ih0, Ih1.
rewrite (root_n_q phi); auto with rnat.
rewrite (root_n_q psi); auto with rnat.
field; auto.
Qed.

(* Now we come to the exercise that triggered my curiosity. *)
(* The objective of the experiment here, is to show a Coq proof, where
  discovery of the solution can happen as we progress in the proof.
  Here, we exploit the fact that there is an equality between
  binomial n m and n! / (m! * (n - m)!.  In the present  experiment, this
  equality is given by definition, but if binomial was given by the
  usual recursive definition based on the Pascal triangle, it would also
  work, as soon as one proves that the recursive definition implies the
  equality with factorials.

  We use eexists to postpone the choice of the answer, and shelve to postpone
  the proof of the various properties that the answer should satisfy
  (being a natural number, being larger that 5, etc. *)

Lemma exo : exists n, binomial n 5 = 17 * binomial n 4.
Proof.
(* One way to perform math is to prove the existence of a number by
  gathering constraints about this number.  Here we go, we assume
  the existence of the number. *)
eexists ?[ex_n].
(* The remember trick is used to make sure the existential variable will
  not be affected by uses of the ring tactic. *)
remember ?ex_n as n eqn:Heqn.
rewrite !binomial_eq.
(* The first step is to remove factorial 4 from both side.  On the left side,
 factorial 4 is found inside factorial 5. *)
rewrite !Rdiv_def, !Rinv_mult, (Rmult_comm (/ Rfactorial 5)), <- Rmult_assoc.
replace (Rfactorial 5) with (5 * Rfactorial 4); cycle 1.
  rewrite (Rfactorial_succ' 5), Rmult_comm.
    replace (5 - 1) with 4 by ring.
    reflexivity.
  lra.
now auto with rnat.
rewrite (Rmult_comm (/ Rfactorial 4)), Rinv_mult, <- !Rmult_assoc.
(* This should be a differently worded tactic, to express explicitely the
   removal of (/Rfactorial 4) *)
apply (Rmult_eq_compat_r (/Rfactorial 4)).
(* This is a dummy tactic to reassert what the goal has become. *)
enough (it : Rfactorial n * / Rfactorial (n - 5) * / 5 =
             17 * Rfactorial n * /Rfactorial (n - 4)) by exact it.
(* The next step is to remove factorial n *)
rewrite <- (Rmult_comm (Rfactorial n)), !Rmult_assoc.
apply (Rmult_eq_compat_l (Rfactorial n)).
enough (it : / Rfactorial (n - 5) * / 5 = 17 * /Rfactorial (n - 4)) by exact it.
replace (Rfactorial (n - 4)) with (Rfactorial (n - 5) * (n - 4)); cycle 1.
  rewrite (Rfactorial_succ' (n - 4)).
      replace (n - 4 - 1) with (n - 5) by ring.
      reflexivity.
    shelve.
  shelve.
(* The next step is to remove factorial (n - 5) *)
rewrite Rinv_mult, <- Rmult_assoc, <- (Rmult_comm (/ Rfactorial (n - 5))), Rmult_assoc.
apply (Rmult_eq_compat_l (/ Rfactorial (n - 5))).
enough (it : / 5 = 17 * / (n - 4)) by exact it.
apply (Rmult_eq_reg_l (5 * (n - 4))).
field_simplify.
apply (Rplus_eq_reg_l 4).
field_simplify.
enough (it : n = 89) by exact it.
(* At this point we accept the constraint as defining n. *)
rewrite Heqn; reflexivity.
(* We now have to prove all the accumulated constraints. *)
(* this one was created by field_simplify *)
lra.
(* this one was create by field_simplify *)
lra.
(* This one was created by the expansion of the factorial function. *)
Unshelve.
  lra.
rewrite Heqn.
auto with rnat.
Qed.

(* This second version only uses Field for algebraic computation and lra
  for bound conditions. *)
Lemma exo' : exists n, binomial n 5 = 17 * binomial n 4.
Proof.
(* One way to perform math is to prove the existence of a number by
  gathering constraints about this number.  Here we go, we assume
  the existance of the number. *)
eexists ?[ex_n].
(* The remember trick is used to make sure the existential variable will
  not be affected by uses of the ring tactic. *)
remember ?ex_n as n eqn:Heqn.
unfold binomial.
(* Preparatory work to get rid of Rfactorial n *)
replace (17 * (Rfactorial n / (Rfactorial 4 * Rfactorial (n - 4)))) with
  (Rfactorial n * (17 / (Rfactorial 4 * Rfactorial (n - 4)))); cycle 1.
  field.
    assert (0 < Rfactorial (n - 4) /\ (0 < Rfactorial 4)).
      split; apply Rfactorial_gt_0.
        (* we need to wait until n is known for this one. *)
        shelve.
      (* this one can be proved right away. *)
      auto with rnat.
    lra.
(* Getting rind of Rfactorial n *)
apply Rmult_eq_compat_l.
(* We now have to prove ... *)
enough (it : / (Rfactorial 5 * Rfactorial (n - 5)) = 17 /
            (Rfactorial 4 * (Rfactorial (n - 4)))) by exact it.
(* Preparatory work to get rid of (Rfactorial (n - 5)) *)
replace (/(Rfactorial 5 * Rfactorial (n - 5))) with
  (/(Rfactorial 5) * /(Rfactorial (n - 5))); cycle 1.
  field.
    assert (0 < Rfactorial (n - 5) /\ 0 < Rfactorial 5).
       split; apply Rfactorial_gt_0.
          shelve.
       auto with rnat.
     lra.
replace (17 / (Rfactorial 4 * Rfactorial (n - 4))) with
   (17 / (Rfactorial 4 * (n - 4)) * /(Rfactorial (n - 5))); cycle 1.
  rewrite (Rfactorial_succ' (n - 4)); cycle 1.
      shelve.
    shelve.
  replace (n - 4 - 1) with (n - 5) by field.
  field.
  split.
    shelve.
    assert (0 < Rfactorial (n - 5) /\ 0 < Rfactorial 4).
       split; apply Rfactorial_gt_0.
          shelve.
       auto with rnat.
     lra.
apply Rmult_eq_compat_r.
(* We now have to prove ... *)
enough (it : / Rfactorial 5  = 17 / (Rfactorial 4 * (n - 4))) by exact it.
(* We now want to isolate Rfactorial 4. *)
replace (/ Rfactorial 5) with (/ Rfactorial 4 * / 5); cycle 1.
  rewrite (Rfactorial_succ' 5); cycle 1.
      lra.
    auto with rnat.
  replace (5 - 1) with 4 by field.
  field.
  (* Here we could use the factorial computation tactic.
  compute_factorial; lra.
  *)
  assert (0 < Rfactorial 4).
    now apply Rfactorial_gt_0; auto with rnat.
  lra.
replace (17 / (Rfactorial 4 * (n - 4))) with
     (/Rfactorial 4 * (17 / (n - 4))); cycle 1.
  field.
  split.
    shelve.
    (* When discovering the duplication, users could go back and include
       the proof that 4! is non zero as an shared first proof. *)
  assert (0 < Rfactorial 4).
    now apply Rfactorial_gt_0; auto with rnat.
  lra.
apply Rmult_eq_compat_l.
(* We need a better tool to move multiplication and division on both sides of
   equality *)
apply (Rmult_eq_reg_l (5 * (n - 4))); cycle 1.
  assert (0 < n - 4).
    shelve.
  lra.
field_simplify; cycle 1.
  assert (0 < n - 4).
    shelve.
  lra.
apply (Rplus_eq_reg_l 4).
field_simplify.
(* The solution has been discovered! *)
rewrite Heqn.
(* Instantiate the unknown, and propagate *)
reflexivity.
Unshelve.
(* There are two kinds of postponed goals.  The first kind is about showing that
   n - 4 or n - 5 is an integer. Here is a way to prove it. *)
rewrite Heqn.
auto with rnat.
(* Let solve all the goals where the same tactic works. *)
all : try solve [rewrite Heqn; auto with rnat].
(* All the remaining goal are about showing that n - 4 is positive, when
  one knows that n = 89.  lra uses the context and will solve that. *)
all : lra.
Qed.
