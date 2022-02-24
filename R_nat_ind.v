Require Import Reals ClassicalEpsilon Lia Lra List.

Import ListNotations.

Open Scope R_scope.

Definition Rnat (x : R) := exists n, x = INR n.

Definition Rnat' (x : R) := exists z, x = IZR z /\ (0 <= z)%Z.

Lemma Rnat_to_Rnat' r : Rnat r <-> Rnat' r.
Proof.
split; intros [w pw].
  exists (Z.of_nat w).
  split; [now rewrite pw; apply INR_IZR_INZ | ].
  apply Zle_0_nat.
exists (Z.to_nat w).
rewrite INR_IZR_INZ, Z2Nat.id; tauto.
Qed.

Lemma Rnat_IZR z : (0 <= z)%Z -> Rnat (IZR z).
Proof.
intros znn; rewrite Rnat_to_Rnat'.
now unfold Rnat'; eapply ex_intro;split; [eapply eq_refl | ].
Qed.

#[export]
Hint Extern 1 (Rnat (IZR _)) => (now apply Rnat_IZR; discriminate) : core.

Lemma Rnat_ind (n : R) (P : R -> Prop) :
  P 0 ->
  (forall k, Rnat k -> P k -> P (k + 1)) ->
  Rnat n ->
  P n.
Proof.
intros P0 Pf [n' nnat].
rewrite nnat; clear nnat; induction n'.
  exact P0.
rewrite S_INR; apply Pf.
  now exists n'.
exact IHn'.
Qed.

Lemma Rnat_ge0 (x : R) : Rnat x -> 0 <= x.
intros [x' xnat]; rewrite xnat; apply pos_INR.
Qed.

Lemma Rnat_lt_succ (x y : R) : Rnat x -> Rnat y ->
  x < y + 1 -> x <= y.
Proof.
intros [x' xnat] [y' ynat].
change 1 with (INR 1); rewrite xnat, ynat, <- plus_INR.
intros hlt; apply INR_lt in hlt; apply le_INR; lia.
Qed.

Lemma Rnat_gt_pred (x y : R) : Rnat x -> Rnat y ->
  x - 1 < y -> x <= y.
Proof.
intros xnat ynat hlt; apply Rnat_lt_succ; auto; lra.
Qed.

Lemma Rnat0 : Rnat 0.
Proof. now exists 0%nat. Qed.

Lemma Rnat_imm (x : positive) : Rnat (IZR (Z.pos x)).
Proof.  auto.  Qed.

Example Rnat42 : Rnat 42.
Proof. apply Rnat_imm. Qed.

Lemma Rnat1 : Rnat 1.
Proof. apply Rnat_imm. Qed.

Lemma Rnat_add (x y : R) : Rnat x -> Rnat y -> Rnat (x + y).
Proof.
intros [x' xnat] [y' ynat]; exists (x' + y')%nat.
now rewrite xnat, ynat, plus_INR.
Qed.

#[export]
Hint Resolve Rnat_add : core.

Lemma Rnat_mul (x y : R) : Rnat x -> Rnat y -> Rnat (x * y).
Proof.
intros [x' xnat] [y' ynat]; exists (x' * y')%nat.
now rewrite xnat, ynat, mult_INR.
Qed.

Lemma Rnat_sub (x y : R) : Rnat x -> Rnat y -> y <= x ->
  Rnat (x - y).
Proof.
intros [x' xnat] [y' ynat]; exists (x' - y')%nat.
rewrite xnat, ynat, minus_INR; auto.
now apply INR_le; rewrite <- xnat, <- ynat.
Qed.

Definition Rnat_iter {A : Type} (n : R) (f : A -> A) (e : A) :=
  epsilon (inhabits e)
    (fun v => forall n', n = INR n' -> Nat.iter n' f e = v).

Lemma Rnat_iter0 {A : Type} (f : A -> A) (e : A) : 
  Rnat_iter 0 f e = e.
Proof.
unfold Rnat_iter.
assert (epsP : exists v : A, forall n', 0 = INR n' -> Nat.iter n' f e = v).
  exists e.
  intros [ | n'];[ easy | ].
  rewrite S_INR; intros abs.
  assert (tmp := pos_INR n'); lra.
assert (tmp := epsilon_spec (inhabits e) _ epsP); simpl in tmp.
now generalize (tmp 0%nat refl_equal); simpl; intros it; rewrite <- it.
Qed.

Lemma Rnat_iterS {A : Type} (n : R) (f : A -> A) (e : A) :
  Rnat n ->
  Rnat_iter (n + 1) f e = f (Rnat_iter n f e).
Proof.
intros [n' nn'].
assert (epsP1 : exists v : A, forall n2, n = INR n2 -> Nat.iter n2 f e = v).
  exists (Nat.iter n' f e).
  intros n2; rewrite nn'.
  now intros n'n2; apply INR_eq in n'n2; rewrite n'n2.
assert (tmp := epsilon_spec (inhabits e) _ epsP1); simpl in tmp.
assert (tmp' := tmp n' nn'); unfold Rnat_iter at 2; rewrite <- tmp'.
assert (epsP2 : exists v : A, forall n2, n + 1 = INR n2 ->
            Nat.iter n2 f e = v).
  exists (Nat.iter (S n') f e).
  intros n2; rewrite nn', <- S_INR.
  now intros n'n2; apply INR_eq in n'n2; rewrite n'n2.
assert (tmp2 := epsilon_spec (inhabits e) _ epsP2); simpl in tmp2.
assert (nn1' : n + 1 = INR (S n')) by now rewrite S_INR, nn'.
assert (tmp2' := tmp2 (S n') nn1'); unfold Rnat_iter; rewrite <- tmp2'.
easy.
Qed.

Lemma Rnat_iterS' {A : Type} (n : R) (f : A -> A) (e : A) :
  Rnat (n - 1) ->
  Rnat_iter n f e = f (Rnat_iter (n - 1) f e).
Proof.
intros nn; replace n with ((n - 1) + 1) at 1 by ring.
now apply Rnat_iterS.
Qed.

Lemma Rnat_iter1 {A : Type} (f : A -> A) (e : A) :
  Rnat_iter 1 f e = f e.
Proof.
rewrite Rnat_iterS'; rewrite Rminus_eq_0; auto.
now rewrite Rnat_iter0.
Qed.

Lemma Rnat_iter_add {A : Type} (n m : R) (f : A -> A) (e : A) :
  Rnat n -> Rnat m -> Rnat_iter (n + m) f e = 
    Rnat_iter n f (Rnat_iter m f e).
Proof.
intros nnat mnat.
induction nnat using Rnat_ind.
  now rewrite Rplus_0_l, Rnat_iter0.
replace (k + 1 + m) with (k + m + 1) by ring.
rewrite !Rnat_iterS; auto.
now rewrite IHnnat.
Qed.

Definition Rseq_Prop (n m : R) (v : list R) :=
  forall m' : nat, m = INR m' ->
              v = map (fun e => n + IZR (Z.of_nat e)) (seq 0 m').

Definition Rseq (n m : R) : list R :=
  epsilon (inhabits nil) (Rseq_Prop n m).

(* The next two lemmas reproduce the reduction rules of Coq.Lists.List.seq *)

Lemma Rseq0 (n : R) : Rseq n 0 = nil.
Proof.
assert (exv : exists v, Rseq_Prop n 0 v).
  exists (map (fun e => n + INR e) (seq 0 0)); intros n2.
  change 0 with (INR 0); intros z0; apply INR_eq in z0.
  now rewrite <- z0.
exact (epsilon_spec (inhabits nil)
             (Rseq_Prop n 0) exv 0%nat refl_equal).
Qed.

Lemma Rseq_S (n m : R) : Rnat m ->
  Rseq n (m + 1) = n :: (Rseq (n + 1) m).
Proof.
intros [m' mnat].
assert (exv1 : exists v, Rseq_Prop (n + 1) m v).
  exists (map (fun e => (n + 1) + IZR (Z.of_nat e)) (seq 0 m')).
  intros m''; rewrite mnat; intros mnat'.
  now apply INR_eq in mnat'; rewrite <- mnat'.
assert (exv2 : exists v, Rseq_Prop n (m + 1) v).
  exists (map (fun e => n + IZR (Z.of_nat e)) (seq 0 (S m'))).
  intros m''; rewrite mnat, <- S_INR; intros mnat'.
  now apply INR_eq in mnat'; rewrite mnat'.
assert (m1nat : m + 1 = INR (S m')) by now rewrite mnat, <- S_INR.
assert (tmp := epsilon_spec (inhabits nil) _ exv2 (S m') m1nat).
assert (tmp2 := epsilon_spec (inhabits nil) _ exv1 m' mnat).
unfold Rseq; rewrite tmp, tmp2; simpl.
rewrite Rplus_0_r, <- seq_shift, map_map.
apply f_equal; apply map_ext.
intros a; rewrite Nat2Z.inj_succ, succ_IZR; ring.
Qed.

Lemma Rseq_S' (n m : R) : Rnat (m - 1) ->
  Rseq n m = n :: Rseq (n + 1) (m - 1).
Proof.
intros mn; replace m with (m - 1 + 1) at 1 by ring.
now rewrite Rseq_S; auto.
Qed.

Lemma Rseq_app (n m p : R) : Rnat m -> Rnat p ->
  Rseq n (m + p) = (Rseq n m) ++ Rseq (n + m) p.
Proof.
intros mnat pnat; revert n.
induction mnat as [ | m' m'nat Ih] using Rnat_ind; intros n.
  now rewrite Rseq0, Rplus_0_l, Rplus_0_r.
rewrite Rseq_S';
  replace (m' + 1 + p - 1) with (m' + p) by ring; auto.
rewrite Rseq_S; simpl; auto; rewrite Ih.
now rewrite <- (Rplus_comm 1 m'), <- Rplus_assoc.
Qed.

Lemma INR_IZN x : (0 <= x)%Z -> IZR x = INR (Z.to_nat x).
Proof.
intros xge0.
destruct (IZN _ xge0) as [n Pn].
now rewrite Pn, <- INR_IZR_INZ, Nat2Z.id.
Qed.

Ltac expand_Rseq :=
  match goal with
  | |- context[Rseq ?x (IZR ?y)] =>
    let Hex := fresh "existential_hypothesis" in
    assert (Hex : exists v, Rseq_Prop x (IZR y) v);
    [exists (map (fun e => x + (IZR (Z.of_nat e))) (seq 0 (Z.to_nat y)));
     let y := fresh "y" in
     intros y; rewrite ?INR_IZR_INZ;
     let yeq := fresh "eq_for_y" in
     intros yeq; apply eq_IZR in yeq; rewrite yeq, !Nat2Z.id; reflexivity |
  unfold Rseq;
  rewrite (epsilon_spec (inhabits nil)
             (Rseq_Prop x (IZR y)) Hex (Z.to_nat y));
     [simpl; rewrite <- !plus_IZR; reflexivity | rewrite INR_IZN; auto; lia ]]
  end.

Ltac expand_Rseq' :=
  repeat (rewrite Rseq_S', <- minus_IZR;
     [ | rewrite <- minus_IZR;
        (apply Rnat_imm || apply Rnat0)]); rewrite Rseq0;
        rewrite <- !plus_IZR; reflexivity.

Example seq14 : Rseq 1 4 = [1; 2; 3; 4].
Proof.
expand_Rseq'.
(* expand_Rseq. also works. *)
Qed.

(* We can use structural recursion on datatypes as usual. *)

Fixpoint sumr (l : list R) : R :=
  match l with nil => 0 | a :: tl => a + sumr tl end.

Lemma sumr_app (l1 l2 : list R) :
  sumr (l1 ++ l2) = sumr l1 + sumr l2.
Proof.
induction l1 as [ | a l1 Ih].
  now simpl; rewrite Rplus_0_l.
now simpl; rewrite Ih, Rplus_assoc.
Qed.

Lemma sumr_seq (n : R) : Rnat n -> sumr (Rseq 0 n) = n * (n - 1) / 2.
Proof.
intros nnat; induction nnat using Rnat_ind.
  rewrite Rseq0; try apply Rnat0; simpl.
  (* field. can finish here. *)
  now unfold Rdiv; rewrite !Rmult_0_l.
rewrite Rseq_app; try (apply Rnat0 || apply Rnat1 || assumption).
rewrite sumr_app.
rewrite IHnnat.
replace 1 with (0 + 1) at 2 by now rewrite Rplus_0_l.
rewrite Rseq_S; auto.
rewrite Rseq0; simpl.
  (*  field. can finish here. *)
rewrite Rplus_0_l.
rewrite Rplus_0_r.
unfold Rminus at 2.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
replace k with ((2 * k) / 2) at 3.
  rewrite <- Rdiv_plus_distr.
  rewrite (Rmult_comm k).
  rewrite <- Rmult_plus_distr_r.
  unfold Rminus; rewrite Rplus_assoc.
  (* The next line needs more thinking. *)
  replace (-(1) + 2) with 1 by ring.
  reflexivity.
unfold Rdiv.
rewrite (Rmult_comm 2).
rewrite Rmult_assoc.
rewrite Rinv_r.
  rewrite Rmult_1_r.
  reflexivity.
  (* The next line needs more thinking *)
lra.
Qed.

Fixpoint rlength {A : Type} (l : list A) : R :=
  match l with nil => 0 | a :: tl => rlength tl + 1 end.

Definition rnth {A : Type} (e : A) (n : R) (l : list A) :=
  hd e (Rnat_iter n (@tl A) l).

Notation "'\big[' f / idf ]_( a <= i < b ) E" :=
  (fold_right f  idf (map (fun i => E) (Rseq a (b - a))))
  (at level 35, a at level 30,  b at level 30, E at level 36, f,
   idf at level 10, i at level 0, right associativity).

Lemma Rseq1 n : Rseq n 1 = [n].
Proof.
replace 1 with (0 + 1) at 1 by ring.
now rewrite Rseq_S; auto; rewrite Rseq0; auto.
Qed.

Definition associative_monoid {A : Type} (f : A -> A -> A) (idx : A) :=
  (forall x y z, f x (f y z) = f (f x y) z) /\
   (forall x, f x idx = x) /\
   (forall x, f idx x = x).

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
rewrite Rseq_S'; [ | apply Rnat_sub; auto]; simpl.
  replace (b - a - 1) with (b - (a + 1)) by ring.
  easy.
assert (0 < b - a) by lra.
apply Rnat_gt_pred; auto; lra.
Qed.

Lemma big_recr {A : Type}(E : R -> A) (f : A -> A -> A) (idx : A) (a b : R) :
  associative_monoid f idx ->
  Rnat (b - a) -> a < b ->
  \big[f / idx]_(a <= i < b) E i =
   f (\big[f / idx]_(a <= i < (b - 1)) E i)
    (E (b - 1)).
Proof.
intros amf hnat altb.
assert (induct_arg : Rnat (b - a  - 1)).
  apply Rnat_sub; auto; apply Rnat_gt_pred; auto; lra.
enough (main : forall p, Rnat p ->
  forall a, fold_right f idx (map (fun i => E i) (Rseq a (p + 1))) =
   f (fold_right f idx (map (fun i => E i) (Rseq a p))) (E (a + p))).
  replace (b - a) with (b - a - 1 + 1) by ring.
  rewrite main; auto.
  replace (a + (b - a - 1)) with (b - 1) by ring.
  now replace (b - 1 - a) with (b - a - 1) by ring.
clear hnat altb induct_arg a.
intros p'; induction 1 as [ | p pnat Ih] using Rnat_ind; clear p'.
  intros a; rewrite Rplus_0_l, Rplus_0_r, Rseq0, Rseq1; simpl.
  now destruct amf as [_ [P1 P2]]; rewrite P1, P2.
intros a; rewrite Rseq_S; auto; simpl.
rewrite (Rseq_S a); auto; simpl.
destruct amf as [Pa [P1 P2]].
now rewrite Ih, Pa; replace (a + (p + 1)) with (a + 1 + p) by ring.
Qed.

Lemma associative_monoid_Rplus : associative_monoid Rplus 0.
Proof.
split;[exact (fun x y z => eq_sym (Rplus_assoc x y z))| ].
split;[exact Rplus_0_r | exact Rplus_0_l].
Qed.

Hint Resolve associative_monoid_Rplus : core.

Lemma sumr_again n :
  Rnat n -> \big[Rplus / 0]_(0 <= i < n) i = n * (n - 1) / 2.
Proof.
induction 1 as [ | p Np Ih] using Rnat_ind.
  rewrite big0; field.
assert (Rnat (p + 1 - 0)) by now rewrite Rminus_0_r; auto.
assert (0 < p + 1) by now assert (tmp := Rnat_ge0 _ Np); lra.
rewrite big_recr; auto.
replace (p + 1 - 1) with p by ring.
rewrite Ih; field.
Qed.
