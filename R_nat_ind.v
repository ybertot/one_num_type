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
Proof.
now exists (Pos.to_nat x); rewrite INR_IPR.
Qed.

Example Rnat42 : Rnat 42.
Proof. apply Rnat_imm. Qed.

Lemma Rnat1 : Rnat 1.
Proof. apply Rnat_imm. Qed.

Lemma Rnat_add (x y : R) : Rnat x -> Rnat y -> Rnat (x + y).
Proof.
intros [x' xnat] [y' ynat]; exists (x' + y')%nat.
now rewrite xnat, ynat, plus_INR.
Qed.

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

Lemma Rnat_iter1 {A : Type} (f : A -> A) (e : A) :
  Rnat_iter 1 f e = f e.
Proof.
replace 1 with (0 + 1) by ring.
rewrite Rnat_iterS;[ | exact Rnat0].
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
now apply Rnat_add.
Qed.

Definition Rseq_Prop (n m : R) (v : list R) :=
  forall n' m' : nat, n = INR n' -> m = INR m' ->
              v = map (fun e => IZR (Z.of_nat e)) (seq n' m').

Definition Rseq (n m : R) : list R :=
  epsilon (inhabits nil) (Rseq_Prop n m).

(* The next two lemmas reproduce the reduction rules of Coq.Lists.List.seq *)

Lemma Rseq0 (n : R) : Rnat n -> Rseq n 0 = nil.
Proof.
intros [n' nnat].
assert (exv : exists v, Rseq_Prop n 0 v).
  exists (map INR (seq n' 0)); intros n2 z nn2.
  change 0 with (INR 0); intros z0; apply INR_eq in z0.
  now rewrite <- z0.
exact (epsilon_spec (inhabits nil)
             (Rseq_Prop n 0)
             exv n' 0%nat nnat refl_equal).
Qed.

Lemma Rseq_S (n m : R) : Rnat n -> Rnat m ->
  Rseq n (m + 1) = n :: (Rseq (n + 1) m).
Proof.
intros [n' nnat] [m' mnat].
assert (exv1 : exists v, Rseq_Prop (n + 1) m v).
  exists (map (fun e => IZR (Z.of_nat e)) (seq (S n') m')).
  intros n'' m''; rewrite nnat, mnat; intros nnat' mnat'.
  rewrite <- S_INR in nnat'.
  now apply INR_eq in nnat', mnat'; rewrite <- nnat', mnat'.
assert (exv2 : exists v, Rseq_Prop n (m + 1) v).
  exists (map (fun e => IZR (Z.of_nat e)) (seq n' (S m'))).
  intros n'' m''; rewrite nnat, mnat, <- S_INR; intros nnat' mnat'.
  now apply INR_eq in nnat', mnat'; rewrite <- nnat', mnat'.
assert (m1nat : m + 1 = INR (S m')) by now rewrite mnat, <- S_INR.
assert (n1nat : n + 1 = INR (S n')) by now rewrite nnat, <- S_INR.
assert (tmp := epsilon_spec (inhabits nil) _ exv2 n' (S m') nnat m1nat).
assert (tmp2 := epsilon_spec (inhabits nil) _ exv1 (S n') m' n1nat mnat).
unfold Rseq; rewrite tmp, tmp2; simpl.
now rewrite <- INR_IZR_INZ, nnat.
Qed.


(* This is the translation of theorem seq_app; most of the work is
  automatic. *)
Lemma Rseq_app (n m p : R) : Rnat n -> Rnat m -> Rnat p ->
  Rseq n (m + p) = (Rseq n m) ++ Rseq (n + m) p.
intros [n' nnat] [m' mnat] [p' pnat].
assert (exv1 : exists v, Rseq_Prop n (m + p) v).
  exists (map (fun e => IZR (Z.of_nat e)) (seq n' (m' + p'))).
  intros n'' mp''; rewrite nnat, mnat, pnat; intros nnat' mpnat'.
  rewrite <- plus_INR in mpnat'.
  now apply INR_eq in nnat', mpnat'; rewrite <- nnat', mpnat'.
assert (exv2 : exists v, Rseq_Prop n m v).
  exists (map (fun e => IZR (Z.of_nat e)) (seq n' m')).
  intros n'' m''; rewrite nnat, mnat; intros nnat' mnat'.
  now apply INR_eq in nnat', mnat'; rewrite <- nnat', mnat'.
assert (exv3 : exists v, Rseq_Prop (n + m) p v).
  exists (map (fun e => IZR (Z.of_nat e)) (seq (n' + m') p')).
  intros n'' m''; rewrite nnat, mnat, pnat; intros nmnat' mnat'.
  rewrite <- plus_INR in nmnat'.
  now apply INR_eq in nmnat', mnat'; rewrite <- nmnat', mnat'.
assert (mpnat : m + p = INR (m' + p')) by now rewrite mnat, pnat, plus_INR.
assert (nmnat : n + m = INR (n' + m')) by now rewrite nnat, mnat, plus_INR.
assert (tmp1 :=
   epsilon_spec (inhabits nil) _ exv1 n' (m' + p')%nat nnat mpnat).
assert (tmp2 :=
   epsilon_spec (inhabits nil) _ exv2 n' m' nnat mnat).
assert (tmp3 :=
   epsilon_spec (inhabits nil) _ exv3 (n' + m')%nat p' nmnat pnat).
now unfold Rseq; rewrite tmp1, tmp2, tmp3, seq_app, map_app.
Qed.

Lemma INR_IZN x : (0 <= x)%Z -> IZR x = INR (Z.to_nat x).
Proof.
intros xge0.
destruct (IZN _ xge0) as [n Pn].
now rewrite Pn, <- INR_IZR_INZ, Nat2Z.id.
Qed.

Ltac expand_Rseq :=
  match goal with
  | |- context[Rseq (IZR ?x) (IZR ?y)] =>
    let Hex := fresh "existential_hypothesis" in
    assert (Hex : exists v, Rseq_Prop (IZR x) (IZR y) v);
    [exists (map (fun e => (IZR (Z.of_nat e))) (seq (Z.to_nat x) (Z.to_nat y)));
     let x := fresh "x" in let y := fresh "y" in
     intros x y; rewrite 2!INR_IZR_INZ;
     let xeq := fresh "eq_for_x" in let yeq := fresh "eq_for_y" in
     intros xeq yeq; apply eq_IZR in xeq; apply eq_IZR in yeq; rewrite xeq, yeq, !Nat2Z.id; reflexivity |
  apply (epsilon_spec (inhabits nil) (Rseq_Prop (IZR x) (IZR y)) Hex (Z.to_nat x) (Z.to_nat y)); apply INR_IZN; lia]
  end.

Example seq14 : Rseq 1 4 = [1; 2; 3; 4].
Proof.
expand_Rseq.
Qed.

Definition increase_list (l : list R) :=
  match l with nil => 0::nil | a :: tl => (a + 1) :: l end.

Example increase_list_4 : Rnat_iter 4 increase_list nil =
   3 :: 2 :: 1 :: 0 :: nil.
Proof.
assert (Rnat3 : Rnat (0 + 1 + 1 + 1)).
  exists 3%nat; compute; ring.
assert (Rnat2 : Rnat (0 + 1 + 1)).
  exists 2%nat; compute; ring.
assert (Rnat1 : Rnat (0 + 1)).
  exists 1%nat; compute; ring.
assert (Rnat0 : Rnat 0).
  now exists 0%nat.
assert (four1 : 4 = 0 + 1 + 1 + 1 + 1) by ring.
rewrite four1 at 1.
repeat rewrite Rnat_iterS; auto; cycle 1.
rewrite Rnat_iter0.
simpl.
replace (0 + 1 + 1 + 1) with 3 by ring.
replace (0 + 1 + 1) with 2 by ring.
replace (0 + 1) with 1 by ring.
easy.
Qed.

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
rewrite Rseq_S;[ | apply Rnat_add | ]; try apply Rnat0; auto.
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
  (* end of the proof done by field. *)
repeat apply Rnat_add; auto; apply Rnat0 || apply Rnat1.
Qed.

Definition rev_iota (n : R) := Rnat_iter n increase_list nil.

Lemma riota_head n : Rnat n ->
  hd (-1) (Rnat_iter n increase_list nil) = n - 1.
Proof.
intros nnat; induction nnat using Rnat_ind.
  rewrite Rnat_iter0; simpl; ring.
rewrite Rnat_iterS; auto.
destruct (Rnat_iter k increase_list nil) as [ | b l].
  simpl in IHnnat |- *; lra.
simpl in IHnnat |- *; rewrite IHnnat; ring.
Qed.

Fixpoint rlength {A : Type} (l : list A) : R :=
  match l with nil => 0 | a :: tl => rlength tl + 1 end.

Lemma riota_length n : Rnat n ->
  rlength (rev_iota n) = n.
intros nnat; induction nnat using Rnat_ind.
  now unfold rev_iota; rewrite Rnat_iter0; simpl.
unfold rev_iota in IHnnat |- *.
rewrite Rnat_iterS; auto; destruct (Rnat_iter k increase_list nil) as [ | a l].
  simpl in IHnnat |- *.
  now rewrite <- IHnnat.
simpl in IHnnat |- *.
now rewrite IHnnat.
Qed.

Definition rnth {A : Type} (e : A) (n : R) (l : list A) :=
  hd e (Rnat_iter n (@tl A) l).

Lemma riota_nth (n p : R) : Rnat n -> Rnat p ->
  p < n -> rnth 0 p (rev_iota n) = n - p - 1.
Proof.
intros nnat; revert p.
induction nnat using Rnat_ind.
  intros p pnat; unfold rnth; simpl.
  intros plt0.
  assert (pge0 := Rnat_ge0 p pnat); lra.
intros p pnat pltk1.
assert (plek : p <= k) by (apply Rnat_lt_succ; auto).
case (Req_dec p 0).
  intros p0; unfold rnth; rewrite p0, Rnat_iter0, Rminus_0_r.
  assert (kp1gt0 : 0 < k + 1) by (generalize (Rnat_ge0 k nnat); lra).
  assert (k1nat : Rnat (k + 1)) by (apply Rnat_add;[assumption | apply Rnat1]).
  apply riota_head in k1nat.
  fold (rev_iota (k + 1)) in k1nat.
  destruct (rev_iota (k + 1)); simpl in k1nat |- *; lra.
intros pn0.
assert (pm1nat : Rnat (p - 1)).
  apply Rnat_sub;[exact pnat | exact Rnat1 | ].
  apply Rnat_lt_succ;
   [exact Rnat1 | auto | assert (t := Rnat_ge0 p pnat); lra].
assert (pm1ltk : p - 1 < k) by lra.
assert (IH' := IHnnat _ pm1nat pm1ltk).
replace p with ((p - 1) + 1) by ring.
replace (rev_iota (k + 1)) with (k :: rev_iota k); cycle 1.
  assert (t1 := riota_head k nnat).
  unfold rev_iota; rewrite Rnat_iterS; auto.
  destruct (Rnat_iter _ _ _) as [ | k' l].
    simpl in t1.
    assert (0 <= p - 1) by now apply Rnat_ge0.
    lra.
  simpl in t1 |- *; rewrite t1.
  now replace (k - 1 + 1) with k by ring.
replace (rnth 0 (p - 1 + 1) (k :: rev_iota k)) with
  (rnth 0 (p - 1) (rev_iota k)).
  rewrite IH'; ring.
unfold rnth.
now rewrite Rnat_iter_add, Rnat_iter1; auto.
Qed.

Lemma increase_listP n : Rnat n ->
  sumr (Rnat_iter n increase_list nil) = n * (n - 1) / 2.
Proof.
intros nnat; induction nnat using Rnat_ind.
rewrite Rnat_iter0; simpl; field.
rewrite Rnat_iterS; simpl; auto.
generalize (riota_head k nnat).
destruct (Rnat_iter k increase_list nil) as [ | k' l].
  simpl; intros k0.
  assert (k0' : 0 = k) by lra.
  rewrite <- k0'; field.
simpl in IHnnat |- *.
rewrite IHnnat.
intros k'k; rewrite k'k; field.
Qed.

Fact Rseq_example : Rseq 0 5 = [0; 1; 2; 3; 4].
Proof.
assert (nat0 : Rnat 0) by now exists 0%nat.
assert (nat4 : Rnat 4) by now exists 4%nat; simpl; ring.
change 5%Z with (((((0 + 1) + 1) + 1)+ 1) + 1)%Z;
 rewrite !plus_IZR, !Rseq_S, Rseq0;
 repeat (apply Rnat_add || apply Rnat1 || apply Rnat0).
rewrite <- ! plus_IZR; simpl.
reflexivity.
Qed.

Notation "'\big[' f / idf ]_( a <= i < b ) E" :=
  (fold_left (fun v e => f v E) (Rseq a b))
(at level 35, E at level 36, f, idf at level 10, i at level 0, right associativity).
