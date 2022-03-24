Require Import Reals ClassicalEpsilon Lia Lra List.
From Coquelicot Require Import Coquelicot.
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

Lemma Rnat_INR n : Rnat (INR n).
Proof. now exists n. Qed.

#[export]
Hint Resolve Rnat_INR : core.

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

Lemma course_of_value_induction (P : R -> Prop) :
  (forall p, (forall r, r < p -> Rnat r -> P r) -> Rnat p -> P p) ->
  forall n, Rnat n -> P n.
Proof.
intros main n nnat.
enough (course_of_value : forall x, x <= n -> Rnat x -> P x).
  apply course_of_value; auto; lra.
induction nnat as [ | p pnat Ih] using Rnat_ind.
  intros r rle0 rnat; apply main; auto.
  assert (rge0 := Rnat_ge0 _ rnat).
  intros r' r'ltr r'nat.
  assert (r'ge0 := Rnat_ge0 _ r'nat); lra.
intros x xlep1 xnat; assert (xge0 := Rnat_ge0 _ xnat).
assert (xltp1Veq : x < p + 1 \/  x = p + 1) by lra.
  destruct xltp1Veq as [xltp1 | xisp1].
  assert (xlep : x <= p) by now apply Rnat_lt_succ.
  apply main; auto.
  intros r rltx rnat; apply Ih; auto; lra.
apply main; auto.
intros r rltx rnat.
assert (rlep : r <= p) by now apply Rnat_lt_succ; auto; lra.
now apply Ih; auto.
Qed.

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

#[export]
Hint Resolve Rnat_mul : core.

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

Lemma Rseq_nat (n m : R) : Rnat n -> Rnat m ->
  List.Forall (fun i => Rnat i) (Rseq n m).
Proof.
intros nnat mnat; revert n nnat.
induction mnat as [ | p pnat Ih] using Rnat_ind; intros n nnat.
  now rewrite Rseq0.
now rewrite Rseq_S; auto.
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

#[export]
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

Section sqrt2_not_rational.

Definition multiple (a b : R) :=
  exists k, Rnat k /\ b = k * a.

Lemma multiple_sub (a b c : R) :
  0 < a ->
  c <= b -> multiple a b -> multiple a c -> multiple a (b - c).
Proof.
intros agt0 cmp [k [nk mb]] [l [nl mc]].
exists (k - l); split.
  apply Rnat_sub; auto.
  (* Here nra finishes the proof. *)
  apply (Rmult_le_reg_r a); auto.
  now rewrite <- mc, <- mb.
now rewrite Rmult_minus_distr_r, mb, mc.
Qed.

Lemma even_or_odd (n : R) :
  Rnat n -> multiple 2 n \/ multiple 2 (n - 1).
Proof.
induction 1 as [ | p pnat Ih] using Rnat_ind.
  left; exists 0; split; auto; field.
destruct Ih as [mp | [l [lnat mp]]].
  now right; replace (p + 1 - 1) with p by ring.
left; exists (l + 1); split; auto; lra.
Qed.

Lemma not_even_and_odd (n : R) :
  Rnat n -> multiple 2 n -> ~multiple 2 (n - 1).
Proof.
enough (Rnat n -> ((multiple 2 n -> ~multiple 2 (n - 1)) /\
                   (multiple 2 (n + 1) -> ~multiple 2 n))).
  tauto.
induction 1 as [ | p pnat Ih] using Rnat_ind.
  split.
    intros _ [k [knat odd0]].
    assert (tmp := Rnat_ge0 _ knat); lra.
  rewrite Rplus_0_l; intros [k [knat even1]].
  revert even1; induction knat as [ | p pnat Ih] using Rnat_ind.
    lra.
  assert (tmp := Rnat_ge0 _ pnat); lra.
split.
  replace (p + 1 - 1) with p by ring.
  tauto.
destruct Ih as [Ih1 Ih2].
replace (p + 1 + 1) with (p + 2) by ring.
intros evenpp2.
assert (evenp : multiple 2 p).
  replace p with (p + 2 - 2) by ring; apply multiple_sub; auto; try lra. 
  assert (tmp := Rnat_ge0 _ pnat); lra.
  exists 1; split; auto; ring.
intros [k [knat evenpp1]]; case (Ih1 evenp).
assert (tmp := Rnat_ge0 _ knat).
exists (k - 1); split;[ | lra].
apply Rnat_sub; auto.
assert (tmp' := Rnat_ge0 _ pnat).
apply Rnat_gt_pred; auto; lra.
(* This part is a bit iffy, lra solves the problem in ways I don't
  really understand. *)
Qed.

Lemma even_square_to_even (n : R) :
  Rnat n -> multiple 2 (n * n) -> multiple 2 n.
Proof.
intros nnat evensqr.
case (even_or_odd _ nnat); auto.
intros [k [knat keq]].
assert (nsqr : Rnat (n * n)) by auto.
case (not_even_and_odd (n * n) nsqr evensqr).
exists (k * k * 2 + (n - 1)).
split;[now rewrite keq; auto | ].
replace n with (n - 1 + 1) by ring.
rewrite keq; ring.
Qed.

Lemma sqr2_not_rational (p q : R) :
  Rnat p -> Rnat q -> q <> 0 -> 2 <> (p ^ 2 / q ^ 2).
Proof.
intros pnat qnat qn0 abs.
assert (abs' : q ^ 2 * 2 = p ^ 2).
  assert (0 < q ^ 2) by nra.
  apply (Rmult_eq_reg_r (/ q ^ 2)).
  rewrite abs; field; auto.
  apply Rinv_neq_0_compat; nra.
clear abs.
assert (main :
     forall p q,  Rnat p /\ Rnat q /\ q <> 0 /\ q ^ 2 * 2 = p ^ 2 ->
        exists r, r < q /\ Rnat r /\ r <> 0 /\ r ^ 2 * 2 = q ^ 2).
  clear p q pnat qnat qn0 abs'.
  intros p q [pnat [qnat [qn0 sqrt2eq]]].
  assert (evenp2 : multiple 2 (p * p)).
    exists (q ^ 2); split.
      now simpl; auto.
    nra.
  destruct (even_square_to_even _ pnat evenp2) as [k [knat kp]].
  exists k.
  assert (kgt0 : 0 < k).
    assert (tmp := Rnat_ge0 _ knat); nra.
  assert (keq : (k ^ 2) * 2 = q ^ 2).
    apply (Rmult_eq_reg_r 2); try lra.
    replace (k ^ 2 * 2 * 2) with ((k * 2) ^ 2) by ring.
    rewrite <- kp; lra.
  assert (kltq : k < q).
    assert (k ^ 2 < q ^ 2) by nra.
    case (Rlt_le_dec k q); auto.
    intros qlek; enough (q ^ 2 <= k ^ 2) by nra.
    apply pow_incr.
    assert (tmp := Rnat_ge0 _ qnat); lra.
  repeat split; (auto || (try lra)).
revert qn0 p pnat abs'.
elim qnat using course_of_value_induction.
clear q qnat.
intros q Ih qnat qneq0 p pnat sqrt2eq.
destruct (main p q) as [r [rlt1 [rnat [rn0 req]]]].
  now repeat split; auto.
now revert req; apply Ih; auto.
Qed.
  
End sqrt2_not_rational.

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

Section Taylor_Lagrange.

Definition Rnat_to_nat (n : R) : nat :=
  Z.to_nat (Int_part n).

Lemma Rnat_to_natP (n : R) : Rnat n -> INR (Rnat_to_nat n) = n.
Proof.
rewrite Rnat_to_Rnat'; intros [k [keq kge0]].
unfold Rnat_to_nat.
assert (toz : Int_part n = k).
  destruct (base_Int_part n) as [P1 P2].
  rewrite keq in P1 at 2.
  apply le_IZR in P1.
  rewrite keq in P2 at 2.
  rewrite <- minus_IZR in P2.
  apply lt_IZR in P2.
  lia.
now rewrite toz, <- INR_IZN; auto.
Qed.

Lemma Rnat_to_natP' (n : nat) : Rnat_to_nat (INR n) = n.
Proof.
now apply INR_eq; rewrite Rnat_to_natP; auto.
Qed.

Ltac compute_Rnat_to_nat n :=
  match n with
  | IZR Z0 =>
    (replace (IZR Z0) with (INR 0) by reflexivity);
    rewrite (Rnat_to_natP' 0)
  | IZR (Zpos ?x) =>
    let v1 := eval compute in (Pos.to_nat x) in
    replace (IZR (Zpos x)) with (INR v1);
    [ rewrite Rnat_to_natP' | change v1 with (Pos.to_nat x);
        rewrite INR_IZN; auto; lia]
  end.

Definition ex_der_n (f : R -> R) (n : R) :=
  ex_derive_n f (Rnat_to_nat n).

Definition sumn (n : R) := \big[Rplus / 0]_(0 <= x < n) x.

Ltac rid_of_Rnat :=   match goal with |- Rnat ?A => field_simplify A end; auto.

Lemma sumn_eq (n : R) : Rnat n -> sumn n = n * (n - 1) / 2.
Proof.
induction 1 using Rnat_ind.
  unfold sumn.
  rewrite big0.
  field.
unfold sumn; rewrite big_recr; cycle 1.
    exact associative_monoid_Rplus.
  rid_of_Rnat.
  apply Rnat_ge0 in H.
 lra.
field_simplify.
field_simplify (k + 1 - 1).
unfold sumn in IHRnat.
rewrite IHRnat.
field.
Qed.

Definition fact (n : R) := \big[Rmult / 1]_(1 <= x < n + 1) x.

Lemma fact_ge0 n : Rnat n -> 1 <= fact n.
Proof.
induction 1 as [ | p pnat Ih] using Rnat_ind .
  unfold fact.
  field_simplify (0 + 1).
  rewrite big0.
  lra.
replace (fact (p + 1)) with (fact p * (p + 1)). (* postponed justification *)
  replace 1 with (1 * 1) at 1 by field.
  apply Rmult_le_compat; try lra.
  apply Rnat_ge0 in pnat; lra.
(* Now proving the postponed justification *)
unfold fact at 2.
rewrite big_recr; auto.
    field_simplify (p + 1 + 1 - 1).
    easy.
  field_simplify (p + 1 + 1 - 1); auto.
apply Rnat_ge0 in pnat; lra.
Qed.

Definition Der_n (f : R -> R) (n : R) :=
  Rnat_iter n (fun (dp : R -> R) => Derive dp) f.

Lemma Der_n_correct (f : R -> R) (n : nat) (x : R) :
  Der_n f (INR n) x = Derive_n f n x.
Proof.
revert x; induction n as [ | p Ih]; intros x.
  now unfold Der_n; simpl; rewrite Rnat_iter0.
unfold Der_n; rewrite S_INR, Rnat_iterS; auto; simpl.
apply Derive_ext; exact Ih.
Qed.

Lemma Der_n_0 (f : R -> R) x : Der_n f 0 x = f x.
Proof.
replace 0 with (INR 0) by (simpl; ring).
now rewrite Der_n_correct.
Qed.

Lemma Der_n_S (f : R -> R) n x : Rnat n -> 1 <= n ->
  Der_n f n x = Derive (Der_n f (n - 1)) x.
Proof.
intros [[ | p] peq] nge1.
  rewrite peq in nge1; simpl in nge1; lra.
rewrite peq, Der_n_correct.
change 1 with (INR 1); rewrite <- minus_INR; try lia.
simpl; apply Derive_ext; intros t; rewrite Der_n_correct.
now rewrite Nat.sub_0_r.
Qed.

Lemma sum_f_R0_big f n :
  sum_f_R0 f n = \big[Rplus / 0]_(0 <= x < INR n + 1) f (Rnat_to_nat x).
Proof.
induction n as [ | p Ih].
  simpl.
  rewrite big_recr; try (lra || auto).
    replace (0 + 1 - 1) with 0 by ring.
    rewrite big0, Rplus_0_l.
    replace 0 with (INR 0) by auto.
    now rewrite Rnat_to_natP'.
  replace (0 + 1 - 0) with 1 by ring; auto.
rewrite S_INR; simpl; rewrite big_recr; try (lra || auto).
    replace (INR p + 1 + 1 - 1) with (INR p + 1) by ring.
    rewrite <- Ih; clear Ih.
    now rewrite <- S_INR, Rnat_to_natP'.
  now apply Rnat_sub; auto with real.
now auto with real.
Qed.

Lemma Rnat_to_nat0 : Rnat_to_nat 0 = 0%nat.
Proof.
now replace 0 with (INR 0) by (simpl; ring); rewrite Rnat_to_natP'.
Qed.

Lemma Rnat_to_natS n :
  Rnat n -> Rnat_to_nat (n + 1) = S (Rnat_to_nat n).
Proof.
now intros [n' n'eq]; rewrite n'eq, <- S_INR, !Rnat_to_natP'.
Qed.


Lemma factP n : Rnat n -> fact n = INR (Factorial.fact (Rnat_to_nat n)).
Proof.
induction 1 as [ | p pnat Ih] using Rnat_ind.
  unfold fact.
  replace (0 + 1) with 1 by ring.
  rewrite big0.
  replace 0 with (INR 0) by (simpl; ring); rewrite Rnat_to_natP'.
  easy.
replace (fact (p + 1)) with ((p + 1) * fact p).
  rewrite Rnat_to_natS; auto; cbn [Factorial.fact].
  rewrite mult_INR, S_INR, Rnat_to_natP; auto.
  now rewrite Ih.
unfold fact at 2.
rewrite big_recr; auto.
    replace (p + 1 + 1 - 1) with (p + 1) by ring.
    now rewrite Rmult_comm.
  now replace (p + 1 + 1 - 1) with (p + 1) by ring; auto.
assert (tmp := Rnat_ge0 p pnat); lra.
Qed.

Lemma big_eq_Rnat (E2 E1 : R -> R)
  (f : R -> R -> R) (idx : R) (a b : R) :
  (forall i, Rnat i -> E1 i = E2 i) ->
  Rnat a -> Rnat b -> a <= b ->
  \big[f / idx]_(a <= i < b) E1 i =
  \big[f / idx]_(a <= i < b) E2 i.
Proof.
intros ext anat bnat altb.
rewrite (map_ext_Forall _ E2); auto.
rewrite Forall_forall; intros x xin.
apply ext; revert x xin; rewrite <- Forall_forall.
apply Rseq_nat; auto.
now apply Rnat_sub.
Qed.

Definition Rnat_pow (x n : R) := x ^ Rnat_to_nat n.

Lemma Taylor_Lagrange (f : R -> R) (n x y : R) :
  Rnat n ->
  x < y ->
  (forall t, x <= t <= y ->
     forall k,  Rnat k -> k <= n + 1 -> ex_der_n f k t) ->
  exists zeta : R,
     x < zeta < y /\
     f y =
     \big[Rplus / 0]_(0 <= m < n + 1)
        (Rnat_pow (y - x) m / fact m * Der_n f m x) +
     Rnat_pow (y - x) (n + 1) / fact (n + 1) * Der_n f (n + 1) zeta.
Proof.
intros [n' n'eq]; rewrite n'eq.
intros xlty.
intros ders.
assert (ders' :
  forall t, x <= t <= y -> forall k, (k <= S n')%nat -> ex_derive_n f k t).
  intros t xty k kleSn'.
  assert (INRkleSn' : INR k <= INR n' + 1).
    change 1 with (INR 1).
    now rewrite <- plus_INR, Nat.add_1_r; apply le_INR.
  generalize (ders t xty (INR k) (Rnat_INR _) INRkleSn').
  now unfold ex_der_n; rewrite Rnat_to_natP'.
destruct (Derive.Taylor_Lagrange f n' x y xlty ders') as
  [zeta [intzeta eqn]].
exists zeta; split;[exact intzeta | rewrite eqn].
rewrite sum_f_R0_big.
assert (ext: forall i,  Rnat i ->
   (y - x) ^ Rnat_to_nat i / INR (Factorial.fact (Rnat_to_nat i)) *
     Derive_n f (Rnat_to_nat i) x =
   Rnat_pow (y - x) i / fact i * Der_n f i x).
  intros i [i' i'eq]; rewrite i'eq, factP; auto.
  rewrite Der_n_correct; auto.
  now unfold Rnat_pow; rewrite !Rnat_to_natP'.
rewrite (big_eq_Rnat _ _ Rplus 0 _ _ ext); auto.
  apply f_equal.
  rewrite <- S_INR, factP; auto.
  unfold Rnat_pow; rewrite !Rnat_to_natP'.
  now rewrite Der_n_correct.
now auto with real.
Qed.

Lemma Rnat_to_nat_interval n : 0 <= n ->
  INR (Rnat_to_nat n) <= n < INR (Rnat_to_nat n) + 1.
Proof.
intros nge0; unfold Rnat_to_nat.
rewrite <- INR_IZN.
  assert (tmp := base_Int_part n); lra.
enough (-1 < Int_part n)%Z by lia.
assert (tmp := base_Int_part n).
apply lt_IZR; lra.
Qed.

Lemma ex_der_n_0 f x : ex_der_n f 0 x.
Proof.
now unfold ex_der_n; rewrite Rnat_to_nat0.
Qed.

Lemma ex_der_n_S' n f x :
  Rnat n ->
  1 <= n ->
  ex_der_n f n x <-> ex_derive (Der_n f (n - 1)) x.
Proof.
intros nnat nge1.
unfold ex_der_n.
assert (exists p, Rnat_to_nat n = S p) as [p pneq].
  destruct (Rnat_to_nat n) as [ | p] eqn:rnat_eq; cycle 1.
    now exists p.
  assert (nge0 : 0 <= n) by lra.
  destruct (Rnat_to_nat_interval n nge0) as [_ abs].
  rewrite rnat_eq in abs; simpl in abs; lra.
rewrite pneq; simpl.
assert (nm1nat : Rnat (n - 1)) by now apply Rnat_sub; auto.
assert (nm1eq : n - 1 = INR p).
  enough (step : n = INR p + INR 1) by now simpl in step; lra.
  now rewrite <- plus_INR, Nat.add_1_r, <- pneq, Rnat_to_natP.
rewrite nm1eq.
split;
  now apply ex_derive_ext; intros t; rewrite Der_n_correct.
Qed.

Lemma Rnat_pow_S x n : Rnat (n - 1) -> Rnat_pow x n = Rnat_pow x (n - 1) * x.
Proof.
intros nnat.
unfold Rnat_pow.
replace n with ((n - 1) + 1) at 1 by ring.
rewrite Rnat_to_natS; simpl;[ring | easy].
Qed.

Lemma Rnat_pow_0 x : Rnat_pow x 0 = 1.
Proof.
unfold Rnat_pow; rewrite Rnat_to_nat0; ring.
Qed.

Lemma is_derive_Rnat_pow_0 :
  forall t, is_derive (fun x => Rnat_pow x 0) t 0.
Proof.
intros t; unfold Rnat_pow; rewrite Rnat_to_nat0.
auto_derive; auto; ring.
Qed.

Global Instance UnaryDiff_Rnat0 :
  UnaryDiff (fun x => Rnat_pow x 0).
Proof.
exists (fun x => 0).
now apply is_derive_Rnat_pow_0.
Defined.

Lemma is_derive_Rnat_pow_S :
  forall n, Rnat n -> 1 <= n ->
  forall t,
  is_derive (fun x => Rnat_pow x n) t (n * Rnat_pow t (n - 1)).
Proof.
intros n nnat nge1 t.
unfold Rnat_pow.
auto_derive; auto.
rewrite Rnat_to_natP, Rmult_1_l; auto.
replace n with ((n - 1) + 1) at 2 by ring.
rewrite Rnat_to_natS; auto; simpl.
apply Rnat_sub; auto; lra.
Qed.

Global Instance UnaryDiff_Rnat_powS :
  forall n, Rnat n -> 1 <= n -> UnaryDiff (fun x => Rnat_pow x n).
Proof.
  intros n nnat nge0.
  exists (fun x => n * Rnat_pow x (n - 1)).
intros x.
now apply is_derive_Rnat_pow_S.
Defined.

Lemma Rnat_pow1n n : Rnat n -> Rnat_pow 1 n = 1.
Proof.
intros nnat; induction nnat as [ | p pnat Ih] using Rnat_ind.
  now rewrite Rnat_pow_0.
rewrite Rnat_pow_S; replace (p + 1 - 1) with p by ring; auto.
rewrite Ih; ring.
Qed.

Lemma Rnat_pow_incr x y n :
  Rnat n -> 0 < n -> 0 < x < y -> 0 < Rnat_pow x n < Rnat_pow y n.
Proof.
induction 1 as [ | p pnat Ih] using Rnat_ind.
  lra.
generalize (refl_equal p).
pattern p at -1; induction pnat as [ | q qnat _] using Rnat_ind.
  intros pis0 _ xlty.
  replace (0 + 1) with 1 by ring.
  rewrite (Rnat_pow_S x), (Rnat_pow_S y); replace (1 - 1) with 0 by ring;
    auto.
  now rewrite !Rnat_pow_0, !Rmult_1_l.
intros peq _ xlty; rewrite <- peq.
rewrite !(Rnat_pow_S _ (p + 1)); replace (p + 1 - 1) with p by ring;
  try (now rewrite peq; auto).
assert (pgt0 : 0 < p).
  assert (tmp := Rnat_ge0 _ qnat); lra.
assert (Ih' := Ih pgt0 xlty).
split.
  apply Rmult_lt_0_compat; lra.
apply Rlt_trans with (Rnat_pow x p * y).
  nra.
nra.
Qed.

Lemma ln23 : ln 3 - ln 2 < 1 / 2 - 1 / 8 + 1 / 24.
Proof.
assert (tmp:= Taylor_Lagrange ln 2 2 3).
assert (nat2 : Rnat 2) by auto.
assert (cmp23 : 2 < 3) by lra.
assert (ex_der_n0 : forall t, 2 <= t <= 3 -> ex_der_n ln 0 t).
  now intros t tint; apply ex_der_n_0.
assert (dln : forall t, 0 < t ->
         is_derive ln t ((fun x => / x) t)).
  intros t tint; auto_derive; lra.
assert (dV : forall t, 0 < t ->
         is_derive (fun x => / x) t ((fun x => - / (Rnat_pow t 2)) t)).
  intros t tint; auto_derive;[lra | ].
  rewrite 2!Rnat_pow_S; auto.
      replace (2 - 1 - 1) with 0 by ring; rewrite Rnat_pow_0; field; lra.
    now replace (2 - 1 - 1) with 0 by ring; auto.
  now replace (2 - 1) with 1 by ring; auto.
assert (dp2 : forall t,
  Derive (fun x => Rnat_pow x 2) t = 2 * Rnat_pow t (2 - 1)).
  intros t.
  apply is_derive_unique.
  apply is_derive_Rnat_pow_S; auto; lra.
assert (dp3 : forall t,
  Derive (fun x => Rnat_pow x 3) t = 3 * Rnat_pow t (3 - 1)).
  intros t.
  apply is_derive_unique.
  apply is_derive_Rnat_pow_S; auto; lra.
assert (dV2 : forall t, 0 < t ->
         is_derive (fun x => -/ Rnat_pow x 2) t
          ((fun x =>  2 / (Rnat_pow t 3)) t)).
  intros t tint; auto_derive.
    split.
      exists (2 * Rnat_pow t (2 - 1)).
      apply is_derive_Rnat_pow_S; auto; lra.
    split; auto.
    rewrite Rnat_pow_S; replace (2 - 1) with 1 by ring; auto.
    rewrite Rnat_pow_S; replace (1 - 1) with 0 by ring; auto.
    rewrite Rnat_pow_0; nra.
  rewrite dp2.
  rewrite !Ropp_mult_distr_l, Ropp_involutive, Rmult_1_l.
  replace (2 - 1) with 1 by ring.
  rewrite Rnat_pow_S; replace (1 - 1) with 0 by ring; auto.
  rewrite Rnat_pow_0, Rmult_1_l.
  rewrite (Rnat_pow_S _ 3); replace (3 - 1) with 2 by ring; auto.
  rewrite 2!Rnat_pow_S; replace (2 - 1) with 1 by ring;
   replace (1 - 1) with 0 by ring; auto.
  rewrite Rnat_pow_0, Rmult_1_l; field; lra.
assert (dV3 : forall t, 0 < t ->
          is_derive (fun x => 2 / Rnat_pow x 3) t
                ((fun x => -6 / Rnat_pow t 4) t)).
  intros t tint; auto_derive.
    split.
      exists (3 * Rnat_pow t (3 - 1)).
      apply is_derive_Rnat_pow_S; auto; lra.
    split; auto.
    rewrite Rnat_pow_S; replace (3 - 1) with 2 by ring; auto.
    rewrite Rnat_pow_S; replace (2 - 1) with 1 by ring; auto.
    rewrite Rnat_pow_S; replace (1 - 1) with 0 by ring; auto.
    rewrite Rnat_pow_0, Rmult_1_l.
    repeat apply Rmult_integral_contrapositive_currified; lra.
  rewrite (Rnat_pow_S _ 4); replace (4 - 1) with 3 by ring; auto.
  rewrite dp3.
  rewrite (Rnat_pow_S _ 3); replace (3 - 1) with 2 by ring; auto.
  rewrite 2!Rnat_pow_S;
   replace (2 - 1) with 1 by ring;
   replace (1 - 1) with 0 by ring; auto.
  rewrite Rnat_pow_0, Rmult_1_l; field; lra.
assert (tmp2 := tmp nat2 cmp23); clear tmp; rename tmp2 into tmp.
assert (der1 : forall t, 0 < t -> Der_n ln 1 t = / t).
  intros t tgt0; rewrite Der_n_S; auto; try lra.
  apply is_derive_unique; replace (1 - 1) with 0 by ring.
  now generalize (dln t tgt0); apply is_derive_ext; intros u; rewrite Der_n_0.
assert (der2 : forall t, 0 < t -> Der_n ln 2 t = - / Rnat_pow t 2).
  intros t tgt0; rewrite Der_n_S; auto; try lra.
  apply is_derive_unique; replace (2 - 1) with 1 by ring.
  generalize (dV t tgt0); apply is_derive_ext_loc.
  exists (mkposreal _ tgt0); simpl; intros u uloc.
  apply Rabs_def2 in uloc; unfold minus, plus, opp in uloc; simpl in uloc.
  assert (uint0 : 0 < u) by lra.
  now symmetry; apply der1.
assert (der3 : forall t, 0 < t -> Der_n ln 3 t = 2 / Rnat_pow t 3).
  intros t tgt0; rewrite Der_n_S; auto; try lra.
  apply is_derive_unique; replace (3 - 1) with 2 by ring.
  generalize (dV2 t tgt0); apply is_derive_ext_loc.
  exists (mkposreal _ tgt0); simpl; intros u uloc.
  apply Rabs_def2 in uloc; unfold minus, plus, opp in uloc; simpl in uloc.
  assert (uint0 : 0 < u) by lra.
  now symmetry; apply der2.
assert (allders : forall t, 2 <= t <= 3 ->
          forall k,  Rnat k -> k <= 2 + 1 -> ex_der_n ln k t).
  intros t tint k knat.
  assert (tint0 : 0 < t) by lra.
  induction knat as [ | k1 k1nat _] using Rnat_ind.
    now intros _; apply ex_der_n0.
  intros k1le'; assert (k1le : k1 <= 2) by lra; clear k1le'.
  rewrite ex_der_n_S'; replace (k1 + 1 - 1) with k1 by ring; auto; cycle 1.
    assert (tmp3 := Rnat_ge0 _ k1nat); lra.
  revert k1le; induction k1nat as [ | k2 k2nat _] using Rnat_ind.
    intros _.
    exists (/ t).
    generalize (dln _ tint0); apply is_derive_ext.
    now intros u; rewrite Der_n_0.
  intros k2le'; assert (k2le : k2 <= 1) by lra; clear k2le'.
  revert k2le; induction k2nat as [ | k3 k3nat _] using Rnat_ind.
    intros _.
    exists (- / Rnat_pow t 2).
    replace (0 + 1) with 1 by ring.
        generalize (dV _ tint0); apply is_derive_ext_loc.
    exists posreal_one.
    intros u uloc.
    apply Rabs_def2 in uloc; unfold minus, plus, opp in uloc; simpl in uloc.
    assert (uint0 : 0 < u) by lra.
    now rewrite der1.
  intros k3le0.
  assert (tmp3 := Rnat_ge0 _ k3nat).
  assert (k3is0 : k3 = 0) by lra; clear tmp3.
  rewrite k3is0.
  replace (0 + 1 + 1) with 2 by (simpl; ring).
  exists (2 / Rnat_pow t 3).
  generalize (dV2 _ tint0).
  apply is_derive_ext_loc.
  exists (mkposreal _ tint0).
  intros u uloc.
  apply Rabs_def2 in uloc; unfold minus, plus, opp in uloc; simpl in uloc.
  assert (uint0 : 0 < u) by lra.
  now rewrite der2.
destruct (tmp allders) as [zeta [zetaint formula]]; clear tmp.
assert (fact0 : fact 0 = 1).
  now unfold fact; replace (0 + 1) with 1 by ring; rewrite big0.
assert (fact1 : fact 1 = 1).
  unfold fact; rewrite big_recl; auto; try lra; cycle 1.
    now replace (1 + 1 - 1) with 1 by ring; auto.
  rewrite big0; ring.
assert (fact2 : fact 2 = 2).
  unfold fact; rewrite big_recl; auto; try lra; cycle 1.
    now replace (2 + 1 - 1) with 2 by ring; auto.
  rewrite big_recl; auto; try lra; cycle 1.
    now replace (2 + 1 - (1 + 1)) with 1 by ring; auto.
  rewrite big0; ring.
assert (fact3 : fact 3 = 6).
  unfold fact; rewrite big_recl; auto; try lra; cycle 1.
    now replace (3 + 1 - 1) with 3 by ring; auto.
  rewrite big_recl; auto; try lra; cycle 1.
    now replace (3 + 1 - (1 + 1)) with 2 by ring; auto.
  rewrite big_recl; auto; try lra; cycle 1.
    now replace (3 + 1 - (1 + 1 + 1)) with 1 by ring; auto.
  replace (1 + 1 + 1 + 1) with 4 by ring.
  replace (3 + 1) with 4 by ring.
  rewrite big0; ring.
revert formula; rewrite big_recr; auto; try lra; cycle 1.
  now replace (2 + 1 - 0) with 3 by ring; auto.
replace (2 + 1) with 3 by ring.
replace (3 - 1) with 2 by ring.
replace (3 - 2) with 1 by ring.
rewrite fact2, fact3, !Rnat_pow1n; auto.
rewrite big_recr; auto; try lra; cycle 1.
  now replace (2 - 0) with 2 by ring; auto.
replace (2 - 1) with 1 by ring.
rewrite Rnat_pow1n; auto.
rewrite big_recl; auto; try lra; cycle 1.
  now replace (1 - 0) with 1 by ring; auto.
replace (0 + 1) with 1 by ring.
rewrite big0, !Rnat_pow1n, fact0, fact1; auto.
rewrite Der_n_0, der1, der2, der3; try lra.
replace (1 / 1 * ln 2) with (ln 2) by field.
replace (1 / 1 * / 2) with (/ 2) by field.
intros tf_formula; rewrite tf_formula; clear tf_formula.
rewrite 2!Rnat_pow_S;
    replace (2 - 1 - 1) with 0 by ring; auto; cycle 1.
  now replace (2 - 1) with 1 by ring; auto.
rewrite Rnat_pow_0.
assert (Rnat_pow zeta 3 <> 0).
  rewrite 3!Rnat_pow_S; cycle 1.
        now replace (3 - 1 - 1 - 1) with 0 by ring; auto.
      now replace (3 - 1 - 1) with 1 by ring; auto.
    now replace (3 - 1) with 2 by ring; auto.
  replace (3 - 1 - 1 - 1) with 0 by ring; rewrite Rnat_pow_0.
  rewrite Rmult_1_l.
  repeat apply Rmult_integral_contrapositive_currified; lra.
match goal with |- ?x < _ =>
  replace x with (1 / 2 - 1 / 8 + 1 / ( 3 * Rnat_pow zeta 3));
  [ | now field; auto]
end.
repeat apply Rplus_lt_compat_l.
apply Rmult_lt_compat_l;[lra | ].
apply Rinv_1_lt_contravar;[lra | ].
apply Rle_lt_trans with (3 * Rnat_pow 2 3).
  rewrite 3!Rnat_pow_S; cycle 1.
        now replace (3 - 1 - 1 - 1) with 0 by ring; auto.
      now replace (3 - 1 - 1) with 1 by ring; auto.
    now replace (3 - 1) with 2 by ring; auto.
  replace (3 - 1 - 1 - 1) with 0 by ring; rewrite Rnat_pow_0; lra.
enough (Rnat_pow 2 3 < Rnat_pow zeta 3) by lra.
assert (rnat3 : Rnat 3) by auto.
assert (gt0 : 0 < 3) by lra.
assert (zetagt2 : 0 < 2 < zeta) by lra.
assert (tmp := Rnat_pow_incr _ _ _ rnat3 gt0 zetagt2); lra.
Qed.

(* This example shows that all lemmas about pow should be ported for
  Rnat_pow. *)

(* It also shows that computation about immediate natural number values
  needs to be made more fluid: see all the patterns
     replace ... with ... by ring  *)
