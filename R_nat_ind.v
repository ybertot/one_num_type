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

Lemma even_minus2 (n : R) :
  Rnat n -> multiple 2 (n + 2) -> multiple 2 n.
Proof.
intros nnat evennp2.
replace n with (n + 2 - 2) by ring.
apply multiple_sub; auto; try lra.
  assert (tmp := Rnat_ge0 _ nnat); lra.
exists 1; split; auto; ring.
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
assert (nsqr : Rnat (n * n)) by now apply Rnat_mul.
case (not_even_and_odd (n * n) nsqr evensqr).
exists (k * k * 2 + (n - 1)).
split.
  apply Rnat_add;[apply Rnat_mul;[apply Rnat_mul | ] | ]; auto.
  rewrite keq; apply Rnat_mul; auto.
replace n with (n - 1 + 1) by ring; rewrite keq.
ring.
Qed.

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
      now simpl; rewrite Rmult_1_r; apply Rnat_mul; auto.
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
