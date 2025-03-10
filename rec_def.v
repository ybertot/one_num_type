From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.
From OneNum.srcElpi Extra Dependency "tools.elpi" as tools.
From OneNum.srcElpi Extra Dependency "recursive.elpi" as recursive.


Set Warnings "-notation-overridden".
Require Import R_subsets.
Set Warnings "+notation-overridden".
Require Import Derive.

Open Scope R_scope.

Module private.

(* This lemma could be used to automatically prove that functions
  defined by our new command satisfy the specification that was given
  as a definition.  This lemma is not intended for final users' eyes
  because it exposes the nat type. We may want to add a pre-condition
  to restrict usage to the Rnat subset.  It is not certain this
  lemma will be used much, since unfold does the same trick.
  *)
Lemma Rnat_rec_to_nat_rec_p {A : Type} (v0 : A) (stf : R -> A -> A)
  (p : positive) :
   Rnat_rec v0 stf (IZR (Z.pos p)) =
   nat_rect (fun _ => A) v0 (fun x => stf (INR x))
     (Z.abs_nat (Z.pos p)).
Proof.
unfold Rnat_rec, IRN.
now rewrite IRZ_IZR.
Qed.

Lemma IRN_to_S (r : R) (p : Z) (q : Z):
  (q < p)%Z ->
  Rnat (r - IZR p) -> IRN (r - IZR q) =
     (Z.abs_nat (p - q) + IRN (r - IZR p))%nat.
Proof.
intros qltp rmpnat.
unfold IRN.
destruct (Rnat_exists_nat (r - IZR p)) as [v vq].
assert (rq : r = IZR (Z.of_nat v + p)).
  apply (Rplus_eq_reg_r (- (IZR p))).
  rewrite <- opp_IZR at 2.
  rewrite <- plus_IZR.
  replace (Z.of_nat v + p + - p)%Z with (Z.of_nat v) by ring.
  exact vq.
rewrite <- Zabs2Nat.inj_add.
    rewrite rq.
    rewrite <- minus_IZR, IRZ_IZR.
    rewrite <- minus_IZR.
    replace (Z.of_nat v + p - p)%Z with (Z.of_nat v) by ring.
    rewrite IRZ_IZR.
    apply f_equal.
    ring.
  lia.
rewrite vq, IRZ_IZR.
apply Nat2Z.is_nonneg.
Qed.

Lemma IRN_to_S_top (r : R) (p : Z) :
  (0 < p)%Z ->
  Rnat (r - IZR p) -> IRN r = (Z.abs_nat p + IRN (r - IZR p))%nat.
Proof.
intros pgt0 rmpnat.
unfold IRN.
destruct (Rnat_exists_nat (r - IZR p)) as [v vq].
  assert (rq : r = IZR (Z.of_nat v + p)).
  apply (Rplus_eq_reg_r (- (IZR p))).
  rewrite <- opp_IZR at 2.
  rewrite <- plus_IZR.
  replace (Z.of_nat v + p + - p)%Z with (Z.of_nat v) by ring.
  exact vq.
rewrite <- Zabs2Nat.inj_add.
    rewrite rq.
    rewrite <- minus_IZR, IRZ_IZR.
    replace (Z.of_nat v + p - p)%Z with (Z.of_nat v) by ring.
    rewrite IRZ_IZR.
    apply f_equal.
    ring.
  lia.
rewrite vq, IRZ_IZR.
apply Nat2Z.is_nonneg.
Qed.

Lemma Rnat_Rabs {f : R -> R} {fz : Z -> Z}
  (abs_morph : forall n z, n = IZR z -> f (Rabs n) = IZR (fz z))
  (n : R) (z : Z) (nnat : Rnat n) (nz : n = IZR z) : f n = IZR (fz z).
Proof.
rewrite <- (Rabs_right n);[ | assert (tmp := Rnat_ge0 n nnat); lra].
now apply abs_morph.
Qed.

Lemma nat_rect_list_IZR (l0 : list Z)
  (l' : list R) (f : nat -> list Z -> list Z)
  (f' : nat -> list R -> list R)
  (n : nat) :
  l' = map IZR l0 ->
  (forall k lR lZ, lR = map IZR lZ ->
        f' k lR = map IZR (f k lZ)) ->
  nat_rect (fun _ => list R) l' f' n =
  map IZR (nat_rect (fun _ => list Z) l0 f n).
Proof.
intros ll' ff'; induction n as [ | n Ih].
  easy.
simpl.
apply ff'.
apply Ih.
Qed.

Lemma Rnat_rec_nat (l0 : list R) (f : R -> list R -> list R) (n : R) :
  Forall Rnat l0 ->
  (forall n l, Rnat n -> Forall Rnat l -> Forall Rnat (f n l)) ->
  Rnat n -> Forall Rnat (Rnat_rec l0 f n).
Proof.
intros ln fn.
induction 1 as [ | n nnat Ih].
  now rewrite Rnat_rec0.
rewrite Rnat_rec_succ;[ | assumption].
now apply fn.
Qed.

Lemma Rnat_rec_nat' (l0 : list R) (f : R -> list R -> list R) :
  (forall k, Rnat (nth k l0 0)) ->
  (forall n l, (forall k, Rnat (nth k l 0)) ->
     Rnat n -> (forall k, Rnat (nth k (f n l) 0))) ->
  forall n, Rnat n -> (forall k, Rnat (nth k (Rnat_rec l0 f n) 0)).
Proof.
intros l0nat fnat m mnat.
induction mnat as [ | n nnat Ih].
  unfold Rnat_rec; rewrite IRN0.
  exact l0nat.
rewrite Rnat_rec_succ;[ | assumption].
apply fnat;[ | assumption].
exact Ih.
Qed.

Lemma IZR_map1 : forall opr opz,
  (forall a, opr (IZR a) = IZR (opz a)) ->
  forall a b, a = IZR b -> opr a = IZR (opz b).
Proof.
intros opr opz morph a b ab.
now rewrite ab, morph.
Qed.

(* This may be dead code. *)
Lemma IZR_map1_abs : forall opr opz,
  (forall x y, x = IZR y -> opr (Rabs x) = IZR (opz y)) ->
  forall a b, a = IZR b -> opr (Rabs a) = IZR (opz b).
Proof.
intros opr opz pmorph; exact pmorph.
Qed.

Lemma Zabs_nat_Zabs_involutive (f : nat -> Z) z :
  f (Z.abs_nat (Z.abs z)) = f (Z.abs_nat z).
Proof.
now unfold Z.abs, Z.abs_nat; destruct z.
Qed.

Lemma IZR_map2 : forall opr opz,
  (forall a b, opr (IZR a) (IZR b) = IZR (opz a b)) ->
  forall a b c d, a = IZR c -> b = IZR d ->
  opr a b = IZR (opz c d).
Proof.
intros opr opz morph a b c d ac bd.
now rewrite ac, bd, morph.
Qed.

Lemma nth_map {A B : Type} (da : A) (db : B) (f : A -> B) (la : list A)
  (lb : list B) (k : nat):
  db = f da ->
  lb = map f la ->
  nth k lb db = f (nth k la da).
Proof.
intros dq lq; rewrite dq, lq; apply map_nth.
Qed.

Lemma IRN_Z_abs_nat n z : n = IZR z -> IRN (Rabs n) = Z.abs_nat z.
Proof.
intros nzq; unfold IRN.
destruct (Rle_or_lt 0 n).
  rewrite Rabs_right;[ | lra].
  now rewrite nzq, IRZ_IZR.
rewrite Rabs_left;[ | lra].
rewrite nzq, <- opp_IZR, IRZ_IZR.
now destruct z.
Qed.

Lemma INR_Z_abs_nat n z : n = IZR z -> Rabs n = INR (Z.abs_nat z).
Proof.
intros nzq.
rewrite nzq.
rewrite <- abs_IZR.
rewrite INR_IZR_INZ.
now rewrite Nat2Z.inj_abs_nat.
Qed.

Lemma cancel_Rabs_pos (f : R -> R) (fz : Z -> Z):
  (forall (n : R) (z : Z), n = IZR z ->
     f (Rabs n) = IZR (fz z)) ->
  forall p : positive,
    f (IZR (Z.pos p)) = IZR (fz(Z.pos p)).
Proof.
intros morph p.
rewrite <- (morph _ _ eq_refl).
now rewrite <- abs_IZR.
Qed.

Lemma cancel_Rabs_0 (f : R -> R) (fz : Z -> Z):
  (forall (n : R) (z : Z), n = IZR z ->
    f (Rabs n) = IZR (fz z)) ->
    f 0 = IZR (fz 0%Z).
Proof.
intros morph; rewrite <- (morph _ _ eq_refl).
now rewrite <- abs_IZR.
Qed.

Lemma compute_Rnat (n : R) (z : Z) : n = IZR z ->
  (0 <=? z)%Z = true -> Rnat n.
Proof.
intros nzq cmp.
apply Rint_Rnat.
  now rewrite nzq; apply Rint_Z.
rewrite nzq.
apply IZR_le.
now rewrite (Zle_is_le_bool 0).
Qed.

End private.

Ltac prove_recursive_specification T Order := unfold T;
  repeat split;
  (* The first now clause attempts to prove the base cases. *)
    (now (rewrite Rnat_rec0 || rewrite private.Rnat_rec_to_nat_rec_p)) ||
    (let N := fresh "n" in let Nnat := fresh "nnat" in
     let Protector := fresh "protect_base" in
     unfold Rnat_rec; intros N Nat;
     set (Protector := IRN (N - IZR Order));
     repeat (rewrite (private.IRN_to_S N Order);[ | reflexivity | assumption]);
     rewrite (private.IRN_to_S_top N Order);[ | reflexivity | assumption];
     (reflexivity (* useful when N is only used in recursive calls*) ||
       (simpl;
        let Last_eqn := fresh "H" in
        enough (Last_eqn : INR (IRN (N - IZR Order)) + IZR Order = N)
            by (rewrite Last_eqn; reflexivity);
            rewrite INR_IRN;[ring | assumption]))).

Elpi Command Recursive.
Elpi Accumulate File tools.
Elpi Accumulate File recursive.

Elpi Export Recursive.

Notation "'def' id 'such' 'that' bo" := (fun id => bo)
 (id binder, bo at level 100, at level 1, only parsing).

Ltac rec_Rnat fun_name :=
(* This tactic is only meant to be used on statements of the form:
  Rnat x -> Rnat (fun_name x)
  where fun_name was defined using the Recursive command.  It succeeds
  if all operations that appear in the body of the definition are
  known to preserve membership in Rnat. *)
  let Nnat := fresh "nnat" in
  let M := fresh "m" in
  let L := fresh "l" in
  let Lnat := fresh "lnat" in
  let Mnat := fresh "mnat" in
  intros nnat;
  unfold fun_name;
  apply private.Rnat_rec_nat';[
    repeat ((intro; apply Rnat0)||(
             intros [ | k];[typeclasses eauto | revert k; cbn [nth]]
    )) |
    intros M L Lnat Mnat;
     repeat ((intro; apply Rnat0)||(
             intros [ | k];[typeclasses eauto | revert k; cbn [nth]]
    )) | assumption].


(* Elpi Trace Browser. *)
