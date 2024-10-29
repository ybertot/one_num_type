From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.
From OneNum.srcElpi Extra Dependency "tools.elpi" as tools.
From OneNum.srcElpi Extra Dependency "recursive.elpi" as recursive.


Set Warnings "-notation-overridden".
Require Import OneNum.R_subsets.
Set Warnings "+notation-overridden".
Require Import Derive.

Open Scope R_scope.

Fixpoint ty_R (n : nat) : Type := 
  match n with
   0 => R
  | S p => (R -> ty_R p)
  end.

Fixpoint id_R (n : nat) : (ty_R n):= 
  match n with
   0 => 0%R
  | S p => (fun k => (id_R p))
  end.

Fixpoint ty_Z (n : nat) : Type := 
  match n with
   0 => Z
  | S p => (Z -> ty_Z p)
  end.

Fixpoint id_Z (n : nat) : (ty_Z n):= 
  match n with
   0 => 0%Z
  | S p => (fun k => (id_Z p))
  end.

Fixpoint MappZ {n : nat} (f : ty_Z n) (l : list Z):=
  match n return ty_Z n -> list Z -> Z with 
  |0 => fun (f : ty_Z 0) (l: list Z) => f
  |S p => fun (f: Z -> ty_Z p) (l : list Z) =>
      match l with nil => MappZ (f 0%Z) nil
                  |a::tl => MappZ (f a) tl end
  end f l.

Fixpoint MappR {n : nat} (f : ty_R n) (l : list R):=
  match n return ty_R n -> list R -> R with 
  |0 => fun (f : ty_R 0) (l: list R) => f
  |S p => fun (f: R -> ty_R p) (l : list R) =>
      match l with nil => MappR (f 0%R) nil
                  |a::tl => MappR (f a) tl end
  end f l.
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

Lemma Rnat_RabsN {n : nat} {f : ty_R (S n)} {fz : ty_Z (S n)}
  (abs_morph : forall r z, r = IZR z -> 
  forall lr lz, lr = map IZR lz ->
  @MappR n (f (Rabs r)) lr = IZR (MappZ (fz z) lz))
  (r : R) (z : Z) (rnat : Rnat r) (rz : r = IZR z) (lr: list R) (lz :list Z) (eql : lr = map IZR lz) : MappR f (r::lr) = IZR (MappZ  fz (z::lz)).
Proof.
rewrite <- (Rabs_right r);[ | assert (tmp := Rnat_ge0 r rnat); lra].
now apply abs_morph.
Qed.

Lemma nat_rect_transfer {A B : Type} (rel : A->B->Prop)
(va : A) (vb : B) (fa : nat-> A -> A) (fb : nat -> B -> B) :
rel va vb -> (forall n ua ub, rel ua ub -> rel (fa n ua) (fb n ub)) ->
forall n, rel (nat_rect (fun _ : nat => A) va fa n) (nat_rect (fun _ : nat => B) vb fb n).
intros base IH.
induction n as [|n IHn].
  simpl.
  exact base.
simpl.
apply IH.
apply IHn.
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
intros ll' ff'.
apply (nat_rect_transfer (fun x y => x = map IZR y)); auto.
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


Lemma IZR_map1' {opr} {opz} : 
  (forall a, opr (IZR a) = IZR (opz a)) ->
  forall a b, a = IZR b -> opr a = IZR (opz b).
Proof.
intros morph a b ab.
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

Lemma IZR_map3 : forall opr opz,
  (forall a b c, opr (IZR a) (IZR b) (IZR c) = IZR (opz a b c)) ->
  forall a b c d e f, a = IZR d -> b = IZR e -> c = IZR f ->
  opr a b c = IZR (opz d e f).
Proof.
intros opr opz morph a b c d e f ad be cf.
now rewrite ad, be, cf, morph.
Qed.

Lemma IZR_map4 : forall opr opz,
  (forall e f g h, opr (IZR e) (IZR f) (IZR g) (IZR h) = IZR (opz e f g h)) ->
  forall a b c d e f g h, a = IZR e -> b = IZR f -> c = IZR g -> d = IZR h ->
  opr a b c d = IZR (opz e f g h).
Proof.
intros opr opz morph a b c d e f g h ae bf cg dh.
now rewrite ae, bf, cg, dh, morph.
Qed.

Lemma IZR_mapN {n opr opz}:
  (forall (lz : list Z), @MappR n opr (List.map IZR lz) = IZR (@MappZ n opz lz))->
  forall (lr : list R)  (lz : list Z), lr = List.map IZR lz ->
   @MappR n opr lr = IZR (@MappZ n opz lz).
Proof.
  intros  morph lz lr eql.
  rewrite eql.
  apply morph.
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

Lemma cancel_Rabs_pos2 (f : R -> R -> R) (fz : Z -> Z -> Z):
  (forall (n : R) (z : Z), n = IZR z ->
   forall (m : R) (y : Z), m = IZR y ->
     f (Rabs n) m = IZR (fz z y)) ->
  forall (p  : positive) (m:R) (y:Z), m=IZR y ->
    f (IZR (Z.pos p)) m = IZR (fz(Z.pos p) y).
Proof.
intros morph p m y my.
rewrite <- (morph _ _ eq_refl _ _ my).
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


Definition P_trans1 (l : list (R -> R)) (f : Z -> R) (l' : list (Z->Z)) :=
forall (i : nat) (x : Z), nth i l (id_R 1) (f x) = f (nth i l' (id_Z 1) x).

Definition P_trans1' (l : list (R -> R)) (f : Z -> R) (l' : list (Z->Z)) :=
forall (i : nat) (x : Z) (y : R), y = (f x) ->
nth i l (id_R 1) y = f (nth i l' (id_Z 1) x).

Definition P_transN (n : nat) (l : list (ty_R n)) (f : Z -> R) (l' : list (ty_Z n)) :=
forall (i : nat) (x : (list Z)),
MappR (nth i l (id_R n)) (List.map f x) = f (MappZ (nth i l' (id_Z n)) x).

Definition P_transN' (n : nat) (l : list (ty_R n)) (f : Z -> R) (l' : list (ty_Z n)) :=
forall (i : nat) (x : (list Z)) (y : (list R)), y = List.map f x ->
MappR (nth i l (id_R n)) y = f (MappZ (nth i l' (id_Z n)) x).

Lemma trf_trans : forall l f l', P_trans1 l f l' -> P_trans1' l f l'.
Proof.
  intros l f l'.
  unfold P_trans1.
  unfold P_trans1'.
  intros H i x y xy.
  rewrite xy.
  apply H.
Qed.

Lemma trf_transN : forall n l f l', P_transN n l f l' -> P_transN' n l f l'.
Proof.
  intros n l f l'.
  unfold P_transN.
  unfold P_transN'.
  intros H i x y eqyx.
  rewrite eqyx.
  apply H.
Qed.

Lemma trf_transN_opp : forall n l f l', P_transN' n l f l' -> P_transN n l f l'.
Proof.
  intros n l f l'.
  unfold P_transN.
  unfold P_transN'.
  intros H i x.
  now apply H.
Qed.

Lemma fun1_trf (g : R -> R) (g' : Z -> Z) (f : Z -> R) : 
(forall x, g (f x) = f (g' x)) <-> (forall x y, x = (f y) -> (g x) = f (g' y)).
Proof.
  split.
    intros H x y xy.
    rewrite xy.
  apply H.
  intros H x.
  apply H.
  reflexivity.
Qed.

Lemma funN_trf {n : nat} (g : ty_R n) (g' : ty_Z n) (f : Z -> R) : 
(forall x, MappR g (map f x) = f (MappZ g' x)) <->
(forall x y, x = map f y -> MappR g x = f (MappZ g' y)).
Proof.
  split.
    intros H x y xy.
    rewrite xy.
  apply H.
  intros H x.
  apply H.
  reflexivity.
Qed.

Lemma mapp_step n (f : ty_R (S n)) (g : ty_Z (S n)) :
(forall y l, MappR (f (IZR y)) (map IZR l) = IZR (MappZ (g y) l)) <->
(forall l, MappR f (map IZR l) = IZR (MappZ g l)).
Proof.
split.
  intros hyp [| a tl].
    apply (hyp 0%Z nil).
  apply (hyp a tl).
intros hyp y l.
apply (hyp (y::l)).
Qed.

Lemma mapp_step' n (f : ty_R (S n))(g : ty_Z (S n)) :
(forall x y, x = IZR y -> forall l1 l2, l1 = map IZR l2 -> MappR (f x) l1 = IZR (MappZ (g y) l2)) <->
(forall l1 l2, l1 = map IZR l2 -> MappR f l1 = IZR (MappZ g l2)).
Proof.
split.
  intros hyp l1 l2 l1l2eq.
  rewrite l1l2eq.
  apply mapp_step.
  intros y l.
  now apply hyp.
intros hyp x y xyeq l1 l2 l1l2eq.
rewrite l1l2eq, xyeq.
apply mapp_step.
intros l.
now apply hyp.
Qed.

Lemma P_trans1_nil :  P_trans1 nil IZR nil.
unfold P_trans1.
destruct i as [|i].
intros.
reflexivity.
intros.
reflexivity.
Qed.

Lemma P_trans1_cons A A' B B': (forall x, A (IZR x) = IZR (A' x)) -> P_trans1 B IZR B' -> P_trans1 (cons A B) IZR (cons A' B').
Proof.
  unfold P_trans1.
  intros Aeq PtB i z.
  case i.
    now simpl.
  simpl.
  intro n.
  apply PtB.
Qed.
Lemma nth_nil {A:Type} n (d:A) : nth n nil d = d.
Proof.
  now destruct n.
Qed.

Lemma P_transN_nil n :  P_transN n (@nil (ty_R n)) IZR (@nil (ty_Z n)).
unfold P_transN.
intros i x.
rewrite !nth_nil.
revert x.
induction n.
  simpl.
  easy.
intros x.
simpl.
destruct x.
  simpl.
  apply (IHn nil).
simpl.
apply IHn.
Qed.

Lemma P_transN_cons n A A' B B' :
(forall x, MappR A (map IZR x) = IZR (MappZ A' x)) ->
 P_transN n B IZR B' -> P_transN n (cons A B) IZR (cons A' B').
Proof.
  unfold P_transN.
  intros Aeq PtB i z.
  case i.
    easy.
  simpl.
  intro j.
  apply PtB.
Qed.

Lemma nth_overflow_1 A A' p x : 
nth (S p) (A::nil) (id_R 1) (IZR x) = IZR (nth (S p) (A'::nil) (id_Z 1) x).
case p.
reflexivity.
reflexivity.
Qed.

(* Lemma prf_if a az b bz c cz : a = IZR A ->  *)

Lemma nat_rect_list :
  forall (l0 : list (Z->Z)) (l' : list (R->R))
    (f : nat -> list (Z->Z) -> list (Z->Z))
    (f' : nat -> list (R->R) -> list (R->R))
    (n : nat),
    P_trans1 l' IZR l0 ->
    (forall n lr lz, P_trans1 lr IZR lz -> 
        P_trans1 (f' n lr) IZR (f n lz)) ->
    P_trans1 (nat_rect (fun _ : nat => list (R->R)) l' f' n) 
             IZR 
             (nat_rect (fun _ : nat => list (Z->Z)) l0 f n).
Proof.
  intros l0 l' f f' n H H'.
  apply (private.nat_rect_transfer (fun x y => P_trans1 x IZR y)); auto.
Qed.

Lemma nat_rect_list_N :
  forall (n' : nat) (l0 : list (ty_Z n')) (l' : list (ty_R n'))
    (f : nat -> list (ty_Z n') -> list (ty_Z n'))
    (f' : nat -> list (ty_R n') -> list (ty_R n'))
    (n : nat),
    P_transN n' l' IZR l0 ->
    (forall n lr lz, P_transN n' lr IZR lz -> 
        P_transN n' (f' n lr) IZR (f n lz)) ->
    P_transN n' (nat_rect (fun _ : nat => list (ty_R n')) l' f' n) 
             IZR 
             (nat_rect (fun _ : nat => list (ty_Z n')) l0 f n).
Proof.
  intros n' l0 l' f f' n H H'.
  apply (private.nat_rect_transfer (fun x y => P_transN n' x IZR y)); auto.
Qed.

Elpi Command Recursive.
Elpi Accumulate File tools.
Elpi Accumulate File recursive.

Elpi Export Recursive.
  


Notation "'def' id 'such' 'that' bo" := (fun id => bo)
 (id binder, bo at level 100, at level 1, only parsing).
 Definition Req_bool (x y :R) := if (Req_dec_T x y) then true else false.
Notation "x =? y" := (Req_bool x y) : R_scope.
Recursive (def bin such that 
    bin 0 = (fun n : R => n) /\ 
    forall n, Rnat (n-1) -> bin n = 
    (fun m => if (m =? 0) then 1 else (bin (n-1)) (m-1) + (bin (n-1)) m)).

Elpi Query lp:{{
% coq.reduction.vm.norm {{ty_R 1}} _ V,
% coq.term->string V VS,
% coq.typecheck {{eq_refl : ty_R 1 = (R -> R)}} _ Diag,
% coq.typecheck {{id_R 1}} {{(R -> R)}} Diag,
coq.typecheck {{fun v : list (R -> R)=> @nth (ty_R 1) 0%nat v (id_R 1)}} A Diag
 }}.


(* R_compute (bin 5 3). *)

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
