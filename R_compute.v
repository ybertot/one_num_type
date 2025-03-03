From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
From OneNum.srcElpi Extra Dependency "translate_prf.elpi" as translate_prf.
From OneNum.srcElpi Extra Dependency "compute.elpi" as compute.
From OneNum.srcElpi Extra Dependency "gen.elpi" as gen.
From OneNum.srcElpi Extra Dependency "tools.elpi" as tools.
#[local]
Set Warnings "-notation-overridden".

Require Import R_subsets rec_def.

#[local]
Set Warnings "+notation-overridden".


Open Scope R_scope.
Lemma add_compute : forall x y, Rplus (IZR x) (IZR y) = IZR (Z.add x y).
Proof.
exact (fun x y => eq_sym (plus_IZR x y)).
Qed.

Lemma mul_compute : forall x y, Rmult (IZR x) (IZR y) = IZR (Z.mul x y).
Proof.
exact (fun x y => eq_sym (mult_IZR x y)).
Qed.

Lemma sub_compute : forall x y, Rminus (IZR x) (IZR y) = IZR (Z.sub x y).
Proof.
exact (fun x y => eq_sym (minus_IZR x y)).
Qed.

Lemma opp_compute : forall x, Ropp (IZR x) = IZR (Z.opp x).
Proof.
exact (fun x => eq_sym (opp_IZR x)).
Qed.

Lemma Zeq_bool_IZR_neq x y : (IZR x) <> (IZR y)  -> x <> y.
Proof.
  intros H1 H2.
  apply H1.
  rewrite H2.
  reflexivity.
Qed.


Lemma abs_compute : forall x, Rabs (IZR x) = IZR (Z.abs x).
Proof.
exact (fun x => eq_sym (abs_IZR x)).
Qed.

Definition Req_bool (x y : R) := if (Req_dec_T x y) then true else false.
Notation "x =? y" := (Req_bool x y) : R_scope.

Lemma eq_bool_compute : forall x y, Req_bool (IZR x) (IZR y) = (Zeq_bool x y).
Proof.
  intros.
  unfold Req_bool.
  destruct Req_dec_T as  [eqR|neqR] .
    now rewrite (Zeq_bool_IZR x y).
  unfold Zeq_bool.
  apply Zeq_bool_IZR_neq in neqR.
  rewrite <- Z.eqb_neq in neqR.
  now rewrite <- Z.eqb_compare, neqR.
Qed.
(*
Lemma if_compute : (forall x y z, if
Search (if _ then _ else _ ). *)
Definition MyINR : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => IZR (Z.pos p)
  end.

Definition at_x (a b c : R) := fun x => if (Req_bool x a) then b else (c).

Definition at_x_Z (a b c : Z) := fun x => if (Zeq_bool x a) then b else c.

Lemma at_x_compute : forall a b c x, at_x (IZR a) (IZR b) (IZR c) (IZR x) = IZR (at_x_Z a b c x).
Lemma at_x_compute : forall a b c x, at_x (IZR a) (IZR b) (IZR c) (IZR x) = IZR (at_x_Z a b c x).
Proof.
  intros.
  unfold at_x.
  unfold at_x_Z.
  rewrite <-eq_bool_compute.
  now destruct (Req_bool (IZR x) (IZR a)).
Qed.


Definition IZR2 (f : Z -> Z) :=
fun r : R =>
  IZR(f (IRZ r)).


Lemma nil_2 :  nil = @map (ty_Z 1) (ty_R 1) IZR2 nil.
Proof.
  unfold IZR2.
  now simpl.
Qed.

Definition nat1 := nat.


Lemma eq_bool_compute : forall x y, Req_bool (IZR x) (IZR y) = (Zeq_bool x y).
Proof.
  intros.
  unfold Req_bool.
  destruct Req_dec_T as  [eqR|neqR] .
    now rewrite (Zeq_bool_IZR x y).
  unfold Zeq_bool.
  apply Zeq_bool_IZR_neq in neqR.
  rewrite <- Z.eqb_neq in neqR.
  now rewrite <- Z.eqb_compare, neqR.
Qed.
(*
Lemma if_compute : (forall x y z, if
Search (if _ then _ else _ ). *)
Definition MyINR : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => IZR (Z.pos p)
  end.

Definition at_x (a b c : R) := fun x => if (Req_bool x a) then b else (c).

Definition at_x_Z (a b c : Z) := fun x => if (Zeq_bool x a) then b else c.

Lemma at_x_compute : forall a b c x, at_x (IZR a) (IZR b) (IZR c) (IZR x) = IZR (at_x_Z a b c x).
Proof.
  intros.
  unfold at_x.
  unfold at_x_Z.
  rewrite <-eq_bool_compute.
  now destruct (Req_bool (IZR x) (IZR a)).
Qed.


Definition IZR2 (f : Z -> Z) :=
fun r : R =>
  IZR(f (IRZ r)).


Lemma nil_2 :  nil = @map (ty_Z 1) (ty_R 1) IZR2 nil.
Proof.
  unfold IZR2.
  now simpl.
Qed.

Definition nat1 := nat.
Elpi Db R_translate.db lp:{{ }}.
Elpi Accumulate R_translate.db File tools.
Elpi Accumulate R_translate.db File gen.
Elpi Accumulate R_translate.db File translate_prf.

Elpi Db R_compute.db lp:{{
}}.
Elpi Accumulate R_compute.db File compute.
Elpi Accumulate R_compute.db File gen.



Elpi Command R_compute.

Elpi Accumulate Db R_compute.db.


Elpi Accumulate lp:{{
pred translate_prf i:term, o:term, o:term.
main [trm E] :-
std.do! [
  translate_prf E E1 _,
  coq.reduction.vm.norm E1 _ E2,
  E3 = {{IZR lp:E2}},
  coq.say " =" {coq.term->string E3}
].

main [trm E, str THM_name] :-
std.do! [
  translate_prf E E1 PRF,
  coq.reduction.vm.norm E1 _ E2,
  E3 = {{IZR lp:E2}},
  coq.say " =" {coq.term->string E3},
  Stmt = {{lp:E = lp:E3:>R}},
  std.assert-ok! (coq.typecheck PRF Stmt) "error typechecking proof",
  coq.env.add-const THM_name PRF Stmt @opaque! _
].
main _ :- coq.say "error R_compute".
}}.
Elpi Accumulate  File compute.
Elpi Accumulate File tools.
Elpi Accumulate File gen.
Elpi Accumulate File translate_prf.
Elpi Export R_compute.

Elpi Command add_computation.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate lp:{{

% TODO: check that the proof C really states that B is the mirror of A
  main [str A, str B, str C] :-
    coq.locate A A1,
    coq.locate B B1,
    coq.locate C C1,
    coq.say "adding correspondence " {coq.term->string (global A1)}
      {coq.term->string (global B1)} "justified by" {coq.term->string (global C1)},
    coq.elpi.accumulate _ "R_compute.db"
     (clause _ _ (thm_table (global A1) (global B1) (global C1))).

  main L :-
    coq.error "Usage: Elpi add_computation Name1 Name2 Name3.\n instead received: " L.
}}.

Elpi Export add_computation.


Elpi Command mirror_recursive_definition.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.
Elpi Accumulate File gen.
Elpi Accumulate lp:{{ }}.

Ltac r_compute_rewrite P := rewrite P.

Elpi Tactic r_compute.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [trm X] as G) GL :-
  std.do! [
  translate_prf X V PRF ,
  coq.reduction.vm.norm V _ _E2,
  coq.typecheck PRF Stmt ok,
  coq.say "stmt :" {coq.term->string Stmt},
  coq.ltac.call "r_compute_rewrite"
    [trm {{lp:PRF : lp:Stmt}}] G GL
  ].

solve A B :-
  coq.say "wrong" A B.
}}.
