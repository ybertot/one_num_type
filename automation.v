From elpi Require Import elpi.
From Stdlib Require Import Reals Lra.
From OneNum Require Import R_subsets rec_def ring_simplify_bank field_simplify_bank.

From OneNum.srcElpi Extra Dependency "tools.elpi" as tools.
From OneNum.srcElpi Extra Dependency "automation.elpi" as automation.

Open Scope R_scope.

 Ltac xx rl :=

  let G := Get_goal in
  
  ring_lookup (PackRing Ring_simplify) [] rl G .

Elpi Tactic test.

Elpi Accumulate lp:{{
  solve (goal C R T E []) GL :- coq.ltac.call-ltac1 "xx" (goal C R T E [trm {{ 0 + 0 }}]) GL.}}.

Goal forall f, 0%Z = f (0 + 0) :> Z.
intro f.
elpi test.
match goal with |- 0%Z = f 0 => idtac end.
Abort. 


Tactic Notation "super_ring" :=
  elpi super_ring.
(* Ltac super_ring' :=
repeat  (progress (super_ring ;try reflexivity)) ;  try reflexivity. *)


Elpi Tactic super_ring.
Elpi Accumulate File automation.
Elpi Accumulate File tools.

Elpi Accumulate lp:{{

    solve (goal C R ({{@eq R lp:T1 lp:T2}} as T) E _ as G)  GL :-
    sub_ringable_r T1 [] L1,
    sub_ringable_r T2 L1 L2,
    remove_duplicates L2 L,
    terms_to_trms L TL, !,
    std.length L N,
    std.any->string N SN,
    std.string.concat  "" ["r", SN] S,
    coq.ltac.call S TL G  GL
    % coq.ltac.call "xx" TL G  GL,
    % coq.ltac.call-ltac1 "xx" (goal C R T E [trm {{(0+0)}}, trm {{0}}]) GL,
    .

    solve _ _ :-
    coq.ltac.fail _ "problem super_ring".

}}.

Elpi Tactic super_ring_i .
Elpi Accumulate File automation.
Elpi Accumulate File tools.
Elpi Accumulate lp:{{

    solve (goal _ _ {{lp:T1 = lp:T2}} _ [trm TL'] as G)  GL :-
    term_to_list TL' L',
    sub_ringable_r T1 [] L1,
    sub_ringable_r T2 L1 L2,
    std.append L' L2 L3,
    remove_duplicates L3 L,
    terms_to_trms L TL, !,
    std.length L N,
    std.any->string N SN,
    std.string.concat  "" ["r", SN] S,
    % coq.ltac.call "xx" TL G  GL,
    % coq.ltac.call-ltac1 "xx" (goal C R T E [trm {{(0+0)}}, trm {{0}}]) GL,
    coq.ltac.call S TL G  GL
    .

    solve _ _ :-
    coq.ltac.fail _ "problem super_ring_i".

}}.

(* parentheses around vars as argument of super_ring_i are needed because
of a quirk of elpi tactics *)

Ltac super_ring_iterator vars := 
repeat (try reflexivity; progress(elpi super_ring_i (vars))).

Elpi Tactic super_ring_iterate.
Elpi Accumulate File automation.
Elpi Accumulate File tools.
Elpi Accumulate lp:{{

    solve (goal _Ctx _ {{lp:T1 = lp:T2}} _  _ as G ) GL :-
    all_vars T1 [] L1',
    all_vars T2 L1' L2',
    remove_duplicates L2' L',!,
    list_to_real L' TL,
    coq.ltac.call "super_ring_iterator" [trm TL] G GL.

    solve _ _ :-
    coq.ltac.fail _ "problem super_ring_iterate".

}}.


Elpi Tactic test_all_vars.
Elpi Accumulate File automation.
Elpi Accumulate File tools.
Elpi Accumulate lp:{{

    solve (goal _Ctx _ {{lp:T1 = lp:T2}} _  _ as G ) [seal G] :-
    coq.say T1,
    all_vars T1 [] L1',
    coq.say "L1'", coq.say L1',
    all_vars T2 L1' L2',
    remove_duplicates L2' L',
    coq.say L',
    !

    .

    solve _ _ :-
    coq.ltac.fail _ "problem test_all_vars".

}}.

Tactic Notation "super_ring'" := elpi super_ring_iterate.
(* Goal cos (0+0) =cos 0.
(* ring_simplify (0+0) (0). *)
super_ring. *)
(* Section Test.
Variable x y z t: R.
Elpi Query lp:{{
 T = {{ cos ( x+ y)+ z + x +3 }},
all_vars T [] L,
sayLT L
}}. *)
Section Test.
Variable x y z t a b psi: R.
Let rho := sqrt (a ^ 2 + b ^ 2) .
Goal True.

  
  Elpi Query lp:{{
    T = {{(rho * sin psi) ^ 2 = rho ^ 2 * sin psi ^ 2}},

    all_vars T [] L
  }}.

easy. Qed.
Elpi Query lp:{{
 T = {{ cos ( x+ y)}},
collect [{{Rplus}}] []T [] L1,
sayL L1 
}}.

Goal forall x y, cos ( x+ y) = cos (y+ x).
intros.
(* ring_simplify (x+y) (y+x). *)
super_ring.
reflexivity.
Qed.
Goal cos (x + 1 + 2) = cos (x + 2 + 1).

 super_ring.
 easy.
Qed.


Goal  x+cos (y +sin t) = cos (sin (t+0) + y +0)+x.
super_ring.
super_ring.
super_ring.
super_ring.
super_ring'.
Qed.

Goal  2 * sin (x+ cos(y)) + cos(y+x+0) = cos (x+y)+2* sin (cos (y)+x) .
super_ring'.
Qed.

Goal sin (x + 0) + 2*x - x = sin x + x.
super_ring'.
Qed.
Goal x + 3*x - 4*x = 0.

super_ring'.
Qed.
Goal (cos (x / 2 ^ (0 + 2))) = (cos (x / 4)).
  super_ring'.
Qed.

Goal - y ^ 2 + x ^ 2  = - y ^ 2 + x ^ 2.
super_ring.
super_ring.
super_ring.
super_ring.
reflexivity.
Qed.
Goal x ^ 2 = y ^ 2 -> x ^ 2 - y ^ 2 = 0.
intros.
super_ring.
super_ring.
super_ring.
lra.
Qed.
End Test.


Ltac super_field :=
  elpi super_field.
Elpi Tactic super_field.
Elpi Accumulate File automation.
Elpi Accumulate File tools.


Elpi Accumulate lp:{{

solve (goal _Ctx _ {{lp:T1 = lp:T2}} _  _ as G ) GL :-
    sub_fieldable_r T1 [] L1,
    sub_fieldable_r T2 L1 L2,
    remove_duplicates L2 L,
    terms_to_trms L TL, !,
    std.length L N,
    std.any->string N SN,
    std.string.concat  "" ["f", SN] S,
    coq.ltac.call S TL G GL
    .

solve _ _ :-
    coq.ltac.fail _ "problem super_field".

}}.



Elpi Tactic add_ge0s.
Elpi Accumulate File automation.
Elpi Accumulate File tools.
Elpi Accumulate lp:{{

solve (goal Ctx _ _ _ _ as G) Gl :-
  std.filter Ctx (is_hyp_ge0 _)OldGe0s,
  newHs Ctx OldGe0s Ts,
  std.rev Ts RTs,
  letifyge0s RTs Let,
  refine Let G Gl.

solve _ _ :-
  coq.ltac.fail _ "problem add_ge0s".

}}.

Elpi Tactic field_progress.
Elpi Accumulate File automation.
Elpi Accumulate lp:{{
solve G [G'|Gs] :-
  coq.ltac.call-ltac1 "super_field" G [G'|Gs],
  not (same_goal_seal_not_seal G G'), !
.

solve _ _ :-
  coq.ltac.fail _ "problem field_progress".
}}.

Section Test.
  Variable x y: R.
Goal (x+0)/2^(x+0) = x/2^x.
elpi field_progress.
super_field.
Fail elpi field_progress.

Admitted.

Goal forall x y, (x+y)/x = (y+x)/x.
intros.

elpi field_progress.
Fail elpi field_progress.
Admitted.

End Test.
Ltac add_ge0s := elpi add_ge0s.


Ltac super_field' :=
repeat (progress (elpi field_progress) ;  try reflexivity ; (add_ge0s ; try lra)) .

Ltac lra' :=
add_ge0s; lra .


From Ltac2 Require Import Ltac2.
Ltac2 count_hyps () :=
  List.length (Control.hyps ()).
Ltac2 assert_hyps_eq (k : int) :=
  let n := List.length (Control.hyps ()) in
  if Int.equal n k then ()
  else fail.

Section Test.

Variable x y z : R.

Goal (Rnat x) -> (Rnat y)->(Rnat (x - y ^3))  -> (Rnat z)  -> (0 <= z) -> 0 <= x.
intros. 
Fail assumption.
Ltac2 Eval (assert_hyps_eq 8).
ltac1:(add_ge0s).
Ltac2 Eval (assert_hyps_eq 11).
ltac1:(add_ge0s).
Ltac2 Eval (assert_hyps_eq 11).
assumption.
Qed.
End Test.

Ltac super :=
  repeat progress (
      super_ring
   || (super_field')
   || add_ge0s
   || lra
  );
  try reflexivity.

