From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.

Open Scope R_scope.

Elpi Db R_compute.db lp:{{

pred compute_table o:term, o:term.

compute_table {{Rplus}} {{Z.add}}.

compute_table {{Rminus}} {{Z.sub}}.

compute_table {{Rmult}} {{Z.mul}}.

compute_table {{Ropp}} {{Z.opp}}.

compute_table {{Rpower}} {{Z.pow}}.
}}.

Elpi Command R_compute.

Elpi Accumulate Db R_compute.db.
Elpi Accumulate lp:{{

pred decompose i:term, o:term.

decompose {{IZR lp:A}}  A :- !.

decompose (app [Fr, A, B]) (app [Fz, A1, B1]) :-
  std.do! [
    decompose A A1,
    decompose B B1,
    compute_table Fr Fz
  ].

decompose (app [Fr, A]) (app [Fz, A1]) :-
  std.do! [
    decompose A A1,
    compute_table Fr Fz
  ].

decompose (app [Fr | _]) _ :-
   coq.error "no correspondence for" {coq.term->string Fr}.

  main [trm E] :-
    std.do! [
      decompose E E1,
      coq.reduction.vm.norm E1 _ E2,
      E3 = {{IZR lp:E2}},
      coq.say " = " {coq.term->string E3}
    ].

}}.

Elpi Typecheck.

Elpi Command add_computation.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate lp:{{

  main [str A, str B] :-
    coq.locate A A1,
    coq.locate B B1,
    coq.say "adding correspondence " {coq.term->string (global A1)}
      {coq.term->string (global B1)},
    coq.elpi.accumulate _ "R_compute.db"
     (clause _ _ (compute_table (global A1) (global B1))).

  main L :-
    coq.error "Usage: Elpi add_computation Name1 Name2.\n instead received: " L.
}}.

Elpi Typecheck.

Elpi Command mirror_recursive_definition.
Elpi Accumulate Db R_compute.db.

Elpi Accumulate lp:{{

% TODO: find the value of the name given in argument
% which should be of the form (nth 0 (@Rnat_rec (list R) L0 F) 0)
% replace all values in L0 by their corresponding integer values to obtain L1
% F should be of type R -> list R -> list R
% In the body of F n l, all occurences of R should be replace by Z
% all occurrences of n should be replaced by Z.of_nat n
% all occurrences of IZR z should be replaced by z
% all occurrences of functions should be replaced by their correspondence
% in compute_table (as in decompose), to obtain F1
% A new function should be defined whose value should be
% (nth 0 (nat_rect (fun _ => list Z) L1 F1) 0%Z)
main L :-
  coq.error "Usage: Elpi mirror_recursive_definition Name.\n instead received: " L.
}}.