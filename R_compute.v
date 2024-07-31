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
}}.

Elpi Typecheck.
