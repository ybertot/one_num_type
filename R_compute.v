From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.

Open Scope R_scope.

Elpi Command R_compute.

Elpi Accumulate lp:{{

pred decompose i:term, o:term.

decompose {{IZR lp:A}}  A.

decompose {{Rplus lp:A lp:B}}
    {{(Z.add lp:A1 lp:B1)}} :-
  std.do! [
    coq.say "debug " {coq.term->string A},
    decompose A A1,
    decompose B B1
  ].


  main [trm E] :-
    std.do! [
      coq.say "start with " {coq.term->string E},
      decompose E E1,
      coq.say " = " {coq.term->string E1}
    ].

}}.

Elpi Typecheck.

Elpi R_compute (3 + 5).