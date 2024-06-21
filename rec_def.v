From elpi Require Import elpi.
Require Import Reals.
Open Scope R_scope.

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall n, Rnat n -> Rnat (n + 1).

Elpi Command Recursive.

Elpi Accumulate lp:{{

pred find_uses i:term o:list term.

find_uses Abs_eqn Uses:-
  std.do! [
    Abs_eqn = fun _Name1 T F,
    pi x\ fold-map (app [x, E]) A (app [x, E]) [E | A] =>
      fold-map (F x) [] _ Uses
  ].

main [str Name, trm Abs_eqn] :- 
  coq.say "Hello" Name,
  find_uses Abs_eqn Uses,
  coq.say "uses " Uses.

main _ :-
  coq.error "Usage: Recursive name equation_1 .. equation_n".

}}.

Elpi Typecheck.

Elpi Recursive fib
  (fun fib =>
    forall n : R, Rnat n -> n < 2 -> fib n = fib (n - 1) + fib (n - 2)).

(* I was exoectubg tge cinnabd to print a list containing representations
  of (n - 1) and (n - 2) *)
