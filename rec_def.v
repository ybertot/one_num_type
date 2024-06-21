From elpi Require Import elpi.
Require Import Reals.
Open Scope R_scope.

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall n, Rnat n -> Rnat (n + 1).

Elpi Command Recursive.

Elpi Accumulate lp:{{

pred find_uses i:term o:list term.

% I was hoping the first clause would discover instances of f (n - k), where
%  k is a free constant.
find_uses Abs_eqn Uses:-
    Abs_eqn = fun _Name1 T F,
    pi f\
      % This should recognize (f (n - k)) and store k in the list
%      fold-map (app [f, app[M, N, E]]) A (app [f, app[M, N, E]]) [E | A],
      % This should recognize (f k) and store k in the list
      fold-map (app [f, E]) A (app [f, E]) [E | A] =>
      fold-map (F f) [] _ Uses.

main [str Name, trm Abs_eqn] :- 
  coq.say "Hello" Name,
  find_uses Abs_eqn Uses,
  coq.say "uses " Uses.

main _ :-
  coq.error "Usage: Recursive name equation_1 .. equation_n".

}}.

Elpi Typecheck.

Elpi Recursive ex1 (fun ex1 => ex1 0 = 0).

Elpi Recursive fib
  (fun fib =>
    forall n : R, Rnat n -> n < 2 -> fib n = fib (n - 1) + fib (n - 2)).

(* I was exoecting the command to print a list containing representations
  of 1 and 2 *)
