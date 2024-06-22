From elpi Require Import elpi.
Require Import Reals.
Open Scope R_scope.

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall n, Rnat n -> Rnat (n + 1).


Elpi Command Recursive.

Elpi Accumulate lp:{{

% sorting a list of integers
pred list_insert i:int i:list int o:list int.

list_insert I [] [I].

list_insert I [A | L] [I, A | L] :-
  I < A, !.

list_insert I [A | L] [A | L1] :-
  list_insert I L L1.
  
% sorting a list of integers: the main predicate

pred list_sort i:list int o:list int.
list_sort [] [].

list_sort [A | L] L1 :-
  list_sort L L2, !,
  list_insert A L2 L1.

% converting a coq object of type positive to a builtin int
pred positive_to_int i:term o:int.

positive_to_int XH 1 :-
  coq.locate "xH" Gref,
  XH = global Gref.

positive_to_int XI N1 :-
  coq.locate "xI" Gref,
  XI = app[global Gref, X],
  positive_to_int X N,
  N1 is 2 * N + 1.

positive_to_int XO N1 :-
  coq.locate "xO" Gref,
  XO = app[global Gref, X],
  positive_to_int X N,
  N1 is 2 * N.

% converting a real number to an int
pred real_to_int i:term o:int.

% actually, this works for any positive number encapsulated in two unary
% functions
real_to_int (app [_, app [_, P]]) I :-
  positive_to_int P I.

% QUIRKY: performs part of the jobs of finding the uses of the function
% given as first argument inside the second argument.
% The second argument has to be a sequence of nested implications whose
% conclusion is an equality.  The instances we are looking for have to be
% of the form (F (n - k)).  The k values must be real-positive numbers.
pred eat_implications i:term i:term.

eat_implications F (prod _ _ G) :- !,
  pi h \ 
   eat_implications F (G h).

eat_implications F G :-
   std.do! [
      G = app [_, _, _, RHS],
      % This should recognize (f (n - k)) and store k in the list
      (pi A E Op V\
         fold-map (app [F, app[Op, V, E]]) A
                  (app [F, app[Op, V, E]]) [E | A])
 =>
      fold-map RHS [] _ Uses,
      std.map Uses (real_to_int) Uses_int,
      list_sort Uses_int Suses,
      coq.say "final list" Suses].

% The input must have the form:
%  fun f => forall n, ... -> ... -> f n = E
% Displays the ordered sequence of k integers (in builtin type int), such
% that (f (n - k)) appears in E.
pred find_uses i:term.

find_uses Abs_eqn :-
    Abs_eqn = fun _Name1 _T F,
    pi f\ sigma F1 \
    (F f) = prod _ _ F1,
    pi n G\
      eat_implications f (F1 n).

main [str Name, trm Abs_eqn] :- 
  coq.say "Hello" Name,
  find_uses Abs_eqn.

main _ :-
  coq.error "Usage: Recursive name equation_1 .. equation_n".

}}.

Elpi Typecheck.

(* Elpi Recursive ex1 (fun ex1 => ex1 0 = 0). *)

Elpi Recursive fib
  (fun fib =>
    forall n : R, Rnat n -> n < 2 -> fib n = fib (n - 1) + fib (n - 2)).

(* I was exoecting the command to print a list containing representations
  of 1 and 2 *)
