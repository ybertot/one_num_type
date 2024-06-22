From elpi Require Import elpi.
Require Import List Reals.
Open Scope R_scope.

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

% the inverse predicate, int_to_real, produces a real number that is
% the representation of the integer.

pred int_to_real i:int o:term.
int_to_real 0 T :-
  std.do! [
    coq.locate "IZR" Izr_gref,
    coq.locate "Z0" Zero_gref,
    T = app[global Izr_gref, global Zero_gref]
  ].

int_to_real N T :-
  int_to_positive N NT,
  std.do![
    coq.locate "IZR" Izr_gref,
    coq.locate "Z.pos" Zpos_gref,
    T = app[global Izr_gref, app[global Zpos_gref, NT]]
  ].

pred int_to_positive i:int o:term.
int_to_positive 1 (global Hgref) :-
  coq.locate "xH" Hgref.

int_to_positive N (app[C, Td]) :-
  1 < N,
  Nd is N div 2,
  B is N mod 2,
  choose_pos_constructor.aux B C,
  int_to_positive Nd Td.

pred int_to_nat i:int o:term.
int_to_positive 0 (global Oref) :-
  coq.locate "O" Oref.

int_to_positive N (app [global Sref, N']) :-
  std.do! [
    0 < N,
    coq.locate "S" Sref,
    N1 is N - 1,
    int_to_nat N1 N'
  ].
  
pred choose_pos_constructor.aux i:int o:term.

choose_pos_constructor.aux 1 T :-
  coq.locate "xI" XI_gref,
  T = global XI_gref.

choose_pos_constructor.aux 0 T :-
  coq.locate "xO" XI_gref,
  T = global XI_gref.

pred replace_rec_call_by_seq_nth i:int i:term i:term i:term i:term o:term.

% replace (F (N - k)) by (nth (L - k) V 0) everywhere in term A
% But the subtraction (L - k) is actually computed and a number of type nat,
% while (N - k) is a term representing a subtraction, where k is a
% positive integer constant of type R

replace_rec_call_by_seq_nth L F N V A B :-
  std.do! [
    coq.locate "Rminus" Rminus,
    A = app[F, app[global Rminus, N, K]],
    real_to_int K Kn,
    In is L - Kn,
    int_to_nat In I,
    coq.locate "nth" Nth,
    coq.locate "R" Rtype,
    Zero = {{:coq 0:R}},
    B = app[global Nth, global Rtype, N, V, Zero]
  ].

choose_pos_constructor.aux _ _ :-
  coq.error "choose_pos_constructor.auxs only accepts 0 or 1 as input".


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
      list_sort Uses_int Srt_uses,
      coq.say "final list" Srt_uses].

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

Check fun fib =>
        fib 0 = 0 /\
        fib 1 = 1 /\
        (forall n, Rnat n -> n < 2 -> fib n = fib (n - 1) + fib (n - 2)).

(* From this input, we should produce the function definition of fib' in
  file fib.v *)
