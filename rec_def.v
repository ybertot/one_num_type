From elpi Require Import elpi.
Require Import List Reals.
Open Scope R_scope.

Inductive Rnat : R -> Prop :=
  Rnat0 : Rnat 0
| Rnat_succ : forall n, Rnat n -> Rnat (n + 1).

Parameter Rnat_rec :
  forall {A : Type} (v0 : A) (step : R -> A -> A) (n : R)
    (h : Rnat n), A.

Parameter Rnat_rec0 : forall {A : Type} (v0 : A) (step : R -> A -> A),
  Rnat_rec v0 step 0 Rnat0 = v0.

Parameter Rnat_rec_succ : forall {A : Type} (v0 : A) (step : R -> A -> A)
  n (h : Rnat n) (h' : Rnat (n + 1)),
  Rnat_rec v0 step (n + 1) h' = step n (Rnat_rec v0 step n h).

Elpi Command Recursive.

Elpi Accumulate lp:{{

% sorting a list of integers removing duplicates
pred list_insert i:int i:list int o:list int.

list_insert I [] [I].

list_insert A [A | L] [A | L] :- !.

list_insert I [A | L] [I, A | L] :-
  I < A, !.

list_insert I [A | L] [A | L1] :-
  list_insert I L L1, !.
  
% sorting a list of integers: the main predicate

pred list_sort i:list int o:list int.
list_sort [] [].

list_sort [A | L] L1 :-
  list_sort L L2, !,
  list_insert A L2 L1.

pred list_max i:list int o:int.
list_max [A] A.

list_max [A, B | L]  V:-
  A < B, !, list_max [B | L] V.

list_max [A, _B | L] V :-
  list_max [A | L] V.

% sorting an association list for values associated to integers

pred alist_insert i:pair int term i:list (pair int term) o:list (pair int term).

alist_insert (pr I _) [pr I _ | _] _ :- !,
  coq.error "There are two declarations for the same integer"  I.

alist_insert (pr I V) [pr I2 V2 | L] [pr I V, pr I2 V2 | L] :-
  I < I2, !.

alist_insert (pr I V) [pr I2 V2 | L] [pr I2 V2 | L2] :-
  alist_insert (pr I V) L L2.

pred alist_sort i:list (pair int term) o:list (pair int term).

alist_sort [] [].

alist_sort [A | L] L2 :-
  alist_insert A L L2.

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
real_to_int (app [Izr, app [Zpos, P]]) I :-
  Izr = {{ IZR}},
  Zpos = {{ Z.pos}},
  positive_to_int P I.

real_to_int Zero 0 :-
  Zero = {{ 0}}.

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
int_to_nat 0 (global Oref) :-
  coq.locate "O" Oref.

int_to_nat N (app [global Sref, N']) :-
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

choose_pos_constructor.aux _ _ :-
  coq.error "choose_pos_constructor.aux only accepts 0 or 1 as input".

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
    Zero = {{ 0}},
    B = app[global Nth, global Rtype, I, V, Zero]
  ].

pred make_one_spec i:term i:term o:pair int term.
make_one_spec V1 V2 (pr I1 V2) :-
  real_to_int V1 I1,!.

pred list_app i:list (pair int term) i:list (pair int term) o:list (pair int term).

list_app [] L2 L2.

list_app [A | L1] L2 [A | L3] :-
  list_app L1 L2 L3.

pred fetch_recursive_equation i:term o:list term.

fetch_recursive_equation X [X] :-
  X = (prod _ _ _), !.

fetch_recursive_equation (app [And, Code1, Code2]) R_eqs :-
  std.do! [
    coq.locate "and" Andgref,
    And = global Andgref,
    fetch_recursive_equation Code1 L1,
    fetch_recursive_equation Code2 L2,
    std.append L1 L2 R_eqs
  ].

fetch_recursive_equation (app [Eq , _, _, _]) [] :-
  coq.locate "eq" Eqgref, Eq = global Eqgref, !.

fetch_recursive_equation A _ :-
  coq.say "wrong term" A,
  coq.error "expecting function specification to be either of the form"
   "f 0 = v1 /\ f 1 = v2  or of the form forall n, .. -> f n = V2"
   "but found expressions of another form".

pred collect_specs i:term i:term o:list (pair int term).

collect_specs F (app [Eq, _, app [F, V1], V2]) [S] :-
% TODO: ask about placing directly {{ eq}} above.
  std.do! [
    coq.locate "eq" Eqgref,
    Eq = global Eqgref,
    make_one_spec V1 V2 S
  ].

collect_specs _F (prod _ _ _) [].

collect_specs F (app [And, Code1, Code2]) Specs :-
% TODO: same as Eq above
  std.do! [
    coq.locate "and" Andgref,
    And = global Andgref,
    collect_specs F Code1 Specs1,
    collect_specs F Code2 Specs2,
    std.append Specs1 Specs2 Specs
  ].

pred check_all_present i:int i:list (pair int term) o:int.

check_all_present N [] N.

check_all_present N [pr N _ | L] N2 :-
  !,
  N1 is N + 1,
  check_all_present N1 L N2.

check_all_present N [pr _ _ | _] _ :-
  coq.error "missing value for" N.

pred make_initial_list i:list (pair int term) o:term.

make_initial_list [] {{ nil}}.

make_initial_list [pr _ V | L] (app [{{ cons}}, V, Tl]) :-
  make_initial_list L Tl.

pred make_recursive_step_list i:(term -> term) i:int i:int o:(term -> term).

make_recursive_step_list Func 0 Rank R :-
  pi V\
   app [{{ cons}}, (Func V), {{ nil }}] = R V.

make_recursive_step_list Func N Rank R :-
  std.do! [
    1 < N,
    N1 is N - 1,
    Rank1 is Rank + 1,
    int_to_nat Rank RankTerm,
    make_recursive_step_list Func N1 Rank1 Func',
    pi V \
      app [{{ cons}}, app [{{ nth}}, RankTerm, V, {{ 0}}],
           Func' V] = R V
  ].

% QUIRKY: performs part of the jobs of finding the uses of the function
% given as first argument inside the second argument.
% The second argument has to be a sequence of nested implications whose
% conclusion is an equality.  The instances we are looking for have to be
% of the form (F (n - k)).  The k values must be real-positive numbers.
pred eat_implications i:term, i:term, i:term, o:term.

eat_implications F N (prod _ _ G) R :- !,
  pi h \ 
   eat_implications F N (G h) R.

eat_implications F N G R :-
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
% TODO: just take the last element
      list_max Srt_uses L,
% Need to generate an abstraction that gives the name V to
% the result of the recursive call
     (pi V \
      (pi A B \ copy A B :-
         replace_rec_call_by_seq_nth L F N V A B) =>
         copy RHS (RHS' V)),
     R = (fun `v` _ RHS'),
].

% The input must have the form:
%  fun f => f 0 = V1 /\ ... f k = Vk /\ forall n, ... -> ... -> f n = E
% Displays the ordered sequence of k integers (in builtin type int), such
% that (f (n - k)) appears in E.
pred find_uses i:term.

find_uses (fun N Ty Bo) :-
  pi f\
    decl f `N` Ty => % let one call the pretty printer and type checker inside
    find_uses_of f (Bo f).

pred find_uses_of i:term, i:term.

find_uses_of F Spec  :-
  std.do! [
    collect_specs F Spec Sps,
    alist_sort Sps Sps2,
    check_all_present 0 Sps2 Order,
    make_initial_list Sps2 ListSps,
    coq.say "ListSps = " {coq.term->string ListSps},
    fetch_recursive_equation Spec Ts,
% TODO : error reporting is not satisfactory here
    std.assert! (Ts = [prod _ _ F1]) "Expecting exactly one recursive equation",
    (pi n\
      eat_implications F n (F1 n) (R n)),
    Final = fun `n` _ R,
    coq.say "Final" {coq.term->string Final},
  ].

main [str Name, trm Abs_eqn] :- 
  coq.say "Hello" Name,
  find_uses Abs_eqn.

main _ :-
  coq.error "Usage: Recursive name equation_1 .. equation_n".

}}.

Elpi Typecheck.

(*
Elpi Query lp:{{ int_to_nat 3 V }}.
*)

(* Elpi Query lp:{{
  sigma F \
  {{ sin 0 = 0 /\ sin 1 = 1}} = F,
  {{ sin}} = G,
  coq.say F "function" G,
  collect_specs {{ sin}} F F1
  }}.
*)

(* Elpi Recursive ex1 (fun ex1 => ex1 0 = 0). *)

Elpi Recursive fib
  (fun fib => fib 0 = 0 /\ fib 1 = 1 /\
    forall n : R, Rnat n -> n < 2 -> fib n = fib (n - 2) + fib (n - 1)).

(* Check fun fib =>
        fib 0 = 0 /\
        fib 1 = 1 /\
        (forall n, Rnat n -> n < 2 -> fib n = fib (n - 1) + fib (n - 2)). *)

(* From this input, we should produce the function definition of fib' in
  file fib.v *)
