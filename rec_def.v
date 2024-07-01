From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.
Require Import R_subsets.

Open Scope R_scope.

Definition Rnat_rec {A : Type} (v0 : A) (stf : R -> A -> A) (x : R) : A :=
  nat_rect (fun _ => A) v0 (fun x => stf (INR x)) (IRN x).

Lemma Rnat_rec0 {A : Type} (v0 : A) stf : Rnat_rec v0 stf 0 = v0.
Proof.
now unfold Rnat_rec, IRN; rewrite IRZ_IZR.
Qed.

Lemma Rnat_rec_succ {A : Type} (v0 : A) stf (x : R) :
  Rnat x ->
  Rnat_rec v0 stf (x + 1) = stf x (Rnat_rec v0 stf x).
Proof.
intros xnat.
destruct (Rnat_exists_nat x) as [x' xx'].
unfold Rnat_rec.
replace (IRN (x + 1)) with (S (IRN x)).
  now simpl; rewrite INR_IRN.
rewrite xx'.
unfold IRN.
rewrite <- plus_IZR.
rewrite !IRZ_IZR.
replace 1%Z with (Z.of_nat 1) by (simpl; ring).
rewrite <- Nat2Z.inj_add.
rewrite !Zabs2Nat.id.
ring.
Qed.

(* This lemma could be used to automatically prove that functions
  defined by our new command satisfy the specification that was given
  as a definition.  This lemma is not intended for final users' eyes
  because it exposes the nat type. We may want to add a pre-condition
  to restrict usage to the Rnat subset.  It is not certain this
  lemma will be used much, since unfold does the same trick.
  *)
Lemma Rnat_rec_to_nat_rec {A : Type} (v0 : A) (stf : R -> A -> A) (x : R) :
   Rnat_rec v0 stf x = 
   nat_rect (fun _ => A) v0 (fun x => stf (INR x)) (IRN x).
Proof. easy. Qed.

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

pred alist_insert i:pair int term i:list (pair int term)
  o:list (pair int term).

alist_insert (pr I _) [pr I _ | _] _ :- !,
  coq.error "There are two declarations for the same integer"  I.

alist_insert (pr I V) [pr I2 V2 | L] [pr I V, pr I2 V2 | L] :-
  I < I2, !.

alist_insert (pr I V) [pr I2 V2 | L] [pr I2 V2 | L2] :-
  alist_insert (pr I V) L L2.

alist_insert (pr I V) [] [pr I V].

pred alist_sort i:list (pair int term) o:list (pair int term).

alist_sort [] [].

alist_sort [A | L] L2 :-
  alist_insert A L L2.

% converting a coq object of type positive to a builtin int
pred positive_to_int i:term o:int.
% TODO regarder dans algebra tactics
positive_to_int XH 1 :-
  coq.locate "xH" Gref,
  XH = global Gref.

positive_to_int {{:coq xI lp:X}} N1 :-
    positive_to_int X N,
  N1 is 2 * N + 1.

% TODO
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

pred list_app i:list (pair int term) i:list (pair int term)
  o:list (pair int term).

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

make_initial_list [] {{ @nil R}}.

make_initial_list [pr _ V | L] (app [{{ @cons R}}, V, Tl]) :-
  make_initial_list L Tl.

pred make_recursive_step_list i:(term -> term) i:int i:int o:(term -> term).

make_recursive_step_list Func 0 _Rank R :-
  pi V\
   app [{{ cons}}, (Func V), {{ nil }}] = R V.

make_recursive_step_list Func N Rank R :-
  std.do! [
    0 < N,
    N1 is N - 1,
    Rank1 is Rank + 1,
    int_to_nat Rank1 RankTerm,
    make_recursive_step_list Func N1 Rank1 Func',
    pi V \
      app [{{ cons}}, app [{{ nth}}, {{R}}, RankTerm, V, {{ 0}}],
           Func' V] = R V
  ].



% make a proof that the input real number is in the Rnat subset
pred mk_Rnat_proof i:term o:term.

mk_Rnat_proof {{0}} {{Rnat0}}.

mk_Rnat_proof {{IZR(Z.pos lp:P)}} {{Rnat_cst lp:P}}.

% QUIRKY: performs part of the jobs of finding the uses of the function
% given as first argument inside the second argument.
% The second argument has to be a sequence of nested implications whose
% conclusion is an equality.  The instances we are looking for have to be
% of the form (F (n - k)).  The k values must be real-positive numbers.
pred eat_implications i:term, o:term.

eat_implications (prod _ _ G) R :-
  %(pi x\ not(occurs x (G x))),
  (pi x y\ G x = G y), !,
  pi h \ 
   eat_implications (G h) R.

eat_implications {{_ = lp:RHS}} RHS.

pred build_step_function i:int, i:term, i:term, i:term, o:term.

build_step_function Order F N RHS STP :-
   std.do! [
      % This should recognize instance of (F (N - k)) and store k in the list
      (pi A E Op V\
         fold-map (app [F, app[Op, V, E]]) A
                  (app [F, app[Op, V, E]]) [E | A])
        =>
      (fold-map RHS [] _ Uses),
      std.map Uses (real_to_int) Uses_int,
      list_max Uses_int L,
            coq.say "arrived here",
% Need to generate an abstraction that gives the name V to
% the result of the recursive call
std.assert! (L = Order)
  "The number of base values does not match the depth of recursive calls",
     (pi V \
      (pi A B \ copy A B :-
         replace_rec_call_by_seq_nth L F N V A B) =>
         copy RHS (RHS' V)),
      L1 is L - 1,
      make_recursive_step_list RHS' L1 0 RecList,
     STP = (fun `v` {{list R}} RecList),
           coq.say "arrived here"
].

% The input must have the form:
%  fun f => f 0 = V1 /\ ... f k = Vk /\ forall n, ... -> ... -> f n = E
% Displays the ordered sequence of k integers (in builtin type int), such
% that (f (n - k)) appears in E.
pred find_uses i:term, o:term.

find_uses (fun N Ty Bo) R :-
  pi f\
    decl f N Ty => % let one call the pretty printer and type checker inside
    find_uses_of f (Bo f) R.  % R does not use f recursively, but rather
                              % the nth value of its recursion history

pred find_uses_of i:term, i:term, o:term.

find_uses_of F Spec Final :-
  std.do! [
    collect_specs F Spec Sps,
    alist_sort Sps Sps2,
    check_all_present 0 Sps2 Order,
    make_initial_list Sps2 ListSps,
    % coq.say "ListSps = " {coq.term->string ListSps},
    fetch_recursive_equation Spec Ts,
% TODO : error reporting is not satisfactory here
    std.assert! (Ts = [prod Scalar_name Sc_type F1])
       "Expecting exactly one recursive equation",
    (pi n\
      decl n Scalar_name Sc_type =>
      (eat_implications (F1 n) (RHS n),
       build_step_function Order F n (RHS n) (Main_expression n))),
    %Final = {{Rnat_rec lp:ListSps (fun x : R => lp:(Main_expression x)) }},
    Final = {{ fun r : R => nth 0 
                (Rnat_rec lp:ListSps lp:{{ fun Scalar_name {{R}}
                              Main_expression}} r) 0}}
  ].


pred prove_base_case i:term i:term i:term o:term.

prove_base_case ListSps STP {{lp:F (IZR lp:Z) = lp:V}} Prf :-
  real_to_int {{IZR lp:Z}} I,
  int_to_nat I N,
  Prf1 =
    {{eq_ind_r (fun z => Z.abs_nat z = lp:N)
       (eq_refl : Z.abs_nat lp:Z = lp:N) (IRZ_IZR lp:Z)}},
  Prf =
    {{eq_ind_r (fun n =>
        nth 0 (nat_rect (fun _ => list R)
                 lp:ListSps lp:STP n) 0 = lp:V)
        (eq_refl : nth 0 (nat_rect (fun _ => list R)
            lp:ListSps lp:STP lp:N) 0 = lp:V) lp:Prf1}},
  std.assert-ok! (coq.typecheck Prf {{lp:F (IZR lp:Z) = lp:V}})
     "failed to prove a base case".

main [trm (fun N _ _ as Abs_eqn)] :-
std.do! [
  find_uses Abs_eqn Final,
  % std.assert! (find_uses Abs_eqn Final) "Oops",
  std.assert-ok! (coq.typecheck Final Ty) "Type error",
  coq.name->id N Name,
  coq.env.add-const Name Final Ty @transparent! C,
  coq.say "Defined" C,

%  (Abs_eqn = fun _ _ F),
% (Statement = (F (global (const C)))),
% (Statement = {{lp:Statement1 /\ lp:_Statement2}}),
%  coq.say "statement to prove" {coq.term->string Statement1},
%  (Statement1 = {{lp:_ lp:Arg = lp:Val}}),
%  coq.say "debug" Arg,
%  mk_Rnat_proof Arg Arg_nat,
% std.assert-ok! (coq.typecheck Arg_nat {{Rnat lp:Arg}})
%   "not the right proof"

].

main _L :-
  coq.error [] "Usage: Recursive name equation_1 .. equation_n".

}}.

Elpi Typecheck.

Elpi Export Recursive.

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

Notation "'def' id 'such' 'that' bo" := (fun id => bo) 
 (id binder, bo at level 100, at level 1, only parsing).

(* Elpi Trace Browser. *)

Recursive (def simple_example such that simple_example 0 = 0 /\
   forall n, Rnat (n - 1) -> simple_example n = simple_example (n - 1) + 1).

Elpi Query
  lp:{{ prove_base_case {{0 :: nil}}
     {{fun (n : nat) (l : list R) => nth 0 l 0 + 1 :: nil}}
     {{simple_example 0 = 0}} P}}.

Recursive (def fib such that fib 0 = 0 /\ (fib 1 = 1) /\
    forall n : R, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)).

Elpi Query
  lp:{{ prove_base_case {{0 :: 1 :: nil}} 
    {{fun (n : nat) (l : list R) => nth 1 l 0 :: nth 0 l 0 + nth 1 l 0 :: nil}}
    {{fib 1 = 1}} P
    }}.

Fixpoint shift_seq {A : Type} (default : A) (offset length : nat)
  (l : list A) (final : list A -> A) :=
  match length with
    0%nat =>  final l :: nil
  | S p => nth (S offset) l default :: shift_seq default (S offset) p l final
  end.

Lemma shift_seq_prop_rec {A : Type} (default : A) base offset length llength l
  (f : nat -> A) final:
  (forall k, (k <= llength)%nat -> nth k l default = f (base + k)%nat) ->
  (offset + length <= llength)%nat ->
  (forall k, (k < length)%nat ->
     nth k (shift_seq default offset length l final) default =
     f (S base + offset + k)%nat).
Proof.
intros lprop.
revert offset; induction length as [ | len Ih].
  intros offset k abs; lia.
intros offset offsetbound k kbound.
  simpl. (* bug of vscoq: if I write simpl, then remove, the goal window
            is not a good representation of the state of Coq. *)
  destruct k as [ | k'].
    replace (S (base + offset + 0)) with (base + S offset)%nat by ring.
    apply lprop; lia.
  rewrite Ih.
    apply f_equal; ring.
  lia.
lia.
Qed.

Print fib.


Lemma fib0 : fib 0 = 0.
Proof.
(* This proof serves as a a workplan for automatic generation in
  the Elpi command. *)
assert (tmp3: Z.abs_nat (IRZ 0) = 0%nat).
  apply (eq_ind_r
           (fun z => Z.abs_nat z = 0%nat)
           (eq_refl : Z.abs_nat 0 = 0%nat) (IRZ_IZR _)).
apply (eq_ind_r
         (fun n =>
          nth 0 (nat_rect (fun _ => list R)
           (0 :: 1 :: nil)
         (fun _ l => (nth 1 l 0 ::
                nth 0 l 0 + nth 1 l 0 :: nil)) n) 0 = 0
         ) (eq_refl : nth 0 (nat_rect (fun _ => list R)
           (0 :: 1 :: nil)
         (fun _ l => (nth 1 l 0 ::
                nth 0 l 0 + nth 1 l 0 :: nil)) 0) 0 = 0) tmp3).
Qed.

Lemma fib1 : fib 1 = 1.
Proof.
(* This proof serves as a a workplan for automatic generation in
  the Elpi command. *)
assert (tmp3: Z.abs_nat (IRZ 1) = 1%nat).
  apply (eq_ind_r
           (fun z => Z.abs_nat z = 1%nat)
           (eq_refl : Z.abs_nat 1 = 1%nat) (IRZ_IZR _)).
apply (eq_ind_r
         (fun n =>
          nth 0 (nat_rect (fun _ => list R)
           (0 :: 1 :: nil)
         (fun _ l => (nth 1 l 0 ::
                nth 0 l 0 + nth 1 l 0 :: nil)) n) 0 = 1
         ) (eq_refl : nth 0 (nat_rect (fun _ => list R)
           (0 :: 1 :: nil)
         (fun _ l => (nth 1 l 0 ::
                nth 0 l 0 + nth 1 l 0 :: nil)) 1) 0 = 1) tmp3).
Qed.

(* This is a first attempt at proving the recursive part of fib's
  definition, but it was discovered later that an induction proof
  is not needed.*)

Lemma fib_succ : forall n, Rnat (n - 2) ->
  fib n = fib (n - 2) + fib (n - 1).
Proof.
unfold fib.
set (step := fun _ v => _ :: _ + _ :: _).

intros n.
enough (main : forall k, Rnat k -> Rnat_rec (0 :: 1 :: nil)
               step k =
   (fib k :: fib (k + 1) :: nil)).
  replace n with (n - 2 + 1 + 1) at 2 by ring.
  replace (n - 1) with (n - 2 + 1) by ring.
  intros n2nat.
  rewrite 2!Rnat_rec_succ; simpl.
  all:try (repeat apply Rnat_succ; exact n2nat).
  now rewrite main; simpl.
intros k; induction 1 as [ | k knat Ih].
  rewrite Rnat_rec0.
  rewrite fib0.
  replace (0 + 1) with 1 by ring.
  now rewrite fib1.
rewrite Rnat_rec_succ; auto.
rewrite Ih.
unfold step; simpl.
apply f_equal.
unfold fib at 3.
rewrite Rnat_rec_succ; [ | repeat apply Rnat_succ; apply knat].
rewrite Rnat_rec_succ; [ | repeat apply Rnat_succ; apply knat].
simpl.
fold step.
now rewrite Ih; simpl.
Qed.

(* This one is based on the discovery that a proof by induction is actually *)
(* not needed. *)
Lemma fib_succ2 : forall n, Rnat (n - 2) ->
  fib n = fib (n - 2) + fib (n - 1).
Proof.
unfold fib.
intros n; set (m := n - 2); intros mnat.
replace n with (m + 1 + 1) by (unfold m; ring).
rewrite !Rplus_minus_r.
rewrite !Rnat_rec_succ; try reflexivity.
all: repeat apply Rnat_succ; try assumption.
Qed.

(* This example puts the user interface under stress, as it returs
  a tree of additions, where all the leaves are either 1 or (0 + 1).
  with the parentheses, this data should take at least 10 k chars. *)
Lemma fib20 : fib 20 = 6765.
Proof.
unfold fib.
rewrite Rnat_rec_to_nat_rec.
unfold IRN.
rewrite IRZ_IZR.
(* If the simpl command is placed alone in a command and its result
  should be improved, this breaks the outputting machinery of
  VsCoq2's current version.  Otherwise, just executing the combined
  simpl; ring command leads to a command that takes 3 seconds to
  execute. *)
simpl; ring_simplify.
easy.
Qed.
