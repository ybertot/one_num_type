From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.

Require Import R_subsets.
Require Import Derive.

Open Scope R_scope.

Module private.

(* This lemma could be used to automatically prove that functions
  defined by our new command satisfy the specification that was given
  as a definition.  This lemma is not intended for final users' eyes
  because it exposes the nat type. We may want to add a pre-condition
  to restrict usage to the Rnat subset.  It is not certain this
  lemma will be used much, since unfold does the same trick.
  *)
Lemma Rnat_rec_to_nat_rec_p {A : Type} (v0 : A) (stf : R -> A -> A)
  (p : positive) :
   Rnat_rec v0 stf (IZR (Z.pos p)) =
   nat_rect (fun _ => A) v0 (fun x => stf (INR x))
     (Z.abs_nat (Z.pos p)).
Proof.
unfold Rnat_rec, IRN.
now rewrite IRZ_IZR.
Qed.

Lemma IRN_to_S (r : R) (p : Z) (q : Z):
  (q < p)%Z ->
  Rnat (r - IZR p) -> IRN (r - IZR q) =
     (Z.abs_nat (p - q) + IRN (r - IZR p))%nat.
Proof.
intros qltp rmpnat.
unfold IRN.
destruct (Rnat_exists_nat (r - IZR p)) as [v vq].
assert (rq : r = IZR (Z.of_nat v + p)).
  apply (Rplus_eq_reg_r (- (IZR p))).
  rewrite <- opp_IZR at 2.
  rewrite <- plus_IZR.
  replace (Z.of_nat v + p + - p)%Z with (Z.of_nat v) by ring.
  exact vq.
rewrite <- Zabs2Nat.inj_add.
    rewrite rq.
    rewrite <- minus_IZR, IRZ_IZR.
    rewrite <- minus_IZR.
    replace (Z.of_nat v + p - p)%Z with (Z.of_nat v) by ring.
    rewrite IRZ_IZR.
    apply f_equal.
    ring.
  lia.
rewrite vq, IRZ_IZR.
apply Nat2Z.is_nonneg.
Qed.

Lemma IRN_to_S_top (r : R) (p : Z) :
  (0 < p)%Z ->
  Rnat (r - IZR p) -> IRN r = (Z.abs_nat p + IRN (r - IZR p))%nat.
Proof.
intros pgt0 rmpnat.
unfold IRN.
destruct (Rnat_exists_nat (r - IZR p)) as [v vq].
  assert (rq : r = IZR (Z.of_nat v + p)).
  apply (Rplus_eq_reg_r (- (IZR p))).
  rewrite <- opp_IZR at 2.
  rewrite <- plus_IZR.
  replace (Z.of_nat v + p + - p)%Z with (Z.of_nat v) by ring.
  exact vq.
rewrite <- Zabs2Nat.inj_add.
    rewrite rq.
    rewrite <- minus_IZR, IRZ_IZR.
    replace (Z.of_nat v + p - p)%Z with (Z.of_nat v) by ring.
    rewrite IRZ_IZR.
    apply f_equal.
    ring.
  lia.
rewrite vq, IRZ_IZR.
apply Nat2Z.is_nonneg.
Qed.

Lemma nat_rect_list_IZR (l0 : list Z) (f : nat -> list Z -> list Z)
  (f' : nat -> list R -> list R)
  (n : nat) :
  (forall k lR lZ, lR = map IZR lZ ->
        f' k lR = map IZR (f k lZ)) ->
  nat_rect (fun _ => list R) (map IZR l0) f' n =
  map IZR (nat_rect (fun _ => list Z) l0 f n).
Proof.
intros ff'; induction n as [ | n Ih].
  easy.
simpl.
apply ff'.
apply Ih.
Qed.

Lemma Rnat_rec_nat (l0 : list R) (f : R -> list R -> list R) (n : R) :
  Forall Rnat l0 ->
  (forall n l, Rnat n -> Forall Rnat l -> Forall Rnat (f n l)) ->
  Rnat n -> Forall Rnat (Rnat_rec l0 f n).
Proof.
intros ln fn.
induction 1 as [ | n nnat Ih].
  now rewrite Rnat_rec0.
rewrite Rnat_rec_succ;[ | assumption].
now apply fn.
Qed.

End private.

Ltac prove_recursive_specification T Order := unfold T;
  repeat split;
    (now (rewrite Rnat_rec0 || rewrite private.Rnat_rec_to_nat_rec_p)) ||
    (let N := fresh "n" in let Nnat := fresh "nnat" in
     let Protector := fresh "protect_base" in
     unfold Rnat_rec; intros N Nat;
     set (Protector := IRN (N - IZR Order));
     repeat (rewrite (private.IRN_to_S N Order);[ | reflexivity | assumption]);
     rewrite (private.IRN_to_S_top N Order);[ | reflexivity | assumption];
     (reflexivity (* useful when N is only used in recursive calls*) ||
       (simpl;
        let Last_eqn := fresh "H" in
        enough (Last_eqn : IZR Order + INR (IRN (N - IZR Order)) = N)
            by (rewrite Last_eqn; reflexivity);
            rewrite INR_IRN;[try ring | assumption]))).


Elpi Command Recursive.

Elpi Accumulate lp:{{

% sorting a list of integers removing duplicates
pred list_insert i:int, i:list int, o:list int.

list_insert I [] [I].

list_insert A [A | L] [A | L] :- !.

list_insert I [A | L] [I, A | L] :-
  I < A, !.

list_insert I [A | L] [A | L1] :-
  list_insert I L L1, !.
  
% sorting a list of integers: the main predicate

pred list_sort i:list int, o:list int.
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

pred alist_insert i:pair int term, i:list (pair int term),
  o:list (pair int term).

alist_insert (pr I _) [pr I _ | _] _ :- !,
  coq.error "There are two declarations for the same integer"  I.

alist_insert (pr I V) [pr I2 V2 | L] [pr I V, pr I2 V2 | L] :-
  I < I2, !.

alist_insert (pr I V) [pr I2 V2 | L] [pr I2 V2 | L2] :-
  alist_insert (pr I V) L L2.

alist_insert (pr I V) [] [pr I V].

pred alist_sort i:list (pair int term), o:list (pair int term).

alist_sort [] [].

alist_sort [A | L] L2 :-
  alist_insert A L L2.

% converting a coq object of type positive to a builtin int
pred positive_to_int i:term, o:int.
% TODO regarder dans algebra tactics
positive_to_int {{xH}} 1 :- !.

positive_to_int {{:coq xI lp:X}} N1 :-
  positive_to_int X N,
  N1 is 2 * N + 1.

% TODO
positive_to_int {{xO lp:X}} N1 :-
  positive_to_int X N,
  N1 is 2 * N.

% converting a real number to an int
pred real_to_int i:term, o:int.

% actually, this works for any positive number encapsulated in two unary
% functions
real_to_int {{IZR (Z.pos lp:P)}} I :-
  positive_to_int P I.

real_to_int {{0}} 0.

% the inverse predicate, int_to_real, produces a real number that is
% the representation of the integer.

pred int_to_real i:int, o:term.

int_to_real I {{IZR lp:Iz}} :-
  int_to_Z I Iz.

pred int_to_Z i:int, o:term.
int_to_Z 0 {{Z0}} :- !.

int_to_Z I {{Z.pos lp:Ip}} :-
  int_to_positive I Ip.

pred int_to_positive i:int, o:term.
int_to_positive 1 {{xH}}:- !.

int_to_positive N (app[C, Td]) :-
  1 < N,
  Nd is N div 2,
  B is N mod 2,
  choose_pos_constructor.aux B C,
  int_to_positive Nd Td.

pred int_to_nat i:int, o:term.
int_to_nat 0 {{O}} :- !.

int_to_nat N {{S lp:N'}} :-
  std.do! [
    0 < N,
    N1 is N - 1,
    int_to_nat N1 N'
  ].
  
pred choose_pos_constructor.aux i:int, o:term.

choose_pos_constructor.aux 1 {{xI}} :- !.

choose_pos_constructor.aux 0 {{xO}} :- !.

choose_pos_constructor.aux _ _ :-
  coq.error "choose_pos_constructor.aux only accepts 0 or 1 as input".

pred replace_rec_call_by_seq_nth i:int, i:term, i:term, i:term ,i:term,
  o:term.

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

pred make_one_spec i:term, i:term, o:pair int term.
make_one_spec V1 V2 (pr I1 V2) :-
  real_to_int V1 I1,!.

pred list_app i:list (pair int term), i:list (pair int term),
  o:list (pair int term).

list_app [] L2 L2.

list_app [A | L1] L2 [A | L3] :-
  list_app L1 L2 L3.

pred fetch_recursive_equation i:term, o:list term.

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

fetch_recursive_equation {{lp:_ = lp: _}} [].

fetch_recursive_equation A _ :-
  coq.say "wrong term" A,
  coq.error "expecting function specification to be a conjunction of"
   "formulas of the form f 0 = v1 f 1 = v2  or forall n, .. -> f n = V2"
   "but found expressions of another form".

pred collect_base_specs i:term, i:term, o:list (pair int term).

collect_base_specs F {{lp:F lp:V1 = lp:V2}} [S] :-
  std.do! [
    make_one_spec V1 V2 S
  ].

collect_base_specs _F (prod _ _ _) [].

collect_base_specs F {{lp:Code1 /\ lp:Code2}} Specs :-
  std.do! [
    collect_base_specs F Code1 Specs1,
    collect_base_specs F Code2 Specs2,
    std.append Specs1 Specs2 Specs
  ].

pred check_all_present i:int, i:list (pair int term), o:int.

check_all_present N [] N.

check_all_present N [pr N _ | L] N2 :-
  !,
  N1 is N + 1,
  check_all_present N1 L N2.

check_all_present N [pr _ _ | _] _ :-
  coq.error "missing value for" N.

pred make_initial_list i:list (pair int term), o:term.

make_initial_list [] {{ @nil R}}.

make_initial_list [pr _ V | L] (app [{{ @cons R}}, V, Tl]) :-
  make_initial_list L Tl.

pred make_recursive_step_list i:(term -> term), i:int, i:int,
   o:(term -> term).

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

pred shift_real i:int, i:term, o:term.

shift_real 0 N N.

shift_real K N {{lp:K_as_real + lp:N}}:-
  std.do! [
    0 < K,
    int_to_real K K_as_real].

% QUIRKY: performs part of the jobs of finding the uses of the function
% given as second argument inside the fourth argument.
% The fourth argument has to be a sequence of nested implications whose
% conclusion is an equality.  The instances we are looking for have to be
% of the form (F (n - k)).  The k values must be real-positive numbers.
% The first argument is the depth of the recursion, The third argument
% is the numeric variable used for recursion.
pred eat_implications i:int, i:term, i:term, i:term, o:term.

eat_implications Order F N (prod _ _ G) R :-
  %(pi x\ not(occurs x (G x))),
  (pi x y\ G x = G y), !,
  pi h \ 
   eat_implications Order F N (G h) R.

eat_implications Order F N G R :-
   std.do! [
    %$  G = {{_ = lp:RHS}}
      G = app [_, _, _, RHS],
      % This should recognize (f (n - k)) and store k in the list
      (pi A E Op V\
         %         fold-map (app [F, app[Op, V, E]]) A
                  %                 (app [F, app[Op, V, E]]) [E | A]
        fold-map {{lp:F (lp:V - lp:E)}} A
                 {{lp:F (lp:V - lp:E)}} [E | A])
        =>
      fold-map RHS [] _ Uses,
      std.map Uses (real_to_int) Uses_int,
      list_sort Uses_int Srt_uses,
% TODO: just take the last element, or avoid sorting
      list_max Srt_uses L,
% Need to generate an abstraction that gives the name V to
% the result of the recursive call
std.assert! (L = Order)
  "The number of base values does not match the depth of recursive calls",
shift_real Order N N_plus_Order,
     (pi V \
      ((pi A B \ copy A B :-
         replace_rec_call_by_seq_nth L F N V A B),
       copy N N_plus_Order) =>
         copy RHS (RHS' V)),
      L1 is L - 1,
      make_recursive_step_list RHS' L1 0 RecList,
     R = (fun `v` {{list R}} RecList)
].

% The input must have the form:
%  fun f => f 0 = V1 /\ ... f k = Vk /\ forall n, ... -> ... -> f n = E
% Displays the ordered sequence of k integers (in builtin type int), such
% that (f (n - k)) appears in E.
pred find_uses i:term, o:term, o:term.

find_uses (fun N Ty Bo) R Order_Z :-
  pi f\
    decl f N Ty => % let one call the pretty printer and type checker inside
    find_uses_of f (Bo f) R Order_Z. 
                              % R does not use f recursively, but rather
                              % the value of its recursion history at depth
                              % Order_Z (which must be a cic term of type Z)

pred find_uses_of i:term, i:term, o:term, o:term.

find_uses_of F Spec Final Order_Z :-
  std.do! [
    collect_base_specs F Spec Sps,
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
      eat_implications Order F n (F1 n) (Main_expression n)),
    %Final = {{Rnat_rec lp:ListSps (fun x : R => lp:(Main_expression x)) }},
    Final = {{ fun r : R => nth 0 
                (Rnat_rec lp:ListSps lp:{{ fun Scalar_name {{R}}
                              Main_expression}} r) 0}},
    int_to_Z Order Order_Z
  ].

pred make_eqn_proof i:Name, i:term, i:term, i:constant.

make_eqn_proof N_id Abs_eqn  Order C :-
std.do![
  Abs_eqn = fun _ _ F,
  Statement = (F (global (const C))),
  Eqs_N_id is N_id ^ "_eqn",
  coq.typecheck Eq_prf Statement ok,
  coq.ltac.collect-goals Eq_prf [G1] _ShelvedGs,
  coq.ltac.open(coq.ltac.call
    "prove_recursive_specification"
    [trm (global (const C)), trm Order]) G1 [],
  coq.env.add-const Eqs_N_id Eq_prf _ @opaque! C_eqn,
  coq.say "Defined" C_eqn].

make_eqn_proof _ _ _ _ :-
  coq.say "proof of equations failed".

main [trm (fun N _ _ as Abs_eqn)] :-
std.do! [
  find_uses Abs_eqn Final Order,
  std.assert-ok! (coq.typecheck Final Ty) "Type error",
  coq.name->id N N_id,
  
  coq.env.add-const N_id Final Ty @transparent! C,
  coq.say "Defined" C,

  make_eqn_proof N_id Abs_eqn Order C
].

main _L :-
  coq.error [] "Usage: Recursive name equation_1 .. equation_n".

}}.

Elpi Typecheck.

Elpi Export Recursive.

Notation "'def' id 'such' 'that' bo" := (fun id => bo) 
 (id binder, bo at level 100, at level 1, only parsing).

(* Elpi Trace Browser. *)

Recursive (def simple_example such that simple_example 0 = 0 /\
   forall n, Rnat (n - 1) -> simple_example n = simple_example (n - 1) + 1).

Recursive (def fib such that fib 0 = 0 /\ fib 1 = 1 /\
    forall n : R, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)).

Definition fibz (n : nat) : Z :=
  nth 0 (nat_rect (fun _ => list Z) (0 :: 1 :: nil)%Z
    (fun k l => nth 1 l 0%Z :: (nth 0 l 0 + nth 1 l 0)%Z :: nil) n) 0%Z.

Lemma fib_fibz n : Rnat n -> fib n = IZR (fibz (IRN n)).
Proof.
intros nnat.
unfold fib, Rnat_rec, fibz.
set (fr := nat_rect (fun _ : nat => list R) _ _ _).
set (fz := nat_rect (fun _ : nat => list Z) _ _ _).
enough (pr : fr = map IZR fz).
  destruct fr as [ | r0 tr].
    destruct fz as [ | z0 tz]; try discriminate.
    easy.
  destruct fz as [ | z0 tz]; try discriminate.
  simpl in pr; injection pr as r0q _.
  easy.
unfold fr, fz.
apply (private.nat_rect_list_IZR (0 :: 1 :: nil)%Z).
intros k lR lZ lq; simpl.
destruct lR as [ | r0 [ | r1 tr]].
    destruct lZ as [ | z0 tz]; try discriminate.
    now simpl; rewrite <- plus_IZR.
  destruct lZ as [ | z0 [ | z1 tz]]; try discriminate.
  simpl.
  now injection lq as r0q; rewrite r0q, <- plus_IZR.
destruct lZ as [ | z0 [ | z1 tz]]; try discriminate.
simpl; injection lq as r0q r1q tq; rewrite r0q, r1q, <- plus_IZR.
easy.
Qed.

Lemma fib_nat n : Rnat n -> Rnat (fib n).
Proof.
intros nnat.
enough (main : Forall Rnat (Rnat_rec (0 :: 1 :: nil)
  (fun _ l => nth 1 l 0 :: nth 0 l 0 + nth 1 l 0 :: nil) n)).
  inversion main as [v0 | x ys xnat ysnat vs].
    unfold fib; rewrite <- v0; simpl; typeclasses eauto.
  now unfold fib; rewrite <- vs; simpl.
apply private.Rnat_rec_nat.
    repeat constructor; typeclasses eauto.
  intros k l _ lnat.
  assert (Rnat (nth 0 l 0) /\ Rnat (nth 1 l 0)) as [nat_at_0 nat_at_1].
    inversion lnat as [v0 | x l' nx nl lq].
      now simpl; repeat constructor.
    inversion nl as [v1 | y l2 ny nl2 l'q].
      now simpl; repeat constructor.
    now simpl; repeat constructor.
  repeat constructor.
    easy.
  typeclasses eauto.
easy.
Qed.

Existing Instance fib_nat.

Derive f36 SuchThat (fib (fib 9 + 2) = f36) As Ex_f_9.
Proof.
assert (Rnat 9) by typeclasses eauto.
assert (Rnat (fib 9 + 2)) by typeclasses eauto.
repeat (rewrite <- plus_IZR || (rewrite fib_fibz; try typeclasses eauto)).
  unfold IRN; rewrite !IRZ_IZR.
  match goal with
  |- IZR ?v0 = _ =>
     let v := eval compute in v0 in change v0 with v
  end.
unfold f36.
reflexivity.
Qed.

(* Using Derive, we need an extra step to see the result. *)
Print f36.

Recursive (def trib such that trib 0 = 0 /\ trib 1 = 1 /\ trib 2 = 2 /\
  forall n, Rnat (n - 3) -> trib n = trib (n - 3) + trib (n - 2)).

Recursive (fun  test3 : R -> R => test3 0 = 0 /\ test3 1 = 1 /\
     forall n, Rnat (n - 2) ->
       test3 n = test3 (n - 2) + test3 (n - 1) + n).

Recursive (def fact3 such that fact3 0 = 1 /\
  forall n, Rnat (n - 1) -> fact3 n = n * fact3 (n - 1)).

Definition fact3z n :=
  nth 0 (nat_rect (fun _ => list Z) (1 :: nil)%Z
    (fun n l => ((1 + Z.of_nat n) * nth 0 l 0)%Z :: nil) n) 0%Z.

Lemma fact3_fact3z n : Rnat n ->
  fact3 n = IZR (fact3z (IRN n)).
Proof.
intros nnat.
unfold fact3, Rnat_rec, fact3z.
set (fr := nat_rect (fun _ => list R) _ _ _).
set (fz := nat_rect (fun _ => list Z) _ _ _).
enough (main : fr = map IZR fz).
  destruct fr as [ | r0 tl].
    destruct fz as [ | z0 tl]; try discriminate.
    easy.
  destruct fz as [ | z0 tlz]; try discriminate.
  now injection main as r0q _; rewrite r0q.
unfold fr, fz.
apply (private.nat_rect_list_IZR (1 :: nil)%Z).
intros k lR lZ lq.
destruct lR as [ | r0 tr].
  destruct lZ as [ | z0 tz]; try discriminate.
  cbn [map].
  rewrite mult_IZR.
  rewrite plus_IZR.
  rewrite INR_IZR_INZ.
  easy.
destruct lZ as [ | z0 tz]; try discriminate.
injection lq as r0q _; rewrite r0q.
cbn [nth map].
rewrite mult_IZR, plus_IZR.
rewrite INR_IZR_INZ.
easy.
Qed.

Derive fct15 SuchThat (fact3 15 = fct15) As fct15_eq.
Proof.
rewrite fact3_fact3z; try typeclasses eauto.
unfold IRN; rewrite IRZ_IZR.
match goal with
 |- IZR ?v0 = _ =>
   let v := eval compute in v0 in
     change v0 with v
end.
unfold fct15.
reflexivity.
Qed.

(* This example puts the user interface under stress, as it returns
  a tree of additions, where all the leaves are either 1 or (0 + 1).
  with the parentheses, this data should take at least 10 k chars. *)
Lemma fib11 : fib 11 = 89.
Proof.
unfold fib.
unfold Rnat_rec.
unfold IRN.
rewrite IRZ_IZR.
(* If the simpl command is placed alone in a command and its result
  should be improved, this breaks the outputting machinery of
  VsCoq2's current version.  Otherwise, just executing the combined
  simpl; ring command leads to a command that takes 3 seconds to
  execute. *)
simpl.
ring_simplify.
reflexivity.
Qed.
