From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import R_subsets.

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

pred translate i:term, o:term.

translate {{IZR lp:A}}  A :- !.

translate (app [Fr, A, B]) (app [Fz, A1, B1]) :-
  std.do! [
    translate A A1,
    translate B B1,
    compute_table Fr Fz
  ].

translate (app [Fr, A]) (app [Fz, A1]) :-
  std.do! [
    translate A A1,
    compute_table Fr Fz
  ].

translate (app [Fr | _]) _ :-
   coq.error "no correspondence for" {coq.term->string Fr}.

  main [trm E] :-
    std.do! [
      translate E E1,
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

pred translate_list i:list term o:list term.
pred translate i:term o:term.
pred start_translate i:term o:term.

start_translate 
  {{fun (x : R) => 
     nth 0 (Rnat_rec lp:L0 lp:F x) 0}}
  {{fun (x : Z) =>
     nth 0 (nat_rect (fun _ => list Z) lp:L1 lp:F1 (Z.abs_nat x)) 0%Z}}
        :-
  std.do! [
    translate L0 L1,
    translate F F1
  ].

translate (fun N {{R}} F) (fun N {{nat}} F1) :-
  (pi Cn \ 
    (translate Cn {{Z.of_nat lp:Cn}} =>
      translate (F Cn) (F1 Cn))).

translate (fun L {{list R}} F) (fun L {{list Z}} F1) :-
  (pi Cl\ 
    (translate Cl Cl =>
      translate (F Cl) (F1 Cl))).

translate {{nth lp:K lp:L 0}} {{nth lp:K lp:L1 0%Z}} :-
  translate L L1.

translate {{nil}} {{nil}}.

translate {{cons lp:A lp:L}} {{cons lp:A1 lp:L1}} :-
  std.do! [
    translate A A1,
    translate L L1
  ].

translate {{IZR lp:V}} V.

translate (app [F | L]) (app [F1 | L1]) :-
  std.do! [
    compute_table F F1,
    translate_list L L1
  ].

translate_list [] [].

translate_list [A | L] [A1 | L1] :-
  std.do! [
    translate A A1,
    translate_list L L1
  ].


translate A _ :-
  coq.error "unexpected term in translation" A.

% TODO: find the value of the name given in argument
% which should be of the form (nth 0 (@Rnat_rec (list R) L0 F) 0)
% replace all values in L0 by their corresponding integer values to obtain L1
% F should be of type R -> list R -> list R
% In the body of F n l, all occurences of R should be replace by Z
% all occurrences of n should be replaced by Z.of_nat n
% all occurrences of IZR z should be replaced by z
% all occurrences of functions should be replaced by their correspondence
% in compute_table (as in translate), to obtain F1
% A new function should be defined whose value should be
% (nth 0 (nat_rect (fun _ => list Z) L1 F1) 0%Z)
main [str F] :-
std.do! [
  std.assert! (coq.locate F (const FGR)) "the argument is not a known constant",
  std.assert! (coq.env.const-body FGR (some Bo)) "the constant does not have a value",
  std.assert! (start_translate Bo T1) "translation failed.  Possible causes are:\n
1/ the function was not generated by the command Recursive\n
2/ some function with not computational correspondence may be used\n
   (in that case, use add_computation or mirror_recursive_definition\n
    to provide missing information)",
  std.assert-ok! (coq.typecheck T1 Ty) "Anomaly: generating an ill-typed term",
  F_mirror is F ^ "_Z_mirror",
  coq.env.add-const F_mirror T1 Ty @transparent! C,
  coq.say "Defined" C,
  coq.elpi.accumulate _ "R_compute.db"
    (clause _ _ (compute_table (global (const FGR))
                   (global (const C))))
].

main L :-
  coq.error "Usage: Elpi mirror_recursive_definition Name.\n instead received: " L.
}}.

Elpi Typecheck.
