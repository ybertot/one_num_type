From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import R_subsets rec_def.

Open Scope R_scope.

Lemma add_compute : forall x y, Rplus (IZR x) (IZR y) = IZR (Z.add x y).
Proof.
exact (fun x y => eq_sym (plus_IZR x y)).
Qed.

Lemma mul_compute : forall x y, Rmult (IZR x) (IZR y) = IZR (Z.mul x y).
Proof.
exact (fun x y => eq_sym (mult_IZR x y)).
Qed.

Lemma sub_compute : forall x y, Rminus (IZR x) (IZR y) = IZR (Z.sub x y).
Proof.
exact (fun x y => eq_sym (minus_IZR x y)).
Qed.

Lemma opp_compute : forall x, Ropp (IZR x) = IZR (Z.opp x).
Proof.
exact (fun x => eq_sym (opp_IZR x)).
Qed.

Elpi Db R_compute.db lp:{{

pred compute_table o:term, o:term.

compute_table {{Rplus}} {{Z.add}}.

compute_table {{Rminus}} {{Z.sub}}.

compute_table {{Rmult}} {{Z.mul}}.

compute_table {{Ropp}} {{Z.opp}}.

compute_table {{Rpower}} {{Z.pow}}.

pred thm_table o:term, o:term, o:term.

thm_table {{Rplus}} {{Z.add}} {{add_compute}}.

thm_table {{Rmult}} {{Z.mul}} {{mul_compute}}.

thm_table {{Rminus}} {{Z.sub}} {{sub_compute}}.

thm_table {{Ropp}} {{Z.opp}} {{opp_compute}}.

pred nat_thm_table o:term, o:term, o:term.

}}.

Elpi Typecheck.

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

pred translate_list_prf i:list term, o:list term, o:list term.
pred translate_prf i:term, o:term, o:term.
pred param_translate_prf i:term, i:term, i:term, o:term, o:term.
pred main_translate_prf i:term, o:term, o:term.

translate_prf (fun N {{nat}} F) (fun N {{nat}} F1) 
  (fun N {{nat}} PF) :-
  (pi CN \
    translate_prf {{INR lp:CN}} {{Z.of_nat lp:CN}} {{INR_IZR_INZ lp:CN}} =>
    translate_prf (F CN) (F1 CN) (PF CN)).

translate_prf (fun L {{list R}} F) (fun L {{list Z}} F1)
  PF0 :-
  (pi Cl1 Cl2 Hll \
    translate_prf Cl1 Cl2 Hll =>
    translate_prf (F Cl1) (F1 Cl2) (PF Cl1 Cl2 Hll)),
    PF0 = {{fun (lr : list R) (lz : list Z)
      (h : lr = @map Z R IZR lz :> list R) => lp:(PF lr lz h)}}.

translate_prf {{nth lp:K lp:L 0}} {{nth lp:K lp:Lz 0%Z}}
  {{private.nth_map 0%Z 0 IZR lp:Lz lp:L lp:K eq_refl lp:H}} :-
  translate_prf L Lz H.

translate_prf {{@nil R}} {{@nil Z}} {{eq_refl : nil = @map Z R IZR nil}}.

translate_prf {{cons lp:A lp:L}} {{cons lp:A1 lp:L1}} 
  {{f_equal2 (@cons R) lp:Pfa lp:Pfl}}:-
  std.do! [
    translate_prf A A1 Pfa,
    translate_prf L L1 Pfl
  ].

translate_prf {{IZR lp:A}} {{lp:A}} {{eq_refl: IZR lp:A = IZR lp:A}}.

translate_prf (app [F, A]) (app [F1, A1]) 
  {{private.IZR_map1 lp:F lp:F1 lp:PFF1 lp:A lp:A1 lp:PFRA}} :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA
  ].

translate_prf (app [F, A, B]) (app [F1, A1, B1]) 
  {{private.IZR_map2 lp:F lp:F1 lp:PFF1 lp:A lp:B lp:A1 lp:B1 lp:PFRA lp:PFRB}} :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA,
  translate_prf B B1 PFRB
  ].

main_translate_prf
  {{fun (x : Z) => 
    nth 0 (nat_rect (fun _ => list R) lp:L lp:F (Z.abs_nat x)) 0}}
  {{fun (x : Z) => 
    nth 0 (nat_rect (fun _ => list Z) lp:L1 lp:F1 (Z.abs_nat x)) 0%Z}}
  {{fun N : R => fun K : nat => fun Hnk : N = INR K =>
     private.nth_map 0%Z 0 IZR _ _ 0 eq_refl
      (private.nat_rect_list_IZR lp:L1 lp:L lp:F1 lp:F K eq_refl lp:FPRF)}} :-
  std.do! [translate L L1,
  translate_prf F F1 FPRF].

main_translate_prf
  {{fun (n : R) =>
      nth 0 (Rnat_rec lp:L lp:Frstep0 n) 0}}
  F Prf1 :-
  Frstep0 = (fun _ {{R}} Frstep),
  Fnstep = (fun _ {{nat}} c \ (Frstep {{INR lp:c}})),
  MainF = {{fun (x : Z) =>
         nth 0 (nat_rect (fun _ => list R) lp:L
           lp:Fnstep (Z.abs_nat x)) 0}},
% It is not sure the that the next step is necessary
% It was useful as a debugging prop
  std.assert-ok! (coq.typecheck MainF
     _) "failed to typecheck step func",
  main_translate_prf MainF F Prf,
  F = (fun _ _ Zbo),
  (sigma c \ Zbo c = {{nth _ (nat_rect _ lp:Lz lp:Fz _) _}}),
  Prf1 = 
    {{fun (n : R) (z : Z) (nnat : Rnat n) (nzq : n = IZR z) =>
       eq_ind_r
         (fun x : nat => 
           nth 0 (nat_rect _ lp:L (fun m => lp:Frstep0 (INR m)) x) 0 =
           IZR (nth 0 (nat_rect _ lp:Lz lp:Fz (Z.abs_nat z)) 0%Z))
        (lp:Prf n (Z.abs_nat z)
          (private.INR_Z_abs_nat _  _ nnat nzq))
          (private.IRN_Z_abs_nat _ _ nzq)}}.


pred translate_list i:list term, o:list term.
pred translate i:term, o:term.
pred main_translate i:term, o:term.

main_translate 
  {{fun (x : R) => 
     nth 0 (Rnat_rec lp:L0 lp:F x) 0}}
  {{fun (x : Z) =>
     nth 0 (nat_rect (fun _ => list Z) lp:L1 lp:F1 (Z.abs_nat x)) 0%Z}}
        :-
  std.do! [
    translate L0 L1,
    translate F F1
  ].

% TODO : add a clause for non recursive definitions, where the body
% is simply treated using the translate predicate.
% but mirror_recursive_definition would be a bad name for the command

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

main [str F] :-
std.do! [
  std.assert! (coq.locate F (const FGR)) "the argument is not a known constant",
  std.assert! (coq.env.const-body FGR (some Bo)) "the constant does not have a value",
  std.assert! (main_translate Bo T1) "translation failed.  Possible causes are:\n
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

Recursive (def fib such that fib 0 = 0 /\ fib 1 = 1 /\
    forall n : R, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)).

Elpi Query lp:{{
  sigma FGR Bo T1 Prf Stmt Fz Cf C\
  (std.assert! (coq.locate "fib" (const FGR)) "could not find fib",
  std.assert! (coq.env.const-body FGR (some Bo)) "could not find the value of fib",
  std.assert! (main_translate_prf Bo T1 Prf) "could not perform translation with proof",
  std.assert-ok! (coq.typecheck T1 {{Z -> Z}}) "The result Z function is incorrect",
  std.assert! (coq.env.add-const "fib_Z_mirror" T1 {{Z -> Z}} @transparent! Cf) 
                "adding the definition failed",
  Fz = global (const Cf),
  Stmt = {{forall n z, Rnat n -> n = IZR z ->
              fib n = IZR (lp:Fz z)}},
  std.assert-ok! (coq.typecheck Prf Stmt) "failed to typecheck the proof",
  std.assert! (coq.env.add-const "fib_Z_proof" Prf Stmt @opaque! C)
       "failed to define fib_Z_proof"),
  coq.elpi.accumulate _ "R_compute.db"
    (clause _ _ (nat_thm_table (global (const FGR))
                 (global (const Cf)) (global (const C))))
}}.

Elpi Query lp:{{
  coq.locate "fib" D,
  nat_thm_table (global D) B C
}}.

Check fib_Z_mirror.
Check fib_Z_proof.
