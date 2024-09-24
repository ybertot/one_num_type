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

Lemma abs_compute : forall x, Rabs (IZR x) = IZR (Z.abs x).
Proof.
exact (fun x => eq_sym (abs_IZR x)).
Qed.

Elpi Db R_translate.db lp:{{
pred translate_prf i:term, o:term, o:term.
pred main_translate_prf i:term, o:term, o:term.
pred translate_collect_prf i:term, o:term, o:term, o:list (pair int term).

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

translate_collect_prf {{IZR lp:A}} {{lp:A}} {{eq_refl: IZR lp:A = IZR lp:A}}
  [].

translate_prf (app [F, {{Rabs lp:A}}]) (app [F1, A1])
  {{lp:PFF1 lp:A lp:A1 lp:PRFA}} :-
  std.do![
    nat_thm_table F F1 PFF1,
    translate_prf A A1 PRFA
  ].

translate_collect_prf (app [F, {{Rabs lp:A}}]) (app [F1, A1])
  {{lp:PFF1 lp:A lp:A1 lp:PRFA}} L :-
  std.do![
    nat_thm_table F F1 PFF1,
    translate_collect_prf A A1 PRFA L
  ].

translate_prf {{lp:F (IZR (Zpos lp:P))}}
  {{lp:Fz (Zpos lp:P)}}
  {{private.cancel_Rabs_pos lp:F lp:Fz lp:Prf lp:P}} :-
  nat_thm_table F Fz Prf.

translate_collect_prf {{lp:F (IZR (Zpos lp:P))}}
  {{lp:Fz (Zpos lp:P)}}
  {{private.cancel_Rabs_pos lp:F lp:Fz lp:Prf lp:P}} [] :-
  nat_thm_table F Fz Prf.

translate_prf (app [F, {{lp:F (IZR 0%Z)}}])
  {{lp:Fz 0%Z}}
  {{private.cancel_Rabs_0 lp:F lp:Fz lp:Prf}} :-
  nat_thm_table F Fz Prf.

translate_collect_prf (app [F, {{lp:F (IZR 0%Z)}}])
  {{lp:Fz 0%Z}}
  {{private.cancel_Rabs_0 lp:F lp:Fz lp:Prf}} [] :-
  nat_thm_table F Fz Prf.

translate_prf (app [F, A]) (app [F1, A1])
  {{private.IZR_map1 lp:F lp:F1 lp:PFF1 lp:A lp:A1 lp:PFRA}} :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA
  ].

translate_collect_prf (app [F, A]) (app [F1, A1])
  {{private.IZR_map1 lp:F lp:F1 lp:PFF1 lp:A lp:A1 lp:PFRA}} L :-
  std.do! [
  thm_table F F1 PFF1,
  translate_collect_prf A A1 PFRA L
  ].

type marker int -> term.

translate_collect_prf (app [F, A]) (app [F1, A1])
  {{private.Rnat_Rabs lp:PFF1 lp:A lp:A1 lp:Nat_prf lp:PRFA}} L' :-
  std.do![
    nat_thm_table F F1 PFF1,
    translate_collect_prf A A1 PRFA L,
    coq.typecheck Hole {{Rnat lp:A}} ok,
    coq.ltac.collect-goals Hole [G] [],
    if (coq.ltac.open (coq.ltac.call-ltac1 "solve_Rnat") G [])
       (Nat_prf = Hole, L' = L)
       (
        Test = {{(0 <=? lp:A1)%Z}},
        coq.reduction.vm.norm Test _ Tv,
        if (Tv = {{false}})
          ( coq.reduction.vm.norm A1 _ V1,
            coq.term->string {{IZR lp:V1}} V1R,
            Diagnostic is
              {coq.term->string F} ^ " has a negative or undefined input "
              ^ V1R,
           coq.error Diagnostic)
          (GPRF = {{private.compute_Rnat lp:A lp:A1 lp:PRFA eq_refl}},
           Nat_prf = GPRF),
        L' = L)
        %new_int Fresh,
        % Nat_prf = marker Fresh,
        % L' = [pr Fresh {{Rnat lp:A}} | L])
  ].

translate_prf (app [F, A, B]) (app [F1, A1, B1])
  {{private.IZR_map2 lp:F lp:F1 lp:PFF1 lp:A lp:B lp:A1 lp:B1 lp:PFRA lp:PFRB}}
  :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA,
  translate_prf B B1 PFRB
  ].

translate_collect_prf (app [F, A, B]) (app [F1, A1, B1])
  {{private.IZR_map2 lp:F lp:F1 lp:PFF1 lp:A lp:B lp:A1 lp:B1 lp:PFRA lp:PFRB}}
     LPRF :-
  std.do! [
  thm_table F F1 PFF1,
  translate_collect_prf A A1 PFRA LA,
  translate_collect_prf B B1 PFRB LB,
  std.append LA LB LPRF
  ].

pred abstract_markers i:list (pair int term) i:term i:term
   i:term o:term o:term.

abstract_markers [] T LHS RHS T1 {{lp:LHS = lp:RHS :> R}} :-
  copy T T1.

abstract_markers [pr N Ty | L] T LHS RHS (fun _ Ty T1) {{lp:Ty -> lp:T1TY}}:-
  @pi-decl _ Ty x \
    (
    (copy (marker N) x :- !)
      =>
    abstract_markers L T LHS RHS (T1 x) T1TY).

}}.

Elpi Db R_compute.db lp:{{

pred compute_table o:term, o:term.

compute_table {{Rplus}} {{Z.add}}.

compute_table {{Rminus}} {{Z.sub}}.

compute_table {{Rmult}} {{Z.mul}}.

compute_table {{Ropp}} {{Z.opp}}.

compute_table {{Rpower}} {{Z.pow}}.

compute_table {{Rabs}} {{Z.abs}}.

pred thm_table o:term, o:term, o:term.

thm_table {{Rplus}} {{Z.add}} {{add_compute}}.

thm_table {{Rmult}} {{Z.mul}} {{mul_compute}}.

thm_table {{Rminus}} {{Z.sub}} {{sub_compute}}.

thm_table {{Ropp}} {{Z.opp}} {{opp_compute}}.

thm_table {{Rabs}} {{Z.abs}} {{abs_compute}}.
% arguments in a nat_thm_table relation are
% 1/ a function f from R -> R
% 2/ a function fz from Z -> Z
% 3/ a theorem f_prf with statement
%   forall x y, Rnat x -> x = IZR y -> f (Rabs x) = IZR (fz y)
%  This reflect that recursive definitions are mirrored
% by function that first perform a Z.abs_nat operation 
% to obtain the integer that will feed the recursive
% computation
% This table is used by R_compute, and its elements
% are produced by mirror_recursive_definition
pred nat_thm_table o:term, o:term, o:term.

}}.

Elpi Typecheck.

Elpi Command R_compute.

Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.

Elpi Accumulate lp:{{

  main [trm E] :-
    std.do! [
      translate_collect_prf E E1 _ OBLS,
      coq.reduction.vm.norm E1 _ E2,
      E3 = {{IZR lp:E2}},
      if (OBLS = [])
        (coq.say " =" {coq.term->string E3})
        (coq.say "(under some obligations) =" {coq.term->string E3})
    ].

main [trm E, str THM_name] :-
    std.do! [
      translate_collect_prf E E1 PRF OBLS,
      coq.reduction.vm.norm E1 _ E2,
      E3 = {{IZR lp:E2}},
      abstract_markers OBLS PRF E E3 PRF1 Stmt,
      coq.say " =" {coq.term->string E3},
      coq.typecheck PRF1 Stmt _,
      coq.env.add-const THM_name PRF1 Stmt @opaque! _
    ].

}}.

Elpi Typecheck.

Elpi Export R_compute.

Elpi Command add_computation.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate lp:{{

  main [str A, str B, str C] :-
    coq.locate A A1,
    coq.locate B B1,
    coq.locate C C1,
    coq.say "adding correspondence " {coq.term->string (global A1)}
      {coq.term->string (global B1)} "justified by" {coq.term->string (global C1)},
    coq.elpi.accumulate _ "R_compute.db"
     (clause _ _ (thm_table (global A1) (global B1) (global C1))).

  main L :-
    coq.error "Usage: Elpi add_computation Name1 Name2 Name3.\n instead received: " L.
}}.

Elpi Typecheck.

Elpi Export add_computation.

Elpi Command mirror_recursive_definition.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.

Elpi Accumulate lp:{{

pred translate_list_prf i:list term, o:list term, o:list term.
pred main_translate_prf1 i:term i:term o:term o:term o:term.

main_translate_prf1
  L F L1 F1
  {{fun N : R => fun z : Z =>
     private.nth_map 0%Z 0 IZR _ _ 0 eq_refl
     (private.nat_rect_list_IZR lp:L1 lp:L lp:F1 lp:F
       (Z.abs_nat z) eq_refl lp:FPRF)}} :-
    std.do! [
      translate_prf L L1 _,
      translate_prf F F1 FPRF
    ].

main_translate_prf
  {{fun (n : R) =>
      nth 0 (Rnat_rec lp:L lp:Frstep0 n) 0}}
  F Prf1 :-
  Frstep0 = (fun _ {{R}} Frstep),
  Fnstep = (fun _ {{nat}} c \ (Frstep {{INR lp:c}})),
  main_translate_prf1 L Fnstep Lz Fz Prf,
  F = {{fun (x : Z) =>
         nth 0 (nat_rect (fun _ => list Z) lp:Lz
           lp:Fz (Z.abs_nat x)) 0%Z}},
  std.assert-ok! (coq.typecheck F {{Z->Z}})
    "failed to typecheck mirror function",
  Prf1 = 
    {{fun (n : R) (z : Z) (nzq : n = IZR z) =>
       eq_ind_r
         (fun x : nat => 
           nth 0 (nat_rect _ lp:L lp:Fnstep x) 0 =
           IZR (nth 0 (nat_rect _ lp:Lz lp:Fz (Z.abs_nat z)) 0%Z))
        (lp:Prf n z
           (* (private.INR_Z_abs_nat _  _ nzq) *)
          )
          (private.IRN_Z_abs_nat _ _ nzq)}}.

main [str F] :-
std.do! [
  std.assert! (coq.locate F (const FGR))
    "the argument is not a known constant",
  std.assert! (coq.env.const-body FGR (some Bo)) 
    "the constant does not have a value",
  std.assert! (main_translate_prf Bo T1 Prf)
    "translation failed.  Possible causes are:\n
1/ the function was not generated by the command Recursive\n
2/ some function without computational correspondence may be used\n
   (in that case, use add_computation to provide missing information)\n
3/ you are using a function that is defined only on natural numbers\n
   but you are not encapsulating its argument in a Rabs call",
  std.assert-ok! (coq.typecheck T1 Ty)
     "Anomaly: generating an ill-typed term",
  F_mirror is F ^ "_Z_mirror",
  coq.env.add-const F_mirror T1 Ty @transparent! C,
  Fterm = global (const C),
  Stmt = {{forall n z, n = IZR z ->
         lp:{{(global (const FGR))}} (Rabs n) =
         IZR (lp:Fterm z)}},
  std.assert-ok! (coq.typecheck Prf Stmt)
         "Anomaly: generating an incorrect proof",
  F_prf is F ^ "_Z_prf",
  coq.env.add-const F_prf Prf Stmt @opaque! Cprf,
  coq.elpi.accumulate _ "R_compute.db"
    (clause _ _ (nat_thm_table (global (const FGR))
                   (global (const C))
                   (global (const Cprf))))                 
].

main L :-
  coq.error "Usage: Elpi mirror_recursive_definition Name.\n instead received: " L.
}}.

Elpi Typecheck.
Ltac r_compute_rewrite P := rewrite P.

Elpi Tactic r_compute.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [trm X] as G) GL :-
  std.do! [
  translate_collect_prf X V PRF OBLS,
  coq.reduction.vm.norm V _ E2,
  E3 = {{IZR lp:E2}},
  abstract_markers OBLS PRF X E3 PRF1 Stmt,
  coq.say "stmt :" {coq.term->string Stmt},
  coq.typecheck PRF1 Stmt ok,
  coq.ltac.call "r_compute_rewrite"
    [trm {{lp:PRF1 : lp:Stmt}}] G GL
  ].

solve A B :-
  coq.say "wrong" A B.
}}.

Elpi Typecheck.

(* The following experiment prefigures what can be done
   so that R_compute returns not only the value but also
   the proof that this value is correct.

Recursive (def fib such that
  (fib 0 = 0 /\ fib 1 = 1 /\
   (forall n, Rnat (n - 2) ->
     fib n = fib (n - 2) + fib (n - 1)))).

Elpi Query lp:{{
  sigma CF CM GP F0 Stmt P P' F1 PRF CP L\
  (
  main [str "fib"],!,
  coq.locate "fib" CF,
  coq.locate "fib_Z_mirror" CM,
  coq.locate "fib_Z_prf" CP,
  nat_thm_table (global CF) (global CM) (global CP) =>
    (F0 = {{fib (fib 3 + fib 4)}}, !,
     translate_collect_prf F0 F1 P L,
     coq.reduction.vm.norm F1 _ V,
     abstract_markers L P P',!,
     coq.typecheck P' Stmt Diag,
     coq.say "thm" {coq.term->string Stmt}
    )
  )
}}.

Lemma fib_nat n : Rnat n -> Rnat (fib n).
Proof.
rec_Rnat fib.
Qed.

Existing Instance fib_nat.

Elpi Query lp:{{
  sigma CF CM GP F0 Stmt P P' F1 PRF CP L\
  (
  coq.locate "fib" CF,
  coq.locate "fib_Z_mirror" CM,
  coq.locate "fib_Z_prf" CP,
  nat_thm_table (global CF) (global CM) (global CP) =>
    (F0 = {{fib (fib 3 + fib 4)}}, !,
     translate_collect_prf F0 F1 P L,
     coq.reduction.vm.norm F1 _ V,
     abstract_markers L P P',!,
     coq.typecheck P' Stmt Diag,
     coq.say "thm" {coq.term->string Stmt}
    )
  )
}}.
*)
(*
Recursive (def fib such that
  (fib 0 = 0 /\ fib 1 = 1 /\
   (forall n, Rnat (n - 2) ->
     fib n = fib (n - 2) + fib (n - 1)))).

Recursive (def monster such that 
  monster 0 = 1 /\
  forall n, Rnat (n - 1) -> monster n = fib (Rabs (monster (n - 1) + 2))).

Elpi Query lp:{{ main [str "fib"] }}.
Elpi Query lp:{{ main [str "monster"]}}.

Elpi R_compute (fib 6).
Elpi R_compute (monster (Rabs (fib 5 + 1))).
*)