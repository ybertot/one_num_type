Require Import List FunctionalExtensionality Lra.
From elpi Require Import elpi.

Require Import Reals.
From OneNum Require Import R_subsets.

Open Scope R_scope.

Lemma let_congr {T1 T2 : Type} (b1 b2 : T1) (F1 F2 : T1 -> T2) :
  b1 = b2 -> (forall x : T1, F1 x = F2 x) ->
  (let x := b1 in F1 x) = (let x := b2 in F2 x).
Proof.
intros bq fq; rewrite bq.
lazy zeta; apply fq.
Qed.

Lemma big_ext_low_nat3 {A : Type} op (v : A) f g b1 b2 n1 n2 :
  (forall x, Rnat x -> b1 <= x < n1 -> f x = g x) ->
  Rnat b1 ->
  Rnat (n1 - b1) ->
  b1 = b2 ->
  n1 = n2 ->
  \big[op/v]_(b1 <= i < n1) f i = \big[op/v]_(b2 <= i < n2) g i.
Proof.
intros b1nat n1nat ext_hyp bq nq.
rewrite <- bq, <- nq.
now apply big_ext_low_nat.
Qed.

Lemma map_ext_in_equal2 [A B : Type] (f g : A -> B) (l1 l2 : list A):
  (forall a : A, In a l1 -> f a = g a) -> l1 = l2 ->
  map f l1 = map g l2.
Proof.
now intros exth l1l2; rewrite <- l1l2; apply map_ext_in.
Qed.

Lemma app_prf [A B : Type] (f g : A -> B) (v1 v2 : A) :
  f = g -> v1 = v2 -> f v1 = g v2.
Proof. now intros fg v1v2; rewrite fg, v1v2. Qed.

Lemma app_prf1 [A : Type] [B : A -> Type] (f g : forall x, B x) (v : A) :
  f = g -> f v = g v.
Proof. now intros fg; rewrite fg. Qed.

Ltac lazy_beta := lazy beta.

Lemma eq_trans_rev {A : Type} (x y z : A) :
  y = z -> x = y -> x = z.
Proof. exact (fun h1 h2 => @eq_trans A x y z h2 h1). Qed.

Elpi Tactic replace.


Elpi Accumulate lp:{{

pred preserve_bound_variables i:term o:term.

preserve_bound_variables I O :-
  (((pi N T F N1 T1 F1 \
    copy (fun N T F) (fun N1 T1 F1) :-
    copy T T1,
    fresh-name N T N1,
    (@pi-decl N1 T1 x\
      copy (F x) (F1 x))),
    (pi B B1 N T F N1 T1 F1 \
      copy (let N T B F)(let N1 T1 B1 F1) :-
        copy T T1,
        copy B B1,
        fresh-name N T N1,
        (@pi-decl N1 T1 x\ copy (F x) (F1 x))),
    (pi N T F N1 T1 F1 \
      copy (prod N T F) (prod N1 T1 F1) :-
        copy T T1,
        fresh-name N T N1,
        (@pi-decl N1 T1 x\
          copy (F x) (F1 x)))) => copy I O).

pred fresh-name i:name, i:term, o:name.

fresh-name N T M :-
  coq.ltac.fresh-id {coq.name->id N} T Mi,
  coq.id->name Mi M.

pred mk-app-prf i:list term, i:list term, i: list term, o:term.

mk-app-prf [F, _] [F, _] [{{@refl_equal _ _}}, P] {{f_equal lp:F lp:P}} :-
  non-dependent-type F,!.
mk-app-prf [F, _, _] [F, _, _] [{{@refl_equal _ _}}, P1, P2]
  {{f_equal2 lp:F lp:P1 lp:P2}} :-
  non-dependent-type F,!.
mk-app-prf [F, _, _, _] [F, _, _, _] [{{@refl_equal _ _}}, P1, P2, P3]
  {{f_equal3 lp:F lp:P1 lp:P2 lp:P3}} :-
  non-dependent-type F,!.
mk-app-prf [F, _, _, _, _] [F, _, _, _, _]
  [{{@refl_equal _ _}}, P1, P2, P3, P4]
  {{f_equal4 lp:F lp:P1 lp:P2 lp:P3 lp:P4}} :-
  non-dependent-type F,!.
% TODO use nary_congruence from ssreflect
mk-app-prf [F, _, _, _, _, _] [F, _, _, _, _, _]
  [{{@refl_equal _ _}}, P1, P2, P3, P4, P5]
  {{f_equal5 lp:F lp:P1 lp:P2 lp:P3 lp:P4 lp:P5}} :-
  non-dependent-type F,!.
mk-app-prf [F1, A] [F2, A] [Pf, {{@refl_equal _ _}}]
   {{app_prf1 lp:F1 lp:F2 lp:A lp:Pf}} :- !.
mk-app-prf [F1, A] [F2, B] [Pf, Pa]
  {{app_prf lp:F1 lp:F2 lp:A lp:B lp:Pf lp:Pa}} :-
  coq.typecheck F1 (prod _ _ Ft) ok,
  (pi c1 c2 \ Ft c1 = Ft c2),!.
 mk-app-prf [F1, A | Args1] [F2, A |Args2] [Pf, {{@refl_equal _ _}} | Ps]
   P :- !,
    mk-app-prf [app [F1, A] | Args1] [app [F2, A] | Args2]
      [{{app_prf1 lp:F1 lp:F2 lp:A lp:Pf}} | Ps] P.

mk-app-prf [F1, A | Args1] [F2, B | Args2] [Pf, Pa | Ps] P :-
  coq.typecheck F1 (prod _ _ Ft) ok,
  (pi c1 c2 \ Ft c1 = Ft c2),!,
  mk-app-prf [app [F1, A] | Args1] [app [F2, B] | Args2]
    [{{app_prf lp:F1 lp:F2 lp:A lp:B lp:Pf lp:Pa}} | Ps] P.

pred fold-map2 i:list term i:A i:(term -> A -> term -> term -> A -> prop)
  o:list term o:list term o:A.

fold-map2 [] A _ [] [] A.
fold-map2 [T | L] A F [T1 | L1] [P1 | PL] A2 :-
  F T A T1 P1 A1, fold-map2 L A1 F L1 PL A2.

pred instantiate_pair i:name, i:term, i:term, i:pair argument argument,
    o:pair argument argument.

pred instantiate i:name, i:term, i:term, i:argument, o:argument.

pred remove_one_unknown i:name, i:term, i:term, i:term, o:term.

% TODO : needs a fix in a rocq-elpi to detect if renaming has happened in
% in the current context.
remove_one_unknown N _T C (fun N1 _T1 F) Res :-
  {coq.name->id N} = {coq.name->id N1},!,
  Res = (F C),!.

 remove_one_unknown N T C (fun N1 T1 F) (fun N1 T1 Res) :-
  (@pi-decl N1 T1 x \
     remove_one_unknown N T C (F x) (Res x)),!.

instantiate N T C (open-trm 1 F) (open-trm 0 Res) :-
  remove_one_unknown N T C F Res,!.

instantiate N T C (open-trm I F) (open-trm J Res) :-
  remove_one_unknown N T C F Res,!,
  J is I - 1.

instantiate _N _T _C (open-trm 0 A) (open-trm 0 A):- !.

instantiate _N _T _C (open-trm _ _ as It) It :- !.

instantiate_pair N T C (pr A1 A2) (pr B1 B2) :-
  std.do! [
  std.assert! (instantiate N T C A1 B1) "first instantiate failed",
  instantiate N T C A2 B2].

pred mk-equality i:(pair argument argument), i:term i:A, o:term, o:term, o:A.

mk-equality (pr (open-trm 0 S) (open-trm 0 T)) S A T P A :- !,
  TY = {{lp:S = lp:T}},
  coq.typecheck-ty TY _ ok,
  coq.typecheck P TY ok.

:name "mk-equality:start"
mk-equality _RW X A Z Y A :- name X,!,
X = Z, {{@refl_equal _ lp:X}} = Y, !.

mk-equality _RW (global _ as C) A C {{@refl_equal _ lp:C}} A :- !.

mk-equality _RW (pglobal _ _ as C) A C {{@refl_equal _ lp:C}} A :- !.

mk-equality _RW (sort _ as C) A C {{@refl_equal _ lp:C}} A :- !.

mk-equality RW (fun N T F) A (fun N1 T F) Res A :-
fresh-name N T N1,
@pi-decl N T x\
  (instantiate_pair N T x RW (RW1 x),
   mk-equality (RW1 x) (F x) A _ {{@refl_equal _ _}} _A2,!,
   Res = {{@refl_equal _ _}}).

mk-equality RW (fun N T F) A (fun N1 T F1)
  {{functional_extensionality lp:{{(fun N T F)}} lp:{{(fun N T F1)}}
      lp:{{(fun N1 T Prf)}}}} A1 :- !,
fresh-name N T N1,
@pi-decl N1 T x\
  (std.assert! (instantiate_pair N1 T x RW (RW1 x)) "instantiate_pair failed",!,
   mk-equality (RW1 x) (F x) A (F1 x) (Prf x) A1).

% TODO: write unit tests for the following clauses
mk-equality RW (let N T B F as C) A (let N1 T B F) {{@refl_equal _ lp:C}} A :-
mk-equality RW B A _ {{@refl_equal _ _}} A2,
fresh-name N T N1,
(@pi-decl N1 T x\
  (std.assert! (instantiate_pair N1 T x RW (RW1 x)) "instantiate_pair failed",!,
  mk-equality (RW1 x) (F x) A2 _ {{@refl_equal _ _}} _A3)),!.

mk-equality RW (let N T B F) A (let N1 T B1 F1)
  {{let_congr lp:B lp:B1 lp:{{fun N1 T F}} lp:{{fun N1 T F1}}
      lp:PB lp:PF}} A3:- !,
fresh-name N T N1,
mk-equality RW B A B1 PB A2,
@pi-decl N1 T x\
  (instantiate_pair N1 T x RW (RW1 x),!,
   mk-equality (RW1 x) (F x) A2 (F1 x) PF A3).

mk-equality RW (prod N T F) A (prod N1 T F1) (fun N1 T P1) A2 :- !,
fresh-name N T N1,
(@pi-decl N1 T x\
  (instantiate_pair N1 T x RW (RW1 x),!,
   mk-equality  (RW1 x) (F x) A (F1 x) (P1 x) A2)),!.

mk-equality RW (app L as C) A C {{@refl_equal _ lp:C}} A :-
fold-map2 L A (mk-equality RW) _ L1 _A1,
std.forall L1 (c \ (sigma A B \ c = {{@refl_equal lp:A lp:B}})),!.

mk-equality RW {{@map lp:T1 lp:T2 lp:{{fun N _ F}} lp:L}}
  A
  {{@map lp:T1 lp:T2 lp:{{fun N1 T1 F1}} lp:L1}}
  R A2 :- !,
  fresh-name N T1 N1,
  @pi-decl N1 T1 x\
  (instantiate_pair N1 T1 x RW (RW1 x),!,
    @pi-decl `H` (Ext_Hyp x) h\
      mk-equality (RW1 x) (F x) A (F1 x) (Pf x h) A1),
  mk-equality RW L A1 L1 Pl A2,
  R = {{map_ext_in_equal2 lp:{{fun N1 _ F}} lp:{{fun N1 _ F1}} lp:L lp:L1
         lp:{{fun N1 T1 x\
              (fun `H` (Ext_Hyp x) h\ Pf x h)}} lp:Pl }}.

mk-equality RW {{@Rbigop lp:Ty lp:Op lp:E lp:B1 lp:B2 lp:{{fun N _ F}}}}
  A
  {{@Rbigop lp:Ty lp:Op lp:E lp:B3 lp:B4 lp:{{fun N1 {{R}} F1}}}}
  R A3 :- !,
  fresh-name N T1 N1,
  @pi-decl N1 T1 x\
    (instantiate_pair N1 T1 x RW (RW1 x),!,
     @pi-decl `Hnat` (Hnat x) hn\
     @pi-decl `H` (Ext_Hyp x) h\
      mk-equality (RW1 x) (F x) A (F1 x) (Pf x hn h) A1),
  mk-equality RW B1 A1 B3 Pb1 A2,
  mk-equality RW B2 A2 B4 Pb2 A3,
  R = {{big_ext_low_nat3 lp:Op lp:E
        lp:{{fun N1 _ F}} lp:{{fun N1 _ F1}} lp:B1 lp:B3 lp:B2 lp:B4
        lp:{{fun N1 T1 x\
             (fun `Hnat` (Hnat x) hn\
               (fun `H` (Ext_Hyp x) h\ Pf x hn h))}}
        lp:P1_ lp:P2_ lp:Pb1 lp:Pb2}}.


mk-equality RW (app L) A (app L1) Prf A1 :-
  fold-map2 L A (mk-equality RW) L1 P1 A1,
  mk-app-prf L L1 P1 Prf.

pred non-dependent-type  i:term.

non-dependent-type F :-
  coq.typecheck F Ty ok,
  ndpt Ty.

pred ndpt i:term.

ndpt (prod _N _T F) :-
  pi c1 c2\ F c1  = F c2,!,
  pi c\ ndpt (F c).

ndpt (prod _ _ _) :- !, fail.

ndpt _ :- !.


pred equal-app i:list term, i:list term, i:list term, o:term.

equal-app  [F, A] [F1, A1] [Pf, Pa]
  {{app_prf lp:F lp:F1 lp:A lp:A1 lp:Pf lp:Pa}} :- !.

equal-app [F, A | Args] [F1, A1 | Args1] [Pf, Pa | Ps]
    R :-
  equal-app [app [F, A] | Args] [app [F1, A1] | Args1]
    [{{app_prf lp:F lp:F1 lp:A lp:A1 lp:Pf lp:Pa}} | Ps] R.

mk-equality _RW (fix _N _Rno _Ty _F as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _RW (match _T _Rty _B as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _RW (primitive _ as C) A C {{@refl_equal _ lp:C}} A :- !.
mk-equality _RW (uvar _M _L as C) A C {{@refl_equal _ lp:C}} A :- !.
% when used in CHR rules
mk-equality _RW (uvar _X _L as C) A C {{@refl_equal _ lp:C}} A :- !.

pred display-open i:int i:term o:string.

display-open 0 T S :-
  coq.term->string T S.

display-open N (fun Name Ty Bo) S :-
  N1 is N - 1,
  @pi-decl Name Ty x \ display-open N1 (Bo x) S.

pred argument->string i:argument o:string.

argument->string (open-trm N F) S :-
  display-open N F S.

solve (goal _ _ {{lp:X = lp:Y }} _ [Arg1, Arg2] as G) GL1 :-
  mk-equality (pr Arg1 Arg2) Y [] Y2 P1 _,
  if (Y == Y2) (
    coq.say "attempting left hand side",
    mk-equality (pr Arg1 Arg2) X [] X2 P _,
    coq.say "equality succeeded",
    if (X == X2) (
      coq.error "tactic repl: the pattern" {argument->string Arg1}
        "does not occur in the goal")
      (std.assert-ok! (coq.typecheck P {{lp:X = lp:X2}}) "proof incorrect",!,
       preserve_bound_variables Y Y1,
       refine {{@eq_trans_rev _ _ lp:X2 lp:Y1 _ lp:P}} G GL))
    (std.assert-ok! (coq.typecheck P1 {{lp:Y = lp:Y2}}) "proof incorrect",!,
     preserve_bound_variables X X1,
     refine {{@eq_trans _ lp:X1 lp:Y2 _ _ (eq_sym lp:P1)}} G GL),
  if (GL = [Ng, Ng2 | Extras])
    (coq.ltac.open (coq.ltac.call "lazy_beta" []) Ng2 [GL_aux],
     GL1 = [Ng, GL_aux | Extras])
    (GL1 = GL).

solve (goal _ _ _ _ [Arg1, Arg2]) _ :-
  coq.say Arg1,
  coq.say Arg2,
  fail.

solve (goal _ _ _ _ [] as _G) _GL :-
  coq.say "failed".
}}.

Tactic Notation (at level 0) "repl" uconstr(x) uconstr(y) :=
  (elpi replace ltac_open_term:(x) ltac_open_term:(y)).

Section demo_zone.

Lemma test1 :   \sum_(0 <= i < 10) (i + 1) =
  \sum_(0 <= i < 10) (sqrt (i ^ 2) + 1).
Proof.
repl (sqrt (i ^ 2)) i.
  easy.
rewrite sqrt_pow_2.
    easy.
  lra.
solve_Rnat.
Qed.

Lemma test2 : \sum_(0 <= i < 10) (sqrt (i ^ 2) + 1) = \sum_(0 <= i < 10) (1 + i).
Proof.
repl (sqrt (i ^ 2)) (i).
    repl (1 + i) (i + 1).
        easy.
      ring.
    solve_Rnat.
  rewrite sqrt_pow_2.
    easy.
  lra.
solve_Rnat.
Qed.

Lemma test_as_before :
  \sum_(0 <= i < 10) i = \sum_(0 <= i < 10) (sqrt (i ^ 2)).
Proof.
apply big_ext_low_nat.
    solve_Rnat.
  solve_Rnat.
intros x Hnat H.
rewrite sqrt_pow_2.
  easy.
lra.
Qed.

End demo_zone.
