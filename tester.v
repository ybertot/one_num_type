From Stdlib Require Import Reals Lra.
Import Ring_polynom.
Open Scope R_scope.
Definition RField_lemma5 :=
  Field_theory.Field_rw_pow_correct_w_gcd (Eqsth R) (Eq_ext Rplus Rmult Ropp)
  (@f_equal _ _ Rinv) (F2AF (Eqsth R) (Eq_ext _ _ _) Rfield) R_rm R_power_theory
  get_signZ_th (Ztriv_div_th Rset IZR).

Ltac compute_gcd D N :=
  constr:(pair 1%Z (pair (PX (Pc 2) 1 (Pc 0))
    (pair (Pc 1) (PX (Pc 1) 1 (Pc 0))))%Z).


(* TODO: find how to reduce Pphi_pow without reducing IZR. *)
Ltac reduce_Pphi_pow :=
    cbv [Pphi_pow Pphi_avoid mult_dev Peq Z.eqb P0 mkmult_c
        mkmult_c_pos get_signZ Pos.eqb mkmult_rec List.rev' add_pow_list
        mkmult1 List.rev_append List.hd BinNat.N.add].

Ltac den_gcd_n0 :=
  split;[ apply Rmult_integral_contrapositive; split;
    [apply not_eq_sym, Rlt_not_eq, Rlt_0_2 | ]| ]; apply PI_neq0.

Ltac find_fraction dummy :=
  let t_eq := fresh "term_eq" in
  let hyp := fresh "rewrite_lemma" in
  intros t_eq hyp;
  match type of t_eq with
  | ?term = _ =>
    clear t_eq;
    match type of hyp with
    | forall _ _ _ _,
      gcd_cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?FV ?D _ ?N _ _ -> _
      =>
    let D1 := eval vm_compute in D in
    let N1 := eval vm_compute in N in
    let hyp_aux := fresh "gcd_cond_proof" in
    let fact_n0 := fresh "factor_not_0" in
    let num_eq := fresh "equality_for_numerator" in
    let den_eq := fresh "equality_for_denumerator" in
      match compute_gcd D1 N1 with
      | (pair ?F (pair ?D2 (pair ?N2 ?Gcd))) =>
        assert (fact_n0 : IZR F <> 0) by (apply eq_IZR_contrapositive; easy);
        enough (gcd_cond 0 1 Rplus Rmult Rminus Ropp eq 0%Z 1%Z Z.eqb IZR
          BinNat.N.to_nat
        pow get_signZ FV D D2 N N2 Gcd /\
          (Pmul 0%Z 1%Z Z.add Z.mul Z.eqb (Pc F) N =
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb N2 Gcd /\
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb (Pc F) D =
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb D2 Gcd)) as [hyp_aux [num_eq den_eq]];
        [
          generalize (hyp F N2 D2 Gcd hyp_aux fact_n0 num_eq den_eq);
          clear hyp_aux hyp fact_n0 num_eq den_eq;
          intros hyp;
          match type of hyp with
          | _ -> ?t = ?r =>
            change t with term in hyp;
            (rewrite hyp; clear hyp);
            [ unfold display_pow_linear; reduce_Pphi_pow|
             cbv [PCond condition PEeval BinList.nth BinNat.N.to_nat
                  List.hd PosDef.Pos.to_nat Init.Nat.add PosDef.Pos.iter_op]]
          end
        |
           split;[split;[intros [? [? ?]]; easy|
          reduce_Pphi_pow] |easy ]
        ]
      end
    end
  end.

Ltac fs5 := Field_simplify_gcd RField_lemma5 ltac:(find_fraction).

Ltac tester f := idtac; f.

Lemma toto : PI / (PI ^ 2 + PI ^ 2) = exp 1 / (exp 1 + exp 1).
field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2)).
