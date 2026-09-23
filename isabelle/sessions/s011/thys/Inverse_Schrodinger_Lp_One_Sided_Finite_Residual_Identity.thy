theory Inverse_Schrodinger_Lp_One_Sided_Finite_Residual_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Residual_Decay"
begin

section \<open>The finite residual in manuscript list coordinates\<close>

lemma slp_point_quadratic_value_as_complex_square:
  "slp_point_quadratic_value z = Re ((slp_point_as_complex z) ^ 2)"
  unfolding slp_point_quadratic_value_def slp_point_as_complex_def
  by (simp only: Re_power2 complex.sel)

lemma slp_finite_branch_pair_quadratic_summand:
  fixes pos neg :: "slp_point^'i::finite"
  shows
    "(\<lambda>pair. slp_point_quadratic_value (fst pair) -
        slp_point_quadratic_value (snd pair)) \<circ>
        (\<lambda>k. (pos $ from_nat_into UNIV k,
          neg $ from_nat_into UNIV k)) =
      (\<lambda>k. slp_point_quadratic_value
          (pos $ from_nat_into UNIV k) -
        slp_point_quadratic_value (neg $ from_nat_into UNIV k))"
  by (rule ext)
    (simp only: comp_apply fst_conv snd_conv)

lemma slp_finite_branch_pair_list_quadratic_sum:
  fixes pos neg :: "slp_point^'i::finite"
  shows
    "sum_list (map (\<lambda>pair.
        slp_point_quadratic_value (fst pair) -
          slp_point_quadratic_value (snd pair))
      (slp_finite_branch_pair_list
        (\<lambda>i. pos $ i) (\<lambda>i. neg $ i))) =
      (\<Sum>i\<in>UNIV. slp_point_quadratic_value (pos $ i) -
        slp_point_quadratic_value (neg $ i))"
  unfolding slp_finite_branch_pair_list_def
  apply (simp only: map_map interv_sum_list_conv_sum_set_nat set_upt
      atLeast0LessThan)
  apply (subst slp_finite_branch_pair_quadratic_summand)
  apply (subst sum.card_from_nat_into[
        where A = "UNIV :: 'i set"
          and h = "\<lambda>i. slp_point_quadratic_value (pos $ i) -
            slp_point_quadratic_value (neg $ i)"])
  by (simp only: card_UNIV)

theorem slp_one_sided_finite_residual_eq_left_branch:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_one_sided_finite_residual coordinates =
      slp_left_branch_residual
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
proof -
  let ?pos = "fst (fst (snd coordinates))"
  let ?neg = "snd (fst (snd coordinates))"
  let ?terminal = "snd (snd coordinates)"
  have finite_formula:
      "slp_one_sided_finite_residual coordinates =
        Re ((\<Sum>i\<in>UNIV. (slp_point_as_complex (?pos $ i)) ^ 2) -
          (\<Sum>i\<in>UNIV. (slp_point_as_complex (?neg $ i)) ^ 2) +
          (slp_point_as_complex ?terminal) ^ 2 -
          (slp_point_as_complex ?terminal +
            (\<Sum>i\<in>UNIV. slp_point_as_complex (?pos $ i) -
              slp_point_as_complex (?neg $ i))) ^ 2)"
    unfolding slp_one_sided_finite_residual_def
      slp_one_sided_packed_residual_def
      slp_one_sided_finite_to_packed_coordinates_def Let_def
    by (simp only: fst_conv snd_conv slp_complex_family_unpack_pack sum.case)
  have quadratic_sum:
      "sum_list (map (\<lambda>pair.
          slp_point_quadratic_value (fst pair) -
            slp_point_quadratic_value (snd pair))
        (slp_finite_branch_pair_list
          (\<lambda>i. ?pos $ i) (\<lambda>i. ?neg $ i))) =
        (\<Sum>i\<in>UNIV. slp_point_quadratic_value (?pos $ i) -
          slp_point_quadratic_value (?neg $ i))"
    by (rule slp_finite_branch_pair_list_quadratic_sum)
  have output_complex:
      "slp_point_as_complex
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. ?pos $ i) (\<lambda>i. ?neg $ i)) ?terminal) =
        slp_point_as_complex ?terminal +
          (\<Sum>i\<in>UNIV. slp_point_as_complex (?pos $ i) -
            slp_point_as_complex (?neg $ i))"
    by (rule slp_finite_branch_pair_list_output_as_complex)
  have list_formula:
      "slp_left_branch_residual
          (slp_finite_branch_pair_list
            (\<lambda>i. ?pos $ i) (\<lambda>i. ?neg $ i)) ?terminal =
        Re ((\<Sum>i\<in>UNIV. (slp_point_as_complex (?pos $ i)) ^ 2) -
          (\<Sum>i\<in>UNIV. (slp_point_as_complex (?neg $ i)) ^ 2) +
          (slp_point_as_complex ?terminal) ^ 2 -
          (slp_point_as_complex ?terminal +
            (\<Sum>i\<in>UNIV. slp_point_as_complex (?pos $ i) -
              slp_point_as_complex (?neg $ i))) ^ 2)"
    unfolding slp_left_branch_residual_def slp_branch_residual_def
    using quadratic_sum output_complex
    by (simp only: slp_point_quadratic_value_as_complex_square
        Re_sum minus_complex.sel plus_complex.sel sum_subtractf)
  show ?thesis
    by (rule HOL.trans[OF finite_formula list_formula[symmetric]])
qed

end
