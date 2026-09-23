theory Inverse_Schrodinger_Lp_Mixed_Branch_Finite_Signed_Residual
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Signed_Normal_Form"
begin

section \<open>Finite mixed branch residual in the combined signed family\<close>

theorem slp_mixed_branch_finite_residual_as_signed:
  fixes left_positive left_negative :: "slp_point^'i::finite"
    and right_positive right_negative :: "slp_point^'j::finite"
  shows
    "slp_mixed_branch_residual origin
        (slp_finite_branch_pair_list
          (\<lambda>i. left_positive $ i) (\<lambda>i. left_negative $ i))
        left_terminal
        (slp_finite_branch_pair_list
          (\<lambda>j. right_positive $ j) (\<lambda>j. right_negative $ j))
        right_terminal =
      slp_signed_residual slp_mixed_combined_sign
        (slp_mixed_combined_family
          (slp_point_as_complex origin)
          (\<lambda>i. slp_point_as_complex (left_positive $ i))
          (\<lambda>i. slp_point_as_complex (left_negative $ i))
          (slp_point_as_complex left_terminal)
          (\<lambda>j. slp_point_as_complex (right_positive $ j))
          (\<lambda>j. slp_point_as_complex (right_negative $ j))
          (slp_point_as_complex right_terminal))"
proof -
  let ?left_pairs = "slp_finite_branch_pair_list
    (\<lambda>i. left_positive $ i) (\<lambda>i. left_negative $ i)"
  let ?right_pairs = "slp_finite_branch_pair_list
    (\<lambda>j. right_positive $ j) (\<lambda>j. right_negative $ j)"
  let ?left_output = "slp_left_branch_output ?left_pairs left_terminal"
  let ?right_output = "slp_right_branch_output ?right_pairs right_terminal"
  let ?family = "slp_mixed_combined_family
    (slp_point_as_complex origin)
    (\<lambda>i. slp_point_as_complex (left_positive $ i))
    (\<lambda>i. slp_point_as_complex (left_negative $ i))
    (slp_point_as_complex left_terminal)
    (\<lambda>j. slp_point_as_complex (right_positive $ j))
    (\<lambda>j. slp_point_as_complex (right_negative $ j))
    (slp_point_as_complex right_terminal)"

  have left_quadratic:
      "sum_list (map (\<lambda>pair.
          slp_point_quadratic_value (fst pair) -
            slp_point_quadratic_value (snd pair)) ?left_pairs) =
        (\<Sum>i\<in>UNIV. slp_point_quadratic_value (left_positive $ i) -
          slp_point_quadratic_value (left_negative $ i))"
    by (rule slp_finite_branch_pair_list_quadratic_sum)
  have right_quadratic:
      "sum_list (map (\<lambda>pair.
          slp_point_quadratic_value (fst pair) -
            slp_point_quadratic_value (snd pair)) ?right_pairs) =
        (\<Sum>j\<in>UNIV. slp_point_quadratic_value (right_positive $ j) -
          slp_point_quadratic_value (right_negative $ j))"
    by (rule slp_finite_branch_pair_list_quadratic_sum)
  have left_output_complex:
      "slp_point_as_complex ?left_output =
        slp_point_as_complex left_terminal +
          (\<Sum>i\<in>UNIV. slp_point_as_complex (left_positive $ i) -
            slp_point_as_complex (left_negative $ i))"
    by (rule slp_finite_branch_pair_list_output_as_complex)
  have right_output_complex:
      "slp_point_as_complex ?right_output =
        slp_point_as_complex right_terminal +
          (\<Sum>j\<in>UNIV. slp_point_as_complex (right_positive $ j) -
            slp_point_as_complex (right_negative $ j))"
    using slp_finite_branch_pair_list_output_as_complex[
      where pos=right_positive and neg=right_negative
        and terminal=right_terminal]
    by (simp only: slp_left_branch_output_eq_right)
  have origin_neg_complex:
      "slp_point_as_complex (- origin) = - slp_point_as_complex origin"
    by (rule complex_eqI)
      (simp_all only: slp_point_as_complex_def complex.sel
        vector_uminus_component uminus_complex.sel)
  have mixed_output_complex:
      "slp_point_as_complex (- origin + ?left_output + ?right_output) =
        - slp_point_as_complex origin +
          (slp_point_as_complex left_terminal +
            (\<Sum>i\<in>UNIV. slp_point_as_complex (left_positive $ i) -
              slp_point_as_complex (left_negative $ i))) +
          (slp_point_as_complex right_terminal +
            (\<Sum>j\<in>UNIV. slp_point_as_complex (right_positive $ j) -
              slp_point_as_complex (right_negative $ j)))"
    using left_output_complex right_output_complex
    by (simp only: slp_point_as_complex_add origin_neg_complex)
  have branch_formula:
      "slp_mixed_branch_residual origin ?left_pairs left_terminal
          ?right_pairs right_terminal =
        - slp_point_quadratic_value origin +
          (\<Sum>i\<in>UNIV. slp_point_quadratic_value (left_positive $ i) -
            slp_point_quadratic_value (left_negative $ i)) +
          slp_point_quadratic_value left_terminal +
          (\<Sum>j\<in>UNIV. slp_point_quadratic_value (right_positive $ j) -
            slp_point_quadratic_value (right_negative $ j)) +
          slp_point_quadratic_value right_terminal -
          slp_point_quadratic_value
            (- origin + ?left_output + ?right_output)"
    unfolding slp_mixed_branch_residual_def slp_left_branch_residual_def
      slp_right_branch_residual_def slp_branch_residual_def
      slp_mixed_core_residual_def
    using left_quadratic right_quadratic
    by (simp add: slp_left_branch_output_eq_right algebra_simps)
  have signed_formula:
      "slp_signed_residual slp_mixed_combined_sign ?family =
        - slp_point_quadratic_value origin +
          (\<Sum>i\<in>UNIV. slp_point_quadratic_value (left_positive $ i) -
            slp_point_quadratic_value (left_negative $ i)) +
          slp_point_quadratic_value left_terminal +
          (\<Sum>j\<in>UNIV. slp_point_quadratic_value (right_positive $ j) -
            slp_point_quadratic_value (right_negative $ j)) +
          slp_point_quadratic_value right_terminal -
          slp_point_quadratic_value
            (- origin + ?left_output + ?right_output)"
  proof -
    note combined = slp_mixed_combined_residual_identity[
      where origin = "slp_point_as_complex origin"
        and left_positive =
          "\<lambda>i. slp_point_as_complex (left_positive $ i)"
        and left_negative =
          "\<lambda>i. slp_point_as_complex (left_negative $ i)"
        and left_terminal = "slp_point_as_complex left_terminal"
        and right_positive =
          "\<lambda>j. slp_point_as_complex (right_positive $ j)"
        and right_negative =
          "\<lambda>j. slp_point_as_complex (right_negative $ j)"
        and right_terminal = "slp_point_as_complex right_terminal"]
    have combined_real:
        "slp_signed_residual slp_mixed_combined_sign ?family =
          - Re ((slp_point_as_complex origin) ^ 2) +
            (\<Sum>i\<in>UNIV.
              Re ((slp_point_as_complex (left_positive $ i)) ^ 2) -
              Re ((slp_point_as_complex (left_negative $ i)) ^ 2)) +
            Re ((slp_point_as_complex left_terminal) ^ 2) +
            (\<Sum>j\<in>UNIV.
              Re ((slp_point_as_complex (right_positive $ j)) ^ 2) -
              Re ((slp_point_as_complex (right_negative $ j)) ^ 2)) +
            Re ((slp_point_as_complex right_terminal) ^ 2) -
            Re ((- slp_point_as_complex origin +
              (\<Sum>i\<in>UNIV.
                slp_point_as_complex (left_positive $ i) -
                slp_point_as_complex (left_negative $ i)) +
              slp_point_as_complex left_terminal +
              (\<Sum>j\<in>UNIV.
                slp_point_as_complex (right_positive $ j) -
                slp_point_as_complex (right_negative $ j)) +
              slp_point_as_complex right_terminal) ^ 2)"
      using combined
      by (simp only: Re_sum minus_complex.sel plus_complex.sel
          uminus_complex.sel sum_subtractf)
    have output_order:
        "- slp_point_as_complex origin +
            (\<Sum>i\<in>UNIV.
              slp_point_as_complex (left_positive $ i) -
              slp_point_as_complex (left_negative $ i)) +
            slp_point_as_complex left_terminal +
            (\<Sum>j\<in>UNIV.
              slp_point_as_complex (right_positive $ j) -
              slp_point_as_complex (right_negative $ j)) +
            slp_point_as_complex right_terminal =
          slp_point_as_complex
            (- origin + ?left_output + ?right_output)"
    proof -
      have reordered:
          "- slp_point_as_complex origin +
              (\<Sum>i\<in>UNIV.
                slp_point_as_complex (left_positive $ i) -
                slp_point_as_complex (left_negative $ i)) +
              slp_point_as_complex left_terminal +
              (\<Sum>j\<in>UNIV.
                slp_point_as_complex (right_positive $ j) -
                slp_point_as_complex (right_negative $ j)) +
              slp_point_as_complex right_terminal =
            - slp_point_as_complex origin +
              (slp_point_as_complex left_terminal +
                (\<Sum>i\<in>UNIV.
                  slp_point_as_complex (left_positive $ i) -
                  slp_point_as_complex (left_negative $ i))) +
              (slp_point_as_complex right_terminal +
                (\<Sum>j\<in>UNIV.
                  slp_point_as_complex (right_positive $ j) -
                  slp_point_as_complex (right_negative $ j)))"
        by (simp only: add.assoc add.left_commute add.commute)
      show ?thesis
        by (rule HOL.trans[OF reordered mixed_output_complex[symmetric]])
    qed
    show ?thesis
      using combined_real output_order
      by (simp only: slp_point_quadratic_value_as_complex_square)
  qed
  show ?thesis
    by (rule HOL.trans[OF branch_formula signed_formula[symmetric]])
qed

end
