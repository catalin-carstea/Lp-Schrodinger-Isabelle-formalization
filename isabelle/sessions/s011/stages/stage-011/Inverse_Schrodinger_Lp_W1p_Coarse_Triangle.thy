theory Inverse_Schrodinger_Lp_W1p_Coarse_Triangle
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Test_Sobolev_Gain"
begin

section \<open>Coarse triangle control for the reviewed Sobolev norm\<close>

lemma slp_nonnegative_three_term_root_bound:
  fixes A B C p :: real
  assumes exponent_one_le: "1 \<le> p"
    and A_nonnegative: "0 \<le> A"
    and B_nonnegative: "0 \<le> B"
    and C_nonnegative: "0 \<le> C"
  shows "(A + B + C) powr (1 / p) \<le>
    4 * (A powr (1 / p) + B powr (1 / p) + C powr (1 / p))"
proof -
  have AB_nonnegative: "0 \<le> A + B"
    using A_nonnegative B_nonnegative by simp
  have outer_bound:
      "(A + B + C) powr (1 / p) \<le>
        2 * ((A + B) powr (1 / p) + C powr (1 / p))"
    by (rule slp_nonnegative_two_term_root_bound[OF exponent_one_le
          AB_nonnegative C_nonnegative])
  have inner_bound:
      "(A + B) powr (1 / p) \<le>
        2 * (A powr (1 / p) + B powr (1 / p))"
    by (rule slp_nonnegative_two_term_root_bound[OF exponent_one_le
          A_nonnegative B_nonnegative])
  have scaled_inner_bound:
      "2 * ((A + B) powr (1 / p) + C powr (1 / p)) \<le>
        2 * (2 * (A powr (1 / p) + B powr (1 / p)) +
          C powr (1 / p))"
    by (rule mult_left_mono[OF add_right_mono[OF inner_bound]]) simp
  have final_scaling:
      "2 * (2 * (A powr (1 / p) + B powr (1 / p)) +
          C powr (1 / p)) \<le>
        4 * (A powr (1 / p) + B powr (1 / p) + C powr (1 / p))"
  proof -
    have C_root_nonnegative: "0 \<le> C powr (1 / p)"
      by simp
    have C_scaling:
        "2 * (C powr (1 / p)) \<le> 4 * (C powr (1 / p))"
      by (rule mult_right_mono[OF _ C_root_nonnegative]) simp
    show ?thesis
      using C_scaling by (simp add: algebra_simps)
  qed
  show ?thesis
    by (rule order_trans[OF outer_bound
          order_trans[OF scaled_inner_bound final_scaling]])
qed

theorem slp_w1p_norm_on_component_sum_bound:
  assumes exponent_one_le: "1 \<le> p"
    and pair: "slp_w1p_pair_on p X u Du"
  shows "slp_w1p_norm_on p X u Du \<le>
    4 *
      (aim_complex_lp_norm p (slp_restrict_field X u) +
        aim_complex_lp_norm p
          (slp_restrict_field X (\<lambda>x. Du x $ 0)) +
        aim_complex_lp_norm p
          (slp_restrict_field X (\<lambda>x. Du x $ 1)))"
proof -
  let ?U = "integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p)"
  let ?D0 = "integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p)"
  let ?D1 = "integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p)"
  have U_nonnegative: "0 \<le> ?U"
    by (rule integral_nonneg_AE) simp
  have D0_nonnegative: "0 \<le> ?D0"
    by (rule integral_nonneg_AE) simp
  have D1_nonnegative: "0 \<le> ?D1"
    by (rule integral_nonneg_AE) simp
  have root_bound:
      "(?U + ?D0 + ?D1) powr (1 / p) \<le>
        4 * (?U powr (1 / p) + ?D0 powr (1 / p) +
          ?D1 powr (1 / p))"
    by (rule slp_nonnegative_three_term_root_bound[OF exponent_one_le
          U_nonnegative D0_nonnegative D1_nonnegative])
  show ?thesis
    unfolding slp_w1p_norm_on_def aim_complex_lp_norm_def
    by (rule root_bound)
qed

theorem slp_w1p_norm_on_diff_coarse_triangle:
  assumes exponent_one_le: "1 \<le> p"
    and first_pair: "slp_w1p_pair_on p X u Du"
    and second_pair: "slp_w1p_pair_on p X v Dv"
  shows "slp_w1p_norm_on p X
      (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x)
    \<le> 48 *
      (slp_w1p_norm_on p X u Du + slp_w1p_norm_on p X v Dv)"
proof -
  let ?Wu = "slp_w1p_norm_on p X u Du"
  let ?Wv = "slp_w1p_norm_on p X v Dv"
  let ?Fu = "aim_complex_lp_norm p (slp_restrict_field X u)"
  let ?Fv = "aim_complex_lp_norm p (slp_restrict_field X v)"
  let ?D0u = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. Du x $ 0))"
  let ?D0v = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. Dv x $ 0))"
  let ?D1u = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. Du x $ 1))"
  let ?D1v = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. Dv x $ 1))"
  let ?Fd = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. u x - v x))"
  let ?D0d = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. (Du x - Dv x) $ 0))"
  let ?D1d = "aim_complex_lp_norm p
    (slp_restrict_field X (\<lambda>x. (Du x - Dv x) $ 1))"
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have difference_pair:
      "slp_w1p_pair_on p X
        (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x)"
    by (rule slp_w1p_pair_on_diff[OF exponent_one_le first_pair second_pair])
  note first_components = slp_w1p_norm_on_component_bounds[
    OF exponent_positive first_pair]
  note second_components = slp_w1p_norm_on_component_bounds[
    OF exponent_positive second_pair]
  have function_presentation:
      "slp_restrict_field X (\<lambda>x. u x - v x) =
        (\<lambda>x. slp_restrict_field X u x - slp_restrict_field X v x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  have derivative_zero_presentation:
      "slp_restrict_field X (\<lambda>x. (Du x - Dv x) $ 0) =
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 0) x -
          slp_restrict_field X (\<lambda>y. Dv y $ 0) x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  have derivative_one_presentation:
      "slp_restrict_field X (\<lambda>x. (Du x - Dv x) $ 1) =
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 1) x -
          slp_restrict_field X (\<lambda>y. Dv y $ 1) x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  note function_difference = slp_complex_lp_diff_norm_coarse_triangle[
    OF exponent_one_le conjunct1[OF first_components(1)]
      conjunct1[OF second_components(1)]]
  note derivative_zero_difference = slp_complex_lp_diff_norm_coarse_triangle[
    OF exponent_one_le conjunct1[OF first_components(2)]
      conjunct1[OF second_components(2)]]
  note derivative_one_difference = slp_complex_lp_diff_norm_coarse_triangle[
    OF exponent_one_le conjunct1[OF first_components(3)]
      conjunct1[OF second_components(3)]]
  have function_difference_bound: "?Fd \<le> 4 * (?Fu + ?Fv)"
    unfolding function_presentation by (rule function_difference(2))
  have derivative_zero_difference_bound: "?D0d \<le> 4 * (?D0u + ?D0v)"
    unfolding derivative_zero_presentation
    by (rule derivative_zero_difference(2))
  have derivative_one_difference_bound: "?D1d \<le> 4 * (?D1u + ?D1v)"
    unfolding derivative_one_presentation
    by (rule derivative_one_difference(2))
  have function_sources_bound: "?Fu + ?Fv \<le> ?Wu + ?Wv"
    by (rule add_mono[OF conjunct2[OF first_components(1)]
          conjunct2[OF second_components(1)]])
  have derivative_zero_sources_bound: "?D0u + ?D0v \<le> ?Wu + ?Wv"
    by (rule add_mono[OF conjunct2[OF first_components(2)]
          conjunct2[OF second_components(2)]])
  have derivative_one_sources_bound: "?D1u + ?D1v \<le> ?Wu + ?Wv"
    by (rule add_mono[OF conjunct2[OF first_components(3)]
          conjunct2[OF second_components(3)]])
  have source_components_bound:
      "(?Fu + ?Fv) + (?D0u + ?D0v) + (?D1u + ?D1v) \<le>
        3 * (?Wu + ?Wv)"
  proof -
    have first_two:
        "(?Fu + ?Fv) + (?D0u + ?D0v) \<le>
          (?Wu + ?Wv) + (?Wu + ?Wv)"
      by (rule add_mono[OF function_sources_bound
            derivative_zero_sources_bound])
    have all_three:
        "((?Fu + ?Fv) + (?D0u + ?D0v)) + (?D1u + ?D1v) \<le>
          ((?Wu + ?Wv) + (?Wu + ?Wv)) + (?Wu + ?Wv)"
      by (rule add_mono[OF first_two derivative_one_sources_bound])
    show ?thesis
      using all_three by (simp add: algebra_simps)
  qed
  have difference_components_to_sources:
      "?Fd + ?D0d + ?D1d \<le>
        4 * ((?Fu + ?Fv) + (?D0u + ?D0v) + (?D1u + ?D1v))"
  proof -
    have first_two:
        "?Fd + ?D0d \<le> 4 * (?Fu + ?Fv) + 4 * (?D0u + ?D0v)"
      by (rule add_mono[OF function_difference_bound
            derivative_zero_difference_bound])
    have all_three:
        "(?Fd + ?D0d) + ?D1d \<le>
          (4 * (?Fu + ?Fv) + 4 * (?D0u + ?D0v)) +
            4 * (?D1u + ?D1v)"
      by (rule add_mono[OF first_two derivative_one_difference_bound])
    show ?thesis
      using all_three by (simp add: algebra_simps)
  qed
  have difference_components_bound:
      "?Fd + ?D0d + ?D1d \<le> 12 * (?Wu + ?Wv)"
  proof (rule order_trans[OF difference_components_to_sources])
    have scaled_source_components:
        "4 * ((?Fu + ?Fv) + (?D0u + ?D0v) + (?D1u + ?D1v)) \<le>
          4 * (3 * (?Wu + ?Wv))"
      by (rule mult_left_mono[OF source_components_bound]) simp
    show "4 * ((?Fu + ?Fv) + (?D0u + ?D0v) + (?D1u + ?D1v)) \<le>
        12 * (?Wu + ?Wv)"
      using scaled_source_components by simp
  qed
  have reviewed_component_bound:
      "slp_w1p_norm_on p X
          (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x) \<le>
        4 * (?Fd + ?D0d + ?D1d)"
    by (rule slp_w1p_norm_on_component_sum_bound[
          OF exponent_one_le difference_pair])
  show ?thesis
  proof (rule order_trans[OF reviewed_component_bound])
    have scaled_difference_components:
        "4 * (?Fd + ?D0d + ?D1d) \<le> 4 * (12 * (?Wu + ?Wv))"
      by (rule mult_left_mono[OF difference_components_bound]) simp
    show "4 * (?Fd + ?D0d + ?D1d) \<le> 48 * (?Wu + ?Wv)"
      using scaled_difference_components by simp
  qed
qed

end
