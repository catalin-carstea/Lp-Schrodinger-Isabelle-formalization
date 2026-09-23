theory Inverse_Schrodinger_Lp_W1p_Zero_Global_Far_Coefficient
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Far_Coefficient_Derivative_Bound"
begin

section \<open>Zero-Sobolev closure for the global far coefficient\<close>

theorem slp_w1p_zero_pair_on_global_far_coefficient:
  assumes exponent_one_le: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on p X u Du"
  shows "slp_w1p_zero_pair_on p X
    (\<lambda>x. slp_global_far_coefficient delta c x * u x)
    (\<lambda>x. \<chi> i. slp_global_far_coefficient delta c x * Du x $ i +
      u x * slp_complex_partial_derivative
        (slp_global_far_coefficient delta c) i x)"
proof -
  let ?A = "2 / delta"
  let ?B = "slp_global_cutoff_L / delta ^ 2 + 2 / delta ^ 2"
  have multiplier_smooth:
      "smooth_on UNIV (slp_global_far_coefficient delta c)"
    by (rule slp_global_far_coefficient_smooth[OF delta_positive])
  have value_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_global_far_coefficient delta c x) \<le> ?A"
    by (rule slp_global_far_coefficient_norm_bound[OF delta_positive])
  have derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (slp_complex_partial_derivative
          (slp_global_far_coefficient delta c) 0 x) \<le> ?B"
    by (rule slp_global_far_coefficient_partial_norm_bound[OF delta_positive])
  have derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (slp_complex_partial_derivative
          (slp_global_far_coefficient delta c) 1 x) \<le> ?B"
    by (rule slp_global_far_coefficient_partial_norm_bound[OF delta_positive])
  have A_nonnegative: "0 \<le> ?A"
    using delta_positive by simp
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct2,
          THEN conjunct2, THEN conjunct1])
  have delta_square_positive: "0 < delta ^ 2"
    using delta_positive by simp
  have cutoff_term_nonnegative:
      "0 \<le> slp_global_cutoff_L / delta ^ 2"
    by (rule divide_nonneg_pos[OF cutoff_nonnegative delta_square_positive])
  have square_term_nonnegative: "0 \<le> 2 / delta ^ 2"
    using delta_positive by simp
  have B_nonnegative: "0 \<le> ?B"
    by (rule add_nonneg_nonneg[OF cutoff_term_nonnegative
          square_term_nonnegative])
  show ?thesis
    by (rule slp_w1p_zero_pair_on_mult_smooth_bounded[
          OF exponent_one_le X_measurable X_bounded zero_pair
            multiplier_smooth value_bound derivative_zero_bound
            derivative_one_bound A_nonnegative B_nonnegative B_nonnegative])
qed

end
