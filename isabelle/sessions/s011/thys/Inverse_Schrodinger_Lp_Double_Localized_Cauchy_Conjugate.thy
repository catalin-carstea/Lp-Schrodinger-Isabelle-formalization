theory Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Conjugate
  imports Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Lp
begin

section \<open>The exact conjugate exponent for the double kernel\<close>

definition slp_double_kernel_source_exponent :: "real \<Rightarrow> real" where
  "slp_double_kernel_source_exponent p = 2 * p / (3 * p - 2)"

lemma slp_double_kernel_source_exponent_arithmetic:
  assumes p_lower: "1 < p" and p_upper: "p < 2"
  shows "1 < slp_double_kernel_source_exponent p"
    and "slp_double_kernel_source_exponent p < 2"
    and "aim_hls_target_exponent (slp_double_kernel_source_exponent p) =
      p / (p - 1)"
proof -
  have denominator_positive: "0 < 3 * p - 2"
    using p_lower by linarith
  show "1 < slp_double_kernel_source_exponent p"
    unfolding slp_double_kernel_source_exponent_def
    using denominator_positive p_upper
    by (simp add: less_divide_eq)
  show "slp_double_kernel_source_exponent p < 2"
    unfolding slp_double_kernel_source_exponent_def
    using denominator_positive p_lower
    by (simp add: divide_less_eq)
  have p_minus_one_nonzero: "p - 1 \<noteq> 0"
    using p_lower by linarith
  have source_denominator_nonzero: "3 * p - 2 \<noteq> 0"
    using denominator_positive by simp
  have denominator_identity:
    "2 - 2 * p / (3 * p - 2) =
      4 * (p - 1) / (3 * p - 2)"
  proof -
    have first:
      "2 - 2 * p / (3 * p - 2) =
        (2 * (3 * p - 2) - 2 * p) / (3 * p - 2)"
      by (rule diff_divide_eq_iff[OF source_denominator_nonzero])
    have numerators:
      "2 * (3 * p - 2) - 2 * p = 4 * (p - 1)"
      by (simp add: algebra_simps)
    show ?thesis
      using first numerators by simp
  qed
  have product_denominator_nonzero:
    "(3 * p - 2) * (4 * (p - 1)) \<noteq> 0"
    using p_minus_one_nonzero source_denominator_nonzero by simp
  have cancelled_fraction:
    "(4 * p * (3 * p - 2)) /
        ((3 * p - 2) * (4 * (p - 1))) = p / (p - 1)"
  proof -
    have cancel_three:
      "(4 * p * (3 * p - 2)) /
          ((3 * p - 2) * (4 * (p - 1))) =
        (4 * p) / (4 * (p - 1))"
      using source_denominator_nonzero
      by (simp add: mult.commute mult.left_commute)
    have cancel_four:
      "(4 * p) / (4 * (p - 1)) = p / (p - 1)"
    proof -
      have four_nonzero: "(4::real) \<noteq> 0"
        by simp
      show ?thesis
        using nonzero_mult_divide_mult_cancel_left[OF four_nonzero,
          of p "p - 1"]
        by simp
    qed
    show ?thesis
      using cancel_three cancel_four by simp
  qed
  have target_identity:
    "2 * (2 * p / (3 * p - 2)) /
        (2 - 2 * p / (3 * p - 2)) = p / (p - 1)"
  proof -
    have numerator_identity:
      "2 * (2 * p / (3 * p - 2)) =
        (4 * p) / (3 * p - 2)"
      by (simp add: algebra_simps)
    have rewritten:
      "2 * (2 * p / (3 * p - 2)) /
          (2 - 2 * p / (3 * p - 2)) =
        ((4 * p) / (3 * p - 2)) /
          ((4 * (p - 1)) / (3 * p - 2))"
      using numerator_identity denominator_identity by simp
    have divided:
      "((4 * p) / (3 * p - 2)) /
          ((4 * (p - 1)) / (3 * p - 2)) =
        (4 * p * (3 * p - 2)) /
          ((3 * p - 2) * (4 * (p - 1)))"
      by (rule divide_divide_times_eq)
    show ?thesis
      using rewritten divided cancelled_fraction by metis
  qed
  show "aim_hls_target_exponent (slp_double_kernel_source_exponent p) =
      p / (p - 1)"
  proof -
    have unfolded:
      "aim_hls_target_exponent (slp_double_kernel_source_exponent p) =
        2 * (2 * p / (3 * p - 2)) /
          (2 - 2 * p / (3 * p - 2))"
      by (simp only: aim_hls_target_exponent_def
          slp_double_kernel_source_exponent_def)
    show ?thesis
      using unfolded target_identity by simp
  qed
qed

context aim_planar_riesz_hls
begin

theorem slp_double_localized_cauchy_kernel_conjugate_lp:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
  shows "aim_real_lp_on_plane (p / (p - 1))
    (slp_double_localized_cauchy_kernel R)"
proof -
  let ?t = "slp_double_kernel_source_exponent p"
  have t_lower: "1 < ?t" and t_upper: "?t < 2"
    and target: "aim_hls_target_exponent ?t = p / (p - 1)"
    using slp_double_kernel_source_exponent_arithmetic[OF p_lower p_upper]
    by blast+
  have membership:
    "aim_real_lp_on_plane (aim_hls_target_exponent ?t)
      (slp_double_localized_cauchy_kernel R)"
    by (rule slp_double_localized_cauchy_kernel_lp[OF
          radius_nonnegative t_lower t_upper])
  show ?thesis
    using membership by (simp only: target)
qed

end

end
