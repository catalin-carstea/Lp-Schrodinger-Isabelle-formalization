theory Inverse_Schrodinger_Lp_Complex_Lp_Coarse_Triangle
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Square_Source_Input_Lp"
begin

section \<open>Project-native coarse triangle bounds for the complex Lp norm\<close>

lemma slp_nonnegative_two_term_root_bound:
  fixes A B p :: real
  assumes exponent_one_le: "1 \<le> p"
    and A_nonnegative: "0 \<le> A"
    and B_nonnegative: "0 \<le> B"
  shows "(A + B) powr (1 / p)
    \<le> 2 * (A powr (1 / p) + B powr (1 / p))"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have inverse_nonnegative: "0 \<le> 1 / p"
    using exponent_positive by simp
  have inverse_le_one: "1 / p \<le> 1"
    using exponent_one_le by (simp add: divide_le_eq)
  have two_root_le_two: "(2::real) powr (1 / p) \<le> 2"
    using powr_mono[of "1 / p" 1 2] inverse_le_one by simp
  show ?thesis
  proof (cases "A \<le> B")
    case True
    have base_bound: "A + B \<le> 2 * B"
      using True by linarith
    have root_base_bound:
        "(A + B) powr (1 / p) \<le> (2 * B) powr (1 / p)"
      by (rule powr_mono2[OF inverse_nonnegative])
        (use A_nonnegative B_nonnegative base_bound in simp_all)
    have factor_bound:
        "2 powr (1 / p) * B powr (1 / p)
          \<le> 2 * (A powr (1 / p) + B powr (1 / p))"
    proof -
      have "2 powr (1 / p) * B powr (1 / p)
          \<le> 2 * B powr (1 / p)"
        by (rule mult_right_mono[OF two_root_le_two]) simp
      also have "... \<le> 2 * (A powr (1 / p) + B powr (1 / p))"
        by simp
      finally show ?thesis .
    qed
    show ?thesis
      using root_base_bound factor_bound by (simp only: powr_mult)
  next
    case False
    have base_bound: "A + B \<le> 2 * A"
      using False by linarith
    have root_base_bound:
        "(A + B) powr (1 / p) \<le> (2 * A) powr (1 / p)"
      by (rule powr_mono2[OF inverse_nonnegative])
        (use A_nonnegative B_nonnegative base_bound in simp_all)
    have factor_bound:
        "2 powr (1 / p) * A powr (1 / p)
          \<le> 2 * (A powr (1 / p) + B powr (1 / p))"
    proof -
      have "2 powr (1 / p) * A powr (1 / p)
          \<le> 2 * A powr (1 / p)"
        by (rule mult_right_mono[OF two_root_le_two]) simp
      also have "... \<le> 2 * (A powr (1 / p) + B powr (1 / p))"
        by simp
      finally show ?thesis .
    qed
    show ?thesis
      using root_base_bound factor_bound by (simp only: powr_mult)
  qed
qed

theorem slp_complex_lp_add_norm_coarse_triangle:
  fixes f g :: slp_scalar_field
  assumes exponent_one_le: "1 \<le> p"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_lp: "aim_complex_lp_on_plane p g"
  shows sum_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. f x + g x)"
    and sum_norm_bound:
      "aim_complex_lp_norm p (\<lambda>x. f x + g x)
        \<le> 4 * (aim_complex_lp_norm p f + aim_complex_lp_norm p g)"
proof -
  let ?A = "integral\<^sup>L lborel (\<lambda>x. norm (f x) powr p)"
  let ?B = "integral\<^sup>L lborel (\<lambda>x. norm (g x) powr p)"
  let ?S = "integral\<^sup>L lborel (\<lambda>x. norm (f x + g x) powr p)"
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have inverse_nonnegative: "0 \<le> 1 / p"
    using exponent_positive by simp
  have f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have g_power_integrable:
      "integrable lborel (\<lambda>x. norm (g x) powr p)"
    using g_lp unfolding aim_complex_lp_on_plane_def by blast
  have established_sum_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. f x + g x)"
    by (rule aim_complex_lp_on_plane_add[OF exponent_positive f_lp g_lp])
  show "aim_complex_lp_on_plane p (\<lambda>x. f x + g x)"
    by (rule established_sum_lp)
  have sum_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x + g x) powr p)"
    using established_sum_lp unfolding aim_complex_lp_on_plane_def by blast
  have majorant_integrable:
      "integrable lborel
        (\<lambda>x. 2 powr p *
          (norm (f x) powr p + norm (g x) powr p))"
  proof (rule integrable_mult_right)
    assume "2 powr p \<noteq> 0"
    show "integrable lborel
        (\<lambda>x. norm (f x) powr p + norm (g x) powr p)"
      by (rule Bochner_Integration.integrable_add[OF
            f_power_integrable g_power_integrable])
  qed
  have integral_bound: "?S \<le> 2 powr p * (?A + ?B)"
  proof -
    have "?S \<le> integral\<^sup>L lborel
        (\<lambda>x. 2 powr p *
          (norm (f x) powr p + norm (g x) powr p))"
      by (rule integral_mono[OF sum_power_integrable majorant_integrable])
        (rule slp_norm_add_powr_bound, use exponent_positive in simp)
    also have "... = 2 powr p * (?A + ?B)"
      using f_power_integrable g_power_integrable by simp
    finally show ?thesis .
  qed
  have A_nonnegative: "0 \<le> ?A"
    by (rule integral_nonneg_AE) simp
  have B_nonnegative: "0 \<le> ?B"
    by (rule integral_nonneg_AE) simp
  have S_nonnegative: "0 \<le> ?S"
    by (rule integral_nonneg_AE) simp
  have root_bound:
      "?S powr (1 / p)
        \<le> (2 powr p * (?A + ?B)) powr (1 / p)"
    by (rule powr_mono2[OF inverse_nonnegative])
      (use S_nonnegative integral_bound in simp_all)
  have exponent_nonzero: "p \<noteq> 0"
    using exponent_positive by simp
  have factor_root:
      "(2 powr p * (?A + ?B)) powr (1 / p)
        = 2 * (?A + ?B) powr (1 / p)"
  proof -
    have "(2 powr p * (?A + ?B)) powr (1 / p)
        = (2 powr p) powr (1 / p) * (?A + ?B) powr (1 / p)"
      by (simp only: powr_mult)
    also have "... = 2 powr (p * (1 / p)) *
        (?A + ?B) powr (1 / p)"
      by (simp only: powr_powr)
    also have "... = 2 * (?A + ?B) powr (1 / p)"
      using exponent_nonzero by simp
    finally show ?thesis .
  qed
  have sum_root_bound:
      "(?A + ?B) powr (1 / p)
        \<le> 2 * (?A powr (1 / p) + ?B powr (1 / p))"
    by (rule slp_nonnegative_two_term_root_bound[OF exponent_one_le
          A_nonnegative B_nonnegative])
  have scaled_sum_root_bound:
      "2 * (?A + ?B) powr (1 / p)
        \<le> 4 * (?A powr (1 / p) + ?B powr (1 / p))"
    using sum_root_bound by linarith
  have final_bound:
      "?S powr (1 / p)
        \<le> 4 * (?A powr (1 / p) + ?B powr (1 / p))"
    using root_bound factor_root scaled_sum_root_bound by linarith
  show "aim_complex_lp_norm p (\<lambda>x. f x + g x)
      \<le> 4 * (aim_complex_lp_norm p f + aim_complex_lp_norm p g)"
    unfolding aim_complex_lp_norm_def by (rule final_bound)
qed

theorem slp_complex_lp_diff_norm_coarse_triangle:
  fixes f g :: slp_scalar_field
  assumes exponent_one_le: "1 \<le> p"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_lp: "aim_complex_lp_on_plane p g"
  shows difference_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. f x - g x)"
    and difference_norm_bound:
      "aim_complex_lp_norm p (\<lambda>x. f x - g x)
        \<le> 4 * (aim_complex_lp_norm p f + aim_complex_lp_norm p g)"
proof -
  have negative_g_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. - g x)"
    by (rule aim_complex_lp_on_plane_uminus[OF g_lp])
  note addition = slp_complex_lp_add_norm_coarse_triangle[OF exponent_one_le
      f_lp negative_g_lp]
  show "aim_complex_lp_on_plane p (\<lambda>x. f x - g x)"
    using addition(1) by simp
  show "aim_complex_lp_norm p (\<lambda>x. f x - g x)
      \<le> 4 * (aim_complex_lp_norm p f + aim_complex_lp_norm p g)"
    using addition(2) unfolding aim_complex_lp_norm_def by simp
qed

end
