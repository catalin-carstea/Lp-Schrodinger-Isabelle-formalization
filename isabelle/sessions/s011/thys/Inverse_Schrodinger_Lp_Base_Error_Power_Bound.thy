theory Inverse_Schrodinger_Lp_Base_Error_Power_Bound
  imports Inverse_Schrodinger_Lp_Derivative_Error_Transfer
begin

section \<open>Bounded-coordinate estimates for the base approximation error\<close>

lemma slp_raw_value_error_center_factor_bound:
  assumes radius_nonnegative: "0 \<le> R"
    and raw_support:
      "slp_raw_value_approximation_error phi g n x \<noteq> 0 \<Longrightarrow>
        norm (z - x) \<le> R"
  shows "norm (x - c) *
      norm (slp_raw_value_approximation_error phi g n x) \<le>
    (R + norm (z - c)) *
      norm (slp_raw_value_approximation_error phi g n x)"
proof (cases "slp_raw_value_approximation_error phi g n x = 0")
  case True
  then show ?thesis by simp
next
  case False
  have center_bound: "norm (x - c) \<le> R + norm (z - c)"
  proof -
    have "norm (x - c) = norm ((x - z) + (z - c))"
      by simp
    also have "... \<le> norm (x - z) + norm (z - c)"
      by (rule norm_triangle_ineq)
    also have "... \<le> R + norm (z - c)"
      using raw_support[OF False]
      by (simp only: norm_minus_commute add_le_cancel_right)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule mult_right_mono[OF center_bound norm_ge_zero])
qed

lemma slp_oscillatory_base_approximation_error_power_bound:
  assumes exponent_nonnegative: "0 \<le> b"
    and radius_nonnegative: "0 \<le> R"
    and raw_support:
      "slp_raw_value_approximation_error phi g n x \<noteq> 0 \<Longrightarrow>
        norm (z - x) \<le> R"
  shows "norm
      (slp_oscillatory_base_approximation_error tau c phi g n x) powr b
      \<le>
    (R + norm (z - c)) powr b *
      norm (slp_raw_value_approximation_error phi g n x) powr b"
proof -
  have product_bound:
      "norm (x - c) *
          norm (slp_raw_value_approximation_error phi g n x) \<le>
        (R + norm (z - c)) *
          norm (slp_raw_value_approximation_error phi g n x)"
    by (rule slp_raw_value_error_center_factor_bound[OF
          radius_nonnegative raw_support])
  have power_bound:
      "(norm (x - c) *
          norm (slp_raw_value_approximation_error phi g n x)) powr b \<le>
        ((R + norm (z - c)) *
          norm (slp_raw_value_approximation_error phi g n x)) powr b"
    by (rule powr_mono2[OF exponent_nonnegative])
       (use product_bound radius_nonnegative in auto)
  show ?thesis
    using power_bound
    by (simp only: slp_oscillatory_base_approximation_error_norm powr_mult)
qed

lemma slp_oscillatory_base_approximation_error_measurable:
  assumes raw_measurable:
    "slp_raw_value_approximation_error phi g n \<in>
      borel_measurable lborel"
  shows "slp_oscillatory_base_approximation_error tau c phi g n \<in>
    borel_measurable lborel"
proof -
  have factorized:
      "slp_oscillatory_base_approximation_error tau c phi g n =
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) *
            slp_raw_value_approximation_error phi g n x)"
    by (rule ext)
       (rule slp_oscillatory_base_approximation_error_factorization)
  show ?thesis
    unfolding factorized
    using raw_measurable slp_point_as_complex_borel_measurable
      slp_center_kernel_measurable[of tau c]
    by measurable
qed

theorem slp_oscillatory_base_approximation_error_lp:
  assumes exponent_positive: "0 < b"
    and radius_nonnegative: "0 \<le> R"
    and raw_lp:
      "aim_complex_lp_on_plane b
        (slp_raw_value_approximation_error phi g n)"
    and raw_support:
      "\<And>x. slp_raw_value_approximation_error phi g n x \<noteq> 0
        \<Longrightarrow> norm (z - x) \<le> R"
  shows "aim_complex_lp_on_plane b
    (slp_oscillatory_base_approximation_error tau c phi g n)"
proof -
  let ?M = "R + norm (z - c)"
  have M_nonnegative: "0 \<le> ?M"
    using radius_nonnegative by simp
  have raw_measurable:
      "slp_raw_value_approximation_error phi g n \<in>
        borel_measurable lborel"
    and raw_power_integrable:
      "integrable lborel (\<lambda>x.
        norm (slp_raw_value_approximation_error phi g n x) powr b)"
    using raw_lp unfolding aim_complex_lp_on_plane_def by auto
  have target_measurable:
      "slp_oscillatory_base_approximation_error tau c phi g n \<in>
        borel_measurable lborel"
    by (rule slp_oscillatory_base_approximation_error_measurable[OF
          raw_measurable])
  have target_power_measurable:
      "(\<lambda>x. norm
        (slp_oscillatory_base_approximation_error tau c phi g n x) powr b)
        \<in> borel_measurable lborel"
    using target_measurable by measurable
  have majorant_integrable:
      "integrable lborel (\<lambda>x. ?M powr b *
        norm (slp_raw_value_approximation_error phi g n x) powr b)"
    using raw_power_integrable by (rule integrable_mult_right)
  have target_power_integrable:
      "integrable lborel (\<lambda>x. norm
        (slp_oscillatory_base_approximation_error tau c phi g n x) powr b)"
  proof (rule Bochner_Integration.integrable_bound[OF
      majorant_integrable target_power_measurable])
    show "AE x in lborel.
      norm (norm
        (slp_oscillatory_base_approximation_error tau c phi g n x) powr b)
      \<le> norm (?M powr b *
        norm (slp_raw_value_approximation_error phi g n x) powr b)"
    proof (rule AE_I2)
      fix x
      have bound:
          "norm
            (slp_oscillatory_base_approximation_error tau c phi g n x)
              powr b \<le>
            ?M powr b *
              norm (slp_raw_value_approximation_error phi g n x) powr b"
        by (rule slp_oscillatory_base_approximation_error_power_bound[OF
              less_imp_le[OF exponent_positive] radius_nonnegative
              raw_support])
      show "norm (norm
          (slp_oscillatory_base_approximation_error tau c phi g n x) powr b)
        \<le> norm (?M powr b *
          norm (slp_raw_value_approximation_error phi g n x) powr b)"
        using bound M_nonnegative by simp
    qed
  qed
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using target_measurable target_power_integrable by blast
qed

theorem slp_oscillatory_base_approximation_error_power_integral_bound:
  assumes exponent_positive: "0 < b"
    and radius_nonnegative: "0 \<le> R"
    and raw_lp:
      "aim_complex_lp_on_plane b
        (slp_raw_value_approximation_error phi g n)"
    and raw_support:
      "\<And>x. slp_raw_value_approximation_error phi g n x \<noteq> 0
        \<Longrightarrow> norm (z - x) \<le> R"
  shows "(\<integral>x. norm
      (slp_oscillatory_base_approximation_error tau c phi g n x) powr b
        \<partial>lborel) \<le>
    (R + norm (z - c)) powr b *
      (\<integral>x.
        norm (slp_raw_value_approximation_error phi g n x) powr b
          \<partial>lborel)"
proof -
  let ?M = "R + norm (z - c)"
  have target_lp:
      "aim_complex_lp_on_plane b
        (slp_oscillatory_base_approximation_error tau c phi g n)"
    by (rule slp_oscillatory_base_approximation_error_lp[OF
          exponent_positive radius_nonnegative raw_lp raw_support])
  have target_power_integrable:
      "integrable lborel (\<lambda>x. norm
        (slp_oscillatory_base_approximation_error tau c phi g n x) powr b)"
    using target_lp unfolding aim_complex_lp_on_plane_def by blast
  have raw_power_integrable:
      "integrable lborel (\<lambda>x.
        norm (slp_raw_value_approximation_error phi g n x) powr b)"
    using raw_lp unfolding aim_complex_lp_on_plane_def by blast
  have majorant_integrable:
      "integrable lborel (\<lambda>x. ?M powr b *
        norm (slp_raw_value_approximation_error phi g n x) powr b)"
    using raw_power_integrable by (rule integrable_mult_right)
  have "(\<integral>x. norm
      (slp_oscillatory_base_approximation_error tau c phi g n x) powr b
        \<partial>lborel) \<le>
    (\<integral>x. ?M powr b *
      norm (slp_raw_value_approximation_error phi g n x) powr b
        \<partial>lborel)"
    by (rule integral_mono[OF target_power_integrable majorant_integrable])
       (rule slp_oscillatory_base_approximation_error_power_bound[OF
          less_imp_le[OF exponent_positive] radius_nonnegative raw_support])
  also have "... = ?M powr b *
      (\<integral>x.
        norm (slp_raw_value_approximation_error phi g n x) powr b
          \<partial>lborel)"
    by simp
  finally show ?thesis .
qed

end
