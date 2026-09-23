theory Inverse_Schrodinger_Lp_Scaled_Young_Limit
  imports Inverse_Schrodinger_Lp_Error_Scale
begin

section \<open>Factorization of the scaled Young majorant\<close>

lemma slp_scaled_young_majorant_integral_factorization:
  fixes a b R :: real
    and h :: "slp_point \<Rightarrow> complex"
  assumes exponent: "2 < b"
    and scale_positive: "0 < a"
    and h_lp: "aim_complex_lp_on_plane b h"
  defines "q \<equiv> slp_holder_conjugate b"
  shows "(\<integral>y.
      (a * slp_localized_cauchy_kernel R (z - y)) powr q / q +
      (inverse a * norm (h y)) powr b / b \<partial>lborel) =
    (a powr q / q) *
      (\<integral>y. slp_localized_cauchy_kernel R (z - y) powr q
        \<partial>lborel) +
    ((\<integral>y. norm (h y) powr b \<partial>lborel) *
      (inverse a) powr b) / b"
proof -
  have q_lower: "1 < q" and q_upper: "q < 2"
    unfolding q_def using slp_holder_conjugate_arithmetic[OF exponent]
    by auto
  have q_positive: "0 < q" and b_positive: "0 < b"
    using q_lower exponent by linarith+
  have h_power_integrable:
      "integrable lborel (\<lambda>y. norm (h y) powr b)"
    using h_lp unfolding aim_complex_lp_on_plane_def by blast
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr q)"
    using slp_localized_cauchy_kernel_power_translate_integrable[of q R z]
      q_lower q_upper slp_localized_cauchy_kernel_nonnegative
    by simp
  have scaled_kernel_integrable:
      "integrable lborel
        (\<lambda>y. (a * slp_localized_cauchy_kernel R (z - y)) powr q / q)"
    using kernel_power_integrable scale_positive q_positive
    by (simp add: powr_mult)
  have scaled_error_integrable:
      "integrable lborel
        (\<lambda>y. (inverse a * norm (h y)) powr b / b)"
    using h_power_integrable scale_positive b_positive
    by (simp add: powr_mult)
  have kernel_factor:
      "(\<lambda>y. (a * slp_localized_cauchy_kernel R (z - y)) powr q / q) =
        (\<lambda>y. (a powr q / q) *
          slp_localized_cauchy_kernel R (z - y) powr q)"
    by (rule ext) (simp add: powr_mult divide_inverse ac_simps)
  have error_factor:
      "(\<lambda>y. (inverse a * norm (h y)) powr b / b) =
        (\<lambda>y. (norm (h y) powr b * (inverse a) powr b) / b)"
    by (rule ext) (simp add: powr_mult ac_simps)
  have "(\<integral>y.
      (a * slp_localized_cauchy_kernel R (z - y)) powr q / q +
      (inverse a * norm (h y)) powr b / b \<partial>lborel) =
    (\<integral>y.
      (a * slp_localized_cauchy_kernel R (z - y)) powr q / q
      \<partial>lborel) +
    (\<integral>y. (inverse a * norm (h y)) powr b / b \<partial>lborel)"
    by (rule Bochner_Integration.integral_add[OF
          scaled_kernel_integrable scaled_error_integrable])
  also have "... =
    (a powr q / q) *
      (\<integral>y. slp_localized_cauchy_kernel R (z - y) powr q
        \<partial>lborel) +
    ((\<integral>y. norm (h y) powr b \<partial>lborel) *
      (inverse a) powr b) / b"
    unfolding kernel_factor error_factor
    by simp
  finally show ?thesis .
qed

theorem slp_scaled_young_majorant_tendsto_zero_of_power_error:
  fixes b R :: real
    and h :: "nat \<Rightarrow> slp_point \<Rightarrow> complex"
    and e a :: "nat \<Rightarrow> real"
    and q :: real
  assumes exponent: "2 < b"
    and h_lp: "\<And>n. aim_complex_lp_on_plane b (h n)"
    and error_limit:
      "((\<lambda>n. \<integral>y. norm (h n y) powr b \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
  defines "e \<equiv> \<lambda>n. \<integral>y. norm (h n y) powr b \<partial>lborel"
    and "a \<equiv> slp_regularized_error_scale b e"
    and "q \<equiv> slp_holder_conjugate b"
  shows "((\<lambda>n. \<integral>y.
      (a n * slp_localized_cauchy_kernel R (z - y)) powr q / q +
      (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel)
    \<longlongrightarrow> 0) sequentially"
proof -
  have q_lower: "1 < q" and q_upper: "q < 2"
    unfolding q_def using slp_holder_conjugate_arithmetic[OF exponent]
    by auto
  have q_positive: "0 < q" and b_positive: "0 < b"
    using q_lower exponent by linarith+
  have e_nonnegative: "0 \<le> e n" for n
    unfolding e_def by (rule Bochner_Integration.integral_nonneg) simp
  have e_limit: "(e \<longlongrightarrow> 0) sequentially"
    using error_limit unfolding e_def .
  have scale_positive: "0 < a n" for n
    unfolding a_def
    by (rule slp_regularized_error_scale_positive[OF
          exponent e_nonnegative])
  have scale_nonnegative: "0 \<le> a n" for n
    using scale_positive[of n] by linarith
  have scale_limit: "(a \<longlongrightarrow> 0) sequentially"
    unfolding a_def
    by (rule slp_regularized_error_scale_tendsto_zero[OF
          exponent e_nonnegative e_limit])
  have scaled_error_limit:
      "((\<lambda>n. e n * (inverse (a n)) powr b)
        \<longlongrightarrow> 0) sequentially"
    unfolding a_def
    by (rule slp_regularized_error_scale_absorbs_error[OF
          exponent e_nonnegative e_limit])
  have scale_power_limit:
      "((\<lambda>n. a n powr q) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. a n powr q) \<longlongrightarrow> 0 powr q) sequentially"
      by (rule tendsto_powr2[OF scale_limit tendsto_const])
         (use scale_nonnegative q_positive in auto)
    then show ?thesis using q_positive by simp
  qed
  let ?K = "\<integral>y. slp_localized_cauchy_kernel R (z - y) powr q
    \<partial>lborel"
  have kernel_coefficient_limit:
      "((\<lambda>n. a n powr q / q) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. a n powr q / q) \<longlongrightarrow> 0 / q) sequentially"
      by (rule tendsto_divide[OF scale_power_limit tendsto_const])
         (use q_positive in simp)
    then show ?thesis by simp
  qed
  have kernel_term_limit:
      "((\<lambda>n. (a n powr q / q) * ?K)
        \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF kernel_coefficient_limit tendsto_const]
    by simp
  have error_term_limit:
      "((\<lambda>n. (e n * (inverse (a n)) powr b) / b)
        \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. (e n * (inverse (a n)) powr b) / b)
        \<longlongrightarrow> 0 / b) sequentially"
      by (rule tendsto_divide[OF scaled_error_limit tendsto_const])
         (use b_positive in simp)
    then show ?thesis by simp
  qed
  have factorized:
      "(\<lambda>n. \<integral>y.
        (a n * slp_localized_cauchy_kernel R (z - y)) powr q / q +
        (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel) =
      (\<lambda>n. (a n powr q / q) * ?K +
        (e n * (inverse (a n)) powr b) / b)"
  proof (rule ext)
    fix n
    show "(\<integral>y.
        (a n * slp_localized_cauchy_kernel R (z - y)) powr q / q +
        (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel) =
      (a n powr q / q) * ?K +
        (e n * (inverse (a n)) powr b) / b"
      unfolding e_def
      by (rule slp_scaled_young_majorant_integral_factorization[OF
            exponent scale_positive h_lp, folded q_def])
  qed
  have sum_limit:
      "((\<lambda>n. (a n powr q / q) * ?K +
        (e n * (inverse (a n)) powr b) / b)
        \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF kernel_term_limit error_term_limit] by simp
  show ?thesis
    unfolding factorized
    by (rule sum_limit)
qed

end
