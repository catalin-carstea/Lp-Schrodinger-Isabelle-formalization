theory Inverse_Schrodinger_Lp_Cauchy_HLS_Local
  imports Inverse_Schrodinger_Lp_Cauchy_HLS_Sum
begin

section \<open>Local restrictions of planar fields\<close>

definition slp_restrict_field ::
  "slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_restrict_field X f x = (if x \<in> X then f x else 0)"

definition slp_complex_lp_on ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow> bool"
where
  "slp_complex_lp_on p X f \<longleftrightarrow>
    aim_complex_lp_on_plane p (slp_restrict_field X f)"

definition slp_complex_lp_norm_on ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow> real"
where
  "slp_complex_lp_norm_on p X f =
    aim_complex_lp_norm p (slp_restrict_field X f)"

lemma slp_restrict_field_measurable:
  assumes X_measurable: "X \<in> sets lborel"
    and f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_restrict_field X f \<in> borel_measurable lborel"
  unfolding slp_restrict_field_def
  using assms by measurable

lemma aim_complex_lp_on_plane_restrict:
  assumes p_positive: "0 < p"
    and X_measurable: "X \<in> sets lborel"
    and f_lp: "aim_complex_lp_on_plane p f"
  shows "slp_complex_lp_on p X f"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by auto
  have restrict_measurable:
    "slp_restrict_field X f \<in> borel_measurable lborel"
    by (rule slp_restrict_field_measurable[OF X_measurable f_measurable])
  have restrict_power_measurable:
    "(\<lambda>x. norm (slp_restrict_field X f x) powr p)
      \<in> borel_measurable lborel"
    using restrict_measurable by measurable
  have restrict_power_bound:
    "AE x in lborel.
      norm (norm (slp_restrict_field X f x) powr p) \<le>
        norm (norm (f x) powr p)"
  proof (rule AE_I2)
    fix x :: slp_point
    have pointwise:
      "norm (slp_restrict_field X f x) powr p \<le> norm (f x) powr p"
      by (cases "x \<in> X") (simp_all add: slp_restrict_field_def)
    have local_nonnegative:
      "0 \<le> norm (slp_restrict_field X f x) powr p"
      by simp
    have global_nonnegative: "0 \<le> norm (f x) powr p"
      by simp
    show "norm (norm (slp_restrict_field X f x) powr p) \<le>
        norm (norm (f x) powr p)"
      using pointwise local_nonnegative global_nonnegative
      by simp
  qed
  have restrict_power_integrable:
    "integrable lborel
      (\<lambda>x. norm (slp_restrict_field X f x) powr p)"
    by (rule Bochner_Integration.integrable_bound[OF f_power_integrable
          restrict_power_measurable restrict_power_bound])
  show ?thesis
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
    using restrict_measurable restrict_power_integrable by blast
qed

lemma slp_complex_lp_norm_on_le:
  assumes p_positive: "0 < p"
    and X_measurable: "X \<in> sets lborel"
    and f_lp: "aim_complex_lp_on_plane p f"
  shows "slp_complex_lp_norm_on p X f \<le> aim_complex_lp_norm p f"
proof -
  have f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by auto
  have local_lp: "slp_complex_lp_on p X f"
    by (rule aim_complex_lp_on_plane_restrict[OF assms])
  have local_power_integrable:
      "integrable lborel
        (\<lambda>x. norm (slp_restrict_field X f x) powr p)"
    using local_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by auto
  have power_le:
    "(\<integral>x. norm (slp_restrict_field X f x) powr p \<partial>lborel)
      \<le> (\<integral>x. norm (f x) powr p \<partial>lborel)"
  proof (rule integral_mono[OF local_power_integrable f_power_integrable])
    fix x :: slp_point
    assume "x \<in> space lborel"
    show "norm (slp_restrict_field X f x) powr p \<le>
      norm (f x) powr p"
      using p_positive
      by (auto simp: slp_restrict_field_def powr_ge_zero)
  qed
  have local_integral_nonnegative:
    "0 \<le> (\<integral>x. norm (slp_restrict_field X f x) powr p
      \<partial>lborel)"
    by (rule Bochner_Integration.integral_nonneg) simp
  have reciprocal_nonnegative: "0 \<le> 1 / p"
    using p_positive by simp
  have powered_le:
    "(\<integral>x. norm (slp_restrict_field X f x) powr p \<partial>lborel)
        powr (1 / p)
      \<le> (\<integral>x. norm (f x) powr p \<partial>lborel) powr (1 / p)"
    by (rule powr_mono2[OF reciprocal_nonnegative
          local_integral_nonnegative power_le])
  show ?thesis
    using powered_le
    unfolding slp_complex_lp_norm_on_def aim_complex_lp_norm_def .
qed

section \<open>The local HLS estimate\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_hls_sum_on_measurable:
  "\<exists>K::real. 0 < K \<and>
    (\<forall>p f X. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f \<and>
        X \<in> sets lborel
      \<longrightarrow>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f) \<and>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) \<and>
      slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) +
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f)
        \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
proof -
  obtain K::real where K_positive: "0 < K"
    and K_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_inverse f) +
          aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_both_cauchy_hls_sum by blast
  have all_local:
    "\<forall>p f X. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f \<and>
        X \<in> sets lborel
      \<longrightarrow>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f) \<and>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) \<and>
      slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) +
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f)
        \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
  proof (intro allI impI)
    fix p :: real and f :: slp_scalar_field and X :: "slp_point set"
    assume hypotheses:
      "1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f \<and>
        X \<in> sets lborel"
    have target_positive: "0 < aim_hls_target_exponent p"
      using hypotheses
      unfolding aim_hls_target_exponent_def
      by (intro divide_pos_pos mult_pos_pos) auto
    have global_result:
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_inverse f) +
          aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      by (rule K_bound) (use hypotheses in auto)
    have local_partial:
      "slp_complex_lp_on (aim_hls_target_exponent p) X
        (slp_partial_inverse f)"
      by (rule aim_complex_lp_on_plane_restrict)
         (use target_positive hypotheses global_result in auto)
    have local_dbar:
      "slp_complex_lp_on (aim_hls_target_exponent p) X
        (slp_dbar_inverse f)"
      by (rule aim_complex_lp_on_plane_restrict)
         (use target_positive hypotheses global_result in auto)
    have partial_le:
      "slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f)
        \<le> aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)"
      by (rule slp_complex_lp_norm_on_le)
         (use target_positive hypotheses global_result in auto)
    have dbar_le:
      "slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f)
        \<le> aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)"
      by (rule slp_complex_lp_norm_on_le)
         (use target_positive hypotheses global_result in auto)
    have local_sum_bound:
      "slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) +
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f)
        \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using partial_le dbar_le global_result by linarith
    show "slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f) \<and>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) \<and>
      slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) +
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f)
        \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using local_dbar local_partial local_sum_bound by blast
  qed
  show ?thesis
    using K_positive all_local by blast
qed

corollary slp_both_cauchy_hls_sum_on_bounded_support:
  "\<exists>K::real. 0 < K \<and>
    (\<forall>p f X. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f \<and>
        X \<in> sets lborel \<and> bounded X \<and> bounded (support f)
      \<longrightarrow>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f) \<and>
      slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) \<and>
      slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_inverse f) +
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_inverse f)
        \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
  using slp_both_cauchy_hls_sum_on_measurable by blast

end

end
