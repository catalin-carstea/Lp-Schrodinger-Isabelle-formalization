theory Inverse_Schrodinger_Lp_Cauchy_HLS
  imports
    Inverse_Schrodinger_Lp_Cauchy_Transform
    "Paper_ISLP_AIM_Planar_Hardy_Littlewood_Sobolev.AIM_Planar_Hardy_Littlewood_Sobolev_Interface"
begin

section \<open>Source-orientation Hardy--Littlewood--Sobolev bound\<close>

lemma slp_point_as_complex_eq_aim [simp]:
  "slp_point_as_complex x = aim_point_as_complex x"
  by (simp add: slp_point_as_complex_def aim_point_as_complex_def)

lemma slp_dbar_integrand_eq_aim [simp]:
  "slp_cauchy_integrand SLP_Dbar_Inverse f z y =
    aim_planar_cauchy_integrand f z y"
  by (simp add: slp_cauchy_integrand_def slp_cauchy_kernel_def
      slp_cauchy_denominator_def aim_planar_cauchy_integrand_def)

lemma slp_dbar_inverse_eq_aim:
  "slp_dbar_inverse f = aim_planar_cauchy_transform f"
proof (rule ext)
  fix z
  have integrands_eq:
    "slp_cauchy_integrand SLP_Dbar_Inverse f z =
      aim_planar_cauchy_integrand f z"
    by (rule ext) simp
  show "slp_dbar_inverse f z = aim_planar_cauchy_transform f z"
    unfolding slp_cauchy_transform_def aim_planar_cauchy_transform_def
    using integrands_eq by simp
qed

lemma slp_hls_target_exponent_reciprocal:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows "1 / aim_hls_target_exponent p = 1 / p - 1 / 2"
proof -
  have p_nonzero: "p \<noteq> 0"
    using p_lower by linarith
  have denominator_nonzero: "2 * p \<noteq> 0"
    using p_nonzero by simp
  have cleared_denominator:
    "(1 / p - 1 / 2) * (2 * p) = 2 - p"
  proof -
    have "(1 / p - 1 / 2) * (2 * p) =
        (1 / p) * (2 * p) - (1 / 2) * (2 * p)"
      by (simp add: algebra_simps)
    also have "... = 2 - p"
      by (simp add: p_nonzero)
    finally show ?thesis .
  qed
  have common_denominator:
    "1 / p - 1 / 2 = (2 - p) / (2 * p)"
    using cleared_denominator denominator_nonzero
    by (simp add: nonzero_eq_divide_eq)
  show ?thesis
    unfolding aim_hls_target_exponent_def
    using common_denominator
    by simp
qed

context aim_planar_hls_cauchy
begin

theorem slp_dbar_inverse_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (slp_dbar_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
  using aim_planar_hls_cauchy
  unfolding aim_planar_hls_cauchy_claim_def slp_dbar_inverse_eq_aim
  by blast

corollary slp_dbar_inverse_hls_at_exponent:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and f_lp: "aim_complex_lp_on_plane p f"
  obtains C::real where
    "0 < C"
    "aim_complex_lp_on_plane (aim_hls_target_exponent p)
      (slp_dbar_inverse f)"
    "aim_complex_lp_norm (aim_hls_target_exponent p)
        (slp_dbar_inverse f)
      \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    "1 / aim_hls_target_exponent p = 1 / p - 1 / 2"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_dbar_inverse_hls by blast
  have mapped_and_bounded:
    "aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (slp_dbar_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    by (rule C_bound[OF p_lower p_upper f_lp])
  have mapped:
    "aim_complex_lp_on_plane (aim_hls_target_exponent p)
      (slp_dbar_inverse f)"
    using mapped_and_bounded by blast
  have bounded:
    "aim_complex_lp_norm (aim_hls_target_exponent p)
        (slp_dbar_inverse f)
      \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using mapped_and_bounded by blast
  show thesis
    by (rule that[OF C_positive mapped
          bounded
          slp_hls_target_exponent_reciprocal[OF p_lower p_upper]])
qed

end

end
