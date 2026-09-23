theory Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Lp
  imports
    Inverse_Schrodinger_Lp_Localized_Cauchy_Endpoint
    Inverse_Schrodinger_Lp_Double_Localized_Cauchy_L1
begin

section \<open>Higher integrability of the double localized kernel\<close>

definition slp_localized_cauchy_kernel_complex ::
  "real \<Rightarrow> slp_scalar_field"
where
  "slp_localized_cauchy_kernel_complex R x =
    of_real (slp_localized_cauchy_kernel R x)"

lemma slp_localized_cauchy_kernel_complex_lp:
  assumes exponent_lower: "1 < t"
    and exponent_upper: "t < 2"
  shows "aim_complex_lp_on_plane t
    (slp_localized_cauchy_kernel_complex R)"
proof -
  have kernel_measurable:
    "slp_localized_cauchy_kernel_complex R \<in> borel_measurable lborel"
    unfolding slp_localized_cauchy_kernel_complex_def
    using slp_localized_cauchy_kernel_borel_measurable by measurable
  have power_integrable:
    "integrable lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr t)"
    by (rule slp_localized_cauchy_kernel_power_integrable)
      (use exponent_lower exponent_upper in linarith)+
  have norm_power:
    "(\<lambda>x. norm (slp_localized_cauchy_kernel_complex R x) powr t) =
      (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr t)"
    by (rule ext)
      (simp add: slp_localized_cauchy_kernel_complex_def)
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using kernel_measurable power_integrable
    by (simp only: norm_power)
qed

lemma slp_localized_kernel_riesz_potential_eq_double:
  "slp_localized_riesz_potential R
      (slp_localized_cauchy_kernel_complex R) =
    slp_double_localized_cauchy_kernel R"
proof (rule ext)
  fix z :: slp_point
  have integrand_eq:
    "slp_localized_riesz_integrand R
        (slp_localized_cauchy_kernel_complex R) z =
      (\<lambda>y. slp_localized_cauchy_kernel R y *
        slp_localized_cauchy_kernel R (z - y))"
  proof (rule ext)
    fix y :: slp_point
    have kernel_nonnegative:
      "0 \<le> slp_localized_cauchy_kernel R y"
      by (rule slp_localized_cauchy_kernel_nonnegative)
    show "slp_localized_riesz_integrand R
          (slp_localized_cauchy_kernel_complex R) z y =
        slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (z - y)"
      unfolding slp_localized_riesz_integrand_def
        slp_localized_cauchy_kernel_complex_def
      using kernel_nonnegative by (simp add: mult.commute)
  qed
  show "slp_localized_riesz_potential R
        (slp_localized_cauchy_kernel_complex R) z =
      slp_double_localized_cauchy_kernel R z"
    unfolding slp_localized_riesz_potential_def
      slp_double_localized_cauchy_kernel_def slp_real_convolution_def
    by (simp only: integrand_eq)
qed

context aim_planar_riesz_hls
begin

theorem slp_double_localized_cauchy_kernel_lp:
  assumes radius_nonnegative: "0 \<le> R"
    and exponent_lower: "1 < t"
    and exponent_upper: "t < 2"
  shows "aim_real_lp_on_plane (aim_hls_target_exponent t)
    (slp_double_localized_cauchy_kernel R)"
proof -
  obtain C::real where C_positive: "0 < C"
    and localized:
      "\<forall>R p f. 0 \<le> R \<and> 1 < p \<and> p < 2 \<and>
          aim_complex_lp_on_plane p f
        \<longrightarrow>
        (AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_localized_riesz_hls by blast
  have kernel_lp:
    "aim_complex_lp_on_plane t
      (slp_localized_cauchy_kernel_complex R)"
    by (rule slp_localized_cauchy_kernel_complex_lp[OF
          exponent_lower exponent_upper])
  have potential_lp:
    "aim_real_lp_on_plane (aim_hls_target_exponent t)
      (slp_localized_riesz_potential R
        (slp_localized_cauchy_kernel_complex R))"
    using localized radius_nonnegative exponent_lower exponent_upper kernel_lp
    by blast
  show ?thesis
    using potential_lp
    by (simp only: slp_localized_kernel_riesz_potential_eq_double)
qed

end

end
