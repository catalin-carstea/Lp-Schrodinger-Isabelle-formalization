theory Inverse_Schrodinger_Lp_Qstar_Localized_Holder
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Exponent_Arithmetic"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Localized_Cauchy_Power_Scaling"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Localized_Cauchy_Endpoint"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Localized_Cauchy_Riesz"
begin

section \<open>Localized Holder estimate at the qstar exponents\<close>

theorem slp_qstar_localized_riesz_holder:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and radius_positive: "0 < R"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows integrable:
      "integrable lborel (slp_localized_riesz_integrand R f z)"
    and bound:
      "integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
        R powr (2 / slp_qstar_holder_exponent a - 1) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
              slp_qstar_holder_exponent a))
            powr (1 / slp_qstar_holder_exponent a) *
          (integral\<^sup>L lborel
            (\<lambda>y. norm (f y) powr aim_hls_target_exponent a))
            powr (1 / aim_hls_target_exponent a)"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?s = "slp_qstar_holder_exponent a"
  have q_lower: "1 < ?q"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have s_lower: "1 < ?s"
    by (rule slp_qstar_exponent_relations(2)[OF exponent_lower
          exponent_upper])
  have s_upper: "?s < 2"
    by (rule slp_qstar_exponent_relations(3)[OF exponent_lower
          exponent_upper])
  have conjugate: "1 / ?s + 1 / ?q = 1"
    using slp_qstar_exponent_relations(4)[OF exponent_lower exponent_upper]
    by (simp only: add.commute)
  have s_at_least_one: "1 \<le> ?s"
    using s_lower by linarith
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    and amplitude_power_integrable:
      "integrable lborel (\<lambda>y. norm (f y) powr ?q)"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast+
  have amplitude_norm_measurable:
      "(\<lambda>y. norm (f y)) \<in> borel_measurable lborel"
    using amplitude_measurable by measurable
  have kernel_measurable:
      "(\<lambda>y. slp_localized_cauchy_kernel R (z - y))
        \<in> borel_measurable lborel"
    using slp_localized_cauchy_kernel_borel_measurable by measurable
  have kernel_nonnegative:
      "0 \<le> slp_localized_cauchy_kernel R (z - y)" for y
    by (rule slp_localized_cauchy_kernel_nonnegative)
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr ?s)"
    using slp_localized_cauchy_kernel_power_translate_integrable[
        OF s_at_least_one s_upper, of R z]
    by (simp add: kernel_nonnegative)
  have product_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (f y))"
    by (rule slp_nonnegative_holder_integral(1)[OF s_lower q_lower
          conjugate kernel_measurable amplitude_norm_measurable
          kernel_nonnegative norm_ge_zero kernel_power_integrable
          amplitude_power_integrable])
  show "integrable lborel (slp_localized_riesz_integrand R f z)"
    unfolding slp_localized_riesz_integrand_def
    by (rule product_integrable)
  have holder_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (f y))
        \<le>
        (integral\<^sup>L lborel
          (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr ?s))
          powr (1 / ?s) *
        (integral\<^sup>L lborel (\<lambda>y. norm (f y) powr ?q))
          powr (1 / ?q)"
    by (rule slp_nonnegative_holder_integral(2)[OF s_lower q_lower
          conjugate kernel_measurable amplitude_norm_measurable
          kernel_nonnegative norm_ge_zero kernel_power_integrable
          amplitude_power_integrable])
  have translated_kernel_root:
      "(integral\<^sup>L lborel
          (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr ?s))
          powr (1 / ?s) =
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr ?s))
          powr (1 / ?s)"
    using slp_localized_cauchy_kernel_power_translate_integral[
        OF s_at_least_one s_upper, of R z]
    by (simp add: slp_localized_cauchy_kernel_nonnegative)
  have scaled_kernel_root:
      "(integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr ?s))
          powr (1 / ?s) =
        R powr (2 / ?s - 1) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr ?s))
            powr (1 / ?s)"
    by (rule slp_localized_cauchy_kernel_power_root_scale[
          OF radius_positive s_at_least_one s_upper])
  show "integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
      R powr (2 / ?s - 1) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr ?s))
          powr (1 / ?s) *
        (integral\<^sup>L lborel (\<lambda>y. norm (f y) powr ?q))
          powr (1 / ?q)"
    unfolding slp_localized_riesz_integrand_def
    using holder_bound
    by (simp only: translated_kernel_root scaled_kernel_root mult.assoc)
qed

end
