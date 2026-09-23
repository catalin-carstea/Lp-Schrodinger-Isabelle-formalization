theory Inverse_Schrodinger_Lp_Cauchy_Bounded_Support_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Holder_Continuity"
begin

section \<open>Linear pointwise Cauchy control from bounded-support Lp data\<close>

theorem slp_cauchy_transform_bounded_support_lp_pointwise:
  fixes b :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and source_lp: "aim_complex_lp_on_plane b h"
    and support_radius:
      "\<And>y. h y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
  defines "q \<equiv> slp_holder_conjugate b"
  shows
    "slp_cauchy_integrable_at orientation h z \<and>
      norm (slp_cauchy_transform orientation h z) \<le>
        norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q))
              powr (1 / q) *
          aim_complex_lp_norm b h"
proof -
  have q_lower: "1 < q"
    and q_upper: "q < 2"
    and conjugates: "1 / q + 1 / b = 1"
    unfolding q_def
    using slp_holder_conjugate_arithmetic[OF exponent_above_two]
    by auto
  have q_at_least_one: "1 \<le> q"
    using q_lower by linarith
  have b_lower: "1 < b"
    using exponent_above_two by linarith
  have source_measurable: "h \<in> borel_measurable lborel"
    and source_power_integrable:
      "integrable lborel (\<lambda>y. norm (h y) powr b)"
    using source_lp unfolding aim_complex_lp_on_plane_def by blast+
  have source_norm_measurable:
      "(\<lambda>y. norm (h y)) \<in> borel_measurable lborel"
    using source_measurable by measurable
  have kernel_measurable:
      "(\<lambda>y. slp_localized_cauchy_kernel R (z - y)) \<in>
        borel_measurable lborel"
    using slp_localized_cauchy_kernel_borel_measurable by measurable
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr q)"
    using slp_localized_cauchy_kernel_power_translate_integrable[
        OF q_at_least_one q_upper, of R z]
      slp_localized_cauchy_kernel_nonnegative
    by simp
  note holder = slp_nonnegative_holder_integral[
    OF q_lower b_lower conjugates kernel_measurable source_norm_measurable]
  have product_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (h y))"
    by (rule holder(1))
      (simp_all add: slp_localized_cauchy_kernel_nonnegative
        kernel_power_integrable source_power_integrable)
  have holder_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (h y))
        \<le>
      (integral\<^sup>L lborel
          (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr q))
            powr (1 / q) *
        (integral\<^sup>L lborel (\<lambda>y. norm (h y) powr b))
          powr (1 / b)"
    by (rule holder(2))
      (simp_all add: slp_localized_cauchy_kernel_nonnegative
        kernel_power_integrable source_power_integrable)
  have kernel_translation:
      "integral\<^sup>L lborel
          (\<lambda>y. slp_localized_cauchy_kernel R (z - y) powr q) =
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q)"
    using slp_localized_cauchy_kernel_power_translate_integral[
        OF q_at_least_one q_upper, of R z]
      slp_localized_cauchy_kernel_nonnegative
    by simp
  have norm_integrand_eq:
      "(\<lambda>y. norm (slp_cauchy_integrand orientation h z y)) =
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (h y))"
    by (rule ext)
      (rule slp_cauchy_integrand_norm_eq_localized[OF support_radius])
  have integral_bound:
      "integral\<^sup>L lborel
          (\<lambda>y. norm (slp_cauchy_integrand orientation h z y))
        \<le>
      (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q))
            powr (1 / q) *
        aim_complex_lp_norm b h"
    unfolding norm_integrand_eq aim_complex_lp_norm_def
    using holder_bound kernel_translation by simp
  have transform_bound:
      "norm (slp_cauchy_transform orientation h z) \<le>
        norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel
            (\<lambda>y. norm (slp_cauchy_integrand orientation h z y))"
    by (rule slp_cauchy_transform_norm_bound)
  have scaled_bound:
      "norm (inverse (of_real pi :: complex)) *
          integral\<^sup>L lborel
            (\<lambda>y. norm (slp_cauchy_integrand orientation h z y))
        \<le>
      norm (inverse (of_real pi :: complex)) *
        ((integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q))
            powr (1 / q) *
          aim_complex_lp_norm b h)"
    by (rule mult_left_mono[OF integral_bound]) simp
  have cauchy_integrable:
      "slp_cauchy_integrable_at orientation h z"
    using slp_cauchy_scaled_young_bound_on_bounded_support[
        OF exponent_above_two radius_nonnegative zero_less_one source_lp
          support_radius, where orientation=orientation]
    by blast
  show ?thesis
  proof (intro conjI)
    show "slp_cauchy_integrable_at orientation h z"
      by (rule cauchy_integrable)
    show "norm (slp_cauchy_transform orientation h z) \<le>
        norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q))
              powr (1 / q) *
          aim_complex_lp_norm b h"
      using order_trans[OF transform_bound scaled_bound]
      by (simp only: mult.assoc)
  qed
qed

end
