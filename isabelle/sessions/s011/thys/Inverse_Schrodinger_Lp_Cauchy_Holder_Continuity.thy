theory Inverse_Schrodinger_Lp_Cauchy_Holder_Continuity
  imports
    Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Weighted_L1_Closure
    Inverse_Schrodinger_Lp_Localized_Cauchy_Endpoint
begin

section \<open>Fixed-output Cauchy continuity from bounded-support Lp decay\<close>

lemma slp_cauchy_integrand_norm_eq_localized:
  assumes support_radius: "\<And>y. h y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
  shows "norm (slp_cauchy_integrand orientation h z y) =
    slp_localized_cauchy_kernel R (z - y) * norm (h y)"
proof (cases "h y = 0")
  case True
  then show ?thesis
    by (simp add: slp_cauchy_integrand_def)
next
  case False
  have inside: "slp_localized_cauchy_kernel R (z - y) =
      inverse (norm (z - y))"
    by (rule slp_localized_cauchy_kernel_inside[OF
          support_radius[OF False]])
  show ?thesis
    unfolding slp_cauchy_integrand_def norm_mult slp_cauchy_kernel_norm
      slp_radial_inverse_def inside
    by (simp only: mult.commute)
qed

theorem slp_cauchy_scaled_young_bound_on_bounded_support:
  assumes exponent: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and scale_positive: "0 < a"
    and h_lp: "aim_complex_lp_on_plane b h"
    and support_radius: "\<And>y. h y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
  defines "q \<equiv> slp_holder_conjugate b"
  shows "slp_cauchy_integrable_at orientation h z \<and>
    (\<integral>y. norm (slp_cauchy_integrand orientation h z y) \<partial>lborel)
      \<le> (\<integral>y.
        (a * slp_localized_cauchy_kernel R (z - y)) powr q / q +
        (inverse a * norm (h y)) powr b / b \<partial>lborel)"
proof -
  have q_lower: "1 < q" and q_upper: "q < 2"
    and conjugates: "1 / q + 1 / b = 1"
    unfolding q_def using slp_holder_conjugate_arithmetic[OF exponent]
    by auto
  have q_positive: "0 < q" and b_positive: "0 < b"
    using q_lower exponent by linarith+
  have h_measurable: "h \<in> borel_measurable lborel"
    and h_power_integrable:
      "integrable lborel (\<lambda>y. norm (h y) powr b)"
    using h_lp unfolding aim_complex_lp_on_plane_def by auto
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>y. abs (slp_localized_cauchy_kernel R (z - y)) powr q)"
    by (rule slp_localized_cauchy_kernel_power_translate_integrable)
       (use q_lower q_upper in linarith)+
  have scaled_kernel_power_integrable:
      "integrable lborel
        (\<lambda>y. (a * slp_localized_cauchy_kernel R (z - y)) powr q)"
    using kernel_power_integrable scale_positive
    by (simp add: powr_mult abs_of_nonneg
          slp_localized_cauchy_kernel_nonnegative)
  have scaled_h_power_integrable:
      "integrable lborel (\<lambda>y. (inverse a * norm (h y)) powr b)"
    using h_power_integrable scale_positive
    by (simp add: powr_mult)
  let ?majorant = "\<lambda>y.
    (a * slp_localized_cauchy_kernel R (z - y)) powr q / q +
    (inverse a * norm (h y)) powr b / b"
  have majorant_integrable: "integrable lborel ?majorant"
    using scaled_kernel_power_integrable scaled_h_power_integrable
      q_positive b_positive
    by simp
  have product_le_majorant:
      "slp_localized_cauchy_kernel R (z - y) * norm (h y)
        \<le> ?majorant y" for y
  proof -
    have young:
        "(a * slp_localized_cauchy_kernel R (z - y)) *
            (inverse a * norm (h y)) \<le> ?majorant y"
      by (rule Youngs_inequality[OF q_lower _ conjugates])
         (use exponent scale_positive
            slp_localized_cauchy_kernel_nonnegative[of R "z - y"]
          in auto)
    have cancellation:
        "(a * slp_localized_cauchy_kernel R (z - y)) *
            (inverse a * norm (h y)) =
          slp_localized_cauchy_kernel R (z - y) * norm (h y)"
      using scale_positive by (simp add: ac_simps)
    show ?thesis
      using young cancellation by simp
  qed
  have majorant_nonnegative: "0 \<le> ?majorant y" for y
    using q_positive b_positive by simp
  have product_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (h y))"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "(\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (h y))
        \<in> borel_measurable lborel"
      using slp_localized_cauchy_kernel_borel_measurable h_measurable
      by measurable
    show "AE y in lborel.
        norm (slp_localized_cauchy_kernel R (z - y) * norm (h y))
          \<le> norm (?majorant y)"
    proof (rule AE_I2)
      fix y
      show "norm (slp_localized_cauchy_kernel R (z - y) * norm (h y))
          \<le> norm (?majorant y)"
        using product_le_majorant[of y] majorant_nonnegative[of y]
          slp_localized_cauchy_kernel_nonnegative[of R "z - y"]
        by simp
    qed
  qed
  have norm_integrand_eq:
      "(\<lambda>y. norm (slp_cauchy_integrand orientation h z y)) =
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y) * norm (h y))"
    by (rule ext)
       (rule slp_cauchy_integrand_norm_eq_localized[OF support_radius])
  have cauchy_integrable: "slp_cauchy_integrable_at orientation h z"
  proof (rule slp_cauchy_integrable_at_of_norm_majorant[OF h_measurable])
    show "integrable lborel
        (\<lambda>y. norm (h y) * norm (slp_cauchy_kernel orientation z y))"
      using product_integrable
      by (simp only: norm_integrand_eq[symmetric]
          slp_cauchy_integrand_def norm_mult)
  qed
  have integral_bound:
      "(\<integral>y. norm (slp_cauchy_integrand orientation h z y) \<partial>lborel)
        \<le> (\<integral>y. ?majorant y \<partial>lborel)"
    unfolding norm_integrand_eq
    by (rule integral_mono[OF product_integrable majorant_integrable])
       (use product_le_majorant in \<open>simp add: ac_simps\<close>)
  show ?thesis
    using cauchy_integrable integral_bound by blast
qed

theorem slp_cauchy_weighted_L1_tendsto_of_scaled_young:
  assumes exponent: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and scale_positive: "\<And>n. 0 < a n"
    and h_lp: "\<And>n. aim_complex_lp_on_plane b (h n)"
    and support_radius:
      "\<And>n y. h n y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
    and majorant_limit:
      "((\<lambda>n. \<integral>y.
        (a n * slp_localized_cauchy_kernel R (z - y)) powr
            slp_holder_conjugate b / slp_holder_conjugate b +
        (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. \<integral>\<^sup>+y.
      norm (slp_cauchy_integrand orientation (h n) z y) \<partial>lborel)
    \<longlongrightarrow> 0) sequentially"
proof -
  let ?q = "slp_holder_conjugate b"
  have bounds: "slp_cauchy_integrable_at orientation (h n) z \<and>
      (\<integral>y. norm (slp_cauchy_integrand orientation (h n) z y)
        \<partial>lborel) \<le> (\<integral>y.
          (a n * slp_localized_cauchy_kernel R (z - y)) powr ?q / ?q +
          (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel)" for n
    by (rule slp_cauchy_scaled_young_bound_on_bounded_support[OF
          exponent radius_nonnegative scale_positive h_lp support_radius])
  have rhs_limit:
      "((\<lambda>n. ennreal (\<integral>y.
          (a n * slp_localized_cauchy_kernel R (z - y)) powr ?q / ?q +
          (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel))
        \<longlongrightarrow> 0) sequentially"
    using tendsto_ennrealI[OF majorant_limit] by simp
  have upper_bound:
      "\<And>n. (\<integral>\<^sup>+y.
          norm (slp_cauchy_integrand orientation (h n) z y) \<partial>lborel)
        \<le> ennreal (\<integral>y.
          (a n * slp_localized_cauchy_kernel R (z - y)) powr ?q / ?q +
          (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel)"
  proof -
    fix n
    have integrand_integrable:
        "integrable lborel (slp_cauchy_integrand orientation (h n) z)"
      using bounds[of n] unfolding slp_cauchy_integrable_at_def by blast
    have norm_integrable:
        "integrable lborel
          (\<lambda>y. norm (slp_cauchy_integrand orientation (h n) z y))"
      by (rule Bochner_Integration.integrable_norm[OF integrand_integrable])
    have nn_as_real:
        "(\<integral>\<^sup>+y.
          norm (slp_cauchy_integrand orientation (h n) z y) \<partial>lborel) =
        ennreal (\<integral>y.
          norm (slp_cauchy_integrand orientation (h n) z y) \<partial>lborel)"
      by (rule nn_integral_eq_integral[OF norm_integrable]) simp
    show "(\<integral>\<^sup>+y.
          norm (slp_cauchy_integrand orientation (h n) z y) \<partial>lborel)
        \<le> ennreal (\<integral>y.
          (a n * slp_localized_cauchy_kernel R (z - y)) powr ?q / ?q +
          (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel)"
      unfolding nn_as_real
      by (rule ennreal_leI) (use bounds[of n] in blast)
  qed
  show ?thesis
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and
          h = "\<lambda>n. ennreal (\<integral>y.
            (a n * slp_localized_cauchy_kernel R (z - y)) powr ?q / ?q +
            (inverse (a n) * norm (h n y)) powr b / b \<partial>lborel)"])
       (use upper_bound rhs_limit in auto)
qed

end
