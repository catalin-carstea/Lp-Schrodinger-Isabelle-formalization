theory Inverse_Schrodinger_Lp_Born_One_Sided_Zero_Riesz
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Riesz_L2
begin

section \<open>The order-zero one-sided positive density\<close>

lemma slp_localized_cauchy_kernel_reflect:
  "slp_localized_cauchy_kernel R (x - y) =
    slp_localized_cauchy_kernel R (y - x)"
  unfolding slp_localized_cauchy_kernel_def
  by (simp add: norm_minus_commute)

lemma slp_positive_root_output_density_zero_riesz:
  assumes root_integrable:
    "integrable lborel
      (slp_localized_riesz_integrand R root_weight output)"
  shows
    "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) 0
        root_weight output =
      ennreal (inverse pi * norm (cutoff output) *
        slp_localized_riesz_potential R root_weight output)"
proof -
  let ?integrand = "slp_localized_riesz_integrand R root_weight output"
  have integrand_nonnegative: "AE root in lborel. 0 \<le> ?integrand root"
    by (rule AE_I2)
       (rule slp_localized_riesz_integrand_nonnegative)
  have positive_integral:
      "(\<integral>\<^sup>+ root. ennreal (?integrand root) \<partial>lborel) =
        ennreal (slp_localized_riesz_potential R root_weight output)"
    unfolding slp_localized_riesz_potential_def
    by (rule nn_integral_eq_integral[OF root_integrable
          integrand_nonnegative])
  have integrand_identity:
      "(\<lambda>root.
          ennreal (norm (root_weight root)) *
            (ennreal (inverse pi) *
              ennreal (slp_localized_cauchy_kernel R (root - output)) *
              ennreal (norm (cutoff output)) * 1)) =
        (\<lambda>root.
          (ennreal (inverse pi) * ennreal (norm (cutoff output))) *
            ennreal (?integrand root))"
  proof (rule ext)
    fix root :: slp_point
    have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel R (output - root)"
      by (rule slp_localized_cauchy_kernel_nonnegative)
    show "ennreal (norm (root_weight root)) *
          (ennreal (inverse pi) *
            ennreal (slp_localized_cauchy_kernel R (root - output)) *
            ennreal (norm (cutoff output)) * 1) =
        (ennreal (inverse pi) * ennreal (norm (cutoff output))) *
          ennreal (?integrand root)"
      unfolding slp_localized_riesz_integrand_def
      using kernel_nonnegative
      by (simp add: slp_localized_cauchy_kernel_reflect ennreal_mult
          mult.commute mult.left_commute mult.assoc)
  qed
  have integrand_measurable:
      "(\<lambda>root. ennreal (?integrand root))
        \<in> borel_measurable lborel"
    using root_integrable by measurable
  have density_zero:
      "slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
          root output =
        ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (root - output)) *
          ennreal (norm (cutoff output)) * 1"
    for root
    by simp
  have density_factor:
      "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) 0
          root_weight output =
        (ennreal (inverse pi) * ennreal (norm (cutoff output))) *
          (\<integral>\<^sup>+ root. ennreal (?integrand root) \<partial>lborel)"
    unfolding slp_positive_root_output_density_def
    apply (simp only: density_zero integrand_identity)
    by (rule nn_integral_cmult[OF integrand_measurable])
  have potential_nonnegative:
      "0 \<le> slp_localized_riesz_potential R root_weight output"
    by (rule slp_localized_riesz_potential_nonnegative)
  show ?thesis
    using density_factor positive_integral potential_nonnegative
    by (simp add: ennreal_mult mult.assoc)
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_zero_riesz_AE:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_support: "bounded {x. root_weight x \<noteq> 0}"
  shows
    "AE output in lborel.
      slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) 0
          root_weight output =
        ennreal (inverse pi * norm (cutoff output) *
          slp_localized_riesz_potential R root_weight output)"
proof -
  have fibers:
      "AE output in lborel.
        integrable lborel
          (slp_localized_riesz_integrand R root_weight output)"
    using slp_localized_riesz_l2_compact_lp[OF radius_nonnegative p_lower
      p_upper root_weight_lp root_weight_support]
    by blast
  show ?thesis
  proof (rule eventually_mono[OF fibers])
    fix z :: slp_point
    assume root_integrable:
      "integrable lborel
        (slp_localized_riesz_integrand R root_weight z)"
    show "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) 0
          root_weight z =
        ennreal (inverse pi * norm (cutoff z) *
          slp_localized_riesz_potential R root_weight z)"
      by (rule slp_positive_root_output_density_zero_riesz[OF
            root_integrable])
  qed
qed

end

end
