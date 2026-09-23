theory Inverse_Schrodinger_Lp_Born_Branch_Base_Mass
  imports
    Inverse_Schrodinger_Lp_Born_Branch_Mass_Bound
    Inverse_Schrodinger_Lp_Localized_Cauchy_Endpoint
begin

section \<open>Unweighted zero-order branch mass\<close>

theorem slp_positive_branch_mass_zero_unweighted_le:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) 0
        origin (\<lambda>_. 1) \<le>
      ennreal (inverse pi) *
        (\<integral>\<^sup>+ x.
          ennreal (slp_localized_cauchy_kernel R (origin - x))
          \<partial>lborel) * ennreal C"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  have kernel_measurable[measurable]:
      "(\<lambda>x. ennreal (slp_localized_cauchy_kernel R (origin - x)))
        \<in> borel_measurable lborel"
    by measurable
  have cutoff_norm_measurable[measurable]:
      "(\<lambda>x. ennreal (norm (cutoff x))) \<in> borel_measurable lborel"
    using cutoff_measurable by measurable
  have pointwise:
      "ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - x)) *
          ennreal (norm (cutoff x)) \<le>
        ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - x)) * ennreal C"
    for x
  proof -
    have norm_le: "ennreal (norm (cutoff x)) \<le> ennreal C"
      by (rule ennreal_leI; rule cutoff_bound)
    show ?thesis
      by (rule mult_left_mono[OF norm_le]) simp
  qed
  have integral_le:
      "(\<integral>\<^sup>+ x.
          ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - x)) *
          ennreal (norm (cutoff x))
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ x.
          ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - x)) * ennreal C
          \<partial>lborel)"
    by (rule nn_integral_mono) (simp add: pointwise)
  have scaled_integral:
      "(\<integral>\<^sup>+ x.
          ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - x)) * ennreal C
          \<partial>lborel) =
        ennreal (inverse pi) *
          (\<integral>\<^sup>+ x.
            ennreal (slp_localized_cauchy_kernel R (origin - x))
            \<partial>lborel) * ennreal C"
  proof -
    have inner_measurable:
        "(\<lambda>x.
            ennreal (slp_localized_cauchy_kernel R (origin - x)) * ennreal C)
          \<in> borel_measurable lborel"
      by measurable
    show ?thesis
      by (simp only: mult.assoc nn_integral_cmult[OF inner_measurable]
          nn_integral_multc[OF kernel_measurable])
  qed
  show ?thesis
    unfolding slp_positive_branch_mass_zero
    using integral_le scaled_integral by simp
qed

corollary slp_positive_branch_mass_zero_unweighted_less_top:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) 0
        origin (\<lambda>_. 1) < top"
proof -
  have power_integrable:
      "integrable lborel
        (\<lambda>x.
          abs (slp_localized_cauchy_kernel R (origin - x)) powr 1)"
    by (rule slp_localized_cauchy_kernel_power_translate_integrable) simp_all
  have kernel_integrable:
      "integrable lborel
        (\<lambda>x. slp_localized_cauchy_kernel R (origin - x))"
    using power_integrable
    by (simp add: slp_localized_cauchy_kernel_nonnegative)
  have kernel_finite:
      "(\<integral>\<^sup>+ x.
          ennreal (slp_localized_cauchy_kernel R (origin - x))
          \<partial>lborel) < top"
    using kernel_integrable
    unfolding integrable_iff_bounded
    by (simp add: slp_localized_cauchy_kernel_nonnegative)
  have bound:
      "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) 0
          origin (\<lambda>_. 1) \<le>
        ennreal (inverse pi) *
          (\<integral>\<^sup>+ x.
            ennreal (slp_localized_cauchy_kernel R (origin - x))
            \<partial>lborel) * ennreal C"
    by (rule slp_positive_branch_mass_zero_unweighted_le[OF
          cutoff_measurable cutoff_bound C_nonnegative])
  have rhs_finite:
      "ennreal (inverse pi) *
          (\<integral>\<^sup>+ x.
            ennreal (slp_localized_cauchy_kernel R (origin - x))
            \<partial>lborel) * ennreal C < top"
    using kernel_finite by (simp add: ennreal_mult_less_top)
  show ?thesis
    by (rule order_le_less_trans[OF bound rhs_finite])
qed

end
