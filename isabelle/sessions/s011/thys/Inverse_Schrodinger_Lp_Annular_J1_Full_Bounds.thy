theory Inverse_Schrodinger_Lp_Annular_J1_Full_Bounds
  imports Inverse_Schrodinger_Lp_Annulus_Logarithmic_Growth
begin

section \<open>The full square-denominator near-output term\<close>

definition slp_annular_J1_full_integrand ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_annular_J1_full_integrand delta R z y =
    (if delta \<le> norm y \<and> norm y \<le> R \<and>
        norm (z - y) \<le> delta then
      slp_radial_inverse (z - y) * slp_radial_inverse_square y
    else 0)"

lemma slp_annular_J1_full_integrand_borel_measurable [measurable]:
  "slp_annular_J1_full_integrand delta R z \<in> borel_measurable lborel"
  unfolding slp_annular_J1_full_integrand_def by measurable

lemma slp_annular_J1_full_integrand_nonnegative [simp]:
  "0 \<le> slp_annular_J1_full_integrand delta R z y"
  unfolding slp_annular_J1_full_integrand_def by simp

lemma slp_annular_J1_full_pointwise_majorant:
  assumes delta_positive: "0 < delta"
  shows "slp_annular_J1_full_integrand delta R z y \<le>
    (1 / delta ^ 2) * slp_localized_cauchy_kernel delta (z - y)"
proof (cases "delta \<le> norm y \<and> norm y \<le> R \<and>
    norm (z - y) \<le> delta")
  case True
  have reduction:
    "slp_radial_inverse (z - y) * slp_radial_inverse_square y \<le>
      (1 / delta ^ 2) * slp_radial_inverse (z - y)"
    by (rule slp_annular_J1_kernel_reduction[OF delta_positive])
      (use True in simp)
  have kernel:
    "slp_localized_cauchy_kernel delta (z - y) =
      slp_radial_inverse (z - y)"
    using True
    by (simp add: slp_localized_cauchy_kernel_def
        slp_radial_inverse_def)
  show ?thesis
    using reduction True kernel
    by (simp add: slp_annular_J1_full_integrand_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_annular_J1_full_integrand_def False
        slp_localized_cauchy_kernel_nonnegative)
qed

lemma slp_annular_J1_full_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_annular_J1_full_integrand delta R z)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta ^ 2) *
    slp_localized_cauchy_kernel delta (z - y)"
  have translated: "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel delta (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using translated by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_annular_J1_full_integrand delta R z \<in>
        borel_measurable lborel"
      by (rule slp_annular_J1_full_integrand_borel_measurable)
    show "AE y in lborel.
        norm (slp_annular_J1_full_integrand delta R z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_annular_J1_full_integrand delta R z y \<le> ?majorant y"
        by (rule slp_annular_J1_full_pointwise_majorant[OF delta_positive])
      have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel delta (z - y)"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have integrand_norm:
        "norm (slp_annular_J1_full_integrand delta R z y) =
          slp_annular_J1_full_integrand delta R z y"
        by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using kernel_nonnegative delta_positive by simp
      show "norm (slp_annular_J1_full_integrand delta R z y) \<le>
          norm (?majorant y)"
        using domination integrand_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_annular_J1_full_integral_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel
      (slp_annular_J1_full_integrand delta R z) \<le>
    (1 / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta ^ 2) *
    slp_localized_cauchy_kernel delta (z - y)"
  have integrand_integrable:
    "integrable lborel (slp_annular_J1_full_integrand delta R z)"
    by (rule slp_annular_J1_full_integrable[OF delta_positive])
  have translated: "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel delta (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using translated by (rule integrable_mult_right)
  have bound:
    "integral\<^sup>L lborel
        (slp_annular_J1_full_integrand delta R z) \<le>
      integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono[OF integrand_integrable
        majorant_integrable])
    fix y :: slp_point
    assume "y \<in> space lborel"
    show "slp_annular_J1_full_integrand delta R z y \<le> ?majorant y"
      by (rule slp_annular_J1_full_pointwise_majorant[OF delta_positive])
  qed
  have translated_integral:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_localized_cauchy_kernel delta (z - y)) =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel delta)"
    by (rule slp_localized_cauchy_kernel_reflected_translate_integral)
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      (1 / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    using translated translated_integral
      slp_localized_cauchy_kernel_integral_delta_square_normalized[OF
        delta_positive]
    by simp
  show ?thesis
    using bound majorant_integral by linarith
qed

lemma slp_J1_full_amplitude_weighted_bound:
  assumes delta_positive: "0 < delta"
    and M_nonnegative: "0 \<le> M"
  shows "M * integral\<^sup>L lborel
      (slp_annular_J1_full_integrand delta R z) \<le>
    (M / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have weighted:
    "M * integral\<^sup>L lborel
        (slp_annular_J1_full_integrand delta R z) \<le>
      M * ((1 / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1))"
    by (rule mult_left_mono[OF
          slp_annular_J1_full_integral_bound[OF delta_positive]
          M_nonnegative])
  show ?thesis
    using weighted by (simp add: algebra_simps)
qed

lemma slp_checked_annular_weighted_sum_full_J1_bound:
  assumes delta_positive: "0 < delta"
    and L_nonnegative: "0 \<le> L"
    and M_nonnegative: "0 \<le> M"
  shows "(L / delta) * M *
        (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
          integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) +
      M * integral\<^sup>L lborel
        (slp_annular_J1_full_integrand delta R z) \<le>
    ((3 * L + 1) * M / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have cutoff:
    "(L / delta) * M *
        (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
          integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) \<le>
      (3 * L * M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_cutoff_annular_weighted_bound[OF
          delta_positive L_nonnegative M_nonnegative])
  have square_near:
    "M * integral\<^sup>L lborel
        (slp_annular_J1_full_integrand delta R z) \<le>
      (M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_J1_full_amplitude_weighted_bound[OF
          delta_positive M_nonnegative])
  have identity:
    "(3 * L * M / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (M / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) =
      ((3 * L + 1) * M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (simp add: algebra_simps add_divide_distrib)
  show ?thesis
    using cutoff square_near identity by linarith
qed

end
