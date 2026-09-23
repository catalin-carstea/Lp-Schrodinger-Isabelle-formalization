theory Inverse_Schrodinger_Lp_Annular_J2_Full_Bounds
  imports Inverse_Schrodinger_Lp_Annular_J1_Full_Bounds
begin

section \<open>The full square-denominator complementary term\<close>

definition slp_annular_J2_full_integrand ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_annular_J2_full_integrand delta R z y =
    (if delta \<le> norm y \<and> norm y \<le> R \<and>
        delta \<le> norm (z - y) then
      slp_radial_inverse (z - y) * slp_radial_inverse_square y
    else 0)"

lemma slp_annular_J2_full_integrand_borel_measurable [measurable]:
  "slp_annular_J2_full_integrand delta R z \<in> borel_measurable lborel"
  unfolding slp_annular_J2_full_integrand_def by measurable

lemma slp_annular_J2_full_integrand_nonnegative [simp]:
  "0 \<le> slp_annular_J2_full_integrand delta R z y"
  unfolding slp_annular_J2_full_integrand_def by simp

lemma slp_annular_J2_full_pointwise_majorant:
  assumes delta_positive: "0 < delta"
  shows "slp_annular_J2_full_integrand delta R z y \<le>
    (1 / delta) * slp_squared_radial_annulus delta R y"
proof (cases "delta \<le> norm y \<and> norm y \<le> R \<and>
    delta \<le> norm (z - y)")
  case True
  have reduction:
    "slp_radial_inverse (z - y) * slp_radial_inverse_square y \<le>
      (1 / delta) * slp_radial_inverse_square y"
    by (rule slp_annular_J2_kernel_reduction[OF delta_positive])
      (use True in simp)
  have annulus:
    "slp_squared_radial_annulus delta R y =
      slp_radial_inverse_square y"
    using True by (simp add: slp_squared_radial_annulus_def)
  show ?thesis
    using reduction True annulus
    by (simp add: slp_annular_J2_full_integrand_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_annular_J2_full_integrand_def False)
qed

lemma slp_annular_J2_full_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_annular_J2_full_integrand delta R z)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_squared_radial_annulus delta R y"
  have annulus_integrable:
    "integrable lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_squared_radial_annulus_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    using annulus_integrable by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_annular_J2_full_integrand delta R z \<in>
        borel_measurable lborel"
      by (rule slp_annular_J2_full_integrand_borel_measurable)
    show "AE y in lborel.
        norm (slp_annular_J2_full_integrand delta R z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_annular_J2_full_integrand delta R z y \<le> ?majorant y"
        by (rule slp_annular_J2_full_pointwise_majorant[OF delta_positive])
      have annulus_nonnegative:
        "0 \<le> slp_squared_radial_annulus delta R y"
        by simp
      have integrand_norm:
        "norm (slp_annular_J2_full_integrand delta R z y) =
          slp_annular_J2_full_integrand delta R z y"
        by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using annulus_nonnegative delta_positive by simp
      show "norm (slp_annular_J2_full_integrand delta R z y) \<le>
          norm (?majorant y)"
        using domination integrand_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_annular_J2_full_integral_radial_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel
      (slp_annular_J2_full_integrand delta R z) \<le>
    (1 / delta) *
      integral\<^sup>L lborel (slp_squared_radial_annulus delta R)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_squared_radial_annulus delta R y"
  have integrand_integrable:
    "integrable lborel (slp_annular_J2_full_integrand delta R z)"
    by (rule slp_annular_J2_full_integrable[OF delta_positive])
  have annulus_integrable:
    "integrable lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_squared_radial_annulus_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    using annulus_integrable by (rule integrable_mult_right)
  have bound:
    "integral\<^sup>L lborel
        (slp_annular_J2_full_integrand delta R z) \<le>
      integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono[OF integrand_integrable
        majorant_integrable])
    fix y :: slp_point
    assume "y \<in> space lborel"
    show "slp_annular_J2_full_integrand delta R z y \<le> ?majorant y"
      by (rule slp_annular_J2_full_pointwise_majorant[OF delta_positive])
  qed
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      (1 / delta) *
        integral\<^sup>L lborel (slp_squared_radial_annulus delta R)"
    using annulus_integrable by simp
  show ?thesis
    using bound majorant_integral by linarith
qed

lemma slp_annular_J2_full_logarithmic_bound:
  assumes delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
  shows "integral\<^sup>L lborel
      (slp_annular_J2_full_integrand delta R z) \<le>
    (1 / delta) * (1 + log 2 (R / delta)) *
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have radial_bound:
    "integral\<^sup>L lborel
        (slp_annular_J2_full_integrand delta R z) \<le>
      (1 / delta) *
        integral\<^sup>L lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_annular_J2_full_integral_radial_bound[OF delta_positive])
  have annulus_bound:
    "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) \<le>
      (1 + log 2 (R / delta)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule slp_squared_radial_annulus_rescaled_logarithmic_majorant[OF
          delta_positive normalized_lower])
  have coefficient_nonnegative: "0 \<le> 1 / delta"
    using delta_positive by simp
  have scaled_annulus_bound:
    "(1 / delta) *
        integral\<^sup>L lborel (slp_squared_radial_annulus delta R) \<le>
      (1 / delta) * ((1 + log 2 (R / delta)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
    by (rule mult_left_mono[OF annulus_bound coefficient_nonnegative])
  show ?thesis
    using radial_bound scaled_annulus_bound
    by (simp add: algebra_simps)
qed

lemma slp_J2_full_amplitude_weighted_logarithmic_bound:
  assumes delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and M_nonnegative: "0 \<le> M"
  shows "M * integral\<^sup>L lborel
      (slp_annular_J2_full_integrand delta R z) \<le>
    (M / delta) * (1 + log 2 (R / delta)) *
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have weighted:
    "M * integral\<^sup>L lborel
        (slp_annular_J2_full_integrand delta R z) \<le>
      M * ((1 / delta) * (1 + log 2 (R / delta)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
    by (rule mult_left_mono[OF
          slp_annular_J2_full_logarithmic_bound[OF
            delta_positive normalized_lower]
          M_nonnegative])
  show ?thesis
    using weighted by (simp add: algebra_simps)
qed

end
