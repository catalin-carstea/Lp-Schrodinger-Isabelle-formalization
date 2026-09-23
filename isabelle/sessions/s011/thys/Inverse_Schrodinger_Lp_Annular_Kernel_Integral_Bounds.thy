theory Inverse_Schrodinger_Lp_Annular_Kernel_Integral_Bounds
  imports Inverse_Schrodinger_Lp_Localized_Cauchy_Scaling
begin

section \<open>Ordinary-integral bounds for three annular pieces\<close>

lemma slp_radial_inverse_borel_measurable[measurable]:
  "slp_radial_inverse \<in> borel_measurable lborel"
  unfolding slp_radial_inverse_def by measurable

lemma slp_radial_inverse_square_borel_measurable[measurable]:
  "slp_radial_inverse_square \<in> borel_measurable lborel"
  unfolding slp_radial_inverse_square_def by measurable

lemma slp_localized_cauchy_kernel_reflected_translate_integral:
  "integral\<^sup>L lborel
      (\<lambda>y. slp_localized_cauchy_kernel R (z - y)) =
    integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
proof -
  have translated:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (-z + y)) =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
    by (rule slp_lborel_integral_translate[OF
          slp_localized_cauchy_kernel_integrable])
  have reflected:
    "(\<lambda>y. slp_localized_cauchy_kernel R (z - y)) =
      (\<lambda>y. slp_localized_cauchy_kernel R (-z + y))"
  proof (rule ext)
    fix y :: slp_point
    show "slp_localized_cauchy_kernel R (z - y) =
        slp_localized_cauchy_kernel R (-z + y)"
      unfolding slp_localized_cauchy_kernel_def
      by (simp add: norm_minus_commute algebra_simps)
  qed
  show ?thesis
    using translated reflected by simp
qed

definition slp_annular_I1_integrand ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_annular_I1_integrand delta z y =
    (if delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
        norm (z - y) \<le> delta then
      slp_radial_inverse (z - y) * slp_radial_inverse y
    else 0)"

definition slp_annular_I2_integrand ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_annular_I2_integrand delta z y =
    (if delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
        delta \<le> norm (z - y) then
      slp_radial_inverse (z - y) * slp_radial_inverse y
    else 0)"

definition slp_annular_J1_integrand ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_annular_J1_integrand delta z y =
    (if delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
        norm (z - y) \<le> delta then
      slp_radial_inverse (z - y) * slp_radial_inverse_square y
    else 0)"

lemma slp_annular_I1_integrand_borel_measurable[measurable]:
  "slp_annular_I1_integrand delta z \<in> borel_measurable lborel"
  unfolding slp_annular_I1_integrand_def by measurable

lemma slp_annular_I2_integrand_borel_measurable[measurable]:
  "slp_annular_I2_integrand delta z \<in> borel_measurable lborel"
  unfolding slp_annular_I2_integrand_def by measurable

lemma slp_annular_J1_integrand_borel_measurable[measurable]:
  "slp_annular_J1_integrand delta z \<in> borel_measurable lborel"
  unfolding slp_annular_J1_integrand_def by measurable

lemma slp_annular_I1_integrand_nonnegative [simp]:
  "0 \<le> slp_annular_I1_integrand delta z y"
  unfolding slp_annular_I1_integrand_def by simp

lemma slp_annular_I2_integrand_nonnegative [simp]:
  "0 \<le> slp_annular_I2_integrand delta z y"
  unfolding slp_annular_I2_integrand_def by simp

lemma slp_annular_J1_integrand_nonnegative [simp]:
  "0 \<le> slp_annular_J1_integrand delta z y"
  unfolding slp_annular_J1_integrand_def by simp

lemma slp_annular_I1_pointwise_majorant:
  assumes delta_positive: "0 < delta"
  shows "slp_annular_I1_integrand delta z y \<le>
    (1 / delta) * slp_localized_cauchy_kernel delta (z - y)"
proof (cases "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
    norm (z - y) \<le> delta")
  case True
  have reduction:
    "slp_radial_inverse (z - y) * slp_radial_inverse y \<le>
      (1 / delta) * slp_radial_inverse (z - y)"
    by (rule slp_annular_I1_kernel_reduction[OF delta_positive])
      (use True in simp)
  have kernel:
    "slp_localized_cauchy_kernel delta (z - y) =
      slp_radial_inverse (z - y)"
    using True
    by (simp add: slp_localized_cauchy_kernel_def
        slp_radial_inverse_def)
  show ?thesis
    using reduction True kernel
    by (simp add: slp_annular_I1_integrand_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_annular_I1_integrand_def False
        slp_localized_cauchy_kernel_nonnegative)
qed

lemma slp_annular_I2_pointwise_majorant:
  assumes delta_positive: "0 < delta"
  shows "slp_annular_I2_integrand delta z y \<le>
    (1 / delta) * slp_localized_cauchy_kernel (2 * delta) y"
proof (cases "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
    delta \<le> norm (z - y)")
  case True
  have reduction:
    "slp_radial_inverse (z - y) * slp_radial_inverse y \<le>
      (1 / delta) * slp_radial_inverse y"
    by (rule slp_annular_I2_kernel_reduction[OF delta_positive])
      (use True in simp)
  have kernel:
    "slp_localized_cauchy_kernel (2 * delta) y = slp_radial_inverse y"
    using True
    by (simp add: slp_localized_cauchy_kernel_def
        slp_radial_inverse_def)
  show ?thesis
    using reduction True kernel
    by (simp add: slp_annular_I2_integrand_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_annular_I2_integrand_def False
        slp_localized_cauchy_kernel_nonnegative)
qed

lemma slp_annular_J1_pointwise_majorant:
  assumes delta_positive: "0 < delta"
  shows "slp_annular_J1_integrand delta z y \<le>
    (1 / delta ^ 2) * slp_localized_cauchy_kernel delta (z - y)"
proof (cases "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
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
    by (simp add: slp_annular_J1_integrand_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_annular_J1_integrand_def False
        slp_localized_cauchy_kernel_nonnegative)
qed

lemma slp_annular_I1_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_annular_I1_integrand delta z)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_localized_cauchy_kernel delta (z - y)"
  have translated: "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel delta (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using translated by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_annular_I1_integrand delta z \<in> borel_measurable lborel"
      by (rule slp_annular_I1_integrand_borel_measurable)
    show "AE y in lborel.
        norm (slp_annular_I1_integrand delta z y) \<le> norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_annular_I1_integrand delta z y \<le> ?majorant y"
        by (rule slp_annular_I1_pointwise_majorant[OF delta_positive])
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using delta_positive slp_localized_cauchy_kernel_nonnegative[of
          delta "z - y"] by simp
      have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel delta (z - y)"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have integrand_norm:
        "norm (slp_annular_I1_integrand delta z y) =
          slp_annular_I1_integrand delta z y"
        by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using kernel_nonnegative delta_positive by simp
      show "norm (slp_annular_I1_integrand delta z y) \<le>
          norm (?majorant y)"
        using domination integrand_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_annular_I2_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_annular_I2_integrand delta z)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_localized_cauchy_kernel (2 * delta) y"
  have kernel_integrable:
    "integrable lborel (slp_localized_cauchy_kernel (2 * delta))"
    by (rule slp_localized_cauchy_kernel_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_integrable by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_annular_I2_integrand delta z \<in> borel_measurable lborel"
      by (rule slp_annular_I2_integrand_borel_measurable)
    show "AE y in lborel.
        norm (slp_annular_I2_integrand delta z y) \<le> norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_annular_I2_integrand delta z y \<le> ?majorant y"
        by (rule slp_annular_I2_pointwise_majorant[OF delta_positive])
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using delta_positive slp_localized_cauchy_kernel_nonnegative[of
          "2 * delta" y] by simp
      have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel (2 * delta) y"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have integrand_norm:
        "norm (slp_annular_I2_integrand delta z y) =
          slp_annular_I2_integrand delta z y"
        by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using kernel_nonnegative delta_positive by simp
      show "norm (slp_annular_I2_integrand delta z y) \<le>
          norm (?majorant y)"
        using domination integrand_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_annular_J1_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_annular_J1_integrand delta z)"
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
    show "slp_annular_J1_integrand delta z \<in> borel_measurable lborel"
      by (rule slp_annular_J1_integrand_borel_measurable)
    show "AE y in lborel.
        norm (slp_annular_J1_integrand delta z y) \<le> norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_annular_J1_integrand delta z y \<le> ?majorant y"
        by (rule slp_annular_J1_pointwise_majorant[OF delta_positive])
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using delta_positive slp_localized_cauchy_kernel_nonnegative[of
          delta "z - y"] by simp
      have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel delta (z - y)"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have integrand_norm:
        "norm (slp_annular_J1_integrand delta z y) =
          slp_annular_J1_integrand delta z y"
        by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using kernel_nonnegative delta_positive by simp
      show "norm (slp_annular_J1_integrand delta z y) \<le>
          norm (?majorant y)"
        using domination integrand_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_annular_I1_integral_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel (slp_annular_I1_integrand delta z) \<le>
    integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_localized_cauchy_kernel delta (z - y)"
  have integrand_integrable:
    "integrable lborel (slp_annular_I1_integrand delta z)"
    by (rule slp_annular_I1_integrable[OF delta_positive])
  have translated: "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel delta (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using translated by (rule integrable_mult_right)
  have bound:
    "integral\<^sup>L lborel (slp_annular_I1_integrand delta z) \<le>
      integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono[OF integrand_integrable
        majorant_integrable])
    fix x :: slp_point
    assume "x \<in> space lborel"
    show "slp_annular_I1_integrand delta z x \<le> ?majorant x"
      by (rule slp_annular_I1_pointwise_majorant[OF delta_positive])
  qed
  have translated_integral:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_localized_cauchy_kernel delta (z - y)) =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel delta)"
    by (rule slp_localized_cauchy_kernel_reflected_translate_integral)
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    using translated translated_integral
      slp_localized_cauchy_kernel_integral_delta_normalized[OF
        delta_positive]
    by simp
  show ?thesis
    using bound majorant_integral by linarith
qed

lemma slp_annular_I2_integral_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel (slp_annular_I2_integrand delta z) \<le>
    2 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_localized_cauchy_kernel (2 * delta) y"
  have integrand_integrable:
    "integrable lborel (slp_annular_I2_integrand delta z)"
    by (rule slp_annular_I2_integrable[OF delta_positive])
  have kernel_integrable:
    "integrable lborel (slp_localized_cauchy_kernel (2 * delta))"
    by (rule slp_localized_cauchy_kernel_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_integrable by (rule integrable_mult_right)
  have bound:
    "integral\<^sup>L lborel (slp_annular_I2_integrand delta z) \<le>
      integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono[OF integrand_integrable
        majorant_integrable])
    fix x :: slp_point
    assume "x \<in> space lborel"
    show "slp_annular_I2_integrand delta z x \<le> ?majorant x"
      by (rule slp_annular_I2_pointwise_majorant[OF delta_positive])
  qed
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      2 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    using kernel_integrable
      slp_localized_cauchy_kernel_integral_two_delta_normalized[OF
        delta_positive]
    by simp
  show ?thesis
    using bound majorant_integral by linarith
qed

lemma slp_annular_J1_integral_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel (slp_annular_J1_integrand delta z) \<le>
    (1 / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta ^ 2) *
    slp_localized_cauchy_kernel delta (z - y)"
  have integrand_integrable:
    "integrable lborel (slp_annular_J1_integrand delta z)"
    by (rule slp_annular_J1_integrable[OF delta_positive])
  have translated: "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel delta (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using translated by (rule integrable_mult_right)
  have bound:
    "integral\<^sup>L lborel (slp_annular_J1_integrand delta z) \<le>
      integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono[OF integrand_integrable
        majorant_integrable])
    fix x :: slp_point
    assume "x \<in> space lborel"
    show "slp_annular_J1_integrand delta z x \<le> ?majorant x"
      by (rule slp_annular_J1_pointwise_majorant[OF delta_positive])
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

end
