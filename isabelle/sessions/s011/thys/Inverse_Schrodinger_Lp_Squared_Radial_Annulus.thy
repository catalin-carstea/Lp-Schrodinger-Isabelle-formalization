theory Inverse_Schrodinger_Lp_Squared_Radial_Annulus
  imports Inverse_Schrodinger_Lp_Annular_Weighted_Bounds
begin

section \<open>The squared inverse-radius annulus\<close>

definition slp_squared_radial_annulus ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_squared_radial_annulus delta R y =
    (if delta \<le> norm y \<and> norm y \<le> R then
      slp_radial_inverse_square y
    else 0)"

lemma slp_squared_radial_annulus_borel_measurable[measurable]:
  "slp_squared_radial_annulus delta R \<in> borel_measurable lborel"
  unfolding slp_squared_radial_annulus_def by measurable

lemma slp_squared_radial_annulus_nonnegative [simp]:
  "0 \<le> slp_squared_radial_annulus delta R y"
  unfolding slp_squared_radial_annulus_def by simp

lemma slp_squared_radial_annulus_pointwise_majorant:
  assumes delta_positive: "0 < delta"
  shows "slp_squared_radial_annulus delta R y \<le>
    (1 / delta) * slp_localized_cauchy_kernel R y"
proof (cases "delta \<le> norm y \<and> norm y \<le> R")
  case True
  have radial:
    "slp_radial_inverse y \<le> 1 / delta"
    by (rule slp_radial_inverse_bound[OF delta_positive])
      (use True in simp)
  have reduction:
    "slp_radial_inverse_square y \<le>
      (1 / delta) * slp_radial_inverse y"
    unfolding slp_radial_inverse_square_def power2_eq_square
    by (rule mult_right_mono[OF radial]) simp
  have kernel:
    "slp_localized_cauchy_kernel R y = slp_radial_inverse y"
    using True
    by (simp add: slp_localized_cauchy_kernel_def slp_radial_inverse_def)
  show ?thesis
    using True reduction kernel
    by (simp add: slp_squared_radial_annulus_def)
next
  case False
  show ?thesis
    using delta_positive
    by (simp add: slp_squared_radial_annulus_def False
        slp_localized_cauchy_kernel_nonnegative)
qed

lemma slp_squared_radial_annulus_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_squared_radial_annulus delta R)"
proof -
  let ?majorant = "\<lambda>y. (1 / delta) *
    slp_localized_cauchy_kernel R y"
  have kernel_integrable:
    "integrable lborel (slp_localized_cauchy_kernel R)"
    by (rule slp_localized_cauchy_kernel_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_integrable by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_squared_radial_annulus delta R \<in> borel_measurable lborel"
      by (rule slp_squared_radial_annulus_borel_measurable)
    show "AE y in lborel.
        norm (slp_squared_radial_annulus delta R y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have domination:
        "slp_squared_radial_annulus delta R y \<le> ?majorant y"
        by (rule slp_squared_radial_annulus_pointwise_majorant[
              OF delta_positive])
      have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel R y"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using delta_positive kernel_nonnegative by simp
      have annulus_norm:
        "norm (slp_squared_radial_annulus delta R y) =
          slp_squared_radial_annulus delta R y"
        by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using kernel_nonnegative delta_positive by simp
      show "norm (slp_squared_radial_annulus delta R y) \<le>
          norm (?majorant y)"
        using domination annulus_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_radial_inverse_square_scale:
  assumes scale_positive: "0 < a"
  shows "slp_radial_inverse_square (a *\<^sub>R y) =
    inverse (a ^ 2) * slp_radial_inverse_square y"
  unfolding slp_radial_inverse_square_def slp_radial_inverse_def
  using scale_positive
  by (simp add: norm_scaleR abs_of_pos inverse_mult_distrib
      power_mult_distrib power_inverse)

lemma slp_squared_radial_annulus_scale:
  assumes scale_positive: "0 < a"
  shows "slp_squared_radial_annulus (a * delta) (a * R) (a *\<^sub>R y) =
    inverse (a ^ 2) * slp_squared_radial_annulus delta R y"
proof -
  have lower:
    "(a * delta \<le> norm (a *\<^sub>R y)) = (delta \<le> norm y)"
    using scale_positive by (simp add: norm_scaleR abs_of_pos)
  have upper:
    "(norm (a *\<^sub>R y) \<le> a * R) = (norm y \<le> R)"
    using scale_positive by (simp add: norm_scaleR abs_of_pos)
  show ?thesis
    unfolding slp_squared_radial_annulus_def
    using lower upper slp_radial_inverse_square_scale[OF scale_positive, of y]
    by simp
qed

lemma slp_squared_radial_annulus_integral_scale:
  assumes scale_positive: "0 < a"
    and delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel
      (slp_squared_radial_annulus (a * delta) (a * R)) =
    integral\<^sup>L lborel (slp_squared_radial_annulus delta R)"
proof -
  let ?g = "(*\<^sub>R) a :: slp_point \<Rightarrow> slp_point"
  have scale_linear: "linear ?g"
    by (rule bounded_linear.linear[OF bounded_linear_scaleR_right])
  have scale_injective: "inj ?g"
  proof (rule injI)
    fix x y :: slp_point
    assume "a *\<^sub>R x = a *\<^sub>R y"
    with scale_positive show "x = y" by simp
  qed
  have target_integrable:
    "integrable lborel
      (slp_squared_radial_annulus (a * delta) (a * R))"
    by (rule slp_squared_radial_annulus_integrable)
      (use scale_positive delta_positive in simp)
  have jacobian:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus (a * delta) (a * R)) =
      \<bar>det (matrix ?g)\<bar> *\<^sub>R
        integral\<^sup>L lborel
          (\<lambda>y. slp_squared_radial_annulus
            (a * delta) (a * R) (?g y))"
    by (rule slp_lborel_linear_pullback(2)[OF scale_linear
          scale_injective target_integrable])
  have determinant: "\<bar>det (matrix ?g)\<bar> = a ^ 2"
    using scale_positive by simp
  have pullback_eq:
    "(\<lambda>y. slp_squared_radial_annulus
        (a * delta) (a * R) (?g y)) =
      (\<lambda>y. inverse (a ^ 2) *
        slp_squared_radial_annulus delta R y)"
    by (rule ext) (rule slp_squared_radial_annulus_scale[OF
          scale_positive])
  have source_integrable:
    "integrable lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_squared_radial_annulus_integrable[OF delta_positive])
  have inverse_nonzero: "inverse (a ^ 2) \<noteq> 0"
    using scale_positive by simp
  have square_nonzero: "a ^ 2 \<noteq> 0"
    using scale_positive by simp
  have pulled_integral:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_squared_radial_annulus
          (a * delta) (a * R) (?g y)) =
      inverse (a ^ 2) *
        integral\<^sup>L lborel (slp_squared_radial_annulus delta R)"
    using source_integrable inverse_nonzero
    by (simp only: pullback_eq Bochner_Integration.integral_mult_right)
  show ?thesis
    using jacobian determinant pulled_integral square_nonzero
    by (simp add: real_scaleR_def)
qed

lemma slp_squared_radial_annulus_integral_normalize:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) =
    integral\<^sup>L lborel (slp_squared_radial_annulus 1 (R / delta))"
proof -
  have inverse_positive: "0 < inverse delta"
    using delta_positive by simp
  have scaled:
    "integral\<^sup>L lborel
        (slp_squared_radial_annulus
          (inverse delta * delta) (inverse delta * R)) =
      integral\<^sup>L lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_squared_radial_annulus_integral_scale[
          OF inverse_positive delta_positive])
  show ?thesis
    using scaled delta_positive by (simp add: divide_inverse mult.commute)
qed

end
