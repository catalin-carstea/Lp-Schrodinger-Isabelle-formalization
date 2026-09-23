theory Inverse_Schrodinger_Lp_Localized_Cauchy_Scaling
  imports
    Inverse_Schrodinger_Lp_Annular_Kernel_Reduction
    Inverse_Schrodinger_Lp_Localized_Cauchy_L1
begin

section \<open>Positive-radius scaling of the localized radial kernel\<close>

lemma slp_localized_cauchy_kernel_scale:
  assumes radius_positive: "0 < R"
  shows "slp_localized_cauchy_kernel R (R *\<^sub>R x) =
    inverse R * slp_localized_cauchy_kernel 1 x"
  unfolding slp_localized_cauchy_kernel_def
  using radius_positive
  by (simp add: norm_scaleR abs_of_pos inverse_mult_distrib)

lemma slp_localized_cauchy_kernel_integral_scale:
  assumes radius_positive: "0 < R"
  shows "integral\<^sup>L lborel (slp_localized_cauchy_kernel R) =
    R * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  let ?g = "(*\<^sub>R) R :: slp_point \<Rightarrow> slp_point"
  have scale_linear: "linear ?g"
    by (rule bounded_linear.linear[OF bounded_linear_scaleR_right])
  have scale_injective: "inj ?g"
  proof (rule injI)
    fix x y :: slp_point
    assume "R *\<^sub>R x = R *\<^sub>R y"
    with radius_positive show "x = y" by simp
  qed
  have jacobian:
    "integral\<^sup>L lborel (slp_localized_cauchy_kernel R) =
      \<bar>det (matrix ?g)\<bar> *\<^sub>R
        integral\<^sup>L lborel
          (\<lambda>x. slp_localized_cauchy_kernel R (?g x))"
    by (rule slp_lborel_linear_pullback(2)[OF scale_linear
          scale_injective slp_localized_cauchy_kernel_integrable])
  have determinant: "\<bar>det (matrix ?g)\<bar> = R ^ 2"
    using radius_positive by simp
  have pullback_eq:
    "(\<lambda>x. slp_localized_cauchy_kernel R (?g x)) =
      (\<lambda>x. inverse R * slp_localized_cauchy_kernel 1 x)"
    by (rule ext) (rule slp_localized_cauchy_kernel_scale[OF
          radius_positive])
  have inverse_nonzero: "inverse R \<noteq> 0"
    using radius_positive by simp
  have pulled_integral:
    "integral\<^sup>L lborel
        (\<lambda>x. slp_localized_cauchy_kernel R (?g x)) =
      inverse R * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    using slp_localized_cauchy_kernel_integrable[of 1] inverse_nonzero
    by (simp only: pullback_eq Bochner_Integration.integral_mult_right)
  show ?thesis
    using jacobian determinant pulled_integral radius_positive
    by (simp add: real_scaleR_def power2_eq_square ac_simps)
qed

lemma slp_localized_cauchy_kernel_integral_delta_normalized:
  assumes delta_positive: "0 < delta"
  shows "(1 / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel delta) =
    integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  using slp_localized_cauchy_kernel_integral_scale[OF delta_positive]
    delta_positive
  by (simp add: divide_inverse ac_simps)

lemma slp_localized_cauchy_kernel_integral_two_delta_normalized:
  assumes delta_positive: "0 < delta"
  shows "(1 / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel (2 * delta)) =
    2 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have two_delta_positive: "0 < 2 * delta"
    using delta_positive by simp
  show ?thesis
    using slp_localized_cauchy_kernel_integral_scale[OF
        two_delta_positive] delta_positive
    by (simp add: divide_inverse ac_simps)
qed

lemma slp_localized_cauchy_kernel_integral_delta_square_normalized:
  assumes delta_positive: "0 < delta"
  shows "(1 / delta ^ 2) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel delta) =
    (1 / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  using slp_localized_cauchy_kernel_integral_scale[OF delta_positive]
    delta_positive
  by (simp add: divide_inverse power2_eq_square ac_simps)

end
