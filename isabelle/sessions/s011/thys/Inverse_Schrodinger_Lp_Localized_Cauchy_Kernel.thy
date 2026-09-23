theory Inverse_Schrodinger_Lp_Localized_Cauchy_Kernel
  imports Inverse_Schrodinger_Lp_Cauchy_Transform
begin

section \<open>Localized positive Cauchy kernels\<close>

text \<open>
  The manuscript's radial kernel is represented by zero both off its closed
  cutoff ball and at the origin.  The latter is the standard harmless
  totalization at a singleton null set.
\<close>

definition slp_localized_cauchy_kernel ::
  "real \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_localized_cauchy_kernel R x =
    (if norm x \<le> R then inverse (norm x) else 0)"

definition slp_real_convolution ::
  "(slp_point \<Rightarrow> real) \<Rightarrow> (slp_point \<Rightarrow> real) \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_real_convolution f g x =
    integral\<^sup>L lborel (\<lambda>y. f y * g (x - y))"

definition slp_double_localized_cauchy_kernel ::
  "real \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_double_localized_cauchy_kernel R =
    slp_real_convolution
      (slp_localized_cauchy_kernel R)
      (slp_localized_cauchy_kernel R)"

lemma slp_localized_cauchy_kernel_zero [simp]:
  "slp_localized_cauchy_kernel R 0 = 0"
  by (simp add: slp_localized_cauchy_kernel_def)

lemma slp_localized_cauchy_kernel_nonnegative:
  "0 \<le> slp_localized_cauchy_kernel R x"
  by (simp add: slp_localized_cauchy_kernel_def)

lemma slp_localized_cauchy_kernel_inside:
  assumes "norm x \<le> R"
  shows "slp_localized_cauchy_kernel R x = inverse (norm x)"
  using assms by (simp add: slp_localized_cauchy_kernel_def)

lemma slp_localized_cauchy_kernel_outside:
  assumes "R < norm x"
  shows "slp_localized_cauchy_kernel R x = 0"
  using assms by (simp add: slp_localized_cauchy_kernel_def)

lemma slp_localized_cauchy_kernel_negative_radius [simp]:
  assumes "R < 0"
  shows "slp_localized_cauchy_kernel R = (\<lambda>_. 0)"
proof (rule ext)
  fix x :: slp_point
  have "\<not> norm x \<le> R"
    using norm_ge_zero[of x] assms by linarith
  then show "slp_localized_cauchy_kernel R x = (\<lambda>_. 0) x"
    by (simp add: slp_localized_cauchy_kernel_def)
qed

lemma slp_localized_cauchy_kernel_borel_measurable:
  "slp_localized_cauchy_kernel R \<in> borel_measurable lborel"
proof -
  have borel:
    "(\<lambda>x::slp_point.
      if norm x \<le> R then inverse (norm x) else 0)
      \<in> borel_measurable borel"
    by measurable
  show ?thesis
    unfolding slp_localized_cauchy_kernel_def
  proof (rule borel_measurable_subalgebra[where N=borel])
    show "sets borel \<subseteq> sets (lborel :: slp_point measure)"
      by simp
    show "space borel = space (lborel :: slp_point measure)"
      by simp
    show "(\<lambda>x::slp_point.
      if norm x \<le> R then inverse (norm x) else 0)
      \<in> borel_measurable borel"
      by (rule borel)
  qed
qed

lemma slp_double_localized_cauchy_kernel_borel_measurable:
  "slp_double_localized_cauchy_kernel R \<in> borel_measurable lborel"
  unfolding slp_double_localized_cauchy_kernel_def
    slp_real_convolution_def
  using slp_localized_cauchy_kernel_borel_measurable
  by measurable

lemma slp_localized_kernel_factors_cannot_both_survive:
  assumes radius_nonnegative: "0 \<le> R"
    and output_outside: "2 * R < norm x"
  shows "slp_localized_cauchy_kernel R y *
      slp_localized_cauchy_kernel R (x - y) = 0"
proof (cases "norm y \<le> R")
  case False
  then show ?thesis
    by (simp add: slp_localized_cauchy_kernel_def)
next
  case True
  have second_outside: "R < norm (x - y)"
  proof (rule ccontr)
    assume "\<not> R < norm (x - y)"
    then have second_inside: "norm (x - y) \<le> R"
      by simp
    have "norm x \<le> norm y + norm (x - y)"
      using norm_triangle_ineq[of y "x - y"]
      by (simp add: add.commute)
    also have "... \<le> R + R"
      using True second_inside by linarith
    also have "... = 2 * R"
      by simp
    finally show False
      using output_outside by linarith
  qed
  then show ?thesis
    by (simp add: slp_localized_cauchy_kernel_def)
qed

lemma slp_double_localized_cauchy_kernel_outside:
  assumes radius_nonnegative: "0 \<le> R"
    and output_outside: "2 * R < norm x"
  shows "slp_double_localized_cauchy_kernel R x = 0"
  unfolding slp_double_localized_cauchy_kernel_def
    slp_real_convolution_def
proof (rule integral_eq_zero_AE, rule AE_I2)
  fix y
  show "slp_localized_cauchy_kernel R y *
      slp_localized_cauchy_kernel R (x - y) = 0"
    by (rule slp_localized_kernel_factors_cannot_both_survive[
          OF radius_nonnegative output_outside])
qed

end
