theory Inverse_Schrodinger_Lp_Born_Branch_Uniform_Base_Mass
  imports
    Inverse_Schrodinger_Lp_Born_Branch_Base_Mass
    Inverse_Schrodinger_Lp_Affine_Transport
begin

section \<open>Origin-uniform zero-order branch mass\<close>

lemma slp_localized_cauchy_kernel_reflect_translate_nn_integral:
  "(\<integral>\<^sup>+ y.
      ennreal (slp_localized_cauchy_kernel R (origin - y))
      \<partial>lborel) =
    (\<integral>\<^sup>+ x. ennreal (slp_localized_cauchy_kernel R x)
      \<partial>lborel)"
proof -
  let ?kernel = "slp_localized_cauchy_kernel R"
  have kernel_integrable: "integrable lborel ?kernel"
    by (rule slp_localized_cauchy_kernel_integrable)
  have translated_integrable:
      "integrable lborel (\<lambda>y. ?kernel (origin - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule linearI) simp_all
  have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule injI) simp
  have determinant_abs:
      "abs (det (matrix (uminus :: slp_point \<Rightarrow> slp_point))) = 1"
    by (simp add: det_2 matrix_def axis_def)
  have transported:
      "integral\<^sup>L lborel ?kernel =
        abs (det (matrix (uminus :: slp_point \<Rightarrow> slp_point)))
          *\<^sub>R integral\<^sup>L lborel
            (\<lambda>y. ?kernel (origin + -y))"
    by (rule slp_lborel_affine_pullback(2)[OF neg_linear neg_injective
          kernel_integrable])
  have integral_eq:
      "integral\<^sup>L lborel (\<lambda>y. ?kernel (origin - y)) =
        integral\<^sup>L lborel ?kernel"
    using transported determinant_abs by simp
  have kernel_nonnegative_AE:
      "AE x in lborel. 0 \<le> ?kernel x"
    by (rule AE_I2) (rule slp_localized_cauchy_kernel_nonnegative)
  have translated_nonnegative_AE:
      "AE y in lborel. 0 \<le> ?kernel (origin - y)"
    by (rule AE_I2) (rule slp_localized_cauchy_kernel_nonnegative)
  have kernel_nn:
      "(\<integral>\<^sup>+ x. ?kernel x \<partial>lborel) =
        ennreal (integral\<^sup>L lborel ?kernel)"
    by (rule nn_integral_eq_integral[OF kernel_integrable
          kernel_nonnegative_AE])
  have translated_nn:
      "(\<integral>\<^sup>+ y. ?kernel (origin - y) \<partial>lborel) =
        ennreal
          (integral\<^sup>L lborel (\<lambda>y. ?kernel (origin - y)))"
    by (rule nn_integral_eq_integral[OF translated_integrable
          translated_nonnegative_AE])
  show ?thesis
    using kernel_nn translated_nn integral_eq by simp
qed

theorem slp_positive_branch_mass_zero_unweighted_uniform:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<exists>M. M < top \<and>
      (\<forall>origin.
        slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) 0
          origin (\<lambda>_. 1) \<le> M)"
proof -
  let ?kernel_mass =
    "\<integral>\<^sup>+ x. ennreal (slp_localized_cauchy_kernel R x)
      \<partial>lborel"
  let ?M = "ennreal (inverse pi) * ?kernel_mass * ennreal C"
  have kernel_finite: "?kernel_mass < top"
    using slp_localized_cauchy_kernel_integrable[of R]
    unfolding integrable_iff_bounded
    by (simp add: slp_localized_cauchy_kernel_nonnegative)
  have M_finite: "?M < top"
    using kernel_finite by (simp add: ennreal_mult_less_top)
  have uniform_bound:
      "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) 0
          origin (\<lambda>_. 1) \<le> ?M"
    for origin
  proof -
    have base_bound:
        "slp_positive_branch_functional R cutoff potential (\<lambda>_. 1) 0
            origin (\<lambda>_. 1) \<le>
          ennreal (inverse pi) *
            (\<integral>\<^sup>+ x.
              ennreal (slp_localized_cauchy_kernel R (origin - x))
              \<partial>lborel) * ennreal C"
      by (rule slp_positive_branch_mass_zero_unweighted_le[OF
            cutoff_measurable cutoff_bound C_nonnegative])
    show ?thesis
      using base_bound
        slp_localized_cauchy_kernel_reflect_translate_nn_integral[
          of R origin]
      by simp
  qed
  show ?thesis
    by (intro exI[of _ ?M] conjI M_finite allI uniform_bound)
qed

end
