theory Inverse_Schrodinger_Lp_Cauchy_Transform
  imports Inverse_Schrodinger_Lp_AE_Interface
begin

section \<open>Planar Cauchy transforms\<close>

definition slp_point_as_complex :: "slp_point \<Rightarrow> complex" where
  "slp_point_as_complex x = Complex (x $ 0) (x $ 1)"

datatype slp_cauchy_orientation = SLP_Partial_Inverse | SLP_Dbar_Inverse

definition slp_cauchy_denominator ::
  "slp_cauchy_orientation \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_cauchy_denominator orientation z y =
    (case orientation of
      SLP_Partial_Inverse \<Rightarrow>
        cnj (slp_point_as_complex z - slp_point_as_complex y)
    | SLP_Dbar_Inverse \<Rightarrow>
        slp_point_as_complex z - slp_point_as_complex y)"

definition slp_cauchy_kernel ::
  "slp_cauchy_orientation \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_cauchy_kernel orientation z y =
    inverse (slp_cauchy_denominator orientation z y)"

definition slp_cauchy_integrand ::
  "slp_cauchy_orientation \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_cauchy_integrand orientation f z y =
    f y * slp_cauchy_kernel orientation z y"

definition slp_cauchy_integrable_at ::
  "slp_cauchy_orientation \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow> bool"
where
  "slp_cauchy_integrable_at orientation f z \<longleftrightarrow>
    integrable lborel (slp_cauchy_integrand orientation f z)"

definition slp_cauchy_transform ::
  "slp_cauchy_orientation \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_cauchy_transform orientation f z =
    inverse (of_real pi) *
      integral\<^sup>L lborel (slp_cauchy_integrand orientation f z)"

abbreviation slp_partial_inverse :: "slp_scalar_field \<Rightarrow> slp_scalar_field" where
  "slp_partial_inverse f \<equiv> slp_cauchy_transform SLP_Partial_Inverse f"

abbreviation slp_dbar_inverse :: "slp_scalar_field \<Rightarrow> slp_scalar_field" where
  "slp_dbar_inverse f \<equiv> slp_cauchy_transform SLP_Dbar_Inverse f"

lemma slp_cauchy_kernel_diagonal [simp]:
  "slp_cauchy_kernel orientation z z = 0"
  by (cases orientation) (simp_all add: slp_cauchy_kernel_def
      slp_cauchy_denominator_def slp_point_as_complex_def)

lemma slp_point_as_complex_continuous:
  "continuous_on UNIV slp_point_as_complex"
  unfolding slp_point_as_complex_def
  by (intro continuous_intros)

lemma slp_point_as_complex_borel_measurable:
  "slp_point_as_complex \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_onI[OF
        slp_point_as_complex_continuous])

lemma slp_cauchy_denominator_borel_measurable:
  "slp_cauchy_denominator orientation z \<in> borel_measurable borel"
proof (cases orientation)
  case SLP_Partial_Inverse
  have difference_measurable:
    "(\<lambda>y. slp_point_as_complex z - slp_point_as_complex y)
      \<in> borel_measurable borel"
    using slp_point_as_complex_borel_measurable by measurable
  have conjugate_continuous:
    "continuous_on UNIV cnj"
    by (rule continuous_on_cnj[OF continuous_on_id])
  have conjugate_measurable:
    "(\<lambda>y. cnj (slp_point_as_complex z - slp_point_as_complex y))
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_on[OF
          conjugate_continuous difference_measurable])
  have denominator_eq:
    "slp_cauchy_denominator orientation z =
      (\<lambda>y. cnj
        (slp_point_as_complex z - slp_point_as_complex y))"
    by (rule ext) (simp add: slp_cauchy_denominator_def
        SLP_Partial_Inverse)
  show ?thesis
    unfolding denominator_eq
    by (rule conjugate_measurable)
next
  case SLP_Dbar_Inverse
  have denominator_eq:
    "slp_cauchy_denominator orientation z =
      (\<lambda>y. slp_point_as_complex z - slp_point_as_complex y)"
    by (rule ext) (simp add: slp_cauchy_denominator_def
        SLP_Dbar_Inverse)
  show ?thesis
    unfolding denominator_eq
    using slp_point_as_complex_borel_measurable by measurable
qed

lemma slp_cauchy_kernel_borel_measurable:
  "slp_cauchy_kernel orientation z \<in> borel_measurable lborel"
proof -
  have kernel_borel:
    "(\<lambda>y. inverse (slp_cauchy_denominator orientation z y))
      \<in> borel_measurable borel"
    by (rule borel_measurable_inverse[OF
          slp_cauchy_denominator_borel_measurable])
  show ?thesis
    unfolding slp_cauchy_kernel_def
  proof (rule borel_measurable_subalgebra[where N=borel])
    show "sets borel \<subseteq> sets (lborel :: slp_point measure)"
      by simp
    show "space borel = space (lborel :: slp_point measure)"
      by simp
    show "(\<lambda>y. inverse (slp_cauchy_denominator orientation z y))
        \<in> borel_measurable borel"
      by (rule kernel_borel)
  qed
qed

lemma slp_cauchy_integrand_borel_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_cauchy_integrand orientation f z \<in> borel_measurable lborel"
  unfolding slp_cauchy_integrand_def
  using f_measurable slp_cauchy_kernel_borel_measurable
  by measurable

lemma slp_cauchy_integrable_at_of_norm_majorant:
  assumes f_measurable: "f \<in> borel_measurable lborel"
    and majorant:
      "integrable lborel
        (\<lambda>y. norm (f y) * norm (slp_cauchy_kernel orientation z y))"
  shows "slp_cauchy_integrable_at orientation f z"
proof (unfold slp_cauchy_integrable_at_def)
  show "integrable lborel (slp_cauchy_integrand orientation f z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant])
    show "slp_cauchy_integrand orientation f z \<in> borel_measurable lborel"
      by (rule slp_cauchy_integrand_borel_measurable[OF f_measurable])
    show "AE y in lborel.
        norm (slp_cauchy_integrand orientation f z y)
          \<le> norm (norm (f y) * norm (slp_cauchy_kernel orientation z y))"
      by (simp add: slp_cauchy_integrand_def norm_mult
          abs_of_nonneg mult_nonneg_nonneg)
  qed
qed

lemma slp_cauchy_transform_norm_bound:
  "norm (slp_cauchy_transform orientation f z)
    \<le> norm (inverse (of_real pi :: complex)) *
      integral\<^sup>L lborel
        (\<lambda>y. norm (slp_cauchy_integrand orientation f z y))"
proof -
  have integral_bound:
    "norm (integral\<^sup>L lborel (slp_cauchy_integrand orientation f z))
      \<le> integral\<^sup>L lborel
        (\<lambda>y. norm (slp_cauchy_integrand orientation f z y))"
    by (rule integral_norm_bound)
  show ?thesis
    unfolding slp_cauchy_transform_def norm_mult
    by (rule mult_left_mono[OF integral_bound norm_ge_zero])
qed

lemma slp_cauchy_integrable_at_add:
  assumes f_integrable: "slp_cauchy_integrable_at orientation f z"
    and g_integrable: "slp_cauchy_integrable_at orientation g z"
  shows "slp_cauchy_integrable_at orientation (\<lambda>y. f y + g y) z"
proof -
  have f_int:
    "integrable lborel (slp_cauchy_integrand orientation f z)"
    using f_integrable unfolding slp_cauchy_integrable_at_def .
  have g_int:
    "integrable lborel (slp_cauchy_integrand orientation g z)"
    using g_integrable unfolding slp_cauchy_integrable_at_def .
  have integrand_add:
    "slp_cauchy_integrand orientation (\<lambda>y. f y + g y) z =
      (\<lambda>y. slp_cauchy_integrand orientation f z y +
        slp_cauchy_integrand orientation g z y)"
    by (rule ext) (simp add: slp_cauchy_integrand_def algebra_simps)
  have "integrable lborel
      (\<lambda>y. slp_cauchy_integrand orientation f z y +
        slp_cauchy_integrand orientation g z y)"
    by (rule Bochner_Integration.integrable_add[OF f_int g_int])
  then show ?thesis
    unfolding slp_cauchy_integrable_at_def integrand_add .
qed

lemma slp_cauchy_transform_add:
  assumes f_integrable: "slp_cauchy_integrable_at orientation f z"
    and g_integrable: "slp_cauchy_integrable_at orientation g z"
  shows "slp_cauchy_transform orientation (\<lambda>y. f y + g y) z =
    slp_cauchy_transform orientation f z +
      slp_cauchy_transform orientation g z"
proof -
  have f_int:
    "integrable lborel (slp_cauchy_integrand orientation f z)"
    using f_integrable unfolding slp_cauchy_integrable_at_def .
  have g_int:
    "integrable lborel (slp_cauchy_integrand orientation g z)"
    using g_integrable unfolding slp_cauchy_integrable_at_def .
  have integrand_add:
    "slp_cauchy_integrand orientation (\<lambda>y. f y + g y) z =
      (\<lambda>y. slp_cauchy_integrand orientation f z y +
        slp_cauchy_integrand orientation g z y)"
    by (rule ext) (simp add: slp_cauchy_integrand_def algebra_simps)
  have integral_add_eq:
    "integral\<^sup>L lborel
        (slp_cauchy_integrand orientation (\<lambda>y. f y + g y) z) =
      integral\<^sup>L lborel (slp_cauchy_integrand orientation f z) +
        integral\<^sup>L lborel (slp_cauchy_integrand orientation g z)"
    unfolding integrand_add
    by (rule Bochner_Integration.integral_add[OF f_int g_int])
  show ?thesis
    unfolding slp_cauchy_transform_def integral_add_eq
    by (simp add: algebra_simps)
qed

lemma slp_cauchy_transform_cong_ae:
  assumes f_integrable: "slp_cauchy_integrable_at orientation f z"
    and g_integrable: "slp_cauchy_integrable_at orientation g z"
    and f_eq_g: "AE y in lborel. f y = g y"
  shows "slp_cauchy_transform orientation f z =
    slp_cauchy_transform orientation g z"
proof -
  have integrands_eq:
    "AE y in lborel.
      slp_cauchy_integrand orientation f z y =
        slp_cauchy_integrand orientation g z y"
    using f_eq_g by eventually_elim (simp add: slp_cauchy_integrand_def)
  have integral_eq:
    "integral\<^sup>L lborel (slp_cauchy_integrand orientation f z) =
      integral\<^sup>L lborel (slp_cauchy_integrand orientation g z)"
  proof (rule integral_cong_AE)
    show "slp_cauchy_integrand orientation f z \<in> borel_measurable lborel"
      using f_integrable
      by (simp add: slp_cauchy_integrable_at_def borel_measurable_integrable)
    show "slp_cauchy_integrand orientation g z \<in> borel_measurable lborel"
      using g_integrable
      by (simp add: slp_cauchy_integrable_at_def borel_measurable_integrable)
    show "AE y in lborel.
      slp_cauchy_integrand orientation f z y =
        slp_cauchy_integrand orientation g z y"
      by (rule integrands_eq)
  qed
  show ?thesis
    using integral_eq by (simp add: slp_cauchy_transform_def)
qed

end
