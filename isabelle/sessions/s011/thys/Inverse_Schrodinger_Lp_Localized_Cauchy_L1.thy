theory Inverse_Schrodinger_Lp_Localized_Cauchy_L1
  imports
    Inverse_Schrodinger_Lp_Localized_Cauchy_Riesz
    Inverse_Schrodinger_Lp_Affine_Transport
begin

section \<open>First-power and translated localized-kernel integrability\<close>

lemma slp_localized_cauchy_kernel_integrable:
  "integrable lborel (slp_localized_cauchy_kernel R)"
proof -
  have power_integrable:
    "integrable lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr (1::real))"
    by (rule slp_localized_cauchy_kernel_power_integrable) simp_all
  have pointwise:
    "(\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr (1::real)) =
      slp_localized_cauchy_kernel R"
  proof (rule ext)
    fix x :: slp_point
    show "abs (slp_localized_cauchy_kernel R x) powr (1::real) =
        slp_localized_cauchy_kernel R x"
      using slp_localized_cauchy_kernel_nonnegative[of R x]
      by simp
  qed
  show ?thesis
    using power_integrable by (simp only: pointwise)
qed

lemma slp_localized_cauchy_kernel_reflected_integrable:
  "integrable lborel (\<lambda>y. slp_localized_cauchy_kernel R (-y))"
proof -
  have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule linearI) simp_all
  have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule injI) simp
  have affine:
    "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel R (0 + -y))"
    by (rule slp_lborel_affine_pullback(1)[OF neg_linear neg_injective
          slp_localized_cauchy_kernel_integrable])
  show ?thesis
    using affine by simp
qed

lemma slp_localized_cauchy_kernel_translate_integrable:
  "integrable lborel (\<lambda>y. slp_localized_cauchy_kernel R (x - y))"
proof -
  have translated:
    "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel R (x + y))"
    by (rule slp_lborel_integrable_translate[
          OF slp_localized_cauchy_kernel_integrable])
  have reflected_translated:
    "integrable lborel
      (\<lambda>y. slp_localized_cauchy_kernel R (x + (-y)))"
  proof -
    have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
      by (rule linearI) simp_all
    have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
      by (rule injI) simp
    have affine:
      "integrable lborel
        (\<lambda>y. (\<lambda>u. slp_localized_cauchy_kernel R (x + u))
          (0 + -y))"
      by (rule slp_lborel_affine_pullback(1)[OF neg_linear neg_injective
            translated])
    show ?thesis
      using affine by simp
  qed
  show ?thesis
    using reflected_translated
    by (simp add: algebra_simps)
qed

end
