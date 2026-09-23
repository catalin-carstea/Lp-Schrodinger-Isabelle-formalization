theory Inverse_Schrodinger_Lp_Localized_Cauchy_Endpoint
  imports
    Inverse_Schrodinger_Lp_Localized_Cauchy_L1
begin

section \<open>Endpoint bound for the localized Cauchy kernel\<close>

definition slp_holder_conjugate :: "real \<Rightarrow> real" where
  "slp_holder_conjugate r = r / (r - 1)"

lemma slp_holder_conjugate_arithmetic:
  assumes "2 < r"
  shows "1 < slp_holder_conjugate r"
    and "slp_holder_conjugate r < 2"
    and "1 / slp_holder_conjugate r + 1 / r = 1"
proof -
  have denominator_positive: "0 < r - 1"
    using assms by linarith
  show "1 < slp_holder_conjugate r"
    unfolding slp_holder_conjugate_def
    using denominator_positive assms
    by (simp add: less_divide_eq)
  show "slp_holder_conjugate r < 2"
    unfolding slp_holder_conjugate_def
    using denominator_positive assms
    by (simp add: divide_less_eq)
  show "1 / slp_holder_conjugate r + 1 / r = 1"
    unfolding slp_holder_conjugate_def
  proof -
    have r_nonzero: "r \<noteq> 0"
      using assms by linarith
    have denominator_nonzero: "r - 1 \<noteq> 0"
      using denominator_positive by simp
    have reciprocal:
      "1 / (r / (r - 1)) = (r - 1) / r"
      using r_nonzero denominator_nonzero
      by (simp add: divide_inverse ac_simps)
    have inverse_times: "inverse r * r = 1"
      using r_nonzero by simp
    show "1 / (r / (r - 1)) + 1 / r = 1"
      using reciprocal inverse_times
      by (simp add: divide_inverse algebra_simps)
  qed
qed

lemma slp_localized_cauchy_kernel_power_translate_integrable:
  assumes "1 \<le> s" "s < 2"
  shows "integrable lborel
    (\<lambda>y. abs (slp_localized_cauchy_kernel R (z - y)) powr s)"
proof -
  let ?h = "\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s"
  have h_integrable: "integrable lborel ?h"
    by (rule slp_localized_cauchy_kernel_power_integrable[OF assms])
  have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule linearI) simp_all
  have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule injI) simp
  have transported: "integrable lborel (\<lambda>y. ?h (z + -y))"
    by (rule slp_lborel_affine_pullback(1)[OF neg_linear neg_injective
          h_integrable])
  show ?thesis
    using transported by (simp add: algebra_simps)
qed

lemma slp_localized_cauchy_kernel_power_translate_integral:
  assumes "1 \<le> s" "s < 2"
  shows "integral\<^sup>L lborel
      (\<lambda>y. abs (slp_localized_cauchy_kernel R (z - y)) powr s) =
    integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s)"
proof -
  let ?h = "\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr s"
  have h_integrable: "integrable lborel ?h"
    by (rule slp_localized_cauchy_kernel_power_integrable[OF assms])
  have h_even: "?h (-x) = ?h x" for x
    by (simp add: slp_localized_cauchy_kernel_def)
  have translated:
    "integral\<^sup>L lborel (\<lambda>y. ?h (-z + y)) =
      integral\<^sup>L lborel ?h"
    by (rule slp_lborel_integral_translate[OF h_integrable])
  have pointwise:
    "(\<lambda>y. ?h (z - y)) = (\<lambda>y. ?h (-z + y))"
  proof (rule ext)
    fix y :: slp_point
    have "z - y = -(-z + y)"
      by simp
    then show "?h (z - y) = ?h (-z + y)"
      by (simp only: h_even)
  qed
  show ?thesis
    using translated by (simp only: pointwise)
qed

theorem slp_localized_cauchy_endpoint_bound:
  assumes exponent: "2 < r"
    and radius_nonnegative: "0 \<le> R"
    and f_lp: "aim_complex_lp_on_plane r f"
  defines "q \<equiv> slp_holder_conjugate r"
  shows "\<forall>z. integrable lborel (slp_localized_riesz_integrand R f z) \<and>
    integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
      integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>y. norm (f y) powr r) / r"
proof (intro allI)
  fix z :: slp_point
  have q_lower: "1 < q" and q_upper: "q < 2"
    and conjugates: "1 / q + 1 / r = 1"
    unfolding q_def using slp_holder_conjugate_arithmetic[OF exponent] by auto
  have q_nonzero: "q \<noteq> 0" and r_nonzero: "r \<noteq> 0"
    using q_lower exponent by linarith+
  have r_lower: "1 < r"
    using exponent by linarith
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have f_power_integrable:
    "integrable lborel (\<lambda>y. norm (f y) powr r)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have kernel_power_integrable:
    "integrable lborel
      (\<lambda>y. abs (slp_localized_cauchy_kernel R (z - y)) powr q)"
    by (rule slp_localized_cauchy_kernel_power_translate_integrable)
      (use q_lower q_upper in linarith)+
  let ?majorant = "\<lambda>y.
    abs (slp_localized_cauchy_kernel R (z - y)) powr q / q +
      norm (f y) powr r / r"
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_power_integrable f_power_integrable q_nonzero r_nonzero
    by simp
  have target_integrable:
    "integrable lborel (slp_localized_riesz_integrand R f z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_localized_riesz_integrand R f z
        \<in> borel_measurable lborel"
      by (rule slp_localized_riesz_integrand_measurable[OF f_measurable])
    show "AE y in lborel.
        norm (slp_localized_riesz_integrand R f z y) \<le> norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have young:
        "abs (slp_localized_cauchy_kernel R (z - y)) * norm (f y) \<le>
          abs (slp_localized_cauchy_kernel R (z - y)) powr q / q +
            norm (f y) powr r / r"
        by (rule Youngs_inequality[OF q_lower r_lower conjugates]) simp_all
      have majorant_nonnegative: "0 \<le> ?majorant y"
      proof -
        have q_positive: "0 < q" and r_positive: "0 < r"
          using q_lower exponent by linarith+
        show ?thesis
          using q_positive r_positive by simp
      qed
      show "norm (slp_localized_riesz_integrand R f z y) \<le>
          norm (?majorant y)"
        unfolding slp_localized_riesz_integrand_def
        using young majorant_nonnegative
        by (simp add: slp_localized_cauchy_kernel_nonnegative)
    qed
  qed
  have pointwise_le: "\<And>y. slp_localized_riesz_integrand R f z y \<le> ?majorant y"
  proof -
    fix y :: slp_point
    show "slp_localized_riesz_integrand R f z y \<le> ?majorant y"
      unfolding slp_localized_riesz_integrand_def
      using Youngs_inequality[OF q_lower r_lower conjugates,
          of "abs (slp_localized_cauchy_kernel R (z - y))" "norm (f y)"]
      by (simp add: slp_localized_cauchy_kernel_nonnegative)
  qed
  have integral_le:
    "integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
      integral\<^sup>L lborel ?majorant"
    by (rule integral_mono[OF target_integrable majorant_integrable pointwise_le])
  have kernel_integral:
    "integral\<^sup>L lborel
        (\<lambda>y. abs (slp_localized_cauchy_kernel R (z - y)) powr q) =
      integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q)"
    by (rule slp_localized_cauchy_kernel_power_translate_integral)
      (use q_lower q_upper in linarith)+
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>y. norm (f y) powr r) / r"
    using kernel_power_integrable f_power_integrable q_nonzero r_nonzero
      kernel_integral
    by simp
  show "integrable lborel (slp_localized_riesz_integrand R f z) \<and>
    integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
      integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>y. norm (f y) powr r) / r"
    using target_integrable integral_le majorant_integral by simp
qed

end
