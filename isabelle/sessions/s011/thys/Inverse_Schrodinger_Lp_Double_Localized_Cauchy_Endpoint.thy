theory Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Endpoint
  imports Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Conjugate
begin

section \<open>Endpoint bound for the double localized kernel\<close>

definition slp_double_localized_endpoint_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_double_localized_endpoint_integrand R f z y =
    slp_double_localized_cauchy_kernel R (z - y) * norm (f y)"

definition slp_double_localized_endpoint_potential ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_double_localized_endpoint_potential R f z =
    integral\<^sup>L lborel (slp_double_localized_endpoint_integrand R f z)"

lemma slp_double_localized_cauchy_kernel_nonnegative:
  "0 \<le> slp_double_localized_cauchy_kernel R x"
  unfolding slp_double_localized_cauchy_kernel_def
    slp_real_convolution_def
  by (rule Bochner_Integration.integral_nonneg)
    (simp add: slp_localized_cauchy_kernel_nonnegative)

lemma slp_double_localized_endpoint_integrand_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_double_localized_endpoint_integrand R f z
    \<in> borel_measurable lborel"
  unfolding slp_double_localized_endpoint_integrand_def
  using slp_double_localized_cauchy_kernel_borel_measurable f_measurable
  by measurable

lemma slp_holder_conjugate_lower_and_pair:
  assumes exponent_lower: "1 < p"
  shows "1 < slp_holder_conjugate p"
    and "1 / slp_holder_conjugate p + 1 / p = 1"
proof -
  have denominator_positive: "0 < p - 1"
    using exponent_lower by linarith
  show "1 < slp_holder_conjugate p"
    unfolding slp_holder_conjugate_def
    using denominator_positive exponent_lower
    by (simp add: less_divide_eq)
  have p_nonzero: "p \<noteq> 0"
    using exponent_lower by linarith
  have denominator_nonzero: "p - 1 \<noteq> 0"
    using denominator_positive by simp
  have reciprocal:
    "1 / (p / (p - 1)) = (p - 1) / p"
    using p_nonzero denominator_nonzero
    by (simp add: divide_inverse ac_simps)
  have inverse_times: "inverse p * p = 1"
    using p_nonzero by simp
  show "1 / slp_holder_conjugate p + 1 / p = 1"
    unfolding slp_holder_conjugate_def
    using reciprocal inverse_times
    by (simp add: divide_inverse algebra_simps)
qed

context aim_planar_riesz_hls
begin

lemma slp_double_localized_kernel_power_translate_integrable:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
  defines "q \<equiv> slp_holder_conjugate p"
  shows "integrable lborel
    (\<lambda>y. abs (slp_double_localized_cauchy_kernel R (z - y)) powr q)"
proof -
  have kernel_lp:
    "aim_real_lp_on_plane q (slp_double_localized_cauchy_kernel R)"
    unfolding q_def slp_holder_conjugate_def
    by (rule slp_double_localized_cauchy_kernel_conjugate_lp[OF
          radius_nonnegative p_lower p_upper])
  have kernel_power_integrable:
    "integrable lborel
      (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q)"
    using kernel_lp unfolding aim_real_lp_on_plane_def by blast
  have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule linearI) simp_all
  have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule injI) simp
  have transported:
    "integrable lborel
      (\<lambda>y. abs (slp_double_localized_cauchy_kernel R (z + -y)) powr q)"
    by (rule slp_lborel_affine_pullback(1)[OF neg_linear neg_injective
          kernel_power_integrable])
  show ?thesis
    using transported by simp
qed

lemma slp_double_localized_kernel_power_translate_integral:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
  defines "q \<equiv> slp_holder_conjugate p"
  shows "integral\<^sup>L lborel
      (\<lambda>y. abs (slp_double_localized_cauchy_kernel R (z - y)) powr q) =
    integral\<^sup>L lborel
      (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q)"
proof -
  let ?h =
    "\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q"
  have kernel_lp:
    "aim_real_lp_on_plane q (slp_double_localized_cauchy_kernel R)"
    unfolding q_def slp_holder_conjugate_def
    by (rule slp_double_localized_cauchy_kernel_conjugate_lp[OF
          radius_nonnegative p_lower p_upper])
  have h_integrable: "integrable lborel ?h"
    using kernel_lp unfolding aim_real_lp_on_plane_def by blast
  have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule linearI) simp_all
  have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule injI) simp
  have determinant_abs:
    "abs (det (matrix (uminus :: slp_point \<Rightarrow> slp_point))) = 1"
    by (simp add: det_2 matrix_def axis_def)
  have transported:
    "integral\<^sup>L lborel ?h =
      abs (det (matrix (uminus :: slp_point \<Rightarrow> slp_point))) *\<^sub>R
        integral\<^sup>L lborel (\<lambda>y. ?h (z + -y))"
    by (rule slp_lborel_affine_pullback(2)[OF neg_linear neg_injective
          h_integrable])
  have reflected:
    "integral\<^sup>L lborel (\<lambda>y. ?h (z + -y)) =
      integral\<^sup>L lborel ?h"
    using transported determinant_abs by simp
  show ?thesis
    using reflected by simp
qed

theorem slp_double_localized_cauchy_endpoint_bound:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and f_lp: "aim_complex_lp_on_plane p f"
  defines "q \<equiv> slp_holder_conjugate p"
  shows "\<forall>z. integrable lborel
      (slp_double_localized_endpoint_integrand R f z) \<and>
    slp_double_localized_endpoint_potential R f z \<le>
      integral\<^sup>L lborel
          (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>y. norm (f y) powr p) / p"
proof (intro allI)
  fix z :: slp_point
  have q_lower: "1 < q" and conjugates: "1 / q + 1 / p = 1"
    unfolding q_def
    using slp_holder_conjugate_lower_and_pair[OF p_lower] by auto
  have q_nonzero: "q \<noteq> 0" and p_nonzero: "p \<noteq> 0"
    using q_lower p_lower by linarith+
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have f_power_integrable:
    "integrable lborel (\<lambda>y. norm (f y) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have kernel_power_integrable:
    "integrable lborel
      (\<lambda>y. abs (slp_double_localized_cauchy_kernel R (z - y)) powr q)"
    by (rule slp_double_localized_kernel_power_translate_integrable[OF
          radius_nonnegative p_lower p_upper, folded q_def])
  let ?majorant = "\<lambda>y.
    abs (slp_double_localized_cauchy_kernel R (z - y)) powr q / q +
      norm (f y) powr p / p"
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_power_integrable f_power_integrable q_nonzero p_nonzero
    by simp
  have target_integrable:
    "integrable lborel (slp_double_localized_endpoint_integrand R f z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_double_localized_endpoint_integrand R f z
        \<in> borel_measurable lborel"
      by (rule slp_double_localized_endpoint_integrand_measurable[
            OF f_measurable])
    show "AE y in lborel.
        norm (slp_double_localized_endpoint_integrand R f z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have young:
        "abs (slp_double_localized_cauchy_kernel R (z - y)) * norm (f y) \<le>
          abs (slp_double_localized_cauchy_kernel R (z - y)) powr q / q +
            norm (f y) powr p / p"
        by (rule Youngs_inequality[OF q_lower p_lower conjugates]) simp_all
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using q_lower p_lower by simp
      have kernel_nonnegative:
        "0 \<le> slp_double_localized_cauchy_kernel R (z - y)"
        by (rule slp_double_localized_cauchy_kernel_nonnegative)
      show "norm (slp_double_localized_endpoint_integrand R f z y) \<le>
          norm (?majorant y)"
        unfolding slp_double_localized_endpoint_integrand_def
        using young majorant_nonnegative kernel_nonnegative by simp
    qed
  qed
  have pointwise_le:
    "\<And>y. slp_double_localized_endpoint_integrand R f z y \<le> ?majorant y"
  proof -
    fix y :: slp_point
    have kernel_nonnegative:
      "0 \<le> slp_double_localized_cauchy_kernel R (z - y)"
      by (rule slp_double_localized_cauchy_kernel_nonnegative)
    show "slp_double_localized_endpoint_integrand R f z y \<le> ?majorant y"
      unfolding slp_double_localized_endpoint_integrand_def
      using Youngs_inequality[OF q_lower p_lower conjugates,
          of "abs (slp_double_localized_cauchy_kernel R (z - y))"
            "norm (f y)"] kernel_nonnegative
      by simp
  qed
  have integral_le:
    "integral\<^sup>L lborel (slp_double_localized_endpoint_integrand R f z)
      \<le> integral\<^sup>L lborel ?majorant"
    by (rule integral_mono[OF target_integrable majorant_integrable
          pointwise_le])
  have kernel_integral:
    "integral\<^sup>L lborel
        (\<lambda>y. abs (slp_double_localized_cauchy_kernel R (z - y)) powr q) =
      integral\<^sup>L lborel
        (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q)"
    by (rule slp_double_localized_kernel_power_translate_integral[OF
          radius_nonnegative p_lower p_upper, folded q_def])
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      integral\<^sup>L lborel
          (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>y. norm (f y) powr p) / p"
    using kernel_power_integrable f_power_integrable q_nonzero p_nonzero
      kernel_integral
    by simp
  show "integrable lborel
      (slp_double_localized_endpoint_integrand R f z) \<and>
    slp_double_localized_endpoint_potential R f z \<le>
      integral\<^sup>L lborel
          (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>y. norm (f y) powr p) / p"
    unfolding slp_double_localized_endpoint_potential_def
    using target_integrable integral_le majorant_integral by simp
qed

end

end
