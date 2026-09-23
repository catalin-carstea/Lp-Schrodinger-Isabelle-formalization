theory Inverse_Schrodinger_Lp_Center_Error_Functional_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Finite_Center_Transpose_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Center_Average_Error_Transpose"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Compact-support duality for the center-average error\<close>

lemma slp_supported_lp_bounded_pairing:
  fixes F H :: slp_scalar_field and a b A :: real and Y :: "slp_point set"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and set_measurable: "Y \<in> sets lborel"
    and set_bounded: "bounded Y"
    and amplitude_lp: "aim_complex_lp_on_plane a F"
    and amplitude_support: "\<And>x. F x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and field_measurable: "H \<in> borel_measurable lborel"
    and bound_nonnegative: "0 \<le> A"
    and local_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm (H x) \<le> A"
  shows "integrable lborel (\<lambda>x. F x * H x)"
    "norm (integral\<^sup>L lborel (\<lambda>x. F x * H x)) \<le>
      aim_complex_lp_norm a F * (A * measure lborel Y powr (1 / b))"
proof -
  have b_positive: "0 < b" using b_lower by simp
  have restricted_lp: "aim_complex_lp_on_plane b (slp_restrict_field Y H)"
    by (rule slp_bounded_restriction_lp_norm(1)[OF b_positive
        set_measurable set_bounded field_measurable bound_nonnegative
        local_bound])
  have restricted_bound:
      "aim_complex_lp_norm b (slp_restrict_field Y H) \<le>
        A * measure lborel Y powr (1 / b)"
    by (rule slp_bounded_restriction_lp_norm(2)[OF b_positive
        set_measurable set_bounded field_measurable bound_nonnegative
        local_bound])
  have product_identity:
      "(\<lambda>x. F x * slp_restrict_field Y H x) = (\<lambda>x. F x * H x)"
    by (rule ext) (auto simp: slp_restrict_field_def dest: amplitude_support)
  show "integrable lborel (\<lambda>x. F x * H x)"
    using slp_aim_complex_lp_on_plane_holder_integral_bound(1)[OF
        a_lower b_lower conjugate amplitude_lp restricted_lp]
    by (simp only: product_identity)
  have holder:
      "norm (integral\<^sup>L lborel (\<lambda>x. F x * H x)) \<le>
        aim_complex_lp_norm a F *
          aim_complex_lp_norm b (slp_restrict_field Y H)"
    using slp_aim_complex_lp_on_plane_holder_integral_bound(2)[OF
        a_lower b_lower conjugate amplitude_lp restricted_lp]
    unfolding aim_complex_lp_norm_def by (simp only: product_identity)
  have amplitude_norm_nonnegative: "0 \<le> aim_complex_lp_norm a F"
    unfolding aim_complex_lp_norm_def by simp
  show "norm (integral\<^sup>L lborel (\<lambda>x. F x * H x)) \<le>
      aim_complex_lp_norm a F * (A * measure lborel Y powr (1 / b))"
    by (rule order_trans[OF holder
        mult_left_mono[OF restricted_bound amplitude_norm_nonnegative]])
qed


theorem slp_center_average_error_functional_bound:
  fixes F G :: slp_scalar_field and a b A tau :: real and Y :: "slp_point set"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and set_measurable: "Y \<in> sets lborel"
    and set_bounded: "bounded Y"
    and amplitude_lp: "aim_complex_lp_on_plane a F"
    and amplitude_support: "\<And>x. F x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and kernel_lp: "aim_complex_lp_on_plane b G"
    and kernel_integrable: "integrable lborel G"
    and bound_nonnegative: "0 \<le> A"
    and transpose_bound:
      "\<And>x. x \<in> Y \<Longrightarrow> norm (slp_center_average tau G x) \<le> A"
  shows "integrable lborel
      (\<lambda>x. (slp_center_average tau F x - F x) * G x)"
    "norm (integral\<^sup>L lborel
        (\<lambda>x. (slp_center_average tau F x - F x) * G x)) \<le>
      (A * measure lborel Y powr (1 / b) + aim_complex_lp_norm b G) *
        aim_complex_lp_norm a F"
proof -
  have a_at_least_one: "1 \<le> a" using a_lower by simp
  have amplitude_integrable: "integrable lborel F"
    by (rule slp_bounded_supported_lp_integrable[OF a_at_least_one
        set_measurable set_bounded amplitude_lp amplitude_support])
  have product_integrable: "integrable lborel (\<lambda>x. F x * G x)"
    by (rule slp_aim_complex_lp_on_plane_holder_integral_bound(1)[OF
        a_lower b_lower conjugate amplitude_lp kernel_lp])
  have product_bound:
      "norm (integral\<^sup>L lborel (\<lambda>x. F x * G x)) \<le>
        aim_complex_lp_norm a F * aim_complex_lp_norm b G"
    using slp_aim_complex_lp_on_plane_holder_integral_bound(2)[OF
        a_lower b_lower conjugate amplitude_lp kernel_lp]
    unfolding aim_complex_lp_norm_def .
  have transpose_measurable:
      "slp_center_average tau G \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF kernel_integrable])
  have paired_transpose_bound:
      "norm (integral\<^sup>L lborel
          (\<lambda>x. F x * slp_center_average tau G x)) \<le>
        aim_complex_lp_norm a F * (A * measure lborel Y powr (1 / b))"
    by (rule slp_supported_lp_bounded_pairing(2)[OF a_lower b_lower
        conjugate set_measurable set_bounded amplitude_lp amplitude_support
        transpose_measurable bound_nonnegative transpose_bound])
  let ?B = "norm (of_real (tau / pi) :: complex) *
    integral\<^sup>L lborel (\<lambda>x. norm (F x))"
  have B_nonnegative: "0 \<le> ?B"
    by (intro mult_nonneg_nonneg) simp_all
  have averaged_amplitude_bound:
      "norm (slp_center_average tau F x) \<le> ?B" for x
    by (rule slp_center_average_fixed_tau_bound)
  have reversed_pair_integrable:
      "integrable lborel (\<lambda>x. G x * slp_center_average tau F x)"
    by (rule slp_integrable_bilinear_mult_bounded[OF kernel_integrable
        slp_center_average_measurable[OF amplitude_integrable]
        B_nonnegative averaged_amplitude_bound])
  have averaged_pair_integrable:
      "integrable lborel (\<lambda>x. slp_center_average tau F x * G x)"
    using reversed_pair_integrable by (simp only: mult.commute)
  show "integrable lborel
      (\<lambda>x. (slp_center_average tau F x - F x) * G x)"
    using Bochner_Integration.integrable_diff[OF
        averaged_pair_integrable product_integrable]
    by (simp only: left_diff_distrib)
  have transpose:
      "integral\<^sup>L lborel
          (\<lambda>x. (slp_center_average tau F x - F x) * G x) =
        integral\<^sup>L lborel (\<lambda>x. F x * slp_center_average tau G x) -
          integral\<^sup>L lborel (\<lambda>x. F x * G x)"
    by (rule slp_center_average_error_bilinear_transpose[OF
        amplitude_integrable kernel_integrable product_integrable])
  have triangle:
      "norm (integral\<^sup>L lborel (\<lambda>x. F x * slp_center_average tau G x) -
          integral\<^sup>L lborel (\<lambda>x. F x * G x)) \<le>
        norm (integral\<^sup>L lborel (\<lambda>x. F x * slp_center_average tau G x)) +
          norm (integral\<^sup>L lborel (\<lambda>x. F x * G x))"
    by (rule norm_triangle_ineq4)
  have combined:
      "norm (integral\<^sup>L lborel
          (\<lambda>x. (slp_center_average tau F x - F x) * G x)) \<le>
        aim_complex_lp_norm a F * (A * measure lborel Y powr (1 / b)) +
          aim_complex_lp_norm a F * aim_complex_lp_norm b G"
    unfolding transpose
    by (rule order_trans[OF triangle
        add_mono[OF paired_transpose_bound product_bound]])
  show "norm (integral\<^sup>L lborel
        (\<lambda>x. (slp_center_average tau F x - F x) * G x)) \<le>
      (A * measure lborel Y powr (1 / b) + aim_complex_lp_norm b G) *
        aim_complex_lp_norm a F"
    using combined by (simp only: algebra_simps)
qed

end
