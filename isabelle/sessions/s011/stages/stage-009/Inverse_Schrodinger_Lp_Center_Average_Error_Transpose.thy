theory Inverse_Schrodinger_Lp_Center_Average_Error_Transpose
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Product_Rough_Smooth_Difference_Decay"
begin

section \<open>Exact transpose of a physical center-average error pairing\<close>

theorem slp_center_average_error_bilinear_transpose:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
    and product_integrable:
      "integrable lborel (\<lambda>x. f x * g x)"
  shows
    "integral\<^sup>L lborel
        (\<lambda>x. (slp_center_average tau f x - f x) * g x) =
      integral\<^sup>L lborel
          (\<lambda>x. f x * slp_center_average tau g x) -
        integral\<^sup>L lborel (\<lambda>x. f x * g x)"
proof -
  let ?B =
    "norm (of_real (tau / pi) :: complex) *
      integral\<^sup>L lborel (\<lambda>x. norm (f x))"
  have B_nonnegative: "0 \<le> ?B"
    by (intro mult_nonneg_nonneg) simp_all
  have average_bound:
      "norm (slp_center_average tau f x) \<le> ?B" for x
    by (rule slp_center_average_fixed_tau_bound)
  have averaged_pair_integrable:
      "integrable lborel
        (\<lambda>x. slp_center_average tau f x * g x)"
  proof -
    have reversed_integrable:
        "integrable lborel
          (\<lambda>x. g x * slp_center_average tau f x)"
      by (rule slp_integrable_bilinear_mult_bounded[OF
            g_integrable slp_center_average_measurable[OF f_integrable]
            B_nonnegative average_bound])
    show ?thesis
      using reversed_integrable by (simp only: mult.commute)
  qed
  have transpose:
      "integral\<^sup>L lborel
          (\<lambda>x. slp_center_average tau f x * g x) =
        integral\<^sup>L lborel
          (\<lambda>x. f x * slp_center_average tau g x)"
    using slp_center_average_bilinear_transpose[OF
      g_integrable f_integrable]
    by (simp only: mult.commute)
  have
      "integral\<^sup>L lborel
          (\<lambda>x. (slp_center_average tau f x - f x) * g x) =
        integral\<^sup>L lborel
          (\<lambda>x.
            slp_center_average tau f x * g x - f x * g x)"
    by (rule Bochner_Integration.integral_cong[OF refl])
      (simp add: algebra_simps)
  also have "... =
      integral\<^sup>L lborel
          (\<lambda>x. slp_center_average tau f x * g x) -
        integral\<^sup>L lborel (\<lambda>x. f x * g x)"
    by (rule Bochner_Integration.integral_diff[OF
          averaged_pair_integrable product_integrable])
  also have "... =
      integral\<^sup>L lborel
          (\<lambda>x. f x * slp_center_average tau g x) -
        integral\<^sup>L lborel (\<lambda>x. f x * g x)"
    by (simp only: transpose)
  finally show ?thesis .
qed

end
