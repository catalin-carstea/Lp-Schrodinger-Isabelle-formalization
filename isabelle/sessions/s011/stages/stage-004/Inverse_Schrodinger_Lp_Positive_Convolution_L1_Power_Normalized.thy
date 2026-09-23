theory Inverse_Schrodinger_Lp_Positive_Convolution_L1_Power_Normalized
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Convolution_L1_Power"
begin

section \<open>Normalized positive endpoint Young inequality\<close>

theorem slp_positive_convolution_L1_power_bound_normalized:
  fixes f g :: "slp_point \<Rightarrow> real"
    and t conjugate_t :: real
  assumes t_lower: "1 < t"
    and conjugate_lower: "1 < conjugate_t"
    and conjugate: "1 / t + 1 / conjugate_t = 1"
    and f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_integrable: "integrable lborel f"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. g x powr t)"
  shows target_integrable:
    "integrable lborel
      (\<lambda>output.
        (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
          powr t)"
    and target_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
            powr t)
      \<le> (integral\<^sup>L lborel f) powr t *
        integral\<^sup>L lborel (\<lambda>x. g x powr t)"
proof -
  let ?M = "integral\<^sup>L lborel f"
  let ?P = "integral\<^sup>L lborel (\<lambda>x. g x powr t)"
  have raw_integrable:
      "integrable lborel
        (\<lambda>output.
          (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
            powr t)"
    by (rule slp_positive_convolution_L1_power_bound(1)[OF assms])
  have raw_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            (integral\<^sup>L lborel
              (\<lambda>root. f root * g (output - root))) powr t)
        \<le> ?M powr (t / conjugate_t) * (?P * ?M)"
    by (rule slp_positive_convolution_L1_power_bound(2)[OF assms])
  have t_nonzero: "t \<noteq> 0" and conjugate_nonzero: "conjugate_t \<noteq> 0"
    using t_lower conjugate_lower by linarith+
  have product_relation: "conjugate_t + t = t * conjugate_t"
  proof -
    have scaled:
        "(1 / t + 1 / conjugate_t) * (t * conjugate_t) =
          1 * (t * conjugate_t)"
      by (rule arg_cong[OF conjugate])
    show ?thesis
      using scaled t_nonzero conjugate_nonzero
      by (simp add: algebra_simps)
  qed
  have exponent: "t / conjugate_t = t - 1"
  proof (rule iffD2[OF nonzero_divide_eq_eq[OF conjugate_nonzero]])
    show "t = (t - 1) * conjugate_t"
      using product_relation by (simp add: algebra_simps)
  qed
  have M_nonnegative: "0 \<le> ?M"
    by (rule integral_nonneg_AE) (simp add: f_nonnegative)
  have normalization:
      "?M powr (t / conjugate_t) * (?P * ?M) = ?M powr t * ?P"
  proof (cases "?M = 0")
    case True
    have exponent_positive: "0 < t / conjugate_t"
      unfolding exponent using t_lower by linarith
    show ?thesis using True exponent_positive t_lower by simp
  next
    case False
    have M_positive: "0 < ?M"
      using M_nonnegative False by linarith
    have powr_merge:
        "?M powr (t - 1) * ?M powr 1 = ?M powr ((t - 1) + 1)"
      by (rule powr_add[symmetric])
    have power_identity: "?M * ?M powr (t - 1) = ?M powr t"
      using powr_merge M_nonnegative by (simp add: algebra_simps)
    show ?thesis
      by (simp add: exponent algebra_simps power_identity)
  qed
  show "integrable lborel
      (\<lambda>output.
        (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
          powr t)"
    by (rule raw_integrable)
  show "integral\<^sup>L lborel
        (\<lambda>output.
          (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))
            powr t)
      \<le> (integral\<^sup>L lborel f) powr t *
        integral\<^sup>L lborel (\<lambda>x. g x powr t)"
    using raw_bound normalization by simp
qed

end
