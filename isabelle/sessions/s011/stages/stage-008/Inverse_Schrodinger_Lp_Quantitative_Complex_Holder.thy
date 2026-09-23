theory Inverse_Schrodinger_Lp_Quantitative_Complex_Holder
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Complex_Lp_Product_Closures"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Quantitative Holder bounds for complex product pairings\<close>

lemma slp_nonnegative_holder_integral:
  fixes q r :: real
    and f g :: "'x \<Rightarrow> real"
  assumes q_lower: "1 < q"
    and r_lower: "1 < r"
    and conjugate: "1 / q + 1 / r = 1"
    and f_measurable: "f \<in> borel_measurable M"
    and g_measurable: "g \<in> borel_measurable M"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_power_integrable: "integrable M (\<lambda>x. f x powr q)"
    and g_power_integrable: "integrable M (\<lambda>x. g x powr r)"
  shows
    "integrable M (\<lambda>x. f x * g x)"
    "integral\<^sup>L M (\<lambda>x. f x * g x) \<le>
      (integral\<^sup>L M (\<lambda>x. f x powr q)) powr (1 / q) *
        (integral\<^sup>L M (\<lambda>x. g x powr r)) powr (1 / r)"
proof -
  have q_positive: "0 < q" and r_positive: "0 < r"
    using q_lower r_lower by linarith+
  have q_nonzero: "q \<noteq> 0" and r_nonzero: "r \<noteq> 0"
    using q_positive r_positive by simp_all
  have product_measurable:
      "(\<lambda>x. f x * g x) \<in> borel_measurable M"
    using f_measurable g_measurable by measurable
  have majorant_integrable:
      "integrable M
        (\<lambda>x. f x powr q / q + g x powr r / r)"
    using f_power_integrable g_power_integrable q_nonzero r_nonzero by simp
  have product_integrable: "integrable M (\<lambda>x. f x * g x)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        product_measurable])
    show "AE x in M.
        norm_class.norm (f x * g x) \<le>
          norm_class.norm (f x powr q / q + g x powr r / r)"
    proof (rule AE_I2)
      fix x
      have young:
          "f x * g x \<le> f x powr q / q + g x powr r / r"
        by (rule Youngs_inequality[OF q_lower r_lower conjugate
              f_nonnegative g_nonnegative])
      show "norm_class.norm (f x * g x) \<le>
          norm_class.norm (f x powr q / q + g x powr r / r)"
        using young f_nonnegative[of x] g_nonnegative[of x]
          q_positive r_positive
        by simp
    qed
  qed
  show "integrable M (\<lambda>x. f x * g x)"
    by (rule product_integrable)

  let ?A = "integral\<^sup>L M (\<lambda>x. f x powr q)"
  let ?B = "integral\<^sup>L M (\<lambda>x. g x powr r)"
  let ?I = "integral\<^sup>L M (\<lambda>x. f x * g x)"
  have A_nonnegative: "0 \<le> ?A"
    by (rule integral_nonneg_AE) (simp add: f_nonnegative)
  have B_nonnegative: "0 \<le> ?B"
    by (rule integral_nonneg_AE) (simp add: g_nonnegative)
  have I_nonnegative: "0 \<le> ?I"
    by (rule integral_nonneg_AE)
      (simp add: f_nonnegative g_nonnegative)
  show "?I \<le> ?A powr (1 / q) * ?B powr (1 / r)"
  proof (cases "?A = 0")
    case A_zero: True
    have f_power_zero: "AE x in M. f x powr q = 0"
      using integral_nonneg_eq_0_iff_AE[OF f_power_integrable] A_zero
      by (simp add: f_nonnegative)
    have f_zero: "AE x in M. f x = 0"
      using f_power_zero
    proof eventually_elim
      fix x
      assume "f x powr q = 0"
      then show "f x = 0"
        using f_nonnegative[of x] q_positive by simp
    qed
    have product_zero: "AE x in M. f x * g x = 0"
      using f_zero by eventually_elim simp
    have I_zero: "?I = 0"
      by (rule integral_eq_zero_AE[OF product_zero])
    show ?thesis
      using A_zero I_zero by simp
  next
    case A_nonzero: False
    then have A_positive: "0 < ?A"
      using A_nonnegative by linarith
    show ?thesis
    proof (cases "?B = 0")
      case B_zero: True
      have g_power_zero: "AE x in M. g x powr r = 0"
        using integral_nonneg_eq_0_iff_AE[OF g_power_integrable] B_zero
        by (simp add: g_nonnegative)
      have g_zero: "AE x in M. g x = 0"
        using g_power_zero
      proof eventually_elim
        fix x
        assume "g x powr r = 0"
        then show "g x = 0"
          using g_nonnegative[of x] r_positive by simp
      qed
      have product_zero: "AE x in M. f x * g x = 0"
        using g_zero by eventually_elim simp
      have I_zero: "?I = 0"
        by (rule integral_eq_zero_AE[OF product_zero])
      show ?thesis
        using B_zero I_zero A_nonnegative by simp
    next
      case B_nonzero: False
      then have B_positive: "0 < ?B"
        using B_nonnegative by linarith
      let ?c = "(?B / ?A) powr (1 / q)"
      have ratio_positive: "0 < ?B / ?A"
        using A_positive B_positive by simp
      have A_notzero: "?A \<noteq> 0" and B_notzero: "?B \<noteq> 0"
        using A_positive B_positive by simp_all
      have ratio_nonzero: "?B / ?A \<noteq> 0"
        using A_notzero B_notzero by simp
      have c_positive: "0 < ?c"
        by (subst powr_gt_zero) (rule ratio_nonzero)
      have c_power: "?c powr q = ?B / ?A"
        using ratio_positive q_nonzero by (simp add: powr_powr)
      have left_integrable:
          "integrable M (\<lambda>x. (f x * g x) * ?c)"
        using product_integrable by simp
      have right_integrable:
          "integrable M
            (\<lambda>x. (f x powr q * (?B / ?A)) / q +
              g x powr r / r)"
        using f_power_integrable g_power_integrable q_nonzero r_nonzero by simp
      have pointwise:
          "(f x * g x) * ?c \<le>
            (f x powr q * (?B / ?A)) / q + g x powr r / r"
        for x
      proof -
        have young:
            "(f x * ?c) * g x \<le>
              (f x * ?c) powr q / q + g x powr r / r"
          using Youngs_inequality[OF q_lower r_lower conjugate,
              of "f x * ?c" "g x"]
          by (simp add: f_nonnegative g_nonnegative c_positive)
        show ?thesis
          using young c_power f_nonnegative[of x]
          by (simp add: powr_mult algebra_simps)
      qed
      have integral_bound:
          "integral\<^sup>L M (\<lambda>x. (f x * g x) * ?c) \<le>
            integral\<^sup>L M
              (\<lambda>x. (f x powr q * (?B / ?A)) / q +
                g x powr r / r)"
        by (rule integral_mono[OF left_integrable right_integrable pointwise])
      have left_value:
          "integral\<^sup>L M (\<lambda>x. (f x * g x) * ?c) = ?I * ?c"
        using product_integrable by simp
      have ratio_cancel: "?A * (?B / ?A) = ?B"
        using A_positive by simp
      have right_value:
          "integral\<^sup>L M
              (\<lambda>x. (f x powr q * (?B / ?A)) / q +
                g x powr r / r) = ?B"
      proof -
        have integral_value:
            "integral\<^sup>L M
                (\<lambda>x. (f x powr q * (?B / ?A)) / q +
                  g x powr r / r) =
              (?A * (?B / ?A)) / q + ?B / r"
          using f_power_integrable g_power_integrable by simp
        have coefficient_value:
            "(?A * (?B / ?A)) / q + ?B / r = ?B"
        proof -
          have first_rewrite:
              "(?A * (?B / ?A)) / q + ?B / r = ?B / q + ?B / r"
            by (simp only: ratio_cancel)
          have factor_rewrite:
              "?B / q + ?B / r = ?B * (1 / q + 1 / r)"
            by (simp add: algebra_simps)
          show ?thesis
            using first_rewrite factor_rewrite conjugate by simp
        qed
        show ?thesis
          using integral_value coefficient_value by simp
      qed
      have normalized_bound: "?I * ?c \<le> ?B"
        using integral_bound left_value right_value by simp
      have comparison_identity:
          "(?A powr (1 / q) * ?B powr (1 / r)) * ?c = ?B"
      proof -
        have A_power_positive: "0 < ?A powr (1 / q)"
          using A_positive by simp
        have exponent_sum: "1 / r + 1 / q = 1"
          using conjugate by linarith
        show ?thesis
          using A_positive B_positive A_power_positive exponent_sum conjugate
          by (simp add: powr_divide powr_add[symmetric]
              mult.commute mult.left_commute mult.assoc)
      qed
      have scaled_comparison:
          "?I * ?c \<le>
            (?A powr (1 / q) * ?B powr (1 / r)) * ?c"
        using normalized_bound comparison_identity by simp
      show ?thesis
        using scaled_comparison c_positive by (simp add: mult_le_cancel_right)
    qed
  qed
qed

lemma slp_aim_complex_lp_on_plane_holder_integral_bound:
  fixes q r :: real
    and f g :: "slp_point \<Rightarrow> complex"
  assumes q_lower: "1 < q"
    and r_lower: "1 < r"
    and conjugate: "1 / q + 1 / r = 1"
    and f_lp: "aim_complex_lp_on_plane q f"
    and g_lp: "aim_complex_lp_on_plane r g"
  shows
    "integrable lborel (\<lambda>x. f x * g x)"
    "norm_class.norm
        (integral\<^sup>L lborel (\<lambda>x. f x * g x)) \<le>
      (integral\<^sup>L lborel
        (\<lambda>x. norm_class.norm (f x) powr q)) powr (1 / q) *
      (integral\<^sup>L lborel
        (\<lambda>x. norm_class.norm (g x) powr r)) powr (1 / r)"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (f x) powr q)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast+
  have g_measurable: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (g x) powr r)"
    using g_lp unfolding aim_complex_lp_on_plane_def by blast+
  have f_norm_measurable:
      "(\<lambda>x. norm_class.norm (f x)) \<in> borel_measurable lborel"
    using f_measurable by measurable
  have g_norm_measurable:
      "(\<lambda>x. norm_class.norm (g x)) \<in> borel_measurable lborel"
    using g_measurable by measurable
  have norm_product_integrable:
      "integrable lborel
        (\<lambda>x. norm_class.norm (f x) * norm_class.norm (g x))"
    by (rule slp_nonnegative_holder_integral(1)[OF q_lower r_lower conjugate
          f_norm_measurable g_norm_measurable])
      (simp_all add: f_power_integrable g_power_integrable)
  have holder_bound:
      "integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (f x) * norm_class.norm (g x)) \<le>
        (integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (f x) powr q)) powr (1 / q) *
        (integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (g x) powr r)) powr (1 / r)"
    by (rule slp_nonnegative_holder_integral(2)[OF q_lower r_lower conjugate
          f_norm_measurable g_norm_measurable])
      (simp_all add: f_power_integrable g_power_integrable)
  have product_measurable:
      "(\<lambda>x. f x * g x) \<in> borel_measurable lborel"
    using f_measurable g_measurable by measurable
  have product_integrable:
      "integrable lborel (\<lambda>x. f x * g x)"
    using Bochner_Integration.integrable_norm_iff[OF product_measurable]
      norm_product_integrable
    by (simp add: norm_mult)
  show "integrable lborel (\<lambda>x. f x * g x)"
    by (rule product_integrable)
  have integral_norm:
      "norm_class.norm
          (integral\<^sup>L lborel (\<lambda>x. f x * g x)) \<le>
        integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (f x * g x))"
    by (rule Bochner_Integration.integral_norm_bound)
  show "norm_class.norm
        (integral\<^sup>L lborel (\<lambda>x. f x * g x)) \<le>
      (integral\<^sup>L lborel
        (\<lambda>x. norm_class.norm (f x) powr q)) powr (1 / q) *
      (integral\<^sup>L lborel
        (\<lambda>x. norm_class.norm (g x) powr r)) powr (1 / r)"
    using integral_norm holder_bound by (simp add: norm_mult)
qed

end
