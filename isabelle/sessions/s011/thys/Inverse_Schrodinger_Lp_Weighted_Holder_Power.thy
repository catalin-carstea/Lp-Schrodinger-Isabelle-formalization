theory Inverse_Schrodinger_Lp_Weighted_Holder_Power
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Zero_Finite_Lp
begin

section \<open>Weighted Holder power estimate\<close>

lemma slp_weighted_holder_power:
  fixes weight datum :: "'x \<Rightarrow> real"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and weight_measurable: "weight \<in> borel_measurable M"
    and datum_measurable: "datum \<in> borel_measurable M"
    and weight_nonnegative: "\<And>x. 0 \<le> weight x"
    and datum_nonnegative: "\<And>x. 0 \<le> datum x"
    and weight_integrable: "integrable M weight"
    and weighted_power_integrable:
      "integrable M (\<lambda>x. weight x * datum x powr a)"
  shows
    "integrable M (\<lambda>x. weight x * datum x)"
    "(integral\<^sup>L M (\<lambda>x. weight x * datum x)) powr a \<le>
      (integral\<^sup>L M weight) powr (a / b) *
        integral\<^sup>L M (\<lambda>x. weight x * datum x powr a)"
proof -
  have a_positive: "0 < a" and b_positive: "0 < b"
    using a_lower b_lower by linarith+
  have a_nonzero: "a \<noteq> 0" and b_nonzero: "b \<noteq> 0"
    using a_positive b_positive by simp_all
  have weighted_measurable:
      "(\<lambda>x. weight x * datum x) \<in> borel_measurable M"
    using weight_measurable datum_measurable by measurable
  have majorant_integrable:
      "integrable M
        (\<lambda>x. (weight x * datum x powr a) / a + weight x / b)"
    using weighted_power_integrable weight_integrable a_nonzero b_nonzero
    by simp
  have weighted_integrable:
      "integrable M (\<lambda>x. weight x * datum x)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        weighted_measurable])
    show "AE x in M.
        norm (weight x * datum x) \<le>
          norm ((weight x * datum x powr a) / a + weight x / b)"
    proof (rule AE_I2)
      fix x
      have young:
          "datum x * 1 \<le> datum x powr a / a + 1 powr b / b"
        by (rule Youngs_inequality[OF a_lower b_lower conjugate
              datum_nonnegative]) simp
      have scaled:
          "weight x * datum x \<le>
            (weight x * datum x powr a) / a + weight x / b"
        using mult_left_mono[OF young weight_nonnegative[of x]]
        by (simp add: algebra_simps)
      show "norm (weight x * datum x) \<le>
          norm ((weight x * datum x powr a) / a + weight x / b)"
        using scaled weight_nonnegative[of x] datum_nonnegative[of x]
          a_positive b_positive
        by simp
    qed
  qed
  show "integrable M (\<lambda>x. weight x * datum x)"
    by (rule weighted_integrable)

  let ?A = "integral\<^sup>L M (\<lambda>x. weight x * datum x powr a)"
  let ?B = "integral\<^sup>L M weight"
  let ?I = "integral\<^sup>L M (\<lambda>x. weight x * datum x)"
  have A_nonnegative: "0 \<le> ?A"
    by (rule integral_nonneg_AE) (simp add: weight_nonnegative)
  have B_nonnegative: "0 \<le> ?B"
    by (rule integral_nonneg_AE) (simp add: weight_nonnegative)
  have I_nonnegative: "0 \<le> ?I"
    by (rule integral_nonneg_AE)
      (simp add: weight_nonnegative datum_nonnegative)
  show "?I powr a \<le> ?B powr (a / b) * ?A"
  proof (cases "?A = 0")
    case A_zero: True
    have power_zero:
        "AE x in M. weight x * datum x powr a = 0"
      using integral_nonneg_eq_0_iff_AE[OF weighted_power_integrable]
        A_zero
      by (simp add: weight_nonnegative)
    have weighted_zero: "AE x in M. weight x * datum x = 0"
      using power_zero
    proof eventually_elim
      fix x
      assume zero: "weight x * datum x powr a = 0"
      show "weight x * datum x = 0"
      proof (cases "weight x = 0")
        case False
        then have "datum x powr a = 0"
          using zero by simp
        then have "datum x = 0"
          using datum_nonnegative[of x] a_positive by simp
        then show ?thesis by simp
      qed simp
    qed
    have I_zero: "?I = 0"
      by (rule integral_eq_zero_AE[OF weighted_zero])
    show ?thesis
      using A_zero I_zero by simp
  next
    case A_nonzero: False
    then have A_positive: "0 < ?A"
      using A_nonnegative by simp
    show ?thesis
    proof (cases "?B = 0")
      case B_zero: True
      have weight_zero: "AE x in M. weight x = 0"
        using integral_nonneg_eq_0_iff_AE[OF weight_integrable] B_zero
        by (simp add: weight_nonnegative)
      have weighted_zero: "AE x in M. weight x * datum x = 0"
        using weight_zero by eventually_elim simp
      have I_zero: "?I = 0"
        by (rule integral_eq_zero_AE[OF weighted_zero])
      show ?thesis
        using B_zero I_zero A_nonnegative a_positive b_positive by simp
    next
      case B_nonzero: False
      then have B_positive: "0 < ?B"
        using B_nonnegative by simp
      let ?c = "(?B / ?A) powr (1 / a)"
      have ratio_positive: "0 < ?B / ?A"
        using A_positive B_positive by simp
      have A_notzero: "?A \<noteq> 0" and B_notzero: "?B \<noteq> 0"
        using A_positive B_positive by simp_all
      have ratio_nonzero: "?B / ?A \<noteq> 0"
        using A_notzero B_notzero by simp
      have c_positive: "0 < ?c"
        by (subst powr_gt_zero) (rule ratio_nonzero)
      have c_power: "?c powr a = ?B / ?A"
        using A_positive B_positive ratio_positive a_nonzero
        by (simp add: powr_powr)
      have left_integrable:
          "integrable M (\<lambda>x. (weight x * datum x) * ?c)"
        using weighted_integrable by simp
      have right_integrable:
          "integrable M
            (\<lambda>x.
              ((weight x * datum x powr a) * (?B / ?A)) / a +
                weight x / b)"
        using weighted_power_integrable weight_integrable a_nonzero b_nonzero
        by simp
      have pointwise:
          "(weight x * datum x) * ?c \<le>
            ((weight x * datum x powr a) * (?B / ?A)) / a +
              weight x / b"
        for x
      proof -
        have young:
            "datum x * ?c \<le>
              (datum x * ?c) powr a / a + 1 / b"
          using Youngs_inequality[OF a_lower b_lower conjugate,
              of "datum x * ?c" 1]
          by (simp add: datum_nonnegative c_positive)
        have scaled:
            "weight x * (datum x * ?c) \<le>
              weight x * ((datum x * ?c) powr a / a + 1 / b)"
          by (rule mult_left_mono[OF young weight_nonnegative[of x]])
        show ?thesis
          using scaled c_power datum_nonnegative[of x]
          by (simp add: powr_mult algebra_simps)
      qed
      have integral_bound:
          "integral\<^sup>L M (\<lambda>x. (weight x * datum x) * ?c) \<le>
            integral\<^sup>L M
              (\<lambda>x.
                ((weight x * datum x powr a) * (?B / ?A)) / a +
                  weight x / b)"
        by (rule integral_mono[OF left_integrable right_integrable pointwise])
      have left_value:
          "integral\<^sup>L M (\<lambda>x. (weight x * datum x) * ?c) =
            ?I * ?c"
        using weighted_integrable by simp
      have ratio_cancel: "?A * (?B / ?A) = ?B"
        using A_positive by simp
      have right_value:
          "integral\<^sup>L M
              (\<lambda>x.
                ((weight x * datum x powr a) * (?B / ?A)) / a +
                  weight x / b) = ?B"
      proof -
        have integral_value:
            "integral\<^sup>L M
                (\<lambda>x.
                  ((weight x * datum x powr a) * (?B / ?A)) / a +
                    weight x / b) =
              (?A * (?B / ?A)) / a + ?B / b"
          using weighted_power_integrable weight_integrable by simp
        have coefficient_value:
            "(?A * (?B / ?A)) / a + ?B / b = ?B"
        proof -
          have first_rewrite:
              "(?A * (?B / ?A)) / a + ?B / b = ?B / a + ?B / b"
            by (simp only: ratio_cancel)
          have factor_rewrite:
              "?B / a + ?B / b = ?B * (1 / a + 1 / b)"
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
          "(?A powr (1 / a) * ?B powr (1 / b)) * ?c = ?B"
      proof -
        have A_power_positive: "0 < ?A powr (1 / a)"
          using A_positive by simp
        have B_exponent_sum: "1 / b + 1 / a = 1"
          using conjugate by linarith
        show ?thesis
          using A_positive B_positive A_power_positive B_exponent_sum
            conjugate
          by (simp add: powr_divide powr_add[symmetric]
              mult.commute mult.left_commute mult.assoc)
      qed
      have scaled_comparison:
          "?I * ?c \<le>
            (?A powr (1 / a) * ?B powr (1 / b)) * ?c"
        using normalized_bound comparison_identity by simp
      have holder_bound:
          "?I \<le> ?A powr (1 / a) * ?B powr (1 / b)"
        using scaled_comparison c_positive
        by (simp add: mult_le_cancel_right)
      have raised_bound:
          "?I powr a \<le>
            (?A powr (1 / a) * ?B powr (1 / b)) powr a"
        by (rule powr_mono2[OF _ I_nonnegative holder_bound])
          (use a_positive in simp)
      have target_power:
          "(?A powr (1 / a) * ?B powr (1 / b)) powr a =
            ?B powr (a / b) * ?A"
        using A_positive B_positive a_nonzero
        by (simp add: powr_mult powr_powr mult.commute)
      show ?thesis
        using raised_bound by (simp only: target_power)
    qed
  qed
qed

end
