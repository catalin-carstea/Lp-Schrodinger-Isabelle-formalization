theory Inverse_Schrodinger_Lp_Positive_Convolution_Finite_Target_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Output_Density_All_Order_Unit_Terminal_Finite_Target"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Convolution_Mixed_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Weighted_Holder_Power"
begin

section \<open>AE-safe pointwise Young envelope for finite targets\<close>

theorem slp_positive_convolution_finite_target_pointwise:
  fixes t :: real
    and f g :: "slp_point \<Rightarrow> real"
  assumes t_lower: "1 < t"
    and f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_power_integrable:
      "integrable lborel
        (\<lambda>x. f x powr slp_mixed_unweighted_branch_exponent t)"
    and g_power_integrable:
      "integrable lborel
        (\<lambda>x. g x powr slp_mixed_unweighted_branch_exponent t)"
    and local_power_finite:
      "(\<integral>\<^sup>+ root.
          ennreal
            (f root powr slp_mixed_unweighted_branch_exponent t *
              g (output - root) powr slp_mixed_unweighted_branch_exponent t)
          \<partial>lborel) < \<infinity>"
  shows convolution_finite:
      "(\<integral>\<^sup>+ root. ennreal (f root * g (output - root))
        \<partial>lborel) < \<infinity>"
    and convolution_power_bound:
      "enn2real
          (\<integral>\<^sup>+ root. ennreal (f root * g (output - root))
            \<partial>lborel) powr t \<le>
        enn2real
          (\<integral>\<^sup>+ root.
            ennreal
              (f root powr slp_mixed_unweighted_branch_exponent t *
                g (output - root) powr
                  slp_mixed_unweighted_branch_exponent t)
            \<partial>lborel) *
        (integral\<^sup>L lborel
            (\<lambda>x. f x powr slp_mixed_unweighted_branch_exponent t) *
          integral\<^sup>L lborel
            (\<lambda>x. g x powr slp_mixed_unweighted_branch_exponent t))
          powr ((t - 1) / 2)"
proof -
  let ?a = "slp_mixed_unweighted_branch_exponent t"
  let ?s = "t / (t + 1)"
  let ?d = "1 / (t + 1)"
  let ?h = "t / (t - 1)"
  let ?W = "\<lambda>root.
    f root powr ?s * g (output - root) powr ?s"
  let ?D = "\<lambda>root.
    f root powr ?d * g (output - root) powr ?d"
  let ?U = "\<lambda>root.
    f root powr ?a * g (output - root) powr ?a"
  let ?I_f = "integral\<^sup>L lborel (\<lambda>x. f x powr ?a)"
  let ?I_g = "integral\<^sup>L lborel (\<lambda>x. g x powr ?a)"
  let ?I_W = "integral\<^sup>L lborel ?W"
  let ?I_U = "integral\<^sup>L lborel ?U"
  let ?H = "\<integral>\<^sup>+ root. ennreal (f root * g (output - root))
    \<partial>lborel"
  let ?U_nn = "\<integral>\<^sup>+ root. ennreal (?U root) \<partial>lborel"
  have t_positive: "0 < t"
    using t_lower by linarith
  have t_minus_one_positive: "0 < t - 1"
    using t_lower by linarith
  have t_plus_one_positive: "0 < t + 1"
    using t_positive by linarith
  have t_nonzero: "t \<noteq> 0"
    using t_positive by simp
  have t_minus_one_nonzero: "t - 1 \<noteq> 0"
    using t_minus_one_positive by simp
  have t_plus_one_nonzero: "t + 1 \<noteq> 0"
    using t_plus_one_positive by simp
  have s_positive: "0 < ?s"
    using t_positive t_plus_one_positive by simp
  have d_positive: "0 < ?d"
    using t_plus_one_positive by simp
  have a_eq: "?a = 2 * t / (t + 1)"
    by (simp only: slp_mixed_unweighted_branch_exponent_def)
  have double_s: "2 * ?s = ?a"
    unfolding a_eq by simp
  have s_plus_d: "?s + ?d = 1"
  proof -
    have common: "t / (t + 1) + 1 / (t + 1) = (t + 1) / (t + 1)"
      by (rule add_divide_distrib [symmetric])
    show ?thesis using common t_plus_one_nonzero by simp
  qed
  have s_plus_t_d: "?s + t * ?d = ?a"
    unfolding a_eq using t_plus_one_nonzero by simp
  have h_lower: "1 < ?h"
    using t_minus_one_positive by (simp add: less_divide_eq)
  have h_conjugate: "1 / t + 1 / ?h = 1"
  proof -
    have inverse_h: "1 / ?h = (t - 1) / t"
      using t_nonzero t_minus_one_nonzero by simp
    have common: "1 / t + (t - 1) / t = (1 + (t - 1)) / t"
      by (rule add_divide_distrib [symmetric])
    show ?thesis
      using inverse_h common t_nonzero by simp
  qed
  have t_over_h: "t / ?h = t - 1"
    using t_nonzero t_minus_one_nonzero by simp
  have W_measurable[measurable]: "?W \<in> borel_measurable lborel"
    by measurable
  have D_measurable[measurable]: "?D \<in> borel_measurable lborel"
    by measurable
  have U_measurable[measurable]: "?U \<in> borel_measurable lborel"
    by measurable
  have W_nonnegative: "0 \<le> ?W root" for root
    by simp
  have D_nonnegative: "0 \<le> ?D root" for root
    by simp
  have U_nonnegative: "0 \<le> ?U root" for root
    by simp
  have W_D: "?W root * ?D root = f root * g (output - root)" for root
    using f_nonnegative[of root] g_nonnegative[of "output - root"]
      s_plus_d
    by (simp add: algebra_simps powr_add [symmetric])
  have W_D_power: "?W root * ?D root powr t = ?U root" for root
    using f_nonnegative[of root] g_nonnegative[of "output - root"]
      s_plus_t_d
    by (simp add: algebra_simps powr_mult powr_powr powr_add [symmetric])
  have g_shift_power_integrable:
      "integrable lborel (\<lambda>root. g (output - root) powr ?a)"
    by (rule slp_lborel_integrable_reflect_translate(1)[OF _
          g_power_integrable]) measurable
  have g_shift_power_integral:
      "integral\<^sup>L lborel (\<lambda>root. g (output - root) powr ?a) =
        ?I_g"
    by (rule slp_lborel_integrable_reflect_translate(2)[OF _
          g_power_integrable]) measurable
  have I_f_nonnegative: "0 \<le> ?I_f"
    by (rule integral_nonneg_AE) simp
  have I_g_nonnegative: "0 \<le> ?I_g"
    by (rule integral_nonneg_AE) simp
  have mass_product_nonnegative: "0 \<le> ?I_f * ?I_g"
    using I_f_nonnegative I_g_nonnegative by simp
  let ?A = "\<lambda>root. ennreal (f root powr ?s)"
  let ?B = "\<lambda>root. ennreal (g (output - root) powr ?s)"
  have A_measurable: "?A \<in> borel_measurable lborel"
    by measurable
  have B_measurable: "?B \<in> borel_measurable lborel"
    by measurable
  have AB: "?A root * ?B root = ennreal (?W root)" for root
    by (rule ennreal_mult [symmetric]) simp_all
  have A_square: "?A root ^ 2 = ennreal (f root powr ?a)" for root
  proof -
    have real_square: "(f root powr ?s) ^ 2 = f root powr ?a"
      using double_s
      by (simp add: power2_eq_square powr_add [symmetric])
    have converted:
        "?A root ^ 2 = ennreal ((f root powr ?s) ^ 2)"
      by (rule ennreal_power) simp
    show ?thesis using converted real_square by simp
  qed
  have B_square: "?B root ^ 2 = ennreal (g (output - root) powr ?a)"
    for root
  proof -
    have real_square:
        "(g (output - root) powr ?s) ^ 2 =
          g (output - root) powr ?a"
      using double_s
      by (simp add: power2_eq_square powr_add [symmetric])
    have converted:
        "?B root ^ 2 = ennreal ((g (output - root) powr ?s) ^ 2)"
      by (rule ennreal_power) simp
    show ?thesis using converted real_square by simp
  qed
  have f_nn:
      "(\<integral>\<^sup>+ root. ennreal (f root powr ?a) \<partial>lborel) =
        ennreal ?I_f"
    by (rule nn_integral_eq_integral[OF f_power_integrable]) simp
  have g_nn:
      "(\<integral>\<^sup>+ root. ennreal (g (output - root) powr ?a)
          \<partial>lborel) = ennreal ?I_g"
  proof -
    have converted:
        "(\<integral>\<^sup>+ root. ennreal (g (output - root) powr ?a)
            \<partial>lborel) =
          ennreal
            (integral\<^sup>L lborel
              (\<lambda>root. g (output - root) powr ?a))"
      by (rule nn_integral_eq_integral[OF g_shift_power_integrable]) simp
    show ?thesis using converted g_shift_power_integral by simp
  qed
  have weight_cauchy:
      "(\<integral>\<^sup>+ root. ennreal (?W root) \<partial>lborel) ^ 2 \<le>
        ennreal ?I_f * ennreal ?I_g"
  proof -
    have raw:
        "(\<integral>\<^sup>+ root. ?A root * ?B root \<partial>lborel) ^ 2 \<le>
          (\<integral>\<^sup>+ root. ?A root ^ 2 \<partial>lborel) *
          (\<integral>\<^sup>+ root. ?B root ^ 2 \<partial>lborel)"
      by (rule Cauchy_Schwarz_nn_integral[OF A_measurable B_measurable])
    show ?thesis
      using raw by (simp only: AB A_square B_square f_nn g_nn)
  qed
  have weight_nn_square_less_top:
      "(\<integral>\<^sup>+ root. ennreal (?W root) \<partial>lborel) ^ 2 <
        \<infinity>"
    by (rule le_less_trans[OF weight_cauchy])
      (simp add: ennreal_mult_less_top)
  have weight_nn_less_top:
      "(\<integral>\<^sup>+ root. ennreal (?W root) \<partial>lborel) <
        \<infinity>"
    using weight_nn_square_less_top by (simp add: power_less_top_ennreal)
  have W_integrable: "integrable lborel ?W"
    unfolding integrable_iff_bounded
    apply (intro conjI)
     apply measurable
    using weight_nn_less_top W_nonnegative by simp
  have W_integral_nonnegative: "0 \<le> ?I_W"
    by (rule integral_nonneg_AE) (simp add: W_nonnegative)
  have W_nn:
      "(\<integral>\<^sup>+ root. ennreal (?W root) \<partial>lborel) =
        ennreal ?I_W"
    by (rule nn_integral_eq_integral[OF W_integrable])
      (simp add: W_nonnegative)
  have W_square_bound: "?I_W ^ 2 \<le> ?I_f * ?I_g"
  proof -
    have lifted: "ennreal (?I_W ^ 2) \<le> ennreal (?I_f * ?I_g)"
      using weight_cauchy W_nn I_f_nonnegative I_g_nonnegative
        W_integral_nonnegative
      by (simp add: ennreal_power ennreal_mult)
    show ?thesis
      using lifted mass_product_nonnegative by simp
  qed
  have W_power_bound:
      "?I_W powr (t - 1) \<le>
        (?I_f * ?I_g) powr ((t - 1) / 2)"
  proof -
    have exponent_nonnegative: "0 \<le> (t - 1) / 2"
      using t_minus_one_positive by simp
    have raised:
        "(?I_W ^ 2) powr ((t - 1) / 2) \<le>
          (?I_f * ?I_g) powr ((t - 1) / 2)"
      by (rule powr_mono2[OF exponent_nonnegative])
        (use W_integral_nonnegative W_square_bound in simp_all)
    have left_power:
        "(?I_W ^ 2) powr ((t - 1) / 2) = ?I_W powr (t - 1)"
    proof -
      have exponent_double:
          "(t - 1) / 2 + (t - 1) / 2 = t - 1"
      proof -
        have common:
            "(t - 1) / 2 + (t - 1) / 2 =
              ((t - 1) + (t - 1)) / 2"
          by (rule add_divide_distrib [symmetric])
        have numerator:
            "(t - 1) + (t - 1) = 2 * (t - 1)"
          by simp
        show ?thesis
          by (simp only: common numerator, simp)
      qed
      show ?thesis
        using W_integral_nonnegative exponent_double
        by (simp add: power2_eq_square powr_mult powr_add [symmetric])
    qed
    show ?thesis using raised left_power by simp
  qed
  have U_integrable: "integrable lborel ?U"
    unfolding integrable_iff_bounded
    apply (intro conjI)
     apply measurable
    using local_power_finite U_nonnegative by simp
  have U_integral_nonnegative: "0 \<le> ?I_U"
    by (rule integral_nonneg_AE) (simp add: U_nonnegative)
  have U_nn: "?U_nn = ennreal ?I_U"
    by (rule nn_integral_eq_integral[OF U_integrable])
      (simp add: U_nonnegative)
  have weighted_power_eq:
      "(\<lambda>root. ?W root * ?D root powr t) = ?U"
    by (rule ext, rule W_D_power)
  have weighted_power_integrable:
      "integrable lborel (\<lambda>root. ?W root * ?D root powr t)"
    unfolding weighted_power_eq by (rule U_integrable)
  note holder = slp_weighted_holder_power[OF
      t_lower h_lower h_conjugate W_measurable D_measurable
      W_nonnegative D_nonnegative W_integrable weighted_power_integrable]
  have convolution_integrable:
      "integrable lborel (\<lambda>root. f root * g (output - root))"
  proof -
    have convolution_eq:
        "(\<lambda>root. f root * g (output - root)) =
          (\<lambda>root. ?W root * ?D root)"
      by (rule ext, rule W_D [symmetric])
    show ?thesis
      unfolding convolution_eq by (rule holder(1))
  qed
  have convolution_integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>root. f root * g (output - root))"
    by (rule integral_nonneg_AE)
      (simp add: f_nonnegative g_nonnegative)
  have H_nn:
      "?H = ennreal
        (integral\<^sup>L lborel (\<lambda>root. f root * g (output - root)))"
    by (rule nn_integral_eq_integral[OF convolution_integrable])
      (simp add: f_nonnegative g_nonnegative)
  show convolution_finite: "?H < \<infinity>"
    using H_nn by simp
  have holder_bound:
      "(integral\<^sup>L lborel
          (\<lambda>root. f root * g (output - root))) powr t \<le>
        ?I_W powr (t - 1) * ?I_U"
  proof -
    have raw:
        "(integral\<^sup>L lborel (\<lambda>root. ?W root * ?D root)) powr t
          \<le> ?I_W powr (t / ?h) *
            integral\<^sup>L lborel
              (\<lambda>root. ?W root * ?D root powr t)"
      by (rule holder(2))
    show ?thesis
      using raw t_over_h
      by (simp only: W_D W_D_power)
  qed
  have scaled_bound:
      "?I_W powr (t - 1) * ?I_U \<le>
        (?I_f * ?I_g) powr ((t - 1) / 2) * ?I_U"
    by (rule mult_right_mono[OF W_power_bound U_integral_nonnegative])
  have real_bound:
      "(integral\<^sup>L lborel
          (\<lambda>root. f root * g (output - root))) powr t \<le>
        ?I_U * (?I_f * ?I_g) powr ((t - 1) / 2)"
  proof -
    have ordered:
        "(integral\<^sup>L lborel
            (\<lambda>root. f root * g (output - root))) powr t \<le>
          (?I_f * ?I_g) powr ((t - 1) / 2) * ?I_U"
      by (rule order_trans[OF holder_bound scaled_bound])
    show ?thesis
      using ordered by (simp add: mult.commute)
  qed
  have H_real:
      "enn2real ?H =
        integral\<^sup>L lborel (\<lambda>root. f root * g (output - root))"
    using H_nn convolution_integral_nonnegative by simp
  have U_real: "enn2real ?U_nn = ?I_U"
    using U_nn U_integral_nonnegative by simp
  show convolution_power_bound:
      "enn2real ?H powr t \<le>
        enn2real ?U_nn * (?I_f * ?I_g) powr ((t - 1) / 2)"
    using real_bound H_real U_real by simp
qed

end
