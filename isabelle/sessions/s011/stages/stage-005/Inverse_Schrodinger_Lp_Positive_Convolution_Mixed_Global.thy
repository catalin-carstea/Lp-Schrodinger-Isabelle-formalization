theory Inverse_Schrodinger_Lp_Positive_Convolution_Mixed_Global
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Convolution_Mixed_Pointwise"
begin

section \<open>Global mixed-exponent convolution square bound\<close>

lemma slp_positive_real_convolution_mass:
  fixes f g :: "slp_point \<Rightarrow> real"
  assumes f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_integrable: "integrable lborel f"
    and g_integrable: "integrable lborel g"
  shows
    "(\<integral>\<^sup>+ out. \<integral>\<^sup>+ root.
        ennreal (f root * g (out - root))
        \<partial>lborel \<partial>lborel) =
      ennreal
        (integral\<^sup>L lborel f * integral\<^sup>L lborel g)"
proof -
  let ?I_f = "integral\<^sup>L lborel f"
  let ?I_g = "integral\<^sup>L lborel g"
  have f_integral_nonnegative: "0 \<le> ?I_f"
    by (rule integral_nonneg_AE, rule AE_I2, rule f_nonnegative)
  have g_integral_nonnegative: "0 \<le> ?I_g"
    by (rule integral_nonneg_AE, rule AE_I2, rule g_nonnegative)
  have joint_measurable:
      "case_prod (\<lambda>out root. ennreal (f root * g (out - root)))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have swap:
      "(\<integral>\<^sup>+ out. \<integral>\<^sup>+ root.
          ennreal (f root * g (out - root))
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ out.
          ennreal (f root * g (out - root))
          \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF joint_measurable] by simp
  have translated_integrable:
      "integrable lborel (\<lambda>out. g ((- shift) + out))"
    for shift
    by (rule slp_lborel_integrable_translate[OF g_integrable])
  have translated_integral:
      "integral\<^sup>L lborel (\<lambda>out. g ((- shift) + out)) = ?I_g"
    for shift
    by (rule slp_lborel_integral_translate[OF g_integrable])
  have translated_nn_integral:
      "(\<integral>\<^sup>+ out. ennreal (g (out - shift)) \<partial>lborel) =
        ennreal ?I_g"
    for shift
  proof -
    have ordinary:
        "(\<integral>\<^sup>+ out. ennreal (g (out - shift)) \<partial>lborel) =
          ennreal
            (integral\<^sup>L lborel (\<lambda>out. g (out - shift)))"
    proof (rule nn_integral_eq_integral)
      show "integrable lborel (\<lambda>out. g (out - shift))"
        using translated_integrable[of shift] by simp
      show "AE out in lborel. 0 \<le> g (out - shift)"
        by (rule AE_I2, simp add: g_nonnegative)
    qed
    have ordinary_integral:
        "integral\<^sup>L lborel (\<lambda>out. g (out - shift)) = ?I_g"
      using translated_integral[of shift] by simp
    show ?thesis using ordinary ordinary_integral by simp
  qed
  have inner:
      "(\<integral>\<^sup>+ out. ennreal (f root * g (out - root))
          \<partial>lborel) =
        ennreal (f root) * ennreal ?I_g"
    for root
  proof -
    have product:
        "ennreal (f root * g (out - root)) =
          ennreal (f root) * ennreal (g (out - root))"
      for out
      by (rule ennreal_mult[OF f_nonnegative g_nonnegative])
    have pull:
        "(\<integral>\<^sup>+ out.
            ennreal (f root) * ennreal (g (out - root)) \<partial>lborel) =
          ennreal (f root) *
            (\<integral>\<^sup>+ out. ennreal (g (out - root)) \<partial>lborel)"
      by (rule nn_integral_cmult) measurable
    show ?thesis
      using product pull translated_nn_integral[of root] by simp
  qed
  have f_nn_integral:
      "(\<integral>\<^sup>+ root. ennreal (f root) \<partial>lborel) =
        ennreal ?I_f"
    by (rule nn_integral_eq_integral[OF f_integrable])
      (rule AE_I2, simp add: f_nonnegative)
  have outer:
      "(\<integral>\<^sup>+ root. ennreal (f root) * ennreal ?I_g
          \<partial>lborel) =
        ennreal ?I_f * ennreal ?I_g"
  proof -
    have pull:
        "(\<integral>\<^sup>+ root. ennreal ?I_g * ennreal (f root)
            \<partial>lborel) =
          ennreal ?I_g *
            (\<integral>\<^sup>+ root. ennreal (f root) \<partial>lborel)"
      by (rule nn_integral_cmult) measurable
    show ?thesis using pull f_nn_integral by (simp add: mult.commute)
  qed
  have converted:
      "ennreal ?I_f * ennreal ?I_g = ennreal (?I_f * ?I_g)"
    by (rule ennreal_mult[OF f_integral_nonnegative
          g_integral_nonnegative, symmetric])
  show ?thesis
    using swap inner outer converted by simp
qed

theorem slp_positive_convolution_mixed_global_square:
  fixes a b q r :: real
    and f g :: "slp_point \<Rightarrow> real"
    and H :: "slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and b_lower: "1 < b"
    and b_upper: "b < 2"
    and q_lower: "1 < q"
    and r_lower: "1 < r"
    and split_conjugate: "1 / q + 1 / r = 1"
    and q_scale: "(2 - a) * q = a"
    and r_scale: "(2 - b) * r = b"
    and f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. f x powr a)"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. g x powr b)"
  defines
    "H \<equiv> \<lambda>out.
      (\<integral>\<^sup>+ root. ennreal (f root * g (out - root))
        \<partial>lborel)"
  shows H_measurable: "H \<in> borel_measurable lborel"
    and H_finite: "AE out in lborel. H out < \<infinity>"
    and H_square_integrable:
      "integrable lborel (\<lambda>out. enn2real (H out) powr 2)"
    and H_square_bound:
      "(\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel) \<le>
        ennreal
          ((integral\<^sup>L lborel (\<lambda>x. f x powr a) *
              integral\<^sup>L lborel (\<lambda>x. g x powr b)) *
            (integral\<^sup>L lborel (\<lambda>x. f x powr a) / q +
              integral\<^sup>L lborel (\<lambda>x. g x powr b) / r))"
proof -
  let ?F = "\<lambda>x. f x powr a"
  let ?G = "\<lambda>x. g x powr b"
  let ?U = "\<lambda>out.
    (\<integral>\<^sup>+ root. ennreal (?F root * ?G (out - root))
      \<partial>lborel)"
  let ?I_f = "integral\<^sup>L lborel ?F"
  let ?I_g = "integral\<^sup>L lborel ?G"
  let ?C = "?I_f / q + ?I_g / r"
  have F_measurable[measurable]: "?F \<in> borel_measurable lborel"
    by measurable
  have G_measurable[measurable]: "?G \<in> borel_measurable lborel"
    by measurable
  have F_nonnegative: "0 \<le> ?F x" for x by simp
  have G_nonnegative: "0 \<le> ?G x" for x by simp
  have I_f_nonnegative: "0 \<le> ?I_f"
    by (rule integral_nonneg_AE, rule AE_I2, rule F_nonnegative)
  have I_g_nonnegative: "0 \<le> ?I_g"
    by (rule integral_nonneg_AE, rule AE_I2, rule G_nonnegative)
  have q_positive: "0 < q" and r_positive: "0 < r"
    using q_lower r_lower by linarith+
  have C_nonnegative: "0 \<le> ?C"
    using I_f_nonnegative I_g_nonnegative q_positive r_positive by simp
  show H_measurable: "H \<in> borel_measurable lborel"
    unfolding H_def by measurable
  have U_measurable[measurable]: "?U \<in> borel_measurable lborel"
    by measurable
  have pointwise:
      "H out ^ 2 \<le> ?U out * ennreal ?C"
    for out
    unfolding H_def
    by (rule slp_positive_convolution_mixed_pointwise_square_bound[OF
          a_lower a_upper b_lower b_upper q_lower r_lower split_conjugate
          q_scale r_scale f_measurable g_measurable f_nonnegative
          g_nonnegative f_power_integrable g_power_integrable])
  have U_mass:
      "(\<integral>\<^sup>+ out. ?U out \<partial>lborel) =
        ennreal (?I_f * ?I_g)"
    by (rule slp_positive_real_convolution_mass[OF F_measurable G_measurable
          F_nonnegative G_nonnegative f_power_integrable
          g_power_integrable])
  have integrated:
      "(\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel) \<le>
        (\<integral>\<^sup>+ out. ?U out \<partial>lborel) * ennreal ?C"
  proof -
    have mono:
        "(\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel) \<le>
          (\<integral>\<^sup>+ out. ?U out * ennreal ?C \<partial>lborel)"
      by (rule nn_integral_mono) (rule pointwise)
    have pull:
        "(\<integral>\<^sup>+ out. ennreal ?C * ?U out \<partial>lborel) =
          ennreal ?C * (\<integral>\<^sup>+ out. ?U out \<partial>lborel)"
      by (rule nn_integral_cmult[OF U_measurable])
    show ?thesis using mono pull by (simp add: mult.commute)
  qed
  have converted:
      "ennreal (?I_f * ?I_g) * ennreal ?C =
        ennreal ((?I_f * ?I_g) * ?C)"
  proof -
    have product_nonnegative: "0 \<le> ?I_f * ?I_g"
      using I_f_nonnegative I_g_nonnegative by simp
    show ?thesis
      by (rule ennreal_mult[OF product_nonnegative C_nonnegative, symmetric])
  qed
  have square_bound:
      "(\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel) \<le>
        ennreal ((?I_f * ?I_g) * ?C)"
    using integrated U_mass converted by simp
  show H_square_bound:
      "(\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel) \<le>
        ennreal
          ((integral\<^sup>L lborel (\<lambda>x. f x powr a) *
              integral\<^sup>L lborel (\<lambda>x. g x powr b)) *
            (integral\<^sup>L lborel (\<lambda>x. f x powr a) / q +
              integral\<^sup>L lborel (\<lambda>x. g x powr b) / r))"
    by (rule square_bound)
  have square_integral_less_top:
      "(\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel) < \<infinity>"
    by (rule le_less_trans[OF square_bound]) simp
  have H_square_measurable:
      "(\<lambda>out. H out ^ 2) \<in> borel_measurable lborel"
    using H_measurable by measurable
  have H_square_finite:
      "AE out in lborel. H out ^ 2 \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF H_square_measurable])
      (use square_integral_less_top in simp)
  show H_finite: "AE out in lborel. H out < \<infinity>"
    using H_square_finite
  proof eventually_elim
    fix out :: slp_point
    assume square_not_top: "H out ^ 2 \<noteq> \<infinity>"
    show "H out < \<infinity>"
      using square_not_top by (simp add: less_top power_eq_top_ennreal)
  qed
  have real_square_measurable:
      "(\<lambda>out. enn2real (H out) powr 2) \<in> borel_measurable lborel"
    using H_measurable by measurable
  have real_square_nn:
      "(\<integral>\<^sup>+ out. enn2real (H out) powr 2 \<partial>lborel) =
        (\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel)"
  proof (rule nn_integral_cong_AE)
    show "AE out in lborel.
        ennreal (enn2real (H out) powr 2) = H out ^ 2"
      using H_finite
    proof eventually_elim
      fix out :: slp_point
      assume H_out_finite: "H out < \<infinity>"
      have H_lift: "H out = ennreal (enn2real (H out))"
        using H_out_finite by simp
      have real_power:
          "enn2real (H out) powr 2 = enn2real (H out) ^ 2"
        by simp
      show "ennreal (enn2real (H out) powr 2) = H out ^ 2"
        unfolding real_power
        apply (subst (2) H_lift)
        apply (rule ennreal_power [symmetric])
        apply simp
        done
    qed
  qed
  show H_square_integrable:
      "integrable lborel (\<lambda>out. enn2real (H out) powr 2)"
  proof (rule integrableI_nn_integral_finite[OF real_square_measurable])
    show "AE out in lborel. 0 \<le> enn2real (H out) powr 2" by simp
    show "(\<integral>\<^sup>+ out. enn2real (H out) powr 2 \<partial>lborel) =
        ennreal
          (enn2real
            (\<integral>\<^sup>+ out. H out ^ 2 \<partial>lborel))"
      using real_square_nn square_integral_less_top by simp
  qed
qed

end
