theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Real_Bridge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Real_Representatives"
begin

section \<open>Real bridge for positive extended-real convolution\<close>

definition slp_positive_ennreal_convolution ::
    "(slp_point \<Rightarrow> ennreal) \<Rightarrow> (slp_point \<Rightarrow> ennreal) \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_positive_ennreal_convolution F G output =
    (\<integral>\<^sup>+ root. F root * G (output - root) \<partial>lborel)"

lemma slp_positive_ennreal_convolution_measurable:
  assumes F_measurable[measurable]: "F \<in> borel_measurable lborel"
    and G_measurable[measurable]: "G \<in> borel_measurable lborel"
  shows "slp_positive_ennreal_convolution F G \<in> borel_measurable lborel"
  unfolding slp_positive_ennreal_convolution_def by measurable

theorem slp_positive_ennreal_convolution_real_bridge_AE:
  fixes F G :: "slp_point \<Rightarrow> ennreal"
    and t conjugate_t :: real
  assumes t_lower: "1 < t"
    and conjugate_lower: "1 < conjugate_t"
    and conjugate: "1 / t + 1 / conjugate_t = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane 1 F"
    and G_lp: "slp_positive_ennreal_lp_on_plane t G"
  shows
    "AE output in lborel.
      slp_positive_ennreal_convolution F G output =
        ennreal (integral\<^sup>L lborel
          (\<lambda>root. enn2real (F root) *
            enn2real (G (output - root))))"
proof -
  let ?f = "\<lambda>x. enn2real (F x)"
  let ?g = "\<lambda>x. enn2real (G x)"
  let ?datum = "\<lambda>root output. ?g (output - root)"
  let ?L = "integral\<^sup>L lborel (\<lambda>x. ?g x powr t)"
  note F_real = slp_positive_ennreal_L1_real_representative[OF F_lp]
  note G_real = slp_positive_ennreal_Lp_real_representative[OF G_lp]
  have G_measurable[measurable]: "G \<in> borel_measurable lborel"
    using G_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have f_measurable[measurable]: "?f \<in> borel_measurable lborel"
    by (rule F_real(1))
  have g_measurable[measurable]: "?g \<in> borel_measurable lborel"
    by (rule G_real(1))
  have f_nonnegative: "0 \<le> ?f x" for x
    by (rule F_real(2))
  have g_nonnegative: "0 \<le> ?g x" for x
    by (rule G_real(2))
  have f_integrable: "integrable lborel ?f"
    by (rule F_real(3))
  have g_power_integrable:
      "integrable lborel (\<lambda>x. ?g x powr t)"
    by (rule G_real(3))
  have F_lift: "AE x in lborel. F x = ennreal (?f x)"
    by (rule F_real(4))
  have G_lift: "AE x in lborel. G x = ennreal (?g x)"
    by (rule G_real(4))
  have datum_joint_measurable:
      "case_prod ?datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have datum_nonnegative: "0 \<le> ?datum root out" for root out
    by (rule g_nonnegative)
  have datum_power_integrable:
      "integrable lborel (\<lambda>output. ?datum root output powr t)"
    for root
  proof -
    have translated:
        "integrable lborel (\<lambda>output. ?g ((- root) + output) powr t)"
      by (rule slp_lborel_integrable_translate[OF g_power_integrable])
    show ?thesis using translated by simp
  qed
  have datum_power_exact:
      "integral\<^sup>L lborel (\<lambda>output. ?datum root output powr t) = ?L"
    for root
  proof -
    have translated:
        "integral\<^sup>L lborel (\<lambda>output. ?g ((- root) + output) powr t) =
          ?L"
      by (rule slp_lborel_integral_translate[OF g_power_integrable])
    show ?thesis using translated by simp
  qed
  have L_nonnegative: "0 \<le> ?L"
    by (rule integral_nonneg_AE) simp
  have fiber_power_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. ?f root * ?datum root output powr t)"
    by (rule slp_weighted_source_power_bound_plane(2)[OF
          f_measurable datum_joint_measurable f_nonnegative datum_nonnegative
          f_integrable datum_power_integrable])
      (use datum_power_exact L_nonnegative in auto)
  have fiber_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. ?f root * ?datum root output)"
    using fiber_power_integrable_AE
  proof eventually_elim
    fix out :: slp_point
    assume power_integrable:
      "integrable lborel (\<lambda>root. ?f root * ?datum root out powr t)"
    have datum_section_measurable:
        "(\<lambda>root. ?datum root out) \<in> borel_measurable lborel"
      by measurable
    show "integrable lborel (\<lambda>root. ?f root * ?datum root out)"
      by (rule slp_weighted_holder_power(1)[OF
            t_lower conjugate_lower conjugate f_measurable
            datum_section_measurable f_nonnegative _ f_integrable
            power_integrable])
        (rule datum_nonnegative)
  qed
  have G_lift_predicate:
      "Measurable.pred lborel (\<lambda>x. G x = ennreal (?g x))"
    by measurable
  have G_lift_shifted:
      "AE root in lborel.
        G (out - root) = ennreal (?g (out - root))"
    for out
    by (rule slp_AE_reflect_translate[OF G_lift_predicate G_lift])
  show ?thesis
    using fiber_integrable_AE
  proof eventually_elim
    fix out :: slp_point
    assume fiber_integrable:
      "integrable lborel (\<lambda>root. ?f root * ?datum root out)"
    have integrand_lift:
        "AE root in lborel.
          F root * G (out - root) =
            ennreal (?f root * ?g (out - root))"
      using F_lift G_lift_shifted[of out]
    proof eventually_elim
      fix root :: slp_point
      assume F_eq: "F root = ennreal (?f root)"
        and G_eq: "G (out - root) = ennreal (?g (out - root))"
      show "F root * G (out - root) =
          ennreal (?f root * ?g (out - root))"
      proof -
        have product_lift:
            "ennreal (?f root * ?g (out - root)) =
              ennreal (?f root) * ennreal (?g (out - root))"
          by (rule ennreal_mult[OF
                f_nonnegative[of root] g_nonnegative[of "out - root"]])
        show ?thesis
        proof (subst F_eq, subst G_eq)
          show "ennreal (?f root) * ennreal (?g (out - root)) =
              ennreal (?f root * ?g (out - root))"
            by (rule product_lift[symmetric])
        qed
      qed
    qed
    have extended_real:
        "slp_positive_ennreal_convolution F G out =
          (\<integral>\<^sup>+ root. ?f root * ?g (out - root) \<partial>lborel)"
      unfolding slp_positive_ennreal_convolution_def
      by (rule nn_integral_cong_AE)
        (use integrand_lift in \<open>eventually_elim, simp\<close>)
    have real_nn:
        "(\<integral>\<^sup>+ root. ?f root * ?g (out - root) \<partial>lborel) =
          ennreal (integral\<^sup>L lborel
            (\<lambda>root. ?f root * ?g (out - root)))"
      by (rule nn_integral_eq_integral[OF fiber_integrable])
        (rule AE_I2, simp add: f_nonnegative g_nonnegative)
    show "slp_positive_ennreal_convolution F G out =
        ennreal (integral\<^sup>L lborel
          (\<lambda>root. ?f root * ?g (out - root)))"
      using extended_real real_nn by simp
  qed
qed

end
