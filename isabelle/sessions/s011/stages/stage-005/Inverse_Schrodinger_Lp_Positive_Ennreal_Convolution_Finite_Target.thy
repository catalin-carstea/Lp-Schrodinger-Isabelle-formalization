theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Finite_Target
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Convolution_Finite_Target_Global"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_L2"
begin

section \<open>Positive extended-real convolution at finite targets\<close>

theorem slp_positive_ennreal_convolution_finite_target:
  fixes t :: real
    and F G :: "slp_point \<Rightarrow> ennreal"
  assumes t_lower: "1 < t"
    and F_lp: "slp_positive_ennreal_lp_on_plane
      (slp_mixed_unweighted_branch_exponent t) F"
    and G_lp: "slp_positive_ennreal_lp_on_plane
      (slp_mixed_unweighted_branch_exponent t) G"
  shows convolution_Lt:
      "slp_positive_ennreal_lp_on_plane t
        (slp_positive_ennreal_convolution F G)"
    and convolution_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>out. enn2real
            (slp_positive_ennreal_convolution F G out) powr t)
        \<le>
        (integral\<^sup>L lborel
            (\<lambda>x. enn2real (F x) powr
              slp_mixed_unweighted_branch_exponent t) *
          integral\<^sup>L lborel
            (\<lambda>x. enn2real (G x) powr
              slp_mixed_unweighted_branch_exponent t)) *
        (integral\<^sup>L lborel
            (\<lambda>x. enn2real (F x) powr
              slp_mixed_unweighted_branch_exponent t) *
          integral\<^sup>L lborel
            (\<lambda>x. enn2real (G x) powr
              slp_mixed_unweighted_branch_exponent t))
          powr ((t - 1) / 2)"
proof -
  let ?a = "slp_mixed_unweighted_branch_exponent t"
  let ?f = "\<lambda>x. enn2real (F x)"
  let ?g = "\<lambda>x. enn2real (G x)"
  let ?H = "\<lambda>out.
    (\<integral>\<^sup>+ root. ennreal (?f root * ?g (out - root))
      \<partial>lborel)"
  note F_real = slp_positive_ennreal_Lp_real_representative[OF F_lp]
  note G_real = slp_positive_ennreal_Lp_real_representative[OF G_lp]
  have F_measurable[measurable]: "F \<in> borel_measurable lborel"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
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
  have f_power_integrable: "integrable lborel (\<lambda>x. ?f x powr ?a)"
    by (rule F_real(3))
  have g_power_integrable: "integrable lborel (\<lambda>x. ?g x powr ?a)"
    by (rule G_real(3))
  have F_lift: "AE x in lborel. F x = ennreal (?f x)"
    by (rule F_real(4))
  have G_lift: "AE x in lborel. G x = ennreal (?g x)"
    by (rule G_real(4))
  have G_lift_predicate:
      "Measurable.pred lborel (\<lambda>x. G x = ennreal (?g x))"
    by measurable
  have G_lift_shifted:
      "AE root in lborel. G (out - root) = ennreal (?g (out - root))"
    for out
    by (rule slp_AE_reflect_translate[OF G_lift_predicate G_lift])
  have convolution_real:
      "slp_positive_ennreal_convolution F G out = ?H out"
    for out
  proof -
    have integrand_lift:
        "AE root in lborel.
          F root * G (out - root) =
            ennreal (?f root * ?g (out - root))"
      using F_lift G_lift_shifted[of out]
    proof eventually_elim
      fix root :: slp_point
      assume F_eq: "F root = ennreal (?f root)"
        and G_eq: "G (out - root) = ennreal (?g (out - root))"
      have product_lift:
          "ennreal (?f root * ?g (out - root)) =
            ennreal (?f root) * ennreal (?g (out - root))"
        by (rule ennreal_mult[OF
              f_nonnegative[of root] g_nonnegative[of "out - root"]])
      show "F root * G (out - root) =
          ennreal (?f root * ?g (out - root))"
        using F_eq G_eq product_lift by simp
    qed
    show ?thesis
      unfolding slp_positive_ennreal_convolution_def
      by (rule nn_integral_cong_AE)
        (use integrand_lift in \<open>eventually_elim, simp\<close>)
  qed
  note global = slp_positive_convolution_finite_target_global[OF
      t_lower f_measurable g_measurable f_nonnegative g_nonnegative
      f_power_integrable g_power_integrable]
  have convolution_eq:
      "slp_positive_ennreal_convolution F G = ?H"
    by (rule ext, rule convolution_real)
  show convolution_Lt:
      "slp_positive_ennreal_lp_on_plane t
        (slp_positive_ennreal_convolution F G)"
    unfolding convolution_eq by (rule global(5))
  have power_function_eq:
      "(\<lambda>out. enn2real
          (slp_positive_ennreal_convolution F G out) powr t) =
        (\<lambda>out. enn2real (?H out) powr t)"
    by (rule ext, subst convolution_real, rule refl)
  show convolution_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>out. enn2real
            (slp_positive_ennreal_convolution F G out) powr t)
        \<le>
        (integral\<^sup>L lborel (\<lambda>x. ?f x powr ?a) *
          integral\<^sup>L lborel (\<lambda>x. ?g x powr ?a)) *
        (integral\<^sup>L lborel (\<lambda>x. ?f x powr ?a) *
          integral\<^sup>L lborel (\<lambda>x. ?g x powr ?a))
          powr ((t - 1) / 2)"
    using global(4) power_function_eq by simp
qed

end
