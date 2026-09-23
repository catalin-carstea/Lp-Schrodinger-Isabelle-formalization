theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Convolution_Mixed_Global"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Real_Bridge"
begin

section \<open>Positive extended-real mixed convolution in L2\<close>

theorem slp_positive_ennreal_convolution_mixed_L2:
  fixes a b q r :: real
    and F G :: "slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and b_lower: "1 < b"
    and b_upper: "b < 2"
    and q_lower: "1 < q"
    and r_lower: "1 < r"
    and split_conjugate: "1 / q + 1 / r = 1"
    and q_scale: "(2 - a) * q = a"
    and r_scale: "(2 - b) * r = b"
    and F_lp: "slp_positive_ennreal_lp_on_plane a F"
    and G_lp: "slp_positive_ennreal_lp_on_plane b G"
  shows convolution_L2:
      "slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution F G)"
    and convolution_square_bound:
      "(\<integral>\<^sup>+ out.
          slp_positive_ennreal_convolution F G out ^ 2
          \<partial>lborel) \<le>
        ennreal
          ((integral\<^sup>L lborel
              (\<lambda>x. enn2real (F x) powr a) *
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (G x) powr b)) *
          (integral\<^sup>L lborel
              (\<lambda>x. enn2real (F x) powr a) / q +
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (G x) powr b) / r))"
proof -
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
  have f_power_integrable:
      "integrable lborel (\<lambda>x. ?f x powr a)"
    by (rule F_real(3))
  have g_power_integrable:
      "integrable lborel (\<lambda>x. ?g x powr b)"
    by (rule G_real(3))
  have F_lift: "AE x in lborel. F x = ennreal (?f x)"
    by (rule F_real(4))
  have G_lift: "AE x in lborel. G x = ennreal (?g x)"
    by (rule G_real(4))
  have G_lift_predicate:
      "Measurable.pred lborel (\<lambda>x. G x = ennreal (?g x))"
    by measurable
  have G_lift_shifted:
      "AE root in lborel.
        G (out - root) = ennreal (?g (out - root))"
    for out
    by (rule slp_AE_reflect_translate[OF G_lift_predicate G_lift])
  have convolution_real: "slp_positive_ennreal_convolution F G out = ?H out"
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
  note global = slp_positive_convolution_mixed_global_square[OF
      a_lower a_upper b_lower b_upper q_lower r_lower split_conjugate
      q_scale r_scale f_measurable g_measurable f_nonnegative
      g_nonnegative f_power_integrable g_power_integrable]
  have H_measurable: "?H \<in> borel_measurable lborel"
    by (rule global(1))
  have H_finite: "AE out in lborel. ?H out < \<infinity>"
    by (rule global(2))
  have H_power_integrable:
      "integrable lborel (\<lambda>out. enn2real (?H out) powr 2)"
    by (rule global(3))
  have H_square_bound:
      "(\<integral>\<^sup>+ out. ?H out ^ 2 \<partial>lborel) \<le>
        ennreal
          ((integral\<^sup>L lborel (\<lambda>x. ?f x powr a) *
              integral\<^sup>L lborel (\<lambda>x. ?g x powr b)) *
            (integral\<^sup>L lborel (\<lambda>x. ?f x powr a) / q +
              integral\<^sup>L lborel (\<lambda>x. ?g x powr b) / r))"
    by (rule global(4))
  have convolution_measurable:
      "slp_positive_ennreal_convolution F G \<in> borel_measurable lborel"
    by (rule slp_positive_ennreal_convolution_measurable[OF
          F_measurable G_measurable])
  have convolution_finite:
      "AE out in lborel.
        slp_positive_ennreal_convolution F G out < \<infinity>"
    using H_finite
    apply eventually_elim
    using convolution_real by simp
  have convolution_power_integrable:
      "integrable lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution F G out) powr 2)"
  proof -
    have function_eq:
        "(\<lambda>out. enn2real
            (slp_positive_ennreal_convolution F G out) powr 2) =
          (\<lambda>out. enn2real (?H out) powr 2)"
      by (rule ext, subst convolution_real, rule refl)
    show ?thesis
      using H_power_integrable function_eq by simp
  qed
  note convolution_finite_top =
    convolution_finite[unfolded infinity_ennreal_def]
  show convolution_L2:
      "slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution F G)"
    unfolding slp_positive_ennreal_lp_on_plane_def
    apply (intro conjI)
      apply (fact convolution_measurable)
     apply (fact convolution_finite_top)
    apply (fact convolution_power_integrable)
    done
  show convolution_square_bound:
      "(\<integral>\<^sup>+ out.
          slp_positive_ennreal_convolution F G out ^ 2
          \<partial>lborel) \<le>
        ennreal
          ((integral\<^sup>L lborel
              (\<lambda>x. enn2real (F x) powr a) *
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (G x) powr b)) *
          (integral\<^sup>L lborel
              (\<lambda>x. enn2real (F x) powr a) / q +
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (G x) powr b) / r))"
  proof -
    have square_integral_eq:
        "(\<integral>\<^sup>+ out.
            slp_positive_ennreal_convolution F G out ^ 2
            \<partial>lborel) =
          (\<integral>\<^sup>+ out. ?H out ^ 2 \<partial>lborel)"
      by (rule nn_integral_cong) (subst convolution_real, rule refl)
    show ?thesis using H_square_bound square_integral_eq by simp
  qed
qed

end
