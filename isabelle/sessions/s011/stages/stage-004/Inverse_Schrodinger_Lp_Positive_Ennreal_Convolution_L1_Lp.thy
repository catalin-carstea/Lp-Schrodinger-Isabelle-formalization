theory Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_L1_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Real_Bridge"
begin

section \<open>Positive extended-real endpoint Young theorem\<close>

theorem slp_positive_ennreal_convolution_L1_Lp:
  fixes F G :: "slp_point \<Rightarrow> ennreal"
    and t conjugate_t :: real
  assumes t_lower: "1 < t"
    and conjugate_lower: "1 < conjugate_t"
    and conjugate: "1 / t + 1 / conjugate_t = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane 1 F"
    and G_lp: "slp_positive_ennreal_lp_on_plane t G"
  shows convolution_lp:
    "slp_positive_ennreal_lp_on_plane t
      (slp_positive_ennreal_convolution F G)"
    and convolution_power_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          enn2real (slp_positive_ennreal_convolution F G output) powr t)
      \<le> enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) powr t *
        integral\<^sup>L lborel (\<lambda>x. enn2real (G x) powr t)"
proof -
  let ?f = "\<lambda>x. enn2real (F x)"
  let ?g = "\<lambda>x. enn2real (G x)"
  let ?H = "\<lambda>output.
    integral\<^sup>L lborel (\<lambda>root. ?f root * ?g (output - root))"
  let ?C = "slp_positive_ennreal_convolution F G"
  note F_real = slp_positive_ennreal_L1_real_representative[OF F_lp]
  note G_real = slp_positive_ennreal_Lp_real_representative[OF G_lp]
  have F_measurable[measurable]: "F \<in> borel_measurable lborel"
    and G_measurable[measurable]: "G \<in> borel_measurable lborel"
    using F_lp G_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
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
  have H_power_integrable:
      "integrable lborel (\<lambda>output. ?H output powr t)"
    by (rule slp_positive_convolution_L1_power_bound_normalized(1)[OF
          t_lower conjugate_lower conjugate f_measurable g_measurable
          f_nonnegative g_nonnegative f_integrable g_power_integrable])
  have H_power_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?H output powr t) \<le>
        (integral\<^sup>L lborel ?f) powr t *
          integral\<^sup>L lborel (\<lambda>x. ?g x powr t)"
    by (rule slp_positive_convolution_L1_power_bound_normalized(2)[OF
          t_lower conjugate_lower conjugate f_measurable g_measurable
          f_nonnegative g_nonnegative f_integrable g_power_integrable])
  have H_nonnegative: "0 \<le> ?H out" for out
    by (rule integral_nonneg_AE)
      (rule AE_I2, simp add: f_nonnegative g_nonnegative)
  have C_measurable: "?C \<in> borel_measurable lborel"
    by (rule slp_positive_ennreal_convolution_measurable[OF
          F_measurable G_measurable])
  have bridge: "AE output in lborel. ?C output = ennreal (?H output)"
    by (rule slp_positive_ennreal_convolution_real_bridge_AE[OF
          t_lower conjugate_lower conjugate F_lp G_lp])
  have C_finite: "AE output in lborel. ?C output < top"
    using bridge by eventually_elim simp
  have power_identity:
      "AE output in lborel.
        enn2real (?C output) powr t = ?H output powr t"
    using bridge
  proof eventually_elim
    fix out :: slp_point
    assume C_eq: "?C out = ennreal (?H out)"
    show "enn2real (?C out) powr t = ?H out powr t"
      unfolding C_eq using H_nonnegative[of out] by simp
  qed
  have C_power_measurable:
      "(\<lambda>output. enn2real (?C output) powr t)
        \<in> borel_measurable lborel"
    using C_measurable by measurable
  have C_power_integrable:
      "integrable lborel (\<lambda>output. enn2real (?C output) powr t)"
    by (rule integrable_cong_AE_imp[OF H_power_integrable
          C_power_measurable])
      (use power_identity in \<open>eventually_elim, simp\<close>)
  show "slp_positive_ennreal_lp_on_plane t ?C"
    unfolding slp_positive_ennreal_lp_on_plane_def
    using C_measurable C_finite C_power_integrable by blast
  have H_power_measurable:
      "(\<lambda>output. ?H output powr t) \<in> borel_measurable lborel"
    using H_power_integrable by measurable
  have power_integral_identity:
      "integral\<^sup>L lborel
          (\<lambda>output. enn2real (?C output) powr t) =
        integral\<^sup>L lborel (\<lambda>output. ?H output powr t)"
    by (rule integral_cong_AE[OF C_power_measurable H_power_measurable
          power_identity])
  have f_mass_nonnegative: "0 \<le> integral\<^sup>L lborel ?f"
    by (rule integral_nonneg_AE) (simp add: f_nonnegative)
  have mass_identity:
      "enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) =
        integral\<^sup>L lborel ?f"
    using F_real(5) f_mass_nonnegative by simp
  show "integral\<^sup>L lborel
        (\<lambda>output. enn2real (?C output) powr t) \<le>
      enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) powr t *
        integral\<^sup>L lborel (\<lambda>x. ?g x powr t)"
    using H_power_bound
    unfolding power_integral_identity mass_identity .
qed

end
