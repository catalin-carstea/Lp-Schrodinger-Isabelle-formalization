theory Inverse_Schrodinger_Lp_Positive_Ennreal_Real_Representatives
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Convolution_L1_Power_Normalized"
begin

section \<open>Real representatives of positive finite extended-real data\<close>

lemma slp_positive_ennreal_L1_real_representative:
  fixes F :: "slp_point \<Rightarrow> ennreal"
  assumes F_lp: "slp_positive_ennreal_lp_on_plane 1 F"
  shows lp_real_measurable:
      "(\<lambda>x. enn2real (F x)) \<in> borel_measurable lborel"
    and real_nonnegative: "\<And>x. 0 \<le> enn2real (F x)"
    and real_integrable: "integrable lborel (\<lambda>x. enn2real (F x))"
    and real_lift: "AE x in lborel. F x = ennreal (enn2real (F x))"
    and mass_identity:
      "(\<integral>\<^sup>+ x. F x \<partial>lborel) =
        ennreal (integral\<^sup>L lborel (\<lambda>x. enn2real (F x)))"
proof -
  have F_measurable: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr 1)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  show "(\<lambda>x. enn2real (F x)) \<in> borel_measurable lborel"
    using F_measurable by measurable
  show "\<And>x. 0 \<le> enn2real (F x)" by simp
  show "integrable lborel (\<lambda>x. enn2real (F x))"
    using F_power_integrable by simp
  show "AE x in lborel. F x = ennreal (enn2real (F x))"
    using F_finite by eventually_elim simp
  have lift_integral:
      "(\<integral>\<^sup>+ x. F x \<partial>lborel) =
        (\<integral>\<^sup>+ x. ennreal (enn2real (F x)) \<partial>lborel)"
    by (rule nn_integral_cong_AE)
      (use F_finite in \<open>eventually_elim, simp\<close>)
  have real_integral:
      "(\<integral>\<^sup>+ x. enn2real (F x) \<partial>lborel) =
        ennreal (integral\<^sup>L lborel (\<lambda>x. enn2real (F x)))"
    by (rule nn_integral_eq_integral)
      (use F_power_integrable in simp_all)
  show "(\<integral>\<^sup>+ x. F x \<partial>lborel) =
      ennreal (integral\<^sup>L lborel (\<lambda>x. enn2real (F x)))"
    using lift_integral real_integral by simp
qed

lemma slp_positive_ennreal_Lp_real_representative:
  fixes G :: "slp_point \<Rightarrow> ennreal"
    and t :: real
  assumes G_lp: "slp_positive_ennreal_lp_on_plane t G"
  shows real_measurable:
      "(\<lambda>x. enn2real (G x)) \<in> borel_measurable lborel"
    and lp_real_nonnegative: "\<And>x. 0 \<le> enn2real (G x)"
    and lp_real_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (G x) powr t)"
    and lp_real_lift: "AE x in lborel. G x = ennreal (enn2real (G x))"
proof -
  have G_measurable: "G \<in> borel_measurable lborel"
    and G_finite: "AE x in lborel. G x < top"
    and G_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (G x) powr t)"
    using G_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  show "(\<lambda>x. enn2real (G x)) \<in> borel_measurable lborel"
    using G_measurable by measurable
  show "\<And>x. 0 \<le> enn2real (G x)" by simp
  show "integrable lborel (\<lambda>x. enn2real (G x) powr t)"
    by (rule G_power_integrable)
  show "AE x in lborel. G x = ennreal (enn2real (G x))"
    using G_finite by eventually_elim simp
qed

end
