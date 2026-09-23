theory Inverse_Schrodinger_Lp_Born_Root_Finite_Power
  imports Inverse_Schrodinger_Lp_Born_Root_Real_Bridge
begin

section \<open>Positive Lp control for an exact root-paired density\<close>

lemma slp_positive_root_output_density_finite_power:
  fixes R a b L :: real
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_integrable: "integrable lborel root_weight"
    and density_lp:
      "\<And>root. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n root)"
    and density_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_positive_output_density R cutoff potential terminal_weight n
            root output) powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows root_lp:
    "slp_positive_ennreal_lp_on_plane a
      (slp_positive_root_output_density R cutoff potential terminal_weight n
        root_weight)"
    and root_power_bound:
    "integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_positive_root_output_density R cutoff potential terminal_weight n
            root_weight output) powr a) \<le>
      (integral\<^sup>L lborel (\<lambda>root. norm (root_weight root)))
          powr (a / b) *
        (L * integral\<^sup>L lborel
          (\<lambda>root. norm (root_weight root)))"
proof -
  let ?density =
    "slp_positive_output_density R cutoff potential terminal_weight n"
  let ?root_density =
    "slp_positive_root_output_density R cutoff potential terminal_weight n
      root_weight"
  let ?weight = "\<lambda>root. norm (root_weight root)"
  let ?datum = "\<lambda>root output. enn2real (?density root output)"
  let ?H = "\<lambda>output. integral\<^sup>L lborel
    (\<lambda>root. ?weight root * ?datum root output)"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable by measurable
  have density_joint[measurable]:
      "case_prod ?density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable])
  have weight_measurable:
      "?weight \<in> borel_measurable lborel"
    using root_weight_measurable by measurable
  have datum_joint_measurable:
      "case_prod ?datum \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have weight_nonnegative: "0 \<le> ?weight root" for root by simp
  have datum_nonnegative: "0 \<le> ?datum root out" for root out by simp
  have weight_integrable: "integrable lborel ?weight"
    by (rule integrable_norm[OF root_weight_integrable])
  have datum_power_integrable:
      "integrable lborel (\<lambda>output. ?datum root output powr a)"
    for root
    using density_lp[of root]
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have fiber_power_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. ?weight root * ?datum root output powr a)"
    by (rule slp_weighted_source_power_bound_plane(2)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          density_power_bound L_nonnegative])
  have real_fiber_integrable:
      "AE output in lborel. integrable lborel
        (\<lambda>root. ?weight root * ?datum root output)"
    using fiber_power_integrable_AE
  proof eventually_elim
    fix out :: slp_point
    assume fiber_power:
      "integrable lborel
        (\<lambda>root. ?weight root * ?datum root out powr a)"
    have datum_section_measurable:
        "(\<lambda>root. ?datum root out) \<in> borel_measurable lborel"
      by measurable
    show "integrable lborel
        (\<lambda>root. ?weight root * ?datum root out)"
      by (rule slp_weighted_holder_power(1)[OF
            a_lower b_lower conjugate weight_measurable
            datum_section_measurable weight_nonnegative _ weight_integrable
            fiber_power])
        (rule datum_nonnegative)
  qed
  have density_finite:
      "AE output in lborel. ?density root output < top"
    for root
    using density_lp[of root]
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have real_lift:
      "AE output in lborel. ?root_density output = ennreal (?H output)"
    by (rule slp_positive_root_output_density_real_lift_AE[OF
          cutoff_measurable potential_measurable terminal_weight_measurable
          root_weight_integrable density_finite real_fiber_integrable])
  have real_power_integrable:
      "integrable lborel (\<lambda>output. ?H output powr a)"
    by (rule slp_positive_root_output_density_real_finite_power(1)[OF
          a_lower b_lower conjugate cutoff_measurable potential_measurable
          terminal_weight_measurable root_weight_integrable density_lp
          density_power_bound L_nonnegative])
  have real_power_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?H output powr a) \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          (L * integral\<^sup>L lborel ?weight)"
    by (rule slp_positive_root_output_density_real_finite_power(2)[OF
          a_lower b_lower conjugate cutoff_measurable potential_measurable
          terminal_weight_measurable root_weight_integrable density_lp
          density_power_bound L_nonnegative])
  have root_measurable:
      "?root_density \<in> borel_measurable lborel"
    by (rule slp_positive_root_output_density_measurable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable
          root_weight_measurable])
  have root_finite: "AE output in lborel. ?root_density output < top"
    using real_lift
    by eventually_elim simp
  have H_nonnegative: "0 \<le> ?H out" for out
    by (rule integral_nonneg_AE) (rule AE_I2, simp)
  have power_identity:
      "AE output in lborel.
        enn2real (?root_density output) powr a = ?H output powr a"
    using real_lift
  proof eventually_elim
    fix out :: slp_point
    assume root_eq: "?root_density out = ennreal (?H out)"
    show "enn2real (?root_density out) powr a = ?H out powr a"
      using root_eq H_nonnegative[of out] by simp
  qed
  have root_power_measurable:
      "(\<lambda>output. enn2real (?root_density output) powr a)
        \<in> borel_measurable lborel"
    using root_measurable by measurable
  have real_power_measurable:
      "(\<lambda>output. ?H output powr a) \<in> borel_measurable lborel"
    using real_power_integrable by measurable
  have root_power_integrable:
      "integrable lborel
        (\<lambda>output. enn2real (?root_density output) powr a)"
    by (rule integrable_cong_AE_imp[OF
          real_power_integrable root_power_measurable])
      (use power_identity in eventually_elim; simp)
  show "slp_positive_ennreal_lp_on_plane a ?root_density"
    unfolding slp_positive_ennreal_lp_on_plane_def
    using root_measurable root_finite root_power_integrable by blast
  have exact_power:
      "integral\<^sup>L lborel
          (\<lambda>output. enn2real (?root_density output) powr a) =
        integral\<^sup>L lborel (\<lambda>output. ?H output powr a)"
    by (rule integral_cong_AE[OF root_power_measurable
          real_power_measurable power_identity])
  show "integral\<^sup>L lborel
        (\<lambda>output. enn2real (?root_density output) powr a) \<le>
      (integral\<^sup>L lborel ?weight) powr (a / b) *
        (L * integral\<^sup>L lborel ?weight)"
    using real_power_bound by (simp only: exact_power)
qed

end
