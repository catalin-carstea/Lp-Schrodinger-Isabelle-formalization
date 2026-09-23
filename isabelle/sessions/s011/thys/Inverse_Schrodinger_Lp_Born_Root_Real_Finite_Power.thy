theory Inverse_Schrodinger_Lp_Born_Root_Real_Finite_Power
  imports Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Plane_AE
    Inverse_Schrodinger_Lp_Born_One_Sided_Root_Density
begin

section \<open>Real power estimate for an exact root-paired density\<close>

lemma slp_positive_root_output_density_real_finite_power:
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
  shows target_integrable:
    "integrable lborel
      (\<lambda>output. (integral\<^sup>L lborel
        (\<lambda>root. norm (root_weight root) *
          enn2real (slp_positive_output_density R cutoff potential
            terminal_weight n root output))) powr a)"
    and target_bound:
    "integral\<^sup>L lborel
        (\<lambda>output. (integral\<^sup>L lborel
          (\<lambda>root. norm (root_weight root) *
            enn2real (slp_positive_output_density R cutoff potential
              terminal_weight n root output))) powr a) \<le>
      (integral\<^sup>L lborel (\<lambda>root. norm (root_weight root)))
          powr (a / b) *
        (L * integral\<^sup>L lborel
          (\<lambda>root. norm (root_weight root)))"
proof -
  let ?weight = "\<lambda>root. norm (root_weight root)"
  let ?datum = "\<lambda>root output.
    enn2real (slp_positive_output_density R cutoff potential terminal_weight n
      root output)"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable by measurable
  have density_joint[measurable]:
      "case_prod
        (slp_positive_output_density R cutoff potential terminal_weight n)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable])
  have weight_measurable:
      "?weight \<in> borel_measurable lborel"
    using root_weight_measurable by measurable
  have datum_joint_measurable:
      "case_prod ?datum \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have weight_nonnegative: "0 \<le> ?weight root" for root
    by simp
  have datum_nonnegative: "0 \<le> ?datum root out" for root out
    by simp
  have weight_integrable: "integrable lborel ?weight"
    by (rule integrable_norm[OF root_weight_integrable])
  have datum_power_integrable:
      "integrable lborel (\<lambda>output. ?datum root output powr a)"
    for root
    using density_lp[of root]
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have source_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>root. ?weight root * ?datum root output powr a))"
    by (rule slp_weighted_source_power_bound_plane(3)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          density_power_bound L_nonnegative])
  have fiber_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. ?weight root * ?datum root output powr a)"
    by (rule slp_weighted_source_power_bound_plane(2)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          density_power_bound L_nonnegative])
  have source_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>root. ?weight root * ?datum root output powr a)) \<le>
        L * integral\<^sup>L lborel ?weight"
    by (rule slp_weighted_source_power_bound_plane(4)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          density_power_bound L_nonnegative])
  have minkowski_integrable:
      "integrable lborel
        (\<lambda>output. (integral\<^sup>L lborel
          (\<lambda>root. ?weight root * ?datum root output)) powr a)"
    by (rule slp_integral_minkowski_power_plane_AE(1)[OF
          a_lower b_lower conjugate weight_measurable datum_joint_measurable
          weight_nonnegative datum_nonnegative weight_integrable
          fiber_integrable_AE source_integrable])
  have minkowski_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. (integral\<^sup>L lborel
            (\<lambda>root. ?weight root * ?datum root output)) powr a) \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root. ?weight root * ?datum root output powr a))"
    by (rule slp_integral_minkowski_power_plane_AE(2)[OF
          a_lower b_lower conjugate weight_measurable datum_joint_measurable
          weight_nonnegative datum_nonnegative weight_integrable
          fiber_integrable_AE source_integrable])
  have scale_nonnegative:
      "0 \<le> (integral\<^sup>L lborel ?weight) powr (a / b)"
    by simp
  have scaled_source:
      "(integral\<^sup>L lborel ?weight) powr (a / b) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root. ?weight root * ?datum root output powr a)) \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          (L * integral\<^sup>L lborel ?weight)"
    by (rule mult_left_mono[OF source_bound scale_nonnegative])
  show "integrable lborel
      (\<lambda>output. (integral\<^sup>L lborel
        (\<lambda>root. ?weight root * ?datum root output)) powr a)"
    by (rule minkowski_integrable)
  show "integral\<^sup>L lborel
        (\<lambda>output. (integral\<^sup>L lborel
          (\<lambda>root. ?weight root * ?datum root output)) powr a) \<le>
      (integral\<^sup>L lborel ?weight) powr (a / b) *
        (L * integral\<^sup>L lborel ?weight)"
    using minkowski_bound scaled_source by linarith
qed

end
