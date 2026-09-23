theory Inverse_Schrodinger_Lp_Born_Block_Finite_Power
  imports Inverse_Schrodinger_Lp_Weighted_Source_Power_Bound_Pair
begin

section \<open>Finite power of one exact positive Born block\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_branch_block_real_finite_power:
  fixes R C p a b L :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
    and origin :: slp_point
    and n :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and density_lp:
      "\<And>inner_origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n
          inner_origin)"
    and density_power_bound:
      "\<And>inner_origin.
        integral\<^sup>L lborel
          (\<lambda>inner_output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                inner_origin inner_output) powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows target_integrable:
    "integrable lborel
      (\<lambda>output.
        (integral\<^sup>L lborel
          (\<lambda>pair.
            slp_positive_branch_block_weight_real R cutoff potential origin
              pair *
            slp_positive_branch_block_datum_real R cutoff potential
              terminal_weight n pair output)) powr a)"
    and target_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          (integral\<^sup>L lborel
            (\<lambda>pair.
              slp_positive_branch_block_weight_real R cutoff potential origin
                pair *
              slp_positive_branch_block_datum_real R cutoff potential
                terminal_weight n pair output)) powr a) \<le>
      (integral\<^sup>L lborel
        (slp_positive_branch_block_weight_real R cutoff potential origin))
          powr (a / b) *
      (L * integral\<^sup>L lborel
        (slp_positive_branch_block_weight_real R cutoff potential origin))"
proof -
  let ?weight =
    "slp_positive_branch_block_weight_real R cutoff potential origin"
  let ?datum =
    "slp_positive_branch_block_datum_real R cutoff potential terminal_weight n"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have weight_measurable: "?weight \<in> borel_measurable lborel"
    by (rule slp_positive_branch_block_weight_real_measurable[OF
          cutoff_measurable potential_measurable])
  have datum_joint_measurable:
      "case_prod ?datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_branch_block_datum_real_joint_measurable[OF
          cutoff_measurable potential_measurable
          terminal_weight_measurable])
  have weight_nonnegative: "0 \<le> ?weight pair" for pair
    by (rule slp_positive_branch_block_weight_real_nonnegative)
  have datum_nonnegative: "0 \<le> ?datum pair out" for pair out
    by (rule slp_positive_branch_block_datum_real_nonnegative)
  have weight_integrable: "integrable lborel ?weight"
    by (rule slp_positive_branch_block_weight_real_integrable[OF
          radius_nonnegative p_lower p_upper cutoff_measurable
          potential_lp cutoff_bound])
  have datum_power_integrable:
      "integrable lborel (\<lambda>output. ?datum pair output powr a)"
    for pair
    by (rule slp_positive_branch_block_datum_real_power_integrable[OF
          density_lp])
  have datum_power_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?datum pair output powr a)
        \<le> L"
    for pair
  proof -
    have inner_integrable:
        "integrable lborel
          (\<lambda>inner_output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                (snd pair) inner_output) powr a)"
      using density_lp[of "snd pair"]
      unfolding slp_positive_ennreal_lp_on_plane_def by blast
    have translated:
        "integral\<^sup>L lborel
            (\<lambda>output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight n
                  (snd pair) ((- fst pair + snd pair) + output)) powr a) =
          integral\<^sup>L lborel
            (\<lambda>inner_output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight n
                  (snd pair) inner_output) powr a)"
      by (rule slp_lborel_integral_translate[OF inner_integrable])
    have exact_translate:
        "integral\<^sup>L lborel (\<lambda>output. ?datum pair output powr a) =
          integral\<^sup>L lborel
            (\<lambda>inner_output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight n
                  (snd pair) inner_output) powr a)"
      using translated
      unfolding slp_positive_branch_block_datum_real_def
      by (simp add: algebra_simps)
    show ?thesis
      unfolding exact_translate
      by (rule density_power_bound)
  qed
  have source_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>pair. ?weight pair * ?datum pair output powr a))"
    by (rule slp_weighted_source_power_bound_pair(1)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have source_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>pair. ?weight pair * ?datum pair output powr a))
        \<le> L * integral\<^sup>L lborel ?weight"
    by (rule slp_weighted_source_power_bound_pair(2)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have fiber_integrable_AE:
      "AE output in lborel.
        integrable lborel
          (\<lambda>pair. ?weight pair * ?datum pair output powr a)"
    by (rule slp_weighted_joint_integrable_pair(2)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have minkowski_integrable:
      "integrable lborel
        (\<lambda>output.
          (integral\<^sup>L lborel
            (\<lambda>pair. ?weight pair * ?datum pair output)) powr a)"
    by (rule slp_integral_minkowski_power_pair_AE(1)[OF
          a_lower b_lower conjugate weight_measurable datum_joint_measurable
          weight_nonnegative datum_nonnegative weight_integrable
          fiber_integrable_AE source_integrable])
  have minkowski_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            (integral\<^sup>L lborel
              (\<lambda>pair. ?weight pair * ?datum pair output)) powr a) \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>pair. ?weight pair * ?datum pair output powr a))"
    by (rule slp_integral_minkowski_power_pair_AE(2)[OF
          a_lower b_lower conjugate weight_measurable datum_joint_measurable
          weight_nonnegative datum_nonnegative weight_integrable
          fiber_integrable_AE source_integrable])
  have weight_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel ?weight"
    by (rule integral_nonneg_AE)
      (rule AE_I2, rule weight_nonnegative)
  have scale_nonnegative:
      "0 \<le> (integral\<^sup>L lborel ?weight) powr (a / b)"
    by simp
  have scaled_source:
      "(integral\<^sup>L lborel ?weight) powr (a / b) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>pair. ?weight pair * ?datum pair output powr a))
        \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          (L * integral\<^sup>L lborel ?weight)"
    by (rule mult_left_mono[OF source_bound scale_nonnegative])
  show target_integrable:
      "integrable lborel
        (\<lambda>output.
          (integral\<^sup>L lborel
            (\<lambda>pair. ?weight pair * ?datum pair output)) powr a)"
    by (rule minkowski_integrable)
  show target_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            (integral\<^sup>L lborel
              (\<lambda>pair. ?weight pair * ?datum pair output)) powr a) \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          (L * integral\<^sup>L lborel ?weight)"
    using minkowski_bound scaled_source by linarith
qed

end

end
