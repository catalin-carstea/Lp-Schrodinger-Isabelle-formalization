theory Inverse_Schrodinger_Lp_Born_Successor_Uniform_Power
  imports Inverse_Schrodinger_Lp_Born_Block_Real_Uniform_Mass
begin

section \<open>Uniform finite-power recurrence for positive Born densities\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_output_density_Suc_uniform_power:
  fixes R C p a b L B :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
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
      "\<And>origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n
          origin)"
    and density_power_bound:
      "\<And>origin.
        integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                origin output) powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
    and block_mass_bound:
      "\<And>origin.
        integral\<^sup>L lborel
          (slp_positive_branch_block_weight_real R cutoff potential origin)
          \<le> B"
    and B_nonnegative: "0 \<le> B"
  shows successor_lp:
    "\<And>origin. slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight (Suc n)
        origin)"
    and successor_power_bound:
    "\<And>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight
              (Suc n) origin output) powr a) \<le>
      inverse (pi ^ 2) powr a *
        (B powr (a / b) * (L * B))"
proof -
  show successor_lp:
      "slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight (Suc n)
          origin)"
    for origin
    by (rule slp_positive_output_density_Suc_finite_power(1)[OF
          radius_nonnegative p_lower p_upper a_lower b_lower conjugate
          cutoff_measurable potential_lp terminal_weight_measurable
          cutoff_bound density_lp density_power_bound L_nonnegative])
  show successor_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight
                (Suc n) origin output) powr a) \<le>
        inverse (pi ^ 2) powr a *
          (B powr (a / b) * (L * B))"
    for origin
  proof -
    let ?mass =
      "integral\<^sup>L lborel
        (slp_positive_branch_block_weight_real R cutoff potential origin)"
    have exact_bound:
        "integral\<^sup>L lborel
            (\<lambda>output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight
                  (Suc n) origin output) powr a) \<le>
          inverse (pi ^ 2) powr a *
            (?mass powr (a / b) * (L * ?mass))"
      by (rule slp_positive_output_density_Suc_finite_power(2)[OF
            radius_nonnegative p_lower p_upper a_lower b_lower conjugate
            cutoff_measurable potential_lp terminal_weight_measurable
            cutoff_bound density_lp density_power_bound L_nonnegative])
    have potential_measurable:
        "potential \<in> borel_measurable lborel"
      using potential_lp unfolding aim_complex_lp_on_plane_def by blast
    have weight_integrable:
        "integrable lborel
          (slp_positive_branch_block_weight_real R cutoff potential origin)"
      by (rule slp_positive_branch_block_weight_real_integrable[OF
            radius_nonnegative p_lower p_upper cutoff_measurable
            potential_lp cutoff_bound])
    have mass_nonnegative: "0 \<le> ?mass"
      by (rule integral_nonneg_AE)
        (rule AE_I2,
          rule slp_positive_branch_block_weight_real_nonnegative)
    have exponent_nonnegative: "0 \<le> a / b"
      using a_lower b_lower by simp
    have mass_power_le: "?mass powr (a / b) \<le> B powr (a / b)"
      by (rule powr_mono2[OF exponent_nonnegative mass_nonnegative
            block_mass_bound])
    have scaled_mass_le: "L * ?mass \<le> L * B"
      by (rule mult_left_mono[OF block_mass_bound L_nonnegative])
    have inner_le:
        "?mass powr (a / b) * (L * ?mass) \<le>
          B powr (a / b) * (L * B)"
      by (rule mult_mono[OF mass_power_le scaled_mass_le])
        (use mass_nonnegative L_nonnegative in simp_all)
    have coefficient_nonnegative:
        "0 \<le> inverse (pi ^ 2) powr a"
      by simp
    have uniform_bound:
        "inverse (pi ^ 2) powr a *
            (?mass powr (a / b) * (L * ?mass)) \<le>
          inverse (pi ^ 2) powr a *
            (B powr (a / b) * (L * B))"
      by (rule mult_left_mono[OF inner_le coefficient_nonnegative])
    show ?thesis
      using exact_bound uniform_bound by linarith
  qed
qed

end

end
