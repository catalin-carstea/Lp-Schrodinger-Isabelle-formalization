theory Inverse_Schrodinger_Lp_Output_Density_All_Order_Unit_Terminal_Finite_Target
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Unweighted_Exponents"
begin

section \<open>All-order unit-terminal branch control for finite unweighted targets\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_positive_output_density_all_orders_unit_terminal_finite_target:
  fixes R C p t :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and t_lower: "1 < t"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows left_all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_mixed_unweighted_branch_exponent t)
          (slp_left_positive_output_density R cutoff potential (\<lambda>_. 1)
            n origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_left_positive_output_density R cutoff potential (\<lambda>_. 1)
              n origin output) powr slp_mixed_unweighted_branch_exponent t) \<le> L)"
    and right_all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_mixed_unweighted_branch_exponent t)
          (slp_right_positive_output_density R cutoff potential (\<lambda>_. 1)
            n origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_right_positive_output_density R cutoff potential (\<lambda>_. 1)
              n origin output) powr slp_mixed_unweighted_branch_exponent t) \<le> L)"
proof -
  let ?a = "slp_mixed_unweighted_branch_exponent t"
  let ?b = "slp_mixed_unweighted_branch_holder_exponent t"
  let ?scale = "inverse pi * C"
  let ?L0 = "?scale powr ?a * integral\<^sup>L lborel
    (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr ?a)"
  note exponents = slp_mixed_unweighted_finite_target_exponents[OF t_lower]
  have inverse_pi_nonnegative: "0 \<le> inverse pi"
    by simp
  have scale_nonnegative: "0 \<le> ?scale"
    using C_nonnegative inverse_pi_nonnegative by simp
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr ?a)"
    by (rule slp_localized_cauchy_kernel_power_integrable[OF
          less_imp_le[OF exponents(1)] exponents(2)])
  have kernel_power_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr ?a)"
    by (rule integral_nonneg_AE) simp
  have L0_nonnegative: "0 \<le> ?L0"
    using kernel_power_nonnegative by simp
  have base_lp:
      "\<And>origin. slp_positive_ennreal_lp_on_plane ?a
        (slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
          origin)"
  proof -
    fix origin :: slp_point
    let ?kernel = "\<lambda>output.
      ennreal (slp_localized_cauchy_kernel R (origin - output))"
    let ?h = "\<lambda>output. inverse pi * cmod (cutoff output)"
    have kernel_lp: "slp_positive_ennreal_lp_on_plane ?a ?kernel"
      by (rule slp_localized_cauchy_kernel_positive_ennreal_lp[OF
            less_imp_le[OF exponents(1)] exponents(2)])
    have h_measurable: "?h \<in> borel_measurable lborel"
      using cutoff_measurable by measurable
    have h_nonnegative: "0 \<le> ?h out" for out
      using inverse_pi_nonnegative by simp
    have h_bound: "?h out \<le> ?scale" for out
      by (rule mult_left_mono[OF cutoff_bound inverse_pi_nonnegative])
    have weighted_lp:
        "slp_positive_ennreal_lp_on_plane ?a
          (\<lambda>output. ennreal (?h output) * ?kernel output)"
      by (rule slp_positive_ennreal_lp_bounded_multiplier[OF
            less_trans[OF zero_less_one exponents(1)] h_measurable
            h_nonnegative h_bound scale_nonnegative kernel_lp])
    have density_eq:
        "slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
            origin =
          (\<lambda>output. ennreal (?h output) * ?kernel output)"
      by (rule ext)
        (simp add: ennreal_mult mult.commute mult.left_commute mult.assoc)
    show "slp_positive_ennreal_lp_on_plane ?a
        (slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
          origin)"
      unfolding density_eq by (rule weighted_lp)
  qed
  have base_power_bound:
      "\<And>origin. integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
            origin output) powr ?a) \<le> ?L0"
  proof -
    fix origin :: slp_point
    let ?kernel = "\<lambda>output.
      ennreal (slp_localized_cauchy_kernel R (origin - output))"
    let ?h = "\<lambda>output. inverse pi * cmod (cutoff output)"
    have kernel_lp: "slp_positive_ennreal_lp_on_plane ?a ?kernel"
      by (rule slp_localized_cauchy_kernel_positive_ennreal_lp[OF
            less_imp_le[OF exponents(1)] exponents(2)])
    have h_measurable: "?h \<in> borel_measurable lborel"
      using cutoff_measurable by measurable
    have h_nonnegative: "0 \<le> ?h out" for out
      using inverse_pi_nonnegative by simp
    have h_bound: "?h out \<le> ?scale" for out
      by (rule mult_left_mono[OF cutoff_bound inverse_pi_nonnegative])
    have weighted_bound:
        "integral\<^sup>L lborel
            (\<lambda>output. enn2real
              (ennreal (?h output) * ?kernel output) powr ?a) \<le>
          ?scale powr ?a * integral\<^sup>L lborel
            (\<lambda>output. enn2real (?kernel output) powr ?a)"
      by (rule slp_positive_ennreal_lp_bounded_multiplier_power_bound[OF
            less_trans[OF zero_less_one exponents(1)] h_measurable
            h_nonnegative h_bound scale_nonnegative kernel_lp])
    have kernel_integral:
        "integral\<^sup>L lborel
            (\<lambda>output. enn2real (?kernel output) powr ?a) =
          integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr ?a)"
      using slp_localized_cauchy_kernel_power_translate_integral[OF
          less_imp_le[OF exponents(1)] exponents(2), of R origin]
        slp_localized_cauchy_kernel_nonnegative
      by simp
    have density_eq:
        "slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
            origin =
          (\<lambda>output. ennreal (?h output) * ?kernel output)"
      by (rule ext)
        (simp add: ennreal_mult mult.commute mult.left_commute mult.assoc)
    show "integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
            origin output) powr ?a) \<le> ?L0"
      unfolding density_eq
      using weighted_bound kernel_integral by simp
  qed
  have terminal_measurable:
      "(\<lambda>_ :: slp_point. (1 :: ennreal)) \<in> borel_measurable lborel"
    by measurable
  obtain B where B_nonnegative: "0 \<le> B"
    and block_mass_bound:
      "\<forall>origin. integral\<^sup>L lborel
        (slp_positive_branch_block_weight_real R cutoff potential origin)
          \<le> B"
    using slp_positive_branch_block_weight_real_uniform[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative] by blast
  have all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane ?a
          (slp_positive_output_density R cutoff potential (\<lambda>_. 1) n
            origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_positive_output_density R cutoff potential (\<lambda>_. 1) n
              origin output) powr ?a) \<le> L)"
    by (rule slp_positive_output_density_all_orders_uniform_power[OF
          radius_nonnegative p_lower p_upper exponents(1) exponents(3)
          exponents(4) cutoff_measurable potential_lp terminal_measurable
          cutoff_bound base_lp base_power_bound L0_nonnegative
          block_mass_bound[rule_format] B_nonnegative])
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane ?a
        (slp_left_positive_output_density R cutoff potential (\<lambda>_. 1)
          n origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_left_positive_output_density R cutoff potential (\<lambda>_. 1)
            n origin output) powr ?a) \<le> L)"
    for n
    using all_orders[of n]
    by (simp only: slp_left_positive_output_density_def)
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane ?a
        (slp_right_positive_output_density R cutoff potential (\<lambda>_. 1)
          n origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_right_positive_output_density R cutoff potential (\<lambda>_. 1)
            n origin output) powr ?a) \<le> L)"
    for n
    using all_orders[of n]
    by (simp only: slp_right_positive_output_density_def)
qed

end

end
