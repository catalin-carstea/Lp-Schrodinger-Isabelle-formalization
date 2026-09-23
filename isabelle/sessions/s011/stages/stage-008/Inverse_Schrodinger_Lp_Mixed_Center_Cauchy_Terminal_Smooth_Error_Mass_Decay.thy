theory Inverse_Schrodinger_Lp_Mixed_Center_Cauchy_Terminal_Smooth_Error_Mass_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Average_Bracket_Algebra"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Uniform_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Measurable_Below_Two"
begin

section \<open>The mixed smooth-error mass\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_density_cauchy_terminal_all_orders_L1:
  fixes B C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight :: slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "slp_positive_ennreal_lp_on_plane 1
      (slp_mixed_center_density (2 * B) cutoff left_potential
        right_potential
        (\<lambda>x. ennreal (cmod
          (slp_cauchy_transform left_orientation left_potential x)))
        (\<lambda>x. ennreal (cmod
          (slp_cauchy_transform right_orientation right_potential x)))
        left_order right_order root_weight)"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?left_weight = "\<lambda>x. ennreal (cmod (?left_terminal x))"
  let ?right_weight = "\<lambda>x. ennreal (cmod (?right_terminal x))"
  let ?left_majorant =
    "slp_positive_terminal_riesz_weight (2 * B) left_potential"
  let ?right_majorant =
    "slp_positive_terminal_riesz_weight (2 * B) right_potential"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      ?left_weight ?right_weight left_order right_order root_weight"
  let ?majorant =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      ?left_majorant ?right_majorant left_order right_order root_weight"
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_terminal_measurable:
      "?left_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper left_potential_lp])
  have right_terminal_measurable:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have left_weight_measurable:
      "?left_weight \<in> borel_measurable lborel"
    using left_terminal_measurable by measurable
  have right_weight_measurable:
      "?right_weight \<in> borel_measurable lborel"
    using right_terminal_measurable by measurable
  have density_measurable: "?density \<in> borel_measurable lborel"
    by (rule slp_mixed_center_density_measurable[OF cutoff_measurable
          left_potential_measurable right_potential_measurable
          left_weight_measurable right_weight_measurable
          root_weight_measurable])
  have left_support_radius:
      "\<And>x y :: slp_point.
        \<lbrakk>cutoff x \<noteq> 0; left_potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
          norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support left_potential_support])
  have right_support_radius:
      "\<And>x y :: slp_point.
        \<lbrakk>cutoff x \<noteq> 0; right_potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
          norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support right_potential_support])
  have left_weight_le:
      "\<And>x. ennreal (cmod (cutoff x)) * ?left_weight x \<le>
        ennreal (cmod (cutoff x)) * ?left_majorant x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          left_support_radius])
  have right_weight_le:
      "\<And>x. ennreal (cmod (cutoff x)) * ?right_weight x \<le>
        ennreal (cmod (cutoff x)) * ?right_majorant x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          right_support_radius])
  have density_le: "?density center \<le> ?majorant center" for center
    by (rule slp_mixed_center_density_cutoff_terminal_mono[OF
          left_weight_le right_weight_le])
  have majorant_L1: "slp_positive_ennreal_lp_on_plane 1 ?majorant"
    by (rule slp_mixed_center_density_terminal_weighted_all_orders_L1[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative])
  show ?thesis
    by (rule slp_positive_ennreal_lp_mono_AE[OF zero_less_one majorant_L1
          density_measurable])
      (use density_le in simp)
qed

theorem slp_mixed_center_density_cauchy_terminal_smooth_error_mass_decay:
  fixes B C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight phi ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and phi_integrable: "integrable lborel phi"
    and uniform_convergence:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi
        at_top"
  shows
    "((\<lambda>tau. \<integral>\<^sup>+ center.
      slp_mixed_center_density (2 * B) cutoff left_potential
        right_potential
        (\<lambda>x. ennreal (cmod
          (slp_cauchy_transform left_orientation left_potential x)))
        (\<lambda>x. ennreal (cmod
          (slp_cauchy_transform right_orientation right_potential x)))
        left_order right_order root_weight center *
      ennreal (norm (slp_center_average tau phi center - phi center))
      \<partial>lborel) \<longlongrightarrow> 0) at_top"
proof -
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod
        (slp_cauchy_transform left_orientation left_potential x)))
      (\<lambda>x. ennreal (cmod
        (slp_cauchy_transform right_orientation right_potential x)))
      left_order right_order root_weight"
  have density_L1: "slp_positive_ennreal_lp_on_plane 1 ?density"
    by (rule slp_mixed_center_density_cauchy_terminal_all_orders_L1[OF
          B_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative
          cutoff_support left_potential_support right_potential_support])
  have density_finite:
      "AE center in lborel. ?density center < top_class.top"
    using density_L1
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have density_real_integrable:
      "integrable lborel (\<lambda>center. enn2real (?density center))"
    using density_L1
    unfolding slp_positive_ennreal_lp_on_plane_def by simp
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have center_average_measurable:
      "\<And>tau. slp_center_average tau phi \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_integrable])
  show ?thesis
    by (rule
      slp_positive_ennreal_uniform_difference_nn_integral_tendsto_zero[OF
        density_finite density_real_integrable center_average_measurable
        phi_measurable uniform_convergence])
qed

end

end
