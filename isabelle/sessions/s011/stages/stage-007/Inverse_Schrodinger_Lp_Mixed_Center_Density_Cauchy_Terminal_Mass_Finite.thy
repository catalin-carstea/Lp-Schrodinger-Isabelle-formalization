theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Cauchy_Terminal_Mass_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Density_Cutoff_Terminal_Monotone"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Weighted_Mass_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Cutoff_Terminal_Bound"
begin

section \<open>Finite mixed-center mass with actual Cauchy terminals\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_cauchy_terminal_all_orders_mass_finite:
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
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_density (2 * B) cutoff left_potential right_potential
        (\<lambda>x. ennreal (cmod
          (slp_cauchy_transform left_orientation left_potential x)))
        (\<lambda>x. ennreal (cmod
          (slp_cauchy_transform right_orientation right_potential x)))
        left_order right_order root_weight center \<partial>lborel) <
      top_class.top"
proof -
  let ?left_terminal = "\<lambda>x. ennreal (cmod
    (slp_cauchy_transform left_orientation left_potential x))"
  let ?right_terminal = "\<lambda>x. ennreal (cmod
    (slp_cauchy_transform right_orientation right_potential x))"
  let ?left_majorant =
    "slp_positive_terminal_riesz_weight (2 * B) left_potential"
  let ?right_majorant =
    "slp_positive_terminal_riesz_weight (2 * B) right_potential"
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
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
  have left_terminal_le:
      "\<And>x. ennreal (cmod (cutoff x)) * ?left_terminal x \<le>
        ennreal (cmod (cutoff x)) * ?left_majorant x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          left_support_radius])
  have right_terminal_le:
      "\<And>x. ennreal (cmod (cutoff x)) * ?right_terminal x \<le>
        ennreal (cmod (cutoff x)) * ?right_majorant x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          right_support_radius])
  have density_le:
      "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
          ?left_terminal ?right_terminal left_order right_order root_weight
          center \<le>
        slp_mixed_center_density (2 * B) cutoff left_potential right_potential
          ?left_majorant ?right_majorant left_order right_order root_weight
          center"
    for center
    by (rule slp_mixed_center_density_cutoff_terminal_mono[OF
          left_terminal_le right_terminal_le])
  have mass_le:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_density (2 * B) cutoff left_potential right_potential
          ?left_terminal ?right_terminal left_order right_order root_weight
          center \<partial>lborel) \<le>
        (\<integral>\<^sup>+ center.
        slp_mixed_center_density (2 * B) cutoff left_potential right_potential
          ?left_majorant ?right_majorant left_order right_order root_weight
          center \<partial>lborel)"
    by (rule nn_integral_mono) (rule density_le)
  have majorant_mass_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_density (2 * B) cutoff left_potential right_potential
          ?left_majorant ?right_majorant left_order right_order root_weight
          center \<partial>lborel) < top_class.top"
    by (rule
      slp_mixed_center_density_terminal_weighted_all_orders_mass_finite[OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound C_nonnegative])
  show ?thesis
    by (rule le_less_trans[OF mass_le majorant_mass_finite])
qed

end

end
