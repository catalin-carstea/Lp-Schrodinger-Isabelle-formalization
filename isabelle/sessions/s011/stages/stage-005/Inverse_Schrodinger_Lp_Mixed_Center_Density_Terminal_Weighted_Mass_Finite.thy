theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Weighted_Mass_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Output_Density_All_Order_Terminal_Weighted_Mass_Power"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Mass_Uniform_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Below_Two"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp"
begin

section \<open>Finite mass with two terminal Riesz weights\<close>

lemma slp_positive_ennreal_mass_le_one_add_power_bound:
  fixes a M :: real
    and F :: "slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and M_nonnegative: "0 \<le> M"
    and F_L1: "slp_positive_ennreal_lp_on_plane 1 F"
    and mass_power_bound:
      "enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) powr a \<le> M"
  shows "(\<integral>\<^sup>+ x. F x \<partial>lborel) \<le> ennreal (1 + M)"
proof -
  let ?D = "\<lambda>x. enn2real (F x)"
  let ?I = "integral\<^sup>L lborel ?D"
  note real_data = slp_positive_ennreal_L1_real_representative[OF F_L1]
  have I_nonnegative: "0 \<le> ?I"
    by (rule integral_nonneg_AE) simp
  have real_mass: "enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel) = ?I"
    using real_data(5) I_nonnegative by simp
  have lower_power: "?I \<le> 1 + ?I powr a"
    using slp_powr_le_one_add_powr[of 1 a ?I] a_lower I_nonnegative
    by simp
  have I_power_bound: "?I powr a \<le> M"
    using mass_power_bound by (simp only: real_mass)
  have I_bound: "?I \<le> 1 + M"
    using lower_power I_power_bound by linarith
  show ?thesis
    apply (subst real_data(5))
    by (rule ennreal_leI[OF I_bound])
qed

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_terminal_weighted_all_orders_mass_finite:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
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
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight center \<partial>lborel) <
      top_class.top"
proof -
  let ?a = "slp_branch_power_exponent p"
  let ?left = "\<lambda>root output.
    slp_left_positive_output_density R cutoff left_potential
      (slp_positive_terminal_riesz_weight R left_potential)
      left_order root output"
  let ?right = "\<lambda>root output.
    slp_right_positive_output_density R cutoff right_potential
      (slp_positive_terminal_riesz_weight R right_potential)
      right_order root output"
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
      "slp_positive_terminal_riesz_weight R left_potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          left_potential_measurable])
  have right_terminal_measurable:
      "slp_positive_terminal_riesz_weight R right_potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          right_potential_measurable])
  note left_L1_data =
    slp_left_right_positive_output_density_all_orders_terminal_weighted_L1[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  note right_L1_data =
    slp_left_right_positive_output_density_all_orders_terminal_weighted_L1[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  have a_lower: "1 < ?a"
    using left_L1_data(1) by blast
  obtain left_power_bound where
      left_power_bound_nonnegative: "0 \<le> left_power_bound"
    and left_power:
      "\<forall>root. enn2real (\<integral>\<^sup>+ output. ?left root output
        \<partial>lborel) powr ?a \<le> left_power_bound"
    using slp_left_right_positive_output_density_all_orders_terminal_weighted_mass_power(1)[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative, of left_order]
    by blast
  obtain right_power_bound where
      right_power_bound_nonnegative: "0 \<le> right_power_bound"
    and right_power:
      "\<forall>root. enn2real (\<integral>\<^sup>+ output. ?right root output
        \<partial>lborel) powr ?a \<le> right_power_bound"
    using slp_left_right_positive_output_density_all_orders_terminal_weighted_mass_power(2)[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative, of right_order]
    by blast
  let ?left_bound = "ennreal (1 + left_power_bound)"
  let ?right_bound = "ennreal (1 + right_power_bound)"
  have left_mass_bound:
      "(\<integral>\<^sup>+ output. ?left root output \<partial>lborel) \<le>
        ?left_bound"
    for root
    by (rule slp_positive_ennreal_mass_le_one_add_power_bound[OF
          a_lower left_power_bound_nonnegative
          left_L1_data(2)]; use left_power in blast)
  have right_mass_bound:
      "(\<integral>\<^sup>+ output. ?right root output \<partial>lborel) \<le>
        ?right_bound"
    for root
    by (rule slp_positive_ennreal_mass_le_one_add_power_bound[OF
          a_lower right_power_bound_nonnegative
          right_L1_data(3)]; use right_power in blast)
  have root_weight_integrable: "integrable lborel root_weight"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded root_weight_lp root_weight_outside])
      (use p_lower in simp)
  have root_norm_integrable:
      "integrable lborel (\<lambda>root. Real_Vector_Spaces.norm (root_weight root))"
    by (rule integrable_norm[OF root_weight_integrable])
  have root_mass:
      "(\<integral>\<^sup>+ root.
          ennreal (Real_Vector_Spaces.norm (root_weight root)) \<partial>lborel) =
        ennreal (integral\<^sup>L lborel
          (\<lambda>root. Real_Vector_Spaces.norm (root_weight root)))"
    by (rule nn_integral_eq_integral[OF root_norm_integrable]) simp
  have mixed_bound:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_density R cutoff left_potential right_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          (slp_positive_terminal_riesz_weight R right_potential)
          left_order right_order root_weight center \<partial>lborel) \<le>
        (\<integral>\<^sup>+ root.
          ennreal (Real_Vector_Spaces.norm (root_weight root)) \<partial>lborel) *
        ?left_bound * ?right_bound"
    by (rule slp_mixed_center_density_mass_uniform_bound[OF
          cutoff_measurable left_potential_measurable
          right_potential_measurable left_terminal_measurable
          right_terminal_measurable root_weight_measurable
          left_mass_bound right_mass_bound])
  have bound_finite:
      "(\<integral>\<^sup>+ root.
          ennreal (Real_Vector_Spaces.norm (root_weight root)) \<partial>lborel) *
        ?left_bound * ?right_bound < top_class.top"
  proof -
    show ?thesis
      apply (subst root_mass)
      by (simp add: ennreal_mult_less_top)
  qed
  show ?thesis
    by (rule le_less_trans[OF mixed_bound bound_finite])
qed

end

end
