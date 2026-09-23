theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Weighted_L1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Weighted_All_Order_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Weighted_Mass_Finite"
begin

section \<open>The terminal-terminal mixed-density L1 endpoint\<close>

lemma slp_positive_ennreal_lp_mass_finite_to_L1:
  fixes F :: "slp_point \<Rightarrow> ennreal"
  assumes F_lp: "slp_positive_ennreal_lp_on_plane a F"
    and mass_finite:
      "(\<integral>\<^sup>+ x. F x \<partial>lborel) < top_class.top"
  shows "slp_positive_ennreal_lp_on_plane 1 F"
proof -
  have F_measurable: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top_class.top"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have real_measurable:
      "(\<lambda>x. enn2real (F x)) \<in> borel_measurable lborel"
    using F_measurable by measurable
  have real_mass:
      "(\<integral>\<^sup>+ x. enn2real (F x) \<partial>lborel) =
        (\<integral>\<^sup>+ x. F x \<partial>lborel)"
    by (rule nn_integral_cong_AE)
      (use F_finite in \<open>eventually_elim, simp\<close>)
  have real_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x))"
  proof (rule integrableI_nn_integral_finite[OF real_measurable])
    show "AE x in lborel. 0 \<le> enn2real (F x)" by simp
    show "(\<integral>\<^sup>+ x. enn2real (F x) \<partial>lborel) =
        ennreal (enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel))"
    proof -
      have mass_lift:
          "ennreal (enn2real (\<integral>\<^sup>+ x. F x \<partial>lborel)) =
            (\<integral>\<^sup>+ x. F x \<partial>lborel)"
        by (rule ennreal_enn2real[OF mass_finite])
      show ?thesis using real_mass mass_lift by simp
    qed
  qed
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using F_measurable F_finite real_integrable by simp
qed

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_terminal_weighted_all_orders_L1:
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
    "slp_positive_ennreal_lp_on_plane 1
      (slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight)"
proof (rule slp_positive_ennreal_lp_mass_finite_to_L1)
  show "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
      (slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight)"
    by (rule slp_mixed_center_density_terminal_weighted_all_orders_Lp(1)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
          root_weight_outside cutoff_bound C_nonnegative])
  show "(\<integral>\<^sup>+ center.
      slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight center \<partial>lborel) <
      top_class.top"
    by (rule
      slp_mixed_center_density_terminal_weighted_all_orders_mass_finite[OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound C_nonnegative])
qed

end

end
