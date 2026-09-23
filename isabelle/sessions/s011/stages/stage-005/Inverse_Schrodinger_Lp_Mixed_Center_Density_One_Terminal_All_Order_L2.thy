theory Inverse_Schrodinger_Lp_Mixed_Center_Density_One_Terminal_All_Order_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_One_Terminal_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp"
begin

section \<open>All-order one-terminal mixed center densities in L2\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_one_terminal_all_orders_L2:
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
  shows left_terminal_right_unit:
    "\<And>left_order right_order.
      slp_positive_ennreal_lp_on_plane 2
        (slp_mixed_center_density R cutoff left_potential right_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          (\<lambda>_. 1) left_order right_order root_weight)"
    and left_unit_right_terminal:
    "\<And>left_order right_order.
      slp_positive_ennreal_lp_on_plane 2
        (slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>_. 1)
          (slp_positive_terminal_riesz_weight R right_potential)
          left_order right_order root_weight)"
proof -
  have root_weight_integrable: "integrable lborel root_weight"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded root_weight_lp root_weight_outside])
      (use p_lower in simp)
  note result = slp_mixed_center_density_one_terminal_L2[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      right_potential_lp root_weight_integrable cutoff_bound C_nonnegative]
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (\<lambda>_. 1) left_order right_order root_weight)"
    for left_order right_order
    by (rule result(1))
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density R cutoff left_potential right_potential
        (\<lambda>_. 1)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight)"
    for left_order right_order
    by (rule result(2))
qed

end

end
