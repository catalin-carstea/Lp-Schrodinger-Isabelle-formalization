theory Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Fiber_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Convolution_Exponents"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Output_Density_All_Order_Unit_Terminal_Companion_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Lp_Translate"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted_Aliases"
begin

section \<open>One-terminal mixed convolution fibers in L2\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_one_terminal_fibers_L2:
  fixes R C p :: real
    and cutoff left_potential right_potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows left_terminal_right_unit:
    "\<And>left_order right_order root.
      slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset)))"
    and left_unit_right_terminal:
    "\<And>left_order right_order root.
      slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)))"
proof -
  note exponents = slp_mixed_one_terminal_exponents[OF p_lower p_upper]
  note split = slp_mixed_one_terminal_convolution_exponents[OF
      p_lower p_upper]
  note left_weighted =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  note right_weighted =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  note left_unit =
    slp_left_right_positive_output_density_all_orders_unit_terminal_companion[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  note right_unit =
    slp_left_right_positive_output_density_all_orders_unit_terminal_companion[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            (\<lambda>_. 1) right_order root (root + offset)))"
    for left_order right_order root
  proof -
    have left_lp:
        "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)"
      using left_weighted(2)[of left_order] by blast
    have right_base_lp:
        "slp_positive_ennreal_lp_on_plane
          (slp_mixed_unit_branch_exponent p)
          (slp_right_positive_output_density R cutoff right_potential
            (\<lambda>_. 1) right_order root)"
      using right_unit(2)[of right_order] by blast
    have right_shifted_lp:
        "slp_positive_ennreal_lp_on_plane
          (slp_mixed_unit_branch_exponent p)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset))"
      by (rule slp_positive_ennreal_lp_translate(1)[OF right_base_lp])
    show ?thesis
      by (rule slp_positive_ennreal_convolution_mixed_L2(1)[OF
            exponents(1) exponents(2) exponents(3) exponents(4)
            split(1) split(2) split(3) split(4) split(5)
            left_lp right_shifted_lp])
  qed
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          (\<lambda>_. 1) left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            (slp_positive_terminal_riesz_weight R right_potential)
            right_order root (root + offset)))"
    for left_order right_order root
  proof -
    have left_lp:
        "slp_positive_ennreal_lp_on_plane
          (slp_mixed_unit_branch_exponent p)
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root)"
      using left_unit(1)[of left_order] by blast
    have right_base_lp:
        "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
          (slp_right_positive_output_density R cutoff right_potential
            (slp_positive_terminal_riesz_weight R right_potential)
            right_order root)"
      using right_weighted(3)[of right_order] by blast
    have right_shifted_lp:
        "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset))"
      by (rule slp_positive_ennreal_lp_translate(1)[OF right_base_lp])
    have conjugate_swapped:
        "1 / slp_mixed_unit_split_exponent p +
          1 / slp_mixed_weight_split_exponent p = 1"
      using split(3) by linarith
    show ?thesis
      by (rule slp_positive_ennreal_convolution_mixed_L2(1)[OF
            exponents(3) exponents(4) exponents(1) exponents(2)
            split(2) split(1) conjugate_swapped split(5) split(4)
            left_lp right_shifted_lp])
  qed
qed

end

end
